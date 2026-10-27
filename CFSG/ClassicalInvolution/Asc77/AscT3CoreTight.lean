module

public import CFSG.ClassicalInvolution.Asc77.AscT3CoreComp
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.AscP1Strong
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Simple

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups commutatorElement

section SL2

theorem mat_sq_eq_one_of_pow_four (F : Type) [Field F] [CharP F 2] (A : Matrix (Fin 2) (Fin 2) F)
    (hdet : A.det = 1) (h4 : A ^ 4 = 1) : A * A = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hCH : A * A = A.trace • A + 1 := by
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
      first | ring1 | linear_combination (-1 : F) * hd - h2
  have key : (A.trace • A + 1) * (A.trace • A + 1) = (A.trace ^ 2) • (A * A) + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
      first
        | ring1
        | linear_combination ((A 0 0 + A 1 1) * A 0 0) * h2
        | linear_combination ((A 0 0 + A 1 1) * A 0 1) * h2
        | linear_combination ((A 0 0 + A 1 1) * A 1 0) * h2
        | linear_combination ((A 0 0 + A 1 1) * A 1 1) * h2
  have hsq : A ^ 4 = (A.trace ^ 2) • (A * A) + 1 := by
    have e : A ^ 4 = (A * A) * (A * A) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e]
    calc A * A * (A * A) = (A.trace • A + 1) * (A * A) := by rw [← hCH]
      _ = (A.trace • A + 1) * (A.trace • A + 1) := by rw [← hCH]
      _ = (A.trace ^ 2) • (A * A) + 1 := key
  have h0 : (A.trace ^ 2) • (A * A) = 0 := by
    have h1 : (A.trace ^ 2) • (A * A) + 1 = 1 := by rw [← hsq, h4]
    simpa using h1
  have hd0 : (A.trace ^ 2) ^ 2 = 0 := by
    have := congrArg Matrix.det h0
    rw [Matrix.det_smul, Matrix.det_mul, hdet, Matrix.det_zero] at this
    simpa using this
  have ht : A.trace = 0 :=
    (pow_eq_zero_iff (by norm_num)).mp ((pow_eq_zero_iff (by norm_num)).mp hd0)
  rw [hCH, ht]
  simp

theorem sl2_sq_eq_one_of_pow_four (F : Type) [Field F] [CharP F 2] (M : SL(2, F))
    (h : M ^ 4 = 1) : M ^ 2 = 1 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  have h4 : (M : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    have := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  have := mat_sq_eq_one_of_pow_four F _ hdet h4
  ext i j
  simpa [pow_two] using congrFun (congrFun this i) j

theorem prod_sq_eq_one_of_pow_four {n : ℕ}
    (g : Multiplicative (Fin n → ZMod 2) × SL(2, GaloisField 2 n)) (h : g ^ 4 = 1) :
    g ^ 2 = 1 := by
  have h1 : g.1 ^ 2 = 1 := by
    obtain ⟨v, hv⟩ : ∃ v : Fin n → ZMod 2, g.1 = Multiplicative.ofAdd v := ⟨g.1.toAdd, rfl⟩
    rw [hv, ← ofAdd_nsmul]
    have h2 : ∀ a : ZMod 2, (2 : ℕ) • a = 0 := by decide
    have : (2 : ℕ) • v = 0 := funext fun i => h2 (v i)
    rw [this]
    rfl
  have h2 : g.2 ^ 2 = 1 := sl2_sq_eq_one_of_pow_four _ _ (by simpa using congrArg Prod.snd h)
  exact Prod.ext h1 h2

end SL2

section Tight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K H : Subgroup G} {z : G}

theorem tightlyEmbedded_of_g2Section (hΩ : ConjInvariant Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hHdef : omegaGen (aStar Ω K) = H) (hsec : G2Section H z) :
    TightlyEmbedded H := by
  have hKS : K ∈ aStar Ω K := Relation.ReflTransGen.refl
  have hzH : z ∈ H := hHdef ▸ le_omegaGen hKS hz.mem
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  refine ⟨even_iff_two_dvd.mpr (hz2 ▸ Subgroup.orderOf_dvd_natCard H hzH), fun g hg => ?_⟩
  by_contra hnot
  have heven : Even (Nat.card ↥(H ⊓ rightConjugate H g)) := Nat.not_odd_iff_even.mp hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hx' : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hx2 : (x : G) * (x : G) = 1 := by rw [← pow_two]; exact hx' ▸ pow_orderOf_eq_one _
  have hx1 : (x : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hx'; omega
  have hxH : (x : G) ∈ H := (Subgroup.mem_inf.mp x.2).1
  have hxg : g * (x : G) * g⁻¹ ∈ H :=
    (mem_rightConjugate_iff H g x).mp (Subgroup.mem_inf.mp x.2).2
  have hy2 : (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) = 1 := by
    calc (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) = g * ((x : G) * (x : G)) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : g * (x : G) * g⁻¹ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this)
  obtain ⟨h, hh, hhx⟩ := hsec.conj x hxH hx2 hx1
  obtain ⟨h', hh', hh'y⟩ := hsec.conj _ hxg hy2 hy1
  have hc : h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹ = z := by
    calc h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹
        = h'⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h' := by group
      _ = h'⁻¹ * (g * (x : G) * g⁻¹) * h' := by rw [hhx]
      _ = h'⁻¹ * (h' * z * h'⁻¹) * h' := by rw [hh'y]
      _ = z := by group
  have hcz : h'⁻¹ * g * h ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hHS : H ≤ conjStab (aStar Ω K) := hHdef.symm.le.trans (omegaGen_aStar_le_conjStab hΩ hK)
  have hmem : g ∈ conjStab (aStar Ω K) := by
    have e : g = h' * (h'⁻¹ * g * h) * h⁻¹ := by group
    rw [e]
    exact (conjStab (aStar Ω K)).mul_mem
      ((conjStab (aStar Ω K)).mul_mem (hHS hh')
        (centralizer_le_conjStab_aStar hΩ hK hz hcz))
      ((conjStab (aStar Ω K)).inv_mem (hHS hh))
  apply hg
  have := conjStab_le_normalizer_omegaGen (aStar Ω K) hmem
  rwa [show omegaGen (aStar Ω K) = H from hHdef] at this

theorem layer_eq_top_of_quasisimple {M : Type*} [Group M] (hM : CFSG.IsQuasisimple M) :
    CFSG.layer M = ⊤ :=
  eq_top_iff.mpr (le_sSup (⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hM,
    Subgroup.IsSubnormal.top⟩ : CFSG.IsComponent (⊤ : Subgroup M)))

omit [Finite G] in
theorem twoPrimeLayerIn_eq_self
    (hq : CFSG.IsQuasisimple (↥H ⧸ classicalInvolutionOddCore ↥H)) : twoPrimeLayerIn H = H := by
  unfold twoPrimeLayerIn
  have h : CFSG.layer (↥H ⧸ CFSG.Assembly.oddCore ↥H) = ⊤ := layer_eq_top_of_quasisimple hq
  rw [h, Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype]

theorem not_mem_oddCoreIn (hz : IsUniqueInvolution K z) : z ∉ oddCoreIn H := by
  rintro ⟨w, hw, hwz⟩
  have hwz' : (w : G) = z := hwz
  have hw2 : w * w = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hwz']; exact hz.sq)
  have hw1 := eq_one_of_mul_self_of_mem_odd (N := classicalInvolutionOddCore ↥H)
    (CFSG.ComponentClassification.OddCore.odd_card ↥H) hw hw2
  exact hz.ne_one (by rw [← hwz, hw1]; rfl)

theorem two_le_pRank_of_commuting {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) {M : Subgroup G} (haM : a ∈ M)
    (hbM : b ∈ M) : 2 ≤ CFSG.Open.pRank 2 M := by
  obtain ⟨hcard, hsq⟩ := T7A.isElemAbelian2_closure_pair ha hb ha1 hb1 hab hc
  have hEM : Subgroup.closure ({a, b} : Set G) ≤ M := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact haM
    · exact hbM
  have hE : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
    have hxy : (x : G) * y * ((x : G) * y) = 1 := hsq _ (Subgroup.mul_mem _ x.2 y.2)
    have hxi : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x x.2)
    have hyi : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y y.2)
    apply Subtype.ext
    have := inv_eq_of_mul_eq_one_right hxy
    rw [mul_inv_rev, hxi, hyi] at this
    exact this.symm
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨_, hEM, hE, hcard⟩
  rintro k ⟨E, -, -, hk⟩
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ = Nat.card E := hk.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group E

omit [Finite G] in
theorem isQuasisimple_of_simple_nonabelian [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.IsQuasisimple G := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hperf : Group.IsPerfect G := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact ⟨h⟩
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

omit [Finite G] in
theorem isSimpleGroup_generalizedFitting [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    IsSimpleGroup (CFSG.generalizedFitting G) := by
  have hlay : CFSG.layer G = ⊤ :=
    layer_eq_top_of_quasisimple (isQuasisimple_of_simple_nonabelian hnab)
  have htop : CFSG.generalizedFitting G = ⊤ :=
    eq_top_iff.mpr (hlay ▸ (le_sup_right : CFSG.layer G ≤ CFSG.fittingSubgroup G ⊔ CFSG.layer G))
  let e : ↥(CFSG.generalizedFitting G) ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact e.isSimpleGroup

variable {p f : ℕ} [Fact p.Prime]

theorem exists_sq_eq_involution (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) : ∃ k ∈ K, k * k = z ∧ k ^ 4 = 1 := by
  obtain ⟨R, hRK, hR2, h8, -⟩ := exists_isPGroup_of_mem_mod hΩ hp hK hz
  obtain ⟨y, hyR, hy⟩ : ∃ y ∈ R, y * y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (R : Set G) ⊆ {1, z} := fun y hy => by
      rcases hz.unique y (hRK hy) (hcon y hy) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h2 : Nat.card ↥R ≤ 2 := by
      calc Nat.card ↥R = (R : Set G).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨m, hm⟩ := hR2 ⟨y, hyR⟩
  have hym : y ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨j, hjm, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hym)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hdvd : orderOf y ∣ 2 := by
      rw [hj]
      exact (Nat.pow_dvd_pow 2 (by omega : j ≤ 1))
    exact hy (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj2
  set k := y ^ (2 ^ d) with hk
  have hkord : orderOf k = 4 := by
    rw [hk, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega)),
      hj, pow_add, Nat.mul_div_cancel _ (by positivity)]
    norm_num
  have hk4 : k ^ 4 = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
  have hkK : k ∈ K := K.pow_mem (hRK hyR) _
  have hkk1 : k * k ≠ 1 := fun h => by
    have : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h)
    rw [hkord] at this
    omega
  have hsq : k * k * (k * k) = 1 := by
    calc k * k * (k * k) = k ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hk4
  exact ⟨k, hkK, (hz.unique _ (K.mul_mem hkK hkK) hsq).resolve_left hkk1, hk4⟩

theorem caseI_false (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h4 : Asc75Theorem4) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hΩ : HypOmegaMod p f Ω) {J : Subgroup G} {t : G}
    (hK : K ∈ Ω) (hv : AViol Ω K J z t) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M)
    (hbelow : CITBelowU p f (Nat.card G)) (hne : aStar Ω K ≠ Ω) : False := by
  obtain ⟨H, hHdef⟩ : ∃ H, omegaGen (aStar Ω K) = H := ⟨_, rfl⟩
  have hKS : K ∈ aStar Ω K := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar Ω K := Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨z, t, hv⟩⟩
  have hKH : K ≤ H := hHdef ▸ le_omegaGen hKS
  have hJH : J ≤ H := hHdef ▸ le_omegaGen hJS
  have hz : IsUniqueInvolution K z := hv.hzK
  have ht : IsUniqueInvolution J t := hv.hzJ
  have hzH : z ∈ H := hKH hz.mem
  have htH : t ∈ H := hJH ht.mem
  have hHtop : H ≠ ⊤ := fun h =>
    hne (aStar_eq_of_omegaGen_eq_top hΩ.conjInvariant hK htrans (hHdef.trans h))
  have hlt : Nat.card ↥H < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top H).mp h))
  have hsec : G2Section H z := g2Section_of_violation hp hq hΩ hbelow hK hHdef hv hlt
  have hT : TightlyEmbedded H :=
    tightlyEmbedded_of_g2Section hΩ.conjInvariant hK hz hHdef hsec
  have hlay : twoPrimeLayerIn H = H := twoPrimeLayerIn_eq_self hsec.quasisimple
  have hne' : twoPrimeLayerIn H ≠ oddCoreIn H := by
    rw [hlay]
    intro h
    exact not_mem_oddCoreIn hz (h ▸ hzH)
  have hHn : ¬ H.Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · exact hz.ne_one (by simpa [h] using hzH)
    · exact hHtop h
  have hF : IsSimpleGroup (CFSG.generalizedFitting G) := isSimpleGroup_generalizedFitting hnab
  rcases h4 G H hT hne' with hB | ⟨hr, -⟩ | ⟨g, hg, T, hTs, hTN, n, hn, φ, hφ, hker⟩
  · exact false_of_normalIn_twoPrimeLayerIn_top hT hHn hF hne' hB
  · rw [hlay] at hr
    have h2 := two_le_pRank_of_commuting hz.sq ht.sq hz.ne_one ht.ne_one
      (hv.ne_involution hΩ hK).symm (hv.comm hp hΩ) hzH htH
    omega
  · obtain ⟨k, hkK, hkk, hk4⟩ := exists_sq_eq_involution hΩ hp hK hz
    have hkH : k ∈ H := hKH hkK
    have hkC : k ∈ oUpperTwoPrime (H ⊔ T) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ T) hkH, 2, by simpa using hk4⟩
    have hzC : z ∈ oUpperTwoPrime (H ⊔ T) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ T) hzH, 1, by simpa [pow_two] using hz.sq⟩
    set k' : ↥(oUpperTwoPrime (H ⊔ T)) := ⟨k, hkC⟩ with hk'
    set z' : ↥(oUpperTwoPrime (H ⊔ T)) := ⟨z, hzC⟩ with hz'
    have hkz : k' ^ 2 = z' := Subtype.ext (by rw [pow_two, Subgroup.coe_mul]; exact hkk)
    have hk'4 : k' ^ 4 = 1 := Subtype.ext (by simpa using hk4)
    have hz1 : φ z' ≠ 1 := by
      intro h
      have hzk : z' ∈ φ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at hzk
      exact not_mem_oddCoreIn hz hzk
    have h44 : (φ k') ^ 4 = 1 := by rw [← map_pow, hk'4, map_one]
    exact hz1 (by rw [← hkz, map_pow]; exact prod_sq_eq_one_of_pow_four _ h44)

end Tight

end CFSG.ClassicalInvolution.Asc77.T3Core
