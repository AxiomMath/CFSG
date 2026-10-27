module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9Constrained
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle

public section

namespace CFSG.ABGTheoremB

open Matrix CFSG.QuasiDihedralFusion

universe u

section Ring

variable {R : Type*} [Ring R]

private theorem ring_cycle {a b : R} (ha : a * a = -1) (hb : b * b = -1)
    (hab : a * b = -(b * a)) :
    (1 + a) * (1 + b) * a = b * ((1 + a) * (1 + b)) ∧
      (1 + a) * (1 + b) * b = a * b * ((1 + a) * (1 + b)) := by
  have hba : b * a = -(a * b) := by rw [hab, neg_neg]
  have haba : a * b * a = b := by
    rw [mul_assoc, hba, mul_neg, ← mul_assoc, ha, neg_mul, one_mul, neg_neg]
  have hbab : b * a * b = a := by
    rw [hba, neg_mul, mul_assoc, hb, mul_neg, mul_one, neg_neg]
  constructor
  · have e1 : (1 + a) * (1 + b) * a = a + b * a + a * a + a * b * a := by noncomm_ring
    have e2 : b * ((1 + a) * (1 + b)) = b + b * a + b * b + b * a * b := by noncomm_ring
    rw [e1, e2, ha, hb, haba, hbab]
    abel
  · have e1 : (1 + a) * (1 + b) * b = b + b * b + a * b + a * (b * b) := by noncomm_ring
    have e2 : a * b * ((1 + a) * (1 + b)) =
        a * b + a * b * a + a * (b * b) + a * b * a * b := by noncomm_ring
    rw [e1, e2, hb, haba, hb]
    abel

end Ring

section Matrix

variable {F : Type*} [Field F]

private theorem mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem det_one_add_fin_two (A : Matrix (Fin 2) (Fin 2) F) :
    (1 + A).det = 1 + A.trace + A.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

private theorem trace_eq_zero_of_mul_self_eq_neg_one {A : Matrix (Fin 2) (Fin 2) F}
    (hA : A * A = -1) (hdet : A.det = 1) : A.trace = 0 := by
  have h := mul_self_fin_two A
  rw [hA, hdet, one_smul] at h
  have h' : A.trace • A = 0 := by
    have h2 := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) F)) h
    simpa using h2.symm
  by_contra htr
  have hA0 : A = 0 := by
    have h3 := congrArg ((A.trace)⁻¹ • ·) h'
    simpa [smul_smul, inv_mul_cancel₀ htr] using h3
  rw [hA0, Matrix.det_zero] at hdet
  exact zero_ne_one hdet

private theorem exists_sl2_cycle (h2 : (2 : F) ≠ 0) (a b : SpecialLinearGroup (Fin 2) F)
    (ha : (a : Matrix (Fin 2) (Fin 2) F) * a = -1) (hb : (b : Matrix (Fin 2) (Fin 2) F) * b = -1)
    (hab : (a : Matrix (Fin 2) (Fin 2) F) * b = -((b : Matrix (Fin 2) (Fin 2) F) * a)) :
    ∃ w : SpecialLinearGroup (Fin 2) F, w * a = b * w ∧ w * b = a * b * w := by
  set M : Matrix (Fin 2) (Fin 2) F :=
    (1 + (a : Matrix (Fin 2) (Fin 2) F)) * (1 + (b : Matrix (Fin 2) (Fin 2) F)) with hM
  have hdetM : M.det = 4 := by
    rw [hM, Matrix.det_mul, det_one_add_fin_two, det_one_add_fin_two,
      trace_eq_zero_of_mul_self_eq_neg_one ha a.2, trace_eq_zero_of_mul_self_eq_neg_one hb b.2,
      a.2, b.2]
    norm_num
  have hdet : ((2 : F)⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hdetM]
    field_simp
    norm_num
  obtain ⟨h1, h2'⟩ := ring_cycle ha hb hab
  refine ⟨⟨(2 : F)⁻¹ • M, hdet⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (2 : F)⁻¹ • M * (a : Matrix (Fin 2) (Fin 2) F) =
      (b : Matrix (Fin 2) (Fin 2) F) * ((2 : F)⁻¹ • M)
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, h1]
  · apply Subtype.ext
    change (2 : F)⁻¹ • M * (b : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) * b * ((2 : F)⁻¹ • M)
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, h2']


private theorem coe_eq_one_or_neg_one_of_mem_center {c : SpecialLinearGroup (Fin 2) F}
    (hc : c ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    (c : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (c : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    rw [← hrc, map_one]
  · right
    rw [← hrc, map_neg, map_one]

private theorem coe_mul_self_eq_neg_one (h2 : (2 : F) ≠ 0) {a : SpecialLinearGroup (Fin 2) F}
    (h1 : (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1)
    (hsq : (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
      (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1) :
    (a : Matrix (Fin 2) (Fin 2) F) * a = -1 := by
  have hmem : a * a ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_mul]; exact hsq)
  rcases coe_eq_one_or_neg_one_of_mem_center hmem with h | h
  · exfalso
    have hxx : a * a = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; simpa using h)
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left hxx
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 a hinv
      with rfl | rfl
    · exact h1 rfl
    · exact h1 ((QuotientGroup.eq_one_iff _).mpr
        (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F))
  · rw [Matrix.SpecialLinearGroup.coe_mul] at h
    exact h

private theorem exists_psl2_cycle (h2 : (2 : F) ≠ 0)
    {v₁ v₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F} (h₁ : v₁ ≠ 1) (h₂ : v₂ ≠ 1)
    (h₁₂ : v₁ ≠ v₂) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁) :
    ∃ w, w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ :=
  CFSG.QuasithinUnique.Unc25K1.exists_psl2_cycle h2 h₁ h₂ h₁₂ hv₁ hv₂ hc


end Matrix

section FourGroup

variable {P : Type*} [Group P]

private theorem cycle_props [Finite P] {v₁ v₂ w : P} (hv₂ : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁)
    (h₁₂ : v₁ ≠ v₂) (hw₁ : w * v₁ * w⁻¹ = v₂) (hw₂ : w * v₂ * w⁻¹ = v₁ * v₂) :
    w ∈ Subgroup.normalizer (Subgroup.closure ({v₁, v₂} : Set P) : Set P) ∧
      w ^ 3 ∈ Subgroup.centralizer (Subgroup.closure ({v₁, v₂} : Set P) : Set P) ∧
      w * v₁ * w⁻¹ ≠ v₁ := by
  have hw₃ : w * (v₁ * v₂) * w⁻¹ = v₁ := by
    calc w * (v₁ * v₂) * w⁻¹ = (w * v₁ * w⁻¹) * (w * v₂ * w⁻¹) := by group
      _ = v₂ * (v₁ * v₂) := by rw [hw₁, hw₂]
      _ = v₁ * (v₂ * v₂) := by rw [← mul_assoc, ← hc, mul_assoc]
      _ = v₁ := by rw [hv₂, mul_one]
  refine ⟨?_, ?_, by rw [hw₁]; exact h₁₂.symm⟩
  · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hle : (Subgroup.closure ({v₁, v₂} : Set P)).map (MulAut.conj w).toMonoidHom ≤
        Subgroup.closure ({v₁, v₂} : Set P) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · change w * y * w⁻¹ ∈ _
        rw [hw₁]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · change w * y * w⁻¹ ∈ _
        rw [hw₂]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    exact hle ⟨n, hn, rfl⟩
  · rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    have hpow : ∀ x : P, w ^ 3 * x * (w ^ 3)⁻¹ = w * (w * (w * x * w⁻¹) * w⁻¹) * w⁻¹ := by
      intro x
      simp only [pow_succ, pow_zero, one_mul]
      group
    rintro x (rfl | rfl)
    · have : w ^ 3 * x * (w ^ 3)⁻¹ = x := by rw [hpow, hw₁, hw₂, hw₃]
      calc x * w ^ 3 = (w ^ 3 * x * (w ^ 3)⁻¹)⁻¹⁻¹ * w ^ 3 := by rw [this, inv_inv]
        _ = w ^ 3 * x := by group
    · have : w ^ 3 * x * (w ^ 3)⁻¹ = x := by rw [hpow, hw₂, hw₃, hw₁]
      calc x * w ^ 3 = (w ^ 3 * x * (w ^ 3)⁻¹)⁻¹⁻¹ * w ^ 3 := by rw [this, inv_inv]
        _ = w ^ 3 * x := by group

end FourGroup

section Elements

private theorem isOddPrimePower_card_of_odd {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hcard' : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨ringChar F, n, hp, ?_, n.pos, hcard'⟩
  rw [hcard'] at hF
  exact (Nat.odd_pow_iff n.ne_zero).mp hF

private theorem not_mem_of_orderOf_eq_two {G : Type*} [Group G] {W : Subgroup G}
    (hW : Odd (Nat.card W)) {t : G} (ht : orderOf t = 2) : t ∉ W := by
  intro htW
  have h := orderOf_dvd_natCard (⟨t, htW⟩ : W)
  rw [Subgroup.orderOf_mk, ht] at h
  exact (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr h)

private theorem eq_one_or_eq_of_mem_zpowers {P : Type*} [Group P] {x g : P} (hx : orderOf x = 2)
    (hg : g ∈ Subgroup.zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one i with h | h <;> rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (zpow_one x)

private theorem isKleinFour_of_card_four' {X : Type*} [Group X] [Finite X] (h4 : Nat.card X = 4)
    (hsq : ∀ x : X, x * x = 1) : IsKleinFour X := by
  refine ⟨h4, ?_⟩
  have hdvd : Monoid.exponent X ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by rw [pow_two]; exact hsq x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have hsub : Subsingleton X := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := X)
    omega
  · exact h1

private theorem mem_of_index_eq_two_of_odd {X : Type*} [Group X] {K : Subgroup X}
    (hK : K.index = 2) {h : X} (hh : Odd (orderOf h)) : h ∈ K := by
  obtain ⟨k, hk⟩ := hh
  have heq : h = h ^ (k + 1) * h ^ (k + 1) := by
    rw [← pow_add, show k + 1 + (k + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [heq]
  exact Subgroup.mul_self_mem_of_index_two hK _

private theorem exists_isSylowOf_ge' {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q K : Subgroup X} (hQ : IsPGroup p Q) (hQK : Q ≤ K) :
    ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p S K ∧ Q ≤ S := by
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun q hq => ⟨⟨q, hQK hq⟩, hP hq, rfl⟩⟩

private theorem exists_two_part_mul_odd {X : Type*} [Group X] [Finite X] (c : X) :
    ∃ a ∈ Subgroup.zpowers c, ∃ b ∈ Subgroup.zpowers c, c = a * b ∧
      (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set x := Nat.gcdA (2 ^ k) m
  set y := Nat.gcdB (2 ^ k) m
  refine ⟨c ^ ((m : ℤ) * y), ⟨_, rfl⟩, c ^ ((2 ^ k : ℕ) * x : ℤ), ⟨_, rfl⟩, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← _root_.zpow_add, add_comm, ← hbez, zpow_one]
  · rw [← zpow_natCast, ← _root_.zpow_mul, show ((m : ℤ) * y) * ((2 ^ k : ℕ) : ℤ) =
        ((orderOf c : ℕ) : ℤ) * y by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, _root_.one_zpow]
  · refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← _root_.zpow_mul, show ((2 ^ k : ℕ) * x : ℤ) * (m : ℤ) =
        ((orderOf c : ℕ) : ℤ) * x by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, _root_.one_zpow]

end Elements

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem exists_image_four_group (hσ : σ.IsValid) {J W : Subgroup G} {F : Type} [Field F]
    [Finite F] (hWJ : W ≤ J) (hWodd : Odd (Nat.card W)) (hFodd : Odd (Nat.card F))
    (ψ : J →* CFSG.GorensteinWalter.PSL2 F) (hψker : ψ.ker = W.subgroupOf J) (hTJ : σ.T ≤ J) :
    ∃ V : Subgroup (CFSG.GorensteinWalter.PSL2 F), IsKleinFour V ∧
      Subgroup.centralizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) = V ∧
      (∀ t (ht : t ∈ σ.T), ψ ⟨t, hTJ ht⟩ ∈ V) ∧
      (∀ v ∈ V, ∃ t, ∃ ht : t ∈ σ.T, ψ ⟨t, hTJ ht⟩ = v) ∧
      σ.T ⊔ W = (V.comap ψ).map J.subtype ∧
      ∃ w ∈ Subgroup.normalizer (V : Set (CFSG.GorensteinWalter.PSL2 F)),
        w ^ 3 ∈ Subgroup.centralizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) ∧
        ∃ t, ∃ ht : t ∈ σ.T, w * ψ ⟨t, hTJ ht⟩ * w⁻¹ ≠ ψ ⟨t, hTJ ht⟩ := by
  have h2F : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  have hker : ∀ g : J, ψ g = 1 ↔ (g : G) ∈ W := fun g => by
    rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
  have hxJ : σ.x ∈ J := hTJ σ.x_mem_T
  have hx₂J : σ.x₂ ∈ J := hTJ σ.x₂_mem_T
  set v₁ := ψ ⟨σ.x, hxJ⟩ with hv₁def
  set v₂ := ψ ⟨σ.x₂, hx₂J⟩ with hv₂def
  have hx1 : σ.x * σ.x = 1 := by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
  have hx₂1 : σ.x₂ * σ.x₂ = 1 := by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
  have hv₁sq : v₁ * v₁ = 1 := by
    rw [hv₁def, ← map_mul]
    exact (hker _).mpr (by change σ.x * σ.x ∈ W; rw [hx1]; exact W.one_mem)
  have hv₂sq : v₂ * v₂ = 1 := by
    rw [hv₂def, ← map_mul]
    exact (hker _).mpr (by change σ.x₂ * σ.x₂ ∈ W; rw [hx₂1]; exact W.one_mem)
  have hv₁1 : v₁ ≠ 1 := fun h =>
    not_mem_of_orderOf_eq_two hWodd hσ.x_order ((hker _).mp h)
  have hv₂1 : v₂ ≠ 1 := fun h =>
    not_mem_of_orderOf_eq_two hWodd hσ.x₂_order ((hker _).mp h)
  have hc : v₁ * v₂ = v₂ * v₁ := by
    rw [hv₁def, hv₂def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hσ.commute
  have h₁₂ : v₁ ≠ v₂ := by
    intro h
    have h' : ψ (⟨σ.x, hxJ⟩ * ⟨σ.x₂, hx₂J⟩) = 1 := by rw [map_mul, ← hv₁def, ← hv₂def, h, hv₂sq]
    have hmem := (hker _).mp h'
    change σ.x * σ.x₂ ∈ W at hmem
    have hord : orderOf (σ.x * σ.x₂) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two, mul_assoc, ← mul_assoc σ.x₂, ← hσ.commute, mul_assoc, hx₂1, mul_one, hx1]
      · intro h1
        apply hσ.x_ne_x₂
        calc σ.x = σ.x * (σ.x₂ * σ.x₂) := by rw [hx₂1, mul_one]
          _ = (σ.x * σ.x₂) * σ.x₂ := by rw [mul_assoc]
          _ = σ.x₂ := by rw [h1, one_mul]
    exact not_mem_of_orderOf_eq_two hWodd hord hmem
  set V : Subgroup (CFSG.GorensteinWalter.PSL2 F) := Subgroup.closure {v₁, v₂} with hVdef
  have hord₁ : orderOf v₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv₁sq) hv₁1
  have hord₂ : orderOf v₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv₂sq) hv₂1
  have hV4 : IsKleinFour V := by
    refine CFSG.Wreathed.isKleinFour_closure_pair hord₁ hord₂ hc ?_
    rw [Subgroup.disjoint_def]
    intro y h1 h2
    rcases eq_one_or_eq_of_mem_zpowers hord₁ h1 with h | rfl
    · exact h
    rcases eq_one_or_eq_of_mem_zpowers hord₂ h2 with h | h
    · exact h
    · exact absurd h h₁₂
  have hCV : Subgroup.centralizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) = V :=
    CFSG.GorensteinWalter.psl2_kleinFour_centralizer_eq_self F (isOddPrimePower_card_of_odd hFodd)
      V hV4
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := by
    intro u hu v hv
    have := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hTV : ∀ t (ht : t ∈ σ.T), ψ ⟨t, hTJ ht⟩ ∈ V := by
    have hle : σ.T ≤ (V.comap ψ).map J.subtype := by
      change Subgroup.closure ({σ.x, σ.x₂} : Set G) ≤ _
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨⟨_, hxJ⟩, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨⟨_, hx₂J⟩, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    intro t ht
    obtain ⟨j, hj, hjt⟩ := hle ht
    have hj' : j = ⟨t, hTJ ht⟩ := Subtype.ext hjt
    rw [← hj']
    exact hj
  have hVT : ∀ v ∈ V, ∃ t, ∃ ht : t ∈ σ.T, ψ ⟨t, hTJ ht⟩ = v := by
    have hle : V ≤ (σ.T.subgroupOf J).map ψ := by
      rw [hVdef, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨⟨σ.x, hxJ⟩, σ.x_mem_T, rfl⟩
      · exact ⟨⟨σ.x₂, hx₂J⟩, σ.x₂_mem_T, rfl⟩
    intro v hv
    obtain ⟨j, hj, rfl⟩ := hle hv
    exact ⟨j, hj, rfl⟩
  obtain ⟨w, hw₁, hw₂⟩ := exists_psl2_cycle h2F hv₁1 hv₂1 h₁₂ hv₁sq hv₂sq hc
  obtain ⟨hwN, hw3, hwC⟩ := cycle_props hv₂sq hc h₁₂ hw₁ hw₂
  have hTW : σ.T ⊔ W = (V.comap ψ).map J.subtype := by
    apply le_antisymm
    · refine sup_le (fun t ht => ⟨⟨t, hTJ ht⟩, hTV t ht, rfl⟩) (fun x hx => ?_)
      refine ⟨⟨x, hWJ hx⟩, ?_, rfl⟩
      change ψ ⟨x, hWJ hx⟩ ∈ V
      rw [(hker _).mpr hx]
      exact V.one_mem
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨t, ht, htj⟩ := hVT (ψ j) hj
      have hk : ψ (⟨t, hTJ ht⟩⁻¹ * j) = 1 := by rw [map_mul, map_inv, htj, inv_mul_cancel]
      have hkW := (hker _).mp hk
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at hkW
      have : (j : G) = t * (t⁻¹ * j) := by group
      change (j : G) ∈ σ.T ⊔ W
      rw [this]
      exact Subgroup.mul_mem_sup ht hkW
  exact ⟨V, hV4, hCV, hTV, hVT, hTW, w, hwN, hw3, σ.x, σ.x_mem_T, hwC⟩

theorem exists_automizer_element_of_psl2_section (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧ ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W := by
  intro J W A F _ _ hWJ hJW hWodd hFodd hF3 ⟨ψ, hψ, hψker⟩ hTJ hA hAJ hAW hAT
  have : Fact r.Prime := ⟨hr⟩
  have hker : ∀ g : J, ψ g = 1 ↔ (g : G) ∈ W := fun g => by
    rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
  obtain ⟨V, hV4, hCV, hTV, hVT, hTW, w, hwN, hw3, t₀, ht₀, hwt₀⟩ :=
    σ.exists_image_four_group hσ hWJ hWodd hFodd ψ hψker hTJ
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := by
    intro u hu v hv
    have := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hconj : ∀ a ∈ A, ∀ g ∈ J, a * g * a⁻¹ ∈ J := fun a ha g hg =>
    (Subgroup.mem_normalizer_iff.mp (hAJ ha) g).mp hg
  let φ : A → J →* J := fun a =>
    { toFun := fun g => ⟨(a : G) * g * (a : G)⁻¹, hconj a a.2 g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ (a : A) (g : J), (φ a g : G) = (a : G) * g * (a : G)⁻¹ := fun _ _ => rfl
  have hφker : ∀ a : A, ψ.ker ≤ (ψ.comp (φ a)).ker := by
    intro a k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [MonoidHom.comp_apply]
    apply (hker _).mpr
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp (hAW a.2) k).mp ((hker k).mp hk)
  let α : A → (CFSG.GorensteinWalter.PSL2 F →* CFSG.GorensteinWalter.PSL2 F) := fun a =>
    (QuotientGroup.lift ψ.ker (ψ.comp (φ a)) (hφker a)).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom
  have hα : ∀ (a : A) (g : J), α a (ψ g) = ψ (φ a g) := by
    intro a g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ g) =
        (g : J ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift ψ.ker (ψ.comp (φ a)) (hφker a)
      ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ g)) = _
    rw [h1]
    rfl
  have hαV : ∀ (a : A) (v : CFSG.GorensteinWalter.PSL2 F), v ∈ V → α a v = v := by
    intro a v hv
    obtain ⟨t, ht, rfl⟩ := hVT v hv
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hφ]
    have h := (Subgroup.mem_centralizer_iff.mp (hAT a.2)) t ht
    change (a : G) * t * (a : G)⁻¹ = t
    rw [← h, mul_inv_cancel_right]
  have hαN : ∀ (a : A) (s : CFSG.GorensteinWalter.PSL2 F),
      s ∈ Subgroup.normalizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) → s⁻¹ * α a s ∈ V := by
    intro a s hs
    rw [← hCV, Subgroup.mem_centralizer_iff]
    intro v hv
    have hsv : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hs v).mp hv
    have h1 : α a (s * v * s⁻¹) = s * v * s⁻¹ := hαV a _ hsv
    rw [map_mul, map_mul, map_inv, hαV a v hv] at h1
    calc v * (s⁻¹ * α a s) = s⁻¹ * (s * v * s⁻¹) * α a s := by group
      _ = s⁻¹ * (α a s * v * (α a s)⁻¹) * α a s := by rw [h1]
      _ = s⁻¹ * α a s * v := by group
  have hVN : V ≤ Subgroup.normalizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) :=
    Subgroup.le_normalizer
  set X : Set (CFSG.GorensteinWalter.PSL2 F) := (fun v => w * v) '' (V : Set _) with hXdef
  have hXN : ∀ s ∈ X, s ∈ Subgroup.normalizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mul_mem _ hwN (hVN hv)
  have hXinv : ∀ (a : A) (s : CFSG.GorensteinWalter.PSL2 F), s ∈ X → α a s ∈ X := by
    intro a s hs
    have hsN := hXN s hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨v * ((w * v)⁻¹ * α a (w * v)), V.mul_mem hv (hαN a _ hsN), ?_⟩
    change w * (v * ((w * v)⁻¹ * α a (w * v))) = α a (w * v)
    group
  have hα1 : ∀ s, α 1 s = s := by
    intro s
    obtain ⟨g, rfl⟩ := hψ s
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hφ, OneMemClass.coe_one, one_mul, inv_one, mul_one]
  have hαmul : ∀ a b s, α (a * b) s = α a (α b s) := by
    intro a b s
    obtain ⟨g, rfl⟩ := hψ s
    rw [hα, hα, hα]
    congr 1
    apply Subtype.ext
    rw [hφ, hφ, hφ, Subgroup.coe_mul]
    group
  let _ : MulAction A X :=
    { smul := fun a x => ⟨α a x, hXinv a x x.2⟩
      one_smul := fun x => Subtype.ext (hα1 x)
      mul_smul := fun a b x => Subtype.ext (hαmul a b x) }
  have hXcard : Nat.card X = 4 := by
    rw [hXdef, Nat.card_image_of_injective (mul_right_injective w)]
    exact IsKleinFour.card_four
  have hr4 : ¬ r ∣ Nat.card X := by
    rw [hXcard]
    intro h
    have h' : r ∣ 2 ^ 2 := by norm_num; exact h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h'))
  obtain ⟨⟨s₀, hs₀X⟩, hfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card X hr4
  have hfix' : ∀ a : A, α a s₀ = s₀ := fun a => congrArg Subtype.val (hfix a)
  have hs₀N := hXN s₀ hs₀X
  have hs₀w : ∀ u ∈ V, s₀ * u * s₀⁻¹ = w * u * w⁻¹ := by
    obtain ⟨v₀, hv₀, rfl⟩ := hs₀X
    intro u hu
    change w * v₀ * u * (w * v₀)⁻¹ = w * u * w⁻¹
    rw [mul_assoc w v₀ u, hVcomm v₀ hv₀ u hu]
    group
  have hwV : ∀ u ∈ V, w * u * w⁻¹ ∈ V := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hwN u).mp hu
  have hs₀3 : ∀ u ∈ V, s₀ ^ 3 * u * (s₀ ^ 3)⁻¹ = u := by
    intro u hu
    have hpow : ∀ y x : CFSG.GorensteinWalter.PSL2 F,
        y ^ 3 * x * (y ^ 3)⁻¹ = y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ := by
      intro y x
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [hpow, hs₀w u hu, hs₀w _ (hwV u hu), hs₀w _ (hwV _ (hwV u hu)), ← hpow]
    have h := (Subgroup.mem_centralizer_iff.mp hw3) u hu
    rw [← h, mul_inv_cancel_right]
  obtain ⟨g₀, hg₀⟩ := hψ s₀
  refine ⟨g₀, g₀.2, ?_, ?_, ?_, t₀, ht₀, ?_⟩
  · intro a ha
    have h := hfix' ⟨a, ha⟩
    rw [← hg₀, hα] at h
    have h' : ψ (φ ⟨a, ha⟩ g₀ * g₀⁻¹) = 1 := by rw [map_mul, h, map_inv, mul_inv_cancel]
    have hmem := (hker _).mp h'
    rwa [Subgroup.coe_mul, hφ, Subgroup.coe_inv] at hmem
  ·
    rw [hTW]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨j, hj, rfl⟩ := hn
    refine ⟨g₀ * j * g₀⁻¹, ?_, rfl⟩
    change ψ (g₀ * j * g₀⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv, hg₀]
    exact (Subgroup.mem_normalizer_iff.mp hs₀N _).mp hj
  · intro t ht
    have h1 : ψ (g₀ ^ 3 * ⟨t, hTJ ht⟩ * (g₀ ^ 3)⁻¹ * ⟨t, hTJ ht⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hg₀, hs₀3 _ (hTV t ht),
        mul_inv_cancel]
    have h2 := (hker _).mp h1
    simpa using h2
  · intro hmem
    have h1 : ψ (g₀ * ⟨t₀, hTJ ht₀⟩ * g₀⁻¹ * ⟨t₀, hTJ ht₀⟩⁻¹) = 1 :=
      (hker _).mpr (by simpa using hmem)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₀, hs₀w _ (hTV t₀ ht₀)] at h1
    exact hwt₀ (mul_inv_eq_one.mp h1)

private theorem isKleinFour_T' (hσ : σ.IsValid) : IsKleinFour σ.T := by
  refine CFSG.Wreathed.isKleinFour_closure_pair hσ.x_order hσ.x₂_order hσ.commute ?_
  rw [Subgroup.disjoint_def]
  intro g h1 h2
  rcases eq_one_or_eq_of_mem_zpowers hσ.x_order h1 with h | rfl
  · exact h
  rcases eq_one_or_eq_of_mem_zpowers hσ.x₂_order h2 with h | h
  · exact h
  · exact absurd h hσ.x_ne_x₂

theorem inf_centralizer_T_le_of_linearType_nine (hσ : σ.IsValid) :
    ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H := by
  intro H _ hHD hlin
  obtain ⟨L, hOL, hLH, hHL, hTL, -, F, _, _, hF9, -, ψ, hψ, hψker⟩ := hlin
  set O := oddCoreIn H with hOdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFodd : Odd (Nat.card F) := by rw [hF9]; decide
  have hF3 : 3 < Nat.card F := by rw [hF9]; norm_num
  have hFpp := isOddPrimePower_card_of_odd hFodd
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn H
  have hker : ∀ l : L, ψ l = 1 ↔ (l : G) ∈ O := fun l => by
    rw [← MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
  obtain ⟨V, hV4, hCV, hTV, hVT, hTO, w, hwN, hw3, t₀, ht₀, hwt₀⟩ :=
    σ.exists_image_four_group hσ hOL hOodd hFodd ψ hψker hTL
  have hsimple : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have := hsimple
  have hcenter : Subgroup.center (CFSG.GorensteinWalter.PSL2 F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (CFSG.GorensteinWalter.PSL2 F)) with h | h
    · exact h
    · exfalso
      apply hwt₀
      have hc : w ∈ Subgroup.center (CFSG.GorensteinWalter.PSL2 F) := h ▸ Subgroup.mem_top w
      rw [← (Subgroup.mem_center_iff.mp hc) (ψ ⟨t₀, hTL ht₀⟩), mul_inv_cancel_right]
  have hcardPSL : Nat.card (CFSG.GorensteinWalter.PSL2 F) = 360 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula F hFpp, hF9]
    norm_num
  have hconj : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := fun h hh l hl =>
    (Subgroup.mem_normalizer_iff.mp (hHL hh) l).mp hl
  let φ : H → L →* L := fun h =>
    { toFun := fun l => ⟨(h : G) * l * (h : G)⁻¹, hconj h h.2 l l.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g k => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ (h : H) (l : L), (φ h l : G) = (h : G) * l * (h : G)⁻¹ := fun _ _ => rfl
  have hφker : ∀ h : H, ψ.ker ≤ (ψ.comp (φ h)).ker := by
    intro h k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [MonoidHom.comp_apply]
    apply (hker _).mpr
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H h.2) k).mp ((hker k).mp hk)
  let α : H → (CFSG.GorensteinWalter.PSL2 F →* CFSG.GorensteinWalter.PSL2 F) := fun h =>
    (QuotientGroup.lift ψ.ker (ψ.comp (φ h)) (hφker h)).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom
  have hα : ∀ (h : H) (l : L), α h (ψ l) = ψ (φ h l) := by
    intro h l
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ l) =
        (l : L ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift ψ.ker (ψ.comp (φ h)) (hφker h)
      ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ l)) = _
    rw [h1]
    rfl
  have hα1 : ∀ s, α 1 s = s := by
    intro s
    obtain ⟨l, rfl⟩ := hψ s
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hφ, OneMemClass.coe_one, one_mul, inv_one, mul_one]
  have hαmul : ∀ a b s, α (a * b) s = α a (α b s) := by
    intro a b s
    obtain ⟨l, rfl⟩ := hψ s
    rw [hα, hα, hα]
    congr 1
    apply Subtype.ext
    rw [hφ, hφ, hφ, Subgroup.coe_mul]
    group
  let _ : MulDistribMulAction H (CFSG.GorensteinWalter.PSL2 F) :=
    { smul := fun h s => α h s
      one_smul := hα1
      mul_smul := hαmul
      smul_mul := fun h x y => map_mul (α h) x y
      smul_one := fun h => map_one (α h) }
  let Φ : H →* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
    MulDistribMulAction.toMulAut H (CFSG.GorensteinWalter.PSL2 F)
  have hΦ : ∀ (h : H) (l : L), Φ h (ψ l) = ψ ⟨(h : G) * l * (h : G)⁻¹, hconj h h.2 l l.2⟩ :=
    fun h l => hα h l
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4.card_four]; norm_num)
  have hsylPSL : ∀ P : Sylow 2 (CFSG.GorensteinWalter.PSL2 F), V ≤ P →
      ¬ IsMulCommutative (P : Subgroup (CFSG.GorensteinWalter.PSL2 F)) := by
    intro P hVP hcomm
    have hPV : (P : Subgroup (CFSG.GorensteinWalter.PSL2 F)) ≤ V := by
      intro p hp
      rw [← hCV, Subgroup.mem_centralizer_iff]
      intro v hv
      have := (isMulCommutative_iff.mp hcomm) ⟨v, hVP hv⟩ ⟨p, hp⟩
      exact congrArg Subtype.val this
    have hdvd : Nat.card P ∣ 4 := hV4.card_four ▸ Subgroup.card_dvd_of_le hPV
    have hidx := P.not_dvd_index
    have hmul := (P : Subgroup (CFSG.GorensteinWalter.PSL2 F)).card_mul_index
    rw [hcardPSL] at hmul
    have hle : Nat.card P ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card P := Nat.card_pos
    interval_cases h : Nat.card P <;> omega
  have hsyl : ∀ S : Sylow 2 H, (∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (CFSG.Open.SemidihedralGroup n ≃* S) := by
    rcases hHD.1 with ⟨hD, -⟩ | ⟨K, hK⟩
    · exact fun S => Or.inl (hD S)
    rcases hK.sylow with ⟨n, hSD, -⟩ | ⟨n, -, hAb⟩
    · exact fun S => Or.inr ⟨n, hSD.1, hSD.2 S⟩
    exfalso
    let ι : L →* H := Subgroup.inclusion hLH
    have hOK : ∀ l : L, (l : G) ∈ O → ι l ∈ K := by
      intro l hl
      refine mem_of_index_eq_two_of_odd hK.index_eq_two ?_
      have h1 : orderOf (ι l) = orderOf (⟨l, hl⟩ : O) :=
        (Subgroup.orderOf_coe (ι l)).symm.trans (Subgroup.orderOf_mk (l : G) hl).symm
      rw [h1]
      exact hOodd.of_dvd_nat (orderOf_dvd_natCard _)
    have hLK : ∀ l : L, ι l ∈ K := by
      have : K.Normal := hK.normal
      have hdvd : (K.comap ι).index ∣ 2 := by
        rw [Subgroup.index_comap, ← hK.index_eq_two]
        exact Subgroup.relIndex_dvd_index_of_normal K ι.range
      have hkerle : ψ.ker ≤ K.comap ι := by
        intro l hl
        exact hOK l ((hker l).mp hl)
      have hidx : ((K.comap ι).map ψ).index = (K.comap ι).index := by
        rw [← Subgroup.index_comap_of_surjective _ hψ, Subgroup.comap_map_eq_self hkerle]
      have h1 : (K.comap ι).index = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact h
        · exfalso
          rw [← hidx] at h
          have : ((K.comap ι).map ψ).Normal := Subgroup.normal_of_index_eq_two h
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K.comap ι).map ψ) with hb | ht
          · rw [hb, Subgroup.index_bot, hcardPSL] at h
            omega
          · rw [ht, Subgroup.index_top] at h
            omega
      intro l
      have := Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top l
      exact this
    obtain ⟨P₀, hVP₀⟩ := hV2.exists_le_sylow
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hψ 2 P₀
    apply hsylPSL P₀ hVP₀
    have hPmap : ((P : Subgroup L).map ψ) = (P₀ : Subgroup (CFSG.GorensteinWalter.PSL2 F)) := by
      rw [← Sylow.coe_mapSurjective hψ, hP]
    have hPK : IsPGroup 2 (((P : Subgroup L).map ι).subgroupOf K) :=
      (P.isPGroup'.map ι).comap_subtype
    obtain ⟨Q, hQ⟩ := hPK.exists_le_sylow
    have hcommP : ∀ x ∈ (P : Subgroup L), ∀ y ∈ (P : Subgroup L), x * y = y * x := by
      intro x hx y hy
      have hx' : (⟨ι x, hLK x⟩ : K) ∈ Q := hQ ⟨x, hx, rfl⟩
      have hy' : (⟨ι y, hLK y⟩ : K) ∈ Q := hQ ⟨y, hy, rfl⟩
      have h := (isMulCommutative_iff.mp (hAb Q)) ⟨_, hx'⟩ ⟨_, hy'⟩
      have h' := congrArg (fun z : (Q : Subgroup K) => ((z : K) : H)) h
      simp only [Subgroup.coe_mul] at h'
      exact Subgroup.inclusion_injective hLH (by simpa using h')
    rw [isMulCommutative_iff]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hPmap] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hcommP x hx y hy]
  have hA : ∀ T' : Subgroup G, T' ≤ H → IsKleinFour T' → ∀ u ∈ H,
      u ∈ Subgroup.centralizer (T' : Set G) → (∃ k : ℕ, u ^ 2 ^ k = 1) → u ∈ T' := by
    intro T' hT'H hT' u huH huC ⟨k, hk⟩
    have hT'2 : IsPGroup 2 T' := IsPGroup.of_card (n := 2) (by rw [hT'.card_four]; norm_num)
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (T' : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ huC)
    have hQ := IsPGroup.to_sup_of_normal_left' hT'2 hu2 hnorm
    obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := H)).exists_le_sylow
    have hT'S : T'.subgroupOf H ≤ S := fun x hx => hS (le_sup_left (a := T') hx)
    have huS : (⟨u, huH⟩ : H) ∈ S := hS (show u ∈ T' ⊔ Subgroup.zpowers u from
      Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    set V' : Subgroup S := (T'.subgroupOf H).subgroupOf S
    let eV : V' ≃* T' :=
      (Subgroup.subgroupOfEquivOfLe hT'S).trans (Subgroup.subgroupOfEquivOfLe hT'H)
    have hV' : IsKleinFour V' :=
      ⟨by rw [Nat.card_congr eV.toEquiv]; exact hT'.card_four,
        by rw [Monoid.exponent_eq_of_mulEquiv eV]; exact hT'.exponent_two⟩
    have huC' : (⟨⟨u, huH⟩, huS⟩ : S) ∈ Subgroup.centralizer (V' : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h := (Subgroup.mem_centralizer_iff.mp huC) ((v : H) : G) hv
      exact Subtype.ext (Subtype.ext h)
    have hmem : (⟨⟨u, huH⟩, huS⟩ : S) ∈ V' := by
      rcases hsyl S with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨f⟩⟩
      · exact CFSG.GorensteinWalter.centralizer_kleinFour_le_of_dihedral_mulEquiv hm e V' hV' huC'
      · have h := (CFSG.Semidihedral.Local.semidihedral_four_subgroup_centralizers n hn f).2.1 V'
          hV'
        rw [h.2.1] at huC'
        exact huC'
    exact hmem
  have hF32 : Nat.card F = 3 ^ 2 := by rw [hF9]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπs := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hF32 hFpp hF3
  have hπi := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_injective F hFpp hF3
  have hBΦ : ∀ y : H, (y : G) ∈ Subgroup.centralizer (σ.T : Set G) → Odd (orderOf y) →
      Φ y = 1 := by
    intro y hyC hyodd
    obtain ⟨γ, hγ⟩ := hπs (Φ y)
    have hΦodd : Odd (orderOf (Φ y)) := hyodd.of_dvd_nat (orderOf_map_dvd Φ y)
    have hγodd : Odd (orderOf γ) := by
      rw [← orderOf_injective _ hπi γ, hγ]
      exact hΦodd
    have hγr : SemidirectProduct.rightHom γ = 1 := by
      have h1 : orderOf (SemidirectProduct.rightHom γ) ∣ orderOf γ := orderOf_map_dvd _ _
      have h2 : orderOf (SemidirectProduct.rightHom γ) ∣ 2 := by
        have h := orderOf_dvd_natCard (SemidirectProduct.rightHom γ)
        rwa [CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F Nat.prime_three hF32] at h
      have h3 : orderOf (SemidirectProduct.rightHom γ) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hγodd) h1 h2
      exact orderOf_eq_one_iff.mp h3
    have hγPGL : γ ∈ CFSG.GorensteinWalter.pGammaL2PGLRange F := by
      rw [CFSG.GorensteinWalter.pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hγr
    have hγPSL : γ ∈ CFSG.GorensteinWalter.pGammaL2PSLRange F := by
      have hrel := CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hFpp
      have hmem := mem_of_index_eq_two_of_odd hrel
        (h := (⟨γ, hγPGL⟩ : CFSG.GorensteinWalter.pGammaL2PGLRange F))
        (by rwa [Subgroup.orderOf_mk])
      exact hmem
    obtain ⟨ℓ, hℓ⟩ := (CFSG.GorensteinWalter.mem_pGammaL2PSLRange_iff F γ).mp hγPSL
    have hΦℓ : ∀ s, Φ y s = ℓ * s * ℓ⁻¹ := by
      intro s
      rw [← hγ, ← hℓ, CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_inl]
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [CFSG.GorensteinWalter.toPGL_pgl2InnerAutPSL2_apply, map_mul, map_mul, map_inv]
    have hℓV : ℓ ∈ Subgroup.centralizer (V : Set (CFSG.GorensteinWalter.PSL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨t, ht, rfl⟩ := hVT v hv
      have h1 : Φ y (ψ ⟨t, hTL ht⟩) = ψ ⟨t, hTL ht⟩ := by
        rw [hΦ]
        congr 1
        apply Subtype.ext
        change (y : G) * t * (y : G)⁻¹ = t
        rw [← (Subgroup.mem_centralizer_iff.mp hyC t ht), mul_inv_cancel_right]
      rw [hΦℓ] at h1
      calc ψ ⟨t, hTL ht⟩ * ℓ = (ℓ * ψ ⟨t, hTL ht⟩ * ℓ⁻¹) * ℓ := by rw [h1]
        _ = ℓ * ψ ⟨t, hTL ht⟩ := by group
    rw [hCV] at hℓV
    have hℓ2 : ℓ * ℓ = 1 := by
      have := IsKleinFour.mul_self (G := V) ⟨ℓ, hℓV⟩
      exact congrArg Subtype.val this
    have hΦ2 : Φ y ^ 2 = 1 := by
      ext s
      rw [pow_two, MulAut.mul_apply, hΦℓ, hΦℓ, MulAut.one_apply]
      calc ℓ * (ℓ * s * ℓ⁻¹) * ℓ⁻¹ = (ℓ * ℓ) * s * (ℓ * ℓ)⁻¹ := by group
        _ = s := by rw [hℓ2, one_mul, inv_one, mul_one]
    have h1 : orderOf (Φ y) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hΦodd)
        (orderOf_dvd_of_pow_eq_one hΦ2) dvd_rfl
    exact orderOf_eq_one_iff.mp h1
  have hT4 := isKleinFour_T' σ hσ
  have hT2 : IsPGroup 2 σ.T := IsPGroup.of_card (n := 2) (by rw [hT4.card_four]; norm_num)
  have hTN : σ.T ≤ Subgroup.normalizer (O : Set G) :=
    (hTL.trans hLH).trans (le_normalizer_oddCoreIn H)
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 σ.T (σ.T ⊔ O) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hT2, ?_⟩
    rw [sup_comm, relIndex_sup_eq_relIndex_of_le_normalizer hTN]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hOodd)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.relIndex_dvd_card _ _)))
  have hTOL : σ.T ⊔ O ≤ L := sup_le hTL hOL
  have hK₁odd : Odd (Nat.card Φ.ker) := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    set u' : G := ((u : H) : G) with hu'def
    have hu'H : u' ∈ H := (u : H).2
    have hu'o : orderOf u' = 2 := by
      rw [hu'def, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
    have hu'2 : u' * u' = 1 := by rw [← pow_two, ← hu'o, pow_orderOf_eq_one]
    have hΦu : ∀ l : L, ψ ⟨u' * l * u'⁻¹, hconj u' hu'H l l.2⟩ = ψ l := by
      intro l
      have h := hΦ (u : H) l
      rw [show Φ (u : H) = 1 from u.2, MulAut.one_apply] at h
      exact h.symm
    have hu'TO : u' ∈ Subgroup.normalizer ((σ.T ⊔ O : Subgroup G) : Set G) := by
      rw [hTO]
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨j, hj, rfl⟩ := hn
      refine ⟨⟨u' * j * u'⁻¹, hconj u' hu'H j j.2⟩, ?_, rfl⟩
      change ψ _ ∈ V
      rw [hΦu]
      exact hj
    have hXN : Subgroup.zpowers u' ⊔ (σ.T ⊔ O) ≤
        Subgroup.normalizer ((σ.T ⊔ O : Subgroup G) : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr hu'TO) Subgroup.le_normalizer
    have hu2 : IsPGroup 2 (Subgroup.zpowers u') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'o, pow_one])
    obtain ⟨S', hS', huS'⟩ := exists_isSylowOf_ge' hu2 (le_sup_left :
      Subgroup.zpowers u' ≤ Subgroup.zpowers u' ⊔ (σ.T ⊔ O))
    set T₂ := S' ⊓ (σ.T ⊔ O) with hT₂def
    have hT₂syl : CFSG.ABGLocalTools.IsSylowOf 2 T₂ (σ.T ⊔ O) :=
      hS'.inf_of_le_normalizer le_sup_right hXN
    have hT₂card : Nat.card T₂ = 4 := by
      rw [hT₂syl.card_eq, ← hTsyl.card_eq, hT4.card_four]
    have hT₂O : T₂ ⊓ O = ⊥ := by
      refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
      rw [hT₂card]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hOodd)
    have hT₂sq : ∀ x ∈ T₂, x * x = 1 := by
      intro x hx
      have hxTO : x ∈ (V.comap ψ).map L.subtype := hTO ▸ hx.2
      obtain ⟨j, hj, rfl⟩ := hxTO
      have hjj : ψ (j * j) = 1 := by
        rw [map_mul]
        exact congrArg Subtype.val (IsKleinFour.mul_self (G := V) ⟨ψ j, hj⟩)
      have hmem : (j : G) * j ∈ T₂ ⊓ O :=
        ⟨T₂.mul_mem hx hx, by simpa using (hker (j * j)).mp hjj⟩
      rw [hT₂O, Subgroup.mem_bot] at hmem
      exact hmem
    have hT₂4 : IsKleinFour T₂ :=
      isKleinFour_of_card_four' hT₂card fun x => Subtype.ext (hT₂sq x x.2)
    have hu'S' : u' ∈ S' := huS' (Subgroup.mem_zpowers u')
    have hu'T₂ : u' ∈ Subgroup.normalizer (T₂ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hu'S', hXN (hS'.le hu'S')⟩
    have hu'C : u' ∈ Subgroup.centralizer (T₂ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htL : t ∈ L := hTOL ht.2
      have hc : u' * t * u'⁻¹ * t⁻¹ ∈ T₂ ⊓ O := by
        refine ⟨T₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hu'T₂ t).mp ht) (T₂.inv_mem ht), ?_⟩
        have h1 : ψ (⟨u' * t * u'⁻¹, hconj u' hu'H t htL⟩ * (⟨t, htL⟩ : L)⁻¹) = 1 := by
          rw [map_mul, hΦu ⟨t, htL⟩, map_inv, mul_inv_cancel]
        simpa using (hker _).mp h1
      rw [hT₂O, Subgroup.mem_bot] at hc
      have h2 : u' * t * u'⁻¹ = t := mul_inv_eq_one.mp hc
      calc t * u' = (u' * t * u'⁻¹) * u' := by rw [h2]
        _ = u' * t := by group
    have hu'T₂mem : u' ∈ T₂ := hA T₂ (inf_le_right.trans (hTOL.trans hLH)) hT₂4 u' hu'H hu'C
      ⟨1, by rw [pow_one, pow_two]; exact hu'2⟩
    have hu'L : u' ∈ L := hTOL hu'T₂mem.2
    have hcent : ψ ⟨u', hu'L⟩ ∈ Subgroup.center (CFSG.GorensteinWalter.PSL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨l, rfl⟩ := hψ s
      have h := hΦu l
      have h' : ψ ⟨u' * l * u'⁻¹, hconj u' hu'H l l.2⟩ =
          ψ ⟨u', hu'L⟩ * ψ l * (ψ ⟨u', hu'L⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h'] at h
      calc ψ l * ψ ⟨u', hu'L⟩ = (ψ ⟨u', hu'L⟩ * ψ l * (ψ ⟨u', hu'L⟩)⁻¹) * ψ ⟨u', hu'L⟩ := by
            rw [h]
        _ = ψ ⟨u', hu'L⟩ * ψ l := by group
    rw [hcenter, Subgroup.mem_bot] at hcent
    exact not_mem_of_orderOf_eq_two hOodd hu'o ((hker _).mp hcent)
  have hB : ∀ y ∈ H, y ∈ Subgroup.centralizer (σ.T : Set G) → Odd (orderOf y) → y ∈ O := by
    intro y hyH hyC hyodd
    have h1 := hBΦ ⟨y, hyH⟩ hyC (by rwa [Subgroup.orderOf_mk])
    have hK₁O : Φ.ker ≤ CFSG.oddCore H := le_sSup ⟨inferInstance, hK₁odd⟩
    exact ⟨⟨y, hyH⟩, hK₁O h1, rfl⟩
  intro c hc
  obtain ⟨a, ha, b, hb, rfl, ha2, hbodd⟩ := exists_two_part_mul_odd c
  have haHC : a ∈ H ⊓ Subgroup.centralizer (σ.T : Set G) := (Subgroup.zpowers_le.mpr hc) ha
  have hbHC : b ∈ H ⊓ Subgroup.centralizer (σ.T : Set G) := (Subgroup.zpowers_le.mpr hc) hb
  exact Subgroup.mul_mem_sup (hA σ.T (hTL.trans hLH) hT4 a haHC.1 haHC.2 ha2)
    (hB b hbHC.1 hbHC.2 hbodd)

end Setting


end CFSG.ABGTheoremB
