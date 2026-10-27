module

public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.ClassicalInvolution.Orders.Twisted

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LieType.Ree CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.Timmesfeld.ExceptionalOrders
  CFSG.ClassicalInvolution CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem comparable_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {p : ℕ}
    (hp : p.Prime) (x y : C) (hx : ∃ k : ℕ, x ^ (p ^ k) = 1) (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) :
    (∃ m : ℤ, x * y ^ m = 1) ∨ ∃ m : ℤ, y * x ^ m = 1 := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  have hx : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hy : orderOf y ∣ p ^ l := orderOf_dvd_of_pow_eq_one hl
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hy
  have key : ∀ {x y : C} {i j : ℕ}, orderOf x = p ^ i → orderOf y = p ^ j → i ≤ j →
      ∃ m : ℤ, x * y ^ m = 1 := by
    intro x y i j hi hj hij
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ Nat.card (Subgroup.zpowers y) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hi, hj]
      exact pow_dvd_pow p hij
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y :=
      IsCyclic.subgroup_le_iff_card_dvd.mpr hdvd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers x))
    exact ⟨-m, by rw [zpow_neg, ← hm]; simp⟩
  rcases le_total i j with hij | hij
  · exact Or.inl (key hi hj hij)
  · exact Or.inr (key hj hi hij)

theorem outPChain_of_cyclic_subgroup {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup (Outer X)) [IsCyclic N]
    (hN : ∀ x : Outer X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ N) : OutPChain p X := by
  classical
  have : Finite (Outer X) := Quotient.finite _
  have : Finite N := inferInstance
  have hpow : ∀ (α : MulAut X) (k : ℕ), α ^ (p ^ k) ∈ Inn X →
      ((QuotientGroup.mk α : Outer X)) ^ (p ^ k) = 1 := fun α k hk => by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  refine ⟨Inn X, N.comap (QuotientGroup.mk' (Inn X)), le_rfl, fun δ hδ _ _ => hδ, ?_, ?_⟩
  · rintro α ⟨k, hk⟩
    exact hN _ ⟨k, hpow α k hk⟩
  · rintro α hα β hβ ⟨k, hk⟩ ⟨l, hl⟩
    let x : N := ⟨QuotientGroup.mk α, hα⟩
    let y : N := ⟨QuotientGroup.mk β, hβ⟩
    have hx : x ^ (p ^ k) = 1 := Subtype.ext (hpow α k hk)
    have hy : y ^ (p ^ l) = 1 := Subtype.ext (hpow β l hl)
    rcases comparable_of_isCyclic (C := N) hp x y ⟨k, hx⟩ ⟨l, hy⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      refine ⟨m, (QuotientGroup.eq_one_iff _).1 ?_⟩
      have := congrArg Subtype.val hm
      simpa [x, y] using this
    · right
      refine ⟨m, (QuotientGroup.eq_one_iff _).1 ?_⟩
      have := congrArg Subtype.val hm
      simpa [x, y] using this

theorem torusCoordHom_eq_rootDiagUnit' {τ : Tag} {K : Type} [Field K]
    (c : Fin τ.rank → Kˣ) :
    ((torusCoordHom τ K c : torusGroup τ K) : ModGL τ K) =
      rootDiagUnit τ (zpowMatrix (G := Kˣ) τ.cartan c) := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)
  · change _ = rootDiag (zpowMatrix (G := Kˣ) τ.cartan c) (hVec τ K j)
    rw [rootDiag_hVec, coe_torusCoordHom, list_ofFn_torusElt, list_prod_torusElt_hVec]
  · change _ = rootDiag (zpowMatrix (G := Kˣ) τ.cartan c) (rootVec τ K α)
    rw [rootDiag_rootVec _ hα, coe_torusCoordHom, list_ofFn_torusElt,
      list_prod_torusElt_rootVec hα, List.map_ofFn, List.prod_ofFn]
    congr 2
    simp only [Function.comp]
    unfold rootChar
    have hz : ∀ i, (zpowMatrix τ.cartan) c i ^ α i = ∏ j, c j ^ (τ.cartan j i * α i) := by
      intro i
      rw [zpowMatrix_apply, ← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    simp only [hz]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => by rw [Finset.prod_zpow_eq_zpow_sum]

theorem eq_one_of_pElement_not_dvd_card {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ Nat.card G) (y : G) (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hy
  have hcop : Nat.Coprime (p ^ k) (Nat.card G) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_natCard y))

theorem rootDiagAut_mem_inner_of_index_eq_one
    {τ : Tag} {K : Type} [Field K] [Finite K]
    (hidx : (monomialHom (G := Kˣ) τ.cartan.transpose).range.index = 1)
    (a : Fin τ.rank → Kˣ) : rootDiagAut τ K a ∈ inner (adjointGroup τ K) := by
  obtain ⟨t, ht⟩ : a ∈ (monomialHom (G := Kˣ) τ.cartan.transpose).range :=
    (Subgroup.index_eq_one.1 hidx) ▸ Subgroup.mem_top a
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t

theorem outPChain_E6_three
    {r f : ℕ} (hr : r.Prime) (hf1 : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (hm : UntwistedChevalleyModel X .E6 (r ^ f)) (h : ¬ 3 ∣ r ^ f - 1 ∨ ¬ 3 ∣ f) :
    OutPChain 3 X := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6 hm
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have hring := card_ringAut_and_isCyclic hr K hK
  have hfinR : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have hcycR : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hr.ne_zero)
  have hfinG : Finite (adjointGroup Tag.E6 K) := Finite.of_equiv X e.toEquiv
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  have hker3 : Nat.card Φ.ker ∣ 3 := hdet ▸ hdvd
  have hexact : ¬ 3 ∣ exactE Tag.E6 := by
    have he : exactE Tag.E6 = 2 := rfl
    rw [he]; norm_num
  refine OutPChain.of_mulEquiv e ?_
  rcases h with hA | hB
  ·
    have hidx : (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range.index = 1 := by
      have h1 := (index_range_monomialHom_dvd K Tag.E6.cartan.transpose).2
      rw [Matrix.det_transpose, hdet] at h1
      have h2 : (monomialHom (G := Kˣ) Tag.E6.cartan.transpose).range.index ∣
          Nat.card (Fin Tag.E6.rank → Kˣ) := Subgroup.index_dvd_card _
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units,
        hK] at h2
      rcases (Nat.dvd_prime hp).1 h1 with h3 | h3
      · exact h3
      · rw [h3] at h2
        exact absurd (hp.dvd_of_dvd_pow h2) hA
    have hbot : Φ.ker = ⊥ := by
      rw [hkerΦ, eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff _).2 (rootDiagAut_mem_inner_of_index_eq_one hidx a)
    let Θ := Φ.comp (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)))
    have := outPNice_of_hom (p := 3) Θ ?_ ?_ ?_ ?_
    · exact this.toChain
    · intro x y
      exact Prod.ext (ringAut_comm K _ _) (mul_comm _ _)
    · intro δ hδ
      have h1 : (QuotientGroup.mk δ : Outer (adjointGroup Tag.E6 K)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hδ
      show Φ (QuotientGroup.mk δ) = 1
      rw [h1, map_one]
    · intro δ hδ k hk
      have hx : (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) δ) ∈ Φ.ker := hδ
      rw [hbot, Subgroup.mem_bot] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    · exact pChain_prod (pChain_of_isCyclic hp) (multiplicative_zmod_pElement hp hexact)
  ·
    have hcyc : IsCyclic Φ.ker := by
      have : Finite Φ.ker := Nat.finite_of_card_ne_zero (fun h0 => by
        rw [h0] at hker3; exact absurd (Nat.eq_zero_of_zero_dvd hker3) (by norm_num))
      rcases (Nat.dvd_prime hp).1 hker3 with h1 | h3
      · have : Subsingleton Φ.ker := Finite.card_le_one_iff_subsingleton.1 (le_of_eq h1)
        exact isCyclic_of_subsingleton
      · have : Fact (Nat.Prime 3) := ⟨hp⟩
        exact isCyclic_of_prime_card h3
    refine outPChain_of_cyclic_subgroup hp Φ.ker ?_
    intro x ⟨k, hk⟩
    have hΦk : (Φ x) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have h1 : (Φ x).1 = 1 := eq_one_of_pElement_not_dvd_card hp
      (by rw [hring.1]; exact hB) _ ⟨k, congrArg Prod.fst hΦk⟩
    have h2 : (Φ x).2 = 1 := multiplicative_zmod_pElement hp hexact _
      ⟨k, congrArg Prod.snd hΦk⟩
    exact Prod.ext h1 h2

section E6

variable {K : Type} [Field K]

noncomputable def t1b_e6CompatHom (σ : K ≃+* K) :
    ((a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      compatSubgroup (t := TwistTag.E6) σ.toRingHom where
  toFun u := ⟨compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u⟩
  map_one' := Subtype.ext compatDiag_one
  map_mul' u v := Subtype.ext (compatDiag_mul u v)

theorem t1b_compatDiagAutHom_mem_inner_of_cartan
    (σ : K ≃+* K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (c : compatSubgroup (t := TwistTag.E6) σ.toRingHom)
    (h : zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c.1 =
      compatDiag TwistTag.E6 σ.toRingHom u) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ twistedE6Inn K σ := by
  have hT : (torusCoordHom TwistTag.E6.tag K c.1 : ModGL TwistTag.E6.tag K) ∈
      compatTorus (t := TwistTag.E6) σ.toRingHom :=
    (mem_compatTorus σ.toRingHom).2 ⟨c.1, c.2, rfl⟩
  have h' := compatTorus_le_graphFixedRootGroup (t := TwistTag.E6) (K := K) σ.toRingHom hT
  have hmem : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rwa [torusCoordHom_eq_rootDiagUnit', h] at h'
  refine ⟨⟨_, hmem⟩, ?_⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_compatDiagAutHom]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

theorem t1b_zpowMatrix_cartan_mem_compat' (σ : K ≃+* K)
    {c : Fin TwistTag.E6.tag.rank → Kˣ} (hc : c ∈ compatSubgroup (t := TwistTag.E6) σ.toRingHom) :
    zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan c ∈
      compatSubgroup (t := TwistTag.E6) σ.toRingHom := by
  intro j
  simp only [zpowMatrix_apply, map_prod, map_zpow]
  rw [← Equiv.prod_comp TwistTag.E6.perm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hc i, TwistTag.cartan_perm]

noncomputable def t1b_e6CartanHom (σ : K ≃+* K) :
    compatSubgroup (t := TwistTag.E6) σ.toRingHom →*
      compatSubgroup (t := TwistTag.E6) σ.toRingHom :=
  ((zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).domRestrict
    (compatSubgroup (t := TwistTag.E6) σ.toRingHom)).codRestrict
      (compatSubgroup (t := TwistTag.E6) σ.toRingHom)
      (fun c => t1b_zpowMatrix_cartan_mem_compat' σ c.2)

theorem t1b_card_range_diag_outer_le_gcd [Finite K]
    {q : ℕ}
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) :
    Nat.card ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range ≤ Nat.gcd 3 (q + 1) := by
  classical
  set S := compatSubgroup (t := TwistTag.E6) σ.toRingHom with hS
  set Z' := t1b_e6CartanHom σ with hZ'
  have hI : Z'.range.Normal := Subgroup.normal_of_isMulCommutative _
  let π1 : ((a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) →*
      S ⧸ Z'.range := (QuotientGroup.mk' Z'.range).comp (t1b_e6CompatHom σ)
  set ψ := (QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom) with hψ
  have hle : π1.ker ≤ ψ.ker := by
    intro u hu
    have hu' : t1b_e6CompatHom σ u ∈ Z'.range := (QuotientGroup.eq_one_iff _).1 hu
    obtain ⟨c, hc⟩ := hu'
    have hinner := t1b_compatDiagAutHom_mem_inner_of_cartan σ u c (congrArg Subtype.val hc)
    exact (QuotientGroup.eq_one_iff _).2 hinner
  have h1 : Nat.card ψ.range = ψ.ker.index := (Subgroup.index_ker ψ).symm
  have h2 : ψ.ker.index ∣ π1.ker.index := Subgroup.index_dvd_of_le hle
  have h3 : π1.ker.index = Nat.card π1.range := Subgroup.index_ker π1
  have h4 : Nat.card π1.range ≤ Z'.range.index :=
    Nat.card_le_card_of_injective (Subtype.val : π1.range → S ⧸ Z'.range) Subtype.val_injective
  have h5 : Z'.range.index = Nat.card Z'.ker := by
    have e1 : Nat.card S = Nat.card Z'.range * Nat.card Z'.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z'.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange Z').toEquiv]
    have e2 : Nat.card Z'.range * Z'.range.index = Nat.card S := Subgroup.card_mul_index _
    have hpos : 0 < Nat.card Z'.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (e2.trans e1)
  have h6 : Nat.card Z'.ker ≤ Nat.gcd 3 (q + 1) := by
    have hinj : Function.Injective (fun x : Z'.ker =>
        (⟨(x : S).1, Subgroup.mem_inf.2 ⟨(x : S).2, by
          have hx : Z' (x : S) = 1 := x.2
          have := congrArg Subtype.val hx
          exact this⟩⟩ :
        ↥(S ⊓ (zpowMatrix (G := Kˣ) TwistTag.E6.tag.cartan).ker))) := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have := Nat.card_le_card_of_injective _ hinj
    rw [hS, card_compat_inf_ker_E6_of_card hK hσ] at this
    exact this
  have hpos : 0 < π1.ker.index := by
    rw [h3]; exact Nat.card_pos
  calc Nat.card ψ.range = ψ.ker.index := h1
    _ ≤ π1.ker.index := Nat.le_of_dvd hpos h2
    _ ≤ Nat.gcd 3 (q + 1) := by rw [h3]; exact h4.trans (h5 ▸ h6)

end E6


theorem outPChain_twistedE6_three
    {r f : ℕ} (hrp : r.Prime) (hf1 : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (hm : TwistedChevalleyModel X .E6 (r ^ f)) (h : ¬ 3 ∣ r ^ f + 1 ∨ ¬ 3 ∣ f) :
    OutPChain 3 X := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hrp hf1 K hcard σ' hσ'
  have hK2 : Nat.card K = (r ^ f) ^ 2 := hcard
  have hK3 : Nat.card K = r ^ (f * 2) := by rw [hK2, ← pow_mul]
  have hring := card_ringAut_and_isCyclic hrp K hK3
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ hrp.ne_zero))
  have hψ := t1b_card_range_diag_outer_le_gcd hK2 σ' hσ'
  refine OutPChain.of_mulEquiv (e.trans E) ?_
  have hinner : Inn (twistedE6RootGroup K σ') ≤ Θ.ker := by
    rw [hker]; exact le_sup_left
  rcases h with hA | hB
  ·
    have hgcd : Nat.gcd 3 (r ^ f + 1) = 1 :=
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hA)
    have hψ1 : Nat.card ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
        (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)).range ≤ 1 := hgcd ▸ hψ
    have hkerle : Θ.ker ≤ Inn (twistedE6RootGroup K σ') := by
      intro x hx
      rw [hker] at hx
      obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      have hsub : Subsingleton ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
          (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)).range :=
        Finite.card_le_one_iff_subsingleton.1 hψ1
      have hz1 : ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
          (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)) u = 1 := by
        have := Subsingleton.elim (⟨_, u, rfl⟩ : ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
          (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)).range) 1
        exact congrArg Subtype.val this
      have hz : compatDiagAutHom TwistTag.E6 K σ'.toRingHom u ∈
          Inn (twistedE6RootGroup K σ') := (QuotientGroup.eq_one_iff _).1 hz1
      rw [← hyz]
      exact mul_mem hy hz
    have := outPNice_of_hom (p := 3) Θ (ringAut_comm K) hinner
      (fun δ hδ k hk => hkerle hδ) (pChain_of_isCyclic hp)
    exact this.toChain
  ·
    have hN1 : (Θ.ker).map (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ'))) ≤
        ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
          (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)).range := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hker] at hx
      obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      refine ⟨u, ?_⟩
      change QuotientGroup.mk' (twistedE6Inn K σ') (compatDiagAutHom TwistTag.E6 K σ'.toRingHom u)
        = _
      have hy1 : QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')) y = 1 :=
        (QuotientGroup.eq_one_iff y).2 hy
      rw [← hyz, map_mul, hy1, one_mul]
    have hfinR : Finite ((QuotientGroup.mk' (twistedE6Inn K σ')).comp
        (compatDiagAutHom TwistTag.E6 K σ'.toRingHom)).range := inferInstance
    have hNfin : Finite ((Θ.ker).map (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) :=
      Finite.of_injective (Subgroup.inclusion hN1) (Subgroup.inclusion_injective hN1)
    have hNle : Nat.card ((Θ.ker).map (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) ≤ 3 :=
      (Subgroup.card_le_of_le hN1).trans (hψ.trans (Nat.gcd_le_left _ (by norm_num)))
    have hcyc : IsCyclic ((Θ.ker).map (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) := by
      have hpos : 0 < Nat.card ((Θ.ker).map
          (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) := Nat.card_pos
      interval_cases hc : Nat.card ((Θ.ker).map
          (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ'))))
      · have : Subsingleton ((Θ.ker).map
            (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) :=
          Finite.card_le_one_iff_subsingleton.1 (le_of_eq hc)
        exact isCyclic_of_subsingleton
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card hc
      · have : Fact (Nat.Prime 3) := ⟨hp⟩
        exact isCyclic_of_prime_card hc
    refine outPChain_of_cyclic_subgroup hp
      ((Θ.ker).map (QuotientGroup.mk' (Inn (twistedE6RootGroup K σ')))) ?_
    intro x ⟨k, hk⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    have hαk : α ^ (3 ^ k) ∈ Inn (twistedE6RootGroup K σ') := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hk
    have hΘk : (Θ α) ^ (3 ^ k) = 1 := by
      rw [← map_pow]; exact hinner hαk
    have h1 : Θ α = 1 := eq_one_of_pElement_not_dvd_card hp
      (by rw [hring.1]; omega) _ ⟨k, hΘk⟩
    exact ⟨α, (MonoidHom.mem_ker).2 h1, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
