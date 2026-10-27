module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseI
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Class

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section Solv

variable {G : Type} [Group G] [Finite G]

theorem l31_solvable_of_hasNormal2Compl {X : Subgroup G} (h : HasNormal2Compl X) :
    Group.IsSolvable ↥X := by
  obtain ⟨N, hNX, hNn, hNodd, a, ha⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNsol : Group.IsSolvable ↥(N.subgroupOf X) := by
    have hcard : Nat.card ↥(N.subgroupOf X) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rw [hcard]; exact hNodd)
  have hQ : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
    rw [IsPGroup.iff_card]
    refine ⟨a, ?_⟩
    rw [← Subgroup.index_eq_card]
    exact ha
  have hQsol : Group.IsSolvable (↥X ⧸ N.subgroupOf X) := by
    have := hQ.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf X).subtype
    (QuotientGroup.mk' (N.subgroupOf X)) (by simp)


theorem l31_solvable_pPrimePCore (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable ↥(pPrimePCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup X := pPrimePCore 2 X
  let N : Subgroup X := pPrimeCore 2 X
  let g : ↥P →* ↥(pCore 2 (X ⧸ N)) :=
    ((QuotientGroup.mk' N).comp P.subtype).codRestrict (pCore 2 (X ⧸ N)) fun x => x.2
  have hNP : N ≤ P := by
    intro n hn
    show QuotientGroup.mk' N n ∈ pCore 2 (X ⧸ N)
    have h : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [h]
    exact one_mem _
  have hNsol : Group.IsSolvable ↥(N.subgroupOf P) := by
    have hcard : Nat.card ↥(N.subgroupOf P) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by
      rw [hcard]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hQsol : Group.IsSolvable ↥(pCore 2 (X ⧸ N)) := by
    have := (pCore_isPGroup (p := 2) (G := X ⧸ N)).isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf P).subtype g ?_
  intro x hx
  have h1 : QuotientGroup.mk' N (x : X) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
  exact ⟨⟨x, (QuotientGroup.eq_one_iff (x : X)).mp h1⟩, rfl⟩

theorem l31_solvable_of_pPrimePCore_quotient (X : Type*) [Group X] [Finite X]
    (h : Group.IsSolvable (X ⧸ pPrimePCore 2 X)) : Group.IsSolvable X := by
  have := l31_solvable_pPrimePCore X
  exact Group.isSolvable_of_ker_le_range (pPrimePCore 2 X).subtype
    (QuotientGroup.mk' (pPrimePCore 2 X)) (by simp)

theorem l31_solvable_of_lemma29b {U : Subgroup G} (h : Lemma29b U) :
    Group.IsSolvable ↥(centralizer (U : Set G)) := by
  obtain ⟨Q, Xg, v, -, -, -, -, -, -, -, -, hq⟩ := h
  have hP : ((O22Of (centralizer (U : Set G))).subgroupOf (centralizer (U : Set G))) =
      pPrimePCore 2 ↥(centralizer (U : Set G)) :=
    Subgroup.comap_map_eq_self_of_injective (centralizer (U : Set G)).subtype_injective _
  apply l31_solvable_of_pPrimePCore_quotient
  rcases hq with ⟨hn, ⟨e⟩⟩ | ⟨hn, ⟨e⟩⟩
  · have : Group.IsSolvable (Multiplicative (ZMod 3)) := inferInstance
    have e2 := (QuotientGroup.quotientMulEquivOfEq hP.symm).trans e
    exact Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective
  · have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    have e2 := (QuotientGroup.quotientMulEquivOfEq hP.symm).trans e
    exact Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective

end Solv

section Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem l31_isCyclic_or_isQuat_of_no_four {R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (h : ¬ ∃ U : Subgroup G, U ≤ R ∧ IVK.IsFourSubgroup U) : IsCyclic ↥R ∨ IsQuat ↥R := by
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥R := by
    intro a b hab
    by_contra hne
    have ha2 : (a : ↥R) * a = 1 := by
      have := pow_orderOf_eq_one (a : ↥R)
      rwa [a.2, pow_two] at this
    have hb2 : (b : ↥R) * b = 1 := by
      have := pow_orderOf_eq_one (b : ↥R)
      rwa [b.2, pow_two] at this
    have ha1 : (a : ↥R) ≠ 1 := by
      intro h1
      have := a.2
      rw [h1, orderOf_one] at this
      omega
    have hb1 : (b : ↥R) ≠ 1 := by
      intro h1
      have := b.2
      rw [h1, orderOf_one] at this
      omega
    obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_involutions ha2 hb2 hab ha1 hb1
      (fun h => hne (Subtype.ext h))
    exact h ⟨V.map R.subtype, Subgroup.map_subtype_le V,
      hat_isFourSubgroup_map hV R.subtype R.subtype_injective⟩
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hR hrank with
    hc | ⟨e, he, ⟨φ⟩⟩
  · exact Or.inl hc
  · refine Or.inr ⟨e + 2, by omega, ⟨?_⟩⟩
    have : e + 2 - 2 = e := by omega
    rw [this]
    exact φ.symm

theorem l31_classical_of_four (h29 : Lemma29First) {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {J₀ U : Subgroup G} (hJ₀ : ¬ Group.IsSolvable ↥J₀)
    (hU : IVK.IsFourSubgroup U) (hJU : J₀ ≤ centralizer (U : Set G)) : IsClassicalKind k := by
  have hnonsolv : ¬ Group.IsSolvable ↥(centralizer (U : Set G)) := fun hs =>
    hJ₀ (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJU)
      (Subgroup.inclusion_injective hJU))
  rcases h29 G z k S hctx U hU with h | ⟨hk, -⟩ | ⟨-, hb⟩
  · exact absurd (l31_solvable_of_hasNormal2Compl h) hnonsolv
  · exact hk
  · exact absurd (l31_solvable_of_lemma29b hb) hnonsolv

theorem l31_exists_central_invol {R : Subgroup G} (hR : IsPGroup 2 ↥R) (h : R ≠ ⊥) :
    ∃ s ∈ R, orderOf s = 2 ∧ ∀ r ∈ R, r * s = s * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr h
  have hZn : Nontrivial ↥(Subgroup.center ↥R) := hR.center_nontrivial
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥R) := hR.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := (hZ.nontrivial_iff_card).mp hZn
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥R) := by
    rw [hn]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥R)) 2 hdvd
  refine ⟨((x : ↥R) : G), (x : ↥R).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  · intro r hr
    have := Subgroup.mem_center_iff.mp x.2 ⟨r, hr⟩
    exact congrArg Subtype.val this

end Dichotomy



section FourInvol

variable {G : Type} [Group G] [Finite G]

theorem l31_exists_invol_not_zpowers {s : G} (hs2 : orderOf s = 2) {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) : ∃ u ∈ U, u * u = 1 ∧ u ∉ zpowers s := by
  by_contra hcon
  push Not at hcon
  have hle : U ≤ zpowers s := fun u hu => hcon u hu (four_sq_eq_one hU hu)
  have h1 : Nat.card ↥U ≤ Nat.card ↥(zpowers s) := Subgroup.card_le_of_le hle
  have h2 : Nat.card ↥(zpowers s) ≤ 2 := by rw [Nat.card_zpowers, hs2]
  have := hU.2
  omega

end FourInvol

section Assemble

theorem l31_cd_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsCyclic B ∨ IsDihedral B) : IsCyclic A ∨ IsDihedral A := by
  rcases h with h | ⟨m, k, hm, hk, ⟨e'⟩⟩
  · have := h
    exact Or.inl (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · exact Or.inr ⟨m, k, hm, hk, ⟨e.trans e'⟩⟩

variable {G : Type} [Group G]

theorem l31_mem_conjMap_iff (c : G) (K : Subgroup G) (y : G) :
    y ∈ K.map (MulAut.conj c⁻¹).toMonoidHom ↔ ∃ x ∈ K, y = c⁻¹ * x * c := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩

theorem l31_a_central_of_conj {z : G}
    (hII : ∀ {R' J₀' : Subgroup G}, IsPGroup 2 ↥R' → z ∈ R' → (∀ r ∈ R', r * z = z * r) →
      (∃ v ∈ R', v * v = 1 ∧ v ∉ zpowers z) →
      (∀ x ∈ J₀', ∀ r ∈ R', x * r = r * x) → ¬ Group.IsSolvable ↥J₀' →
      IsCyclic ↥R' ∨ IsDihedral ↥R')
    {R J₀ : Subgroup G} {s : G} (hR : IsPGroup 2 ↥R) (hsR : s ∈ R) (hsZ : ∀ r ∈ R, r * s = s * r)
    (hrk : ∃ v ∈ R, v * v = 1 ∧ v ∉ zpowers s)
    (hcomm : ∀ x ∈ J₀, ∀ r ∈ R, x * r = r * x) (hJ₀ : ¬ Group.IsSolvable ↥J₀)
    (hconj : IsConj z s) : IsCyclic ↥R ∨ IsDihedral ↥R := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hzs : z = c⁻¹ * s * c := by rw [← hc]; group
  let R' : Subgroup G := R.map (MulAut.conj c⁻¹).toMonoidHom
  let J' : Subgroup G := J₀.map (MulAut.conj c⁻¹).toMonoidHom
  let eR : ↥R ≃* ↥R' := Subgroup.equivMapOfInjective R (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective
  let eJ : ↥J₀ ≃* ↥J' := Subgroup.equivMapOfInjective J₀ (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective
  have hzR' : z ∈ R' := (l31_mem_conjMap_iff c R z).mpr ⟨s, hsR, hzs⟩
  have hzZ' : ∀ r ∈ R', r * z = z * r := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := (l31_mem_conjMap_iff c R r).mp hr
    rw [hzs]
    calc c⁻¹ * x * c * (c⁻¹ * s * c) = c⁻¹ * (x * s) * c := by group
      _ = c⁻¹ * (s * x) * c := by rw [hsZ x hx]
      _ = c⁻¹ * s * c * (c⁻¹ * x * c) := by group
  have hcomm' : ∀ x ∈ J', ∀ r ∈ R', x * r = r * x := by
    intro x hx r hr
    obtain ⟨x₀, hx₀, rfl⟩ := (l31_mem_conjMap_iff c J₀ x).mp hx
    obtain ⟨r₀, hr₀, rfl⟩ := (l31_mem_conjMap_iff c R r).mp hr
    calc c⁻¹ * x₀ * c * (c⁻¹ * r₀ * c) = c⁻¹ * (x₀ * r₀) * c := by group
      _ = c⁻¹ * (r₀ * x₀) * c := by rw [hcomm x₀ hx₀ r₀ hr₀]
      _ = c⁻¹ * r₀ * c * (c⁻¹ * x₀ * c) := by group
  have hns' : ¬ Group.IsSolvable ↥J' := by
    intro hsol
    have := hsol
    exact hJ₀ (Group.isSolvable_of_isSolvable_injective (f := eJ.toMonoidHom) eJ.injective)
  have hrk' : ∃ v ∈ R', v * v = 1 ∧ v ∉ zpowers z := by
    obtain ⟨v, hvR, hv2, hvs⟩ := hrk
    refine ⟨c⁻¹ * v * c, (l31_mem_conjMap_iff c R _).mpr ⟨v, hvR, rfl⟩, ?_, ?_⟩
    · calc c⁻¹ * v * c * (c⁻¹ * v * c) = c⁻¹ * (v * v) * c := by group
        _ = 1 := by rw [hv2]; group
    · rintro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hvs
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h1 : z ^ n = c⁻¹ * s ^ n * c := by
        rw [hzs]
        have := conj_zpow (a := c⁻¹) (b := s) (i := n)
        simpa using this
      have h2 : c⁻¹ * s ^ n * c = c⁻¹ * v * c := by rw [← h1, hn]
      have := mul_right_cancel h2
      exact mul_left_cancel this
  exact l31_cd_of_equiv eR (hII (hR.of_equiv eR) hzR' hzZ' hrk' hcomm' hns')

end Assemble

section MainA

variable {G : Type} [Group G] [Finite G]

theorem l31_a_of_cases
    (h29 : Lemma29First) (hNCD : NonCentralDihedral) (hT1 : NonCentralT1)
    {z : G} {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S)
    (hII : IsClassicalKind k → ∀ {R' J₀' : Subgroup G}, IsPGroup 2 ↥R' → z ∈ R' →
      (∀ r ∈ R', r * z = z * r) → (∃ v ∈ R', v * v = 1 ∧ v ∉ zpowers z) →
      (∀ x ∈ J₀', ∀ r ∈ R', x * r = r * x) → ¬ Group.IsSolvable ↥J₀' →
      IsCyclic ↥R' ∨ IsDihedral ↥R')
    {H J R : Subgroup G} (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    (hR1 : R ≠ ⊥) : IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R := by
  classical
  obtain ⟨hpg, -, -, hcomm, hJ0J, hcov⟩ := l31_reduce hJ hR
  have hqJ : IsQuasisimple (Hat J) := TwoThin.isQuasisimple_hat hJ
  obtain ⟨e⟩ := hat_equiv_of_cover hJ0J hcov hqJ
  have hq0 : IsQuasisimple (↥(redJ0 J R) ⧸ pPrimeCore 2 ↥(redJ0 J R)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqJ
  have hns : ¬ Group.IsSolvable ↥(redJ0 J R) := hat_not_isSolvable_of_isQuasisimple hq0
  by_cases hfour : ∃ U : Subgroup G, U ≤ R ∧ IVK.IsFourSubgroup U
  · obtain ⟨U, hUR, hU⟩ := hfour
    have hk : IsClassicalKind k :=
      l31_classical_of_four h29 hctx hns hU (fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm x hx u (hUR hu)).symm)
    obtain ⟨s, hsR, hs2, hsZ⟩ := l31_exists_central_invol hpg hR1
    by_cases hsc : IsCentralInvolution s
    · obtain ⟨u, huU, hu2, hus⟩ := l31_exists_invol_not_zpowers hs2 hU
      rcases l31_a_central_of_conj (hII hk) hpg hsR hsZ ⟨u, hUR huU, hu2, hus⟩ hcomm hns
          (isConj_of_central hctx hsc) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · have hJ₀s : redJ0 J R ≤ O2Of (centralizer ({s} : Set G)) := by
        refine O2Of_mono fun x hx => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 s hsR).symm
      rcases l31_a_nonCentral hNCD hT1 hctx hk hpg ⟨hs2, hsc⟩ hsR hsZ hcomm hJ₀s hq0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · rcases l31_isCyclic_or_isQuat_of_no_four hpg hfour with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end MainA

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
