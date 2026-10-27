module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog82A10

open CFSG Subgroup Equiv Equiv.Perm CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedLayer

theorem conjNormal_injective_of_centralizer {H : Type} [Group H] (G : Subgroup H) [G.Normal]
    (hC : centralizer (G : Set H) = ⊥) :
    Function.Injective (MulAut.conjNormal : H →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  rw [← hC, mem_centralizer_iff]
  intro g hg
  have h1 := congrArg (fun φ : MulAut G => ((φ ⟨g, hg⟩ : G) : H)) (MonoidHom.mem_ker.mp ht)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc g * t = t * g * t⁻¹ * t := by rw [h1]
    _ = t * g := by group

theorem exists_perm_embedding {H : Type} [Group H] (G : Subgroup H) [G.Normal]
    (hC : centralizer (G : Set H) = ⊥) (e : G ≃* alternatingGroup (Fin 10)) :
    ∃ φ : H →* Perm (Fin 10), Function.Injective φ ∧ ∀ s : G, φ s = (e s : Perm (Fin 10)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  set ψ := MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)) :
    Perm (Fin 10) →* MulAut (alternatingGroup (Fin 10))) hbij
  refine ⟨ψ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal),
    ψ.symm.injective.comp ((MulAut.congr e).injective.comp
      (conjNormal_injective_of_centralizer G hC)), fun s => ?_⟩
  apply ψ.injective
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  have h1 : (MulAut.conjNormal (s : H) (e.symm a) : G) = s * e.symm a * s⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  change ((e (MulAut.conjNormal (s : H) (e.symm a)) : alternatingGroup (Fin 10)) :
    Perm (Fin 10)) = _
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp [ψ, MulAut.conjNormal_apply]

theorem alternating_le_range {H : Type} [Group H] (G : Subgroup H)
    (e : G ≃* alternatingGroup (Fin 10)) (φ : H →* Perm (Fin 10))
    (hφ : ∀ s : G, φ s = (e s : Perm (Fin 10))) : alternatingGroup (Fin 10) ≤ φ.range := by
  intro a ha
  refine ⟨(e.symm ⟨a, ha⟩ : H), ?_⟩
  rw [hφ, MulEquiv.apply_symm_apply]

theorem exists_conj_normal {H : Type} [Group H] (φ : H →* Perm (Fin 10))
    (hinj : Function.Injective φ) (hA : alternatingGroup (Fin 10) ≤ φ.range) {ι : H}
    {σ' : Perm (Fin 10)} (hc : IsConj (φ ι) σ') :
    ∃ φ' : H →* Perm (Fin 10), Function.Injective φ' ∧
      alternatingGroup (Fin 10) ≤ φ'.range ∧ φ' ι = σ' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hc
  refine ⟨(MulAut.conj τ).toMonoidHom.comp φ, (MulAut.conj τ).injective.comp hinj, ?_, ?_⟩
  · intro a ha
    have hmem : τ⁻¹ * a * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 10) :=
      (inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem a ha τ⁻¹
    obtain ⟨h, hh⟩ := hA hmem
    refine ⟨h, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh]
    group
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hτ

theorem ordA_one_two_mul {q : ℕ} (hq : Odd q) : Open.ordA 1 q * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  unfold Open.ordA
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, hg]
  apply Nat.div_mul_cancel
  have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    omega
  rw [h1]
  exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _

theorem sq_dvd_ordA {q : ℕ} (hq : Odd q) : q ^ 2 ∣ Open.ordA 1 (q ^ 2) := by
  have hq2 : Odd (q ^ 2) := hq.pow
  have h1 := ordA_one_two_mul hq2
  have hcop : Nat.Coprime (q ^ 2) 2 := Nat.coprime_two_right.mpr hq2
  exact hcop.dvd_of_dvd_mul_right ⟨_, h1⟩

theorem arith_sec8 {p f m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm1 : 1 ≤ m)
    (hm5 : m ≤ 5)
    (hdvd : Open.ordA 1 (p ^ (2 * f)) ∣ (10 - 2 * m).factorial * 2 ^ m * m.factorial) :
    p = 3 ∧ f = 1 ∧ m ≤ 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ f := ⟨_, rfl⟩
  have hqodd : Odd q := hq ▸ (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ q := by
    rw [hq]
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact le_trans h3 (Nat.le_self_pow (by omega) p)
  have hpq : p ^ (2 * f) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  rw [hpq] at hdvd
  have hsq := (sq_dvd_ordA hqodd).trans hdvd
  have hcop : ∀ a, Nat.Coprime (q ^ 2) (2 ^ a) := fun a =>
    Nat.Coprime.pow _ _ (Nat.coprime_two_right.mpr hqodd)
  have key : q = 3 → p = 3 ∧ f = 1 := fun h => Nat.prime_three.pow_eq_iff.mp (h ▸ hq).symm
  have hdiv : ∀ {M a : ℕ}, (10 - 2 * m).factorial * 2 ^ m * m.factorial = M * 2 ^ a →
      q ^ 2 ∣ M := fun hN => (hcop _).dvd_of_dvd_mul_right (hN ▸ hsq)
  have hbound : ∀ {M : ℕ}, 0 < M → M ≤ 315 → q ^ 2 ∣ M → q ≤ 17 := fun hM hM' h => by
    have := Nat.le_of_dvd hM h
    nlinarith
  interval_cases m
  · have h1 : q ^ 2 ∣ 315 := hdiv (a := 8) (by decide)
    have := hbound (by norm_num) le_rfl h1
    interval_cases q <;> first | exact ⟨(key rfl).1, (key rfl).2, by norm_num⟩ | (norm_num at h1)
  · have h1 : q ^ 2 ∣ 45 := hdiv (a := 7) (by decide)
    have := hbound (by norm_num) (by norm_num) h1
    interval_cases q <;> first | exact ⟨(key rfl).1, (key rfl).2, by norm_num⟩ | (norm_num at h1)
  · have h1 : q ^ 2 ∣ 9 := hdiv (a := 7) (by decide)
    have := hbound (by norm_num) (by norm_num) h1
    interval_cases q <;> norm_num at h1
    exfalso
    revert hdvd
    decide
  · have h1 : q ^ 2 ∣ 3 := hdiv (a := 8) (by decide)
    have := hbound (by norm_num) (by norm_num) h1
    interval_cases q <;> norm_num at h1
  · have h1 : q ^ 2 ∣ 15 := hdiv (a := 8) (by decide)
    have := hbound (by norm_num) (by norm_num) h1
    interval_cases q <;> norm_num at h1

theorem ne_bot_of_isPComp {X : Type*} [Group X] {L : Subgroup X} (hL : IsPComponent 2 L) :
    L ≠ ⊥ := by
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  intro h
  rw [h, Subgroup.map_bot] at hLK
  subst hLK
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have : a = b := Subsingleton.elim _ _
  rw [this]

theorem map_eq_altOn {H : Type} [Group H] [Finite H] (φ : H →* Perm (Fin 10))
    (hinj : Function.Injective φ) (hA : alternatingGroup (Fin 10) ≤ φ.range) (ι : H)
    (J : Subgroup H) (hJC : J ≤ centralizer ({ι} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({ι} : Set H))))
    (hS : (φ ι).support.card ≤ 4) : J.map φ = altOn (φ ι).supportᶜ := by
  classical
  set C := centralizer ({ι} : Set H)
  set T := (φ ι).supportᶜ
  have hT : 6 ≤ T.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hJperf : ⁅J, J⁆ = J := by
    have hP : Group.IsPerfect (J.subgroupOf C) := CatalogueBAlternating.pComponent_perfect hJ
    have : Group.IsPerfect J := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hJC).toMonoidHom) (subgroupOfEquivOfLe hJC).surjective
    exact Subgroup.isPerfect_iff.mp this
  have hmapperf : ⁅J.map φ, J.map φ⁆ = J.map φ := by rw [← Subgroup.map_commutator, hJperf]
  have hpres : ∀ g ∈ J.map φ, ∀ x, g x ∈ (φ ι).support ↔ x ∈ (φ ι).support := by
    rintro _ ⟨j, hj, rfl⟩ x
    apply mem_support_iff_of_commute
    have hjc : ι * j = j * ι := mem_centralizer_iff.mp (hJC hj) ι rfl
    rw [← map_mul, ← map_mul, hjc]
  have hfix := perfect_fix_small (J.map φ) hmapperf (φ ι).support hS hpres
  have halt := perfect_le_alternating (J.map φ) hmapperf
  have hle : J.map φ ≤ altOn T := by
    intro g hg
    refine mem_altOn.mpr ⟨halt hg, fun x hx => ?_⟩
    rw [Finset.mem_compl]
    intro hxσ
    exact (Equiv.Perm.mem_support.mp hx) (hfix g hg x hxσ)
  set N := (altOn T).comap φ
  have hJN : J ≤ N := Subgroup.map_le_iff_le_comap.mp hle
  have hNC : N ≤ C := by
    intro n hn
    rw [mem_centralizer_iff]
    rintro _ rfl
    apply hinj
    rw [map_mul, map_mul]
    exact (commute_of_support_subset_compl (mem_altOn.mp hn).2).symm
  have hNmap : N.map φ = altOn T := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (fun g hg => hA (mem_altOn.mp hg).1)
  have hNsimple : IsSimpleGroup N := by
    have := isSimpleGroup_altOn T (by omega)
    exact ((N.equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr hNmap)).isSimpleGroup
  have hsub : (J.subgroupOf C).IsSubnormal := hJ.choose_spec.2.1
  have hsubN : (J.subgroupOf N).IsSubnormal := by
    have h1 := hsub.comap (Subgroup.inclusion hNC)
    have h2 : (J.subgroupOf C).comap (Subgroup.inclusion hNC) = J.subgroupOf N := by
      ext x
      simp [mem_subgroupOf]
    rwa [h2] at h1
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hNsimple hsubN with h | h
  · exfalso
    apply ne_bot_of_isPComp hJ
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x.val, hJN (mem_subgroupOf.mp hx)⟩ : N) ∈ J.subgroupOf N :=
      mem_subgroupOf.mpr (mem_subgroupOf.mp hx)
    rw [h, mem_bot] at h1
    rw [mem_bot]
    have h2 : (x : H) = 1 := congrArg (fun y : N => (y : H)) h1
    exact Subtype.ext h2
  · have hNJ : N ≤ J := by
      intro n hn
      have : (⟨n, hn⟩ : N) ∈ J.subgroupOf N := h ▸ mem_top _
      exact this
    rw [← hNmap, le_antisymm hJN hNJ]

theorem lieModel_of_equiv_psl {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Blueprint.LieModel X .PSL 2 p e := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)

theorem lieModel_alternatingGroup_six :
    Blueprint.LieModel (alternatingGroup (Fin 6)) .PSL 2 3 2 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  obtain ⟨E⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) (by rw [Fintype.card_eq_nat_card, hcard]; norm_num)
  exact lieModel_of_equiv_psl Nat.prime_three (by norm_num) hcard (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num) E.symm

end CFSG.ComponentClassification.GSThmB.Catalog82A10
