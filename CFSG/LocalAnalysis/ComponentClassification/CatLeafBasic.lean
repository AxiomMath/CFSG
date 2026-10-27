module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

@[expose] def ProperFixedComponent {S : Type*} [Group S] (σ : MulAut S) (P : Subgroup S) : Prop :=
  (∀ y, σ (σ y) = y) ∧ P ≤ fixedSubgroup σ ∧ IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) ∧
    P ≠ ⊤

variable {S T : Type*} [Group S] [Group T]

theorem subgroupOf_map_fixedSubgroupCongr (e : S ≃* T) (σ : MulAut S) (P : Subgroup S) :
    (P.subgroupOf (fixedSubgroup σ)).map (Sporadic.HeldB.fixedSubgroupCongr e σ).toMonoidHom =
      (P.map e.toMonoidHom).subgroupOf (fixedSubgroup (MulAut.congr e σ)) := by
  ext y
  obtain ⟨x, rfl⟩ := (Sporadic.HeldB.fixedSubgroupCongr e σ).surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_subgroupOf, mem_subgroupOf]
  change (x : S) ∈ P ↔ e (x : S) ∈ P.map e.toMonoidHom
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]

theorem ProperFixedComponent.map [Finite S] [Finite T] (e : S ≃* T) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ProperFixedComponent (MulAut.congr e σ) (P.map e.toMonoidHom) ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃*
        (P.map e.toMonoidHom) ⧸ Open.fusionZStar (P.map e.toMonoidHom)) := by
  obtain ⟨hσ, hPF, hP, hPne⟩ := h
  refine ⟨⟨fun y => ?_, ?_, ?_, ?_⟩, GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective e.toMonoidHom e.injective)⟩
  · change e (σ (e.symm (e (σ (e.symm y))))) = y
    rw [MulEquiv.symm_apply_apply, hσ, MulEquiv.apply_symm_apply]
  · rw [← Sporadic.HeldB.fixedSubgroup_map_congr]
    exact map_mono hPF
  · rw [← subgroupOf_map_fixedSubgroupCongr]
    exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 _ hP
  · intro htop
    apply hPne
    have h1 : (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
      rw [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S from by
        ext; simp, map_id]
    rw [← h1, htop, map_top_of_surjective _ e.symm.surjective]

theorem ProperFixedComponent.ne_one [Finite S] [IsSimpleGroup S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) : σ ≠ 1 := by
  obtain ⟨-, -, hP, hPne⟩ := h
  rintro rfl
  have hFtop : fixedSubgroup (1 : MulAut S) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rfl
  have : IsSimpleGroup (fixedSubgroup (1 : MulAut S)) :=
    ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
  have h := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
  apply hPne
  rw [eq_top_iff]
  intro x _
  have hx : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup (1 : MulAut S)) ∈
      P.subgroupOf (fixedSubgroup (1 : MulAut S)) := h ▸ mem_top _
  exact hx

theorem center_eq_bot_of_simple [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x) :
    center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (mem_center_iff.mp (hc ▸ mem_top y) x)

theorem mulAut_conj_injective_of_simple [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ center S := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [center_eq_bot_of_simple hnab, mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem generalizedFitting_mulAut_eq_range {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) :
    CFSG.generalizedFitting (MulAut S) = (MulAut.conj : S →* MulAut S).range := by
  have hκ := mulAut_conj_injective_of_simple hna
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  let e : S ≃* Inn := MonoidHom.ofInjective hκ
  have : Inn.Normal := OuterAutomorphisms.inner_normal S
  have : IsSimpleGroup Inn := e.symm.isSimpleGroup
  have hnc : ∃ x y : Inn, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hC : centralizer (Inn : Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [mem_bot]
    ext s
    have h := mem_centralizer_iff.mp hσ (MulAut.conj s) ⟨s, rfl⟩
    have h' : MulAut.conj (σ s) = MulAut.conj s := by
      apply MulEquiv.ext
      intro y
      have h2 := congrArg (fun φ : MulAut S => φ (σ.symm y)) h
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h2
      rw [MulAut.conj_apply, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    exact hκ h'
  exact Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
    Inn hnc hC

theorem ProperFixedComponent.inner [Finite S] [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) {t : S}
    (ht : σ = MulAut.conj t) :
    orderOf t = 2 ∧ P ≤ centralizer ({t} : Set S) ∧
      IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set S))) ∧ P ≠ ⊤ := by
  have hσ1 := h.ne_one
  obtain ⟨hσ, hPF, hP, hPne⟩ := h
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [ht]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hinj := mulAut_conj_injective_of_simple hnab
  have ht2 : t ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← ht]
    ext y
    rw [pow_two, MulAut.mul_apply, hσ, MulAut.one_apply]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hσ1
    rw [ht, map_one]
  refine ⟨orderOf_eq_prime ht2 ht1, hfix ▸ hPF, ?_, hPne⟩
  rw [← hfix]
  exact hP

theorem card_dvd_of_fusionZStar_equiv [Finite S] {X : Type*} {P : Subgroup S}
    (e : P ⧸ Open.fusionZStar P ≃ X) : Nat.card X ∣ Nat.card S := by
  rw [← Nat.card_congr e]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card P)

theorem exists_conj_or_not_mem_range (σ : MulAut S) :
    (∃ t : S, σ = MulAut.conj t) ∨ σ ∉ (MulAut.conj : S →* MulAut S).range := by
  by_cases h : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨t, ht⟩ := h
    exact Or.inl ⟨t, ht.symm⟩
  · exact Or.inr h

theorem fusionZStar_eq_center_of_quasisimple {L : Type*} [Group L] (hq : IsQuasisimple L)
    (hO : pPrimeCore 2 L ≠ ⊤) : Open.fusionZStar L = center L := by
  have hOc : pPrimeCore 2 L ≤ center L :=
    (LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq inferInstance).resolve_left hO
  obtain ⟨-, hs, hnab⟩ := hq
  have hZ : center (L ⧸ center L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (L ⧸ center L)) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (mem_center_iff.mp (hc ▸ mem_top y) x)
  ext x
  rw [GSThmB.OddQuot.mem_fusionZStar_iff]
  constructor
  · intro hx
    have hxZ : QuotientGroup.mk' (center L) x ∈ center (L ⧸ center L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center L) g
      have h1 : ⁅x, m⁆ ∈ center L := hOc (hx m)
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxZ
    exact hxZ
  · intro hx m
    have h1 : ⁅x, m⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hx m).symm
    rw [h1]
    exact one_mem _

theorem pPrimeCore_ne_top_of_isPComponent {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsPComponent 2 L) : pPrimeCore 2 L ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).mp hL
  obtain ⟨-, hs, -⟩ := hq
  have : Nontrivial ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)) := hs.toNontrivial
  have : Subsingleton (L ⧸ pPrimeCore 2 L) := QuotientGroup.subsingleton_iff.mpr htop
  obtain ⟨a, b, hab⟩ := exists_pair_ne ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  exact hab (by rw [Subsingleton.elim a' b'])

theorem ProperFixedComponent.fusionZStar_equiv_of_quasisimple [Finite S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ))) :
    IsComponent (P.subgroupOf (fixedSubgroup σ)) ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃* (P.subgroupOf (fixedSubgroup σ)) ⧸
        center (P.subgroupOf (fixedSubgroup σ))) := by
  obtain ⟨-, hPF, hP, -⟩ := h
  have hZ := fusionZStar_eq_center_of_quasisimple hq (pPrimeCore_ne_top_of_isPComponent hP)
  obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  exact ⟨⟨hq, hP.choose_spec.2.1⟩, ⟨eP.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩

end CFSG.ComponentClassification.CatLeaf
