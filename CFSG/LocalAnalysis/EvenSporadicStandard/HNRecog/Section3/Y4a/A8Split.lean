module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

private theorem y4aA8Split_commutator_prod_eq :
    _root_.commutator (Elem2 2 × alternatingGroup (Fin 8)) =
      (⊥ : Subgroup (Elem2 2)).prod ⊤ := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_prod]
    refine ⟨?_, Subgroup.mem_top _⟩
    have hxy : ⁅x, y⁆ = (⁅x.1, y.1⁆, ⁅x.2, y.2⁆) := by
      ext <;> simp [commutatorElement_def]
    rw [hxy]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all x.1 y.1)
  · have hcommB : _root_.commutator (alternatingGroup (Fin 8)) = ⊤ :=
      commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; norm_num)
    have hran : (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range =
        (⊥ : Subgroup (Elem2 2)).prod ⊤ := by
      ext p; constructor
      · rintro ⟨b, rfl⟩
        exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
      · rintro ⟨hp1, -⟩
        exact ⟨p.2, by ext <;> simp [Subgroup.mem_bot.mp hp1]⟩
    rw [← hran]
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨b, rfl⟩ := hx
    have hb : b ∈ _root_.commutator (alternatingGroup (Fin 8)) := by rw [hcommB]; trivial
    have hmapcomm : (_root_.commutator (alternatingGroup (Fin 8))).map
        (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) =
        ⁅(MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range,
          (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))).range⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top]
    have hmem : MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8)) b ∈
        (_root_.commutator (alternatingGroup (Fin 8))).map
          (MonoidHom.inr (Elem2 2) (alternatingGroup (Fin 8))) :=
      Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    rw [hmapcomm] at hmem
    exact Subgroup.commutator_mono le_top le_top hmem

private theorem y4aA8Split_natCard_elem2_two : Nat.card (Elem2 2) = 4 := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

private theorem y4aA8Split_mem_derivedOf_iff {G : Type} [Group G] {H : Subgroup G}
    (e : ↥H ≃* Elem2 2 × alternatingGroup (Fin 8)) (h : ↥H) :
    (h : G) ∈ derivedOf H ↔ (e h).1 = 1 := by
  have hmap : (_root_.commutator ↥H).map e.toMonoidHom =
      _root_.commutator (Elem2 2 × alternatingGroup (Fin 8)) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [mem_derivedOf_iff]
  constructor
  · rintro ⟨h₁, hh⟩
    have hmem : e h ∈ (_root_.commutator ↥H).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    rw [hmap, y4aA8Split_commutator_prod_eq, Subgroup.mem_prod] at hmem
    exact Subgroup.mem_bot.mp hmem.1
  · intro hh
    refine ⟨h.2, ?_⟩
    have hmem : e h ∈ _root_.commutator (Elem2 2 × alternatingGroup (Fin 8)) := by
      rw [y4aA8Split_commutator_prod_eq, Subgroup.mem_prod]
      exact ⟨Subgroup.mem_bot.mpr hh, Subgroup.mem_top _⟩
    rw [← hmap] at hmem
    obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hmem
    have hk' : h ∈ _root_.commutator ↥H := by
      rw [← e.injective hk_eq]; exact hk
    exact hk'

private theorem y4aA8Split_mem_Gx_iff {G : Type} [Group G] {H : Subgroup G}
    (e : ↥H ≃* Elem2 2 × alternatingGroup (Fin 8)) {t : G} (htH : t ∈ H)
    {s : alternatingGroup (Fin 8)} (het : e ⟨t, htH⟩ = (1, s)) (h : ↥H) :
    (h : G) ∈ Gx t ↔ (e h).2 ∈ Gx s := by
  simp only [mem_Gx]
  have h1 : (t * (h : G) = (h : G) * t) ↔
      e (⟨t, htH⟩ * h) = e (h * ⟨t, htH⟩) := by
    constructor
    · intro hh
      have hh' : (⟨t, htH⟩ : ↥H) * h = h * ⟨t, htH⟩ := Subtype.ext (by simpa using hh)
      rw [hh']
    · intro hh
      simpa using congrArg Subtype.val (e.injective hh)
  rw [h1]
  constructor
  · intro hh
    simp only [map_mul, het] at hh
    simpa using congrArg Prod.snd hh
  · intro hh
    simp only [map_mul, het]
    exact Prod.ext (by simp) hh

theorem y4a_card_inf_Gx_eq {G : Type} [Group G] {H : Subgroup G}
    (hH : IsShapeTwoTwoTimesA8 ↥H) {t : G} (ht : t ∈ derivedOf H) :
    Nat.card ↥(H ⊓ Gx t) = 4 * Nat.card ↥(derivedOf H ⊓ Gx t) := by
  classical
  obtain ⟨e⟩ := hH
  have htH : t ∈ H := derivedOf_le H ht
  have het1 : (e ⟨t, htH⟩).1 = 1 := (y4aA8Split_mem_derivedOf_iff e ⟨t, htH⟩).mp ht
  let s : alternatingGroup (Fin 8) := (e ⟨t, htH⟩).2
  have hs : e ⟨t, htH⟩ = (1, s) := Prod.ext het1 rfl
  have hL1 : ((H ⊓ Gx t).subgroupOf H).map e.toMonoidHom =
      (⊤ : Subgroup (Elem2 2)).prod (Gx s) := by
    ext p
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩
      exact (y4aA8Split_mem_Gx_iff e htH hs h).mp (Subgroup.mem_subgroupOf.mp hh).2
    · intro hp
      rw [Subgroup.mem_prod] at hp
      obtain ⟨h, rfl⟩ := e.surjective p
      refine Subgroup.mem_map.mpr ⟨h, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        ⟨h.2, (y4aA8Split_mem_Gx_iff e htH hs h).mpr hp.2⟩
  have hL2 : ((derivedOf H ⊓ Gx t).subgroupOf H).map e.toMonoidHom =
      (⊥ : Subgroup (Elem2 2)).prod (Gx s) := by
    ext p
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨hh1, hh2⟩ := Subgroup.mem_subgroupOf.mp hh
      refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr ?_, ?_⟩
      · exact (y4aA8Split_mem_derivedOf_iff e h).mp hh1
      · exact (y4aA8Split_mem_Gx_iff e htH hs h).mp hh2
    · intro hp
      rw [Subgroup.mem_prod] at hp
      obtain ⟨h, rfl⟩ := e.surjective p
      refine Subgroup.mem_map.mpr ⟨h, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        ⟨(y4aA8Split_mem_derivedOf_iff e h).mpr (Subgroup.mem_bot.mp hp.1),
          (y4aA8Split_mem_Gx_iff e htH hs h).mpr hp.2⟩
  have hcard1 : Nat.card ↥(H ⊓ Gx t) = Nat.card ↥((⊤ : Subgroup (Elem2 2)).prod (Gx s)) :=
    calc Nat.card ↥(H ⊓ Gx t)
        = Nat.card ↥((H ⊓ Gx t).subgroupOf H) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      _ = Nat.card ↥(((H ⊓ Gx t).subgroupOf H).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective (K := (H ⊓ Gx t).subgroupOf H) e.injective).symm
      _ = Nat.card ↥((⊤ : Subgroup (Elem2 2)).prod (Gx s)) := by rw [hL1]
  have hcard2 : Nat.card ↥(derivedOf H ⊓ Gx t) = Nat.card ↥((⊥ : Subgroup (Elem2 2)).prod (Gx s)) :=
    calc Nat.card ↥(derivedOf H ⊓ Gx t)
        = Nat.card ↥((derivedOf H ⊓ Gx t).subgroupOf H) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (inf_le_left.trans (derivedOf_le H))).toEquiv).symm
      _ = Nat.card ↥(((derivedOf H ⊓ Gx t).subgroupOf H).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective
            (K := (derivedOf H ⊓ Gx t).subgroupOf H) e.injective).symm
      _ = Nat.card ↥((⊥ : Subgroup (Elem2 2)).prod (Gx s)) := by rw [hL2]
  rw [hcard1, hcard2,
    Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup (Elem2 2)) (Gx s)).toEquiv,
    Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup (Elem2 2)) (Gx s)).toEquiv]
  simp only [Nat.card_prod, Subgroup.card_top, Subgroup.card_bot,
    y4aA8Split_natCard_elem2_two]
  ring

theorem y4a_card_inf_Gx_of_mulEquiv {G A : Type} [Group G] [Group A] {K : Subgroup G}
    (φ : A ≃* ↥K) (s : A) : Nat.card ↥(K ⊓ Gx (φ s : G)) = Nat.card ↥(Gx s) := by
  let f : A →* G := K.subtype.comp φ.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp φ.injective
  have htop : (⊤ : Subgroup A).map f = K := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      simpa [f] using (φ a).2
    · intro hx
      refine Subgroup.mem_map.mpr ⟨φ.symm ⟨x, hx⟩, Subgroup.mem_top _, ?_⟩
      simp [f]
  have hmap : K ⊓ Gx (φ s : G) = (Gx s).map f := by
    have h := map_inf_Gx_of_injective hf (⊤ : Subgroup A) s
    rw [htop, top_inf_eq] at h
    simpa [f] using h
  rw [hmap, Subgroup.card_map_of_injective hf]

end CFSG.EvenSporadicStandard.HNRecog.Section3
