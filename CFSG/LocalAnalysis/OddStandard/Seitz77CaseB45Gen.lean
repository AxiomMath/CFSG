module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Model

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open

section Gen

variable {G : Type*} [Group G] {Q : Type} [Group Q] {N : Subgroup G} (θ : ↥N →* Wr Q)
  {T₀ : Subgroup G} (hTN : T₀ ≤ N)

@[expose] def restrT : ↥T₀ →* Wr Q := θ.comp (Subgroup.inclusion hTN)

theorem restrT_apply (y : ↥T₀) : restrT θ hTN y = θ ⟨y.1, hTN y.2⟩ := rfl

variable {θ hTN}

@[expose] def imgT (X : Subgroup G) : Subgroup (Wr Q) := (X.subgroupOf T₀).map (restrT θ hTN)

theorem mem_imgT_iff (hinj : Function.Injective (restrT θ hTN)) {X : Subgroup G} (y : ↥T₀) :
    restrT θ hTN y ∈ imgT (θ := θ) (hTN := hTN) X ↔ y.1 ∈ X := by
  unfold imgT
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have := hinj hzy
    rw [← this]
    exact Subgroup.mem_subgroupOf.1 hz
  · intro h
    exact ⟨y, Subgroup.mem_subgroupOf.2 h, rfl⟩

theorem imgT_mono (hinj : Function.Injective (restrT θ hTN)) {X Y : Subgroup G} (hX : X ≤ T₀)
    (h : imgT (θ := θ) (hTN := hTN) X ≤ imgT (θ := θ) (hTN := hTN) Y) : X ≤ Y := by
  intro x hx
  have hxT : x ∈ T₀ := hX hx
  have := h ((mem_imgT_iff hinj ⟨x, hxT⟩).2 hx)
  exact (mem_imgT_iff hinj ⟨x, hxT⟩).1 this

theorem natCard_imgT (hinj : Function.Injective (restrT θ hTN)) {X : Subgroup G} (hX : X ≤ T₀) :
    Nat.card (imgT (θ := θ) (hTN := hTN) X) = Nat.card X := by
  unfold imgT
  rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).symm.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

theorem isElemAbelian_imgT {X : Subgroup G} (hE : IsElemAbelian 2 X) :
    IsElemAbelian 2 (imgT (θ := θ) (hTN := hTN) X) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun w hw => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    have := hE.1.is_comm.comm ⟨a'.1, Subgroup.mem_subgroupOf.1 ha'⟩
      ⟨b'.1, Subgroup.mem_subgroupOf.1 hb'⟩
    have h2 : a'.1 * b'.1 = b'.1 * a'.1 := congrArg Subtype.val this
    exact Subtype.ext h2
  · obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    rw [← map_pow]
    have := hE.2 w'.1 (Subgroup.mem_subgroupOf.1 hw')
    have h1 : w' ^ 2 = 1 := Subtype.ext this
    rw [h1, map_one]

theorem imgT_le_range {X : Subgroup G} : imgT (θ := θ) (hTN := hTN) X ≤ (restrT θ hTN).range :=
  Subgroup.map_le_range _ _

theorem isPGroup_range (hT : IsPGroup 2 T₀) : IsPGroup 2 (restrT θ hTN).range := by
  intro y
  obtain ⟨z, hz⟩ := y.2
  obtain ⟨k, hk⟩ := hT z
  refine ⟨k, Subtype.ext ?_⟩
  simp only [OneMemClass.coe_one, Subgroup.coe_pow]
  rw [← hz, ← map_pow, hk, map_one]

theorem equiv_cent (hinj : Function.Injective (restrT θ hTN)) {y : G} (hy : y ∈ T₀) :
    Nonempty (↥(T₀ ⊓ centralizer {y}) ≃*
      ↥((restrT θ hTN).range ⊓ centralizer {restrT θ hTN ⟨y, hy⟩})) := by
  let yt : ↥T₀ := ⟨y, hy⟩
  have e1 : (T₀ ⊓ centralizer {y}).subgroupOf T₀ = centralizer {yt} := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨z.2, congrArg Subtype.val h⟩
  have e2 : (centralizer {yt}).map (restrT θ hTN) =
      (restrT θ hTN).range ⊓ centralizer {restrT θ hTN yt} := by
    ext w
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hz]
    · rintro ⟨⟨z, rfl⟩, hc⟩
      refine ⟨z, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), rfl⟩
      rw [map_mul, map_mul]
      exact hc
  exact ⟨((Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    (MulEquiv.subgroupCongr e1)).trans
    ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr e2))⟩

end Gen

section Main

variable {G : Type*} [Group G] {Q : Type} [Group Q] [Finite Q] (M : ModelData Q)
  {N : Subgroup G} {θ : ↥N →* Wr Q} {T₀ : Subgroup G} {hTN : T₀ ≤ N}

theorem gen_elem_le (hT : IsPGroup 2 T₀) (hinj : Function.Injective (restrT θ hTN))
    {S : Subgroup G} (hST : S ≤ T₀) (hS : imgT (θ := θ) (hTN := hTN) S ≤ Wr.ss M.Lm)
    (hcardS : Nat.card S = 2 ^ 12) {E : Subgroup G} (hET : E ≤ T₀) (hE : IsElemAbelian 2 E)
    (hcardE : Nat.card E = 2 ^ 8) : E ≤ S := by
  have h := M.elem_le (isPGroup_range hT) (imgT_le_range (θ := θ) (hTN := hTN)) hS
    (by rw [natCard_imgT hinj hST, hcardS]) (imgT_le_range (θ := θ) (hTN := hTN))
    (isElemAbelian_imgT hE) (by rw [natCard_imgT hinj hET, hcardE])
  exact imgT_mono hinj hET h

theorem gen_not_equiv (hT : IsPGroup 2 T₀) (hinj : Function.Injective (restrT θ hTN))
    {S : Subgroup G} (hST : S ≤ T₀) (hS : imgT (θ := θ) (hTN := hTN) S ≤ Wr.ss M.Lm)
    (hcardS : Nat.card S = 2 ^ 12) {τ x : G} (hτT : τ ∈ T₀) (hxT : x ∈ T₀)
    (hτe : (restrT θ hTN ⟨τ, hτT⟩).e = true) (hτ2 : τ * τ = 1)
    (hxe : (restrT θ hTN ⟨x, hxT⟩).e = false) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ Nonempty (↥(T₀ ⊓ centralizer {x}) ≃* ↥(T₀ ⊓ centralizer {τ})) := by
  rintro ⟨f⟩
  obtain ⟨ex⟩ := equiv_cent hinj hxT
  obtain ⟨eτ⟩ := equiv_cent hinj hτT
  have hSR : imgT (θ := θ) (hTN := hTN) S ≤ (restrT θ hTN).range := imgT_le_range
  refine M.not_equiv (isPGroup_range hT) hSR hS (by rw [natCard_imgT hinj hST, hcardS])
    (τ := restrT θ hTN ⟨τ, hτT⟩) (x := restrT θ hTN ⟨x, hxT⟩) ⟨_, rfl⟩ hτe ?_ ⟨_, rfl⟩ hxe ?_ ?_
    ⟨ex.symm.trans (f.trans eτ)⟩
  · rw [← map_mul]
    have : (⟨τ, hτT⟩ : ↥T₀) * ⟨τ, hτT⟩ = 1 := Subtype.ext hτ2
    rw [this, map_one]
  · rw [← map_mul]
    have : (⟨x, hxT⟩ : ↥T₀) * ⟨x, hxT⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  · intro h1
    apply hx1
    have := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this

end Main

end CFSG.OddStandard.Seitz77.CaseB45
