module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsMain

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

theorem ThLocalIn.exists_conj_le_S (W : ThLocalIn L S A B z) {Y : Subgroup G} (hYL : Y ≤ L)
    (hY : IsPGroup 2 Y) : ∃ l ∈ L, ∀ y ∈ Y, l⁻¹ * y * l ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.comap L.subtype) := W.pgroup.comap_subtype
  have hY' : IsPGroup 2 (Y.comap L.subtype) := hY.comap_subtype
  let Ssyl : Sylow 2 ↥L := ⟨S.comap L.subtype, hS', fun {Q} hQ hle => by
    refine le_antisymm (fun q hq => ?_) hle
    have hmax := W.maximal (Q.map L.subtype) (Subgroup.map_subtype_le Q) (hQ.map _)
      (fun s hs => ⟨⟨s, W.S_le hs⟩, hle hs, rfl⟩)
    exact hmax ⟨q, hq, rfl⟩⟩
  obtain ⟨P, hYP⟩ := hY'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L Ssyl P
  refine ⟨(g : G), g.2, fun y hy => ?_⟩
  have h1 : (⟨y, hYL hy⟩ : ↥L) ∈ (P : Subgroup ↥L) := hYP hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : ((g⁻¹ * ⟨y, hYL hy⟩ * g : ↥L) : G) ∈ S := h1
  simpa using h2

namespace SylowBounds

omit [Finite G] in
theorem card_map_conj (g : G) (Y : Subgroup G) :
    Nat.card (Y.map (MulAut.conj g).toMonoidHom) = Nat.card Y :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end SylowBounds

theorem ThLocalIn.card_le_of_abelian (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hT : TransvCent L A B Aa) {Y : Subgroup G} (hYL : Y ≤ L) (hY : IsPGroup 2 Y)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : Nat.card Y ≤ 2 ^ 8 := by
  obtain ⟨l, -, hlY⟩ := W.exists_conj_le_S hYL hY
  have hS : Y.map (MulAut.conj l⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hlY y hy
  have hc : ∀ x ∈ Y.map (MulAut.conj l⁻¹).toMonoidHom, ∀ y ∈ Y.map (MulAut.conj l⁻¹).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  rw [← SylowBounds.card_map_conj l⁻¹ Y]
  exact W.card_le_of_abelian_le_S W2 hT hS hc

theorem ThLocalIn.card_le_of_elementary (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {Y : Subgroup G} (hYL : Y ≤ L) (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hsq : ∀ y ∈ Y, y ^ 2 = 1) : Nat.card Y ≤ 2 ^ 7 := by
  have hY : IsPGroup 2 Y := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hsq g g.2)⟩
  obtain ⟨l, -, hlY⟩ := W.exists_conj_le_S hYL hY
  have hS : Y.map (MulAut.conj l⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hlY y hy
  have hc : ∀ x ∈ Y.map (MulAut.conj l⁻¹).toMonoidHom, ∀ y ∈ Y.map (MulAut.conj l⁻¹).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hsq' : ∀ y ∈ Y.map (MulAut.conj l⁻¹).toMonoidHom, y ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hsq y hy, map_one]
  rw [← SylowBounds.card_map_conj l⁻¹ Y]
  exact W.card_le_of_elementary_le_S W2 hS hc hsq'

namespace SylowBounds

omit [Finite G] in
theorem map_conj_le_of_le_map {L Y : Subgroup G} (g : G)
    (hY : Y ≤ L.map (MulAut.conj g).toMonoidHom) : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨l, hl, hly⟩ := hY hy
  have : (MulAut.conj g⁻¹).toMonoidHom y = l := by
    rw [← hly]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    group
  rw [this]
  exact hl

end SylowBounds

theorem ThLocalIn.card_le_of_abelian_conj (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hT : TransvCent L A B Aa) (g : G) {Y : Subgroup G}
    (hY : Y ≤ L.map (MulAut.conj g).toMonoidHom) (hp : IsPGroup 2 Y)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : Nat.card Y ≤ 2 ^ 8 := by
  have hL := SylowBounds.map_conj_le_of_le_map g hY
  have hp' : IsPGroup 2 (Y.map (MulAut.conj g⁻¹).toMonoidHom) := hp.map _
  have hc : ∀ x ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  rw [← SylowBounds.card_map_conj g⁻¹ Y]
  exact W.card_le_of_abelian W2 hT hL hp' hc

theorem ThLocalIn.card_le_of_elementary_conj (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (g : G) {Y : Subgroup G} (hY : Y ≤ L.map (MulAut.conj g).toMonoidHom)
    (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hsq : ∀ y ∈ Y, y ^ 2 = 1) :
    Nat.card Y ≤ 2 ^ 7 := by
  have hL := SylowBounds.map_conj_le_of_le_map g hY
  have hc : ∀ x ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hsq' : ∀ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom, y ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hsq y hy, map_one]
  rw [← SylowBounds.card_map_conj g⁻¹ Y]
  exact W.card_le_of_elementary W2 hL hc hsq'

theorem ThLocalIn.sylowBounds (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hT : TransvCent L A B Aa) :
    (∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8) ∧
    (∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7) :=
  ⟨fun g _ hY hp hcomm => W.card_le_of_abelian_conj W2 hT g hY hp hcomm,
    fun g _ hY hcomm hsq => W.card_le_of_elementary_conj W2 g hY hcomm hsq⟩

end CFSG.EvenSporadicStandard.ThStd
