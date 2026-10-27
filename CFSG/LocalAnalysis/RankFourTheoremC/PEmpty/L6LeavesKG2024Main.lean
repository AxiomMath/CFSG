module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Perm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Subgroup CFSG.Open KG2024

namespace KG2024

theorem s622IsSimpleSection_of_map {Y A : Type} [Group Y] [Group A] (f : Y →* A)
    (hf : Function.Injective f) {L D : Subgroup Y}
    (h : S622IsSimpleSection (L.map f) (D.map f)) : S622IsSimpleSection L D := by
  obtain ⟨hDL, hDn, hDne, hmin, hnab⟩ := h
  have hDL' : D ≤ L := (Subgroup.map_le_map_iff_of_injective hf).1 hDL
  have hDn' := (Subgroup.normal_subgroupOf_iff hDL).1 hDn
  refine ⟨hDL', ?_, fun h => hDne (by rw [h]), ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hDL']
    intro d l hd hl
    obtain ⟨d', hd', hdd'⟩ := hDn' (f d) (f l) ⟨d, hd, rfl⟩ ⟨l, hl, rfl⟩
    have : d' = l * d * l⁻¹ := hf (by rw [hdd']; simp)
    rw [← this]
    exact hd'
  · intro N hDN hNL hNn
    have hmapDN : D.map f ≤ N.map f := Subgroup.map_mono hDN
    have hmapNL : N.map f ≤ L.map f := Subgroup.map_mono hNL
    have hNn' : ((N.map f).subgroupOf (L.map f)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hmapNL]
      rintro _ _ ⟨n, hn, rfl⟩ ⟨l, hl, rfl⟩
      have := (Subgroup.normal_subgroupOf_iff hNL).1 hNn n l hn hl
      exact ⟨l * n * l⁻¹, this, by simp⟩
    rcases hmin _ hmapDN hmapNL hNn' with h1 | h1
    · left
      exact Subgroup.map_injective hf h1
    · right
      exact Subgroup.map_injective hf h1
  · intro hall
    apply hnab
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹ * b⁻¹, hall a ha b hb, by simp⟩

theorem mem_normalizer_map {B A : Type*} [Group B] [Group A] (f : B →* A) {K : Subgroup B}
    {g : B} (hg : g ∈ normalizer (K : Set B)) :
    f g ∈ normalizer ((K.map f : Subgroup A) : Set A) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro a
  have hg' := Subgroup.mem_set_normalizer_iff.1 hg
  have hgi := Subgroup.mem_set_normalizer_iff''.1 hg
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g * k * g⁻¹, (hg' k).1 hk, by simp⟩
  · rintro ⟨k, hk, hka⟩
    refine ⟨g⁻¹ * k * g, (hgi k).1 hk, ?_⟩
    simp only [map_mul, map_inv, hka]
    group

end KG2024

theorem kg2024_of_hom {A : Type} [Group A] [Finite A] (X S : Subgroup A) (z : A) (n p : ℕ)
    (ψ : ↥X →* Equiv.Perm (Fin n)) (hψ : Function.Injective ψ)
    (halt : alternatingGroup (Fin n) ≤ ψ.range) (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n < 2 * p)
    (hz : orderOf z = p) (hzX : z ∈ X) (hSX : S ≤ X) (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) :
    ∃ T Y : Subgroup A, T ≤ S ∧ T ≠ ⊥ ∧ z ∈ normalizer (T : Set A) ∧
      S ≤ normalizer (T : Set A) ∧ Y ≤ normalizer (T : Set A) ⊓ X ∧ z ∈ Y ∧
      S622IsSimpleSection Y (rankThreePrimeCore p Y) ∧
      3 ∣ (rankThreePrimeCore p Y).relIndex Y := by
  set f : ↥X →* A := X.subtype with hfdef
  have hf : Function.Injective f := Subtype.val_injective
  set zx : ↥X := ⟨z, hzX⟩ with hzx
  set S' : Subgroup (Equiv.Perm (Fin n)) := (S.subgroupOf X).map ψ with hS'
  have hzxo : orderOf zx = p := by rw [hzx, Subgroup.orderOf_mk, hz]
  have hz' : orderOf (ψ zx) = p := by rw [orderOf_injective ψ hψ zx, hzxo]
  have hn' : Fintype.card (Fin n) < 2 * p := by simpa using hnp
  have hS2' : IsPGroup 2 S' := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hS2
    refine (IsPGroup.iff_card).2 ⟨m, ?_⟩
    rw [hS', Subgroup.card_map_of_injective hψ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hm]
  have hS0' : S' ≠ ⊥ := by
    intro hbot
    apply hS
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hmem : ψ ⟨s, hSX hs⟩ ∈ S' := Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hs)
    rw [hbot, Subgroup.mem_bot] at hmem
    have := hψ (hmem.trans (map_one ψ).symm)
    exact congrArg Subtype.val this
  have hzxS : zx ∈ normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_set_normalizer_iff.1 hzS h
  have hzS' : ψ zx ∈ normalizer (S' : Set (Equiv.Perm (Fin n))) := mem_normalizer_map ψ hzxS
  obtain ⟨T', Y', D', hT'S, hT'0, hzT', hST', hYT', hY'alt, hzY', hsec', hcop', h3'⟩ :=
    perm_level hp hp5 hz' hn' hS2' hS0' hzS'
  have hT'r : T' ≤ ψ.range := hT'S.trans (Subgroup.map_le_range ψ _)
  have hY'r : Y' ≤ ψ.range := hY'alt.trans halt
  have hD'r : D' ≤ ψ.range := hsec'.1.trans hY'r
  set Ty : Subgroup ↥X := T'.comap ψ with hTy
  set Yy : Subgroup ↥X := Y'.comap ψ with hYy
  set Dy : Subgroup ↥X := D'.comap ψ with hDy
  have hYm : Yy.map ψ = Y' := Subgroup.map_comap_eq_self hY'r
  have hDm : Dy.map ψ = D' := Subgroup.map_comap_eq_self hD'r
  have hTm : Ty.map ψ = T' := Subgroup.map_comap_eq_self hT'r
  have hsecX : S622IsSimpleSection Yy Dy :=
    s622IsSimpleSection_of_map ψ hψ (by rw [hYm, hDm]; exact hsec')
  have hsecA : S622IsSimpleSection (Yy.map f) (Dy.map f) :=
    L6LeavesNS.s622IsSimpleSection_map f hf hsecX
  have hzY : z ∈ Yy.map f := ⟨zx, hzY', rfl⟩
  have hnormT : ∀ g : ↥X, ψ g ∈ normalizer (T' : Set (Equiv.Perm (Fin n))) →
      g ∈ normalizer (Ty : Set ↥X) := fun g hg => L6LeavesNS.mem_normalizer_comap ψ hg
  have hcore : rankThreePrimeCore p (Yy.map f) = Dy.map f := by
    refine rankThreePrimeCore_eq_of_section hp hsecA ?_ hzY hz
    rw [Subgroup.card_map_of_injective hf, ← Subgroup.card_map_of_injective hψ, hDm]
    exact hcop'
  refine ⟨Ty.map f, Yy.map f, ?_, ?_, ?_, ?_, ?_, hzY, ?_, ?_⟩
  ·
    have h1 : Ty ≤ S.subgroupOf X := by
      intro g hg
      have hg' : ψ g ∈ S' := hT'S hg
      obtain ⟨g', hg'S, hgg'⟩ := hg'
      rw [hψ hgg'] at hg'S
      exact hg'S
    calc Ty.map f ≤ (S.subgroupOf X).map f := Subgroup.map_mono h1
      _ = S := Subgroup.map_subgroupOf_eq_of_le hSX
  ·
    intro hbot
    apply hT'0
    rw [← hTm]
    have : Ty = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have hmem : f g ∈ Ty.map f := Subgroup.mem_map_of_mem f hg
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    rw [this, Subgroup.map_bot]
  · exact mem_normalizer_map f (hnormT zx hzT')
  · intro s hs
    have hsX : s ∈ X := hSX hs
    have hmem : ψ ⟨s, hsX⟩ ∈ S' := Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hs)
    exact mem_normalizer_map f (hnormT ⟨s, hsX⟩ (hST' hmem))
  · refine le_inf ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_normalizer_map f (hnormT y (hYT' hy))
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
  · rw [hcore]
    exact hsecA
  · rw [hcore, Subgroup.relIndex_map_map_of_injective _ _ hf,
      ← Subgroup.relIndex_map_map_of_injective _ _ hψ, hDm, hYm]
    exact h3'

theorem kg2024_holds : KG2024 := by
  intro A _ _ X S z n p hX hn hp hp5 hpn hnp hz hzX hSX hS2 hS hzS
  obtain ⟨T, Y, hTS, hT0, hzT, hST, hY, hzY, hsec, h3⟩ : ∃ T Y : Subgroup A, T ≤ S ∧ T ≠ ⊥ ∧
      z ∈ normalizer (T : Set A) ∧ S ≤ normalizer (T : Set A) ∧
      Y ≤ normalizer (T : Set A) ⊓ X ∧ z ∈ Y ∧
      S622IsSimpleSection Y (rankThreePrimeCore p Y) ∧
      3 ∣ (rankThreePrimeCore p Y).relIndex Y := by
    rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine kg2024_of_hom X S z n p ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
        (Subtype.val_injective.comp e.injective) ?_ hp hp5 hnp hz hzX hSX hS2 hS hzS
      intro g hg
      exact ⟨e.symm ⟨g, hg⟩, by simp⟩
    · refine kg2024_of_hom X S z n p e.toMonoidHom e.injective ?_ hp hp5 hnp hz hzX hSX hS2 hS hzS
      intro g _
      exact ⟨e.symm g, by simp⟩
  exact ⟨T, Y, hTS, hT0, hzT, hST, hY, hzY, hsec, h3⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
