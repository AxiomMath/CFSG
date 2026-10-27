module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Conv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Orbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremB (not_dvd_card_glaPPrimeCoreOf)

section Max

variable {G : Type} [Group G] [Finite G]

theorem exists_maximal_B_subgroup (B L T₀ : Subgroup G) (hT₀L : T₀ ≤ L) (hT₀2 : IsPGroup 2 T₀)
    (hT₀B : B ≤ Subgroup.normalizer (T₀ : Set G)) :
    ∃ T : Subgroup G, T₀ ≤ T ∧ T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ T' : Subgroup G, T ≤ T' → T' ≤ L → IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) → T' = T := by
  haveI : Finite (Subgroup G) := Finite.of_injective (fun T : Subgroup G => (T : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {T' | T₀ ≤ T' ∧ T' ≤ L ∧ IsPGroup 2 T' ∧ B ≤ Subgroup.normalizer (T' : Set G)}
  obtain ⟨T, hTS, hmax⟩ := (Set.toFinite S).exists_maximal ⟨T₀, le_rfl, hT₀L, hT₀2, hT₀B⟩
  obtain ⟨h1, h2, h3, h4⟩ := hTS
  refine ⟨T, h1, h2, h3, h4, fun T' hTT' hT'L hT'2 hT'B => ?_⟩
  have hmem : T' ∈ S := ⟨h1.trans hTT', hT'L, hT'2, hT'B⟩
  exact le_antisymm (hmax hmem hTT') hTT'

theorem normalizes_map_of_invariant {B L : Subgroup G} (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) {T' : Subgroup ↥L}
    (hinv : ∀ g : ↥B, ∀ t ∈ T', conjHom L B hBL hcomm g t ∈ T') :
    B ≤ Subgroup.normalizer ((T'.map L.subtype : Subgroup G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    have hdi : d⁻¹ ∈ B := B.inv_mem hd
    have hs := hinv ⟨d⁻¹, hdi⟩ t ht
    refine Subgroup.mem_map.2 ⟨_, hs, ?_⟩
    rw [conjHom_apply]
    simp [conjAutOf_apply]
  · intro hh
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hh
    have hs := hinv ⟨d, hd⟩ t ht
    refine Subgroup.mem_map.2 ⟨_, hs, ?_⟩
    rw [conjHom_apply]
    simp only [conjAutOf_apply, Subgroup.coe_subtype] at hte ⊢
    rw [hte]
    group

theorem layer_transport_G {p : ℕ} (hp : p.Prime) {B L : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g)
    {a : G} (hd : a ∈ Subgroup.normalizer (L : Set G)) {T' : Subgroup ↥L}
    (hT'L : T' ≤ GLAPLayer p (fixSub (conjAutOf L a hd))) (hT'2 : IsPGroup 2 T')
    (hinv : ∀ g : ↥B, ∀ t ∈ T', conjHom L B hBL hcomm g t ∈ T')
    (hT'O : ¬ T' ≤ GLAPPrimeCoreOf p (GLAPLayer p (fixSub (conjAutOf L a hd)))) :
    (T'.map L.subtype) ≤ GLAPLayer p (L ⊓ cx a) ∧ IsPGroup 2 (T'.map L.subtype) ∧
      B ≤ Subgroup.normalizer ((T'.map L.subtype : Subgroup G) : Set G) ∧
      ¬ (T'.map L.subtype) ≤ GLAPPrimeCoreOf p (GLAPLayer p (L ⊓ cx a)) := by
  rw [fixSub_conjAutOf] at hT'L hT'O
  set ℓH : Subgroup ↥L := GLAPLayer p ((L ⊓ cx a).subgroupOf L) with hℓH
  set ℓG : Subgroup G := ℓH.map L.subtype with hℓG
  have hℓG_le : ℓG ≤ GLAPLayer p (L ⊓ cx a) := map_glaPLayer_subgroupOf_le inf_le_left
  have hℓG_le_L : ℓG ≤ L := Subgroup.map_subtype_le _
  have hT''ℓ : T'.map L.subtype ≤ ℓG := Subgroup.map_mono hT'L
  refine ⟨hT''ℓ.trans hℓG_le, hT'2.map L.subtype, normalizes_map_of_invariant hBL hcomm hinv, ?_⟩
  intro hle
  set O' : Subgroup G := GLAPPrimeCoreOf p (GLAPLayer p (L ⊓ cx a)) with hO'
  have hNnorm : ∀ g ∈ ℓG, ∀ t ∈ O' ⊓ ℓG, g * t * g⁻¹ ∈ O' ⊓ ℓG := by
    intro g hg t ht
    exact ⟨glaPPrimeCoreOf_normalized _ (Subgroup.le_normalizer (hℓG_le hg)) ht.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ht.2) (Subgroup.inv_mem _ hg)⟩
  have hNcop : Nat.Coprime p (Nat.card ↥(O' ⊓ ℓG)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hdvd' : Nat.card ↥(O' ⊓ ℓG) ∣ Nat.card ↥O' := Subgroup.card_dvd_of_le inf_le_left
    exact not_dvd_card_glaPPrimeCoreOf hp _ (hdvd.trans hdvd')
  have hN_le : O' ⊓ ℓG ≤ GLAPPrimeCoreOf p ℓG := le_glaPPrimeCoreOf inf_le_right hNnorm hNcop
  have hT''O : T'.map L.subtype ≤ GLAPPrimeCoreOf p ℓG := (le_inf hle hT''ℓ).trans hN_le
  have key := map_glaPPrimeCoreOf_subgroupOf (p := p) (J := L) (A := ℓG) hℓG_le_L
  rw [hℓG, subgroupOf_map_subtype_self] at key
  apply hT'O
  intro x hx
  have hxG : (x : G) ∈ GLAPPrimeCoreOf p ℓG := hT''O (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  rw [hℓG, ← key] at hxG
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxG
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy


end Max

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
