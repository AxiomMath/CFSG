module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP3

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

section Subgroups

variable {X : Type*} [Group X] {H T M L : Subgroup X}

theorem subgroupOf_normT (hLH : L ≤ H) :
    (T ⊓ Subgroup.normalizer (L : Set X)).subgroupOf H =
      normT (T.subgroupOf H) (L.subgroupOf H) := by
  have h1 : (T ⊓ Subgroup.normalizer (L : Set X)).subgroupOf H =
      T.subgroupOf H ⊓ (Subgroup.normalizer (L : Set X)).subgroupOf H :=
    Subgroup.ext fun _ => Iff.rfl
  rw [h1, Subgroup.subgroupOf_normalizer_eq hLH]

theorem subgroupOf_locL (hLH : L ≤ H) (hTH : T ≤ H) :
    (L ⊔ (T ⊓ Subgroup.normalizer (L : Set X))).subgroupOf H =
      locL (T.subgroupOf H) (L.subgroupOf H) := by
  rw [Subgroup.subgroupOf_sup hLH (inf_le_left.trans hTH), subgroupOf_normT hLH]

theorem subgroupOf_maxL (hLH : L ≤ H) (hTH : T ≤ H) :
    ((M ⊓ L) ⊔ (T ⊓ Subgroup.normalizer (L : Set X))).subgroupOf H =
      maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) := by
  have h1 : (M ⊓ L).subgroupOf H = M.subgroupOf H ⊓ L.subgroupOf H :=
    Subgroup.ext fun _ => Iff.rfl
  rw [Subgroup.subgroupOf_sup (inf_le_right.trans hLH) (inf_le_left.trans hTH), h1,
    subgroupOf_normT hLH]

end Subgroups

section Aut

variable {X : Type*} [Group X]

@[expose] def autCongr {H L : Subgroup X} (hLH : L ≤ H) :
    MulAut ↥(L.subgroupOf H) ≃* MulAut ↥L :=
  MulAut.congr (Subgroup.subgroupOfEquivOfLe hLH)

theorem autCongr_normalizerMonoidHom {H L : Subgroup X} (hLH : L ≤ H) {n : ↥H}
    (hn : n ∈ normL (L.subgroupOf H)) {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (hgn : (n : X) = g) :
    autCongr hLH ((L.subgroupOf H).normalizerMonoidHom ⟨n, hn⟩) =
      conjAct L ⟨g, hg⟩ := by
  subst hgn
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp [autCongr, conjAct]

theorem autOn_eq_map_actImg {H L Y : Subgroup X} (hLH : L ≤ H) (hYH : Y ≤ H) :
    autOn Y L = (actImg (L.subgroupOf H) (Y.subgroupOf H)).map (autCongr hLH).toMonoidHom := by
  ext a
  constructor
  · intro ha
    obtain ⟨⟨g, hg⟩, hgY, rfl⟩ := Subgroup.mem_map.1 ha
    have hgY' : g ∈ Y := hgY
    have hgH : g ∈ H := hYH hgY'
    have hn : (⟨g, hgH⟩ : ↥H) ∈ normL (L.subgroupOf H) := by
      have h1 : (⟨g, hgH⟩ : ↥H) ∈ (Subgroup.normalizer (L : Set X)).subgroupOf H := hg
      rwa [Subgroup.subgroupOf_normalizer_eq hLH] at h1
    refine Subgroup.mem_map.2 ⟨(L.subgroupOf H).normalizerMonoidHom ⟨⟨g, hgH⟩, hn⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨⟨⟨g, hgH⟩, hn⟩, hgY', rfl⟩
    · exact autCongr_normalizerMonoidHom hLH hn hg rfl
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨⟨n, hn⟩, hnY, rfl⟩ := Subgroup.mem_map.1 hb
    have hnY' : (n : X) ∈ Y := hnY
    have hg : (n : X) ∈ Subgroup.normalizer (L : Set X) := by
      have h1 : n ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := hn
      rw [← Subgroup.subgroupOf_normalizer_eq hLH] at h1
      exact h1
    exact Subgroup.mem_map.2 ⟨⟨(n : X), hg⟩, hnY', (autCongr_normalizerMonoidHom hLH hn hg rfl)⟩

end Aut

end CFSG.QuasithinUnique.Setup.Layer.Actor
