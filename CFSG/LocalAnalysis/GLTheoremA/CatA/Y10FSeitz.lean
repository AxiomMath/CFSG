module

public import CFSG.LieType.Seitz.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def centFixAut {K : Type} [Group K] (F : Subgroup (MulAut K)) : Subgroup K :=
  CFSG.LieType.Seitz.fixedPoints F

theorem mem_centFixAut {K : Type} [Group K] {F : Subgroup (MulAut K)} {k : K} :
    k ∈ centFixAut F ↔ ∀ φ ∈ F, φ k = k := Iff.rfl

@[expose] def SeitzGen : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut K), IsElemAbelian q E →
      Nat.card E ≤ q ^ 3 →
      (∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
        ∀ φ ∈ E, ∀ t ∈ T, φ t ∈ T) →
      (⨆ (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E ≤ q), centFixAut F) = ⊤

theorem card_map_le_of_finite {X Y : Type} [Group X] [Group Y] [Finite X] (f : X →* Y) (E : Subgroup X) :
    Nat.card (E.map f) ≤ Nat.card E :=
  Nat.card_le_card_of_surjective (fun x : E => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : E.map f))
    (by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, rfl⟩)

@[expose] def centFixAct {K Y : Type} [Group K] [Group Y] (ρ : Y →* MulAut K) (F : Subgroup Y) :
    Subgroup K :=
  centFixAut (F.map ρ)

theorem mem_centFixAct {K Y : Type} [Group K] [Group Y] {ρ : Y →* MulAut K} {F : Subgroup Y}
    {k : K} : k ∈ centFixAct ρ F ↔ ∀ f ∈ F, ρ f k = k := by
  rw [centFixAct, mem_centFixAut]
  constructor
  · intro h f hf
    exact h _ (Subgroup.mem_map_of_mem ρ hf)
  · intro h φ hφ
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hφ
    exact h f hf

theorem seitzGen_action (h : SeitzGen) {K : Type} [Group K] [Finite K]
    (hK : HasLabel K (fun _ => True)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y : Type} [Group Y]
    (ρ : Y →* MulAut K) {E : Subgroup Y} (hE : IsElemAbelian q E) (hcard : Nat.card (E.map ρ) ≤ q ^ 3)
    (hT : ∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
      ∀ e ∈ E, ∀ t ∈ T, ρ e t ∈ T) :
    (⨆ (F : Subgroup Y) (_ : F ≤ E ∧ F.relIndex E ≤ q), centFixAct ρ F) = ⊤ := by
  have hE' : IsElemAbelian q (E.map ρ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
      show (a : MulAut K) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE ha' hb']
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, hE.2 x' hx', map_one]
  obtain ⟨T, hT2, hTc, hTinv⟩ := hT
  have hall := h K hK q hq hq2 (E.map ρ) hE' hcard ⟨T, hT2, hTc, by
    rintro φ hφ t ht
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hφ
    exact hTinv e he t ht⟩
  rw [eq_top_iff, ← hall]
  refine iSup₂_le fun Fh ⟨hFhE, hFhi⟩ => ?_
  refine le_trans ?_ (le_iSup₂_of_le ((Fh.comap ρ) ⊓ E) ⟨inf_le_right, ?_⟩ le_rfl)
  · intro k hk
    rw [mem_centFixAut] at hk
    rw [mem_centFixAct]
    intro f hf
    exact hk (ρ f) hf.1
  · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
    exact hFhi

end CFSG.LocalAnalysis.GLTheoremA.Y10F
