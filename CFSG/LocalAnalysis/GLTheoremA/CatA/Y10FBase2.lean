module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

section Maps

variable {X Y : Type} [Group X] [Group Y]

theorem isPGroup_map_iff_of_injective {p : ℕ} {ι : X →* Y} (hι : Function.Injective ι)
    (H : Subgroup X) : IsPGroup p ↥(H.map ι) ↔ IsPGroup p ↥H := by
  constructor
  · intro h
    exact h.of_injective (Subgroup.equivMapOfInjective H ι hι).toMonoidHom
      (Subgroup.equivMapOfInjective H ι hι).injective
  · intro h
    exact h.of_injective (Subgroup.equivMapOfInjective H ι hι).symm.toMonoidHom
      (Subgroup.equivMapOfInjective H ι hι).symm.injective

theorem le_pRank_of_elem [Finite X] {p : ℕ} (hp : 1 < p) {H E : Subgroup X} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  apply le_csSup
  · refine ⟨Nat.card X, ?_⟩
    rintro k' ⟨E', -, -, hc⟩
    have h1 : p ^ k' ≤ Nat.card X := hc ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp).le.trans h1
  · exact ⟨E, hEH, hE, hk⟩

theorem card_mul_relIndex {E F : Subgroup X} (hFE : F ≤ E) :
    Nat.card F * F.relIndex E = Nat.card E := by
  have h := Subgroup.card_mul_index (F.subgroupOf E)
  have e1 : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
  rw [e1] at h
  exact h

end Maps


section Rank

variable {X : Type} [Group X] [Finite X]

theorem exists_elem_of_le_pRank {q : ℕ} (hq : 1 < q) {H : Subgroup X} {n : ℕ}
    (h : n ≤ CFSG.Open.pRank q H) :
    ∃ E : Subgroup X, E ≤ H ∧ IsElemAbelian q E ∧ ∃ k : ℕ, n ≤ k ∧ Nat.card E = q ^ k := by
  have hne : {k | ∃ E : Subgroup X, E ≤ H ∧ IsElemAbelian q E ∧ Nat.card E = q ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
      have : x = 1 := Subgroup.mem_bot.1 hx
      simp [this]⟩, by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup X, E ≤ H ∧ IsElemAbelian q E ∧ Nat.card E = q ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k' ⟨E', -, -, hc⟩
    have h1 : q ^ k' ≤ Nat.card X := hc ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hq).le.trans h1
  obtain ⟨E, hEH, hE, hc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEH, hE, _, h, hc⟩

end Rank

theorem exists_conj_le_sylow {K : Type} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    {E' Q' : Subgroup K} (hE : IsPGroup q E') (hQ : IsPGroup q Q')
    (hmax : ∀ Q : Subgroup K, IsPGroup q Q → Q' ≤ Q → Q = Q') :
    ∃ g : K, E'.map (MulAut.conj g).toMonoidHom ≤ Q' := by
  let P : Sylow q K := ⟨Q', hQ, fun hQ' hle => hmax _ hQ' hle⟩
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S P
  refine ⟨g, ?_⟩
  have h1 : ((g • S : Sylow q K) : Subgroup K) = (MulAut.conj g) • (S : Subgroup K) :=
    Sylow.coe_subgroup_smul
  rw [hg] at h1
  have h2 : (P : Subgroup K) = Q' := rfl
  rw [← h2, h1]
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
  exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) _ (hS he)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
