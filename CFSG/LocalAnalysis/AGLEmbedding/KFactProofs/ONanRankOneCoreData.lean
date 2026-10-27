module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

open CFSG.Open CFSG.AGLEmbedding.KFactProofs.SmallGamma

structure RankOneCoreData (L : Type*) [Group L] (T : Subgroup L) : Prop where
  normalizer_le : ∀ Q : Subgroup L, Q ≤ T → Q ≠ ⊥ →
    Subgroup.normalizer (Q : Set L) ≤ Subgroup.normalizer (T : Set L)
  ne_top : Subgroup.normalizer (T : Set L) ≠ ⊤

namespace RankOneCoreData

variable {L L' : Type*} [Group L] [Group L'] {T : Subgroup L} {T' : Subgroup L'}

theorem glbCore_ne_top [Finite L] {p : ℕ} (hp : 2 ≤ p) (h : RankOneCoreData L T) :
    GLBCore p 1 T ≠ ⊤ := by
  intro htop
  apply h.ne_top
  rw [eq_top_iff, ← htop]
  exact glbCore_le_of_normalizer_le hp h.normalizer_le

theorem map (e : L ≃* L') (hT : ∀ g, g ∈ T ↔ e g ∈ T') (h : RankOneCoreData L T) :
    RankOneCoreData L' T' := by
  refine ⟨fun Q' hQ'T hQ' y' hy' => ?_, fun htop => h.ne_top ?_⟩
  · set Q : Subgroup L := Q'.comap e.toMonoidHom with hQdef
    have hQmem : ∀ g, g ∈ Q ↔ e g ∈ Q' := fun g => Iff.rfl
    have hQT : Q ≤ T := fun g hg => (hT g).2 (hQ'T hg)
    have hQbot : Q ≠ ⊥ := by
      intro hbot
      apply hQ'
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxQ : e.symm x ∈ Q := by rw [hQmem]; simpa using hx
      rw [hbot, Subgroup.mem_bot] at hxQ
      simpa using congrArg e hxQ
    have hnorm : ∀ n : L, n ∈ Subgroup.normalizer (Q : Set L) ↔
        e n ∈ Subgroup.normalizer (Q' : Set L') := fun n =>
      SmallGammaData.mem_normalizer_iff (T := Q) (T' := Q') e hQmem n
    have hy := (hnorm (e.symm y')).2 (by simpa using hy')
    have := (SmallGammaData.mem_normalizer_iff (T := T) (T' := T') e hT _).1
      (h.normalizer_le Q hQT hQbot hy)
    simpa using this
  · rw [eq_top_iff]
    intro g _
    exact (SmallGammaData.mem_normalizer_iff e hT g).2 (by rw [htop]; exact Subgroup.mem_top _)

theorem of_equiv_map (e : L ≃* L') (hT : T.map e.toMonoidHom = T') (h : RankOneCoreData L' T') :
    RankOneCoreData L T :=
  map e.symm (fun y => by rw [← hT, Subgroup.mem_map_equiv]) h

theorem of_equiv_sylow [Finite L] {p : ℕ} [Fact p.Prime] (e : L ≃* L') (U : Sylow p L)
    (S : Sylow p L') (hS : RankOneCoreData L' (S : Subgroup L')) :
    RankOneCoreData L (U : Subgroup L) := by
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  exact of_equiv_map e' he' hS

end RankOneCoreData

theorem normalizer_ne_top_of_card_sylow {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    (U : Sylow p L) (h : 1 < Nat.card (Sylow p L)) :
    Subgroup.normalizer ((U : Subgroup L) : Set L) ≠ ⊤ := by
  intro htop
  have h1 : Nat.card (Sylow p L) = (Subgroup.normalizer ((U : Subgroup L) : Set L)).index :=
    U.card_eq_index_normalizer
  rw [h1, htop, Subgroup.index_top] at h
  exact lt_irrefl 1 h

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
