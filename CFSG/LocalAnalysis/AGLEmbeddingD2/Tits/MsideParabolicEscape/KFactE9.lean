module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactL32
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoLayerCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped Pointwise

theorem card_dvd_card_mulAut_of_faithful {X : Type} [Group X] [Finite X] (N Q : Subgroup X)
    [N.Normal] (hQC : Q ⊓ Subgroup.centralizer (N : Set X) = ⊥) :
    Nat.card Q ∣ Nat.card (MulAut ↥N) := by
  set φ : X →* MulAut ↥N := MulAut.conjNormal with hφ
  have hinj : Function.Injective (φ.comp Q.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : φ (x : X) = 1 := hx
    have hxC : (x : X) ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := congrArg (fun f : MulAut ↥N => (f ⟨h, hh⟩ : X)) hx1
      simp only [hφ, MulAut.conjNormal_apply] at this
      show h * (x : X) = (x : X) * h
      have h2 : (x : X) * h * (x : X)⁻¹ = h := this
      calc h * (x : X) = ((x : X) * h * (x : X)⁻¹) * (x : X) := by rw [h2]
        _ = (x : X) * h := by group
    have : (x : X) ∈ Q ⊓ Subgroup.centralizer (N : Set X) := ⟨x.2, hxC⟩
    rw [hQC, Subgroup.mem_bot] at this
    exact Subtype.ext (by simpa using this)
  have h1 : Nat.card Q = Nat.card (φ.comp Q.subtype).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem false_of_l32_faithful_nine {X : Type} [Group X] [Finite X] (N Q : Subgroup X)
    [N.Normal] (hmod : StatedClassicalModel ↥N .PSL 3 2 1) (hQ9 : Nat.card Q = 9)
    (hQC : Q ⊓ Subgroup.centralizer (N : Set X) = ⊥) : False := by
  obtain ⟨e⟩ := nonempty_equiv_gl32_of_model hmod
  have h := card_dvd_card_mulAut_of_faithful N Q hQC
  rw [hQ9, Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32] at h
  omega

@[expose] def KFactE9U33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N Q : Subgroup X) [N.Normal], IsSimpleGroup ↥N →
    StatedClassicalModel ↥N .PSU 3 3 1 → IsElemAbelian 3 Q → Nat.card Q = 9 →
    Q ⊓ Subgroup.centralizer (N : Set X) = ⊥ →
    (∀ x ∈ Q, ∀ y ∈ Q, x ≠ 1 → y ≠ 1 → ∃ g ∈ Subgroup.normalizer (Q : Set X), g * x * g⁻¹ = y) →
    False

theorem kFactRankTwoE9_of_u33 (hU : KFactE9U33) : KFactRankTwoE9 := by
  intro X _ _ N Q _ hs hty hQ3 hQ9 hQC htrans
  rcases hty with he | hL | hU33
  · exact he
  · exact (false_of_l32_faithful_nine N Q hL hQ9 hQC).elim
  · exact (hU X N Q hs hU33 hQ3 hQ9 hQC htrans).elim

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
