module

public import CFSG.ClassicalInvolution.Asc77.AscS16E
public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind
import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual3
import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscSix63

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Disconnected

section Connected

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem hall_of_connected (hp : p ≠ 2) (hΦ : HypOmegaMod p f Φ) (hconn : DConnected Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z) :
    ∀ B ∈ Φ, IsUniqueInvolution B z := by
  have hpath : ∀ N, Relation.ReflTransGen
      (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N → N ∈ Φ ∧ IsUniqueInvolution N z := by
    intro N hN
    induction hN with
    | refl => exact ⟨hA, hzA⟩
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      obtain ⟨hMΦ, hzM⟩ := ih
      refine ⟨hN'Φ, ?_⟩
      rcases hadj with h | h
      · obtain ⟨w, hw1, hw2⟩ :=
          hstar M hMΦ N' hN'Φ (T3.omegaNbr_subset_omegaStarNbr hp hΦ M h)
        have := hzM.eq hw1
        subst this
        exact hw2
      · obtain ⟨w, hw1, hw2⟩ :=
          hstar N' hN'Φ M hMΦ (T3.omegaNbr_subset_omegaStarNbr hp hΦ N' h)
        have := hzM.eq hw2
        subst this
        exact hw1
  intro B hB
  exact (hpath B (hconn A hA B hB)).2

theorem false_of_s3_shape (hΦ : HypOmegaMod p f Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    (hs3 : MuTab.ShapeS3 Φ) : False := by
  obtain ⟨hDE, B, hB, J, hJ⟩ := hs3
  obtain ⟨w, hw1, hw2⟩ := hstar B hB J hJ.1 hJ
  rcases mem_kPerp_of_twin hΦ hJ.1 hB hw2 hw1 with h | h
  · exact hJ.2.1 h
  · exact hDE B hB J hJ.1 (Or.inl h)

theorem false_of_t6_section (hR1 : Z2NoD8 p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hBelow : CITBelowU p f n) (hlt : Nat.card X < n) (hS : TransSection p f Φ)
    (htop : (⊤ : Subgroup X) ∉ Φ) (hDE : DEdgeless Φ)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a v : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (hv : ∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (hvA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) (hv2 : v * v = 1) (hav : v * a * v⁻¹ = a⁻¹) : False := by
  classical
  have hΦ : HypOmegaMod p f Φ := hS.hyp
  have hsh : MuTab.MuSmallShapes p f :=
    MuTab.muSmallShapes_of_g2d4 ih8D4Star (MuTab.muResidualG2D4_proved p f)
  have h6 := thm6SectBelow'_of_citBelow (ih8SmallEdge p) hBelow hp hq X hlt Φ hS.toGen
    ⟨A, hA⟩ htop hDE
  have hmain : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}, HasLieType p f Φ t k →
      ∀ (D : OmegaLie p f Φ) (hcard : D.card = 1) (i : Fin D.card), D.tag i = t → D.rank i = k →
        (MuTab.muKind (piSign p f) t k = .s3 ∨
          ((t = .PSL ∧ k = 3 ∧ p ^ f % 4 = 3) ∨ (t = .PSU ∧ k = 3 ∧ p ^ f % 4 = 1))) →
        False := by
    intro t k hL D hcard i ht hk hkind
    rcases hkind with hk3 | hZ2
    · have hshape := MuTab.kindShape_of_shapes hsh hp hq hS ⟨A, hA⟩ htop hL
      rw [hk3] at hshape
      exact false_of_s3_shape hΦ hstar hshape
    · refine false_of_z2_section hR1 hp hq hS.toGen D hcard i ?_ ι hι a v ha hv hA hzA haA hvA
        ha2 hv2 hav
      rw [ht, hk]
      exact hZ2
  rcases h6 with hL | hL | hL | hL
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    by_cases hπ : piSign p f = true
    · exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inl (by simp [MuTab.muKind, hπ]))
    · have hπf : piSign p f = false := by simpa using hπ
      exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inr (Or.inl ⟨rfl, rfl, MuTab.pow_mod_four_of_piSign_false hp hπf⟩))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    by_cases hπ : piSign p f = true
    · exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inr (Or.inr ⟨rfl, rfl, MuTab.piSign_true_iff.mp hπ⟩))
    · have hπf : piSign p f = false := by simpa using hπ
      exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk
        (Or.inl (by simp [MuTab.muKind, hπf]))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk (Or.inl (by simp [MuTab.muKind]))
  · obtain ⟨D, hcard, i, ht, hk⟩ := hL
    exact hmain ⟨D, hcard, i, ht, hk⟩ D hcard i ht hk (Or.inl (by simp [MuTab.muKind]))

end Connected

end S16

end CFSG.ClassicalInvolution.Asc77
