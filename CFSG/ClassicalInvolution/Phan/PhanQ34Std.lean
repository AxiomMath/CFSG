module

public import CFSG.ClassicalInvolution.Phan.PhanQ33Frame
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Phan.PhanQ12KData
public import CFSG.ClassicalInvolution.Phan.PhanQ6Bwd

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Res

variable {F : Type} [Field F] {ε : F}

@[expose] def QuadRes (ε : F) (a b c d : NPair ε) : Prop :=
  (∃ e : NPair ε, ColP ε e a ∧ ColP ε e b ∧ ColP ε e c ∧ ColP ε e d) ∨
  (∃ c' : NPair ε, ColP ε c' b ∧ ColP ε c' c ∧ ColP ε c' d ∧
    ∃ e : NPair ε, ColP ε e a ∧ ColP ε e b ∧ ColP ε e c' ∧ ColP ε e d) ∨
  (∃ d' : NPair ε, ColP ε d' a ∧ ColP ε d' c ∧ ColP ε d' d ∧
    ∃ e : NPair ε, ColP ε e a ∧ ColP ε e b ∧ ColP ε e c ∧ ColP ε e d')

theorem QuadRes.of_smul (g : spinGroup (quadPlus 4 F)) {a b c d : NPair ε}
    (h : QuadRes ε (g • a) (g • b) (g • c) (g • d)) : QuadRes ε a b c d := by
  have key : ∀ {x y : NPair ε}, ColP ε x (g • y) → ColP ε (g⁻¹ • x) y := fun {x y} h => by
    have := (colP_smul g⁻¹).2 h
    rwa [NPair.inv_smul_smul'] at this
  have key2 : ∀ {x y : NPair ε}, ColP ε x y → ColP ε (g⁻¹ • x) (g⁻¹ • y) :=
    fun {x y} h => (colP_smul g⁻¹).2 h
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨c', h1, h2, h3, e, h4, h5, h6, h7⟩ |
    ⟨d', h1, h2, h3, e, h4, h5, h6, h7⟩
  · exact Or.inl ⟨g⁻¹ • e, key h1, key h2, key h3, key h4⟩
  · exact Or.inr (Or.inl ⟨g⁻¹ • c', key h1, key h2, key h3, g⁻¹ • e, key h4, key h5, key2 h6,
      key h7⟩)
  · exact Or.inr (Or.inr ⟨g⁻¹ • d', key h1, key h2, key h3, g⁻¹ • e, key h4, key h5, key h6,
      key2 h7⟩)

end Res

section Std

variable {p e : ℕ} [Fact p.Prime]

theorem resolved_normal (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {b c d : NPair M.ε}
    (hb : InW0 b.x ∧ InW0 b.y) (cab : ColP M.ε (z0 M.ε) b) (cbc : ColP M.ε b c)
    (ccd : ColP M.ε c d) (cda : ColP M.ε d (z0 M.ε)) : QuadRes M.ε (z0 M.ε) b c d := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  have hinz : InW0 (z0 M.ε).x ∧ InW0 (z0 M.ε).y := by
    rw [z0_x_eq, z0_y_eq]
    exact ⟨inW0_incl _, inW0_incl _⟩
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hK := StdModel.card_K hq
  let _ : Algebra (GaloisField p e) (GaloisField p (2 * e)) := (Aniso.nonempty_algebra hF hK).some
  obtain ⟨D⟩ := exists_kdata (F := GaloisField p e) (K := GaloisField p (2 * e)) p e hF hK hp2
    M.hε M.nonsq
  have := Fintype.ofFinite (GaloisField p (2 * e))
  classical
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hq2 : 2 ≤ Nat.card (GaloisField p e) := by omega
  have hq5 : 4 * (Nat.card (GaloisField p e) + 1) < Nat.card (GaloisField p e) ^ 2 := by
    rw [hF]
    nlinarith
  have Fr : QFrame D (vecK D (z0 M.ε)) (vecK D b) (vecK D c) (vecK D d) :=
    ⟨inW0_vecK D hinz.1 hinz.2, inW0_vecK D hb.1 hb.2, ffK_vecK D h2K M.hε _,
      ffK_vecK D h2K M.hε _, ffK_vecK D h2K M.hε _, ffK_vecK D h2K M.hε _,
      (colK_vecK_iff D h2K M.hε).2 cab, (colK_vecK_iff D h2K M.hε).2 cbc,
      (colK_vecK_iff D h2K M.hε).2 ccd, (colK_vecK_iff D h2K M.hε).2 cda⟩
  have P : ∀ {x y : NPair M.ε}, ColK D (vecK D x) (vecK D y) → ColP M.ε x y :=
    fun h => (colK_vecK_iff D h2K M.hε).1 h
  rcases quad_frame D h2K M.hε hq2 hq5 Fr with ⟨f, hff, h1, h2, h3, h4⟩ |
    ⟨c', hc'f, h1, h2, h3, f, hff, h4, h5, h6, h7⟩ |
    ⟨d', hd'f, h1, h2, h3, f, hff, h4, h5, h6, h7⟩
  · obtain ⟨κ, hκ, f', rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hff
    rw [colK_smul_left D hκ] at h1 h2 h3 h4
    exact Or.inl ⟨f', P h1, P h2, P h3, P h4⟩
  · obtain ⟨κ₁, hκ₁, c'', rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hc'f
    obtain ⟨κ₂, hκ₂, f', rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hff
    rw [colK_smul_left D hκ₁] at h1 h2 h3
    rw [colK_smul_left D hκ₂] at h4 h5 h7
    rw [colK_smul D hκ₂ hκ₁] at h6
    exact Or.inr (Or.inl ⟨c'', P h1, P h2, P h3, f', P h4, P h5, P h6, P h7⟩)
  · obtain ⟨κ₁, hκ₁, d'', rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hd'f
    obtain ⟨κ₂, hκ₂, f', rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hff
    rw [colK_smul_left D hκ₁] at h1 h2 h3
    rw [colK_smul_left D hκ₂] at h4 h5 h6
    rw [colK_smul D hκ₂ hκ₁] at h7
    exact Or.inr (Or.inr ⟨d'', P h1, P h2, P h3, f', P h4, P h5, P h6, P h7⟩)

theorem resolved_std (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {a b c d : NPair M.ε}
    (hab : ColP M.ε a b) (hbc : ColP M.ε b c) (hcd : ColP M.ε c d) (hda : ColP M.ε d a) :
    QuadRes M.ε a b c d := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨g₁, hg₁⟩ := exists_smul_z0 h2 hodd M.hε M.h4 a
  have hcol1 : ColP M.ε (z0 M.ε) (g₁⁻¹ • b) := by
    have := (colP_smul g₁⁻¹).2 hab
    rwa [← hg₁, NPair.inv_smul_smul'] at this
  obtain ⟨g, hgz, N, hN, hgx, hgy⟩ := exists_normal_pair M hp2 hq hcol1
  have ha' : (g * g₁⁻¹) • a = z0 M.ε := by
    rw [NPair.mul_smul', ← hg₁, NPair.inv_smul_smul', hgz]
  have hb' : (g * g₁⁻¹) • b = g • (g₁⁻¹ • b) := NPair.mul_smul' g g₁⁻¹ b
  set h := g * g₁⁻¹ with hh
  have hinb : InW0 (h • b).x ∧ InW0 (h • b).y := by
    rw [hb', hgx, hgy]
    exact ⟨inW0_incl _, inW0_incl _⟩
  refine QuadRes.of_smul h ?_
  have cab : ColP M.ε (h • a) (h • b) := (colP_smul h).2 hab
  have cbc : ColP M.ε (h • b) (h • c) := (colP_smul h).2 hbc
  have ccd : ColP M.ε (h • c) (h • d) := (colP_smul h).2 hcd
  have cda : ColP M.ε (h • d) (h • a) := (colP_smul h).2 hda
  rw [ha'] at cab cda ⊢
  exact resolved_normal M hp2 hq hinb cab cbc ccd cda

end Std

end CFSG.ClassicalInvolution.PhanQ
