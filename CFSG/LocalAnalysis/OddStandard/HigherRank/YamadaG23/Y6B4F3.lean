module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_conj_mem_sup_zpowers {F : Subgroup G} {t x : G}
    (hF : ∀ a ∈ F, x * a * x⁻¹ ∈ F) (ht : x * t * x⁻¹ ∈ F ⊔ zpowers t) :
    ∀ c ∈ F ⊔ zpowers t, x * c * x⁻¹ ∈ F ⊔ zpowers t := by
  have hle : F ⊔ zpowers t ≤ (F ⊔ zpowers t).comap (MulAut.conj x).toMonoidHom := by
    apply sup_le
    · intro a ha
      exact Subgroup.mem_comap.mpr
        (by simpa [MulAut.conj_apply] using Subgroup.mem_sup_left (hF a ha))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_comap.mpr (by simpa [MulAut.conj_apply] using ht)
  intro c hc
  simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp (hle hc)

private lemma y6b_mem_normalizer_sup_zpowers {F : Subgroup G} {t x : G}
    (h : ∀ c ∈ F ⊔ zpowers t, x * c * x⁻¹ ∈ F ⊔ zpowers t) :
    x ∈ normalizer ((F ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply] using h c hc
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj x : G →* G))
      (MulAut.conj x).injective]

theorem y6b_equivar (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) {a : G} (haX : a ∈ y6bX c)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) (haW : a ∉ y6bW c) :
    ∀ n ∈ normIn L c.s.fr.F, a⁻¹ * (n * a * n⁻¹) ∈ y6bW c := by
  intro n hn
  set y : G := a⁻¹ * (n * a * n⁻¹) with hy
  have hnX : n ∈ y6bX c := y6b_NL_le_X c hH hRT hn
  have hnInvX : n⁻¹ ∈ y6bX c := (y6bX c).inv_mem hnX
  have hnM3 : n ∈ normalizer (M3 c.s : Set G) := y6e_NL_le_normalizer_M3 c hH hn
  have hnInvM3 : n⁻¹ ∈ normalizer (M3 c.s : Set G) :=
    (Subgroup.normalizer (M3 c.s : Set G)).inv_mem hnM3
  have hnF : n ∈ normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (show n ∈ L ⊓ normalizer (c.s.fr.F : Set G) from hn)).2
  have hnInvF : n⁻¹ ∈ normalizer (c.s.fr.F : Set G) :=
    (Subgroup.normalizer (c.s.fr.F : Set G)).inv_mem hnF
  have hanX : n * a * n⁻¹ ∈ y6bX c :=
    (y6bX c).mul_mem ((y6bX c).mul_mem hnX haX) ((y6bX c).inv_mem hnX)
  have hanF : ∀ f ∈ c.s.fr.F, (n * a * n⁻¹) * f = f * (n * a * n⁻¹) := by
    intro f hf
    have hnf : n⁻¹ * f * n ∈ c.s.fr.F := by
      have := (Subgroup.mem_normalizer_iff.mp hnInvF f).mp hf
      simpa using this
    calc (n * a * n⁻¹) * f = n * (a * (n⁻¹ * f * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * f * n) * a) * n⁻¹ := by rw [haF (n⁻¹ * f * n) hnf]
      _ = f * (n * a * n⁻¹) := by group
  have haInvF : ∀ f ∈ c.s.fr.F, a⁻¹ * f = f * a⁻¹ := by
    intro f hf
    have h := haF f hf
    calc a⁻¹ * f = a⁻¹ * (f * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * f) * a⁻¹ := by rw [← h]
      _ = f * a⁻¹ := by group
  have haInvX : a⁻¹ ∈ y6bX c := (y6bX c).inv_mem haX
  have haInvW : a⁻¹ ∉ y6bW c := fun hmem => haW (by simpa using (y6bW c).inv_mem hmem)
  have hanW : n * a * n⁻¹ ∉ y6bW c := by
    intro hmem
    obtain ⟨e, heE, m, hmM3, heq⟩ := (y6b_mem_W c hH hF hRT).mp hmem
    have hnInvE : n⁻¹ * e * n ∈ y6bE c := by
      have h' : n⁻¹ ∈ normalizer ((y6bE c : Subgroup G) : Set G) := hnInvX
      have := (Subgroup.mem_normalizer_iff.mp h' e).mp heE
      simpa using this
    have hnInvM : n⁻¹ * m * n ∈ M3 c.s := by
      have := (Subgroup.mem_normalizer_iff.mp hnInvM3 m).mp hmM3
      simpa using this
    have haEq : a = (n⁻¹ * e * n) * (n⁻¹ * m * n) := by
      rw [show (n⁻¹ * e * n) * (n⁻¹ * m * n) = n⁻¹ * (e * m) * n by group, ← heq]
      group
    exact haW ((y6b_mem_W c hH hF hRT).mpr
      ⟨n⁻¹ * e * n, hnInvE, n⁻¹ * m * n, hnInvM, haEq⟩)
  obtain ⟨f₁, hf₁, h₁eq⟩ := y6b_swap c hH hF hRT a haX haF haW
  obtain ⟨f₂, hf₂, h₂eq⟩ := y6b_swap c hH hF hRT a⁻¹ haInvX haInvF haInvW
  have h₂eq' : a⁻¹ * c.s.t * a = f₂ * (c.g * c.s.t) := by simpa using h₂eq
  obtain ⟨f₃, hf₃, h₃eq⟩ := y6b_swap c hH hF hRT (n * a * n⁻¹) hanX hanF hanW
  have hainvE16 : a⁻¹ * c.g * a ∈ y6bE16 c := by
    have hmem := y6b_X_le_normalizer_E16 c hH hF hRT h1 haInvX
    have := (Subgroup.mem_normalizer_iff.mp hmem c.g).mp (y6b_g_mem_E16 c)
    simpa using this
  have hf₄exists : ∃ f₄ ∈ c.s.fr.F, a⁻¹ * c.g * a = f₄ * c.g := by
    obtain ⟨f₄, hf₄mem, hf₄ | hf₄⟩ := (y6b_mem_E16 c hH hRT).mp hainvE16
    · exfalso
      have hgeq : c.g = f₄ := by
        calc c.g = a * (a⁻¹ * c.g * a) * a⁻¹ := by group
          _ = a * f₄ * a⁻¹ := by rw [hf₄]
          _ = f₄ := by rw [haF f₄ hf₄mem]; group
      exact y6b_g_not_mem_F c hH hRT (hgeq.symm ▸ hf₄mem)
    · exact ⟨f₄, hf₄mem, hf₄⟩
  obtain ⟨f₄, hf₄mem, hf₄eq⟩ := hf₄exists
  have hconj : y * c.s.t * y⁻¹ = (f₃ * f₄ * f₂) * c.s.t := by
    rw [hy]
    have h1' : a⁻¹ * (n * a * n⁻¹) * c.s.t * (a⁻¹ * (n * a * n⁻¹))⁻¹
        = a⁻¹ * ((n * a * n⁻¹) * c.s.t * (n * a * n⁻¹)⁻¹) * a := by group
    rw [h1', h₃eq]
    have h2' : a⁻¹ * (f₃ * (c.g * c.s.t)) * a
        = (a⁻¹ * f₃ * a) * (a⁻¹ * c.g * a) * (a⁻¹ * c.s.t * a) := by group
    rw [h2']
    have hf₃conj : a⁻¹ * f₃ * a = f₃ := by
      have h := haF f₃ hf₃
      calc a⁻¹ * f₃ * a = a⁻¹ * (f₃ * a) := by group
        _ = a⁻¹ * (a * f₃) := by rw [← h]
        _ = f₃ := by group
    rw [hf₃conj, hf₄eq, h₂eq']
    have hinner : f₄ * c.g * f₂ * c.g = f₄ * f₂ := by
      calc f₄ * c.g * f₂ * c.g = f₄ * (c.g * f₂) * c.g := by group
        _ = f₄ * (f₂ * c.g) * c.g := by rw [y6b_g_comm_F c hH hRT f₂ hf₂]
        _ = f₄ * f₂ * (c.g * c.g) := by group
        _ = f₄ * f₂ := by rw [y6b_g_sq c hRT, mul_one]
    calc f₃ * (f₄ * c.g) * (f₂ * (c.g * c.s.t))
        = f₃ * (f₄ * c.g * f₂ * c.g) * c.s.t := by group
      _ = f₃ * (f₄ * f₂) * c.s.t := by rw [hinner]
      _ = (f₃ * f₄ * f₂) * c.s.t := by group
  have haCen : a ∈ centralizer (c.s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (haF f hf).symm
  have hanCen : n * a * n⁻¹ ∈ centralizer (c.s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hanF f hf).symm
  have hyCent : y ∈ centralizer (c.s.fr.F : Set G) := by
    rw [hy]
    exact (centralizer (c.s.fr.F : Set G)).mul_mem
      ((centralizer (c.s.fr.F : Set G)).inv_mem haCen) hanCen
  have hyCentF : ∀ a' ∈ c.s.fr.F, y * a' * y⁻¹ ∈ c.s.fr.F := by
    intro a' ha'
    have hcomm : a' * y = y * a' := Subgroup.mem_centralizer_iff.mp hyCent a' ha'
    have heq : y * a' * y⁻¹ = a' := by
      calc y * a' * y⁻¹ = (y * a') * y⁻¹ := by rw [mul_assoc]
        _ = (a' * y) * y⁻¹ := by rw [← hcomm]
        _ = a' := by group
    rw [heq]
    exact ha'
  have ht_mem : y * c.s.t * y⁻¹ ∈ c.s.fr.F ⊔ zpowers c.s.t := by
    rw [hconj]
    exact Subgroup.mul_mem_sup (c.s.fr.F.mul_mem (c.s.fr.F.mul_mem hf₃ hf₄mem) hf₂)
      (Subgroup.mem_zpowers c.s.t)
  have hyX : y ∈ f4X c.s :=
    y6b_mem_normalizer_sup_zpowers (y6b_conj_mem_sup_zpowers hyCentF ht_mem)
  have hyY : y ∈ f4Y c.s := Subgroup.mem_inf.mpr ⟨hyX, hyCent⟩
  obtain ⟨m, hmM3, x, hxX0, hyeq⟩ := y54_Y_decomp (c := c) hH (y54_M3_cand c hH) y hyY
  have hxE : x ∈ y6bE c := y6b_cent_H_F_le_E c hH hRT hxX0
  rw [hyeq]
  exact (y6bW c).mul_mem (Subgroup.mem_sup_right hmM3) (Subgroup.mem_sup_left hxE)

end CFSG.OddStandard.HigherRank.YamadaG23
