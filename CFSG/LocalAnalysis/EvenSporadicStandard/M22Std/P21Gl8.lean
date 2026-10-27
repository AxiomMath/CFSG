module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Matrix

@[expose] def gl8 : ℕ := 5348063769211699200

theorem card_GL8 : Nat.card (GL (Fin 8) (ZMod 2)) = gl8 := by
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_eight, gl8]

theorem exists_embedding_gl8 {V : Type} [Group V] (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x * x = 1) (hcard : Nat.card V = 256) {G : Type} [Group G]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ) :
    ∃ f : G →* GL (Fin 8) (ZMod 2), Function.Injective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 8) hcomm
    (fun a => by rw [pow_two]; exact hsq a) (by rw [hcard]; norm_num)
  exact ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ,
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp hρ⟩

theorem card_dvd_gl8 {V : Type} [Group V] (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x * x = 1) (hcard : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ) : Nat.card G ∣ gl8 := by
  obtain ⟨f, hf⟩ := exists_embedding_gl8 hcomm hsq hcard ρ hρ
  rw [← card_GL8, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact Subgroup.card_subgroup_dvd_card f.range

theorem not_dvd_gl8_u52 : ¬ 13685760 ∣ gl8 := by
  unfold gl8; norm_num

theorem not_dvd_gl8_u43 : ¬ 3265920 ∣ gl8 := by
  unfold gl8; norm_num

end CFSG.EvenSporadicStandard.M22Std
