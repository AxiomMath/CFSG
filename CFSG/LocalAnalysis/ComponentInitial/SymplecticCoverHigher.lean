module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigherCore
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher

open Subgroup CFSG.Assembly.LowTwoRank BinarySymplecticSix

theorem ker_eq_bot_of_statedSp {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {n : ℕ}
    (hn : 4 ≤ n) (θ : E →* StatedSp n (ZMod 2)) (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ center E) (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  set D := powers hC 2 with hD
  have : D.Normal := normal_of_le_center ((powers_le hC 2).trans hC)
  have hDle : D ≤ θ.ker := powers_le hC 2
  set θ' := QuotientGroup.lift D θ hDle with hθ'
  have hθ'mk : ∀ y : E, θ' (y : E ⧸ D) = θ y := fun y => QuotientGroup.lift_mk _ _ _
  have hθ'surj : Function.Surjective θ' := by
    intro x
    obtain ⟨y, rfl⟩ := hθ x
    exact ⟨y, hθ'mk y⟩
  have hθ'C : θ'.ker ≤ center (E ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hθ'mk] at hc
      refine mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (hC hc) g]
  have hsq : ∀ c, θ' c = 1 → c ^ 2 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθ'mk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  have hbot := ker_eq_bot_of_sq hθ'surj hθ'C hn hsq
  have hsqr : ∀ x ∈ θ.ker, ∃ y ∈ θ.ker, x = y ^ 2 := fun x hx => by
    have hmem : (x : E ⧸ D) ∈ θ'.ker := by
      rw [MonoidHom.mem_ker, hθ'mk]
      exact hx
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hexp := sq_eq_one_of_forall_sq_eq_pow_four hC h2 fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hsqr x hx
    exact ⟨y, hy, by rw [← pow_mul]⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hsqr x hx
  exact mem_bot.mpr (hexp y hy)

theorem even_higher_symplectic_prime_field_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {n : ℕ}
    (hn : 4 ≤ n) (hJ : CFSG.Blueprint.LieModel J .PSp n 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel_n hJ
  set η' : E →* StatedSp n (ZMod 2) := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_statedSp hn η' (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
