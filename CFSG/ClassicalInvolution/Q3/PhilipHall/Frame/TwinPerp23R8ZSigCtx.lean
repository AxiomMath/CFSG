module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Members
public import CFSG.ClassicalInvolution.Sp62Rec.I1.MemberFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr

section Finite

@[expose] def E4MoveW (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    ∀ a : M, a * a = 1 → a ≠ 1 → a ≠ s → (∀ x ∈ K, a * x = x * a) →
      ∃ c : M, c ^ 3 = 1 ∧ c * s = s * c ∧ c * a ≠ a * c

@[expose] def E4ModelMove : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) → E4MoveW M

@[expose] def MFA : Prop :=
  ∀ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool) (v : Wr 6), v ∈ memAt β hβ b → v ≠ 1 →
    v * v = 1 → ∃ A : Subgroup (Wr 6), A ≤ aeSub 6 ∧ IsElemAbelian 2 A ∧ 2 ^ 2 ≤ Nat.card A ∧
      ∀ a ∈ A, a ≠ 1 → ∃ y ∈ aeSub 6, a = y * v * y⁻¹

theorem mFL_holds :
    ∀ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool) (w : Wr 6), Odd (orderOf w) →
      (∀ x ∈ memAt β hβ b, w * x = x * w) → w = 1 := fun _ hβ b _ hodd hw =>
  CFSG.ClassicalInvolution.Sp62Rec.I1.eq_one_of_centralizes_member hβ b hw hodd

theorem mFA_holds : MFA := fun _ hβ b _ hv hv1 hv2 =>
  CFSG.ClassicalInvolution.Sp62Rec.I1.exists_four_group hβ b hv hv1 hv2

theorem mFS_holds :
    ∀ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool) (v : Wr 6), v ∈ memAt β hβ b → v ≠ 1 →
      v * v = 1 → ∃ g ∈ aeSub 6, g * v ≠ v * g := fun _ hβ b _ hv hv1 hv2 =>
  CFSG.ClassicalInvolution.Sp62Rec.I1.exists_noncentral hβ b hv hv1 hv2

end Finite


section Ctx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

structure ZHat (R : Subgroup Y) (e : Y) : Prop where
  e_mem : e ∈ rLayer (Om R) e
  normal : ∀ h ∈ Subgroup.centralizer ({e} : Set Y), conjSub h (rLayer (Om R) e) = rLayer (Om R) e
  odd : oddCoreOf (rLayer (Om R) e) = ⊥
  labels : ∃ f : ↥(rLayer (Om R) e) →* Wr 6, Function.Injective f ∧ f.range = aeSub 6 ∧
    Sp62Rec.MemberLabels (Om R) (rLayer (Om R) e) f ∧
    ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∃ w : Wr 6, Sp62Rec.ActsOnE f h w

structure ZCtx (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g x : Y) : Prop where
  cfg : P23Cfg n Y R S t K' W u e g
  two : ∀ J ∈ Om R, IsPGroup 2 J
  ae6 : SecAE R e 6
  eO2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set Y))).map
    (Subgroup.centralizer ({t} : Set Y)).subtype
  hat : ZHat R e
  ne : conjSub x (rLayer (Om R) e) ≠ rLayer (Om R) e
  top : p23XE R e x ≠ ⊤

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem card_lt : Nat.card (p23XE R e x) < n := by
  have hC := H.cfg.std.perp.core
  haveI := hC.simple
  rw [← hC.card]
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
    H.top ((Subgroup.card_eq_iff_eq_top _).mp heq)

end ZCtx

end Ctx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
