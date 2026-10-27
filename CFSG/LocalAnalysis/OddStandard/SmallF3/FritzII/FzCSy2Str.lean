module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenRank

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

structure FzCSy2Str (t rho : G) (Z E W Q : Subgroup G) : Prop where
  ZE : Z ≤ E
  EW : E ≤ W
  WQ : W ≤ Q
  card_Z : Nat.card Z = 4
  card_E : Nat.card E = 16
  card_W : Nat.card W = 32
  card_Q : Nat.card Q = 128
  W_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  W_rank : S4A.RankLE W 3
  t_mem : t ∈ W
  t_sq : t ^ 2 = 1
  t_notin_E : t ∉ E
  W_split : ∀ w ∈ W, w ∈ E ∨ t * w ∈ E
  E_sq : ∀ e ∈ E, e ^ 2 ∈ Z
  Z_sq : ∀ z ∈ Z, z ^ 2 = 1
  Z_sqrt : ∀ z ∈ Z, ∃ e ∈ E, e ^ 2 = z
  E_invol : ∀ e ∈ E, e ^ 2 = 1 → e ∈ Z
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ W
  Q_sq : ∀ q ∈ Q, q ^ 2 ∈ W
  Q_Z : ∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ = z
  Q_t : ∀ n ∈ Q, n ∉ W → n * t * n⁻¹ ≠ t
  rho_ord : rho ^ 3 = 1
  rho_t : rho * t * rho⁻¹ = t
  rho_nrm_E : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E
  rho_nrm_W : ∀ w ∈ W, rho * w * rho⁻¹ ∈ W
  rho_nrm_Q : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q
  rho_Q : ∀ q ∈ Q, rho * q * rho⁻¹ = q → q = 1 ∨ q = t
  rho_QW : ∀ q ∈ Q, rho * q * rho⁻¹ * q⁻¹ ∈ W → q ∈ W

namespace FzCSy2Str

variable {t rho : G} {Z E W Q : Subgroup G}

theorem W_nrm (hs : FzCSy2Str t rho Z E W Q) : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W := by
  intro q hq w hw
  have h1 : q * w * q⁻¹ = ⁅q, w⁆ * w := by
    rw [commutatorElement_def]
    group
  rw [h1]
  exact W.mul_mem (hs.Q_comm q hq w (hs.WQ hw)) hw

theorem rho_nrm_Z (hs : FzCSy2Str t rho Z E W Q) : ∀ z ∈ Z, rho * z * rho⁻¹ ∈ Z := by
  intro z hz
  refine hs.E_invol _ (hs.rho_nrm_E z (hs.ZE hz)) ?_
  have h1 : (rho * z * rho⁻¹) ^ 2 = rho * z ^ 2 * rho⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [h1, hs.Z_sq z hz]
  group

theorem t_comm (hs : FzCSy2Str t rho Z E W Q) {w : G} (hw : w ∈ W) : t * w = w * t :=
  hs.W_comm t hs.t_mem w hw

theorem W_sq (hs : FzCSy2Str t rho Z E W Q) : ∀ w ∈ W, w ^ 2 ∈ Z := by
  intro w hw
  rcases hs.W_split w hw with hwE | htwE
  · exact hs.E_sq w hwE
  · have h1 : (t * w) ^ 2 = w ^ 2 := by
      rw [pow_two, pow_two]
      calc t * w * (t * w) = t * (w * t) * w := by group
        _ = t * (t * w) * w := by rw [hs.t_comm hw]
        _ = (t * t) * (w * w) := by group
        _ = w * w := by rw [← pow_two t, hs.t_sq, one_mul]
    rw [← h1]
    exact hs.E_sq _ htwE

theorem W_exp (hs : FzCSy2Str t rho Z E W Q) : ∀ w ∈ W, w ^ 4 = 1 := by
  intro w hw
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact hs.Z_sq _ (hs.W_sq w hw)

theorem W_invol (hs : FzCSy2Str t rho Z E W Q) :
    ∀ w ∈ W, w ^ 2 = 1 → w ∈ Z ∨ t * w ∈ Z := by
  intro w hw hw2
  rcases hs.W_split w hw with hwE | htwE
  · exact Or.inl (hs.E_invol w hwE hw2)
  · refine Or.inr (hs.E_invol _ htwE ?_)
    rw [pow_two]
    calc t * w * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [hs.t_comm hw]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [← pow_two t, ← pow_two w, hs.t_sq, hw2, one_mul]

theorem pgroup (hs : FzCSy2Str t rho Z E W Q) : IsPGroup 2 Q :=
  IsPGroup.of_card (n := 7) (by rw [hs.card_Q]; norm_num)

theorem rho_conj3 (hs : FzCSy2Str t rho Z E W Q) (x : G) :
    rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ = x := by
  have h3 : rho * rho * rho = 1 := by
    have h1 := hs.rho_ord
    rw [pow_succ, pow_two] at h1
    exact h1
  calc rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹
      = (rho * rho * rho) * x * (rho * rho * rho)⁻¹ := by group
    _ = x := by rw [h3]; group

end FzCSy2Str

end CFSG.OddStandard.SmallF3.FritzII
