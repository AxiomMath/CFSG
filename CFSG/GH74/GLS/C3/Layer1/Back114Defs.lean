module

public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

structure IsAConfigW {G : Type} [Group G] [Finite G] (n : ℕ) (x : G) (K T Q S : Subgroup G) (a : G) :
    Prop where
  twoTerminal : IsTwoTerminal x K
  terminal : IsTerminalPair 2 x K
  kbar : Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n))
  normalInC : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hQ : Q = T ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (CxK x K)
  card_Q : Nat.card ↥Q = 4
  elemQ : IsElementaryAbelian 2 ↥Q
  sylowS : IsSylowOf 2 S ⊤
  T_lt_S : T < S
  a_mem : a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T
  cond6 : (∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) →
    ∀ u ∈ Q, u ≠ 1 → IsSylowOf 2 T (centralizer ({u} : Set G))
  quotientType : ∃ ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin n),
    ψ.ker = (CxK x K).subgroupOf (centralizer ({x} : Set G))
  fiveCase : n = 5 → ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ K) ⊔ Q ⊔ zpowers y ∧
    ∃ q ∈ Q, y * q ≠ q * y

@[expose] def Ysub {G : Type} [Group G] (x : G) (K T : Subgroup G) (a : G) : Subgroup G :=
  (T ⊓ K).map (MulAut.conj a).toMonoidHom ⊔ zpowers (a * x * a⁻¹)

section Basic

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfigW

theorem x_order (h : IsAConfigW n x K T Q S a) : orderOf x = 2 := h.twoTerminal.1.1

theorem x_sq (h : IsAConfigW n x K T Q S a) : x ^ 2 = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h.x_order] at this

theorem x_ne_one (h : IsAConfigW n x K T Q S a) : x ≠ 1 := by
  intro hx
  have := h.x_order
  rw [hx, orderOf_one] at this
  omega

theorem K_le_C (h : IsAConfigW n x K T Q S a) : K ≤ centralizer ({x} : Set G) :=
  h.twoTerminal.1.2.2.1

theorem T_le_C (h : IsAConfigW n x K T Q S a) : T ≤ centralizer ({x} : Set G) := h.sylowT.le

theorem Q_le_T (h : IsAConfigW n x K T Q S a) : Q ≤ T := by
  rw [h.hQ]; exact inf_le_left

theorem Q_le_CxK (h : IsAConfigW n x K T Q S a) : Q ≤ CxK x K := by
  rw [h.hQ]; exact inf_le_right

omit [Finite G] in
theorem CxK_le_C : CxK x K ≤ centralizer ({x} : Set G) := by
  unfold CxK; exact inf_le_left

theorem x_mem_T (h : IsAConfigW n x K T Q S a) : x ∈ T :=
  C3.Layer1.Back.mem_of_isSylowOf_of_central h.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) h.x_order

theorem x_mem_CxK (h : IsAConfigW n x K T Q S a) : x ∈ CxK x K := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (h.K_le_C hk)).symm
  · unfold pPrimeCoreOf
    intro y hy
    obtain ⟨y', -, rfl⟩ := hy
    exact y'.2

theorem x_mem_Q (h : IsAConfigW n x K T Q S a) : x ∈ Q := by
  rw [h.hQ]
  exact ⟨h.x_mem_T, h.x_mem_CxK⟩

end IsAConfigW

end Basic

end CFSG.GH74.GLS
