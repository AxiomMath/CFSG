module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2d
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Ot

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

abbrev K1 : List (Perm (Fin 4)) := [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3]

abbrev D8 : List (Perm (Fin 4)) := [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3,
  swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3 * swap 0 1,
  swap 0 2 * swap 1 3 * swap 2 3]

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

theorem t_mem_B (S : A7Base X) : S.t ∈ S.B := subset_closure (by simp)

namespace Case2

variable (C : S.Case2)

theorem conj_t_of_mem_normalizer {n : X} (hn : n ∈ normalizer (S.data.T : Set X)) :
    n * S.t * n⁻¹ = S.t ∨ n * S.t * n⁻¹ = S.t * C.f :=
  (C.fusion _ (S.conj_mem_B hn S.t_mem_B)).mp ⟨n, rfl⟩

theorem conj_tf_of_mem_normalizer {n : X} (hn : n ∈ normalizer (S.data.T : Set X)) :
    n * (S.t * C.f) * n⁻¹ = S.t ∨ n * (S.t * C.f) * n⁻¹ = S.t * C.f := by
  have hb : n * (S.t * C.f) * n⁻¹ ∈ S.B := S.conj_mem_B hn (mul_mem S.t_mem_B C.f_mem)
  refine (C.fusion _ hb).mp ?_
  rw [conjTo_conj_iff]
  exact (C.fusion _ (mul_mem S.t_mem_B C.f_mem)).mpr (Or.inr rfl)

@[expose] noncomputable def ofT₁ {n : X} (hn : n ∈ C.T₁) : normalizer (S.E C.yb : Set X) :=
  ⟨n, C.T₁_le_normalizer hn⟩

theorem π_mem_K1 {n : X} (hn : n ∈ C.T₁) : C.π (C.ofT₁ hn) ∈ K1 := by
  have h0 : C.π (C.ofT₁ hn) 0 = 0 ∨ C.π (C.ofT₁ hn) 0 = 1 := by
    have h := C.π_spec (C.ofT₁ hn) 0
    change n * C.e 0 * n⁻¹ = _ at h
    rcases C.conj_t_of_mem_normalizer (C.T₁_le hn) with h1 | h1
    · left
      exact C.e_injective (by rw [← h, C.e_zero, h1])
    · right
      exact C.e_injective (by rw [← h, C.e_zero, h1, C.e_one])
  have h1 : C.π (C.ofT₁ hn) 1 = 0 ∨ C.π (C.ofT₁ hn) 1 = 1 := by
    have h := C.π_spec (C.ofT₁ hn) 1
    change n * C.e 1 * n⁻¹ = _ at h
    rcases C.conj_tf_of_mem_normalizer (C.T₁_le hn) with h2 | h2
    · left
      exact C.e_injective (by rw [← h, C.e_one, h2, C.e_zero])
    · right
      exact C.e_injective (by rw [← h, C.e_one, h2])
  generalize C.π (C.ofT₁ hn) = σ at h0 h1
  revert σ
  decide

theorem x_mem_T₁ : S.x ∈ C.T₁ := C.T_le S.x_mem.1

theorem π_x : C.π (C.ofT₁ C.x_mem_T₁) = swap 2 3 := by
  apply C.π_eq
  have huT : C.u ∈ S.data.T := C.E_le_T C.u_mem
  have hxu := S.conj_x_of_not_mem_B huT C.u_sq C.u_not_mem
  have hxB : ∀ b ∈ S.B, S.x * b * S.x⁻¹ = b := fun b hb => by
    rw [← S.central_of_mem_B hb S.x_mem.1]
    group
  intro i
  change S.x * C.e i * S.x⁻¹ = _
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 3)]
    rw [C.e_zero, hxB _ S.t_mem_B]
  · simp only [Fin.mk_one, Fin.isValue, swap_apply_of_ne_of_ne (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)]
    rw [C.e_one, hxB _ (mul_mem S.t_mem_B C.f_mem)]
  · show S.x * C.e 2 * S.x⁻¹ = C.e ((swap (2 : Fin 4) 3) 2)
    rw [swap_apply_left, C.e_two, C.e_three, hxu]
  · show S.x * C.e 3 * S.x⁻¹ = C.e ((swap (2 : Fin 4) 3) 3)
    rw [swap_apply_right, C.e_two, C.e_three]
    calc S.x * (S.z * C.u) * S.x⁻¹ = S.z * (S.x * C.u * S.x⁻¹) := by
          rw [show S.x * (S.z * C.u) * S.x⁻¹ = (S.x * S.z) * C.u * S.x⁻¹ by group,
            ← S.z_comm_of_mem_T S.x_mem.1]
          group
      _ = C.u := by rw [hxu, ← mul_assoc, ← pow_two, S.z_sq, one_mul]

theorem exists_w : ∃ (n : X) (hn : n ∈ C.T₁), n ∉ S.data.T ∧ C.π (C.ofT₁ hn) 0 = 1 := by
  have hlt : S.data.T < C.T₁ := by
    refine lt_of_le_of_ne C.T_le fun h => ?_
    have := C.card_T₁
    rw [← h] at this
    have hpos : 0 < Nat.card S.data.T := Nat.card_pos
    omega
  obtain ⟨n, hn, hnT⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨n, hn, hnT, ?_⟩
  have hnt : n * S.t * n⁻¹ ≠ S.t := by
    intro h
    have hnC : n ∈ centralizer ({S.t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc n * S.t = n * S.t * n⁻¹ * n := by group
        _ = S.t * n := by rw [h]
    have hle : S.data.T ⊔ zpowers n ≤ C.T₁ := sup_le C.T_le (zpowers_le.mpr hn)
    have heq := S.eq_T_of_le' (C.T₁_p.to_le hle) le_sup_left
      (sup_le S.data.T_le_centralizer (zpowers_le.mpr hnC))
    exact hnT (heq ▸ mem_sup_right (mem_zpowers n))
  have h := C.π_spec (C.ofT₁ hn) 0
  change n * C.e 0 * n⁻¹ = _ at h
  rcases C.conj_t_of_mem_normalizer (C.T₁_le hn) with h1 | h1
  · exact absurd h1 hnt
  · exact C.e_injective (by rw [← h, C.e_zero, h1, C.e_one])

section V

variable {V : Subgroup X} (hT₁V : C.T₁ ≤ V) (hVN : V ≤ normalizer (S.E C.yb : Set X))
  (hVc : Nat.card V = 4 * Nat.card S.data.T)

@[expose] noncomputable def ofV {v : X} (hv : v ∈ V) : normalizer (S.E C.yb : Set X) := ⟨v, hVN hv⟩

include hT₁V hVc in
theorem conj_mem_T₁ {v : X} (hv : v ∈ V) {n : X} (hn : n ∈ C.T₁) : v * n * v⁻¹ ∈ C.T₁ := by
  have hidx : (C.T₁.subgroupOf V).index = 2 := by
    have h := relIndex_mul_card (H := C.T₁) (K := V)
    rw [inf_of_le_left hT₁V, hVc, C.card_T₁] at h
    have hpos : 0 < Nat.card S.data.T := Nat.card_pos
    change C.T₁.relIndex V = 2
    nlinarith
  have key := mul_mem_iff_of_index_two hidx (a := ⟨v * n, mul_mem hv (hT₁V hn)⟩)
    (b := ⟨v⁻¹, inv_mem hv⟩)
  have key2 := mul_mem_iff_of_index_two hidx (a := ⟨v, hv⟩) (b := ⟨n, hT₁V hn⟩)
  have hnH : (⟨n, hT₁V hn⟩ : V) ∈ C.T₁.subgroupOf V := hn
  have hinv : (⟨v⁻¹, inv_mem hv⟩ : V) ∈ C.T₁.subgroupOf V ↔ (⟨v, hv⟩ : V) ∈ C.T₁.subgroupOf V := by
    rw [mem_subgroupOf, mem_subgroupOf]
    exact inv_mem_iff
  have : (⟨v * n, mul_mem hv (hT₁V hn)⟩ * ⟨v⁻¹, inv_mem hv⟩ : V) ∈ C.T₁.subgroupOf V := by
    rw [key, hinv]
    have : (⟨v, hv⟩ * ⟨n, hT₁V hn⟩ : V) = ⟨v * n, mul_mem hv (hT₁V hn)⟩ := rfl
    rw [← this, key2]
    tauto
  exact this

include hT₁V hVc in
theorem π_mem_D8 {v : X} (hv : v ∈ V) : C.π (C.ofV hVN hv) ∈ D8 := by
  have hm := C.conj_mem_T₁ hT₁V hVc hv C.x_mem_T₁
  have hK := C.π_mem_K1 hm
  have heq : C.ofT₁ hm = C.ofV hVN hv * C.ofT₁ C.x_mem_T₁ * (C.ofV hVN hv)⁻¹ := rfl
  rw [heq, map_mul, map_mul, map_inv, C.π_x] at hK
  generalize C.π (C.ofV hVN hv) = σ at hK
  revert σ
  decide

include hT₁V hVc in
theorem exists_move (hVp : IsPGroup 2 V) : ∃ (v : X) (hv : v ∈ V), C.π (C.ofV hVN hv) 0 ≠ 0 ∧
    C.π (C.ofV hVN hv) 0 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hTVC : S.data.T ≤ V ⊓ centralizer ({S.t} : Set X) :=
    le_inf (C.T_le.trans hT₁V) S.data.T_le_centralizer
  have heq : V ⊓ centralizer ({S.t} : Set X) = S.data.T :=
    S.eq_T_of_le' (hVp.to_le inf_le_left) hTVC inf_le_right
  have horb : {b | ∃ g ∈ V, g * S.t * g⁻¹ = b} ⊆ ({S.t, S.t * C.f} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    have h := C.π_spec (C.ofV hVN hg) 0
    change g * C.e 0 * g⁻¹ = _ at h
    rw [C.e_zero] at h
    by_cases h0 : C.π (C.ofV hVN hg) 0 = 0
    · rw [h, h0, C.e_zero]
      simp
    · rw [h, hcon g hg h0, C.e_one]
      simp
  have hidx := relIndex_inf_centralizer_eq_ncard V S.t
  have hle : (V ⊓ centralizer ({S.t} : Set X)).relIndex V ≤ 2 := by
    rw [hidx]
    calc _ ≤ ({S.t, S.t * C.f} : Set X).ncard := Set.ncard_le_ncard horb (Set.toFinite _)
      _ ≤ ({S.t * C.f} : Set X).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hmul := relIndex_mul_card (H := V ⊓ centralizer ({S.t} : Set X)) (K := V)
  rw [inf_of_le_left inf_le_left, hVc] at hmul
  rw [heq] at hmul hle
  have hpos : 0 < Nat.card S.data.T := Nat.card_pos
  nlinarith

include hT₁V hVc in
theorem exists_s₀ (hVp : IsPGroup 2 V) :
    ∃ (s₀ : X) (hs : s₀ ∈ V), C.π (C.ofV hVN hs) = swap 0 2 * swap 1 3 := by
  obtain ⟨v, hv, hv0, hv1⟩ := C.exists_move hT₁V hVN hVc hVp
  obtain ⟨w, hw, -, hw0⟩ := C.exists_w
  have hwK := C.π_mem_K1 hw
  have hvD := C.π_mem_D8 hT₁V hVN hVc hv
  have hxV := hT₁V C.x_mem_T₁
  have hwV := hT₁V hw
  have key : ∀ σ ∈ D8, σ 0 ≠ 0 → σ 0 ≠ 1 → ∀ τ ∈ K1, τ 0 = 1 →
      σ = swap 0 2 * swap 1 3 ∨ σ * swap 2 3 = swap 0 2 * swap 1 3 ∨
        σ * τ = swap 0 2 * swap 1 3 ∨ σ * (τ * swap 2 3) = swap 0 2 * swap 1 3 := by decide
  have hπx : C.π (C.ofV hVN hxV) = swap 2 3 := C.π_x
  have hπw : C.π (C.ofV hVN hwV) = C.π (C.ofT₁ hw) := rfl
  rcases key _ hvD hv0 hv1 _ hwK hw0 with h | h | h | h
  · exact ⟨v, hv, h⟩
  · refine ⟨v * S.x, mul_mem hv hxV, ?_⟩
    have : C.ofV hVN (mul_mem hv hxV) = C.ofV hVN hv * C.ofV hVN hxV := rfl
    rw [this, map_mul, hπx, h]
  · refine ⟨v * w, mul_mem hv hwV, ?_⟩
    have : C.ofV hVN (mul_mem hv hwV) = C.ofV hVN hv * C.ofV hVN hwV := rfl
    rw [this, map_mul, hπw, h]
  · refine ⟨v * (w * S.x), mul_mem hv (mul_mem hwV hxV), ?_⟩
    have : C.ofV hVN (mul_mem hv (mul_mem hwV hxV)) =
        C.ofV hVN hv * (C.ofV hVN hwV * C.ofV hVN hxV) := rfl
    rw [this, map_mul, map_mul, hπw, hπx, h]

theorem π_of_mem_E {g : X} (hg : g ∈ S.E C.yb) :
    C.π ⟨g, Subgroup.le_normalizer hg⟩ = 1 := by
  rw [C.π_eq_one_iff]
  intro e he
  change g * e * g⁻¹ = e
  rw [C.comm hg he]
  group

end V

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
