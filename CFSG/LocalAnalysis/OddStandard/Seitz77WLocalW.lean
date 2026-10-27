module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalMod

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four CFSG.Open Subgroup
open scoped commutatorElement

namespace Config25

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q} (c : Config25 Q V t)
  [V.Normal]

@[expose] def Wsub (C : AddSubgroup c.M) : Subgroup Q where
  carrier := {x | c.cls x ∈ C}
  mul_mem' {x y} hx hy := by
    show c.cls (x * y) ∈ C
    rw [c.cls_mul]; exact C.add_mem hx hy
  one_mem' := by
    show c.cls 1 ∈ C
    rw [c.cls_one]; exact C.zero_mem
  inv_mem' {x} hx := by
    show c.cls x⁻¹ ∈ C
    have : c.cls x⁻¹ = - c.cls x := by
      rw [eq_neg_iff_add_eq_zero, add_comm, ← c.cls_mul, mul_inv_cancel, c.cls_one]
    rw [this]; exact C.neg_mem hx

variable {c}

theorem mem_Wsub {C : AddSubgroup c.M} {x : Q} : x ∈ c.Wsub C ↔ c.cls x ∈ C := Iff.rfl

variable (c) {C : AddSubgroup c.M}

theorem V_le_Wsub : V ≤ c.Wsub C := fun v hv => by
  rw [mem_Wsub, (c.cls_eq_zero_iff v).mpr hv]
  exact C.zero_mem

theorem t_not_mem_Wsub (hinj : ∀ m ∈ C, c.π m = 0 → m = 0) : t ∉ c.Wsub C := by
  intro h
  exact c.m₀_ne (hinj _ (mem_Wsub.mp h) c.π_m₀)

theorem comm_Wsub (hB : ∀ x ∈ C, ∀ y ∈ C, c.B x y = 0) {x y : Q} (hx : x ∈ c.Wsub C)
    (hy : y ∈ c.Wsub C) : x * y = y * x := by
  have h := hB _ hx _ hy
  rw [B_cls, c.coord_eq_zero_iff (c.comm_mem_V x y)] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem index_Wsub (hsurj : ∀ v, ∃ m ∈ C, c.π m = v) (hinj : ∀ m ∈ C, c.π m = 0 → m = 0) :
    (c.Wsub C).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨t, fun b => ?_⟩
  have hnot : ¬ (b * t ∈ c.Wsub C ∧ b ∈ c.Wsub C) := by
    rintro ⟨h1, h2⟩
    rw [mem_Wsub, c.cls_mul] at h1
    rw [mem_Wsub] at h2
    exact c.t_not_mem_Wsub hinj (by
      have := C.sub_mem h1 h2
      rwa [add_sub_cancel_left] at this)
  have hone : b ∈ c.Wsub C ∨ b * t ∈ c.Wsub C := by
    obtain ⟨c₀, hc₀, hπ⟩ := hsurj (c.π (c.cls b))
    have h0 : c.π (c.cls b + c₀) = 0 := by
      rw [map_add, hπ]; exact WFacts.two _
    rcases c.π_ker _ h0 with h | h
    · left
      have : c.cls b = c₀ := by
        have := congrArg (· + c₀) h
        simpa [add_assoc, c.M_two c₀] using this
      rw [mem_Wsub, this]; exact hc₀
    · right
      have : c.cls b + c.cls t = c₀ := by
        rw [← h, ← add_assoc, c.M_two, zero_add]
      rw [mem_Wsub, c.cls_mul, this]; exact hc₀
  rcases hone with h | h
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩

theorem exists_mem_Wsub (hsurj : ∀ v, ∃ m ∈ C, c.π m = v) :
    ∀ v ∈ V, ∃ w ∈ c.Wsub C, ⁅t, w⁆ = v := by
  intro v hv
  obtain ⟨c₀, hc₀, hπ⟩ := hsurj (c.coord v)
  obtain ⟨w, rfl⟩ := c.cls_surj c₀
  refine ⟨w, hc₀, c.coord_inj (c.comm_mem w) hv ?_⟩
  rw [← hπ, π_cls]

end Config25

namespace WLocal

theorem eq_of_le_of_index_eq {Q : Type} [Group Q] {H K : Subgroup Q} (h : H ≤ K)
    (hi : H.index = K.index) (hK : K.index ≠ 0) : H = K := by
  have h1 : H.relIndex K * K.index = H.index := Subgroup.relIndex_mul_index h
  rw [hi] at h1
  have h2 : H.relIndex K * K.index = 1 * K.index := by rw [h1, one_mul]
  have h3 : H.relIndex K = 1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK) h2
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp h3)

theorem unique_index_two_comm {Q : Type} [Group Q] [Finite Q] (V : Subgroup Q)
    (hZ : Subgroup.center Q ≤ V) (hcardQ : Nat.card Q = 2 ^ 9) (hcardV : Nat.card V = 16)
    {W W' : Subgroup Q} (hW : W.index = 2) (hW' : W'.index = 2)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hc' : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x) :
    W' = W := by
  by_contra hne
  have h2 : ¬ W' ≤ W := by
    intro hle
    exact hne (eq_of_le_of_index_eq hle (by rw [hW, hW']) (by rw [hW]; norm_num))
  have h3 : W ⊔ W' = ⊤ := by
    have hdvd : (W ⊔ W').index ∣ W.index := Subgroup.index_dvd_of_le le_sup_left
    rw [hW] at hdvd
    have hle : (W ⊔ W').index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : (W ⊔ W').index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_cases h1 : (W ⊔ W').index = 1
    · exact Subgroup.index_eq_one.mp h1
    · have h2' : (W ⊔ W').index = 2 := by omega
      have hEq : W = W ⊔ W' :=
        eq_of_le_of_index_eq le_sup_left (by rw [hW, h2']) (by rw [h2']; norm_num)
      exact absurd (hEq ▸ le_sup_right : W' ≤ W) h2
  have h4 : W ⊓ W' ≤ Subgroup.center Q := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ W ⊔ W' := by rw [h3]; exact Subgroup.mem_top g
    have hle : W ⊔ W' ≤ Subgroup.centralizer {x} := by
      apply sup_le
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hc _ hx.1 _ hw
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hc' _ hx.2 _ hw
    have hg' := hle hg
    rw [Subgroup.mem_centralizer_iff] at hg'
    exact (hg' x (Set.mem_singleton x)).symm
  have h5 : W ⊓ W' ≤ V := h4.trans hZ
  have hdvd5 : V.index ∣ (W ⊓ W').index := Subgroup.index_dvd_of_le h5
  have hVidx : V.index = 32 := by
    have h := Subgroup.index_mul_card V
    rw [hcardV, hcardQ] at h
    omega
  have h6 : (W ⊓ W').index ≤ 4 := by
    have h : (W ⊓ W').index ≤ W.index * W'.index := Subgroup.index_inf_le
    rw [hW, hW'] at h
    exact h
  have hpos : (W ⊓ W').index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h7 : V.index ≤ (W ⊓ W').index := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd5
  omega

theorem map_eq_of_index_two_comm {Q : Type} [Group Q] [Finite Q] (V : Subgroup Q)
    (hZ : Subgroup.center Q ≤ V) (hcardQ : Nat.card Q = 2 ^ 9) (hcardV : Nat.card V = 16)
    {W : Subgroup Q} (hW : W.index = 2) (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (φ : MulAut Q) :
    W.map φ.toMonoidHom = W := by
  have hidx : (W.map φ.toMonoidHom).index = 2 := by
    rw [← hW]
    exact Subgroup.index_map_equiv W φ
  have hc' : ∀ x ∈ W.map φ.toMonoidHom, ∀ y ∈ W.map φ.toMonoidHom, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hc a ha b hb]
  exact unique_index_two_comm V hZ hcardQ hcardV hW hidx hc hc'

end WLocal

end CFSG.OddStandard.Seitz77
