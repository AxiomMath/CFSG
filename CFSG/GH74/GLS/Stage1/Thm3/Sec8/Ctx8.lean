module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx7

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem conj_eq_of_comm {G : Type} [Group G] {X c : G} (h : X * c = c * X) : X⁻¹ * c * X = c := by
  calc X⁻¹ * c * X = X⁻¹ * (c * X) := by group
    _ = X⁻¹ * (X * c) := by rw [← h]
    _ = c := by group

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem V_pow (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ v ∈ conjugate (Vof S K₁ W₂) h, v ^ (2 ^ k) = 1 := by
  intro v hv
  have := Basic.pow_card_of_mem hv
  rwa [conjugate_card, hk] at this

theorem A_mem (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ Aof S K₁ W₂ h) :
    ∃ a ∈ Vof S K₁ W₂, ∃ b ∈ conjugate (Vof S K₁ W₂) h, x = a * b :=
  Basic.mem_sup_of_commute' (hs.V₁V_comm hII hq hrec) hx

theorem cent_decomp (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hxS : x ∈ S)
    (hxc : ∀ a ∈ Aof S K₁ W₂ h, x * a = a * x) :
    ∃ w ∈ W₂, ∃ v ∈ conjugate (Vof S K₁ W₂) h, x = w * v ∧ w * v = v * w := by
  have hxV₁ : ∀ a ∈ Vof S K₁ W₂, x * a = a * x := fun a ha => hxc a (Subgroup.mem_sup_left ha)
  have hxV : ∀ a ∈ conjugate (Vof S K₁ W₂) h, x * a = a * x :=
    fun a ha => hxc a (Subgroup.mem_sup_right ha)
  have hxS1 : x ∈ S1 S K₁ := hs.cent_le_S1 hII hq hxS hxV₁
  have hcard := hs.card_S1_eq hII hq hrec
  have h8 : 8 * Nat.card ↥(Qof S K₂) ≤ Nat.card ↥(S1 S K₁) := by
    have h1 := hs.V₁h_card hII hq
    have h2 : 8 ≤ Nat.card ↥(Pof S K₁) := (hs.gq_P hII hq (Or.inl rfl)).eight_le_card
    rw [hcard, h1]
    exact Nat.mul_le_mul_right _ h2
  obtain ⟨hN, a, b, hab⟩ := hs.nab_quot (K := K₂) (Or.inr rfl) (hs.Q₂_le_S1 hII) h8
  obtain ⟨v, hvV, q, hqQ, hxvq⟩ := Basic.mem_sup_of_centralizes (S₁ := S1 S K₁) (Q := Qof S K₂)
    (V := conjugate (Vof S K₁ W₂) h) (hs.Q₂_le_S1 hII) (hs.V₁h_le_S1 hII hq hrec)
    (hs.V₁h_inf_Q hII hq (Or.inr rfl)) hs.cyc_V_comm hcard ⟨a, b, hab⟩ hxS1 hxV
  have hvS1 : v ∈ S1 S K₁ := hs.V₁h_le_S1 hII hq hrec hvV
  have hqeq : q = v⁻¹ * x := by rw [hxvq]; group
  have hqV₁ : ∀ a ∈ Vof S K₁ W₂, q * a = a * q := by
    intro a ha
    have h1 : a * v = v * a := hs.V₁V_comm hII hq hrec a ha v hvV
    have h2 : x * a = a * x := hxV₁ a ha
    have h3 : a * v⁻¹ = v⁻¹ * a := (Commute.inv_right (show Commute a v from h1)).eq
    rw [hqeq]
    calc v⁻¹ * x * a = v⁻¹ * (x * a) := by group
      _ = v⁻¹ * (a * x) := by rw [h2]
      _ = (v⁻¹ * a) * x := by group
      _ = (a * v⁻¹) * x := by rw [h3]
      _ = a * (v⁻¹ * x) := by group
  have hqW : q ∈ W₂ := hs.cent_Q₂_le_W₂ hII hq hqQ hqV₁
  have hwW : v * q * v⁻¹ ∈ W₂ := hs.W₂_norm v hvS1 q hqW
  have hx' : x = (v * q * v⁻¹) * v := by rw [hxvq]; group
  refine ⟨v * q * v⁻¹, hwW, v, hvV, hx', ?_⟩
  have hxv := hxV v hvV
  rw [hx'] at hxv
  have h4 : (v * q * v⁻¹) * v * v = (v * (v * q * v⁻¹)) * v := by rw [hxv]; group
  exact mul_right_cancel h4

theorem cent_pow (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {x : G}
    (hxS : x ∈ S) (hxc : ∀ a ∈ Aof S K₁ W₂ h, x * a = a * x) : x ^ (2 ^ k) = 1 ∨ x ^ (2 ^ k) = z := by
  obtain ⟨w, hwW, v, hvV, hx, hcomm⟩ := hs.cent_decomp hII hq hrec hxS hxc
  have hvk : v ^ (2 ^ k) = 1 := hs.V_pow hk v hvV
  have hxk : x ^ (2 ^ k) = w ^ (2 ^ k) := by
    rw [hx, Commute.mul_pow (show Commute w v from hcomm), hvk, mul_one]
  have hw2 : w ^ (2 ^ k) * w ^ (2 ^ k) = 1 := by
    rw [← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]
    exact hs.W₂_pow hII hq hrec hk w hwW
  rw [hxk]
  exact (hs.gq_Q₂ hII).uniq _ (pow_mem (hs.W₂_le_Q₂ hwW) _) hw2

theorem cent_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {x : G}
    (hxS : x ∈ S) (hxc : ∀ a ∈ Aof S K₁ W₂ h, x * a = a * x) (hx1 : x ^ (2 ^ k) = 1) :
    x ∈ Aof S K₁ W₂ h := by
  obtain ⟨w, hwW, v, hvV, hx, hcomm⟩ := hs.cent_decomp hII hq hrec hxS hxc
  have hvk : v ^ (2 ^ k) = 1 := hs.V_pow hk v hvV
  have hwk : w ^ (2 ^ k) = 1 := by
    have : x ^ (2 ^ k) = w ^ (2 ^ k) := by
      rw [hx, Commute.mul_pow (show Commute w v from hcomm), hvk, mul_one]
    rw [← this]; exact hx1
  have hwV₁ : w ∈ Vof S K₁ W₂ :=
    Basic.mem_of_pow_card_eq_one (V := Vof S K₁ W₂) hs.W₂_max.2.1 inf_le_left hwW
      (by rw [hk]; exact hwk)
  rw [hx]
  exact Subgroup.mul_mem_sup hwV₁ hvV

theorem mem_Vm {x : G} : x ∈ conjugate (Vof S K₁ W₂) h⁻¹ ↔ h⁻¹ * x * h ∈ Vof S K₁ W₂ := by
  rw [mem_conjugate_iff, inv_inv]

theorem Vm_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    conjugate (Vof S K₁ W₂) h⁻¹ ≤ Wsub S U := by
  intro b hb
  have hc : h⁻¹ * b * h ∈ Vof S K₁ W₂ := mem_Vm.1 hb
  have hcW : h⁻¹ * b * h ∈ Wsub S U := hs.V₁_le_W hII hq hc
  have h1 : h * (h⁻¹ * b * h) * h⁻¹ ∈ Wsub S U :=
    ((Subgroup.mem_normalizer_iff.1 hs.h_W) _).1 hcW
  have h2 : h * (h⁻¹ * b * h) * h⁻¹ = b := by group
  rwa [h2] at h1

theorem Vm_comm_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ conjugate (Vof S K₁ W₂) h⁻¹, a * b = b * a := by
  intro a ha b hb
  have hc : h⁻¹ * b * h ∈ Vof S K₁ W₂ := mem_Vm.1 hb
  have hv : h⁻¹ * a * h ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * a * h) * h⁻¹ = a := by group
    rw [e]; exact ha
  have key := hs.V₁V_comm hII hq hrec _ hc _ hv
  have e1 : h⁻¹ * b * h * (h⁻¹ * a * h) = h⁻¹ * (b * a) * h := by group
  have e2 : h⁻¹ * a * h * (h⁻¹ * b * h) = h⁻¹ * (a * b) * h := by group
  rw [e1, e2] at key
  exact (mul_left_cancel (mul_right_cancel key)).symm

theorem Vm_comm_V (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ b ∈ conjugate (Vof S K₁ W₂) h⁻¹, ∀ v ∈ conjugate (Vof S K₁ W₂) h, b * v = v * b := by
  intro b hb v hv
  have hc : h⁻¹ * b * h ∈ Vof S K₁ W₂ := mem_Vm.1 hb
  have hc₁ : h * v * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 hv
  have hcW : h⁻¹ * b * h ∈ Wsub S U := hs.V₁_le_W hII hq hc
  have h3 := hs.h_cube _ hcW
  rw [pow_three] at h3
  have hb' : h * b * h⁻¹ ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h * b * h⁻¹) * h⁻¹ =
        (h * (h * h)) * (h⁻¹ * b * h) * (h * (h * h))⁻¹ := by group
    have e2 : (h * (h * h)) * (h⁻¹ * b * h) * (h * (h * h))⁻¹ = h⁻¹ * b * h := by
      rw [h3]; group
    rw [e, e2]; exact hc
  have key := hs.V₁V_comm hII hq hrec _ hc₁ _ hb'
  have e1 : h * v * h⁻¹ * (h * b * h⁻¹) = h * (v * b) * h⁻¹ := by group
  have e2 : h * b * h⁻¹ * (h * v * h⁻¹) = h * (b * v) * h⁻¹ := by group
  rw [e1, e2] at key
  exact (mul_left_cancel (mul_right_cancel key)).symm

theorem Vm_le_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    conjugate (Vof S K₁ W₂) h⁻¹ ≤ Aof S K₁ W₂ h := by
  intro b hb
  have hbS : b ∈ S := (hs.Vm_le_W hII hq hb).1
  have hbc : ∀ a ∈ Aof S K₁ W₂ h, b * a = a * b := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
    have h1 := hs.Vm_comm_V₁ hII hq hrec a₁ ha₁ b hb
    have h2 := hs.Vm_comm_V hII hq hrec b hb a₂ ha₂
    calc b * (a₁ * a₂) = (b * a₁) * a₂ := by group
      _ = (a₁ * b) * a₂ := by rw [h1]
      _ = a₁ * (b * a₂) := by group
      _ = a₁ * (a₂ * b) := by rw [h2]
      _ = a₁ * a₂ * b := by group
  have hb1 : b ^ (2 ^ k) = 1 := by
    have := Basic.pow_card_of_mem hb
    rwa [conjugate_card, hk] at this
  exact hs.cent_mem_A hII hq hrec hk hbS hbc hb1

theorem A_conj (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {a : G}
    (ha : a ∈ Aof S K₁ W₂ h) :
    h * a * h⁻¹ ∈ Aof S K₁ W₂ h ∧ h⁻¹ * a * h ∈ Aof S K₁ W₂ h := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
  have hVm := hs.Vm_le_A hII hq hrec hk
  have p1 : h * a₁ * h⁻¹ ∈ Aof S K₁ W₂ h := by
    apply hVm
    rw [mem_Vm]
    have e : h⁻¹ * (h * a₁ * h⁻¹) * h = a₁ := by group
    rw [e]; exact ha₁
  have p2 : h * a₂ * h⁻¹ ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left (mem_conjugate_iff.1 ha₂)
  have p3 : h⁻¹ * a₁ * h ∈ Aof S K₁ W₂ h := by
    apply Subgroup.mem_sup_right
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * a₁ * h) * h⁻¹ = a₁ := by group
    rw [e]; exact ha₁
  have p4 : h⁻¹ * a₂ * h ∈ Aof S K₁ W₂ h := by
    apply hVm
    rw [mem_Vm]
    have hc : h * a₂ * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 ha₂
    have hcW : h * a₂ * h⁻¹ ∈ Wsub S U := hs.V₁_le_W hII hq hc
    have h3 := hs.h_cube _ hcW
    rw [pow_three] at h3
    have e : h⁻¹ * (h⁻¹ * a₂ * h) * h =
        (h * (h * h))⁻¹ * (h * a₂ * h⁻¹) * (h * (h * h)) := by group
    rw [e, conj_eq_of_comm h3]
    exact hc
  constructor
  · have e : h * (a₁ * a₂) * h⁻¹ = (h * a₁ * h⁻¹) * (h * a₂ * h⁻¹) := by group
    rw [e]; exact mul_mem p1 p2
  · have e : h⁻¹ * (a₁ * a₂) * h = (h⁻¹ * a₁ * h) * (h⁻¹ * a₂ * h) := by group
    rw [e]; exact mul_mem p3 p4

theorem A_normedBy_h (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    NormedBy (Aof S K₁ W₂ h) (zpowers h) := by
  have hh : h ∈ normalizer (Aof S K₁ W₂ h : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact (hs.A_conj hII hq hrec hk hy).1
    · intro hy
      have := (hs.A_conj hII hq hrec hk hy).2
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rwa [e] at this
  intro x hx a ha
  have hxn : x ∈ normalizer (Aof S K₁ W₂ h : Set G) := (zpowers_le.2 hh) hx
  exact ((Subgroup.mem_normalizer_iff.1 hxn) a).1 ha

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
