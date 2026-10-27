module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public noncomputable section

namespace CFSG.Alternating.Multipliers

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

section SqLift

variable {P Q : Type*} [Group P] [Group Q]

open Classical in
def sqLift (f : P →* Q) (q : Q) : P :=
  if h : ∃ y, f y = q ∧ y ^ 2 = 1 then h.choose else 1

theorem eq_one_of_sq_eq_one_of_odd {K : Type*} [Group K] (hK : Odd (Nat.card K)) {k : K}
    (hk : k ^ 2 = 1) : k = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero fun h => by simp [h] at hK
  have h1 : orderOf k ∣ Nat.gcd (Nat.card K) 2 :=
    Nat.dvd_gcd (orderOf_dvd_natCard k) (orderOf_dvd_of_pow_eq_one hk)
  rw [show Nat.gcd (Nat.card K) 2 = 1 from Nat.coprime_two_right.mpr hK, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact h1

variable {f : P →* Q}

theorem eq_of_sq_eq_one (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {y y' : P}
    (h : f y = f y') (hy : y ^ 2 = 1) (hy' : y' ^ 2 = 1) : y = y' := by
  have hk : y⁻¹ * y' ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc : Commute y (y⁻¹ * y') := mem_center_iff.mp (hK hk) y
  have hk2 : (y⁻¹ * y') ^ 2 = 1 := by
    have e : y' = y * (y⁻¹ * y') := by rw [mul_inv_cancel_left]
    rw [e, hc.mul_pow, hy, one_mul] at hy'
    exact hy'
  have h1 : (⟨y⁻¹ * y', hk⟩ : f.ker) = 1 :=
    eq_one_of_sq_eq_one_of_odd hodd (Subtype.ext (by simpa using hk2))
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem exists_lift_sq_eq_one (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q : Q}
    (hq : q ∈ f.range) (hq2 : q ^ 2 = 1) : ∃ y, f y = q ∧ y ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := hq
  have hy2 : y ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hq2]
  obtain ⟨l, hl⟩ := (Nat.Coprime.pow_left_bijective (n := 2) (G := f.ker)
    (Nat.coprime_two_right.mpr hodd)).2 ⟨y ^ 2, hy2⟩
  have hl' : (l : P) ^ 2 = y ^ 2 := by simpa using congrArg Subtype.val hl
  have hc : Commute y (l : P)⁻¹ := mem_center_iff.mp (hK (inv_mem l.2)) y
  refine ⟨y * (l : P)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp l.2, inv_one, mul_one]
  · rw [hc.mul_pow, inv_pow, hl', mul_inv_cancel]

theorem sqLift_spec (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q : Q}
    (hq : q ∈ f.range) (hq2 : q ^ 2 = 1) : f (sqLift f q) = q ∧ sqLift f q ^ 2 = 1 := by
  have h := exists_lift_sq_eq_one hK hodd hq hq2
  rw [sqLift, dite_eq_left h]
  exact h.choose_spec

theorem eq_sqLift (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q : Q} {y : P}
    (hy : f y = q) (hy2 : y ^ 2 = 1) : y = sqLift f q := by
  have h : ∃ y, f y = q ∧ y ^ 2 = 1 := ⟨y, hy, hy2⟩
  have hs : f (sqLift f q) = q ∧ sqLift f q ^ 2 = 1 := by
    rw [sqLift, dite_eq_left h]
    exact h.choose_spec
  exact eq_of_sq_eq_one hK hodd (hy.trans hs.1.symm) hy2 hs.2

theorem sqLift_inv (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q : Q}
    (hq : q ∈ f.range) (hq2 : q ^ 2 = 1) : (sqLift f q)⁻¹ = sqLift f q :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, (sqLift_spec hK hodd hq hq2).2])

theorem sqLift_conj (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) (g : P) {q : Q}
    (hq : q ∈ f.range) (hq2 : q ^ 2 = 1) :
    g * sqLift f q * g⁻¹ = sqLift f (f g * q * (f g)⁻¹) := by
  obtain ⟨h1, h2⟩ := sqLift_spec hK hodd hq hq2
  refine eq_sqLift hK hodd ?_ ?_
  · rw [map_mul, map_mul, map_inv, h1]
  · rw [conj_pow, h2, mul_one, mul_inv_cancel]

theorem sqLift_mul_comm (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q₁ q₂ : Q}
    (h₁ : q₁ ∈ f.range) (h₁2 : q₁ ^ 2 = 1) (h₂ : q₂ ∈ f.range) (h₂2 : q₂ ^ 2 = 1)
    (hc : q₁ * q₂ = q₂ * q₁) : sqLift f q₁ * sqLift f q₂ = sqLift f q₂ * sqLift f q₁ := by
  have e := sqLift_conj hK hodd (sqLift f q₁) h₂ h₂2
  rw [(sqLift_spec hK hodd h₁ h₁2).1, hc, mul_inv_cancel_right] at e
  exact mul_inv_eq_iff_eq_mul.mp e

theorem sqLift_mul (hK : f.ker ≤ center P) (hodd : Odd (Nat.card f.ker)) {q₁ q₂ : Q}
    (h₁ : q₁ ∈ f.range) (h₁2 : q₁ ^ 2 = 1) (h₂ : q₂ ∈ f.range) (h₂2 : q₂ ^ 2 = 1)
    (hc : q₁ * q₂ = q₂ * q₁) : sqLift f q₁ * sqLift f q₂ = sqLift f (q₁ * q₂) := by
  obtain ⟨e₁, s₁⟩ := sqLift_spec hK hodd h₁ h₁2
  obtain ⟨e₂, s₂⟩ := sqLift_spec hK hodd h₂ h₂2
  refine eq_sqLift hK hodd (by rw [map_mul, e₁, e₂]) ?_
  rw [Commute.mul_pow (sqLift_mul_comm hK hodd h₁ h₁2 h₂ h₂2 hc), s₁, s₂, one_mul]

end SqLift

section Swaps

variable {α : Type*} [DecidableEq α]

theorem conj_swap_mul_swap' (σ : Perm α) (u v w z : α) :
    σ * (swap u v * swap w z) * σ⁻¹ = swap (σ u) (σ v) * swap (σ w) (σ z) := by
  rw [swap_apply_apply, swap_apply_apply]
  group

theorem swap_mul_swap_mem_alternatingGroup [Fintype α] {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) : swap a b * swap c d ∈ alternatingGroup α := by
  rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]
  rfl

theorem commute_mul_mul_left {G : Type*} [Group G] {x y z : G} (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z) : Commute (x * y) (y * z) :=
  (hxy.mul_right hxz).mul_left ((Commute.refl y).mul_right hyz)

theorem commute_mul_mul_right {G : Type*} [Group G] {x y z : G} (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z) : Commute (x * y) (z * y) :=
  (hxz.mul_right hxy).mul_left (hyz.mul_right (Commute.refl y))

theorem swap_mul_swap_mul_swap_mul_swap_cancel {o a l b u v : α} (hlu : l ≠ u) (hlv : l ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) :
    swap o a * swap l b * (swap u v * swap l b) = swap o a * swap u v := by
  rw [mul_assoc, ← mul_assoc (swap l b), swap_mul_swap_comm_of_ne hlu hlv (Ne.symm hbu) hbv,
    mul_assoc, swap_mul_self, mul_one]

theorem exists_pair_notMem {N : ℕ} (s : Finset (Fin N)) (hs : s.card + 2 ≤ N) :
    ∃ b d, b ∉ s ∧ d ∉ s ∧ b ≠ d := by
  classical
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := insert b s)
    (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Finset.card_insert_le _ _).trans_lt (by omega))
  exact ⟨b, d, hb, fun h => hd (Finset.mem_insert_of_mem h),
    fun h => hd (h ▸ Finset.mem_insert_self _ _)⟩

end Swaps

section Lift3

variable {P : Type*} [Group P] {m : ℕ}

def lift3 (ρ : P →* Perm (Fin (m + 2))) (a b d : Fin (m + 2)) : P :=
  sqLift ρ (swap 0 a * swap b d) * sqLift ρ (swap 0 1 * swap b d)

variable {ρ : P →* Perm (Fin (m + 2))} (hK : ρ.ker ≤ center P) (hodd : Odd (Nat.card ρ.ker))
  (hρ : ∀ σ ∈ alternatingGroup (Fin (m + 2)), σ ∈ ρ.range)
include hK hodd hρ

theorem sqLift_dt_spec {p q r s : Fin (m + 2)} (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    ρ (sqLift ρ (swap p q * swap r s)) = swap p q * swap r s ∧
      sqLift ρ (swap p q * swap r s) ^ 2 = 1 :=
  sqLift_spec hK hodd (hρ _ (swap_mul_swap_mem_alternatingGroup hpq hrs))
    (swap_mul_swap_sq_of_ne hpr hps (Ne.symm hqr) hqs)

theorem sqLift_dt_mul_left {p q r s u v : Fin (m + 2)} (h : [p, q, r, s, u, v].Nodup) :
    sqLift ρ (swap p q * swap r s) * sqLift ρ (swap r s * swap u v) =
      sqLift ρ (swap p q * swap u v) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  obtain ⟨⟨hpq, hpr, hps, hpu, hpv⟩, ⟨hqr, hqs, hqu, hqv⟩, ⟨hrs, hru, hrv⟩, ⟨hsu, hsv⟩, huv⟩ := h
  rw [sqLift_mul hK hodd (hρ _ (swap_mul_swap_mem_alternatingGroup hpq hrs))
      (swap_mul_swap_sq_of_ne hpr hps (Ne.symm hqr) hqs)
      (hρ _ (swap_mul_swap_mem_alternatingGroup hrs huv))
      (swap_mul_swap_sq_of_ne hru hrv (Ne.symm hsu) hsv)
      (commute_mul_mul_left (swap_mul_swap_comm_of_ne hpr hps (Ne.symm hqr) hqs)
        (swap_mul_swap_comm_of_ne hpu hpv (Ne.symm hqu) hqv)
        (swap_mul_swap_comm_of_ne hru hrv (Ne.symm hsu) hsv)),
    mul_assoc, ← mul_assoc (swap r s), swap_mul_self, one_mul]

theorem map_lift3 {a b d : Fin (m + 2)} (h : [0, 1, a, b, d].Nodup) :
    ρ (lift3 ρ a b d) = swap 0 a * swap 0 1 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  obtain ⟨⟨h01, h0a, h0b, h0d⟩, ⟨h1a, h1b, h1d⟩, ⟨hab, had⟩, hbd⟩ := h
  rw [lift3, map_mul, (sqLift_dt_spec hK hodd hρ h0a hbd h0b h0d hab had).1,
    (sqLift_dt_spec hK hodd hρ h01 hbd h0b h0d h1b h1d).1]
  exact swap_mul_swap_mul_swap_mul_swap_cancel (Ne.symm h0b) (Ne.symm h1b) (Ne.symm h0d)
    (Ne.symm h1d)

theorem lift3_eq_of_disjoint {a b d e f : Fin (m + 2)} (h : [0, 1, a, b, d, e, f].Nodup) :
    lift3 ρ a b d = lift3 ρ a e f := by
  have h1 : [0, a, b, d, e, f].Nodup := h.sublist (.cons_cons _ (.cons _ (.refl _)))
  have h2 : [0, 1, b, d, e, f].Nodup := h.sublist (.cons_cons _ (.cons_cons _ (.cons _ (.refl _))))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  obtain ⟨⟨h01, h0a, h0b, h0d, h0e, h0f⟩, ⟨h1a, h1b, h1d, h1e, h1f⟩, ⟨hab, had, hae, haf⟩,
    ⟨hbd, hbe, hbf⟩, ⟨hde, hdf⟩, hef⟩ := h
  set u := sqLift ρ (swap b d * swap e f)
  have hu := sqLift_dt_spec hK hodd hρ hbd hef hbe hbf hde hdf
  have hc : sqLift ρ (swap 0 1 * swap b d) * u = u * sqLift ρ (swap 0 1 * swap b d) :=
    sqLift_mul_comm hK hodd (hρ _ (swap_mul_swap_mem_alternatingGroup h01 hbd))
      (swap_mul_swap_sq_of_ne h0b h0d (Ne.symm h1b) h1d)
      (hρ _ (swap_mul_swap_mem_alternatingGroup hbd hef))
      (swap_mul_swap_sq_of_ne hbe hbf (Ne.symm hde) hdf)
      (commute_mul_mul_left (swap_mul_swap_comm_of_ne h0b h0d (Ne.symm h1b) h1d)
        (swap_mul_swap_comm_of_ne h0e h0f (Ne.symm h1e) h1f)
        (swap_mul_swap_comm_of_ne hbe hbf (Ne.symm hde) hdf))
  unfold lift3
  rw [← sqLift_dt_mul_left hK hodd hρ h1, ← sqLift_dt_mul_left hK hodd hρ h2]
  calc sqLift ρ (swap 0 a * swap b d) * sqLift ρ (swap 0 1 * swap b d)
      = sqLift ρ (swap 0 a * swap b d) * (sqLift ρ (swap 0 1 * swap b d) * u * u) := by
        rw [mul_assoc (sqLift ρ (swap 0 1 * swap b d)), ← sq, hu.2, mul_one]
    _ = sqLift ρ (swap 0 a * swap b d) * (u * sqLift ρ (swap 0 1 * swap b d) * u) := by rw [hc]
    _ = sqLift ρ (swap 0 a * swap b d) * u * (sqLift ρ (swap 0 1 * swap b d) * u) := by
        simp only [mul_assoc]

theorem lift3_eq (hm : 6 ≤ m) {a b d e f : Fin (m + 2)} (h : [0, 1, a, b, d].Nodup)
    (h' : [0, 1, a, e, f].Nodup) : lift3 ρ a b d = lift3 ρ a e f := by
  have hh := h
  have hh' := h'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hh hh'
  obtain ⟨⟨h01, h0a, h0b, h0d⟩, ⟨h1a, h1b, h1d⟩, ⟨hab, had⟩, hbd⟩ := hh
  obtain ⟨⟨-, -, h0e, h0f⟩, ⟨-, h1e, h1f⟩, ⟨hae, haf⟩, hef⟩ := hh'
  have key : ∀ c : Fin (m + 2), (e = b ∨ e = d ∨ e = c) → (f = b ∨ f = d ∨ f = c) →
      lift3 ρ a b d = lift3 ρ a e f := by
    intro c hec hfc
    obtain ⟨g, g', hg, hg', hgg⟩ := exists_pair_notMem {0, 1, a, b, d, c}
      (by
        have h6 : ({0, 1, a, b, d, c} : Finset (Fin (m + 2))).card ≤ 6 := Finset.card_le_six
        omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg hg'
    obtain ⟨hg0, hg1, hga, hgb, hgd, hgc⟩ := hg
    obtain ⟨hg'0, hg'1, hg'a, hg'b, hg'd, hg'c⟩ := hg'
    have n1 : [0, 1, a, b, d, g, g'].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨h01, h0a, h0b, h0d, Ne.symm hg0, Ne.symm hg'0⟩, ⟨h1a, h1b, h1d, Ne.symm hg1,
        Ne.symm hg'1⟩, ⟨hab, had, Ne.symm hga, Ne.symm hg'a⟩, ⟨hbd, Ne.symm hgb, Ne.symm hg'b⟩,
        ⟨Ne.symm hgd, Ne.symm hg'd⟩, hgg⟩
    have hge : e ≠ g := by rcases hec with rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hg'e : e ≠ g' := by rcases hec with rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hgf : f ≠ g := by rcases hfc with rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have hg'f : f ≠ g' := by rcases hfc with rfl | rfl | rfl <;> exact Ne.symm ‹_›
    have n2 : [0, 1, a, e, f, g, g'].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      exact ⟨⟨h01, h0a, h0e, h0f, Ne.symm hg0, Ne.symm hg'0⟩, ⟨h1a, h1e, h1f, Ne.symm hg1,
        Ne.symm hg'1⟩, ⟨hae, haf, Ne.symm hga, Ne.symm hg'a⟩, ⟨hef, hge, hg'e⟩,
        ⟨hgf, hg'f⟩, hgg⟩
    rw [lift3_eq_of_disjoint hK hodd hρ n1, lift3_eq_of_disjoint hK hodd hρ n2]
  by_cases hbe : b = e
  · exact key f (Or.inl hbe.symm) (Or.inr (Or.inr rfl))
  by_cases hbf : b = f
  · exact key e (Or.inr (Or.inr rfl)) (Or.inl hbf.symm)
  by_cases hde : d = e
  · exact key f (Or.inr (Or.inl hde.symm)) (Or.inr (Or.inr rfl))
  by_cases hdf : d = f
  · exact key e (Or.inr (Or.inr rfl)) (Or.inr (Or.inl hdf.symm))
  refine lift3_eq_of_disjoint hK hodd hρ ?_
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  exact ⟨⟨h01, h0a, h0b, h0d, h0e, h0f⟩, ⟨h1a, h1b, h1d, h1e, h1f⟩, ⟨hab, had, hae, haf⟩,
    ⟨hbd, hbe, hbf⟩, ⟨hde, hdf⟩, hef⟩

theorem lift3_pow_three {a b d : Fin (m + 2)} (h : [0, 1, a, b, d].Nodup) :
    lift3 ρ a b d ^ 3 = 1 := by
  have hmap := map_lift3 hK hodd hρ h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  obtain ⟨⟨h01, h0a, h0b, h0d⟩, ⟨h1a, h1b, h1d⟩, ⟨hab, had⟩, hbd⟩ := h
  set A := sqLift ρ (swap 0 a * swap b d)
  set T := sqLift ρ (swap 0 1 * swap b d)
  have hA := sqLift_dt_spec hK hodd hρ h0a hbd h0b h0d hab had
  have hT := sqLift_dt_spec hK hodd hρ h01 hbd h0b h0d h1b h1d
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right (by rw [← sq, hA.2])
  have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right (by rw [← sq, hT.2])
  have hconj : T * (A * T) * T⁻¹ = (A * T)⁻¹ := by
    rw [mul_inv_rev, hAi, hTi, mul_assoc, mul_assoc, ← sq, hT.2, mul_one]
  have hX3 : (A * T) ^ 3 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    change ρ (lift3 ρ a b d) ^ 3 = 1
    rw [hmap, ← (isThreeCycle_swap_mul_swap_same h0a h01 (Ne.symm h1a)).orderOf]
    exact pow_orderOf_eq_one _
  have e : T * (A * T) ^ 3 * T⁻¹ = (A * T)⁻¹ ^ 3 := by rw [← conj_pow, hconj]
  rw [(mem_center_iff.mp (hK hX3) T), mul_inv_cancel_right] at e
  have h6 : ((A * T) ^ 3) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [e]
    rw [inv_pow, inv_mul_cancel]
  have h1 : (⟨(A * T) ^ 3, hX3⟩ : ρ.ker) = 1 :=
    eq_one_of_sq_eq_one_of_odd hodd (Subtype.ext (by simpa using h6))
  exact congrArg Subtype.val h1

theorem lift3_mul_sq {a a' b d : Fin (m + 2)} (h : [0, 1, a, a', b, d].Nodup) :
    (lift3 ρ a b d * lift3 ρ a' b d) ^ 2 = 1 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  obtain ⟨⟨h01, h0a, h0a', h0b, h0d⟩, ⟨h1a, h1a', h1b, h1d⟩, ⟨haa', hab, had⟩, ⟨ha'b, ha'd⟩,
    hbd⟩ := h
  set A := sqLift ρ (swap 0 a * swap b d)
  set B := sqLift ρ (swap 0 a' * swap b d)
  set T := sqLift ρ (swap 0 1 * swap b d)
  have hT := sqLift_dt_spec hK hodd hρ h01 hbd h0b h0d h1b h1d
  have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right (by rw [← sq, hT.2])
  have e1 : T * B * T⁻¹ = sqLift ρ (swap 1 a' * swap b d) := by
    have v0 : (swap 0 1 * swap b d : Perm (Fin (m + 2))) 0 = 1 := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h0b h0d, swap_apply_left]
    have va : (swap 0 1 * swap b d : Perm (Fin (m + 2))) a' = a' := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha'b ha'd,
        swap_apply_of_ne_of_ne (Ne.symm h0a') (Ne.symm h1a')]
    have vb : (swap 0 1 * swap b d : Perm (Fin (m + 2))) b = d := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm h0d) (Ne.symm h1d)]
    have vd : (swap 0 1 * swap b d : Perm (Fin (m + 2))) d = b := by
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm h0b) (Ne.symm h1b)]
    rw [sqLift_conj hK hodd T (hρ _ (swap_mul_swap_mem_alternatingGroup h0a' hbd))
      (swap_mul_swap_sq_of_ne h0b h0d (Ne.symm ha'b) ha'd), hT.1, conj_swap_mul_swap', v0, va,
      vb, vd, swap_comm d b]
  have e2 : A * sqLift ρ (swap 1 a' * swap b d) = sqLift ρ (swap 0 a * swap 1 a') := by
    rw [sqLift_mul hK hodd (hρ _ (swap_mul_swap_mem_alternatingGroup h0a hbd))
      (swap_mul_swap_sq_of_ne h0b h0d (Ne.symm hab) had)
      (hρ _ (swap_mul_swap_mem_alternatingGroup h1a' hbd))
      (swap_mul_swap_sq_of_ne h1b h1d (Ne.symm ha'b) ha'd)
      (commute_mul_mul_right (swap_mul_swap_comm_of_ne h0b h0d (Ne.symm hab) had)
        (swap_mul_swap_comm_of_ne h01 h0a' h1a haa')
        (swap_mul_swap_comm_of_ne (Ne.symm h1b) (Ne.symm ha'b) h1d (Ne.symm ha'd))),
      swap_mul_swap_mul_swap_mul_swap_cancel (Ne.symm h1b) (Ne.symm ha'b) (Ne.symm h1d)
        (Ne.symm ha'd)]
  have e3 : lift3 ρ a b d * lift3 ρ a' b d = A * (T * B * T⁻¹) := by
    rw [hTi]
    simp only [lift3, A, B, T, mul_assoc]
  rw [e3, e1, e2]
  exact (sqLift_dt_spec hK hodd hρ h0a h1a' h01 h0a' (Ne.symm h1a) haa').2

end Lift3

section Main

variable {P : Type*} [Group P]

theorem card_ker_eq_one_of_odd [Finite P] [Group.IsPerfect P] {m : ℕ} (hm : 6 ≤ m)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) : Nat.card η.ker = 1 := by
  classical
  set ρ : P →* Perm (Fin (m + 2)) := (alternatingGroup (Fin (m + 2))).subtype.comp η
  have hker : ρ.ker = η.ker := by
    ext y
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hK' : ρ.ker ≤ center P := hker ▸ hK
  have hodd' : Odd (Nat.card ρ.ker) := hker ▸ hodd
  have hρ : ∀ σ ∈ alternatingGroup (Fin (m + 2)), σ ∈ ρ.range := fun σ hσ => by
    obtain ⟨y, hy⟩ := hη ⟨σ, hσ⟩
    exact ⟨y, by simp [ρ, hy]⟩
  have hpair : ∀ i : Fin m, ∃ b d : Fin (m + 2), [0, 1, i.addNat 2, b, d].Nodup := fun i => by
    obtain ⟨b, d, hb, hd, hbd⟩ := exists_pair_notMem {0, 1, i.addNat 2} (by
      have h3 : ({0, 1, i.addNat 2} : Finset (Fin (m + 2))).card ≤ 3 := Finset.card_le_three
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hd
    have := addNat_two_ne_zero i
    have := addNat_two_ne_one i
    have := zero_ne_one_fin (n := m)
    refine ⟨b, d, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    grind
  choose b d hbd using hpair
  set x : Fin m → P := fun i => lift3 ρ (i.addNat 2) (b i) (d i)
  have hxη : ∀ i, η (x i) = altThreeCycle i := fun i =>
    Subtype.ext (map_lift3 hK' hodd' hρ (hbd i))
  have hx3 : ∀ i, x i ^ 3 = 1 := fun i => lift3_pow_three hK' hodd' hρ (hbd i)
  have hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    obtain ⟨b', d', hb', hd', hbd'⟩ := exists_pair_notMem {0, 1, i.addNat 2, j.addNat 2} (by
      have h4 : ({0, 1, i.addNat 2, j.addNat 2} : Finset (Fin (m + 2))).card ≤ 4 :=
        Finset.card_le_four
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb' hd'
    have := addNat_two_ne_zero i
    have := addNat_two_ne_one i
    have := addNat_two_ne_zero j
    have := addNat_two_ne_one j
    have := addNat_two_ne hij
    have := zero_ne_one_fin (n := m)
    have h' : [0, 1, i.addNat 2, j.addNat 2, b', d'].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      grind
    have ei : x i = lift3 ρ (i.addNat 2) b' d' :=
      lift3_eq hK' hodd' hρ hm (hbd i)
        (h'.sublist (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.refl _))))))
    have ej : x j = lift3 ρ (j.addNat 2) b' d' :=
      lift3_eq hK' hodd' hρ hm (hbd j)
        (h'.sublist (.cons_cons _ (.cons_cons _ (.cons _ (.refl _)))))
    rw [ei, ej]
    exact lift3_mul_sq hK' hodd' hρ h'
  have hL : closure (Set.range x) = ⊤ := by
    have hmap : (closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (closure (Set.range x)) η.ker hK
    rw [hsup, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  have hcard := card_closure_le_of_carmichael m x hx3 hxx
  rw [hL, card_top] at hcard
  have hP : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [η.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hpos : 0 < Nat.card η.ker := Nat.card_pos
  rw [hP, hA] at hcard
  have h1 : Nat.card η.ker ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [mul_one]; exact hcard) hApos
  omega

end Main

end CFSG.Alternating.Multipliers
