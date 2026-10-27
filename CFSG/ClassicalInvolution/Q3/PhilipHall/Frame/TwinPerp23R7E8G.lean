module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Core94

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7E

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def ModZ (z x y : Q) : Prop := x = y ∨ x = y * z

section ModZ

variable {z : Q}

theorem ModZ.symm (hz2 : z * z = 1) {x y : Q} (h : ModZ z x y) : ModZ z y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [mul_assoc, hz2, mul_one]

theorem ModZ.trans (hz2 : z * z = 1) {x y w : Q} (h₁ : ModZ z x y) (h₂ : ModZ z y w) :
    ModZ z x w := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left
    rw [mul_assoc, hz2, mul_one]

theorem ModZ.mul_right_z (x : Q) : ModZ z (x * z) x := Or.inr rfl

theorem ModZ.conj (hz : ∀ q : Q, q * z = z * q) {x y : Q} (h : ModZ z x y) (c : Q) :
    ModZ z (c * x * c⁻¹) (c * y * c⁻¹) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    calc c * (y * z) * c⁻¹ = c * y * (z * c⁻¹) := by group
      _ = c * y * (c⁻¹ * z) := by rw [hz c⁻¹]
      _ = c * y * c⁻¹ * z := by group

theorem ModZ.comm_iff (hz : ∀ q : Q, q * z = z * q) {x y : Q} (h : ModZ z x y) (w : Q) :
    (x * w = w * x ↔ y * w = w * y) := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · constructor
    · intro h
      have : y * w * z = w * y * z := by
        calc y * w * z = y * z * w := by rw [mul_assoc, hz w, ← mul_assoc]
          _ = w * (y * z) := h
          _ = w * y * z := by group
      exact mul_right_cancel this
    · intro h
      calc y * z * w = y * w * z := by rw [mul_assoc, ← hz w, ← mul_assoc]
        _ = w * y * z := by rw [h]
        _ = w * (y * z) := by group

theorem ModZ.comm_iff' (hz : ∀ q : Q, q * z = z * q) {x y : Q} (h : ModZ z x y) (w : Q) :
    (w * x = x * w ↔ w * y = y * w) := by
  rw [eq_comm, ModZ.comm_iff hz h w, eq_comm]

end ModZ

section Q8

variable {A : Subgroup Q} {z : Q}

theorem comm_or_q8 (hs : IsUniqueInvolution A z) (h8 : Nat.card A = 8)
    (hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {x y : Q} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x ∨ x * y = y * x * z := by
  rcases commutator_eq_q8 hs h8 hnab hx hy with h | h
  · left
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  · right
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = z * (y * x) := by rw [h]
      _ = y * x * z := (comm_of_mem_q8 hs (A.mul_mem hy hx)).symm

theorem modZ_of_comm_q8 (hs : IsUniqueInvolution A z) (h8 : Nat.card A = 8)
    (hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {x y : Q} (hx : x ∈ A) (hy : y ∈ A)
    (hx1 : x ≠ 1) (hxz : x ≠ z) (hy1 : y ≠ 1) (hyz : y ≠ z) (hxy : x * y = y * x) :
    ModZ z y x := by
  have hxx := mul_self_eq_q8 hs h8 hnab hx hx1 hxz
  have hyy := mul_self_eq_q8 hs h8 hnab hy hy1 hyz
  by_cases h1 : x * y = 1
  · right
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hxx, hs.sq]
  by_cases h2 : x * y = z
  · left
    calc y = x⁻¹ * (x * y) := by group
      _ = x⁻¹ * (x * x) := by rw [h2, hxx]
      _ = x := by group
  exfalso
  have h3 := mul_self_eq_q8 hs h8 hnab (A.mul_mem hx hy) h1 h2
  apply hs.ne_one
  rw [← h3]
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hxx, hyy, hs.sq]

end Q8

section Pair

variable {A B : Subgroup Q} {z : Q}

theorem dec_modZ (hz : ∀ q : Q, q * z = z * q) (hz2 : z * z = 1)
    (hinf : ∀ w ∈ A, w ∈ B → w = 1 ∨ w = z) {a a' b b' : Q} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : ModZ z a' a ∧ ModZ z b' b := by
  have h1 : a⁻¹ * a' = b * b'⁻¹ := by
    calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
      _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
      _ = b * b'⁻¹ := by group
  have hL1 : a⁻¹ * a' ∈ A := A.mul_mem (A.inv_mem ha) ha'
  have hL2 : a⁻¹ * a' ∈ B := h1 ▸ B.mul_mem hb (B.inv_mem hb')
  have hA : ModZ z a' a := by
    rcases hinf _ hL1 hL2 with h3 | h3
    · left
      calc a' = a * (a⁻¹ * a') := by group
        _ = a := by rw [h3, mul_one]
    · right
      calc a' = a * (a⁻¹ * a') := by group
        _ = a * z := by rw [h3]
  refine ⟨hA, ?_⟩
  rcases hA with rfl | rfl
  · left
    exact (mul_left_cancel h).symm
  · right
    have hb2 : b = z * b' := by
      apply mul_left_cancel (a := a)
      rw [h]; group
    rw [hb2, ← hz b', mul_assoc, hz2, mul_one]

theorem comm_of_modZ (hz : ∀ q : Q, q * z = z * q) {x y : Q} (h : ModZ z x y) :
    x * y = y * x :=
  (ModZ.comm_iff hz h y).mpr rfl

theorem prod_comm_iff (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z)
    (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8) (h8B : Nat.card B = 8)
    (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {a a' b b' : Q} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∈ B) (hb' : b' ∈ B) :
    (a * b) * (a' * b') = (a' * b') * (a * b) ↔ (a * a' = a' * a ↔ b * b' = b' * b) := by
  have e1 : (a * b) * (a' * b') = (a * a') * (b * b') := by
    calc (a * b) * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hcomm a' ha' b hb]
      _ = (a * a') * (b * b') := by group
  have e2 : (a' * b') * (a * b) = (a' * a) * (b' * b) := by
    calc (a' * b') * (a * b) = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [hcomm a ha b' hb']
      _ = (a' * a) * (b' * b) := by group
  rw [e1, e2]
  have hz1 := hsA.ne_one
  have hz2 := hsA.sq
  have hne : ∀ x : Q, x * z ≠ x := fun x h => hz1 (mul_eq_left.mp h)
  rcases comm_or_q8 hsA h8A hnabA ha ha' with hA | hA <;>
    rcases comm_or_q8 hsB h8B hnabB hb hb' with hB | hB
  · exact ⟨fun _ => ⟨fun _ => hB, fun _ => hA⟩, fun _ => by rw [hA, hB]⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      rw [hA, hB, ← mul_assoc] at h
      exact hne _ h
    · exact absurd (h.mp hA) (by rw [hB]; exact hne _)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      rw [hA, hB, mul_assoc, ← hz (b' * b), ← mul_assoc] at h
      exact hne _ h
    · exact absurd (h.mpr hB) (by rw [hA]; exact hne _)
  · refine ⟨fun _ => iff_of_false (by rw [hA]; exact hne _) (by rw [hB]; exact hne _),
      fun _ => ?_⟩
    rw [hA, hB]
    calc a' * a * z * (b' * b * z) = a' * a * (b' * b) * (z * z) := by
          rw [mul_assoc (a' * a) z, ← hz (b' * b * z)]; group
      _ = a' * a * (b' * b) := by rw [hz2, mul_one]

theorem mem_inf_q8 (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z)
    (h8A : Nat.card A = 8) (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {w : Q} (hwA : w ∈ A) (hwB : w ∈ B) :
    w = 1 ∨ w = z := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, hxy⟩ := hnabA
  have hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := ⟨x, hx, y, hy, hxy⟩
  have hx1 : x ≠ 1 := by rintro rfl; exact hxy (by rw [one_mul, mul_one])
  have hxz : x ≠ z := by rintro rfl; exact hxy (comm_of_mem_q8 hsA hy).symm
  have hy1 : y ≠ 1 := by rintro rfl; exact hxy (by rw [one_mul, mul_one])
  have hyz : y ≠ z := by rintro rfl; exact hxy (comm_of_mem_q8 hsA hx)
  have h1 : ModZ z x w :=
    modZ_of_comm_q8 hsA h8A hnab hwA hx h.1 h.2 hx1 hxz (hcomm x hx w hwB).symm
  have h2 : ModZ z y w :=
    modZ_of_comm_q8 hsA h8A hnab hwA hy h.1 h.2 hy1 hyz (hcomm y hy w hwB).symm
  exact hxy (comm_of_modZ hz (ModZ.trans hsA.sq h1 (ModZ.symm hsA.sq h2)))

theorem pigeon {α : Type*} {o q₁ q₂ d₁ d₂ d₃ d : α} (h₁ : d₁ = o ∨ d₁ = q₁ ∨ d₁ = q₂)
    (h₂ : d₂ = o ∨ d₂ = q₁ ∨ d₂ = q₂) (h₃ : d₃ = o ∨ d₃ = q₁ ∨ d₃ = q₂)
    (h : d = o ∨ d = q₁ ∨ d = q₂) (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) :
    d = d₁ ∨ d = d₂ ∨ d = d₃ := by
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    rcases h₃ with rfl | rfl | rfl <;> rcases h with rfl | rfl | rfl <;> simp_all

theorem conj_comm_iff (g x y : Q) :
    (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) ↔ x * y = y * x := by
  rw [show (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group,
    show (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ by group]
  constructor
  · intro h
    calc x * y = g⁻¹ * (g * (x * y) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (y * x) * g⁻¹) * g := by rw [h]
      _ = y * x := by group
  · intro h
    rw [h]

theorem comm_conj_of_orbit (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z)
    (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8) (h8B : Nat.card B = 8)
    (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hinf : ∀ w ∈ A, w ∈ B → w = 1 ∨ w = z)
    (hperm : ∀ q : Q,
      (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    {a b : Q} (ha : a ∈ A) (hb : b ∈ B) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1)
    (hbz : b ≠ z) {s : Q} (hsAB : conjSub s A = B) (hsBA : conjSub s B = A)
    (hsp : ModZ z (s * (a * b) * s⁻¹) (a * b)) {q₁ q₂ : Q}
    (horb : ∀ q : Q, ∃ d : Q, (d = 1 ∨ d = q₁ ∨ d = q₂) ∧
      ModZ z (q * (a * b) * q⁻¹) (d * (a * b) * d⁻¹)) (c : Q) :
    (c * (a * b) * c⁻¹) * (a * b) = (a * b) * (c * (a * b) * c⁻¹) := by
  have hz2 := hsA.sq
  have hzB := hsB.mem
  have hmem : ∀ (g : Q) (M N : Subgroup Q), conjSub g M = N → ∀ m ∈ M, g * m * g⁻¹ ∈ N :=
    fun g M N h m hm => h ▸ conj_mem_conjSub hm
  have hnt : ∀ (g x : Q), x ≠ 1 → x ≠ z → g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ ≠ z := by
    intro g x h1 h2
    constructor
    · intro h
      apply h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h
      apply h2
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (z * g) := by rw [h]; group
        _ = g⁻¹ * (g * z) := by rw [hz g]
        _ = z := by group
  have hdecomp : ∀ g : Q, ∃ a' ∈ A, ∃ b' ∈ B, a' ≠ 1 ∧ a' ≠ z ∧ b' ≠ 1 ∧ b' ≠ z ∧
      g * (a * b) * g⁻¹ = a' * b' := by
    intro g
    obtain ⟨hga1, hgaz⟩ := hnt g a ha1 haz
    obtain ⟨hgb1, hgbz⟩ := hnt g b hb1 hbz
    rcases hperm g with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact ⟨_, hmem g A A hA a ha, _, hmem g B B hB b hb, hga1, hgaz, hgb1, hgbz, by group⟩
    · refine ⟨_, hmem g B A hB b hb, _, hmem g A B hA a ha, hgb1, hgbz, hga1, hgaz, ?_⟩
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) :=
          (hcomm _ (hmem g B A hB b hb) _ (hmem g A B hA a ha)).symm
  have hsb : ModZ z (s * b * s⁻¹) a ∧ ModZ z (s * a * s⁻¹) b := by
    have hsbA := hmem s B A hsBA b hb
    have hsaB := hmem s A B hsAB a ha
    have hsp' : s * (a * b) * s⁻¹ = (s * b * s⁻¹) * (s * a * s⁻¹) := by
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = _ := (hcomm _ hsbA _ hsaB).symm
    rcases hsp with h | h
    · rw [hsp'] at h
      exact dec_modZ hz hz2 hinf ha hsbA hb hsaB h.symm
    · rw [hsp'] at h
      have h' : a * (b * z) = (s * b * s⁻¹) * (s * a * s⁻¹) := by rw [← mul_assoc]; exact h.symm
      obtain ⟨h1, h2⟩ := dec_modZ hz hz2 hinf ha hsbA (B.mul_mem hb hzB) hsaB h'
      exact ⟨h1, ModZ.trans hz2 h2 (ModZ.mul_right_z b)⟩
  by_contra hncomm
  have hpv : ¬ (a * b) * (c * (a * b) * c⁻¹) = (c * (a * b) * c⁻¹) * (a * b) :=
    fun h => hncomm h.symm
  obtain ⟨a', ha', b', hb', ha'1, ha'z, hb'1, hb'z, hv⟩ := hdecomp c
  have hnot : ¬ (a * a' = a' * a ↔ b * b' = b' * b) := by
    rw [← prod_comm_iff hz hsA hsB h8A h8B hnabA hnabB hcomm ha ha' hb hb', ← hv]
    exact hpv
  have ha'' : s * b' * s⁻¹ ∈ A := hmem s B A hsBA b' hb'
  have hb'' : s * a' * s⁻¹ ∈ B := hmem s A B hsAB a' ha'
  have hvs : s * (a' * b') * s⁻¹ = (s * b' * s⁻¹) * (s * a' * s⁻¹) := by
    calc s * (a' * b') * s⁻¹ = (s * a' * s⁻¹) * (s * b' * s⁻¹) := by group
      _ = _ := (hcomm _ ha'' _ hb'').symm
  have k1 : (a * (s * b' * s⁻¹) = (s * b' * s⁻¹) * a) ↔ b * b' = b' * b := by
    rw [ModZ.comm_iff hz (ModZ.symm hz2 hsb.1) (s * b' * s⁻¹)]
    exact conj_comm_iff s b b'
  have k2 : (b * (s * a' * s⁻¹) = (s * a' * s⁻¹) * b) ↔ a * a' = a' * a := by
    rw [ModZ.comm_iff hz (ModZ.symm hz2 hsb.2) (s * a' * s⁻¹)]
    exact conj_comm_iff s a a'
  have hpvs : ¬ (a * b) * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) =
      ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * (a * b) := by
    rw [prod_comm_iff hz hsA hsB h8A h8B hnabA hnabB hcomm ha ha'' hb hb'', k1, k2]
    exact fun h => hnot h.symm
  have hkey : ¬ (a' * (s * b' * s⁻¹) = (s * b' * s⁻¹) * a') ∧
      ¬ (b' * (s * a' * s⁻¹) = (s * a' * s⁻¹) * b') := by
    by_cases hbb : b * b' = b' * b
    · have haa : ¬ a * a' = a' * a := fun h => hnot ⟨fun _ => hbb, fun _ => h⟩
      have hm : ModZ z b' b := modZ_of_comm_q8 hsB h8B hnabB hb hb' hb1 hbz hb'1 hb'z hbb
      have hm2 : ModZ z (s * b' * s⁻¹) a := ModZ.trans hz2 (ModZ.conj hz hm s) hsb.1
      constructor
      · rw [ModZ.comm_iff' hz hm2 a']
        exact fun h => haa h.symm
      · rw [ModZ.comm_iff hz hm _, k2]
        exact haa
    · have haa : a * a' = a' * a := by
        by_contra h
        exact hnot ⟨fun h' => absurd h' h, fun h' => absurd h' hbb⟩
      have hm : ModZ z a' a := modZ_of_comm_q8 hsA h8A hnabA ha ha' ha1 haz ha'1 ha'z haa
      have hm2 : ModZ z (s * a' * s⁻¹) b := ModZ.trans hz2 (ModZ.conj hz hm s) hsb.2
      constructor
      · rw [ModZ.comm_iff hz hm _, k1]
        exact hbb
      · rw [ModZ.comm_iff' hz hm2 b']
        exact fun h => hbb h.symm
  have hvvs : (a' * b') * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) =
      ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * (a' * b') := by
    rw [prod_comm_iff hz hsA hsB h8A h8B hnabA hnabB hcomm ha' ha'' hb' hb'']
    exact iff_of_false hkey.1 hkey.2
  have hvs_ne : ¬ ModZ z ((s * b' * s⁻¹) * (s * a' * s⁻¹)) (a' * b') := by
    intro h
    have hm : ModZ z (s * b' * s⁻¹) a' := by
      rcases h with h | h
      · exact (dec_modZ hz hz2 hinf ha' ha'' hb' hb'' h.symm).1
      · have h' : a' * (b' * z) = (s * b' * s⁻¹) * (s * a' * s⁻¹) := by
          rw [← mul_assoc]; exact h.symm
        exact (dec_modZ hz hz2 hinf ha' ha'' (B.mul_mem hb' hzB) hb'' h').1
    apply hkey.1
    rw [ModZ.comm_iff' hz hm a']
  have hVS : (s * c) * (a * b) * (s * c)⁻¹ = (s * b' * s⁻¹) * (s * a' * s⁻¹) := by
    rw [← hvs, ← hv]
    group
  have hpV : ¬ ModZ z (a' * b') (a * b) := fun h => by
    apply hpv
    rw [hv]
    exact (comm_of_modZ hz h).symm
  have hpVS : ¬ ModZ z ((s * b' * s⁻¹) * (s * a' * s⁻¹)) (a * b) := fun h =>
    hpvs (comm_of_modZ hz h).symm
  obtain ⟨dP, hdP, hmP⟩ := horb 1
  obtain ⟨dV, hdV, hmV⟩ := horb c
  obtain ⟨dS, hdS, hmS⟩ := horb (s * c)
  rw [show (1 : Q) * (a * b) * 1⁻¹ = a * b by group] at hmP
  rw [hv] at hmV
  rw [hVS] at hmS
  have hPV : dP ≠ dV := by
    rintro rfl
    exact hpV (ModZ.trans hz2 hmV (ModZ.symm hz2 hmP))
  have hPS : dP ≠ dS := by
    rintro rfl
    exact hpVS (ModZ.trans hz2 hmS (ModZ.symm hz2 hmP))
  have hVS' : dV ≠ dS := by
    rintro rfl
    exact hvs_ne (ModZ.trans hz2 hmS (ModZ.symm hz2 hmV))
  have hcover : ∀ q : Q, ModZ z (q * (a * b) * q⁻¹) (a * b) ∨
      ModZ z (q * (a * b) * q⁻¹) (a' * b') ∨
      ModZ z (q * (a * b) * q⁻¹) ((s * b' * s⁻¹) * (s * a' * s⁻¹)) := by
    intro q
    obtain ⟨dq, hdq, hmq⟩ := horb q
    rcases pigeon hdP hdV hdS hdq hPV hPS hVS' with rfl | rfl | rfl
    · exact Or.inl (ModZ.trans hz2 hmq (ModZ.symm hz2 hmP))
    · exact Or.inr (Or.inl (ModZ.trans hz2 hmq (ModZ.symm hz2 hmV)))
    · exact Or.inr (Or.inr (ModZ.trans hz2 hmq (ModZ.symm hz2 hmS)))
  have hn1 : ¬ (a' * b') * (c * (a' * b') * c⁻¹) = (c * (a' * b') * c⁻¹) * (a' * b') := by
    rw [← hv, conj_comm_iff c (a * b) (c * (a * b) * c⁻¹)]
    exact hpv
  have hn2 : ¬ (a' * b') * (c * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * c⁻¹) =
      (c * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * c⁻¹) * (a' * b') := by
    rw [← hv, conj_comm_iff c (a * b)]
    exact hpvs
  have hto : ∀ w : Q, ¬ (a' * b') * w = w * (a' * b') →
      (ModZ z w (a * b) ∨ ModZ z w (a' * b') ∨
        ModZ z w ((s * b' * s⁻¹) * (s * a' * s⁻¹))) → ModZ z w (a * b) := by
    intro w hw h
    rcases h with h | h | h
    · exact h
    · exact absurd ((ModZ.comm_iff' hz h _).mpr rfl) hw
    · exact absurd ((ModZ.comm_iff' hz h _).mpr hvvs) hw
  have hw1 := hto _ hn1 (by
    have := hcover (c * c)
    rwa [show (c * c) * (a * b) * (c * c)⁻¹ = c * (a' * b') * c⁻¹ by rw [← hv]; group] at this)
  have hw2 := hto _ hn2 (by
    have := hcover (c * (s * c))
    rwa [show (c * (s * c)) * (a * b) * (c * (s * c))⁻¹ =
      c * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * c⁻¹ by rw [← hVS]; group] at this)
  have h12 := ModZ.conj hz (ModZ.trans hz2 hw1 (ModZ.symm hz2 hw2)) c⁻¹
  rw [show c⁻¹ * (c * (a' * b') * c⁻¹) * c⁻¹⁻¹ = a' * b' by group,
    show c⁻¹ * (c * ((s * b' * s⁻¹) * (s * a' * s⁻¹)) * c⁻¹) * c⁻¹⁻¹ =
      (s * b' * s⁻¹) * (s * a' * s⁻¹) by group] at h12
  exact hvs_ne (ModZ.symm hz2 h12)

end Pair

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7E
