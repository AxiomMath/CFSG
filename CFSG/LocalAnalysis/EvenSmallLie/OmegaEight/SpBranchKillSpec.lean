module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLike
public import Mathlib.Algebra.Group.TypeTags.Finite

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ}

section Counting

variable (h0 : mul 0 0 = 0)
include h0

theorem f_mul_self_eq_zero (x : H) : mul (Φ.f x) (Φ.f x) = 0 ↔ x * x = 1 := by
  rw [← Φ.map_mul, ← Φ.f_one h0, Φ.f_eq_iff]

theorem f_eq_zero (x : H) : Φ.f x = 0 ↔ x = 1 := by
  rw [← Φ.f_one h0, Φ.f_eq_iff]

omit h0 in
theorem mem_kInv {c : ℕ} : c ∈ kInv mul N ↔ c < N ∧ mul c c = 0 ∧ c ≠ 0 := by
  unfold kInv
  simp [List.mem_filter, List.mem_range]

theorem kCount_kInv (u : H) : kCount mul (kInv mul N) (Φ.f u) = aInv u := by
  unfold kCount kInv aInv
  rw [List.filter_filter]
  have e1 : ∀ x : H, ((mul (Φ.f x) (Φ.f u) == mul (Φ.f u) (Φ.f x)) &&
      (mul (Φ.f x) (Φ.f x) == 0 && Φ.f x != 0)) = true ↔ x * x = 1 ∧ x ≠ 1 ∧ x * u = u * x := by
    intro x
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, Φ.f_eq_iff,
      f_eq_zero Φ h0]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight e1).symm]
  exact (Φ.card_eq (fun c => (mul c (Φ.f u) == mul (Φ.f u) c) &&
    (mul c c == 0 && c != 0))).symm

theorem kCount_kOrd4 (u : H) : kCount mul (kOrd4 mul N) (Φ.f u) = aOrd4 u := by
  unfold kCount kOrd4 aOrd4
  rw [List.filter_filter]
  have e2 : ∀ x : H, ((mul (Φ.f x) (Φ.f u) == mul (Φ.f u) (Φ.f x)) &&
      (mul (Φ.f x) (Φ.f x) != 0 && mul (mul (Φ.f x) (Φ.f x)) (mul (Φ.f x) (Φ.f x)) == 0)) = true ↔
      x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * u = u * x := by
    intro x
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, Φ.f_eq_iff,
      f_eq_zero Φ h0]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight e2).symm]
  exact (Φ.card_eq (fun c => (mul c (Φ.f u) == mul (Φ.f u) c) &&
    (mul c c != 0 && mul (mul c c) (mul c c) == 0))).symm

end Counting

section Main

variable (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N)
include Φ h0 hinv hgens hG

omit h0 hinv hG in
public theorem reach_lt {c : ℕ} (hc : Reach mul gens c) : c < N := by
  induction hc with
  | zero => exact Φ.pos
  | step _ hg ih =>
    rw [← Φ.f_g ih, ← Φ.f_g (hgens _ hg), ← Φ.map_mul]; exact Φ.lt _

theorem chi_mul {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true) {a c : ℕ}
    (ha : a < N) (hc : c < N) : χ[mul a c]! = (χ[a]! ^^ χ[c]!) := by
  unfold chiOK at hchi
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_range] at hchi
  obtain ⟨⟨-, h0χ⟩, hstep⟩ := hchi
  have key : ∀ c, Reach mul gens c → χ[mul a c]! = (χ[a]! ^^ χ[c]!) := by
    intro c hc
    induction hc with
    | zero =>
      have : mul a 0 = a := by
        rw [← Φ.f_g ha, ← Φ.f_one h0, ← Φ.map_mul, mul_one]
      rw [this, h0χ, Bool.xor_false]
    | @step c g hr hg ih =>
      have hcl := reach_lt Φ hgens hr
      have hgl := hgens g hg
      have hac : mul a c < N := by
        rw [← Φ.f_g ha, ← Φ.f_g hcl, ← Φ.map_mul]; exact Φ.lt _
      have hassoc : mul a (mul c g) = mul (mul a c) g := by
        rw [← Φ.f_g ha, ← Φ.f_g hcl, ← Φ.f_g hgl, ← Φ.map_mul, ← Φ.map_mul, ← Φ.map_mul,
          ← Φ.map_mul, mul_assoc]
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
      have hgd : gens.getD j 0 = g := by rw [List.getD_eq_getElem _ _ hj, hgj]
      have h1 := hstep _ hac j hj
      have h2 := hstep _ hcl j hj
      rw [hgd] at h1 h2
      rw [hassoc, h1, ih, h2, Bool.xor_assoc]
  exact key c (hG c hc)

@[expose] noncomputable def chiHom {b : List Bool} {χ : Array Bool}
    (hchi : chiOK mul gens N b χ = true) : H →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (if χ[Φ.f x]! then 1 else 0)
  map_one' := by
    have h := hchi
    unfold chiOK at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [Φ.f_one h0, h.1.2]; rfl
  map_mul' x y := by
    rw [Φ.map_mul, chi_mul Φ h0 hinv hgens hG hchi (Φ.lt x) (Φ.lt y)]
    cases χ[Φ.f x]! <;> cases χ[Φ.f y]! <;> rfl

theorem chiHom_apply {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true) (x : H) :
    chiHom Φ h0 hinv hgens hG hchi x = Multiplicative.ofAdd (if χ[Φ.f x]! then 1 else 0) := rfl

theorem mem_ker_chiHom {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true)
    (x : H) : x ∈ (chiHom Φ h0 hinv hgens hG hchi).ker ↔ χ[Φ.f x]! = false := by
  rw [MonoidHom.mem_ker, chiHom_apply]
  cases χ[Φ.f x]! <;> decide

theorem index_ker_chiHom {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true)
    {t : H} (ht : χ[Φ.f t]! = true) : (chiHom Φ h0 hinv hgens hG hchi).ker.index = 2 := by
  have := Φ.finite
  rw [Subgroup.index_ker]
  have htop : (chiHom Φ h0 hinv hgens hG hchi).range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 := by
      obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = z := ⟨Multiplicative.toAdd z, rfl⟩
      fin_cases a
      · left; rfl
      · right; rfl
    rcases hz with rfl | rfl
    · exact one_mem _
    · exact ⟨t, by rw [chiHom_apply, ht]; rfl⟩
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

end Main

end CFSG.EvenSmallLie.OmegaEight.SpBranch
