module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Orbit2
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Pointwise

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_eq_ncard_mul (N A : Subgroup X) :
    Nat.card N = {B : Subgroup X | ∃ n ∈ N, A.map (MulAut.conj n).toMonoidHom = B}.ncard *
      Nat.card (N ⊓ normalizer (A : Set X) : Subgroup X) := by
  let _ : MulAction N (Subgroup X) :=
    MulAction.compHom (Subgroup X) ((MulAut.conj : X →* MulAut X).comp N.subtype)
  have hsmul : ∀ (n : N) (H : Subgroup X), n • H = H.map (MulAut.conj (n : X)).toMonoidHom := by
    intro n H
    show (MulAut.conj (n : X)) • H = _
    rw [Subgroup.pointwise_smul_def]
    rfl
  have horb : MulAction.orbit N A =
      {B : Subgroup X | ∃ n ∈ N, A.map (MulAut.conj n).toMonoidHom = B} := by
    ext B
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, (hsmul n A).symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hsmul _ A⟩
  have hstab : MulAction.stabilizer N A = (normalizer (A : Set X)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf]
    exact ⟨fun h => mem_normalizer_of_map_eq h, fun h => map_conj_eq_of_mem_normalizer h⟩
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer N A)
  rw [MulAction.index_stabilizer, horb, hstab, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : N ⊓ normalizer (A : Set X) ≤ N)).toEquiv]
    at h1
  exact h1.symm

omit [Finite X] in
theorem mem_of_pow_three_mem {H : Subgroup X} {s : X} {m : ℕ} (h3 : s ^ 3 ∈ H)
    (h2 : s ^ (2 ^ m) ∈ H) : s ∈ H := by
  have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  have hg := Nat.gcd_eq_gcd_ab (2 ^ m) 3
  rw [Nat.Coprime.gcd_eq_one hcop] at hg
  have h1 : (1 : ℤ) = ((2 ^ m : ℕ) : ℤ) * Nat.gcdA (2 ^ m) 3 + ((3 : ℕ) : ℤ) * Nat.gcdB (2 ^ m) 3 :=
    by exact_mod_cast hg
  have : s = (s ^ (2 ^ m)) ^ (Nat.gcdA (2 ^ m) 3) * (s ^ 3) ^ (Nat.gcdB (2 ^ m) 3) := by
    calc s = s ^ (1 : ℤ) := (zpow_one _).symm
      _ = s ^ (((2 ^ m : ℕ) : ℤ) * Nat.gcdA (2 ^ m) 3 + ((3 : ℕ) : ℤ) * Nat.gcdB (2 ^ m) 3) := by
        rw [← h1]
      _ = _ := by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [this]
  exact mul_mem (zpow_mem h2 _) (zpow_mem h3 _)

abbrev act (s : X) (A : Subgroup X) : Subgroup X := A.map (MulAut.conj s).toMonoidHom

omit [Finite X] in
theorem act_mul (s s' : X) (A : Subgroup X) : act (s * s') A = act s (act s' A) :=
  (map_conj_map A s s').symm

namespace Setup

variable {S : A7Base X} (C : Setup S)

def Ω : Set (Subgroup X) := {C.E₁, C.G₁, C.G₂, C.G₃}

theorem mem_Ω_iff {A : Subgroup X} : A ∈ C.Ω ↔ A = C.E₁ ∨ A = C.G₁ ∨ A = C.G₂ ∨ A = C.G₃ := by
  unfold Ω; rfl


theorem E₁_ne_G {r : X} (hrQ : r ∈ C.D₁.Q₁) (hr2 : r ^ 2 ∈ C.E₀) (hr : alpha S r ≠ 1) :
    C.E₁ ≠ C.E₀ ⊔ zpowers r := fun h => hr (by
  rw [C.E₁_eq] at h
  exact (C.alpha_eq_of_sup_eq C.t_mem_Q₁ hrQ (C.isRefl_y.t_not_mem_E0 C.isK_k) hr2 h).symm.trans
    (alpha_t S))

theorem r₁_sq_mem : (S.t * C.v' * C.w₁') ^ 2 ∈ C.E₀ := by rw [C.r₁_sq]; exact one_mem _

theorem r₂_sq_mem : (S.t * C.v' * C.D₁.w₂) ^ 2 ∈ C.E₀ := by rw [C.r₂_sq]; exact one_mem _

theorem r₃_sq_mem : (S.t * C.v' * C.w₁' * C.D₁.w₂) ^ 2 ∈ C.E₀ := by
  rw [C.r₃_sq]; exact one_mem _

theorem E₁_ne_G₁ : C.E₁ ≠ C.G₁ :=
  C.E₁_ne_G C.r₁_mem C.r₁_sq_mem (by rw [C.alpha_r₁]; exact C.kz_ne_one)

theorem E₁_ne_G₂ : C.E₁ ≠ C.G₂ :=
  C.E₁_ne_G C.r₂_mem C.r₂_sq_mem (by rw [C.alpha_r₂]; exact C.ky_ne_one)

theorem E₁_ne_G₃ : C.E₁ ≠ C.G₃ :=
  C.E₁_ne_G C.r₃_mem C.r₃_sq_mem (by rw [C.alpha_r₃]; exact C.kzy_ne_one)

theorem ncard_Ω : C.Ω.ncard = 4 := by
  rw [Ω, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair C.G₂_ne_G₃]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨C.G₁_ne_G₂, C.G₁_ne_G₃⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨C.E₁_ne_G₁, C.E₁_ne_G₂, C.E₁_ne_G₃⟩

theorem conj₁_E₁ : C.Conj₁ C.E₁ :=
  C.conj₁_def.mpr ⟨1, one_mem _, by ext x; simp⟩

theorem conj₁_iff {A : Subgroup X} : C.Conj₁ A ↔ A ∈ C.Ω := by
  constructor
  · intro hA
    obtain ⟨n, hn, rfl⟩ := C.conj₁_def.mp hA
    rcases C.conj_E₁_cases hn with h | h | h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact absurd h (C.map_ne_Fv n)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact C.conj₁_E₁
    · exact C.conj₁_all.1
    · exact C.conj₁_all.2.1
    · exact C.conj₁_all.2.2

theorem act_mem_Ω {s : X} (hs : s ∈ normalizer (C.D₁.Q₁ : Set X)) {A : Subgroup X}
    (hA : A ∈ C.Ω) : act s A ∈ C.Ω :=
  C.conj₁_iff.mp (C.conj₁_map (C.conj₁_iff.mpr hA) hs)

theorem card_normalizer : Nat.card (normalizer (C.D₁.Q₁ : Set X)) =
    4 * Nat.card (normalizer (C.D₁.Q₁ : Set X) ⊓ normalizer (C.E₁ : Set X) : Subgroup X) := by
  rw [card_eq_ncard_mul]
  congr 1
  rw [← C.ncard_Ω]
  congr 1
  ext B
  exact C.conj₁_def.symm.trans C.conj₁_iff

theorem exists_S₂ : ∃ S₂ : Subgroup X,
    ABGLocalTools.IsSylowOf 2 S₂ (normalizer (C.D₁.Q₁ : Set X)) ∧ C.D₁.S₁ ≤ S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁N : C.D₁.S₁ ≤ normalizer (C.D₁.Q₁ : Set X) := C.S₁_le_normalizer_Q₁
  have h2 : IsPGroup 2 (C.D₁.S₁.subgroupOf (normalizer (C.D₁.Q₁ : Set X))) :=
    C.D₁.isPGroup_S₁.comap_subtype
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  exact ⟨(P : Subgroup _).map (normalizer (C.D₁.Q₁ : Set X)).subtype, ⟨P, rfl⟩,
    fun x hx => ⟨⟨x, hS₁N hx⟩, hP hx, rfl⟩⟩

def S₂ : Subgroup X := Classical.choose C.exists_S₂

theorem S₂_sylow : ABGLocalTools.IsSylowOf 2 C.S₂ (normalizer (C.D₁.Q₁ : Set X)) :=
  (Classical.choose_spec C.exists_S₂).1

theorem S₁_le_S₂ : C.D₁.S₁ ≤ C.S₂ := (Classical.choose_spec C.exists_S₂).2

theorem S₂_le : C.S₂ ≤ normalizer (C.D₁.Q₁ : Set X) := C.S₂_sylow.le

theorem isPGroup_S₂ : IsPGroup 2 C.S₂ := C.S₂_sylow.isPGroup

theorem u_mem_S₂ : C.D₁.u ∈ C.S₂ := C.S₁_le_S₂ C.u_mem_S₁

theorem S₂_inf : C.S₂ ⊓ normalizer (C.E₁ : Set X) = C.D₁.S₁ :=
  C.D₁.S₁_maximal _ (C.isPGroup_S₂.to_le inf_le_left) (le_inf C.S₁_le_S₂ C.D₁.S₁_le)
    inf_le_right

theorem S₁_sylow_N₁ : ABGLocalTools.IsSylowOf 2 C.D₁.S₁
    (normalizer (C.D₁.Q₁ : Set X) ⊓ normalizer (C.E₁ : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₁ := normalizer (C.D₁.Q₁ : Set X) ⊓ normalizer (C.E₁ : Set X) with hN₁
  have hS₁N : C.D₁.S₁ ≤ N₁ := le_inf C.S₁_le_normalizer_Q₁ C.D₁.S₁_le
  have h2 : IsPGroup 2 (C.D₁.S₁.subgroupOf N₁) := C.D₁.isPGroup_S₁.comap_subtype
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  have hle : C.D₁.S₁ ≤ (P : Subgroup N₁).map N₁.subtype :=
    fun x hx => ⟨⟨x, hS₁N hx⟩, hP hx, rfl⟩
  have heq := C.D₁.S₁_maximal _ (P.isPGroup'.map _) hle
    ((Subgroup.map_subtype_le _).trans inf_le_right)
  exact ⟨P, heq⟩

theorem card_S₂ : Nat.card C.S₂ = 4 * Nat.card C.D₁.S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [C.S₂_sylow.card_eq, C.S₁_sylow_N₁.card_eq, C.card_normalizer,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
  rw [Finsupp.add_apply, pow_add]
  congr 1
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  rfl

theorem exists_mem_S₂ {A : Subgroup X} (hA : A ∈ C.Ω) : ∃ q ∈ C.S₂, act q C.E₁ = A := by
  set O := {B : Subgroup X | ∃ n ∈ C.S₂, C.E₁.map (MulAut.conj n).toMonoidHom = B} with hO
  have h1 := card_eq_ncard_mul C.S₂ C.E₁
  rw [C.S₂_inf, C.card_S₂, ← hO] at h1
  have hO4 : O.ncard = 4 := (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hsub : O ⊆ C.Ω := by
    rintro _ ⟨n, hn, rfl⟩
    exact C.act_mem_Ω (C.S₂_le hn) (Or.inl rfl)
  have heq : O = C.Ω := Set.eq_of_subset_of_ncard_le hsub (by rw [C.ncard_Ω, hO4])
    (Set.toFinite _)
  rw [← heq] at hA
  exact hA

theorem mem_Ω_E₁ : C.E₁ ∈ C.Ω := Or.inl rfl

theorem mem_Ω_G₁ : C.G₁ ∈ C.Ω := Or.inr (Or.inl rfl)

theorem mem_Ω_G₂ : C.G₂ ∈ C.Ω := Or.inr (Or.inr (Or.inl rfl))

theorem mem_Ω_G₃ : C.G₃ ∈ C.Ω := Or.inr (Or.inr (Or.inr rfl))

theorem no_three_cycle {s : X} (hs : s ∈ C.S₂) {A B D : Subgroup X} (h1 : act s A = B)
    (h2 : act s B = D) (h3 : act s D = A) (hAB : A ≠ B) : False := by
  obtain ⟨m, hm⟩ := C.isPGroup_S₂ ⟨s, hs⟩
  have hm' : s ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hs3 : s ^ 3 ∈ normalizer (A : Set X) := by
    refine mem_normalizer_of_map_eq ?_
    rw [show s ^ 3 = s * (s * s) by rw [pow_succ, pow_two]; group]
    change act (s * (s * s)) A = A
    rw [act_mul, act_mul, h1, h2, h3]
  have hs2 : s ^ (2 ^ m) ∈ normalizer (A : Set X) := by rw [hm']; exact one_mem _
  have hsA := map_conj_eq_of_mem_normalizer (mem_of_pow_three_mem hs3 hs2)
  exact hAB (hsA.symm.trans h1)

theorem u_E₁ : act C.D₁.u C.E₁ = C.E₁ :=
  map_conj_eq_of_mem_normalizer (C.D₁.S₁_le C.u_mem_S₁)

theorem u_G₁ : act C.D₁.u C.G₁ = C.G₁ := by
  show C.G₁.map (MulAut.conj C.D₁.u).toMonoidHom = C.G₁
  rw [C.map_sup_zpowers C.u_normalizes]
  have hut : C.D₁.u * S.t * C.D₁.u⁻¹ = S.t := conj_eq_of_comm (C.u_comm_B t_mem_B)
  have hxQ := C.conj_mem_Q₁ C.u_normalizes C.r₁_mem
  have hx2 := conj_sq_one (n := C.D₁.u) C.r₁_sq
  have hα : alpha S (C.D₁.u * (S.t * C.v' * C.w₁') * C.D₁.u⁻¹) = C.F.kF * S.z := by
    rw [alpha_conj S hut, C.alpha_r₁, conj_eq_of_comm (C.u_comm_B (mul_mem (kF_mem_B C.F)
      z_mem_B))]
  have hx0 := C.not_mem_E0_of_alpha (by rw [hα]; exact C.kz_ne_one)
  rcases C.sup_eq_of_alpha hxQ hx2 hx0 (by rw [hα]; exact C.kz_ne_one)
    (by rw [hα]; exact C.kz_ne_k) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · exact absurd (hα.symm.trans h) C.kz_ne_ky
  · exact absurd (hα.symm.trans h) C.kz_ne_kzy

theorem u_G₂' : act C.D₁.u C.G₂ = C.G₃ := C.u_G₂

theorem u_G₃' : act C.D₁.u C.G₃ = C.G₂ := C.u_G₃

theorem exists_q₁ : ∃ q ∈ C.S₂, act q C.E₁ = C.G₁ ∧ act q C.G₁ = C.E₁ ∧
    act q C.G₂ = C.G₃ ∧ act q C.G₃ = C.G₂ := by
  obtain ⟨q, hq, h0⟩ := C.exists_mem_S₂ C.mem_Ω_G₁
  have hu := C.u_mem_S₂
  have hΩ : ∀ {A}, A ∈ C.Ω → act q A ∈ C.Ω := fun hA => C.act_mem_Ω (C.S₂_le hq) hA
  have inj : ∀ {A B : Subgroup X}, act q A = act q B → A = B := fun h => map_conj_inj h
  have d01 := C.E₁_ne_G₁
  have d02 := C.E₁_ne_G₂
  have d03 := C.E₁_ne_G₃
  have d12 := C.G₁_ne_G₂
  have d13 := C.G₁_ne_G₃
  have d23 := C.G₂_ne_G₃
  rcases hΩ C.mem_Ω_G₁ with h1 | h1 | h1 | h1
  · rcases hΩ C.mem_Ω_G₂ with h2 | h2 | h2 | h2
    · exact absurd (inj (h2.trans h1.symm)) d12.symm
    · exact absurd (inj (h2.trans h0.symm)) d02.symm
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
      · refine ⟨C.D₁.u * q, mul_mem hu hq, ?_, ?_, ?_, ?_⟩ <;> rw [act_mul]
        · rw [h0, C.u_G₁]
        · rw [h1, C.u_E₁]
        · rw [h2, C.u_G₂']
        · rw [h3, C.u_G₃']
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact ⟨q, hq, h0, h1, h2, h3⟩
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
  · exact absurd (inj (h1.trans h0.symm)) d01.symm
  · rcases hΩ C.mem_Ω_G₂ with h2 | h2 | h2 | h2
    · exact (C.no_three_cycle hq h0 h1 h2 d01).elim
    · exact absurd (inj (h2.trans h0.symm)) d02.symm
    · exact absurd (inj (h2.trans h1.symm)) d12.symm
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · exact (C.no_three_cycle (mul_mem hq hu) (A := C.E₁) (B := C.G₁) (D := C.G₂)
          (by rw [act_mul, C.u_E₁, h0]) (by rw [act_mul, C.u_G₁, h1])
          (by rw [act_mul, C.u_G₂', h3]) d01).elim
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
  · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
    · exact (C.no_three_cycle hq h0 h1 h3 d01).elim
    · exact absurd (inj (h3.trans h0.symm)) d03.symm
    · rcases hΩ C.mem_Ω_G₂ with h2 | h2 | h2 | h2
      · exact (C.no_three_cycle (mul_mem hq hu) (A := C.E₁) (B := C.G₁) (D := C.G₃)
          (by rw [act_mul, C.u_E₁, h0]) (by rw [act_mul, C.u_G₁, h1])
          (by rw [act_mul, C.u_G₃', h2]) d01).elim
      · exact absurd (inj (h2.trans h0.symm)) d02.symm
      · exact absurd (inj (h2.trans h3.symm)) d23
      · exact absurd (inj (h2.trans h1.symm)) d12.symm
    · exact absurd (inj (h3.trans h1.symm)) d13.symm

theorem exists_q₂ : ∃ q ∈ C.S₂, act q C.E₁ = C.G₂ ∧ act q C.G₂ = C.E₁ ∧
    act q C.G₁ = C.G₃ ∧ act q C.G₃ = C.G₁ := by
  obtain ⟨q, hq, h0⟩ := C.exists_mem_S₂ C.mem_Ω_G₂
  have hu := C.u_mem_S₂
  have hΩ : ∀ {A}, A ∈ C.Ω → act q A ∈ C.Ω := fun hA => C.act_mem_Ω (C.S₂_le hq) hA
  have inj : ∀ {A B : Subgroup X}, act q A = act q B → A = B := fun h => map_conj_inj h
  have d01 := C.E₁_ne_G₁
  have d02 := C.E₁_ne_G₂
  have d03 := C.E₁_ne_G₃
  have d12 := C.G₁_ne_G₂
  have d13 := C.G₁_ne_G₃
  have d23 := C.G₂_ne_G₃
  rcases hΩ C.mem_Ω_G₂ with h2 | h2 | h2 | h2
  · rcases hΩ C.mem_Ω_G₁ with h1 | h1 | h1 | h1
    · exact absurd (inj (h1.trans h2.symm)) d12
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact (C.no_three_cycle (mul_mem hq hu) (A := C.E₁) (B := C.G₂) (D := C.G₃)
          (by rw [act_mul, C.u_E₁, h0]) (by rw [act_mul, C.u_G₂', h3])
          (by rw [act_mul, C.u_G₃', h2]) d02).elim
    · exact absurd (inj (h1.trans h0.symm)) d01.symm
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
      · exact ⟨q, hq, h0, h2, h1, h3⟩
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
  · rcases hΩ C.mem_Ω_G₁ with h1 | h1 | h1 | h1
    · exact (C.no_three_cycle hq h0 h2 h1 d02).elim
    · exact absurd (inj (h1.trans h2.symm)) d12
    · exact absurd (inj (h1.trans h0.symm)) d01.symm
    · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
      · refine ⟨q * C.D₁.u, mul_mem hq hu, ?_, ?_, ?_, ?_⟩ <;> rw [act_mul]
        · rw [C.u_E₁, h0]
        · rw [C.u_G₂', h3]
        · rw [C.u_G₁, h1]
        · rw [C.u_G₃', h2]
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
      · exact absurd (inj (h3.trans h0.symm)) d03.symm
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
  · exact absurd (inj (h2.trans h0.symm)) d02.symm
  · rcases hΩ C.mem_Ω_G₃ with h3 | h3 | h3 | h3
    · exact (C.no_three_cycle hq h0 h2 h3 d02).elim
    · exact (C.no_three_cycle (mul_mem hq hu) (A := C.E₁) (B := C.G₂) (D := C.G₁)
        (by rw [act_mul, C.u_E₁, h0]) (by rw [act_mul, C.u_G₂', h3])
        (by
          rw [act_mul, C.u_G₁]
          rcases hΩ C.mem_Ω_G₁ with h1 | h1 | h1 | h1
          · exact h1
          · exact absurd (inj (h1.trans h3.symm)) d13
          · exact absurd (inj (h1.trans h0.symm)) d01.symm
          · exact absurd (inj (h1.trans h2.symm)) d12) d02).elim
    · exact absurd (inj (h3.trans h0.symm)) d03.symm
    · exact absurd (inj (h3.trans h2.symm)) d23.symm

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
