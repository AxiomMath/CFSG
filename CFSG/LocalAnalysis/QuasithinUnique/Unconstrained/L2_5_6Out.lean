module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Sharp
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import Certificates.Certificate110

public section

namespace CFSG.QuasithinUnique.Unc25G2

open Equiv

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

@[expose] def wordPerms (W : List (Fin 11 × List (ℕ × Bool))) : List (Perm (Fin 11)) :=
  W.map fun w => CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2

@[expose] def wordPermsT (W : List (Fin 11 × List (ℕ × Bool))) : List (Perm (Fin 11)) :=
  W.map fun w => CFSG.Sporadic.Schreier.tab
    (CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2)

theorem wordPermsT_eq (W : List (Fin 11 × List (ℕ × Bool))) : wordPermsT W = wordPerms W :=
  List.map_congr_left fun _ _ => CFSG.Sporadic.Schreier.tab_eq _

theorem cover0 : ∀ p : Fin 11, ∃ w ∈ CFSG.Sporadic.Bridge.M11.witnesses0, w.1 = p := by
  decide +kernel

theorem cover1 : ∀ p : Fin 11, p ≠ 0 → ∃ w ∈ CFSG.Sporadic.Bridge.M11.witnesses1, w.1 = p := by
  decide +kernel

theorem cover2 : ∀ p : Fin 11, p ≠ 0 → p ≠ 1 →
    ∃ w ∈ CFSG.Sporadic.Bridge.M11.witnesses2, w.1 = p := by
  decide +kernel

theorem cover3 : ∀ p : Fin 11, p ≠ 0 → p ≠ 1 → p ≠ 2 →
    ∃ w ∈ CFSG.Sporadic.Bridge.M11.witnesses3, w.1 = p := by
  decide +kernel

theorem mem_wordPerms {W : List (Fin 11 × List (ℕ × Bool))} {t : Perm (Fin 11)} :
    t ∈ wordPerms W ↔ ∃ w ∈ W, CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2 = t := by
  simp [wordPerms]

theorem sift_step {g t : Perm (Fin 11)} {b : Fin 11} (hgm : g ∈ 𝓜) (htm : t ∈ 𝓜)
    (hb : t b = g b) {F : List (Fin 11)} (hgF : ∀ p ∈ F, g p = p) (htF : ∀ p ∈ F, t p = p) :
    t⁻¹ * g ∈ 𝓜 ∧ (∀ p ∈ F, (t⁻¹ * g) p = p) ∧ (t⁻¹ * g) b = b := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ htm) hgm, fun p hp => ?_, ?_⟩
  · show t⁻¹ (g p) = p
    rw [hgF p hp]
    have := perm_inv_apply_self t p
    rwa [htF p hp] at this
  · show t⁻¹ (g b) = b
    rw [← hb]
    exact perm_inv_apply_self t b

theorem ne_of_fixed {h : Perm (Fin 11)} {p q : Fin 11} (hp : h p = p) (hne : p ≠ q) : h q ≠ p := by
  intro e
  exact hne (h.injective (hp.trans e.symm))

theorem level3
    {h : Perm (Fin 11)} (hm : h ∈ 𝓜) (h0 : h 0 = 0) (h1 : h 1 = 1) (h2 : h 2 = 2) :
    ∃ t₃ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses3, h = t₃ := by
  have n0 : h 3 ≠ 0 := ne_of_fixed h0 (by decide)
  have n1 : h 3 ≠ 1 := ne_of_fixed h1 (by decide)
  have n2 : h 3 ≠ 2 := ne_of_fixed h2 (by decide)
  obtain ⟨w, hw, hp⟩ := cover3 (h 3) n0 n1 n2
  obtain ⟨o0, o1, o2, o3⟩ := CFSG.Sporadic.Bridge.M11.witnesses_ok3 w hw
  have htm : CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2 ∈ 𝓜 :=
    CFSG.Sporadic.Bridge.M11.nativeWord_mem _
  obtain ⟨hm', hF, hb⟩ := sift_step (b := 3) (F := [0, 1, 2]) hm htm (by rw [o3, hp])
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> assumption)
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> assumption)
  have h1' := m11_eq_one_of_fix_base hm' (hF 0 (by simp)) (hF 1 (by simp)) (hF 2 (by simp)) hb
  exact ⟨_, mem_wordPerms.mpr ⟨w, hw, rfl⟩, (inv_mul_eq_one.mp h1').symm⟩

theorem level2
    {h : Perm (Fin 11)} (hm : h ∈ 𝓜) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    ∃ t₂ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses2,
      ∃ t₃ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses3, h = t₂ * t₃ := by
  have n0 : h 2 ≠ 0 := ne_of_fixed h0 (by decide)
  have n1 : h 2 ≠ 1 := ne_of_fixed h1 (by decide)
  obtain ⟨w, hw, hp⟩ := cover2 (h 2) n0 n1
  obtain ⟨o0, o1, o2⟩ := CFSG.Sporadic.Bridge.M11.witnesses_ok2 w hw
  have htm : CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2 ∈ 𝓜 :=
    CFSG.Sporadic.Bridge.M11.nativeWord_mem _
  obtain ⟨hm', hF, hb⟩ := sift_step (b := 2) (F := [0, 1]) hm htm (by rw [o2, hp])
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> assumption)
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> assumption)
  obtain ⟨t₃, ht₃, he⟩ := level3 hm' (hF 0 (by simp)) (hF 1 (by simp)) hb
  refine ⟨_, mem_wordPerms.mpr ⟨w, hw, rfl⟩, t₃, ht₃, ?_⟩
  rw [← he, mul_inv_cancel_left]

theorem level1 {h : Perm (Fin 11)} (hm : h ∈ 𝓜) (h0 : h 0 = 0) :
    ∃ t₁ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses1,
      ∃ t₂ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses2,
        ∃ t₃ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses3, h = t₁ * (t₂ * t₃) := by
  have n0 : h 1 ≠ 0 := ne_of_fixed h0 (by decide)
  obtain ⟨w, hw, hp⟩ := cover1 (h 1) n0
  obtain ⟨o0, o1⟩ := CFSG.Sporadic.Bridge.M11.witnesses_ok1 w hw
  have htm : CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2 ∈ 𝓜 :=
    CFSG.Sporadic.Bridge.M11.nativeWord_mem _
  obtain ⟨hm', hF, hb⟩ := sift_step (b := 1) (F := [0]) hm htm (by rw [o1, hp])
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'
      assumption)
    (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'
      assumption)
  obtain ⟨t₂, ht₂, t₃, ht₃, he⟩ := level2 hm' (hF 0 (by simp)) hb
  refine ⟨_, mem_wordPerms.mpr ⟨w, hw, rfl⟩, t₂, ht₂, t₃, ht₃, ?_⟩
  rw [← he, mul_inv_cancel_left]

theorem level0 {h : Perm (Fin 11)} (hm : h ∈ 𝓜) :
    ∃ t₀ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses0,
      ∃ t₁ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses1,
        ∃ t₂ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses2,
          ∃ t₃ ∈ wordPerms CFSG.Sporadic.Bridge.M11.witnesses3,
            h = t₀ * (t₁ * (t₂ * t₃)) := by
  obtain ⟨w, hw, hp⟩ := cover0 (h 0)
  have o0 := CFSG.Sporadic.Bridge.M11.witnesses_ok0 w hw
  have htm : CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen w.2 ∈ 𝓜 :=
    CFSG.Sporadic.Bridge.M11.nativeWord_mem _
  obtain ⟨hm', hF, hb⟩ := sift_step (b := 0) (F := []) hm htm (by rw [o0, hp])
    (by simp) (by simp)
  obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, he⟩ := level1 hm' hb
  refine ⟨_, mem_wordPerms.mpr ⟨w, hw, rfl⟩, t₁, ht₁, t₂, ht₂, t₃, ht₃, ?_⟩
  rw [← he, mul_inv_cancel_left]

@[expose] def pA : Perm (Fin 11) := CFSG.Sporadic.Schreier.tab (CFSG.Sporadic.Bridge.M11.gen 0)

@[expose] def pB : Perm (Fin 11) := CFSG.Sporadic.Schreier.tab (CFSG.Sporadic.Bridge.M11.gen 1)

@[expose] def pC : Perm (Fin 11) := CFSG.Sporadic.Schreier.tab (pA * pB)

@[expose] def wordN : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true)]

@[expose] def pN : Perm (Fin 11) :=
  CFSG.Sporadic.Schreier.tab (CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen wordN)

theorem pA_eq : pA = CFSG.Sporadic.Bridge.M11.gen 0 := CFSG.Sporadic.Schreier.tab_eq _

theorem pB_eq : pB = CFSG.Sporadic.Bridge.M11.gen 1 := CFSG.Sporadic.Schreier.tab_eq _

theorem pC_eq : pC = pA * pB := CFSG.Sporadic.Schreier.tab_eq _

theorem pN_eq : pN = CFSG.Sporadic.Bridge.wordProd CFSG.Sporadic.Bridge.M11.gen wordN :=
  CFSG.Sporadic.Schreier.tab_eq _

theorem pA_sq : pA * pA = 1 := by
  decide +kernel

theorem pC_pow : pC ^ 11 = 1 := by
  decide +kernel

theorem pC_ne : pC ≠ 1 := by
  decide +kernel

theorem pB_pow : pB ^ 4 = 1 := by
  decide +kernel

theorem pB_sq_ne : pB ^ 2 ≠ 1 := by
  decide +kernel

theorem pW_pow : (pA * pC * pA * pC * pC * pA * pC⁻¹) ^ 5 = 1 := by
  decide +kernel

theorem pN_conj : pN * pC * pN⁻¹ = pC ^ 3 := by
  decide +kernel

@[expose] def KProp (y : Perm (Fin 11)) : Prop :=
  y * y = 1 →
    ((y * pC) ^ 4 = 1 → (y * pC) ^ 2 ≠ 1 →
      ∃ j ∈ List.range 11, y = pC ^ j * pA * (pC ^ j)⁻¹) ∧
    ((y * pC ^ 2) ^ 4 = 1 → (y * pC ^ 2) ^ 2 ≠ 1 →
      (y * pC ^ 2 * y * pC ^ 2 * pC ^ 2 * y * (pC ^ 2)⁻¹) ^ 5 ≠ 1)

instance (y : Perm (Fin 11)) : Decidable (KProp y) := inferInstanceAs (Decidable (_ → _))

theorem finite_check :
    (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses0).all (fun t₀ =>
      (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses1).all fun t₁ =>
        (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses2).all fun t₂ =>
          (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses3).all fun t₃ =>
            decide (KProp (t₀ * (t₁ * (t₂ * t₃))))) = true := by
  decide +kernel

theorem kProp_of_mem {y : Perm (Fin 11)} (hy : y ∈ 𝓜) : KProp y := by
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩ := level0 hy
  rw [← wordPermsT_eq] at ht₀ ht₁ ht₂ ht₃
  have h := finite_check
  rw [List.all_eq_true] at h
  have h0 := h t₀ ht₀
  rw [List.all_eq_true] at h0
  have h1 := h0 t₁ ht₁
  rw [List.all_eq_true] at h1
  have h2 := h1 t₂ ht₂
  rw [List.all_eq_true] at h2
  exact of_decide_eq_true (h2 t₃ ht₃)

theorem closure_pair_eq_top' {M : Type*} [Group M] {K : Subgroup M} {x y : M}
    (hK : K = Subgroup.closure {x, y}) (hx : x ∈ K) (hy : y ∈ K) :
    Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set K) = ⊤ := by
  subst hK
  refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := {x, y}))
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

@[expose] def gA : ↥𝓜 :=
  ⟨pA, by rw [pA_eq]; exact CFSG.Sporadic.Bridge.M11.gen_mem 0⟩

@[expose] def gB : ↥𝓜 :=
  ⟨pB, by rw [pB_eq]; exact CFSG.Sporadic.Bridge.M11.gen_mem 1⟩

@[expose] def gC : ↥𝓜 := gA * gB

@[expose] def gN : ↥𝓜 :=
  ⟨pN, by rw [pN_eq]; exact CFSG.Sporadic.Bridge.M11.nativeWord_mem wordN⟩

theorem coe_gA : (gA : Perm (Fin 11)) = pA := rfl

theorem coe_gB : (gB : Perm (Fin 11)) = pB := rfl

theorem coe_gC : (gC : Perm (Fin 11)) = pC := pC_eq.symm

theorem coe_gN : (gN : Perm (Fin 11)) = pN := rfl

theorem gA_sq : gA * gA = 1 := Subtype.ext pA_sq

theorem gA_mul_gC : gA * gC = gB := by
  rw [gC, ← mul_assoc, gA_sq, one_mul]

theorem gC_pow : gC ^ 11 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_gC]
  exact pC_pow

theorem gC_ne : gC ≠ 1 := fun h => pC_ne (by rw [← coe_gC, h]; rfl)

theorem gB_pow : gB ^ 4 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_gB]
  exact pB_pow

theorem gB_sq_ne : gB ^ 2 ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  rw [Subgroup.coe_pow, coe_gB] at this
  exact pB_sq_ne this

theorem gW_pow : (gA * gC * gA * gC * gC * gA * gC⁻¹) ^ 5 = 1 := by
  apply Subtype.ext
  have := pW_pow
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, coe_gA, coe_gC,
    OneMemClass.coe_one] using this

theorem gN_conj : gN * gC * gN⁻¹ = gC ^ 3 := by
  apply Subtype.ext
  have := pN_conj
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, coe_gN, coe_gC] using this

theorem orderOf_gC : orderOf gC = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime gC_pow gC_ne

theorem closure_gA_gB : Subgroup.closure ({gA, gB} : Set ↥𝓜) = ⊤ := by
  have hK : 𝓜 = Subgroup.closure {pA, pB} := by
    rw [pA_eq, pB_eq]
    rfl
  exact closure_pair_eq_top' hK gA.2 gB.2

theorem closure_gA_gC : Subgroup.closure ({gA, gC} : Set ↥𝓜) = ⊤ := by
  rw [eq_top_iff, ← closure_gA_gB]
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [← gA_mul_gC]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem exists_conj_mem_zpowers {c' : ↥𝓜} (hc' : orderOf c' = 11) :
    ∃ g : ↥𝓜, g * c' * g⁻¹ ∈ Subgroup.zpowers gC := by
  have hfact : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hcard : Nat.card ↥𝓜 = 7920 := CFSG.Semidihedral.GL2Recognition.card_nativeM11
  have hfin : Finite ↥𝓜 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have sylow : ∀ x : ↥𝓜, orderOf x = 11 →
      ∃ P : Sylow 11 ↥𝓜, (P : Subgroup ↥𝓜) = Subgroup.zpowers x := by
    intro x hx
    have hcx : Nat.card ↥(Subgroup.zpowers x) = 11 := by rw [Nat.card_zpowers, hx]
    have hp : IsPGroup 11 ↥(Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [hcx]; norm_num)
    have hidx : ¬ 11 ∣ (Subgroup.zpowers x).index := by
      have h1 := Subgroup.card_mul_index (Subgroup.zpowers x)
      rw [hcx, hcard] at h1
      omega
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨P', hP'⟩ := sylow c' hc'
  obtain ⟨P, hP⟩ := sylow gC orderOf_gC
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥𝓜 P' P
  refine ⟨g, ?_⟩
  have hmem : c' ∈ (P' : Subgroup ↥𝓜) := by
    rw [hP']
    exact Subgroup.mem_zpowers c'
  have h2 : g * c' * g⁻¹ ∈ ((g • P' : Sylow 11 ↥𝓜) : Subgroup ↥𝓜) := by
    rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨c', hmem, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg, hP] at h2
  exact h2

theorem conj_pow_gN
    (j : ℕ) : gN ^ j * gC * (gN ^ j)⁻¹ = gC ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : gN ^ (j + 1) * gC * (gN ^ (j + 1))⁻¹ =
        gN * (gN ^ j * gC * (gN ^ j)⁻¹) * gN⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [h1, ih, ← conj_pow, gN_conj, ← pow_mul, pow_succ', mul_comm]

theorem exists_conj_to_small (r : ℕ) (hr0 : 0 < r) (hr : r < 11) :
    ∃ h : ↥𝓜, ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ h * gC ^ r * h⁻¹ = gC ^ s := by
  have hj : ∃ j : ℕ, j < 5 ∧ ((3 ^ j * r) % 11 = 1 ∨ (3 ^ j * r) % 11 = 2) := by
    interval_cases r <;> decide
  obtain ⟨j, -, hj⟩ := hj
  refine ⟨gN ^ j, (3 ^ j * r) % 11, hj, ?_⟩
  have hmod : gC ^ ((3 ^ j * r) % 11) = gC ^ (3 ^ j * r) := by
    have := pow_mod_orderOf gC (3 ^ j * r)
    rwa [orderOf_gC] at this
  rw [← conj_pow, conj_pow_gN, ← pow_mul, hmod]

theorem coe_pow_eq_one_iff {u : ↥𝓜} {n : ℕ} : u ^ n = 1 ↔ (u : Perm (Fin 11)) ^ n = 1 := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
  · intro h
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h

theorem aut_inner
    (φ : MulAut ↥𝓜) : ∃ g : ↥𝓜, ∀ x, φ x = g * x * g⁻¹ := by
  have hc' : orderOf (φ gC) = 11 := by rw [MulEquiv.orderOf_eq, orderOf_gC]
  obtain ⟨g₁, hg₁⟩ := exists_conj_mem_zpowers hc'
  have hne : g₁ * φ gC * g₁⁻¹ ≠ 1 := by
    intro h1
    have h2 : φ gC = 1 := by
      have := congrArg (fun z => g₁⁻¹ * z * g₁) h1
      simpa [mul_assoc] using this
    have : gC = 1 := φ.injective (by rw [h2, map_one])
    exact gC_ne this
  obtain ⟨r, hr, hrx⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hg₁)
  rw [Finset.mem_range, orderOf_gC] at hr
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      apply hne
      rw [← hrx, h0, pow_zero]
    · exact h0
  obtain ⟨h₂, s, hs, hh₂⟩ := exists_conj_to_small r hr0 hr
  let h : ↥𝓜 := h₂ * g₁
  let ψ : MulAut ↥𝓜 := φ.trans (MulAut.conj h)
  have hψ : ∀ x, ψ x = h * φ x * h⁻¹ := fun x => rfl
  have hψc : ψ gC = gC ^ s := by
    rw [hψ]
    have : h * φ gC * h⁻¹ = h₂ * (g₁ * φ gC * g₁⁻¹) * h₂⁻¹ := by
      simp only [h]
      group
    rw [this, ← hrx]
    exact hh₂
  set y : ↥𝓜 := ψ gA with hy
  have hy2 : y * y = 1 := by rw [hy, ← map_mul, gA_sq, map_one]
  have hyc : y * gC ^ s = ψ gB := by rw [← hψc, hy, ← map_mul, gA_mul_gC]
  have h4 : (y * gC ^ s) ^ 4 = 1 := by rw [hyc, ← map_pow, gB_pow, map_one]
  have h2 : (y * gC ^ s) ^ 2 ≠ 1 := by
    rw [hyc, ← map_pow]
    intro h'
    exact gB_sq_ne (ψ.injective (by rw [h', map_one]))
  have hw : (y * gC ^ s * y * gC ^ s * gC ^ s * y * (gC ^ s)⁻¹) ^ 5 = 1 := by
    have e : y * gC ^ s * y * gC ^ s * gC ^ s * y * (gC ^ s)⁻¹ =
        ψ (gA * gC * gA * gC * gC * gA * gC⁻¹) := by
      simp only [map_mul, map_inv, hψc, hy]
    rw [e, ← map_pow, gW_pow, map_one]
  have hK := kProp_of_mem (y := (y : Perm (Fin 11))) y.2
  have hy2' : (y : Perm (Fin 11)) * (y : Perm (Fin 11)) = 1 := congrArg Subtype.val hy2
  have hK' := hK hy2'
  rcases hs with rfl | rfl
  ·
    have h4' : ((y : Perm (Fin 11)) * pC) ^ 4 = 1 := by
      have := coe_pow_eq_one_iff.mp h4
      simpa [coe_gC] using this
    have h2' : ((y : Perm (Fin 11)) * pC) ^ 2 ≠ 1 := by
      intro h'
      apply h2
      rw [coe_pow_eq_one_iff]
      simpa [coe_gC] using h'
    obtain ⟨j, -, hj⟩ := hK'.1 h4' h2'
    have hyj : y = gC ^ j * gA * (gC ^ j)⁻¹ := by
      apply Subtype.ext
      simpa [coe_gC, coe_gA] using hj
    have hcomm : gC ^ j * gC * (gC ^ j)⁻¹ = gC := by
      have hc : gC ^ j * gC = gC * gC ^ j := (Commute.self_pow gC j).symm.eq
      rw [hc, mul_inv_cancel_right]
    have hconj : ∀ x, ψ x = (gC ^ j) * x * (gC ^ j)⁻¹ := by
      have hEq := MonoidHom.eqOn_closure (f := ψ.toMonoidHom)
        (g := (MulAut.conj (gC ^ j)).toMonoidHom) (s := ({gA, gC} : Set ↥𝓜)) (by
          intro x hx
          rcases hx with rfl | hx
          · exact hyj
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            show ψ gC = gC ^ j * gC * (gC ^ j)⁻¹
            rw [hcomm, hψc, pow_one])
      rw [closure_gA_gC] at hEq
      intro x
      exact hEq (Subgroup.mem_top x)
    refine ⟨h⁻¹ * gC ^ j, fun x => ?_⟩
    have hx := hconj x
    rw [hψ] at hx
    have : φ x = h⁻¹ * (gC ^ j * x * (gC ^ j)⁻¹) * h := by
      rw [← hx]
      group
    rw [this]
    group
  ·
    exfalso
    have h4' : ((y : Perm (Fin 11)) * pC ^ 2) ^ 4 = 1 := by
      have := coe_pow_eq_one_iff.mp h4
      simpa [coe_gC] using this
    have h2' : ((y : Perm (Fin 11)) * pC ^ 2) ^ 2 ≠ 1 := by
      intro h'
      apply h2
      rw [coe_pow_eq_one_iff]
      simpa [coe_gC] using h'
    apply hK'.2 h4' h2'
    have := coe_pow_eq_one_iff.mp hw
    simpa [coe_gC] using this

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

theorem m11OutTrivial : M11OutTrivial := by
  intro G _ L ⟨e₀⟩ g hg
  let e : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e₀
  let φ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩
  obtain ⟨m, hm⟩ := Unc25G2.aut_inner (MulAut.congr e φ)
  refine ⟨((e.symm m : ↥L) : G), (e.symm m).2, fun x hx => ?_⟩
  have h1 : (φ ⟨x, hx⟩ : ↥L) = e.symm m * ⟨x, hx⟩ * (e.symm m)⁻¹ := by
    apply e.injective
    have h2 := hm (e ⟨x, hx⟩)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h2
  have h3 := congrArg Subtype.val h1
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  simpa using h3

end CFSG.QuasithinUnique
