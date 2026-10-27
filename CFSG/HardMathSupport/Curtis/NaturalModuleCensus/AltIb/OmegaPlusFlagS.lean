module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusFlag

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell (flag_eq_isoFlag Jfl)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (isoFlag stabilizer mem_isoFlag mem_stabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (mem_flagStabilizer)

variable {n : ℕ} {F : Type} [Field F]

abbrev act (A : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) : Fin n ⊕ Fin n → F :=
  ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w

theorem act_mul (A B : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) :
    act (A * B) w = act A (act B w) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_inv_act (A : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) : act A⁻¹ (act A w) = w := by
  rw [← act_mul, inv_mul_cancel]
  simp [act]

theorem act_act_inv (A : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) : act A (act A⁻¹ w) = w := by
  rw [← act_mul, mul_inv_cancel]
  simp [act]

theorem act_Q (A : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F (act A w) = StatedQuadPlus n F w := om_preserves A.2 w

theorem act_polar (A : ↥(Om n F)) (u v : Fin n ⊕ Fin n → F) :
    quadPlusPolar n F (act A u) (act A v) = quadPlusPolar n F u v :=
  (quadPlusForm n F).polar_map_of_Q (g := Matrix.toLin' ((A : GL (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) (fun w => om_preserves A.2 w) u v

theorem act_add (A : ↥(Om n F)) (u v : Fin n ⊕ Fin n → F) :
    act A (u + v) = act A u + act A v := Matrix.mulVec_add _ _ _

theorem act_smul (A : ↥(Om n F)) (c : F) (u : Fin n ⊕ Fin n → F) :
    act A (c • u) = c • act A u := Matrix.mulVec_smul _ _ _

@[expose] def stSub (n : ℕ) (F : Type) [Field F] (W : Submodule F (Fin n ⊕ Fin n → F)) :
    Subgroup ↥(Om n F) where
  carrier := {A | ∀ w, act A w ∈ W ↔ w ∈ W}
  mul_mem' := by
    intro A B hA hB w
    rw [act_mul, hA, hB]
  one_mem' := by
    intro w
    simp [act]
  inv_mem' := by
    intro A hA w
    have := hA (act A⁻¹ w)
    rw [act_act_inv] at this
    exact this.symm

theorem mem_stSub {W : Submodule F (Fin n ⊕ Fin n → F)} {A : ↥(Om n F)} :
    A ∈ stSub n F W ↔ ∀ w, act A w ∈ W ↔ w ∈ W := Iff.rfl

theorem stabW_eq_stSub (k : Fin n) : stabW n F k = stSub n F (flagSpace F (nodeCowt n k)) :=
  Subgroup.ext fun _ => Iff.rfl

theorem mem_stSub_iff_forall {W : Submodule F (Fin n ⊕ Fin n → F)} {A : ↥(Om n F)} :
    A ∈ stSub n F W ↔ ∀ w ∈ W, act A w ∈ W ∧ act A⁻¹ w ∈ W := by
  constructor
  · intro h w hw
    exact ⟨(h w).2 hw, (mem_stSub.1 (inv_mem h) w).2 hw⟩
  · intro h w
    refine ⟨fun hw => ?_, fun hw => (h w hw).1⟩
    have := (h _ hw).2
    rwa [act_inv_act] at this

theorem omSp_mem_stabilizer_iff [CharP F 2] (W : Submodule F (Fin n ⊕ Fin n → F)) (A : ↥(Om n F)) :
    omSp A ∈ stabilizer n F W ↔ A ∈ stSub n F W := by
  rw [mem_stabilizer]
  constructor
  · intro h w
    constructor
    · intro hw
      rw [← h] at hw
      obtain ⟨x, hx, hxw⟩ := hw
      change act A x = act A w at hxw
      have := congrArg (act A⁻¹) hxw
      rw [act_inv_act, act_inv_act] at this
      rwa [← this]
    · intro hw
      have : act A w ∈ Submodule.map (Matrix.mulVecLin ((A : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) W := ⟨w, hw, rfl⟩
      exact h.le this
  · intro h
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (h v).2 hv
    · intro v hv
      refine ⟨act A⁻¹ v, ?_, act_act_inv A v⟩
      have := h (act A⁻¹ v)
      rw [act_act_inv] at this
      exact this.1 hv

theorem mem_JO_iff [CharP F 2] {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (A : ↥(Om n F)) :
    A ∈ JO n F S ↔ ∀ i ∈ S, A ∈ stSub n F (isoFlag n F i) := by
  rw [mem_JO, Jfl, mem_flagStabilizer]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_coe]
  refine forall_congr' fun hi => ?_
  rw [flag_eq_isoFlag (hS i hi).2, omSp_mem_stabilizer_iff]

theorem mem_JK_iff {K : Set (Fin n)} {A : ↥(Om n F)} :
    A ∈ JK n F K ↔ ∀ k ∈ K, A ∈ stSub n F (flagSpace F (nodeCowt n k)) := by
  rw [mem_JK]
  simp only [stabW_eq_stSub]

theorem flagSpace_eq_isoFlag_of_lt {k : Fin n} (hk : k.val + 2 < n) :
    flagSpace F (nodeCowt n k) = isoFlag n F (k.val + 1) := by
  ext v
  rw [mem_flagSpace_iff, mem_isoFlag]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_contra hne
      have := h _ hne
      simp only [flagWt, nodeCowt, hk, ite_true] at this
      split_ifs at this <;> omega
    · by_contra hne
      have := h _ hne
      simp only [flagWt, nodeCowt, hk, ite_true] at this
      split_ifs at this <;> omega
  · rintro ⟨h1, h2⟩ a ha
    rcases a with j | j
    · by_contra hne
      have := h2 j (by simp only [flagWt, nodeCowt, hk, ite_true] at hne; split_ifs at hne <;> omega)
      exact ha this
    · exact absurd (h1 j) ha

theorem flagSpace_eq_isoFlag_of_last {k : Fin n} (hk : k.val + 1 = n) :
    flagSpace F (nodeCowt n k) = isoFlag n F n := by
  have h1 : ¬ k.val + 2 < n := by omega
  have h2 : ¬ k.val + 2 = n := by omega
  ext v
  rw [mem_flagSpace_iff, mem_isoFlag]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_contra hne
      have := h _ hne
      simp only [flagWt, nodeCowt, h1, h2, ite_false] at this
      omega
    · have := j.isLt
      omega
  · rintro ⟨h1', -⟩ a ha
    rcases a with j | j
    · simp [flagWt, nodeCowt, h1, h2]
    · exact absurd (h1' j) ha

theorem mem_flagSpace_of_secondLast {k : Fin n} (hk : k.val + 2 = n) (v : Fin n ⊕ Fin n → F) :
    v ∈ flagSpace F (nodeCowt n k) ↔
      (∀ j : Fin n, j.val + 1 = n → v (Sum.inl j) = 0) ∧
        ∀ j : Fin n, j.val + 1 ≠ n → v (Sum.inr j) = 0 := by
  have h1 : ¬ k.val + 2 < n := by omega
  rw [mem_flagSpace_iff]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · by_contra hne
      have := h _ hne
      simp only [flagWt, nodeCowt, hk, ite_true, hj] at this
      omega
    · by_contra hne
      have := h _ hne
      simp only [flagWt, nodeCowt, hk, ite_true] at this
      split_ifs at this <;> omega
  · rintro ⟨hl, hr⟩ a ha
    rcases a with j | j
    · by_contra hne
      have hj : j.val + 1 ≠ n := fun hj => ha (hl j hj)
      simp only [flagWt, nodeCowt, hk, ite_true, ite_false, hj] at hne
      omega
    · by_contra hne
      have hj : j.val + 1 = n := by
        by_contra hj
        exact ha (hr j hj)
      simp only [flagWt, nodeCowt, hk, ite_true, hj] at hne
      omega

theorem inf_secondLast_last {k₁ k₂ : Fin n} (h₁ : k₁.val + 2 = n) (h₂ : k₂.val + 1 = n) {i : ℕ}
    (hi : i + 1 = n) :
    flagSpace F (nodeCowt n k₁) ⊓ flagSpace F (nodeCowt n k₂) = isoFlag n F i := by
  ext v
  rw [Submodule.mem_inf, mem_flagSpace_of_secondLast h₁, flagSpace_eq_isoFlag_of_last h₂,
    mem_isoFlag, mem_isoFlag]
  constructor
  · rintro ⟨⟨hl, hr⟩, h1, -⟩
    refine ⟨h1, fun j hj => hl j ?_⟩
    have := j.isLt
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun j hj => h2 j (by omega), fun j _ => h1 j⟩, h1, fun j hj => ?_⟩
    have := j.isLt
    omega

theorem mem_stSub_inf {W₁ W₂ : Submodule F (Fin n ⊕ Fin n → F)} {A : ↥(Om n F)}
    (h₁ : A ∈ stSub n F W₁) (h₂ : A ∈ stSub n F W₂) : A ∈ stSub n F (W₁ ⊓ W₂) := by
  intro w
  rw [Submodule.mem_inf, Submodule.mem_inf, h₁ w, h₂ w]

theorem polar_single_inl_right (u : Fin n ⊕ Fin n → F) (a : Fin n) :
    quadPlusPolar n F u (Pi.single (Sum.inl a) 1) = u (Sum.inr a) := by
  simp [quadPlusPolar, Pi.single_apply]

theorem polar_single_inr_left (v : Fin n ⊕ Fin n → F) (m : Fin n) :
    quadPlusPolar n F (Pi.single (Sum.inr m) 1) v = v (Sum.inl m) := by
  simp [quadPlusPolar, Pi.single_apply]

theorem isoFlag_mem_of_single_inl {i : ℕ} {a : Fin n} (ha : a.val < i) :
    (Pi.single (Sum.inl a) 1 : Fin n ⊕ Fin n → F) ∈ isoFlag n F i := by
  rw [mem_isoFlag]
  refine ⟨fun j => by simp, fun j hj => ?_⟩
  exact Pi.single_eq_of_ne (by
    intro h
    have := Sum.inl_injective h
    subst this
    omega) _

theorem act_single_inr_last {m : Fin n} (hm : m.val + 1 = n) {A : ↥(Om n F)}
    (h₁ : A ∈ stSub n F (isoFlag n F (n - 1))) (h₂ : A ∈ stSub n F (isoFlag n F n)) :
    act A (Pi.single (Sum.inr m) 1) (Sum.inl m) = 0 ∧
      ∀ j : Fin n, j.val + 1 ≠ n → act A (Pi.single (Sum.inr m) 1) (Sum.inr j) = 0 := by
  set u := act A (Pi.single (Sum.inr m) 1) with hu
  have hzero : ∀ j : Fin n, j.val + 1 ≠ n → u (Sum.inr j) = 0 := by
    intro j hj
    have hjlt : j.val < n - 1 := by have := j.isLt; omega
    have hej := isoFlag_mem_of_single_inl (F := F) (a := j) hjlt
    have hmem := (mem_stSub_iff_forall.1 h₁ _ hej).2
    have hm0 : act A⁻¹ (Pi.single (Sum.inl j) 1) (Sum.inl m) = 0 :=
      ((mem_isoFlag.1 hmem).2) m (by omega)
    have := act_polar A (Pi.single (Sum.inr m) 1) (act A⁻¹ (Pi.single (Sum.inl j) 1))
    rw [act_act_inv, polar_single_inr_left, hm0, ← hu, polar_single_inl_right] at this
    exact this
  refine ⟨?_, hzero⟩
  set d := act A (Pi.single (Sum.inl m) 1) with hd
  have hdF : ∀ i, d (Sum.inr i) = 0 := by
    have hem := isoFlag_mem_of_single_inl (F := F) (a := m) (i := n) m.isLt
    exact (mem_isoFlag.1 ((h₂ _).2 hem)).1
  have hpol : d (Sum.inl m) * u (Sum.inr m) = 1 := by
    have := act_polar A (Pi.single (Sum.inr m) 1) (Pi.single (Sum.inl m) 1)
    rw [← hu, ← hd, polar_single_inr_left] at this
    simp only [Pi.single_eq_same] at this
    rw [← this]
    simp only [quadPlusPolar]
    rw [Finset.sum_eq_single m]
    · simp [hdF m]
    · intro i _ him
      have hi : i.val + 1 ≠ n := fun h => him (Fin.ext (by omega))
      simp [hdF i, hzero i hi]
    · simp
  have hQ : u (Sum.inl m) * u (Sum.inr m) = 0 := by
    have := act_Q A (Pi.single (Sum.inr m) 1)
    rw [← hu] at this
    have h0 : StatedQuadPlus n F (Pi.single (Sum.inr m) 1) = 0 := by
      simp [StatedQuadPlus]
    rw [h0] at this
    rw [← this]
    simp only [StatedQuadPlus]
    rw [Finset.sum_eq_single m]
    · intro i _ him
      have hi : i.val + 1 ≠ n := fun h => him (Fin.ext (by omega))
      simp [hzero i hi]
    · simp
  have hne : u (Sum.inr m) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpol
    exact zero_ne_one hpol
  exact (mul_eq_zero.1 hQ).resolve_right hne

theorem mem_stSub_secondLast {k : Fin n} (hk : k.val + 2 = n) {i : ℕ} (hi : i + 1 = n)
    {A : ↥(Om n F)} (h₁ : A ∈ stSub n F (isoFlag n F i)) (h₂ : A ∈ stSub n F (isoFlag n F n)) :
    A ∈ stSub n F (flagSpace F (nodeCowt n k)) := by
  have hi' : i = n - 1 := by omega
  subst hi'
  have hn1 : 1 ≤ n := by omega
  let m : Fin n := ⟨n - 1, by omega⟩
  have hm : m.val + 1 = n := by simp [m]; omega
  have key : ∀ B : ↥(Om n F), B ∈ stSub n F (isoFlag n F (n - 1)) → B ∈ stSub n F (isoFlag n F n) →
      ∀ w ∈ flagSpace F (nodeCowt n k), act B w ∈ flagSpace F (nodeCowt n k) := by
    intro B hB1 hB2 w hw
    rw [mem_flagSpace_of_secondLast hk] at hw
    obtain ⟨hwl, hwr⟩ := hw
    set c := w (Sum.inr m) with hc
    set w' : Fin n ⊕ Fin n → F := w - c • Pi.single (Sum.inr m) 1 with hw'
    have hw'F : w' ∈ isoFlag n F (n - 1) := by
      rw [mem_isoFlag]
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · by_cases hjm : j = m
        · subst hjm
          simp [hw', hc]
        · have hj : j.val + 1 ≠ n := fun h => hjm (Fin.ext (by simp [m]; omega))
          simp [hw', hwr j hj, hjm]
      · have hj : j.val + 1 = n := by have := j.isLt; omega
        have hjm : j = m := Fin.ext (by simp [m]; omega)
        subst hjm
        simp [hw', hwl _ hm]
    have hBw' := ((mem_stSub_iff_forall.1 hB1) w' hw'F).1
    obtain ⟨hBl, hBr⟩ := mem_isoFlag.1 hBw'
    have hu := act_single_inr_last hm hB1 hB2
    have hwdec : w = w' + c • Pi.single (Sum.inr m) 1 := by
      simp [hw']
    rw [hwdec, act_add, act_smul, mem_flagSpace_of_secondLast hk]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hjm : j = m := Fin.ext (by simp [m]; omega)
      rw [hjm]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hBr m (by simp [m]), hu.1, mul_zero, zero_add]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hBl j, hu.2 j hj, mul_zero, zero_add]
  rw [mem_stSub_iff_forall]
  intro w hw
  exact ⟨key A h₁ h₂ w hw, key A⁻¹ (inv_mem h₁) (inv_mem h₂) w hw⟩

open scoped Classical in
@[expose] noncomputable def normSet (n : ℕ) (K : Set (Fin n)) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun i =>
    (∃ k ∈ K, k.val + 2 < n ∧ i = k.val + 1) ∨
    (i + 1 = n ∧ ∃ ka ∈ K, ∃ kb ∈ K, ka.val + 2 = n ∧ kb.val + 1 = n) ∨
    (i = n ∧ ∃ kb ∈ K, kb.val + 1 = n)

theorem mem_normSet {K : Set (Fin n)} {i : ℕ} :
    i ∈ normSet n K ↔ i ≤ n ∧
      ((∃ k ∈ K, k.val + 2 < n ∧ i = k.val + 1) ∨
       (i + 1 = n ∧ ∃ ka ∈ K, ∃ kb ∈ K, ka.val + 2 = n ∧ kb.val + 1 = n) ∨
       (i = n ∧ ∃ kb ∈ K, kb.val + 1 = n)) := by
  simp only [normSet, Finset.mem_filter, Finset.mem_range]
  rw [Nat.lt_succ_iff]

theorem exists_JO_of_JK_normalized [CharP F 2] (hn : 4 ≤ n) {K : Set (Fin n)} (hK : K.Nonempty)
    (hnorm : ∀ ka ∈ K, ka.val + 2 = n → ∃ kb ∈ K, kb.val + 1 = n) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, 1 ≤ i ∧ i ≤ n) ∧ (n - 1 ∈ S → n ∈ S) ∧
      JK n F K = JO n F S := by
  have hSn : ∀ kb ∈ K, kb.val + 1 = n → n ∈ normSet n K := fun kb hkb h =>
    mem_normSet.2 ⟨le_rfl, Or.inr (Or.inr ⟨rfl, kb, hkb, h⟩)⟩
  have hbd : ∀ i ∈ normSet n K, 1 ≤ i ∧ i ≤ n := by
    intro i hi
    obtain ⟨hin, hP⟩ := mem_normSet.1 hi
    refine ⟨?_, hin⟩
    rcases hP with ⟨k, -, -, rfl⟩ | ⟨h, -⟩ | ⟨rfl, -⟩ <;> omega
  refine ⟨normSet n K, ?_, hbd, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hK
    have := k.isLt
    by_cases h1 : k.val + 2 < n
    · exact ⟨k.val + 1, mem_normSet.2 ⟨by omega, Or.inl ⟨k, hk, h1, rfl⟩⟩⟩
    · by_cases h2 : k.val + 2 = n
      · obtain ⟨kb, hkb, h⟩ := hnorm k hk h2
        exact ⟨n, hSn kb hkb h⟩
      · exact ⟨n, hSn k hk (by omega)⟩
  · intro h
    obtain ⟨hin, hP⟩ := mem_normSet.1 h
    rcases hP with ⟨k, -, hk, h'⟩ | ⟨-, ka, -, kb, hkb, -, h'⟩ | ⟨h', -⟩
    · omega
    · exact hSn kb hkb h'
    · omega
  · ext A
    rw [mem_JK_iff, mem_JO_iff hbd]
    constructor
    · intro hA i hi
      obtain ⟨hin, hP⟩ := mem_normSet.1 hi
      rcases hP with ⟨k, hk, hk2, rfl⟩ | ⟨hi1, ka, hka, kb, hkb, hka2, hkb1⟩ | ⟨rfl, kb, hkb, hkb1⟩
      · have := hA k hk
        rwa [flagSpace_eq_isoFlag_of_lt hk2] at this
      · have := mem_stSub_inf (hA ka hka) (hA kb hkb)
        rwa [inf_secondLast_last hka2 hkb1 hi1] at this
      · have := hA kb hkb
        rwa [flagSpace_eq_isoFlag_of_last hkb1] at this
    · intro hA k hk
      have hkn := k.isLt
      by_cases h1 : k.val + 2 < n
      · have := hA (k.val + 1) (mem_normSet.2 ⟨by omega, Or.inl ⟨k, hk, h1, rfl⟩⟩)
        rwa [← flagSpace_eq_isoFlag_of_lt h1] at this
      · by_cases h2 : k.val + 2 = n
        · obtain ⟨kb, hkb, h⟩ := hnorm k hk h2
          have hA1 := hA (n - 1) (mem_normSet.2 ⟨by omega,
            Or.inr (Or.inl ⟨by omega, k, hk, kb, hkb, h2, h⟩)⟩)
          have hA2 := hA n (hSn kb hkb h)
          exact mem_stSub_secondLast h2 (i := n - 1) (by omega) hA1 hA2
        · have h3 : k.val + 1 = n := by omega
          have := hA n (hSn k hk h3)
          rwa [← flagSpace_eq_isoFlag_of_last h3] at this

@[expose] def swapE (m : Fin n) : Equiv.Perm (Fin n ⊕ Fin n) := Equiv.swap (Sum.inl m) (Sum.inr m)

theorem swapE_swapE (m : Fin n) (x : Fin n ⊕ Fin n) : swapE m (swapE m x) = x :=
  Equiv.swap_apply_self _ _ _

theorem swapE_inl {m : Fin n} (hm : m.val + 1 = n) (j : Fin n) :
    swapE m (Sum.inl j) = if j.val + 1 = n then Sum.inr m else Sum.inl j := by
  have : (j = m) ↔ j.val + 1 = n := ⟨fun h => h ▸ hm, fun h => Fin.ext (by omega)⟩
  simp [swapE, Equiv.swap_apply_def, this]

theorem swapE_inr {m : Fin n} (hm : m.val + 1 = n) (j : Fin n) :
    swapE m (Sum.inr j) = if j.val + 1 = n then Sum.inl m else Sum.inr j := by
  have : (j = m) ↔ j.val + 1 = n := ⟨fun h => h ▸ hm, fun h => Fin.ext (by omega)⟩
  simp [swapE, Equiv.swap_apply_def, this]

@[expose] def swapMat (F : Type) [Field F] (m : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.of fun i j => if swapE m i = j then 1 else 0

theorem swapMat_mulVec (m : Fin n) (w : Fin n ⊕ Fin n → F) :
    swapMat F m *ᵥ w = w ∘ swapE m := by
  ext i
  simp [swapMat, Matrix.mulVec, dotProduct]

theorem swapMat_mul_self (m : Fin n) : swapMat F m * swapMat F m = 1 := by
  ext i j
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, swapE_swapE, Matrix.one_apply]

theorem Q_swap (m : Fin n) (hm : m.val + 1 = n) (w : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F (w ∘ swapE m) = StatedQuadPlus n F w := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val + 1 = n
  · obtain rfl : i = m := Fin.ext (by omega)
    simp [swapE_inl hm, swapE_inr hm, hm, mul_comm]
  · simp [swapE_inl hm, swapE_inr hm, hi]
@[expose] def swapGL (F : Type) [Field F] (m : Fin n) : GL (Fin n ⊕ Fin n) F :=
  ⟨swapMat F m, swapMat F m, swapMat_mul_self m, swapMat_mul_self m⟩

theorem coe_swapGL (m : Fin n) :
    ((swapGL F m : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      swapMat F m := rfl

theorem coe_swapGL_inv (m : Fin n) :
    (((swapGL F m)⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      swapMat F m := rfl

theorem swapGL_mem_orthGroup {m : Fin n} (hm : m.val + 1 = n) :
    swapGL F m ∈ orthGroup (StatedQuadPlus n F) :=
  Subgroup.subset_closure fun w => by
    show StatedQuadPlus n F (swapMat F m *ᵥ w) = StatedQuadPlus n F w
    rw [swapMat_mulVec]
    exact Q_swap m hm w

theorem map_conj_eq_of_mem {M : Type*} [Group M] {G : Subgroup M} {τ : M} (hτ : τ ∈ G) :
    G.map (MulAut.conj τ).toMonoidHom = G := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := mul_mem (mul_mem hτ h) (inv_mem hτ)
    simpa [mul_assoc] using this
  · intro h
    exact mul_mem (mul_mem (inv_mem hτ) h) hτ

theorem om_map_conj {m : Fin n} (hm : m.val + 1 = n) :
    (Om n F).map (MulAut.conj (swapGL F m)).toMonoidHom = Om n F := by
  change ⁅orthGroup (StatedQuadPlus n F), orthGroup (StatedQuadPlus n F)⁆.map _ =
    ⁅orthGroup (StatedQuadPlus n F), orthGroup (StatedQuadPlus n F)⁆
  rw [Subgroup.map_commutator, map_conj_eq_of_mem (swapGL_mem_orthGroup hm)]

@[expose] noncomputable def swapAut {m : Fin n} (hm : m.val + 1 = n) :
    ↥(Om n F) ≃* ↥(Om n F) :=
  ((MulAut.conj (swapGL F m)).subgroupMap (Om n F)).trans
    (MulEquiv.subgroupCongr (om_map_conj hm))

theorem act_swapAut {m : Fin n} (hm : m.val + 1 = n) (C : ↥(Om n F)) (w : Fin n ⊕ Fin n → F) :
    act (swapAut hm C) w = swapMat F m *ᵥ (act C (swapMat F m *ᵥ w)) := by
  change ((((swapGL F m * (C : GL (Fin n ⊕ Fin n) F) * (swapGL F m)⁻¹ : GL (Fin n ⊕ Fin n) F)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) *ᵥ w = _
  rw [Units.val_mul, Units.val_mul, coe_swapGL, coe_swapGL_inv, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

omit [Field F] in
theorem comp_swapE_swapE (m : Fin n) (w : Fin n ⊕ Fin n → F) :
    (w ∘ swapE m) ∘ swapE m = w := by
  ext x
  simp [swapE_swapE]

theorem mem_stSub_swapAut {m : Fin n} (hm : m.val + 1 = n) (C : ↥(Om n F))
    (W : Submodule F (Fin n ⊕ Fin n → F)) :
    swapAut hm C ∈ stSub n F W ↔
      C ∈ stSub n F (W.comap (LinearMap.funLeft F F (swapE m))) := by
  rw [mem_stSub, mem_stSub]
  have hf : ∀ u : Fin n ⊕ Fin n → F, LinearMap.funLeft F F (swapE m) u = u ∘ swapE m :=
    fun _ => rfl
  simp only [act_swapAut, swapMat_mulVec, Submodule.mem_comap, hf]
  constructor
  · intro h w'
    have := h (w' ∘ swapE m)
    rwa [comp_swapE_swapE] at this
  · intro h w
    have := h (w ∘ swapE m)
    rwa [comp_swapE_swapE] at this

theorem flagWt_swapE {m m' : Fin n} (hm : m.val + 1 = n) (hm' : m'.val + 2 = n) (k : Fin n)
    (b : Fin n ⊕ Fin n) :
    flagWt (nodeCowt n k) (swapE m b) = flagWt (nodeCowt n (Equiv.swap m' m k)) b := by
  have hk := k.isLt
  have hsw : Equiv.swap m' m k = if k.val + 2 < n then k else if k.val + 2 = n then m else m' := by
    by_cases h1 : k.val + 2 < n
    · have hkm' : k ≠ m' := fun h => by subst h; omega
      have hkm : k ≠ m := fun h => by subst h; omega
      rw [Equiv.swap_apply_of_ne_of_ne hkm' hkm, ite_eq_left h1]
    · by_cases h2 : k.val + 2 = n
      · have : k = m' := Fin.ext (by omega)
        rw [this, Equiv.swap_apply_left, ite_eq_right (by omega), ite_eq_left (by omega)]
      · have : k = m := Fin.ext (by omega)
        rw [this, Equiv.swap_apply_right, ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hsw]
  rcases b with j | j
  · rw [swapE_inl hm]
    by_cases hj : j.val + 1 = n
    · simp only [hj, ite_true, flagWt, nodeCowt]
      split_ifs <;> simp_all <;> omega
    · simp only [hj, ite_false, flagWt, nodeCowt]
      split_ifs <;> (simp_all; try omega)
  · rw [swapE_inr hm]
    by_cases hj : j.val + 1 = n
    · simp only [hj, ite_true, flagWt, nodeCowt]
      split_ifs <;> simp_all <;> omega
    · simp only [hj, ite_false, flagWt, nodeCowt]
      split_ifs <;> (simp_all; try omega)

theorem comap_flagSpace_swapE {m m' : Fin n} (hm : m.val + 1 = n) (hm' : m'.val + 2 = n)
    (k : Fin n) :
    (flagSpace F (nodeCowt n k)).comap (LinearMap.funLeft F F (swapE m)) =
      flagSpace F (nodeCowt n (Equiv.swap m' m k)) := by
  have hf : ∀ u : Fin n ⊕ Fin n → F, LinearMap.funLeft F F (swapE m) u = u ∘ swapE m :=
    fun _ => rfl
  ext u
  rw [Submodule.mem_comap, hf, mem_flagSpace_iff, mem_flagSpace_iff]
  constructor
  · intro h b hb
    have := h (swapE m b) (by simpa [Function.comp, swapE_swapE] using hb)
    rwa [flagWt_swapE hm hm' k b] at this
  · intro h a ha
    have := h (swapE m a) ha
    rwa [← flagWt_swapE hm hm' k (swapE m a), swapE_swapE] at this

theorem map_JK_swapAut {m m' : Fin n} (hm : m.val + 1 = n) (hm' : m'.val + 2 = n)
    (K : Set (Fin n)) :
    (JK n F K).map (swapAut hm).toMonoidHom = JK n F (Equiv.swap m' m ⁻¹' K) := by
  ext B
  obtain ⟨C, rfl⟩ := (swapAut hm).surjective B
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_JK_iff, mem_JK_iff]
  simp only [mem_stSub_swapAut hm, comap_flagSpace_swapE hm hm']
  constructor
  · intro h k' hk'
    exact h _ hk'
  · intro h k hk
    have := h (Equiv.swap m' m k) (by simpa using hk)
    simpa using this

theorem exists_JO_of_JK [Finite F] [CharP F 2] (hn : 4 ≤ n) {K : Set (Fin n)} (hK : K.Nonempty) :
    ∃ (σ : ↥(Om n F) ≃* ↥(Om n F)) (S : Finset ℕ), S.Nonempty ∧ (∀ i ∈ S, 1 ≤ i ∧ i ≤ n) ∧
      (n - 1 ∈ S → n ∈ S) ∧ (JK n F K).map σ.toMonoidHom = JO n F S := by
  by_cases hs : ∃ ka ∈ K, ka.val + 2 = n ∧ ∀ kb ∈ K, kb.val + 1 ≠ n
  · obtain ⟨ka, hka, hka2, hkb⟩ := hs
    let m : Fin n := ⟨n - 1, by omega⟩
    let m' : Fin n := ⟨n - 2, by omega⟩
    have hm : m.val + 1 = n := by simp [m]; omega
    have hm' : m'.val + 2 = n := by simp [m']; omega
    have hkam' : ka = m' := Fin.ext (by simp [m']; omega)
    have hmK' : m ∈ (Equiv.swap m' m ⁻¹' K) := by
      rw [Set.mem_preimage, Equiv.swap_apply_right, ← hkam']
      exact hka
    have hnorm : ∀ ka' ∈ (Equiv.swap m' m ⁻¹' K), ka'.val + 2 = n →
        ∃ kb ∈ (Equiv.swap m' m ⁻¹' K), kb.val + 1 = n := by
      intro ka' hka' hka'2
      exfalso
      have : ka' = m' := Fin.ext (by simp [m']; omega)
      rw [this, Set.mem_preimage, Equiv.swap_apply_left] at hka'
      exact hkb m hka' hm
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := exists_JO_of_JK_normalized hn (F := F) ⟨m, hmK'⟩ hnorm
    exact ⟨swapAut hm, S, hS1, hS2, hS3, by rw [map_JK_swapAut hm hm', hS4]⟩
  · push Not at hs
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := exists_JO_of_JK_normalized hn (F := F) hK hs
    exact ⟨MulEquiv.refl _, S, hS1, hS2, hS3, by rw [hS4]; exact Subgroup.map_id _⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
