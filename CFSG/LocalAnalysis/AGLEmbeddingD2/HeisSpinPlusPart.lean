module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PartStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinPlus
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusNode

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareSpinPlus CFSG.AGLEmbeddingD2.PartStab
  QuadraticMap

section PartMatrix

variable {n : ℕ} {F : Type} [Field F] {κ : Type}

theorem spinMatrix_apply (g : spinGroup (quadPlus n F)) (i j : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j =
      spinAction (quadPlus n F) g (Pi.single j 1) i := by
  rw [← spinMatrix_mulVec, Matrix.mulVec_single_one]
  rfl

@[expose] def Compat (s : Fin n ⊕ Fin n → κ) (k : Fin n) : Prop :=
  s (nodeX k) = s (nodeY k).swap ∧ s (nodeY k) = s (nodeX k).swap

theorem rootD_apply_eq_zero {s : Fin n ⊕ Fin n → κ} {k : Fin n} (hk : Compat s k) (hn : 3 ≤ n)
    (c : F) {i j : Fin n ⊕ Fin n} (h : s i ≠ s j) :
    spinAction (quadPlus n F) (rootD F hn k (.ofAdd c)) (Pi.single j 1) i = 0 := by
  rw [spinAction_rootD]
  have hij : i ≠ j := fun e => h (e ▸ rfl)
  have t1 : (Pi.single j 1 : Fin n ⊕ Fin n → F) i = 0 := Pi.single_eq_of_ne hij _
  have t2 : (Pi.single j 1 : Fin n ⊕ Fin n → F) (nodeY k).swap *
      (Pi.single (nodeX k) 1 : Fin n ⊕ Fin n → F) i = 0 := by
    by_cases h1 : (nodeY k).swap = j
    · by_cases h2 : i = nodeX k
      · exact absurd (by rw [h2, hk.1, h1]) h
      · simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h1]
  have t3 : (Pi.single j 1 : Fin n ⊕ Fin n → F) (nodeX k).swap *
      (Pi.single (nodeY k) 1 : Fin n ⊕ Fin n → F) i = 0 := by
    by_cases h1 : (nodeX k).swap = j
    · by_cases h2 : i = nodeY k
      · exact absurd (by rw [h2, hk.2, h1]) h
      · simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h1]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t1]
  rw [mul_assoc, t2, mul_assoc, t3]
  simp

theorem negRootD_apply_eq_zero {s : Fin n ⊕ Fin n → κ} {k : Fin n} (hk : Compat s k)
    (hn : 3 ≤ n) (c : F) {i j : Fin n ⊕ Fin n} (h : s i ≠ s j) :
    spinAction (quadPlus n F) (negRootD F hn k (.ofAdd c)) (Pi.single j 1) i = 0 := by
  rw [spinAction_negRootD]
  have hij : i ≠ j := fun e => h (e ▸ rfl)
  have t1 : (Pi.single j 1 : Fin n ⊕ Fin n → F) i = 0 := Pi.single_eq_of_ne hij _
  have t2 : (Pi.single j 1 : Fin n ⊕ Fin n → F) (nodeX k) *
      (Pi.single (nodeY k).swap 1 : Fin n ⊕ Fin n → F) i = 0 := by
    by_cases h1 : nodeX k = j
    · by_cases h2 : i = (nodeY k).swap
      · exact absurd (by rw [h2, ← hk.1, h1]) h
      · simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h1]
  have t3 : (Pi.single j 1 : Fin n ⊕ Fin n → F) (nodeY k) *
      (Pi.single (nodeX k).swap 1 : Fin n ⊕ Fin n → F) i = 0 := by
    by_cases h1 : nodeY k = j
    · by_cases h2 : i = (nodeX k).swap
      · exact absurd (by rw [h2, ← hk.2, h1]) h
      · simp [Pi.single_apply, h2]
    · simp [Pi.single_apply, h1]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, t1]
  rw [mul_assoc, t2, mul_assoc, t3]
  simp

theorem torusD_apply_eq_zero (hn : 3 ≤ n) (k : Fin n) (τ : Fˣ) {i j : Fin n ⊕ Fin n}
    (hij : i ≠ j) :
    spinAction (quadPlus n F) (torusD F hn k τ) (Pi.single j 1) i = 0 := by
  have hj : (Pi.single j 1 : Fin n ⊕ Fin n → F) = plusVec n F (coordIdx j) j.isLeft := by
    rw [plusVec_eq_single]
    congr 1
    cases j <;> rfl
  rw [hj, spinAction_torusD]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hj, Pi.single_eq_of_ne hij, mul_zero]

end PartMatrix

section PartSub

variable {n : ℕ} {F : Type} [Field F] [Finite F] {κ : Type}

@[expose] noncomputable def partSub (s : Fin n ⊕ Fin n → κ) : Subgroup (spinGroup (quadPlus n F)) :=
  (partStab F s).comap (spinMatrix (quadPlus n F))

theorem mem_partSub {s : Fin n ⊕ Fin n → κ} {g : spinGroup (quadPlus n F)} :
    g ∈ partSub (F := F) s ↔
      ∀ i j, s i ≠ s j → spinAction (quadPlus n F) g (Pi.single j 1) i = 0 := by
  rw [partSub, Subgroup.mem_comap, mem_partStab]
  unfold IsPartDiag
  simp only [spinMatrix_apply]

theorem rootD_mem_partSub {s : Fin n ⊕ Fin n → κ} {k : Fin n} (hk : Compat s k) (hn : 3 ≤ n)
    (c : Multiplicative F) : rootD F hn k c ∈ partSub (F := F) s :=
  mem_partSub.2 fun _ _ h => by
    rw [← ofAdd_toAdd c]
    exact rootD_apply_eq_zero hk hn _ h

theorem negRootD_mem_partSub {s : Fin n ⊕ Fin n → κ} {k : Fin n} (hk : Compat s k) (hn : 3 ≤ n)
    (c : Multiplicative F) : negRootD F hn k c ∈ partSub (F := F) s :=
  mem_partSub.2 fun _ _ h => by
    rw [← ofAdd_toAdd c]
    exact negRootD_apply_eq_zero hk hn _ h

theorem leviM_le_partSub (hn : 3 ≤ n) {s : Fin n ⊕ Fin n → κ} {I : Set (Fin n)}
    (hI : ∀ k ∈ I, Compat s k) : leviM (plusDatum n F hn) I ≤ partSub (F := F) s := by
  refine iSup₂_le fun (k : Fin n) hk => sup_le ?_ ?_
  · change plusRootGroup n F hn (Pi.single k 1) ≤ _
    rw [plusRootGroup_single]
    rintro _ ⟨c, rfl⟩
    exact rootD_mem_partSub (hI k hk) hn c
  · change plusRootGroup n F hn (-Pi.single k 1) ≤ _
    rw [plusRootGroup_neg_single]
    rintro _ ⟨c, rfl⟩
    exact negRootD_mem_partSub (hI k hk) hn c

theorem torus_le_partSub (hn : 3 ≤ n) (s : Fin n ⊕ Fin n → κ) :
    (⨆ k, (torusD F hn k).range) ≤ partSub (F := F) s :=
  iSup_le fun k => by
    rintro _ ⟨τ, rfl⟩
    exact mem_partSub.2 fun i j h => torusD_apply_eq_zero hn k τ (fun e => h (e ▸ rfl))

end PartSub

section Blocks

variable {n : ℕ} {F : Type} [Field F] [Finite F] {κ : Type} [DecidableEq κ]

@[expose] noncomputable def blockExt (s : Fin n ⊕ Fin n → κ) (κ₀ : κ) :
    ({z // s z = κ₀} → F) →ₗ[F] (Fin n ⊕ Fin n → F) :=
  Fintype.linearCombination F
    (fun a : {z // s z = κ₀} => (Pi.single (a : Fin n ⊕ Fin n) 1 : Fin n ⊕ Fin n → F))

omit [Finite F] in
theorem blockExt_apply (s : Fin n ⊕ Fin n → κ) (κ₀ : κ) (v : {z // s z = κ₀} → F)
    (z : Fin n ⊕ Fin n) :
    blockExt s κ₀ v z =
      ∑ a : {z // s z = κ₀}, v a * (Pi.single (a : Fin n ⊕ Fin n) 1 : _ → F) z := by
  rw [blockExt, Fintype.linearCombination_apply, Finset.sum_apply]
  rfl

omit [Finite F] in
theorem blockExt_of_eq {s : Fin n ⊕ Fin n → κ} {κ₀ : κ} (v : {z // s z = κ₀} → F)
    {z : Fin n ⊕ Fin n} (h : s z = κ₀) : blockExt s κ₀ v z = v ⟨z, h⟩ := by
  rw [blockExt_apply, Finset.sum_eq_single ⟨z, h⟩]
  · simp
  · intro a _ ha
    have : z ≠ (a : Fin n ⊕ Fin n) := fun e => ha (Subtype.ext e.symm)
    simp [this]
  · simp

omit [Finite F] in
theorem blockExt_of_ne {s : Fin n ⊕ Fin n → κ} {κ₀ : κ} (v : {z // s z = κ₀} → F)
    {z : Fin n ⊕ Fin n} (h : s z ≠ κ₀) : blockExt s κ₀ v z = 0 := by
  rw [blockExt_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : z ≠ (a : Fin n ⊕ Fin n) := fun e => h (e ▸ a.2)
  simp [this]

theorem spinAction_blockExt {s : Fin n ⊕ Fin n → κ} {g : spinGroup (quadPlus n F)}
    (hg : g ∈ partSub (F := F) s) (κ₀ : κ) (v : {z // s z = κ₀} → F) :
    spinAction (quadPlus n F) g (blockExt s κ₀ v) = blockExt s κ₀
      (((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).submatrix
        Subtype.val Subtype.val) *ᵥ v) := by
  have hg' := mem_partSub.1 hg
  funext z
  rw [← spinMatrix_mulVec]
  by_cases hz : s z = κ₀
  · rw [blockExt_of_eq _ hz]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => s j = κ₀)]
    have h0 : ∑ a : {j // ¬ s j = κ₀},
        (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z a *
          blockExt s κ₀ v a = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [blockExt_of_ne v a.2, mul_zero]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [blockExt_of_eq v a.2]
    rfl
  · rw [blockExt_of_ne _ hz]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : s j = κ₀
    · have : (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z j = 0 := by
        rw [spinMatrix_apply]
        exact hg' z j (by rw [hj]; exact hz)
      rw [this, zero_mul]
    · rw [blockExt_of_ne v hj, mul_zero]

@[expose] noncomputable def blockForm (s : Fin n ⊕ Fin n → κ) (κ₀ : κ) :
    QuadraticForm F ({z // s z = κ₀} → F) :=
  (quadPlus n F).comp (blockExt s κ₀)

omit [Finite F] in
theorem blockForm_apply (s : Fin n ⊕ Fin n → κ) (κ₀ : κ) (v : {z // s z = κ₀} → F) :
    blockForm (F := F) s κ₀ v = quadPlus n F (blockExt s κ₀ v) := rfl

@[expose] noncomputable def isoBlock (F : Type) [Field F] [Finite F] (s : Fin n ⊕ Fin n → κ)
    (κ₀ : κ) : Subgroup (GL {z // s z = κ₀} F) where
  carrier := {A | ∀ v, blockForm (F := F) s κ₀ ((A : Matrix _ _ F) *ᵥ v) = blockForm s κ₀ v}
  mul_mem' := by
    intro A B hA hB v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' := by
    intro A hA v
    have := hA ((↑A⁻¹ : Matrix _ _ F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

theorem blockHom_mem_isoBlock {s : Fin n ⊕ Fin n → κ} {g : spinGroup (quadPlus n F)}
    (hg : g ∈ partSub (F := F) s) (κ₀ : κ) :
    blockHom s κ₀ (⟨spinMatrix (quadPlus n F) g, hg⟩ : partStab F s) ∈ isoBlock F s κ₀ := by
  intro v
  have h := spinAction_blockExt hg κ₀ v
  rw [blockForm_apply, blockForm_apply]
  change quadPlus n F (blockExt s κ₀ (((spinMatrix (quadPlus n F) g :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).submatrix Subtype.val Subtype.val) *ᵥ v)) = _
  rw [← h, map_spinAction]

omit [Finite F] in
theorem spinMatrix_injective [CharP F 2] : Function.Injective (spinMatrix (quadPlus n F)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero)

theorem isMulCommutative_of_blocks [CharP F 2] {s : Fin n ⊕ Fin n → κ}
    {Q : Subgroup (spinGroup (quadPlus n F))} (hQs : Q ≤ partSub (F := F) s)
    (hQ5 : IsPGroup 5 Q)
    (hblk : ∀ κ₀, ∀ P : Subgroup (GL {z // s z = κ₀} F), P ≤ isoBlock F s κ₀ → IsPGroup 5 P →
      IsMulCommutative P) : IsMulCommutative Q := by
  let ψ : ↥Q →* partStab F s :=
    ((spinMatrix (quadPlus n F)).comp Q.subtype).codRestrict (partStab F s) fun g => hQs g.2
  have hψ : Function.Injective ψ := fun a b h =>
    Subtype.ext (spinMatrix_injective (congrArg Subtype.val h))
  let B : ∀ κ₀ : κ, ↥Q →* GL {z // s z = κ₀} F := fun κ₀ => (blockHom s κ₀).comp ψ
  have hΦ : Function.Injective (MonoidHom.pi B) :=
    (injective_pi_blockHom s).comp hψ
  have hcomm : ∀ κ₀, ∀ a b : ↥Q, B κ₀ a * B κ₀ b = B κ₀ b * B κ₀ a := by
    intro κ₀ a b
    have h5 : IsPGroup 5 (B κ₀).range :=
      hQ5.of_surjective (B κ₀).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    have hiso : (B κ₀).range ≤ isoBlock F s κ₀ := by
      rintro _ ⟨g, rfl⟩
      exact blockHom_mem_isoBlock (hQs g.2) κ₀
    have hab := (hblk κ₀ _ hiso h5).is_comm.comm ⟨B κ₀ a, a, rfl⟩ ⟨B κ₀ b, b, rfl⟩
    exact congrArg Subtype.val hab
  refine ⟨⟨fun a b => hΦ ?_⟩⟩
  funext κ₀
  simp only [map_mul, MonoidHom.pi_apply]
  exact hcomm κ₀ a b

end Blocks

section Labels

variable {n : ℕ}

@[expose] def Link (I : Set (Fin n)) (m : ℕ) : Prop := ∃ k ∈ I, (rootIdxD n k).val = m

@[expose] noncomputable def lab (I : Set (Fin n)) (m : ℕ) : ℕ :=
  open Classical in Nat.count (fun j => ¬ Link I j) m

theorem lab_succ_of_not_link {I : Set (Fin n)} {m : ℕ} (h : ¬ Link I m) :
    lab I (m + 1) = lab I m + 1 := by
  classical
  unfold lab
  rw [Nat.count_succ]
  simp [h]

theorem lab_succ_of_link {I : Set (Fin n)} {m : ℕ} (h : Link I m) : lab I (m + 1) = lab I m := by
  classical
  unfold lab
  rw [Nat.count_succ]
  simp [h]

theorem lab_mono (I : Set (Fin n)) {m m' : ℕ} (h : m ≤ m') : lab I m ≤ lab I m' := by
  classical
  exact Nat.count_monotone _ h

theorem link_of_lab_eq {I : Set (Fin n)} {m m' j : ℕ} (hmj : m ≤ j) (hjm' : j < m')
    (h : lab I m = lab I m') : Link I j := by
  by_contra hj
  have h1 : lab I (j + 1) = lab I j + 1 := lab_succ_of_not_link hj
  have h2 := lab_mono I hmj
  have h3 : lab I (j + 1) ≤ lab I m' := lab_mono I hjm'
  omega

@[expose] def Dt (I : Set (Fin n)) : Prop := (∃ a ∈ I, a.val + 2 = n) ∧ ∃ b ∈ I, b.val + 1 = n

@[expose] def HB (I : Set (Fin n)) : Prop := ∃ b ∈ I, b.val + 1 = n

@[expose] noncomputable def sgn (I : Set (Fin n)) (m : Fin n) : Bool :=
  open Classical in decide (¬ (m.val + 1 = n ∧ HB I))

theorem sgn_eq_true_iff {I : Set (Fin n)} {m : Fin n} :
    sgn I m = true ↔ ¬ (m.val + 1 = n ∧ HB I) := by
  classical
  simp only [sgn, decide_eq_true_eq]

@[expose] def IsD (I : Set (Fin n)) (z : Fin n ⊕ Fin n) : Prop :=
  Dt I ∧ lab I (coordIdx z).val = lab I (n - 1)

@[expose] noncomputable def cls (I : Set (Fin n)) (z : Fin n ⊕ Fin n) : Bool :=
  open Classical in if IsD I z then false else (z.isLeft == sgn I (coordIdx z))

@[expose] noncomputable def part (I : Set (Fin n)) (z : Fin n ⊕ Fin n) : ℕ × Bool :=
  (lab I (coordIdx z).val, cls I z)

theorem lab_node {I : Set (Fin n)} (hn : 2 ≤ n) {k : Fin n} (hk : k ∈ I) :
    lab I (rootIdxD' n k).val = lab I (rootIdxD n k).val := by
  rw [val_rootIdxD' n hn k]
  exact lab_succ_of_link ⟨k, hk, rfl⟩

theorem compat_part (hn : 3 ≤ n) {I : Set (Fin n)} {k : Fin n} (hk : k ∈ I) :
    Compat (part I) k := by
  have hlab := lab_node (by omega) hk
  have hD : IsD I (nodeX k) ↔ IsD I (nodeY k).swap := by
    unfold IsD
    simp only [coordIdx_nodeX, coordIdx_swap, coordIdx_nodeY, hlab]
  have hD' : IsD I (nodeY k) ↔ IsD I (nodeX k).swap := by
    unfold IsD
    simp only [coordIdx_nodeX, coordIdx_swap, coordIdx_nodeY, hlab]
  have hDxy : IsD I (nodeX k) ↔ IsD I (nodeY k) := by
    unfold IsD
    simp only [coordIdx_nodeX, coordIdx_nodeY, hlab]
  have h1 : lab I (coordIdx (nodeX k)).val = lab I (coordIdx (nodeY k).swap).val := by
    simp [hlab]
  have h2 : lab I (coordIdx (nodeY k)).val = lab I (coordIdx (nodeX k).swap).val := by
    simp [hlab]
  by_cases hDk : IsD I (nodeX k)
  · have a1 := hD.1 hDk
    have a2 := hDxy.1 hDk
    have a3 := hD'.1 a2
    simp only [Compat, part, cls, ite_eq_left hDk, ite_eq_left a1, ite_eq_left a2, ite_eq_left a3,
      h1, h2, and_self]
  · have a1 : ¬ IsD I (nodeY k).swap := fun h => hDk (hD.2 h)
    have a2 : ¬ IsD I (nodeY k) := fun h => hDk (hDxy.2 h)
    have a3 : ¬ IsD I (nodeX k).swap := fun h => a2 (hD'.2 h)
    unfold Compat part cls
    simp only [ite_eq_right hDk, ite_eq_right a1, ite_eq_right a2, ite_eq_right a3, h1, h2,
      Prod.mk.injEq, true_and]
    by_cases h : k.val + 1 < n
    · have hsk : sgn I k = true := sgn_eq_true_iff.2 fun hh => by omega
      have hsk1 : sgn I ⟨k.val + 1, h⟩ = true := sgn_eq_true_iff.2 fun hh => by
        apply hDk
        refine ⟨⟨⟨k, hk, by have := hh.1; simp at this; omega⟩, hh.2⟩, ?_⟩
        rw [coordIdx_nodeX, rootIdxD_of_lt n h]
        have := lab_succ_of_link (I := I) (m := k.val) ⟨k, hk, by rw [rootIdxD_of_lt n h]⟩
        rw [← this]
        congr 1
        have := hh.1
        simp at this
        omega
      rw [nodeX_of_lt h, nodeY_of_lt h]
      simp [hsk, hsk1]
    · have h' : k.val + 1 = n := by have := k.2; omega
      have hs1 : sgn I ⟨n - 2, by omega⟩ = true := sgn_eq_true_iff.2 fun hh => by
        have := hh.1; simp at this; omega
      have hs2 : sgn I ⟨n - 1, by omega⟩ = false := by
        by_contra hc
        have := sgn_eq_true_iff.1 (by simpa using hc)
        exact this ⟨by simp; omega, ⟨k, hk, h'⟩⟩
      rw [nodeX_of_last h' (by omega), nodeY_of_last h' (by omega)]
      simp [hs1, hs2]

@[expose] noncomputable def fib (I : Set (Fin n)) (ℓ : ℕ) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter fun m => lab I m.val = ℓ

theorem mem_fib {I : Set (Fin n)} {ℓ : ℕ} {m : Fin n} : m ∈ fib I ℓ ↔ lab I m.val = ℓ := by
  simp [fib]

theorem card_block_le (I : Set (Fin n)) (ℓ : ℕ) (c : Bool) :
    Fintype.card {z // part I z = (ℓ, c)} ≤ 2 * (fib I ℓ).card := by
  classical
  rw [Fintype.card_subtype, two_mul]
  refine (Finset.card_le_card (t := (fib I ℓ).disjSum (fib I ℓ)) fun z hz => ?_).trans
    (Finset.card_disjSum _ _).le
  rw [Finset.mem_filter] at hz
  rw [mem_disjSum_iff, mem_fib]
  exact (Prod.mk.inj hz.2).1

theorem card_block_le_of_not_isD (I : Set (Fin n)) (ℓ : ℕ) (c : Bool)
    (h : ¬ (Dt I ∧ ℓ = lab I (n - 1))) :
    Fintype.card {z // part I z = (ℓ, c)} ≤ (fib I ℓ).card := by
  classical
  rw [Fintype.card_subtype]
  refine Finset.card_le_card_of_injOn coordIdx (fun z hz => ?_) (fun z hz z' hz' hzz' => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hz
    rw [Finset.mem_coe, mem_fib]
    exact (Prod.mk.inj hz.2).1
  · rw [Finset.mem_coe, Finset.mem_filter] at hz hz'
    have hl : lab I (coordIdx z).val = ℓ := (Prod.mk.inj hz.2).1
    have hc : cls I z = c := (Prod.mk.inj hz.2).2
    have hc' : cls I z' = c := (Prod.mk.inj hz'.2).2
    have hnD : ¬ IsD I z := fun hD => h ⟨hD.1, hl ▸ hD.2⟩
    have hl' : lab I (coordIdx z').val = ℓ := by rw [← hzz']; exact hl
    have hnD' : ¬ IsD I z' := fun hD => h ⟨hD.1, hl' ▸ hD.2⟩
    unfold cls at hc hc'
    rw [ite_eq_right hnD] at hc
    rw [ite_eq_right hnD'] at hc'
    rw [← hzz'] at hc'
    have hside : z.isLeft = z'.isLeft := by
      rw [← hc'] at hc
      revert hc
      cases z.isLeft <;> cases z'.isLeft <;> cases sgn I (coordIdx z) <;> simp
    cases z <;> cases z' <;> simp_all [coordIdx]

theorem fib_spec (I : Set (Fin n)) (ℓ : ℕ) (h : 0 < (fib I ℓ).card) :
    ∃ m₀ m₁ : ℕ, m₀ ≤ m₁ ∧ m₁ < n ∧ (fib I ℓ).card ≤ m₁ - m₀ + 1 ∧
      (∀ j, m₀ ≤ j → j < m₁ → Link I j) ∧ (∃ m ∈ fib I ℓ, m.val = m₁) ∧
      (∀ m ∈ fib I ℓ, m₀ ≤ m.val ∧ m.val ≤ m₁) := by
  classical
  set S : Finset ℕ := (fib I ℓ).image Fin.val with hS
  have hne : S.Nonempty := by
    obtain ⟨m, hm⟩ := Finset.card_pos.1 h
    exact ⟨m.val, Finset.mem_image_of_mem _ hm⟩
  have hcard : S.card = (fib I ℓ).card := Finset.card_image_of_injective _ Fin.val_injective
  have h0 := S.min'_mem hne
  have h1 := S.max'_mem hne
  obtain ⟨a, ha, ha'⟩ := Finset.mem_image.1 h0
  obtain ⟨b, hb, hb'⟩ := Finset.mem_image.1 h1
  have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun x hx =>
    Finset.mem_Icc.2 ⟨S.min'_le x hx, S.le_max' x hx⟩
  have hc : (fib I ℓ).card ≤ (Finset.Icc (S.min' hne) (S.max' hne)).card :=
    hcard ▸ Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  refine ⟨S.min' hne, S.max' hne, S.min'_le _ (S.max'_mem hne), ?_, by omega, ?_, ?_, ?_⟩
  · rw [← hb']; exact b.2
  · intro j hj1 hj2
    exact link_of_lab_eq hj1 hj2
      (by rw [← ha', ← hb']; exact (mem_fib.1 ha).trans (mem_fib.1 hb).symm)
  · exact ⟨b, hb, hb'⟩
  · intro m hm
    exact ⟨S.min'_le _ (Finset.mem_image_of_mem _ hm), S.le_max' _ (Finset.mem_image_of_mem _ hm)⟩

theorem mem_of_link {I : Set (Fin n)} {j : ℕ} (hj : j + 3 ≤ n) (h : Link I j) {k : Fin n}
    (hk : k.val = j) : k ∈ I := by
  obtain ⟨k', hk', hk'j⟩ := h
  rw [val_rootIdxD] at hk'j
  split_ifs at hk'j with hlt
  · have : k = k' := Fin.ext (by omega)
    rw [this]
    exact hk'
  · omega

theorem rootIdxD_val_of_lt {k : Fin n} (h : k.val + 1 < n) : (rootIdxD n k).val = k.val := by
  rw [val_rootIdxD, ite_eq_left h]

theorem exists_orth_triple_or_card_lt_ten (hn : 3 ≤ n) (I : Set (Fin n)) :
    (∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ cartanD n a b = 0 ∧ cartanD n a c = 0 ∧
      cartanD n b c = 0) ∨ ∀ κ₀ : ℕ × Bool, Fintype.card {z // part I z = κ₀} < 10 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨htri, ⟨ℓ, c⟩, hcard⟩ := hcon
  by_cases hD : Dt I ∧ ℓ = lab I (n - 1)
  ·
    have hf : 5 ≤ (fib I ℓ).card := by
      have := card_block_le I ℓ c
      omega
    obtain ⟨m₀, m₁, hm01, hm1n, hcm, hlink, -, hbd⟩ := fib_spec I ℓ (by omega)
    have hmem : (⟨n - 1, by omega⟩ : Fin n) ∈ fib I ℓ := mem_fib.2 hD.2.symm
    have hm1 : m₁ = n - 1 := by have := (hbd _ hmem).2; simp at this; omega
    obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD.1
    have hm₀ : (⟨m₀, by omega⟩ : Fin n) ∈ I :=
      mem_of_link (j := m₀) (by omega) (hlink m₀ le_rfl (by omega)) rfl
    refine htri _ hm₀ a ha b hb ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h; have := congrArg Fin.val h; omega
    · exact cartanD_eq_zero_of_not_adj (by intro h; have := congrArg Fin.val h; simp at this; omega)
        (by simp; omega)
    · exact cartanD_eq_zero_of_not_adj (by intro h; have := congrArg Fin.val h; simp at this; omega)
        (by simp; omega)
    · exact cartanD_eq_zero_of_not_adj (by intro h; have := congrArg Fin.val h; omega)
        (by omega)
  ·
    have hf : 10 ≤ (fib I ℓ).card := (card_block_le_of_not_isD I ℓ c hD).trans' hcard
    obtain ⟨m₀, m₁, hm01, hm1n, hcm, hlink, -⟩ := fib_spec I ℓ (by omega)
    have hn0 : ∀ j (hj : j ≤ 4), (⟨m₀ + j, by omega⟩ : Fin n) ∈ I := fun j hj =>
      mem_of_link (j := m₀ + j) (by omega) (hlink _ (by omega) (by omega)) rfl
    have hr : ∀ j (hj : j ≤ 4), (rootIdxD n (⟨m₀ + j, by omega⟩ : Fin n)).val = m₀ + j :=
      fun j hj => rootIdxD_val_of_lt (by simp; omega)
    refine htri _ (hn0 0 (by omega)) _ (hn0 2 (by omega)) _ (hn0 4 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; have := congrArg Fin.val h; simp at this
    · intro h; have := congrArg Fin.val h; simp at this
    · intro h; have := congrArg Fin.val h; simp at this
    · exact (cartanD_eq_zero_of_far (a := ⟨m₀ + 0, by omega⟩) (b := ⟨m₀ + 2, by omega⟩)
        (by have := hr 0 (by omega); have := hr 2 (by omega); omega)).2
    · exact (cartanD_eq_zero_of_far (a := ⟨m₀ + 0, by omega⟩) (b := ⟨m₀ + 4, by omega⟩)
        (by have := hr 0 (by omega); have := hr 4 (by omega); omega)).2
    · exact (cartanD_eq_zero_of_far (a := ⟨m₀ + 2, by omega⟩) (b := ⟨m₀ + 4, by omega⟩)
        (by have := hr 2 (by omega); have := hr 4 (by omega); omega)).2

theorem part_swap_of_isD {I : Set (Fin n)} {z : Fin n ⊕ Fin n} (hD : IsD I z) :
    part I z.swap = part I z := by
  have hD' : IsD I z.swap := by unfold IsD at hD ⊢; rwa [coordIdx_swap]
  unfold part cls
  rw [ite_eq_left hD, ite_eq_left hD', coordIdx_swap]

@[expose] def BadA (I : Set (Fin n)) (u : ℕ) : Prop :=
  u + 11 < n ∧ ∀ k : Fin n, u ≤ k.val → k.val ≤ u + 10 → (k.val - u) % 4 ≠ 3 → k ∈ I

@[expose] def BadD (I : Set (Fin n)) : Prop :=
  11 ≤ n ∧ ∀ k : Fin n, ((n ≤ k.val + 11 ∧ k.val + 5 ≤ n ∧ (k.val + 11 - n) % 4 ≠ 3) ∨
    n ≤ k.val + 3) → k ∈ I

theorem badA_or_badD_or_card (hn : 3 ≤ n) (I : Set (Fin n)) :
    (∃ u, BadA I u) ∨ BadD I ∨ ∀ κ₀ : ℕ × Bool, Fintype.card {z // part I z = κ₀} < 20 ∨
      (Fintype.card {z // part I z = κ₀} = 20 ∧ ∀ z, part I z = κ₀ → part I z.swap = κ₀) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hDD, ⟨ℓ, c⟩, hcard⟩ := hcon
  by_cases hD : Dt I ∧ ℓ = lab I (n - 1)
  ·
    have hsw : ∀ z, part I z = (ℓ, c) → part I z.swap = (ℓ, c) := fun z hz => by
      have hzD : IsD I z := ⟨hD.1, ((Prod.mk.inj hz).1).trans hD.2⟩
      rw [part_swap_of_isD hzD]
      exact hz
    obtain ⟨h20, h21⟩ := hcard
    have hne : Fintype.card {z // part I z = (ℓ, c)} ≠ 20 := fun h => by
      obtain ⟨z, hz, hz'⟩ := h21 h
      exact hz' (hsw z hz)
    have hf : 11 ≤ (fib I ℓ).card := by
      have := card_block_le I ℓ c
      omega
    obtain ⟨m₀, m₁, hm01, hm1n, hcm, hlink, -, hbd⟩ := fib_spec I ℓ (by omega)
    have hmem : (⟨n - 1, by omega⟩ : Fin n) ∈ fib I ℓ := mem_fib.2 hD.2.symm
    have hm1 : m₁ = n - 1 := by have := (hbd _ hmem).2; simp at this; omega
    obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD.1
    refine hDD ⟨by omega, fun k hk => ?_⟩
    rcases hk with ⟨h1, h2, h3⟩ | h
    · exact mem_of_link (j := k.val) (by omega) (hlink _ (by omega) (by omega)) rfl
    · by_cases hk3 : k.val + 3 = n
      · exact mem_of_link (j := k.val) (by omega) (hlink _ (by omega) (by omega)) rfl
      · by_cases hk2 : k.val + 2 = n
        · have : k = a := Fin.ext (by omega)
          rw [this]
          exact ha
        · have : k = b := Fin.ext (by omega)
          rw [this]
          exact hb
  · have hf : 20 ≤ (fib I ℓ).card := (card_block_le_of_not_isD I ℓ c hD).trans' hcard.1
    obtain ⟨m₀, m₁, hm01, hm1n, hcm, hlink, -⟩ := fib_spec I ℓ (by omega)
    refine hA m₀ ⟨by omega, fun k hk1 hk2 hk3 => ?_⟩
    exact mem_of_link (j := k.val) (by omega) (hlink _ (by omega) (by omega)) rfl

end Labels

end CFSG.AGLEmbeddingD2.HeisSpinPlus
