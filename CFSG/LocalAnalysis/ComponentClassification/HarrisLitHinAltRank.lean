module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAltPerm

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {σ : Perm α}

omit [Fintype α] in
theorem commute_swap_of_fix {g : Perm α} {u v : α} (hu : g u = u) (hv : g v = v) :
    g * swap u v = swap u v * g := by
  have h := swap_apply_apply g u v
  rw [hu, hv] at h
  calc g * swap u v = g * swap u v * g⁻¹ * g := by group
    _ = swap u v * g := by rw [← h]

omit [DecidableEq α] [Fintype α] in
theorem two_mul_card_le_sup [Finite α] {H : Subgroup (Perm α)} {g : Perm α} {z : α}
    (hH : ∀ h ∈ H, h z = z) (hg : g z ≠ z) : 2 * Nat.card H ≤ Nat.card ↥(H ⊔ zpowers g) := by
  have hlt : H < H ⊔ zpowers g :=
    lt_of_le_of_ne le_sup_left fun heq => hg (hH g (heq ▸ mem_sup_right (mem_zpowers g)))
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : H ≤ H ⊔ zpowers g)
  have hlt' := Subgroup.card_lt_of_lt hlt
  rw [hk] at hlt' ⊢
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp at hlt'
  exact Nat.mul_comm 2 _ ▸ Nat.mul_le_mul_left _ hk2

omit [DecidableEq α] [Fintype α] in
theorem elemAbelian_closure {S : Set (Perm α)} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) :
    (∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x) ∧ ∀ x ∈ closure S, x * x = 1 := by
  have hc : ∀ x ∈ closure S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have hle : closure S ≤ centralizer {y} := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact hcomm z hz y hy
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hcc : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    have hle : closure S ≤ centralizer {x} := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hc x hx z hz).symm
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  refine ⟨hcc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hcc x hx y hy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

variable (hσ : σ * σ = 1)

include hσ in
theorem exists_elemAbelian_of_points (f : Fin 6 → α) (hf : Function.Injective f)
    (hfσ : ∀ i, σ (f i) = f i) {a : α} (ha : σ a ≠ a) :
    ∃ E : Subgroup (Perm α), E ≤ alternatingGroup α ⊓ centralizer {σ} ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ 8 ≤ Nat.card E ∧
      (σ ∈ alternatingGroup α → ∀ b, σ b ≠ b → b ≠ a → b ≠ σ a →
        ∃ E' : Subgroup (Perm α), E' ≤ alternatingGroup α ⊓ centralizer {σ} ∧
          (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) ∧ (∀ x ∈ E', x * x = 1) ∧
          16 ≤ Nat.card E') := by
  classical
  set t := swap a (σ a) with htdef
  set s : Fin 3 → Perm α := fun i => swap (f ⟨2 * i, by omega⟩) (f ⟨2 * i + 1, by omega⟩)
  set x : Fin 3 → Perm α := fun i => s i * t
  have hfa : ∀ i, f i ≠ a := fun i h => ha (by rw [← h, hfσ])
  have hfσa : ∀ i, f i ≠ σ a := fun i h => ha (by
    have := hfσ i
    rw [h, apply_apply_of_mul_self hσ] at this
    exact this.symm)
  have hft : ∀ i, t (f i) = f i := fun i => swap_apply_of_ne_of_ne (hfa i) (hfσa i)
  have hne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j h => hf.ne h
  have hsA : ∀ i, (s i).sign = -1 := fun i => Perm.sign_swap (hne _ _ (by
    intro h; simp [Fin.ext_iff] at h))
  have htA : t.sign = -1 := Perm.sign_swap ha.symm
  have hxA : ∀ i, x i ∈ alternatingGroup α := fun i => by
    rw [mem_alternatingGroup, Perm.sign_mul, hsA, htA]
    decide
  have hsσ : ∀ i, σ * s i = s i * σ := fun i => commute_swap_of_fix (hfσ _) (hfσ _)
  have htσ : σ * t = t * σ := by
    have h := swap_apply_apply σ a (σ a)
    rw [apply_apply_of_mul_self hσ, swap_comm] at h
    calc σ * t = σ * t * σ⁻¹ * σ := by group
      _ = t * σ := by rw [← h]
  have hxσ : ∀ i, x i * σ = σ * x i := fun i => by
    simp only [x]
    rw [mul_assoc, ← htσ, ← mul_assoc, ← hsσ, mul_assoc]
  have hst : ∀ i, s i * t = t * s i := fun i => (commute_swap_of_fix (hft _) (hft _)).symm
  have hss : ∀ i j, s i * s j = s j * s i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · refine (commute_swap_of_fix ?_ ?_).symm <;> refine swap_apply_of_ne_of_ne ?_ ?_ <;>
        refine hne _ _ ?_ <;> intro h <;> simp [Fin.ext_iff] at h <;> omega
  have hxx : ∀ i j, x i * x j = x j * x i := by
    intro i j
    simp only [x]
    calc s i * t * (s j * t) = s i * (t * s j) * t := by group
      _ = s i * (s j * t) * t := by rw [hst j]
      _ = s i * s j * (t * t) := by group
      _ = s j * s i * (t * t) := by rw [hss]
      _ = s j * (s i * t) * t := by group
      _ = s j * (t * s i) * t := by rw [hst i]
      _ = s j * t * (s i * t) := by group
  have hxsq : ∀ i, x i * x i = 1 := by
    intro i
    simp only [x]
    calc s i * t * (s i * t) = s i * (t * s i) * t := by group
      _ = s i * (s i * t) * t := by rw [hst i]
      _ = (s i * s i) * (t * t) := by group
      _ = 1 := by simp only [s, t, swap_mul_self, mul_one]
  have hxf : ∀ i : Fin 3, ∀ k : Fin 6, k.val ≠ 2 * i.val → k.val ≠ 2 * i.val + 1 →
      x i (f k) = f k := by
    intro i k h1 h2
    simp only [x, Perm.mul_apply, hft]
    exact swap_apply_of_ne_of_ne (hne _ _ (by simp [Fin.ext_iff]; omega))
      (hne _ _ (by simp [Fin.ext_iff]; omega))
  have hxf' : ∀ i : Fin 3, x i (f ⟨2 * i.val, by omega⟩) ≠ f ⟨2 * i.val, by omega⟩ := by
    intro i
    simp only [x, Perm.mul_apply, hft, s, swap_apply_left]
    exact hne _ _ (by simp [Fin.ext_iff])
  have hxb : ∀ i, ∀ b, σ b ≠ b → b ≠ a → b ≠ σ a → x i b = b := by
    intro i b hb hba hbσa
    have hbf : ∀ k, b ≠ f k := fun k h => hb (by rw [h, hfσ])
    simp only [x, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hba hbσa, swap_apply_of_ne_of_ne (hbf _) (hbf _)]
  set T := closure ({σ, x 0, x 1, x 2} : Set (Perm α))
  have hT := elemAbelian_closure (S := ({σ, x 0, x 1, x 2} : Set (Perm α))) (by
      intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
        first | rfl | exact hxx _ _ | exact hxσ _ | exact (hxσ _).symm)
    (by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact hσ
      all_goals exact hxsq _)
  have hxT : ∀ i, x i ∈ T := fun i => subset_closure (by fin_cases i <;> simp)
  have hσT : σ ∈ T := subset_closure (by simp)
  set H₁ := (⊥ : Subgroup (Perm α)) ⊔ zpowers (x 0)
  set H₂ := H₁ ⊔ zpowers (x 1)
  set H₃ := H₂ ⊔ zpowers (x 2)
  have hfix : ∀ (H : Subgroup (Perm α)) (z : α), H ≤ MulAction.stabilizer (Perm α) z →
      ∀ h ∈ H, h z = z := fun H z hH h hh => hH hh
  have hstab : ∀ (z : α) (g : Perm α), g z = z → zpowers g ≤ MulAction.stabilizer (Perm α) z :=
    fun z g hg => (zpowers_le).mpr hg
  have h1 : 2 * Nat.card (⊥ : Subgroup (Perm α)) ≤ Nat.card H₁ :=
    two_mul_card_le_sup (z := f 0) (fun h hh => by rw [(mem_bot.mp hh)]; rfl) (hxf' 0)
  have h2 : 2 * Nat.card H₁ ≤ Nat.card H₂ := by
    refine two_mul_card_le_sup (z := f 2) (hfix _ _ (sup_le bot_le (hstab _ _ ?_))) (hxf' 1)
    exact hxf 0 2 (by decide) (by decide)
  have h3 : 2 * Nat.card H₂ ≤ Nat.card H₃ := by
    refine two_mul_card_le_sup (z := f 4) (hfix _ _ (sup_le (sup_le bot_le (hstab _ _ ?_))
      (hstab _ _ ?_))) (hxf' 2)
    · exact hxf 0 4 (by decide) (by decide)
    · exact hxf 1 4 (by decide) (by decide)
  rw [card_bot] at h1
  have hH₃T : H₃ ≤ T :=
    sup_le (sup_le (sup_le bot_le ((zpowers_le).mpr (hxT 0))) ((zpowers_le).mpr (hxT 1)))
      ((zpowers_le).mpr (hxT 2))
  have hxAC : ∀ i, x i ∈ alternatingGroup α ⊓ centralizer {σ} := fun i =>
    ⟨hxA i, mem_centralizer_singleton_iff.mpr (hxσ i)⟩
  have hH₃AC : H₃ ≤ alternatingGroup α ⊓ centralizer {σ} :=
    sup_le (sup_le (sup_le bot_le ((zpowers_le).mpr (hxAC 0))) ((zpowers_le).mpr (hxAC 1)))
      ((zpowers_le).mpr (hxAC 2))
  refine ⟨H₃, hH₃AC, fun u hu v hv => hT.1 u (hH₃T hu) v (hH₃T hv),
    fun u hu => hT.2 u (hH₃T hu), by omega, fun hσA b hb hba hbσa => ?_⟩
  have h4 : 2 * Nat.card H₃ ≤ Nat.card ↥(H₃ ⊔ zpowers σ) := by
    refine two_mul_card_le_sup (z := b) (hfix _ _ (sup_le (sup_le (sup_le bot_le
      (hstab _ _ ?_)) (hstab _ _ ?_)) (hstab _ _ ?_))) hb
    all_goals exact hxb _ b hb hba hbσa
  have hle : H₃ ⊔ zpowers σ ≤ T := sup_le hH₃T ((zpowers_le).mpr hσT)
  refine ⟨H₃ ⊔ zpowers σ, sup_le hH₃AC ((zpowers_le).mpr
      ⟨hσA, mem_centralizer_singleton_iff.mpr rfl⟩),
    fun u hu v hv => hT.1 u (hle hu) v (hle hv), fun u hu => hT.2 u (hle hu), by omega⟩

end CFSG.ComponentClassification.HarrisLit.Hin
