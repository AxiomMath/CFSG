module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Base

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open scoped Pointwise

private def fz59cbS3 : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2, Equiv.addRight 1, Equiv.addRight 2]

private def fz59cbB (a b c : Fin 6) : Equiv.Perm Fz59Cell :=
  Equiv.prodShear (Equiv.refl _) ![fz59cbS3 a, fz59cbS3 b, fz59cbS3 c]

private def fz59cbL : Fin 6 → Equiv.Perm Fz59Cell :=
  ![1, fz59RowRot, fz59RowRot * fz59RowRot, fz59RowSwap, fz59RowSwap * fz59RowRot,
    fz59RowSwap * fz59RowRot * fz59RowRot]

private def fz59cbT12 : Equiv.Perm Fz59Cell := fz59RowRot * fz59RowSwap * fz59RowRot⁻¹

private def fz59cbT : Fin 3 → Equiv.Perm Fz59Cell :=
  ![fz59RowSwap, fz59cbT12, fz59RowRot⁻¹ * fz59RowSwap * fz59RowRot]

private def fz59cbF (e : Equiv.Perm Fz59Cell) : Equiv.Perm Fz59Cell :=
  fz59RowRot * e * fz59RowRot⁻¹

private def fz59cbE (m : Equiv.Perm Fz59Cell) (k : Fin 3) : Equiv.Perm Fz59Cell :=
  m * (fz59cbT k * m * (fz59cbT k)⁻¹)

private def fz59cbP (m : Equiv.Perm Fz59Cell) (k i j : Fin 3) : Equiv.Perm Fz59Cell :=
  fz59cbE m k ^ (i : ℕ) * fz59cbF (fz59cbE m k) ^ (j : ℕ)

private def fz59cbY (m : Equiv.Perm Fz59Cell) : Equiv.Perm Fz59Cell := (m * fz59cbF m) ^ 3

private def fz59cbEw (g m : Equiv.Perm Fz59Cell) : Fin 3 → Equiv.Perm Fz59Cell :=
  ![g, g * g, (g * m) ^ 2]

private def fz59cbDw (e : Equiv.Perm Fz59Cell) : Fin 3 → Equiv.Perm Fz59Cell :=
  ![e, e * (fz59cbF e)⁻¹, e * fz59cbF e * fz59cbF (fz59cbF e)]

private def fz59cbWw (m d : Equiv.Perm Fz59Cell) : Fin 2 → Equiv.Perm Fz59Cell :=
  ![m * d, m * d * d]

private def Fz59cbCol0 (w : Equiv.Perm Fz59Cell) : Prop :=
  w ≠ 1 ∧ ∀ i : Fin 3, w (i, 0) = (i, 0)

private instance fz59cbCol0Decidable (w : Equiv.Perm Fz59Cell) : Decidable (Fz59cbCol0 w) := by
  unfold Fz59cbCol0
  infer_instance

private def Fz59cbKlein (y z : Equiv.Perm Fz59Cell) : Prop :=
  y * y = 1 ∧ z * z = 1 ∧ y * z = z * y ∧ y ≠ 1 ∧ z ≠ 1 ∧ y ≠ z

private instance fz59cbKleinDecidable (y z : Equiv.Perm Fz59Cell) :
    Decidable (Fz59cbKlein y z) := by
  unfold Fz59cbKlein
  infer_instance

private def Fz59cbKleinStab (y z : Equiv.Perm Fz59Cell) (T : Finset Fz59Cell) : Prop :=
  Fz59cbKlein y z ∧ T.image y = T ∧ T.image z = T

private instance fz59cbKleinStabDecidable (y z : Equiv.Perm Fz59Cell) (T : Finset Fz59Cell) :
    Decidable (Fz59cbKleinStab y z T) := by
  unfold Fz59cbKleinStab
  infer_instance

private def Fz59cbBad (m : Equiv.Perm Fz59Cell) (k i j i' j' : Fin 3) : Prop :=
  ((fz59Tr fun _ => 0).image (fz59cbP m k i j) = fz59Tr ![1, 1, 1] ∧
      Fz59cbKleinStab fz59cbT12 (m * fz59cbP m k i' j') (fz59Tr ![1, 2, 2])) ∨
    ((fz59Tr fun _ => 0).image (fz59cbP m k i j) = fz59Tr ![2, 2, 2] ∧
      Fz59cbKleinStab fz59cbT12 (m * fz59cbP m k i' j') (fz59Tr ![2, 1, 1]))

private instance fz59cbBadDecidable (m : Equiv.Perm Fz59Cell) (k i j i' j' : Fin 3) :
    Decidable (Fz59cbBad m k i j i' j') := by
  unfold Fz59cbBad
  infer_instance

private def Fz59cbInv (m : Equiv.Perm Fz59Cell) : Prop :=
  (Fz59cbKlein m (fz59cbY m) ∧ ∀ i : Fin 3, (fz59cbY m (i, 0)).1 = i) ∨
    (Fz59cbCol0 m ∨ ∃ k : Fin 3, Fz59cbCol0 (fz59cbE m k * m)) ∨
    (∃ k i j i' j' : Fin 3, Fz59cbBad m k i j i' j') ∨
    m = fz59ColPerm (Equiv.swap 0 2) ∨ m = fz59ColPerm (Equiv.swap 0 1)

private instance fz59cbInvDecidable (m : Equiv.Perm Fz59Cell) : Decidable (Fz59cbInv m) := by
  unfold Fz59cbInv
  infer_instance

private def Fz59cbGood (g m : Equiv.Perm Fz59Cell) : Prop :=
  g = 1 ∨ g = m ∨ (g * g = 1 ∧ g * m = m * g) ∨
    ∃ e d : Fin 3, ∃ w : Fin 2, Fz59cbCol0 (fz59cbWw m (fz59cbDw (fz59cbEw g m e) d) w)

private instance fz59cbGoodDecidable (g m : Equiv.Perm Fz59Cell) :
    Decidable (Fz59cbGood g m) := by
  unfold Fz59cbGood
  infer_instance

private theorem fz59cb_S3_surj : ∀ σ : Equiv.Perm (Fin 3), ∃ k : Fin 6, fz59cbS3 k = σ := by
  decide +kernel

private theorem fz59cb_L_surj :
    ∀ σ : Equiv.Perm (Fin 3), ∃ k : Fin 6, ∀ i : Fin 3, (fz59cbL k (i, 0)).1 = σ i := by
  decide +kernel

private theorem fz59cb_inv_cases : ∀ a b c : Fin 6, fz59cbB a b c * fz59cbB a b c = 1 →
    fz59cbB a b c ≠ 1 → Fz59cbInv (fz59cbB a b c) := by
  decide +kernel

private theorem fz59cb_good_cases : ∀ a b c : Fin 6,
    Fz59cbGood (fz59cbB a b c) (fz59ColPerm (Equiv.swap 0 2)) ∧
      Fz59cbGood (fz59cbB a b c) (fz59ColPerm (Equiv.swap 0 1)) := by
  decide +kernel

private theorem fz59cb_four_dvd {H : Type*} [Group H] (K : Subgroup H) {x y : H} (hx : x ∈ K)
    (hy : y ∈ K) (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hne : x ≠ y) : 4 ∣ Nat.card K := by
  have e1 : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have e2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hyy, mul_one]
  have e3 : x * y * x = y := by rw [mul_assoc, ← hxy, ← mul_assoc, hxx, one_mul]
  have e4 : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
  have e5 : x * y * (x * y) = 1 := by rw [← mul_assoc, e3, hyy]
  let V : Subgroup H :=
    { carrier := {1, x, y, x * y}
      mul_mem' := by
        rintro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hxx, hyy, hxy.symm, e1, e2, e3, e4, e5]
      one_mem' := by simp
      inv_mem' := by
        rintro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · simp [inv_eq_of_mul_eq_one_right hxx]
        · simp [inv_eq_of_mul_eq_one_right hyy]
        · simp [inv_eq_of_mul_eq_one_right e5] }
  have hVK : V ≤ K := by
    rintro a ha
    change a ∈ ({1, x, y, x * y} : Set H) at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [K.one_mem, hx, hy, K.mul_mem hx hy]
  have hxy1 : x * y ≠ 1 := fun h => hne (by rw [← e1, h, mul_one])
  have hxyx : x * y ≠ x := fun h => hy1 (by rw [← e1, h, hxx])
  have hxyy : x * y ≠ y := fun h => hx1 (by rw [← e4, h, hyy])
  have hV : Nat.card V = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({1, x, y, x * y} : Set H).ncard = 4
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hxyy.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hxyx.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hx1.symm, hy1.symm, hxy1.symm⟩
  exact hV ▸ Subgroup.card_dvd_of_le hVK

private theorem fz59cb_eq_B {g : Equiv.Perm Fz59Cell} (hg : ∀ c : Fz59Cell, (g c).1 = c.1) :
    ∃ a b c : Fin 6, g = fz59cbB a b c := by
  have hg' : ∀ c : Fz59Cell, (g⁻¹ c).1 = c.1 := fun c => by
    simpa using (hg (g⁻¹ c)).symm
  have key : ∀ i j : Fin 3, g (i, j) = (i, (g (i, j)).2) := fun i j => Prod.ext (hg _) rfl
  have key' : ∀ i j : Fin 3, g⁻¹ (i, j) = (i, (g⁻¹ (i, j)).2) := fun i j =>
    Prod.ext (hg' _) rfl
  let q : Fin 3 → Equiv.Perm (Fin 3) := fun i =>
    { toFun := fun j => (g (i, j)).2
      invFun := fun j => (g⁻¹ (i, j)).2
      left_inv := fun j => by
        change (g⁻¹ (i, (g (i, j)).2)).2 = j
        rw [← key]
        simp
      right_inv := fun j => by
        change (g (i, (g⁻¹ (i, j)).2)).2 = j
        rw [← key']
        simp }
  obtain ⟨a, ha⟩ := fz59cb_S3_surj (q 0)
  obtain ⟨b, hb⟩ := fz59cb_S3_surj (q 1)
  obtain ⟨c, hc⟩ := fz59cb_S3_surj (q 2)
  refine ⟨a, b, c, Equiv.ext fun x => ?_⟩
  obtain ⟨i, j⟩ := x
  have hq : ![fz59cbS3 a, fz59cbS3 b, fz59cbS3 c] i = q i := by
    fin_cases i
    exacts [ha, hb, hc]
  calc g (i, j) = (i, q i j) := key i j
    _ = fz59cbB a b c (i, j) := by rw [← hq]; rfl

private def fz59cbRow (g : Equiv.Perm Fz59Cell) (i : Fin 3) : Fin 3 := (g (i, 0)).1

private theorem fz59cbRow_mul {g : Equiv.Perm Fz59Cell}
    (hg : ∀ i k k' : Fin 3, (g (i, k)).1 = (g (i, k')).1) (h : Equiv.Perm Fz59Cell)
    (i : Fin 3) : fz59cbRow (g * h) i = fz59cbRow g (fz59cbRow h i) :=
  hg (h (i, 0)).1 (h (i, 0)).2 0

private def fz59cbRowHom (N : Subgroup (Equiv.Perm Fz59Cell))
    (hrow : ∀ g ∈ N, ∀ i k k' : Fin 3, (g (i, k)).1 = (g (i, k')).1) :
    N →* Equiv.Perm (Fin 3) where
  toFun g :=
    { toFun := fz59cbRow g
      invFun := fz59cbRow (g : Equiv.Perm Fz59Cell)⁻¹
      left_inv := fun i => by
        rw [← fz59cbRow_mul (hrow _ (N.inv_mem g.2)), inv_mul_cancel]
        rfl
      right_inv := fun i => by
        rw [← fz59cbRow_mul (hrow _ g.2), mul_inv_cancel]
        rfl }
  map_one' := Equiv.ext fun _ => rfl
  map_mul' g h := Equiv.ext fun i => fz59cbRow_mul (hrow _ g.2) h i

theorem fz59_cb (N : Subgroup (Equiv.Perm Fz59Cell))
    (hrow : ∀ g ∈ N, ∀ i k k' : Fin 3, (g (i, k)).1 = (g (i, k')).1)
    (hrot : fz59RowRot ∈ N) (hswap : fz59RowSwap ∈ N)
    (hstab : ∀ g ∈ N, (∀ i : Fin 3, g (i, 0) = (i, 0)) → g = 1)
    (h4 : 4 ∣ Nat.card N) (h8 : ¬ 8 ∣ Nat.card N)
    (C : Set (Fin 3 → Fin 3)) (h0 : (fun _ => (0 : Fin 3)) ∈ C)
    (hN : ∀ g ∈ N, ∀ ω ∈ C, ∀ ω' : Fin 3 → Fin 3, (fz59Tr ω).image g = fz59Tr ω' → ω' ∈ C)
    (hF : ∀ p ∈ fz59FusPairs, (p.1 ∈ C ↔ p.2 ∈ C))
    (hcrit : ∀ ω ∈ C, ¬ 4 ∣ Nat.card (MulAction.stabilizer N (fz59Tr ω))) :
    Nat.card N = 12 ∧ ∃ σ : Equiv.Perm (Fin 3), (σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 0 1) ∧
      fz59ColPerm σ ∈ N := by
  have hF_mem : ∀ {e}, e ∈ N → fz59cbF e ∈ N := fun he =>
    N.mul_mem (N.mul_mem hrot he) (N.inv_mem hrot)
  have hT12 : fz59cbT12 ∈ N := N.mul_mem (N.mul_mem hrot hswap) (N.inv_mem hrot)
  have hT : ∀ k, fz59cbT k ∈ N := by
    intro k
    fin_cases k
    exacts [hswap, hT12, N.mul_mem (N.mul_mem (N.inv_mem hrot) hswap) hrot]
  have hE : ∀ {m}, m ∈ N → ∀ k, fz59cbE m k ∈ N := fun hm k =>
    N.mul_mem hm (N.mul_mem (N.mul_mem (hT k) hm) (N.inv_mem (hT k)))
  have hP : ∀ {m}, m ∈ N → ∀ k i j, fz59cbP m k i j ∈ N := fun hm k i j =>
    N.mul_mem (N.pow_mem (hE hm k) _) (N.pow_mem (hF_mem (hE hm k)) _)
  have hY : ∀ {m}, m ∈ N → fz59cbY m ∈ N := fun hm => N.pow_mem (N.mul_mem hm (hF_mem hm)) 3
  have hEw : ∀ {g m}, g ∈ N → m ∈ N → ∀ e, fz59cbEw g m e ∈ N := by
    intro g m hg hm e
    fin_cases e
    exacts [hg, N.mul_mem hg hg, N.pow_mem (N.mul_mem hg hm) 2]
  have hDw : ∀ {e}, e ∈ N → ∀ d, fz59cbDw e d ∈ N := by
    intro e he d
    fin_cases d
    exacts [he, N.mul_mem he (N.inv_mem (hF_mem he)),
      N.mul_mem (N.mul_mem he (hF_mem he)) (hF_mem (hF_mem he))]
  have hWw : ∀ {m d}, m ∈ N → d ∈ N → ∀ w, fz59cbWw m d w ∈ N := by
    intro m d hm hd w
    fin_cases w
    exacts [N.mul_mem hm hd, N.mul_mem (N.mul_mem hm hd) hd]
  have hL : ∀ k, fz59cbL k ∈ N := by
    intro k
    fin_cases k
    exacts [N.one_mem, hrot, N.mul_mem hrot hrot, hswap, N.mul_mem hswap hrot,
      N.mul_mem (N.mul_mem hswap hrot) hrot]
  have hC0 : ∀ w ∈ N, ¬ Fz59cbCol0 w := fun w hw h => h.1 (hstab w hw h.2)
  let φ := fz59cbRowHom N hrow
  have hsurj : Function.Surjective φ := by
    intro σ
    obtain ⟨k, hk⟩ := fz59cb_L_surj σ
    exact ⟨⟨fz59cbL k, hL k⟩, Equiv.ext hk⟩
  have hcard : Nat.card φ.ker * 6 = Nat.card N := by
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hker : ∀ g : N, g ∈ φ.ker ↔ ∀ i : Fin 3, ((g : Equiv.Perm Fz59Cell) (i, 0)).1 = i := by
    intro g
    rw [MonoidHom.mem_ker, Equiv.ext_iff]
    rfl
  have hfix : ∀ g : N, g ∈ φ.ker → ∀ c : Fz59Cell, ((g : Equiv.Perm Fz59Cell) c).1 = c.1 := by
    rintro g hg ⟨i, j⟩
    rw [hrow _ g.2 i j 0]
    exact (hker g).1 hg i
  have hk2 : 2 ∣ Nat.card φ.ker := by omega
  have hk4 : ¬ 4 ∣ Nat.card φ.ker := fun h => h8 (by omega)
  have hK : ∀ x y : Equiv.Perm Fz59Cell, x ∈ N → y ∈ N → (∀ i : Fin 3, (x (i, 0)).1 = i) →
      (∀ i : Fin 3, (y (i, 0)).1 = i) → ¬ Fz59cbKlein x y := by
    rintro x y hx hy hx0 hy0 ⟨e1, e2, e3, e4, e5, e6⟩
    refine hk4 (fz59cb_four_dvd φ.ker (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) ((hker _).2 hx0)
      ((hker _).2 hy0) (Subtype.ext e1) (Subtype.ext e2) (Subtype.ext e3) ?_ ?_ ?_)
    · exact fun h => e4 (congrArg Subtype.val h)
    · exact fun h => e5 (congrArg Subtype.val h)
    · exact fun h => e6 (congrArg Subtype.val h)
  have hS : ∀ (u : Equiv.Perm Fz59Cell) (ω : Fin 3 → Fin 3), u ∈ N →
      Fz59cbKleinStab fz59cbT12 u (fz59Tr ω) →
      4 ∣ Nat.card (MulAction.stabilizer N (fz59Tr ω)) := by
    rintro u ω hu ⟨⟨e1, e2, e3, e4, e5, e6⟩, e7, e8⟩
    refine fz59cb_four_dvd _ (x := ⟨fz59cbT12, hT12⟩) (y := ⟨u, hu⟩)
      (MulAction.mem_stabilizer_iff.2 e7) (MulAction.mem_stabilizer_iff.2 e8)
      (Subtype.ext e1) (Subtype.ext e2) (Subtype.ext e3) ?_ ?_ ?_
    · exact fun h => e4 (congrArg Subtype.val h)
    · exact fun h => e5 (congrArg Subtype.val h)
    · exact fun h => e6 (congrArg Subtype.val h)
  have hgood : ∀ σ : Equiv.Perm (Fin 3), (σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 0 1) →
      fz59ColPerm σ ∈ N → Nat.card N = 12 := by
    intro σ hσ hσN
    have hσ0 : ∀ i : Fin 3, (fz59ColPerm σ (i, 0)).1 = i := fun _ => rfl
    have hσ1 : fz59ColPerm σ ≠ 1 := by rcases hσ with rfl | rfl <;> decide
    have hσ2 : fz59ColPerm σ * fz59ColPerm σ = 1 := by rcases hσ with rfl | rfl <;> decide
    have hall : ∀ g : N, g ∈ φ.ker →
        (g : Equiv.Perm Fz59Cell) = 1 ∨ (g : Equiv.Perm Fz59Cell) = fz59ColPerm σ := by
      intro g hg
      obtain ⟨a, b, c, hgB⟩ := fz59cb_eq_B (hfix g hg)
      have hD : Fz59cbGood (g : Equiv.Perm Fz59Cell) (fz59ColPerm σ) := by
        rw [hgB]
        rcases hσ with rfl | rfl
        exacts [(fz59cb_good_cases a b c).1, (fz59cb_good_cases a b c).2]
      rcases hD with h | h | ⟨e1, e2⟩ | ⟨e, d, w, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · by_contra hne
        push Not at hne
        exact hK _ _ g.2 hσN ((hker g).1 hg) hσ0 ⟨e1, hσ2, e2, hne.1, hσ1, hne.2⟩
      · exact (hC0 _ (hWw hσN (hDw (hEw g.2 hσN e) d) w) h).elim
    have hσker : (⟨fz59ColPerm σ, hσN⟩ : N) ∈ φ.ker := (hker _).2 hσ0
    have h2 : Nat.card φ.ker = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨1, ⟨⟨fz59ColPerm σ, hσN⟩, hσker⟩, ?_, ?_⟩
      · intro h
        exact hσ1 (congrArg (fun z : φ.ker => ((z : N) : Equiv.Perm Fz59Cell)) h).symm
      · ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        rcases hall z z.2 with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h))
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨⟨m, hmN⟩, hmk⟩, hmo⟩ := exists_prime_orderOf_dvd_card' 2 hk2
  have hmo' : orderOf m = 2 := by simpa using hmo
  have hmm : m * m = 1 := by rw [← sq, ← hmo', pow_orderOf_eq_one]
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hmo'
    exact absurd hmo' (by decide)
  have hm0 : ∀ i : Fin 3, (m (i, 0)).1 = i := (hker _).1 hmk
  obtain ⟨a, b, c, rfl⟩ := fz59cb_eq_B (hfix _ hmk)
  rcases fz59cb_inv_cases a b c hmm hm1 with
    ⟨hk, hy0⟩ | hcol | ⟨k, i, j, i', j', hbad⟩ | hσ | hσ
  · exact (hK _ _ hmN (hY hmN) hm0 hy0 hk).elim
  · rcases hcol with h | ⟨k, h⟩
    · exact (hC0 _ hmN h).elim
    · exact (hC0 _ (N.mul_mem (hE hmN k) hmN) h).elim
  · exfalso
    rcases hbad with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hC1 : ![1, 1, 1] ∈ C := hN _ (hP hmN k i j) _ h0 _ e1
      have hC2 : ![1, 2, 2] ∈ C := (hF (![1, 1, 1], ![1, 2, 2]) (by decide)).1 hC1
      exact hcrit _ hC2 (hS _ _ (N.mul_mem hmN (hP hmN k i' j')) e2)
    · have hC1 : ![2, 2, 2] ∈ C := hN _ (hP hmN k i j) _ h0 _ e1
      have hC2 : ![2, 1, 1] ∈ C := (hF (![2, 2, 2], ![2, 1, 1]) (by decide)).1 hC1
      exact hcrit _ hC2 (hS _ _ (N.mul_mem hmN (hP hmN k i' j')) e2)
  · exact ⟨hgood _ (Or.inl rfl) (hσ ▸ hmN), _, Or.inl rfl, hσ ▸ hmN⟩
  · exact ⟨hgood _ (Or.inr rfl) (hσ ▸ hmN), _, Or.inr rfl, hσ ▸ hmN⟩

end CFSG.OddStandard.SmallF3.FritzII
