module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Tri

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

theorem zpowers_eq_one_of_centralizes {y : Q} {L : Subgroup Q} (ho : orderOf y = 3)
    (hnc : ∃ m ∈ L, y * m ≠ m * y) :
    ∀ z ∈ Subgroup.zpowers y, (∀ w ∈ L, z * w = w * z) → z = 1 := by
  intro z hz hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  obtain ⟨m, hm, hne⟩ := hnc
  have h3 : y ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one y
  have e := zpow_eq_zpow_emod' (x := y) k h3
  have hr : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rcases hr with h | h | h
  · rw [e, h]; simp
  · exfalso
    apply hne
    rw [e, h] at hc
    simpa using hc m hm
  · exfalso
    apply hne
    rw [e, h] at hc
    have h2 : Commute (y ^ (2 : ℤ)) m := hc m hm
    have h4 : y = (y ^ (2 : ℤ)) ^ 2 := by
      have h44 : y ^ 4 = y := by
        calc y ^ 4 = y ^ 3 * y := by group
          _ = y := by rw [h3, one_mul]
      calc y = y ^ 4 := h44.symm
        _ = (y ^ (2 : ℤ)) ^ 2 := by group
    have h5 : Commute y m := by rw [h4]; exact h2.pow_left 2
    exact h5.eq

theorem noncentral_conj {y : Q} {L : Subgroup Q} (g : Q) (hnc : ∃ m ∈ L, y * m ≠ m * y) :
    ∃ m ∈ GLBConj g L, (g⁻¹ * y * g) * m ≠ m * (g⁻¹ * y * g) := by
  obtain ⟨m, hm, hne⟩ := hnc
  refine ⟨g⁻¹ * m * g, ?_, fun h => hne ?_⟩
  · rw [mem_gLBConj]; simpa [mul_assoc] using hm
  · have : g⁻¹ * (y * m) * g = g⁻¹ * (m * y) * g := by
      calc g⁻¹ * (y * m) * g = (g⁻¹ * y * g) * (g⁻¹ * m * g) := by group
        _ = (g⁻¹ * m * g) * (g⁻¹ * y * g) := h
        _ = g⁻¹ * (m * y) * g := by group
    simpa using this

namespace Triple3

variable {B M : Subgroup Q} {c : Q} (T : Triple3 B M c)

include T

theorem sup01_comm2 {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ M) (h1 : P1 ≤ GLBConj c M)
    (h2 : P2 ≤ GLBConj (c ^ 2) M) : ∀ p ∈ P0 ⊔ P1, ∀ r ∈ P2, p * r = r * p := by
  intro p hp r hr
  have hle : P0 ⊔ P1 ≤ Subgroup.centralizer ({r} : Set Q) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm02 u (h0 hu) r (h2 hr)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm12 u (h1 hu) r (h2 hr)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

theorem mem_join {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ M) (h1 : P1 ≤ GLBConj c M)
    (h2 : P2 ≤ GLBConj (c ^ 2) M) {z : Q} (hz : z ∈ P0 ⊔ P1 ⊔ P2) :
    ∃ u ∈ P0, ∃ v ∈ P1, ∃ w ∈ P2, u * v * w = z := by
  obtain ⟨q, hq, w, hw, rfl⟩ := t113_mem_sup (T.sup01_comm2 h0 h1 h2) hz
  obtain ⟨u, hu, v, hv, rfl⟩ := t113_mem_sup
    (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hq
  exact ⟨u, hu, v, hv, w, hw, rfl⟩

theorem join_eq_one {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ M) (h1 : P1 ≤ GLBConj c M)
    (h2 : P2 ≤ GLBConj (c ^ 2) M)
    (n0 : ∀ z ∈ P0, (∀ w ∈ M, z * w = w * z) → z = 1)
    (n1 : ∀ z ∈ P1, (∀ w ∈ GLBConj c M, z * w = w * z) → z = 1)
    (n2 : ∀ z ∈ P2, (∀ w ∈ GLBConj (c ^ 2) M, z * w = w * z) → z = 1) {z : Q}
    (hz : z ∈ P0 ⊔ P1 ⊔ P2) (c0 : ∀ m ∈ M, z * m = m * z)
    (c1 : ∀ m ∈ GLBConj c M, z * m = m * z) (c2 : ∀ m ∈ GLBConj (c ^ 2) M, z * m = m * z) :
    z = 1 := by
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := T.mem_join h0 h1 h2 hz
  have hu1 : u = 1 := by
    refine n0 u hu fun m hm => ?_
    have a1 : Commute (u * v * w) m := c0 m hm
    have a2 : Commute v m := (T.comm01 m hm v (h1 hv)).symm
    have a3 : Commute w m := (T.comm02 m hm w (h2 hw)).symm
    have : Commute (u * v * w * w⁻¹ * v⁻¹) m := ((a1.mul_left a3.inv_left).mul_left a2.inv_left)
    have e : u * v * w * w⁻¹ * v⁻¹ = u := by group
    rw [e] at this
    exact this.eq
  subst hu1
  have hv1 : v = 1 := by
    refine n1 v hv fun m hm => ?_
    have a1 : Commute (1 * v * w) m := c1 m hm
    have a3 : Commute w m := (T.comm12 m hm w (h2 hw)).symm
    have : Commute (1 * v * w * w⁻¹) m := a1.mul_left a3.inv_left
    have e : 1 * v * w * w⁻¹ = v := by group
    rw [e] at this
    exact this.eq
  subst hv1
  have hw1 : w = 1 := by
    refine n2 w hw fun m hm => ?_
    simpa using c2 m hm
  subst hw1
  simp

theorem join_elem {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ M) (h1 : P1 ≤ GLBConj c M)
    (h2 : P2 ≤ GLBConj (c ^ 2) M)
    (n0 : ∀ z ∈ P0, (∀ w ∈ M, z * w = w * z) → z = 1)
    (n1 : ∀ z ∈ P1, (∀ w ∈ GLBConj c M, z * w = w * z) → z = 1)
    (n2 : ∀ z ∈ P2, (∀ w ∈ GLBConj (c ^ 2) M, z * w = w * z) → z = 1)
    (e0 : IsElemAbelian 3 P0) (e1 : IsElemAbelian 3 P1) (e2 : IsElemAbelian 3 P2) :
    IsElemAbelian 3 (P0 ⊔ P1 ⊔ P2) ∧
      Nat.card ↥(P0 ⊔ P1 ⊔ P2) = Nat.card P0 * Nat.card P1 * Nat.card P2 := by
  have hi01 : P0 ⊓ P1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact n0 z hz.1 fun m hm => (T.comm01 m hm z (h1 hz.2)).symm
  obtain ⟨f01, c01⟩ := t113_sup_elemAbelian e0 e1
    (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hi01
  have hi2 : (P0 ⊔ P1) ⊓ P2 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine T.join_eq_one h0 h1 h2 n0 n1 n2 (Subgroup.mem_sup_left hz.1) ?_ ?_ ?_
    · exact fun m hm => (T.comm02 m hm z (h2 hz.2)).symm
    · exact fun m hm => (T.comm12 m hm z (h2 hz.2)).symm
    · exact fun m hm => T.sup01_comm2 h0 h1 le_rfl z hz.1 m hm
  obtain ⟨f, c'⟩ := t113_sup_elemAbelian f01 e2 (T.sup01_comm2 h0 h1 h2) hi2
  exact ⟨f, by rw [c', c01]⟩

theorem Y_spec {y : Q} (hy : y ∈ M) (ho : orderOf y = 3) (hnc : ∃ m ∈ M, y * m ≠ m * y) :
    IsElemAbelian 3 (t113Y c y) ∧ Nat.card (t113Y c y) = 27 ∧ t113Y c y ≤ t113K B M ∧
      (∀ z ∈ t113Y c y, z ∈ t113B0 B M → z = 1) := by
  have m1 := T.conj1_mem hy
  have m2 := T.conj2_mem hy
  have o1 : orderOf (c⁻¹ * y * c) = 3 := by rw [t113_orderOf_conj, ho]
  have o2 : orderOf ((c ^ 2)⁻¹ * y * c ^ 2) = 3 := by rw [t113_orderOf_conj, ho]
  have h0 : Subgroup.zpowers y ≤ M := Subgroup.zpowers_le.2 hy
  have h1 : Subgroup.zpowers (c⁻¹ * y * c) ≤ GLBConj c M := Subgroup.zpowers_le.2 m1
  have h2 : Subgroup.zpowers ((c ^ 2)⁻¹ * y * c ^ 2) ≤ GLBConj (c ^ 2) M :=
    Subgroup.zpowers_le.2 m2
  have n0 := zpowers_eq_one_of_centralizes ho hnc
  have n1 := zpowers_eq_one_of_centralizes o1 (noncentral_conj c hnc)
  have n2 := zpowers_eq_one_of_centralizes o2 (noncentral_conj (c ^ 2) hnc)
  obtain ⟨e0, c0⟩ := t113_zpowers_elem ho
  obtain ⟨e1, c1⟩ := t113_zpowers_elem o1
  obtain ⟨e2, c2⟩ := t113_zpowers_elem o2
  obtain ⟨hel, hcard⟩ := T.join_elem h0 h1 h2 n0 n1 n2 e0 e1 e2
  refine ⟨hel, by unfold t113Y; rw [hcard, c0, c1, c2], ?_, fun z hz hb => ?_⟩
  · exact sup_le (sup_le (h0.trans T.L_le_K) (h1.trans (T.conj_le_K T.mem)))
      (h2.trans (T.conj_le_K (B.pow_mem T.mem 2)))
  · refine T.join_eq_one h0 h1 h2 n0 n1 n2 hz ?_ ?_ ?_
    · exact fun m hm => (T.B0_comm_K hb m (T.L_le_K hm)).symm
    · exact fun m hm => (T.B0_comm_K hb m (T.conj_le_K T.mem hm)).symm
    · exact fun m hm => (T.B0_comm_K hb m (T.conj_le_K (B.pow_mem T.mem 2) hm)).symm

theorem Y12_spec {y : Q} (hy : y ∈ M) (ho : orderOf y = 3) (hnc : ∃ m ∈ M, y * m ≠ m * y) :
    IsElemAbelian 3 (t113Y12 c y) ∧ Nat.card (t113Y12 c y) = 9 ∧ t113Y12 c y ≤ t113K B M ∧
      (∀ z ∈ t113Y12 c y, z ∈ t113B0 B M → z = 1) := by
  have m1 := T.conj1_mem hy
  have m2 := T.conj2_mem hy
  have o1 : orderOf (c⁻¹ * y * c) = 3 := by rw [t113_orderOf_conj, ho]
  have o2 : orderOf ((c ^ 2)⁻¹ * y * c ^ 2) = 3 := by rw [t113_orderOf_conj, ho]
  have h1 : Subgroup.zpowers (c⁻¹ * y * c) ≤ GLBConj c M := Subgroup.zpowers_le.2 m1
  have h2 : Subgroup.zpowers ((c ^ 2)⁻¹ * y * c ^ 2) ≤ GLBConj (c ^ 2) M :=
    Subgroup.zpowers_le.2 m2
  have n0 : ∀ z ∈ (⊥ : Subgroup Q), (∀ w ∈ M, z * w = w * z) → z = 1 := fun z hz _ =>
    Subgroup.mem_bot.1 hz
  have n1 := zpowers_eq_one_of_centralizes o1 (noncentral_conj c hnc)
  have n2 := zpowers_eq_one_of_centralizes o2 (noncentral_conj (c ^ 2) hnc)
  obtain ⟨e1, c1⟩ := t113_zpowers_elem o1
  obtain ⟨e2, c2⟩ := t113_zpowers_elem o2
  obtain ⟨eb, cb⟩ := t113_bot_elem (Q := Q)
  obtain ⟨hel, hcard⟩ := T.join_elem (bot_le : (⊥ : Subgroup Q) ≤ M) h1 h2 n0 n1 n2 eb e1 e2
  have hb' : (⊥ : Subgroup Q) ⊔ Subgroup.zpowers (c⁻¹ * y * c) ⊔
      Subgroup.zpowers ((c ^ 2)⁻¹ * y * c ^ 2) = t113Y12 c y := by
    rw [bot_sup_eq]; rfl
  rw [hb'] at hel hcard
  refine ⟨hel, by rw [hcard, cb, c1, c2], ?_, fun z hz hz0 => ?_⟩
  · exact sup_le (h1.trans (T.conj_le_K T.mem)) (h2.trans (T.conj_le_K (B.pow_mem T.mem 2)))
  · refine T.join_eq_one (bot_le : (⊥ : Subgroup Q) ≤ M) h1 h2 n0 n1 n2 ?_ ?_ ?_ ?_
    · rw [← hb'] at hz; exact hz
    · exact fun m hm => (T.B0_comm_K hz0 m (T.L_le_K hm)).symm
    · exact fun m hm => (T.B0_comm_K hz0 m (T.conj_le_K T.mem hm)).symm
    · exact fun m hm => (T.B0_comm_K hz0 m (T.conj_le_K (B.pow_mem T.mem 2) hm)).symm

theorem Y12_le_Y (y : Q) : t113Y12 c y ≤ t113Y c y := by
  unfold t113Y12 t113Y
  exact sup_le (le_sup_of_le_left le_sup_right) le_sup_right

theorem Y12_comm_M {y : Q} (hy : y ∈ M) : ∀ z ∈ t113Y12 c y, ∀ l ∈ M, z * l = l * z := by
  intro z hz l hl
  have hle : t113Y12 c y ≤ Subgroup.centralizer ({l} : Set Q) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.comm01 l hl _ (T.conj1_mem hy)).symm
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.comm02 l hl _ (T.conj2_mem hy)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)

theorem Y12_noncyclic {y : Q} (hy : y ∈ M) (ho : orderOf y = 3)
    (hnc : ∃ m ∈ M, y * m ≠ m * y) :
    ∃ u ∈ t113Y12 c y, ∃ v ∈ t113Y12 c y, (∀ m ∈ M, u * m = m * u) ∧ (∀ m ∈ M, v * m = m * v) ∧
      u ≠ 1 ∧ v ∉ Subgroup.zpowers u := by
  have m1 := T.conj1_mem hy
  have m2 := T.conj2_mem hy
  have o1 : orderOf (c⁻¹ * y * c) = 3 := by rw [t113_orderOf_conj, ho]
  have hu1 : c⁻¹ * y * c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at o1
    omega
  have hmem1 : c⁻¹ * y * c ∈ t113Y12 c y := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hmem2 : (c ^ 2)⁻¹ * y * c ^ 2 ∈ t113Y12 c y := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨c⁻¹ * y * c, hmem1, (c ^ 2)⁻¹ * y * c ^ 2, hmem2, fun l hl => T.comm01 l hl _ m1 |>.symm,
    fun l hl => T.comm02 l hl _ m2 |>.symm, hu1, fun hv => ?_⟩
  obtain ⟨m, hm, hne⟩ := noncentral_conj (c ^ 2) hnc
  apply hne
  have hv' : (c ^ 2)⁻¹ * y * c ^ 2 ∈ GLBConj c M :=
    (Subgroup.zpowers_le.2 m1) hv
  exact T.comm12 _ hv' m hm

end Triple3

end CFSG.LocalAnalysis.GLTheoremA.I113
