module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.Assembly.LowTwoRank (StatedSL)

private theorem fin_two_cross_aux {F : Type*} [Field F] (a1 a2 a3 b1 b2 b3 c1 c2 c3 : F)
    (ha1 : a2 * c3 = a3 * c2) (ha2 : a3 * c1 = a1 * c3) (ha3 : a1 * c2 = a2 * c1)
    (hb1 : b2 * c3 = b3 * c2) (hb2 : b3 * c1 = b1 * c3) (hb3 : b1 * c2 = b2 * c1)
    (hc : c1 ≠ 0 ∨ c2 ≠ 0 ∨ c3 ≠ 0) :
    a2 * b3 - a3 * b2 = 0 ∧ a3 * b1 - a1 * b3 = 0 ∧ a1 * b2 - a2 * b1 = 0 := by
  have h11 : c1 * (a2 * b3 - a3 * b2) = 0 := by
    linear_combination (-b2) * ha2 + (-b3) * ha3 + (-a1) * hb1
  have h12 : c1 * (a3 * b1 - a1 * b3) = 0 := by
    linear_combination b1 * ha2 + (-a1) * hb2
  have h13 : c1 * (a1 * b2 - a2 * b1) = 0 := by
    linear_combination b1 * ha3 + (-a1) * hb3
  have h21 : c2 * (a2 * b3 - a3 * b2) = 0 := by
    linear_combination b2 * ha1 + (-a2) * hb1
  have h22 : c2 * (a3 * b1 - a1 * b3) = 0 := by
    linear_combination (-b1) * ha1 + (-b3) * ha3 + (-a2) * hb2
  have h23 : c2 * (a1 * b2 - a2 * b1) = 0 := by
    linear_combination b2 * ha3 + (-a2) * hb3
  have h31 : c3 * (a2 * b3 - a3 * b2) = 0 := by
    linear_combination b3 * ha1 + (-a3) * hb1
  have h32 : c3 * (a3 * b1 - a1 * b3) = 0 := by
    linear_combination b3 * ha2 + (-a3) * hb2
  have h33 : c3 * (a1 * b2 - a2 * b1) = 0 := by
    linear_combination b3 * ha3 + a1 * hb1 + a2 * hb2
  rcases hc with h | h | h
  · exact ⟨(mul_eq_zero.mp h11).resolve_left h, (mul_eq_zero.mp h12).resolve_left h,
      (mul_eq_zero.mp h13).resolve_left h⟩
  · exact ⟨(mul_eq_zero.mp h21).resolve_left h, (mul_eq_zero.mp h22).resolve_left h,
      (mul_eq_zero.mp h23).resolve_left h⟩
  · exact ⟨(mul_eq_zero.mp h31).resolve_left h, (mul_eq_zero.mp h32).resolve_left h,
      (mul_eq_zero.mp h33).resolve_left h⟩

theorem exists_smul_one_of_commute_noncommuting {F : Type*} [Field F]
    {A B C : Matrix (Fin 2) (Fin 2) F} (hAB : A * B ≠ B * A)
    (hA : A * C = C * A) (hB : B * C = C * B) :
    ∃ c : F, C = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have eA00 := congr_fun (congr_fun hA 0) 0
  have eA01 := congr_fun (congr_fun hA 0) 1
  have eA10 := congr_fun (congr_fun hA 1) 0
  have eB00 := congr_fun (congr_fun hB 0) 0
  have eB01 := congr_fun (congr_fun hB 0) 1
  have eB10 := congr_fun (congr_fun hB 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at eA00 eA01 eA10 eB00 eB01 eB10
  have hscal : C 0 1 = 0 ∧ C 1 0 = 0 ∧ C 0 0 = C 1 1 := by
    by_contra hne
    apply hAB
    have hc : (C 0 0 - C 1 1) ≠ 0 ∨ C 0 1 ≠ 0 ∨ C 1 0 ≠ 0 := by
      by_contra hcc
      push Not at hcc
      exact hne ⟨hcc.2.1, hcc.2.2, sub_eq_zero.mp hcc.1⟩
    obtain ⟨w1, w2, w3⟩ := fin_two_cross_aux (A 0 0 - A 1 1) (A 0 1) (A 1 0)
      (B 0 0 - B 1 1) (B 0 1) (B 1 0) (C 0 0 - C 1 1) (C 0 1) (C 1 0)
      (by linear_combination eA00) (by linear_combination eA10) (by linear_combination eA01)
      (by linear_combination eB00) (by linear_combination eB10) (by linear_combination eB01) hc
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination w1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination w3
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination w2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : F) * w1
  obtain ⟨h01, h10, h00⟩ := hscal
  refine ⟨C 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

theorem mem_center_of_commute_noncommuting {F : Type*} [Field F] {a b c : GL (Fin 2) F}
    (hab : a * b ≠ b * a) (ha : c * a = a * c) (hb : c * b = b * c) :
    c ∈ Subgroup.center (GL (Fin 2) F) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  have hab' : (a : Matrix (Fin 2) (Fin 2) F) * b ≠ b * a := fun h =>
    hab (Units.ext (by simpa using h))
  have ha' : (a : Matrix (Fin 2) (Fin 2) F) * c = c * a := by
    simpa using congrArg Units.val ha.symm
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) * c = c * b := by
    simpa using congrArg Units.val hb.symm
  obtain ⟨s, hs⟩ := exists_smul_one_of_commute_noncommuting hab' ha' hb'
  exact ⟨s, by rw [hs, Matrix.smul_one_eq_diagonal]; simp [Matrix.scalar_apply]⟩

theorem exists_noncomm_of_not_isSolvable {G : Type*} [Group G] {X : Subgroup G}
    (hX : ¬ Group.IsSolvable ↥X) : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x := by
  by_contra h
  push Not at h
  exact hX (Group.isSolvable_of_comm fun a b => Subtype.ext (h a.1 a.2 b.1 b.2))

theorem isSolvable_of_comap_commutator_comm {G Q : Type*} [Group G] [Group Q] (ρ : G →* Q)
    (hρ : Function.Surjective ρ) (X : Subgroup Q)
    (h : ∀ a ∈ ⁅X.comap ρ, X.comap ρ⁆, ∀ b ∈ ⁅X.comap ρ, X.comap ρ⁆, a * b = b * a) :
    Group.IsSolvable ↥X := by
  have hWX : (X.comap ρ).map ρ = X := Subgroup.map_comap_eq_self_of_surjective hρ X
  have hY : ⁅⁅X.comap ρ, X.comap ρ⁆, ⁅X.comap ρ, X.comap ρ⁆⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h a ha b hb)
  refine ⟨⟨2, ?_⟩⟩
  have h2 : (derivedSeries ↥X 2).map X.subtype = ⁅⁅X, X⁆, ⁅X, X⁆⁆ := by
    have : derivedSeries ↥X 2 = ⁅⁅(⊤ : Subgroup ↥X), ⊤⁆, ⁅(⊤ : Subgroup ↥X), ⊤⁆⁆ := rfl
    rw [this]
    simp only [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h3 : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⊥ := by
    calc ⁅⁅X, X⁆, ⁅X, X⁆⁆
        = ⁅⁅(X.comap ρ).map ρ, (X.comap ρ).map ρ⁆, ⁅(X.comap ρ).map ρ, (X.comap ρ).map ρ⁆⁆ := by
          rw [hWX]
      _ = (⁅⁅X.comap ρ, X.comap ρ⁆, ⁅X.comap ρ, X.comap ρ⁆⁆).map ρ := by
          simp only [Subgroup.map_commutator]
      _ = ⊥ := by rw [hY, Subgroup.map_bot]
  rw [h3] at h2
  exact Subgroup.map_injective X.subtype_injective (h2.trans (Subgroup.map_bot _).symm)

theorem centralizer_le_center_of_sl2_of_noncomm {L : Type} [Group L] {F : Type} [Field F]
    (e : L ≃* StatedSL 2 F) {x y g : L} (hxy : x * y ≠ y * x) (hgx : g * x = x * g)
    (hgy : g * y = y * g) : g ∈ Subgroup.center L := by
  let φ : L →* GL (Fin 2) F := (StatedSL 2 F).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hc : φ g ∈ Subgroup.center (GL (Fin 2) F) :=
    mem_center_of_commute_noncommuting (a := φ x) (b := φ y)
      (fun h => hxy (hφ (by simpa only [map_mul] using h)))
      (by rw [← map_mul, ← map_mul, hgx]) (by rw [← map_mul, ← map_mul, hgy])
  rw [Subgroup.mem_center_iff]
  intro h
  apply hφ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hc (φ h)

theorem centralizer_le_center_of_sl2 {L : Type} [Group L] {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (e : L ≃* StatedSL 2 F) {X : Subgroup L}
    (hX : ¬ Group.IsSolvable ↥X) {g : L} (hg : ∀ x ∈ X, g * x = x * g) :
    g ∈ Subgroup.center L := by
  have _ := hF
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_of_not_isSolvable hX
  exact centralizer_le_center_of_sl2_of_noncomm e hxy (hg x hx) (hg y hy)

theorem centralizer_eq_one_of_pgl2_of_not_isSolvable {Q : Type} [Group Q] {F : Type} [Field F]
    (e : Q ≃* Matrix.ProjGenLinGroup (Fin 2) F) {X : Subgroup Q}
    (hX : ¬ Group.IsSolvable ↥X) {g : Q} (hg : ∀ x ∈ X, g * x = x * g) : g = 1 := by
  let ρ : GL (Fin 2) F →* Q := e.symm.toMonoidHom.comp Matrix.ProjGenLinGroup.mk
  have hρ : Function.Surjective ρ := e.symm.surjective.comp Matrix.ProjGenLinGroup.mk_surjective
  have hker : ∀ z : GL (Fin 2) F, ρ z = 1 ↔ z ∈ Subgroup.center (GL (Fin 2) F) := by
    intro z
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    simp [ρ]
  obtain ⟨ĝ, hĝ⟩ := hρ g
  set W : Subgroup (GL (Fin 2) F) := X.comap ρ
  set A : Subgroup (GL (Fin 2) F) := (Subgroup.centralizer (X : Set Q)).comap ρ with hA
  have hgA : ĝ ∈ A := by
    rw [hA, Subgroup.mem_comap, hĝ, Subgroup.mem_centralizer_iff]
    exact fun x hx => (hg x hx).symm
  have hWA : ⁅W, A⁆ ≤ Subgroup.center (GL (Fin 2) F) := by
    rw [Subgroup.commutator_le]
    intro w hw a ha
    rw [← hker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp ha) (ρ w)
      (Subgroup.mem_comap.mp hw)
  have hAW : ⁅A, W⁆ ≤ Subgroup.center (GL (Fin 2) F) := by
    rw [Subgroup.commutator_comm]; exact hWA
  have h1 : ⁅⁅W, A⁆, W⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono_left hWA).trans ?_)
    rw [Subgroup.commutator_center_left]
  have h2 : ⁅⁅A, W⁆, W⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono_left hAW).trans ?_)
    rw [Subgroup.commutator_center_left]
  have h3 : ⁅⁅W, W⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hcomm : ∀ a ∈ ⁅W, W⁆, ĝ * a = a * ĝ := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 ha) ĝ hgA
  have hnc : ∃ a ∈ ⁅W, W⁆, ∃ b ∈ ⁅W, W⁆, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hX (isSolvable_of_comap_commutator_comm ρ hρ X hcon)
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have hc : ĝ ∈ Subgroup.center (GL (Fin 2) F) :=
    mem_center_of_commute_noncommuting hab (hcomm a ha) (hcomm b hb)
  rw [← hĝ]
  exact (hker ĝ).mpr hc

theorem centralizer_eq_one_of_pgl2 {Q : Type} [Group Q] {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (e : Q ≃* Matrix.ProjGenLinGroup (Fin 2) F) {X : Subgroup Q}
    (hX : ¬ Group.IsSolvable ↥X) {g : Q} (hg : ∀ x ∈ X, g * x = x * g) : g = 1 := by
  have _ := hF
  exact centralizer_eq_one_of_pgl2_of_not_isSolvable e hX hg

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
