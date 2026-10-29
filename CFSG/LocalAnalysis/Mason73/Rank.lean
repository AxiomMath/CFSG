module

public import CFSG.LocalAnalysis.Mason73.Omega

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

@[expose] def pat (p : Fin 2 × Fin 2 × Fin 2) : Fin 4 → ℕ := ![0, p.1, p.2.1, p.2.2]

@[expose] def PatFix (π : Perm (Fin 4)) (χ : Fin 4 → ℕ) : Prop :=
  ∀ i j, (χ (π⁻¹ i) + χ j) % 2 = (χ (π⁻¹ j) + χ i) % 2

instance (π : Perm (Fin 4)) (χ : Fin 4 → ℕ) : Decidable (PatFix π χ) :=
  inferInstanceAs (Decidable (∀ i j, (χ (π⁻¹ i) + χ j) % 2 = (χ (π⁻¹ j) + χ i) % 2))

@[expose] def omegaEl (hn : 3 ≤ n) (p : Fin 2 × Fin 2 × Fin 2) : L4Model n :=
  if hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 0 then
    el (hv n (pat p)) 1 (detSum_hv (by omega) hp)
  else el (wv n (pat p)) 1 (detSum_wv hn (by omega))

theorem exists_eq_omegaEl (hn : 3 ≤ n) {a : L4Model n} (ha : a ∈ A n) (ha2 : a * a = 1) :
    ∃ p, a = omegaEl hn p := by
  obtain ⟨χ, hχ2, hχ0, hcase⟩ := eq_of_mem_A_of_mul_self hn ha ha2
  have hpat : pat (⟨χ 1, hχ2 1⟩, ⟨χ 2, hχ2 2⟩, ⟨χ 3, hχ2 3⟩) = χ := by
    funext i
    fin_cases i <;> simp [pat, hχ0]
  refine ⟨(⟨χ 1, hχ2 1⟩, ⟨χ 2, hχ2 2⟩, ⟨χ 3, hχ2 3⟩), ?_⟩
  rw [omegaEl]
  rcases hcase with ⟨h, hpar, rfl⟩ | ⟨h, hpar, rfl⟩
  · rw [dif_pos (by rw [hpat]; exact hpar)]
    exact el_congr _ _ (by rw [hpat]) rfl
  · rw [dif_neg (by rw [hpat]; omega)]
    exact el_congr _ _ (by rw [hpat]) rfl

theorem patFix_of_comm (hn : 3 ≤ n) {s : L4Model n} {p : Fin 2 × Fin 2 × Fin 2}
    (h : s * omegaEl hn p = omegaEl hn p * s) : PatFix (piT s : Perm (Fin 4)) (pat p) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el s
  rw [piT_el]
  have key : ∀ e : Fin 4 → ZMod (2 ^ n), IsConst (pv (π : Perm (Fin 4)) e - e) →
      pv (π : Perm (Fin 4)) e - e = pv (π : Perm (Fin 4)) (hv n (pat p)) - hv n (pat p) →
      PatFix π (pat p) := by
    intro e hc heq
    rw [heq, pv_hv, hv_sub_hv_isConst_iff (by omega)] at hc
    exact hc
  unfold omegaEl at h
  split_ifs at h with hp
  · exact key _ ((el_comm_diag_iff (by omega) hd _).1 h) rfl
  · refine key _ ((el_comm_diag_iff (by omega) hd _).1 h) ?_
    funext i
    simp only [Pi.sub_apply, pv, wv]
    ring

theorem mul_comm_of_mul_self {G : Type*} [Group G] {E : Subgroup G} (hE : ∀ x ∈ E, x * x = 1)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (hE x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left (hE y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_left (hE _ (E.mul_mem hx hy))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem card_eq_card_inf_A_mul (E : Subgroup (L4Model n)) :
    Nat.card E = Nat.card (E ⊓ A n : Subgroup (L4Model n)) * Nat.card (E.map piT) := by
  set f : E →* Fin81.R0 := piT.comp E.subtype
  have hker : Nat.card f.ker = Nat.card (E ⊓ A n : Subgroup (L4Model n)) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, mem_A_iff.2 (MonoidHom.mem_ker.1 x.2)⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
          MonoidHom.mem_ker.2 (mem_A_iff.1 (Subgroup.mem_inf.1 y.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : f.range = E.map piT := by
    ext π
    simp [f, MonoidHom.mem_range, Subgroup.mem_map]
  have h := Subgroup.card_ker_mul_card_of_surjective f.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict, hker] at h
  rw [← h, hrange]

theorem card_inf_A_le (hn : 3 ≤ n) (E : Subgroup (L4Model n)) (hE : ∀ x ∈ E, x * x = 1)
    (S : Set (L4Model n)) (hS : ∀ s ∈ S, ∀ x ∈ E ⊓ A n, s * x = x * s)
    (P : Finset (Fin 2 × Fin 2 × Fin 2))
    (hP : ∀ p, (∀ s ∈ S, PatFix (piT s : Perm (Fin 4)) (pat p)) → p ∈ P) :
    Nat.card (E ⊓ A n : Subgroup (L4Model n)) ≤ P.card := by
  classical
  have hsub : ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)) ⊆
      ((P.image (omegaEl hn) : Finset (L4Model n)) : Set (L4Model n)) := by
    intro x hx
    have hx' := Subgroup.mem_inf.1 hx
    obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hx'.2 (hE _ hx'.1)
    rw [Finset.coe_image]
    exact ⟨p, hP p fun s hs => patFix_of_comm hn (hS s hs _ hx), rfl⟩
  calc Nat.card (E ⊓ A n : Subgroup (L4Model n))
      = ((E ⊓ A n : Subgroup (L4Model n)) : Set (L4Model n)).ncard := Nat.card_coe_set_eq _
    _ ≤ ((P.image (omegaEl hn) : Finset (L4Model n)) : Set (L4Model n)).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (P.image (omegaEl hn)).card := Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le

abbrev c4 : Fin81.R0 := ⟨swap 0 2 * swap 1 3 * swap 0 1, by decide⟩

theorem card_map_piT_le_four (E : Subgroup (L4Model n)) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card (E.map piT) ≤ 4 := by
  have hdvd : Nat.card (E.map piT) ∣ 8 := by
    rw [← Fin81.card_R0]
    exact Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (E.map piT) ≠ 8 := by
    intro h8
    have htop : E.map piT = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h8, Fin81.card_R0])
    have hc : c4 ∈ E.map piT := htop ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 hc
    have h1 := congrArg piT (hE x hx)
    rw [map_mul, hxc, map_one] at h1
    exact absurd h1 (by decide)
  have hmem : Nat.card (E.map piT) ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 8 = {1, 2, 4, 8} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem card_map_piT_le_two (E : Subgroup (L4Model n)) {τ : Fin81.R0}
    (hτ : ∀ x ∈ E, piT x = 1 ∨ piT x = τ) : Nat.card (E.map piT) ≤ 2 := by
  have hsub : ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0) ⊆ {1, τ} := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hτ x hx with h | h <;> simp [h]
  calc Nat.card (E.map piT) = ((E.map piT : Subgroup Fin81.R0) : Set Fin81.R0).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, τ} : Set Fin81.R0).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem card_pat_le : (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).card ≤ 8 := by decide

theorem card_patFix_le : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → π ≠ 1 →
    (Finset.univ.filter fun p : Fin 2 × Fin 2 × Fin 2 => PatFix π (pat p)).card ≤ 4 := by
  decide

theorem card_patFix_s23_le : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → π * swap 2 3 = swap 2 3 * π →
    π ≠ 1 → π ≠ swap 2 3 →
    (Finset.univ.filter fun p : Fin 2 × Fin 2 × Fin 2 =>
      PatFix (swap 2 3) (pat p) ∧ PatFix π (pat p)).card ≤ 2 := by
  decide

theorem card_inf_A_le_eight (hn : 3 ≤ n) (E : Subgroup (L4Model n)) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card (E ⊓ A n : Subgroup (L4Model n)) ≤ 8 :=
  (card_inf_A_le hn E hE ∅ (by simp) Finset.univ (fun p _ => Finset.mem_univ p)).trans
    card_pat_le

theorem card_inf_A_le_four (hn : 3 ≤ n) (E : Subgroup (L4Model n)) (hE : ∀ x ∈ E, x * x = 1)
    {g : L4Model n} (hg : piT g ≠ 1) (hgE : ∀ x ∈ E ⊓ A n, g * x = x * g) :
    Nat.card (E ⊓ A n : Subgroup (L4Model n)) ≤ 4 := by
  refine (card_inf_A_le hn E hE {g} (by simpa using hgE) _ ?_).trans
    (card_patFix_le _ (piT g).2 fun h => hg (Subtype.ext h))
  intro p hp
  simpa using hp g rfl

theorem card_le_sixteen_of_mul_self (hn : 3 ≤ n) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  rw [card_eq_card_inf_A_mul]
  by_cases hall : ∀ x ∈ E, piT x = 1
  · have h1 : Nat.card (E.map piT) ≤ 1 := by
      rw [Subgroup.card_le_one_iff_eq_bot, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_bot).2 (hall x hx)
    have h8 := card_inf_A_le_eight hn E hE
    calc _ ≤ 8 * 1 := Nat.mul_le_mul h8 h1
      _ ≤ 16 := by norm_num
  · push Not at hall
    obtain ⟨g, hg, hg1⟩ := hall
    have h4 := card_inf_A_le_four hn E hE hg1 fun x hx =>
      mul_comm_of_mul_self hE hg (Subgroup.mem_inf.1 hx).1
    calc _ ≤ 4 * 4 := Nat.mul_le_mul h4 (card_map_piT_le_four E hE)
      _ = 16 := rfl

theorem card_le_eight_of_piT_mem (hn : 3 ≤ n) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) {τ : Fin81.R0} (hτ : ∀ x ∈ E, piT x = 1 ∨ piT x = τ) :
    Nat.card E ≤ 8 := by
  rw [card_eq_card_inf_A_mul]
  by_cases hall : ∀ x ∈ E, piT x = 1
  · have h1 : Nat.card (E.map piT) ≤ 1 := by
      rw [Subgroup.card_le_one_iff_eq_bot, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_bot).2 (hall x hx)
    calc _ ≤ 8 * 1 := Nat.mul_le_mul (card_inf_A_le_eight hn E hE) h1
      _ = 8 := rfl
  · push Not at hall
    obtain ⟨g, hg, hg1⟩ := hall
    have h4 := card_inf_A_le_four hn E hE hg1 fun x hx =>
      mul_comm_of_mul_self hE hg (Subgroup.mem_inf.1 hx).1
    calc _ ≤ 4 * 2 := Nat.mul_le_mul h4 (card_map_piT_le_two E hτ)
      _ = 8 := rfl

theorem card_le_eight_of_le_centralizer (hn : 3 ≤ n) {g : L4Model n}
    (hg : (piT g : Perm (Fin 4)) = swap 2 3) (E : Subgroup (L4Model n))
    (hE : ∀ x ∈ E, x * x = 1) (hEg : E ≤ centralizer {g}) : Nat.card E ≤ 8 := by
  have hcomm : ∀ x ∈ E, g * x = x * g := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hEg hx)).symm
  have hg1 : piT g ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    rw [hg] at this
    exact absurd this (by decide)
  rw [card_eq_card_inf_A_mul]
  by_cases hall : ∀ x ∈ E, piT x = 1 ∨ piT x = piT g
  · have h4 := card_inf_A_le_four hn E hE hg1 fun x hx => hcomm x (Subgroup.mem_inf.1 hx).1
    calc _ ≤ 4 * 2 := Nat.mul_le_mul h4 (card_map_piT_le_two E hall)
      _ = 8 := rfl
  · push Not at hall
    obtain ⟨e, he, he1, heg⟩ := hall
    have hcomm' : (piT e : Perm (Fin 4)) * swap 2 3 = swap 2 3 * (piT e : Perm (Fin 4)) := by
      rw [← hg]
      exact congrArg Subtype.val
        (show piT e * piT g = piT g * piT e by rw [← map_mul, ← map_mul, hcomm e he])
    have h2 : Nat.card (E ⊓ A n : Subgroup (L4Model n)) ≤ 2 := by
      refine (card_inf_A_le hn E hE {g, e} ?_ _ ?_).trans
        (card_patFix_s23_le _ (piT e).2 hcomm' (fun h => he1 (Subtype.ext h))
          (fun h => heg (Subtype.ext (h.trans hg.symm))))
      · rintro s (rfl | rfl) x hx
        · exact hcomm x (Subgroup.mem_inf.1 hx).1
        · exact mul_comm_of_mul_self hE he (Subgroup.mem_inf.1 hx).1
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hg ▸ hp g (by simp), hp e (by simp)⟩
    calc _ ≤ 2 * 4 := Nat.mul_le_mul h2 (card_map_piT_le_four E hE)
      _ = 8 := rfl

end CFSG.LocalAnalysis.Mason73
