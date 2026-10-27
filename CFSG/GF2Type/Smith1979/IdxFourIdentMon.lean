module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMonPlanes

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

open MonAux

@[expose] def unitSub : Subgroup G12 := Subgroup.centralizer {theta0e}

@[expose] def D6 : Subgroup G12 where
  carrier := {g | ∃ c, g = diagE c}
  mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩; exact ⟨c + c', (diagE_add c c').symm⟩
  one_mem' := ⟨0, diagE_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, inv_eq_of_mul_eq_one_left ?_⟩
    rw [← diagE_add, neg_add_cancel, diagE_zero]

@[expose] def D5 : Subgroup G12 where
  carrier := {g | ∃ c, (∑ i, c i) = 0 ∧ g = diagE c}
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', by simp [Finset.sum_add_distrib, hc, hc'], (diagE_add c c').symm⟩
  one_mem' := ⟨0, by simp, diagE_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨-c, by simp [Finset.sum_neg_distrib, hc], inv_eq_of_mul_eq_one_left ?_⟩
    rw [← diagE_add, neg_add_cancel, diagE_zero]

@[expose] def monGamma : Subgroup G12 where
  carrier := {g | ∃ (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2),
    g = diagE c * permE π * frobE ^ ε.val}
  mul_mem' := by
    rintro _ _ ⟨c, π, ε, rfl⟩ ⟨c', π', ε', rfl⟩
    obtain ⟨c'', ε'', h⟩ := exists_diag_perm_aux (π := π * π')
      (mul_mem (mon_mem_gammaU c π ε) (mon_mem_gammaU c' π' ε'))
      (fun _ _ hx => mon_mem_plane c π ε (mon_mem_plane c' π' ε' hx))
    exact ⟨c'', π * π', ε'', h⟩
  one_mem' := ⟨0, 1, 0, by rw [diagE_zero, permE_one, frobPow_zero, mul_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨c, π, ε, rfl⟩
    obtain ⟨c', ε', h⟩ := exists_diag_perm_aux (π := π⁻¹) (inv_mem (mon_mem_gammaU c π ε))
      (fun _ _ hx => mon_inv_mem_plane c π ε hx)
    exact ⟨c', π⁻¹, ε', h⟩

@[expose] def monLin : Subgroup G12 := monGamma ⊓ unitSub

theorem mem_monLin_iff {g : G12} : g ∈ monLin ↔ ∃ (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)),
    g = diagE c * permE π := by
  constructor
  · rintro ⟨⟨c, π, ε, rfl⟩, hu⟩
    rcases zmod2_cases ε with rfl | rfl
    · exact ⟨c, π, by rw [frobPow_zero, mul_one]⟩
    · exfalso
      rw [frobPow_one] at hu
      have h := Subgroup.mem_centralizer_iff.1 hu theta0e (Set.mem_singleton _)
      have h' : theta0e * frobE = frobE * theta0e := by
        refine mul_left_cancel (a := diagE c * permE π) ?_
        calc diagE c * permE π * (theta0e * frobE)
            = (diagE c * permE π * theta0e) * frobE := (mul_assoc _ _ _).symm
          _ = (theta0e * (diagE c * permE π)) * frobE := by rw [mon_comm_theta0e]
          _ = theta0e * (diagE c * permE π * frobE) := mul_assoc _ _ _
          _ = diagE c * permE π * frobE * theta0e := h
          _ = diagE c * permE π * (frobE * theta0e) := mul_assoc _ _ _
      exact frobE_not_comm h'.symm
  · rintro ⟨c, π, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨c, π, 0, by rw [frobPow_zero, mul_one]⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    exact mon_comm_theta0e c π

theorem D6_le_monLin : D6 ≤ monLin := by
  rintro g ⟨c, rfl⟩
  exact mem_monLin_iff.2 ⟨c, 1, by rw [permE_one, mul_one]⟩

theorem monLin_le_monGamma : monLin ≤ monGamma := inf_le_left

theorem monGamma_le_gammaU : monGamma ≤ gammaU := by
  rintro g ⟨c, π, ε, rfl⟩
  exact mon_mem_gammaU c π ε

theorem permE_mem_monLin (π : Equiv.Perm (Fin 6)) : permE π ∈ monLin :=
  mem_monLin_iff.2 ⟨0, π, by rw [diagE_zero, one_mul]⟩

namespace MonAux

theorem nat_card_fun_zmod3 : Nat.card (Fin 6 → ZMod 3) = 3 ^ 6 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem nat_card_perm_fin6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

@[expose] def sumZeroEquiv : {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} ≃ (Fin 5 → ZMod 3) where
  toFun c := fun i => c.1 i.castSucc
  invFun a := ⟨Fin.snoc (α := fun _ => ZMod 3) a (-∑ i, a i), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact add_neg_cancel _⟩
  left_inv c := by
    refine Subtype.ext (funext fun i => ?_)
    have h := c.2
    rw [Fin.sum_univ_castSucc] at h
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      exact neg_eq_of_add_eq_zero_right h
    · simp only [Fin.snoc_castSucc]
  right_inv a := funext fun i => by simp only [Fin.snoc_castSucc]

end MonAux

theorem card_D5 : Nat.card D5 = 3 ^ 5 := by
  have hbij : Function.Bijective (fun c : {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} =>
      (⟨diagE c.1, c.1, c.2, rfl⟩ : D5)) :=
    ⟨fun _ _ hab => Subtype.ext (diagE_injective (congrArg Subtype.val hab)),
      fun ⟨_, c, hc, hg⟩ => ⟨⟨c, hc⟩, Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_congr sumZeroEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_monLin : Nat.card monLin = 3 ^ 6 * 720 := by
  have hbij : Function.Bijective (fun a : (Fin 6 → ZMod 3) × Equiv.Perm (Fin 6) =>
      (⟨diagE a.1 * permE a.2, mem_monLin_iff.2 ⟨a.1, a.2, rfl⟩⟩ : monLin)) := by
    refine ⟨fun a b hab => ?_, fun ⟨g, hg⟩ => ?_⟩
    · have h := congrArg Subtype.val hab
      have h' : diagE a.1 * permE a.2 * frobE ^ (0 : ZMod 2).val =
          diagE b.1 * permE b.2 * frobE ^ (0 : ZMod 2).val := by
        rw [frobPow_zero, mul_one, mul_one]
        exact h
      obtain ⟨h1, h2, -⟩ := mon_inj h'
      exact Prod.ext h1 h2
    · obtain ⟨c, π, rfl⟩ := mem_monLin_iff.1 hg
      exact ⟨(c, π), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, nat_card_fun_zmod3,
    nat_card_perm_fin6]

theorem card_monGamma : Nat.card monGamma = 3 ^ 6 * 720 * 2 := by
  have hbij : Function.Bijective (fun a : (Fin 6 → ZMod 3) × Equiv.Perm (Fin 6) × ZMod 2 =>
      (⟨diagE a.1 * permE a.2.1 * frobE ^ a.2.2.val, a.1, a.2.1, a.2.2, rfl⟩ : monGamma)) := by
    refine ⟨fun a b hab => ?_, fun ⟨g, c, π, ε, hg⟩ => ⟨(c, π, ε), Subtype.ext hg.symm⟩⟩
    obtain ⟨h1, h2, h3⟩ := mon_inj (congrArg Subtype.val hab)
    exact Prod.ext h1 (Prod.ext h2 h3)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_prod,
    nat_card_fun_zmod3, nat_card_perm_fin6, Nat.card_zmod, mul_assoc]

theorem mul_mem_D5_of_mem_monGamma {g d : G12} (hg : g ∈ monGamma) (hd : d ∈ D5) :
    g * d * g⁻¹ ∈ D5 := by
  obtain ⟨c, π, ε, rfl⟩ := hg
  obtain ⟨c', hc', rfl⟩ := hd
  rcases zmod2_cases ε with rfl | rfl
  · rw [frobPow_zero, mul_one, conj_mon_zero]
    refine ⟨fun i => c' (π.symm i), ?_, rfl⟩
    show (∑ i, c' (π.symm i)) = 0
    rw [Equiv.sum_comp π.symm c']
    exact hc'
  · rw [frobPow_one, conj_mon_one]
    refine ⟨fun i => (-c') (π.symm i), ?_, rfl⟩
    show (∑ i, (-c') (π.symm i)) = 0
    rw [Equiv.sum_comp π.symm (-c')]
    simp [Finset.sum_neg_distrib, hc']

namespace MonAux

theorem conj_inv_mem_D5 {g : G12} (h : ∀ d ∈ D5, g * d * g⁻¹ ∈ D5) :
    ∀ d ∈ D5, g⁻¹ * d * g ∈ D5 := by
  haveI : Finite D5 := Finite.of_surjective
    (fun c : {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} => (⟨diagE c.1, c.1, c.2, rfl⟩ : D5))
    (fun ⟨_, c, hc, hg⟩ => ⟨⟨c, hc⟩, Subtype.ext hg.symm⟩)
  intro d hd
  let φ : D5 → D5 := fun d' => ⟨g * d' * g⁻¹, h d' d'.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨⟨d', hd'⟩, hd'eq⟩ := Finite.injective_iff_surjective.1 hφ ⟨d, hd⟩
  have h1 : g * d' * g⁻¹ = d := congrArg Subtype.val hd'eq
  have h2 : g⁻¹ * d * g = d' := by rw [← h1]; group
  rw [h2]
  exact hd'

theorem exists_plane_of_normalizes {g : G12} (hg : g ∈ gammaU)
    (hinv : ∀ d ∈ D5, g⁻¹ * d * g ∈ D5) {i : Fin 6} {x : V12} (hx : x ∈ plane i) (h0 : x ≠ 0) :
    ∃ j, g x ∈ plane j := by
  obtain ⟨e, he⟩ := g_diag_const hg
  have hy0 : g x ≠ 0 := fun h => h0 (g.injective (h.trans (map_zero g).symm))
  have key : ∀ c : Fin 6 → ZMod 3, (∑ l, c l) = 0 →
      ∃ m : ZMod 3, diagE c (g x) = diagE (fun _ => m) (g x) := by
    intro c hc
    obtain ⟨c', -, hc'⟩ := hinv (diagE c) ⟨c, hc, rfl⟩
    refine ⟨e * c' i, ?_⟩
    have h1 : diagE c * g = g * diagE c' := by rw [← hc']; group
    calc diagE c (g x) = (g * diagE c') x := by rw [← h1]; rfl
      _ = g (diagE (fun _ => c' i) x) := by
        rw [LinearEquiv.mul_apply, diagE_eq_const_of_mem_plane hx]
      _ = diagE (fun _ => e * c' i) (g x) := he _ _
  obtain ⟨j, hj⟩ : ∃ j, pr (g x) j ≠ 0 := by
    by_contra hcon
    exact hy0 (ext_pr fun j => not_not.1 fun hne => hcon ⟨j, hne⟩)
  refine ⟨j, mem_plane_iff_pr.2 fun l hl => ?_⟩
  by_contra hl0
  obtain ⟨c, hcj, hcl, hcsum⟩ : ∃ c : Fin 6 → ZMod 3, c j = 1 ∧ c l = 2 ∧ ∑ t, c t = 0 :=
    ⟨fun t => if t = j then 1 else if t = l then 2 else 0, if_pos rfl,
      (if_neg hl).trans (if_pos rfl), sum_clash j l hl.symm⟩
  obtain ⟨m, hm⟩ := key c hcsum
  have h1 := congrArg (fun y => pr y j) hm
  have h2 := congrArg (fun y => pr y l) hm
  simp only [pr_diagE, hcj, hcl] at h1 h2
  exact omegaPow_clash m _ _ hj hl0 h1 h2

theorem exists_planes_map {g : G12} (hg : g ∈ gammaU) (hinv : ∀ d ∈ D5, g⁻¹ * d * g ∈ D5) :
    ∃ f : Fin 6 → Fin 6, ∀ i, ∀ x ∈ plane i, g x ∈ plane (f i) := by
  have hex : ∀ i, ∃ j, g (pairVec i (1, 0)) ∈ plane j := fun i =>
    exists_plane_of_normalizes hg hinv (pairVec_mem_plane i _) (pairVec_ne_zero i (by decide))
  choose f hf using hex
  refine ⟨f, fun i x hx => ?_⟩
  rw [eq_pairVec_of_mem_plane hx]
  by_cases hp : pr x i = 0
  · rw [hp, pairVec_zero, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨k, hk⟩ := exists_omegaPow_of_ne_zero _ hp
    obtain ⟨e, he⟩ := g_diag_const hg
    have h1 : pairVec i (pr x i) = diagE (fun _ => k) (pairVec i (1, 0)) := by
      rw [diagE_pairVec, hk]
    rw [h1, he]
    exact diagE_mem_plane (hf i) _

end MonAux

theorem exists_diag_perm_of_planes {g : G12} (hg : g ∈ gammaU) {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, ∀ x ∈ plane i, g x ∈ plane (π i)) :
    ∃ (c : Fin 6 → ZMod 3) (ε : ZMod 2), g = diagE c * permE π * frobE ^ ε.val :=
  exists_diag_perm_aux hg h

theorem mem_monGamma_of_normalizes_D5 {g : G12} (hg : g ∈ gammaU)
    (h : ∀ d ∈ D5, g * d * g⁻¹ ∈ D5) : g ∈ monGamma := by
  obtain ⟨f, hf⟩ := exists_planes_map hg (conj_inv_mem_D5 h)
  obtain ⟨f', hf'⟩ := exists_planes_map (inv_mem hg) (fun d hd => by rw [inv_inv]; exact h d hd)
  have hg_inv : ∀ x : V12, g⁻¹ (g x) = x := fun x => g.symm_apply_apply x
  have hg_apply : ∀ x : V12, g (g⁻¹ x) = x := fun x => g.apply_symm_apply x
  have hleft : ∀ i, f' (f i) = i := fun i => by
    have h1 := hf i _ (pairVec_mem_plane i (1, 0))
    have h2 := hf' (f i) _ h1
    rw [hg_inv] at h2
    exact (eq_of_mem_plane_of_mem_plane (pairVec_mem_plane i _) h2
      (pairVec_ne_zero i (by decide))).symm
  have hright : ∀ i, f (f' i) = i := fun i => by
    have h1 := hf' i _ (pairVec_mem_plane i (1, 0))
    have h2 := hf (f' i) _ h1
    rw [hg_apply] at h2
    exact (eq_of_mem_plane_of_mem_plane (pairVec_mem_plane i _) h2
      (pairVec_ne_zero i (by decide))).symm
  let π : Equiv.Perm (Fin 6) := ⟨f, f', hleft, hright⟩
  obtain ⟨c, ε, hgc⟩ := exists_diag_perm_of_planes hg (π := π) (fun i x hx => hf i x hx)
  exact ⟨c, π, ε, hgc⟩

end CFSG.GF2Type.Smith1979.IdxFour
