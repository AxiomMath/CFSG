module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LieType.Chevalley.G2Rank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace G2Radical

section ClassTwo

variable {G : Type*} [Group G]

theorem class_two_pow_aux (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * (x * y ^ n) := by
  have hc : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * y := (hy.symm.pow_right n).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (⁅y, x⁆ ^ n * (x * y ^ n)) := by rw [ih]
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by rw [← mul_assoc, h1]; group
      _ = ⁅y, x⁆ ^ n * (⁅y, x⁆ * (x * y)) * y ^ n := by rw [hc]
      _ = ⁅y, x⁆ ^ (n + 1) * (x * y ^ (n + 1)) := by rw [pow_succ, pow_succ']; group

theorem class_two_pow (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x ^ n := ((hx.pow_pow n n).symm).eq
    have h2 : (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
    have h3 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := h2
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (y ^ n * x) * y) := by rw [ih]; group
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (⁅y, x⁆ ^ n * (x * y ^ n)) * y) := by
        rw [class_two_pow_aux x y hx hy n]
      _ = ⁅y, x⁆ ^ n.choose 2 * (⁅y, x⁆ ^ n * (x ^ n * (x * y ^ n)) * y) := by
        rw [← mul_assoc (x ^ n), h1]; group
      _ = ⁅y, x⁆ ^ (n + 1).choose 2 * (x ^ (n + 1) * y ^ (n + 1)) := by
        rw [h3]; group

theorem class_two_pow_prime {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (x y : G)
    (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [class_two_pow x y hx hy p]
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : 2 ≠ 0) hp3
  rw [hk, pow_mul, hc, one_pow, one_mul]

theorem commute_iSup {ι : Sort*} (S : ι → Subgroup G) (z : G)
    (h : ∀ i, ∀ y ∈ S i, z * y = y * z) : ∀ g ∈ ⨆ i, S i, z * g = g * z := by
  intro g hg
  refine Subgroup.iSup_induction S (C := fun g => z * g = g * z) hg h (by simp) ?_
  intro a b ha hb
  rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem commutator_mem_iSup {ι : Sort*} (S : ι → Subgroup G) (Z : Subgroup G)
    (hZV : ∀ z ∈ Z, ∀ g ∈ ⨆ i, S i, z * g = g * z)
    (hgen : ∀ i j, ∀ x ∈ S i, ∀ y ∈ S j, x * y * x⁻¹ * y⁻¹ ∈ Z) :
    ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y * x⁻¹ * y⁻¹ ∈ Z := by
  have step1 : ∀ i, ∀ x ∈ S i, ∀ y ∈ ⨆ i, S i, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro i x hx y hy
    refine Subgroup.iSup_induction' S (C := fun y _ => x * y * x⁻¹ * y⁻¹ ∈ Z) ?_ ?_ ?_ hy
    · intro j y hy; exact hgen i j x hx y hy
    · simp
    · intro y1 y2 hy1 hy2 h1 h2
      have key : x * (y1 * y2) * x⁻¹ * (y1 * y2)⁻¹ =
          (x * y1 * x⁻¹ * y1⁻¹) * (y1 * (x * y2 * x⁻¹ * y2⁻¹) * y1⁻¹) := by group
      have hconj : y1 * (x * y2 * x⁻¹ * y2⁻¹) * y1⁻¹ = x * y2 * x⁻¹ * y2⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]; exact (hZV _ h2 y1 hy1).symm
      rw [key, hconj]
      exact mul_mem h1 h2
  intro x hx y hy
  refine Subgroup.iSup_induction' S (C := fun x _ => x * y * x⁻¹ * y⁻¹ ∈ Z) ?_ ?_ ?_ hx
  · intro i x hx; exact step1 i x hx y hy
  · simp
  · intro x1 x2 hx1 hx2 h1 h2
    have key : x1 * x2 * y * (x1 * x2)⁻¹ * y⁻¹ =
        (x1 * (x2 * y * x2⁻¹ * y⁻¹) * x1⁻¹) * (x1 * y * x1⁻¹ * y⁻¹) := by group
    have hconj : x1 * (x2 * y * x2⁻¹ * y⁻¹) * x1⁻¹ = x2 * y * x2⁻¹ * y⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]; exact (hZV _ h2 x1 hx1).symm
    rw [key, hconj]
    exact mul_mem h2 h1

theorem pow_eq_one_iSup {ι : Sort*} (S : ι → Subgroup G) (Z : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hp3 : 2 < p) (hZV : ∀ z ∈ Z, ∀ g ∈ ⨆ i, S i, z * g = g * z)
    (hcomm : ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hZp : ∀ z ∈ Z, z ^ p = 1) (hS : ∀ i, ∀ x ∈ S i, x ^ p = 1) :
    ∀ g ∈ ⨆ i, S i, g ^ p = 1 := by
  intro g hg
  refine Subgroup.iSup_induction' S (C := fun g _ => g ^ p = 1) ?_ ?_ ?_ hg
  · exact hS
  · simp
  · intro x y hx hy h1 h2
    have hc : ⁅y, x⁆ ∈ Z := by
      rw [commutatorElement_def]; exact hcomm y hy x hx
    have hcx : Commute ⁅y, x⁆ x := hZV _ hc x hx
    have hcy : Commute ⁅y, x⁆ y := hZV _ hc y hy
    rw [class_two_pow_prime hp hp3 x y hcx hcy (hZp _ hc), h1, h2, one_mul]

end ClassTwo

section FirstCoord


theorem g2_root_first_coord {γ : Fin 2 → ℤ} (hγ : IsRoot .G2 γ) :
    γ 0 ≤ 2 ∧ (γ 0 = 2 → γ 1 = 3) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  interval_cases k <;> decide

end FirstCoord

end G2Radical

section G2

namespace G2Radical

noncomputable def radRoot : Fin 5 → Root .G2 :=
  ![g2Root [1, 0, 1, 0, 1] 0, g2Root [0, 1, 0, 1] 1, g2Root [1, 0, 1] 0, g2Root [0, 1] 1,
    g2Root [1] 0]

abbrev rc (β : Root .G2) (k : Fin 2) : ℤ := β.1 k

theorem g2Root_val (ω : List (Fin 2)) (i : Fin 2) :
    (g2Root ω i).1 = ω.reverse.foldr (reflect .G2) (Pi.single i 1) :=
  val_inv_smul_simpleRoot (τ := .G2) ω i

theorem radRoot_coords (i : Fin 5) :
    rc (radRoot i) 0 = ![1, 1, 2, 1, 1] i ∧ rc (radRoot i) 1 = ![0, 1, 3, 2, 3] i := by
  fin_cases i
  · show rc (g2Root [1, 0, 1, 0, 1] 0) 0 = 1 ∧ rc (g2Root [1, 0, 1, 0, 1] 0) 1 = 0
    unfold rc
    rw [g2Root_val]
    decide +kernel
  · show rc (g2Root [0, 1, 0, 1] 1) 0 = 1 ∧ rc (g2Root [0, 1, 0, 1] 1) 1 = 1
    unfold rc
    rw [g2Root_val]
    decide +kernel
  · show rc (g2Root [1, 0, 1] 0) 0 = 2 ∧ rc (g2Root [1, 0, 1] 0) 1 = 3
    unfold rc
    rw [g2Root_val]
    decide +kernel
  · show rc (g2Root [0, 1] 1) 0 = 1 ∧ rc (g2Root [0, 1] 1) 1 = 2
    unfold rc
    rw [g2Root_val]
    decide +kernel
  · show rc (g2Root [1] 0) 0 = 1 ∧ rc (g2Root [1] 0) 1 = 3
    unfold rc
    rw [g2Root_val]
    decide +kernel

theorem radRoot_c0 (i : Fin 5) : 1 ≤ rc (radRoot i) 0 ∧ rc (radRoot i) 0 ≤ 2 := by
  rw [(radRoot_coords i).1]
  fin_cases i <;> decide

theorem radRoot_c0_two : rc (radRoot 2) 0 = 2 := by
  rw [(radRoot_coords 2).1]; rfl

theorem radRoot_height_pos (i : Fin 5) : 0 < height (radRoot i).1 := by
  have h0 := (radRoot_coords i)
  have h1 : 0 ≤ rc (radRoot i) 1 := by
    rw [h0.2]; fin_cases i <;> decide
  have h2 := (radRoot_c0 i).1
  have hsum : height (radRoot i).1 = rc (radRoot i) 0 + rc (radRoot i) 1 := Fin.sum_univ_two _
  omega

theorem radRoot_injective : Function.Injective radRoot := by
  intro i j hij
  have h0 := congrArg (fun β => rc β 0) hij
  have h1 := congrArg (fun β => rc β 1) hij
  simp only [(radRoot_coords _).1, (radRoot_coords _).2] at h0 h1
  revert h0 h1
  revert i j
  decide

theorem coord_of_sum (i j : Fin 5) (γ : Root .G2) (a b : ℕ)
    (h : γ.1 = a • (radRoot i).1 + b • (radRoot j).1) :
    rc γ 0 = a * rc (radRoot i) 0 + b * rc (radRoot j) 0 := by
  have := congrFun h (0 : Fin 2)
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at this
  exact this

theorem radRoot_sum_eq (i j : Fin 5) (γ : Root .G2) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : γ.1 = a • (radRoot i).1 + b • (radRoot j).1) : γ = radRoot 2 := by
  have hγ := g2_root_first_coord γ.2
  have h0 := coord_of_sum i j γ a b h
  have hi := radRoot_c0 i
  have hj := radRoot_c0 j
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hai : 1 ≤ (a : ℤ) * rc (radRoot i) 0 := by nlinarith [hi.1]
  have hbj : 1 ≤ (b : ℤ) * rc (radRoot j) 0 := by nlinarith [hj.1]
  have hle : rc γ 0 ≤ 2 := hγ.1
  have e0 : rc γ 0 = 2 := by linarith
  have e1 : rc γ 1 = 3 := hγ.2 e0
  apply Subtype.ext
  funext k
  fin_cases k
  · show rc γ 0 = rc (radRoot 2) 0
    rw [e0, radRoot_c0_two]
  · show rc γ 1 = rc (radRoot 2) 1
    rw [e1, (radRoot_coords 2).2]; rfl

theorem radRoot_central_no_root (i : Fin 5) (γ : Root .G2) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : γ.1 = a • (radRoot 2).1 + b • (radRoot i).1) : False := by
  have hγ := g2_root_first_coord γ.2
  have h0 := coord_of_sum 2 i γ a b h
  have hi := radRoot_c0 i
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hai : 2 ≤ (a : ℤ) * rc (radRoot 2) 0 := by rw [radRoot_c0_two]; linarith
  have hbj : 1 ≤ (b : ℤ) * rc (radRoot i) 0 := by nlinarith [hi.1]
  have hle : rc γ 0 ≤ 2 := hγ.1
  linarith

noncomputable abbrev Xr (F : Type) [Field F] (β : Root .G2) : Subgroup (adjointGroup .G2 F) :=
  (rootOperatorFamily .G2).rootSubgroup F β

theorem Xr_comm (F : Type) [Field F] (β : Root .G2) {x y : adjointGroup .G2 F}
    (hx : x ∈ Xr F β) (hy : y ∈ Xr F β) : x * y = y * x := by
  obtain ⟨c, rfl⟩ := ((rootOperatorFamily .G2).mem_rootSubgroup).1 hx
  obtain ⟨d, rfl⟩ := ((rootOperatorFamily .G2).mem_rootSubgroup).1 hy
  rw [← (rootOperatorFamily .G2).eltElement_add, ← (rootOperatorFamily .G2).eltElement_add,
    add_comm]

theorem radRoot_comm_mem (F : Type) [Field F] (i j : Fin 5) (hij : i ≠ j) :
    ∀ x ∈ Xr F (radRoot i), ∀ y ∈ Xr F (radRoot j), x * y * x⁻¹ * y⁻¹ ∈ Xr F (radRoot 2) := by
  intro x hx y hy
  have h := commContained_pos F (radRoot i) (radRoot j) (radRoot_height_pos i)
    (radRoot_height_pos j) (radRoot_injective.ne hij) x hx y hy
  have hle : (⨆ (γ : Root .G2) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      γ.1 = a • (radRoot i).1 + b • (radRoot j).1), (rootOperatorFamily .G2).rootSubgroup F γ) ≤
      Xr F (radRoot 2) := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, ha, hb, hγ⟩ := hγ
    rw [radRoot_sum_eq i j γ a b ha hb hγ]
  exact hle h

theorem radRoot_central (F : Type) [Field F] (i : Fin 5) :
    ∀ z ∈ Xr F (radRoot 2), ∀ y ∈ Xr F (radRoot i), z * y = y * z := by
  intro z hz y hy
  by_cases hi : i = 2
  · subst hi
    exact Xr_comm F _ hz hy
  · have h := commContained_pos F (radRoot 2) (radRoot i) (radRoot_height_pos 2)
      (radRoot_height_pos i) (radRoot_injective.ne (Ne.symm hi)) z hz y hy
    have hbot : (⨆ (γ : Root .G2) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
        γ.1 = a • (radRoot 2).1 + b • (radRoot i).1), (rootOperatorFamily .G2).rootSubgroup F γ) =
        ⊥ := iSup₂_eq_bot.2 fun γ ⟨a, b, ha, hb, hγ⟩ =>
      (radRoot_central_no_root i γ a b ha hb hγ).elim
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h

noncomputable def radG2 (F : Type) [Field F] : Subgroup (adjointGroup .G2 F) :=
  ⨆ i : Fin 5, Xr F (radRoot i)

theorem Xr_pow_card (F : Type) [Field F] (i : Fin 5) {x : adjointGroup .G2 F}
    (hx : x ∈ Xr F (radRoot i)) : x ^ Nat.card F = 1 := by
  obtain ⟨c, rfl⟩ := ((rootOperatorFamily .G2).mem_rootSubgroup).1 hx
  have h1 : (rootOperatorFamily .G2).eltElement (radRoot i) c =
      rootHom (radRoot i) (Multiplicative.ofAdd c) := rfl
  have hc : (Multiplicative.ofAdd c) ^ Nat.card F = 1 := by
    have := pow_card_eq_one' (G := Multiplicative F) (x := Multiplicative.ofAdd c)
    rwa [show Nat.card (Multiplicative F) = Nat.card F from Nat.card_congr Multiplicative.toAdd]
      at this
  rw [h1, ← map_pow, hc, map_one]

theorem radG2_pow (F : Type) [Field F] {p : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hF : Nat.card F = p) : ∀ g ∈ radG2 F, g ^ p = 1 := by
  have hS : ∀ i : Fin 5, ∀ x ∈ Xr F (radRoot i), x ^ p = 1 := fun i x hx => by
    rw [← hF]; exact Xr_pow_card F i hx
  have hZV : ∀ z ∈ Xr F (radRoot 2), ∀ g ∈ ⨆ i : Fin 5, Xr F (radRoot i), z * g = g * z :=
    fun z hz => commute_iSup _ z (fun i y hy => radRoot_central F i z hz y hy)
  have hgen : ∀ i j : Fin 5, ∀ x ∈ Xr F (radRoot i), ∀ y ∈ Xr F (radRoot j),
      x * y * x⁻¹ * y⁻¹ ∈ Xr F (radRoot 2) := by
    intro i j x hx y hy
    by_cases hij : i = j
    · subst hij
      rw [Xr_comm F _ hx hy]
      simp
    · exact radRoot_comm_mem F i j hij x hx y hy
  exact pow_eq_one_iSup (fun i : Fin 5 => Xr F (radRoot i)) (Xr F (radRoot 2)) hp hp3 hZV
    (commutator_mem_iSup _ _ hZV hgen) (fun z hz => hS 2 z hz) hS

noncomputable def radProd (F : Type) [Field F] (c : Fin 5 → Multiplicative F) :
    adjointGroup .G2 F :=
  rootHom (radRoot 4) (c 4) * rootHom (radRoot 3) (c 3) * rootHom (radRoot 2) (c 2) *
    rootHom (radRoot 1) (c 1) * rootHom (radRoot 0) (c 0)

theorem radProd_mem (F : Type) [Field F] (c : Fin 5 → Multiplicative F) :
    radProd F c ∈ radG2 F := by
  have hmem : ∀ (i : Fin 5) (x : Multiplicative F), rootHom (radRoot i) x ∈ radG2 F :=
    fun i x => Subgroup.mem_iSup_of_mem i
      ((rootOperatorFamily .G2).eltElement_mem_rootSubgroup (radRoot i) x.toAdd)
  exact mul_mem (mul_mem (mul_mem (mul_mem (hmem 4 _) (hmem 3 _)) (hmem 2 _)) (hmem 1 _))
    (hmem 0 _)

theorem radProd_injective (F : Type) [Field F] [Finite F] : Function.Injective (radProd F) := by
  have hy : ∀ c : Fin 5 → Multiplicative F,
      List.Forall₂ (fun g (β : Root .G2) => g ∈ (nativeRootSubgroups .G2 F).X β)
        [rootHom (radRoot 0) (c 0), rootHom (radRoot 1) (c 1), rootHom (radRoot 2) (c 2),
          rootHom (radRoot 3) (c 3), rootHom (radRoot 4) (c 4), 1] (wordRoots g2LongWord) := by
    intro c
    rw [wordRoots_g2LongWord]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons (one_mem _) .nil)))))
    all_goals exact (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _
  intro c c' h
  have h2 := eq_of_reverse_prod_eq (K := F) g2LongWord isReduced_G2_alternating _ _ (hy c) (hy c')
    (by simpa [radProd, mul_assoc] using h)
  simp only [List.cons.injEq, and_true] at h2
  obtain ⟨h0, h1, h2, h3, h4⟩ := h2
  funext i
  fin_cases i
  · exact rootHom_injective _ h0
  · exact rootHom_injective _ h1
  · exact rootHom_injective _ h2
  · exact rootHom_injective _ h3
  · exact rootHom_injective _ h4

theorem radG2_card (F : Type) [Field F] [Finite F] [Finite (adjointGroup .G2 F)] :
    Nat.card F ^ 5 ≤ Nat.card (radG2 F) := by
  have hinj : Function.Injective
      (fun c : Fin 5 → Multiplicative F => (⟨radProd F c, radProd_mem F c⟩ : radG2 F)) :=
    fun c c' h => radProd_injective F (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
    show Nat.card (Multiplicative F) = Nat.card F from Nat.card_congr Multiplicative.toAdd] at this
  exact this

theorem sylowDichotomyAt_adjointG2 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hF : Nat.card F = p) [Finite (adjointGroup .G2 F)] :
    SylowDichotomyAt (adjointGroup .G2 F) p := by
  have hpow := radG2_pow F hp (by omega) hF
  refine SylowDichotomyAt.of_exponent (U := radG2 F) ?_ hpow ?_
  · intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hpow g g.2)⟩
  · have := radG2_card F
    rw [hF] at this
    exact this

end G2Radical

theorem sdG2p_holds : SDG2p := by
  intro K _ _ p hp h5 hmodel
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.chevalleyExceptionalModel (by decide)
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e2 : AdjointQuotient .G2 F ≃* ↥(adjointGroup .G2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e3 : K ≃* ↥(adjointGroup .G2 F) := e.trans e2
  haveI : Finite ↥(adjointGroup .G2 F) := Finite.of_equiv K e3.toEquiv
  exact SylowDichotomyAt.of_mulEquiv hp e3
    (G2Radical.sylowDichotomyAt_adjointG2 F hp h5 (by simpa using hF))

end G2

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
