module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

section Abstract

theorem rkY_false_of_cover {Y : Type} [Group Y] (hRk : RkY Y) {S Q : Type} [Group S] [Group Q]
    (ρ : S →* Y) (q : Y →* Q) (π : S →* Q) (hcomp : ∀ g, q (ρ g) = π g)
    (hZ : ∀ y ∈ Subgroup.center Y, q y = 1) {E₀ U₀ : Subgroup S} (hE : IsElemAbelian 3 E₀)
    (hcard : 27 < Nat.card E₀) (hEπ : ∀ g ∈ E₀, π g = 1 → g = 1) (hU2 : IsPGroup 2 U₀)
    (hU : ∃ u ∈ U₀, π u ≠ 1) (hnorm : ∀ e ∈ E₀, ∀ u ∈ U₀, e * u * e⁻¹ ∈ U₀) : False := by
  have hρ1 : ∀ g ∈ E₀, ρ g = 1 → g = 1 := fun g hg h => hEπ g hg (by rw [← hcomp, h, map_one])
  have hcardE : Nat.card (E₀.map ρ) = Nat.card E₀ := by
    refine (Nat.card_congr
      (Equiv.ofBijective (fun x : E₀ => (⟨ρ x, x, x.2, rfl⟩ : E₀.map ρ)) ⟨?_, ?_⟩)).symm
    · intro x y hxy
      have h : ρ (x : S) = ρ (y : S) := congrArg Subtype.val hxy
      have hxy' : (x : S)⁻¹ * y = 1 :=
        hρ1 _ (E₀.mul_mem (E₀.inv_mem x.2) y.2) (by rw [map_mul, map_inv, h, inv_mul_cancel])
      exact Subtype.ext (inv_mul_eq_one.1 hxy')
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hEZ : E₀.map ρ ⊓ Subgroup.center Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨⟨x, hx, rfl⟩, hyZ⟩
    have h1 : π x = 1 := by rw [← hcomp]; exact hZ _ hyZ
    rw [hEπ x hx h1, map_one]
  have hUne : U₀.map ρ ≠ ⊥ := by
    obtain ⟨u, hu, hπu⟩ := hU
    intro hbot
    have hmem : ρ u ∈ U₀.map ρ := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hπu (by rw [← hcomp, hmem, map_one])
  have hnorm' : E₀.map ρ ≤ Subgroup.normalizer ((U₀.map ρ : Subgroup Y) : Set Y) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, hnorm e he u hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u, hu, hu'⟩
      refine ⟨e⁻¹ * u * e, by simpa using hnorm e⁻¹ (E₀.inv_mem he) u hu, ?_⟩
      rw [map_mul, map_mul, map_inv, hu']
      group
  obtain ⟨-, h27⟩ := hRk (U₀.map ρ) hUne (hU2.map ρ) (E₀.map ρ) hnorm' (hE.map ρ)
  have := h27 hEZ
  omega

end Abstract

section Torus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def tEntry (a b c d : Kˣ) (k : ℕ) : Kˣ :=
  if k = 0 then a else if k = 1 then b else if k = 2 then c else if k = 3 then d
    else if k = 4 then (a * b * c * d)⁻¹ else 1

theorem tEntry_mul (a b c d a' b' c' d' : Kˣ) (k : ℕ) :
    tEntry (a * a') (b * b') (c * c') (d * d') k = tEntry a b c d k * tEntry a' b' c' d' k := by
  unfold tEntry
  split_ifs <;> first | rfl | (rw [← mul_inv]; congr 1; ac_rfl) | simp

theorem tEntry_one (k : ℕ) : tEntry (1 : Kˣ) 1 1 1 k = 1 := by
  unfold tEntry
  split_ifs <;> simp

theorem prod_tEntry (hn : 5 ≤ n) (a b c d : Kˣ) : ∏ i : Fin n, tEntry a b c d i = 1 := by
  rw [show (∏ i : Fin n, tEntry a b c d i) = ∏ k ∈ Finset.range n, tEntry a b c d k from
    Fin.prod_univ_eq_prod_range (fun k => tEntry a b c d k) n, ← Finset.prod_subset (Finset.range_subset_range.2 hn) ?_]
  · simp [Finset.prod_range_succ, tEntry]
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [tEntry, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega,
      show k ≠ 3 by omega, show k ≠ 4 by omega]

@[expose] noncomputable def tDiag (hn : 5 ≤ n) (a b c d : Kˣ) : SpecialLinearGroup (Fin n) K :=
  ⟨diagonal fun i : Fin n => (tEntry a b c d i : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_tEntry hn, Units.val_one]⟩

theorem coe_tDiag (hn : 5 ≤ n) (a b c d : Kˣ) :
    (tDiag hn a b c d : Matrix (Fin n) (Fin n) K) = diagonal fun i : Fin n => (tEntry a b c d i : K) :=
  rfl

theorem tDiag_mul (hn : 5 ≤ n) (a b c d a' b' c' d' : Kˣ) :
    tDiag hn (a * a') (b * b') (c * c') (d * d') = tDiag hn a b c d * tDiag hn a' b' c' d' := by
  have h : (tDiag hn (a * a') (b * b') (c * c') (d * d') : Matrix (Fin n) (Fin n) K) =
      (tDiag hn a b c d : Matrix (Fin n) (Fin n) K) * (tDiag hn a' b' c' d' : Matrix (Fin n) (Fin n) K) := by
    simp only [coe_tDiag, diagonal_mul_diagonal, tEntry_mul, Units.val_mul]
  exact Subtype.ext (h.trans (Matrix.SpecialLinearGroup.coe_mul (tDiag hn a b c d) (tDiag hn a' b' c' d')).symm)

theorem tDiag_one (hn : 5 ≤ n) : tDiag hn (1 : Kˣ) 1 1 1 = 1 := by
  apply Subtype.ext
  simp only [coe_tDiag, tEntry_one, Units.val_one, SpecialLinearGroup.coe_one]
  exact diagonal_one

theorem tDiag_comm (hn : 5 ≤ n) (a b c d a' b' c' d' : Kˣ) :
    tDiag hn a b c d * tDiag hn a' b' c' d' = tDiag hn a' b' c' d' * tDiag hn a b c d := by
  rw [← tDiag_mul, ← tDiag_mul, mul_comm a, mul_comm b, mul_comm c, mul_comm d]

theorem tDiag_apply (hn : 5 ≤ n) (a b c d : Kˣ) (i : Fin n) :
    (tDiag hn a b c d : Matrix (Fin n) (Fin n) K) i i = (tEntry a b c d i : K) := by
  rw [coe_tDiag, diagonal_apply_eq]

theorem tDiag_scalar (hn : 6 ≤ n) {a b c d : Kˣ}
    (h : tDiag (by omega) a b c d ∈ scalars n K) : a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  obtain ⟨z, -, hz⟩ := mem_scalars.1 h
  have hc : ∀ i : Fin n, (tEntry a b c d i : K) = z := by
    intro i
    have := tDiag_apply (by omega) a b c d i
    rw [hz, scalar_apply, diagonal_apply_eq] at this
    exact this.symm
  have h5 : (tEntry a b c d 5 : K) = z := hc ⟨5, by omega⟩
  have h5' : (tEntry a b c d 5 : Kˣ) = 1 := by simp [tEntry]
  have hz1 : (z : K) = 1 := by rw [← h5, h5', Units.val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hc ⟨0, by omega⟩
    simp only [tEntry, if_true] at this
    exact Units.ext (by rw [this, hz1, Units.val_one])
  · have := hc ⟨1, by omega⟩
    simp only [tEntry, if_true, one_ne_zero, if_false] at this
    exact Units.ext (by rw [this, hz1, Units.val_one])
  · have := hc ⟨2, by omega⟩
    simp [tEntry] at this
    exact Units.ext (by rw [this, hz1, Units.val_one])
  · have := hc ⟨3, by omega⟩
    simp [tEntry] at this
    exact Units.ext (by rw [this, hz1, Units.val_one])

@[expose] noncomputable def torusHom (hn : 5 ≤ n) :
    (rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K) →*
      SpecialLinearGroup (Fin n) K where
  toFun w := tDiag hn (w.1 : Kˣ) (w.2.1 : Kˣ) (w.2.2.1 : Kˣ) (w.2.2.2 : Kˣ)
  map_one' := tDiag_one hn
  map_mul' w w' := tDiag_mul hn _ _ _ _ _ _ _ _

theorem torusHom_scalar (hn : 6 ≤ n)
    {w : rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K × rootsOfUnity 3 K}
    (h : torusHom (by omega : 5 ≤ n) w ∈ scalars n K) : w = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := tDiag_scalar hn h
  exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2)
    (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))

theorem torusHom_injective (hn : 6 ≤ n) : Function.Injective (torusHom (K := K) (by omega : 5 ≤ n)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact torusHom_scalar hn (by rw [hw]; exact one_mem _)

theorem three_le_card_roots [Finite K] {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    3 ≤ Nat.card (rootsOfUnity 3 K) := by
  have hmem : ζ ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have h1 : orderOf (⟨ζ, hmem⟩ : rootsOfUnity 3 K) = 3 := by rw [Subgroup.orderOf_mk, hζ]
  have h2 := orderOf_dvd_natCard (⟨ζ, hmem⟩ : rootsOfUnity 3 K)
  rw [h1] at h2
  exact Nat.le_of_dvd Nat.card_pos h2

theorem torus_card [Finite K] (hn : 6 ≤ n) {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    27 < Nat.card (torusHom (K := K) (by omega : 5 ≤ n)).range := by
  have hinj := torusHom_injective (K := K) hn
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  have h3 := three_le_card_roots (K := K) hζ
  have : 3 * (3 * (3 * 3)) ≤ Nat.card (rootsOfUnity 3 K) *
      (Nat.card (rootsOfUnity 3 K) * (Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K))) :=
    Nat.mul_le_mul h3 (Nat.mul_le_mul h3 (Nat.mul_le_mul h3 h3))
  omega

theorem pow_three_eq_one_roots (u : rootsOfUnity 3 K) : u ^ 3 = 1 :=
  Subtype.ext (by simpa using (mem_rootsOfUnity 3 (u : Kˣ)).1 u.2)

theorem torus_elemAbelian (hn : 5 ≤ n) : IsElemAbelian 3 (torusHom (K := K) hn).range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    show (x : SpecialLinearGroup (Fin n) K) * y = y * x
    rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
  · obtain ⟨u, rfl⟩ := hx
    have : u ^ 3 = 1 := by
      refine Prod.ext (pow_three_eq_one_roots _) (Prod.ext (pow_three_eq_one_roots _)
        (Prod.ext (pow_three_eq_one_roots _) (pow_three_eq_one_roots _)))
    rw [← map_pow, this, map_one]

@[expose] noncomputable def negDiag (hn : 5 ≤ n) : SpecialLinearGroup (Fin n) K :=
  tDiag hn (-1) (-1) 1 1

theorem negDiag_sq (hn : 5 ≤ n) : negDiag (K := K) hn ^ 2 = 1 := by
  rw [sq, negDiag, ← tDiag_mul]
  have h : ((-1 : Kˣ) * -1) = 1 := by simp
  rw [h, mul_one, tDiag_one]

theorem negDiag_not_scalar (hn : 6 ≤ n) (h2 : ringChar K ≠ 2) :
    negDiag (K := K) (by omega : 5 ≤ n) ∉ scalars n K := by
  intro h
  obtain ⟨a, -, -, -⟩ := tDiag_scalar hn h
  exact Ring.neg_one_ne_one_of_char_ne_two h2 (by simpa using congrArg Units.val a)

end Torus

section Root

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def rootElt (hn : 2 ≤ n) (t : K) : SpecialLinearGroup (Fin n) K :=
  ⟨transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ t,
    det_transvection_of_ne _ _ (by simp [Fin.ext_iff]) t⟩

theorem coe_rootElt (hn : 2 ≤ n) (t : K) :
    (rootElt hn t : Matrix (Fin n) (Fin n) K) =
      transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ t := rfl

theorem rootElt_mul (hn : 2 ≤ n) (s t : K) :
    rootElt hn s * rootElt hn t = rootElt hn (s + t) := by
  have h : (rootElt hn s : Matrix (Fin n) (Fin n) K) * (rootElt hn t : Matrix (Fin n) (Fin n) K) =
      (rootElt hn (s + t) : Matrix (Fin n) (Fin n) K) :=
    transvection_mul_transvection_same _ _ (by simp [Fin.ext_iff]) s t
  exact Subtype.ext
    ((Matrix.SpecialLinearGroup.coe_mul (rootElt hn s) (rootElt hn t)).symm.trans h)

theorem rootElt_zero (hn : 2 ≤ n) : rootElt hn (0 : K) = 1 := by
  apply Subtype.ext
  show (rootElt hn (0 : K) : Matrix (Fin n) (Fin n) K) = 1
  rw [coe_rootElt, transvection_zero]

@[expose] noncomputable def rootHom (hn : 2 ≤ n) : Multiplicative K →* SpecialLinearGroup (Fin n) K where
  toFun t := rootElt hn (Multiplicative.toAdd t)
  map_one' := rootElt_zero hn
  map_mul' s t := (rootElt_mul hn _ _).symm

theorem rootHom_range_pGroup [CharP K 2] (hn : 2 ≤ n) : IsPGroup 2 (rootHom (K := K) hn).range := by
  rintro ⟨_, t, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  show (rootHom hn t) ^ 2 ^ 1 = 1
  rw [pow_one, sq, ← map_mul]
  show rootElt hn (Multiplicative.toAdd (t * t)) = 1
  rw [toAdd_mul, CharTwo.add_self_eq_zero, rootElt_zero]

theorem rootElt_not_scalar (hn : 2 ≤ n) : rootElt hn (1 : K) ∉ scalars n K := by
  intro h
  obtain ⟨z, -, hz⟩ := mem_scalars.1 h
  have h1 := congrFun (congrFun hz ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [coe_rootElt] at h1
  simp [transvection, scalar_apply, diagonal_apply_ne, Fin.ext_iff] at h1

theorem diagonal_mul_transvection {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → K)
    (hd : ∀ k, d k ≠ 0) (i j : ι) (t : K) :
    diagonal d * transvection i j t = transvection i j (d i * t * (d j)⁻¹) * diagonal d := by
  ext x y
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, diagonal_mul, mul_diagonal, Matrix.add_apply,
    one_apply, single_apply, Matrix.one_mul, Matrix.mul_one]
  by_cases h : i = x ∧ j = y
  · obtain ⟨rfl, rfl⟩ := h
    by_cases hij : i = j
    · subst hij
      simp
      field_simp [hd i]
    · simp [hij]
      field_simp [hd j]
  · by_cases hxy : x = y
    · subst hxy
      simp [h]
    · simp [h, hxy]

theorem tDiag_mul_rootElt (hn : 6 ≤ n) (a b c d : Kˣ) (t : K) :
    tDiag (by omega : 5 ≤ n) a b c d * rootElt (by omega : 2 ≤ n) t =
      rootElt (by omega : 2 ≤ n) ((a : K) * t * (b : K)⁻¹) * tDiag (by omega : 5 ≤ n) a b c d := by
  have h : (tDiag (by omega : 5 ≤ n) a b c d : Matrix (Fin n) (Fin n) K) *
      (rootElt (by omega : 2 ≤ n) t : Matrix (Fin n) (Fin n) K) =
      (rootElt (by omega : 2 ≤ n) ((a : K) * t * (b : K)⁻¹) : Matrix (Fin n) (Fin n) K) *
        (tDiag (by omega : 5 ≤ n) a b c d : Matrix (Fin n) (Fin n) K) := by
    rw [coe_tDiag, coe_rootElt, coe_rootElt]
    have := diagonal_mul_transvection (fun i : Fin n => (tEntry a b c d i : K))
      (fun k => Units.ne_zero _) ⟨0, by omega⟩ ⟨1, by omega⟩ t
    simpa [tEntry] using this
  exact Subtype.ext ((Matrix.SpecialLinearGroup.coe_mul _ _).trans
    (h.trans (Matrix.SpecialLinearGroup.coe_mul _ _).symm))

end Root

theorem rkY_false_psl {Y : Type} [Group Y] (hRk : RkY Y) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 6 ≤ n) {ζ : Kˣ} (hζ : orderOf ζ = 3) (ρ : SpecialLinearGroup (Fin n) K →* Y)
    (q : Y →* projectiveSL n K) (hcomp : ∀ g, q (ρ g) = proj n K g)
    (hZ : ∀ y ∈ Subgroup.center Y, q y = 1) : False := by
  have hn5 : 5 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hEπ : ∀ g ∈ (torusHom (K := K) hn5).range, proj n K g = 1 → g = 1 := by
    rintro _ ⟨w, rfl⟩ h
    rw [torusHom_scalar hn (proj_eq_one_iff.1 h), map_one]
  have hcard := torus_card (K := K) hn hζ
  have hE := torus_elemAbelian (K := K) hn5
  by_cases h2 : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h2
    refine rkY_false_of_cover hRk ρ q (proj n K) hcomp hZ hE hcard hEπ
      (rootHom_range_pGroup hn2) ?_ ?_
    · exact ⟨rootElt hn2 1, ⟨Multiplicative.ofAdd 1, rfl⟩,
        fun h => rootElt_not_scalar hn2 (proj_eq_one_iff.1 h)⟩
    · rintro _ ⟨w, rfl⟩ _ ⟨s, rfl⟩
      refine ⟨Multiplicative.ofAdd (((w.1 : Kˣ) : K) * Multiplicative.toAdd s * ((w.2.1 : Kˣ) : K)⁻¹),
        ?_⟩
      show rootElt hn2 _ = torusHom hn5 w * rootElt hn2 (Multiplicative.toAdd s) * (torusHom hn5 w)⁻¹
      exact eq_mul_inv_of_mul_eq (tDiag_mul_rootElt hn _ _ _ _ _).symm
  · refine rkY_false_of_cover hRk ρ q (proj n K) hcomp hZ hE hcard hEπ
      (U₀ := Subgroup.zpowers (negDiag (K := K) hn5))
      (isElemAbelian_zpowers (negDiag_sq hn5)).isPGroup ?_ ?_
    · exact ⟨negDiag hn5, Subgroup.mem_zpowers _,
        fun h => negDiag_not_scalar hn h2 (proj_eq_one_iff.1 h)⟩
    · rintro _ ⟨w, rfl⟩ u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hc : Commute (torusHom hn5 w) (negDiag (K := K) hn5) :=
        tDiag_comm hn5 _ _ _ _ _ _ _ _
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end CFSG.HardMathSupport.Dickson.Sec6.I1431
