module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Config
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBigCell

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open scoped commutatorElement


section D4F2Defs

@[expose] noncomputable def d4F2_QGens (K : Type) [Field K] : Set ↥(adjointGroup Tag.D4 K) :=
  {g | ∃ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ ∧ 0 < d4F2Lvl γ ∧
    ∃ c : K, g = xPar (rootOperatorFamily Tag.D4) γ c}

@[expose] noncomputable def d4F2_Qgrp (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.D4 K) :=
  Subgroup.closure (d4F2_QGens K)

@[expose] noncomputable def d4F2_ULGens (K : Type) [Field K] : Set ↥(adjointGroup Tag.D4 K) :=
  {g | ∃ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ ∧ d4F2Lvl γ = 0 ∧ 0 < height γ ∧
    ∃ c : K, g = xPar (rootOperatorFamily Tag.D4) γ c}

@[expose] noncomputable def d4F2_ULgrp (K : Type) [Field K] : Subgroup ↥(adjointGroup Tag.D4 K) :=
  Subgroup.closure (d4F2_ULGens K)

@[expose] noncomputable def d4F2_StabSL2 (K : Type) [Field K] :
    Subgroup ↥(adjointGroup Tag.D4 K) where
  carrier := {m | ∃ χ : Kˣ,
    (∀ c : K, m * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * m⁻¹ =
      xPar (rootOperatorFamily Tag.D4) d4F2Theta ((χ : K) * c)) ∧
    (∀ c : K, m * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c * m⁻¹ =
      xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) (((χ⁻¹ : Kˣ) : K) * c))}
  one_mem' := ⟨1, fun c => by simp, fun c => by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨χ₁, h₁, h₁'⟩ ⟨χ₂, h₂, h₂'⟩
    refine ⟨χ₁ * χ₂, fun c => ?_, fun c => ?_⟩
    · have e : m₁ * m₂ * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * (m₁ * m₂)⁻¹ =
          m₁ * (m₂ * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * m₂⁻¹) * m₁⁻¹ := by group
      rw [e, h₂ c, h₁ ((χ₂ : K) * c), Units.val_mul, mul_assoc]
    · have e : m₁ * m₂ * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c * (m₁ * m₂)⁻¹ =
          m₁ * (m₂ * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c * m₂⁻¹) * m₁⁻¹ := by group
      rw [e, h₂' c, h₁' (((χ₂⁻¹ : Kˣ) : K) * c)]
      congr 1
      rw [mul_inv_rev, Units.val_mul]
      ring
  inv_mem' := by
    rintro m ⟨χ, h, h'⟩
    refine ⟨χ⁻¹, fun c => ?_, fun c => ?_⟩
    · have := h (((χ⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, Units.mul_inv, one_mul] at this
      rw [eq_comm, ← mul_inv_eq_iff_eq_mul, ← inv_mul_eq_iff_eq_mul] at this
      simpa [mul_assoc] using this
    · have := h' ((χ : K) * c)
      simp only [← mul_assoc, Units.inv_mul, one_mul] at this
      rw [eq_comm, ← mul_inv_eq_iff_eq_mul, ← inv_mul_eq_iff_eq_mul] at this
      simpa [mul_assoc] using this

end D4F2Defs

section D4F2Q

theorem d4F2_lvl_add (u v : Fin Tag.D4.rank → ℤ) : d4F2Lvl (u + v) = d4F2Lvl u + d4F2Lvl v := rfl

theorem d4F2_lvl_nsmul (n : ℕ) (u : Fin Tag.D4.rank → ℤ) : d4F2Lvl (n • u) = n * d4F2Lvl u := by
  simp [d4F2Lvl]

theorem d4F2_xPar_mem_Qgrp {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h : 0 < d4F2Lvl γ) (c : K) : xPar (rootOperatorFamily Tag.D4) γ c ∈ d4F2_Qgrp K :=
  Subgroup.subset_closure ⟨γ, hγ, h, c, rfl⟩

theorem d4F2_xPar_mem_ULgrp {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h0 : d4F2Lvl γ = 0) (hh : 0 < height γ) (c : K) :
    xPar (rootOperatorFamily Tag.D4) γ c ∈ d4F2_ULgrp K :=
  Subgroup.subset_closure ⟨γ, hγ, h0, hh, c, rfl⟩

theorem d4F2_commute_theta {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hpos : 0 < height γ) (a c : K) :
    Commute (xPar (rootOperatorFamily Tag.D4) γ a)
      (xPar (rootOperatorFamily Tag.D4) d4F2Theta c) :=
  (IsMaxHeightRoot.commute_xPar_of_cone d4F2_theta_isMax hγ hpos c a).symm

theorem d4F2_commute_Q_theta {K : Type} [Field K] {q : ↥(adjointGroup Tag.D4 K)}
    (hq : q ∈ d4F2_Qgrp K) (c : K) :
    Commute q (xPar (rootOperatorFamily Tag.D4) d4F2Theta c) := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, a, rfl⟩ := hx
    exact d4F2_commute_theta hγ (d4F2_height_pos_of_lvl_pos hγ hl) a c
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem d4F2_comm_mem {τ : Tag} {K : Type} [Field K] {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hγp : 0 < height γ) (hδp : 0 < height δ) (hne : γ ≠ δ)
    {H : Subgroup ↥(adjointGroup τ K)}
    (hH : ∀ (γ' : Root τ) (m n : ℕ), 1 ≤ m → 1 ≤ n → γ'.1 = m • γ + n • δ →
      (rootOperatorFamily τ).rootSubgroup K γ' ≤ H) (a b : K) :
    xPar (rootOperatorFamily τ) γ a * xPar (rootOperatorFamily τ) δ b *
      (xPar (rootOperatorFamily τ) γ a)⁻¹ * (xPar (rootOperatorFamily τ) δ b)⁻¹ ∈ H := by
  have hne' : (⟨γ, hγ⟩ : Root τ) ≠ ⟨δ, hδ⟩ := fun h => hne (congrArg Subtype.val h)
  have hc := commContained_pos K ⟨γ, hγ⟩ ⟨δ, hδ⟩ hγp hδp hne'
  have hle : (⨆ (γ' : Root τ) (_ : ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ γ'.1 = m • γ + n • δ),
      (rootOperatorFamily τ).rootSubgroup K γ') ≤ H :=
    iSup₂_le fun γ' ⟨m, n, hm, hn, he⟩ => hH γ' m n hm hn he
  rw [xPar_of_isRoot hγ, xPar_of_isRoot hδ]
  exact hle (hc _ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ a) _
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ b))

theorem d4F2_rootSubgroup_le_theta {K : Type} [Field K] (γ' : Root Tag.D4)
    (h : 2 ≤ d4F2Lvl γ'.1) :
    (rootOperatorFamily Tag.D4).rootSubgroup K γ' ≤
      rootGroup (rootOperatorFamily Tag.D4) K d4F2Theta := by
  have hθ : γ'.1 = d4F2Theta :=
    d4F2_eq_theta_of_lvl γ'.2 (le_antisymm (d4F2_lvl_bound γ'.2).2 h)
  have hγ' : γ' = ⟨d4F2Theta, d4F2_isRoot_theta⟩ := Subtype.ext hθ
  rw [hγ', rootGroup_of_isRoot d4F2_isRoot_theta]

theorem d4F2_rootSubgroup_le_Qgrp {K : Type} [Field K] (γ' : Root Tag.D4)
    (h : 0 < d4F2Lvl γ'.1) : (rootOperatorFamily Tag.D4).rootSubgroup K γ' ≤ d4F2_Qgrp K := by
  obtain ⟨γ', hγ'⟩ := γ'
  intro x hx
  obtain ⟨c, rfl⟩ := (rootOperatorFamily Tag.D4).mem_rootSubgroup.1 hx
  rw [← xPar_of_isRoot hγ']
  exact d4F2_xPar_mem_Qgrp hγ' h c

theorem d4F2_conj_gen_level_one {K : Type} [Field K] {γ δ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (hl : 0 < d4F2Lvl γ) (hδ : IsRoot Tag.D4 δ) (hδl : d4F2Lvl δ = 1)
    (a t : K) :
    ∃ c : K, xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) δ t *
        (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ =
      xPar (rootOperatorFamily Tag.D4) δ t * xPar (rootOperatorFamily Tag.D4) d4F2Theta c := by
  have hδp : 0 < height δ := d4F2_height_pos_of_lvl_pos hδ (by omega)
  by_cases hγδ : γ = δ
  · subst hγδ
    refine ⟨0, ?_⟩
    rw [xPar_zero, mul_one, ← xPar_add, add_comm, xPar_add, mul_inv_cancel_right]
  · have hmem := d4F2_comm_mem hγ hδ (d4F2_height_pos_of_lvl_pos hγ hl) hδp hγδ
      (H := rootGroup (rootOperatorFamily Tag.D4) K d4F2Theta) (fun γ' m n hm hn he => by
        apply d4F2_rootSubgroup_le_theta
        rw [he, d4F2_lvl_add, d4F2_lvl_nsmul, d4F2_lvl_nsmul, hδl]
        have h1 : 0 < (m : ℤ) * d4F2Lvl γ := mul_pos (by omega) hl
        omega) a t
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff d4F2_isRoot_theta _).1 hmem
    refine ⟨c, ?_⟩
    have e : xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) δ t *
        (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ =
          (xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) δ t *
            (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ * (xPar (rootOperatorFamily Tag.D4) δ t)⁻¹) *
          xPar (rootOperatorFamily Tag.D4) δ t := by group
    rw [e, ← hc]
    exact (d4F2_commute_theta hδ hδp t c).symm.eq

theorem d4F2_Q_conj_delta_any {K : Type} [Field K] {q : ↥(adjointGroup Tag.D4 K)}
    (hq : q ∈ d4F2_Qgrp K) {δ : Fin Tag.D4.rank → ℤ} (hδ : IsRoot Tag.D4 δ)
    (hδl : d4F2Lvl δ = 1) (t : K) :
    ∃ c : K, q * xPar (rootOperatorFamily Tag.D4) δ t * q⁻¹ =
      xPar (rootOperatorFamily Tag.D4) δ t * xPar (rootOperatorFamily Tag.D4) d4F2Theta c := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl, a, rfl⟩ := hx
    exact d4F2_conj_gen_level_one hγ hl hδ hδl a t
  | one => exact ⟨0, by rw [xPar_zero]; group⟩
  | mul x y hx _ ihx ihy =>
    obtain ⟨c, hc⟩ := ihx
    obtain ⟨c', hc'⟩ := ihy
    refine ⟨c + c', ?_⟩
    have e : x * y * xPar (rootOperatorFamily Tag.D4) δ t * (x * y)⁻¹ =
        x * (y * xPar (rootOperatorFamily Tag.D4) δ t * y⁻¹) * x⁻¹ := by group
    rw [e, hc']
    have e2 : x * (xPar (rootOperatorFamily Tag.D4) δ t *
        xPar (rootOperatorFamily Tag.D4) d4F2Theta c') * x⁻¹ =
          (x * xPar (rootOperatorFamily Tag.D4) δ t * x⁻¹) *
            (x * xPar (rootOperatorFamily Tag.D4) d4F2Theta c' * x⁻¹) := by group
    rw [e2, hc, (d4F2_commute_Q_theta hx c').eq, mul_inv_cancel_right, mul_assoc, ← xPar_add]
  | inv x hx ihx =>
    obtain ⟨c, hc⟩ := ihx
    refine ⟨-c, ?_⟩
    have hcomm : x⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * x =
        xPar (rootOperatorFamily Tag.D4) d4F2Theta c := by
      have := ((d4F2_commute_Q_theta hx c).inv_left).eq
      rw [this, mul_assoc, inv_mul_cancel, mul_one]
    have h2 : xPar (rootOperatorFamily Tag.D4) δ t =
        (x⁻¹ * xPar (rootOperatorFamily Tag.D4) δ t * x) *
          xPar (rootOperatorFamily Tag.D4) d4F2Theta c := by
      calc xPar (rootOperatorFamily Tag.D4) δ t
          = x⁻¹ * (x * xPar (rootOperatorFamily Tag.D4) δ t * x⁻¹) * x := by group
        _ = x⁻¹ * (xPar (rootOperatorFamily Tag.D4) δ t *
            xPar (rootOperatorFamily Tag.D4) d4F2Theta c) * x := by rw [hc]
        _ = (x⁻¹ * xPar (rootOperatorFamily Tag.D4) δ t * x) *
            (x⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Theta c * x) := by group
        _ = _ := by rw [hcomm]
    have h3 := eq_mul_inv_of_mul_eq h2.symm
    rw [xPar_neg] at h3
    rw [inv_inv, h3]

theorem d4F2_Q_conj_delta {K : Type} [Field K] {q : ↥(adjointGroup Tag.D4 K)}
    (hq : q ∈ d4F2_Qgrp K) {δ : Fin Tag.D4.rank → ℤ} (hδ : IsRoot Tag.D4 δ)
    (hδl : d4F2Lvl δ = 1) :
    ∃ c : K, q * xPar (rootOperatorFamily Tag.D4) δ 1 * q⁻¹ =
      xPar (rootOperatorFamily Tag.D4) δ 1 * xPar (rootOperatorFamily Tag.D4) d4F2Theta c :=
  d4F2_Q_conj_delta_any hq hδ hδl 1

end D4F2Q

section D4F2Levi

theorem d4F2_lvl_zero_cases {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h0 : d4F2Lvl γ = 0) (hh : 0 < height γ) :
    γ = (Tag.rootCertificate Tag.D4).root 0 ∨ γ = (Tag.rootCertificate Tag.D4).root 1 ∨
      γ = (Tag.rootCertificate Tag.D4).root 3 := by
  have key : ∀ γ ∈ rootFinset Tag.D4, d4F2Lvl γ = 0 → 0 < height γ →
      γ = (Tag.rootCertificate Tag.D4).root 0 ∨ γ = (Tag.rootCertificate Tag.D4).root 1 ∨
        γ = (Tag.rootCertificate Tag.D4).root 3 := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h0 hh

theorem d4F2_commute_neg_theta {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (h0 : d4F2Lvl γ = 0) (hh : 0 < height γ) (a c : K) :
    Commute (xPar (rootOperatorFamily Tag.D4) γ a)
      (xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c) := by
  have h23 : (Tag.rootCertificate Tag.D4).root 23 = -d4F2Theta := by decide
  rw [← h23, ← commutatorElement_eq_one_iff_commute]
  rcases d4F2_lvl_zero_cases hγ h0 hh with rfl | rfl | rfl
  · have hc : RootOps.repCheck Tag.D4 0 23 [] = true := by decide +kernel
    have h := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := Tag.D4) (K := K) hc a c
    rw [List.map_nil, List.prod_nil] at h
    exact h
  · have hc : RootOps.repCheck Tag.D4 1 23 [] = true := by decide +kernel
    have h := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := Tag.D4) (K := K) hc a c
    rw [List.map_nil, List.prod_nil] at h
    exact h
  · have hc : RootOps.repCheck Tag.D4 3 23 [] = true := by decide +kernel
    have h := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := Tag.D4) (K := K) hc a c
    rw [List.map_nil, List.prod_nil] at h
    exact h

theorem d4F2_commute_UL_pm_theta {K : Type} [Field K] {l : ↥(adjointGroup Tag.D4 K)}
    (hl : l ∈ d4F2_ULgrp K) (c : K) :
    Commute l (xPar (rootOperatorFamily Tag.D4) d4F2Theta c) ∧
      Commute l (xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) c) := by
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hl0, hh, a, rfl⟩ := hx
    exact ⟨d4F2_commute_theta hγ hh a c, d4F2_commute_neg_theta hγ hl0 hh a c⟩
  | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
  | mul x y _ _ hx hy => exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
  | inv x _ hx => exact ⟨hx.1.inv_left, hx.2.inv_left⟩

theorem d4F2_ULgrp_le_StabSL2 {K : Type} [Field K] : d4F2_ULgrp K ≤ d4F2_StabSL2 K := fun l hl => by
  refine ⟨1, fun c => ?_, fun c => ?_⟩
  · rw [((d4F2_commute_UL_pm_theta hl c).1).eq, mul_inv_cancel_right]; simp
  · rw [((d4F2_commute_UL_pm_theta hl c).2).eq, mul_inv_cancel_right]; simp

theorem d4F2_conj_QGen_of_UL_gen {K : Type} [Field K] {γ β : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (hγ0 : d4F2Lvl γ = 0) (hh : 0 < height γ) (hβ : IsRoot Tag.D4 β)
    (hβl : 0 < d4F2Lvl β) (a c : K) :
    xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) β c *
      (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ ∈ d4F2_Qgrp K := by
  have hne : γ ≠ β := fun h => by rw [h] at hγ0; omega
  have hmem := d4F2_comm_mem hγ hβ hh (d4F2_height_pos_of_lvl_pos hβ hβl) hne (H := d4F2_Qgrp K)
    (fun γ' m n hm hn he => by
      apply d4F2_rootSubgroup_le_Qgrp
      rw [he, d4F2_lvl_add, d4F2_lvl_nsmul, d4F2_lvl_nsmul, hγ0]
      have h1 : 0 < (n : ℤ) * d4F2Lvl β := mul_pos (by omega) hβl
      omega) a c
  have e : xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) β c *
      (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ =
        (xPar (rootOperatorFamily Tag.D4) γ a * xPar (rootOperatorFamily Tag.D4) β c *
          (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ * (xPar (rootOperatorFamily Tag.D4) β c)⁻¹) *
        xPar (rootOperatorFamily Tag.D4) β c := by group
  rw [e]
  exact Subgroup.mul_mem _ hmem (d4F2_xPar_mem_Qgrp hβ hβl c)

theorem d4F2_conj_Q_of_UL_gen {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (hγ0 : d4F2Lvl γ = 0) (hh : 0 < height γ) (a : K)
    {q : ↥(adjointGroup Tag.D4 K)} (hq : q ∈ d4F2_Qgrp K) :
    xPar (rootOperatorFamily Tag.D4) γ a * q * (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ ∈
      d4F2_Qgrp K := by
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, hl, c, rfl⟩ := hx
    exact d4F2_conj_QGen_of_UL_gen hγ hγ0 hh hβ hl a c
  | one => simp
  | mul x y _ _ hx hy =>
    have e : xPar (rootOperatorFamily Tag.D4) γ a * (x * y) *
        (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ =
          (xPar (rootOperatorFamily Tag.D4) γ a * x * (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹) *
            (xPar (rootOperatorFamily Tag.D4) γ a * y *
              (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : xPar (rootOperatorFamily Tag.D4) γ a * x⁻¹ *
        (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹ =
          (xPar (rootOperatorFamily Tag.D4) γ a * x *
            (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hx

theorem d4F2_ULgrp_le_normalizer_Qgrp {K : Type} [Field K] :
    d4F2_ULgrp K ≤ Subgroup.normalizer (d4F2_Qgrp K : Set ↥(adjointGroup Tag.D4 K)) := by
  rw [d4F2_ULgrp, Subgroup.closure_le]
  rintro g ⟨γ, hγ, hγ0, hh, a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact d4F2_conj_Q_of_UL_gen hγ hγ0 hh a
  · intro hq
    have h := d4F2_conj_Q_of_UL_gen hγ hγ0 hh (-a) hq
    have e : xPar (rootOperatorFamily Tag.D4) γ (-a) *
        (xPar (rootOperatorFamily Tag.D4) γ a * q * (xPar (rootOperatorFamily Tag.D4) γ a)⁻¹) *
          (xPar (rootOperatorFamily Tag.D4) γ (-a))⁻¹ = q := by
      rw [← xPar_neg, inv_inv]; group
    rwa [e] at h

theorem d4F2_lvl_nonneg_of_height_pos {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h : 0 < height γ) : 0 ≤ d4F2Lvl γ := by
  have key : ∀ γ ∈ rootFinset Tag.D4, 0 < height γ → 0 ≤ d4F2Lvl γ := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h

theorem d4F2_torusElement_mem_StabSL2 {K : Type} [Field K] (i : Fin Tag.D4.rank) (s : Kˣ) :
    CFSG.LieType.Chevalley.torusElement Tag.D4 K i s ∈ d4F2_StabSL2 K := by
  have hθ := d4F2_isRoot_theta
  have hθn : IsRoot Tag.D4 (-d4F2Theta) := IsRoot.neg hθ
  refine ⟨s ^ (∑ j, Tag.D4.cartan i j * d4F2Theta j), fun c => ?_, fun c => ?_⟩
  · rw [xPar_of_isRoot hθ, (rootOperatorFamily Tag.D4).torusElement_mul_eltElement_mul_inv,
      ← xPar_of_isRoot hθ]
  · rw [xPar_of_isRoot hθn, (rootOperatorFamily Tag.D4).torusElement_mul_eltElement_mul_inv,
      ← xPar_of_isRoot hθn]
    congr 2
    simp [Finset.sum_neg_distrib, mul_neg, zpow_neg]

theorem d4F2_torus_le_StabSL2 {K : Type} [Field K] :
    (⨆ i : Fin Tag.D4.rank, torus (τ := Tag.D4) K i) ≤ d4F2_StabSL2 K := by
  refine iSup_le fun i => ?_
  rintro _ ⟨s, rfl⟩
  exact d4F2_torusElement_mem_StabSL2 i s

end D4F2Levi

section D4F2Borel

theorem d4F2_posUnip_decomp {K : Type} [Field K] {u : ↥(adjointGroup Tag.D4 K)}
    (hu : u ∈ posUnipD Tag.D4 K) : ∃ q ∈ d4F2_Qgrp K, ∃ l ∈ d4F2_ULgrp K, u = q * l := by
  have hle : posUnipD Tag.D4 K ≤ d4F2_Qgrp K ⊔ d4F2_ULgrp K := by
    unfold posUnipD
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hh⟩ := hγ
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr x).1 hx
    rcases (d4F2_lvl_nonneg_of_height_pos hr hh).lt_or_eq with hpos | hzero
    · exact Subgroup.mem_sup_left (d4F2_xPar_mem_Qgrp hr hpos c)
    · exact Subgroup.mem_sup_right (d4F2_xPar_mem_ULgrp hr hzero.symm hh c)
  have hu2 : u ∈ (↑(d4F2_Qgrp K ⊔ d4F2_ULgrp K) : Set ↥(adjointGroup Tag.D4 K)) := hle hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ d4F2_ULgrp_le_normalizer_Qgrp,
    Set.mem_mul] at hu2
  obtain ⟨q, hq, l, hl, hql⟩ := hu2
  exact ⟨q, hq, l, hl, hql.symm⟩

theorem d4F2_posUnip_torus_conj {K : Type} [Field K] (i : Fin Tag.D4.rank) (s : Kˣ)
    {h : ↥(adjointGroup Tag.D4 K)} (hh : h ∈ posUnipD Tag.D4 K) :
    CFSG.LieType.Chevalley.torusElement Tag.D4 K i s * h *
      (CFSG.LieType.Chevalley.torusElement Tag.D4 K i s)⁻¹ ∈ posUnipD Tag.D4 K := by
  have hle : posUnipD Tag.D4 K ≤ (posUnipD Tag.D4 K).comap
      (MulAut.conj (CFSG.LieType.Chevalley.torusElement Tag.D4 K i s)).toMonoidHom := by
    refine iSup₂_le fun γ hγ => ?_
    have hγ' : IsRoot Tag.D4 γ ∧ 0 < height γ := hγ
    intro x hx
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (le_iSup₂ (f := fun γ (_ : γ ∈ {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ ∧
      0 < height γ}) => rootGroup (rootOperatorFamily Tag.D4) K γ) γ hγ)
      (torusElement_conj_mem i s hγ'.1 hx)
  exact Subgroup.mem_comap.1 (hle hh)

theorem d4F2_borel_decomp {K : Type} [Field K] {b : ↥(adjointGroup Tag.D4 K)}
    (hb : b ∈ borelSubD Tag.D4 K) :
    ∃ u ∈ posUnipD Tag.D4 K, ∃ t ∈ (⨆ i : Fin Tag.D4.rank, torus (τ := Tag.D4) K i), b = u * t := by
  have hT : (⨆ i : Fin Tag.D4.rank, torus (τ := Tag.D4) K i) ≤
      Subgroup.normalizer (posUnipD Tag.D4 K : Set ↥(adjointGroup Tag.D4 K)) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    change CFSG.LieType.Chevalley.torusElement Tag.D4 K i s ∈
      Subgroup.normalizer (posUnipD Tag.D4 K : Set ↥(adjointGroup Tag.D4 K))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : h ∈ posUnipD Tag.D4 K := hh
      exact d4F2_posUnip_torus_conj i s hh'
    · intro hh
      have hh' : CFSG.LieType.Chevalley.torusElement Tag.D4 K i s * h *
          (CFSG.LieType.Chevalley.torusElement Tag.D4 K i s)⁻¹ ∈ posUnipD Tag.D4 K := hh
      have h1 := d4F2_posUnip_torus_conj i s⁻¹ hh'
      have hinv : CFSG.LieType.Chevalley.torusElement Tag.D4 K i s⁻¹ =
          (CFSG.LieType.Chevalley.torusElement Tag.D4 K i s)⁻¹ :=
        map_inv (torusHom (τ := Tag.D4) K i) s
      rw [hinv, inv_inv] at h1
      have h2 : h ∈ posUnipD Tag.D4 K := by
        convert h1 using 1
        group
      exact h2
  have hb2 : b ∈ (↑(posUnipD Tag.D4 K ⊔ ⨆ i : Fin Tag.D4.rank, torus (τ := Tag.D4) K i) :
      Set ↥(adjointGroup Tag.D4 K)) := by
    rw [sup_comm]
    exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT, Set.mem_mul] at hb2
  obtain ⟨u, hu, t, ht, hut⟩ := hb2
  exact ⟨u, hu, t, ht, hut.symm⟩

theorem d4F2_exists_Q_decomp {K : Type} [Field K] {b : ↥(adjointGroup Tag.D4 K)}
    (hb : b ∈ borelSubD Tag.D4 K) : ∃ q ∈ d4F2_Qgrp K, ∃ m ∈ d4F2_StabSL2 K, b = q * m := by
  obtain ⟨u, hu, t, ht, rfl⟩ := d4F2_borel_decomp hb
  obtain ⟨q, hq, l, hl, rfl⟩ := d4F2_posUnip_decomp hu
  exact ⟨q, hq, l * t, Subgroup.mul_mem _ (d4F2_ULgrp_le_StabSL2 hl) (d4F2_torus_le_StabSL2 ht),
    by group⟩

end D4F2Borel

end CFSG.LieType.SeitzGeneration.ExcWideThree
