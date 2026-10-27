module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.QGroup
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCellConj

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section QBorel

variable {τ : Tag} {K : Type} [Field K]

theorem posUnip_decomp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {u : ↥(adjointGroup τ K)}
    (hu : u ∈ posUnip τ K) : ∃ q ∈ Qgrp τ K, ∃ l ∈ ULgrp τ K, u = q * l := by
  have hle : posUnip τ K ≤ Qgrp τ K ⊔ ULgrp τ K := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hh⟩ := hγ
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr x).1 hx
    rcases (lvl_nonneg_of_height_pos hτ hr hh).lt_or_eq with hpos | hzero
    · exact Subgroup.mem_sup_left (xPar_mem_Qgrp hr hpos c)
    · exact Subgroup.mem_sup_right (xPar_mem_ULgrp hr hzero.symm hh c)
  have hu2 : u ∈ (↑(Qgrp τ K ⊔ ULgrp τ K) : Set ↥(adjointGroup τ K)) := hle hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (ULgrp_le_normalizer_Qgrp hτ), Set.mem_mul] at hu2
  obtain ⟨q, hq, l, hl, hql⟩ := hu2
  exact ⟨q, hq, l, hl, hql.symm⟩

private theorem posUnip_torus_conj (i : Fin τ.rank) (s : Kˣ) {h : ↥(adjointGroup τ K)}
    (hh : h ∈ posUnip τ K) :
    CFSG.LieType.Chevalley.torusElement τ K i s * h * (CFSG.LieType.Chevalley.torusElement τ K i s)⁻¹ ∈
      posUnip τ K := by
  have hle : posUnip τ K ≤ (posUnip τ K).comap
      (MulAut.conj (CFSG.LieType.Chevalley.torusElement τ K i s)).toMonoidHom := by
    refine iSup₂_le fun γ hγ => ?_
    have hγ' : IsRoot τ γ ∧ 0 < height γ := hγ
    intro x hx
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (le_iSup₂ (f := fun γ (_ : γ ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ}) =>
      rootGroup (rootOperatorFamily τ) K γ) γ hγ) (torusElement_conj_mem i s hγ'.1 hx)
  exact Subgroup.mem_comap.1 (hle hh)

theorem borel_decomp {b : ↥(adjointGroup τ K)} (hb : b ∈ borelSub τ K) :
    ∃ u ∈ posUnip τ K, ∃ t ∈ (⨆ i : Fin τ.rank, torus (τ := τ) K i), b = u * t := by
  have hT : (⨆ i : Fin τ.rank, torus (τ := τ) K i) ≤
      Subgroup.normalizer (posUnip τ K : Set ↥(adjointGroup τ K)) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    change CFSG.LieType.Chevalley.torusElement τ K i s ∈
      Subgroup.normalizer (posUnip τ K : Set ↥(adjointGroup τ K))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : h ∈ posUnip τ K := hh
      exact posUnip_torus_conj i s hh'
    · intro hh
      have hh' : CFSG.LieType.Chevalley.torusElement τ K i s * h *
          (CFSG.LieType.Chevalley.torusElement τ K i s)⁻¹ ∈ posUnip τ K := hh
      have h1 := posUnip_torus_conj i s⁻¹ hh'
      have hinv : CFSG.LieType.Chevalley.torusElement τ K i s⁻¹ =
          (CFSG.LieType.Chevalley.torusElement τ K i s)⁻¹ :=
        map_inv (torusHom (τ := τ) K i) s
      rw [hinv, inv_inv] at h1
      have h2 : h ∈ posUnip τ K := by
        convert h1 using 1
        group
      exact h2
  have hb2 : b ∈ (↑(posUnip τ K ⊔ ⨆ i : Fin τ.rank, torus (τ := τ) K i) :
      Set ↥(adjointGroup τ K)) := by
    rw [sup_comm]
    exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT, Set.mem_mul] at hb2
  obtain ⟨u, hu, t, ht, hut⟩ := hb2
  exact ⟨u, hu, t, ht, hut.symm⟩

theorem exists_Q_decomp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {b : ↥(adjointGroup τ K)}
    (hb : b ∈ borelSub τ K) : ∃ q ∈ Qgrp τ K, ∃ m ∈ StabSL2 τ K, b = q * m := by
  obtain ⟨u, hu, t, ht, rfl⟩ := borel_decomp hb
  obtain ⟨q, hq, l, hl, rfl⟩ := posUnip_decomp hτ hu
  exact ⟨q, hq, l * t, Subgroup.mul_mem _ (ULgrp_le_StabSL2 hτ hl) (torus_le_StabSL2 hτ ht), by group⟩

theorem bigCell_conj_borel (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hlam : entry g (negLabel hθ.1) (rootLabel hθ.1) ≠ 0) :
    ∃ (b : ↥(adjointGroup τ K)) (χ μ : K), b ∈ borelSub τ K ∧ χ ≠ 0 ∧
      (∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ (χ * c)) ∧
      (χ⁻¹ * μ = entry g (negLabel hθ.1) (rootLabel hθ.1) ∨
        χ⁻¹ * μ = -entry g (negLabel hθ.1) (rootLabel hθ.1)) ∧
      ∀ c : K, g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b * xPar (rootOperatorFamily τ) (-θ) (μ * c) * b⁻¹ := by
  classical
  obtain ⟨w, b₁, b₂, hb₁, hb₂, hg⟩ := exists_bruhat_decomp hτ g
  obtain ⟨χ₁, hv₁, hz₁, hc₁⟩ := borel_stab hτ hθ hb₁
  obtain ⟨χ₂, hv₂, hz₂, hc₂⟩ := borel_stab hτ hθ hb₂
  obtain ⟨θ', hθ', ε, ε', hε, hε', hn, hvw, hxw⟩ := wordProd_stab (K := K) hτ hθ w
  have hentry : entry g (negLabel hθ.1) (rootLabel hθ.1) =
      (χ₂ : K) * ε * (((χ₁⁻¹ : Kˣ) : K) * (rootVec τ K θ') (negLabel hθ.1)) := by
    unfold entry
    have hv : (Finsupp.single (rootLabel hθ.1) (1 : K) : RootModule τ K) = rootVec τ K θ :=
      (rootVec_eq_single hθ.1).symm
    rw [hv, hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv₂, map_smul, hvw,
      map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hz₁]
    simp only [smul_eq_mul]
    ring
  have hθ'eq : θ' = -θ := by
    by_contra hne
    apply hlam
    rw [hentry]
    have : (rootVec τ K θ') (negLabel hθ.1) = 0 := by
      rw [rootVec_eq_single hθ', Finsupp.single_apply, if_neg]
      intro h
      apply hne
      have h' := h
      simp only [negLabel, rootLabel, Sum.inr.injEq, Subtype.mk.injEq] at h'
      exact h'
    rw [this]
    simp
  subst hθ'eq
  have hone : (rootVec τ K (-θ)) (negLabel hθ.1) = 1 := by
    rw [rootVec_eq_single hθ']
    simp [negLabel, rootLabel]
  rw [hone] at hentry
  refine ⟨b₁, (χ₁ : K), (ε' : K) * χ₂, hb₁, Units.ne_zero _, hc₁, ?_, fun c => ?_⟩
  · have hχ : ((χ₁⁻¹ : Kˣ) : K) = (χ₁ : K)⁻¹ := by simp
    have hlamE : entry g (negLabel hθ.1) (rootLabel hθ.1) = (χ₂ : K) * ε * (χ₁ : K)⁻¹ := by
      rw [hentry, hχ]
      ring
    have hχ0 : (χ₁ : K) ≠ 0 := Units.ne_zero _
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    · left; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · left; rw [hlamE]; push_cast; field_simp
  · have e : g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b₁ * (wordProd τ K w * (b₂ * xPar (rootOperatorFamily τ) θ c * b₂⁻¹) * (wordProd τ K w)⁻¹) *
          b₁⁻¹ := by
      rw [hg]
      group
    rw [e, hc₂, hxw]
    congr 3
    ring

theorem bigCell_conj_Q (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (g : ↥(adjointGroup τ K))
    (hlam : entry g (negLabel (hiRoot_isMax hτ).1) (rootLabel (hiRoot_isMax hτ).1) ≠ 0) :
    ∃ q ∈ Qgrp τ K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      g * xPar (rootOperatorFamily τ) (hiRoot τ) c * g⁻¹ =
        q * xPar (rootOperatorFamily τ) (-hiRoot τ)
          ((ε : K) * entry g (negLabel (hiRoot_isMax hτ).1) (rootLabel (hiRoot_isMax hτ).1) * c) * q⁻¹ := by
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h | h | h <;> simp [h]
  obtain ⟨b, χ, μ, hb, hχ, hbθ, hμ, hg⟩ := bigCell_conj_borel hτ' (hiRoot_isMax hτ) g hlam
  obtain ⟨q, hq, m, ⟨χm, hm1, hm2⟩, rfl⟩ := exists_Q_decomp hτ hb
  have hθ := (hiRoot_isMax hτ).1
  have hχm : (χm : K) = χ := by
    have h1 := hbθ 1
    have e : q * m * xPar (rootOperatorFamily τ) (hiRoot τ) 1 * (q * m)⁻¹ =
        q * (m * xPar (rootOperatorFamily τ) (hiRoot τ) 1 * m⁻¹) * q⁻¹ := by group
    rw [e, hm1 1, ((commute_Q_hiRoot hτ hq _).eq), mul_inv_cancel_right] at h1
    have := xPar_injective hθ h1
    simpa using this
  refine ⟨q, hq, ?_⟩
  have hε : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ χ⁻¹ * μ = (ε : K) * entry g (negLabel (hiRoot_isMax hτ).1)
      (rootLabel (hiRoot_isMax hτ).1) := by
    rcases hμ with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  obtain ⟨ε, hε1, hε2⟩ := hε
  refine ⟨ε, hε1, fun c => ?_⟩
  have e : q * m * xPar (rootOperatorFamily τ) (-hiRoot τ) (μ * c) * (q * m)⁻¹ =
      q * (m * xPar (rootOperatorFamily τ) (-hiRoot τ) (μ * c) * m⁻¹) * q⁻¹ := by group
  rw [hg c, e, hm2 (μ * c)]
  congr 2
  rw [Units.val_inv_eq_inv_val, hχm, ← hε2]
  ring

end QBorel

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
