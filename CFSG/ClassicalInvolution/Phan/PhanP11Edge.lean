module

public import CFSG.ClassicalInvolution.Phan.PhanP9Omega
public import CFSG.ClassicalInvolution.Phan.PhanP10Dec
public import CFSG.ClassicalInvolution.Phan.PhanP8Orient

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section Edge

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem range_le_parab_pair {j : Fin 4} (hj : j = 2 ∨ j = 3) :
    (S.ι j).range ≤ parab S {2, 3} := by
  refine le_trans ?_ (Lsup_le_parab (S := S) {2, 3})
  rintro x hx
  rw [Lsup_pair]
  rcases hj with rfl | rfl
  · exact Subgroup.mem_sup_left hx
  · exact Subgroup.mem_sup_right hx

theorem edge_core [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (hε' : ¬IsSquare (-ε)) {h k ρ ρ' : spinGroup (quadPlus 4 F)} (hh : h ∈ parab S {1, 2, 3})
    (hk : k ∈ parab S {1, 2, 3}) (hρ : ρ ∈ (S.ι 0).range) (hρ' : ρ' ∈ (S.ι 0).range)
    (hρ'T : ρ' ∉ torusSub S) (hrel : h * ρ' = ρ * k) : h ∈ parab S {2, 3} := by
  have hhJ := parab_le_stabJ hK hg hS h2 h2K hh
  have hkJ := parab_le_stabJ hK hg hS h2 h2K hk
  have hrel' : ∀ y, spinAction (quadPlus 4 F) h (spinAction (quadPlus 4 F) ρ' y) =
      spinAction (quadPlus 4 F) ρ (spinAction (quadPlus 4 F) k y) := fun y => by
    have := LinearEquiv.congr_fun (congrArg (spinAction (quadPlus 4 F)) hrel) y
    simpa only [map_mul, LinearEquiv.mul_apply] using this
  have hW : ∀ x ∈ (frame0 (F := F)).span,
      spinAction (quadPlus 4 F) h x ∈ (frame0 (F := F)).span := by
    intro x hx
    obtain ⟨a, ha, a', ha', rfl⟩ :=
      exists_decomp_span_of_mem_range_zero hK hg hS hq h2 h2K hε' hρ' hρ'T hx
    rw [map_add, hrel']
    exact add_mem (planeA_le_span h2 ((hhJ.1 a).2 ha))
      (spinAction_mem_span_of_mem_range_zero hS hρ (planeA_le_span h2 ((hkJ.1 a').2 ha')))
  have hJ : ∀ x ∈ (frame0 (F := F)).span, spinAction (quadPlus 4 F) h (jOp ε x) =
      jOp ε (spinAction (quadPlus 4 F) h x) := by
    intro x hx
    obtain ⟨a, ha, a', ha', rfl⟩ :=
      exists_decomp_span_of_mem_range_zero hK hg hS hq h2 h2K hε' hρ' hρ'T hx
    have e1 : jOp ε (spinAction (quadPlus 4 F) ρ' a') =
        spinAction (quadPlus 4 F) ρ' (jOp ε a') :=
      (spinAction_comm_jOp_of_mem_range_zero hS hρ' a').symm
    have e2 : spinAction (quadPlus 4 F) h (spinAction (quadPlus 4 F) ρ' (jOp ε a')) =
        jOp ε (spinAction (quadPlus 4 F) h (spinAction (quadPlus 4 F) ρ' a')) := by
      rw [hrel', hrel', hkJ.2 a' ha', spinAction_comm_jOp_of_mem_range_zero hS hρ]
    rw [map_add, map_add, e1, hhJ.2 a ha, e2, map_add, map_add]
  obtain ⟨t, ht, hteq⟩ := exists_tor_eq_on_span hK hg hS hq h2 h2K hhJ hW hJ
  have hfix : ∀ x ∈ (frame0 (F := F)).span,
      spinAction (quadPlus 4 F) (t⁻¹ * h) x = x := by
    intro x hx
    rw [map_mul, LinearEquiv.mul_apply, ← hteq x hx, ← LinearEquiv.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  obtain ⟨A, B, hAB⟩ := exists_La_mul_of_fix h2 hfix
  have hr2 : (frame2 (F := F)).La A ∈ (S.ι 2).range.map (spinAction (quadPlus 4 F)) := by
    rw [hS.map_range 2]
    exact ⟨A, rfl⟩
  have hr3 : (frame2 (F := F)).swap.La B ∈ (S.ι 3).range.map (spinAction (quadPlus 4 F)) := by
    rw [hS.map_range 3]
    exact ⟨B, rfl⟩
  obtain ⟨ρ₂, hρ₂, hρ₂A⟩ := hr2
  obtain ⟨ρ₃, hρ₃, hρ₃B⟩ := hr3
  have hz : spinAction (quadPlus 4 F) ((ρ₂ * ρ₃)⁻¹ * (t⁻¹ * h)) = 1 := by
    rw [map_mul, map_inv, map_mul, hρ₂A, hρ₃B, ← hAB, inv_mul_cancel]
  have hzT := mem_torusSub_of_spinAction_eq_one hg hS h2 h2K hz
  have hh' : h = t * (ρ₂ * ρ₃ * ((ρ₂ * ρ₃)⁻¹ * (t⁻¹ * h))) := by group
  rw [hh']
  exact mul_mem (torusSub_le_parab (S := S) {2, 3} ht) (mul_mem (mul_mem
    (range_le_parab_pair (Or.inl rfl) hρ₂) (range_le_parab_pair (Or.inr rfl) hρ₃))
    (torusSub_le_parab (S := S) {2, 3} hzT))

theorem edge_group [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (hε' : ¬IsSquare (-ε)) {h k r r' : spinGroup (quadPlus 4 F)} (hh : h ∈ parab S {1, 2, 3})
    (hk : k ∈ parab S {1, 2, 3}) (hr : r ∈ parab S {0}) (hr' : r' ∈ parab S {0})
    (hnr : r ∉ parab S {1, 2, 3}) (hrel : h * r' = r * k) :
    h ∈ parab S {2, 3} ∧ k ∈ parab S {2, 3} := by
  obtain ⟨t₁, ht₁, ρ₁, hρ₁, rfl⟩ := exists_mul_of_mem_parab_zero hK hr
  obtain ⟨t₂, ht₂, ρ₂, hρ₂, rfl⟩ := exists_mul_of_mem_parab_zero hK hr'
  have hT123 : torusSub S ≤ parab S {1, 2, 3} := torusSub_le_parab {1, 2, 3}
  have hT23 : torusSub S ≤ parab S {2, 3} := torusSub_le_parab {2, 3}
  have hρ₁T : ρ₁ ∉ torusSub S := fun hT => hnr (mul_mem (hT123 ht₁) (hT123 hT))
  have hρ₂T : ρ₂ ∉ torusSub S := by
    intro hT
    refine hnr ?_
    have : t₁ * ρ₁ = h * (t₂ * ρ₂) * k⁻¹ := by rw [hrel]; group
    rw [this]
    exact mul_mem (mul_mem hh (hT123 (mul_mem ht₂ hT))) (inv_mem hk)
  have hrel1 : (t₁⁻¹ * h * t₂) * ρ₂ = ρ₁ * k := by
    calc (t₁⁻¹ * h * t₂) * ρ₂ = t₁⁻¹ * (h * (t₂ * ρ₂)) := by group
      _ = t₁⁻¹ * ((t₁ * ρ₁) * k) := by rw [hrel]
      _ = ρ₁ * k := by group
  have hh1 : t₁⁻¹ * h * t₂ ∈ parab S {1, 2, 3} :=
    mul_mem (mul_mem (inv_mem (hT123 ht₁)) hh) (hT123 ht₂)
  have hP1 := edge_core hK hg hS hq h2 h2K hε' hh1 hk hρ₁ hρ₂ hρ₂T hrel1
  refine ⟨?_, ?_⟩
  · have : h = t₁ * (t₁⁻¹ * h * t₂) * t₂⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (hT23 ht₁) hP1) (inv_mem (hT23 ht₂))
  · have hrel2 : k⁻¹ * ρ₁⁻¹ = ρ₂⁻¹ * (t₁⁻¹ * h * t₂)⁻¹ := by
      have := congrArg (fun x => x⁻¹) hrel1
      simpa only [mul_inv_rev] using this.symm
    have hρ₁T' : ρ₁⁻¹ ∉ torusSub S := fun hT => hρ₁T (by simpa using inv_mem hT)
    have := edge_core hK hg hS hq h2 h2K hε' (inv_mem hk) (inv_mem hh1) (inv_mem hρ₂)
      (inv_mem hρ₁) hρ₁T' hrel2
    simpa using inv_mem this

theorem ptEdge_of_model [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (hε' : ¬IsSquare (-ε)) : CFSG.ClassicalInvolution.PhanG.PtEdge S := by
  intro a b c d hac hbd hab hcd hne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective d
  rw [phanSystem_adj_mk] at hac hbd
  rw [CFSG.ClassicalInvolution.PhanG.ptMap_eq_iff,
    CFSG.ClassicalInvolution.PhanG.mem_residue_mk_iff] at hab hcd
  have hne' : a⁻¹ * c ∉ parab S {1, 2, 3} := fun h =>
    hne (by
      rw [CFSG.ClassicalInvolution.PhanG.ptMap_mk, CFSG.ClassicalInvolution.PhanG.ptMap_mk]
      exact QuotientGroup.eq.2 h)
  have hrel : (a⁻¹ * b) * (b⁻¹ * d) = (a⁻¹ * c) * (c⁻¹ * d) := by group
  obtain ⟨h1, h2'⟩ := edge_group hK hg hS hq h2 h2K hε' hab hcd hac hbd hne' hrel
  exact ⟨(CFSG.ClassicalInvolution.PhanG.mem_residue_mk_iff _ _ _).2 h2',
    (CFSG.ClassicalInvolution.PhanG.mem_residue_mk_iff _ _ _).2 h1⟩

end Edge

end CFSG.ClassicalInvolution.PhanP
