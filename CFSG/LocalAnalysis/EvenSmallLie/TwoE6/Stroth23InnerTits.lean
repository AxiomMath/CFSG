module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerKer
public import CFSG.Monster.B.GSide.NativeTrianglePresentation
public import CFSG.Monster.B.GSide.EdgeAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

open Classical in
@[expose] noncomputable def chiH : vStab cv0 →* Multiplicative (ZMod 2) where
  toFun h := if h ∈ commutator (vStab cv0) then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' a b := by
    have h := Subgroup.mul_mem_iff_of_index_two index_commutator_H (a := a) (b := b)
    by_cases ha : a ∈ commutator (vStab cv0)
    · by_cases hb : b ∈ commutator (vStab cv0)
      · simp only [ha, hb, h.2 (iff_of_true ha hb), ite_true, mul_one]
      · have hab : a * b ∉ commutator (vStab cv0) := fun hab => hb ((h.1 hab).1 ha)
        simp only [ha, hb, hab, ite_true, ite_false, one_mul]
    · by_cases hb : b ∈ commutator (vStab cv0)
      · have hab : a * b ∉ commutator (vStab cv0) := fun hab => ha ((h.1 hab).2 hb)
        simp only [ha, hb, hab, ite_true, ite_false, mul_one]
      · simp only [ha, hb, h.2 (iff_of_false ha hb), ite_true, ite_false]
        decide

theorem chiH_of_mem {h : vStab cv0} (hh : h ∈ commutator (vStab cv0)) : chiH h = 1 := by
  simp only [chiH, MonoidHom.coe_mk, OneHom.coe_mk, hh, ite_true]

theorem chiH_of_not_mem {h : vStab cv0} (hh : h ∉ commutator (vStab cv0)) :
    chiH h = Multiplicative.ofAdd 1 := by
  simp only [chiH, MonoidHom.coe_mk, OneHom.coe_mk, hh, ite_false]

theorem cvMul_inv_of_eq {v w : CVert} {s : Shat} (h : cvMul v s = w) : cvMul w s⁻¹ = v := by
  rw [← h, cvMul_inv_cancel]

theorem conj_mem_cEdgeFix {s : Shat} (hs : s ∈ cEdgeStab) {x : Shat} (hx : x ∈ cEdgeFix) :
    s * x * s⁻¹ ∈ cEdgeFix := by
  have h0 : cvMul cv0 x = cv0 := hx.1
  have h1 : cvMul cw0 x = cw0 := hx.2
  rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hs with ⟨hs0, hs1⟩ | ⟨hs0, hs1⟩
  · exact ⟨mem_vStab.2 (by rw [cvMul_mul, cvMul_mul, hs0, h0, cvMul_inv_of_eq hs0]),
      mem_vStab.2 (by rw [cvMul_mul, cvMul_mul, hs1, h1, cvMul_inv_of_eq hs1])⟩
  · exact ⟨mem_vStab.2 (by rw [cvMul_mul, cvMul_mul, hs0, h1, cvMul_inv_of_eq hs0]),
      mem_vStab.2 (by rw [cvMul_mul, cvMul_mul, hs1, h0, cvMul_inv_of_eq hs1])⟩

@[expose] noncomputable def conjA {s : Shat} (hs : s ∈ cEdgeStab) : cEdgeFix ≃* cEdgeFix :=
  conjSubgroupEquiv cEdgeFix s (fun _ hx => conj_mem_cEdgeFix hs hx)
    (fun x hx => by simpa only [inv_inv] using conj_mem_cEdgeFix (inv_mem hs) hx)

theorem conj_mem_HS_iff {s : Shat} (hs : s ∈ cEdgeStab) {x : Shat} (hx : x ∈ cEdgeFix) :
    s * x * s⁻¹ ∈ HS ↔ x ∈ HS := by
  have e1 : s * x * s⁻¹ = ((cEdgeFixToH (conjA hs ⟨x, hx⟩) : vStab cv0) : Shat) := rfl
  rw [e1, coe_mem_HS_iff, mem_commutator_H_iff cEdgeFix_commutator_index,
    mem_commutator_iff_of_mulEquiv]
  exact ((coe_mem_HS_iff (cEdgeFixToH ⟨x, hx⟩)).trans
    (mem_commutator_H_iff cEdgeFix_commutator_index ⟨x, hx⟩)).symm

@[expose] noncomputable def chiA : cEdgeFix →* Multiplicative (ZMod 2) := chiH.comp cEdgeFixToH

theorem chiA_apply (a : cEdgeFix) : chiA a = chiH (cEdgeFixToH a) := rfl

theorem chiH_eq_of_iff {h h' : vStab cv0}
    (hh : h ∈ commutator (vStab cv0) ↔ h' ∈ commutator (vStab cv0)) : chiH h = chiH h' := by
  by_cases h1 : h' ∈ commutator (vStab cv0)
  · exact (chiH_of_mem (hh.2 h1)).trans (chiH_of_mem h1).symm
  · exact (chiH_of_not_mem (fun h2 => h1 (hh.1 h2))).trans (chiH_of_not_mem h1).symm

theorem chiA_cEdgeSigma {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    (a : cEdgeFix) : chiA (cEdgeSigma hs0 hs1 a) = chiA a := by
  rw [chiA_apply, chiA_apply]
  refine chiH_eq_of_iff ?_
  rw [← coe_mem_HS_iff, ← coe_mem_HS_iff]
  exact conj_mem_HS_iff (swap_mem_cEdgeStab hs0 hs1) a.2

theorem mul_self_C2 : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide

theorem exists_chiE {b : Shat} (hb0 : cvMul cv0 b = cw0) (hb1 : cvMul cw0 b = cv0)
    (hb2 : b * b = 1) : ∃ f : cEdgeStab →* Multiplicative (ZMod 2),
      (∀ a : cEdgeFix, f (cEdgeIncl a) = chiA a) ∧ f (swapE hb0 hb1) = 1 := by
  have ht : ∀ a, (1 : Multiplicative (ZMod 2)) * chiA a * 1⁻¹ = chiA (cEdgeSigma hb0 hb1 a) :=
    fun a => by
      simp only [one_mul, inv_one, mul_one]
      exact (chiA_cEdgeSigma hb0 hb1 a).symm
  have hτ : swapE hb0 hb1 * swapE hb0 hb1 = cEdgeIncl 1 :=
    (Subtype.ext hb2 : swapE hb0 hb1 * swapE hb0 hb1 = 1).trans (map_one cEdgeIncl).symm
  have hσ : ∀ a, swapE hb0 hb1 * cEdgeIncl a * (swapE hb0 hb1)⁻¹ =
      cEdgeIncl (cEdgeSigma hb0 hb1 a) := cEdgeSigma_spec hb0 hb1
  have hρ : (1 : Multiplicative (ZMod 2)) * 1 = chiA 1 := (mul_one 1).trans (map_one chiA).symm
  have hτρ : (1 : cEdgeFix) = 1 * (1 * cEdgeSigma hb0 hb1 1) :=
    ((one_mul _).trans ((one_mul _).trans (map_one _))).symm
  have hd : (1 : cEdgeFix) ∈ Subgroup.center cEdgeFix := one_mem _
  obtain ⟨f, hfA, hfs⟩ := exists_hom_of_index_two_of_norm cEdgeIncl cEdgeIncl_injective
    index_range_cEdgeIncl (swapE_not_mem_range hb0 hb1) (cEdgeSigma hb0 hb1) hσ chiA 1 ht hτ hρ
    hd hτρ
  exact ⟨f, hfA, hfs.trans ((congrArg (1 * ·) (map_one chiA)).trans (mul_one 1))⟩

theorem mem_cEdgeFix_of_mem {x : Shat} (hx : x ∈ vStab cv0) (hx' : x ∈ cEdgeStab) :
    x ∈ cEdgeFix := by
  rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hx' with ⟨h0, h1⟩ | ⟨h0, -⟩
  · exact ⟨h0, h1⟩
  · exact absurd ((mem_vStab.1 hx).symm.trans h0) cgraph_adj_cv0_cw0.ne

@[expose] noncomputable def chiT (j : Fin 2) :
    ↥(cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0) →* Multiplicative (ZMod 2) :=
  chiH.comp (Subgroup.inclusion (inf_le_right : cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0 ≤ _))

theorem chiT_apply (j : Fin 2) (x : ↥(cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0)) :
    chiT j x = chiH ⟨x, x.2.2⟩ := rfl

@[expose] noncomputable def phiT (j : Fin 2) (φe : cEdgeStab →* Multiplicative (ZMod 2)) :
    ↥(cvSetStab {cv0, cw0, cu j} ⊓ cvSetStab {cv0, cw0}) →* Multiplicative (ZMod 2) :=
  φe.comp (Subgroup.inclusion
    (inf_le_right : cvSetStab {cv0, cw0, cu j} ⊓ cvSetStab {cv0, cw0} ≤ _))

theorem phiT_apply (j : Fin 2) (φe : cEdgeStab →* Multiplicative (ZMod 2))
    (x : ↥(cvSetStab {cv0, cw0, cu j} ⊓ cvSetStab {cv0, cw0})) :
    phiT j φe x = φe ⟨x, x.2.2⟩ := rfl

theorem exists_triangle_ext (j : Fin 2) {a b : Shat} (ha : IsTriA j a) (hb : IsTriB j b)
    (hab : (a * b) ^ 3 = 1) (φe : cEdgeStab →* Multiplicative (ZMod 2))
    (hφ : ∀ x (hx : x ∈ cEdgeFix), φe ⟨x, cEdgeFix_le_cEdgeStab hx⟩ = chiH ⟨x, hx.1⟩)
    (hval : chiH ⟨a, mem_vStab.2 ha.1⟩ = φe ⟨b, swap_mem_cEdgeStab hb.1 hb.2.1⟩) :
    ∃ φt : cvSetStab {cv0, cw0, cu j} →* Multiplicative (ZMod 2),
      (∀ x (hx : x ∈ cvSetStab {cv0, cw0, cu j}) (h₁ : x ∈ vStab cv0),
        φt ⟨x, hx⟩ = chiH ⟨x, h₁⟩) ∧
      ∀ x (hx : x ∈ cvSetStab {cv0, cw0, cu j}) (h₂ : x ∈ cEdgeStab),
        φt ⟨x, hx⟩ = φe ⟨x, h₂⟩ := by
  have hf : ∀ k (h₁ : k ∈ cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0)
      (h₂ : k ∈ cvSetStab {cv0, cw0, cu j} ⊓ cvSetStab {cv0, cw0}),
      chiT j ⟨k, h₁⟩ = phiT j φe ⟨k, h₂⟩ := fun k h₁ h₂ => by
    rw [chiT_apply, phiT_apply]
    exact (hφ k (mem_cEdgeFix_of_mem h₁.2 h₂.2)).symm
  have hrel : ∀ (h₁ : a ∈ cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0)
      (h₂ : b ∈ cvSetStab {cv0, cw0, cu j} ⊓ cvSetStab {cv0, cw0})
      (h₃ : (a * b) ^ 3 ∈ cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0),
      (chiT j ⟨a, h₁⟩ * phiT j φe ⟨b, h₂⟩) ^ 3 = chiT j ⟨(a * b) ^ 3, h₃⟩ := by
    intro h₁ h₂ h₃
    have e1 : chiT j ⟨a, h₁⟩ = phiT j φe ⟨b, h₂⟩ := hval
    have e2 : (⟨(a * b) ^ 3, h₃⟩ : ↥(cvSetStab {cv0, cw0, cu j} ⊓ vStab cv0)) = 1 :=
      Subtype.ext hab
    calc (chiT j ⟨a, h₁⟩ * phiT j φe ⟨b, h₂⟩) ^ 3
        = (phiT j φe ⟨b, h₂⟩ * phiT j φe ⟨b, h₂⟩) ^ 3 :=
          congrArg (fun x => (x * phiT j φe ⟨b, h₂⟩) ^ 3) e1
      _ = 1 := (congrArg (· ^ 3) (mul_self_C2 _)).trans (one_pow 3)
      _ = chiT j ⟨(a * b) ^ 3, h₃⟩ := ((congrArg (chiT j) e2).trans (map_one _)).symm
  obtain ⟨f, ⟨hf1, hf2⟩, -⟩ :=
    exists_unique_extend_cvTriangle (isCTriangle_cu j) (chiT j) (phiT j φe) hf ha hb hrel
  refine ⟨f, fun x hx h₁ => ?_, fun x hx h₂ => ?_⟩
  · exact (hf1 x hx ⟨hx, h₁⟩).trans (chiT_apply j _)
  · exact (hf2 x hx ⟨hx, h₂⟩).trans (phiT_apply j φe _)

theorem cV0_coe_ne_one : (cV0 : Shat) ≠ 1 := fun h => by
  have h1 : cV0 = 1 := Subtype.ext h
  have h2 := orderOf_cV0
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem inv_mul_mem_HS {a₀ b₀ a₁ b₁ : Shat} (ha₀ : IsTriA 0 a₀) (hb₀ : IsTriB 0 b₀)
    (ha₁ : IsTriA 1 a₁) (hb₁ : IsTriB 1 b₁) (h₀ : (a₀ * b₀) ^ 3 = 1) (h₁ : (a₁ * b₁) ^ 3 = 1)
    (hb₀2 : b₀ * b₀ = 1) (ha₀H : a₀ ∈ HS) (ha₁H : a₁ ∉ HS) : b₀⁻¹ * b₁ ∈ HS := by
  by_contra hne
  obtain ⟨φe, hφA, hφb⟩ := exists_chiE hb₀.1 hb₀.2.1 hb₀2
  have hφ : ∀ x (hx : x ∈ cEdgeFix), φe ⟨x, cEdgeFix_le_cEdgeStab hx⟩ = chiH ⟨x, hx.1⟩ :=
    fun x hx => hφA ⟨x, hx⟩
  have hA : b₀⁻¹ * b₁ ∈ cEdgeFix := by
    refine ⟨mem_vStab.2 ?_, mem_vStab.2 ?_⟩
    · rw [cvMul_mul, cvMul_inv_of_eq hb₀.2.1, hb₁.2.1]
    · rw [cvMul_mul, cvMul_inv_of_eq hb₀.1, hb₁.1]
  have hb₁v : φe ⟨b₁, swap_mem_cEdgeStab hb₁.1 hb₁.2.1⟩ = Multiplicative.ofAdd 1 := by
    have e : (⟨b₁, swap_mem_cEdgeStab hb₁.1 hb₁.2.1⟩ : cEdgeStab) =
        swapE hb₀.1 hb₀.2.1 * cEdgeIncl ⟨b₀⁻¹ * b₁, hA⟩ :=
      Subtype.ext (mul_inv_cancel_left b₀ b₁).symm
    rw [e, map_mul, hφb, one_mul, hφA, chiA_apply]
    exact chiH_of_not_mem (fun h => hne ((coe_mem_HS_iff _).2 h))
  have hv0 : chiH ⟨a₀, mem_vStab.2 ha₀.1⟩ = φe ⟨b₀, swap_mem_cEdgeStab hb₀.1 hb₀.2.1⟩ :=
    (chiH_of_mem ((coe_mem_HS_iff ⟨a₀, mem_vStab.2 ha₀.1⟩).1 ha₀H)).trans hφb.symm
  have hv1 : chiH ⟨a₁, mem_vStab.2 ha₁.1⟩ = φe ⟨b₁, swap_mem_cEdgeStab hb₁.1 hb₁.2.1⟩ :=
    (chiH_of_not_mem (fun h => ha₁H ((coe_mem_HS_iff _).2 h))).trans hb₁v.symm
  have key : ∀ j : Fin 2, ∃ φt : cvSetStab {cv0, cw0, cu j} →* Multiplicative (ZMod 2),
      (∀ x (hx : x ∈ cvSetStab {cv0, cw0, cu j}) (h₁ : x ∈ vStab cv0),
        φt ⟨x, hx⟩ = chiH ⟨x, h₁⟩) ∧
      ∀ x (hx : x ∈ cvSetStab {cv0, cw0, cu j}) (h₂ : x ∈ cEdgeStab),
        φt ⟨x, hx⟩ = φe ⟨x, h₂⟩ := by
    intro j
    fin_cases j
    · exact exists_triangle_ext 0 ha₀ hb₀ h₀ φe hφ hv0
    · exact exists_triangle_ext 1 ha₁ hb₁ h₁ φe hφ hv1
  choose φt hφt₁ hφt₂ using key
  obtain ⟨Φ, ⟨hΦv, -, -⟩, -⟩ := native_universal_completion_of_ambient_cu ambientRootOrbitsHyp
    chiH φe φt (fun x ha hb => (hφ x (mem_cEdgeFix_of_mem ha hb)).symm)
    (fun j x ha hb => (hφt₁ j x hb ha).symm) (fun j x ha hb => (hφt₂ j x hb ha).symm)
  haveI : IsSimpleGroup Shat := CFSG.Monster.B.GSide.isSimpleGroup_Shat
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with hk | hk
  · have h1 : (cV0 : Shat) ∈ Φ.ker := by
      rw [MonoidHom.mem_ker, hΦv cV0]
      exact chiH_of_mem cV0_mem_commutator_H.1
    rw [hk, Subgroup.mem_bot] at h1
    exact cV0_coe_ne_one h1
  · have h1 : a₁ ∈ Φ.ker := by
      rw [hk]
      exact Subgroup.mem_top _
    have h2 : Φ a₁ = Multiplicative.ofAdd 1 := by
      have h3 := hΦv ⟨a₁, mem_vStab.2 ha₁.1⟩
      exact h3.trans (chiH_of_not_mem (fun h => ha₁H ((coe_mem_HS_iff _).2 h)))
    rw [MonoidHom.mem_ker, h2] at h1
    exact absurd h1 (by decide)

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
