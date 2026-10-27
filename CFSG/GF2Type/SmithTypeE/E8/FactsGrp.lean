module

public import CFSG.GF2Type.SmithTypeE.E8.ModFacts
public import CFSG.GF2Type.SmithTypeE.E8.FactsData
public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.GF2Type.SmithTypeE.E8.SfAct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


theorem rep_injective {g h : ↥(adjointGroup .E7 (ZMod 2))}
    (H : ∀ v : Fin e7Data.d →₀ ZMod 2, e7Rep56 (ZMod 2) g v = e7Rep56 (ZMod 2) h v) : g = h := by
  have hE : e7Data_valid.endo (ZMod 2) (e7Psi (ZMod 2) g) =
      e7Data_valid.endo (ZMod 2) (e7Psi (ZMod 2) h) := LinearMap.ext H
  have hpsi : e7Psi (ZMod 2) g = e7Psi (ZMod 2) h := e7Data_valid.endo_injective (ZMod 2) hE
  have hpsi' : (e7Equiv (K := ZMod 2)).symm g = (e7Equiv (K := ZMod 2)).symm h := hpsi
  exact (e7Equiv (K := ZMod 2)).symm.injective hpsi'

theorem pinnedElt_mem_posUnipotent {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hpos : 0 < height β) :
    ((pinnedElt .E7 β (1 : ZMod 2) : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
      posUnipotent .E7 (ZMod 2) := by
  have hmem : β ∈ {α : Fin (Tag.rank .E7) → ℤ | IsRoot .E7 α ∧ 0 < height α} := ⟨hβ, hpos⟩
  have hle : rootSubgroup .E7 (ZMod 2) β ≤ posUnipotent .E7 (ZMod 2) :=
    le_biSup (rootSubgroup .E7 (ZMod 2)) hmem
  have h1 : ((pinnedElt .E7 β (1 : ZMod 2) : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
      pinnedX .E7 (ZMod 2) β 1 := rfl
  rw [h1]
  exact hle (Subgroup.subset_closure ⟨1, rfl⟩)

theorem posUnipotent_induction {P : ↥(adjointGroup .E7 (ZMod 2)) → Prop}
    (h1 : P 1) (hmul : ∀ g h, P g → P h → P (g * h)) (hinv : ∀ g, P g → P g⁻¹)
    (hgen : ∀ β, IsRoot .E7 β → 0 < height β → P (pinnedElt .E7 β (1 : ZMod 2)))
    {u : ↥(adjointGroup .E7 (ZMod 2))}
    (hu : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) : P u := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup ↥(adjointGroup .E7 (ZMod 2)), ∀ g, g ∈ H ↔ P g :=
    ⟨{ carrier := {g | P g}
       mul_mem' := fun {a b} ha hb => hmul a b ha hb
       one_mem' := h1
       inv_mem' := fun {a} ha => hinv a ha }, fun g => Iff.rfl⟩
  have hle : posUnipotent .E7 (ZMod 2) ≤ H.map (adjointGroup .E7 (ZMod 2)).subtype := by
    refine iSup₂_le fun β hβ => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨hroot, hpos⟩ := hβ
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · rw [CFSG.Blueprint.Chevalley.pinnedX_zero]
      exact one_mem _
    · exact Subgroup.mem_map.2
        ⟨pinnedElt .E7 β (1 : ZMod 2),
          (hH (pinnedElt .E7 β (1 : ZMod 2))).2 (hgen β hroot hpos), rfl⟩
  obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.1 (hle hu)
  have hgu' : g = u := Subtype.ext hgu
  rw [← hgu']
  exact (hH g).1 hg

theorem pinnedElt_mul_self (β : Fin (Tag.rank .E7) → ℤ) :
    pinnedElt .E7 β (1 : ZMod 2) * pinnedElt .E7 β 1 = 1 := by
  refine Subtype.ext ?_
  show pinnedX .E7 (ZMod 2) β 1 * pinnedX .E7 (ZMod 2) β 1 = 1
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [← pinnedX_add, h2, pinnedX_zero]

theorem nWC_mul_xtheta_mul_inv (w : WeylGroup .E7) :
    nWC .E7 (ZMod 2) w * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * (nWC .E7 (ZMod 2) w)⁻¹ =
      pinnedElt .E7 (w • highRoot .E7) (1 : ZMod 2) := by
  obtain ⟨ε, hε, h⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv (ZMod 2) w (isRoot_highRoot .E7)
  have hε1 : ε = 1 := by
    have key : ∀ e : ZMod 2, e * e = 1 → e = 1 := by decide
    exact key ε hε
  refine Subtype.ext ?_
  have h1 := h 1
  rw [hε1, one_mul] at h1
  exact h1

theorem isRootInvol_pinnedElt {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    IsRootInvol (pinnedElt .E7 β (1 : ZMod 2)) := by
  obtain ⟨w, hw⟩ := exists_smul_highRoot_eq (τ := .E7) (Or.inr (Or.inl rfl)) hβ
  show IsConj _ _
  refine isConj_iff.2 ⟨nWC .E7 (ZMod 2) w, ?_⟩
  rw [nWC_mul_xtheta_mul_inv, hw]

theorem isRootInvol_mul_self {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r) :
    r * r = 1 := by
  unfold IsRootInvol at hr
  obtain ⟨c, hc⟩ := isConj_iff.1 hr
  rw [← hc]
  have h := pinnedElt_mul_self (highRoot .E7)
  calc c * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * c⁻¹ *
        (c * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * c⁻¹)
      = c * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) *
          pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * c⁻¹ := by group
    _ = 1 := by rw [h]; simp

theorem isRootInvol_conj {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (g : ↥(adjointGroup .E7 (ZMod 2))) : IsRootInvol (g * r * g⁻¹) := by
  unfold IsRootInvol at hr ⊢
  obtain ⟨c, hc⟩ := isConj_iff.1 hr
  refine isConj_iff.2 ⟨g * c, ?_⟩
  rw [← hc]
  group

theorem nC_eq_prod (i : Fin (Tag.rank .E7)) :
    nC .E7 (ZMod 2) i = pinnedElt .E7 (Pi.single i 1) (1 : ZMod 2) *
      pinnedElt .E7 (-Pi.single i 1) 1 * pinnedElt .E7 (Pi.single i 1) 1 := by
  refine Subtype.ext ?_
  show weylElt .E7 (ZMod 2) i 1 = pinnedX .E7 (ZMod 2) (Pi.single i 1) 1 *
    pinnedX .E7 (ZMod 2) (-Pi.single i 1) 1 * pinnedX .E7 (ZMod 2) (Pi.single i 1) 1
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, pinnedX_single, pinnedX_neg_single]
  simp only [inv_one, Units.val_one]
  have hY : CFSG.Blueprint.Chevalley.yUnit .E7 (ZMod 2) i (-1) =
      CFSG.Blueprint.Chevalley.yUnit .E7 (ZMod 2) i 1 := by
    congr 1
  exact congrArg (fun y => CFSG.Blueprint.Chevalley.xUnit .E7 (ZMod 2) i 1 * y *
    CFSG.Blueprint.Chevalley.xUnit .E7 (ZMod 2) i 1) hY

private theorem one_add_mul_comm_of_mul_comm {R : Type*} [Ring R] {a b : R} (h : a * b = b * a) :
    (1 + a) * (1 + b) = (1 + b) * (1 + a) := by
  have e1 : (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring
  have e2 : (1 + b) * (1 + a) = 1 + b + a + b * a := by noncomm_ring
  rw [e1, e2, h]
  abel

private theorem mul_three_comm_of_involutions {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (h3 : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have hPP : a * b * a * (a * b * a) = 1 := by
    calc a * b * a * (a * b * a) = a * (b * (a * a)) * (b * a) := by simp only [mul_assoc]
      _ = a * (b * 1) * (b * a) := by rw [ha]
      _ = a * (b * b) * a := by simp only [mul_one, mul_assoc]
      _ = a * 1 * a := by rw [hb]
      _ = a * a := by simp only [mul_one]
      _ = 1 := ha
  have hPQ : a * b * a * (b * a * b) = 1 := by
    calc a * b * a * (b * a * b) = (a * b) ^ 3 := by simp only [pow_three', mul_assoc]
      _ = 1 := h3
  exact (mul_left_cancel (hPQ.trans hPP.symm)).symm

theorem dihedral_of_nilpotent {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) (a b : R)
    (ha : a * a = 0) (hb : b * b = 0) (hab : a * b * a = 0) (hba : b * a * b = 0) :
    (1 + a) * (1 + b) * (1 + a) * (1 + b) = (1 + b) * (1 + a) * (1 + b) * (1 + a) := by
  have eL : (1 + a) * (1 + b) * (1 + a) * (1 + b)
      = 1 + (a + a) + (b + b) + (a * b + a * b + a * b) + b * a + a * a + b * b
        + a * b * a + a * (b * b) + a * a * b + b * a * b + a * b * a * b := by
    noncomm_ring
  have eR : (1 + b) * (1 + a) * (1 + b) * (1 + a)
      = 1 + (b + b) + (a + a) + (b * a + b * a + b * a) + a * b + b * b + a * a
        + b * a * b + b * (a * a) + b * b * a + a * b * a + b * a * b * a := by
    noncomm_ring
  have k1 : a + a = 0 := h2 a
  have k2 : b + b = 0 := h2 b
  have k3 : a * b + a * b = 0 := h2 (a * b)
  have k4 : b * a + b * a = 0 := h2 (b * a)
  rw [eL, eR]
  simp only [ha, hb, hab, hba, k1, k2, k3, k4, mul_zero, zero_mul, add_zero, zero_add]
  abel

set_option maxRecDepth 20000 in
theorem pinnedElt_commute {γ δ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (hδ : IsRoot .E7 δ)
    (h0 : γ + δ ≠ 0) (hn : ¬ IsRoot .E7 (γ + δ)) :
    pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 δ 1 = pinnedElt .E7 δ 1 * pinnedElt .E7 γ 1 := by
  obtain ⟨-, hc⟩ := e7Data_valid.pairRel (R := ZMod 2) hγ hδ h0
  apply rep_injective
  intro v
  have hkey : e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) =
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) := by
    simp only [e7Rep56_pinnedElt hγ, e7Rep56_pinnedElt hδ, one_smul]
    exact one_add_mul_comm_of_mul_comm (hc hn)
  rw [map_mul, map_mul, hkey]

set_option maxRecDepth 20000 in
theorem pinnedElt_dihedral {γ δ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hδ : IsRoot .E7 δ) (h0 : γ + δ ≠ 0) (hr : IsRoot .E7 (γ + δ)) :
    pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 δ 1 * pinnedElt .E7 γ 1 * pinnedElt .E7 δ 1 =
      pinnedElt .E7 δ 1 * pinnedElt .E7 γ 1 * pinnedElt .E7 δ 1 * pinnedElt .E7 γ 1 := by
  obtain ⟨hr1, -⟩ := e7Data_valid.pairRel (R := ZMod 2) hγ hδ h0
  obtain ⟨-, hab, hba⟩ := hr1 hr
  have ha := e7Data_valid.rootOp_mul_self (R := ZMod 2) γ
  have hb := e7Data_valid.rootOp_mul_self (R := ZMod 2) δ
  have h2 : ∀ x : Module.End (ZMod 2) (Fin e7Data.d →₀ ZMod 2), x + x = 0 :=
    fun x => ZModModule.add_self x
  have key := dihedral_of_nilpotent h2 (e7Data.rootOp (ZMod 2) γ) (e7Data.rootOp (ZMod 2) δ)
    ha hb hab hba
  apply rep_injective
  intro v
  have hkey : e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) =
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 δ (1 : ZMod 2)) *
      e7Rep56 (ZMod 2) (pinnedElt .E7 γ (1 : ZMod 2)) := by
    simp only [e7Rep56_pinnedElt hγ, e7Rep56_pinnedElt hδ, one_smul]
    exact key
  simp only [map_mul]
  rw [hkey]

theorem pinnedElt_braid {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 (-γ) 1 * pinnedElt .E7 γ 1 =
      pinnedElt .E7 (-γ) 1 * pinnedElt .E7 γ 1 * pinnedElt .E7 (-γ) 1 := by
  have h3 : (pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 (-γ) 1) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (CFSG.RankThree.PartOne.evenH .E7 (ZMod 2) γ)
    rw [CFSG.RankThree.PartOne.orderOf_evenH (K := ZMod 2) hγ] at h
    exact Subtype.ext h
  exact mul_three_comm_of_involutions (pinnedElt_mul_self γ) (pinnedElt_mul_self (-γ)) h3

theorem finsupp_eq_sum_single (u : Fin e7Data.d →₀ ZMod 2) :
    u = ∑ b ∈ u.support, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) := by
  have h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  ext c
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finsupp.mem_support_iff]
  by_cases h : u c = 0
  · simp [h]
  · simp [h, h1 _ h]

theorem rep_mul_apply (g h : ↥(adjointGroup .E7 (ZMod 2))) (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (g * h) v = e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) h v) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_one_apply (v : Fin e7Data.d →₀ ZMod 2) : e7Rep56 (ZMod 2) 1 v = v := by
  rw [map_one]; rfl

theorem rep_inv_apply (g : ↥(adjointGroup .E7 (ZMod 2))) (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) g⁻¹ v) = v := by
  rw [← rep_mul_apply, mul_inv_cancel, rep_one_apply]

theorem rep_inv_apply' (g : ↥(adjointGroup .E7 (ZMod 2))) (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) g⁻¹ (e7Rep56 (ZMod 2) g v) = v := by
  rw [← rep_mul_apply, inv_mul_cancel, rep_one_apply]

theorem rep_conj_sub (g x : ↥(adjointGroup .E7 (ZMod 2))) (c : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (g * x * g⁻¹) c - c =
      e7Rep56 (ZMod 2) g
        (e7Rep56 (ZMod 2) x (e7Rep56 (ZMod 2) g⁻¹ c) - e7Rep56 (ZMod 2) g⁻¹ c) := by
  rw [map_sub, rep_inv_apply, ← rep_mul_apply g x, rep_mul_apply (g * x) g⁻¹ c]

theorem list_prod_conj {G : Type*} [Group G] (g : G) (l : List G) :
    (l.map fun s => g * s * g⁻¹).prod = g * l.prod * g⁻¹ := by
  induction l with
  | nil => simp
  | cons s t ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    group

theorem isRoot_neg {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) : IsRoot .E7 (-β) :=
  CFSG.LieType.Chevalley.IsRoot.neg hβ

theorem isRoot_ne_zero {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) : γ ≠ 0 :=
  forall_root_of_listed (P := fun γ => γ ≠ 0) (by decide +kernel) hγ

end CFSG.GF2Type.SmithTypeE.E8.F
