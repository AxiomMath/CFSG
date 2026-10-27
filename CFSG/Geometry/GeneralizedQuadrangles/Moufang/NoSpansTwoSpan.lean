module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Geometry.GeneralizedQuadrangles.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

public theorem noSpansTwoSpanContradiction
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hs2 : 2 ≤ s)
    {p L0 L1 M0 M1 z0 z1 y : V}
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2)
    (hL0 : Γ.Adj p L0) (hL1 : Γ.Adj p L1) (hL10' : L0 ≠ L1) (hcL1 : c L1 = 1)
    (hz0L0 : Γ.Adj L0 z0) (hz0M0 : Γ.Adj z0 M0) (hM0ne : M0 ≠ L0)
    (hz1L1 : Γ.Adj L1 z1) (hz1M1 : Γ.Adj z1 M1) (hM1ne : M1 ≠ L1)
    (hyM0 : Γ.Adj y M0) (hyM1 : Γ.Adj y M1)
    (hM01 : M0 ≠ M1) (hM1L0 : M1 ≠ L0) (hM0L1 : M0 ≠ L1)
    (hL1M0_4 : Γ.dist L1 M0 = 4)
    (E : Subgroup H)
    (hE_fixL0 : ∀ e : H, e ∈ E → e • L0 = L0)
    (hE_fixL1 : ∀ e : H, e ∈ E → e • L1 = L1)
    (hS0_inter_S1 : (E ⊓ MulAction.stabilizer H M0) ⊓
      (E ⊓ MulAction.stabilizer H M1) = ⊥)
    (hS0_card : Nat.card ↥(E ⊓ MulAction.stabilizer H M0) = s)
    (hS1_card : Nat.card ↥(E ⊓ MulAction.stabilizer H M1) = s)
    (hprod_comm : (((E ⊓ MulAction.stabilizer H M1 : Subgroup H) : Set H) *
      ((E ⊓ MulAction.stabilizer H M0 : Subgroup H) : Set H)) =
      (((E ⊓ MulAction.stabilizer H M0 : Subgroup H) : Set H) *
      ((E ⊓ MulAction.stabilizer H M1 : Subgroup H) : Set H))) :
    False := by
  classical
  let S0 : Subgroup H := E ⊓ MulAction.stabilizer H M0
  let S1 : Subgroup H := E ⊓ MulAction.stabilizer H M1
  have htrace_card : (traceSet Γ L1 M0).ncard = s + 1 := by
    rw [ncard_trace hP hL1M0_4, hdeg L1, if_neg (by rw [hcL1]; decide)]
  have hL0_mem_trace : L0 ∈ traceSet Γ L1 M0 := by
    refine ⟨?_, ?_⟩
    · exact dist_eq_two_of_adj_of_adj_of_ne hP hL1.symm hL0 hL10'.symm
    · exact dist_eq_two_of_adj_of_adj_of_ne hP hz0M0.symm hz0L0.symm hM0ne
  have hSM1_mem_trace : ∀ σ : H, σ ∈ S0 → σ • M1 ∈ traceSet Γ L1 M0 := by
    intro σ hσ
    have hσE : σ ∈ E := (Subgroup.mem_inf.mp hσ).1
    have hσM : σ • M0 = M0 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hσ).2)
    have hσL1 : σ • L1 = L1 := hE_fixL1 σ hσE
    constructor
    · have hadj : Γ.Adj (σ • M1) (σ • z1) :=
        ((GraphAction.adj_smul σ z1 M1).mpr hz1M1).symm
      have hz1L1' : Γ.Adj (σ • z1) L1 := by
        have h := (GraphAction.adj_smul σ z1 L1).mpr hz1L1.symm
        rw [hσL1] at h
        exact h
      have hne : σ • M1 ≠ L1 := by
        intro hh
        have h2' : M1 = (σ : H)⁻¹ • L1 := by
          have h := congrArg (fun X => (σ : H)⁻¹ • X) hh
          simpa using h
        have h3 : (σ : H)⁻¹ • L1 = L1 := hE_fixL1 σ⁻¹ (E.inv_mem hσE)
        rw [h3] at h2'
        exact hM1ne h2'
      have hd := dist_eq_two_of_adj_of_adj_of_ne (x := σ • M1) (y := L1) (L := σ • z1)
        hP hadj hz1L1' hne
      rwa [SimpleGraph.dist_comm]
    · have hadj : Γ.Adj (σ • M1) (σ • y) :=
        ((GraphAction.adj_smul σ y M1).mpr hyM1).symm
      have hyM0' : Γ.Adj (σ • y) M0 := by
        have h := (GraphAction.adj_smul σ y M0).mpr hyM0
        rw [hσM] at h
        exact h
      have hne : σ • M1 ≠ M0 := by
        intro hh
        have h2' : M1 = (σ : H)⁻¹ • M0 := by
          have h := congrArg (fun X => (σ : H)⁻¹ • X) hh
          simpa using h
        have h3 : (σ : H)⁻¹ • M0 = M0 := by
          have h := congrArg (fun X => (σ : H)⁻¹ • X) hσM
          simpa using h.symm
        rw [h3] at h2'
        exact hM01 h2'.symm
      have hd := dist_eq_two_of_adj_of_adj_of_ne (x := σ • M1) (y := M0) (L := σ • y)
        hP hadj hyM0' hne
      rwa [SimpleGraph.dist_comm]
  have hspan_of_tau : ∀ τ : H, τ ∈ S1 → τ • M0 ∈ spanSet Γ L1 M0 := by
    intro τ hτ
    have hτE : τ ∈ E := (Subgroup.mem_inf.mp hτ).1
    have hτL0 : τ • L0 = L0 := hE_fixL0 τ hτE
    have hτL1 : τ • L1 = L1 := hE_fixL1 τ hτE
    let fτ : ↥S0 → V := fun σ => (σ : H) • M1
    have himg_trace : insert L0 (fτ '' Set.univ) = traceSet Γ L1 M0 := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with hx | hx
        · rw [hx]; exact hL0_mem_trace
        · rcases hx with ⟨σ, -, hσx⟩
          rw [← hσx]
          exact hSM1_mem_trace σ σ.2
      · rw [htrace_card]
        have hinj : Function.Injective fτ := by
          intro a b hab
          have hab' : (a : H) • M1 = (b : H) • M1 := hab
          have hmem : (a : H)⁻¹ * (b : H) ∈ S0 ⊓ S1 := by
            refine ⟨S0.mul_mem (S0.inv_mem a.2) b.2, ?_⟩
            have h : (a : H)⁻¹ • ((a : H) • M1) = (a : H)⁻¹ • ((b : H) • M1) := by rw [hab']
            have h' : M1 = ((a : H)⁻¹ * (b : H)) • M1 := by
              simpa [mul_smul] using h
            refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · exact E.mul_mem (E.inv_mem (Subgroup.mem_inf.mp a.2).1) (Subgroup.mem_inf.mp b.2).1
            · exact MulAction.mem_stabilizer_iff.mpr h'.symm
          rw [hS0_inter_S1] at hmem
          have h1' : (a : H)⁻¹ * (b : H) = 1 := Subgroup.mem_bot.mp hmem
          have h2' : (b : H) = (a : H) := by
            calc (b : H) = (a : H) * ((a : H)⁻¹ * (b : H)) := by group
              _ = (a : H) := by rw [h1', mul_one]
          exact Subtype.ext h2'.symm
        have hL0_notin : L0 ∉ fτ '' Set.univ := by
          rintro ⟨σ, -, hσ⟩
          change (σ : H) • M1 = L0 at hσ
          have h2' : M1 = (σ : H)⁻¹ • L0 := by
            have h := congrArg (fun X => (σ : H)⁻¹ • X) hσ
            simpa using h
          have h3 : (σ : H)⁻¹ • L0 = L0 := hE_fixL0 σ⁻¹ (E.inv_mem (Subgroup.mem_inf.mp σ.2).1)
          rw [h3] at h2'
          exact hM1L0 h2'
        have himg_card : (fτ '' Set.univ).ncard = s := by
          rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
          exact hS0_card
        rw [Set.ncard_insert_of_notMem hL0_notin, himg_card]
    intro w hw
    rw [← himg_trace] at hw
    rcases Set.mem_insert_iff.mp hw with hw | hw
    · rw [hw]
      have h1' : Γ.dist (τ • M0) (τ • z0) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((GraphAction.adj_smul τ z0 M0).mpr hz0M0).symm
      have h2' : Γ.dist (τ • z0) L0 = 1 := by
        refine SimpleGraph.dist_eq_one_iff_adj.mpr ?_
        have h := (GraphAction.adj_smul τ z0 L0).mpr hz0L0.symm
        rw [hτL0] at h
        exact h
      have htri := hP.connected.dist_triangle (u := τ • M0) (v := τ • z0) (w := L0)
      omega
    · rcases hw with ⟨σ, hσ, hσw⟩
      rw [← hσw]
      change Γ.dist (τ • M0) ((σ : H) • M1) ≤ 2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp
        (hprod_comm ▸ Set.mul_mem_mul (S1.inv_mem hτ) σ.2)
      have hσeq : (σ : H) = τ * a * b := by
        calc (σ : H) = τ * (τ⁻¹ * (σ : H)) := by group
          _ = τ * (a * b) := by rw [← hab]
          _ = τ * a * b := by group
      have haM : Γ.Adj ((a : H) • y) M0 := by
        have h := (GraphAction.adj_smul (a : H) y M0).mpr hyM0
        have haM0 : (a : H) • M0 = M0 := by
          simpa using (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp ha).2)
        rwa [haM0] at h
      have hadj1 : Γ.Adj (τ • M0) (τ • ((a : H) • y)) :=
        ((GraphAction.adj_smul τ ((a : H) • y) M0).mpr haM).symm
      have hbM : Γ.Adj ((b : H)⁻¹ • y) M1 := by
        have h := (GraphAction.adj_smul (b : H)⁻¹ y M1).mpr hyM1
        have hbM1 : (b : H)⁻¹ • M1 = M1 := by
          simpa using (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (S1.inv_mem hb)).2)
        rwa [hbM1] at h
      have hx_eq : τ • ((a : H) • y) = (σ : H) • ((b : H)⁻¹ • y) := by
        calc τ • ((a : H) • y) = (τ * (a : H)) • y := by rw [← mul_smul]
          _ = (σ * (b : H)⁻¹) • y := by
              have h : τ * (a : H) = σ * (b : H)⁻¹ := by rw [hσeq]; group
              rw [h]
          _ = (σ : H) • ((b : H)⁻¹ • y) := by rw [mul_smul]
      have hadj2 : Γ.Adj ((σ : H) • M1) (τ • ((a : H) • y)) := by
        have h := (GraphAction.adj_smul (σ : H) ((b : H)⁻¹ • y) M1).mpr hbM
        have h' : (σ : H) • ((b : H)⁻¹ • y) = τ • ((a : H) • y) := hx_eq.symm
        rw [h'] at h
        exact h.symm
      have h1' : Γ.dist (τ • M0) (τ • ((a : H) • y)) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj1
      have h2' : Γ.dist (τ • ((a : H) • y)) ((σ : H) • M1) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj2.symm
      have htri := hP.connected.dist_triangle (u := τ • M0) (v := τ • ((a : H) • y))
        (w := (σ : H) • M1)
      omega
  have hspan_card : s + 1 ≤ (spanSet Γ L1 M0).ncard := by
    let g : ↥S1 → V := fun τ => (τ : H) • M0
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : (a : H) • M0 = (b : H) • M0 := hab
      have hmem : (a : H)⁻¹ * (b : H) ∈ S1 ⊓ S0 := by
        refine ⟨S1.mul_mem (S1.inv_mem a.2) b.2, ?_⟩
        have h : (a : H)⁻¹ • ((a : H) • M0) = (a : H)⁻¹ • ((b : H) • M0) := by rw [hab']
        have h' : M0 = ((a : H)⁻¹ * (b : H)) • M0 := by
          simpa [mul_smul] using h
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact E.mul_mem (E.inv_mem (Subgroup.mem_inf.mp a.2).1) (Subgroup.mem_inf.mp b.2).1
        · exact MulAction.mem_stabilizer_iff.mpr h'.symm
      rw [inf_comm, hS0_inter_S1] at hmem
      have h1' : (a : H)⁻¹ * (b : H) = 1 := Subgroup.mem_bot.mp hmem
      have h2' : (b : H) = (a : H) := by
        calc (b : H) = (a : H) * ((a : H)⁻¹ * (b : H)) := by group
          _ = (a : H) := by rw [h1', mul_one]
      exact Subtype.ext h2'.symm
    have hL1_notin : L1 ∉ g '' Set.univ := by
      rintro ⟨τ, -, hτ⟩
      change (τ : H) • M0 = L1 at hτ
      have h2' : M0 = (τ : H)⁻¹ • L1 := by
        have h := congrArg (fun X => (τ : H)⁻¹ • X) hτ
        simpa using h
      have h3 : (τ : H)⁻¹ • L1 = L1 := hE_fixL1 τ⁻¹ (E.inv_mem (Subgroup.mem_inf.mp τ.2).1)
      rw [h3] at h2'
      exact hM0L1 h2'
    have himg_card : (g '' Set.univ).ncard = s := by
      rw [Set.ncard_image_of_injective _ hginj, Set.ncard_univ]
      exact hS1_card
    have hT'card : (insert L1 (g '' Set.univ)).ncard = s + 1 := by
      rw [Set.ncard_insert_of_notMem hL1_notin, himg_card]
    have hT'sub : insert L1 (g '' Set.univ) ⊆ spanSet Γ L1 M0 := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · rw [hx]; exact left_mem_spanSet hL1M0_4
      · rcases hx with ⟨τ, -, hτx⟩
        rw [← hτx]
        exact hspan_of_tau τ τ.2
    have hle := Set.ncard_le_ncard hT'sub (Set.toFinite _)
    rwa [hT'card] at hle
  have hlinespan := h2 L1 M0 hL1 hL1M0_4
  omega


end CFSG.Geometry.GeneralizedQuadrangles
