module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviFrobenius
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

variable {τ : Tag} {K : Type} [Field K]

private theorem exists_eq_zpowers_of_isCyclic' {G : Type*} [Group G] {X : Subgroup G}
    (hX : IsCyclic X) : ∃ x ∈ X, X = Subgroup.zpowers x := by
  obtain ⟨⟨x, hxX⟩, hgen⟩ := IsCyclic.exists_generator (α := X)
  refine ⟨x, hxX, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 hxX)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem zpowers_le_centralizer_zpowers' {G : Type*} [Group G] (x : G) :
    Subgroup.zpowers x ≤ centralizer (Subgroup.zpowers x : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_zpow_self x b a).eq

theorem eq_one_of_mem_center_SL2 [CharP K 2] {B : SL2 K} (hB : B ∈ center (SL2 K)) : B = 1 := by
  obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hB
  rw [Fintype.card_fin] at hr
  refine Subtype.ext ?_
  rw [← hrB, F4Pilot.eq_one_of_sq_eq_one_of_charTwo hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

section RootSL2


theorem rootSL2_highRoot_injective [CharP K 2] : Function.Injective (rootSL2 τ K (highRoot τ)) :=
  (even_Chevalley_pinned_root_SL2_maps τ K (isRoot_highRoot τ)).1

theorem range_rootSL2_highRoot [CharP K 2] :
    (rootSL2 τ K (highRoot τ)).range = EPilot.highRootSL2 τ K :=
  (even_Chevalley_pinned_root_SL2_maps τ K (isRoot_highRoot τ)).2.1

theorem baseChangeGL_rootSL2_highRoot [CharP K 2] {M : Type} [Field M] (f : K →+* M)
    (A : SL2 K) :
    baseChangeGL f (rootSL2 τ K (highRoot τ) A) =
      rootSL2 τ M (highRoot τ) (Matrix.SpecialLinearGroup.map f A) :=
  baseChangeGL_rootSL2_of_charTwo f (isRoot_highRoot τ) A

theorem rootSL2_highRoot_HSL (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2] (c : Kˣ) :
    rootSL2 τ K (highRoot τ) (HSL c) = rootDiagUnit τ (EPilot.highDiag τ c) := by
  obtain ⟨-, -, -, -, -, -, hv, -⟩ := even_Chevalley_pinned_root_SL2_maps τ K (isRoot_highRoot τ)
  obtain ⟨hh, hr⟩ := hv c
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · change (rootTorusSL2 τ K (highRoot τ) c : Module.End K (RootModule τ K)) (hVec τ K j) =
      rootDiag (EPilot.highDiag τ c) (hVec τ K j)
    rw [hh, rootDiag_hVec]
  · change (rootTorusSL2 τ K (highRoot τ) c : Module.End K (RootModule τ K)) (rootVec τ K δ) =
      rootDiag (EPilot.highDiag τ c) (rootVec τ K δ)
    rw [hr δ hδ, rootDiag_rootVec _ hδ, EPilot.rootChar_highDiag, EPilot.iform_highRoot_self hτ,
      EPilot.iform_highRoot hτ]
    congr 3
    omega

theorem rootSL2_highRoot_mem_adjointGroup [CharP K 2] (A : SL2 K) :
    rootSL2 τ K (highRoot τ) A ∈ adjointGroup τ K :=
  EPilot.highRootSL2_le_adjointGroup (by rw [← range_rootSL2_highRoot]; exact ⟨A, rfl⟩)

theorem rootSL2_highRoot_mem_highRootSL2 [CharP K 2] (A : SL2 K) :
    rootSL2 τ K (highRoot τ) A ∈ EPilot.highRootSL2 τ K := by
  rw [← range_rootSL2_highRoot]
  exact ⟨A, rfl⟩

theorem exists_nonsplit_le_highRootSL2 [Finite K] [CharP K 2] :
    ∃ X : Subgroup (ModGL τ K), X ≤ EPilot.highRootSL2 τ K ∧ IsCyclic X ∧
      Nat.card X = Nat.card K + 1 := by
  obtain ⟨A, hA⟩ := F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  refine ⟨Subgroup.zpowers (rootSL2 τ K (highRoot τ) A), ?_, Subgroup.isCyclic_zpowers _, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact rootSL2_highRoot_mem_highRootSL2 A
  · rw [Nat.card_zpowers, orderOf_injective _ rootSL2_highRoot_injective, hA]

theorem exists_nonsplit_le_subgroupOf_highRootSL2 [Finite K] [CharP K 2] :
    ∃ X : Subgroup (adjointGroup τ K),
      X ≤ (EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K) ∧ IsCyclic X ∧
        Nat.card X = Nat.card K + 1 := by
  obtain ⟨A, hA⟩ := F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  refine ⟨Subgroup.zpowers ⟨rootSL2 τ K (highRoot τ) A, rootSL2_highRoot_mem_adjointGroup A⟩, ?_,
    Subgroup.isCyclic_zpowers _, ?_⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact rootSL2_highRoot_mem_highRootSL2 A
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    change orderOf (rootSL2 τ K (highRoot τ) A) = _
    rw [orderOf_injective _ rootSL2_highRoot_injective, hA]

theorem exists_baseChangeGL_eq_of_mem_highRootSL2 [CharP K 2] {M : Type} [Field M]
    (ι : K →+* M) (σ : M →+* M) (hfix : ∀ z : M, σ z = z ↔ z ∈ Set.range ι)
    {j : ModGL τ M} (hj : j ∈ EPilot.highRootSL2 τ M) (hσj : baseChangeGL σ j = j) :
    ∃ y ∈ EPilot.highRootSL2 τ K, baseChangeGL ι y = j := by
  have : CharP M 2 := charP_of_injective_ringHom ι.injective 2
  rw [← range_rootSL2_highRoot] at hj
  obtain ⟨B₂, rfl⟩ := hj
  rw [baseChangeGL_rootSL2_highRoot] at hσj
  obtain ⟨B, hB⟩ :=
    F4Pilot.exists_map_eq_of_map_eq ι σ hfix B₂ (rootSL2_highRoot_injective hσj)
  exact ⟨rootSL2 τ K (highRoot τ) B, rootSL2_highRoot_mem_highRootSL2 B,
    by rw [baseChangeGL_rootSL2_highRoot, hB]⟩

end RootSL2

section Levi


theorem commute_of_mem_highRootSL2_of_mem_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {j d : ModGL τ K} (hj : j ∈ EPilot.highRootSL2 τ K)
    (hd : d ∈ rootSpan τ K (EPilot.perpRoots τ)) : j * d = d * j :=
  Subgroup.mem_centralizer_iff.1 (EPilot.rootSpan_perpRoots_le_centralizer_highRootSL2 hτ hd) j hj

theorem disjoint_highRootSL2_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2] :
    Disjoint (EPilot.highRootSL2 τ K) (rootSpan τ K (EPilot.perpRoots τ)) := by
  rw [Subgroup.disjoint_def]
  intro g hgJ hgD
  rw [← range_rootSL2_highRoot] at hgJ
  obtain ⟨B, rfl⟩ := hgJ
  have hB : B ∈ center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply rootSL2_highRoot_injective
    rw [map_mul, map_mul]
    exact commute_of_mem_highRootSL2_of_mem_perpLevi hτ (rootSL2_highRoot_mem_highRootSL2 A) hgD
  rw [eq_one_of_mem_center_SL2 hB, map_one]

end Levi

@[expose] def PerpLeviFrobDescent
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] : Prop :=
  ∀ d ∈ rootSpan τ (FiniteField.Extension K 2 2) (EPilot.perpRoots τ),
    baseChangeGL (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom d = d →
      ∃ d₀ ∈ rootSpan τ K (EPilot.perpRoots τ),
        baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) d₀ = d

section Nonsplit


theorem exists_mem_zpowers_mul_of_commute_nonsplit_of_descent
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2] (hdesc : PerpLeviFrobDescent τ K)
    {x : ModGL τ K} (hxJ : x ∈ EPilot.highRootSL2 τ K) (hx : orderOf x = Nat.card K + 1)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) (hgx : g * x = x * g) :
    ∃ y ∈ Subgroup.zpowers x, ∃ d ∈ rootSpan τ K (EPilot.perpRoots τ), g = y * d := by
  rw [← range_rootSL2_highRoot] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = Nat.card K + 1 := by
    rw [← hx, orderOf_injective _ rootSL2_highRoot_injective]
  set ι : K →+* FiniteField.Extension K 2 2 := algebraMap K (FiniteField.Extension K 2 2) with hι
  set σ : FiniteField.Extension K 2 2 →+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom with hσ
  have hfix : ∀ z : FiniteField.Extension K 2 2, σ z = z ↔ z ∈ Set.range ι :=
    fun z => F4Pilot.frob_eq_self_iff z
  have hσι : σ.comp ι = ι := RingHom.ext fun a => (FiniteField.Extension.frob K 2 2).commutes a
  have hK₂ : ringChar (FiniteField.Extension K 2 2) = 2 := ringChar.eq _ 2
  obtain ⟨l, P, -, hl1, -, hP⟩ := F4Pilot.exists_inv_mul_map_mul_eq_HSL hA
  have hl3 : 3 ≤ orderOf l := by
    have hl2 : l ^ 2 ≠ 1 := fun h => hl1 (Units.ext (F4Pilot.eq_one_of_sq_eq_one_of_charTwo (by
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one])))
    have hpos : 0 < orderOf l := orderOf_pos l
    by_contra hlt
    have hpow := pow_orderOf_eq_one l
    rcases (show orderOf l = 1 ∨ orderOf l = 2 by omega) with h | h
    · exact hl1 (orderOf_eq_one_iff.1 h)
    · rw [h] at hpow
      exact hl2 hpow
  set n := rootSL2 τ (FiniteField.Extension K 2 2) (highRoot τ) P with hn
  have hnJ : n ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
    rootSL2_highRoot_mem_highRootSL2 P
  have hconj : n⁻¹ * baseChangeGL ι (rootSL2 τ K (highRoot τ) A) * n =
      rootDiagUnit τ (EPilot.highDiag τ l) := by
    rw [baseChangeGL_rootSL2_highRoot, hn, ← map_inv, ← map_mul, ← map_mul, hP,
      rootSL2_highRoot_HSL hτ]
  have hm : n⁻¹ * baseChangeGL ι g * n ∈ toralCentralizer τ (FiniteField.Extension K 2 2)
      (EPilot.highDiag τ l) := by
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem (rootSL2_highRoot_mem_adjointGroup P))
        (baseChangeGL_mem_adjointGroup ι hg)) (rootSL2_highRoot_mem_adjointGroup P)
    · have hgx₂ : baseChangeGL ι g * baseChangeGL ι (rootSL2 τ K (highRoot τ) A) =
          baseChangeGL ι (rootSL2 τ K (highRoot τ) A) * baseChangeGL ι g := by
        rw [← map_mul, hgx, map_mul]
      rw [← hconj]
      calc n⁻¹ * baseChangeGL ι (rootSL2 τ K (highRoot τ) A) * n * (n⁻¹ * baseChangeGL ι g * n) *
            (n⁻¹ * baseChangeGL ι (rootSL2 τ K (highRoot τ) A) * n)⁻¹ =
          n⁻¹ * (baseChangeGL ι (rootSL2 τ K (highRoot τ) A) * baseChangeGL ι g) *
            (baseChangeGL ι (rootSL2 τ K (highRoot τ) A))⁻¹ * n := by group
        _ = n⁻¹ * baseChangeGL ι g * n := by rw [← hgx₂]; group
  rw [(EPilot.toralCentralizer_highDiag_eq_sup hτ hK₂ hl3).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      EPilot.highTorusLine_le_normalizer_perpLevi] at hm
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.1 hm
  set j := n * t * n⁻¹ with hjdef
  have hjJ : j ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
    mul_mem (mul_mem hnJ (EPilot.highTorusLine_le_highRootSL2 hτ ht)) (inv_mem hnJ)
  have hg₂ : baseChangeGL ι g = j * d := by
    have hnd : n * d * n⁻¹ = d := by
      rw [commute_of_mem_highRootSL2_of_mem_perpLevi hτ hnJ hd, mul_inv_cancel_right]
    calc baseChangeGL ι g = n * (n⁻¹ * baseChangeGL ι g * n) * n⁻¹ := by group
      _ = n * (t * d) * n⁻¹ := by rw [htd]
      _ = (n * t * n⁻¹) * (n * d * n⁻¹) := by group
      _ = j * d := by rw [hnd]
  have hσg : baseChangeGL σ (baseChangeGL ι g) = baseChangeGL ι g := by
    rw [F4Pilot.baseChangeGL_baseChangeGL, hσι]
  have hσj : baseChangeGL σ j ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) := by
    rw [← range_rootSL2_highRoot] at hjJ
    obtain ⟨B, hB⟩ := hjJ
    rw [← hB, baseChangeGL_rootSL2_highRoot]
    exact rootSL2_highRoot_mem_highRootSL2 _
  have hσd : baseChangeGL σ d ∈ rootSpan τ (FiniteField.Extension K 2 2) (EPilot.perpRoots τ) :=
    F4Pilot.map_rootSpan_baseChangeGL_le σ _ ⟨d, hd, rfl⟩
  have hjd : baseChangeGL σ j = j ∧ baseChangeGL σ d = d := by
    have h1 : (baseChangeGL σ j)⁻¹ * j = baseChangeGL σ d * d⁻¹ := by
      have h2 : baseChangeGL σ j * baseChangeGL σ d = j * d := by
        rw [← map_mul, ← hg₂, hσg]
      calc (baseChangeGL σ j)⁻¹ * j = (baseChangeGL σ j)⁻¹ * (j * d) * d⁻¹ := by group
        _ = (baseChangeGL σ j)⁻¹ * (baseChangeGL σ j * baseChangeGL σ d) * d⁻¹ := by rw [h2]
        _ = baseChangeGL σ d * d⁻¹ := by group
    have hJ : (baseChangeGL σ j)⁻¹ * j ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
      mul_mem (inv_mem hσj) hjJ
    have hD : (baseChangeGL σ j)⁻¹ * j ∈
        rootSpan τ (FiniteField.Extension K 2 2) (EPilot.perpRoots τ) := by
      rw [h1]
      exact mul_mem hσd (inv_mem hd)
    have h0 := (Subgroup.disjoint_def.1 (disjoint_highRootSL2_perpLevi hτ)) hJ hD
    rw [h0] at h1
    exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩
  obtain ⟨d₀, hd₀D, hd₀⟩ := hdesc d hd hjd.2
  obtain ⟨y, hyJ, hy⟩ := exists_baseChangeGL_eq_of_mem_highRootSL2 ι σ hfix hjJ hjd.1
  have hgyd : g = y * d₀ := baseChangeGL_injective ι (by rw [map_mul, hy, hd₀, hg₂])
  refine ⟨y, ?_, d₀, hd₀D, hgyd⟩
  have hyx : Commute y (rootSL2 τ K (highRoot τ) A) := by
    have hd₀x : Commute (rootSL2 τ K (highRoot τ) A) d₀ :=
      commute_of_mem_highRootSL2_of_mem_perpLevi hτ (rootSL2_highRoot_mem_highRootSL2 A) hd₀D
    rw [show y = g * d₀⁻¹ by rw [hgyd, mul_inv_cancel_right]]
    exact Commute.mul_left hgx hd₀x.symm.inv_left
  rw [← range_rootSL2_highRoot] at hyJ
  obtain ⟨B, rfl⟩ := hyJ
  have hBA : B ∈ Subgroup.centralizer {A} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply rootSL2_highRoot_injective
    rw [map_mul, map_mul]
    exact hyx.eq
  rw [F4Pilot.centralizer_eq_zpowers_of_orderOf_eq hA] at hBA
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hBA
  exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow (rootSL2 τ K (highRoot τ)) A k).symm⟩

theorem adjointGroup_inf_centralizer_nonsplit_of_descent (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] [CharP K 2] (hdesc : PerpLeviFrobDescent τ K) {X : Subgroup (ModGL τ K)}
    (hXJ : X ≤ EPilot.highRootSL2 τ K) (hcyc : IsCyclic X) (hX : Nat.card X = Nat.card K + 1) :
    adjointGroup τ K ⊓ centralizer (X : Set (ModGL τ K)) =
        X ⊔ rootSpan τ K (EPilot.perpRoots τ) ∧
      Disjoint X (rootSpan τ K (EPilot.perpRoots τ)) ∧
      X ≤ centralizer (rootSpan τ K (EPilot.perpRoots τ) : Set (ModGL τ K)) := by
  obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic' hcyc
  have hx : orderOf x = Nat.card K + 1 := by rw [← Nat.card_zpowers, hX]
  have hxJ : x ∈ EPilot.highRootSL2 τ K := hXJ (Subgroup.mem_zpowers x)
  have hXD : Subgroup.zpowers x ≤
      centralizer (rootSpan τ K (EPilot.perpRoots τ) : Set (ModGL τ K)) :=
    hXJ.trans (EPilot.highRootSL2_le_centralizer_perpLevi hτ)
  refine ⟨le_antisymm (fun g hg => ?_)
    (sup_le (le_inf (hXJ.trans EPilot.highRootSL2_le_adjointGroup)
      (zpowers_le_centralizer_zpowers' x)) (le_inf (EPilot.rootSpan_le_adjointGroup' _)
        (Subgroup.le_centralizer_iff.1 hXD))),
    (disjoint_highRootSL2_perpLevi hτ).mono_left hXJ, hXD⟩
  obtain ⟨hgC, hgX⟩ := Subgroup.mem_inf.1 hg
  have hgx : g * x = x * g := (Subgroup.mem_centralizer_iff.1 hgX x (Subgroup.mem_zpowers x)).symm
  obtain ⟨y, hy, d, hd, rfl⟩ :=
    exists_mem_zpowers_mul_of_commute_nonsplit_of_descent hτ hdesc hxJ hx hgC hgx
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hd)

theorem exists_mul_of_mem_centralizer_nonsplit_of_descent (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] [CharP K 2] (hdesc : PerpLeviFrobDescent τ K) {X : Subgroup (adjointGroup τ K)}
    (hXJ : X ≤ (EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) {c : adjointGroup τ K}
    (hc : c ∈ centralizer (X : Set (adjointGroup τ K))) :
    ∃ y ∈ X, ∃ d ∈ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K),
      c = y * d := by
  obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic' hcyc
  have hx : orderOf (x : ModGL τ K) = Nat.card K + 1 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hX]
  have hxJ : (x : ModGL τ K) ∈ EPilot.highRootSL2 τ K := by
    have h := hXJ (Subgroup.mem_zpowers x)
    rwa [Subgroup.mem_subgroupOf] at h
  have hcx : (c : ModGL τ K) * x = x * c :=
    congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc x (Subgroup.mem_zpowers x)).symm
  obtain ⟨y, hy, d, hd, hcyd⟩ :=
    exists_mem_zpowers_mul_of_commute_nonsplit_of_descent hτ hdesc hxJ hx c.2 hcx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨x ^ k, Subgroup.zpow_mem_zpowers x k, ⟨d, EPilot.rootSpan_le_adjointGroup' _ hd⟩,
    Subgroup.mem_subgroupOf.2 hd, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_zpow, hcyd]

theorem commute_of_mem_subgroupOf_highRootSL2_of_mem_subgroupOf_perpLevi
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {y d : adjointGroup τ K}
    (hy : y ∈ (EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K))
    (hd : d ∈ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K)) :
    y * d = d * y :=
  Subtype.ext (commute_of_mem_highRootSL2_of_mem_perpLevi hτ (Subgroup.mem_subgroupOf.1 hy)
    (Subgroup.mem_subgroupOf.1 hd))

theorem centralizer_nonsplit_of_descent (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (hdesc : PerpLeviFrobDescent τ K) {X : Subgroup (adjointGroup τ K)}
    (hXJ : X ≤ (EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) :
    centralizer (X : Set (adjointGroup τ K)) =
        X ⊔ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) ∧
      Disjoint X ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K)) ∧
      X ≤ centralizer
        ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
          Set (adjointGroup τ K)) := by
  have hXD : X ≤ centralizer
      ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Set (adjointGroup τ K)) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      (commute_of_mem_subgroupOf_highRootSL2_of_mem_subgroupOf_perpLevi hτ (hXJ hy) hd).symm
  refine ⟨le_antisymm (fun c hc => ?_) (sup_le ?_ (Subgroup.le_centralizer_iff.1 hXD)), ?_, hXD⟩
  · obtain ⟨y, hy, d, hd, rfl⟩ :=
      exists_mul_of_mem_centralizer_nonsplit_of_descent hτ hdesc hXJ hcyc hX hc
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hd)
  · obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic' hcyc
    exact zpowers_le_centralizer_zpowers' x
  · rw [Subgroup.disjoint_def]
    intro g hgX hgD
    exact Subtype.ext ((Subgroup.disjoint_def.1 (disjoint_highRootSL2_perpLevi hτ))
      (Subgroup.mem_subgroupOf.1 (hXJ hgX)) (Subgroup.mem_subgroupOf.1 hgD))

end Nonsplit

section E6


theorem perpLeviFrobDescent_E6 [Finite K] [CharP K 2] : PerpLeviFrobDescent .E6 K :=
  fun _ hd hσd => exists_baseChangeGL_eq_of_mem_rootSpan_a5LeviRoots_frob hd hσd


theorem exists_mem_zpowers_mul_of_commute_nonsplit_E6 [Finite K] [CharP K 2]
    {x : ModGL .E6 K} (hxJ : x ∈ EPilot.highRootSL2 .E6 K) (hx : orderOf x = Nat.card K + 1)
    {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K) (hgx : g * x = x * g) :
    ∃ y ∈ Subgroup.zpowers x, ∃ d ∈ rootSpan .E6 K a5LeviRoots, g = y * d :=
  exists_mem_zpowers_mul_of_commute_nonsplit_of_descent (Or.inl rfl) perpLeviFrobDescent_E6 hxJ hx
    hg hgx

theorem adjointGroup_inf_centralizer_nonsplit_E6 [Finite K] [CharP K 2]
    {X : Subgroup (ModGL .E6 K)} (hXJ : X ≤ EPilot.highRootSL2 .E6 K)
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    adjointGroup .E6 K ⊓ centralizer (X : Set (ModGL .E6 K)) =
        X ⊔ rootSpan .E6 K a5LeviRoots ∧
      Disjoint X (rootSpan .E6 K a5LeviRoots) ∧
      X ≤ centralizer (rootSpan .E6 K a5LeviRoots : Set (ModGL .E6 K)) :=
  adjointGroup_inf_centralizer_nonsplit_of_descent (Or.inl rfl) perpLeviFrobDescent_E6 hXJ hcyc hX

theorem exists_mul_of_mem_centralizer_nonsplit_E6 [Finite K] [CharP K 2]
    {X : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) {c : adjointGroup .E6 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .E6 K))) :
    ∃ y ∈ X, ∃ d ∈ a5Levi K, c = y * d :=
  exists_mul_of_mem_centralizer_nonsplit_of_descent (Or.inl rfl) perpLeviFrobDescent_E6 hXJ hcyc
    hX hc

theorem centralizer_nonsplit_E6 [Finite K] [CharP K 2] {X : Subgroup (adjointGroup .E6 K)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K))
    (hX : Nat.card X = Nat.card K + 1) (hcyc : IsCyclic X) :
    centralizer (X : Set (adjointGroup .E6 K)) = X ⊔ a5Levi K ∧ Disjoint X (a5Levi K) ∧
      X ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K)) :=
  centralizer_nonsplit_of_descent (Or.inl rfl) perpLeviFrobDescent_E6 hXJ hcyc hX

end E6

end CFSG.SeitzReduction.E6Pilot
