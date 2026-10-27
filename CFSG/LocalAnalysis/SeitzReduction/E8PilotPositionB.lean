module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def e8PosXCoverB : Bool :=
  Tag.E8.rootCertificate.roots.all fun c =>
    (!decide (0 < decodeVec (τ := .E8) c (highNode .E8)) ||
        oddDerivMemB (decodeVec c) (e8PosXDeriv.map Prod.fst)) &&
      (!decide (decodeVec (τ := .E8) c (highNode .E8) = 0) ||
        oddDerivMemB (decodeVec c) e8PosXPerp)

theorem e8PosXCoverB_eq_true : e8PosXCoverB = true := by
  decide +kernel


theorem mem_e8PosX_of_isRoot {α : Fin (Tag.rank .E8) → ℤ} (hα : IsRoot .E8 α) :
    (0 < α (highNode .E8) → α ∈ e8PosXDeriv.map Prod.fst) ∧
      (α (highNode .E8) = 0 → α ∈ e8PosXPerp) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E8.rootCertificate_check hα
  have h1 := List.all_eq_true.1 e8PosXCoverB_eq_true _
    (List.getElem_mem (l := Tag.E8.rootCertificate.roots) hk)
  rw [← List.getD_eq_getElem _ 0 hk] at h1
  have e : Tag.E8.rootCertificate.root k =
      decodeVec (Tag.E8.rootCertificate.roots.getD k 0) := rfl
  rw [← e] at h1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h1
  obtain ⟨h1a, h1b⟩ := h1
  refine ⟨fun hpos => ?_, fun hzero => ?_⟩
  · rcases h1a with h | h
    · exact absurd hpos h
    · exact mem_of_oddDerivMemB h
  · rcases h1b with h | h
    · exact absurd hzero h
    · exact mem_of_oddDerivMemB h

variable {K : Type} [Field K]

theorem centralizer_pinnedX_highRoot_inf_eq_e8PosXSpan :
    centralizer ({pinnedX .E8 K (highRoot .E8) 1} : Set (ModGL .E8 K)) ⊓ adjointGroup .E8 K =
      e8PosXSpan K := by
  refine le_antisymm ?_ (le_inf e8PosXSpan_le_centralizer
    (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α))
  rw [EPilot.centralizer_pinnedX_highRoot_inf_eq (Or.inr (Or.inr rfl)) one_ne_zero]
  have hgen : ∀ α, α ∈ e8PosXDeriv.map Prod.fst ∨ α ∈ e8PosXPerp →
      rootSubgroup .E8 K α ≤ e8PosXSpan K := fun α hα =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ e8PosXDeriv.map Prod.fst ∨ γ ∈ e8PosXPerp}) =>
      rootSubgroup .E8 K δ) α hα le_rfl
  refine sup_le (iSup₂_le fun α hα => hgen α (Or.inl ?_)) (iSup₂_le fun α hα => hgen α (Or.inr ?_))
  · obtain ⟨hr, hpos⟩ := EPilot.mem_parabolicRadicalRoots_perpNodes.1 hα
    exact (mem_e8PosX_of_isRoot hr).1 hpos
  · exact (mem_e8PosX_of_isRoot hα.1).2 hα.2

theorem map_conj_centralizer_singleton {G : Type*} [Group G] (n x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * x * n⁻¹} : Set G) := by
  ext g
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * (n * x * n⁻¹) = n * (n⁻¹ * g * n * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * g * n)) * n⁻¹ := by rw [h]
      _ = n * x * n⁻¹ * g := by group
  · intro h
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹ * g) * n := by rw [h]
      _ = x * (n⁻¹ * g * n) := by group

theorem commutator_centralizer_pinnedElt_highRoot_E8 [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)),
        centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} :
          Set (adjointGroup .E8 K))⁆ =
      centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) := by
  have hsub : e8PosXSpan K ≤ adjointGroup .E8 K := iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have h : centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} :
      Set (adjointGroup .E8 K)) = (e8PosXSpan K).subgroupOf (adjointGroup .E8 K) := by
    rw [F4Pilot.centralizer_eq_subgroupOf]
    exact congrArg (fun H => H.subgroupOf (adjointGroup .E8 K))
      centralizer_pinnedX_highRoot_inf_eq_e8PosXSpan
  rw [h]
  exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self hsub (commutator_e8PosXSpan hq)

variable (K) in
@[expose] noncomputable def posJE8 : Subgroup (adjointGroup .E8 K) :=
  (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K)

@[expose] def rootXE8 : Fin (Tag.rank .E8) → ℤ := Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E8)) 1

theorem isRoot_rootXE8 : IsRoot .E8 rootXE8 := isRoot_single .E8 _

theorem rootXE8_mem_perpRoots : rootXE8 ∈ EPilot.perpRoots .E8 :=
  EPilot.single_mem_perpRoots (by decide)

variable (K) in
@[expose] noncomputable def repXE8 : adjointGroup .E8 K := EPilot.pinnedElt .E8 rootXE8 (1 : K)

variable (K) in
@[expose] noncomputable def xLeviE8 : Subgroup (adjointGroup .E8 K) :=
  EPilot.rootPerpLevi .E8 K rootXE8

variable (K) in
@[expose] noncomputable def xRadicalE8 : Subgroup (adjointGroup .E8 K) :=
  EPilot.rootRadical .E8 K rootXE8

theorem repXE8_mem_e7Levi : repXE8 K ∈ e7Levi K :=
  EPilot.pinnedElt_mem_perpLevi rootXE8_mem_perpRoots 1

theorem repXE8_ne_one : repXE8 K ≠ 1 := by
  intro h
  have h1 : pinnedX .E8 K rootXE8 1 = pinnedX .E8 K rootXE8 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (pinnedX_injective .E8 K _ h1)

theorem isTwoRadicalDecomp_repXE8 [Finite K] [CharP K 2] :
    F4Pilot.IsTwoRadicalDecomp (repXE8 K) (xRadicalE8 K) (xLeviE8 K) :=
  EPilot.isTwoRadicalDecomp_root (Or.inr (Or.inr rfl)) isRoot_rootXE8 one_ne_zero

theorem posJE8_le_xLeviE8 : posJE8 K ≤ xLeviE8 K :=
  EPilot.highRootSL2_subgroupOf_le_rootPerpLevi (Or.inr (Or.inr rfl)) rootXE8_mem_perpRoots

theorem exists_conj_pinnedElt_highRoot_eq_repXE8 [CharP K 2] :
    ∃ n : adjointGroup .E8 K,
      n * EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) * n⁻¹ = repXE8 K :=
  exists_conj_pinnedElt_highRoot_eq (Or.inr (Or.inr rfl)) isRoot_rootXE8

theorem commutator_centralizer_repXE8 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({repXE8 K} : Set (adjointGroup .E8 K)),
        centralizer ({repXE8 K} : Set (adjointGroup .E8 K))⁆ =
      centralizer ({repXE8 K} : Set (adjointGroup .E8 K)) := by
  obtain ⟨n, hn⟩ := exists_conj_pinnedElt_highRoot_eq_repXE8 (K := K)
  rw [← hn, ← map_conj_centralizer_singleton, ← map_commutator,
    commutator_centralizer_pinnedElt_highRoot_E8 hq]

theorem exists_xLeviE8_eq_map :
    ∃ c : adjointGroup .E8 K, xLeviE8 K = (e7Levi K).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inr rfl)) isRoot_rootXE8
  refine ⟨⟨canonicalRep (coxeterSystem .E8) K w, canonicalRep_mem_adjointGroup _ K w⟩, ?_⟩
  rw [xLeviE8, EPilot.rootPerpLevi, ← hw,
    ← EPilot.map_conj_rootSpan_perpRoots (Or.inr (Or.inr rfl)) w, e7Levi,
    CFSG.LieType.Chevalley.map_conj_subgroupOf (EPilot.rootSpan_le_adjointGroup' _)]

theorem isSimpleGroup_xLeviE8 [Finite K] [CharP K 2] : IsSimpleGroup (xLeviE8 K) := by
  obtain ⟨c, hc⟩ := exists_xLeviE8_eq_map (K := K)
  have := isSimpleGroup_e7Levi (K := K)
  exact ((MulEquiv.subgroupCongr hc).trans
    ((e7Levi K).equivMapOfInjective _ (MulAut.conj c).injective).symm).isSimpleGroup

theorem forall_normal_isPGroup_eq_bot_xLeviE8 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (N : Subgroup (xLeviE8 K)) (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, hQM, -, hMN⟩ := isTwoRadicalDecomp_repXE8 (K := K)
  exact EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup_of_perfect hQ hMN
    isSimpleGroup_xLeviE8 (by rw [hQM]; exact commutator_centralizer_repXE8 hq) N hN hN2

variable (K) in
@[expose] def FactF5E8 : Prop :=
  ∀ ι : xLeviE8 K ≃* xLeviE8 K, ∃ c : adjointGroup .E8 K,
    (((posJE8 K).subgroupOf (xLeviE8 K)).map ι.toMonoidHom).map (xLeviE8 K).subtype =
      (posJE8 K).map (MulAut.conj c).toMonoidHom

variable (K) in
@[expose] def FactF56E8 : Prop :=
  ∀ ι : xLeviE8 K ≃* xLeviE8 K, Nonempty (centralizer
    (((((posJE8 K).subgroupOf (xLeviE8 K)).map ι.toMonoidHom).map (xLeviE8 K).subtype :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) ≃* e7Levi K)

theorem nonempty_centralizer_map_conj_posJE8_mulEquiv [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (c : adjointGroup .E8 K) :
    Nonempty (centralizer (((posJE8 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) ≃* e7Levi K) := by
  have hcen : centralizer (((posJE8 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) =
        (e7Levi K).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c) (posJE8 K), posJE8,
      EPilot.centralizer_highRootSL2_subgroupOf (Or.inr (Or.inr rfl)) hq]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((e7Levi K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem factF56E8_of_factF5E8 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (h : FactF5E8 K) :
    FactF56E8 K := by
  intro ι
  obtain ⟨c, hc⟩ := h ι
  rw [hc]
  exact nonempty_centralizer_map_conj_posJE8_mulEquiv hq c

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_E8 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .E8 K)
    (hF56 : FactF56E8 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm (repXE8 K) : G)} : Set G) ∧
      Nonempty (P ≃* e7Levi K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ : Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 := Or.inr (Or.inr rfl)
  set φ : adjointGroup .E8 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hperf : ⁅centralizer ({repXE8 K} : Set (adjointGroup .E8 K)),
      centralizer ({repXE8 K} : Set (adjointGroup .E8 K))⁆ =
        centralizer ({repXE8 K} : Set (adjointGroup .E8 K)) := commutator_centralizer_repXE8 hq
  obtain ⟨U, hU⟩ := hzU
  set zC : adjointGroup .E8 K := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := by
    intro h
    apply hz1
    rw [← hφz, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .E8 K) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .E8 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hzCU : zC ∈ centralizer ((UC : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨c, hc⟩ :=
    exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE8 UC hzCU hzC1
  set y : G := φ (repXE8 K) with hydef
  have hyL : y ∈ L := hφr ▸ ⟨repXE8 K, rfl⟩
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, repXE8, ← hc, map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := mem_centralizer_singleton_iff.1 (hLt hcL)
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]
  set Λ := (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ with hΛdef
  have hΛeq : Λ = L ⊓ centralizer ({y} : Set G) := by
    rw [hΛdef, F4Pilot.map_centralizer_singleton hφ, hφr]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛdef, ← map_commutator, hperf]
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛeq ▸ inf_le_left.trans hLt
  have hΛy : Λ ≤ centralizer ({y} : Set G) := hΛeq ▸ inf_le_right
  have hΛt' : Λ ≤ centralizer ({g₁⁻¹ * t * g₁} : Set G) := by
    rw [hg₁]
    exact fun x hx => F4Pilot.mem_centralizer_singleton_mul (hΛt hx) (hΛy hx)
  have hΛL' : Λ ≤ L ⊓ CFSG.conjugate L g₁ :=
    std_perfect_le_inf_conjugate hset hOut htC ht g₁ hΛperf hΛt hΛt'
  set φ'₀ : adjointGroup .E8 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (adjointGroup .E8 K)).map (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * repXE8 K = repXE8 K * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := mem_centralizer_iff.1 hzCU u hu
    rw [repXE8, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * u * c⁻¹ * (c * zC * c⁻¹) = c * (u * zC) * c⁻¹ := by group
      _ = c * (zC * u) * c⁻¹ := by rw [h]
      _ = c * zC * c⁻¹ * (c * u * c⁻¹) := by group
  set U₀ := W₁.map φ with hU₀def
  have hU₀Λ : U₀ ≤ Λ := by
    rw [hΛeq]
    rintro _ ⟨a, ha, rfl⟩
    refine mem_inf.2 ⟨hφr ▸ ⟨a, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hydef, ← map_mul, ← map_mul, hW₁y a ha]
  have hU₀L' : U₀ ≤ φ'₀.range := hφ'₀r ▸ hU₀Λ.trans (hΛL'.trans inf_le_right)
  set W := U₀.comap φ'₀ with hWdef
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (adjointGroup .E8 K)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k, hk⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk)
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (adjointGroup .E8 K)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (adjointGroup .E8 K)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (adjointGroup .E8 K)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (adjointGroup .E8 K) := hWp.toSylow hWidx with hWS
  have hwW : w ∈ centralizer ((WS : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw1 : w ≠ 1 := by
    intro h
    apply repXE8_ne_one (K := K)
    apply hφ
    rw [map_one, ← hydef, ← hw, h, map_one]
  obtain ⟨c', hc'⟩ := exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE8 WS hwW hw1
  set φ' : adjointGroup .E8 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' (repXE8 K) = y := by
    rw [hφ'def, MonoidHom.comp_apply, repXE8, ← hc', ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ =
      (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' := by
    have hR : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [F4Pilot.map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ',
          (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ'⁆ =
          (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' := by
        rw [← map_commutator, hperf]
      have ht' : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' ≤
          centralizer ({t} : Set G) := by
        rw [hR]
        intro x hx
        have h1 := F4Pilot.conjugate_le_centralizer htC g₁ hx.1
        rw [hg₁] at h1
        exact F4Pilot.mem_centralizer_singleton_of_mul h1 hx.2
      have hle := std_perfect_le hset hOut htC ht hperf' ht'
      rw [hR] at hle
      rw [hΛeq]
      exact fun x hx => ⟨hle hx, hx.2⟩
  obtain ⟨hQ, hQM, hQMb, hMN⟩ := isTwoRadicalDecomp_repXE8 (K := K)
  have hQMd : Disjoint (xRadicalE8 K) (xLeviE8 K) := disjoint_iff.2 hQMb
  have hΛQM : (xRadicalE8 K ⊔ xLeviE8 K).map φ = (xRadicalE8 K ⊔ xLeviE8 K).map φ' := by
    rw [hQM]
    exact hΛ'
  have hXJ' : X ≤ (posJE8 K).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_two_decompositions
    hφ hφ' hQ hQ (forall_normal_isPGroup_eq_bot_xLeviE8 hq)
    (forall_normal_isPGroup_eq_bot_xLeviE8 hq) hMN hMN hQMd hQMd hΛQM posJE8_le_xLeviE8 hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := hF56 ι
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ F4Pilot.conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

end CFSG.SeitzReduction.E8Pilot
