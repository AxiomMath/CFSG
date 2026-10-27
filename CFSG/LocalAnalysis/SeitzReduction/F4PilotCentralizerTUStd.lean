module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToral
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerVBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped Pointwise

local instance f4CentralizerTUStdNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem centralizer_eq_subgroupOf {G : Type*} [Group G] {C : Subgroup G} (z : C) :
    centralizer ({z} : Set C) = (centralizer ({(z : G)} : Set G) ⊓ C).subgroupOf C := by
  ext g
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, mem_subgroupOf, mem_inf,
    g.2, and_true]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem decomp_subgroupOf {G : Type*} [Group G] {C Q M : Subgroup G} (hQC : Q ≤ C) (hMC : M ≤ C)
    (z : C) (h1 : centralizer ({(z : G)} : Set G) ⊓ C = Q ⊔ M) (h2 : Q ⊓ M = ⊥)
    (h3 : M ≤ normalizer (Q : Set G)) :
    Q.subgroupOf C ⊔ M.subgroupOf C = centralizer ({z} : Set C) ∧
      Q.subgroupOf C ⊓ M.subgroupOf C = ⊥ ∧
      M.subgroupOf C ≤ normalizer (Q.subgroupOf C : Set C) := by
  refine ⟨by rw [centralizer_eq_subgroupOf, h1, subgroupOf_sup hQC hMC], ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxM⟩ := mem_inf.1 hx
    have h := mem_inf.2 ⟨mem_subgroupOf.1 hxQ, mem_subgroupOf.1 hxM⟩
    rw [h2, mem_bot] at h
    exact (mem_bot).2 (Subtype.ext h)
  · intro m hm
    rw [mem_normalizer_iff]
    intro y
    have hmN := mem_normalizer_iff.1 (h3 (mem_subgroupOf.1 hm)) (y : G)
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact hmN

theorem isPGroup_subgroupOf_of_le {G : Type*} [Group G] {C Q : Subgroup G} {p : ℕ} (hQC : Q ≤ C)
    (hQ : IsPGroup p Q) : IsPGroup p (Q.subgroupOf C) :=
  hQ.of_equiv (subgroupOfEquivOfLe hQC).symm

@[expose] def nodesT : Set (Fin (Tag.rank .F4)) := {j | j ≠ 0}

@[expose] def nodesTU : Set (Fin (Tag.rank .F4)) := {j | j ≠ 0 ∧ j ≠ 3}

theorem parabolicRoots_nodesT : parabolicRoots .F4 nodesT = c3LeviRoots := by
  ext γ
  simp only [parabolicRoots, nodesT, c3LeviRoots, Set.mem_ofPred_eq, ne_eq, not_not, forall_eq]
  rfl

@[expose] def b2LeviRoots : Set (Fin (Tag.rank .F4) → ℤ) := parabolicRoots .F4 nodesTU

theorem mem_b2LeviRoots {γ : Fin (Tag.rank .F4) → ℤ} :
    γ ∈ b2LeviRoots ↔ IsRoot .F4 γ ∧ γ 0 = 0 ∧ γ 3 = 0 := by
  simp only [b2LeviRoots, parabolicRoots, nodesTU, Set.mem_ofPred_eq, ne_eq, not_and_or, not_not]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, h' 0 (Or.inl rfl), h' 3 (Or.inr rfl)⟩
  · rintro ⟨h, h0, h3⟩
    refine ⟨h, fun i hi => ?_⟩
    rcases hi with rfl | rfl
    · exact h0
    · exact h3

theorem b2LeviRoots_subset_c3LeviRoots : b2LeviRoots ⊆ c3LeviRoots := fun _ hγ =>
  ⟨(mem_b2LeviRoots.1 hγ).1, (mem_b2LeviRoots.1 hγ).2.1⟩

theorem b2LeviRoots_subset_b3LeviRoots : b2LeviRoots ⊆ b3LeviRoots := fun _ hγ =>
  ⟨(mem_b2LeviRoots.1 hγ).1, (mem_b2LeviRoots.1 hγ).2.2⟩

section Weyl


theorem smul_apply_zero_eq_of_smul_rootR {w : WeylGroup .F4} (hw : w • rootR = rootR)
    (v : Fin (Tag.rank .F4) → ℤ) : (w • v) 0 = v 0 := by
  have h := iform_smul w rootR v
  rw [hw, iform_rootR, iform_rootR] at h
  omega

theorem smul_apply_three_eq_of_smul_rootS {w : WeylGroup .F4} (hw : w • rootS = rootS)
    (v : Fin (Tag.rank .F4) → ℤ) : (w • v) 3 = v 3 := by
  have h := iform_smul w rootS v
  rwa [hw, iform_rootS, iform_rootS] at h

theorem mem_parabolicWeylGroup_nodesT {w : WeylGroup .F4} (hw : w • rootR = rootR) :
    w ∈ parabolicWeylGroup .F4 nodesT := by
  have h : w ∈ (parabolicWeylGroup .F4 nodesT : Set (WeylGroup .F4)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer .F4 nodesT).1]
    intro v i hi
    have hi0 : i = 0 := by simpa [nodesT] using hi
    subst hi0
    exact smul_apply_zero_eq_of_smul_rootR hw v
  exact h

theorem mem_parabolicWeylGroup_nodesTU {w : WeylGroup .F4} (hr : w • rootR = rootR)
    (hs : w • rootS = rootS) : w ∈ parabolicWeylGroup .F4 nodesTU := by
  have h : w ∈ (parabolicWeylGroup .F4 nodesTU : Set (WeylGroup .F4)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer .F4 nodesTU).1]
    intro v i hi
    simp only [nodesTU, Set.mem_ofPred_eq, ne_eq, not_and_or, not_not] at hi
    rcases hi with rfl | rfl
    · exact smul_apply_zero_eq_of_smul_rootR hr v
    · exact smul_apply_three_eq_of_smul_rootS hs v
  exact h

end Weyl

section Bruhat

variable {K : Type} [Field K]


theorem orbitCertRoot_47_44 : orbitCertRoot .F4 47 = rootR ∧ orbitCertRoot .F4 44 = rootS :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem ne_zero_of_conj_f4x_eq {k : ℕ} {b : ModGL .F4 K} {d : K}
    (h : b * f4x K k 1 * b⁻¹ = f4x K k d) : d ≠ 0 := by
  rintro rfl
  rw [f4x_zero, mul_inv_eq_one, mul_eq_left] at h
  exact one_ne_zero (pinnedX_injective .F4 K _ (h.trans (pinnedX_zero .F4 K _).symm))

theorem mem_parabolicSubgroup_nodesT_of_conj [CharP K 2] {g : ModGL .F4 K}
    (hg : g ∈ adjointGroup .F4 K) {c : K} (hc : g * f4x K 47 1 * g⁻¹ = f4x K 47 c) :
    g ∈ parabolicSubgroup .F4 K nodesT := by
  have hg' : g ∈ ⋃ w, bruhatCell .F4 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  obtain ⟨d, hd⟩ := exists_conj_f4x_central_of_mem_borel (Or.inr rfl) hb' (1 : K)
  obtain ⟨e, he⟩ := exists_conj_f4x_central_of_mem_borel (Or.inr rfl) (inv_mem hb) c
  have hd0 : d ≠ 0 := ne_zero_of_conj_f4x_eq hd
  have hr := f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩
  have hnd : n * f4x K 47 d * n⁻¹ = f4x K 47 e := by
    rw [← hd, ← he, ← hc]
    group
  simp only [f4x] at hnd
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero w hr.1 d] at hnd
  have hwr := eq_of_pinnedX_eq_pinnedX (IsRoot.smul hr.1 w) hr hd0 hnd
  rw [orbitCertRoot_47_44.1] at hwr
  have hmem : b * n * b' ∈ (parabolicSubgroup .F4 K nodesT : Set (ModGL .F4 K)) := by
    rw [(standard_parabolic_cells .F4 K).1 nodesT]
    exact Set.mem_biUnion (mem_parabolicWeylGroup_nodesT hwr) hw
  exact hmem

theorem pinnedX_mul_pinnedX_ne_one_of_pos {α β : Fin (Tag.rank .F4) → ℤ}
    (hα : IsRoot .F4 α ∧ 0 < height α) (hβ : IsRoot .F4 β ∧ 0 < height β) (hαβ : α ≠ β)
    {c c' : K} (hc : c ≠ 0) : pinnedX .F4 K α c * pinnedX .F4 K β c' ≠ 1 := by
  intro h
  have hL := pinnedX_list_prod_injective (R := K) [α, β] (by simpa using hαβ)
    (by
      intro ρ hρ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact hα
      · exact hβ)
    (fun ρ => if ρ = α then c else if ρ = β then c' else 0) (fun _ => 0)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Ne.symm hαβ, ↓reduceIte, pinnedX_zero]
      exact h)
    α (by simp)
  simp only [↓reduceIte] at hL
  exact hc hL

theorem mem_parabolicSubgroup_nodesTU_of_commute [CharP K 2] {g : ModGL .F4 K}
    (hg : g ∈ adjointGroup .F4 K)
    (hc : g * (f4x K 47 1 * f4x K 44 1) * g⁻¹ = f4x K 47 1 * f4x K 44 1) :
    g ∈ parabolicSubgroup .F4 K nodesTU := by
  have hg' : g ∈ ⋃ w, bruhatCell .F4 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  obtain ⟨d, hd⟩ := exists_conj_f4x_central_of_mem_borel (Or.inr rfl) hb' (1 : K)
  obtain ⟨d', hd'⟩ := exists_conj_f4x_central_of_mem_borel (Or.inl rfl) hb' (1 : K)
  obtain ⟨e, he⟩ := exists_conj_f4x_central_of_mem_borel (Or.inr rfl) (inv_mem hb) (1 : K)
  obtain ⟨e', he'⟩ := exists_conj_f4x_central_of_mem_borel (Or.inl rfl) (inv_mem hb) (1 : K)
  have hd0 : d ≠ 0 := ne_zero_of_conj_f4x_eq hd
  have hd0' : d' ≠ 0 := ne_zero_of_conj_f4x_eq hd'
  have hr := f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩
  have hs := f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hconj : n * (f4x K 47 d * f4x K 44 d') * n⁻¹ = f4x K 47 e * f4x K 44 e' := by
    have e1 : f4x K 47 e * f4x K 44 e' = b⁻¹ * (f4x K 47 1 * f4x K 44 1) * b⁻¹⁻¹ := by
      rw [← he, ← he']
      group
    have e2 : f4x K 47 d * f4x K 44 d' = b' * (f4x K 47 1 * f4x K 44 1) * b'⁻¹ := by
      rw [← hd, ← hd']
      group
    rw [e1, e2]
    conv_rhs => rw [← hc]
    group
  have hn1 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hr.1 d
  have hn2 := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hs.1 d'
  rw [← hn] at hn1 hn2
  have hkey : pinnedX .F4 K (w • orbitCertRoot .F4 47) d *
      pinnedX .F4 K (w • orbitCertRoot .F4 44) d' = f4x K 47 e * f4x K 44 e' := by
    rw [← hn1, ← hn2, ← hconj]
    simp only [f4x]
    group
  set α := w • orbitCertRoot .F4 47 with hαdef
  set β := w • orbitCertRoot .F4 44 with hβdef
  have hα : IsRoot .F4 α := IsRoot.smul hr.1 w
  have hβ : IsRoot .F4 β := IsRoot.smul hs.1 w
  have hY : f4x K 47 e * f4x K 44 e' ∈ posUnipotent .F4 K :=
    mul_mem (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ e)
      (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ e')
  have hBN : ∀ x : ModGL .F4 K, x ∈ posUnipotent .F4 K → x ∈ negUnipotent .F4 K → x = 1 := by
    intro x hxU hxN
    have h : x ∈ borelGroup .F4 K ⊓ negUnipotent .F4 K := mem_inf.2 ⟨mem_sup_right hxU, hxN⟩
    rwa [borelGroup_inf_negUnipotent, mem_bot] at h
  have hrs : orbitCertRoot .F4 47 ≠ orbitCertRoot .F4 44 := by decide
  have hpos : 0 < height α ∧ 0 < height β := by
    rcases IsRoot.height_pos_or_neg hα with hαp | hαn <;>
      rcases IsRoot.height_pos_or_neg hβ with hβp | hβn
    · exact ⟨hαp, hβp⟩
    · exfalso
      have e1 : pinnedX .F4 K β d' = (pinnedX .F4 K α d)⁻¹ * (f4x K 47 e * f4x K 44 e') := by
        rw [← hkey]
        group
      have h1 := hBN _ (by
          rw [e1]
          exact mul_mem (inv_mem (pinnedX_mem_rootSpan
            (S := {γ | IsRoot .F4 γ ∧ 0 < height γ}) ⟨hα, hαp⟩ d)) hY)
        (pinnedX_mem_rootSpan (S := {γ | IsRoot .F4 γ ∧ height γ < 0}) ⟨hβ, hβn⟩ d')
      exact hd0' (pinnedX_injective .F4 K β (h1.trans (pinnedX_zero .F4 K β).symm))
    · exfalso
      have e1 : pinnedX .F4 K α d = (f4x K 47 e * f4x K 44 e') * (pinnedX .F4 K β d')⁻¹ := by
        rw [← hkey]
        group
      have h1 := hBN _ (by
          rw [e1]
          exact mul_mem hY (inv_mem (pinnedX_mem_rootSpan
            (S := {γ | IsRoot .F4 γ ∧ 0 < height γ}) ⟨hβ, hβp⟩ d')))
        (pinnedX_mem_rootSpan (S := {γ | IsRoot .F4 γ ∧ height γ < 0}) ⟨hα, hαn⟩ d)
      exact hd0 (pinnedX_injective .F4 K α (h1.trans (pinnedX_zero .F4 K α).symm))
    · exfalso
      have h1 := hBN _ (by rw [hkey]; exact hY)
        (mul_mem (pinnedX_mem_rootSpan (S := {γ | IsRoot .F4 γ ∧ height γ < 0}) ⟨hα, hαn⟩ d)
          (pinnedX_mem_rootSpan (S := {γ | IsRoot .F4 γ ∧ height γ < 0}) ⟨hβ, hβn⟩ d'))
      rw [← hn1, ← hn2] at h1
      have h3 : pinnedX .F4 K (orbitCertRoot .F4 47) d * pinnedX .F4 K (orbitCertRoot .F4 44) d'
          = 1 := by
        have h4 : n * (pinnedX .F4 K (orbitCertRoot .F4 47) d *
            pinnedX .F4 K (orbitCertRoot .F4 44) d') * n⁻¹ = 1 := by
          rw [← h1]
          group
        rw [mul_inv_eq_one, mul_eq_left] at h4
        exact h4
      exact pinnedX_mul_pinnedX_ne_one_of_pos hr hs hrs hd0 h3
  have hlen : iform α α = 4 ∧ iform β β = 2 := by
    rw [hαdef, hβdef, iform_smul, iform_smul, orbitCertRoot_47_44.1, orbitCertRoot_47_44.2]
    exact ⟨iform_rootR_rootS_values.1, iform_rootR_rootS_values.2.1⟩
  have hαs : α ≠ orbitCertRoot .F4 44 := by
    intro h
    have := hlen.1
    rw [h, orbitCertRoot_47_44.2, iform_rootR_rootS_values.2.1] at this
    exact absurd this (by norm_num)
  have hβr : β ≠ orbitCertRoot .F4 47 := by
    intro h
    have := hlen.2
    rw [h, orbitCertRoot_47_44.1, iform_rootR_rootS_values.1] at this
    exact absurd this (by norm_num)
  have hαβ : α ≠ β := fun h => hrs (smul_left_cancel w h)
  obtain ⟨hwr, hws⟩ := eq_and_eq_of_pinnedX_mul_eq ⟨hα, hpos.1⟩ ⟨hβ, hpos.2⟩ hr hs hαβ hrs hαs hβr
    hd0 hd0' (by simpa only [f4x] using hkey)
  rw [hαdef, orbitCertRoot_47_44.1] at hwr
  rw [hβdef, orbitCertRoot_47_44.2] at hws
  have hmem : b * n * b' ∈ (parabolicSubgroup .F4 K nodesTU : Set (ModGL .F4 K)) := by
    rw [(standard_parabolic_cells .F4 K).1 nodesTU]
    exact Set.mem_biUnion (mem_parabolicWeylGroup_nodesTU hwr hws) hw
  exact hmem

end Bruhat

@[expose] def IsTwoRadicalDecomp {G : Type*} [Group G] (z : G) (Q M : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧ Q ⊔ M = centralizer ({z} : Set G) ∧ Q ⊓ M = ⊥ ∧
    M ≤ normalizer (Q : Set G)

theorem IsTwoRadicalDecomp.map {G : Type*} [Group G] {z : G} {Q M : Subgroup G}
    (h : IsTwoRadicalDecomp z Q M) (e : MulAut G) :
    IsTwoRadicalDecomp (e z) (Q.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.map _, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, h2]
    ext x
    rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro hx
      have := congrArg e hx
      simpa using this
    · intro hx
      have := congrArg e.symm hx
      simpa using this
  · rw [← map_inf_eq _ _ _ e.injective, h3, Subgroup.map_bot]
  · rw [← map_equiv_normalizer_eq]
    exact Subgroup.map_mono h4

theorem commutator_centralizer_map {G : Type*} [Group G] {z : G}
    (h : ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ = centralizer ({z} : Set G))
    (e : MulAut G) :
    ⁅centralizer ({e z} : Set G), centralizer ({e z} : Set G)⁆ = centralizer ({e z} : Set G) := by
  have hmap : (centralizer ({z} : Set G)).map e.toMonoidHom = centralizer ({e z} : Set G) := by
    ext x
    rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro hx
      have := congrArg e hx
      simpa using this
    · intro hx
      have := congrArg e.symm hx
      simpa using this
  rw [← hmap, ← map_commutator, h]

section Levi

variable {K : Type} [Field K]


theorem rootChar_eq_one_of_commute_pinnedX {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {a : Fin (Tag.rank .F4) → Kˣ}
    (h : rootDiagUnit .F4 a * pinnedX .F4 K γ 1 = pinnedX .F4 K γ 1 * rootDiagUnit .F4 a) :
    rootChar a γ = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX a hγ (1 : K)
  rw [h, mul_inv_cancel_right, mul_one] at h1
  exact Units.ext (by rw [Units.val_one]; exact (pinnedX_injective .F4 K γ h1).symm)

theorem mem_sup_rootSpan_of_mem_parabolicSubgroup {J : Set (Fin (Tag.rank .F4))}
    {z : ModGL .F4 K} (hQ : ∀ q ∈ parabolicRadical .F4 K J, q * z = z * q)
    (hL : ∀ l ∈ rootSpan .F4 K (parabolicRoots .F4 J), l * z = z * l)
    (hH : ∀ a : Fin (Tag.rank .F4) → Kˣ, rootDiagUnit .F4 a * z = z * rootDiagUnit .F4 a →
      rootDiagUnit .F4 a ∈ rootSpan .F4 K (parabolicRoots .F4 J))
    {g : ModGL .F4 K} (hgP : g ∈ parabolicSubgroup .F4 K J) (hgz : g * z = z * g) :
    g ∈ parabolicRadical .F4 K J ⊔ rootSpan .F4 K (parabolicRoots .F4 J) := by
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .F4 K J
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq g hgP
  have hm' : m ∈ (torusGroup .F4 K : Set (ModGL .F4 K)) *
      (rootSpan .F4 K (parabolicRoots .F4 J) : Set (ModGL .F4 K)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))]
    exact parabolicLevi_le_torusGroup_sup J hm
  obtain ⟨h, hh, l, hl, rfl⟩ := hm'
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hcq : Commute q z := hQ q hq
  have hcl : Commute l z := hL l hl
  have hcg : Commute (q * (rootDiagUnit .F4 a * l)) z := hgz
  have hch : Commute (rootDiagUnit .F4 a) z := by
    have e : rootDiagUnit .F4 a = q⁻¹ * (q * (rootDiagUnit .F4 a * l)) * l⁻¹ := by group
    rw [e]
    exact (hcq.inv_left.mul_left hcg).mul_left hcl.inv_left
  exact mul_mem (mem_sup_left hq) (mem_sup_right (mul_mem (hH a hch.eq) hl))

theorem commute_f4x47_of_mem_rootSpan_c3 {l : ModGL .F4 K}
    (hl : l ∈ rootSpan .F4 K c3LeviRoots) : l * f4x K 47 1 = f4x K 47 1 * l := by
  have hle : rootSpan .F4 K c3LeviRoots ≤
      centralizer (rootSubgroup .F4 K rootR : Set (ModGL .F4 K)) := by
    refine iSup₂_le fun γ hγ x hx => mem_centralizer_iff.2 fun y hy => ?_
    have h0 : iform γ rootR = 0 := by
      rw [iform_comm, iform_rootR]
      have : γ 0 = 0 := hγ.2
      rw [this, mul_zero]
    exact (commute_of_iform_eq_zero_of_long hγ.1 isRoot_rootR iform_rootR_rootS_values.1 h0 hx
      hy).eq.symm
  have hx : f4x K 47 1 ∈ rootSubgroup .F4 K rootR := by
    rw [f4x, orbitCertRoot_47_44.1]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  exact (mem_centralizer_iff.1 (hle hl) _ hx).symm

theorem rootDiagUnit_mem_rootSpan_c3 {a : Fin (Tag.rank .F4) → Kˣ} (ha : rootChar a rootR = 1) :
    rootDiagUnit .F4 a ∈ rootSpan .F4 K c3LeviRoots := by
  refine rootDiagUnit_mem_rootSpan_of_rootChar fun j => ?_
  by_cases hj : j = 0
  · subst hj
    exact Or.inl (by rw [f4FundWeight_zero_three.1]; exact ha)
  · refine Or.inr ⟨mem_c3LeviRoots.2 ⟨isRoot_single _ j, ?_⟩,
      mem_c3LeviRoots.2 ⟨isRoot_neg_single _ j, ?_⟩⟩
    · show (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) 0 = 0
      exact Pi.single_eq_of_ne (Ne.symm hj) _
    · show (-(Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) 0 = 0
      rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj), neg_zero]

theorem rootDiagUnit_mem_rootSpan_b2 {a : Fin (Tag.rank .F4) → Kˣ} (ha : rootChar a rootR = 1)
    (hb : rootChar a rootS = 1) : rootDiagUnit .F4 a ∈ rootSpan .F4 K b2LeviRoots := by
  refine rootDiagUnit_mem_rootSpan_of_rootChar fun j => ?_
  by_cases hj : j = 0
  · subst hj
    exact Or.inl (by rw [f4FundWeight_zero_three.1]; exact ha)
  by_cases hj3 : j = 3
  · subst hj3
    exact Or.inl (by rw [f4FundWeight_zero_three.2]; exact hb)
  · refine Or.inr ⟨mem_b2LeviRoots.2 ⟨isRoot_single _ j, Pi.single_eq_of_ne (Ne.symm hj) _,
      Pi.single_eq_of_ne (Ne.symm hj3) _⟩, mem_b2LeviRoots.2 ⟨isRoot_neg_single _ j, ?_, ?_⟩⟩
    · rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj), neg_zero]
    · rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj3), neg_zero]

theorem centralizer_f4x47_inf_eq [CharP K 2] :
    centralizer ({f4x K 47 1} : Set (ModGL .F4 K)) ⊓ adjointGroup .F4 K =
      parabolicRadical .F4 K nodesT ⊔ rootSpan .F4 K c3LeviRoots := by
  refine le_antisymm (fun g hg => ?_) (sup_le (fun q hq => ?_) (fun l hl => ?_))
  · obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
    have hgz : f4x K 47 1 * g = g * f4x K 47 1 := mem_centralizer_iff.1 hgC _ rfl
    have hgP := mem_parabolicSubgroup_nodesT_of_conj hgG (c := 1) (by rw [← hgz]; group)
    have h := mem_sup_rootSpan_of_mem_parabolicSubgroup (z := f4x K 47 1) (J := nodesT)
      (fun q hq => f4x_central (Or.inr rfl) 1 (parabolicRadical_le_posUnipotent _ hq))
      (fun l hl => commute_f4x47_of_mem_rootSpan_c3 (by rwa [parabolicRoots_nodesT] at hl))
      (fun a ha => by
        rw [parabolicRoots_nodesT]
        refine rootDiagUnit_mem_rootSpan_c3 (rootChar_eq_one_of_commute_pinnedX isRoot_rootR ?_)
        simpa only [f4x, orbitCertRoot_47_44.1] using ha)
      hgP hgz.symm
    rwa [parabolicRoots_nodesT] at h
  · refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_,
      posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hq)⟩
    rintro _ rfl
    exact (f4x_central (Or.inr rfl) 1 (parabolicRadical_le_posUnipotent _ hq)).symm
  · refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_, rootSpan_le_adjointGroup K _ hl⟩
    rintro _ rfl
    exact (commute_f4x47_of_mem_rootSpan_c3 hl).symm

theorem commute_f4x44_of_mem_rootSpan_b3 [Finite K] [CharP K 2] {l : ModGL .F4 K}
    (hl : l ∈ rootSpan .F4 K b3LeviRoots) : l * f4x K 44 1 = f4x K 44 1 * l := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  have hlB : (⟨l, rootSpan_le_adjointGroup K _ hl⟩ : adjointGroup .F4 K) ∈ B3Levi K :=
    mem_B3Levi_iff.2 hl
  rw [← map_graphAutF4_C3Levi] at hlB
  obtain ⟨m, hm, hml⟩ := hlB
  have hmc : m * (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ * m :=
    Subtype.ext (commute_f4x47_of_mem_rootSpan_c3 (mem_C3Levi_iff.1 hm))
  have h := congrArg (graphAutF4 K) hmc
  rw [map_mul, map_mul] at h
  have h47 : graphAutF4 K (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := f4Phi_f4x_47_44.1
  have hml' : graphAutF4 K m = ⟨l, rootSpan_le_adjointGroup K _ hl⟩ := hml
  rw [h47, hml'] at h
  exact congrArg Subtype.val h

theorem rootChar_eq_one_of_commute_f4x47_f4x44 {a : Fin (Tag.rank .F4) → Kˣ}
    (h : rootDiagUnit .F4 a * (f4x K 47 1 * f4x K 44 1) =
      f4x K 47 1 * f4x K 44 1 * rootDiagUnit .F4 a) :
    rootChar a rootR = 1 ∧ rootChar a rootS = 1 := by
  obtain ⟨hr, hrp⟩ := f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩
  obtain ⟨hs, hsp⟩ := f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩
  have hrs : orbitCertRoot .F4 47 ≠ orbitCertRoot .F4 44 := by decide
  have h1 := rootDiagUnit_conj_pinnedX a hr (1 : K)
  have h2 := rootDiagUnit_conj_pinnedX a hs (1 : K)
  have h3 : pinnedX .F4 K (orbitCertRoot .F4 47) ((rootChar a (orbitCertRoot .F4 47) : K) * 1) *
      pinnedX .F4 K (orbitCertRoot .F4 44) ((rootChar a (orbitCertRoot .F4 44) : K) * 1) =
      pinnedX .F4 K (orbitCertRoot .F4 47) 1 * pinnedX .F4 K (orbitCertRoot .F4 44) 1 := by
    rw [← h1, ← h2]
    have e : rootDiagUnit .F4 a * pinnedX .F4 K (orbitCertRoot .F4 47) 1 *
        (rootDiagUnit .F4 a)⁻¹ * (rootDiagUnit .F4 a * pinnedX .F4 K (orbitCertRoot .F4 44) 1 *
          (rootDiagUnit .F4 a)⁻¹) = rootDiagUnit .F4 a * (f4x K 47 1 * f4x K 44 1) *
          (rootDiagUnit .F4 a)⁻¹ := by
      simp only [f4x]
      group
    rw [e, h, mul_inv_cancel_right]
    rfl
  have hL := pinnedX_list_prod_injective (R := K) [orbitCertRoot .F4 47, orbitCertRoot .F4 44]
    (by simpa using hrs)
    (by
      intro ρ hρ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact ⟨hr, hrp⟩
      · exact ⟨hs, hsp⟩)
    (fun ρ => if ρ = orbitCertRoot .F4 47 then (rootChar a (orbitCertRoot .F4 47) : K) * 1 else
      if ρ = orbitCertRoot .F4 44 then (rootChar a (orbitCertRoot .F4 44) : K) * 1 else 0)
    (fun ρ => if ρ = orbitCertRoot .F4 47 then 1 else if ρ = orbitCertRoot .F4 44 then 1 else 0)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Ne.symm hrs, ↓reduceIte]
      simpa only [mul_one] using h3)
  have hr1 := hL (orbitCertRoot .F4 47) (by simp)
  have hs1 := hL (orbitCertRoot .F4 44) (by simp)
  simp only [Ne.symm hrs, ↓reduceIte, mul_one] at hr1 hs1
  rw [← orbitCertRoot_47_44.1, ← orbitCertRoot_47_44.2]
  exact ⟨Units.ext (by rw [Units.val_one]; exact hr1), Units.ext (by rw [Units.val_one]; exact hs1)⟩

theorem centralizer_f4x47_f4x44_inf_eq [Finite K] [CharP K 2] :
    centralizer ({f4x K 47 1 * f4x K 44 1} : Set (ModGL .F4 K)) ⊓ adjointGroup .F4 K =
      parabolicRadical .F4 K nodesTU ⊔ rootSpan .F4 K b2LeviRoots := by
  have hQ : ∀ q ∈ parabolicRadical .F4 K nodesTU,
      q * (f4x K 47 1 * f4x K 44 1) = f4x K 47 1 * f4x K 44 1 * q := by
    intro q hq
    have hqU := parabolicRadical_le_posUnipotent _ hq
    rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hqU, mul_assoc, f4x_central (Or.inl rfl) 1 hqU,
      ← mul_assoc]
  have hL : ∀ l ∈ rootSpan .F4 K b2LeviRoots,
      l * (f4x K 47 1 * f4x K 44 1) = f4x K 47 1 * f4x K 44 1 * l := by
    intro l hl
    have h1 := commute_f4x47_of_mem_rootSpan_c3
      (rootSpan_mono (R := K) b2LeviRoots_subset_c3LeviRoots hl)
    have h2 := commute_f4x44_of_mem_rootSpan_b3
      (rootSpan_mono (R := K) b2LeviRoots_subset_b3LeviRoots hl)
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  refine le_antisymm (fun g hg => ?_) (sup_le (fun q hq => ?_) (fun l hl => ?_))
  · obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
    have hgz : f4x K 47 1 * f4x K 44 1 * g = g * (f4x K 47 1 * f4x K 44 1) :=
      mem_centralizer_iff.1 hgC _ rfl
    have hgP := mem_parabolicSubgroup_nodesTU_of_commute hgG (by rw [← hgz]; group)
    exact mem_sup_rootSpan_of_mem_parabolicSubgroup (z := f4x K 47 1 * f4x K 44 1) hQ hL
      (fun a ha => by
        obtain ⟨h1, h2⟩ := rootChar_eq_one_of_commute_f4x47_f4x44 ha
        exact rootDiagUnit_mem_rootSpan_b2 h1 h2)
      hgP hgz.symm
  · exact mem_inf.2 ⟨mem_centralizer_iff.2 (by rintro _ rfl; exact (hQ q hq).symm),
      posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hq)⟩
  · exact mem_inf.2 ⟨mem_centralizer_iff.2 (by rintro _ rfl; exact (hL l hl).symm),
      rootSpan_le_adjointGroup K _ hl⟩

end Levi

section Decomp


variable (K : Type) [Field K]

@[expose] noncomputable def B2Levi : Subgroup ↥(adjointGroup .F4 K) :=
  (rootSpan .F4 K b2LeviRoots).subgroupOf (adjointGroup .F4 K)

@[expose] noncomputable def radicalT : Subgroup ↥(adjointGroup .F4 K) :=
  (parabolicRadical .F4 K nodesT).subgroupOf (adjointGroup .F4 K)

@[expose] noncomputable def radicalTU : Subgroup ↥(adjointGroup .F4 K) :=
  (parabolicRadical .F4 K nodesTU).subgroupOf (adjointGroup .F4 K)

@[expose] noncomputable def zT : adjointGroup .F4 K := ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩

@[expose] noncomputable def zU : adjointGroup .F4 K := ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩

variable {K}


theorem isPGroup_parabolicRadical_subgroupOf [Finite K] [CharP K 2] (J : Set (Fin (Tag.rank .F4))) :
    IsPGroup 2 ((parabolicRadical .F4 K J).subgroupOf (adjointGroup .F4 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQp, -⟩ := (parabolic_root_radical_Levi_factors .F4 K J).2.2.2.2.2.2.2.2.2.2.2.2 2
  exact isPGroup_subgroupOf_of_le ((parabolicRadical_le_posUnipotent _).trans
    posUnipotent_le_adjointGroup) hQp

theorem isTwoRadicalDecomp_zT [Finite K] [CharP K 2] :
    IsTwoRadicalDecomp (zT K) (radicalT K) (C3Levi K) := by
  obtain ⟨h1, h2, h3⟩ := decomp_subgroupOf ((parabolicRadical_le_posUnipotent _).trans
    posUnipotent_le_adjointGroup) (rootSpan_le_adjointGroup K c3LeviRoots) (zT K)
    centralizer_f4x47_inf_eq
    (by rw [← parabolicRoots_nodesT]; exact parabolicRadical_inf_rootSpan nodesT)
    (by rw [← parabolicRoots_nodesT]; exact rootSpan_parabolicRoots_le_normalizer nodesT)
  exact ⟨isPGroup_parabolicRadical_subgroupOf nodesT, h1, h2, h3⟩

theorem isTwoRadicalDecomp_zTU [Finite K] [CharP K 2] :
    IsTwoRadicalDecomp (zT K * zU K) (radicalTU K) (B2Levi K) := by
  obtain ⟨h1, h2, h3⟩ := decomp_subgroupOf ((parabolicRadical_le_posUnipotent _).trans
    posUnipotent_le_adjointGroup) (rootSpan_le_adjointGroup K b2LeviRoots) (zT K * zU K)
    centralizer_f4x47_f4x44_inf_eq (parabolicRadical_inf_rootSpan nodesTU)
    (rootSpan_parabolicRoots_le_normalizer nodesTU)
  exact ⟨isPGroup_parabolicRadical_subgroupOf nodesTU, h1, h2, h3⟩

theorem graphAutF4_zT [Finite K] [CharP K 2] : graphAutF4 K (zT K) = zU K :=
  f4Phi_f4x_47_44.1

theorem isTwoRadicalDecomp_zU [Finite K] [CharP K 2] :
    IsTwoRadicalDecomp (zU K) ((radicalT K).map (graphAutF4 K).toMonoidHom) (B3Levi K) := by
  have h := (isTwoRadicalDecomp_zT (K := K)).map (graphAutF4 K)
  have e1 : (C3Levi K).map (graphAutF4 K).toMonoidHom = B3Levi K := map_graphAutF4_C3Levi
  have e2 : graphAutF4 K (zT K) = zU K := graphAutF4_zT
  rwa [e1, e2] at h

end Decomp

end CFSG.SeitzReduction.F4Pilot
