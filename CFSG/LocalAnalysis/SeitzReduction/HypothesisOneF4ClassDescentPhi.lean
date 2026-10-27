module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescentBasic
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
open CFSG.LieType.Ree (ReeTag)

theorem f4Desc_dualRoot_single : ∀ j : Fin Tag.F4.rank,
    ReeTag.F4.dualRoot (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Pi.single (ReeTag.F4.perm j) 1 := by
  decide +kernel

theorem f4Desc_perm_perm : ∀ j : Fin ReeTag.F4.tag.rank, ReeTag.F4.perm (ReeTag.F4.perm j) = j := by
  decide +kernel

theorem f4Desc_perm_mem_long : ∀ j : Fin ReeTag.F4.tag.rank, j ∉ classKillLongSimple ReeTag.F4.tag →
    ReeTag.F4.perm j ∈ classKillLongSimple ReeTag.F4.tag := by
  decide +kernel

theorem f4Desc_quadForm_single_short : ∀ j : Fin Tag.F4.rank, j ∉ classKillLongSimple .F4 →
    ReeTag.F4.quadForm (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = 2 := by
  decide +kernel

theorem f4Desc_dualRoot_apply_eq_zero {α : Fin Tag.F4.rank → ℤ} {j : Fin Tag.F4.rank}
    (h : α (ReeTag.F4.perm.symm j) = 0) : ReeTag.F4.dualRoot α j = 0 := by
  simp [ReeTag.dualRoot, ReeTag.dualMapInt, h]

theorem f4Desc_dualRoot_mem
    {J J₂ : List (Fin Tag.F4.rank)}
    (hJ : ∀ j ∈ J, ∃ j₂ ∈ J₂, (j₂ : ℕ) = (ReeTag.F4.perm j : ℕ)) {i : Fin Tag.F4.rank}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ parabolicPosRoots .F4 {j | j ∈ J} \ {Pi.single i 1}) :
    IsRoot .F4 α ∧ ReeTag.F4.dualRoot α ∈
      parabolicPosRoots .F4 {j | j ∈ J₂} \ {Pi.single (ReeTag.F4.perm i) 1} := by
  obtain ⟨⟨⟨hαr, hαs⟩, hαp⟩, hαi⟩ := hα
  obtain ⟨-, hd⟩ := CFSG.LieType.Ree.ReeTag.dualRoot_mem_posRoots (t := ReeTag.F4) hαp
  refine ⟨hαr, ⟨⟨hd.1, fun l hl => f4Desc_dualRoot_apply_eq_zero (hαs _ fun h => hl ?_)⟩, hd⟩,
    fun h => hαi ?_⟩
  · obtain ⟨j₂, hj₂, hv⟩ := hJ _ h
    have e : j₂ = l :=
      Fin.ext (hv.trans (congrArg Fin.val (Equiv.apply_symm_apply ReeTag.F4.perm l)))
    exact e ▸ hj₂
  · have h' : ReeTag.F4.dualRoot α = Pi.single (ReeTag.F4.perm i) 1 := h
    have hinv := (CFSG.LieType.Ree.ReeTag.rootDualityCheck_spec (t := ReeTag.F4) hαr).2.2.2.1
    rw [Set.mem_singleton_iff, ← hinv, h']
    exact (f4Desc_dualRoot_single _).trans
      (congrArg (fun j => (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) (f4Desc_perm_perm i))

@[expose] def f4DescCandidates : List (List ℕ) :=
  [[47], [47, 32], [47, 32, 30], [47, 32, 30, 27], [44, 35, 30], [44, 35, 30, 27], [44, 40],
    [44, 40, 33], [44, 40, 25], [44, 40, 33, 25]]

variable {K : Type} [Field K]

section Good


variable (K) in
@[expose] def F4DescGood (x : ModGL .F4 K) : Prop :=
  ∃ hx : x ∈ adjointGroup .F4 K, ∃ ψ : MulAut (adjointGroup .F4 K), ∃ L ∈ f4DescCandidates,
    ((ψ ⟨x, hx⟩ : adjointGroup .F4 K) : ModGL .F4 K) = f4DescProd K L

theorem f4DescGood_of_mem {L : List ℕ} (hL : L ∈ f4DescCandidates) :
    F4DescGood K (f4DescProd K L) :=
  ⟨f4DescProd_mem_adjointGroup L, 1, L, hL, rfl⟩

theorem F4DescGood.of_conj {g x : ModGL .F4 K} (hg : g ∈ adjointGroup .F4 K)
    (hx : x ∈ adjointGroup .F4 K) (h : F4DescGood K (g * x * g⁻¹)) : F4DescGood K x := by
  obtain ⟨hgx, ψ, L, hL, he⟩ := h
  refine ⟨hx, ψ * MulAut.conj ⟨g, hg⟩, L, hL, ?_⟩
  have e : (MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K)) ⟨x, hx⟩ = ⟨g * x * g⁻¹, hgx⟩ :=
    Subtype.ext rfl
  rw [MulAut.mul_apply, e]
  exact he

theorem f4Desc_rootSpan_le_adjointGroup (S : Set (Fin Tag.F4.rank → ℤ)) :
    rootSpan .F4 K S ≤ adjointGroup .F4 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

end Good

section Phi


variable [Finite K] [CharP K 2]

variable (K) in
noncomputable abbrev f4DescPhi : MulAut (adjointGroup .F4 K) :=
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  ReeTag.F4.finiteExceptionalAut K

theorem F4DescGood.of_phi {x : ModGL .F4 K} (hx : x ∈ adjointGroup .F4 K)
    (h : F4DescGood K ((f4DescPhi K ⟨x, hx⟩ : adjointGroup .F4 K) : ModGL .F4 K)) :
    F4DescGood K x := by
  obtain ⟨hy, ψ, L, hL, he⟩ := h
  refine ⟨hx, ψ * f4DescPhi K, L, hL, ?_⟩
  have e : (⟨((f4DescPhi K ⟨x, hx⟩ : adjointGroup .F4 K) : ModGL .F4 K), hy⟩ :
      adjointGroup .F4 K) = f4DescPhi K ⟨x, hx⟩ := Subtype.ext rfl
  rw [MulAut.mul_apply, ← e]
  exact he

theorem f4Desc_phi_mem_rootSpan {S S' : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot .F4 α ∧ ReeTag.F4.dualRoot α ∈ S') {u : adjointGroup .F4 K}
    (hu : (u : ModGL .F4 K) ∈ rootSpan .F4 K S) :
    ((f4DescPhi K u : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K S' := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hle : ((rootSpan ReeTag.F4.tag K S).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
      (ReeTag.F4.finiteReeAut K 0).toMonoidHom ≤
        (rootSpan ReeTag.F4.tag K S').subgroupOf (adjointGroup ReeTag.F4.tag K) := by
    rw [CFSG.LieType.Ree.ReeTag.subgroupOf_rootSpan (t := ReeTag.F4) S,
      CFSG.LieType.Ree.ReeTag.subgroupOf_rootSpan (t := ReeTag.F4) S', Subgroup.map_iSup]
    refine iSup_le fun α => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hα => ?_
    rw [CFSG.LieType.Ree.ReeTag.map_finiteReeAut_rootSubgroup (t := ReeTag.F4) (hS α hα).1]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ S') =>
      (rootSubgroup ReeTag.F4.tag K β).subgroupOf (adjointGroup ReeTag.F4.tag K)) _ (hS α hα).2
      le_rfl
  have hu' : u ∈ (rootSpan ReeTag.F4.tag K S).subgroupOf (adjointGroup ReeTag.F4.tag K) :=
    Subgroup.mem_subgroupOf.2 hu
  have h := hle (Subgroup.mem_map_of_mem _ hu')
  rw [finiteReeAut_zero_F4] at h
  exact Subgroup.mem_subgroupOf.1 h

theorem f4Desc_phi_pinnedX_short {i : Fin Tag.F4.rank} (hi : i ∉ classKillLongSimple .F4)
    (c : K) :
    f4DescPhi K ⟨pinnedX .F4 K (Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨pinnedX .F4 K (Pi.single (ReeTag.F4.perm i) 1) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hs : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ ReeTag.F4.shortRoots :=
    ⟨isRoot_single _ i, CFSG.LieType.Ree.ReeTag.lengthParam_eq_one_iff.2
      (f4Desc_quadForm_single_short i hi)⟩
  have h := finiteExceptionalAut_pinnedX_short (K := K) hs c
  rw [f4Desc_dualRoot_single] at h
  exact h

theorem f4Desc_phi_f4DescProd_nil :
    ((f4DescPhi K ⟨f4DescProd K [], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) :
      ModGL .F4 K) = f4DescProd K [] := by
  have e : (⟨f4DescProd K [], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) = 1 :=
    Subtype.ext (by simp [f4DescProd])
  rw [e, map_one]
  simp [f4DescProd]


theorem f4Desc_phi_f4x_pairLong (k : Fin 12) :
    f4DescPhi K ⟨f4x K (f4PairLong k) 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K (f4PairShort k) 1, pinnedX_mem_adjointGroup _ _⟩ := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨hl, -, hd, -⟩ := f4Pair_roots k
  have h := finiteExceptionalAut_pinnedX_long (K := K) hl 1
  rw [hd] at h
  exact h

theorem f4Desc_phi_f4x_47 :
    f4DescPhi K ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := by
  have h := f4Desc_phi_f4x_pairLong (K := K) 11
  rw [show f4PairLong 11 = 47 from rfl, show f4PairShort 11 = 44 from rfl] at h
  exact h

theorem f4Desc_phi_f4x_32 :
    f4DescPhi K ⟨f4x K 32 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 35 1, pinnedX_mem_adjointGroup _ _⟩ := by
  have h := f4Desc_phi_f4x_pairLong (K := K) 6
  rw [show f4PairLong 6 = 32 from rfl, show f4PairShort 6 = 35 from rfl] at h
  exact h

theorem f4Desc_phi_f4DescProd_47 :
    ((f4DescPhi K ⟨f4DescProd K [47], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) :
      ModGL .F4 K) = f4DescProd K [44] := by
  have e : (⟨f4DescProd K [47], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ := Subtype.ext (f4DescProd_singleton 47)
  rw [e, f4Desc_phi_f4x_47]
  exact (f4DescProd_singleton 44).symm

theorem f4Desc_phi_f4DescProd_47_32 :
    ((f4DescPhi K ⟨f4DescProd K [47, 32], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) :
      ModGL .F4 K) = f4DescProd K [44, 35] := by
  have e : (⟨f4DescProd K [47, 32], f4DescProd_mem_adjointGroup _⟩ : adjointGroup .F4 K) =
      ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ * ⟨f4x K 32 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (by simp [f4DescProd])
  rw [e, map_mul, f4Desc_phi_f4x_47, f4Desc_phi_f4x_32]
  simp [f4DescProd]

end Phi

section Levels


theorem f4DescGood_of_level [CharP K 2] (J : List (Fin Tag.F4.rank)) (F : List ℕ)
    (hF : f4DescFrameOK J F = true)
    (hcase : ∀ i ∈ J, ∀ c : K, c ≠ 0 →
      ∀ u ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J} \ {Pi.single i 1}),
        (pinnedX .F4 K (Pi.single i 1) c * u) ^ 2 = 1 →
          F4DescGood K (f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u)))
    {ℓ : ModGL .F4 K} (hℓ : ℓ ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J}))
    (h2 : ℓ ^ 2 = 1) (h1 : ℓ ≠ 1) : F4DescGood K (f4DescProd K F * ℓ) := by
  obtain ⟨ω, hω, i, hi, c, hc, u, hu, he⟩ :=
    exists_prod_weylElt_conj_eq_pinnedX_simple_mul {j | j ∈ J} hℓ h1
  have hPg : (ω.map fun j => weylElt .F4 K j 1).prod ∈ cascadeConjGroup .F4 K {j | j ∈ J} :=
    prod_weylElt_mem_cascadeConjGroup hω
  have hPF := f4DescProd_commute_of_mem_cascadeConjGroup hF hPg
  have h2' : (pinnedX .F4 K (Pi.single i 1) c * u) ^ 2 = 1 := by
    rw [← he, conj_pow, h2, mul_one, mul_inv_cancel]
  refine F4DescGood.of_conj (cascadeConjGroup_le_adjointGroup _ hPg)
    (mul_mem (f4DescProd_mem_adjointGroup F) (f4Desc_rootSpan_le_adjointGroup _ hℓ)) ?_
  have e : (ω.map fun j => weylElt .F4 K j 1).prod * (f4DescProd K F * ℓ) *
      ((ω.map fun j => weylElt .F4 K j 1).prod)⁻¹ =
        f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u) := by
    rw [← he, ← mul_assoc, hPF]
    group
  rw [e]
  exact hcase i hi c hc u hu h2'

theorem f4DescGood_of_long [Finite K] [CharP K 2] (J : List (Fin Tag.F4.rank)) (F : List ℕ)
    (p : ℕ) (J' : List (Fin Tag.F4.rank)) (hF : f4DescFrameOK J F = true)
    (hdom : f4DescDomCheck J p = true) (hJ' : cascNextL .F4 J (orbitCertRoot .F4 p) = J')
    (hcont : ∀ z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J'}), z ^ 2 = 1 →
      F4DescGood K (f4DescProd K (F ++ [p]) * z))
    {i : Fin Tag.F4.rank} (hi : i ∈ J) (hlong : i ∈ classKillLongSimple .F4) {c : K}
    (hc : c ≠ 0) {u : ModGL .F4 K}
    (hu : u ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J} \ {Pi.single i 1}))
    (h2 : (pinnedX .F4 K (Pi.single i 1) c * u) ^ 2 = 1) :
    F4DescGood K (f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u)) := by
  obtain ⟨g, hg, γ, hγ, hdomγ, hlen, z, hz, hz2, he⟩ := f4Desc_frameStep J F hF hi hlong hc hu h2
  obtain rfl := f4DescDomCheck_sound hdom hγ hdomγ hlen
  rw [hJ'] at hz
  refine F4DescGood.of_conj hg (mul_mem (f4DescProd_mem_adjointGroup F)
    (mul_mem (pinnedX_mem_adjointGroup _ _) (f4Desc_rootSpan_le_adjointGroup _ hu))) ?_
  rw [he]
  have h := hcont z hz hz2
  rw [f4DescProd_append, f4DescProd_singleton] at h
  exact h

theorem f4DescGood_of_short [Finite K] [CharP K 2] (J J₂ : List (Fin Tag.F4.rank))
    (hJ : ∀ j ∈ J, ∃ j₂ ∈ J₂, (j₂ : ℕ) = (ReeTag.F4.perm j : ℕ)) (F F₂ : List ℕ)
    (hφ : ((f4DescPhi K ⟨f4DescProd K F, f4DescProd_mem_adjointGroup F⟩ : adjointGroup .F4 K) :
      ModGL .F4 K) = f4DescProd K F₂)
    (hcont : ∀ i₂ ∈ J₂, i₂ ∈ classKillLongSimple .F4 → ∀ c₂ : K, c₂ ≠ 0 →
      ∀ u₂ ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J₂} \ {Pi.single i₂ 1}),
        (pinnedX .F4 K (Pi.single i₂ 1) c₂ * u₂) ^ 2 = 1 →
          F4DescGood K (f4DescProd K F₂ * (pinnedX .F4 K (Pi.single i₂ 1) c₂ * u₂)))
    {i : Fin Tag.F4.rank} (hi : i ∈ J) (hshort : i ∉ classKillLongSimple .F4) {c : K}
    (hc : c ≠ 0) {u : ModGL .F4 K}
    (hu : u ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J} \ {Pi.single i 1}))
    (h2 : (pinnedX .F4 K (Pi.single i 1) c * u) ^ 2 = 1) :
    F4DescGood K (f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u)) := by
  have huC : u ∈ adjointGroup .F4 K := f4Desc_rootSpan_le_adjointGroup _ hu
  have hxC : f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u) ∈ adjointGroup .F4 K :=
    mul_mem (f4DescProd_mem_adjointGroup F) (mul_mem (pinnedX_mem_adjointGroup _ _) huC)
  refine F4DescGood.of_phi hxC ?_
  have e : (⟨f4DescProd K F * (pinnedX .F4 K (Pi.single i 1) c * u), hxC⟩ : adjointGroup .F4 K) =
      ⟨f4DescProd K F, f4DescProd_mem_adjointGroup F⟩ *
        (⟨pinnedX .F4 K (Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ * ⟨u, huC⟩) :=
    Subtype.ext rfl
  have e2 : (⟨pinnedX .F4 K (Pi.single i 1) c * u, mul_mem (pinnedX_mem_adjointGroup _ _) huC⟩ :
      adjointGroup .F4 K) =
        ⟨pinnedX .F4 K (Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ * ⟨u, huC⟩ :=
    Subtype.ext rfl
  have hu₂ : ((f4DescPhi K ⟨u, huC⟩ : adjointGroup .F4 K) : ModGL .F4 K) ∈
      rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ J₂} \ {Pi.single (ReeTag.F4.perm i) 1}) :=
    f4Desc_phi_mem_rootSpan (fun α hα => f4Desc_dualRoot_mem hJ hα) hu
  have hsq : (⟨pinnedX .F4 K (Pi.single i 1) c * u, mul_mem (pinnedX_mem_adjointGroup _ _) huC⟩ :
      adjointGroup .F4 K) ^ 2 = 1 := Subtype.ext (by simpa using h2)
  have h2₂ : (pinnedX .F4 K (Pi.single (ReeTag.F4.perm i) 1) (c ^ 2) *
      ((f4DescPhi K ⟨u, huC⟩ : adjointGroup .F4 K) : ModGL .F4 K)) ^ 2 = 1 := by
    have h := congrArg (fun y : adjointGroup .F4 K => ((y : adjointGroup .F4 K) : ModGL .F4 K))
      (show f4DescPhi K (⟨pinnedX .F4 K (Pi.single i 1) c * u,
          mul_mem (pinnedX_mem_adjointGroup _ _) huC⟩ ^ 2) = 1 by rw [hsq, map_one])
    rw [map_pow, e2, map_mul, f4Desc_phi_pinnedX_short hshort c] at h
    simpa using h
  rw [e, map_mul, map_mul, f4Desc_phi_pinnedX_short hshort c, Subgroup.coe_mul,
    Subgroup.coe_mul, hφ]
  have hmem : ReeTag.F4.perm i ∈ J₂ := by
    obtain ⟨j₂, hj₂, hv⟩ := hJ i hi
    have e : j₂ = ReeTag.F4.perm i := Fin.ext hv
    exact e ▸ hj₂
  exact hcont _ hmem (f4Desc_perm_mem_long i hshort) (c ^ 2) (pow_ne_zero 2 hc) _ hu₂ h2₂

theorem f4DescGood_of_torus [Finite K] [CharP K 2] {F : List ℕ} {p : ℕ} (hp : 24 ≤ p ∧ p ≤ 47)
    (hFp : ∀ q ∈ F, (24 ≤ q ∧ q ≤ 47) ∧ iform (orbitCertRoot .F4 p) (orbitCertRoot .F4 q) = 0)
    {a : K} (ha : a ≠ 0) {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot .F4 δ ∧ iform (orbitCertRoot .F4 p) δ = 0) {w : ModGL .F4 K}
    (hw : w ∈ rootSpan .F4 K S) (h : F4DescGood K (f4DescProd K (F ++ [p]) * w)) :
    F4DescGood K (f4DescProd K F * f4x K p a * w) := by
  obtain ⟨t, htC, ht1, htfix⟩ := f4Desc_exists_torus_conj (K := K) (f4_isRoot_pos hp).1 ha
  have hwfix : t * w * t⁻¹ = w :=
    f4Desc_conj_eq_of_mem_rootSpan (fun δ hδ e => htfix δ (hS δ hδ).1 (hS δ hδ).2 e) hw
  have hFfix : t * f4DescProd K F * t⁻¹ = f4DescProd K F := by
    have hc : t * f4DescProd K F = f4DescProd K F * t := by
      refine f4DescProd_commute F fun q hq => ?_
      have := htfix _ (f4_isRoot_pos (hFp q hq).1).1 (hFp q hq).2 1
      calc t * f4x K q 1 = t * f4x K q 1 * t⁻¹ * t := by group
        _ = f4x K q 1 * t := by rw [f4x, this]
    rw [hc]
    group
  refine F4DescGood.of_conj htC (mul_mem (mul_mem (f4DescProd_mem_adjointGroup F)
    (pinnedX_mem_adjointGroup _ _)) (f4Desc_rootSpan_le_adjointGroup _ hw)) ?_
  have e : t * (f4DescProd K F * f4x K p a * w) * t⁻¹ = f4DescProd K (F ++ [p]) * w := by
    rw [f4DescProd_append, f4DescProd_singleton]
    calc t * (f4DescProd K F * f4x K p a * w) * t⁻¹
        = (t * f4DescProd K F * t⁻¹) * (t * f4x K p a * t⁻¹) * (t * w * t⁻¹) := by group
      _ = f4DescProd K F * f4x K p 1 * w := by rw [hFfix, hwfix, f4x, ht1]; rfl
  rw [e]
  exact h

end Levels

end CFSG.SeitzReduction
