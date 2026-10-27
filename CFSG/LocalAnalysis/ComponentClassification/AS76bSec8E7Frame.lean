module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Residual
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcLineSplit

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

@[expose] def e7FrameUHead : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0, 0]]

@[expose] def e7FrameUTail : Fin Tag.E7.rank → ℤ := ![0, 1, 0, 1, 1, 1, 1]

@[expose] def e7FrameVHead : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 0]]

@[expose] def e7FrameVTail : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 1, 0, 0]

theorem e7FrameU_eq_append : e7FrameU = e7FrameUHead ++ [e7FrameUTail] := rfl

theorem e7FrameV_eq_append : e7FrameV = e7FrameVHead ++ [e7FrameVTail] := rfl

@[expose] def e7WordUHead : List (Fin Tag.E7.rank) := ([3, 4, 5, 6] : List (Fin 7))

@[expose] def e7WordVHead : List (Fin Tag.E7.rank) :=
  ([0, 2, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 4, 1, 3, 2, 0] : List (Fin 7))

@[expose] def e7WordUTail : List (Fin Tag.E7.rank) := ([5, 4, 3, 2] : List (Fin 7))

@[expose] def e7WordVTail : List (Fin Tag.E7.rank) := ([5, 6, 4, 5] : List (Fin 7))

theorem e7WordUHead_map :
    e7FrameUHead.map (fun σ => e7WordUHead.foldr (reflect .E7) σ) = e7FrameY := by
  decide +kernel

theorem e7WordVHead_map :
    e7FrameVHead.map (fun σ => e7WordVHead.foldr (reflect .E7) σ) = e7FrameZ := by
  decide +kernel

theorem e7WordUTail_map :
    [e7FrameUTail].map (fun σ => e7WordUTail.foldr (reflect .E7) σ) = e7FrameX := by
  decide +kernel

theorem e7WordVTail_map :
    [e7FrameVTail].map (fun σ => e7WordVTail.foldr (reflect .E7) σ) = e7FrameX := by
  decide +kernel

theorem e7Split_check : ∀ F ∈ [e7FrameU, e7FrameV, e7FrameUHead, e7FrameVHead],
    F ≠ [] ∧ F.Nodup ∧ (∀ σ ∈ F, List.ofFn σ ∈ Tag.artifactRoots .E7 ∧ 0 < height σ) ∧
      F.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

theorem e7Split_facts {F : List (Fin Tag.E7.rank → ℤ)}
    (hF : F ∈ [e7FrameU, e7FrameV, e7FrameUHead, e7FrameVHead]) :
    F ≠ [] ∧ F.Nodup ∧ (∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ) ∧
      F.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := e7Split_check F hF
  exact ⟨h1, h2, fun σ hσ => ⟨isRoot_iff_mem_artifactRoots.2 (h3 σ hσ).1, (h3 σ hσ).2⟩, h4⟩

variable {K : Type} [Field K]

theorem e7FrameElt_append_single (F' : List (Fin Tag.E7.rank → ℤ))
    (γ : Fin Tag.E7.rank → ℤ) (d : K) :
    e7FrameElt K (F' ++ [γ]) d = e7FrameElt K F' d * e7FrameElt K [γ] d := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_e7FrameElt, List.map_append, List.prod_append]

theorem commute_e7FrameElt_head_tail {F' : List (Fin Tag.E7.rank → ℤ)}
    {γ : Fin Tag.E7.rank → ℤ} (hr : ∀ σ ∈ F' ++ [γ], IsRoot .E7 σ)
    (ho : (F' ++ [γ]).Pairwise fun σ σ' => iform σ σ' = 0) (b c : K) :
    Commute (e7FrameElt K F' b) (e7FrameElt K [γ] c) := by
  have hγ := hr γ (List.mem_append_right _ (List.mem_singleton_self _))
  rw [List.pairwise_append] at ho
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_e7FrameElt, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
  exact commute_pinnedX_of_iform_eq_zero_e7 (hr σ (List.mem_append_left _ hσ)) hγ
    (ho.2.2 σ hσ γ (List.mem_singleton_self _)) b c

theorem e7FrameScale_conj_head {F' : List (Fin Tag.E7.rank → ℤ)} {γ : Fin Tag.E7.rank → ℤ}
    (hγ : IsRoot .E7 γ) (hr : ∀ σ ∈ F', IsRoot .E7 σ) (ho : ∀ σ ∈ F', iform γ σ = 0) (s : Kˣ)
    (b : K) : e7FrameScale K [γ] s * e7FrameElt K F' b * (e7FrameScale K [γ] s)⁻¹ =
      e7FrameElt K F' b := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e7FrameScale, coe_e7FrameElt]
  set H := ([γ].map fun σ => rootTorusSL2 .E7 K σ s).prod with hH
  have hl : ∀ p ∈ [γ].map (fun σ => (σ, s)), IsRoot .E7 p.1 := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_singleton] at hσ
    subst hσ
    exact hγ
  have h1 : ∀ α ∈ F', H * pinnedX .E7 K α b * H⁻¹ = pinnedX .E7 K α b := by
    intro α hα
    have h := list_prod_rootTorusSL2_conj_pinnedX (hr α hα) ([γ].map fun σ => (σ, s)) hl b
    simp only [List.map_map, Function.comp_def] at h
    rw [hH, h]
    simp [ho α hα]
  have key : ∀ L : List (Fin Tag.E7.rank → ℤ), (∀ α ∈ L, α ∈ F') →
      H * (L.map fun α => pinnedX .E7 K α b).prod * H⁻¹ =
        (L.map fun α => pinnedX .E7 K α b).prod := by
    intro L hL
    induction L with
    | nil => simp
    | cons α L ih =>
      simp only [List.map_cons, List.prod_cons]
      calc H * (pinnedX .E7 K α b * (L.map fun α => pinnedX .E7 K α b).prod) * H⁻¹
          = (H * pinnedX .E7 K α b * H⁻¹) *
              (H * (L.map fun α => pinnedX .E7 K α b).prod * H⁻¹) := by group
        _ = _ := by
          rw [h1 α (hL α List.mem_cons_self), ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ)]
  exact key F' fun α hα => hα

theorem e7FrameScale_conj_tail {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot .E7 γ) (s : Kˣ) (c : K) :
    e7FrameScale K [γ] s * e7FrameElt K [γ] c * (e7FrameScale K [γ] s)⁻¹ =
      e7FrameElt K [γ] ((s : K) ^ 2 * c) :=
  e7FrameScale_conj (fun σ hσ => by rw [List.mem_singleton] at hσ; subst hσ; exact hγ)
    (List.pairwise_singleton _ _) s c

theorem mem_e7FrameLine_split [CharP K 2] {F' : List (Fin Tag.E7.rank → ℤ)}
    {γ : Fin Tag.E7.rank → ℤ} (hr : ∀ σ ∈ F' ++ [γ], IsRoot .E7 σ)
    (ho : (F' ++ [γ]).Pairwise fun σ σ' => iform σ σ' = 0) (z : adjointGroup .E7 K) :
    z ∈ e7FrameLine K (F' ++ [γ]) ↔ ∃ d, z = e7FrameElt K F' d * e7FrameElt K [γ] d := by
  rw [mem_e7FrameLine hr ho]
  exact ⟨fun ⟨d, hd⟩ => ⟨d, by rw [← hd, e7FrameElt_append_single]⟩,
    fun ⟨d, hd⟩ => ⟨d, by rw [hd, e7FrameElt_append_single]⟩⟩

theorem eq_zero_of_head_eq_tail {F' : List (Fin Tag.E7.rank → ℤ)} {γ : Fin Tag.E7.rank → ℤ}
    (hne : F' ≠ []) (hnd : (F' ++ [γ]).Nodup)
    (hF : ∀ σ ∈ F' ++ [γ], IsRoot .E7 σ ∧ 0 < height σ) {b c : K}
    (h : e7FrameElt K F' b = e7FrameElt K [γ] c) : b = 0 := by
  have hγ : γ ∉ F' := fun h' => (List.nodup_append.1 hnd).2.2 γ h' γ
    (List.mem_singleton_self _) rfl
  have h' := congrArg Subtype.val h
  simp only [coe_e7FrameElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at h'
  have hcoe : ((F' ++ [γ]).map fun σ =>
        pinnedX .E7 K σ ((fun σ => if σ = γ then 0 else b) σ)).prod =
      ((F' ++ [γ]).map fun σ => pinnedX .E7 K σ ((fun σ => if σ = γ then c else 0) σ)).prod := by
    rw [List.map_append, List.prod_append, List.map_append, List.prod_append]
    have e1 : (F'.map fun σ => pinnedX .E7 K σ ((fun σ => if σ = γ then 0 else b) σ)) =
        F'.map fun σ => pinnedX .E7 K σ b := List.map_congr_left fun σ hσ => by
      have hne' : σ ≠ γ := fun h => hγ (h ▸ hσ)
      simp only [hne', ↓reduceIte]
    have e2 : (F'.map fun σ => pinnedX .E7 K σ ((fun σ => if σ = γ then c else 0) σ)) =
        F'.map fun σ => pinnedX .E7 K σ 0 := List.map_congr_left fun σ hσ => by
      have hne' : σ ≠ γ := fun h => hγ (h ▸ hσ)
      simp only [hne', ↓reduceIte]
    rw [e1, e2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ↓reduceIte,
      pinnedX_zero, List.map_const', List.prod_replicate, one_pow, one_mul]
    exact h'
  have hc := pinnedX_list_prod_injective (F' ++ [γ]) hnd hF _ _ hcoe
  obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil F' hne
  have := hc σ (List.mem_append_left _ hσ)
  have hne' : σ ≠ γ := fun h => hγ (h ▸ hσ)
  simpa [hne'] using this

theorem exists_scalar_split [Finite K] [CharP K 2] {F' : List (Fin Tag.E7.rank → ℤ)}
    {γ : Fin Tag.E7.rank → ℤ} (hr : ∀ σ ∈ F' ++ [γ], IsRoot .E7 σ)
    (ho : (F' ++ [γ]).Pairwise fun σ σ' => iform σ σ' = 0) {c : K} (hc : c ≠ 0) :
    ∃ a : adjointGroup .E7 K, ∀ x : K, a⁻¹ * e7FrameElt K F' x * a = e7FrameElt K F' x ∧
      a⁻¹ * e7FrameElt K [γ] x * a = e7FrameElt K [γ] (c * x) := by
  have hγ := hr γ (List.mem_append_right _ (List.mem_singleton_self _))
  have hr₁ : ∀ σ ∈ F', IsRoot .E7 σ := fun σ hσ => hr σ (List.mem_append_left _ hσ)
  have ho₁ : ∀ σ ∈ F', iform γ σ = 0 := by
    intro σ hσ
    rw [List.pairwise_append] at ho
    rw [iform_comm]
    exact ho.2.2 σ hσ γ (List.mem_singleton_self _)
  obtain ⟨r, hr'⟩ := isSquare_of_charTwo' c
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc (by rw [hr', mul_zero])
  refine ⟨(e7FrameScale K [γ] (Units.mk0 r hr0))⁻¹, fun x => ⟨?_, ?_⟩⟩
  · rw [inv_inv, e7FrameScale_conj_head hγ hr₁ ho₁]
  · rw [inv_inv, e7FrameScale_conj_tail hγ, Units.val_mk0, sq, ← hr']

theorem isConj_e7FrameElt_one [Finite K] [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) {b : K}
    (hb : b ≠ 0) : IsConj (e7FrameElt K F 1) (e7FrameElt K F b) := by
  obtain ⟨r, hr'⟩ := isSquare_of_charTwo' b
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hb (by rw [hr', mul_zero])
  refine isConj_iff.2 ⟨e7FrameScale K F (Units.mk0 r hr0), ?_⟩
  rw [e7FrameScale_conj hr ho, Units.val_mk0, mul_one, sq, ← hr']

theorem isConj_e7FrameElt_word [CharP K 2] (ω : List (Fin Tag.E7.rank))
    {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ) :
    IsConj (e7FrameElt K F 1) (e7FramePt K (F.map fun σ => ω.foldr (reflect .E7) σ)) := by
  rw [e7FrameElt_one]
  exact isConj_e7FramePt_of_frameProdConj (E8.frameProdConj_word (K := K) ω hF)

theorem isConj_e7FramePt_head_u [Finite K] [CharP K 2] {b : K} (hb : b ≠ 0) :
    IsConj (e7FramePt K e7FrameY) (e7FrameElt K e7FrameUHead b) := by
  obtain ⟨-, -, hF, ho⟩ := e7Split_facts (F := e7FrameUHead) (by simp)
  have hr : ∀ σ ∈ e7FrameUHead, IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  have h1 := isConj_e7FrameElt_word (K := K) e7WordUHead hr
  rw [e7WordUHead_map] at h1
  exact h1.symm.trans (isConj_e7FrameElt_one hr ho hb)

theorem isConj_e7FramePt_head_v [Finite K] [CharP K 2] {b : K} (hb : b ≠ 0) :
    IsConj (e7FramePt K e7FrameZ) (e7FrameElt K e7FrameVHead b) := by
  obtain ⟨-, -, hF, ho⟩ := e7Split_facts (F := e7FrameVHead) (by simp)
  have hr : ∀ σ ∈ e7FrameVHead, IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  have h1 := isConj_e7FrameElt_word (K := K) e7WordVHead hr
  rw [e7WordVHead_map] at h1
  exact h1.symm.trans (isConj_e7FrameElt_one hr ho hb)

theorem isConj_e7FramePt_tail_u [Finite K] [CharP K 2] {c : K} (hc : c ≠ 0) :
    IsConj (e7FramePt K e7FrameX) (e7FrameElt K [e7FrameUTail] c) := by
  obtain ⟨-, -, hF, -⟩ := e7Split_facts (F := e7FrameU) (by simp)
  have hmem : e7FrameUTail ∈ e7FrameU := by
    rw [e7FrameU_eq_append]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hγ : IsRoot .E7 e7FrameUTail := (hF e7FrameUTail hmem).1
  have hr : ∀ σ ∈ [e7FrameUTail], IsRoot .E7 σ := fun σ hσ => by
    rw [List.mem_singleton] at hσ; subst hσ; exact hγ
  have h1 := isConj_e7FrameElt_word (K := K) e7WordUTail hr
  rw [e7WordUTail_map] at h1
  exact h1.symm.trans (isConj_e7FrameElt_one hr (List.pairwise_singleton _ _) hc)

theorem isConj_e7FramePt_tail_v [Finite K] [CharP K 2] {c : K} (hc : c ≠ 0) :
    IsConj (e7FramePt K e7FrameX) (e7FrameElt K [e7FrameVTail] c) := by
  obtain ⟨-, -, hF, -⟩ := e7Split_facts (F := e7FrameV) (by simp)
  have hmem : e7FrameVTail ∈ e7FrameV := by
    rw [e7FrameV_eq_append]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hγ : IsRoot .E7 e7FrameVTail := (hF e7FrameVTail hmem).1
  have hr : ∀ σ ∈ [e7FrameVTail], IsRoot .E7 σ := fun σ hσ => by
    rw [List.mem_singleton] at hσ; subst hσ; exact hγ
  have h1 := isConj_e7FrameElt_word (K := K) e7WordVTail hr
  rw [e7WordVTail_map] at h1
  exact h1.symm.trans (isConj_e7FrameElt_one hr (List.pairwise_singleton _ _) hc)

theorem residualMem_of_witness_isConj {C : Type*} [Group C] {t w : C} {P : Subgroup C}
    (hP : IsPGroup 2 P) (hPt : P ≤ closure {c | c * t = t * c ∧ Odd (orderOf c)})
    (ht : t ∈ ⁅P, P⁆) (h : IsConj t w) : Exc.ResidualMem w := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact E8.residualMem_conj_of_witness hP hPt ht g

theorem residualMem_e7FrameElt_head_u [Finite K] [CharP K 2] {b : K} (hb : b ≠ 0) :
    Exc.ResidualMem (e7FrameElt K e7FrameUHead b) := by
  obtain ⟨P, hP, hPt, ht⟩ := residual_witness_e7_y (K := K)
  exact residualMem_of_witness_isConj hP hPt ht
    ((isConj_e7FramePt_inner (K := K)).2.1.trans (isConj_e7FramePt_head_u hb))

theorem residualMem_e7FrameElt_head_v [Finite K] [CharP K 2] {b : K} (hb : b ≠ 0) :
    Exc.ResidualMem (e7FrameElt K e7FrameVHead b) := by
  obtain ⟨P, hP, hPt, ht⟩ := residual_witness_e7_z (K := K)
  exact residualMem_of_witness_isConj hP hPt ht
    ((isConj_e7FramePt_inner (K := K)).2.2.1.trans (isConj_e7FramePt_head_v hb))

theorem residualMem_e7FrameElt_tail_u [Finite K] [CharP K 2] {c : K} (hc : c ≠ 0) :
    Exc.ResidualMem (e7FrameElt K [e7FrameUTail] c) := by
  obtain ⟨P, hP, hPt, ht⟩ := residual_witness_e7_x (K := K)
  exact residualMem_of_witness_isConj hP hPt ht
    ((isConj_e7FramePt_inner (K := K)).1.trans (isConj_e7FramePt_tail_u hc))

theorem residualMem_e7FrameElt_tail_v [Finite K] [CharP K 2] {c : K} (hc : c ≠ 0) :
    Exc.ResidualMem (e7FrameElt K [e7FrameVTail] c) := by
  obtain ⟨P, hP, hPt, ht⟩ := residual_witness_e7_x (K := K)
  exact residualMem_of_witness_isConj hP hPt ht
    ((isConj_e7FramePt_inner (K := K)).1.trans (isConj_e7FramePt_tail_v hc))

theorem lineSplit_e7FrameU [Finite K] [CharP K 2] :
    Exc.LineSplit (e7FrameLine K e7FrameU) K (e7FrameElt K e7FrameUHead)
      (e7FrameElt K [e7FrameUTail]) Exc.ResidualMem := by
  obtain ⟨-, hnd, hF, ho⟩ := e7Split_facts (F := e7FrameU) (by simp)
  obtain ⟨hne₁, hnd₁, hF₁, ho₁⟩ := e7Split_facts (F := e7FrameUHead) (by simp)
  rw [e7FrameU_eq_append] at hnd hF ho ⊢
  have hr : ∀ σ ∈ e7FrameUHead ++ [e7FrameUTail], IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  have hr₁ : ∀ σ ∈ e7FrameUHead, IsRoot .E7 σ := fun σ hσ => (hF₁ σ hσ).1
  have hF₂ : ∀ σ ∈ [e7FrameUTail], IsRoot .E7 σ ∧ 0 < height σ := fun σ hσ =>
    hF σ (List.mem_append_right _ hσ)
  have hr₂ : ∀ σ ∈ [e7FrameUTail], IsRoot .E7 σ := fun σ hσ => (hF₂ σ hσ).1
  exact
    { map_add₁ := e7FrameElt_add hr₁ ho₁
      map_add₂ := e7FrameElt_add hr₂ (List.pairwise_singleton _ _)
      inj₁ := fun x hx => (e7FrameElt_eq_one_iff hne₁ hnd₁ hF₁).1 hx
      inj₂ := fun x hx =>
        (e7FrameElt_eq_one_iff (List.cons_ne_nil _ _) (List.nodup_singleton _) hF₂).1 hx
      comm := commute_e7FrameElt_head_tail hr ho
      inf := fun _ _ h => eq_zero_of_head_eq_tail hne₁ hnd hF h
      mem_iff := mem_e7FrameLine_split hr ho
      prop₁ := fun _ hx => residualMem_e7FrameElt_head_u hx
      prop₂ := fun _ hx => residualMem_e7FrameElt_tail_u hx
      scalar := fun _ hc => exists_scalar_split hr ho hc }

theorem lineSplit_e7FrameV [Finite K] [CharP K 2] :
    Exc.LineSplit (e7FrameLine K e7FrameV) K (e7FrameElt K e7FrameVHead)
      (e7FrameElt K [e7FrameVTail]) Exc.ResidualMem := by
  obtain ⟨-, hnd, hF, ho⟩ := e7Split_facts (F := e7FrameV) (by simp)
  obtain ⟨hne₁, hnd₁, hF₁, ho₁⟩ := e7Split_facts (F := e7FrameVHead) (by simp)
  rw [e7FrameV_eq_append] at hnd hF ho ⊢
  have hr : ∀ σ ∈ e7FrameVHead ++ [e7FrameVTail], IsRoot .E7 σ := fun σ hσ => (hF σ hσ).1
  have hr₁ : ∀ σ ∈ e7FrameVHead, IsRoot .E7 σ := fun σ hσ => (hF₁ σ hσ).1
  have hF₂ : ∀ σ ∈ [e7FrameVTail], IsRoot .E7 σ ∧ 0 < height σ := fun σ hσ =>
    hF σ (List.mem_append_right _ hσ)
  have hr₂ : ∀ σ ∈ [e7FrameVTail], IsRoot .E7 σ := fun σ hσ => (hF₂ σ hσ).1
  exact
    { map_add₁ := e7FrameElt_add hr₁ ho₁
      map_add₂ := e7FrameElt_add hr₂ (List.pairwise_singleton _ _)
      inj₁ := fun x hx => (e7FrameElt_eq_one_iff hne₁ hnd₁ hF₁).1 hx
      inj₂ := fun x hx =>
        (e7FrameElt_eq_one_iff (List.cons_ne_nil _ _) (List.nodup_singleton _) hF₂).1 hx
      comm := commute_e7FrameElt_head_tail hr ho
      inf := fun _ _ h => eq_zero_of_head_eq_tail hne₁ hnd hF h
      mem_iff := mem_e7FrameLine_split hr ho
      prop₁ := fun _ hx => residualMem_e7FrameElt_head_v hx
      prop₂ := fun _ hx => residualMem_e7FrameElt_tail_v hx
      scalar := fun _ hc => exists_scalar_split hr ho hc }

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
