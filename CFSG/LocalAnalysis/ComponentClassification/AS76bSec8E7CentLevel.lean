module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7LineTransport
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

variable {K : Type} [Field K]

theorem conjCoeff_smul (α : Fin Tag.E7.rank → ℤ) (t d : K) (l : List (Fin Tag.E7.rank → ℤ))
    (c : (Fin Tag.E7.rank → ℤ) → K) : conjCoeff α t l (d • c) = d • conjCoeff α t l c := by
  classical
  simp only [conjCoeff]
  induction l with
  | nil => simp
  | cons β l ih =>
    simp only [List.map_cons, List.sum_cons, smul_add, ih]
    congr 1
    ext ρ
    by_cases h : α ≠ β ∧ IsRoot .E7 (α + β)
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Pi.zero_apply, smul_eq_mul]
      split_ifs <;> ring

variable (K) in
@[expose] noncomputable def linConjSubgroup
    (l : List (Fin Tag.E7.rank → ℤ)) : Subgroup (ModGL .E7 K) where
  carrier := {g | (∀ c, ∃ c', g * rootProd .E7 K l c * g⁻¹ = rootProd .E7 K l c' ∧
      ∀ d : K, g * rootProd .E7 K l (d • c) * g⁻¹ = rootProd .E7 K l (d • c')) ∧
    (∀ c, ∃ c', g⁻¹ * rootProd .E7 K l c * g = rootProd .E7 K l c' ∧
      ∀ d : K, g⁻¹ * rootProd .E7 K l (d • c) * g = rootProd .E7 K l (d • c'))}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨fun c => ?_, fun c => ?_⟩
    · obtain ⟨c₁, e₁, f₁⟩ := hh c
      obtain ⟨c₂, e₂, f₂⟩ := hg c₁
      refine ⟨c₂, ?_, fun d => ?_⟩
      · rw [← e₂, ← e₁]
        group
      · rw [← f₂, ← f₁]
        group
    · obtain ⟨c₁, e₁, f₁⟩ := hg' c
      obtain ⟨c₂, e₂, f₂⟩ := hh' c₁
      refine ⟨c₂, ?_, fun d => ?_⟩
      · rw [← e₂, ← e₁]
        group
      · rw [← f₂, ← f₁]
        group
  one_mem' := ⟨fun c => ⟨c, by group, fun d => by group⟩, fun c => ⟨c, by group, fun d => by group⟩⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c => ?_⟩
    · obtain ⟨c', e, f⟩ := hg' c
      exact ⟨c', by rw [inv_inv]; exact e, fun d => by rw [inv_inv]; exact f d⟩
    · obtain ⟨c', e, f⟩ := hg c
      exact ⟨c', by rw [inv_inv]; exact e, fun d => by rw [inv_inv]; exact f d⟩

theorem commute_e7FrameLine_of_conj
    {F F' : List (Fin Tag.E7.rank → ℤ)} {n : adjointGroup .E7 K}
    (hn : ∀ d : K, n * e7FrameElt K F d * n⁻¹ = e7FrameElt K F' d)
    (hcomm : ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z) :
    ∀ z ∈ e7FrameLine K F', ∀ g ∈ Exc.cent (e7FramePt K F'), z * g = g * z := by
  intro z hz g hg
  rw [← map_conj_e7FrameLine_of hn] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hx : e7FramePt K F' = n * e7FramePt K F * n⁻¹ := by
    rw [← e7FrameElt_one, ← e7FrameElt_one, hn]
  have hg' : n⁻¹ * g * n ∈ Exc.cent (e7FramePt K F) := by
    rw [Exc.cent, mem_centralizer_singleton_iff] at hg ⊢
    rw [hx] at hg
    calc n⁻¹ * g * n * e7FramePt K F = n⁻¹ * (g * (n * e7FramePt K F * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * e7FramePt K F * n⁻¹) * g) * n := by rw [hg]
      _ = e7FramePt K F * (n⁻¹ * g * n) := by group
  have h1 := hcomm z₀ hz₀ _ hg'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc n * z₀ * n⁻¹ * g = n * (z₀ * (n⁻¹ * g * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * g * n) * z₀) * n⁻¹ := by rw [h1]
    _ = g * (n * z₀ * n⁻¹) := by group

section Gen


theorem pinnedX_mem_linConjSubgroup [CharP K 2] {l : List (Fin Tag.E7.rank → ℤ)}
    (hnd : l.Nodup) (hlr : ∀ β ∈ l, IsRoot .E7 β) (hl : RootCommFamily .E7 K l)
    {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hαl : ∀ β ∈ l, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ l)) (t : K) :
    pinnedX .E7 K α t ∈ linConjSubgroup K l := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hconj := fun (s : K) (c : (Fin Tag.E7.rank → ℤ) → K) =>
    E6Pilot.conj_rootProd hτ CharTwo.two_eq_zero hnd hlr hl hα hαl s c
  refine ⟨fun c => ⟨_, hconj t c, fun d => by rw [hconj t, conjCoeff_smul]⟩, fun c => ?_⟩
  refine ⟨conjCoeff α (-t) l c, ?_, fun d => ?_⟩
  · have h := hconj (-t) c
    rwa [← pinnedX_neg, inv_inv] at h
  · have h := hconj (-t) (d • c)
    rwa [← pinnedX_neg, inv_inv, conjCoeff_smul] at h

theorem torusGroup_le_linConjSubgroup {l : List (Fin Tag.E7.rank → ℤ)}
    (hlr : ∀ β ∈ l, IsRoot .E7 β) : torusGroup .E7 K ≤ linConjSubgroup K l := by
  intro h hh
  have hlin : ∀ g ∈ torusGroup .E7 K, ∀ c,
      ∃ c', g * rootProd .E7 K l c * g⁻¹ = rootProd .E7 K l c' ∧
        ∀ d : K, g * rootProd .E7 K l (d • c) * g⁻¹ = rootProd .E7 K l (d • c') := by
    intro g hg c
    refine ⟨_, E6Pilot.conj_rootProd_of_mem_torusGroup hg hlr c, fun d => ?_⟩
    rw [E6Pilot.conj_rootProd_of_mem_torusGroup hg hlr]
    congr 1
    ext β
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨hlin h hh, fun c => ?_⟩
  have := hlin h⁻¹ (inv_mem hh) c
  rwa [inv_inv] at this

theorem parabolicSubgroup_le_linConjSubgroup [CharP K 2] {l : List (Fin Tag.E7.rank → ℤ)}
    (hnd : l.Nodup) (hlr : ∀ β ∈ l, IsRoot .E7 β) (hl : RootCommFamily .E7 K l)
    {J : Set (Fin Tag.E7.rank)}
    (hrad : ∀ α ∈ parabolicRadicalRoots .E7 J,
      ∀ β ∈ l, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ l))
    (hlevi : ∀ j ∈ J, ∀ β ∈ l,
      ((Pi.single j 1 : Fin Tag.E7.rank → ℤ) ≠ -β ∧
        (IsRoot .E7 (Pi.single j 1 + β) → Pi.single j 1 + β ∈ l)) ∧
      ((-Pi.single j 1 : Fin Tag.E7.rank → ℤ) ≠ -β ∧
        (IsRoot .E7 (-Pi.single j 1 + β) → -Pi.single j 1 + β ∈ l))) :
    parabolicSubgroup .E7 K J ≤ linConjSubgroup K l := by
  rw [← parabolicRadical_sup_parabolicLevi J]
  refine sup_le (iSup₂_le fun α hα => (closure_le _).2 ?_) (sup_le
    (torusGroup_le_linConjSubgroup hlr) ((closure_le _).2 ?_))
  · rintro _ ⟨t, rfl⟩
    exact pinnedX_mem_linConjSubgroup hnd hlr hl hα.1.1 (hrad α hα) t
  · rintro _ ⟨j, hj, t, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact pinnedX_mem_linConjSubgroup hnd hlr hl (isRoot_single .E7 j)
        (fun β hβ => (hlevi j hj β hβ).1) t
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_linConjSubgroup hnd hlr hl (isRoot_neg_single .E7 j)
        (fun β hβ => (hlevi j hj β hβ).2) t

theorem rootProd_append_indicator {F l' : List (Fin Tag.E7.rank → ℤ)} (hnd : (F ++ l').Nodup)
    (d : K) :
    rootProd .E7 K (F ++ l') (d • fun β => if β ∈ F then (1 : K) else 0) =
      (e7FrameElt K F d : ModGL .E7 K) := by
  classical
  rw [E6Pilot.rootProd_append, coe_e7FrameElt]
  have h1 : rootProd .E7 K l' (d • fun β => if β ∈ F then (1 : K) else 0) = 1 := by
    have hdisj : ∀ β ∈ l', β ∉ F := fun β hβ hβF =>
      List.disjoint_of_nodup_append hnd hβF hβ
    simp only [rootProd]
    refine List.prod_eq_one fun g hg => ?_
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hg
    simp [hdisj β hβ, pinnedX_zero]
  rw [h1, mul_one]
  simp only [rootProd]
  congr 1
  refine List.map_congr_left fun β hβ => ?_
  simp [hβ]

theorem commute_e7FrameLine_of_le_parabolic [CharP K 2] {F l' : List (Fin Tag.E7.rank → ℤ)}
    (hnd : (F ++ l').Nodup) (hpos : ∀ β ∈ F ++ l', IsRoot .E7 β ∧ 0 < height β)
    (hl : RootCommFamily .E7 K (F ++ l')) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    {J : Set (Fin Tag.E7.rank)}
    (hrad : ∀ α ∈ parabolicRadicalRoots .E7 J,
      ∀ β ∈ F ++ l', α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ F ++ l'))
    (hlevi : ∀ j ∈ J, ∀ β ∈ F ++ l',
      ((Pi.single j 1 : Fin Tag.E7.rank → ℤ) ≠ -β ∧
        (IsRoot .E7 (Pi.single j 1 + β) → Pi.single j 1 + β ∈ F ++ l')) ∧
      ((-Pi.single j 1 : Fin Tag.E7.rank → ℤ) ≠ -β ∧
        (IsRoot .E7 (-Pi.single j 1 + β) → -Pi.single j 1 + β ∈ F ++ l')))
    (hC : ∀ g ∈ Exc.cent (e7FramePt K F), (g : ModGL .E7 K) ∈ parabolicSubgroup .E7 K J) :
    ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z := by
  classical
  have hlr : ∀ β ∈ F ++ l', IsRoot .E7 β := fun β hβ => (hpos β hβ).1
  have hr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => hlr σ (List.mem_append_left _ hσ)
  set cF : (Fin Tag.E7.rank → ℤ) → K := fun β => if β ∈ F then 1 else 0 with hcF
  intro z hz g hg
  obtain ⟨d, rfl⟩ := (mem_e7FrameLine hr ho).1 hz
  have hgP := parabolicSubgroup_le_linConjSubgroup (K := K) hnd hlr hl hrad hlevi (hC g hg)
  obtain ⟨c', e, f⟩ := hgP.1 cF
  have hfix : (g : ModGL .E7 K) * rootProd .E7 K (F ++ l') cF * (g : ModGL .E7 K)⁻¹ =
      rootProd .E7 K (F ++ l') cF := by
    have h1 := rootProd_append_indicator (K := K) hnd 1
    rw [one_smul] at h1
    rw [h1]
    have h2 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hg)
    rw [← e7FrameElt_one] at h2
    simp only [Subgroup.coe_mul] at h2
    rw [h2, mul_inv_cancel_right]
  have hc : ∀ β ∈ F ++ l', c' β = cF β := by
    have h3 : rootProd .E7 K (F ++ l') c' = rootProd .E7 K (F ++ l') cF := by rw [← e, hfix]
    exact (pinnedX_list_prod_injective (F ++ l') hnd hpos c' cF h3)
  have hd : (g : ModGL .E7 K) * (e7FrameElt K F d : ModGL .E7 K) * (g : ModGL .E7 K)⁻¹ =
      (e7FrameElt K F d : ModGL .E7 K) := by
    rw [← rootProd_append_indicator (K := K) hnd d, f d]
    simp only [rootProd]
    congr 1
    refine List.map_congr_left fun β hβ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hc β hβ, hcF]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc (e7FrameElt K F d : ModGL .E7 K) * (g : ModGL .E7 K) =
        (g : ModGL .E7 K) * (e7FrameElt K F d : ModGL .E7 K) * (g : ModGL .E7 K)⁻¹ *
          (g : ModGL .E7 K) := by rw [hd]
    _ = (g : ModGL .E7 K) * (e7FrameElt K F d : ModGL .E7 K) := by group

end Gen

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
