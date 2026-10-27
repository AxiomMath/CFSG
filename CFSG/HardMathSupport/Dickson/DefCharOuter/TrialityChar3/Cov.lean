module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3RedAlg
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

theorem CocycleData.eq_one_of_fix_mul {G : Type*} [Group G] {β : MulAut G} {N : ℕ → Subgroup G}
    {d : ℕ} {A : ℕ → Type*} [∀ k, CommGroup (A k)] {Φ : ∀ k, N k →* A k} {τ : ∀ k, A k →* A k}
    {b : ℕ → ℕ} (h : CocycleData β N d Φ τ b)
    (hlift : ∀ k < d, ∀ a ∈ (Φ k).range, τ k a = a → ∃ x : N k, β x = x ∧ Φ k x = a)
    (T : ∀ k, Subgroup (A k))
    (hT : ∀ k < d, ∀ a ∈ (Φ k).range, τ k a * a⁻¹ ∈ T k → τ k a = a)
    {y v : G} (hy : y ∈ N 0) (hβ : β y = y * v)
    (hv : ∀ k < d, ∀ hvk : v ∈ N k, Φ k ⟨v, hvk⟩ ∈ T k) : v = 1 := by
  have step : ∀ k (hk : k < d) (z : G), z ∈ N k → β z = z * v →
      ∃ z' : G, z' ∈ N (k + 1) ∧ β z' = z' * v := by
    intro k hk z hz hβz
    have hβzN : β z ∈ N k := h.stable k z hz
    have hvk : v ∈ N k := by
      have e : v = z⁻¹ * β z := by rw [hβz]; group
      rw [e]
      exact mul_mem (inv_mem hz) hβzN
    have hrange : Φ k ⟨z, hz⟩ ∈ (Φ k).range := MonoidHom.mem_range.2 ⟨⟨z, hz⟩, rfl⟩
    have ea : Φ k ⟨β z, hβzN⟩ = τ k (Φ k ⟨z, hz⟩) := h.act k hk ⟨z, hz⟩
    have eb : Φ k ⟨β z, hβzN⟩ = Φ k ⟨z, hz⟩ * Φ k ⟨v, hvk⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hβz
    have hTv : τ k (Φ k ⟨z, hz⟩) * (Φ k ⟨z, hz⟩)⁻¹ ∈ T k := by
      have e : τ k (Φ k ⟨z, hz⟩) * (Φ k ⟨z, hz⟩)⁻¹ = Φ k ⟨v, hvk⟩ := by
        rw [← ea, eb, mul_right_comm, mul_inv_cancel, one_mul]
      rw [e]
      exact hv k hk hvk
    have hτ := hT k hk _ hrange hTv
    obtain ⟨x, hxβ, hxΦ⟩ := hlift k hk _ hrange hτ
    have hxz : (x : G)⁻¹ * z ∈ N k := mul_mem (inv_mem x.2) hz
    have hΦ1 : Φ k ⟨(x : G)⁻¹ * z, hxz⟩ = 1 := by
      have e : (⟨(x : G)⁻¹ * z, hxz⟩ : N k) = x⁻¹ * ⟨z, hz⟩ :=
        Subtype.ext (by simp [Subgroup.coe_mul, Subgroup.coe_inv])
      rw [e, map_mul, map_inv, hxΦ, inv_mul_cancel]
    refine ⟨(x : G)⁻¹ * z, h.ker k hk ⟨(x : G)⁻¹ * z, hxz⟩ hΦ1, ?_⟩
    rw [map_mul, map_inv, hxβ, hβz, mul_assoc]
  have iter : ∀ j, j ≤ d → ∃ z : G, z ∈ N j ∧ β z = z * v := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨y, hy, hβ⟩
    | succ j ih =>
      intro hj
      obtain ⟨z, hz, hβz⟩ := ih (Nat.le_of_succ_le hj)
      exact step j (Nat.lt_of_succ_le hj) z hz hβz
  obtain ⟨z, hz, hβz⟩ := iter d le_rfl
  rw [h.bot, Subgroup.mem_bot] at hz
  subst hz
  rw [map_one, one_mul] at hβz
  exact hβz.symm


section Coordinates

variable {K : Type} [Field K] [Finite K]

private def singleSupp (k : ℕ) : Subgroup (LayerCoord (K := K) k) where
  carrier := {a | ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), O.1.card ≠ 1 →
    Multiplicative.toAdd a O = 0}
  mul_mem' := by
    intro a b ha hb O hO
    simp [ha O hO, hb O hO]
  one_mem' := by
    intro O _
    simp
  inv_mem' := by
    intro a ha O hO
    simp [ha O hO]

private theorem mem_singleSupp {k : ℕ} {a : LayerCoord (K := K) k} :
    a ∈ singleSupp (K := K) k ↔
      ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), O.1.card ≠ 1 →
        Multiplicative.toAdd a O = 0 :=
  Iff.rfl

private theorem cov_d4_height_four_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, 4 ≤ l.sum →
    l = [1, 1, 1, 1] ∨ l = [1, 1, 2, 1] := by
  decide

private theorem cov_height_ge_four {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hpos : 0 < height γ) (h4 : (4 : ℤ) ≤ height γ) :
    γ = rootC ∨ γ = rootD := by
  have hs : (4 : ℤ) ≤ (List.ofFn γ).sum := by
    rw [List.sum_ofFn]
    exact h4
  rcases cov_d4_height_four_check _ (isRoot_iff_mem_artifactRoots.1 hγ) hs with h | h
  · exact Or.inl (List.ofFn_injective (h.trans rfl))
  · exact Or.inr (List.ofFn_injective (h.trans rfl))

private theorem covB_root : IsRoot TwistTag.D4.tag rootB ∧ 0 < height rootB :=
  ⟨isRoot_rootB, by rw [height_rootB]; norm_num⟩

private theorem covC_root : IsRoot TwistTag.D4.tag rootC ∧ 0 < height rootC :=
  ⟨isRoot_rootC, by rw [height_rootC]; norm_num⟩

private theorem covD_root : IsRoot TwistTag.D4.tag rootD ∧ 0 < height rootD :=
  ⟨isRoot_rootD, by rw [height_rootD]; norm_num⟩

private theorem cov_rootB_fixed : permLattice TwistTag.D4.perm rootB = rootB := by
  decide +kernel

private theorem cov_rootC_fixed : permLattice TwistTag.D4.perm rootC = rootC := by
  decide

private theorem cov_rootD_fixed : permLattice TwistTag.D4.perm rootD = rootD := by
  decide

private theorem rootC_ne_rootB : rootC ≠ rootB := by decide
private theorem rootD_ne_rootB : rootD ≠ rootB := by decide
private theorem rootD_ne_rootC : rootD ≠ rootC := by decide

private theorem cov_diagramOrbit_eq_singleton {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (h : permLattice TwistTag.D4.perm γ = γ) : TwistTag.diagramOrbit TwistTag.D4 γ = {γ} := by
  have hk : ∀ k : ℕ, permLattice (TwistTag.D4.perm ^ k) γ = γ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [permLattice_pow_succ TwistTag.D4 TwistTag.D4.perm k γ, ih, h]
  ext β
  unfold TwistTag.diagramOrbit
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact hk k
  · rintro rfl
    exact ⟨0, by decide, hk 0⟩

private theorem cov_diagramOrbit_card {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (h : permLattice TwistTag.D4.perm γ = γ) : (TwistTag.diagramOrbit TwistTag.D4 γ).card = 1 := by
  rw [cov_diagramOrbit_eq_singleton h, Finset.card_singleton]

private theorem repOf_ne_of_fixed {h : ℤ} (O : ↥(orbitsAt TwistTag.D4 h)) (hO : O.1.card ≠ 1)
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : permLattice TwistTag.D4.perm γ = γ) :
    repOf TwistTag.D4 h O ≠ γ := by
  intro e
  apply hO
  rw [← (repOf_spec TwistTag.D4 h O).2.2, e, cov_diagramOrbit_card hγ]

private theorem mem_heightSeries_of_height_le {α γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ ∧ 0 < height γ) (hle : height α ≤ height γ) (c : K) :
    pinnedX TwistTag.D4.tag K γ c ∈ heightSeries TwistTag.D4.tag K (height α) :=
  heightSeries_antitone hle (pinnedX_mem_heightSeries_height hγ c)

private theorem coord_B_long (s r r' : K) :
    rootCoord covB_root (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r') = s := by
  have hBC : height rootB ≤ height rootC := by rw [height_rootB, height_rootC]; norm_num
  have hBD : height rootB ≤ height rootD := by rw [height_rootB, height_rootD]; norm_num
  rw [rootCoord_mul covB_root
      (mul_mem (pinnedX_mem_heightSeries_height covB_root s)
        (mem_heightSeries_of_height_le covC_root hBC r))
      (mem_heightSeries_of_height_le covD_root hBD r'),
    rootCoord_mul covB_root (pinnedX_mem_heightSeries_height covB_root s)
      (mem_heightSeries_of_height_le covC_root hBC r),
    rootCoord_self covB_root s, rootCoord_pinnedX_of_ne covB_root covC_root hBC rootC_ne_rootB r,
    rootCoord_pinnedX_of_ne covB_root covD_root hBD rootD_ne_rootB r', add_zero, add_zero]

private theorem coord_C_long (r r' : K) :
    rootCoord covC_root (pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r') =
      r := by
  have hCD : height rootC ≤ height rootD := by rw [height_rootC, height_rootD]; norm_num
  rw [rootCoord_mul covC_root (pinnedX_mem_heightSeries_height covC_root r)
      (mem_heightSeries_of_height_le covD_root hCD r'),
    rootCoord_self covC_root r, rootCoord_pinnedX_of_ne covC_root covD_root hCD rootD_ne_rootC r',
    add_zero]

private theorem coord_zero_of_le_one {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hαB : α ≠ rootB) (hαC : α ≠ rootC) (hαD : α ≠ rootD) (hle : height α ≤ 1) (s r r' : K) :
    rootCoord hα (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r') = 0 := by
  have hB : height α ≤ height rootB := by rw [height_rootB]; exact hle
  have hC : height α ≤ height rootC := by rw [height_rootC]; omega
  have hD : height α ≤ height rootD := by rw [height_rootD]; omega
  rw [rootCoord_mul hα
      (mul_mem (mem_heightSeries_of_height_le covB_root hB s)
        (mem_heightSeries_of_height_le covC_root hC r))
      (mem_heightSeries_of_height_le covD_root hD r'),
    rootCoord_mul hα (mem_heightSeries_of_height_le covB_root hB s)
      (mem_heightSeries_of_height_le covC_root hC r),
    rootCoord_pinnedX_of_ne hα covB_root hB (Ne.symm hαB) s,
    rootCoord_pinnedX_of_ne hα covC_root hC (Ne.symm hαC) r,
    rootCoord_pinnedX_of_ne hα covD_root hD (Ne.symm hαD) r', add_zero, add_zero]

private theorem coord_zero_of_two_le {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hαB : α ≠ rootB) (hαC : α ≠ rootC) (hαD : α ≠ rootD)
    (h2 : 2 ≤ height α) (h4 : height α ≤ 4) (s r r' : K)
    (hL : pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r' ∈ heightSeries TwistTag.D4.tag K (height α)) :
    rootCoord hα (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r') = 0 := by
  have hs : s = 0 := by
    have e2 : height rootB + 1 = 2 := by rw [height_rootB]; norm_num
    have hL2 : pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
        pinnedX TwistTag.D4.tag K rootD r' ∈ heightSeries TwistTag.D4.tag K (height rootB + 1) := by
      rw [e2]
      exact heightSeries_antitone h2 hL
    have h0 := rootCoord_of_mem_coordKer covB_root (heightSeries_succ_le_coordKer rootB hL2)
    rw [coord_B_long] at h0
    exact h0
  subst hs
  have hC : height α ≤ height rootC := by rw [height_rootC]; exact h4
  have hD : height α ≤ height rootD := by rw [height_rootD]; omega
  rw [pinnedX_zero, one_mul,
    rootCoord_mul hα (mem_heightSeries_of_height_le covC_root hC r)
      (mem_heightSeries_of_height_le covD_root hD r'),
    rootCoord_pinnedX_of_ne hα covC_root hC (Ne.symm hαC) r,
    rootCoord_pinnedX_of_ne hα covD_root hD (Ne.symm hαD) r', add_zero]

end Coordinates

section Layers

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

private theorem cov_toAdd_layerPhi {k : ℕ} (x : layerN σ k)
    (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)))
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hαO : α = repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :
    Multiplicative.toAdd (layerPhi σ k x) O =
      rootCoord hα ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) := by
  subst hαO
  rfl

private theorem cov_mem_layerN_zero (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    x ∈ layerN σ 0 ↔ (x : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K := by
  rw [mem_layerN]
  show (x : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 1 ↔ _
  rw [heightSeries_one]

end Layers

section Concrete

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem cov_lift {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    (a : LayerCoord (K := K) k) (hτ : layerTau σ k a = a) :
    ∃ x : layerN σ k,
      fieldActor (t := TwistTag.D4) σ σ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧ layerPhi σ k x = a := by
  classical
  have hσa : ∀ O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)),
      σ (Multiplicative.toAdd a O) = Multiplicative.toAdd a O := fun O =>
    congrArg (fun b : LayerCoord (K := K) k => Multiplicative.toAdd b O) hτ
  have key : ∀ S : Finset ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)), ∃ x : layerN σ k,
      fieldActor (t := TwistTag.D4) σ σ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      layerPhi σ k x = ∏ O ∈ S, Multiplicative.ofAdd (Pi.single O (Multiplicative.toAdd a O)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by rw [Subgroup.coe_one, map_one], by rw [map_one, Finset.prod_empty]⟩
    | @insert O S hO ih =>
      obtain ⟨x, hxδ, hxΦ⟩ := ih
      obtain ⟨y, hyΦ, hyδ⟩ :=
        exists_orbitElt hf hK σ hσ hk O (Multiplicative.toAdd a O) (fun _ => hσa O)
      refine ⟨x * y, ?_, ?_⟩
      · rw [Subgroup.coe_mul, map_mul, hxδ, hyδ (hσa O)]
      · rw [map_mul, hxΦ, hyΦ, Finset.prod_insert hO, mul_comm]
  obtain ⟨x, hxδ, hxΦ⟩ := key Finset.univ
  refine ⟨x, hxδ, hxΦ.trans ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  simp only [toAdd_ofAdd]
  rw [Finset.univ_sum_single]

private theorem cov_hT {k : ℕ} (hk : k < (maxHeight TwistTag.D4.tag).toNat)
    (a : LayerCoord (K := K) k) (ha : a ∈ (layerPhi σ k).range)
    (hc : layerTau σ k a * a⁻¹ ∈ singleSupp (K := K) k) : layerTau σ k a = a := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
  apply Multiplicative.toAdd.injective
  funext O
  by_cases hO : O.1.card = 1
  · exact layerPhi_apply_fixed hf hK σ hσ hk x O hO
  · have h0 : Multiplicative.toAdd (layerTau σ k (layerPhi σ k x) * (layerPhi σ k x)⁻¹) O = 0 :=
      mem_singleSupp.1 hc O hO
    have e : Multiplicative.toAdd (layerTau σ k (layerPhi σ k x)) O =
        σ (Multiplicative.toAdd (layerPhi σ k x) O) := rfl
    rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, e]
      at h0
    rw [e]
    linear_combination h0

theorem fieldActor_eq_mul_long_imp (u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (s r r' : K) (hs : σ s = s) (hr : σ r = r) (hr' : σ r' = r')
    (h : fieldActor (t := TwistTag.D4) σ σ u =
      u * (longElt hf hK σ hσ (Or.inl rfl) s hs * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr')) :
    s = 0 ∧ r = 0 ∧ r' = 0 := by
  classical
  obtain ⟨v, hvdef⟩ : ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      v = longElt hf hK σ hσ (Or.inl rfl) s hs * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' := ⟨_, rfl⟩
  have hβ : fieldActor (t := TwistTag.D4) σ σ u = u * v := by
    rw [hvdef]
    exact h
  have hvL : ((v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
        pinnedX TwistTag.D4.tag K rootD r' := by
    rw [hvdef, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_longElt hf hK σ hσ (Or.inl rfl) s hs,
      coe_longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr,
      coe_longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr']
  have hu0 : u ∈ layerN σ 0 := (cov_mem_layerN_zero σ u).2 (Subgroup.mem_inf.1 hu).1
  have hlift : ∀ k < (maxHeight TwistTag.D4.tag).toNat, ∀ a ∈ (layerPhi σ k).range,
      layerTau σ k a = a → ∃ x : layerN σ k,
        fieldActor (t := TwistTag.D4) σ σ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
          (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧ layerPhi σ k x = a :=
    fun k hk a _ hτ => cov_lift hf hK σ hσ hk a hτ
  have hT : ∀ k < (maxHeight TwistTag.D4.tag).toNat, ∀ a ∈ (layerPhi σ k).range,
      layerTau σ k a * a⁻¹ ∈ singleSupp (K := K) k → layerTau σ k a = a :=
    fun k hk a ha hc => cov_hT hf hK σ hσ hk a ha hc
  have hv : ∀ k < (maxHeight TwistTag.D4.tag).toNat, ∀ hvk : v ∈ layerN σ k,
      layerPhi σ k ⟨v, hvk⟩ ∈ singleSupp (K := K) k := by
    intro k _ hvk
    rw [mem_singleSupp]
    intro O hO
    have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
    have hαroot : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) ∧
        0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :=
      ⟨hrep.1, by rw [hrep.2.1]; positivity⟩
    rw [cov_toAdd_layerPhi σ ⟨v, hvk⟩ O hαroot rfl]
    change rootCoord hαroot ((v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = 0
    rw [hvL]
    have hLmem : pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
        pinnedX TwistTag.D4.tag K rootD r' ∈
          heightSeries TwistTag.D4.tag K (height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)) := by
      rw [← hvL, hrep.2.1]
      exact (mem_layerN σ).1 hvk
    have hαB := repOf_ne_of_fixed O hO cov_rootB_fixed
    have hαC := repOf_ne_of_fixed O hO cov_rootC_fixed
    have hαD := repOf_ne_of_fixed O hO cov_rootD_fixed
    rcases le_or_gt (height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)) 3 with h3 | h3
    · rcases le_or_gt (height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)) 1 with h1 | h1
      · exact coord_zero_of_le_one hαroot hαB hαC hαD h1 s r r'
      · exact coord_zero_of_two_le hαroot hαB hαC hαD (by omega) (by omega) s r r' hLmem
    · rcases cov_height_ge_four hαroot.1 hαroot.2 (by omega) with h | h
      · exact absurd h hαC
      · exact absurd h hαD
  have hv1 : v = 1 :=
    CocycleData.eq_one_of_fix_mul (cocycleData_delta0 σ) hlift (fun k => singleSupp (K := K) k)
      hT hu0 hβ hv
  have hL1 : pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r' = 1 := by
    rw [← hvL, hv1, Subgroup.coe_one]
  have hs0 : s = 0 := by
    have h := coord_B_long s r r'
    rw [hL1, rootCoord_one] at h
    exact h.symm
  subst hs0
  rw [pinnedX_zero, one_mul] at hL1
  have hr0 : r = 0 := by
    have h := coord_C_long r r'
    rw [hL1, rootCoord_one] at h
    exact h.symm
  subst hr0
  rw [pinnedX_zero, one_mul] at hL1
  have hr'0 : r' = 0 := by
    have h := rootCoord_self covD_root r'
    rw [hL1, rootCoord_one] at h
    exact h.symm
  exact ⟨rfl, rfl, hr'0⟩

end Concrete

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
