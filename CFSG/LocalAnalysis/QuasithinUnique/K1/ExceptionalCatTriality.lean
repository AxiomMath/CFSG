module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatCommon
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTrialityAlgebra
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatWeyl
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.K1.ExceptionalCat
open scoped commutatorElement

theorem add_of_hom {H : Type*} [Group H] {P A : Subgroup H} {M : Type*} [AddCommGroup M]
    (f : Multiplicative M →* P) (X : M → A)
    (hf : ∀ c : M, ((f (Multiplicative.ofAdd c) : P) : H) = (X c : H)) :
    ∀ c d : M, X (c + d) = X c * X d := by
  intro c d
  apply Subtype.ext
  have h1 := hf (c + d)
  rw [ofAdd_add, map_mul, Subgroup.coe_mul, hf c, hf d] at h1
  exact h1.symm

section StrongClosure

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem noStronglyClosedElemAbelian_triality
    :
    NoStronglyClosedElemAbelian (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
  have hQ : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊤ := by
    rw [← hP]
    exact isSylowTwoOf_top_iff.mpr ⟨P.isPGroup', P.not_dvd_index⟩
  obtain ⟨⟨f₁, hf₁i, hf₁⟩, ⟨f₂, hf₂i, hf₂⟩, ⟨f₃, hf₃i, hf₃⟩, ⟨f₄, hf₄i, hf₄⟩,
    ⟨f₅, hf₅i, hf₅⟩, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨k14, k34, k25, c15, c16, -, -, c26, c35, -, c45, c46, c56, htr, hnd⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have hCle := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  refine noStronglyClosedElemAbelian_of_witnesses _ hQ ?_
  intro z hz hz1 hzc
  have hzP : (z : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ := hz
  have a₁ := add_of_hom f₁ (trialityX₁ K τ₀) hf₁
  have a₂ := add_of_hom f₂ (trialityX₂ K τ₀) hf₂
  have a₃ := add_of_hom f₃ (trialityX₃ K τ₀) hf₃
  have a₄ := add_of_hom f₄ (trialityX₄ K τ₀) hf₄
  have a₅ := add_of_hom f₅ (trialityX₅ K τ₀) hf₅
  have a₆ := add_of_hom f₆ (trialityX₆ K τ₀) hf₆
  have mP : ∀ {M : Type} [AddCommGroup M] (f : Multiplicative M →* ↥(graphFixedPosUnipotent
      TwistTag.D4 K τ₀)) (X : M → adjointGroup TwistTag.D4.tag K),
      (∀ c : M, ((f (Multiplicative.ofAdd c) : graphFixedPosUnipotent TwistTag.D4 K τ₀) :
        ModGL TwistTag.D4.tag K) = (X c : ModGL TwistTag.D4.tag K)) →
      ∀ c, (X c : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun f X hf c => by rw [← hf c]; exact (f (Multiplicative.ofAdd c)).2
  have mP₁ := mP f₁ (trialityX₁ K τ₀) hf₁
  have mP₂ := mP f₂ (trialityX₂ K τ₀) hf₂
  have mP₄ := mP f₄ (trialityX₄ K τ₀) hf₄
  have mP₅ := mP f₅ (trialityX₅ K τ₀) hf₅
  obtain ⟨⟨a, b, c, d, e, f⟩, -, hzN⟩ := hbij.2.2 hzP
  have hzz' : (z : ModGL TwistTag.D4.tag K) =
      ((trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f : adjointGroup TwistTag.D4.tag K) :
          ModGL TwistTag.D4.tag K) := hzN.symm
  set Z' : adjointGroup TwistTag.D4.tag K :=
    trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
      trialityX₅ K τ₀ e * trialityX₆ K τ₀ f with hZ'
  have hcent : ∀ y : adjointGroup TwistTag.D4.tag K,
      (y : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ →
      y * Z' = Z' * y := by
    intro y hy
    have h := congrArg Subtype.val (hzc ⟨(y : ModGL TwistTag.D4.tag K), hCle hy⟩ hy)
    apply Subtype.ext
    have e1 : ((y * Z' : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (y : ModGL TwistTag.D4.tag K) * (Z' : ModGL TwistTag.D4.tag K) := rfl
    have e2 : ((Z' * y : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
        (Z' : ModGL TwistTag.D4.tag K) * (y : ModGL TwistTag.D4.tag K) := rfl
    rw [e1, e2, ← hzz']
    exact h
  have hnd₁ : ∀ s : K, (∀ t : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → s = 0 := fun s hs =>
    hnd.1 s fun t => (htr s t).trans (hs t)
  have hnd₂ : ∀ t : K, (∀ s : K, trialityTrace K τ₀ hσ3 (s * t) = 0) → t = 0 := fun t ht =>
    hnd.2 t fun s => (htr s t).trans (ht s)
  have inj : ∀ (a a' : K) (b b' : trialityFixedField K τ₀) (c c' d d' : K)
      (e e' f f' : trialityFixedField K τ₀),
      trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f =
      trialityX₁ K τ₀ a' * trialityX₂ K τ₀ b' * trialityX₃ K τ₀ c' * trialityX₄ K τ₀ d' *
        trialityX₅ K τ₀ e' * trialityX₆ K τ₀ f' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
    intro a a' b b' c c' d d' e e' f f' h
    have := hbij.2.1 (Set.mem_univ (a, b, c, d, e, f)) (Set.mem_univ (a', b', c', d', e', f'))
      (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at this
    exact this
  have key := triality_center_aux (trialityX₁ K τ₀) (trialityX₃ K τ₀) (trialityX₄ K τ₀)
    (trialityX₂ K τ₀) (trialityX₅ K τ₀) (trialityX₆ K τ₀)
    (fun s t => trialityTrace K τ₀ hσ3 (s * t)) (fun b e => b * e) (1 : trialityFixedField K τ₀)
    a₁ a₂ a₃ a₄ a₅ a₆ inj c15 c16 c26 c35 c45 c46 c56 k14 k34 k25 hnd₁ hnd₂
    (fun e => one_mul e) (fun b => mul_one b) a b c d e f
    (hcent _ (mP₅ 1)) (fun t => hcent _ (mP₄ t)) (fun t => hcent _ (mP₁ t))
    (hcent _ (mP₂ 1))
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key
  have z1 := zero_of_add (trialityX₁ K τ₀) a₁
  have z2 := zero_of_add (trialityX₂ K τ₀) a₂
  have z3 := zero_of_add (trialityX₃ K τ₀) a₃
  have z4 := zero_of_add (trialityX₄ K τ₀) a₄
  have z5 := zero_of_add (trialityX₅ K τ₀) a₅
  have z6 := zero_of_add (trialityX₆ K τ₀) a₆
  have hz6 : (z : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (f : K) := by
    rw [hzz', hZ', z1, z2, z3, z4, z5]
    simp only [one_mul]
    rfl
  have hf0 : (f : K) ≠ 0 := by
    intro h0
    apply hz1
    apply Subtype.ext
    simp [hz6, h0, pinnedX_zero]
  have hinj6 : ∀ u : trialityFixedField K τ₀, trialityX₆ K τ₀ u = 1 → u = 0 := fun u hu => by
    have h := inj 0 0 0 0 0 0 0 0 0 0 u 0 (by rw [z1, z2, z3, z4, z5, z6, hu])
    exact h.2.2.2.2.2
  let a₀ : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  let a₁' : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩
  have hn₀ := canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := τ₀) a₀
  have hn₁ := canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := τ₀) a₁'
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hroot5 : IsRoot TwistTag.D4.tag (trialityRoot 4) := (isRoot_trialityRoot 4 0).1
  have hr1 : TwistTag.D4.orbitReflection a₁' • trialityRoot 5 = trialityRoot 4 := by
    have hw : TwistTag.D4.orbitWord a₁' = [⟨2, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have hr0 : TwistTag.D4.orbitReflection a₀ • trialityRoot 4 = trialityRoot 1 := by
    have hw : TwistTag.D4.orbitWord a₀ =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  set n₀ := canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a₀)
    with hn₀def
  set n₁ := canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a₁')
    with hn₁def
  have hc1 : n₁ * pinnedX TwistTag.D4.tag K (trialityRoot 5) (f : K) * n₁⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 4) (f : K) := by
    rw [hn₁def, canonicalRep_conj_charTwo _ hroot6, hr1]
  have hc0 : n₀ * pinnedX TwistTag.D4.tag K (trialityRoot 4) (f : K) * n₀⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 1) (f : K) := by
    rw [hn₀def, canonicalRep_conj_charTwo _ hroot5, hr0]
  let g : graphFixedRootGroup TwistTag.D4 K τ₀ :=
    (⟨n₁, hn₁⟩ : graphFixedRootGroup TwistTag.D4 K τ₀)⁻¹
  let h : graphFixedRootGroup TwistTag.D4 K τ₀ :=
    (⟨n₀, hn₀⟩ * ⟨n₁, hn₁⟩ : graphFixedRootGroup TwistTag.D4 K τ₀)⁻¹
  have hgz : ((g⁻¹ * z * g : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) =
      ((trialityX₅ K τ₀ f : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    have e : ((g⁻¹ * z * g : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) =
        n₁ * (z : ModGL TwistTag.D4.tag K) * n₁⁻¹ := by
      simp only [g, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [e, hz6, hc1]
    rfl
  have hhz : ((h⁻¹ * z * h : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) =
      ((trialityX₂ K τ₀ f : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    have e : ((h⁻¹ * z * h : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) =
        n₀ * (n₁ * (z : ModGL TwistTag.D4.tag K) * n₁⁻¹) * n₀⁻¹ := by
      simp only [h, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev, mul_assoc]
    rw [e, hz6, hc1, hc0]
    rfl
  refine ⟨g, h, ?_, ?_, ?_⟩
  · show ((g⁻¹ * z * g : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K τ₀
    rw [hgz]
    exact mP₅ f
  · show ((h⁻¹ * z * h : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K τ₀
    rw [hhz]
    exact mP₂ f
  · intro hcomm
    have h1 : ((trialityX₅ K τ₀ f * trialityX₂ K τ₀ f : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) =
        ((trialityX₂ K τ₀ f * trialityX₅ K τ₀ f : adjointGroup TwistTag.D4.tag K) :
          ModGL TwistTag.D4.tag K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hgz, ← hhz]
      exact congrArg Subtype.val hcomm
    have h2 : trialityX₅ K τ₀ f * trialityX₂ K τ₀ f = trialityX₂ K τ₀ f * trialityX₅ K τ₀ f :=
      Subtype.ext h1
    have h3 : ⁅trialityX₂ K τ₀ f, trialityX₅ K τ₀ f⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr h2.symm
    rw [k25] at h3
    have h4 := hinj6 _ h3
    exact hf0 (congrArg Subtype.val (mul_self_eq_zero.mp h4))

end StrongClosure

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom

theorem sylowCentralizingAutInner_triality
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    SylowCentralizingAutInner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, hUV, hopp, -, -⟩ :=
    exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
  have hU : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀)) ⊤ := by
    rw [← hPU]
    exact isSylowTwoOf_top_iff.mpr ⟨PU.isPGroup', PU.not_dvd_index⟩
  have hV : IsSylowTwoOf ((graphFixedNegUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀)) ⊤ := by
    rw [← hPV]
    exact isSylowTwoOf_top_iff.mpr ⟨PV.isPGroup', PV.not_dvd_index⟩
  have hUV' : (graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀) ⊓
      (graphFixedNegUnipotent TwistTag.D4 K τ₀).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀ ⊓ graphFixedNegUnipotent TwistTag.D4 K τ₀ :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hUV, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  refine sylowCentralizingAutInner_of_opposite hU hV hUV' ?_ ?_
  · intro S hS hUS
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hS
    have hcoe : ((hp.toSylow hi : Sylow 2 (graphFixedRootGroup TwistTag.D4 K τ₀)) :
        Subgroup (graphFixedRootGroup TwistTag.D4 K τ₀)) = S := IsPGroup.toSylow_coe hp hi
    obtain ⟨u, hu, hSu⟩ := (hopp (hp.toSylow hi)).1 (by rw [hcoe]; exact hUS)
    exact ⟨u, hu, hcoe ▸ hSu⟩
  · rintro δ hUδ hVδ ⟨w, hwU, hw⟩
    have hδA : δ ∈ graphFixedUnipotentStabilizer TwistTag.D4 K τ₀ := ⟨hUδ, hVδ⟩
    obtain ⟨u, δ', hδ⟩ := exists_normalActor_eq_D4 Nat.prime_two hf hK σ hσ hδA
    have hX : ∀ (a : Fin TwistTag.D4.foldedTag.rank) (c : orbitField TwistTag.D4 K τ₀ a),
        ((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
          orbitFieldRestrict TwistTag.D4 σ δ' a c = c := by
      intro a c
      obtain ⟨hle, hnorm, -, hdec, -, huniq, -, -, -, -⟩ :=
        fixed_simple_positive_complement TwistTag.D4 K σ a
      have hxU : fixedOrbitX TwistTag.D4 K τ₀ a c ∈
          (graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K τ₀) := orbitX_mem_graphFixedPosUnipotent _ τ₀ a c
      have h1 : δ (fixedOrbitX TwistTag.D4 K τ₀ a c) = fixedOrbitX TwistTag.D4 K τ₀ a
          (((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
            orbitFieldRestrict TwistTag.D4 σ δ' a c) := by
        rw [hδ, normalActor_fixedOrbitX]
      have h2 := hw _ hxU
      have h3 : (w : ModGL TwistTag.D4.tag K) *
          (orbitX TwistTag.D4 K τ₀ a c : ModGL TwistTag.D4.tag K) *
            (w : ModGL TwistTag.D4.tag K)⁻¹ =
          (orbitX TwistTag.D4 K τ₀ a
            (((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
              orbitFieldRestrict TwistTag.D4 σ δ' a c) : ModGL TwistTag.D4.tag K) := by
        have := congrArg (fun g : graphFixedRootGroup TwistTag.D4 K τ₀ =>
          (g : ModGL TwistTag.D4.tag K)) (h2.symm.trans h1)
        exact this
      exact eq_of_conj_eq_of_complement
        (fun c : orbitField TwistTag.D4 K τ₀ a =>
          (orbitX TwistTag.D4 K τ₀ a c : ModGL TwistTag.D4.tag K))
        hle hnorm (fun c => orbitX_mem_graphFixedPosUnipotent _ τ₀ a c)
        (fun c c' => by
          rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← orbitX_add, ← orbitX_add, add_comm])
        hdec huniq (Subgroup.mem_subgroupOf.mp hwU) h3
    have hu : ∀ a, u a = 1 := fun a => by
      have h2 : ((u a : orbitField TwistTag.D4 K τ₀ a) : K) * δ' 1 = 1 :=
        congrArg Subtype.val (hX a 1)
      rw [map_one, mul_one] at h2
      exact Units.ext (Subtype.ext h2)
    have h0 : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ = ⊤ :=
      orbitField_D4_zero_eq_top σ (ringEquiv_cube_apply_eq hK hσ)
    have hδ'1 : δ' = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hmem : c ∈ orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ := by
        rw [h0]
        exact Subfield.mem_top c
      have h : ((u ⟨0, by decide⟩ : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩) : K) * δ' c = c :=
        congrArg Subtype.val (hX ⟨0, by decide⟩ ⟨c, hmem⟩)
      have hu0 : ((u ⟨0, by decide⟩ : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩) : K) = 1 :=
        congrArg (fun x : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ => (x : K))
          (congrArg Units.val (hu ⟨0, by decide⟩))
      rw [hu0, one_mul] at h
      exact h
    have hu1 : u = 1 := funext hu
    have hδ1 : normalActor σ u δ' = 1 := by
      rw [hu1, hδ'1, normalActor_one_right]
      exact map_one _
    exact hδ.trans hδ1

end Aut

theorem centralizes_of_triality
    {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 2 f)
    {w : G} (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨-, K, _, _, hK, σ₀, hσ₀, ⟨e⟩⟩ := hmodel
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega)
    (show Nat.card K = 2 ^ (f * 3) by rw [hK3, ← pow_mul])
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    rw [ringHom_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK3 hσ c
  obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK3 σ hσ
  exact centralizes_of_mulEquiv h (e.trans E) (noStronglyClosedElemAbelian_triality σ hσ3)
    (sylowCentralizingAutInner_triality σ hf hK3 hσ) hwU hwS

end CFSG.QuasithinUnique.K1
