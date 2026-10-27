module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Gen
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Weyl
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoIdx
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {K : Type} [Field K]

theorem d4Sign_congr {c c' : Fin TwistTag.D4.tag.rank → ℤ} (h : ∀ j, (c j - c' j) % 2 = 0) :
    d4Sign K c = d4Sign K c' := by
  funext j
  have h1 : (-1 : Kˣ) ^ (c j - c' j) = 1 := (Int.even_iff.2 (h j)).neg_one_zpow
  rw [zpow_sub, mul_inv_eq_one] at h1
  exact h1

theorem d4Sign_mul_self (c : Fin TwistTag.D4.tag.rank → ℤ) : d4Sign K c * d4Sign K c = 1 := by
  funext j
  change (-1 : Kˣ) ^ c j * (-1 : Kˣ) ^ c j = 1
  rw [← zpow_add, ← two_mul, zpow_mul]
  simp

theorem entrywise_rootDiagUnit_d4Sign (δ : K ≃+* K) (c : Fin TwistTag.D4.tag.rank → ℤ) :
    Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit TwistTag.D4.tag (d4Sign K c)) =
      rootDiagUnit TwistTag.D4.tag (d4Sign K c) := by
  rw [show Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit TwistTag.D4.tag (d4Sign K c)) =
      rootDiagUnit TwistTag.D4.tag (fun i => Units.map δ.toRingHom.toMonoidHom (d4Sign K c i)) from
    Units.ext (entrywise_rootDiag δ.toRingHom _)]
  congr 1
  funext i
  simp [d4Sign, map_zpow]

section Basic

variable (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4_torus_comm {x y : 𝒞}
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hy : (y : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    x * y = y * x := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hx).1
  apply Subtype.ext
  change (x : ModGL TwistTag.D4.tag K) * y = y * x
  rw [hl]
  exact rootDiagUnit_mul_comm_of_mem_torusGroup l (Subgroup.mem_inf.1 hy).1

@[expose] def d4TorTwo : Subgroup 𝒞 where
  carrier := {x | (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
    x * x = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have hc := d4_torus_comm σ hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = 1 := by rw [← mul_assoc, hx2, one_mul, hy2]
  one_mem' := ⟨one_mem _, mul_one 1⟩
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hx2, inv_one]

theorem isPGroup_d4TorTwo : IsPGroup 2 (d4TorTwo σ) := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, sq]; exact x.2.2)⟩

theorem d4TorTwo_comm : ∀ x ∈ d4TorTwo σ, ∀ y ∈ d4TorTwo σ, x * y = y * x :=
  fun _ hx _ hy => d4_torus_comm σ hx.1 hy.1

theorem map_d4TorTwo_le (φ : MulAut 𝒞)
    (hφ : ∀ x : 𝒞, (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      ((φ x : 𝒞) : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    (d4TorTwo σ).map φ.toMonoidHom ≤ d4TorTwo σ := by
  rintro _ ⟨x, ⟨hx, hx2⟩, rfl⟩
  exact ⟨hφ x hx, by rw [MulEquiv.coe_toMonoidHom, ← map_mul, hx2, map_one]⟩

theorem map_d4TorTwo (φ : MulAut 𝒞)
    (hφ : ∀ x : 𝒞, (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      ((φ x : 𝒞) : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hφ' : ∀ x : 𝒞, (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      ((φ⁻¹ x : 𝒞) : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    (d4TorTwo σ).map φ.toMonoidHom = d4TorTwo σ := by
  refine le_antisymm (map_d4TorTwo_le σ φ hφ) fun x hx => ?_
  refine ⟨φ⁻¹ x, map_d4TorTwo_le σ φ⁻¹ hφ' ⟨x, hx, rfl⟩, ?_⟩
  change φ (φ.symm x) = x
  exact φ.apply_symm_apply x

theorem graphFixedTorus_le_normalizer_U :
    graphFixedTorus TwistTag.D4 K σ.toRingHom ≤ Subgroup.normalizer
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
  intro h hh
  obtain ⟨hhH, hhΓ⟩ := Subgroup.mem_inf.1 hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent hhH) g
  constructor
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hN.1 hgU, mul_mem (mul_mem hhΓ hgΓ) (inv_mem hhΓ)⟩
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hN.2 hgU, ?_⟩
    have e : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhΓ) hgΓ) hhΓ

theorem rootDiagUnit_d4Sign_mem (c : Fin TwistTag.D4.tag.rank → ℤ) (i : Fin TwistTag.D4.tag.rank)
    (hci : ∀ j, (TwistTag.D4.tag.cartan i j - c j) % 2 = 0)
    (hρ : ∀ j, c (TwistTag.D4.perm.symm j) = c j) :
    rootDiagUnit TwistTag.D4.tag (d4Sign K c) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  have ht : torusElt TwistTag.D4.tag K i (-1) = rootDiagUnit TwistTag.D4.tag (d4Sign K c) := by
    rw [torusElt_eq_rootDiagUnit]
    exact congrArg _ (d4Sign_congr hci)
  refine Subgroup.mem_inf.2 ⟨ht ▸ torusElt_mem_torusGroup i (-1), ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨ht ▸ torusElt_mem_adjointGroup i (-1), ?_⟩
  rw [twistHom_rootDiagUnit_eq]
  congr 1
  funext j
  simp [d4Sign, hρ, map_zpow]

end Basic

section Full

variable
  [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem fieldActor_torus (δ : K ≃+* K) (x : 𝒞)
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ((fieldActor (t := TwistTag.D4) σ δ x : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom :=
  fieldActor_mem_graphFixedTorus σ δ hx

omit [Finite K] in
theorem conj_torus {n : 𝒞}
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom) (x : 𝒞)
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ((MulAut.conj n x : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, -, hnorm, -⟩ := fixed_monomial_quotient TwistTag.D4 K σ.toRingHom
  have hxM : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom :=
    graphFixedTorus_le_graphFixedMonomial _ _ _ hx
  have h := hnorm.conj_mem ⟨_, hxM⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨_, hn⟩
  rw [Subgroup.mem_subgroupOf] at h
  exact h

omit
  [Finite K] in
theorem coe_conj_rootDiagUnit_monoY (n : monoY σ) (b : Fin TwistTag.D4.tag.rank → Kˣ)
    (x : 𝒞) (hx : (x : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag b) :
    ((MulAut.conj (n : 𝒞) x : 𝒞) : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag (weylTuple (weylY σ n) b) := by
  have hnM : ((n : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom := Subgroup.mem_subgroupOf.1 n.2
  obtain ⟨w, k, hk, hnk⟩ := monomialSubgroup_le_torusWeylCosets
    (graphFixedMonomial_le_monomialSubgroup _ _ _ hnM)
  have hw : weylY σ n = w := by
    change graphFixedWeylHom TwistTag.D4 K σ.toRingHom ⟨((n : 𝒞) : ModGL TwistTag.D4.tag K), hnM⟩
      = w
    exact graphFixedWeylHom_eq (hnk ▸ mapsRootLines_mul_canonicalRep hk w)
  change ((n : 𝒞) : ModGL TwistTag.D4.tag K) * x * ((n : 𝒞) : ModGL TwistTag.D4.tag K)⁻¹ = _
  rw [hx, hw, hnk]
  have h3 := canonicalRep_conj_rootDiagUnit (K := K) w b
  have h4 := rootDiagUnit_mul_comm_of_mem_torusGroup (weylTuple w b) hk
  calc k * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootDiagUnit TwistTag.D4.tag b *
        (k * canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
      k * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) * k⁻¹ := by group
    _ = k * rootDiagUnit TwistTag.D4.tag (weylTuple w b) * k⁻¹ := by rw [h3]
    _ = rootDiagUnit TwistTag.D4.tag (weylTuple w b) := by
      rw [← h4, mul_inv_cancel_right]

end Full

end CFSG.OddStandard.GH71.S55
