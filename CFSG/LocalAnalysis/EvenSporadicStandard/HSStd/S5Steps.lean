module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction

@[expose] def derivedCentralizerIn {G : Type*} [Group G] (L : Subgroup G) (v : G) : Subgroup G :=
  (commutator ↥(centralizer ({v} : Set G) ⊓ L)).map (centralizer ({v} : Set G) ⊓ L).subtype

structure HSFusionData {G : Type*} [Group G] (L : Subgroup G) (t : G) (S : Subgroup G) (z n : G) :
    Prop where
  le : S ≤ centralizer ({t} : Set G)
  pgroup : IsPGroup 2 S
  index : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))
  zS : z ∈ S
  zL : z ∈ L
  z2 : orderOf z = 2
  zc : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z
  nS : n ∈ normalizer (S : Set G)
  nt : n * t * n⁻¹ = z * t

theorem sylowFusion_iff {G : Type} [Group G] (L : Subgroup G) (t : G) :
    SylowFusion L t ↔ ∃ (S : Subgroup G) (z n : G), HSFusionData L t S z n :=
  ⟨fun ⟨S, z, hle, hp, hi, hzS, hzL, hz2, hzc, n, hn, hnt⟩ =>
    ⟨S, z, n, ⟨hle, hp, hi, hzS, hzL, hz2, hzc, hn, hnt⟩⟩,
    fun ⟨S, z, n, h⟩ =>
      ⟨S, z, h.le, h.pgroup, h.index, h.zS, h.zL, h.z2, h.zc, n, h.nS, h.nt⟩⟩

structure HSOuterCtx {G : Type*} [Group G] [Finite G] (L : Subgroup G) (t : G) (S : Subgroup G)
    (z n v s : G) : Prop where
  fusion : HSFusionData L t S z n
  v_mem : v ∈ S
  v_outer : v ∉ L ⊔ zpowers t
  v_sq : v * v = 1
  v_cls : Nonempty (↥(centralizer ({v} : Set G) ⊓ L) ≃* Equiv.Perm (Fin 8))
  s_mem : s ∈ S
  s_conj : s * v * s⁻¹ = v * z

@[expose] def HSOuterChoice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2 →
        ∃ (S : Subgroup G) (z n v s : G), HSOuterCtx L t S z n v s ∧
          ¬ ((derivedCentralizerIn L v).subgroupOf (centralizer ({v} : Set G))).Normal ∧
          ¬ ((derivedCentralizerIn L (t * v)).subgroupOf (centralizer ({t * v} : Set G))).Normal

@[expose] def HSInnerFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) = L ⊔ zpowers t →
        ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
          (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
            φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
          ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e

end CFSG.EvenSporadicStandard.HSStd
