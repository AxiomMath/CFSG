module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest6

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure Rest6Config {G : Type} [Group G] [Finite G] (L : Subgroup G) (z t : G)
    (T₀ E : Subgroup G) (Q : Sylow 2 G) (x β : G) (B : Subgroup G) : Prop where
  std : StdHyp G L
  sporadic : IsSporadic L .J2 ∨ IsSporadic L .J3
  card_sylow : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  inner : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G)
  cfg : InnerConfig G L z t T₀
  econfig : EConfig L T₀ E t
  weak : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T₀ ⊔ zpowers z →
    E.map (MulAut.conj g).toMonoidHom = E
  norm : ∀ y ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G), y ∈ normalizer (E : Set G)
  shape : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → S = zpowers z ⊔ zpowers t ∨
      (∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n)
  le_Q : T₀ ⊔ zpowers z ≤ (Q : Subgroup G)
  x_mem : x ∈ (Q : Subgroup G)
  x_not_mem : x ∉ T₀ ⊔ zpowers z
  x_norm : x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G)
  x_z : x * z * x⁻¹ = z * t
  x_t : x * t * x⁻¹ = t
  t_central : ∀ q ∈ (Q : Subgroup G), q * t = t * q
  B_le : B ≤ L
  B_cent : B ≤ centralizer ({t} : Set G)
  B_iso : Nonempty (↥B ≃* alternatingGroup (Fin 5))
  beta_mem : β ∈ B
  beta_order : orderOf β = 3
  lemma64 : ∃ hz : z ∈ centralizer ({β} : Set G),
    Lemma64Conclusion ↥(centralizer ({β} : Set G))
      (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))

theorem exists_maximal_two_subgroup {G : Type*} [Group G] [Finite G] (C : Subgroup G) {z : G}
    (hz : z ∈ C) (hz2 : orderOf z = 2) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ C ∧
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ C → S ≤ R → R = S) ∧ z ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2' : orderOf (⟨z, hz⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hZ : IsPGroup 2 (zpowers (⟨z, hz⟩ : C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2']; norm_num)
  obtain ⟨P, hP⟩ := hZ.exists_le_sylow
  refine ⟨(P : Subgroup C).map C.subtype, P.isPGroup'.map _, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro R hR hRC hSR
    have hR' : IsPGroup 2 (R.subgroupOf C) := hR.comap_subtype
    have hle : (P : Subgroup C) ≤ R.subgroupOf C := fun y hy =>
      mem_subgroupOf.2 (hSR ⟨y, hy, rfl⟩)
    have heq : R.subgroupOf C = (P : Subgroup C) := P.is_maximal' hR' hle
    refine le_antisymm (fun r hr => ?_) hSR
    have hr' : (⟨r, hRC hr⟩ : C) ∈ R.subgroupOf C := mem_subgroupOf.2 hr
    rw [heq] at hr'
    exact ⟨_, hr', rfl⟩
  · exact ⟨⟨z, hz⟩, hP (mem_zpowers _), rfl⟩

@[expose] def Fin76bLemma65b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      Nonempty (S ≃* DihedralGroup 4) ∧ ∀ b ∈ B, ∀ s ∈ S, b * s = s * b

@[expose] def Fin76bInnerRest₇ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
      (∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) → False

theorem fin76bInnerRest₆_of_rest₇ (h65 : Fin76bLemma65b) (hR : Fin76bInnerRest₇) :
    Fin76bInnerRest₆ := by
  intro G _ _ L z t T₀ E Q x β B h hJ hS hinner hcfg hE hw hn hS2 hTQ hxQ hxT hxN hxz hxt hQt hBL
    hBt hBiso hβB hβ3 h64
  have hconf : Rest6Config L z t T₀ E Q x β B :=
    ⟨h, hJ, hS, hinner, hcfg, hE, hw, hn, hS2, hTQ, hxQ, hxT, hxN, hxz, hxt, hQt, hBL, hBt, hBiso,
      hβB, hβ3, h64⟩
  obtain ⟨S, hSp, hSC, hSmax, hzS⟩ := exists_maximal_two_subgroup (centralizer (E : Set G))
    (hE.z_mem_centralizer hcfg) hcfg.z_order
  obtain ⟨hD8, hBS⟩ := h65 G L z t T₀ E Q x β B hconf S hSp hSC hSmax hzS
  obtain ⟨e⟩ := hD8
  have hodd := hE.centralizer_oddCore_dihedral hcfg hSp hSC hSmax (k := 2) (by norm_num) ⟨e⟩
  exact hR G L z t T₀ E Q x β B hconf S hSp hSC hSmax hzS ⟨e⟩ hBS hodd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end CFSG.EvenSporadicStandard.Fin76b
