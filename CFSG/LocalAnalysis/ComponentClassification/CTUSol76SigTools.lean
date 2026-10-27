module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L33
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G]

theorem three_subgroups_rel {X Y Z N : Subgroup G}
    (hX : X ≤ normalizer (N : Set G)) (hY : Y ≤ normalizer (N : Set G))
    (hZ : Z ≤ normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set K := normalizer (N : Set G)
  have hN : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hmap : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf K, B.subgroupOf K⁆, C.subgroupOf K⁆).map K.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔
        ⁅⁅(A.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)),
          (B.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆,
          (C.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem commutator_le_of_eq_commutator {M X V O : Subgroup G}
    (hXM : X ≤ normalizer (M : Set G)) (hXO : X ≤ normalizer (O : Set G))
    (hVO : V ≤ normalizer (O : Set G)) (hMO : M ≤ normalizer (O : Set G))
    (hMV : ⁅M, V⁆ ≤ O) (hXV : ⁅X, V⁆ = X) : ⁅M, X⁆ ≤ O := by
  have h1 : ⁅⁅V, M⁆, X⁆ ≤ O := by
    rw [commutator_comm V M]
    exact (Subgroup.commutator_mono hMV le_rfl).trans
      (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing O X hXO)
  have h2 : ⁅⁅M, X⁆, V⁆ ≤ O := by
    have hMX : ⁅M, X⁆ ≤ M :=
      CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing M X hXM
    exact (Subgroup.commutator_mono hMX le_rfl).trans hMV
  have h3 := three_subgroups_rel hVO hMO hXO h1 h2
  rw [hXV] at h3
  rwa [commutator_comm]

variable [Finite G]

theorem not_le_oddCoreIn_of_isTwoComponentIn {M C : Subgroup G} (hM : IsTwoComponentIn M C) :
    ¬ M ≤ oddCoreIn M := by
  intro hle
  obtain ⟨b, hbM, hb2⟩ := Sol76T13.exists_orderOf_eq_two_of_isTwoComponentIn hM
  have hodd := coprime_card_oddCoreIn M
  have h1 : orderOf b ∣ Nat.card (oddCoreIn M) := by
    have h3 := orderOf_dvd_natCard (⟨b, hle hbM⟩ : oddCoreIn M)
    rwa [Subgroup.orderOf_mk] at h3
  rw [hb2] at h1
  exact absurd (Nat.Coprime.coprime_dvd_right h1 hodd) (by norm_num)

theorem le_oddCoreIn_of_commutator_le {C X : Subgroup G} (hXC : X ≤ C)
    (hodd : Odd (Nat.card X)) (hO22 : ⁅oddTwoCoreIn C, X⁆ ≤ oddCoreIn C)
    (hcomp : ∀ M : Subgroup G, IsTwoComponentIn M C → ⁅M, X⁆ ≤ oddCoreIn C) :
    X ≤ oddCoreIn C := by
  have hodd' : Odd (Nat.card (X.subgroupOf C)) := by
    rw [← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hXC]
    exact hodd
  have hmem : ∀ {y d : ↥C}, ((y : G) ∈ C → (y : G)⁻¹ ∈ C) → True := fun _ => trivial
  clear hmem
  have hle := GrSLit.le_pPrimeCore_of_commutators hodd' (fun y hy d hd => by
      have h1 : ((⁅y⁻¹, d⁻¹⁆ : ↥C) : G) ∈ ⁅oddTwoCoreIn C, X⁆ :=
        commutator_mem_commutator ⟨y⁻¹, inv_mem (mem_comap.mp hy), rfl⟩
          (mem_subgroupOf.mp (inv_mem hd))
      have h2 : ⁅y⁻¹, d⁻¹⁆ ∈ pPrimeCore 2 ↥C :=
        (mem_map_iff_mem C.subtype_injective).mp (hO22 h1)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h2)
    (fun M' hM' y hy d hd => by
      have hMM : (M'.map C.subtype).subgroupOf C = M' :=
        comap_map_eq_self_of_injective C.subtype_injective M'
      have hM'2 : IsTwoComponentIn (M'.map C.subtype) C := ⟨map_subtype_le M', hMM.symm ▸ hM'⟩
      have h1 : ((⁅y⁻¹, d⁻¹⁆ : ↥C) : G) ∈ ⁅M'.map C.subtype, X⁆ :=
        commutator_mem_commutator (mem_map_of_mem _ (inv_mem hy))
          (mem_subgroupOf.mp (inv_mem hd))
      have h2 : ⁅y⁻¹, d⁻¹⁆ ∈ pPrimeCore 2 ↥C :=
        (mem_map_iff_mem C.subtype_injective).mp (hcomp _ hM'2 h1)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h2)
  intro x hx
  exact ⟨_, hle (mem_subgroupOf.mpr (show ((⟨x, hXC hx⟩ : ↥C) : G) ∈ X from hx)), rfl⟩

theorem sol25 {S T : Subgroup G} (hS : S ≠ ⊥) (hT : T ≠ ⊥) (hSe : CFSG.Open.IsElemAbelian 2 S)
    (hTe : CFSG.Open.IsElemAbelian 2 T) (hST : S ≤ centralizer (T : Set G)) :
    ⁅oddTwoCoreIn (centralizer (T : Set G)),
        oddCoreIn (centralizer (S : Set G)) ⊓ centralizer (T : Set G)⁆ ≤
      oddCoreIn (centralizer (T : Set G)) ∧
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer (T : Set G)) →
      oddCoreIn (centralizer (S : Set G)) ⊓ centralizer (T : Set G) ≤
          normalizer (M : Set G) ∧
        (¬ ⁅M, oddCoreIn (centralizer (S : Set G)) ⊓ centralizer (T : Set G)⁆ ≤ oddCoreIn M →
          S ⊓ normalizer (M : Set G) ≠ ⊥ ∧
            oddCoreIn M ⊔ ⁅M, S ⊓ normalizer (M : Set G)⁆ = M) := by
  have hcomm : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A → ∀ x ∈ A, ∀ y ∈ A,
      x * y = y * x := fun A hA x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsq : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A → ∀ x ∈ A, x * x = 1 :=
    fun A hA x hx => by rw [← pow_two]; exact hA.2 x hx
  have hST' : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    ((mem_centralizer_iff.mp (hST hx)) y hy).symm
  have hh := GrSLit.solomonCommutingCoreInput G S T hS hT (hcomm S hSe) (hsq S hSe)
    (hcomm T hTe) (hsq T hTe) hST'
  dsimp only at hh
  obtain ⟨⟨h1, -⟩, h2, -⟩ := hh
  refine ⟨h1, fun M hM => ?_⟩
  obtain ⟨hDN, hc⟩ := h2 M hM.1 hM.2
  refine ⟨hDN, fun hn => ?_⟩
  obtain ⟨hSL, -, hL2⟩ := hc hn
  exact ⟨hSL, hL2⟩

theorem commutator_le_oddCoreIn_of_not_moves {S T M X : Subgroup G} (hS : S ≠ ⊥) (hT : T ≠ ⊥)
    (hSe : CFSG.Open.IsElemAbelian 2 S) (hTe : CFSG.Open.IsElemAbelian 2 T)
    (hST : S ≤ centralizer (T : Set G)) (hM : IsTwoComponentIn M (centralizer (T : Set G)))
    (hX : X ≤ oddCoreIn (centralizer (S : Set G)) ⊓ centralizer (T : Set G))
    (hmove : S ⊓ normalizer (M : Set G) = ⊥ ∨
      ⁅M, S ⊓ normalizer (M : Set G)⁆ ≤ oddCoreIn M) :
    ⁅M, X⁆ ≤ oddCoreIn M := by
  refine (Subgroup.commutator_mono le_rfl hX).trans ?_
  by_contra hn
  obtain ⟨hSL, hL2⟩ := ((sol25 hS hT hSe hTe hST).2 M hM).2 hn
  rcases hmove with h | h
  · exact hSL h
  · rw [sup_eq_left.mpr h] at hL2
    exact not_le_oddCoreIn_of_isTwoComponentIn hM hL2.ge

end CFSG.ComponentClassification.Sol76.Sig
