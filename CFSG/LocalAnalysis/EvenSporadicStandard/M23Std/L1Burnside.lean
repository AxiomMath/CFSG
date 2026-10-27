module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.L1Sylow

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

theorem exists_normal_two_complement (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) :
    ∃ N : Subgroup G, N ≤ centralizer (L1sub h D hgood : Set G) ∧
      (∀ c ∈ centralizer (L1sub h D hgood : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) ∧
      ¬ 2 ∣ Nat.card N ∧ Disjoint N (L1sub h D hgood) ∧
      N ⊔ L1sub h D hgood = centralizer (L1sub h D hgood : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL1P, hodd⟩ := L1_sylow h hZ D hgood X htrans hR
  set L1 := L1sub h D hgood with hL1
  set C := centralizer (L1 : Set G) with hC
  have hL1C : L1 ≤ C := fun x hx =>
    mem_centralizer_iff.2 fun y hy => L1sub_comm h D hgood hy hx
  let P : Sylow 2 C := (hL1P.comap_subtype (K := C)).toSylow hodd
  have hPmem : ∀ x : C, x ∈ (P : Subgroup C) ↔ (x : G) ∈ L1 := fun x => Iff.rfl
  have hP : normalizer (P : Set C) ≤ centralizer (P : Set C) := by
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (mem_centralizer_iff.1 g.2 (x : G) ((hPmem x).1 hx))
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  let Nk : Subgroup C := (MonoidHom.transferSylow P hP).ker
  refine ⟨Nk.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rintro c hc _ ⟨k, hk, rfl⟩
    refine ⟨⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    exact (MonoidHom.normal_ker _).conj_mem k hk ⟨c, hc⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact MonoidHom.not_dvd_card_ker_transferSylow P hP
  · rw [Subgroup.disjoint_def]
    rintro x ⟨k, hk, rfl⟩ hx
    have hkP : k ∈ (P : Subgroup C) := (hPmem k).2 hx
    have hdis := MonoidHom.ker_transferSylow_disjoint P hP (P : Subgroup C) P.isPGroup'
    have := Subgroup.disjoint_def.1 hdis hk hkP
    rw [this]
    rfl
  · refine le_antisymm (sup_le (by rintro _ ⟨k, -, rfl⟩; exact k.2) hL1C) fun c hc => ?_
    obtain ⟨⟨k, p⟩, hkp⟩ := hcompl.2 ⟨c, hc⟩
    have hc' : c = (k : C) * (p : C) := congrArg Subtype.val hkp.symm
    rw [hc']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, k.2, rfl⟩)
      (Subgroup.mem_sup_right ((hPmem (p : C)).1 p.2))

end CFSG.EvenSporadicStandard.M23Std
