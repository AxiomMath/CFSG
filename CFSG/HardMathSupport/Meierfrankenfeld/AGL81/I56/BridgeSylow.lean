module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.QuasithinUnique

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_le {L S M : Subgroup G} (hS : IsSylowTwoOf S L) (hM : IsPGroup 2 M)
    (hSM : S ≤ M) (hML : M ≤ L) : M ≤ S := by
  have h1 : S.relIndex M * M.relIndex L = S.relIndex L := Subgroup.relIndex_mul_relIndex S M L hSM hML
  have hodd : ¬ 2 ∣ S.relIndex L := hS.2.2
  have h2 : ¬ 2 ∣ S.relIndex M := fun h => hodd (h1 ▸ h.mul_right _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' : IsPGroup 2 ↥M := hM
  obtain ⟨k, hk⟩ := hM'.index (S.subgroupOf M)
  have hk0 : k = 0 := by
    by_contra hk0
    exact h2 (by rw [Subgroup.relIndex, hk]; exact dvd_pow_self 2 hk0)
  rw [hk0, pow_zero] at hk
  have : S.relIndex M = 1 := hk
  exact (Subgroup.relIndex_eq_one.mp this)

theorem pCoreOf_le_of_sylow_shape {H L A T : Subgroup G} (hLH : L ≤ H) (hAH : A ≤ H)
    (hAn : A ≤ Subgroup.normalizer (L : Set G)) (hHA : H ≤ L ⊔ A) (hAT : A ≤ T)
    (hT : IsPGroup 2 T) (hTL : IsSylowTwoOf (T ⊓ L) L) : CFSG.Open.pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := (T ⊓ L) ⊔ A with hSdef
  have hSH : S ≤ H := sup_le (inf_le_right.trans hLH) hAH
  have hST : S ≤ T := sup_le inf_le_left hAT
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    (hT.to_le hST).of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨Q, hSQ⟩ := hS2.exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥H).map H.subtype with hRdef
  have hRH : IsSylowTwoOf R H := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · exact Q.isPGroup'.map H.subtype
    · have : R.subgroupOf H = Q :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [this]
      exact Q.not_dvd_index
  have hSR : S ≤ R := fun s hs =>
    ⟨⟨s, hSH hs⟩, hSQ (show (⟨s, hSH hs⟩ : ↥H) ∈ S.subgroupOf H from hs), rfl⟩
  have hR2 : IsPGroup 2 R := Q.isPGroup'.map H.subtype
  have hRS : R ≤ S := by
    intro r hr
    have hrH : r ∈ H := Subgroup.map_subtype_le _ hr
    obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_sup hAn (hHA hrH)
    have haR : a ∈ R := hSR (Subgroup.mem_sup_right ha)
    have hlR : l ∈ R := by
      have := R.mul_mem hr (R.inv_mem haR)
      simpa using this
    have hM2 : IsPGroup 2 (R ⊓ L : Subgroup G) := hR2.to_le inf_le_left
    have hle : T ⊓ L ≤ R ⊓ L := le_inf (fun x hx => hSR (Subgroup.mem_sup_left hx)) inf_le_right
    have hlT : l ∈ T ⊓ L := eq_of_isSylowTwoOf_le hTL hM2 hle inf_le_right ⟨hlR, hl⟩
    exact Subgroup.mul_mem_sup hlT ha
  exact (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hRH).trans (hRS.trans hST)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
