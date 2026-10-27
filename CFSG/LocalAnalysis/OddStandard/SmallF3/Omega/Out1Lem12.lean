module

public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12End
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12N2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12R

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem aor_l12_gen3 {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {t : S}
    (ht : orderOf t = 2)
    (hR : Nonempty (↥(centralizer ({t} : Set S)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))))
    (P : Subgroup S) : ∃ s : Finset S, s.card ≤ 3 ∧ closure (s : Set S) = P := by
  rcases aor_l12_coord_or_square ht hR with ⟨u, hu⟩ | hsq
  · by_cases hc : ∀ x : S, x * t = t * x
    · exact aor_gen_of_card_le (k := 3) ((aor_l12_card_of_central hR hc).le.trans (by norm_num)) P
    · obtain ⟨u₀, hM⟩ := aor_l12_main hS hu hc
      exact aor_l12_end hS hM P
  · exact aor_gen_of_card_le (k := 3) ((aor_l12_card_of_square hS hR hsq).le.trans (by norm_num)) P

theorem aor_l12_cent_equiv {G : Type} [Group G] (T : Subgroup G) {t : G} (ht : t ∈ T) :
    Nonempty (↥(centralizer ({(⟨t, ht⟩ : ↥T)} : Set ↥T)) ≃*
      ↥(T ⊓ centralizer ({t} : Set G))) := by
  have key : ∀ x : ↥T, x ∈ centralizer ({(⟨t, ht⟩ : ↥T)} : Set ↥T) ↔
      (x : G) ∈ centralizer ({t} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let f : ↥(centralizer ({(⟨t, ht⟩ : ↥T)} : Set ↥T)) →* ↥(T ⊓ centralizer ({t} : Set G)) :=
    { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2, (key x.1).mp x.2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y hxy
    have h1 : ((f x : ↥(T ⊓ centralizer ({t} : Set G))) : G) =
        ((f y : ↥(T ⊓ centralizer ({t} : Set G))) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  · rintro ⟨g, hg⟩
    obtain ⟨hgT, hgC⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨⟨g, hgT⟩, (key ⟨g, hgT⟩).mpr hgC⟩, rfl⟩

theorem asc82Lemma12_holds : ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsPGroup 2 T →
    ∀ t : G, t ∈ T → orderOf t = 2 →
      Nonempty (↥(T ⊓ centralizer ({t} : Set G)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) →
        CFSG.GH74.sectionalTwoRank T ≤ 3 := by
  intro G _ _ T hT t htT ht hR
  obtain ⟨e⟩ := hR
  obtain ⟨c⟩ := aor_l12_cent_equiv T htT
  have ht' : orderOf (⟨t, htT⟩ : ↥T) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  refine Nat.sInf_le ?_
  intro P _
  exact aor_l12_gen3 hT ht' ⟨c.trans e⟩ P

end CFSG.OddStandard.SmallF3.Omega
