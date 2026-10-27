module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G44
import CFSG.Goldschmidt.Steps.G71
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G72

variable {G : Type} [Group G] [Finite G]

theorem benderM_nonempty {s : G} (hs : Subgroup.centralizer ({s} : Set G) ≠ ⊤) :
    (CFSG.Walter.benderM s).Nonempty := by
  classical
  set C := Subgroup.centralizer ({s} : Set G)
  set 𝒦 : Set (Subgroup G) := {K | IsCoatom K ∧ C ≤ K}
  have hne : 𝒦.Nonempty := by
    rcases eq_top_or_exists_le_coatom C with h | ⟨K, hK, hCK⟩
    · exact absurd h hs
    · exact ⟨K, hK, hCK⟩
  by_cases hfp : ∃ K : Subgroup G, IsCoatom K ∧ C ≤ K ∧ CFSG.Walter.HasFixedPointFreeCore s K
  · obtain ⟨K, hK, hCK, hKfp⟩ := hfp
    exact ⟨K, hK, hCK, Or.inl hKfp⟩
  · push Not at hfp
    obtain ⟨K, ⟨hK, hCK⟩, hmax⟩ := Set.exists_max_image 𝒦
      (fun K => Nat.card (GorensteinWalter.componentLayerOf K)) (Set.toFinite 𝒦) hne
    exact ⟨K, hK, hCK, Or.inr ⟨fun K' hK' hCK' => hfp K' hK' hCK',
      fun K' hK' hCK' => hmax K' ⟨hK', hCK'⟩⟩⟩

omit [Finite G] in
theorem centralizer_ne_top [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {w : G}
    (hw1 : w ≠ 1) : Subgroup.centralizer ({w} : Set G) ≠ ⊤ := by
  intro htop
  have hw : w ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({w} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [PropHSetup.center_eq_bot hnab, Subgroup.mem_bot] at hw
  exact hw1 hw

theorem goldschmidtLayer_eq_bot_of_isSolvable (Q : Type*) [Group Q] [Group.IsSolvable Q] :
    goldschmidtLayer Q = ⊥ := by
  refine sSup_eq_bot.mpr fun L hL => ?_
  obtain ⟨-, -, hcomm, hs⟩ := hL
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hcomm
  have : Subsingleton L := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable L inferInstance
  obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine absurd ((QuotientGroup.eq_one_iff g).mpr ?_) hx
  rw [Subsingleton.elim g 1]
  exact one_mem _

end G72

open G72 in
theorem G72_of
    (h4 : S_G4) (h71 : S_G71) : S_G72 := by
  intro G _ _ _ hnab hIH hrank hse S A U hAS hA hAcl hUA hmin h8
  have hGS : GoldSetting G S U := h4 G hnab hIH hrank hse S A U hAS hA hAcl hUA hmin
  by_contra hcon
  refine G44.corX_false hnab hIH S A U hAS hA hAcl hUA hmin h8 (fun w hwU hw1 => ?_) hse
  obtain ⟨H, hH⟩ := benderM_nonempty (centralizer_ne_top hnab hw1)
  obtain ⟨n, hn⟩ := h71 G S U hGS h8 w hwU hw1 H hH
  have hE : GorensteinWalter.componentLayerOf (normalClosureIn H U) = ⊥ := by
    by_contra hE
    exact hcon ⟨w, hwU, hw1, H, hH, hE⟩
  rw [hE, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    at hn
  have : Group.IsSolvable (normalClosureIn H U) := ⟨⟨n, hn⟩⟩
  have hMK : normalClosureIn (Subgroup.centralizer ({w} : Set G)) U ≤ normalClosureIn H U :=
    G71.normalClosureIn_mono U hH.2.1
  have : Group.IsSolvable (normalClosureIn (Subgroup.centralizer ({w} : Set G)) U) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMK)
  exact goldschmidtLayer_eq_bot_of_isSolvable _

end CFSG.Goldschmidt
