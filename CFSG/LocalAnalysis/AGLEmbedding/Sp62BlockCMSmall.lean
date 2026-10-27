module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszOut
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentMethod

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactOmegaMinusThreePerfectCent : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 6 ≤ m →
    IsOmegaMinusTwoIndex m d → Nonempty (L ≃* CatGroup d) → ∀ x : L, orderOf x = 3 →
    ∃ D : Subgroup L, D ≤ Subgroup.centralizer ({x} : Set L) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D

theorem exists_perfect_centralizer_lift {Y : Type} [Group Y] [Finite Y] (O : Subgroup Y)
    [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) {e : Y} (he : IsPGroup 3 (Subgroup.zpowers e))
    {D : Subgroup (Y ⧸ O)}
    (hDC : D ≤ Subgroup.centralizer ({QuotientGroup.mk' O e} : Set (Y ⧸ O)))
    (hDp : ⁅D, D⁆ = D) (h3 : 3 ∣ Nat.card D) :
    ∃ D' : Subgroup Y, D' ≤ Subgroup.centralizer ({e} : Set Y) ∧ ⁅D', D'⁆ = D' ∧
      3 ∣ Nat.card D' := by
  set W : Subgroup Y := Subgroup.centralizer ({e} : Set Y) ⊓ D.comap (QuotientGroup.mk' O)
  have hWD : W.map (QuotientGroup.mk' O) = D := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · obtain ⟨g, hg, hgy⟩ := exists_mem_centralizer_mk_eq Nat.prime_three O hO he (hDC hy)
      exact ⟨g, ⟨hg, show QuotientGroup.mk' O g ∈ D by rw [hgy]; exact hy⟩, hgy⟩
  refine ⟨perfectCore W, (perfectCore_le W).trans inf_le_left, perfectCore_perfect W, ?_⟩
  have hmap : (perfectCore W).map (QuotientGroup.mk' O) = D := by
    rw [map_perfectCore, hWD]
    exact perfectCore_eq_self_of_perfect hDp
  exact h3.trans (hmap ▸ Subgroup.card_map_dvd (perfectCore W) (QuotientGroup.mk' O))

section Perfect

variable {G : Type} [Group G] [Finite G] {M C : Subgroup G}

theorem coprime_card_of_perfect_of_not_mem
    {Tb : Sylow 3 (C ⧸ primeComplementCore (G := C) 3)}
    {KC : Subgroup (C ⧸ primeComplementCore (G := C) 3)}
    (hred : ReducedNongeneration 3 (C ⧸ primeComplementCore (G := C) 3) Tb
      (((C ⊓ M).subgroupOf C).map (QuotientGroup.mk' (primeComplementCore 3))))
    (hR4 : 4 ≤ CFSG.Open.pRank 3 (Tb : Subgroup (C ⧸ primeComplementCore (G := C) 3)))
    (hcat : CatalogSimpleSections (C ⧸ primeComplementCore (G := C) 3))
    {z : C ⧸ primeComplementCore (G := C) 3}
    (hzZ : z ∈ Subgroup.center _) (hzp : orderOf z = 3) (hKC : IsComponentOf KC ⊤)
    (hKCn : KC.Normal)
    (huniqC : ∀ L' : Subgroup (C ⧸ primeComplementCore (G := C) 3),
        IsComponentOf L' ⊤ → L' = KC)
    (hzK : z ∉ KC) (hβ : KFactBeta) (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable)
    (hSch : KFactCatalogSchreier) {D : Subgroup G}
    (hDC : D ≤ C) (hDM : D ≤ M) (hDp : ⁅D, D⁆ = D) :
    Nat.Coprime 3 (Nat.card D) := by
  have hO := primeComplementCore_coprime (G := C) 3
  have hDCmap : (D.subgroupOf C).map C.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDC
  have hDCp : ⁅D.subgroupOf C, D.subgroupOf C⁆ = D.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hDCmap, hDp]
  have hDtp : ⁅(D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3)),
      (D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3))⁆ =
      (D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3)) := by
    rw [← Subgroup.map_commutator, hDCp]
  have hDtK : (D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3)) ≤ KC :=
    Sp48NCent.le_of_isPerfect_unique hred hcat hSch hKC hKCn huniqC
      (Subgroup.isPerfect_iff.mpr hDtp)
  have hDtX : (D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3)) ≤
      ((C ⊓ M).subgroupOf C).map (QuotientGroup.mk' (primeComplementCore 3)) := by
    refine Subgroup.map_mono fun c hc => ?_
    exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hDM (Subgroup.mem_subgroupOf.mp hc)⟩
  have hsolv := hred.isSolvable_inf_of_not_mem hR4 hcat hzZ hzp hKC hKCn hzK hβ hKO hΓ
  let f : ((D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3))) →*
      ((((C ⊓ M).subgroupOf C).map (QuotientGroup.mk' (primeComplementCore 3))).subgroupOf KC) :=
    { toFun := fun d => ⟨⟨d, hDtK d.2⟩, hDtX d.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (congrArg (fun y => y.1.1) hab)
  have hsD := Group.isSolvable_of_isSolvable_injective hf
  have hbot : (D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3)) = ⊥ := by
    by_contra hne
    have : Nontrivial ((D.subgroupOf C).map
        (QuotientGroup.mk' (primeComplementCore (G := C) 3))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ((D.subgroupOf C).map
        (QuotientGroup.mk' (primeComplementCore (G := C) 3))) :=
      Subgroup.isPerfect_iff.mpr hDtp
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := ((D.subgroupOf C).map (QuotientGroup.mk' (primeComplementCore (G := C) 3))))
    rw [Group.IsPerfect.commutator_eq_top] at hlt
    exact lt_irrefl _ hlt
  have hDCO : D.subgroupOf C ≤ primeComplementCore (G := C) 3 := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hcard : Nat.card D = Nat.card (D.subgroupOf C) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv).symm
  rw [hcard]
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hDCO) hO

end Perfect

end CFSG.AGLEmbedding
