module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Chain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Tits
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C58Sub
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Can
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Abs

public section

namespace CFSG.QuasithinUnique.A5.Kc3G2

open CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.Quasithin
open scoped commutatorElement

theorem kc3ForS'_of_rt2 {P : ∀ (X : Type) [Group X], Prop}
    (hrt : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), P ↥K → BT2 K ∧ Lat2 K) :
    Kc3ForS' P := by
  intro G _ _ K L S₀ T₀ hq hKP hZ hLK hD5 hperf hSL hS hT hST hTK hTS
  obtain ⟨hBT, hLat⟩ := hrt G K hKP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hcomm, α, hα, hαQ, β, hβ⟩ := id hD5
  have hQK : Q ≤ K := hQL.trans hLK
  have hQ0 : Q ≠ ⊥ := fun h => d5_V_ne_bot β (le_bot_iff.1 (h ▸ hVQ))
  have hSQ : ∀ s ∈ S₀, s ∈ Subgroup.normalizer (Q : Set G) := fun s hs =>
    normalizer_le_normalizer_Q hQL hQ2 α hα hαQ (hSL hs)
  obtain ⟨n, hn⟩ := exists_stable hQK hQ2
  set W : Subgroup G := chainIter K Q n with hWdef
  have hWK : W ≤ K := chainIter_le hQK n
  have hW2 : IsPGroup 2 W := chainIter_isPGroup hQ2 n
  have hQW : Q ≤ W := chainIter_mono hQK hQ2 (Nat.zero_le n)
  have hW0 : W ≠ ⊥ := fun h => hQ0 (le_bot_iff.1 (h ▸ hQW))
  have hSW : ∀ s ∈ S₀, s ∈ Subgroup.normalizer (W : Set G) := fun s hs =>
    mem_normalizer_chainIter (hTK (hST hs)) (hSQ s hs) n
  have hLW : L ≤ nKW K W := (le_inf hLK hLQ).trans (nKW_le_chainIter n)
  obtain ⟨S, hSsyl, hSP, hPK, hcore⟩ := stable_parabolic hBT hWK hW0 hW2 hn
  have hC : K ⊓ Subgroup.centralizer (W : Set G) ≤ W :=
    centralizer_le_of_lat2 hLat hSsyl hSP hPK hcore
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (W : Set G) with hXdef
  have hXchar : CharTwo X := Kc3Gen.charTwo_normalizer hT hTK hW2 hWK hC
  have hLX : L ⊔ S₀ ≤ X :=
    sup_le (le_inf (hLK.trans le_sup_left) (hLW.trans inf_le_right))
      (le_inf (hST.trans le_sup_right) fun s hs => hSW s hs)
  obtain ⟨S₁, hS₀S₁, hS₁⟩ := Kc3Gen.exists_sylowTwoOf_le (X := X) (le_sup_right.trans hLX) hS
  refine ⟨X, S₁, hXchar, hLX, inf_le_left, hS₁, hS₀S₁, ?_⟩
  intro hsub
  set Pp : Subgroup G := nKW K W with hPpdef
  have hPX : Pp ≤ X := le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hXP : X ≤ Subgroup.normalizer (Pp : Set G) := by
    intro x hx
    have hxK : x ∈ Subgroup.normalizer (K : Set G) :=
      (sup_le Subgroup.le_normalizer hTK : K ⊔ T₀ ≤ Subgroup.normalizer (K : Set G)) hx.1
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxK, Subgroup.le_normalizer hx.2⟩
  have hSylX : IsSylowOf 2 S₁ X := isSylowTwoOf_iff_isSylowOf.1 hS₁
  have hU₁P : IsSylowOf 2 (S₁ ⊓ Pp) Pp := hSylX.inf_of_le_normalizer hPX hXP
  have hSK : IsSylowOf 2 S K := isSylowTwoOf_iff_isSylowOf.1 hSsyl
  have hSPP : IsSylowOf 2 S Pp := hSK.of_le hSP (nKW_le_left K W)
  have hU₁K : IsSylowTwoOf (S₁ ⊓ Pp) K := by
    refine isSylowTwoOf_iff_isSylowOf.2
      (isSylowOf_of_card (inf_le_right.trans (nKW_le_left K W)) ?_)
    rw [hU₁P.card_eq, ← hSPP.card_eq, hSK.card_eq]
  set M : Subgroup G := L ⊔ (S₁ ⊓ Pp) with hMdef
  have hMP : M ≤ Pp := sup_le hLW inf_le_right
  have hMns : ¬ Group.IsSolvable ↥M := by
    intro hsolv
    have hL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_sup_left : L ≤ M))
        (Subgroup.inclusion_injective _)
    exact not_isSolvable_alt5 (Group.isSolvable_of_surjective hα)
  obtain ⟨P'', Q'', hF, hPP'', hP''K, hlat⟩ :=
    hLat (S₁ ⊓ Pp) Pp hU₁K inf_le_right (nKW_le_left K W) hPK
  have hper : perfectCore M = perfectCore P'' := hlat M le_sup_right hMP hMns
  have hLD : L ≤ perfectCore M := le_perfectCore_of_perfect le_sup_left hperf
  have hDM : perfectCore M ≤ M := perfectCore_le M
  have hMY : M ≤ L ⊔ S₁ := sup_le_sup_left inf_le_left L
  have h1 : (L.subgroupOf (L ⊔ S₁)).IsSubnormal := (isSubnormal_iff_subgroupOf le_sup_left).1 hsub
  have h2 : (L.subgroupOf (perfectCore M)).IsSubnormal :=
    C58.isSubnormal_subgroupOf_of_le (hDM.trans hMY) h1
  have hDn : ((perfectCore M).subgroupOf P'').Normal := by
    rw [hper] at *
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le P'')).2
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P''))
  have h3 : (L.subgroupOf P'').IsSubnormal := by
    refine C58.isSubnormal_subgroupOf_trans hLD h2 ?_
    exact hDn.isSubnormal
  exact ParabolicFacts.no_d5 hF (hLW.trans hPP'') h3 hperf hD5

end CFSG.QuasithinUnique.A5.Kc3G2
