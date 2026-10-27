module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28End
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28L44

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28_false_of_config (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hK1 : KFactL28Three)
    (hK2 : KFactL28FieldSignalizer) (hK3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hR1 : L28Prop34 3 P J x) {U : Subgroup G} (hV : L28InV 3 P x U)
    (hAb : L28PointFAbelian 3 M U)
    (h42 : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (h43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) → normalizer (Y : Set G) ≤ M) :
    False := by
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  have hwc : LineWeaklyClosed x U := l28plane_wc hgen hR1 hV
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  obtain ⟨hUQ, hUel, hUc, hxU, -⟩ := id hV
  have hUP : U ≤ (P : Subgroup G) := hUQ.trans inf_le_left
  obtain ⟨w, hwU, hwx⟩ : ∃ w ∈ U, w ∉ zpowers x := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (fun u hu => hno u hu : U ≤ zpowers x)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
    rw [hUc, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at h1
    omega
  have hout := l28plane_outer hgen hR1 hV hwU hwx
  exact l28end_false_three_of_plane hS hU0 hD1 hInn hWC hp hM hxP hx1 hx3 hUel hUc hUP hxU hwc hAb
    h42 h43
    (l28_exists_maximal_not_le_of_plane hS hU0 hK2 hp hM hgen hJ hxJ hUel hUc hUP hxU hwU hwx hout)
    (l28_not_two_dvd_card hS hU0 hD1 hK1 hK3 hp hM hgen hJ)

end CFSG.LocalAnalysis.RankThreeTheoremC
