module

public import CFSG.Goldschmidt.Steps.G310
public import CFSG.Goldschmidt.Steps.G310ZJ2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Glauberman

namespace G310

section Core

variable {M : Type} [Group M] [Finite M]

theorem centralizer_le_of_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup M}
    (hP : Maximal (· ∈ sigN ⊤ A p) P) {L : Subgroup M} (hL : L ∈ typeIISet A) :
    (L ⊔ P) ⊓ Subgroup.centralizer (L : Set M) ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hPp, hAP, -⟩ := hP.prop
  have hPL : P ≤ Subgroup.normalizer (L : Set M) := (le_h0 hO hS hp hp2 hP.prop).2 L hL.1
  set C := (L ⊔ P) ⊓ Subgroup.centralizer (L : Set M) with hC
  have hCp : IsPGroup p C := by
    rintro ⟨c, hcLP, hcC⟩
    have hc' : c ∈ P ⊔ L := by rwa [sup_comm]
    obtain ⟨q, hq, l, hl, rfl⟩ := exists_mul_of_mem_sup hPL hc'
    obtain ⟨n, hn⟩ := hPp ⟨q, hq⟩
    have hqn : q ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨l', hl', hpow⟩ := exists_pow_mul_eq (hPL hq) hl (p ^ n)
    rw [hqn, one_mul] at hpow
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    refine eq_one_of_central_typeII hO hS hL (hpow ▸ hl') fun y hy => ?_
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hcC (p ^ n)) y hy
    rw [hpow] at this ⊢
    exact this.symm
  have hLPn : L ⊔ P ≤ Subgroup.normalizer ((L ⊔ P : Subgroup M) : Set M) :=
    Subgroup.le_normalizer
  have hPC : P ≤ Subgroup.normalizer (C : Set M) :=
    le_normalizer_inf (le_sup_right.trans hLPn)
      (hPL.trans (normalizer_le_normalizer_centralizer' L))
  have hAL : A ≤ Subgroup.normalizer (L : Set M) := fun a ha =>
    mem_normalizer_of_mem hO hS hL.1 (le_normalClosureIn_top A ha)
  have hAC : A ≤ Subgroup.normalizer (C : Set M) :=
    le_normalizer_inf (le_normalizer_sup hAL hAP)
      (hAL.trans (normalizer_le_normalizer_centralizer' L))
  have hR := hPp.to_sup_of_normal_right' hCp hPC
  have hRle : P ⊔ C ≤ layerII A ⊔ P :=
    sup_le le_sup_right (inf_le_left.trans (sup_le_sup_right (le_layerII hL) _))
  have heq := eq_of_le_layerII_sup hO hS hp hp2 hP hRle hR (le_normalizer_sup hAP hAC) le_sup_left
  exact le_sup_right.trans heq.le

theorem isSimpleGroup_of_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) : IsSimpleGroup L := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.2.2
  exact ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_typeII hO hS hL)).trans
    QuotientGroup.quotientBot).isSimpleGroup_congr.mp inferInstance

theorem exists_involution_of_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) :
    ∃ t ∈ L, t ≠ 1 ∧ t ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := (compFacts hO hS hL.1).noncentral
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [one_mul, mul_one] at hxy
    exact hxy rfl
  have h2 : IsPGroup 2 ↥(A ⊓ L) := (isPGroup_two_of_isSStarIn hS).to_le inf_le_left
  have hdvd : 2 ∣ Nat.card ↥(A ⊓ L) := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rcases k with _ | k
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk
      apply hx1
      have : x ∈ (⊥ : Subgroup M) := hk ▸ hx
      exact (Subgroup.mem_bot).mp this
    · rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨t, t.2.2, fun h => ?_, ?_⟩
  · have : t = 1 := Subtype.ext h
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa using congrArg Subtype.val this

theorem isMulCommutative_of_le_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) {S : Subgroup M} (hSL : S ≤ L)
    (hS2 : IsPGroup 2 S) : IsMulCommutative S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hS2.comap_subtype (K := L)).exists_le_sylow
  have hTsyl : fusionIsSylowIn 2 ((T : Subgroup L).map L.subtype) L := fusionIsSylowIn_map T
  obtain ⟨y, -, hy⟩ := exists_conjSub_eq_of_fusionIsSylowIn (isSylow_inf_of_typeII hO hS hL)
    hTsyl
  have hab : IsMulCommutative ↥((T : Subgroup L).map L.subtype) := by
    rw [hy]
    have hAL : IsMulCommutative ↥(A ⊓ L) :=
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_isMulCommutative hS.2.1 a.2.1 b.2.1)⟩⟩
    exact CFSG.Goldschmidt.isMulCommutative_map hAL _
  have hST : S ≤ (T : Subgroup L).map L.subtype := fun s hs =>
    ⟨⟨s, hSL hs⟩, hT (show (⟨s, hSL hs⟩ : L) ∈ S.comap L.subtype from hs), rfl⟩
  exact ⟨⟨fun a b => Subtype.ext (mul_comm_of_isMulCommutative hab (hST a.2) (hST b.2))⟩⟩

end Core

section Lift

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_zj_of_typeII
    {H A P : Subgroup G} (hS : IsSStarIn H A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : Maximal (· ∈ sigN H A p) P)
    (hF : IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H))
    {L : Subgroup (H ⧸ goldschmidtOddCore H)} (hL : L ∈ typeIISet (barOf H A)) :
    preOf H L ≤ Subgroup.normalizer (ZJ P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup 2 A := isPGroup_two_of_isSStarIn hS
  have hAH : A ≤ H := hS.1
  obtain ⟨hPH, hPp, -, -⟩ := hP.prop
  have hOM := goldschmidtOddCore_quotient_eq_bot H
  have hSM := SStarTransport.isSStarIn_barOf hS
  have hPM := maximal_sigN_barOf hAH hA hp hp2 hP
  set π := QuotientGroup.mk' (goldschmidtOddCore H) with hπ
  set O := oddCoreOf H with hOdef
  set Y := preOf H L ⊔ P with hY
  have hLH : preOf H L ≤ H := Subgroup.map_subtype_le _
  have hYH : Y ≤ H := sup_le hLH hPH
  have hOL : O ≤ preOf H L := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff o).mpr ho]
    exact L.one_mem
  have hOY : O ≤ Y := hOL.trans le_sup_left
  set ρ : Y →* H ⧸ goldschmidtOddCore H := π.comp (Subgroup.inclusion hYH) with hρ
  have hρapply : ∀ y : Y, ρ y = π ⟨y, hYH y.2⟩ := fun y => rfl
  have hker : ρ.ker = O.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, hρapply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨o, ho, hoy⟩
      rwa [show o = ⟨y, hYH y.2⟩ from Subtype.ext hoy] at ho
  have hOYn : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr
      (hYH.trans (le_normalizer_oddCoreOf H))
  have hOYodd : Odd (Nat.card (O.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOY).toEquiv]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_two_dvd_card_oddCoreOf H))
  have hker' : ρ.ker ≤ goldschmidtOddCore Y := by
    rw [hker]
    exact le_sSup ⟨hOYn, hOYodd⟩
  have hsylPO := (fusionIsSylowIn_of_maximal_sigN hAH hA hp hp2 hP).1
  have hsyl : fusionIsSylowIn p (P.subgroupOf Y) (P.subgroupOf Y ⊔ ρ.ker) := by
    rw [hker, ← Subgroup.subgroupOf_sup le_sup_right hOY]
    exact fusionIsSylowIn_subgroupOf hsylPO (sup_le le_sup_right hOY)
  have hPmap : (P.subgroupOf Y).map ρ = barOf H P := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hYH y.2⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, (le_sup_right : P ≤ Y) hx⟩, hx, rfl⟩
  have hrange : ρ.range = L ⊔ (P.subgroupOf Y).map ρ := by
    rw [hPmap, hρ, MonoidHom.range_comp, Subgroup.inclusion_range, hY,
      Subgroup.subgroupOf_sup hLH hPH, Subgroup.map_sup]
    congr 1
    rw [preOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hPL : (P.subgroupOf Y).map ρ ≤ Subgroup.normalizer (L : Set (H ⧸ goldschmidtOddCore H)) := by
    rw [hPmap]
    exact (le_h0 hOM hSM hp hp2 hPM.prop).2 L hL.1
  have hsimple : ∀ N : Subgroup (H ⧸ goldschmidtOddCore H), N ≤ L →
      L ≤ Subgroup.normalizer (N : Set (H ⧸ goldschmidtOddCore H)) → N = ⊥ ∨ N = L := by
    intro N hNL hLN
    have := isSimpleGroup_of_typeII hOM hSM hL
    have hn : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
    · left
      have := congrArg (Subgroup.map L.subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hNL, Subgroup.map_bot] at this
    · right
      have := congrArg (Subgroup.map L.subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hNL, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at this
  have hcent : ρ.range ⊓ Subgroup.centralizer (L : Set (H ⧸ goldschmidtOddCore H)) ≤
      (P.subgroupOf Y).map ρ := by
    rw [hrange, hPmap]
    exact centralizer_le_of_typeII hOM hSM hp hp2 hPM hL
  set F := GorensteinWalter.generalizedFittingSubgroupOf H with hFdef
  have hFH : F ≤ H := (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).1
  have hHF : H ≤ Subgroup.normalizer (F : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).2 h hh x
    · intro hx
      have := (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).2 h⁻¹ (H.inv_mem hh) _ hx
      simpa [mul_assoc] using this
  have hFodd : ¬ 2 ∣ Nat.card F := by
    obtain ⟨n, hn⟩ := hF.exists_card_eq
    rw [hn]
    exact fun h => (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hp2).pow) (even_iff_two_dvd.mpr h)
  have hFO : F ≤ O := le_oddCoreOf_of_normalizer hFH hHF hFodd
  have hFY : F ≤ Y := hFO.trans hOY
  have hd : Subgroup.centralizer (CFSG.pCore p Y : Set Y) ≤ CFSG.pCore p Y := by
    have hFn : (F.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFY).mpr (hYH.trans hHF)
    have hFle : F.subgroupOf Y ≤ CFSG.pCore p Y := le_sSup ⟨hFn, hF.comap_subtype⟩
    refine (Subgroup.centralizer_le hFle).trans (le_trans ?_ hFle)
    intro y hy
    have hyC : (y : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy ⟨f, hFY hf⟩ hf)
    exact GorensteinWalter.centralizer_intersection_fstar_le_fstar H ⟨hyC, hYH y.2⟩
  have hZY := zj_normal_of_map hp2 (hPp.comap_subtype : IsPGroup p (P.subgroupOf Y)) ρ L hker'
    hsyl hrange hPL hsimple (exists_involution_of_typeII hOM hSM hL) hcent
    (fun S hSL hS2 => isMulCommutative_of_le_typeII hOM hSM hL hSL hS2) hd
  change (ZJ (P.subgroupOf Y)).Normal at hZY
  rw [zj_subgroupOf (show P ≤ Y from le_sup_right)] at hZY
  have hYN := (Subgroup.normal_subgroupOf_iff_le_normalizer ((zj_le P).trans le_sup_right)).mp hZY
  exact le_sup_left.trans hYN

theorem oddCoreOf_le_normalizer_zj
    {H A P : Subgroup G} (hS : IsSStarIn H A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : Maximal (· ∈ sigN H A p) P)
    (hF : IsPGroup p (GorensteinWalter.generalizedFittingSubgroupOf H)) :
    oddCoreOf H ≤ Subgroup.normalizer (ZJ P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup 2 A := isPGroup_two_of_isSStarIn hS
  obtain ⟨hPH, hPp, -, -⟩ := hP.prop
  set O := oddCoreOf H with hOdef
  set F := GorensteinWalter.generalizedFittingSubgroupOf H with hFdef
  have hFH : F ≤ H := (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).1
  have hHF : H ≤ Subgroup.normalizer (F : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).2 h hh x
    · intro hx
      have := (GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn H).2 h⁻¹ (H.inv_mem hh) _ hx
      simpa [mul_assoc] using this
  have hFodd : ¬ 2 ∣ Nat.card F := by
    obtain ⟨n, hn⟩ := hF.exists_card_eq
    rw [hn]
    exact fun h => (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hp2).pow) (even_iff_two_dvd.mpr h)
  have hFO : F ≤ O := le_oddCoreOf_of_normalizer hFH hHF hFodd
  have hsylPO := (fusionIsSylowIn_of_maximal_sigN hS.1 hA hp hp2 hP).1
  have hPO : P ≤ Subgroup.normalizer (O : Set G) := hPH.trans (le_normalizer_oddCoreOf H)
  have hodd : Odd (Nat.card (P ⊔ O : Subgroup G)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (not_two_dvd_card_sup hp hp2 hPp hPO (not_two_dvd_card_oddCoreOf H)))
  have hYH : P ⊔ O ≤ H := sup_le hPH (oddCoreOf_le H)
  have h1 := normalizer_le_normalizer_zj_of_odd hodd hsylPO (hFO.trans le_sup_right)
    (hYH.trans hHF) hF (fun y hy => GorensteinWalter.centralizer_intersection_fstar_le_fstar H
      ⟨hy.2, hYH hy.1⟩)
  exact (le_sup_right.trans Subgroup.le_normalizer).trans h1

end Lift

end G310

theorem G311 :
    S_G311 := by
  intro G _ _ H A hS p hp hp2 P hP hF
  have : Fact p.Prime := ⟨hp⟩
  set Z := ZJ P with hZ
  set π := QuotientGroup.mk' (goldschmidtOddCore H) with hπ
  have hO := G310.oddCoreOf_le_normalizer_zj hS hp hp2 hP hF
  have hL : typeIILayer H A ≤ Subgroup.normalizer (Z : Set G) := by
    rw [G310.typeIILayer_eq]
    set N := (Subgroup.normalizer (Z : Set G)).subgroupOf H with hN
    have hLN : G310.layerII (barOf H A) ≤ N.map π := by
      refine sSup_le fun L hL => ?_
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L]
      refine Subgroup.map_mono fun y hy => ?_
      exact G310.le_normalizer_zj_of_typeII hS hp hp2 hP hF hL ⟨y, hy, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hnx⟩ := hLN hx
    have hker : n⁻¹ * x ∈ goldschmidtOddCore H := by
      rw [← QuotientGroup.eq]
      exact hnx
    have h1 : ((n⁻¹ * x : H) : G) ∈ Subgroup.normalizer (Z : Set G) := hO ⟨_, hker, rfl⟩
    have e : (x : G) = (n : G) * ((n⁻¹ * x : H) : G) := by simp
    show (x : G) ∈ _
    rw [e]
    exact Subgroup.mul_mem _ hn h1
  have h2 := (G310 G H A hS p hp hp2 P hP).2
  rw [← h2]
  exact sup_le hL (inf_le_right.trans (G310.normalizer_le_normalizer_zj P))

end CFSG.Goldschmidt
