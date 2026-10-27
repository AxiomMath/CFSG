module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactL34FixedPointsProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L45b
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M N : Subgroup G}

private theorem sylow_three_not_commutative {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (hZcard : Nat.card (Subgroup.center L) = 3)
    (R : Sylow 3 L) (hRcard : Nat.card ↥(R : Subgroup L) = 27) :
    ∃ r ∈ (R : Subgroup L), ∃ s ∈ (R : Subgroup L), r * s ≠ s * r := by
  by_contra h
  push Not at h
  have hcomm : IsMulCommutative ↥(R : Subgroup L) :=
    ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 (by rw [hZcard])
  have hz : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzorder
    exact absurd hzorder (by norm_num)
  have hz3 : ((z : ↥(Subgroup.center L)) : L) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center L) (x := z)
    rw [hZcard] at h
    exact congrArg Subtype.val h
  have hzo : orderOf ((z : ↥(Subgroup.center L)) : L) = 3 := by
    refine orderOf_eq_prime hz3 fun h1 => hz (Subtype.ext h1)
  exact CFSG.LocalAnalysis.RankThreeTheoremC.m11l45_false_of_central R hcomm z.2 hzo

private theorem cube_eq_one_of_conj_inv {L : Type} [Group L]
    (hZcard : Nat.card (Subgroup.center L) = 3) {x : L}
    (hx3 : x ^ 3 ∈ Subgroup.center L)
    (hconj : ∀ y : L ⧸ Subgroup.center L, y ^ 3 = 1 →
      ∃ g : L ⧸ Subgroup.center L, g * y * g⁻¹ = y⁻¹) :
    x ^ 3 = 1 := by
  classical
  set Z : Subgroup L := Subgroup.center L with hZ
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  have hx3Z : x ^ 3 ∈ Z := hx3
  by_cases hq1 : q x = 1
  · have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff (N := Z) x).mp hq1
    have h := pow_card_eq_one' (G := Z) (x := ⟨x, hxZ⟩)
    rw [hZcard] at h
    simpa using congrArg Subtype.val h
  · have hq3 : (q x) ^ 3 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := Z) (x ^ 3)).mpr hx3Z
    obtain ⟨g, hg⟩ := hconj (q x) hq3
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    have hqconj : q (g₀ * x * g₀⁻¹) = q x⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hg
    obtain ⟨c, hc, hceq⟩ : ∃ c ∈ Z, g₀ * x * g₀⁻¹ = x⁻¹ * c := by
      refine ⟨(x⁻¹)⁻¹ * (g₀ * x * g₀⁻¹), ?_, by group⟩
      exact QuotientGroup.eq.mp hqconj.symm
    have hc3 : c ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Z) (x := ⟨c, hc⟩)
      rw [hZcard] at h
      simpa using congrArg Subtype.val h
    have hcomm : Commute x⁻¹ c := Subgroup.mem_center_iff.mp hc x⁻¹
    have h2 : (g₀ * x * g₀⁻¹) ^ 3 = (x ^ 3)⁻¹ := by
      rw [hceq, hcomm.mul_pow, hc3, mul_one, inv_pow]
    have heq : x ^ 3 = (x ^ 3)⁻¹ := by
      have h1 : x ^ 3 = (g₀ * x * g₀⁻¹) ^ 3 := by
        rw [conj_pow, Subgroup.mem_center_iff.mp hx3Z g₀, mul_assoc, mul_inv_cancel, mul_one]
      exact h1.trans h2
    have hsq : (x ^ 3) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [heq]
      exact mul_inv_cancel _
    have hdvd2 : orderOf (x ^ 3) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hdvd3 : orderOf (x ^ 3) ∣ 3 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      have h := pow_card_eq_one' (G := Z) (x := ⟨x ^ 3, hx3Z⟩)
      rw [hZcard] at h
      simpa using congrArg Subtype.val h
    have hdvd1 : orderOf (x ^ 3) ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvd3
      simpa using this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

private theorem pow_three_eq_one_of_sylow_three {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (hZcard : Nat.card (Subgroup.center L) = 3)
    (hconj : ∀ y : L ⧸ Subgroup.center L, y ^ 3 = 1 →
      ∃ g : L ⧸ Subgroup.center L, g * y * g⁻¹ = y⁻¹)
    (R : Sylow 3 L) (hRcard : Nat.card ↥(R : Subgroup L) = 27) :
    ∀ x ∈ (R : Subgroup L), x ^ 3 = 1 := by
  have hna := sylow_three_not_commutative hZcard R hRcard
  have hna' : ∃ a b : ↥(R : Subgroup L), a * b ≠ b * a := by
    obtain ⟨r, hr, s, hs, hrs⟩ := hna
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, fun h => hrs (congrArg Subtype.val h)⟩
  have hcenter := CFSG.HardMathSupport.Solomon.Coordinator.i112v_sylow_center
    hZcard R hRcard hna
  intro x hx
  refine cube_eq_one_of_conj_inv hZcard ?_ hconj
  rw [← hcenter.2]
  exact Subgroup.mem_map_of_mem (R : Subgroup L).subtype
    (CFSG.RankThree.PartTwo.Sec4.RonanK432.pow_three_mem_center_of_card_27
      hRcard hna' ⟨x, hx⟩)

private theorem exists_conj_inv_of_isL34Type
    {L : Type} [Group L]
    (hL : IsL34Type L) :
    ∀ y : L ⧸ Subgroup.center L, y ^ 3 = 1 →
      ∃ g : L ⧸ Subgroup.center L, g * y * g⁻¹ = y⁻¹ := by
  classical
  intro y hy3
  by_cases hy1 : y = 1
  · exact ⟨1, by rw [hy1, inv_one]; group⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hL
  obtain ⟨eS⟩ := KFactL34FixedPointsProof.nonempty_mulEquiv_S ⟨e⟩
  set z : ↥CFSG.ComponentClassification.PSL3Four.S := eS y with hzdef
  have hz3 : (z : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    have h : z ^ 3 = 1 := by rw [hzdef, ← map_pow, hy3, map_one]
    simpa using congrArg Subtype.val h
  have hz1 : (z : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h1
    apply hy1
    have hz1' : z = 1 := Subtype.ext h1
    rw [hzdef] at hz1'
    exact eS.injective (by rw [hz1', map_one])
  have hzS : (z : Equiv.Perm (Fin 42)) ∈ CFSG.ComponentClassification.PSL3Four.S := z.2
  have hz3inv : ((z : Equiv.Perm (Fin 42))⁻¹) ^ 3 = 1 := by
    rw [inv_pow, hz3, inv_one]
  have hz1inv : (z : Equiv.Perm (Fin 42))⁻¹ ≠ 1 := by
    intro h1; exact hz1 (inv_eq_one.mp h1)
  obtain ⟨s, hsS, hsz⟩ := KFactL34FixedPointsProof.exists_conj_eq_z0 hzS hz3 hz1
    (CFSG.ComponentClassification.PSL3Four.S.inv_mem hzS) hz3inv hz1inv
  have hconj : (⟨s, hsS⟩ : ↥CFSG.ComponentClassification.PSL3Four.S)⁻¹ * z *
      ⟨s, hsS⟩ = z⁻¹ := by
    apply Subtype.ext
    show s⁻¹ * (z : Equiv.Perm (Fin 42)) * s = (z : Equiv.Perm (Fin 42))⁻¹
    calc s⁻¹ * (z : Equiv.Perm (Fin 42)) * s
        = s⁻¹ * (s * (z : Equiv.Perm (Fin 42))⁻¹ * s⁻¹) * s := by rw [hsz]
      _ = (z : Equiv.Perm (Fin 42))⁻¹ := by group
  refine ⟨(eS.symm ⟨s, hsS⟩)⁻¹, ?_⟩
  apply eS.injective
  simpa using hconj

private theorem exists_conj_inv_of_isA6Type {L : Type} [Group L] (hL : IsA6Type L) :
    ∀ y : L ⧸ Subgroup.center L, y ^ 3 = 1 →
      ∃ g : L ⧸ Subgroup.center L, g * y * g⁻¹ = y⁻¹ := by
  intro y hy3
  obtain ⟨e⟩ := hL
  have hyperm : (e y : Equiv.Perm (Fin 6)) ^ 3 = 1 := by
    have h : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    simpa using congrArg Subtype.val h
  obtain ⟨τ, hτsign, hτ⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res4Proof.perm_six_exists_inv_of_pow_three
      (e y : Equiv.Perm (Fin 6)) hyperm
  let τ' : alternatingGroup (Fin 6) := ⟨τ, by rwa [Equiv.Perm.mem_alternatingGroup]⟩
  have hτ' : τ' * e y * τ'⁻¹ = (e y)⁻¹ := by
    apply Subtype.ext
    exact hτ
  refine ⟨e.symm τ', ?_⟩
  apply e.injective
  simpa using hτ'

private theorem card_inf_oTwoZStar {J' S' : Subgroup G}
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J')
    (hZcard : Nat.card (Subgroup.center (threeStar J')) = 3)
    (hZle : Subgroup.center (threeStar J') ≤
      (S'.subgroupOf J').map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J'))) :
    Nat.card ↥(S' ⊓ oTwoZStar J') = 3 := by
  classical
  let q : ↥J' →* threeStar J' := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J')
  let S : Subgroup ↥J' := S'.subgroupOf J'
  have hInj : Set.InjOn q (S : Set ↥J') := pPrimeCore_quotient_injOn_of_isSylowOf hS'
  have hSeq : (S'.subgroupOf J').map J'.subtype = S' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS'.le]
  have hD : S' ⊓ oTwoZStar J' = (S ⊓ (Subgroup.center (threeStar J')).comap q).map J'.subtype := by
    have hS'map : S.map J'.subtype = S' := hSeq
    apply le_antisymm
    · rintro x ⟨hxS', hxO⟩
      rw [oTwoZStar] at hxO
      obtain ⟨y, hyZ, hyx⟩ := Subgroup.mem_map.mp hxO
      rw [← hS'map] at hxS'
      obtain ⟨z, hzS, hzx⟩ := Subgroup.mem_map.mp hxS'
      have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
      refine Subgroup.mem_map.mpr ⟨z, ⟨hzS, ?_⟩, hzx⟩
      rw [← hyz]
      exact hyZ
    · rintro x ⟨y, ⟨hyS, hyZ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hS'map]
        exact Subgroup.mem_map_of_mem J'.subtype hyS
      · rw [oTwoZStar]
        exact Subgroup.mem_map_of_mem J'.subtype hyZ
  have hDmap : (S ⊓ (Subgroup.center (threeStar J')).comap q).map q =
      Subgroup.center (threeStar J') := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
      rw [← hxz]
      exact hx.2
    · intro z hz
      obtain ⟨x, hxS, hxz⟩ := Subgroup.mem_map.mp (hZle hz)
      have hxZ : x ∈ (Subgroup.center (threeStar J')).comap q := by
        rw [Subgroup.mem_comap, hxz]
        exact hz
      exact Subgroup.mem_map.mpr ⟨x, ⟨hxS, hxZ⟩, hxz⟩
  have hcardD : Nat.card ↥(S ⊓ (Subgroup.center (threeStar J')).comap q) = 3 := by
    have hsub : ((S ⊓ (Subgroup.center (threeStar J')).comap q : Subgroup ↥J') : Set ↥J') ⊆
        (S : Set ↥J') := fun x hx => hx.1
    have hcardmap : Nat.card ↥((S ⊓ (Subgroup.center (threeStar J')).comap q).map q) =
        Nat.card ↥(S ⊓ (Subgroup.center (threeStar J')).comap q) := by
      rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn (hInj.mono hsub)]
      rfl
    rw [← hcardmap, hDmap, hZcard]
  rw [hD, Subgroup.card_map_of_injective J'.subtype_injective, hcardD]

private theorem inf_oTwoZStar_le_center {J' S' : Subgroup G}
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J') :
    S' ⊓ oTwoZStar J' ≤ (Subgroup.center ↥S').map S'.subtype := by
  classical
  let q : ↥J' →* threeStar J' := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J')
  have hSO : S'.subgroupOf J' ⊓ CFSG.pPrimeCore 3 ↥J' = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := (hS'.isPGroup.comap_subtype (K := J')).exists_card_eq
    have hn' : Nat.card ↥(S'.subgroupOf J') = 3 ^ n := hn
    rw [hn']
    exact Nat.Coprime.pow_left n (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J'))
  have hcentral : ∀ d ∈ S' ⊓ oTwoZStar J', ∀ s ∈ S', d * s = s * d := by
    intro d hd s hs
    have hdJ : d ∈ J' := hS'.le hd.1
    have hsJ : s ∈ J' := hS'.le hs
    have hq1 : q ⟨d, hdJ⟩ ∈ Subgroup.center (threeStar J') := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hd.2
      have hy' : y = ⟨d, hdJ⟩ := Subtype.ext hyx
      rwa [hy'] at hy
    have hq2 : q (⟨d, hdJ⟩ * ⟨s, hsJ⟩ * ⟨d, hdJ⟩⁻¹ * ⟨s, hsJ⟩⁻¹) = 1 := by
      have hc := Subgroup.mem_center_iff.mp hq1 (q ⟨s, hsJ⟩)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    have hmemO : (⟨d, hdJ⟩ * ⟨s, hsJ⟩ * ⟨d, hdJ⟩⁻¹ * ⟨s, hsJ⟩⁻¹ : ↥J') ∈
        CFSG.pPrimeCore 3 ↥J' := by
      rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥J')]
      exact hq2
    have hmemS : (⟨d, hdJ⟩ * ⟨s, hsJ⟩ * ⟨d, hdJ⟩⁻¹ * ⟨s, hsJ⟩⁻¹ : ↥J') ∈
        S'.subgroupOf J' :=
      (S'.subgroupOf J').mul_mem ((S'.subgroupOf J').mul_mem
        ((S'.subgroupOf J').mul_mem (Subgroup.mem_subgroupOf.mpr hd.1)
          (Subgroup.mem_subgroupOf.mpr hs))
        ((S'.subgroupOf J').inv_mem (Subgroup.mem_subgroupOf.mpr hd.1)))
        ((S'.subgroupOf J').inv_mem (Subgroup.mem_subgroupOf.mpr hs))
    have hone : (⟨d, hdJ⟩ * ⟨s, hsJ⟩ * ⟨d, hdJ⟩⁻¹ * ⟨s, hsJ⟩⁻¹ : ↥J') = 1 := by
      have hbot : (⟨d, hdJ⟩ * ⟨s, hsJ⟩ * ⟨d, hdJ⟩⁻¹ * ⟨s, hsJ⟩⁻¹ : ↥J') ∈
          (⊥ : Subgroup ↥J') := by
        rw [← hSO]
        exact ⟨hmemS, hmemO⟩
      simpa using hbot
    have h1 : d * s * d⁻¹ * s⁻¹ = 1 := by simpa using congrArg Subtype.val hone
    calc d * s = (d * s * d⁻¹ * s⁻¹) * (s * d) := by group
      _ = s * d := by rw [h1, one_mul]
  intro d hd
  refine Subgroup.mem_map.mpr ⟨⟨d, hd.1⟩, Subgroup.mem_center_iff.mpr fun s => ?_, rfl⟩
  apply Subtype.ext
  exact (hcentral d hd s s.2).symm

private theorem inf_oTwoZStar_eq_center {J' S' : Subgroup G}
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J')
    (hZcard : Nat.card (Subgroup.center (threeStar J')) = 3)
    (hcardS' : Nat.card S' = 27)
    (hnaS' : ∃ a b : ↥S', a * b ≠ b * a)
    (hZle : Subgroup.center (threeStar J') ≤
      (S'.subgroupOf J').map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J'))) :
    S' ⊓ oTwoZStar J' = (Subgroup.center ↥S').map S'.subtype := by
  have hcardD := card_inf_oTwoZStar hS' hZcard hZle
  have hcardZ : Nat.card ↥((Subgroup.center ↥S').map S'.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective S'.subtype_injective]
    exact CFSG.RankThree.PartTwo.Sec4.RonanK432.card_center_eq_three_of_card_27 hcardS' hnaS'
  exact Subgroup.eq_of_le_of_card_ge
    (inf_oTwoZStar_le_center (J' := J') (S' := S') hS')
    (by rw [hcardZ, hcardD])

private theorem card_sylow_three {J' S' : Subgroup G}
    (htype : IsSL34Star J' ∨ Is3A6Star J')
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J') : Nat.card S' = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardL : Nat.card (threeStar J') = 60480 ∨ Nat.card (threeStar J') = 1080 := by
    rcases htype with hSL | hA6
    · exact Or.inl (IsSL34Star.card_threeStar hSL)
    · exact Or.inr (CFSG.RankThree.PartTwo.Sec19.Item19Res4Proof.card_eq_of_isTripleA6
        ⟨hA6.2, hA6.1⟩)
  have hJcard : Nat.card J' = Nat.card (CFSG.pPrimeCore 3 ↥J') *
      Nat.card (threeStar J') := by
    rw [← Subgroup.card_mul_index (CFSG.pPrimeCore 3 ↥J'), Subgroup.index_eq_card]
  have hfact : (Nat.card J').factorization 3 = 3 := by
    rw [hJcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J'))), zero_add]
    rcases hcardL with h | h
    · rw [h, show 60480 = 3 ^ 3 * 2240 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    · rw [h, show 1080 = 3 ^ 3 * 40 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hS'.card_eq, hfact]
  norm_num

private theorem pow_three_eq_one_of_component
    {J' S' : Subgroup G} (hJ' : IsKComp M N J')
    (htype : IsSL34Star J' ∨ Is3A6Star J')
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J') (hcardS' : Nat.card S' = 27) :
    ∀ x ∈ S', x ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := hJ'.isQuasisimple
  haveI : Group.IsPerfect (threeStar J') := hq.1
  have hZcard : Nat.card (Subgroup.center (threeStar J')) = 3 := by
    rcases htype with hSL | hA6
    · exact hSL.2
    · exact hA6.2
  set q : ↥J' →* threeStar J' := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J') with hqdef
  set S : Subgroup ↥J' := S'.subgroupOf J' with hSdef
  set P : Subgroup (threeStar J') := S.map q with hPdef
  have hInj : Set.InjOn q (S : Set ↥J') := pPrimeCore_quotient_injOn_of_isSylowOf hS'
  have hPcard : Nat.card P = 27 := by
    have h1 : Nat.card P = Nat.card S := by
      rw [hPdef, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hInj]
      rfl
    rw [h1, hSdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'.le).toEquiv, hcardS']
  obtain ⟨Q, hQ⟩ := hS'.exists_sylow_eq_subgroupOf
  set R : Sylow 3 (threeStar J') := Q.mapSurjective (QuotientGroup.mk'_surjective _) with hRdef
  have hRcoe : (R : Subgroup (threeStar J')) = P := by
    rw [hRdef, Sylow.coe_mapSurjective, hQ, hPdef, hSdef]
  have hRcard : Nat.card ↥(R : Subgroup (threeStar J')) = 27 := by
    rw [hRcoe]; exact hPcard
  have hRexp : ∀ x ∈ (R : Subgroup (threeStar J')), x ^ 3 = 1 := by
    refine pow_three_eq_one_of_sylow_three hZcard ?_ R hRcard
    rcases htype with hSL | hA6
    · exact exists_conj_inv_of_isL34Type hSL.1
    · exact exists_conj_inv_of_isA6Type hA6.1
  intro x hx
  let xJ : ↥J' := ⟨x, hS'.le hx⟩
  have hxS : xJ ∈ S := Subgroup.mem_subgroupOf.mpr hx
  have hmap3 : (q xJ) ^ 3 = 1 := by
    refine hRexp (q xJ) ?_
    rw [hRcoe]
    exact Subgroup.mem_map.mpr ⟨xJ, hxS, rfl⟩
  have hq3 : q (xJ ^ 3) = 1 := by rw [map_pow, hmap3]
  have hx3S : xJ ^ 3 ∈ S := S.pow_mem hxS 3
  have h1 : xJ ^ 3 = 1 := hInj hx3S S.one_mem (by rw [hq3, map_one])
  simpa using congrArg Subtype.val h1

private theorem not_commutative_and_center_le_image {J' S' : Subgroup G}
    (hJ' : IsKComp M N J')
    (htype : IsSL34Star J' ∨ Is3A6Star J')
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J') (hcardS' : Nat.card S' = 27) :
    (∃ a b : ↥S', a * b ≠ b * a) ∧
      Subgroup.center (threeStar J') ≤
        (S'.subgroupOf J').map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J')) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := hJ'.isQuasisimple
  haveI : Group.IsPerfect (threeStar J') := hq.1
  have hZcard : Nat.card (Subgroup.center (threeStar J')) = 3 := by
    rcases htype with hSL | hA6
    · exact hSL.2
    · exact hA6.2
  set q : ↥J' →* threeStar J' := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J') with hqdef
  set S : Subgroup ↥J' := S'.subgroupOf J' with hSdef
  set P : Subgroup (threeStar J') := S.map q with hPdef
  have hInj : Set.InjOn q (S : Set ↥J') := pPrimeCore_quotient_injOn_of_isSylowOf hS'
  have hPcard : Nat.card P = 27 := by
    have h1 : Nat.card P = Nat.card S := by
      rw [hPdef, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hInj]
      rfl
    rw [h1, hSdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'.le).toEquiv, hcardS']
  obtain ⟨Q, hQ⟩ := hS'.exists_sylow_eq_subgroupOf
  set R : Sylow 3 (threeStar J') := Q.mapSurjective (QuotientGroup.mk'_surjective _) with hRdef
  have hRcoe : (R : Subgroup (threeStar J')) = P := by
    rw [hRdef, Sylow.coe_mapSurjective, hQ, hPdef, hSdef]
  have hRcard : Nat.card ↥(R : Subgroup (threeStar J')) = 27 := by
    rw [hRcoe]; exact hPcard
  have hnaR := sylow_three_not_commutative hZcard R hRcard
  have hZleP : Subgroup.center (threeStar J') ≤ P := by
    rw [← hRcoe]
    exact (CFSG.HardMathSupport.Solomon.Coordinator.i112v_sylow_center
      hZcard R hRcard hnaR).1
  have hnaP : ∃ a b : ↥P, a * b ≠ b * a := by
    obtain ⟨r, hr, s, hs, hrs⟩ := hnaR
    rw [hRcoe] at hr hs
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, fun h => hrs (congrArg Subtype.val h)⟩
  have hnaS' : ∃ a b : ↥S', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnaP
    obtain ⟨a₀, ha₀S, ha₀⟩ := Subgroup.mem_map.mp (by rw [← hPdef]; exact a.2)
    obtain ⟨b₀, hb₀S, hb₀⟩ := Subgroup.mem_map.mp (by rw [← hPdef]; exact b.2)
    rw [hSdef] at ha₀S hb₀S
    have ha₀' : (a₀ : G) ∈ S' := Subgroup.mem_subgroupOf.mp ha₀S
    have hb₀' : (b₀ : G) ∈ S' := Subgroup.mem_subgroupOf.mp hb₀S
    refine ⟨⟨a₀, ha₀'⟩, ⟨b₀, hb₀'⟩, fun h => hab ?_⟩
    have hG : (a₀ : G) * (b₀ : G) = (b₀ : G) * (a₀ : G) :=
      congrArg (fun z : ↥S' => (z : G)) h
    have hq : q (a₀ * b₀) = q (b₀ * a₀) := by
      apply congrArg q
      apply Subtype.ext
      simpa using hG
    rw [map_mul, map_mul] at hq
    apply Subtype.ext
    change (a : threeStar J') * (b : threeStar J') =
      (b : threeStar J') * (a : threeStar J')
    rw [← ha₀, ← hb₀]
    exact hq
  refine ⟨hnaS', ?_⟩
  simpa [hPdef, hSdef, hqdef] using hZleP

theorem IsKComp.sylow_three_structure
    {J' S' : Subgroup G} (hJ' : IsKComp M N J')
    (htype : IsSL34Star J' ∨ Is3A6Star J')
    (hS' : CFSG.ABGLocalTools.IsSylowOf 3 S' J') :
    Nat.card S' = 27 ∧ (∀ x ∈ S', x ^ 3 = 1) ∧
      S' ⊓ oTwoZStar J' = (Subgroup.center ↥S').map S'.subtype ∧
      Nat.card ↥((Subgroup.center ↥S').map S'.subtype) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card (Subgroup.center (threeStar J')) = 3 := by
    rcases htype with hSL | hA6
    · exact hSL.2
    · exact hA6.2
  have hcardS' := card_sylow_three htype hS'
  obtain ⟨hnaS', hZle⟩ := not_commutative_and_center_le_image hJ' htype hS' hcardS'
  have hexp := pow_three_eq_one_of_component hJ' htype hS' hcardS'
  have hcardZ' : Nat.card ↥((Subgroup.center ↥S').map S'.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective S'.subtype_injective]
    exact CFSG.RankThree.PartTwo.Sec4.RonanK432.card_center_eq_three_of_card_27 hcardS' hnaS'
  exact ⟨hcardS', hexp,
    inf_oTwoZStar_eq_center hS' hZcard hcardS' hnaS' hZle, hcardZ'⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
