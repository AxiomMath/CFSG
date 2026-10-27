module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeLift
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}

theorem D1CaseTwoData.false_of_ree (hd : D1CaseTwoData 3 P M H R Rbar)
    (hKR4 : KFactReeBorelMaximal) (hKJ : KFactReeInvolution) (hL28 : KFactL28AutThree)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 3 M H) (hLc : IsCaseTwoGroup 3 L) {z : H} (hzR : (z : G) ∈ R)
    (hzp : orderOf (z : G) = 3) (hRz : R ≤ Subgroup.centralizer ({(z : G)} : Set G))
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) 3) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) 3)))
    {P' : Sylow 3 G} (hP'M : (P' : Subgroup G) ≤ M) (hRP' : R ≤ P')
    {Pbar : Sylow 3 (D1CzQuot 3 (z : G))} {KC : Subgroup (D1CzQuot 3 (z : G))}
    (hRC : D1ReducedCentralizer 3 P' M (z : G) Pbar KC) (hzK : d1CzElt 3 (z : G) ∉ KC)
    {d : TauCeti.ValidLieTypeIndex} (hRee : IsReeGTwoIndex 3 d)
    (he : Nonempty (KC ≃* (TauCeti.CFSGIndex.lie d).Group)) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hext := hd.cfg.ext
  set C := Subgroup.centralizer ({(z : G)} : Set G)
  set OC := primeComplementCore (G := C) 3
  set ρ := QuotientGroup.mk' OC
  have hOC := primeComplementCore_coprime (G := C) 3
  have := hRC.normal
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hRC.normal.isSubnormal
  obtain ⟨J, hJN, hJ2, hconj, hVel, hVcard, hCB⟩ := hKJ KC d hRee he T
  have hn := hRee.three_le_fieldExponent
  set U : Subgroup (D1CzQuot 3 (z : G)) := (Pbar : Subgroup (D1CzQuot 3 (z : G))) ⊓ KC
  set J' : D1CzQuot 3 (z : G) := (J : D1CzQuot 3 (z : G))
  set V : Subgroup (D1CzQuot 3 (z : G)) :=
    ((T : Subgroup KC) ⊓ Subgroup.centralizer ({J} : Set KC)).map KC.subtype
  have hVel' : IsElemAbelian 3 V := elementary_abelian_map 3 hVel KC.subtype
  have hVcard' : Nat.card V = 3 ^ d.1.fieldExponent := by
    rw [Subgroup.card_map_of_injective KC.subtype_injective, hVcard]
  have hVU : V ≤ U := by
    rw [← hT]
    exact Subgroup.map_mono inf_le_left
  have hVJ : V ≤ Subgroup.centralizer ({J'} : Set (D1CzQuot 3 (z : G))) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hv.2))
  have hU3 : 3 ≤ Open.pRank 3 U :=
    hn.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨V, hVU, hVel', hVcard'⟩)
  have hB := hRC.not_map_le_of_isCoatom T hT hU3 (hKR4 KC d hRee he T) hCB
  have hUN : ∀ y ∈ (Pbar : Subgroup (D1CzQuot 3 (z : G))),
      y ∈ Subgroup.normalizer (U : Set (D1CzQuot 3 (z : G))) := fun y hy =>
    mem_normalizer_inf_of_mem_normalizer (Subgroup.le_normalizer hy)
      ((Subgroup.normalizer_eq_top KC).symm ▸ Subgroup.mem_top y)
  have hJ'N : J' ∈ Subgroup.normalizer (U : Set (D1CzQuot 3 (z : G))) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map KC.subtype ⟨J, hJN, rfl⟩
  have hUX : U ≤ d1CzX0 3 M (z : G) :=
    Subgroup.le_normalizer.trans (hRC.normalizer_le inf_le_left hU3)
  have hJ'X : J' ∈ d1CzX0 3 M (z : G) := hRC.normalizer_le inf_le_left hU3 hJ'N
  have hJ'2 : J' ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hJ2, pow_orderOf_eq_one, Subgroup.coe_one]
  have hJ'1 : J' ≠ 1 := fun h => by
    rw [show J = 1 from Subtype.ext h, orderOf_one] at hJ2
    omega
  set Rt : Subgroup (D1CzQuot 3 (z : G)) := (R.subgroupOf C).map ρ
  have hRtP : Rt ≤ Pbar := by
    rw [hRC.sylow_eq]
    exact Subgroup.map_mono fun r hr => hRP' hr
  have hYP : Rt ⊔ U ≤ Pbar := sup_le hRtP inf_le_left
  have hconj' : ∀ y ∈ Rt ⊔ U, ∃ u ∈ U, y * J' * y⁻¹ = u * J' * u⁻¹ := by
    intro y hy
    have hyN := hUN y (hYP hy)
    set t : KC := ⟨y * J' * y⁻¹, hRC.normal.conj_mem _ J.2 y⟩
    have hmemT : ∀ k : KC, k ∈ (T : Subgroup KC) ↔ (k : D1CzQuot 3 (z : G)) ∈ U := fun k => by
      rw [← hT]
      exact ⟨fun hk => ⟨k, hk, rfl⟩, fun ⟨k', hk', hkk'⟩ => (Subtype.ext hkk' : k' = k) ▸ hk'⟩
    have htN : t ∈ Subgroup.normalizer ((T : Subgroup KC) : Set KC) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [hmemT, hmemT]
      exact Subgroup.mem_normalizer_iff.mp ((mul_mem (mul_mem hyN hJ'N) (inv_mem hyN))) k
    have ht2 : orderOf t = 2 := by
      rw [← Subgroup.orderOf_coe t, ← hJ2, ← Subgroup.orderOf_coe J]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective J'
    obtain ⟨u, hu, htu⟩ := hconj t htN ht2
    exact ⟨u, (hmemT u).mp hu, by simpa [t] using congrArg Subtype.val htu⟩
  have hcount := card_mul_card_inf_centralizer_eq (fun y hy => hUN y (hRtP hy)) hconj'
  have hRU : Nat.card (Rt ⊓ U : Subgroup (D1CzQuot 3 (z : G))) ≤ 27 :=
    (Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_right)).trans
      (hd.card_inf_le hL28 hL hLX hLc hzR hzp hRz hzL hzK)
  have hUJ : 27 ≤ Nat.card (U ⊓ Subgroup.centralizer ({J'} : Set (D1CzQuot 3 (z : G))) :
      Subgroup (D1CzQuot 3 (z : G))) := by
    have h27 : 27 ≤ 3 ^ d.1.fieldExponent :=
      (show 27 = 3 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hn
    exact h27.trans (hVcard' ▸ Subgroup.card_le_of_le (le_inf hVU hVJ))
  have hRt : Nat.card Rt = Nat.card R := by
    obtain ⟨φ, -⟩ := exists_mulEquiv_map_mk OC hp hOC hext.isPGroup hRz
    exact (Nat.card_congr φ.toEquiv).symm
  set X := (Rt ⊔ U) ⊓ Subgroup.centralizer ({J'} : Set (D1CzQuot 3 (z : G)))
  have hXR : Nat.card R ≤ Nat.card X := by
    rw [← hRt]
    refine Nat.le_of_mul_le_mul_right ?_ (by norm_num : 0 < 27)
    calc Nat.card Rt * 27 ≤ Nat.card Rt * Nat.card (U ⊓ Subgroup.centralizer
          ({J'} : Set (D1CzQuot 3 (z : G))) : Subgroup (D1CzQuot 3 (z : G))) :=
          Nat.mul_le_mul_left _ hUJ
      _ = Nat.card X * Nat.card (Rt ⊓ U : Subgroup (D1CzQuot 3 (z : G))) := hcount
      _ ≤ Nat.card X * 27 := Nat.mul_le_mul_left _ hRU
  obtain ⟨hzZ, hzbarp⟩ :=
    hRC.center ⟨(z : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  have hztX : d1CzElt 3 (z : G) ∈ X :=
    ⟨Subgroup.mem_sup_left ⟨⟨(z : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, hzR, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hzZ J').symm⟩
  have hztV : d1CzElt 3 (z : G) ∉ V := by
    rintro ⟨v, -, hv⟩
    exact hzK (hv ▸ v.2)
  have hztC : d1CzElt 3 (z : G) ∈ Subgroup.centralizer (V : Set (D1CzQuot 3 (z : G))) :=
    Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hzZ v
  have hzt3 : d1CzElt 3 (z : G) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (d1CzElt 3 (z : G))
    rwa [show orderOf (d1CzElt 3 (z : G)) = 3 from hzbarp] at h
  have hX4 := succ_le_pRank_of_isElemAbelian hp hVel' hVcard' hztC hzt3 hztV
    (le_inf (hVU.trans le_sup_right) hVJ) hztX
  have hR3 : Open.pRank 3 R = 3 := hd.cfg.pRank_rbar_eq ▸ hd.rank
  have hRtX : Rt ≤ d1CzX0 3 M (z : G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, ⟨r.2, hext.le_M hr⟩, rfl⟩
  have hCJ := hext.centralizer_le_of_reducedCentralizer hRz
    (hext.odd_card_primeCore hP'M hRP' hRz hRC (by omega)) hJ'X hJ'2 hJ'1
    (Pbar.isPGroup'.to_le (inf_le_left.trans hYP)) (inf_le_left.trans (sup_le hRtX hUX))
    inf_le_right hXR (by omega)
  apply hB
  rintro _ ⟨k, hk, rfl⟩
  exact hCJ (Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)))

end CFSG.AGLEmbedding
