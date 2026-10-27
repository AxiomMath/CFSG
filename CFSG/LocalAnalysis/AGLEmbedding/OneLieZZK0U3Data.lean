module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0U3
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0U3Lift
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Norm
public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0U3Sylow

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroComp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}
  {Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p)}
  {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} {T₁ : Sylow p L}

theorem exists_u3Data [Fact p.Prime] (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    (hK : KFactOneLie) (hKU2 : KFactUnitarySylowStructure) (hKU3 : KFactUnitarySylowCenterTorus)
    (hKU4 : KFactUnitaryTorusPPD) (hKU6 : KFactUnitaryBorelMaximal)
    (hKU8 : KFactUnitarySylowNormalizerSolvable) (hKU9 : KFactUnitaryAutElemRank)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hWK : d1MapPCore p M H ≤ K)
    (hcore₁ : GLBPrimeCore p (H₁ ⊓ M) = GLBPrimeCore p H₁) (h3₁ : D1PhaseThree p P' M H₁ S)
    (hZT : centerOf ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L) ≤
      d1MapPCore p M H₁)
    (hU : IsUnitaryGroup p L)
    (hcard : Nat.card ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) :
      Subgroup L) = Nat.card (d1LiftX p H R K)) :
    ∃ n : ℕ, D1OneLieU3Data p n P' M H₁ S (d1LiftX p H₁ S L) (d1LiftX p H R K)
      (d1PlusCore p H₁ L) := by
  have hc := h.kzero
  have hd := hc.data
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.red.ne_two
  have : L.Normal := h.normal
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set U := d1LiftX p H₁ S L with hUdef
  obtain ⟨d, hdU, hLe⟩ := hU
  have hLe' : Nonempty (L ≃* CatGroup d) := hLe
  have hn2 : 2 ≤ d.1.fieldExponent := by
    by_contra hlt
    apply h.big
    obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup (MulAut L))
    have h1 := hKU9 L p d hdU hLe' E hE
    rw [hEcard] at h1
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  set n := d.1.fieldExponent with hn
  have hTF : OneLieTorusFacts p L T₁ n 1 :=
    oneLieTorusFacts_of_unitary hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 hp2 hdU hn2 hLe' T₁
  obtain ⟨hTcard, hTcomm, hTpow, -⟩ := hKU2 L p d hp2 hdU hLe' T₁
  obtain ⟨ψ, hψinj, hψrange, -⟩ := hKU3 L p d hdU hLe' T₁
  have hZTcard : Nat.card ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) :
      Subgroup L) = p ^ n := by
    rw [← hψrange, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, GaloisField.card p n (by omega)]
  have hXcard : Nat.card X = p ^ n := hcard.symm.trans hZTcard
  have hXH₁ : X ≤ H₁ := hc.liftX_le_H₁
  have hSp : IsPGroup p S := hc.escape.isPGroup
  have hSH₁ : S ≤ H₁ := hc.escape.le_H
  have hUH₁ : U ≤ H₁ := d1LiftX_le_H p H₁ S L
  have hUS : U ≤ S := d1LiftX_le p H₁ S L
  have hUp : IsPGroup p U := hSp.to_le hUS
  have hUmap : (U.subgroupOf H₁).map π₁ = (T₁ : Subgroup L).map L.subtype := by
    rw [hUdef, map_d1LiftX, h.sylow, ← h.rbar]
  have hW := hc.d1MapPCore_le_map_liftX hK h84 hD2 hWK h3₁
  have hZeq : ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map
      L.subtype = centerOf ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L) := by
    rw [← h.sylow]
    exact map_subtype_centerOf _
  have hXmap : (X.subgroupOf H₁).map π₁ =
      ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map L.subtype := by
    have hle : ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map
        L.subtype ≤ (X.subgroupOf H₁).map π₁ := hZeq ▸ hZT.trans hW
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Subgroup.card_map_of_injective L.subtype_injective, hZTcard, hc.card_map_eq.2, hXcard]
  have hXU : X ≤ U := fun x hx => ⟨⟨x, hXH₁ hx⟩,
    ⟨Subgroup.mem_subgroupOf.mpr (hc.liftX_le hx), Subgroup.mem_comap.mpr (h.le
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (le_nclIn (d1LiftX_le_H p H R K) hx))))⟩, rfl⟩
  obtain ⟨hZC, hcomm, hcardU, hpowU⟩ :=
    sylow_structure_of_map_eq hUH₁ hUp hXU hUmap hXmap hTcard hTcomm hTpow
  have hrank : Open.pRank p (⊤ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤ 2 * n + 1 :=
    pRank_top_le_of_aut (K := L)
      (fun A hA hAp => h.red.isCyclic_of_le_centralizer h.comp h.not_le hAp hA)
      (fun E hE => by simpa using hTF.autRank E hE)
  have hY₀T := le_normalizer_inf_of_isCoatom Rb₁ h.borel_le h.not_le T₁ h.sylow
    hTF.borel_coatom
  have hperf : ∀ L₀ : Subgroup G, L₀ ≤ H₁ ⊓ M → ⁅L₀, L₀⁆ = L₀ → L₀ ≤ d1PlusCore p H₁ L :=
    fun L₀ hL₀ hL₀L₀ => le_d1PlusCore_of_map_le (hL₀.trans inf_le_left)
      (le_centralizer_of_perfect_of_borel T₁ h.sylow hTF hY₀T
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H₁ hL₀))
        (commutator_map_eq_self (hL₀.trans inf_le_left) hL₀L₀))
  have hcommplus : ∀ x ∈ U, ∀ c ∈ d1PlusCore p H₁ L,
      x * c * x⁻¹ * c⁻¹ ∈ GLBPrimeCore p H₁ := by
    intro x hx c' hc'
    obtain ⟨x', ⟨-, hx'L⟩, rfl⟩ := hx
    obtain ⟨c'', hc''C, rfl⟩ := hc'
    have hcomm' := Subgroup.mem_centralizer_iff.mp hc''C _ (Subgroup.mem_comap.mp hx'L)
    refine (mem_glbPrimeCore_iff_mk_eq_one (x' * c'' * x'⁻¹ * c''⁻¹)).mpr ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm'
  have hXY : X ≤ pCorePreimage p M := by
    have hmap : (X.subgroupOf H₁).map π₁ ≤
        ((S ⊓ pCorePreimage p M).subgroupOf H₁).map π₁ := by
      rw [← h3₁.d1MapPCore_eq h84 hD2, hXmap, hZeq]
      exact hZT
    exact (le_of_map_mk_le_of_isPGroup hSH₁ hSp hc.liftX_le inf_le_left hmap).trans inf_le_right
  have hYX : ∀ {A : Subgroup G}, A ≤ S → A ≤ pCorePreimage p M → A ≤ X := fun hAS hAY =>
    le_of_map_mk_le_of_isPGroup hSH₁ hSp hAS hc.liftX_le
      ((Subgroup.map_mono (Subgroup.comap_mono hAY)).trans hW)
  have hcommY : ∀ x ∈ U, ∀ y ∈ S ⊓ pCorePreimage p M, x * y = y * x := by
    intro x hx y hy
    have hyC : y ∈ U ⊓ Subgroup.centralizer (U : Set G) := hZC ▸ hYX inf_le_left inf_le_right hy
    exact Subgroup.mem_centralizer_iff.mp hyC.2 x hx
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3
      (show 3 ≤ 2 * n by omega)
  have := Fact.mk hr
  obtain ⟨c, hcN, hcord, hcirr⟩ := hKU4 L p d hdU hn2 hLe' T₁ r hr hrdvd hprim
  have hpr : (p : ZMod r) ^ (2 * n) = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos _).mp hrdvd
  have hord : orderOf (p : ZMod r) = 2 * n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨hpr, fun k hk hk0 h => hprim k hk0 hk
      ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpr
    exact zero_ne_one hpr
  have hndvd : 2 * n ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have hr2n : 2 * n < r := by
    have h1 : 0 < r - 1 := by
      rcases Nat.lt_or_ge (r - 1) 1 with h | h
      · exfalso
        have : r = 2 := by have := hr.two_le; omega
        subst this
        obtain ⟨c', hc'⟩ := hndvd
        omega
      · omega
    have := Nat.le_of_dvd h1 hndvd
    omega
  have hrp : r ≠ p := by
    rintro rfl
    exact hp0 (ZMod.natCast_self r)
  have hrp1 : ¬ r ∣ p - 1 := by
    have h := hprim 1 one_pos (by omega)
    rwa [pow_one] at h
  have hNHM : GLBPrimeCore p H₁ ≤ H₁ ⊓ M := le_inf (glbPrimeCore_le p H₁) hc.escape.primeCore_le
  have hNle : L ⊓ Subgroup.normalizer ((((T₁ : Subgroup L).map L.subtype :
      Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p))) :
      Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤ ((H₁ ⊓ M).subgroupOf H₁).map π₁ := by
    rw [h.sylow]
    exact h.borel_le
  obtain ⟨t, htK, htU, htr, htrU, htnt, hirr⟩ :=
    exists_lift_of_ppd_of_map hUH₁ hUp hXU hNHM hUmap hXmap hNle hcN hcord hcirr
  have htX : t ∈ Subgroup.normalizer (X : Set G) := by
    rw [hZC]
    exact mem_normalizer_centerOf htU
  have htXc := mem_centralizer_of_isPGroup_of_card_eq_pow hXcard htX htr
    (fun k hk hkn => hprim k hk (by omega)) hrp
  exact ⟨n,
    { ph3 := h3₁
      ind := hd.cfg.indBetaFour
      two_le := hn2
      le_R := hUS
      center_eq := hZC
      card_eq := hcardU
      card_center := hXcard
      commutator_eq := hcomm
      pow_eq_one := hpowU
      pRank_le := pRank_inf_le_of_pRank_top_le (M := M) hp hrank
      perfect_le := hperf
      plus_cyclic := fun A hAN hA => h.isCyclic_of_le_plusCore hAN hA
      comm_plus := hcommplus
      comm_core := h.commutator_le_twoCore h3₁ hXY
      core_eq := hcore₁
      le_pCore := hXY
      inf_pCore := hYX (inf_le_left.trans hUS) inf_le_right
      comm_pCore := hcommY
      ppd := ⟨r, t, hr, hr2n, hrp, hrp1, htK, htU, htr, htXc, htrU, htnt, hirr⟩ }⟩

end D1OneLieKZeroComp

end CFSG.AGLEmbedding
