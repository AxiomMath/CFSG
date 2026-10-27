module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.ASHypK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.RankTwoK
public import CFSG.Quasithin.Background.E2TwoProofAS
public import CFSG.Quasithin.Background.GoldschmidtB69DeepOrdA
public import CFSG.Quasithin.MS93.FFTypes
public import CFSG.Quasithin.Background.GoldschmidtB69DeepG2Aux

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69K

variable {V : Type} [CommGroup V] [Finite V]

theorem card_of_isPSU_three_three {X : Type} [Group X] (hX : IsPSU 3 3 1 X) :
    Nat.card X = 6048 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hX
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have hbot := CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e2 : StatedProj (StatedSU 3 3 F) ≃* StatedSU 3 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  rw [Nat.card_congr (e.toEquiv.trans e2.toEquiv),
    CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9]

theorem asCases_famC {X : Type} [Group X] {K T M : Subgroup X} (h : E2P.ASCases K T M) :
    B69.E22FamC ↥K := by
  unfold E2P.ASCases at h
  rcases h with ⟨n, ⟨h2, h | h | h⟩, -⟩ | ⟨n, hn, h | h, -, -⟩ | ⟨p, e, -, -, -, -, h, -, -⟩ |
    ⟨p, -, hp2, ⟨h4, h⟩ | ⟨h4, h, -⟩, -⟩
  · exact Or.inl ⟨2, n, h⟩
  · exact Or.inr (Or.inl ⟨n, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h⟩))))
  · exact Or.inl ⟨p, e, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp2, h4, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp2, h4, h⟩)))))

theorem not_psu_three_three (hF : E2P.E22Families)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) :
    ¬ IsPSU 3 3 1 (↥L ⧸ Subgroup.center ↥L) := by
  intro h
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e⟩⟩ := asHyp_of_compHypK hH
  have hKp : IsPSU 3 3 1 ↥K := IsPSU.of_mulEquiv e h
  have hlist : A23List ↥K :=
    Or.inr (Or.inl ⟨3, Nat.prime_three, by norm_num, Or.inr (Or.inr hKp)⟩)
  have hfam : B69.E22FamC ↥K := asCases_famC (E2P.asCases_of_families hF hAS hlist)
  exact B69.E22FamC.not_card_6048 hfam odd_one (by rw [mul_one, card_of_isPSU_three_three hKp])

theorem false_of_sl_sectionK (hLn : E2P.E22LnTwoFam)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K]
    (hK : Nat.card K = 2) (π : ↥(StatedSL n K) →* ↥(B69.wtL L W))
    (hπ : Function.Surjective π) : False := by
  obtain ⟨-, -, -, -, -, -, hL, -⟩ := id hH
  obtain ⟨hLW, hLZ⟩ := B69.stab_of_irr hW
  obtain ⟨ℓ, hℓs, -⟩ := B69.exists_surj_autSec hLW hLZ
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hs : IsSimpleGroup ↥(StatedSL n K) := B69.isSimpleGroup_statedSL_two hK (by omega)
  have hnt : Nontrivial ↥(B69.wtL L W) := B69.nontrivial_autSec hW
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rcases CFSG.eq_bot_or_eq_top_of_normal π.ker (MonoidHom.normal_ker π) with hbot | htop
    · have : g ∈ π.ker := MonoidHom.mem_ker.2 hg
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  let eπ : ↥(StatedSL n K) ≃* ↥(B69.wtL L W) := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  haveI : IsSimpleGroup ↥(B69.wtL L W) := (MulEquiv.isSimpleGroup_congr eπ).mp hs
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  obtain ⟨eLZ⟩ := B69.equiv_of_central_quotients hL.2.2 (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) ℓ hℓs
  have hPSL : IsPSL n 2 1 (↥L ⧸ Subgroup.center ↥L) := by
    refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, K, inferInstance, hfin,
      by simpa using hK, ⟨(eLZ.trans eπ.symm).trans (B69.statedSLEquivStatedProj hK n)⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  exact B69K.not_lnTwo hLn hH hn hPSL

theorem equiv_quot_L_of_hyp {V : Type} [CommGroup V] [Finite V] {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) {P : Type} [Group P] (hP : CFSG.IsQuasisimple P)
    (ℓ : ↥L →* P) (hℓs : Function.Surjective ℓ) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* P ⧸ Subgroup.center P) := by
  obtain ⟨-, -, -, -, -, -, hL, -⟩ := id hH
  haveI : IsSimpleGroup (P ⧸ Subgroup.center P) := hP.2.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  exact B69.equiv_of_central_quotients hL.2.2 (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.mk' (Subgroup.center P)).comp ℓ)
    ((QuotientGroup.mk'_surjective _).comp hℓs)

theorem isG2_quot_L_absurd {V : Type} [CommGroup V] [Finite V] (hExc : E2P.E22Char2ExcFam)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] (hG2 : IsG2 2 n (↥(quasithinG2 K) ⧸ Subgroup.center ↥(quasithinG2 K)))
    {P : Type} [Group P] (eL : ↥(quasithinG2 K) ≃* P) (hP : CFSG.IsQuasisimple P)
    (ℓ : ↥L →* P) (hℓs : Function.Surjective ℓ) : False := by
  obtain ⟨eLZ⟩ := equiv_quot_L_of_hyp hH hP ℓ hℓs
  have hwt : IsG2 2 n (P ⧸ Subgroup.center P) :=
    IsG2.of_mulEquiv (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)) hG2
  exact not_char2Exc hExc hH (Or.inl ⟨n, hn, IsG2.of_mulEquiv eLZ.symm hwt⟩)

theorem not_psu_of_quot {V : Type} [CommGroup V] [Finite V]
    (hF : E2P.E22Families) {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L)
    {P : Type} [Group P] (hP : CFSG.IsQuasisimple P) (ℓ : ↥L →* P) (hℓs : Function.Surjective ℓ)
    (hPSU : IsPSU 3 3 1 (P ⧸ Subgroup.center P)) : False := by
  obtain ⟨eLZ⟩ := equiv_quot_L_of_hyp hH hP ℓ hℓs
  exact not_psu_three_three hF hH (IsPSU.of_mulEquiv eLZ.symm hPSU)

section NoG2


theorem noG2K (hExc : E2P.E22Char2ExcFam) (hF : E2P.E22Families) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), B69.CompHypK X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
          ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
            IsFFStarOffender (B69.wtLA A L W) B → ¬ B42Case4 (B69.wtLA A L W) (B69.wtL L W) B := by
  intro V _ _ hV X T M A L hH W hW B hBA hB hc
  obtain ⟨ℓ, hℓs, -, hLbq, hIrr, hFstar, hLbn, -⟩ := sectionFittingDataK hV hH hW
  obtain ⟨⟨n, hn, -, hn2⟩, -⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Bridge.TypeList.exists_equiv_of_g2Natural hn
  have hn1 : 1 ≤ n := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge n 2 with hlt | hge
  ·
    obtain rfl : n = 1 := by omega
    have h2 : Nat.card K = 2 := by simpa using hK
    have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
    have hLJ : autSec L W (W ⊓ fixV L) ≤ ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) :=
      B69.le_ffJ_of_fitting hS2 hFstar.symm hLbq hIrr hB
    have hJG := CFSG.QuasithinUnique.Bridge.TypeList.ffJ_le_self (autSec (L ⊔ A) W (W ⊓ fixV L))
    set J := ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) with hJdef
    have hnorm : ((autSec L W (W ⊓ fixV L)).subgroupOf J).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hLbn _ (hJG g.2) _ hx
    set N := ((autSec L W (W ⊓ fixV L)).subgroupOf J).map e.symm.toMonoidHom with hNdef
    have hNn : N.Normal := Subgroup.Normal.map hnorm e.symm.toMonoidHom e.symm.surjective
    let iso : ↥(autSec L W (W ⊓ fixV L)) ≃* ↥N :=
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.trans
        (e.symm.subgroupMap ((autSec L W (W ⊓ fixV L)).subgroupOf J))
    have hperf : Group.IsPerfect ↥N := by
      have : Group.IsPerfect ↥(autSec L W (W ⊓ fixV L)) := hLbq.1
      exact Group.IsPerfect.ofSurjective (f := iso.toMonoidHom) iso.surjective
    have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := B69.nontrivial_autSec hW
    have hne : N ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot]
      exact iso.injective.nontrivial
    have hperf' : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.1 hperf
    have hinj := (quasithinG2 K).subtype_injective
    have hgd := B69.g2Derived_simple_card h2
    have hNeq : N.map (quasithinG2 K).subtype = ⁅quasithinG2 K, quasithinG2 K⁆ := by
      refine B69.eq_commutator_of_perfect_normal (H := quasithinG2 K) ?_ ?_ ?_ ?_ hgd.1
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · rintro h hh _ ⟨x, hx, rfl⟩
        exact ⟨⟨h, hh⟩ * x * ⟨h, hh⟩⁻¹, hNn.conj_mem x hx ⟨h, hh⟩, rfl⟩
      · rw [← Subgroup.map_commutator, hperf']
      · intro hbot
        exact hne ((Subgroup.map_eq_bot_iff_of_injective N hinj).1 hbot)
    let eD : ↥N ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
      (N.equivMapOfInjective (quasithinG2 K).subtype hinj).trans (MulEquiv.subgroupCongr hNeq)
    obtain ⟨-, hPSU⟩ :=
      (CFSG.Quasithin.MS93.card_quot_of_equiv_g2Derived h2 (eD.symm.trans iso.symm)).1
    exact not_psu_of_quot hF hH hLbq ℓ hℓs hPSU
  ·
    have heq : ffJ (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) := hn2 hge
    let eL : ↥(quasithinG2 K) ≃* ↥(autSec L W (W ⊓ fixV L)) :=
      e.trans (MulEquiv.subgroupCongr heq)
    haveI : Fintype K := Fintype.ofFinite K
    have hF' : Fintype.card K = 2 ^ n := by rw [Fintype.card_eq_nat_card, hK]
    exact isG2_quot_L_absurd hExc hH hge (CFSG.Quasithin.SmithC27.isG2_quasithinG2 hge hF') eL
      hLbq ℓ hℓs

end NoG2

end B69K

end CFSG.Quasithin
