module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614JFaith
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614JModule
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Stage
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

namespace P614J

variable {G : Type} [Group G] [Finite G]

theorem false_of_card_lt {M B H S H₁ R : Subgroup G} (h : Prop614Extremal M B H S)
    (hH₁ : IsTwoLocal H₁) (hBH₁ : B ≤ H₁) (hH₁M : ¬ H₁ ≤ M)
    (hR : IsTwoInvariantIn B (H₁ ⊓ M) R) (hcard : Nat.card S < Nat.card R) : False := by
  obtain ⟨S₁, hRS₁, hS₁⟩ := exists_isMaxTwoInvariantIn_of_le hR
  have hlt : Nat.card S < Nat.card S₁ := hcard.trans_le (Subgroup.card_le_of_le hRS₁)
  have hS₁1 : S₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hlt
    have : 0 < Nat.card S := Nat.card_pos
    omega
  exact h.max H₁ S₁ ⟨hH₁, hBH₁, hH₁M, hS₁, hS₁1⟩ (Or.inl hlt)

theorem exists_not_commute_of_axb {M T₁ : Subgroup G} {z : G} (hT₁ : IsPGroup 2 T₁)
    (hT₁M : T₁ ≤ M) (hzT₁ : ∀ t ∈ T₁, z * t = t * z) (hzM : z ∈ M) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) (hchar : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M) :
    ∃ r ∈ pCoreOf 2 M ⊓ centralizer (T₁ : Set G), z * r ≠ r * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  set R : Subgroup G := pCoreOf 2 M with hRdef
  have hR : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  have hRn : M ≤ normalizer (R : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  let α : ↥(zpowers z) →* MulAut ↥R :=
    R.normalizerMonoidHom.comp (Subgroup.inclusion (zpowers_le.mpr (hRn hzM)))
  let β : ↥T₁ →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion (hT₁M.trans hRn))
  have hα : ∀ (a : ↥(zpowers z)) (r : ↥R), ((α a r : ↥R) : G) = (a : G) * r * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hβ : ∀ (t : ↥T₁) (r : ↥R), ((β t r : ↥R) : G) = (t : G) * r * (t : G)⁻¹ :=
    fun _ _ => rfl
  have hpow : ∀ a ∈ zpowers z, ∀ g : G, z * g = g * z → a * g = g * a := by
    intro a ha g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hg k).eq
  have hA : ¬ 2 ∣ Nat.card ↥(zpowers z) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    norm_num
  have hcomm : ∀ a t, α a * β t = β t * α a := by
    intro a t
    ext r
    have hat : (a : G) * t = t * a := hpow a a.2 t (hzT₁ t t.2)
    show (a : G) * ((t : G) * r * (t : G)⁻¹) * (a : G)⁻¹ =
      (t : G) * ((a : G) * r * (a : G)⁻¹) * (t : G)⁻¹
    calc (a : G) * ((t : G) * r * (t : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * t) * r * ((a : G) * t)⁻¹ := by group
      _ = ((t : G) * a) * r * ((t : G) * a)⁻¹ := by rw [hat]
      _ = (t : G) * ((a : G) * r * (a : G)⁻¹) * (t : G)⁻¹ := by group
  have hfix : ∀ a r, (∀ t, β t r = r) → α a r = r := by
    intro a r hr
    have hrc : (r : G) ∈ pCoreOf 2 M ⊓ centralizer (T₁ : Set G) := by
      refine ⟨r.2, mem_centralizer_iff.mpr fun t ht => ?_⟩
      have h1 : (t : G) * r * t⁻¹ = r := congrArg Subtype.val (hr ⟨t, ht⟩)
      calc t * (r : G) = t * r * t⁻¹ * t := by group
        _ = r * t := by rw [h1]
    have har : (a : G) * r = r * a := hpow a a.2 r (hcon r hrc)
    apply Subtype.ext
    rw [hα, har, mul_inv_cancel_right]
  have hall := CFSG.GroupTheory.thompson_A_times_B hR hA hT₁ α β hcomm hfix
  have hzc : z ∈ centralizer (R : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    have h1 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : G))
      (hall ⟨z, mem_zpowers z⟩)
    have h2 : z * r * z⁻¹ = r := h1
    calc r * z = z * r * z⁻¹ * z := by rw [h2]
      _ = z * r := by group
  exact hz1 (eq_one_of_isPGroup_two hR (hchar ⟨hzM, hzc⟩) hz3)

theorem exists_conj_le_normalizer_of_le (hS : RankThreeTheoremC.Setting G) {P : Sylow 3 G}
    {M : Subgroup G} (hsit : SmallRankSituation G 3 P M) (hα : HasPrimeConstraint (G := M) 3)
    {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    ∃ g : G, g ∈ M ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ normalizer (T : Set G) ∧
      zpowers x ⊔ zpowers z ≤ (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hgM, hPg⟩ := fail614_exists_conj_le_normalizer hS hsit hα hx hz hT
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hPM
  have hB3 : IsPGroup 3 ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card (n := 2) hpl.card_eq
  have hPgM : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨p, hp, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hPM hp)) (M.inv_mem hgM)
  have hle : ((g • P : Sylow 3 G) : Subgroup G) ≤ M ⊓ normalizer (T : Set G) := by
    rw [sylow_conjugate_eq_map]
    exact le_inf hPgM hPg
  obtain ⟨c, hc⟩ := pGroup_conjugate_into_sylow_within_overgroup 3 Nat.prime_three (g • P)
    (M ⊓ normalizer (T : Set G)) hle _ hB3 (le_inf hBM hT.1.2.2)
  rw [sylow_conjugate_eq_map] at hc
  have hcM : (c : G) ∈ M := (mem_inf.mp c.2).1
  have hcT : (c : G) ∈ normalizer (T : Set G) := (mem_inf.mp c.2).2
  refine ⟨(c : G)⁻¹ * g, M.mul_mem (M.inv_mem hcM) hgM, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have h1 : g * p * g⁻¹ ∈ normalizer (T : Set G) := hPg ⟨p, hp, rfl⟩
    have e : (c : G)⁻¹ * g * p * ((c : G)⁻¹ * g)⁻¹ = (c : G)⁻¹ * (g * p * g⁻¹) * (c : G)⁻¹⁻¹ := by
      group
    show (c : G)⁻¹ * g * p * ((c : G)⁻¹ * g)⁻¹ ∈ normalizer (T : Set G)
    rw [e]
    exact mul_mem (mul_mem (inv_mem hcT) h1) (inv_mem (inv_mem hcT))
  · intro y hy
    obtain ⟨p, hp, hpeq⟩ := hc ⟨y, hy, rfl⟩
    refine ⟨p, hp, ?_⟩
    have hpeq' : g * p * g⁻¹ = (c : G) * y * (c : G)⁻¹ := hpeq
    show (c : G)⁻¹ * g * p * ((c : G)⁻¹ * g)⁻¹ = y
    calc (c : G)⁻¹ * g * p * ((c : G)⁻¹ * g)⁻¹ = (c : G)⁻¹ * (g * p * g⁻¹) * c := by group
      _ = (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * c := by rw [hpeq']
      _ = y := by group

end P614J

theorem pieceClosing_holds : PieceClosing := by
  intro k3010 G _ _ P M x z H S K b hyp h618 h620 h620iii
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hyp.setting
  have hsit := hyp.situation
  have hx := hyp.point
  have hz := hyp.central
  have hopt := hyp.optimal
  have hK := h618.comp
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hsetup : Setup65A G P M x z := ⟨hS, hyp.u0, hsit, h618.alpha, hx, hz⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hP3 : CFSG.Open.pRank 3 (P : Subgroup G) = 3 :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
  have hzM : z ∈ M := hPM hz.mem
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hPM
  have hz1 : z ≠ 1 := hz.ne_one
  have hz3 : z ^ 3 = 1 := hz.pow_eq_one
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hH2 : IsTwoLocal H := hopt.ext.pair.isTwoLocal
  have hbH : b ∈ H := hBH h620.b_mem
  have hb3 : b ^ 3 = 1 := hpl.isElemAbelian.2 b h620.b_mem
  have hb1 : b ≠ 1 := fun h => h620.b_not_mem (h ▸ one_mem _)
  have hzK : z ∈ K := hK.mem (mem_zpowers z)
  have hHQ : H ≤ normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hKQ : K ≤ normalizer (pCoreOf 2 H : Set G) := hK.le.trans hHQ
  have hgen := P614J.eq_of_le_of_mem hK h618.core_eq hz3 hz1
  set V : Subgroup G := pCoreOf 2 H ⊓ centralizer (K : Set G) with hVdef
  have hVne : V ≠ ⊥ := by
    intro hV
    have hbQc := P614J.commute_of_inf_centralizer_eq_bot k3010 hKQ hV hzK hz1 hz3
      h620iii.core hgen (hK.normal hbH) (hHQ hbH) h620.b_cent (h620.kbar.imp (fun h => h.1) id)
    have hbC : b ∈ centralizer (pCoreOf 2 H : Set G) :=
      mem_centralizer_iff.mpr fun q hq => (hbQc q hq).symm
    exact hb1 (P614J.eq_one_of_isPGroup_two (pCoreOf_isPGroup 2 H)
      (hS.charTwo H hH2 ⟨hbH, hbC⟩) hb3)
  set N : Subgroup G := normalizer (V : Set G) with hNdef
  have hV2 : IsPGroup 2 V := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hN2 : IsTwoLocal N := ⟨V, hVne, hV2, rfl⟩
  have hHN : H ≤ N :=
    (le_inf hHQ (hK.normal.trans (P614J.normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  have hBN : zpowers x ⊔ zpowers z ≤ N := hBH.trans hHN
  have hNM : ¬ N ≤ M := fun h => hK.not_le (hK.le.trans (hHN.trans h))
  obtain ⟨⟨hSHM, hS2, hBS⟩, -⟩ := hopt.ext.pair.isMax
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  have hTM : T ≤ M := hT.1.1
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : zpowers x ⊔ zpowers z ≤ normalizer (T : Set G) := hT.1.2.2
  have hNT : N ⊓ T ≤ S := by
    by_contra hle
    have hSNT : S ≤ N ⊓ T := le_inf ((hSHM.trans inf_le_left).trans hHN) hST
    have hlt : S < N ⊓ T := lt_of_le_of_ne hSNT fun h => hle h.symm.le
    exact P614J.false_of_card_lt hopt.ext hN2 hBN hNM
      ⟨inf_le_inf_left N hTM, hT2.to_le inf_le_right,
        (le_inf (hBN.trans le_normalizer) hBT).trans inf_normalizer_le_normalizer_inf⟩
      (Subgroup.card_lt_of_lt hlt)
  set T₁ : Subgroup G := T ⊓ centralizer (zpowers z : Set G) with hT₁def
  set T₀ : Subgroup G := pCoreOf 2 M ⊓ centralizer (T₁ : Set G) with hT₀def
  have hOT : pCoreOf 2 M ≤ T := pCoreOf_le_of_isMaxTwoInvariantIn hBM hT
  have hVT₁ : V ≤ T₁ :=
    le_inf (inf_le_left.trans (hopt.core_le.trans hST))
      (inf_le_right.trans (Subgroup.centralizer_le hK.mem))
  have hT₀N : T₀ ≤ N := fun t ht =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hVT₁ ht.2)
  have hT₀S : T₀ ≤ S := (le_inf hT₀N (inf_le_left.trans hOT)).trans hNT
  have hidx : (centralizer (zpowers z : Set G)).relIndex T₀ ≤ 16 :=
    (Subgroup.relIndex_le_of_le_right hT₀S Subgroup.index_ne_zero_of_finite).trans
      h620iii.sylow
  have hzT₁ : ∀ t ∈ T₁, z * t = t * z := fun t ht =>
    P614J.mem_centralizer_zpowers_iff.mp ht.2
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hcharM : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hS.charTwo M hsit.isCoreMaxLocal.1.1
  have hzT₀ := P614J.exists_not_commute_of_axb hT₁2 (inf_le_left.trans hTM) hzT₁ hzM hz1 hz3
    hcharM
  obtain ⟨g, hgM, hP₁T, hBP₁⟩ :=
    P614J.exists_conj_le_normalizer_of_le hS hsit h618.alpha hx hz hT
  set P₁ : Subgroup G := (P : Subgroup G).map (MulAut.conj g).toMonoidHom with hP₁def
  have hP₁3 : IsPGroup 3 P₁ := P.isPGroup'.map _
  have hP₁M : P₁ ≤ M := by
    rintro _ ⟨p, hp, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hPM hp)) (M.inv_mem hgM)
  have hP₁27 : 27 ≤ Nat.card P₁ := by
    obtain ⟨E, hEP, -, hEc⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
    rw [hP3] at hEc
    have h1 : Nat.card P₁ = Nat.card (P : Subgroup G) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [h1, show (27 : ℕ) = 3 ^ 3 by norm_num, ← hEc]
    exact Subgroup.card_le_of_le hEP
  set z₁ : G := g * z * g⁻¹ with hz₁def
  have hz₁c : z₁ ∈ centralizer (P₁ : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    have hpz : p * z = z * p := mem_centralizer_iff.mp hz.centralizes p hp
    show g * p * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * p * g⁻¹)
    calc g * p * g⁻¹ * (g * z * g⁻¹) = g * (p * z) * g⁻¹ := by group
      _ = g * (z * p) * g⁻¹ := by rw [hpz]
      _ = g * z * g⁻¹ * (g * p * g⁻¹) := by group
  have hz₁3 : z₁ ^ 3 = 1 := by rw [hz₁def, conj_pow, hz3, mul_one, mul_inv_cancel]
  have hz₁B : z₁ ∈ zpowers x ⊔ zpowers z :=
    hpl.mem_of_mem_centralizer z₁ (Subgroup.centralizer_le hBP₁ hz₁c) hz₁3
  have hz₁Z : z₁ ∈ zpowers z := mem_zpowers_of_conj_mem_plane hsetup hz₁B
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [← hz₁def, h]; group
  have hzz₁ : zpowers z₁ = zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz₁Z)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hz3 hz1,
      orderOf_eq_prime hz₁3 hz₁1]
  have hzc : z ∈ centralizer (P₁ : Set G) :=
    zpowers_le.mpr hz₁c (by rw [hzz₁]; exact mem_zpowers z)
  have hzP₁ : z ∈ P₁ := hBP₁ (mem_sup_right (mem_zpowers z))
  have hcen : ∀ w ∈ P₁, w ∈ centralizer (P₁ : Set G) → w ^ 3 = 1 → w ∈ zpowers z := by
    rintro _ ⟨p, hp, rfl⟩ hwc hw3
    have hpc : p ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have h1 : g * q * g⁻¹ * (g * p * g⁻¹) = g * p * g⁻¹ * (g * q * g⁻¹) :=
        mem_centralizer_iff.mp hwc (g * q * g⁻¹) ⟨q, hq, rfl⟩
      calc q * p = g⁻¹ * (g * q * g⁻¹ * (g * p * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * p * g⁻¹ * (g * q * g⁻¹)) * g := by rw [h1]
        _ = p * q := by group
    have hp3 : p ^ 3 = 1 := by
      have h1 : (g * p * g⁻¹) ^ 3 = 1 := hw3
      rw [conj_pow] at h1
      calc p ^ 3 = g⁻¹ * (g * p ^ 3 * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hpl.center p hp hpc hp3)
    rw [← hzz₁]
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    show (g * z * g⁻¹) ^ k = g * p * g⁻¹
    rw [conj_zpow, hk]
  have hP₁cz : P₁ ≤ centralizer (zpowers z : Set G) := fun y hy =>
    P614J.mem_centralizer_zpowers_iff.mpr (mem_centralizer_iff.mp hzc y hy).symm
  have hP₁T₁ : P₁ ≤ normalizer (T₁ : Set G) :=
    (le_inf hP₁T (hP₁cz.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hP₁T₀ : P₁ ≤ normalizer (T₀ : Set G) :=
    (le_inf (hP₁M.trans (localGroup_le_normalizer_pCoreOf 2 M))
      (hP₁T₁.trans (P614J.normalizer_le_normalizer_centralizer T₁))).trans
      inf_normalizer_le_normalizer_inf
  have hT₀2 : IsPGroup 2 T₀ := (pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hlt := P614J.lt_relIndex_centralizer hT₀2 hP₁3 hP₁27 hP₁T₀ hzP₁ hzc hz3 hcen hzT₀
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
