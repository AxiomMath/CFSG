module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Unipotent
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankFourTheoremC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem u3c_commutator_double_eq_self (P K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let : Subgroup.Normalizes P K := ⟨hPK⟩
  let : MulDistribMulAction (↥P) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup (↥K) := commutatorAction (A := ↥P) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := ↥P) (G := ↥K) = C :=
    commutatorAction₂_eq_commutatorAction_of_coprime hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype ≤ ⁅⁅K, P⁆, P⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥P, ∃ k : ↥K, k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype =
          (Subgroup.closure S).map K.subtype := by
            rfl
      _ = Subgroup.closure (K.subtype '' S) := by
            simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
            refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
            rintro _ ⟨y, hy, rfl⟩
            rcases hy with ⟨a, k, hkC, rfl⟩
            have hkX : (k : G) ∈ ⁅K, P⁆ := by
              rw [← hCmap]
              exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
            have hgen : ⁅((k : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
              Subgroup.commutator_mem_commutator (H₁ := ⁅K, P⁆) (H₂ := P)
                (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
            simpa [commutatorElement_def,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc] using hgen
  apply le_antisymm hXle
  intro x hx
  have hx₂ : x ∈ (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype := by
    rw [hC2eq, hCmap]
    exact hx
  exact hcomm₂_le hx₂

omit [Finite G] in
private theorem u3c_mem_normalizer_commutator {A D : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hD : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, D⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hD ⊢
  rw [Subgroup.map_commutator, hA, hD]

private theorem u3c_exists_mul_of_sup_eq {T Z S : Subgroup G}
    (hcomm : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hsup : T ⊔ Z = S) :
    ∀ s ∈ S, ∃ t ∈ T, ∃ z ∈ Z, s = t * z := by
  have hrange := MonoidHom.noncommCoprod_range T.subtype Z.subtype
    (fun a b => (hcomm b b.2 a a.2).symm)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  intro s hs
  rw [← hsup, ← hrange] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

private theorem u3c_commutator_le_O (hc : U3Config G p P M x J) {D : Subgroup G}
    (hDC : D ≤ Subgroup.centralizer ({x} : Set G)) (hDp : ¬ p ∣ Nat.card D)
    {t : G} (ht : t ∈ u3ZT P x J) (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    ⁅D, Subgroup.zpowers t⁆ ≤ rankThreePrimeCore p J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := u3_T_structure hc
  obtain ⟨-, -, -, -, -, -, hZTJ⟩ := u3U0_facts hc
  have htT : t ∈ u3T P x J := ht.1
  have htJ : t ∈ J := hZTJ ht
  have hCJ : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  by_cases ht1 : t = 1
  · rw [ht1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    exact bot_le
  have htp : t ^ p = 1 := hTexp t htT
  have hto : orderOf t = p := orderOf_eq_prime htp ht1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.u3
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) := glbPrimeCore_coprime p J
  have hu1 : ψ ⟨t, htJ⟩ ≠ 1 := by
    intro h
    have hmem : (⟨t, htJ⟩ : J) ∈ ψ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have hk : orderOf (⟨t, hmem⟩ : rankThreePrimeCore p J) ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using htp))
    have hk' : orderOf (⟨t, hmem⟩ : rankThreePrimeCore p J) ∣ Nat.card (rankThreePrimeCore p J) :=
      orderOf_dvd_natCard _
    have h1 : orderOf (⟨t, hmem⟩ : rankThreePrimeCore p J) = 1 :=
      (Nat.Coprime.coprime_dvd_left hk' hOcop.symm).eq_one_of_dvd hk
    apply ht1
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  have hu_pow : ψ ⟨t, htJ⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨t, htJ⟩ : J) ^ p = 1 := Subtype.ext (by simpa using htp)
    rw [this, map_one]
  have hu_ord : orderOf (ψ ⟨t, htJ⟩) = p := orderOf_eq_prime hu_pow hu1
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = ⁅D, Subgroup.zpowers t⁆ := ⟨_, rfl⟩
  have hWD : W ≤ D := by
    rw [hW, Subgroup.commutator_le]
    intro d hd g hg
    have hgN : g ∈ Subgroup.normalizer (D : Set G) := (Subgroup.zpowers_le.mpr htD) hg
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN d⁻¹).mp (D.inv_mem hd)
    have h2 : d * g * d⁻¹ * g⁻¹ = d * (g * d⁻¹ * g⁻¹) := by group
    change d * g * d⁻¹ * g⁻¹ ∈ D
    rw [h2]
    exact D.mul_mem hd h1
  have hWJ : W ≤ J := by
    rw [hW, Subgroup.commutator_le]
    intro d hd g hg
    have hgJ : g ∈ J := (Subgroup.zpowers_le.mpr htJ) hg
    have h1 : d * g * d⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCJ (hDC hd)) g).mp hgJ
    change d * g * d⁻¹ * g⁻¹ ∈ J
    exact J.mul_mem h1 (J.inv_mem hgJ)
  have hWp : ¬ p ∣ Nat.card W := fun h => hDp (h.trans (Subgroup.card_dvd_of_le hWD))
  have hWn : t ∈ Subgroup.normalizer (W : Set G) := by
    rw [hW]
    exact u3c_mem_normalizer_commutator htD (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
  have hVp : ¬ p ∣ Nat.card ((W.subgroupOf J).map ψ) := by
    intro h
    apply hWp
    have h1 := h.trans (Subgroup.card_map_dvd (H := W.subgroupOf J) ψ)
    have h2 : Nat.card (W.subgroupOf J) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWJ).toEquiv
    rwa [h2] at h1
  have hNorm : ψ ⟨t, htJ⟩ ∈ Subgroup.normalizer (((W.subgroupOf J).map ψ : Subgroup Q) : Set Q) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨wJ, hwJ, rfl⟩ := hn
    refine ⟨⟨t, htJ⟩ * wJ * ⟨t, htJ⟩⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show t * (wJ : G) * t⁻¹ ∈ W
    exact (Subgroup.mem_normalizer_iff.mp hWn (wJ : G)).mp hwJ
  have hcomm := kFactU3UnipotentCentralizing p hc.five Q hQ (ψ ⟨t, htJ⟩) hu_ord
    ((W.subgroupOf J).map ψ) hVp hNorm
  have hWO : ⁅W, Subgroup.zpowers t⁆ ≤ rankThreePrimeCore p J := by
    rw [Subgroup.commutator_le]
    intro w hw g hg
    have hgJ : g ∈ J := (Subgroup.zpowers_le.mpr htJ) hg
    have hwJ : w ∈ J := hWJ hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgeq : (⟨t ^ k, hgJ⟩ : J) = ⟨t, htJ⟩ ^ k := Subtype.ext (by simp)
    have h1 : ψ ⟨w, hwJ⟩ ∈ (W.subgroupOf J).map ψ := ⟨⟨w, hwJ⟩, hw, rfl⟩
    have h2 := hcomm (ψ ⟨w, hwJ⟩) h1
    have h3 : ψ ⟨t ^ k, hgJ⟩ * ψ ⟨w, hwJ⟩ = ψ ⟨w, hwJ⟩ * ψ ⟨t ^ k, hgJ⟩ := by
      rw [hgeq, map_zpow]
      exact (Commute.zpow_left (show Commute (ψ ⟨t, htJ⟩) (ψ ⟨w, hwJ⟩) from h2) k).eq
    have h4 : ψ (⟨w, hwJ⟩ * ⟨t ^ k, hgJ⟩ * ⟨w, hwJ⟩⁻¹ * ⟨t ^ k, hgJ⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h3]
      group
    have h5 : (⟨w, hwJ⟩ * ⟨t ^ k, hgJ⟩ * ⟨w, hwJ⟩⁻¹ * ⟨t ^ k, hgJ⟩⁻¹ : J) ∈ ψ.ker := h4
    rw [hker, Subgroup.mem_subgroupOf] at h5
    exact h5
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card D) := by
    rw [Nat.card_zpowers, hto]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hDp
  have hdbl : ⁅⁅D, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ = ⁅D, Subgroup.zpowers t⁆ :=
    u3c_commutator_double_eq_self (Subgroup.zpowers t) D (Subgroup.zpowers_le.mpr htD) hcop
  calc ⁅D, Subgroup.zpowers t⁆ = ⁅⁅D, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ := hdbl.symm
    _ = ⁅W, Subgroup.zpowers t⁆ := by rw [hW]
    _ ≤ rankThreePrimeCore p J := hWO

private theorem u3c_le_M (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J) {D : Subgroup G} (hDC : D ≤ Subgroup.centralizer ({x} : Set G))
    (hcomm : ∀ t ∈ u3ZT P x J, ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ rankThreePrimeCore p J) : D ≤ M := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := u3U0_facts hc
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  have hCJ : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  have hOM : rankThreePrimeCore p J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hJC hCJ).1
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) := glbPrimeCore_coprime p J
  have hOnorm : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((rankThreePrimeCore p J : Subgroup G) : Set G) := by
    intro g hg
    have hgJ : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJ hg)
    have h1 := glbPrimeCore_map_automorphism p J (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hU0M : u3U0 P x J ≤ M := hU0S.trans (hSP.trans hPM)
  have hU0p : IsPGroup p (u3U0 P x J) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _ hU0el
  have hNU0 : Subgroup.normalizer ((u3U0 P x J : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hU0p hU0M
      (le_pRank_of_elemAbelian_card le_rfl hU0el hU0card)
  have hUnorm : u3U0 P x J ≤ Subgroup.normalizer ((rankThreePrimeCore p J : Subgroup G) : Set G) :=
    hU0S.trans (hSC.trans hOnorm)
  have hdisj : Disjoint (rankThreePrimeCore p J) (u3U0 P x J) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU0p
    rw [hk]
    exact Nat.Coprime.pow_right k hOcop.symm
  have hHcard : Nat.card (rankThreePrimeCore p J ⊔ u3U0 P x J : Subgroup G) =
      Nat.card (rankThreePrimeCore p J) * Nat.card (u3U0 P x J) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hUnorm hdisj
  have hSylH : CFSG.ABGLocalTools.IsSylowOf p (u3U0 P x J) (rankThreePrimeCore p J ⊔ u3U0 P x J) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_right ?_
    rw [hHcard, hU0card]
    have hO0 : Nat.card (rankThreePrimeCore p J) ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card (rankThreePrimeCore p J)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hOcop)
    have h2 : (p ^ 2).factorization p = 2 := by
      rw [hp.factorization_pow]
      simp
    rw [Nat.factorization_mul hO0 (pow_ne_zero 2 hp.ne_zero), Finsupp.add_apply, h1, h2]
  have hHM : rankThreePrimeCore p J ⊔ u3U0 P x J ≤ M := sup_le hOM hU0M
  have hZTU0 : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hxU0' : Subgroup.zpowers x ≤ u3U0 P x J := le_sup_right
  have hcommx : ∀ z ∈ Subgroup.zpowers x, ∀ t ∈ u3ZT P x J, z * t = t * z := by
    intro z hz t ht
    have hzS : z ∈ u3S P x := (Subgroup.zpowers_le.mpr (hU0S hxU0)) hz
    exact hU0cent z hzS t (hZTU0 ht)
  intro d hd
  have hdC : d ∈ Subgroup.centralizer ({x} : Set G) := hDC hd
  have hEH : (u3U0 P x J).map (MulAut.conj d).toMonoidHom ≤ rankThreePrimeCore p J ⊔ u3U0 P x J := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, ht, z, hz, rfl⟩ := u3c_exists_mul_of_sup_eq hcommx
      (rfl : u3ZT P x J ⊔ Subgroup.zpowers x = u3U0 P x J) u hu
    have hxd : x ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hdC).symm
    have hzd : z * d = d * z :=
      Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hxd) hz)
    have hdzd : d * z * d⁻¹ = z := by rw [← hzd]; group
    have hmem : d * (t * z) * d⁻¹ = (d * t * d⁻¹ * t⁻¹) * (t * z) := by
      calc d * (t * z) * d⁻¹ = (d * t * d⁻¹) * (d * z * d⁻¹) := by group
        _ = (d * t * d⁻¹ * t⁻¹) * (t * z) := by rw [hdzd]; group
    show d * (t * z) * d⁻¹ ∈ _
    rw [hmem]
    exact Subgroup.mul_mem_sup (hcomm t ht d hd)
      (Subgroup.mul_mem _ (hZTU0 ht) (hxU0' hz))
  obtain ⟨h, hhH, hhE⟩ := exists_conj_le_of_isSylowOf hSylH hEH (hU0p.map _)
  have hcardE : Nat.card (((u3U0 P x J).map (MulAut.conj d).toMonoidHom).map
      (MulAut.conj h).toMonoidHom) = Nat.card (u3U0 P x J) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
      Subgroup.card_map_of_injective (MulAut.conj d).injective]
  have hEq : ((u3U0 P x J).map (MulAut.conj d).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      u3U0 P x J := Subgroup.eq_of_le_of_card_ge hhE (le_of_eq hcardE.symm)
  have hcomp : (MulAut.conj (h * d)).toMonoidHom =
      (MulAut.conj h).toMonoidHom.comp (MulAut.conj d).toMonoidHom :=
    MonoidHom.ext fun _ => by simp [mul_assoc]
  have hmapeq : (u3U0 P x J).map (MulAut.conj (h * d)).toMonoidHom = u3U0 P x J := by
    rw [hcomp, ← Subgroup.map_map]
    exact hEq
  have hhdN : h * d ∈ Subgroup.normalizer ((u3U0 P x J : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapeq
  have hhM : h ∈ M := hHM hhH
  have hhdM : h * d ∈ M := hNU0 hhdN
  have hdeq : d = h⁻¹ * (h * d) := by group
  rw [hdeq]
  exact M.mul_mem (M.inv_mem hhM) hhdM

theorem u3_cor46 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J)
    (hL42 : ∀ a ∈ u3U0 P x J, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M) :
    ∀ F : Subgroup G, ¬ p ∣ Nat.card F → u3U0 P x J ≤ Subgroup.normalizer (F : Set G) → F ≤ M := by
  intro F hFp hFN
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hU0el, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := u3U0_facts hc
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hZTU0 : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hxU0' : Subgroup.zpowers x ≤ u3U0 P x J := le_sup_right
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hpow : ∀ member : u3U0 P x J, member ^ p = 1 := fun m =>
    Subtype.ext (by simpa using hU0el.2 (m : G) m.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp (u3U0 P x J) F hpow hU0card hFp hFN
  refine hgen.le.trans (iSup_le fun a => iSup_le fun ha1 => ?_)
  by_cases hax : (a : G) ∈ Subgroup.zpowers x
  ·
    have hne : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hao : orderOf (a : G) = p := orderOf_eq_prime (hU0el.2 a a.2) hne
    have hzz : Subgroup.zpowers (a : G) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hax) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hao, hxo])
    have hxa : x ∈ Subgroup.zpowers (a : G) := hzz ▸ Subgroup.mem_zpowers x
    have hcent : F ⊓ Subgroup.centralizer ({(a : G)} : Set G) ≤
        F ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine inf_le_inf_left F ?_
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxa
      rw [← hk]
      exact (Commute.zpow_right (show Commute g (a : G) from hg) k).eq
    refine hcent.trans ?_
    have hDC : F ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
      inf_le_right
    have hDp : ¬ p ∣ Nat.card (F ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
      fun h => hFp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    refine u3c_le_M hS hD1 hU0 hc hDC (fun t ht d hd => ?_)
    have htU0 : t ∈ u3U0 P x J := hZTU0 ht
    have htC : t ∈ Subgroup.centralizer ({x} : Set G) := hSC (hU0S htU0)
    have htD : t ∈ Subgroup.normalizer ((F ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hFN htU0) n).mp hn.1, ?_⟩
      show t * n * t⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hct : Commute t x := Subgroup.mem_centralizer_singleton_iff.mp htC
      have hcn : Commute n x := Subgroup.mem_centralizer_singleton_iff.mp hn.2
      exact ((Commute.mul_left (Commute.mul_left hct hcn) (Commute.inv_left hct))).eq
    have h1 := u3c_commutator_le_O hc hDC hDp ht htD
    have hdt : d * t * d⁻¹ * t⁻¹ ∈ ⁅F ⊓ Subgroup.centralizer ({x} : Set G), Subgroup.zpowers t⁆ := by
      have := Subgroup.commutator_mem_commutator hd (Subgroup.mem_zpowers t)
      exact this
    exact h1 hdt
  · exact inf_le_right.trans (hL42 a a.2 hax)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
