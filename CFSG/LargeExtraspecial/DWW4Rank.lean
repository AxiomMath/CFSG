module

public import CFSG.LargeExtraspecial.DWTransGL
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGElevenGeneratorPrimeThree
import CFSG.GF2Type.Entry
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
import CFSG.CGT.PushingUpLit.SolK.GenFourA8
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2ExtraspecialWidthFour
public import CFSG.GH74.SectionalRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4Rank

open Subgroup Module CFSG.LargeExtraspecial.Bridge CFSG.Open CFSG.GH74
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators
  pGeneratorRank_generators)
open CFSG.LocalAnalysis.GorensteinLyons
open scoped commutatorElement

section Embedding

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

theorem card_Mbar_dvd_of_maxEA [CFSG.IsElementaryAbelian 2 A] (hw : S.width = 4)
    (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) : Nat.card S.Mbar ∣ 20160 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_mulEquiv_GL (hA.finrank_clSub.trans hw)
  have h := Subgroup.card_dvd_of_injective (resAt S A hM) (hA.resAt_injective hM)
  rwa [Nat.card_congr e.toEquiv, CFSG.GH74.Exceptional.card_GL_four_two] at h

theorem sectionalTwoRankLE_Mbar [CFSG.IsElementaryAbelian 2 A] (hw : S.width = 4)
    (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) : SectionalTwoRankLE S.Mbar 4 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_mulEquiv_GL (hA.finrank_clSub.trans hw)
  exact SectionalTwoRankLE.of_injective (resAt S A hM) (hA.resAt_injective hM)
    (SectionalTwoRankLE.of_mulEquiv e.symm
      CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_GL_four_two)

theorem card_dvd_card_Mbar_of_odd {B : Subgroup G} (hBM : B ≤ S.M) (hodd : Odd (Nat.card B)) :
    Nat.card B ∣ Nat.card S.Mbar := by
  let f : B →* S.Mbar := S.ρ.rangeRestrict.comp (Subgroup.inclusion hBM)
  refine Subgroup.card_dvd_of_injective f ((injective_iff_map_eq_one f).mpr fun b hb => ?_)
  have hb' : S.ρ ⟨b, hBM b.2⟩ = 1 := congrArg Subtype.val hb
  have hq : (⟨b, hBM b.2⟩ : S.M) ∈ S.Q := S.mem_Q_of_ρ_eq_one hb'
  obtain ⟨k, hk⟩ := S.extraspecial.1 ⟨_, hq⟩
  have h2 : (b : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : S.Q => ((x : S.M) : G)) hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card B) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 := pow_gcd_eq_one.mpr ⟨(Subtype.ext h2 : b ^ 2 ^ k = 1), pow_card_eq_one' (G := B)⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem false_of_maxEA_of_dvd [CFSG.IsElementaryAbelian 2 A] (hw : S.width = 4) (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {B : Subgroup G} (hBM : B ≤ S.M)
    (hodd : Odd (Nat.card B)) (h27 : 27 ∣ Nat.card B) : False := by
  have h := (h27.trans (card_dvd_card_Mbar_of_odd hBM hodd)).trans
    (card_Mbar_dvd_of_maxEA hw hA hM)
  omega

theorem false_of_maxEA_of_three_rank [CFSG.IsElementaryAbelian 2 A] (hw : S.width = 4)
    (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) {B : Subgroup G} (hBM : B ≤ S.M)
    {r : ℕ} (hr : 3 ≤ r) (hB : Nat.card B = 3 ^ r) : False := by
  refine false_of_maxEA_of_dvd hw hA hM hBM ?_ ?_
  · rw [hB]
    exact Odd.pow (by decide)
  · rw [hB]
    exact (pow_dvd_pow 3 hr : 3 ^ 3 ∣ 3 ^ r)

end Embedding

theorem two_pow_succ_pGeneratorRank_le_card {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (hna : ∃ a b : X, a * b ≠ b * a) : 2 ^ (pGeneratorRank 2 X + 1) ≤ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 X) := ⟨hX⟩
  obtain ⟨a, b, hab⟩ := hna
  have hΦ : frattini X ≠ ⊥ := by
    intro h
    have h1 : ⁅a, b⁆ ∈ frattini X :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2)
        ((commutator_def X) ▸ commutator_mem_commutator (mem_top a) (mem_top b))
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  have h2 : 1 < Nat.card (frattini X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hΦ
  have h3 := (frattini X).card_eq_card_quotient_mul_card_subgroup
  rw [SymplecticSixLayer.card_frattini_quotient_eq_pow Nat.prime_two hX] at h3
  rw [h3, pow_succ]
  exact Nat.mul_le_mul_left _ h2

section Generators

variable {G : Type} [Group G] [Finite G] (S : Setting G)

noncomputable abbrev toMbar (P : Subgroup S.M) : P →* S.Mbar :=
  S.ρ.rangeRestrict.comp P.subtype

noncomputable abbrev kerEmb (P : Subgroup S.M) : (toMbar S P).ker →* G :=
  S.M.subtype.comp (P.subtype.comp (toMbar S P).ker.subtype)

variable {S}

theorem mem_ker_toMbar_iff {P : Subgroup S.M} (x : P) :
    x ∈ (toMbar S P).ker ↔ ((x : S.M) : G) ∈ S.QG := by
  rw [MonoidHom.mem_ker, ← S.ρ_eq_one_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem kerEmb_injective (P : Subgroup S.M) : Function.Injective (kerEmb S P) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

theorem kerEmb_mem (P : Subgroup S.M) (x : (toMbar S P).ker) : kerEmb S P x ∈ S.QG :=
  (mem_ker_toMbar_iff x.1).mp x.2

theorem kerEmb_range_le (P : Subgroup S.M) : (kerEmb S P).range ≤ S.QG := by
  rintro _ ⟨x, rfl⟩
  exact kerEmb_mem P x

theorem card_ker_toMbar (P : Subgroup S.M) :
    Nat.card (toMbar S P).ker = Nat.card (kerEmb S P).range :=
  Nat.card_congr (Equiv.ofInjective _ (kerEmb_injective P))

theorem card_QG_eq_pow (hw : S.width = 4) : Nat.card S.QG = 2 ^ 9 := by
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]

theorem card_ker_toMbar_dvd (hw : S.width = 4) (P : Subgroup S.M) :
    Nat.card (toMbar S P).ker ∣ 2 ^ 9 := by
  rw [card_ker_toMbar, ← card_QG_eq_pow hw]
  exact Subgroup.card_dvd_of_le (kerEmb_range_le P)

theorem card_ker_toMbar_le_of_comm (hw : S.width = 4) (P : Subgroup S.M)
    (hcomm : ∀ x y : (toMbar S P).ker, x * y = y * x) : Nat.card (toMbar S P).ker ≤ 2 ^ 5 := by
  have h1 : ∀ x ∈ (kerEmb S P).range, ∀ y ∈ (kerEmb S P).range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a b]
  have h2 := S.card_le_of_commute (kerEmb_range_le P) h1
  rwa [← card_ker_toMbar, hw] at h2

theorem pGeneratorRank_quotient_toMbar_le (hS4 : SectionalTwoRankLE S.Mbar 4)
    {P : Subgroup S.M} (hP : IsPGroup 2 P) : pGeneratorRank 2 (P ⧸ (toMbar S P).ker) ≤ 4 := by
  have hR : IsPGroup 2 (toMbar S P).range :=
    hP.of_surjective (toMbar S P).rangeRestrict (toMbar S P).rangeRestrict_surjective
  have : Finite (toMbar S P).range :=
    Finite.of_surjective (toMbar S P).rangeRestrict (toMbar S P).rangeRestrict_surjective
  obtain ⟨s, hs, hcl⟩ :=
    (SectionalTwoRankLE.subgroup (toMbar S P).range hS4) ⊤ (hR.to_subgroup ⊤)
  rw [SymplecticSixLayer.pGeneratorRank_congr
    (QuotientGroup.quotientKerEquivRange (toMbar S P))]
  exact (pGeneratorRank_le_generators Nat.prime_two hR s hcl).trans hs

theorem pGeneratorRank_ker_toMbar_le (hw : S.width = 4) {P : Subgroup S.M} (hP : IsPGroup 2 P) :
    pGeneratorRank 2 (toMbar S P).ker ≤ 8 ∧
      (Nat.card (toMbar S P).ker ≤ 2 ^ 8 → pGeneratorRank 2 (toMbar S P).ker ≤ 7) := by
  have hN2 : IsPGroup 2 (toMbar S P).ker := hP.to_subgroup _
  have hpow := SymplecticSixLayer.pow_pGeneratorRank_le_card Nat.prime_two hN2
  have h9 : Nat.card (toMbar S P).ker ≤ 2 ^ 9 :=
    Nat.le_of_dvd (by positivity) (card_ker_toMbar_dvd hw P)
  by_cases hcomm : ∀ x y : (toMbar S P).ker, x * y = y * x
  · have h3 : pGeneratorRank 2 (toMbar S P).ker ≤ 5 :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp
        (hpow.trans (card_ker_toMbar_le_of_comm hw P hcomm))
    exact ⟨by omega, fun _ => by omega⟩
  · push Not at hcomm
    obtain ⟨x, y, hxy⟩ := hcomm
    have h2 := two_pow_succ_pGeneratorRank_le_card hN2 ⟨x, y, hxy⟩
    refine ⟨?_, fun h8 => ?_⟩
    · have := (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2.trans h9)
      omega
    · have := (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2.trans h8)
      omega

theorem commutator_ne_one_ne_z {g x : G} (hx : x ∈ S.QG)
    (h : S.cl (g * x * g⁻¹) ≠ S.cl x) : ⁅x, g⁆ ≠ 1 ∧ ⁅x, g⁆ ≠ S.z := by
  constructor
  · intro h1
    apply h
    have h2 : x * g = g * x := commutatorElement_eq_one_iff_mul_comm.mp h1
    have h3 : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h2]
        _ = x := by group
    rw [h3]
  · intro h1
    apply h
    have h2 : g * x * g⁻¹ = S.z * x := by
      calc g * x * g⁻¹ = (x * g * x⁻¹ * g⁻¹)⁻¹ * x := by group
        _ = S.z⁻¹ * x := by rw [← commutatorElement_def, h1]
        _ = S.z * x := by rw [S.z_inv]
    rw [h2, S.cl_mul S.z_mem_QG hx, S.cl_z, zero_add]

theorem exists_two_commutators (hw : S.width = 4) {P : Subgroup S.M}
    (hk : Nat.card (toMbar S P).ker = 2 ^ 9) {m : P} (hm : m ∉ (toMbar S P).ker) :
    ∃ t u : P, t ∈ ⁅(toMbar S P).ker, (⊤ : Subgroup P)⁆ ∧
      u ∈ ⁅(toMbar S P).ker, (⊤ : Subgroup P)⁆ ∧ t ≠ 1 ∧ u ≠ 1 ∧ t ≠ u := by
  have hrange_eq : (kerEmb S P).range = S.QG := by
    refine Subgroup.eq_of_le_of_card_ge (kerEmb_range_le P) ?_
    rw [card_QG_eq_pow hw, ← card_ker_toMbar, hk]
  have hlift : ∀ x ∈ S.QG, ∃ n : (toMbar S P).ker, kerEmb S P n = x := fun x hx => by
    have : x ∈ (kerEmb S P).range := hrange_eq ▸ hx
    exact this
  obtain ⟨x, y, hxy⟩ : ∃ x y : (toMbar S P).ker, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    have := card_ker_toMbar_le_of_comm hw P hcomm
    rw [hk] at this
    norm_num at this
  have hcomm_z : ⁅kerEmb S P x, kerEmb S P y⁆ = S.z := by
    rcases S.commutator_eq_one_or_z (kerEmb_mem P x) (kerEmb_mem P y) with h | h
    · refine absurd (kerEmb_injective P ?_) hxy
      rw [map_mul, map_mul]
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    · exact h
  have hmQ : ((m : S.M) : G) ∉ S.QG := fun h => hm ((mem_ker_toMbar_iff m).mpr h)
  have hρm : S.ρ (m : S.M) ≠ 1 := fun h => hmQ ((S.ρ_eq_one_iff _).mp h)
  obtain ⟨v, hv⟩ : ∃ v : S.Qt, ((S.ρ (m : S.M) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
    by_contra h
    push Not at h
    exact hρm (Subtype.ext (LinearEquiv.ext h))
  obtain ⟨x₀, hx₀Q, rfl⟩ := S.exists_cl v
  rw [S.ρ_cl _ hx₀Q] at hv
  obtain ⟨n, hn⟩ := hlift x₀ hx₀Q
  obtain ⟨hu1, huz⟩ := commutator_ne_one_ne_z hx₀Q hv
  let e : P →* G := S.M.subtype.comp P.subtype
  have het : e ⁅(x : P), (y : P)⁆ = S.z := by
    rw [map_commutatorElement]
    exact hcomm_z
  have heu : e ⁅(n : P), m⁆ = ⁅x₀, ((m : S.M) : G)⁆ := by
    rw [map_commutatorElement]
    exact congrArg (fun a => ⁅a, ((m : S.M) : G)⁆) hn
  refine ⟨⁅(x : P), (y : P)⁆, ⁅(n : P), m⁆, commutator_mem_commutator x.2 (mem_top _),
    commutator_mem_commutator n.2 (mem_top _), fun h => S.z_ne_one ?_, fun h => hu1 ?_,
    fun h => huz ?_⟩
  · rw [← het, h, map_one]
  · rw [← heu, h, map_one]
  · rw [← heu, ← h, het]

theorem pGeneratorRank_le_eleven_of_full_ker (hw : S.width = 4)
    (hS4 : SectionalTwoRankLE S.Mbar 4) {P : Subgroup S.M} (hP : IsPGroup 2 P)
    (hk : Nat.card (toMbar S P).ker = 2 ^ 9) (htop : (toMbar S P).ker ≠ ⊤) :
    pGeneratorRank 2 P ≤ 11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m : P, m ∉ (toMbar S P).ker := by
    by_contra h
    push Not at h
    exact htop (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨t, u, ht, hu, ht1, hu1, htu⟩ := exists_two_commutators hw hk hm
  set N := (toMbar S P).ker with hN
  set D : Subgroup P := (frattini N).map N.subtype ⊔ ⁅N, ⊤⁆ with hD
  have htD : t ∈ D := mem_sup_right ht
  have huD : u ∈ D := mem_sup_right hu
  have hD4 : 4 ≤ Nat.card D := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hP.to_subgroup D)
    rcases j with _ | _ | j
    · exfalso
      have h1 : D = ⊥ := Subgroup.card_eq_one.mp (by simpa using hj)
      exact ht1 (by simpa [h1] using htD)
    · exfalso
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : D)).mp (by simpa using hj)
      exact htu (congrArg Subtype.val
        ((hy ⟨t, htD⟩ (fun h => ht1 (congrArg Subtype.val h))).trans
          (hy ⟨u, huD⟩ (fun h => hu1 (congrArg Subtype.val h))).symm))
    · rw [hj, pow_succ, pow_succ]
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
  obtain ⟨-, -, hDN, -, dP, dQ, dN, hdP, hdQ, hdN, hle, -⟩ :=
    p_group_Frattini_coinvariant_generator_bound hP N hD
  have hdPeq : pGeneratorRank 2 P = dP := by rw [pGeneratorRank, hdP, Nat.log_pow (by norm_num)]
  have hdQeq : pGeneratorRank 2 (P ⧸ N) = dQ := by
    rw [pGeneratorRank, hdQ, Nat.log_pow (by norm_num)]
  have hdN7 : dN ≤ 7 := by
    have h1 := (D.subgroupOf N).card_eq_card_quotient_mul_card_subgroup
    rw [hdN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv, hk] at h1
    have h2 : 2 ^ dN * 4 ≤ 2 ^ 9 := h1 ▸ Nat.mul_le_mul_left _ hD4
    have h3 : 2 ^ (dN + 2) ≤ 2 ^ 9 := by
      rw [pow_add]
      exact h2
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    omega
  have h4 : pGeneratorRank 2 (P ⧸ N) ≤ 4 := pGeneratorRank_quotient_toMbar_le hS4 hP
  omega

theorem pGeneratorRank_le_eleven (hw : S.width = 4) (hS4 : SectionalTwoRankLE S.Mbar 4)
    {P : Subgroup S.M} (hP : IsPGroup 2 P) : pGeneratorRank 2 P ≤ 11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd := SymplecticSixLayer.pGeneratorRank_le_quotient_add Nat.prime_two hP
    (toMbar S P).ker
  have hdQ := pGeneratorRank_quotient_toMbar_le hS4 hP
  have hdN := pGeneratorRank_ker_toMbar_le hw hP
  obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (card_ker_toMbar_dvd hw P)
  by_cases hk8 : k ≤ 8
  · have : Nat.card (toMbar S P).ker ≤ 2 ^ 8 := hk ▸ Nat.pow_le_pow_right (by norm_num) hk8
    have := hdN.2 this
    omega
  have hk9' : k = 9 := by omega
  by_cases htop : (toMbar S P).ker = ⊤
  · have h1 : pGeneratorRank 2 (P ⧸ (toMbar S P).ker) = 0 := by
      have h := SymplecticSixLayer.pGeneratorRank_le_log_card 2 (X := P ⧸ (toMbar S P).ker)
      have hc : Nat.card (P ⧸ (toMbar S P).ker) = 1 := by
        rw [htop]
        exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
      rw [hc, Nat.log_one_right] at h
      omega
    have := hdN.1
    omega
  · exact pGeneratorRank_le_eleven_of_full_ker hw hS4 hP (hk.trans (by rw [hk9'])) htop

theorem exists_generators_le_eleven (hw : S.width = 4) (hS4 : SectionalTwoRankLE S.Mbar 4)
    (P : Subgroup S.M) (hP : IsPGroup 2 P) :
    ∃ T : Finset P, T.card ≤ 11 ∧ Subgroup.closure (T : Set P) = ⊤ := by
  obtain ⟨T, hT, hcard⟩ := pGeneratorRank_generators Nat.prime_two hP
  exact ⟨T, hcard ▸ pGeneratorRank_le_eleven hw hS4 hP, hT⟩

end Generators

section CoreSetting

variable {G : Type} [Group G] [Finite G] {z : G}

theorem timmesfeld_core_hypotheses
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9) :
    timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({z} : Set G))) ∧
      Nat.card (timmesfeldFStar (centralizer ({z} : Set G))) = 2 ^ (1 + 2 * 4) :=
  CFSG.GF2Type.timmesfeld_hypotheses (w := 4) hext (hcard.trans (by norm_num))

@[expose] noncomputable def settingOfCore (z : G) (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9) :
    Setting G :=
  Setting.ofFStar z hz (timmesfeld_core_hypotheses hext hcard).1

@[simp] theorem settingOfCore_z (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9) :
    (settingOfCore z hz hext hcard).z = z := rfl

theorem settingOfCore_width (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9) :
    (settingOfCore z hz hext hcard).width = 4 :=
  width_ofFStar hz _ (timmesfeld_core_hypotheses hext hcard).2

theorem settingOfCore_QG (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9) :
    (settingOfCore z hz hext hcard).QG =
      inSubgroup generalizedFitting (centralizer ({z} : Set G)) := by
  change (timmesfeldFStar (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype =
    (generalizedFitting (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
  rw [generalizedFitting_eq_timmesfeldFStar]

end CoreSetting

section Reducible

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem mem_center_map_QG_iff {x : G} :
    x ∈ (center S.QG).map S.QG.subtype ↔ x = 1 ∨ x = S.z := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    exact S.eq_one_or_z_of_commute hy fun w hw =>
      (congrArg Subtype.val (mem_center_iff.mp hyc ⟨w, hw⟩)).symm
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact ⟨⟨S.z, S.z_mem_QG⟩, mem_center_iff.mpr fun w => Subtype.ext (S.z_comm_QG w.2), rfl⟩

theorem isReducible_of_lt {A : Subgroup G} (hlo : (center S.QG).map S.QG.subtype < A)
    (hhi : A < S.QG) (hnorm : S.M ≤ normalizer (A : Set G)) : S.IsReducible := by
  have hAQ : A ≤ S.QG := hhi.le
  have hzA : S.z ∈ A := hlo.le ((mem_center_map_QG_iff S).mpr (Or.inr rfl))
  refine ⟨S.clSub A, ?_, ?_, ?_⟩
  · obtain ⟨x, hxA, hxn⟩ := (SetLike.lt_iff_le_and_exists.mp hlo).2
    intro hbot
    have hxQ := hAQ hxA
    have h0 : S.cl x = 0 := by
      have := S.cl_mem_clSub hxA hxQ
      rw [hbot] at this
      exact (Submodule.mem_bot _).mp this
    exact hxn ((mem_center_map_QG_iff S).mpr ((S.cl_eq_zero_iff hxQ).mp h0))
  · intro htop
    have h1 := S.clPre_clSub hAQ hzA
    rw [htop, S.clPre_top] at h1
    exact hhi.ne h1.symm
  · intro m v hv
    obtain ⟨x, hxA, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.ρ_cl m hxQ]
    have hmx : (m : G) * x * (m : G)⁻¹ ∈ A := (mem_normalizer_iff.mp (hnorm m.2) x).mp hxA
    exact S.cl_mem_clSub hmx (S.conj_mem_QG m.2 hxQ)

end Reducible

section Conjugate

variable {G : Type*} [Group G] {z : G} (S : Setting G)

theorem exists_conj_of_not_weaklyClosed (hz : S.z = z)
    (hQ : S.QG = inSubgroup generalizedFitting (centralizer ({z} : Set G)))
    (h : ¬ ∀ g : G, g⁻¹ * z * g ∈ inSubgroup generalizedFitting (centralizer ({z} : Set G)) →
      g⁻¹ * z * g = z) :
    ∃ g₀ : G, g₀ * S.z * g₀⁻¹ ∈ S.QG ∧ g₀ * S.z * g₀⁻¹ ≠ S.z := by
  by_contra hcon
  refine h fun g hg => ?_
  by_contra hne
  refine hcon ⟨g⁻¹, ?_, ?_⟩
  · rw [hQ, hz, inv_inv]
    exact hg
  · rw [hz, inv_inv]
    exact hne

end Conjugate

section Rank

theorem four_le_rank_of_eleven_generated {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (he : 4 ≤ CFSG.Assembly.evenRank G)
    (hgen : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ T : Finset G, T.card ≤ 11 ∧ closure (T : Set G) = P) :
    4 ≤ CFSG.Assembly.LargeEvenTwoLocalRank 3 G := by
  have hchar' : CFSG.IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar
  have he' : 4 ≤ CFSG.twoLocalOddRank G := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact he
  exact (eleven_generator_two_subgroups_force_large_odd_local_prime_three hchar' he' hgen).2.2

theorem exists_generators_le_eleven_of_witness {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 4) (hS4 : SectionalTwoRankLE S.Mbar 4)
    (hchar : CFSG.Assembly.IsCharTwoType G) (hmax : CFSG.Assembly.LargeEvenIsMaxTwoLocal S.M)
    (hsym : CFSG.Assembly.LargeEvenSymplecticType (CFSG.Assembly.pCoreOf 2 S.M))
    {B : Subgroup G} (hB : CFSG.Assembly.LargeEvenIsBmax 3 B) (hBM : B ≤ S.M) :
    ∀ P : Subgroup G, IsPGroup 2 P → ∃ T : Finset G, T.card ≤ 11 ∧ closure (T : Set G) = P := by
  have hchar' : CFSG.IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar
  obtain ⟨⟨z', -, -, -, -, -, -, hSyl⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar' (M := S.M) (B := B) hmax hsym hB hBM
      (Q := CFSG.inSubgroup (CFSG.pCore 2) S.M) rfl (r := GLATwoLocalRank 3 G) rfl
  obtain ⟨Sy⟩ := (inferInstance : Nonempty (Sylow 2 S.M))
  have hSyM : CFSG.ABGLocalTools.IsSylowOf 2 ((Sy : Subgroup S.M).map S.M.subtype) S.M :=
    ⟨Sy, rfl⟩
  exact fun P hP => SteinbergBK.two_subgroups_generated_of_sylow_le (map_subtype_le _)
    (hSyl _ hSyM).1 (fun X hX => exists_generators_le_eleven hw hS4 X hX) P hP

theorem four_le_rank_of_maxEA {G : Type} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
    [CFSG.IsElementaryAbelian 2 A] (hw : S.width = 4) (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) (hchar : CFSG.Assembly.IsCharTwoType G)
    (he : 4 ≤ CFSG.Assembly.evenRank G) (hmax : CFSG.Assembly.LargeEvenIsMaxTwoLocal S.M)
    (hsym : CFSG.Assembly.LargeEvenSymplecticType (CFSG.Assembly.pCoreOf 2 S.M))
    {B : Subgroup G} (hB : CFSG.Assembly.LargeEvenIsBmax 3 B) (hBM : B ≤ S.M) :
    4 ≤ CFSG.Assembly.LargeEvenTwoLocalRank 3 G :=
  four_le_rank_of_eleven_generated hchar he
    (exists_generators_le_eleven_of_witness S hw (sectionalTwoRankLE_Mbar hw hA hM) hchar hmax
      hsym hB hBM)

end Rank

@[expose] def TheoremAWidthFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 4 →
    (∃ g₀ : G, g₀ * S.z * g₀⁻¹ ∈ S.QG ∧ g₀ * S.z * g₀⁻¹ ≠ S.z) → S.IsReducible →
      ∃ A : Subgroup G, CFSG.IsElementaryAbelian 2 A ∧ MaxEA S A ∧
        S.M ≤ normalizer (A : Set G)

theorem exists_maxEA_of_core (hThmA : TheoremAWidthFour)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9)
    (hnwc : ¬ ∀ g : G, g⁻¹ * z * g ∈ inSubgroup generalizedFitting (centralizer ({z} : Set G)) →
      g⁻¹ * z * g = z)
    (hred : ∃ A : Subgroup G,
      (center (inSubgroup generalizedFitting (centralizer ({z} : Set G)))).map
        (inSubgroup generalizedFitting (centralizer ({z} : Set G))).subtype < A ∧
      A < inSubgroup generalizedFitting (centralizer ({z} : Set G)) ∧
      centralizer ({z} : Set G) ≤ normalizer (A : Set G)) :
    ∃ (S : Setting G) (A : Subgroup G), S.z = z ∧ S.width = 4 ∧ CFSG.IsElementaryAbelian 2 A ∧
      MaxEA S A ∧ S.M ≤ normalizer (A : Set G) := by
  have hw := settingOfCore_width hz hext hcard
  have hQ := settingOfCore_QG hz hext hcard
  set S := settingOfCore z hz hext hcard with hS
  have hSz : S.z = z := rfl
  have hconj := exists_conj_of_not_weaklyClosed S hSz hQ hnwc
  obtain ⟨A₀, hlo, hhi, hnorm⟩ := hred
  rw [← hQ] at hlo hhi
  have hred' : S.IsReducible := isReducible_of_lt S hlo hhi hnorm
  obtain ⟨A, hEA, hA, hMA⟩ := hThmA G S hw hconj hred'
  exact ⟨S, A, hSz, hw, hEA, hA, hMA⟩

section Final

theorem false_of_width_four_reducible_of_theoremA (hThmA : TheoremAWidthFour)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (hset : (∃ a b : G, a * b ≠ b * a) ∧ CFSG.Assembly.KProper CFSG.Assembly.InCatalog G ∧
      CFSG.Assembly.IsCharTwoType G ∧ 4 ≤ CFSG.Assembly.evenRank G ∧ orderOf z = 2 ∧
      CFSG.Assembly.LargeEvenIsMaxTwoLocal (centralizer ({z} : Set G)) ∧
      CFSG.Assembly.LargeEvenSymplecticType
        (CFSG.Assembly.pCoreOf 2 (centralizer ({z} : Set G))) ∧
      ∃ B : Subgroup G, CFSG.Assembly.LargeEvenIsBmax 3 B ∧ B ≤ centralizer ({z} : Set G))
    (hext : IsExtraspecialPGroup 2 (inSubgroup generalizedFitting (centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (centralizer ({z} : Set G))) = 2 ^ 9)
    (hnwc : ¬ ∀ g : G, g⁻¹ * z * g ∈ inSubgroup generalizedFitting (centralizer ({z} : Set G)) →
      g⁻¹ * z * g = z)
    (hred : ∃ A : Subgroup G,
      (center (inSubgroup generalizedFitting (centralizer ({z} : Set G)))).map
        (inSubgroup generalizedFitting (centralizer ({z} : Set G))).subtype < A ∧
      A < inSubgroup generalizedFitting (centralizer ({z} : Set G)) ∧
      centralizer ({z} : Set G) ≤ normalizer (A : Set G)) : False := by
  obtain ⟨-, -, hchar, he, hz, hmax, hsym, B, hB, hBM⟩ := hset
  obtain ⟨S, A, hSz, hw, hEA, hA, hMA⟩ := exists_maxEA_of_core hThmA hz hext hcard hnwc hred
  have hMeq : S.M = centralizer ({z} : Set G) := by
    change centralizer ({S.z} : Set G) = _
    rw [hSz]
  have := hEA
  have hrank := four_le_rank_of_maxEA hw hA hMA hchar he (hMeq ▸ hmax) (hMeq ▸ hsym) hB
    (hMeq ▸ hBM)
  exact false_of_maxEA_of_three_rank hw hA hMA (hMeq ▸ hBM) (r := _) (by omega) hB.2.1

end Final

end CFSG.LargeExtraspecial.DW.W4Rank
