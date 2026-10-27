module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCat
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBender
public import CFSG.Monster.B.Recog.GenericGoldschmidtArithOmega
public import CFSG.Walter.J1Props.Aut
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

theorem gmi_sq_of_iso {Y : Type} [Group Y] [Finite Y] {K T : Subgroup Y} (hT : IsSylowOf 2 T K)
    {H : Type} [Group H] [Finite H] (e : K ≃* H)
    (hH : ∀ S : Sylow 2 H, ∀ x ∈ (S : Subgroup H), x ^ 2 = 1) : ∀ x ∈ T, x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxK : x ∈ K := hT.le hx
  have hp : IsPGroup 2 ((T.subgroupOf K).map e.toMonoidHom) :=
    (hT.isPGroup.comap_subtype).map _
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hy : e ⟨x, hxK⟩ ∈ (S : Subgroup H) := hS ⟨⟨x, hxK⟩, mem_subgroupOf.mpr hx, rfl⟩
  have h2 := hH S _ hy
  rw [← map_pow] at h2
  have h3 : (⟨x, hxK⟩ : K) ^ 2 = 1 := e.injective (by rw [h2, map_one])
  simpa using congrArg Subtype.val h3

theorem gmiCatFourInput_holds : GmiCatFourInput := by
  intro L _ _ hL
  have h2 : Nat.Prime 2 := Nat.prime_two
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have key : 2 ≤ (Nat.card L).factorization 2 → 4 ∣ Nat.card L := fun hv =>
    (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ (h2.pow_dvd_iff_le_factorization hL0).mpr hv
  rcases hL with ⟨n, hn, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ |
      ⟨p, n, hp, hpodd, hn0, -, h8, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (by omega)]
    refine Dvd.dvd.mul_right ?_ _
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  · rw [Nat.card_congr e.toEquiv, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz n]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  · have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd
      (p := n) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    have hdvd : 2 ^ 2 ∣ Nat.card L * Nat.gcd 3 (2 ^ n + 1) := by
      rw [h]
      refine Dvd.dvd.mul_right ?_ _
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have hcop : Nat.Coprime (2 ^ 2) (Nat.gcd 3 (2 ^ n + 1)) :=
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num : Nat.Coprime 2 3)).pow_left 2
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ hcop.dvd_of_dvd_mul_right hdvd
  · exact key (CFSG.Monster.B.Recog.GoldschmidtArithOmega.psl2_odd_factorization hpodd hn0 h8 e).ge
  · exact key (CFSG.Monster.B.Recog.GoldschmidtArithOmega.ree_factorization hcard ▸ (by norm_num))
  · rw [Nat.card_congr e.toEquiv]
    show 4 ∣ Nat.card CFSG.Open.walterJ1
    rw [CFSG.Walter.J1Props.card_walterJ1]
    norm_num

theorem gmiCatSimpleInput_holds :
    GmiCatSimpleInput := by
  intro Y _ _ K T hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro n hn ⟨e⟩
    have hKcard : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (by omega)]
    refine ⟨hKcard, ?_, ?_⟩
    · have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
        rw [← pow_mul]
        exact CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_sub_one (by omega)
      rw [hT.card_eq, hKcard,
        CFSG.Monster.B.Recog.GoldschmidtArith.factorization_two_pow_mul_odd n hodd]
    · exact gmi_sq_of_iso hT e (fun S x hx => by
        have := (CFSG.Walter.psl2_even_sylow_two hn S).1
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx)
  ·
    rintro n - ⟨e⟩
    exact CFSG.Monster.B.Recog.GoldschmidtArithOmega.sz_not_three_dvd e
  ·
    rintro n hn ⟨e⟩
    refine ⟨?_, ?_⟩
    · have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd
        (p := n) (by omega)
      rw [← Nat.card_congr e.toEquiv] at h
      have hg : ¬ 2 ∣ Nat.gcd 3 (2 ^ n + 1) := fun h2 =>
        absurd (h2.trans (Nat.gcd_dvd_left 3 _)) (by norm_num)
      have hg0 : Nat.gcd 3 (2 ^ n + 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
      have hodd : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
        refine Odd.mul ?_ ?_
        · rw [← pow_mul]
          exact CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_sub_one (by omega)
        · rw [← pow_mul]
          exact CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_add_one (by omega)
      have hv2 : ((2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))).factorization 2 =
          3 * n := by
        rw [show (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) =
          2 ^ (3 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) by ring]
        exact CFSG.Monster.B.Recog.GoldschmidtArith.factorization_two_pow_mul_odd _ hodd
      have hv1 : (Nat.card K * Nat.gcd 3 (2 ^ n + 1)).factorization 2 =
          (Nat.card K).factorization 2 := by
        rw [Nat.factorization_mul Nat.card_pos.ne' hg0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hg, add_zero]
      rw [hT.card_eq, ← hv1, h, hv2, ← pow_mul, mul_comm]
    · have hB : CFSG.ComponentClassification.AschbacherTheorem3.IsBenderType K n :=
        Or.inr (Or.inr ⟨hn, ⟨e⟩⟩)
      obtain ⟨k, -, hBB, -⟩ :=
        CFSG.ComponentClassification.AschbacherTheorem3.FourEight.exists_benderBorel hB
      have hcent :=
        (CFSG.ComponentClassification.AschbacherTheorem3.FourEight.bender_sylow hB hT).1
      obtain ⟨Q, hQ⟩ := hT
      obtain ⟨-, -, -, hZcard, -⟩ := hBB Q
      intro W hWT hW2
      have hle : W ≤ (Subgroup.center (Q : Subgroup K)).map
          (K.subtype.comp (Q : Subgroup K).subtype) := by
        intro w hw
        have hwT := hWT hw
        rw [← hQ] at hwT
        obtain ⟨q, hq, rfl⟩ := hwT
        refine ⟨⟨q, hq⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subtype.ext ?_), rfl⟩
        have h1 := hcent _ (by rw [← hQ]; exact mem_map_of_mem _ hq) (hW2 _ hw) _
          (by rw [← hQ]; exact mem_map_of_mem _ g.2)
        exact h1.symm
      calc Nat.card W ≤ Nat.card ((Subgroup.center (Q : Subgroup K)).map
            (K.subtype.comp (Q : Subgroup K).subtype)) := Subgroup.card_le_of_le hle
        _ = Nat.card (Subgroup.center (Q : Subgroup K)) :=
            Subgroup.card_map_of_injective (fun _ _ hab => Subtype.ext (Subtype.ext hab))
        _ = 2 ^ n := hZcard
  ·
    rintro p n _ hp hn h8 ⟨e⟩
    obtain ⟨Q, hQ⟩ := hT
    obtain ⟨hcard, hsq, -⟩ := CFSG.Goldschmidt.GoldType.sylow_of_psl2_odd hp hn h8 e Q
    refine ⟨by rw [← hQ, Subgroup.card_map_of_injective K.subtype_injective, hcard], ?_⟩
    intro x hx
    rw [← hQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hsq y hy
    simpa using congrArg Subtype.val this
  ·
    rintro ⟨e⟩
    refine ⟨by rw [Nat.card_congr e.toEquiv]; exact CFSG.Walter.J1Props.card_walterJ1, ?_⟩
    exact gmi_sq_of_iso hT e (fun S x hx => by
      have := (CFSG.Walter.J1Props.jankoHyp.sylow_structure S).2.1 x hx
      rw [sq]
      exact this)

@[expose] def GmiCatSL2CoverInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.IsQuasisimple K →
    IsPGroup 2 (center K) → center K ≠ ⊥ →
    ∀ (p n : ℕ) [Fact p.Prime], Odd p → 0 < n → (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) →
      Nonempty ((K ⧸ center K) ≃* PSL(2, GaloisField p n)) →
      ∀ T : Subgroup Y, IsSylowOf 2 T K → ∃ u ∈ K, (∀ x ∈ T, u * x * u⁻¹ ∈ T) ∧
        ∀ k ∈ T, (∃ y ∈ K, k * y ≠ y * k) → k * (u * k * u⁻¹) ≠ u * k * u⁻¹ * k

theorem gmiCatSchurInput_of_sl2 (hSL2 : GmiCatSL2CoverInput) : GmiCatSchurInput := by
  intro Y _ _ K hK hZp hZ
  have hcomm : commutator K = ⊤ := hK.1.commutator_eq_top
  have hodd_false : Odd (Nat.card (center K)) → False := by
    intro hodd
    obtain ⟨c, hc⟩ := hZp.exists_card_eq
    rw [hc] at hodd
    have hc0 : c = 0 := by
      by_contra hc0
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hc0⟩)
    rw [hc0, pow_zero] at hc
    exact hZ (Subgroup.card_eq_one.mp hc)
  refine ⟨fun n hn => ⟨fun e => hodd_false
      (CFSG.ComponentClassification.GMS78.odd_card_center_of_psl2 hcomm hn e)⟩,
    fun n hn => ⟨fun e => hodd_false
      (CFSG.ComponentClassification.GMS78.odd_card_center_of_psu3 hcomm hn e)⟩,
    ⟨fun e => ?_⟩, hSL2 Y K hK hZp hZ⟩
  let π : K →* CFSG.Open.walterJ1 := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center K := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).ker = center K
    rw [← MonoidHom.comap_ker, (MonoidHom.ker_eq_bot_iff _).mpr e.injective,
      MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have h1 := CFSG.Walter.J1Props.J3_multiplier π hπ hker.le hcomm
  rw [hker] at h1
  exact hZ h1

theorem gmi_center_walterJ1 :
    Subgroup.center CFSG.Open.walterJ1 = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.Walter.J1Props.isSimpleGroup_walterJ1
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 CFSG.Open.walterJ1))
  obtain ⟨hScard, -, -, hScent⟩ := CFSG.Walter.J1Props.jankoHyp.sylow_structure S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center CFSG.Open.walterJ1) with h | h
  · exact h
  · exfalso
    have hle : (⊤ : Subgroup CFSG.Open.walterJ1) ≤ S := by
      rw [← hScent, ← h]
      exact Subgroup.center_le_centralizer _
    have hc := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, CFSG.Walter.J1Props.card_walterJ1, hScard] at hc
    norm_num at hc

theorem gmi_fix_sylow_of_j1 {Y : Type} [Group Y] [Finite Y]
    {K T : Subgroup Y} (e₀ : K ≃* goldschmidtJ1) (hT : IsSylowOf 2 T K) (σ : MulAut Y)
    (hσK : ∀ k ∈ K, σ k ∈ K) (hσ2 : ∀ x, σ (σ x) = x) (hσT : ∀ x ∈ T, σ x ∈ T) :
    ∀ x ∈ T, σ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : K ≃* CFSG.Open.walterJ1 :=
    e₀.trans (MulEquiv.subgroupCongr (show goldschmidtJ1 = CFSG.Open.walterJ1 from rfl))
  have hKmap : K.map σ.toMonoidHom = K :=
    le_antisymm (by rintro _ ⟨k, hk, rfl⟩; exact hσK k hk)
      (fun k hk => ⟨σ k, hσK k hk, hσ2 k⟩)
  let σK : K ≃* K := (σ.subgroupMap K).trans (MulEquiv.subgroupCongr hKmap)
  have hσKapp : ∀ k : K, ((σK k : K) : Y) = σ k := fun k => rfl
  let φ : MulAut CFSG.Open.walterJ1 := (e.symm.trans σK).trans e
  have hφapp : ∀ k : K, φ (e k) = e (σK k) := fun k => by
    show e (σK (e.symm (e k))) = e (σK k)
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut φ
  have hgapp : ∀ y, φ y = g * y * g⁻¹ := fun y => by rw [hg]; rfl
  have hσK2 : ∀ k : K, σK (σK k) = k := fun k => Subtype.ext (hσ2 k)
  have hg2 : g * g = 1 := by
    have hcen : g * g ∈ Subgroup.center CFSG.Open.walterJ1 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := e.surjective y
      have h1 : φ (φ (e k)) = e k := by rw [hφapp, hφapp, hσK2]
      rw [hgapp (φ (e k)), hgapp (e k)] at h1
      calc e k * (g * g) = (g * (g * e k * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = g * g * e k := by group
    rw [gmi_center_walterJ1, Subgroup.mem_bot] at hcen
    exact hcen
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  obtain ⟨Q, hQ⟩ := hT
  let TW : Sylow 2 CFSG.Open.walterJ1 := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTW : (TW : Subgroup CFSG.Open.walterJ1) = (Q : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hσQ : ∀ q ∈ (Q : Subgroup K), σK q ∈ (Q : Subgroup K) := by
    intro q hq
    have hqT : (q : Y) ∈ T := by rw [← hQ]; exact mem_map_of_mem _ hq
    have h1 := hσT _ hqT
    rw [← hQ] at h1
    obtain ⟨q', hq', hq'e⟩ := h1
    rwa [show σK q = q' from Subtype.ext hq'e.symm]
  have hgTW : ∀ y ∈ (TW : Subgroup CFSG.Open.walterJ1), g * y * g⁻¹ ∈
      (TW : Subgroup CFSG.Open.walterJ1) := by
    intro y hy
    rw [hTW] at hy ⊢
    obtain ⟨q, hq, rfl⟩ := hy
    rw [← hgapp, MulEquiv.coe_toMonoidHom, hφapp]
    exact mem_map_of_mem _ (hσQ q hq)
  have hgN : g ∈ normalizer ((TW : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hgTW y, fun hy => ?_⟩
    have := hgTW _ hy
    rwa [hginv, show g * (g * y * g) * g = (g * g) * y * (g * g) by group, hg2, one_mul,
      mul_one] at this
  have hgp : IsPGroup 2 (zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    show (g ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [sq, hg2]
  have hsup := hgp.to_sup_of_normal_right' TW.isPGroup' (zpowers_le.mpr hgN)
  have heq := TW.is_maximal' hsup le_sup_right
  have hgmem : g ∈ (TW : Subgroup CFSG.Open.walterJ1) := heq ▸ mem_sup_left (mem_zpowers g)
  have hTWab := (CFSG.Walter.J1Props.jankoHyp.sylow_structure TW).2.2.1
  intro x hx
  rw [← hQ] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hqTW : e q ∈ (TW : Subgroup CFSG.Open.walterJ1) := by
    rw [hTW]
    exact mem_map_of_mem _ hq
  have h1 : e (σK q) = e q := by
    rw [← hφapp, hgapp, hTWab g hgmem _ hqTW, mul_inv_cancel_right]
  have h2 : σK q = q := e.injective h1
  show σ (q : Y) = (q : Y)
  rw [← hσKapp]
  exact congrArg Subtype.val h2

end CFSG.SeitzReduction.RankOne
