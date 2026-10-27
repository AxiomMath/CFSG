module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatSetup
import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridge
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFF
import CFSG.Quasithin.Background.G64Alt
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7Klein
import CFSG.CGT.PushingUpLit.BHS.FourFourC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.Quasithin.B1Red (conj_mem_pCoreOf fixV_pCoreOf_inv le_stabSub_fixV_pCoreOf
  pCoreOf_autSub_eq_bot)
open CFSG.Open
open CFSG.RankThree.PartTwo (altHeart evenWeightPerm)
open CFSG.QuasithinUnique (evenWeight)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (altFix)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altAct_mk IsAltNaturalSection
  isAltNaturalSection_commV_of_le exists_permRep_of_isAltNaturalSection)
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive (natFF mem_altFix_iff_altAct
  IsMatchingGroup)
open CFSG.LocalAnalysis.RankThreeUC.S15.GN15 (AltNatSetup altNatSetup)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)

variable {W : Type} [CommGroup W] [Finite W]

private theorem card_fixV_le_card_inf_mul_index {M : Type} [CommGroup M] [Finite M]
    {E : Subgroup (MulAut M)} {U : Subgroup M} :
    Nat.card (fixV E : Subgroup M) ≤ Nat.card ↥(U ⊓ fixV E) * U.index := by
  classical
  set F : Subgroup M := fixV E with hF
  have hcardF : Nat.card F * F.index = Nat.card M := Subgroup.card_mul_index F
  have hcardI : Nat.card ↥(F ⊓ U) * (F ⊓ U).index = Nat.card M :=
    Subgroup.card_mul_index (F ⊓ U)
  have h := Subgroup.index_inf_le (H := F) (K := U)
  have hmul : Nat.card F * F.index ≤ Nat.card ↥(F ⊓ U) * U.index * F.index := by
    calc Nat.card F * F.index = Nat.card M := hcardF
      _ = Nat.card ↥(F ⊓ U) * (F ⊓ U).index := hcardI.symm
      _ ≤ Nat.card ↥(F ⊓ U) * (F.index * U.index) := Nat.mul_le_mul_left _ h
      _ = Nat.card ↥(F ⊓ U) * U.index * F.index := by ring
  rw [inf_comm]
  exact Nat.le_of_mul_le_mul_right hmul
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := F)))

private theorem commV_zpowers_ne_bot {M : Type} [CommGroup M] [Finite M]
    {e : MulAut M} (he : e ≠ 1) : commV (Subgroup.zpowers e) ≠ ⊥ := by
  intro hbot
  apply he
  ext v
  have hmem : e v * v⁻¹ ∈ commV (Subgroup.zpowers e) :=
    Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, v, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private theorem card_mul_card_fixV_le_two {M : Type} [CommGroup M] [Finite M]
    {E : Subgroup (MulAut M)} (hEcard : Nat.card E = 2) :
    Nat.card E * Nat.card (fixV E) ≤ Nat.card M := by
  classical
  obtain ⟨e, he, huniq⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hEcard
  have hEeq : E = Subgroup.zpowers (e : MulAut M) := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : (⟨x, hx⟩ : E) = 1
      · rw [show x = 1 from congrArg Subtype.val hx1]
        exact Subgroup.one_mem _
      · have hxe : (⟨x, hx⟩ : E) = e := huniq ⟨x, hx⟩ hx1
        have hxval : x = (e : MulAut M) := congrArg Subtype.val hxe
        rw [hxval]
        exact Subgroup.mem_zpowers _
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact E.zpow_mem e.2 n
  have hcomm_ne : commV (Subgroup.zpowers (e : MulAut M)) ≠ ⊥ :=
    commV_zpowers_ne_bot (e := (e : MulAut M)) (fun h => he (Subtype.ext h))
  have hcomm_ge2 : 2 ≤ Nat.card (commV (Subgroup.zpowers (e : MulAut M))) := by
    have hpos : 0 < Nat.card (commV (Subgroup.zpowers (e : MulAut M))) := Nat.card_pos
    have hne1 : Nat.card (commV (Subgroup.zpowers (e : MulAut M))) ≠ 1 :=
      fun h1 => hcomm_ne (Subgroup.card_eq_one.mp h1)
    omega
  rw [hEcard, hEeq]
  calc 2 * Nat.card (fixV (Subgroup.zpowers (e : MulAut M)))
      ≤ Nat.card (commV (Subgroup.zpowers (e : MulAut M))) *
          Nat.card (fixV (Subgroup.zpowers (e : MulAut M))) :=
        Nat.mul_le_mul_right _ hcomm_ge2
    _ = Nat.card M := CFSG.CGT.PushingUpLit.BHS.card_commV_zpowers_mul (e : MulAut M)

private theorem card_mul_card_fixV_le_four_case {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {E : Subgroup (MulAut M)} (hEcard : Nat.card E = 4)
    (hnt : ∀ e ∈ E, e ≠ 1 → Nat.card (commV (Subgroup.zpowers e)) ≠ 2) :
    Nat.card E * Nat.card (fixV E) ≤ Nat.card M := by
  classical
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : E ≤ ⊥ := fun x hx => Subgroup.mem_bot.2 (h x hx)
    have := Subgroup.card_le_of_le hsub
    rw [Subgroup.card_bot] at this
    omega
  have hfix_le : fixV E ≤ fixV (Subgroup.zpowers e) := by
    intro v hv
    rw [mem_fixV] at hv ⊢
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact hv _ (E.zpow_mem he n)
  have hcomm_ge4 : 4 ≤ Nat.card (commV (Subgroup.zpowers e)) := by
    have hpow : Nat.card (commV (Subgroup.zpowers e)) =
        2 ^ CFSG.Quasithin.rk (commV (Subgroup.zpowers e)) :=
      CFSG.Quasithin.card_eq_two_pow hM2 (commV (Subgroup.zpowers e))
    have hcomm_ne : commV (Subgroup.zpowers e) ≠ ⊥ := commV_zpowers_ne_bot he1
    have hcomm_ge2 : 2 ≤ Nat.card (commV (Subgroup.zpowers e)) := by
      have hpos : 0 < Nat.card (commV (Subgroup.zpowers e)) := Nat.card_pos
      have hne1 : Nat.card (commV (Subgroup.zpowers e)) ≠ 1 :=
        fun h1 => hcomm_ne (Subgroup.card_eq_one.mp h1)
      omega
    have hge2 : 1 ≤ CFSG.Quasithin.rk (commV (Subgroup.zpowers e)) := by
      by_contra h
      have h0 : CFSG.Quasithin.rk (commV (Subgroup.zpowers e)) = 0 := by omega
      rw [hpow, h0] at hcomm_ge2
      norm_num at hcomm_ge2
    have hne1 : CFSG.Quasithin.rk (commV (Subgroup.zpowers e)) ≠ 1 := by
      intro h1
      apply hnt e he he1
      rw [hpow, h1]
      norm_num
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Quasithin.rk (commV (Subgroup.zpowers e)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = Nat.card (commV (Subgroup.zpowers e)) := hpow.symm
  calc Nat.card E * Nat.card (fixV E)
      = 4 * Nat.card (fixV E) := by rw [hEcard]
    _ ≤ 4 * Nat.card (fixV (Subgroup.zpowers e)) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hfix_le)
    _ ≤ Nat.card (commV (Subgroup.zpowers e)) * Nat.card (fixV (Subgroup.zpowers e)) :=
        Nat.mul_le_mul_right _ hcomm_ge4
    _ = Nat.card M := CFSG.CGT.PushingUpLit.BHS.card_commV_zpowers_mul e

private theorem card_mul_card_fixV_le_four {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {E : Subgroup (MulAut M)}
    (hE2 : ∀ e ∈ E, e * e = 1) (hEcard : Nat.card E ≤ 4)
    (hnt : ∀ e ∈ E, e ≠ 1 → Nat.card (commV (Subgroup.zpowers e)) ≠ 2) :
    Nat.card E * Nat.card (fixV E) ≤ Nat.card M := by
  classical
  have hEpg : IsPGroup 2 E := fun e => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hE2 e e.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hEpg
  have hk4 : k ≤ 2 := by
    have h2k : 2 ^ k ≤ 4 := by rw [← hk]; exact hEcard
    by_contra hgt
    have h3 : 3 ≤ k := by omega
    have h8 : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k
  · have hEbot : E = ⊥ := (Subgroup.card_eq_one).mp (by rw [hk]; norm_num)
    rw [hEbot, Subgroup.card_bot, one_mul,
      show fixV (⊥ : Subgroup (MulAut M)) = ⊤ by
        ext v; simp [CFSG.Quasithin.mem_fixV], Subgroup.card_top]
  · exact card_mul_card_fixV_le_two (by rw [hk]; norm_num)
  · exact card_mul_card_fixV_le_four_case hM2 (by rw [hk]; norm_num) hnt

private theorem altSub_LP1 {W : Type} [CommGroup W] [Finite W]
    {H L : Subgroup (MulAut W)} {n : ℕ} (hn5 : 5 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n)) (hLH : L ≤ H) :
    L ⊓ pCoreOf 2 H = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup e
  let _ : IsSimpleGroup ↥L := hsimple
  have hnorm : ((L ⊓ pCoreOf 2 H).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y l hy hl =>
      ⟨L.mul_mem (L.mul_mem hl hy.1) (L.inv_mem hl), conj_mem_pCoreOf (hLH hl) hy.2⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ _ _ hnorm with h | h
  · refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 H).subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
  · exfalso
    have hLP : L ≤ pCoreOf 2 H := fun x hx => by
      have hx' : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 H).subgroupOf L := by rw [h]; trivial
      exact hx'.2
    have h2 : IsPGroup 2 ↥L := hP2.to_le hLP
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.alt_not_two_group (by omega)
      (h2.of_surjective e.toMonoidHom e.surjective)

private theorem altSub_restrict_iso {W : Type} [CommGroup W] [Finite W]
    {H L : Subgroup (MulAut W)} {n : ℕ} (hn5 : 5 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n)) (hLH : L ≤ H)
    (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H)
    (hLP1 : L ⊓ pCoreOf 2 H = ⊥) :
    ∃ _ : ↥(autSub L (fixV (pCoreOf 2 H))) ≃* alternatingGroup (Fin n),
      CFSG.Open.IsQuasisimple ↥(autSub L (fixV (pCoreOf 2 H))) := by
  classical
  set P := pCoreOf 2 H with hPdef
  set W₁ := fixV P with hWdef
  have hHst : H ≤ stabSub W₁ := CFSG.Quasithin.B1Red.le_stabSub_fixV_pCoreOf H
  have hLst : L ≤ stabSub W₁ := hLH.trans hHst
  let fL : ↥L →* MulAut ↥W₁ := (resHom W₁).comp (Subgroup.inclusion hLst)
  have hfL_mem : ∀ l, fL l ∈ autSub L W₁ := fun l => mem_autSub.2 ⟨⟨l, hLst l.2⟩, l.2, rfl⟩
  let φ : ↥L →* ↥(autSub L W₁) := fL.codRestrict _ hfL_mem
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : fL l = 1 := congrArg Subtype.val hl
    have h2 : (⟨(l : MulAut W), hLst l.2⟩ : stabSub W₁) ∈ (resHom W₁).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
    have h3 : (l : MulAut W) ∈ H ⊓ centSub W₁ := ⟨hLH l.2, h2⟩
    rw [hker] at h3
    have h4 : (l : MulAut W) ∈ L ⊓ P := ⟨l.2, h3⟩
    rw [hLP1, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hψ
    exact ⟨⟨g.1, hgL⟩, Subtype.ext hg⟩
  let eL : ↥L ≃* ↥(autSub L W₁) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let eLb : ↥(autSub L W₁) ≃* alternatingGroup (Fin n) := eL.symm.trans e
  refine ⟨eLb, ?_⟩
  exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt (by omega) eLb

private theorem altSub_fstar {W : Type} [CommGroup W] [Finite W]
    {H L A : Subgroup (MulAut W)} {n : ℕ} (hn5 : 5 ≤ n)
    (eLb : ↥(autSub L (fixV (pCoreOf 2 H))) ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L)
    (hHA : H ≤ L ⊔ A) (hAH : A ≤ H) (hA2 : ∀ a ∈ A, a * a = 1)
    (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H) :
    quasithinGenFitting (autSub H (fixV (pCoreOf 2 H))) =
        autSub L (fixV (pCoreOf 2 H)) ∧
      pCoreOf 2 (autSub H (fixV (pCoreOf 2 H))) = ⊥ := by
  classical
  set P := pCoreOf 2 H with hPdef
  set W₁ := fixV P with hWdef
  have hq : CFSG.Open.IsQuasisimple ↥(autSub L W₁) :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt hn5 eLb
  have hconj : ∀ y ∈ autSub H W₁, ∀ l ∈ autSub L W₁, y * l * y⁻¹ ∈ autSub L W₁ :=
    fun y hy l hl => CFSG.Quasithin.autSub_conj_mem (fun x hx y hy => hLn x hx y hy) hy hl
  have hsq : ∀ x ∈ H, x ^ 2 ∈ L := by
    have hAn : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      le_normalizer_of_conj fun a ha l hl => hLn a (hAH ha) l hl
    intro x hx
    obtain ⟨l, hl, a, ha, rfl⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.exists_mul_of_sup hAn (hHA hx)
    have ha1 : a * a = 1 := by simpa [pow_two] using hA2 a ha
    have hmul : (l * a) ^ 2 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_two]; simp [mul_assoc]
    rw [hmul, ha1, mul_one]
    exact L.mul_mem hl (hLn a (hAH ha) l hl)
  have h2 : ∀ y ∈ autSub H W₁, ∃ k : ℕ, y ^ 2 ^ k ∈ autSub L W₁ := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine ⟨1, mem_autSub.2 ⟨g ^ 2, ?_, ?_⟩⟩
    · exact hsq _ hgH
    · simp [map_pow]
  have hO2 : pCoreOf 2 (autSub H W₁) = ⊥ := CFSG.Quasithin.B1Red.pCoreOf_autSub_eq_bot hker
  exact ⟨CFSG.Quasithin.C124.quasithinGenFitting_eq_of_two_group_quot (autSub_mono hLH W₁)
    hconj (Or.inl hq) h2 hO2, hO2⟩

private theorem altSub_iso {W : Type} [CommGroup W] [Finite W]
    {H L A : Subgroup (MulAut W)} {n : ℕ} (hn5 : 5 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L)
    (hHA : H ≤ L ⊔ A) (hAH : A ≤ H) (hA2 : ∀ a ∈ A, a * a = 1)
    (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H) :
    ∃ _ : ↥(autSub L (fixV (pCoreOf 2 H))) ≃* alternatingGroup (Fin n),
      quasithinGenFitting (autSub H (fixV (pCoreOf 2 H))) =
          autSub L (fixV (pCoreOf 2 H)) ∧
        pCoreOf 2 (autSub H (fixV (pCoreOf 2 H))) = ⊥ := by
  have hLP1 := altSub_LP1 hn5 e hLH
  obtain ⟨eLb, -⟩ := altSub_restrict_iso hn5 e hLH hker hLP1
  obtain ⟨hFstar, hO2⟩ := altSub_fstar hn5 eLb hLH hLn hHA hAH hA2 hker
  exact ⟨eLb, hFstar, hO2⟩

private theorem altSub_offender {W : Type} [CommGroup W] [Finite W]
    {H L A : Subgroup (MulAut W)}
    (hAH : A ≤ H) (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H)
    (hlp : ∀ x ∈ L, ∀ q ∈ pCoreOf 2 H, x * q = q * x)
    (hoff : IsFFStarOffender H A) (hLA : ⁅L, A⁆ ≠ ⊥) :
    IsFFStarOffender (autSub H (fixV (pCoreOf 2 H)))
      (autSub A (fixV (pCoreOf 2 H))) := by
  classical
  have hWA : commSub (fixV (pCoreOf 2 H)) A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hLA
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro l hl a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hmem : a ∈ H ⊓ centSub (fixV (pCoreOf 2 H)) :=
      ⟨hAH ha, fun w hw => h hw a ha⟩
    rw [hker] at hmem
    exact hlp l hl a hmem
  exact B7_1_1 hoff (fun a ha w hw => fixV_pCoreOf_inv a (hAH ha) w hw) hWA

private theorem card_commV_eq_card_inf_mul_altHeart {M : Type} [CommGroup M] [Finite M]
    {L : Subgroup (MulAut M)} {n : ℕ}
    (π : ↥(commV L) →* Multiplicative (altHeart n))
    (hπs : Function.Surjective π)
    (hπker : π.ker = (commV L ⊓ fixV L).subgroupOf (commV L)) :
    Nat.card (commV L) = Nat.card ↥(commV L ⊓ fixV L) * Nat.card (altHeart n) := by
  classical
  have h1 := Subgroup.card_ker_mul_card_range π
  rw [hπker] at h1
  have h2 : Nat.card ↥((commV L ⊓ fixV L).subgroupOf (commV L)) =
      Nat.card ↥(commV L ⊓ fixV L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card π.range = Nat.card (altHeart n) := by
    rw [MonoidHom.range_eq_top.mpr hπs, Subgroup.card_top]
    simp [Nat.card_eq_fintype_card]
  rw [h2, h3] at h1
  exact h1.symm

private theorem card_ker_comp_inclusion_le {M : Type} [CommGroup M] [Finite M]
    {L : Subgroup (MulAut M)} {n : ℕ}
    (π : ↥(commV L) →* Multiplicative (altHeart n))
    (hπker : π.ker = (commV L ⊓ fixV L).subgroupOf (commV L))
    (D : Subgroup M) (hDU : D ≤ commV L) :
    Nat.card (π.comp (Subgroup.inclusion hDU)).ker ≤ Nat.card ↥(commV L ⊓ fixV L) := by
  classical
  have hker_le : (π.comp (Subgroup.inclusion hDU)).ker ≤
      (commV L ⊓ fixV L).subgroupOf D := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (Subgroup.inclusion hDU x) ∈ π.ker := hx
    rw [hπker, Subgroup.mem_subgroupOf] at hx'
    exact hx'
  have h1 : Nat.card (π.comp (Subgroup.inclusion hDU)).ker ≤
      Nat.card ↥((commV L ⊓ fixV L).subgroupOf D) := Subgroup.card_le_of_le hker_le
  have h2 : Nat.card ↥((commV L ⊓ fixV L).subgroupOf D) =
      Nat.card ↥((commV L ⊓ fixV L) ⊓ D) := by
    have hEq : (commV L ⊓ fixV L).subgroupOf D =
        ((commV L ⊓ fixV L) ⊓ D).subgroupOf D := by ext x; simp
    rw [hEq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (commV L ⊓ fixV L) ⊓ D ≤ D)).toEquiv
  have h3 : Nat.card ↥((commV L ⊓ fixV L) ⊓ D) ≤ Nat.card ↥(commV L ⊓ fixV L) :=
    Subgroup.card_le_of_le inf_le_left
  omega

private theorem pi_fixed_mem_altFix {M : Type} [CommGroup M] [Finite M]
    {H A L : Subgroup (MulAut M)} {n : ℕ} {θ : ↥H →* Equiv.Perm (Fin n)}
    (π : ↥(commV L) →* Multiplicative (altHeart n))
    (hπeq : ∀ (h : ↥H) (u v : ↥(commV L)), (v : M) = (h : MulAut M) (u : M) →
      ∀ x : evenWeight n, Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π v) =
        (QuotientAddGroup.mk (evenWeightPerm (θ h : Equiv.Perm (Fin n)) x) : altHeart n))
    {B : Subgroup (Equiv.Perm (Fin n))}
    (hB : B = (A.subgroupOf H).map θ) {x : ↥(commV L)}
    (hx : ∀ a ∈ A, (a : MulAut M) (x : M) = (x : M)) :
    Multiplicative.toAdd (π x) ∈ altFix n B := by
  rw [hB]
  rw [mem_altFix_iff_altAct]
  rintro b ⟨a, ha, rfl⟩
  have haA : (a : MulAut M) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hx' : (a : MulAut M) (x : M) = (x : M) := hx a haA
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π x))
  have h1 := hπeq a x x (by simpa using hx'.symm) y hy.symm
  have h2 : Multiplicative.toAdd (π x) = (QuotientAddGroup.mk y : altHeart n) := hy.symm
  show altAct (θ a) (Multiplicative.toAdd (π x)) = Multiplicative.toAdd (π x)
  rw [h2, altAct_mk]
  exact h1.symm.trans h2

private theorem card_fixU_le {M : Type} [CommGroup M] [Finite M]
    {H L A : Subgroup (MulAut M)} {n : ℕ}
    (hAH : A ≤ H)
    (θ : ↥H →* Equiv.Perm (Fin n))
    (hθinj : Function.Injective θ)
    (π : ↥(commV L) →* Multiplicative (altHeart n))
    (hπs : Function.Surjective π)
    (hπker : π.ker = (commV L ⊓ fixV L).subgroupOf (commV L))
    (hπeq : ∀ (h : ↥H) (u v : ↥(commV L)), (v : M) = (h : MulAut M) (u : M) →
      ∀ x : evenWeight n, Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π v) =
        (QuotientAddGroup.mk (evenWeightPerm (θ h : Equiv.Perm (Fin n)) x) : altHeart n))
    (B : Subgroup (Equiv.Perm (Fin n)))
    (hB : B = (A.subgroupOf H).map θ)
    (hnatFF : Nat.card B * Nat.card (altFix n B) ≤ Nat.card (altHeart n)) :
    Nat.card A * Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card (commV L) := by
  classical
  let D : Subgroup M := commV L ⊓ fixV A
  let K : Subgroup M := commV L ⊓ fixV L
  let f : ↥D →* Multiplicative (altHeart n) :=
    π.comp (Subgroup.inclusion (inf_le_left : D ≤ commV L))
  have hkerπ : Nat.card (commV L) = Nat.card K * Nat.card (altHeart n) :=
    card_commV_eq_card_inf_mul_altHeart π hπs hπker
  have hf_range : ∀ y ∈ f.range, Multiplicative.toAdd y ∈ altFix n B := by
    rintro y ⟨x, rfl⟩
    exact pi_fixed_mem_altFix π hπeq hB fun a ha => (mem_fixV.1 x.2.2) a ha
  have hcard_range : Nat.card f.range ≤ Nat.card (altFix n B) := by
    let g : ↥f.range → ↥(altFix n B) := fun y =>
      ⟨Multiplicative.toAdd (y : Multiplicative (altHeart n)), hf_range y y.2⟩
    have hg : Function.Injective g := by
      intro y z h
      have hval : Multiplicative.toAdd (y : Multiplicative (altHeart n)) =
          Multiplicative.toAdd (z : Multiplicative (altHeart n)) :=
        congrArg (fun w : ↥(altFix n B) => (w : altHeart n)) h
      exact Subtype.ext (Multiplicative.toAdd.injective hval)
    exact Nat.card_le_card_of_injective g hg
  have hcard_ker : Nat.card f.ker ≤ Nat.card K :=
    card_ker_comp_inclusion_le π hπker D (inf_le_left : D ≤ commV L)
  have hEcard : Nat.card A = Nat.card B := by
    rw [hB, Subgroup.card_map_of_injective hθinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).symm
  have hD : Nat.card ↥D = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  rw [hD, hkerπ]
  calc Nat.card A * (Nat.card f.ker * Nat.card f.range)
      = Nat.card B * Nat.card f.ker * Nat.card f.range := by rw [hEcard]; ring
    _ ≤ Nat.card B * Nat.card K * Nat.card (altFix n B) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hcard_ker) hcard_range
    _ = Nat.card K * (Nat.card B * Nat.card (altFix n B)) := by ring
    _ ≤ Nat.card K * Nat.card (altHeart n) := Nat.mul_le_mul_left _ hnatFF

private theorem tight_natural {M : Type} [CommGroup M] [Finite M]
    {H L A : Subgroup (MulAut M)} {n : ℕ}
    (hn5 : 5 ≤ n) (hodd : Odd n) (eLb : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hAH : A ≤ H) (hA2 : ∀ a ∈ A, a * a = 1)
    (hFstar : L = quasithinGenFitting H)
    (hnatH : IsAltNaturalSection L (commV H) n) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card M := by
  classical
  have hn4 : 4 ≤ n := by omega
  have hn6 : n ≠ 6 := by rintro rfl; norm_num at hodd
  have hnatL : IsAltNaturalSection L (commV L) n :=
    isAltNaturalSection_commV_of_le hLH hn4 hnatH
  obtain ⟨θ, π, hπs, hπker, -, hπeq, hθinj⟩ :=
    exists_permRep_of_isAltNaturalSection hFstar hLH hn5 hn6 ⟨eLb⟩ hnatL
  let B : Subgroup (Equiv.Perm (Fin n)) := (A.subgroupOf H).map θ
  have hB : B = (A.subgroupOf H).map θ := rfl
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : MulAut M) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have haa : a * a = 1 := Subtype.ext (hA2 (a : MulAut M) haA)
    rw [← map_mul, haa, map_one]
  have hΔ : ¬ IsMatchingGroup B := fun h =>
    (Nat.not_even_iff_odd.2 hodd) (by simpa using h.even_card)
  have hnatFF := (natFF hn5 hB2).2 hΔ
  have hUle := card_fixU_le hAH θ hθinj π hπs hπker hπeq B hB hnatFF
  let U : Subgroup M := commV L
  have hfixU := card_fixV_le_card_inf_mul_index (M := M) (E := A) (U := U)
  have hcardU : Nat.card U * U.index = Nat.card M := Subgroup.card_mul_index U
  calc Nat.card A * Nat.card (fixV A)
      ≤ Nat.card A * (Nat.card ↥(U ⊓ fixV A) * U.index) :=
          Nat.mul_le_mul_left _ hfixU
    _ = Nat.card A * Nat.card ↥(U ⊓ fixV A) * U.index := by ring
    _ ≤ Nat.card U * U.index := Nat.mul_le_mul_right _ hUle
    _ = Nat.card M := hcardU

private theorem tight_sixteen {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {L A : Subgroup (MulAut M)}
    (eLb : ↥L ≃* alternatingGroup (Fin 7)) (hAL : A ≤ L)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card M := by
  classical
  have hAcard : Nat.card A ≤ 4 := by
    have h2 : ∀ b ∈ (A.subgroupOf L).map eLb.toMonoidHom, b * b = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      have haA : (a : MulAut M) ∈ A := Subgroup.mem_subgroupOf.mp ha
      have haa : a * a = 1 := Subtype.ext (hA2 (a : MulAut M) haA)
      rw [← map_mul, haa, map_one]
    have hle :=
      CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.alt7_elemAbelian_card_le h2
    rw [Subgroup.card_map_of_injective eLb.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv] at hle
    exact hle
  have hnt : ∀ e ∈ A, e ≠ 1 → Nat.card (commV (Subgroup.zpowers e)) ≠ 2 := by
    intro e he he1 htr
    exact CFSG.Quasithin.G64.false_of_alt_transvection hM2 (Or.inr (Or.inr rfl))
      eLb.symm (hAL he) (hA2 e he) he1 htr
  exact card_mul_card_fixV_le_four hM2 hA2 hAcard hnt

private theorem step3_sup_eq {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {A : Subgroup (MulAut W)} {W₁ : Subgroup W}
    (hoff : IsFFStarOffender H A)
    (hstep2 : Nat.card A * Nat.card ↥(W₁ ⊓ fixV A) ≤
      Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) * Nat.card W₁) :
    Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) *
        Nat.card (fixV ((A ⊓ centSub W₁ : Subgroup (MulAut W)))) =
      Nat.card A * Nat.card (fixV A) ∧
      W₁ ⊔ fixV A = fixV ((A ⊓ centSub W₁ : Subgroup (MulAut W))) := by
  classical
  set B : Subgroup (MulAut W) := A ⊓ centSub W₁ with hBdef
  have hBA : B ≤ A := inf_le_left
  have hWfix : W₁ ≤ fixV B := by
    intro w hw b hb
    exact hb.2 w hw
  have hinfW : W₁ ⊓ fixV B = W₁ := inf_eq_left.mpr hWfix
  have hle := CFSG.Quasithin.B1.card_inf_fixV_le hoff hBA W₁
  rw [hinfW] at hle
  have heq : Nat.card B * Nat.card ↥(W₁ ⊓ fixV B) =
      Nat.card A * Nat.card ↥(W₁ ⊓ fixV A) := by
    rw [hinfW]
    exact le_antisymm hle hstep2
  obtain ⟨hweight, hsup⟩ := CFSG.Quasithin.B1.card_inf_fixV_eq hoff hBA W₁ heq
  refine ⟨hweight, ?_⟩
  rw [hinfW] at hsup
  exact hsup

private theorem step3_B_bot {W : Type} [CommGroup W] [Finite W]
    {H Y L A : Subgroup (MulAut W)} {W₁ : Subgroup W}
    (hA : A ∈ PstarSet Y) (hoff : IsFFStarOffender H A)
    (hker : H ⊓ centSub W₁ = pCoreOf 2 H)
    (hlp : ∀ x ∈ L, ∀ q ∈ pCoreOf 2 H, x * q = q * x)
    (hLA : ⁅L, A⁆ ≠ ⊥)
    (hweight : Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) *
        Nat.card (fixV ((A ⊓ centSub W₁ : Subgroup (MulAut W)))) =
      Nat.card A * Nat.card (fixV A)) :
    (A ⊓ centSub W₁ : Subgroup (MulAut W)) = ⊥ := by
  classical
  by_contra hBne
  set B : Subgroup (MulAut W) := A ⊓ centSub W₁ with hBdef
  have hBA : B ≤ A := inf_le_left
  have hAoff : IsFFStarOffender Y A := hA.1
  have hBoff : IsFFStarOffender Y B := by
    refine ⟨hBA.trans hAoff.1, hBne, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb
      exact hAoff.2.2.1.1 a ha.1 b hb.1
    · intro a ha
      exact hAoff.2.2.1.2 a ha.1
    · intro C hC
      have h1 := hAoff.2.2.2 C (hC.trans hBA)
      rwa [hweight]
  have hBeq : B = A := hA.2 B hBoff hBA hweight.symm
  have hAcent : A ≤ centSub W₁ := by
    rw [← hBeq]
    exact inf_le_right
  have hAP : A ≤ pCoreOf 2 H := by
    intro a ha
    have hmem : a ∈ H ⊓ centSub W₁ := ⟨hoff.1 ha, hAcent ha⟩
    rwa [hker] at hmem
  apply hLA
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro l hl a ha
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hlp l hl a (hAP ha)

private theorem commutator_eq_of_alt {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {n : ℕ} (hn5 : 5 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hLA : ⁅L, A⁆ ≠ ⊥) :
    ⁅L, A⁆ = L := by
  classical
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup e
  let _ : IsSimpleGroup ↥L := hsimple
  have hcomm_le : ⁅L, A⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl a ha
    rw [commutatorElement_def]
    have h1 : a * l⁻¹ * a⁻¹ ∈ L := hAn a ha l⁻¹ (L.inv_mem hl)
    have heq : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
    rw [heq]
    exact L.mul_mem hl h1
  have hnormal : ((⁅L, A⁆).subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hcomm_le).2 ?_
    intro y l hy hl
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.normalizer_commutator_ge_left (H₁ := L) (H₂ := A) hl) y).mp hy
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ _ _ hnormal with h | h
  · exfalso
    apply hLA
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hcomm_le hx⟩ : ↥L) ∈ (⁅L, A⁆).subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  · ext x
    constructor
    · intro hx
      exact hcomm_le hx
    · intro hx
      have hx' : (⟨x, hx⟩ : ↥L) ∈ (⁅L, A⁆).subgroupOf L := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp hx'

private theorem commV_le_of_trivial_quot {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {W₁ : Subgroup W}
    (hLW : ∀ l ∈ L, ∀ w ∈ W₁, l w ∈ W₁)
    (hAtriv : ∀ a ∈ A, ∀ v : W, a v * v⁻¹ ∈ W₁)
    (hLAeq : ⁅L, A⁆ = L) : commV L ≤ W₁ := by
  classical
  let N : Subgroup (MulAut W) :=
    { carrier := {g : MulAut W | ∀ v : W, g v * v⁻¹ ∈ W₁}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro g h hg hh v
        have e : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
          simp only [MulAut.mul_apply]; group
        rw [e]; exact W₁.mul_mem (hg (h v)) (hh v)
      inv_mem' := by
        intro g hg v
        have h1 := hg (g⁻¹ v)
        have e : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]; simp
        rw [e]; exact W₁.inv_mem h1 }
  have hAN : A ≤ N := hAtriv
  have hNconj : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := by
    intro l hl n hn v
    have h1 := hn (l⁻¹ v)
    have h2 := hLW l hl _ h1
    have e : (l * n * l⁻¹) v * v⁻¹ = l (n (l⁻¹ v) * (l⁻¹ v)⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv]
      rw [MulAut.apply_inv_self]
    rw [e]; exact h2
  have hLN : L ≤ N := by
    rw [← hLAeq, Subgroup.commutator_le]
    intro l hl a ha
    have h1 : l * a * l⁻¹ ∈ N := hNconj l hl a (hAN ha)
    have h2 : a⁻¹ ∈ N := N.inv_mem (hAN ha)
    rw [commutatorElement_def]
    exact N.mul_mem h1 h2
  unfold commV
  refine (Subgroup.closure_le W₁).2 ?_
  rintro _ ⟨l, hl, v, rfl⟩
  exact hLN hl v

private theorem tight_step2 {W : Type} [CommGroup W] [Finite W] (hGF : GF2EightFive)
    (hW : ∀ w : W, w ^ 2 = 1) {H L A : Subgroup (MulAut W)} {n : ℕ}
    (hn5 : 5 ≤ n) (hn7 : 7 ≤ n) (hodd : Odd n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L)
    (hHA : H ≤ L ⊔ A) (hAH : A ≤ H) (hA2 : ∀ a ∈ A, a * a = 1)
    (hker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H)
    (hlp : ∀ x ∈ L, ∀ q ∈ pCoreOf 2 H, x * q = q * x)
    (hoffH : IsFFStarOffender H A) (hLA : ⁅L, A⁆ ≠ ⊥) :
    Nat.card A * Nat.card ↥(fixV (pCoreOf 2 H) ⊓ fixV A) ≤
      Nat.card (A ⊓ centSub (fixV (pCoreOf 2 H)) : Subgroup (MulAut W)) *
        Nat.card (fixV (pCoreOf 2 H)) := by
  classical
  set W₁ := fixV (pCoreOf 2 H) with hW₁def
  obtain ⟨eLb, hFstar, -⟩ := altSub_iso hn5 e hLH hLn hHA hAH hA2 hker
  have hoff' := altSub_offender hAH hker hlp hoffH hLA
  have hW2 : ∀ v : ↥W₁, v ^ 2 = 1 := fun v => Subtype.ext (hW v)
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hcase : n = 7 ∨ 9 ≤ n := by
    by_cases h8 : n ≤ 8
    · have hn78 : n = 7 ∨ n = 8 := by omega
      rcases hn78 with rfl | rfl
      · exact Or.inl rfl
      · rw [show (8 : ℕ) % 2 = 0 by norm_num] at hmod
        omega
    · exact Or.inr (by omega)
  have hnat := hGF ↥W₁ hW2 (autSub H W₁) (autSub L W₁) hFstar.symm n hcase
    ⟨eLb⟩ ⟨autSub A W₁, hoff'⟩
  have hLH' : autSub L W₁ ≤ autSub H W₁ := autSub_mono hLH W₁
  have hAH' : autSub A W₁ ≤ autSub H W₁ := autSub_mono hAH W₁
  have hA2' : ∀ a ∈ autSub A W₁, a * a = 1 := hoff'.2.2.1.2
  have hsub : Nat.card (autSub A W₁) * Nat.card (fixV (autSub A W₁)) ≤ Nat.card ↥W₁ := by
    rcases hnat with hnat | ⟨hn7, hHL, -⟩
    · exact tight_natural hn5 hodd eLb hLH' hAH' hA2' hFstar.symm hnat
    · have eLb7 : ↥(autSub L W₁) ≃* alternatingGroup (Fin 7) := hn7 ▸ eLb
      have hAL' : autSub A W₁ ≤ autSub L W₁ := by rw [← hHL]; exact hoff'.1
      exact tight_sixteen hW2 eLb7 hAL' hA2'
  have hAst : A ≤ stabSub W₁ := hAH.trans (le_stabSub_fixV_pCoreOf H)
  have hcardA : Nat.card (autSub A W₁) *
      Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) = Nat.card A :=
    card_autSub_mul hAst
  have hcardFix : Nat.card ↥(W₁ ⊓ fixV A) = Nat.card (fixV (autSub A W₁)) := by
    rw [← map_subtype_fixV_autSub hAst, Subgroup.card_map_of_injective W₁.subtype_injective]
  rw [← hcardA, hcardFix]
  calc Nat.card (autSub A W₁) * Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) *
        Nat.card (fixV (autSub A W₁))
      = Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) *
          (Nat.card (autSub A W₁) * Nat.card (fixV (autSub A W₁))) := by ring
    _ ≤ Nat.card ((A ⊓ centSub W₁ : Subgroup (MulAut W))) * Nat.card W₁ :=
        Nat.mul_le_mul_left _ hsub

private theorem finish_step {W : Type} [CommGroup W] [Finite W]
    {H Y L A : Subgroup (MulAut W)} {W₁ : Subgroup W}
    (hA : A ∈ PstarSet Y) (hoffH : IsFFStarOffender H A)
    (hker : H ⊓ centSub W₁ = pCoreOf 2 H)
    (hlp : ∀ x ∈ L, ∀ q ∈ pCoreOf 2 H, x * q = q * x)
    (hLH : L ≤ H) (hWH : ∀ h ∈ H, ∀ w ∈ W₁, h w ∈ W₁)
    (hLAeq : ⁅L, A⁆ = L) (hLA : ⁅L, A⁆ ≠ ⊥)
    (hstep2 : Nat.card A * Nat.card ↥(W₁ ⊓ fixV A) ≤
      Nat.card (A ⊓ centSub W₁ : Subgroup (MulAut W)) * Nat.card W₁) :
    commV L ≤ W₁ := by
  classical
  obtain ⟨hweight, hsup⟩ := step3_sup_eq hoffH hstep2
  have hBbot : (A ⊓ centSub W₁ : Subgroup (MulAut W)) = ⊥ :=
    step3_B_bot hA hoffH hker hlp hLA hweight
  have hsup_top : W₁ ⊔ fixV A = ⊤ := by
    rw [hBbot] at hsup
    rwa [show fixV (⊥ : Subgroup (MulAut W)) = ⊤ by
      ext v; simp [CFSG.Quasithin.mem_fixV]] at hsup
  have hAtriv : ∀ a ∈ A, ∀ v : W, a v * v⁻¹ ∈ W₁ := by
    intro a ha v
    have hv : v ∈ W₁ ⊔ fixV A := by rw [hsup_top]; trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
    have haw : a w * w⁻¹ ∈ W₁ := W₁.mul_mem (hWH a (hoffH.1 ha) w hw) (W₁.inv_mem hw)
    have hac : a c = c := (CFSG.Quasithin.mem_fixV.1 hc) a ha
    simpa [map_mul, hac] using haw
  have hLW : ∀ l ∈ L, ∀ w ∈ W₁, l w ∈ W₁ := fun l hl => hWH l (hLH hl)
  exact commV_le_of_trivial_quot hLW hAtriv hLAeq

theorem commV_le_fixV_pCoreOf (h85 : GF2EightFive) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L A : Subgroup (MulAut W)} {n : ℕ} (hn : 7 ≤ n) (hno : Odd n) (hL : IsAlt ↥L n)
    (hA : A ∈ PstarSet Y) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLA : ⁅L, A⁆ ≠ ⊥) :
    commV L ≤ fixV (CFSG.Open.pCoreOf 2 (L ⊔ A)) := by
  classical
  obtain ⟨e⟩ := hL
  let H : Subgroup (MulAut W) := L ⊔ A
  let P : Subgroup (MulAut W) := pCoreOf 2 H
  let W₁ : Subgroup W := fixV P
  have hn5 : 5 ≤ n := by omega
  have hLH : L ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hLN : L ≤ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.le_normalizer
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut W)) := sup_le hLN hAN
  have hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := fun h hh l hl =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) l).mp hl
  have hA2 : ∀ a ∈ A, a * a = 1 := hA.1.2.2.1.2
  have hS : AltNatSetup H L A := altNatSetup hW hn5 e hLH hLn le_rfl hAH hA2
  have hoffH : IsFFStarOffender H A :=
    ⟨hAH, hA.1.2.1, hA.1.2.2.1, hA.1.2.2.2⟩
  have hstep2 := tight_step2 h85 hW hn5 hn hno e hLH hLn le_rfl hAH hA2 hS.ker hS.lp
    hoffH hLA
  have hLAeq : ⁅L, A⁆ = L := commutator_eq_of_alt hn5 e hS.an hLA
  have hWH : ∀ h ∈ H, ∀ w ∈ W₁, h w ∈ W₁ := fixV_pCoreOf_inv
  have hfin := finish_step hA hoffH hS.ker hS.lp hLH hWH hLAeq hLA hstep2
  show commV L ≤ W₁
  exact hfin

end CFSG.GroupTheory

end
