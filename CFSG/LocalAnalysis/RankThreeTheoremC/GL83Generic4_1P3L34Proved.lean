module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

private theorem isRankThreeL34_iff_index {K : Type} [Group K] :
    IsRankThreeL34 K ↔ ∃ d : TauCeti.ValidLieTypeIndex, IsL34Index d ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  constructor
  · rintro ⟨q, hq2, hqe, hv, he⟩
    exact ⟨⟨.A 2 q, hv⟩, ⟨q, hq2, hqe, rfl⟩, he⟩
  · rintro ⟨⟨d, hv⟩, ⟨q, hq2, hqe, hd⟩, he⟩
    simp only at hd
    subst hd
    exact ⟨q, hq2, hqe, hv, he⟩

theorem kFactL34ThreeExponent : KFactL34ThreeExponent := by
  intro X _ _ K hK hC hL g ⟨n, hn⟩
  obtain ⟨d, hd, he⟩ := isRankThreeL34_iff_index.1 hL
  refine kFactL34Exp3 d hd X K hK hC he g ?_
  rintro ⟨_, m, rfl⟩
  refine ⟨n, Subtype.ext ?_⟩
  show (g ^ m) ^ 3 ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]

theorem kFactL34SylowCentralizer : KFactL34SylowCentralizer := by
  intro K _ _ hL S u hu hu1
  obtain ⟨d, hd, ⟨e⟩⟩ := isRankThreeL34_iff_index.1 hL
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hF
  have hS9 : Nat.card (S : Subgroup K) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfK]
    norm_num
  have hE9 : Nat.card ((S : Subgroup K).map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hS9
  have hc := CFSG.RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hF hE9
    (Subgroup.mem_map_of_mem _ hu) (by simpa using hu1)
  ext z
  have h1 : z ∈ Subgroup.centralizer ({u} : Set K) ↔
      ψ.toMonoidHom z ∈ Subgroup.centralizer ({ψ.toMonoidHom u} : Set _) := by
    simp only [Subgroup.mem_centralizer_singleton_iff, ← map_mul, MulEquiv.coe_toMonoidHom,
      ψ.apply_eq_iff_eq]
  rw [h1, hc]
  simp

theorem kFactL34OutThree : KFactL34OutThree := by
  intro X _ _ K hK hC hL F hF
  obtain ⟨d, hd, ⟨e⟩⟩ := isRankThreeL34_iff_index.1 hL
  obtain ⟨Fld, _, hFld, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcard : Nat.card K = 20160 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hFld
  have hAut : Nat.card (MulAut K) = 241920 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hFld
  have hθ : Function.Injective (MulAut.conjNormal (H := K) : X →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 : g * k * g⁻¹ = k := by
        have h3 : ((MulAut.conjNormal g : MulAut K) ⟨k, hk⟩ : X) = g * k * g⁻¹ :=
          MulAut.conjNormal_apply g ⟨k, hk⟩
        rw [← h3, hg]
        rfl
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hC] at hmem
    exact hmem
  have hXdvd : Nat.card X ∣ 12 * 20160 := by
    have := Subgroup.card_dvd_of_injective _ hθ
    rwa [hAut] at this
  have hidx : K.index ∣ 12 := by
    have h1 : K.index * 20160 = Nat.card X := by rw [← hKcard]; exact K.index_mul_card
    rw [← h1] at hXdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hXdvd
  have hrel : K.relIndex F ∣ 12 := (Subgroup.relIndex_dvd_index_of_normal K F).trans hidx
  obtain ⟨n, hn⟩ := hF.index (K.subgroupOf F)
  have hle : 3 ^ n ≤ 3 := by
    have h12 : 3 ^ n ∣ 12 := by
      rw [← hn]
      exact hrel
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num
    · exfalso
      have : 3 ^ 2 ∣ 12 := (pow_dvd_pow 3 h).trans h12
      norm_num at this
  have hcard : Nat.card F = Nat.card (K.subgroupOf F) * (K.subgroupOf F).index :=
    (Subgroup.card_mul_index _).symm
  have hsub : Nat.card (K.subgroupOf F) = Nat.card (F ⊓ K : Subgroup X) := by
    rw [← Subgroup.inf_subgroupOf_left K F]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard, hsub, hn, mul_comm]
  exact Nat.mul_le_mul_right _ hle

theorem kFactL34Three :
    KFactL34Three := by
  intro K _ _ hL T
  obtain ⟨d, hd, ⟨e⟩⟩ := isRankThreeL34_iff_index.1 hL
  obtain ⟨Fld, _, hFld, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hFld
  have hT9 : Nat.card (T : Subgroup K) = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hfK]
  have hT9' : Nat.card (T : Subgroup K) = 9 := by rw [hT9]; norm_num
  have hC8 := kFactL34SylowCentralizer K hL T
  have hE9 : Nat.card ((T : Subgroup K).map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hT9'
  refine ⟨hT9, ?_, ?_, ?_⟩
  · intro z hz
    have hex : ∃ u ∈ (T : Subgroup K), u ≠ 1 := by
      by_contra h
      push Not at h
      have : (T : Subgroup K) = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
      rw [this, Subgroup.card_bot] at hT9'
      norm_num at hT9'
    obtain ⟨u, hu, hu1⟩ := hex
    have hzu : z ∈ Subgroup.centralizer ({u} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hz u hu).symm
    rwa [hC8 u hu hu1] at hzu
  ·
    have hcenter : Subgroup.centralizer (((⊤ : Subgroup K) : Set K)) = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      have hz' : ψ z ∈ Subgroup.center _ := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨w, rfl⟩ := ψ.surjective q
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_centralizer_iff.1 hz w (Subgroup.mem_top w)
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.center_projectiveSL_three_eq_bot
        hFld] at hz'
      have : ψ z = 1 := Subgroup.mem_bot.1 hz'
      exact Subgroup.mem_bot.2 (ψ.injective (by rw [this, map_one]))
    have hEA : CFSG.IsElementaryAbelian 3 ((T : Subgroup K).map ψ.toMonoidHom) :=
      CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine hFld hE9
    have hTea : CFSG.Open.IsElemAbelian 3 (T : Subgroup K) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · have := hEA.toIsMulCommutative.is_comm.comm
          ⟨ψ a, Subgroup.mem_map_of_mem ψ.toMonoidHom a.2⟩
          ⟨ψ b, Subgroup.mem_map_of_mem ψ.toMonoidHom b.2⟩
        apply ψ.injective
        show ψ ((a : K) * b) = ψ ((b : K) * a)
        rw [map_mul, map_mul]
        exact congrArg Subtype.val this
      · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3)
          (A := (T : Subgroup K).map ψ.toMonoidHom) (ψ x)
          (Subgroup.mem_map_of_mem ψ.toMonoidHom hx)
        apply ψ.injective
        simpa [map_pow] using this
    exact CFSG.AGLEmbeddingD2.kFactL34Inner d hd K ⊤ inferInstance hcenter
      ⟨Subgroup.topEquiv.trans e⟩ (T : Subgroup K) hTea hT9 le_top
  · intro u hu hu1 V hV hVN huV
    have hcop : ∀ c : K, c ∈ V → c ∈ (T : Subgroup K) → c = 1 := by
      intro c hcV hcT
      have h1 : orderOf c ∣ 9 := hT9' ▸ Subgroup.orderOf_dvd_natCard _ hcT
      obtain ⟨k, hk⟩ := hV ⟨c, hcV⟩
      have h2 : orderOf c ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have h3 : orderOf c ∣ Nat.gcd 9 (2 ^ k) := Nat.dvd_gcd h1 h2
      have h4 : Nat.gcd 9 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
      rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    refine eq_bot_iff.2 fun v hv => Subgroup.mem_bot.2 ?_
    have hvN : v ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := hVN hv
    have hc1 : v * u * v⁻¹ ∈ (T : Subgroup K) := (Subgroup.mem_normalizer_iff.1 hvN u).1 hu
    have hc2 : u * v⁻¹ * u⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 huV v⁻¹).1 (V.inv_mem hv)
    have hcT : v * u * v⁻¹ * u⁻¹ ∈ (T : Subgroup K) :=
      (T : Subgroup K).mul_mem hc1 ((T : Subgroup K).inv_mem hu)
    have hcV : v * u * v⁻¹ * u⁻¹ ∈ V := by
      have := V.mul_mem hv hc2
      simpa [mul_assoc] using this
    have hcomm : v * u * v⁻¹ * u⁻¹ = 1 := hcop _ hcV hcT
    have hvc : v ∈ Subgroup.centralizer ({u} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : v * u = u * v := by
        calc v * u = (v * u * v⁻¹ * u⁻¹) * (u * v) := by group
          _ = u * v := by rw [hcomm, one_mul]
      exact this
    rw [hC8 u hu hu1] at hvc
    exact hcop v hv hvc

open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
private theorem transitive_eZero {k : Type*} [Field k] (hk : Nat.card k = 4)
    {a b : projectiveSL 3 k} (ha : a ∈ eZero k) (hb : b ∈ eZero k) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)), n * a * n⁻¹ = b := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hA3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hB3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  have hAB : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hF := fP_mem_normalizer hk hu
  have hJ := jP_mem_normalizer hk hu
  have hFA := fP_conj_aP hk hu
  have hFB := fP_conj_bP hk hu
  have hJA := jP_conj_aP hk hu
  have mul_conj : ∀ n y z : projectiveSL 3 k, n * (y * z) * n⁻¹ = (n * y * n⁻¹) * (n * z * n⁻¹) :=
    fun n y z => by group
  have inv_conj : ∀ n y : projectiveSL 3 k, n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ :=
    fun n y => by group
  have hy2 : fP hk hu * (bP * (aP u)⁻¹) * (fP hk hu)⁻¹ = (aP u)⁻¹ * bP⁻¹ := by
    rw [mul_conj, inv_conj, hFA, hFB]
  have hy3 : fP hk hu * ((aP u)⁻¹ * bP⁻¹) * (fP hk hu)⁻¹ = bP⁻¹ * aP u := by
    rw [mul_conj, inv_conj, inv_conj, hFA, hFB, inv_inv]
  have hy4 : fP hk hu * (bP⁻¹ * aP u) * (fP hk hu)⁻¹ = aP u * bP := by
    rw [mul_conj, inv_conj, hFA, hFB, inv_inv]
  have key : ∀ x ∈ eZero k, x ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)), n * aP u * n⁻¹ = x := by
    intro x hx hx1
    obtain ⟨i, j, hi, hj, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
    set f := fP hk hu with hf
    set g := jP hk hu with hg
    interval_cases i <;> interval_cases j
    · simp at hx1
    · exact ⟨f, hF, by simpa using hFA⟩
    · refine ⟨f * f * f, mul_mem (mul_mem hF hF) hF, ?_⟩
      have e : f * f * f * aP u * (f * f * f)⁻¹ = f * (f * (f * aP u * f⁻¹) * f⁻¹) * f⁻¹ := by
        group
      rw [e, hFA, hFB, inv_conj, hFA, sq_eq_inv_of_pow_three hB3]
      simp
    · exact ⟨1, one_mem _, by simp⟩
    · refine ⟨f * f * f * g, mul_mem (mul_mem (mul_mem hF hF) hF) hJ, ?_⟩
      have e : f * f * f * g * aP u * (f * f * f * g)⁻¹ =
          f * (f * (f * (g * aP u * g⁻¹) * f⁻¹) * f⁻¹) * f⁻¹ := by group
      rw [e, hJA, hy2, hy3, hy4]
      simp
    · refine ⟨f * f * g, mul_mem (mul_mem hF hF) hJ, ?_⟩
      have e : f * f * g * aP u * (f * f * g)⁻¹ = f * (f * (g * aP u * g⁻¹) * f⁻¹) * f⁻¹ := by
        group
      rw [e, hJA, hy2, hy3, sq_eq_inv_of_pow_three hB3, pow_one, (hAB.inv_right).eq]
    · refine ⟨f * f, mul_mem hF hF, ?_⟩
      have e : f * f * aP u * (f * f)⁻¹ = f * (f * aP u * f⁻¹) * f⁻¹ := by group
      rw [e, hFA, hFB, sq_eq_inv_of_pow_three hA3]
      simp
    · refine ⟨g, hJ, ?_⟩
      rw [hJA, sq_eq_inv_of_pow_three hA3, pow_one, (hAB.inv_left).eq]
    · refine ⟨f * g, mul_mem hF hJ, ?_⟩
      have e : f * g * aP u * (f * g)⁻¹ = f * (g * aP u * g⁻¹) * f⁻¹ := by group
      rw [e, hJA, hy2, sq_eq_inv_of_pow_three hA3, sq_eq_inv_of_pow_three hB3]
  obtain ⟨na, hna, hna'⟩ := key a ha ha1
  obtain ⟨nb, hnb, hnb'⟩ := key b hb hb1
  refine ⟨nb * na⁻¹, mul_mem hnb (inv_mem hna), ?_⟩
  rw [← hna', ← hnb']
  group

theorem kFactL34SylowTransitive : KFactL34SylowTransitive := by
  intro K _ _ hL S a b ha hb ha1 hb1
  obtain ⟨d, hd, ⟨e⟩⟩ := isRankThreeL34_iff_index.1 hL
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hF
  have hS9 : Nat.card (S : Subgroup K) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfK]
    norm_num
  set E := (S : Subgroup K).map ψ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective]
    exact hS9
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_eq_map_conj_eZero hF hE9
  have hmemE : ∀ h, h ∈ E ↔ g⁻¹ * h * g ∈ CFSG.RankThree.PartTwo.KFacts.L34.eZero F := by
    intro h
    rw [hg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : g⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g)) y * g = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact hy
    · intro h'
      refine ⟨g⁻¹ * h * g, h', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hSE : ∀ h : K, h ∈ (S : Subgroup K) ↔ ψ h ∈ E := by
    intro h
    constructor
    · intro hh
      exact ⟨h, hh, rfl⟩
    · rintro ⟨y, hy, hyh⟩
      rwa [← ψ.injective hyh]
  have hne : ∀ x : K, x ≠ 1 → g⁻¹ * ψ x * g ≠ 1 := by
    intro x hx h
    apply hx
    apply ψ.injective
    rw [map_one]
    calc ψ x = g * (g⁻¹ * ψ x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨m, hm, hmab⟩ := transitive_eZero hF ((hmemE _).1 ((hSE a).1 ha))
    ((hmemE _).1 ((hSE b).1 hb)) (hne a ha1) (hne b hb1)
  refine ⟨ψ.symm (g * m * g⁻¹), ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hSE, hSE, map_mul, map_mul, map_inv, ψ.apply_symm_apply, hmemE, hmemE]
    have hm' := Subgroup.mem_normalizer_iff.1 hm (g⁻¹ * ψ h * g)
    have : g⁻¹ * (g * m * g⁻¹ * ψ h * (g * m * g⁻¹)⁻¹) * g = m * (g⁻¹ * ψ h * g) * m⁻¹ := by
      group
    rw [this]
    exact hm'
  · apply ψ.injective
    rw [map_mul, map_mul, map_inv, ψ.apply_symm_apply]
    calc g * m * g⁻¹ * ψ a * (g * m * g⁻¹)⁻¹ = g * (m * (g⁻¹ * ψ a * g) * m⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * ψ b * g) * g⁻¹ := by rw [hmab]
      _ = ψ b := by group

end CFSG.LocalAnalysis.RankThreeTheoremC
