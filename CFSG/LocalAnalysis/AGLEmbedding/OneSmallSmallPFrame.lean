module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem index_le_ncard_fusionSet {N R : Subgroup G} {z : G}
    (hN : N ≤ Subgroup.normalizer (R : Set G)) (hz1 : z ≠ 1)
    (hstab : ∀ n ∈ N, n * z = z * n → n ∈ R) (hRz : ∀ r ∈ R, r * z = z * r) :
    (R.subgroupOf N).index ≤ (fusionSet R z).ncard := by
  have hmem : ∀ n : N, (n : G) * z * (n : G)⁻¹ ∈ fusionSet R z := fun n =>
    ⟨fun h => hz1 (by
      calc z = (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * n := by group
        _ = 1 := by rw [h]; group), n, hN n.2, Subgroup.mem_zpowers _⟩
  let f : N ⧸ R.subgroupOf N → fusionSet R z :=
    Quotient.lift (fun n : N => (⟨(n : G) * z * (n : G)⁻¹, hmem n⟩ : fusionSet R z))
      (fun a b hab => by
        have h : a⁻¹ * b ∈ R.subgroupOf N := QuotientGroup.leftRel_apply.mp hab
        have hr : (a : G)⁻¹ * b ∈ R := by simpa [Subgroup.mem_subgroupOf] using h
        apply Subtype.ext
        have hc := hRz _ hr
        show (a : G) * z * (a : G)⁻¹ = b * z * (b : G)⁻¹
        calc (a : G) * z * (a : G)⁻¹
            = a * (((a : G)⁻¹ * b) * z * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by
              rw [hc]; group
          _ = b * z * (b : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro x y
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : (a : G) * z * (a : G)⁻¹ = b * z * (b : G)⁻¹ := congrArg Subtype.val hab
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have hab' : ((a⁻¹ * b : N) : G) = (a : G)⁻¹ * b := by simp
    rw [hab']
    apply hstab _ (N.mul_mem (N.inv_mem a.2) b.2)
    calc (a : G)⁻¹ * b * z = (a : G)⁻¹ * (b * z * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * (a * z * (a : G)⁻¹) * b := by rw [h1]
      _ = z * ((a : G)⁻¹ * b) := by group
  rw [Subgroup.index, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

theorem card_le_three_mul_of_index_lt_nine {N R : Subgroup G} (hRN : R ≤ N)
    (hNp : IsPGroup 3 N) (hidx : (R.subgroupOf N).index < 9) :
    Nat.card N ≤ 3 * Nat.card R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hNp.index (R.subgroupOf N)
  have hj1 : j ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hcard := Subgroup.card_mul_index (R.subgroupOf N)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv] at hcard
  rw [← hcard, hj]
  interval_cases j
  · simp only [pow_zero, mul_one]; omega
  · simp only [pow_one]; omega

theorem conj_mem_of_mem_normalizer_of_not_mem {P R T : Subgroup G} {z g : G} (hP : IsPGroup 3 P)
    (hzp : orderOf z = 3) (hB0 : ∀ g ∈ P, g * z = z * g → g ∈ R)
    (hZT : ∀ w ∈ fusionSet R z, w ∉ T → w ∈ Subgroup.zpowers z)
    (hgP : g ∈ P) (hgN : g ∈ Subgroup.normalizer (R : Set G)) (hgR : g ∉ R) :
    g * z * g⁻¹ ∈ T := by
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; norm_num at hzp
  by_contra hT
  have hw : g * z * g⁻¹ ∈ fusionSet R z :=
    ⟨fun h => hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group), g, hgN, Subgroup.mem_zpowers _⟩
  have hxz := hZT _ hw hT
  have hxzN : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hxz n
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have hgk : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc := commute_of_mem_normalizer_zpowers_of_pow_prime_pow Nat.prime_three hzp hxzN hgk
  exact hgR (hB0 g hgP hc.eq)

theorem false_of_centralizes_nine {P R T E : Subgroup G} {z y : G} (hP : IsPGroup 3 P)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hRcard : Nat.card R = 27) (hTR : T ≤ R) (hTcard : Nat.card T = 9) (hzT : z ∉ T)
    (hzp : orderOf z = 3) (hB0 : ∀ g ∈ P, g * z = z * g → g ∈ R)
    (hZT : ∀ w ∈ fusionSet R z, w ∉ T → w ∈ Subgroup.zpowers z)
    (hyP : y ∈ P) (hyN : y ∈ Subgroup.normalizer (R : Set G)) (hyR : y ∉ R)
    (hER : E ≤ R) (hEcard : 9 ≤ Nat.card E) (hyE : ∀ e ∈ E, y * e = e * y) : False := by
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : t * h * t⁻¹ = h := by rw [hRcomm t (hTR ht) h (hER hh)]; group
      rw [this]; exact hh
    · intro hh
      have hhR : h ∈ R := by
        have : h = t⁻¹ * (t * h * t⁻¹) * t := by group
        rw [this]
        exact R.mul_mem (R.mul_mem (R.inv_mem (hTR ht)) (hER hh)) (hTR ht)
      have : t * h * t⁻¹ = h := by rw [hRcomm t (hTR ht) h hhR]; group
      rw [← this]; exact hh
  have hcardET := card_sup_mul_card_inf_eq_of_le_normalizer hTE
  have hsup : Nat.card (E ⊔ T : Subgroup G) ≤ 27 :=
    (Subgroup.card_le_of_le (sup_le hER hTR)).trans hRcard.le
  obtain ⟨e, ⟨heE, heT⟩, he1⟩ : ∃ e ∈ (E ⊓ T : Subgroup G), e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : (E ⊓ T : Subgroup G) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot, mul_one, hTcard] at hcardET
    omega
  have hyz : y * z ≠ z * y := fun h => hyR (hB0 y hyP h)
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hy2R : y ^ 2 ∉ R := by
    intro h2
    apply hyR
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have : y = (y ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hyk, one_mul]
    rw [this]; exact R.pow_mem h2 _
  obtain ⟨a, ha⟩ : ∃ a : G, a = y * z * y⁻¹ := ⟨_, rfl⟩
  have haT : a ∈ T := ha ▸ conj_mem_of_mem_normalizer_of_not_mem hP hzp hB0 hZT hyP hyN hyR
  have hbT : y * a * y⁻¹ ∈ T := by
    have h1 := conj_mem_of_mem_normalizer_of_not_mem hP hzp hB0 hZT (P.pow_mem hyP 2)
      (Subgroup.pow_mem _ hyN 2) hy2R
    have h2 : y ^ 2 * z * (y ^ 2)⁻¹ = y * a * y⁻¹ := by rw [ha, pow_two]; group
    rw [← h2]; exact h1
  have hye : y * e * y⁻¹ = e := by rw [hyE e heE]; group
  by_cases hae : a ∈ Subgroup.zpowers e
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hae
    have hfix : y * a * y⁻¹ = a := by rw [← hn, ← conj_zpow, hye]
    apply hyz
    have h3 : y * (y * z * y⁻¹) * y⁻¹ = y * z * y⁻¹ := by rw [← ha]; exact hfix
    have h4 : y * z * y⁻¹ = z := mul_left_cancel (mul_right_cancel h3)
    calc y * z = y * z * y⁻¹ * y := by group
      _ = z * y := by rw [h4]
  · have hexpT : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => hexp t (hTR ht)
    have hce : Commute e a := hRcomm e (hER heE) a (hTR haT)
    set A := commPlane (by norm_num : 0 < 3) hce (hexpT e heT) (hexpT a haT) with hA
    have hAT : A ≤ T := by
      rintro _ ⟨i, j, rfl⟩
      exact T.mul_mem (T.pow_mem heT i) (T.pow_mem haT j)
    have hord : ∀ t ∈ T, t ≠ 1 → orderOf t = 3 := fun t ht ht1 => by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one (hexpT t ht)) with
        h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ht1
      · exact h
    have ha1 : a ≠ 1 := fun h => by
      apply hzT
      have : z = y⁻¹ * a * y := by rw [ha]; group
      rw [this, h, mul_one, inv_mul_cancel]; exact T.one_mem
    have hep := hord e heT he1
    have hap := hord a haT ha1
    have hinf : Subgroup.zpowers e ⊓ Subgroup.zpowers a = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
      by_contra hw1
      exact hae ((Subgroup.zpowers_le.mpr hw.1)
        (mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hap hw.2 hw1))
    have hAcard : 9 ≤ Nat.card A := by
      have h1 := mul_card_le_of_inf_eq_bot (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩ :
        Subgroup.zpowers e ≤ A) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩ :
          Subgroup.zpowers a ≤ A) hinf
      rw [Nat.card_zpowers, Nat.card_zpowers, hep, hap] at h1
      exact h1
    have hAeq : A = T := Subgroup.eq_of_le_of_card_ge hAT (by rw [hTcard]; exact hAcard)
    have hmaps : ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
      intro t ht
      rw [← hAeq] at ht
      obtain ⟨i, j, rfl⟩ := ht
      have : y * (e ^ i * a ^ j) * y⁻¹ = (y * e ^ i * y⁻¹) * (y * a ^ j * y⁻¹) := by group
      rw [this, ← conj_pow, ← conj_pow, hye]
      exact T.mul_mem (T.pow_mem heT i) (T.pow_mem hbT j)
    have hiter : ∀ n : ℕ, ∀ t ∈ T, y ^ n * t * (y ^ n)⁻¹ ∈ T := by
      intro n
      induction n with
      | zero => intro t ht; simpa using ht
      | succ n ih =>
        intro t ht
        have : y ^ (n + 1) * t * (y ^ (n + 1))⁻¹ = y ^ n * (y * t * y⁻¹) * (y ^ n)⁻¹ := by
          rw [pow_succ]; group
        rw [this]
        exact ih _ (hmaps t ht)
    apply hzT
    have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h1 := hiter (3 ^ k - 1) a haT
    have heq : y ^ (3 ^ k - 1) * a * (y ^ (3 ^ k - 1))⁻¹ = z := by
      have h2 : y ^ (3 ^ k - 1) * (y * z * y⁻¹) * (y ^ (3 ^ k - 1))⁻¹ =
          y ^ (3 ^ k - 1 + 1) * z * (y ^ (3 ^ k - 1 + 1))⁻¹ := by
        rw [pow_succ]; group
      rw [ha, h2, Nat.sub_add_cancel hpos, hyk]; group
    rw [heq] at h1; exact h1

theorem pRank_le_three_of_card_le {P : Subgroup G} (hP : Nat.card P ≤ 81)
    (hnc : ¬ ∀ g ∈ P, ∀ h ∈ P, g * h = h * g) : Open.pRank 3 P ≤ 3 := by
  refine csSup_le' ?_
  intro k hk
  obtain ⟨E, hEP, hEab, hEk⟩ := hk
  by_contra hk3
  push Not at hk3
  have h81 : 81 ≤ Nat.card E := by
    rw [hEk]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hEP' : E = P := Subgroup.eq_of_le_of_card_ge hEP (by omega)
  apply hnc
  intro g hg h hh
  rw [← hEP'] at hg hh
  exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)

theorem le_card_of_four_le_pRank {P : Subgroup G} (h4 : 4 ≤ Open.pRank 3 P) :
    81 ≤ Nat.card P := by
  obtain ⟨E, hEP, -, hEk⟩ := PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three P
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ Open.pRank 3 P := Nat.pow_le_pow_right (by norm_num) h4
    _ = Nat.card E := hEk.symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hEP

theorem false_of_frame {P R T : Subgroup G} {z : G} (hP : IsPGroup 3 P) (hRP : R ≤ P)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hRcard : Nat.card R = 27) (hTR : T ≤ R) (hTcard : Nat.card T = 9) (hzR : z ∈ R)
    (hzT : z ∉ T) (hzp : orderOf z = 3) (hB0 : ∀ g ∈ P, g * z = z * g → g ∈ R)
    (hZ : (fusionSet R z).ncard < 9)
    (hZT : ∀ w ∈ fusionSet R z, w ∉ T → w ∈ Subgroup.zpowers z)
    (h4 : 4 ≤ Open.pRank 3 P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; norm_num at hzp
  set N : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hRN : R ≤ N := le_inf hRP Subgroup.le_normalizer
  have hNp : IsPGroup 3 N := hP.to_le inf_le_left
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr => hRcomm r hr z hzR
  have hidx := index_le_ncard_fusionSet (N := N) inf_le_right hz1
    (fun n hn hc => hB0 n hn.1 hc) hRz
  have hNcard : Nat.card N ≤ 81 := by
    have := card_le_three_mul_of_index_lt_nine hRN hNp (hidx.trans_lt hZ)
    rw [hRcard] at this
    omega
  have hPN : P = N := by
    refine eq_of_isPGroup_of_le_of_normalizer hP inf_le_left fun g hgP hgN => ?_
    by_contra hgN'
    have hgR : g ∉ Subgroup.normalizer (R : Set G) := fun h => hgN' ⟨hgP, h⟩
    set R' := R.map (MulAut.conj g).toMonoidHom with hR'
    have hR'N : R' ≤ N := by
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN r).mp (hRN hr)
    have hR'card : Nat.card R' = 27 := by
      rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective, hRcard]
    obtain ⟨y, hyR', hyR⟩ : ∃ y ∈ R', y ∉ R := by
      by_contra h
      push Not at h
      have heq : R' = R := Subgroup.eq_of_le_of_card_ge h (by rw [hRcard, hR'card])
      apply hgR
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        rw [← heq]
        exact ⟨r, hr, rfl⟩
      · intro hr
        rw [← heq] at hr
        obtain ⟨r', hr', hrr⟩ := hr
        have : r' = r := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hrr
          exact mul_left_cancel (mul_right_cancel hrr)
        rw [← this]
        exact hr'
    have hR'R : R' ≤ Subgroup.normalizer (R : Set G) := hR'N.trans inf_le_right
    have hc := card_sup_mul_card_inf_eq_of_le_normalizer hR'R
    have hsup : Nat.card (R ⊔ R' : Subgroup G) ≤ 81 :=
      (Subgroup.card_le_of_le (sup_le hRN hR'N)).trans hNcard
    have hE : 9 ≤ Nat.card (R ⊓ R' : Subgroup G) := by
      rw [hRcard, hR'card] at hc
      by_contra h
      push Not at h
      have : Nat.card (R ⊔ R' : Subgroup G) * Nat.card (R ⊓ R' : Subgroup G) ≤ 81 * 8 :=
        Nat.mul_le_mul hsup (by omega)
      omega
    have hyN := hR'N hyR'
    refine false_of_centralizes_nine hP hRcomm hexp hRcard hTR hTcard hzT hzp hB0 hZT hyN.1
      hyN.2 hyR inf_le_left hE fun e he => ?_
    obtain ⟨r, hr, rfl⟩ := hyR'
    obtain ⟨s, hs, hse⟩ := he.2
    rw [← hse]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * r * g⁻¹ * (g * s * g⁻¹) = g * (r * s) * g⁻¹ := by group
      _ = g * (s * r) * g⁻¹ := by rw [hRcomm r hr s hs]
      _ = g * s * g⁻¹ * (g * r * g⁻¹) := by group
  have hPcard : Nat.card P ≤ 81 := hPN ▸ hNcard
  have hle := pRank_le_three_of_card_le hPcard (fun h => by
    have hPR : P ≤ R := fun g hg => hB0 g hg (h g hg z (hRP hzR))
    have h1 := Subgroup.card_le_of_le hPR
    have h2 := le_card_of_four_le_pRank h4
    omega)
  omega

end CFSG.AGLEmbedding
