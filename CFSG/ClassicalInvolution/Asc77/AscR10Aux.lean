module

public import CFSG.ClassicalInvolution.Asc77.AscT3Z2
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

theorem r_pairNormalizers_mono {G : Type} [Group G] {K K' J J' : Subgroup G} (hK : K ≤ K')
    (hJ : J ≤ J') (z j : G) : pairNormalizers K J z j ≤ pairNormalizers K' J' z j := by
  unfold pairNormalizers
  exact sup_le_sup (inf_le_inf_right _ hK) (inf_le_inf_right _ hJ)

theorem fact2_sl2 {m : ℕ} (hm : Odd m) (hm1 : 1 < m) :
    (m ^ 2 * ((m ^ 2) ^ 2 - 1)).factorization 2 = (m * (m ^ 2 - 1)).factorization 2 + 1 := by
  have hm0 : m ≠ 0 := by omega
  have hm2 : 1 < m ^ 2 := by nlinarith
  have e1 : (m ^ 2) ^ 2 - 1 = (m ^ 2 - 1) * (m ^ 2 + 1) := by
    have : (m ^ 2 - 1) * (m ^ 2 + 1) + 1 = (m ^ 2) ^ 2 := by
      have h : 1 ≤ m ^ 2 := by omega
      zify [h]
      ring
    omega
  have hs : m ^ 2 - 1 ≠ 0 := by omega
  have hodd2 : Odd (m ^ 2) := hm.pow
  have hf1 : (m ^ 2).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd2.not_two_dvd_nat
  have hf0 : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat
  have hf2 : (m ^ 2 + 1).factorization 2 = 1 := by
    obtain ⟨a, rfl⟩ := hm
    have : (2 * a + 1) ^ 2 + 1 = 2 * (2 * a ^ 2 + 2 * a + 1) := by ring
    rw [this, Nat.factorization_mul (by norm_num) (by omega)]
    have hodd : Odd (2 * a ^ 2 + 2 * a + 1) := ⟨a ^ 2 + a, by ring⟩
    simp [Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat,
      Nat.Prime.factorization_self Nat.prime_two]
  have hs1 : m ^ 2 + 1 ≠ 0 := by omega
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hX : (m ^ 2) ^ 2 - 1 ≠ 0 := by rw [e1]; exact mul_ne_zero hs hs1
  rw [Nat.factorization_mul hm20 hX, e1, Finsupp.add_apply, hf1, zero_add,
    Nat.factorization_mul hs hs1, Finsupp.add_apply, hf2,
    Nat.factorization_mul hm0 hs, Finsupp.add_apply, hf0, zero_add]

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r_natCard_sylow (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) {e₀ : ℕ}
    (hfe : f = 2 * e₀) (h5 : 5 ≤ p ^ e₀) {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {w : Y}
    (hL : IsClassicalMember p e₀ L w) (P : Sylow 2 ↥L) :
    Nat.card ↥(P : Subgroup ↥L) = 2 ^ (k + 1) := by
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      simp at h5
    · exact h
  have hm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have hq : Nat.card (GaloisField p f) = (p ^ e₀) ^ 2 := by
    rw [GaloisField.card p f (by omega), hfe, ← pow_mul, mul_comm, pow_mul]
  have hmodd : Odd (p ^ e₀) := (Nat.Prime.odd_of_ne_two Fact.out d.branch.odd).pow
  have hm1 : 1 < p ^ e₀ := by omega
  obtain ⟨eL⟩ := hL.nonempty_equiv
  have hPcard : Nat.card ↥(P : Subgroup ↥L) =
      2 ^ (p ^ e₀ * ((p ^ e₀) ^ 2 - 1)).factorization 2 := by
    rw [Uniform.natCard_sylow_eq P, Nat.card_congr eL.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm]
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨zK, hzK⟩ := d.hyp.classical K hK
  obtain ⟨eK⟩ := hzK.nonempty_equiv
  have hRcard : Nat.card ↥R = 2 ^ ((p ^ e₀) ^ 2 * (((p ^ e₀) ^ 2) ^ 2 - 1)).factorization 2 := by
    rw [Uniform.natCard_isSylow2In_eq d.hR, Nat.card_congr eK.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq]
  have hRu : Nat.card ↥R = 2 * Nat.card ↥(K ⊓ W) :=
    Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp d.late_KW d.late_mem_K d.hR
  have hKW : Nat.card ↥(K ⊓ W) = 2 ^ (k + 1) := by rw [← hu, Nat.card_zpowers, huo]
  rw [hRcard, hKW, fact2_sl2 hmodd hm1] at hRu
  have hpow : 2 ^ ((p ^ e₀ * ((p ^ e₀) ^ 2 - 1)).factorization 2 + 1) = 2 ^ (k + 2) := by
    rw [hRu]
    ring
  have := Nat.pow_right_injective (le_refl 2) hpow
  rw [hPcard]
  congr 1
  omega

theorem Std20.r_mem_perfectCore (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) (h9 : p ^ f ≠ 9) {b : G}
    (hb : FieldInv20 S K K' W z t b) {x : G} (hxK : x ∈ K) (hxb : b * x = x * b)
    (hx2 : ∃ j : ℕ, x ^ 2 ^ j = 1) :
    x ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨hbN, -, e₀, eK, g, σ, hfe, hσ2, hσ1, -, hg⟩ := d.x_fieldData c9 h8 hb
  have hp2 : p ≠ 2 := d.branch.odd
  have hq := d.branch.five
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      rw [hfe] at hq
      simp at hq
    · exact h
  have h5 : 5 ≤ p ^ e₀ := by
    have h9' : p ^ (2 * e₀) ≠ 9 := hfe ▸ h9
    exact five_le_pow_of_ne_nine hp2 he₀ h9'
  subst hfe
  have hφ : ∀ x, semilinHom g σ (semilinHom g σ x) = x := by
    intro x
    have h2 : phiG K eK b * phiG K eK b = 1 := by
      rw [← phiG_mul hbN hbN, hb.sq, phiG_one]
    have := congrArg (fun φ : MulAut SL(2, GaloisField p (2 * e₀)) => φ x) h2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [← hg x, ← hg (phiG K eK b x)]
    exact this
  obtain ⟨φ⟩ := factF0 p e₀ hp2 he₀ σ hσ1 hσ2 g hφ
  have hfix : slFix eK ⟨b, hbN⟩ = MonoidHom.eqLocus (semilinHom g σ)
      (MonoidHom.id SL(2, GaloisField p (2 * e₀))) := by
    ext x
    change slAut K eK ⟨b, hbN⟩ x = x ↔ _ = x
    have h1 : slAut K eK ⟨b, hbN⟩ x = phiG K eK b x := by
      rw [phiG_of_mem hbN]
      rfl
    rw [h1, hg x]
  let φ' : ↥(slFix eK ⟨b, hbN⟩) ≃* SL(2, GaloisField p e₀) :=
    (MulEquiv.subgroupCongr hfix).trans φ
  have hcardm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have : Fintype (GaloisField p e₀) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p e₀), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p e₀))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardm]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField p e₀) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p e₀) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect ↥(slFix eK ⟨b, hbN⟩) :=
    Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  set A : Subgroup G := K ⊓ Subgroup.centralizer ({b} : Set G) with hA
  have hxA : x ∈ A := ⟨hxK, Subgroup.mem_centralizer_singleton_iff.mpr hxb.symm⟩
  set a : ↥A := ⟨x, hxA⟩ with ha
  let π : ↥A →* ↥(slFix eK ⟨b, hbN⟩) :=
    ((slProj K eK).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
      change slAut K eK ⟨b, hbN⟩ (slProj K eK (Subgroup.inclusion inf_le_left c)) =
        slProj K eK (Subgroup.inclusion inf_le_left c)
      rw [slAut_slProj]
      congr 1
      apply Subtype.ext
      rw [normalizerConj_apply_coe]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
      change b * c * b⁻¹ = c
      rw [← hc]
      group
  have hπ : ∀ y, ((π y : ↥(slFix eK ⟨b, hbN⟩)) : SL(2, GaloisField p (2 * e₀))) =
      slProj K eK (Subgroup.inclusion inf_le_left y) := fun y => rfl
  have hπsurj : Function.Surjective π := by
    rintro ⟨c, hc⟩
    obtain ⟨y, hyb, hyc⟩ := exists_mem_centralizer_of_slAut_eq eK hbN hb.sq hc
    exact ⟨⟨y, y.2, hyb⟩, Subtype.ext hyc⟩
  have hmap := finite_perfectResidual_surjects_to_perfect_image π hπsurj
  obtain ⟨p₀, hp₀, hp₀e⟩ : ∃ p₀ ∈ Helpers.perfectResidual ↥A, π p₀ = π a := by
    have : π a ∈ (Helpers.perfectResidual ↥A).map π := by
      rw [hmap]
      trivial
    obtain ⟨y, hy, hye⟩ := this
    exact ⟨y, hy, hye⟩
  have hy1 : π (a * p₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hp₀e]
    exact mul_inv_cancel _
  have hyO : (((a * p₀⁻¹ : ↥A)) : G) ∈ oddCoreOf K := by
    have h1 : slProj K eK (Subgroup.inclusion inf_le_left (a * p₀⁻¹)) = 1 := by
      have := congrArg Subtype.val hy1
      rw [hπ] at this
      exact this
    exact (slProj_eq_one_iff eK _).mp h1
  have hPc : (Helpers.perfectResidual ↥A).Characteristic :=
    Helpers.perfectResidual_characteristic
  have hyodd : Odd (orderOf (a * p₀⁻¹)) := by
    have h1 : orderOf (((a * p₀⁻¹ : ↥A)) : G) ∣ Nat.card ↥(oddCoreOf K) :=
      Subgroup.orderOf_dvd_natCard (oddCoreOf K) hyO
    rw [Subgroup.orderOf_coe] at h1
    exact (oddCoreOf_odd_natCard K).of_dvd_nat h1
  obtain ⟨j, hj⟩ := hx2
  have haj : a ^ 2 ^ j = 1 := Subtype.ext hj
  set mkP := QuotientGroup.mk' (Helpers.perfectResidual ↥A) with hmk
  have hp1 : mkP p₀ = 1 := (QuotientGroup.eq_one_iff p₀).mpr hp₀
  have hmka : mkP (a * p₀⁻¹) = mkP a := by
    rw [map_mul, map_inv, hp1, inv_one, mul_one]
  have hd1 : orderOf (mkP a) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, haj, map_one])
  have hd2 : orderOf (mkP a) ∣ orderOf (a * p₀⁻¹) := by
    rw [← hmka]
    exact orderOf_map_dvd mkP _
  have hodd1 : Odd (orderOf (mkP a)) := hyodd.of_dvd_nat hd2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd1
    exact (Nat.not_even_iff_odd.mpr hodd1) ((Nat.even_pow.mpr ⟨even_two, hne⟩))
  have hone : orderOf (mkP a) = 1 := by rw [hi, hi0, pow_zero]
  have ha1 : mkP a = 1 := orderOf_eq_one_iff.mp hone
  have haP : a ∈ Helpers.perfectResidual ↥A := (QuotientGroup.eq_one_iff a).mp ha1
  exact ⟨a, haP, rfl⟩


section AV


theorem Std20.r_exists_c [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    ∃ c : G, c * b = b * c ∧ conjSub c K = J ∧ c * z * c⁻¹ = t := by
  obtain ⟨c₀, hc₀b, hc₀z⟩ := hb.fuse
  obtain ⟨s, hsS, hsK, hsb⟩ := d.z_exists_swap c7 c9 h8 hb
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hsS)
  have hΩ := d.hyp
  have hI := d.viol.hzK
  have hL₁ : IsUniqueInvolution (conjSub c₀ K) t := by
    have := hI.conj c₀
    rwa [hc₀z] at this
  have hJtw : J ∈ twinSet (CoreAssembly.conjClass K) (conjSub c₀ K) :=
    ⟨d.late_mem_J, t, hL₁, d.viol.hzJ⟩
  have h1 := twinSet_conj hΩ.conjInvariant hJtw c₀⁻¹
  rw [conjSub_inv_conjSub, d.twins] at h1
  rcases Set.mem_insert_iff.mp h1 with h | h
  · refine ⟨c₀, hc₀b, ?_, hc₀z⟩
    have := congrArg (conjSub c₀) h
    rw [conjSub_conjSub_inv] at this
    exact this.symm
  · have h' : conjSub c₀⁻¹ J = K' := Set.mem_singleton_iff.mp h
    refine ⟨c₀ * s, ?_, ?_, ?_⟩
    · calc c₀ * s * b = c₀ * (s * b) := by group
        _ = c₀ * (b * s) := by rw [hsb]
        _ = (c₀ * b) * s := by group
        _ = b * c₀ * s := by rw [hc₀b]
        _ = b * (c₀ * s) := by group
    · rw [conjSub_mul, hsK, ← h', conjSub_conjSub_inv]
    · calc c₀ * s * z * (c₀ * s)⁻¹ = c₀ * (s * z * s⁻¹) * c₀⁻¹ := by group
        _ = c₀ * z * c₀⁻¹ := by rw [hsz]; group
        _ = t := hc₀z

theorem Std20.r_v0 [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) :
    ∃ v₀ : G, Subgroup.zpowers v₀ = J ⊓ W ∧ orderOf v₀ = 2 ^ (k + 1) ∧ v₀ ^ 2 ^ k = t ∧
      b * v₀ ^ 2 = v₀ ^ 2 * b := by
  obtain ⟨hbN, -⟩ := d.x_fieldData c9 h8 hb
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, huz, hWgen, huv, hdis⟩ := d.v_W_gen hu huo
  refine ⟨v₀, hv₀, hv₀o, hv₀t, ?_⟩
  have hat : b * t * b⁻¹ = t := by
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [hb.comm_t]
      _ = t := by group
  have hbK : conjSub b K = K := mem_normalizer_iff_conjSub_eq.mp hbN
  obtain ⟨l, hl⟩ := d.y_scalar hu huo hb.mem hbK hat
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hv₀JW : v₀ ∈ J ⊓ W := hv₀ ▸ Subgroup.mem_zpowers v₀
  have h1 : u ^ l = u ^ ((2 : ℤ) ^ k + 1) := by
    rw [← hl u huKW.2, hact u huKW]
  have h2 : (orderOf u : ℤ) ∣ l - ((2 : ℤ) ^ k + 1) := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, mul_inv_cancel]
  rw [huo] at h2
  have h3 : ((2 : ℤ) ^ k) ∣ l - 1 := by
    have h4 : (2 : ℤ) ^ k ∣ (2 : ℤ) ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    have h5 : (2 : ℤ) ^ k ∣ l - ((2 : ℤ) ^ k + 1) := by
      have := h2
      push_cast at this
      exact h4.trans this
    have : l - 1 = (l - ((2 : ℤ) ^ k + 1)) + (2 : ℤ) ^ k := by ring
    rw [this]
    exact dvd_add h5 dvd_rfl
  have hbv : b * v₀ * b⁻¹ = v₀ ^ l := hl v₀ hv₀JW.2
  have hv₀l : v₀ ^ (2 * l) = v₀ ^ 2 := by
    have h6 : (orderOf v₀ : ℤ) ∣ 2 * l - 2 := by
      rw [hv₀o]
      obtain ⟨c, hc⟩ := h3
      refine ⟨c, ?_⟩
      push_cast
      calc 2 * l - 2 = 2 * (l - 1) := by ring
        _ = 2 * ((2 : ℤ) ^ k * c) := by rw [hc]
        _ = (2 : ℤ) ^ (k + 1) * c := by ring
    have h7 := (orderOf_dvd_iff_zpow_eq_one).mp h6
    rw [zpow_sub, mul_inv_eq_one] at h7
    simpa using h7
  have : b * v₀ ^ 2 * b⁻¹ = v₀ ^ 2 := by
    calc b * v₀ ^ 2 * b⁻¹ = (b * v₀ * b⁻¹) ^ 2 := (conj_pow).symm
      _ = (v₀ ^ l) ^ 2 := by rw [hbv]
      _ = v₀ ^ (2 * l) := by rw [← zpow_natCast, ← zpow_mul]; ring_nf
      _ = v₀ ^ 2 := hv₀l
  calc b * v₀ ^ 2 = b * v₀ ^ 2 * b⁻¹ * b := by group
    _ = v₀ ^ 2 * b := by rw [this]

end AV

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
