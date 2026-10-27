module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open scoped Pointwise

section Abstract

variable {A : Type} [Group A] [Finite A]

theorem exists_three_lift {N : Subgroup A} [N.Normal] {J : Subgroup (A ⧸ N)}
    (hJ : Nat.card J = 3) :
    ∃ j : A, (∃ n : ℕ, j ^ 3 ^ n = 1) ∧ zpowers (QuotientGroup.mk' N j) = J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ1 : J ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hJ
    omega
  obtain ⟨⟨u, huJ⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu3 : orderOf u = 3 := by
    have h1 : orderOf u ∣ 3 := by
      have := orderOf_dvd_natCard (⟨u, huJ⟩ : J)
      rwa [Subgroup.orderOf_mk, hJ] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1'
    · exact h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N u
  obtain ⟨e, m, hm3, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' 3 (by norm_num)
  refine ⟨a ^ m, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  · have hle : zpowers (QuotientGroup.mk' N (a ^ m)) ≤ J := by
      rw [zpowers_le, map_pow]
      exact J.pow_mem huJ m
    have hne : QuotientGroup.mk' N (a ^ m) ≠ 1 := by
      rw [map_pow]
      intro h
      apply hm3
      rw [← hu3]
      exact orderOf_dvd_of_pow_eq_one h
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hJ, Nat.card_zpowers]
    have h1 : orderOf (QuotientGroup.mk' N (a ^ m)) ∣ 3 := by
      rw [← hu3]
      exact orderOf_dvd_of_pow_eq_one (by rw [map_pow, ← pow_mul, mul_comm, pow_mul,
        pow_orderOf_eq_one, one_pow])
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h.ge

omit [Finite A] in
theorem eq_one_of_mul_central {N : Subgroup A} (hN : Odd (Nat.card N)) {t o : A} (ho : o ∈ N)
    (hc : t * o = o * t) {m : ℕ} (ht : t ^ 2 ^ m = 1) (hto : (t * o) ^ 2 ^ m = 1) : o = 1 := by
  have h1 : o ^ 2 ^ m = 1 := by
    rw [(Commute.mul_pow hc), ht, one_mul] at hto
    exact hto
  have h2 : o ^ Nat.card N = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨o, ho⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hcop : Nat.Coprime (2 ^ m) (Nat.card N) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hN)
  have h3 : o ^ Nat.gcd (2 ^ m) (Nat.card N) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem exists_borel_torus (c : L34Cover A) (hNZ : standardComponentOddCore A ≤ center A)
    (T : Sylow 2 A) :
    ∃ j : A, (∃ n : ℕ, j ^ 3 ^ n = 1) ∧ j ∈ normalizer ((T : Subgroup A) : Set A) ∧
      (∀ z ∈ centerIn (T : Subgroup A), j * z = z * j → z ∈ center A) ∧
      ∀ y ∈ normalizer ((T : Subgroup A) : Set A), ∃ t ∈ (T : Subgroup A), ∃ k : ℕ,
        ∃ w ∈ center A, y = t * j ^ k * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N
  set S : Sylow 2 (A ⧸ N) := T.mapSurjective (QuotientGroup.mk'_surjective N)
  have hS : (S : Subgroup (A ⧸ N)) = (T : Subgroup A).map p := Sylow.coe_mapSurjective _ _
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers
    c.card_k c.π c.surj c.ker_le_center c.elem
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (A ⧸ N) S₀ S
  set π' := c.π.comp (MulAut.conj x⁻¹).toMonoidHom
  have hker' : π'.ker = c.π.ker := by
    ext y
    simp only [π', MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker]
    constructor
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x
      simpa [mul_assoc] using this
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x⁻¹
      simpa [mul_assoc] using this
  have hsurj' : Function.Surjective π' := c.surj.comp (MulAut.conj x⁻¹).surjective
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  have hT' : (projUnip c.k).comap π' = (S : Subgroup (A ⧸ N)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀]
    ext y
    rw [mem_pointwise_smul_iff_inv_smul_mem, mem_comap, mem_comap]
    simp [π', MulAut.smul_def]
  obtain ⟨-, -, -, -, -, hcenter, -, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ, -, -, hσ, -⟩, -⟩ := hlevi 0
  obtain ⟨-, ⟨hJ3, -, hTJ, -, -, -, -, -, -, -, -, -, -, -, -, -, hZJ, -⟩, -⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ hσ
  set J := (sl2Torus c.k).map σ
  set Tb := (projUnip c.k).comap π'
  have hTb : Tb = (T : Subgroup A).map p := hT'.trans hS
  have hJN : J ≤ normalizer (Tb : Set (A ⧸ N)) := hTJ ▸ le_sup_right
  obtain ⟨j, hj3, hjJ⟩ := exists_three_lift (N := N) hJ3
  have hpjJ : p j ∈ J := hjJ ▸ mem_zpowers (p j)
  have hlift : ∀ y : A, p y ∈ Tb → ∃ t ∈ (T : Subgroup A), t⁻¹ * y ∈ N := by
    intro y hy
    rw [hTb] at hy
    obtain ⟨t, htT, ht⟩ := hy
    exact ⟨t, htT, QuotientGroup.eq.mp ht⟩
  have hTexp : ∀ t ∈ (T : Subgroup A), t ^ 2 ^ (Nat.card A).factorization 2 = 1 := by
    intro t ht
    rw [← T.card_eq_multiplicity]
    have h := congrArg Subtype.val (pow_card_eq_one' (G := (T : Subgroup A)) (x := ⟨t, ht⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  refine ⟨j, hj3, ?_, ?_, ?_⟩
  ·
    apply mem_normalizer_fintype
    intro u hu
    have hpu : p (j * u * j⁻¹) ∈ Tb := by
      rw [map_mul, map_mul, map_inv]
      have h1 : p u ∈ Tb := hTb ▸ ⟨u, hu, rfl⟩
      exact (mem_normalizer_iff.mp (hJN hpjJ) (p u)).mp h1
    obtain ⟨t, htT, hto⟩ := hlift _ hpu
    have hoZ : t⁻¹ * (j * u * j⁻¹) ∈ center A := hNZ hto
    have hc : t * (t⁻¹ * (j * u * j⁻¹)) = (t⁻¹ * (j * u * j⁻¹)) * t :=
      mem_center_iff.mp hoZ t
    have h1 := eq_one_of_mul_central hN hto hc (hTexp t htT) (by
      rw [mul_inv_cancel_left, conj_pow, hTexp u hu, mul_one, mul_inv_cancel])
    have h2 : j * u * j⁻¹ = t := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    rw [SetLike.mem_coe, h2]
    exact htT
  ·
    intro z hz hjz
    have hzT : z ∈ (T : Subgroup A) := hz.1
    have hpzZ : p z ∈ (projCenterW c.k).comap π' := by
      rw [← hcenter]
      refine ⟨⟨p z, hTb ▸ ⟨z, hzT, rfl⟩⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      rintro ⟨y, hy⟩
      obtain ⟨s, hs, rfl⟩ : y ∈ (T : Subgroup A).map p := hTb ▸ hy
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hz.2 s hs]
    have hpzJ : p z ∈ centralizer (J : Set (A ⧸ N)) := by
      rw [← hjJ, mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      have hcomm : Commute (p j) (p z) := by
        show p j * p z = p z * p j
        rw [← map_mul, ← map_mul, hjz]
      exact (hcomm.zpow_left k).eq
    have hker : p z ∈ c.π.ker := hker' ▸ hZJ ▸ ⟨hpzZ, hpzJ⟩
    rw [c.ker_eq] at hker
    obtain ⟨w, hw, hwz⟩ := hker
    have hwN : w⁻¹ * z ∈ N := QuotientGroup.eq.mp hwz
    have : z = w * (w⁻¹ * z) := by group
    rw [this]
    exact mul_mem hw (hNZ hwN)
  ·
    intro y hy
    have hpy : p y ∈ normalizer (Tb : Set (A ⧸ N)) := by
      rw [hTb]
      exact le_normalizer_map p ⟨y, hy, rfl⟩
    rw [← hTJ] at hpy
    have hpy' : p y ∈ ((Tb : Set (A ⧸ N)) * (J : Set (A ⧸ N))) := by
      rw [← coe_mul_of_right_le_normalizer_left Tb J hJN]
      exact hpy
    obtain ⟨tb, htb, jb, hjb, hy'⟩ := hpy'
    obtain ⟨t, htT, rfl⟩ : tb ∈ (T : Subgroup A).map p := hTb ▸ htb
    rw [← hjJ, SetLike.mem_coe, ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hjb
    obtain ⟨k, rfl⟩ := hjb
    refine ⟨t, htT, k, (t * j ^ k)⁻¹ * y, hNZ (QuotientGroup.eq.mp ?_), by group⟩
    show p (t * j ^ k) = p y
    rw [map_mul, map_pow]
    exact hy'

end Abstract

section Frame

open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_torus_frame (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) :
    ∃ j ∈ A, (∃ n : ℕ, j ^ 3 ^ n = 1) ∧ j ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ∧
      (∀ v ∈ E ⊓ F, j * v = v * j → v ∈ R) ∧
      ∀ y ∈ A, y ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) → ∃ k : ℕ, ∀ v ∈ E ⊓ F,
        y⁻¹ * v * y = (j ^ k)⁻¹ * v * j ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  have hNZ := oddCore_le_center hstd.1.1 hstd.1.2
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRV : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  have hEF : E ⊔ F ≤ A ⊔ R := sup_le hF.E_le hF.F_le
  have hREF : R ≤ E ⊔ F := hF.R_le_E.trans le_sup_left
  have hVEF : E ⊓ F ≤ E ⊔ F := inf_le_left.trans le_sup_left
  have hVc : ∀ v ∈ E ⊓ F, ∀ e ∈ E ⊔ F, v * e = e * v := by
    intro v hv e he
    rw [hF.inf_eq_center] at hv
    exact (mem_centralizer_iff.mp hv.2 e he).symm
  have hTsyl : IsSylowOf 2 ((E ⊔ F) ⊓ A) A :=
    hF.sylow.inf_of_le_normalizer le_sup_left (sup_le_normalizer_left hRA)
  obtain ⟨T, hT⟩ := hTsyl
  have hmemT : ∀ a : A, a ∈ (T : Subgroup A) ↔ (a : G) ∈ (E ⊔ F) ⊓ A := by
    intro a
    rw [← hT]
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hba⟩
      rwa [show b = a from Subtype.ext hba] at hb
  obtain ⟨j₀, hj3, hjN, hjC, hjB⟩ := exists_borel_torus c hNZ T
  have hcomR : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := fun a ha r hr =>
    mem_centralizer_iff.mp (hRA hr) a ha
  have hjEF : (j₀ : G) ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) := by
    apply mem_normalizer_fintype
    intro e he
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hREF hEF he
    have haT : (⟨a, ha.2⟩ : A) ∈ (T : Subgroup A) := (hmemT _).mpr ha
    have h1 := (mem_normalizer_iff.mp hjN ⟨a, ha.2⟩).mp haT
    rw [hmemT] at h1
    have h2 : (j₀ : G) * (a * r) * (j₀ : G)⁻¹ = ((j₀ : G) * a * (j₀ : G)⁻¹) * r := by
      have hjr := hcomR _ j₀.2 r hr
      calc (j₀ : G) * (a * r) * (j₀ : G)⁻¹ = (j₀ : G) * a * (r * (j₀ : G)⁻¹) := by group
        _ = (j₀ : G) * a * ((j₀ : G)⁻¹ * r) := by
          rw [show r * (j₀ : G)⁻¹ = (j₀ : G)⁻¹ * r from by
            have := hcomR _ (A.inv_mem j₀.2) r hr
            exact this.symm]
        _ = ((j₀ : G) * a * (j₀ : G)⁻¹) * r := by group
    rw [SetLike.mem_coe, h2]
    exact mul_mem h1.1 (hREF hr)
  have hdec : ∀ v ∈ E ⊓ F, ∃ a : A, a ∈ centerIn (T : Subgroup A) ∧ (a : G) ∈ E ⊓ F ∧
      ∃ r ∈ R, v = (a : G) * r := by
    intro v hv
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hREF hEF (hVEF hv)
    have haV : a ∈ E ⊓ F := by
      have := (E ⊓ F).mul_mem hv ((E ⊓ F).inv_mem (hRV hr))
      rwa [mul_inv_cancel_right] at this
    refine ⟨⟨a, (mem_inf.mp ha).2⟩, ⟨(hmemT _).mpr ha, ?_⟩, haV, r, hr, rfl⟩
    show (⟨a, (mem_inf.mp ha).2⟩ : A) ∈ centralizer ((T : Subgroup A) : Set A)
    rw [mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    exact (hVc a haV s ((hmemT s).mp hs).1).symm
  refine ⟨j₀, j₀.2, ?_, hjEF, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hj3
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  ·
    intro v hv hjv
    obtain ⟨a, haZ, haV, r, hr, rfl⟩ := hdec v hv
    have hjr := hcomR _ j₀.2 r hr
    have hja : (j₀ : G) * a = a * j₀ := by
      have h1 : (j₀ : G) * a * r = a * j₀ * r := by
        calc (j₀ : G) * a * r = (j₀ : G) * (a * r) := by group
          _ = a * r * j₀ := hjv
          _ = a * (r * j₀) := by group
          _ = a * j₀ * r := by rw [← hjr]; group
      exact mul_right_cancel h1
    have haZA := hjC a haZ (Subtype.ext hja)
    have haK : (a : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (mem_center_iff.mp haZA ⟨b, hb⟩)
    have ha2 : IsPGroup 2 (zpowers (a : G)) :=
      (isPGroup_two_of_isElemAbelian hF.elemE).to_le (zpowers_le.mpr haV.1)
    exact mul_mem (mem_of_mem_centralizer_of_isPGroup hF.sylowR a.2 haK ha2) hr
  ·
    intro y hyA hyN
    have hyT : (⟨y, hyA⟩ : A) ∈ normalizer ((T : Subgroup A) : Set A) := by
      apply mem_normalizer_fintype
      intro t ht
      rw [SetLike.mem_coe, hmemT] at ht ⊢
      refine ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp hyN t).mp (mem_inf.mp ht).1
      · exact A.mul_mem (A.mul_mem hyA (mem_inf.mp ht).2) (A.inv_mem hyA)
    obtain ⟨t₀, ht₀, k, w, hw, hy⟩ := hjB _ hyT
    have hy' : y = (t₀ : G) * (j₀ : G) ^ k * w := by
      have := congrArg Subtype.val hy
      simpa using this
    refine ⟨k, fun v hv => ?_⟩
    have ht₀v : (t₀ : G) * v = v * t₀ := (hVc v hv _ ((hmemT _).mp ht₀).1).symm
    have hjk : ((j₀ : G) ^ k)⁻¹ ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
      (normalizer _).inv_mem ((normalizer _).pow_mem hjEF k)
    have hu : ((j₀ : G) ^ k)⁻¹ * v * ((j₀ : G) ^ k)⁻¹⁻¹ ∈ E ⊔ F :=
      (mem_normalizer_iff.mp hjk v).mp (hVEF hv)
    rw [inv_inv] at hu
    have hwc : ∀ e ∈ E ⊔ F, (w : G) * e = e * w := by
      intro e he
      obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hREF hEF he
      have h1 : (w : G) * a = a * w := congrArg Subtype.val (mem_center_iff.mp hw ⟨a, ha.2⟩).symm
      have h2 : (w : G) * r = r * w := hcomR _ w.2 r hr
      calc (w : G) * (a * r) = (w * a) * r := by group
        _ = a * (w * r) := by rw [h1]; group
        _ = a * r * w := by rw [h2]; group
    rw [hy']
    calc ((t₀ : G) * (j₀ : G) ^ k * w)⁻¹ * v * ((t₀ : G) * (j₀ : G) ^ k * w)
        = (w : G)⁻¹ * (((j₀ : G) ^ k)⁻¹ * ((t₀ : G)⁻¹ * (t₀ * v)) * (j₀ : G) ^ k) * w := by
          rw [ht₀v]; group
      _ = (w : G)⁻¹ * (((j₀ : G) ^ k)⁻¹ * v * (j₀ : G) ^ k) * w := by group
      _ = ((j₀ : G) ^ k)⁻¹ * v * (j₀ : G) ^ k := by
          rw [mul_assoc, ← hwc _ hu, ← mul_assoc, inv_mul_cancel, one_mul]

end Frame

end CFSG.ComponentClassification.AS81
