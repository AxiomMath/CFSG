module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUFrame
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUType
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_of_isSylowTwoIn {P K : Subgroup X} (hP : IsSylowTwoIn P K) : IsPGroup 2 P := by
  obtain ⟨hPK, Q, hQ⟩ := hP
  have h := (Q.isPGroup').map K.subtype
  rwa [hQ, subgroupOf_map_subtype, inf_eq_left.mpr hPK] at h

theorem exists_sylowTwoIn_normalized {K T : Subgroup X} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set X)) :
    ∃ P : Subgroup X, IsSylowTwoIn P K ∧ T ≤ normalizer (P : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMN : K ⊔ T ≤ normalizer (K : Set X) := sup_le le_normalizer hTK
  obtain ⟨U, hU⟩ := (hT.comap_subtype (K := K ⊔ T)).exists_le_sylow
  have hUM : ABGLocalTools.IsSylowOf 2 ((U : Subgroup ↥(K ⊔ T)).map (K ⊔ T).subtype) (K ⊔ T) :=
    ⟨U, rfl⟩
  have hTU : T ≤ (U : Subgroup ↥(K ⊔ T)).map (K ⊔ T).subtype := fun t ht =>
    ⟨⟨t, (le_sup_right : T ≤ K ⊔ T) ht⟩, hU (mem_comap.mpr ht), rfl⟩
  have hP := hUM.inf_of_le_normalizer (le_sup_left : K ≤ K ⊔ T) hMN
  obtain ⟨S', hS'⟩ := hP.exists_sylow_eq_subgroupOf
  refine ⟨_ ⊓ K, ⟨inf_le_right, S', hS'⟩, fun t ht => ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer (hTU ht), hTK ht⟩

omit [Finite X] in
theorem mem_of_isSylowTwoIn_of_central {P K : Subgroup X} (hP : IsSylowTwoIn P K) {b : X}
    (hbK : b ∈ K) (hb : ∀ k ∈ K, k * b = b * k) (hb2 : orderOf b = 2) : b ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, Q, hQ⟩ := hP
  set b' : ↥K := ⟨b, hbK⟩
  have hcen : ∀ g : ↥K, g * b' = b' * g := fun g => Subtype.ext (hb g g.2)
  have hN : (zpowers b').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g (b' ^ m) := (Commute.zpow_right (hcen g) m)
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers b') m
  have h2 : IsPGroup 2 (zpowers b') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hb2, pow_one])
  have hle := h2.le_sylow_of_normal Q
  have hmem : b' ∈ (Q : Subgroup ↥K) := hle (mem_zpowers b')
  rw [hQ, mem_subgroupOf] at hmem
  exact hmem

omit [Finite X] in
theorem isPGroup_sup_zpowers {u w : X} (hu : u * u = 1) (hw : w * w = 1) (huw : u * w = w * u) :
    IsPGroup 2 ↥(zpowers u ⊔ zpowers w) := by
  have hp : ∀ z : X, z * z = 1 → IsPGroup 2 (zpowers z) := by
    intro z hz
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, sq, hz, one_zpow]
  refine IsPGroup.to_sup_of_normal_left' (hp u hu) (hp w hw) ?_
  rw [zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  exact (Commute.zpow_left huw m).eq

section Frame


theorem exists_unitary_candidate
    {K P : Subgroup X} {v y : X}
    (hvN : v ∈ normalizer (K : Set X)) (hyN : y ∈ normalizer (K : Set X))
    (hyP : y ∈ normalizer (P : Set X)) (hy : IsL34Unitary K y) (hvy : v * y = y * v)
    {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K} (hQS : IsQSetting q l)
    (hvq : ∀ e, q (betaHat K hvN e) = r₂ * q e * r₂⁻¹)
    (hT0 : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) :
    ∃ t < 64, ∃ i < 36, candOK t i = true ∧
      ∀ w, (nf l t 0 0)⁻¹ * betaHat K hyN (l (cv w)) * nf l t 0 0 =
        l (cv (substWord (aut i) w)) := by
  obtain ⟨ρ, hρR, hρ⟩ := GrS4.exists_realization_betaHat hyN hQS.qS hQS.qsurj hQS.ker
  have hρN : ∀ τ ∈ T0, ρ * τ * ρ⁻¹ ∈ T0 := by
    intro τ hτ
    obtain ⟨e, rfl⟩ := hQS.qsurj τ (T0_le_S hτ)
    obtain ⟨p, hpP, hpK, rfl⟩ := (hT0 e).mp hτ
    rw [← hρ, betaHat_jq]
    refine (hT0 _).mpr ⟨y⁻¹ * p * y, ?_, _, rfl⟩
    have := (mem_normalizer_iff.mp (inv_mem hyP) p).mp hpP
    rwa [inv_inv] at this
  obtain ⟨i, hi, t, ht, hρeq, hβ⟩ := exists_betaRep hQS hρR hρN hρ
  have hρ2 : ρ * ρ = 1 := realization_mul_self hyN hy.2.1 hQS.qsurj hρR hρ
  have hcomm : ∀ e, betaHat K hyN (betaHat K hvN e) = betaHat K hvN (betaHat K hyN e) := by
    intro e
    obtain ⟨j, rfl⟩ := jq_surjective K e
    rw [betaHat_jq, betaHat_jq, betaHat_jq, betaHat_jq]
    have h : conjJ K hyN (conjJ K hvN j) = conjJ K hvN (conjJ K hyN j) := by
      apply Subtype.ext
      simp only [coe_conjJ]
      calc y⁻¹ * (v⁻¹ * (j : X) * v) * y = (v * y)⁻¹ * j * (v * y) := by group
        _ = (y * v)⁻¹ * j * (y * v) := by rw [hvy]
        _ = v⁻¹ * (y⁻¹ * j * y) * v := by group
    rw [h]
  have hρr : ρ * r₂ = r₂ * ρ := by
    refine GrS4.realization_unique hQS.qsurj (R.mul_mem hρR r₂_mem_R)
      (R.mul_mem r₂_mem_R hρR) (β := fun e => betaHat K hyN (betaHat K hvN e)) (fun e => ?_)
      (fun e => ?_)
    · rw [hρ, hvq]
      group
    · rw [hcomm, hvq, hρ]
      group
  have hcard : Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 :=
    card_centralizer_of_count hyN hQS.qS hQS.qsurj hQS.ker hρ hy.2.2.2
  have hconj := exists_conj_r₄_of_card hρR hρ2 hcard
  subst hρeq
  exact ⟨t, ht, i, hi, candOK_of hi hρR hρ2 hρr hconj, hβ⟩

theorem jq_eq_zz_two {K : Subgroup X} {v b : X} {hvN : v ∈ normalizer (K : Set X)}
    {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K} (hQS : IsQSetting q l)
    (hzz : ∀ c d : ZMod 4, betaHat K hvN (zz l c d) = zz l (c + 3 * d) (3 * d))
    (hinj : ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0) (hbK : b ∈ K)
    (hbcen : ∀ k ∈ K, k * b = b * k) (hb2 : orderOf b = 2) (hvb : v * b = b * v) :
    jq K ⟨b, hbK⟩ = zz l 2 0 := by
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  refine eq_zz_two_of_fixed hQS hzz hinj ?_ ?_ ?_ ?_
  · rw [mem_center_iff]
    intro e
    obtain ⟨k, rfl⟩ := jq_surjective K e
    have hk : k * (⟨b, hbK⟩ : ↥K) = ⟨b, hbK⟩ * k := Subtype.ext (hbcen k k.2)
    rw [← map_mul, ← map_mul, hk]
  · have hc : conjJ K hvN ⟨b, hbK⟩ = ⟨b, hbK⟩ := by
      apply Subtype.ext
      rw [coe_conjJ]
      calc v⁻¹ * b * v = v⁻¹ * (b * v) := by group
        _ = v⁻¹ * (v * b) := by rw [hvb]
        _ = b := by group
    rw [betaHat_jq, hc]
  · have : (⟨b, hbK⟩ : ↥K) * ⟨b, hbK⟩ = 1 := Subtype.ext hbb
    rw [← map_mul, this, map_one]
  · intro h1
    have := L34P.eq_one_of_mem_oddIn_of_pow hbK (k := 1) (by rw [pow_one, pow_two, hbb]) h1
    rw [this, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)

theorem exists_fixed_lift
    {K P : Subgroup X} {v y : X} (hPK : P ≤ K)
    (hP2 : IsPGroup 2 P) (hvN : v ∈ normalizer (K : Set X)) (hyN : y ∈ normalizer (K : Set X))
    (hvP : v ∈ normalizer (P : Set X)) (hyP : y ∈ normalizer (P : Set X))
    {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K} (hQS : IsQSetting q l)
    (hT0 : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e)
    (hvl : ∀ w, betaHat K hvN (l (cv w)) = l (cv (substWord (aut 1) w))) {t i : ℕ}
    (ht : t < 64) (hi : i < 36) (hcand : candOK t i = true)
    (hβ : ∀ w, (nf l t 0 0)⁻¹ * betaHat K hyN (l (cv w)) * nf l t 0 0 =
      l (cv (substWord (aut i) w))) :
    ∃ p ∈ P, p * v = v * p ∧ ∃ h : (p * (y⁻¹ * p * y)) ^ 4 ∈ K,
      jq K ⟨(p * (y⁻¹ * p * y)) ^ 4, h⟩ = zz l 2 0 := by
  obtain ⟨x, hx, hx1, hx2⟩ := exists_sixteen_witness ht hi hcand
  have hk : x.1 < 64 := lt_of_mem_allM hx
  have hxT : q (nfM l x) ∈ T0 := by
    rw [q_nfM hQS hk]
    exact tg_mem_T0 _ hk
  obtain ⟨p, hpP, hpK, hpx⟩ := (hT0 _).mp hxT
  have hvfix : betaHat K hvN (jq K ⟨p, hpK⟩) = jq K ⟨p, hpK⟩ := by
    rw [hpx]
    have h1 : betaHat K hvN (nfM l x) = nfM l (betaRepM 1 x) :=
      beta_nf hQS (by norm_num) hk hvl x.2.1 x.2.2
    rw [h1, hx1]
  have hpv : v⁻¹ * p * v = p := (GrS4.conj_eq_iff_betaHat hPK hP2 hvN hvP hpP).mpr hvfix
  have hp'P : y⁻¹ * p * y ∈ P := by
    have := (mem_normalizer_iff.mp (inv_mem hyP) p).mp hpP
    rwa [inv_inv] at this
  have hp'x : jq K ⟨y⁻¹ * p * y, hPK hp'P⟩ = nfM l (betaYM t i x) := by
    have h1 : betaHat K hyN (jq K ⟨p, hpK⟩) = jq K ⟨y⁻¹ * p * y, hPK hp'P⟩ := by
      rw [betaHat_jq]
      rfl
    rw [← h1, hpx]
    exact betaY_nfM hQS ht hi hβ hk
  have hk' : (betaYM t i x).1 < 64 := betaYM_lt ht hi hk
  have hmk : (mulM x (betaYM t i x)).1 < 64 := mulM_lt hk hk'
  have hmm : (mulM (mulM x (betaYM t i x)) (mulM x (betaYM t i x))).1 < 64 := mulM_lt hmk hmk
  have hpp'P : p * (y⁻¹ * p * y) ∈ P := P.mul_mem hpP hp'P
  have hpp' : jq K ⟨p * (y⁻¹ * p * y), hPK hpp'P⟩ = nfM l (mulM x (betaYM t i x)) := by
    have e1 : (⟨p * (y⁻¹ * p * y), hPK hpp'P⟩ : ↥K) = ⟨p, hpK⟩ * ⟨y⁻¹ * p * y, hPK hp'P⟩ := rfl
    rw [e1, map_mul, hpx, hp'x, nfM_mul hQS hk hk']
  refine ⟨p, hpP, ?_, hPK (P.pow_mem hpp'P 4), ?_⟩
  · calc p * v = v * (v⁻¹ * p * v) := by group
      _ = v * p := by rw [hpv]
  · have e1 : (⟨(p * (y⁻¹ * p * y)) ^ 4, hPK (P.pow_mem hpp'P 4)⟩ : ↥K) =
        (⟨p * (y⁻¹ * p * y), hPK hpp'P⟩ : ↥K) ^ 4 := rfl
    rw [e1, map_pow, hpp']
    have e2 : nfM l (mulM x (betaYM t i x)) ^ 4 = nfM l (pow4X (mulM x (betaYM t i x))) := by
      rw [pow4X, ← nfM_mul hQS hmm hmm, ← nfM_mul hQS hmk hmk]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e2, hx2]
    show l (cv (tw 0)) * zz l 2 0 = zz l 2 0
    have htw : tw 0 = [] := by decide
    rw [htw, show l (cv []) = 1 from map_one l, one_mul]

end Frame

theorem exists_order_sixteen
    {K : Subgroup X} {b v y : X}
    (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (h16 : Nat.card (zStarIn K) = 16 * Nat.card (oddIn K)) (hb2 : orderOf b = 2) (hbK : b ∈ K)
    (hKb : K ≤ centralizer ({b} : Set X)) (hv : HarrisLit.EndB.IsL34Field K v)
    (hy : IsL34Unitary K y) (hvy : v * y = y * v) (hvb : v * b = b * v) (hyb : y * b = b * y) :
    ∃ W : Subgroup X, IsPGroup 2 W ∧ W ≤ centralizer ({b} : Set X) ∧ v ∈ W ∧ y ∈ W ∧
      ∃ r ∈ W, r * v = v * r ∧ r ^ 8 = b := by
  have hvN : v ∈ normalizer (K : Set X) := hv.1
  have hyN : y ∈ normalizer (K : Set X) := hy.1
  have hy2 : y * y = 1 := hy.2.1
  have hT2 : IsPGroup 2 ↥(zpowers v ⊔ zpowers y) := isPGroup_sup_zpowers hv.2.1 hy2 hvy
  have hTK : zpowers v ⊔ zpowers y ≤ normalizer (K : Set X) :=
    sup_le (zpowers_le.mpr hvN) (zpowers_le.mpr hyN)
  obtain ⟨P, hP, hTP⟩ := exists_sylowTwoIn_normalized hT2 hTK
  have hPK : P ≤ K := hP.1
  have hP2 : IsPGroup 2 P := isPGroup_of_isSylowTwoIn hP
  have hvP : v ∈ normalizer (P : Set X) := hTP (mem_sup_left (mem_zpowers v))
  have hyP : y ∈ normalizer (P : Set X) := hTP (mem_sup_right (mem_zpowers y))
  have hbcen : ∀ k ∈ K, k * b = b * k := fun k hk => mem_centralizer_singleton_iff.mp (hKb hk)
  have hbP : b ∈ P := mem_of_isSylowTwoIn_of_central hP hbK hbcen hb2
  obtain ⟨q, l, hQS, hvq, hT0, hvl, hzz, hinj⟩ := exists_field_frame16 hK hL34 hvN hv h16 hP hvP
  obtain ⟨t, ht, i, hi, hcand, hβ⟩ := exists_unitary_candidate hvN hyN hyP hy hvy hQS hvq hT0
  obtain ⟨p, hpP, hpv, h4K, h4⟩ :=
    exists_fixed_lift hPK hP2 hvN hyN hvP hyP hQS hT0 hvl ht hi hcand hβ
  have h4P : (p * (y⁻¹ * p * y)) ^ 4 ∈ P :=
    P.pow_mem (P.mul_mem hpP (by
      have := (mem_normalizer_iff.mp (inv_mem hyP) p).mp hpP
      rwa [inv_inv] at this)) 4
  have hb := jq_eq_zz_two hQS hzz hinj hbK hbcen hb2 hvb
  have h8 : (p * (y⁻¹ * p * y)) ^ 4 = b := eq_of_jq_eq hPK hP2 h4P hbP (h4.trans hb.symm)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  refine ⟨P ⊔ (zpowers v ⊔ zpowers y), IsPGroup.to_sup_of_normal_left' hP2 hT2 hTP, ?_,
    mem_sup_right (mem_sup_left (mem_zpowers v)), mem_sup_right (mem_sup_right (mem_zpowers y)),
    p * y, mul_mem (mem_sup_left hpP) (mem_sup_right (mem_sup_right (mem_zpowers y))), ?_, ?_⟩
  · refine sup_le (hPK.trans hKb) (sup_le ?_ ?_)
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr hvb
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr hyb
  · calc p * y * v = p * (v * y) := by rw [mul_assoc, ← hvy]
      _ = v * (p * y) := by rw [← mul_assoc, hpv, mul_assoc]
  · have hr2 : (p * y) ^ 2 = p * (y⁻¹ * p * y) := by
      rw [hyinv, pow_two]
      simp only [mul_assoc]
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hr2, h8]

end CFSG.ComponentClassification.TBLit.L34FU
