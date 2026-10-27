module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PFrame
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFieldStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB
public import Certificates.Certificate23200
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModelBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open scoped MatrixGroups

theorem l34pFieldParts :
    alphaZOK = true ∧ ∀ k < 64, wordPerm (tg k) * r₂ = r₂ * wordPerm (tg k) →
      fourthM k = (0, 0, 0) ∨ fourthM k = (0, 2, 0) := by
  have h := Certificates.certificate23200
  rw [l34pFieldOK, Bool.and_eq_true] at h
  refine ⟨h.1, fun k hk hc => ?_⟩
  have h2 := h.2
  rw [fourthOK, allBelow_eq_true] at h2
  have h3 := h2 k hk
  have hcb : (comp 42 (wordTab (tg k)) r₂T == comp 42 r₂T (wordTab (tg k))) = true :=
    (((tabRep_wordTab _).comp tabRep_r₂).beq_iff (tabRep_r₂.comp (tabRep_wordTab _))).2 hc
  rw [hcb, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h3
  exact h3

theorem alphaZ_r₂ :
    (alphaEntry 1 64).2.1 = 1 ∧ (alphaEntry 1 64).2.2.1 = 0 ∧ (alphaEntry 1 65).2.1 = 3 ∧
      (alphaEntry 1 65).2.2.1 = 3 := by
  have h := l34pFieldParts.1
  simp only [alphaZOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem repPerm_one : repPerm 1 = r₂ := by
  simp [repPerm, rPerm, realRepWords, genR, r₂]

theorem exists_two_zero : ∀ c d : ZMod 4, ¬ (c = 0 ∧ d = 0) →
    ∃ m n : ZMod 4, m * c + n * (c + 3 * d) = 2 ∧ m * d + n * (3 * d) = 0 := by
  decide

theorem factorization_336_two : (336 : ℕ).factorization 2 = 4 := by
  have hprod : (336 : ℕ) = 2 ^ 4 * 21 := by norm_num
  rw [hprod, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]
  rfl

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem not_mem_withKernel_of_outer {K : Subgroup X} {x : X}
    (hxN : x ∈ normalizer (K : Set X)) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) {ρ : Equiv.Perm (Fin 42)}
    (hρR : ρ ∈ R) (hρS : ρ ∉ S) (hβ : ∀ e, q (betaHat K hxN e) = ρ * q e * ρ⁻¹) :
    x ∉ withKernel K := by
  intro hx
  obtain ⟨e₀, he₀⟩ := exists_inner hx hxN
  have hc : q e₀ * ρ ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_,
      R.mul_mem (S_le_R (hqS e₀)) hρR⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have h1 := hβ e
    rw [he₀ e, map_mul, map_mul, map_inv] at h1
    calc q e * (q e₀ * ρ) = q e₀ * ((q e₀)⁻¹ * q e * q e₀) * ρ := by group
      _ = q e₀ * (ρ * q e * ρ⁻¹) * ρ := by rw [h1]
      _ = q e₀ * ρ * q e := by group
  rw [centralizer_S_inf_R, mem_bot] at hc
  exact hρS (eq_inv_of_mul_eq_one_right hc ▸ S.inv_mem (hqS e₀))

theorem isL34Field_of_frame {K : Subgroup X} {β : X}
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat K))
    (hβ : ∀ e, q (betaHat K hβN e) = r₂ * q e * r₂⁻¹) : HarrisLit.EndB.IsL34Field K β := by
  refine ⟨hβN, hβ2, not_mem_withKernel_of_outer hβN hqS hqsurj r₂_mem_R not_mem_S_r₂ hβ, ?_⟩
  rw [card_set_eq_of_realization hβN hqS hqsurj hqker hβ]
  exact congrArg (· * Nat.card (zStarIn K)) card_C₂

theorem card_eq_seven_of_field {K L : Subgroup X} (hLK : L ≤ K)
    (hL : ⁅L, L⁆ = L) {β : X} (hβN : β ∈ normalizer (K : Set X))
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    {q : Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqker : q.ker = center (Jhat K))
    (hβ : ∀ e, q (betaHat K hβN e) = r₂ * q e * r₂⁻¹) : Nat.card F = 7 := by
  have h3 : 3 ≤ Nat.card F := by
    have h1 := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hne3 : Nat.card F ≠ 3 := card_ne_three_of_isPerfect (isPerfect_sl2 hL e)
  have h1 := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) e
    q hqker
  have h2 : Nat.card (imageHom hLK q).range ∣ 168 := by
    rw [← card_C₂]
    exact Subgroup.card_dvd_of_le (range_imageHom_le hLK hβN hLβ hqS hβ)
  rw [card_sl2] at h1
  exact eq_seven_of_dvd hodd h3 hne3 (h1.trans (mul_dvd_mul_left 2 h2))

theorem exists_pow_four_not_mem {L : Subgroup X} {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) (Q : Sylow 2 ↥L) :
    ∃ s ∈ (Q : Subgroup ↥L), s ^ 4 ∉ pPrimeCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥L →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card F) := by rw [h7]; decide
  obtain ⟨n, hn3, ⟨φ⟩⟩ :=
    CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd (Q.mapSurjective hπs)
  have hcard : Nat.card ((Q.mapSurjective hπs : Sylow 2 SL(2, F)) : Subgroup SL(2, F)) = 16 := by
    rw [Sylow.card_eq_multiplicity, card_sl2, h7,
      show (7 : ℕ) * (7 ^ 2 - 1) = 336 from rfl, factorization_336_two]
    rfl
  have hQcard : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 4 * 2 ^ (n - 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hm : 2 ^ (n - 2) = 2 ^ 2 := by
    have := Nat.card_congr φ.toEquiv
    omega
  have hn : n = 4 := by
    have := Nat.pow_right_injective (le_refl 2) hm
    omega
  subst hn
  have hne : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (4 - 2))) ^ 4 ≠ 1 := by decide
  have hy : (φ.symm (QuaternionGroup.a 1) : SL(2, F)) ∈ (Q : Subgroup ↥L).map π := by
    rw [← Sylow.coe_mapSurjective hπs]
    exact (φ.symm (QuaternionGroup.a 1)).2
  obtain ⟨s, hs, hsy⟩ := hy
  refine ⟨s, hs, fun h => hne ?_⟩
  have h1 : π (s ^ 4) = 1 := by
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr h,
      map_one]
  rw [map_pow, hsy] at h1
  have h2 : (φ.symm (QuaternionGroup.a 1)) ^ 4 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h1
  have h3 := congrArg φ h2
  rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h3

theorem exists_invariant_sylowTwoIn {K Qx : Subgroup X} {β : X}
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hQK : Qx ≤ K) (hQ : IsPGroup 2 Qx)
    (hQβ : Qx ≤ centralizer ({β} : Set X)) :
    ∃ P : Subgroup X, IsSylowTwoIn P K ∧ Qx ≤ P ∧ β ∈ normalizer (P : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (zpowers β) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, sq, hβ2, one_zpow]
  have hβc : β ∈ centralizer (Qx : Set X) :=
    mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hQβ hy)
  have hnorm : zpowers β ≤ normalizer (Qx : Set X) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hβc)
  have hQT : IsPGroup 2 (Qx ⊔ zpowers β : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hQ hT hnorm
  have hTK : Qx ⊔ zpowers β ≤ normalizer (K : Set X) :=
    sup_le (hQK.trans le_normalizer) (zpowers_le.mpr hβN)
  have hMN : K ⊔ (Qx ⊔ zpowers β) ≤ normalizer (K : Set X) := sup_le le_normalizer hTK
  obtain ⟨U, hU⟩ := (hQT.comap_subtype (K := K ⊔ (Qx ⊔ zpowers β))).exists_le_sylow
  have hUM : ABGLocalTools.IsSylowOf 2 ((U : Subgroup ↥(K ⊔ (Qx ⊔ zpowers β))).map
      (K ⊔ (Qx ⊔ zpowers β)).subtype) (K ⊔ (Qx ⊔ zpowers β)) := ⟨U, rfl⟩
  have hTU : Qx ⊔ zpowers β ≤ (U : Subgroup ↥(K ⊔ (Qx ⊔ zpowers β))).map
      (K ⊔ (Qx ⊔ zpowers β)).subtype := fun t ht =>
    ⟨⟨t, (le_sup_right : Qx ⊔ zpowers β ≤ K ⊔ (Qx ⊔ zpowers β)) ht⟩, hU (mem_comap.mpr ht), rfl⟩
  have hP := hUM.inf_of_le_normalizer (le_sup_left : K ≤ K ⊔ (Qx ⊔ zpowers β)) hMN
  obtain ⟨S', hS'⟩ := hP.exists_sylow_eq_subgroupOf
  refine ⟨_ ⊓ K, ⟨inf_le_right, S', hS'⟩, le_inf (le_sup_left.trans hTU) hQK, ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer (hTU (mem_sup_right (mem_zpowers β))), hβN⟩

theorem exists_field_frame
    {β : X} {K L : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    (hfield : HarrisLit.EndB.IsL34Field K β) :
    ∃ (q : Jhat K →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat K), IsQSetting q l ∧
      (∀ e, q (betaHat K hβN e) = r₂ * q e * r₂⁻¹) ∧
      (∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d)) ∧
      ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0 := by
  obtain ⟨-, -, hβK, hcount⟩ := hfield
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  obtain ⟨s, hsQ, hs4⟩ := exists_pow_four_not_mem h7 e Q
  set Qx : Subgroup X := (Q : Subgroup ↥L).map L.subtype with hQx
  have hQxK : Qx ≤ K := by
    rintro _ ⟨u, -, rfl⟩
    exact hLK u.2
  have hQx2 : IsPGroup 2 Qx := (Q.isPGroup').map L.subtype
  have hQxβ : Qx ≤ centralizer ({β} : Set X) := by
    rintro _ ⟨u, -, rfl⟩
    exact hLβ u.2
  obtain ⟨P, hP, hQP, hβP⟩ := exists_invariant_sylowTwoIn hβN hβ2 hQxK hQx2 hQxβ
  obtain ⟨q, l, hQS, hβq, hT0⟩ := exists_field_standard hK hL34 hβN hβ2 hβK hcount hP hβP
  set x : Jhat K := jq K ⟨s, hLK s.2⟩ with hx
  have hxT : q x ∈ T0 := (hT0 x).2 ⟨s, hQP ⟨s, hsQ, rfl⟩, hLK s.2, rfl⟩
  have hxr : q x * r₂ = r₂ * q x := by
    have hfix : betaHat K hβN x = x := by
      rw [hx, betaHat_mk]
      congr 1
      exact Subtype.ext (conj_eq_of_mem_centralizer (hLβ s.2))
    have h1 := hβq x
    rw [hfix] at h1
    calc q x * r₂ = r₂ * q x * r₂⁻¹ * r₂ := by rw [← h1]
      _ = r₂ * q x := by group
  have hx4 : x ^ 4 ≠ 1 := by
    intro h
    have hmem : ((s ^ 4 : ↥L) : X) ∈ Qx := ⟨s ^ 4, (Q : Subgroup ↥L).pow_mem hsQ 4, rfl⟩
    have h' : jq K ⟨((s ^ 4 : ↥L) : X), hQxK hmem⟩ = 1 := by
      rw [← h, hx, ← map_pow]
      rfl
    have h1 := eq_one_of_jq_eq_one hQxK hQx2 hmem h'
    exact hs4 ((Subtype.ext h1 : s ^ 4 = 1) ▸ one_mem _)
  obtain ⟨k, hk, i, j, hxe⟩ := exists_nf hQS hxT
  have hkr : wordPerm (tg k) * r₂ = r₂ * wordPerm (tg k) := by
    rw [← q_nf hQS hk i j, ← hxe]
    exact hxr
  have hx4' : x ^ 4 = nfM l (fourthM k) := by
    have hk0 : nf l k i j = nf l k 0 0 * zz l i j := by
      rw [nf, nf, zz_zero, mul_one]
    have hc : Commute (nf l k 0 0) (zz l i j) := (zz_comm hQS i j _)
    have hz4 : zz l i j ^ 4 = 1 := by
      rw [zz_pow]
      have h4 : ((4 : ℕ) : ZMod 4) = 0 := by decide
      rw [h4, zero_mul, zero_mul, zz_zero]
    have hlt : ((k, 0, 0) : MElt).1 < 64 := hk
    have hlt2 : (mulM (k, 0, 0) (k, 0, 0)).1 < 64 := mulM_lt hlt hlt
    have hp4 : ∀ y : Jhat K, y ^ 4 = (y * y) * (y * y) := fun y => by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [hxe, hk0, hc.mul_pow, hz4, mul_one, hp4,
      show nf l k 0 0 = nfM l ((k, 0, 0) : MElt) from rfl, nfM_mul hQS hlt hlt,
      nfM_mul hQS hlt2 hlt2]
    rfl
  have hz2 : zz l 2 0 ≠ 1 := by
    rcases l34pFieldParts.2 k hk hkr with h0 | h2
    · exfalso
      apply hx4
      rw [hx4', h0]
      exact nf_zero
    · intro hz
      apply hx4
      rw [hx4', h2]
      show nf l 0 2 0 = 1
      have htw : tw 0 = [] := by decide
      rw [nf, htw, hz]
      simp only [mul_one]
      exact map_one l
  have hβl : ∀ w, betaHat K hβN (l (cv w)) = l (cv (substWord (aut 1) w)) :=
    beta_cv_of hQS.ker_le hQS.ql (fun e => by rw [repPerm_one]; exact hβq e)
      (abPerm_uA (by norm_num)) (abPerm_uB (by norm_num))
  obtain ⟨a1, a2, a3, a4⟩ := alphaZ_r₂
  have hzz : ∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d) := by
    intro c d
    rw [beta_zz hQS (by norm_num) hβl, a1, a2, a3, a4]
    congr 1 <;> push_cast <;> ring
  have hinj : ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0 := by
    intro c d hcd
    by_contra hne
    have h2 : zz l (c + 3 * d) (3 * d) = 1 := by rw [← hzz, hcd, map_one]
    obtain ⟨m, n, hm1, hm2⟩ := exists_two_zero c d hne
    apply hz2
    calc zz l 2 0 = zz l (m * c + n * (c + 3 * d)) (m * d + n * (3 * d)) := by rw [hm1, hm2]
      _ = zz l c d ^ m.val * zz l (c + 3 * d) (3 * d) ^ n.val := by
        rw [zz_pow, zz_pow, zz_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = 1 := by rw [hcd, h2, one_pow, one_pow, one_mul]
  exact ⟨q, l, hQS, hβq, hzz, hinj⟩

theorem card_zStarIn_of_field
    {β : X} {K L : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    (hfield : HarrisLit.EndB.IsL34Field K β) :
    Nat.card (zStarIn K) = 16 * Nat.card (oddIn K) := by
  obtain ⟨q, l, hQS, -, -, hinj⟩ :=
    exists_field_frame hK hL34 hβN hβ2 hLK hLβ h7 e hfield
  have hmem : ∀ c d : ZMod 4, zz l c d ∈ center (Jhat K) := fun c d => by
    rw [← hQS.ker]
    exact zz_mem_ker hQS c d
  set f : ZMod 4 × ZMod 4 → center (Jhat K) := fun c => ⟨zz l c.1 c.2, hmem c.1 c.2⟩ with hf
  have hfinj : Function.Injective f := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have h1 : zz l c d = zz l c' d' := congrArg Subtype.val h
    have h2 : zz l (c - c') (d - d') = 1 := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ← zz_mul, ← zz_inv, h1, mul_inv_cancel]
    obtain ⟨hc, hd⟩ := hinj _ _ h2
    rw [sub_eq_zero] at hc hd
    rw [hc, hd]
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← hQS.ker] at hz
    obtain ⟨a, b, rfl⟩ := (mem_ker_iff hQS.ql hQS.lsurj hQS.three).1 hz
    exact ⟨((a : ZMod 4), (b : ZMod 4)), Subtype.ext (zz_ofNat a b)⟩
  have hcard : Nat.card (center (Jhat K)) = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)]
    simp
  have h := card_center_jhat K
  rw [hcard] at h
  exact h.symm

end CFSG.ComponentClassification.TBLit.L34P
