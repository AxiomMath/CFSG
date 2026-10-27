module

public import CFSG.GH74.Generic.S45.LSporCommon
public import CFSG.GH74.Generic.S45.LRed
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.GH74.Generic.S45.LAltCore

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.External
open CFSG.Sporadic.Schreier
open scoped MatrixGroups

theorem eq_five_of_card_dvd_1920 {N q : ℕ} (hN : N ∣ 1920) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (h : N * 2 = q * (q ^ 2 - 1)) : q = 5 := by
  have hN1920 : N ≤ 1920 := Nat.le_of_dvd (by norm_num) hN
  have hq15 : q ≤ 15 := by
    by_contra hgt
    push Not at hgt
    have h1 : 16 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 16 * (16 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  obtain ⟨k, hk⟩ := hqodd
  interval_cases q
  · rfl
  · omega
  · exfalso
    norm_num at h
    have : N = 168 := by omega
    subst this
    norm_num at hN
  · omega
  · exfalso
    norm_num at h
    have : N = 360 := by omega
    subst this
    norm_num at hN
  · omega
  · exfalso
    norm_num at h
    have : N = 660 := by omega
    subst this
    norm_num at hN
  · omega
  · exfalso
    norm_num at h
    have : N = 1092 := by omega
    subst this
    norm_num at hN
  · omega
  · exfalso
    norm_num at h
    have : N = 1680 := by omega
    subst this
    norm_num at hN

theorem eq_seven_of_card_dvd_336 {N q : ℕ} (hN : N ∣ 336) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (h : N * 2 = q * (q ^ 2 - 1)) : q = 7 := by
  have hN336 : N ≤ 336 := Nat.le_of_dvd (by norm_num) hN
  have hq9 : q ≤ 8 := by
    by_contra hgt
    push Not at hgt
    have h1 : 9 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  obtain ⟨k, hk⟩ := hqodd
  interval_cases q
  · exfalso
    norm_num at h
    have : N = 60 := by omega
    subst this
    norm_num at hN
  · omega
  · rfl
  · omega

theorem exists_order_four_of_hasL2Model_seven {L : Type} [Group L]
    (h : HasL2Model L (fun q => q = 7)) (hinv : ∃ v : L, orderOf v = 2) :
    ∃ x : L, orderOf x = 4 := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  obtain ⟨-, F, hFfield, hFfin, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have : Fact p.Prime := ⟨hp⟩
  let e' : L ≃* PSL(2, F) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hodd : Odd p := by
    by_contra hp'
    have hpe : Even p := Nat.not_odd_iff_even.1 hp'
    have h2 : Even (p ^ f) := Nat.even_pow.2 ⟨hpe, by omega⟩
    rw [hq] at h2
    exact absurd h2 (by decide)
  obtain ⟨v, hv⟩ := hinv
  have hv' : orderOf (e' v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨-, ⟨d⟩⟩ := (CFSG.Walter.psl2_centralizer_involution F hF hodd (by omega) hv').2
    (by rw [hq])
  have h4 : (p ^ f + 1) / 2 = 4 := by omega
  rw [h4] at d
  refine ⟨e'.symm (d.symm (DihedralGroup.r 1) : PSL(2, F)), ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact DihedralGroup.orderOf_r_one

theorem j2_involution_data {p : P} (hp : orderOf p = 2) :
    (Nat.card (Subgroup.centralizer ({p} : Set P)) = 240 ∧
        Models.fixCount (p : Equiv.Perm (Fin 315)) = 15) ∨
      (Nat.card (Subgroup.centralizer ({p} : Set P)) = 1920 ∧
        Models.fixCount (p : Equiv.Perm (Fin 315)) = 11) := by
  have hp' : orderOf (p : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hp
  obtain ⟨r, hr, c, hcP, hpc⟩ := inner_classes.1 (p : Equiv.Perm (Fin 315)) p.2 hp'
  have hmap : (Subgroup.centralizer ({p} : Set P)).map P.subtype =
      centralizerIn P (p : Equiv.Perm (Fin 315)) := by
    ext x
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxp), rfl⟩
  have hcard : Nat.card (Subgroup.centralizer ({p} : Set P)) =
      Nat.card (centralizerIn P (p : Equiv.Perm (Fin 315))) := by
    rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]
  have hfix : Models.fixCount (p : Equiv.Perm (Fin 315)) = Models.fixCount r := by
    rw [hpc]
    exact Models.fixCount_conj c r
  rw [hcard, hfix, hpc, centralizerIn_conj P hcP,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, -, h1c, -, h2c⟩ := inner_classes
  obtain ⟨hA, hT, -⟩ := fixed_points_reps
  rcases hr with rfl | rfl
  · left
    refine ⟨?_, ?_⟩
    · rw [h1c]
      exact cent2B_facts.2.1
    · unfold Models.fixCount
      rw [← Nat.card_eq_fintype_card]
      exact hA
  · right
    refine ⟨?_, ?_⟩
    · rw [h2c]
      exact cent2A_facts.2.1
    · unfold Models.fixCount
      rw [← Nat.card_eq_fintype_card]
      exact hT

theorem spor_j2
    {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K} (hyp : Hyp1310 K y L)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.J2)
    (hrow : Subgroup.center K ≠ ⊥ → ∀ k : K, y = MulAut.conj k →
      Nat.card (Subgroup.centralizer ({(QuotientGroup.mk k : K ⧸ Subgroup.center K)} :
        Set (K ⧸ Subgroup.center K))) = 1920 → False) :
    Concl1310 K y L := by
  classical
  have hKq : CFSG.Assembly.IsQuasisimple K := ⟨hyp.1.1.1.commutator_eq_top, hyp.1.1.2.1⟩
  obtain ⟨hKp, hz2, hy, hLfix, hno4, hLs, hLnab, hLinv, q, hq5, hqodd, hqcard, hmodel⟩ := hyp.data
  obtain ⟨yb, hyb, hyb1, hyb2⟩ := LAlt.exists_induced_quotient hKp y hy
  obtain ⟨e2, -⟩ : ∃ e2 : K ⧸ Subgroup.center K ≃* P, True := ⟨e.trans nativeEquivP, trivial⟩
  let ya : P ≃* P := (MulAut.congr e2) yb
  let π : K →* P := e2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπsurj : Function.Surjective π := e2.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e2.injective, QuotientGroup.ker_mk']
  have hπy : ∀ k : K, π (y k) = ya (π k) := by
    intro k
    show e2 (QuotientGroup.mk (y k)) = (MulAut.congr e2 yb) (e2 (QuotientGroup.mk k))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hyb]
  have hya1 : ya ≠ 1 := fun h => hyb1 ((MulAut.congr e2).injective (by rw [map_one]; exact h))
  have hya2 : ya * ya = 1 := by
    show (MulAut.congr e2) yb * (MulAut.congr e2) yb = 1
    rw [← map_mul, hyb2, map_one]
  have hLinj : Function.Injective (π.comp L.subtype) := LAlt.inj_restrict π hπker hLs hLnab
  have hLfixed : ∀ l ∈ L, ya (π l) = π l := fun l hl => by rw [← hπy, hLfix l hl]
  have hcongr : ∀ s : K ⧸ Subgroup.center K,
      (MulAut.congr e2) (MulAut.conj s) = MulAut.conj (e2 s) := by
    intro s
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  by_cases hin : ya ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P
  ·
    obtain ⟨g, hg⟩ := hin
    have hgg : g * g = 1 := by
      have h1 : MulAut.conj (g * g) = 1 := by rw [map_mul, hg, hya2]
      have hc : g * g ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro x
        have := congrArg (fun a : MulAut P => a x) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * (g * g) = (g * g * x * (g * g)⁻¹) * (g * g) := by rw [this]
          _ = g * g * x := by group
      rw [center_P, Subgroup.mem_bot] at hc
      exact hc
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hya1 (by rw [← hg, map_one])
    have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
    have hLC : ∀ l ∈ L, π l ∈ Subgroup.centralizer ({g} : Set P) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hLfixed l hl
      rw [← hg, MulAut.conj_apply] at h1
      calc π l * g = (g * π l * g⁻¹) * g := by rw [h1]
        _ = g * π l := by group
    have hdvd : Nat.card ↥L ∣ Nat.card (Subgroup.centralizer ({g} : Set P)) :=
      LAlt.card_dvd_of_map_le π hLinj _ hLC
    have hdvd1920 : Nat.card ↥L ∣ 1920 := by
      rcases j2_involution_data hgord with ⟨hc, -⟩ | ⟨hc, -⟩
      · rw [hc] at hdvd
        exact dvd_trans hdvd (by norm_num)
      · rw [hc] at hdvd
        exact hdvd
    have hq : q = 5 := eq_five_of_card_dvd_1920 hdvd1920 hq5 hqodd hqcard
    by_cases hZ : Subgroup.center K = ⊥
    · have hinj : Function.Injective π :=
        (MonoidHom.ker_eq_bot_iff π).1 (by rw [hπker]; exact hZ)
      let φ : K ≃* P := MulEquiv.ofBijective π ⟨hinj, hπsurj⟩
      have hφ : NativeSporadic.IsSporadic K .J2 := ⟨φ.trans nativeEquivP.symm⟩
      exact ⟨hmodel _ hq, Or.inr (Or.inr (Or.inr (Or.inr hφ))), fun h => (h hφ).elim⟩
    · exfalso
      have hcard2 : Nat.card (Subgroup.center K) ≤ 2 :=
        CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound K hKq hz2
          (Or.inr ⟨e⟩)
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
      have hcard : Nat.card (Subgroup.center K) = 2 := by
        have := (Subgroup.one_lt_card_iff_ne_bot _).2 hZ
        omega
      have hasq : a ^ 2 = 1 := by
        have := pow_card_eq_one' (G := Subgroup.center K) (x := a)
        rwa [hcard] at this
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hζord : orderOf (a : K) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime hasq ha1
      have hcenZ : Subgroup.center K = Subgroup.zpowers (a : K) :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 a.2)
          (by rw [Nat.card_zpowers, hζord, hcard])).symm
      have hker : π.ker = Subgroup.zpowers (a : K) := hπker.trans hcenZ
      obtain ⟨kh, hkh⟩ := hπsurj g
      have hybc : yb = MulAut.conj (QuotientGroup.mk kh) := by
        apply (MulAut.congr e2).injective
        show ya = (MulAut.congr e2) (MulAut.conj (QuotientGroup.mk kh))
        rw [hcongr]
        have : e2 (QuotientGroup.mk kh) = g := hkh
        rw [this, hg]
      have hyc : y = MulAut.conj kh := LAlt.eq_conj_of_induced_eq_conj hKp y yb hyb kh hybc
      rcases j2_involution_data hgord with ⟨hc240, hfix15⟩ | ⟨hc1920, -⟩
      · have hlift := (j2_double_cover_involution_lift_orders_fixCount hKq hζord hcenZ π hπsurj
          hker).2.2 kh (by rw [hkh, hgord]) (by rw [hkh]; exact hfix15)
        have hyk : y kh = kh := by
          rw [hyc, MulAut.conj_apply]
          group
        exact hno4 kh hyk (by rw [hlift.2])
      · refine hrow hZ kh hyc ?_
        have hmapc : (Subgroup.centralizer ({(QuotientGroup.mk kh : K ⧸ Subgroup.center K)} :
            Set (K ⧸ Subgroup.center K))).map e2.toMonoidHom =
            Subgroup.centralizer ({g} : Set P) := by
          ext x
          simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
            MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨z, hz, rfl⟩
            have : e2 (QuotientGroup.mk kh) = g := hkh
            rw [← this, ← map_mul, ← map_mul, hz]
          · intro hx
            refine ⟨e2.symm x, ?_, e2.apply_symm_apply x⟩
            apply e2.injective
            have : e2 (QuotientGroup.mk kh) = g := hkh
            rw [map_mul, map_mul, this, e2.apply_symm_apply, hx]
        rw [← hc1920, ← hmapc, Subgroup.card_map_of_injective e2.injective]
  ·
    exfalso
    have hya_ord : orderOf ya = 2 := orderOf_eq_prime (by rw [pow_two]; exact hya2) hya1
    obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hya_ord hin
    have hLfb : ∀ l ∈ L, π l ∈ CFSG.Sporadic.Schreier.fixSub
        (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) := by
      intro l hl
      rw [CFSG.Sporadic.Schreier.mem_fixSub, ← hg]
      exact hLfixed l hl
    have hdvd : Nat.card ↥L ∣ Nat.card (CFSG.Sporadic.Schreier.fixSub
        (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)) :=
      LAlt.card_dvd_of_map_le π hLinj _ hLfb
    rw [card_fixSub_conj_beta] at hdvd
    have hq : q = 7 := eq_seven_of_card_dvd_336 hdvd hq5 hqodd hqcard
    obtain ⟨v, hvL, hv⟩ := hLinv
    obtain ⟨x, hx⟩ := exists_order_four_of_hasL2Model_seven (hmodel _ hq)
      ⟨⟨v, hvL⟩, by rw [Subgroup.orderOf_mk]; exact hv⟩
    exact hno4 (x : K) (hLfix _ x.2) (by rw [Subgroup.orderOf_coe, hx])

end CFSG.GH74.Generic.S45
