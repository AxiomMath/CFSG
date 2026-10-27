module

public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

section DihedralOvergroup

open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp CFSG.Glauberman.Dickson.MaxCases
  CFSG.BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem dihedral_r_sr_not_comm {k : ℕ} (hk : 3 ≤ k) :
    DihedralGroup.r (1 : ZMod k) * DihedralGroup.sr 0 ≠ DihedralGroup.sr 0 * DihedralGroup.r 1 := by
  have : NeZero k := ⟨by omega⟩
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  intro h
  have h1 : ((0 : ZMod k) - 1) = 0 + 1 := DihedralGroup.sr.inj h
  have h2 : (2 : ZMod k) = 0 := by linear_combination -h1
  have h3 : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h2
  have h4 := (ZMod.natCast_eq_zero_iff 2 k).mp h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem exists_not_comm_of_dihedral {G : Type*} [Group G] {D : Subgroup G} {k : ℕ}
    (φ : D ≃* DihedralGroup k) (hk : 3 ≤ k) :
    ∃ a b : D, (a : G) * b ≠ b * a := by
  refine ⟨φ.symm (DihedralGroup.r 1), φ.symm (DihedralGroup.sr 0), fun h => ?_⟩
  have h' : φ.symm (DihedralGroup.r 1) * φ.symm (DihedralGroup.sr 0) =
      φ.symm (DihedralGroup.sr 0) * φ.symm (DihedralGroup.r 1) := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  exact dihedral_r_sr_not_comm hk (φ.symm.injective h')

private theorem exists_r_of_two_lt_orderOf {n : ℕ} {g : DihedralGroup n} (h : 2 < orderOf g) :
    ∃ i, g = DihedralGroup.r i := by
  rcases g with i | i
  · exact ⟨i, rfl⟩
  · rw [DihedralGroup.orderOf_sr] at h
    omega

theorem sr_zero_mul_r_one_mul_inv {k : ℕ} :
    DihedralGroup.sr (0 : ZMod k) * DihedralGroup.r 1 * (DihedralGroup.sr 0)⁻¹ =
      (DihedralGroup.r 1)⁻¹ := by
  simp [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]

theorem dihedral_overgroup
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {k : ℕ} (hk3 : 3 ≤ k)
    (hk4 : k ≠ 4) (hkq : 2 * k = p ^ f + 1 ∨ 2 * k + 1 = p ^ f)
    (D M : Subgroup (PSL2MatrixGroup F)) (φ : D ≃* DihedralGroup k) (hDM : D ≤ M) :
    M = D ∨ M = ⊤ ∨ (Nonempty (M ≃* alternatingGroup (Fin 4)) ∧ k = 3) ∨
      (Nonempty (M ≃* Equiv.Perm (Fin 4)) ∧ k = 3) ∨
      (Nonempty (M ≃* alternatingGroup (Fin 5)) ∧ k = 5) := by
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    rcases hpodd with ⟨j, hj⟩
    omega
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, Fact.out, hpodd, Nat.pos_of_ne_zero hf0, hF⟩
  have : NeZero k := ⟨by omega⟩
  have hkp : Nat.Coprime k p := by
    refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr ?_ |>.symm
    intro hpd
    have h1 : p ∣ p ^ f := dvd_pow_self p hf0
    have h2 : p ∣ 2 * k := Dvd.dvd.mul_left hpd 2
    rcases hkq with h | h
    · have : p ∣ 1 := (Nat.dvd_add_right h1).mp (h ▸ h2)
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
    · have h3 : p ∣ 2 * k + 1 := h ▸ h1
      have : p ∣ 1 := (Nat.dvd_add_right h2).mp h3
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨j, hj⟩ := (hpodd.pow : Odd (p ^ f))
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 j)
  set x : D := φ.symm (DihedralGroup.r 1) with hx
  set s : D := φ.symm (DihedralGroup.sr 0) with hs
  have hxord : orderOf (x : PSL2MatrixGroup F) = k := by
    rw [Subgroup.orderOf_coe, hx, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hxM : (x : PSL2MatrixGroup F) ∈ M := hDM x.2
  have hsM : (s : PSL2MatrixGroup F) ∈ M := hDM s.2
  have hsx : s * x * s⁻¹ = x⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, hx, hs, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact sr_zero_mul_r_one_mul_inv
  have hcardD : Nat.card D = 2 * k := by rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  rcases dickson_psl2_subgroup_list hF M with
    ⟨m, hm, hcard, hel⟩ | ⟨z', hz'div, hcard, hcyc⟩ | ⟨z', hz'2, hz'div, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨h5, ⟨e⟩⟩ |
    ⟨m, t, hm1, hmf, htm, htq, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup, hfaith, -⟩ |
    ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := exists_not_comm_of_dihedral φ hk3
    apply hab
    have h1 : (⟨a, hDM a.2⟩ : M) * ⟨b, hDM b.2⟩ = ⟨b, hDM b.2⟩ * ⟨a, hDM a.2⟩ :=
      hel.toIsMulCommutative.is_comm.comm _ _
    exact congrArg Subtype.val h1
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := exists_not_comm_of_dihedral φ hk3
    apply hab
    have h1 : (⟨a, hDM a.2⟩ : M) * ⟨b, hDM b.2⟩ = ⟨b, hDM b.2⟩ * ⟨a, hDM a.2⟩ :=
      hcyc.commGroup.mul_comm _ _
    exact congrArg Subtype.val h1
  ·
    left
    have : NeZero z' := ⟨by omega⟩
    have hxe : orderOf (e ⟨x, hxM⟩) = k := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hxord
    obtain ⟨i, hi⟩ := exists_r_of_two_lt_orderOf (by omega : 2 < orderOf (e ⟨x, hxM⟩))
    have hkz : k ∣ z' := by
      rw [← hxe, hi, DihedralGroup.orderOf_r]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    rw [hgcd] at hz'div
    have hq5 : 5 ≤ p ^ f := by rcases hkq with h | h <;> omega
    have hz'le : z' ≤ (p ^ f + 1) / 2 := by
      rcases hz'div with h | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (Nat.le_of_dvd (by omega) h).trans (Nat.div_le_div_right (by omega))
    obtain ⟨j, hj⟩ := hkz
    have hj1 : j = 1 := by
      rcases j with _ | _ | j
      · omega
      · rfl
      · exfalso
        have h2k : 2 * k ≤ z' := by
          rw [hj]
          nlinarith [Nat.zero_le (k * j)]
        omega
    subst hj1
    refine (Subgroup.eq_of_le_of_card_ge hDM ?_).symm
    rw [hcardD, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hj]
    omega
  ·
    right; right; left
    refine ⟨⟨e⟩, ?_⟩
    rcases pow_of_mulEquiv_alternatingFour e hxM with h | h
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hxord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hxord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
  ·
    right; right; right; left
    refine ⟨⟨e⟩, ?_⟩
    rcases pow_of_mulEquiv_permFour e hxM with h | h
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hxord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have h4 := orderOf_dvd_of_pow_eq_one h
      rw [hxord] at h4
      have h4' := Nat.le_of_dvd (by norm_num) h4
      have hk3' : k = 3 := by omega
      rw [hk3'] at h4
      omega
  ·
    have hk35 : k = 3 ∨ k = 5 := by
      rcases pow_of_mulEquiv_alternatingFive e hxM with h | h | h
      · exfalso
        have := orderOf_dvd_of_pow_eq_one h
        rw [hxord] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      · have := orderOf_dvd_of_pow_eq_one h
        rw [hxord] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      · have h5' := orderOf_dvd_of_pow_eq_one h
        rw [hxord] at h5'
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5' with h1 | h1
        · omega
        · exact Or.inr h1
    rcases hk35 with hk | hk
    · have hq : p ^ f = 5 ∨ p ^ f = 7 := by omega
      rcases hq with hq | hq
      · right; left
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_congr e.toEquiv, card_alternatingFive', psl2_card_formula F hodd, hF, hq]
        norm_num
      · exfalso
        rcases h5 with h | h
        · subst h
          have : 5 ∣ 5 ^ f := dvd_pow_self 5 hf0
          rw [hq] at this
          omega
        · rw [hq] at h
          norm_num [Nat.ModEq] at h
    · right; right; right; right
      exact ⟨⟨e⟩, hk⟩
  ·
    exfalso
    have hc := overgroup_comm_mem N C hCcyc hsup (⟨s, hsM⟩ : M) ⟨x, hxM⟩
    have hmem : (⟨x, hxM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M)⁻¹ ∈ N := by
      have hG : (s : PSL2MatrixGroup F) * x * (s : PSL2MatrixGroup F)⁻¹ = (x : PSL2MatrixGroup F)⁻¹ :=
        congrArg Subtype.val hsx
      have : (⟨s, hsM⟩ : M) * ⟨x, hxM⟩ * (⟨s, hsM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M)⁻¹ =
          (⟨x, hxM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M)⁻¹ := by
        apply Subtype.ext
        show (s : PSL2MatrixGroup F) * x * (s : PSL2MatrixGroup F)⁻¹ * (x : PSL2MatrixGroup F)⁻¹ =
          (x : PSL2MatrixGroup F)⁻¹ * (x : PSL2MatrixGroup F)⁻¹
        rw [hG]
      rwa [this] at hc
    have hpow := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := N) _ hmem
    have hpowG := congrArg Subtype.val hpow
    have h3 : (x : PSL2MatrixGroup F) ^ (2 * p) = 1 := by
      have hpowG' : ((x : PSL2MatrixGroup F)⁻¹ * (x : PSL2MatrixGroup F)⁻¹) ^ p = 1 := by
        simpa using hpowG
      have h4 : (x : PSL2MatrixGroup F)⁻¹ * (x : PSL2MatrixGroup F)⁻¹ =
          ((x : PSL2MatrixGroup F) ^ 2)⁻¹ := by rw [sq, mul_inv_rev]
      rw [h4, inv_pow, inv_eq_one, ← pow_mul] at hpowG'
      exact hpowG'
    have h5 := orderOf_dvd_of_pow_eq_one h3
    rw [hxord] at h5
    have h6 : k ∣ 2 := hkp.dvd_of_dvd_mul_right h5
    have := Nat.le_of_dvd (by norm_num) h6
    omega
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      exact hf0 hmf
    by_cases hmeq : m = f
    · right; left
      subst hmeq
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hm0, psl2_card_formula F hodd, hF,
        pow_mul' p 2 m]
    · exfalso
      have hf2m : 2 * m ≤ f := by
        obtain ⟨c, hc⟩ := hmf
        rcases c with _ | _ | c
        · omega
        · omega
        · nlinarith
      have hpu : p ^ (2 * m) ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2m
      have hord := psl2_orderOf_le (GaloisField p m) (e ⟨x, hxM⟩)
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxord, GaloisField.card p m hm0] at hord
      have ha3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
      rw [pow_mul' p 2 m] at hpu
      have h1 : (p ^ m) * (p ^ m) ≤ 2 * (p ^ m) + 3 := by
        rcases hkq with h | h <;> nlinarith
      have h2 : p ^ m ≤ 3 := by nlinarith
      have h3 : p ^ m = 3 := le_antisymm h2 ha3
      rw [h3] at hord hpu
      omega
  ·
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      exact hf0 hmf
    have hf2m : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have hpu : p ^ (2 * m) ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2m
    have hord := pgl2_orderOf_le (GaloisField p m) (e ⟨x, hxM⟩)
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxord, GaloisField.card p m hm0] at hord
    have ha3 : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow hm0 p)
    rw [pow_mul' p 2 m] at hpu
    have h1 : (p ^ m) * (p ^ m) ≤ 2 * (p ^ m) + 3 := by
      rcases hkq with h | h <;> nlinarith
    have h2 : p ^ m ≤ 3 := by nlinarith
    have h3 : p ^ m = 3 := le_antisymm h2 ha3
    rw [h3] at hord hpu
    omega

end DihedralOvergroup

section Lemma13e

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fixed_dihedral_data (hF : L2Field F) (e : K ≃* L2 F) {x : MulAut K} (hx : x ∈ innDiagSub e)
    (hx2 : orderOf x = 2) :
    ∃ k : ℕ, 2 ≤ k ∧ (2 * k = Nat.card F + 1 ∨ 2 * k + 1 = Nat.card F) ∧
      (x ∉ innAut K → Odd k) ∧ Nonempty (↥(fixedSubgroup K x) ≃* DihedralGroup k) := by
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  by_cases hin : x ∈ innAut K
  · obtain ⟨u, rfl⟩ := hin
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_conj_eq e u]
      exact hx2
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu2).2.1
    refine ⟨k, hk2, ?_, fun h => absurd ⟨u, rfl⟩ h,
      ⟨(MulEquiv.subgroupCongr (Lemma118.fixedSubgroup_conj u)).trans ψ⟩⟩
    rcases hε1 with rfl | rfl
    · right
      omega
    · left
      omega
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
      ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3b F hF K e ε hε1 hε d hd x hx hin hx2).2.1
    have hkodd : Odd k := by
      refine Nat.odd_iff.mpr ?_
      rcases hε1 with rfl | rfl <;> unfold Int.ModEq at hε <;> omega
    refine ⟨k, hk2, ?_, fun _ => hkodd, ⟨ψ⟩⟩
    rcases hε1 with rfl | rfl
    · left
      omega
    · right
      omega

theorem ivk_1_3e
    : IVK_1_3e := by
  intro F _ _ hF K _ _ e u hu hu2
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨a, ha⟩, h3⟩ := hF
    omega
  let φ : K ≃* PSL2 F := toPSL e
  obtain ⟨k, hk2, hkq, hkodd, ⟨ψ⟩⟩ := fixed_dihedral_data hF e hu hu2
  have hkq' : 2 * k = p ^ n + 1 ∨ 2 * k + 1 = p ^ n := by
    rw [← hq]
    exact hkq
  let C : Subgroup K := fixedSubgroup K u
  let D : Subgroup (PSL2 F) := C.map φ.toMonoidHom
  let ψ' : D ≃* DihedralGroup k :=
    (Subgroup.equivMapOfInjective C φ.toMonoidHom φ.injective).symm.trans ψ
  have key : ∀ M : Subgroup K, C ≤ M → 3 ≤ k → k ≠ 4 →
      M = C ∨ M = ⊤ ∨ (Nonempty (↥M ≃* alternatingGroup (Fin 4)) ∧ k = 3) ∨
        (Nonempty (↥M ≃* Equiv.Perm (Fin 4)) ∧ k = 3) ∨
        (Nonempty (↥M ≃* alternatingGroup (Fin 5)) ∧ k = 5) := by
    intro M hCM hk3 hk4
    have hM' : D ≤ M.map φ.toMonoidHom := Subgroup.map_mono hCM
    have eM : ↥M ≃* ↥(M.map φ.toMonoidHom) :=
      Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective
    rcases dihedral_overgroup hq hp2 hk3 hk4 hkq' D (M.map φ.toMonoidHom) ψ' hM' with
      h | h | ⟨⟨e4⟩, hk⟩ | ⟨⟨e4⟩, hk⟩ | ⟨⟨e5⟩, hk⟩
    · exact Or.inl (Subgroup.map_injective φ.injective h)
    · right; left
      rw [← Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective M, h,
        Subgroup.comap_top]
    · exact Or.inr (Or.inr (Or.inl ⟨⟨eM.trans e4⟩, hk⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨eM.trans e4⟩, hk⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨eM.trans e5⟩, hk⟩)))
  obtain ⟨x, hxC, hxord⟩ : ∃ x : K, u x = x ∧ orderOf x = k := by
    have : NeZero k := ⟨by omega⟩
    refine ⟨(ψ.symm (DihedralGroup.r 1) : K), (ψ.symm (DihedralGroup.r 1)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  refine ⟨fun h11 => ?_, fun hout => ?_⟩
  · have hk6 : 6 ≤ k := by omega
    have hCtop : C ≠ ⊤ := by
      intro htop
      have h1 : Nat.card C = Nat.card K := by rw [htop, Subgroup.card_top]
      have h2 : Nat.card C = 2 * k := by
        have : NeZero k := ⟨by omega⟩
        rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
      have h3 := ivk_1_2b F hF K e
      have h144 : 144 ≤ Nat.card F ^ 2 := by nlinarith
      have h4 : Nat.card F * 143 ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h5 : (Nat.card F * 143) / 2 ≤ Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
        Nat.div_le_div_right h4
      omega
    refine ⟨hCtop, fun M hCM => ?_⟩
    rcases key M hCM.le (by omega) (by omega) with h | h | ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩
    · exact absurd h (ne_of_gt hCM)
    · exact h
    · omega
    · omega
    · omega
  · refine ⟨?_, fun M hCM hMu => ?_⟩
    · intro htop
      have : u = 1 := by
        ext y
        have hy : y ∈ fixedSubgroup K u := by rw [show fixedSubgroup K u = ⊤ from htop]; exact Subgroup.mem_top y
        exact hy
      rw [this, orderOf_one] at hu2
      omega
    · have hkodd' := hkodd hout
      have hk3 : 3 ≤ k := by
        obtain ⟨j, hj⟩ := hkodd'
        omega
      have hk4 : k ≠ 4 := by
        rintro rfl
        exact absurd hkodd' (by decide)
      have hMu' : ∀ m ∈ M, u m ∈ M := by
        intro m hm
        have : u m ∈ M.map u.toMonoidHom := ⟨m, hm, rfl⟩
        rwa [hMu] at this
      rcases key M hCM hk3 hk4 with h | h | ⟨⟨e4⟩, hk⟩ | ⟨⟨e4⟩, hk⟩ | ⟨⟨e5⟩, hk⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (no_outer_normalizes_a4 hF e hu hout M e4 hMu' (hCM hxC) (hxord.trans hk) hxC).elim
      · exact (no_outer_normalizes_s4 hF e hu hout M e4 hMu' (hCM hxC) (hxord.trans hk) hxC).elim
      · exact (no_outer_normalizes_a5 hF e hu hout M e5 hMu' (hCM hxC) (hxord.trans hk) hxC).elim

end Lemma13e

end CFSG.GH74.GLS.IVK.Proofs2
