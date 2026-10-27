module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveQuat

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup QuaternionGroup

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ c : G, ∀ x ∈ P, c * x * c⁻¹ ∈ S := by
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨c, fun x hx => ?_⟩
  have : c * x * c⁻¹ ∈ ((c • S' : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hS' hx, by simp [MulAut.conj_apply]⟩
  rwa [hc] at this

theorem centralizer_eq_of_zpowers_eq {G : Type*} [Group G] {a b : G}
    (h : zpowers a = zpowers b) : centralizer ({a} : Set G) = centralizer ({b} : Set G) := by
  rw [← centralizer_closure, ← centralizer_closure ({b} : Set G), ← zpowers_eq_closure,
    ← zpowers_eq_closure, h]

theorem hasKlein_image_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (S : Set G) :
    HasKlein (e '' S) ↔ HasKlein S := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, h1, h2, h3, h4⟩
    refine ⟨a, ha, b, hb, ?_, ?_, fun h => h3 (by rw [h]), e.injective ?_⟩
    · rwa [MulEquiv.orderOf_eq] at h1
    · rwa [MulEquiv.orderOf_eq] at h2
    · rw [map_mul, map_mul]
      exact h4
  · rintro ⟨a, ha, b, hb, h1, h2, h3, h4⟩
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_, ?_, fun h => h3 (e.injective h), ?_⟩
    · rwa [MulEquiv.orderOf_eq]
    · rwa [MulEquiv.orderOf_eq]
    · rw [← map_mul, ← map_mul, h4]

@[expose] def klein5a : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

@[expose] def klein5b : A5 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem klein5a_sq : klein5a ^ 2 = 1 := by decide

theorem klein5b_sq : klein5b ^ 2 = 1 := by decide

theorem klein5a_ne_one : klein5a ≠ 1 := by decide

theorem klein5b_ne_one : klein5b ≠ 1 := by decide

theorem klein5_ne : klein5a ≠ klein5b := by decide

theorem klein5_comm : klein5a * klein5b = klein5b * klein5a := by decide

theorem orderOf_klein5a : orderOf klein5a = 2 :=
  orderOf_eq_prime klein5a_sq klein5a_ne_one

theorem orderOf_klein5b : orderOf klein5b = 2 :=
  orderOf_eq_prime klein5b_sq klein5b_ne_one

theorem hasKlein_of_equiv_alt5 {G : Type*} [Group G] (D : Subgroup G) (e : D ≃* A5) :
    HasKlein (D : Set G) := by
  refine ⟨(e.symm klein5a : D), (e.symm klein5a).2, (e.symm klein5b : D), (e.symm klein5b).2,
    ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_klein5a]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_klein5b]
  · intro h
    exact klein5_ne (e.symm.injective (Subtype.ext h))
  · have := congrArg (fun x : A5 => ((e.symm x : D) : G)) klein5_comm
    simpa using this

theorem exists_hom_quat {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hH : Nat.card H = 1000) (hN : Nat.card N = 125) (ψ : QuaternionGroup 2 →* H)
    (hψ : Function.Injective ψ) : ∃ ρ : H →* QuaternionGroup 2, ρ.ker = N := by
  set f : QuaternionGroup 2 →* H ⧸ N := (QuotientGroup.mk' N).comp ψ with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : ψ x ∈ N := by
      have : ψ x ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at this
    have h1 : orderOf (ψ x) ∣ 125 := hN ▸ Subgroup.orderOf_dvd_natCard N hxN
    have h2 : orderOf x ∣ 8 := card_quat2 ▸ orderOf_dvd_natCard x
    rw [orderOf_injective ψ hψ x] at h1
    have h3 : orderOf x ∣ Nat.gcd 8 125 := Nat.dvd_gcd h2 h1
    have h4 : orderOf x = 1 := by
      have : Nat.gcd 8 125 = 1 := by norm_num
      rw [this] at h3
      exact Nat.dvd_one.1 h3
    exact orderOf_eq_one_iff.1 h4
  have hcard : Nat.card (H ⧸ N) = 8 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hH, hN] at this
    omega
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, card_quat2])
  let e : QuaternionGroup 2 ≃* H ⧸ N := MulEquiv.ofBijective f hbij
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem exists_inj_of_hom {H : Type*} [Group H] (ρ : H →* QuaternionGroup 2)
    (hker : IsPGroup 5 ρ.ker) :
    ∃ φ : H ⧸ CFSG.pCore 5 H →* QuaternionGroup 2, Function.Injective φ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : CFSG.pCore 5 H ≤ ρ.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 5) (G := H)))
      ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 : orderOf (ρ x) ∣ 5 ^ k := hk ▸ orderOf_map_dvd ρ x
    have h2 : orderOf (ρ x) ∣ 8 := card_quat2 ▸ orderOf_dvd_natCard (ρ x)
    have h3 : orderOf (ρ x) ∣ Nat.gcd (5 ^ k) 8 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd (5 ^ k) 8 = 1 := by
      apply Nat.Coprime.pow_left
      norm_num
    rw [h4] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hker_le : ρ.ker ≤ CFSG.pCore 5 H :=
    le_sSup (show ρ.ker ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 5 K} from ⟨inferInstance, hker⟩)
  refine ⟨QuotientGroup.lift (CFSG.pCore 5 H) ρ hle, ?_⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H x =>
    have : ρ x = 1 := hq
    exact (QuotientGroup.eq_one_iff x).2 (hker_le this)

theorem exists_hom_of_inj {H : Type*} [Group H] (φ : H ⧸ CFSG.pCore 5 H →* QuaternionGroup 2)
    (hφ : Function.Injective φ) :
    ∃ ρ : H →* QuaternionGroup 2, IsPGroup 5 ρ.ker := by
  refine ⟨φ.comp (QuotientGroup.mk' (CFSG.pCore 5 H)), ?_⟩
  refine (CFSG.pCore_isPGroup (p := 5) (G := H)).to_le ?_
  intro x hx
  have : φ (QuotientGroup.mk' (CFSG.pCore 5 H) x) = 1 := hx
  have h := (map_eq_one_iff φ hφ).1 this
  exact (QuotientGroup.eq_one_iff x).1 h

theorem not_hasKlein_of_hom {G : Type*} [Group G] (H : Subgroup G)
    (ρ : H →* QuaternionGroup 2) (hker : IsPGroup 5 ρ.ker) : ¬ HasKlein (H : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rintro ⟨a, ha, b, hb, ha2, hb2, hab, hcomm⟩
  set a' : H := ⟨a, ha⟩
  set b' : H := ⟨b, hb⟩
  have ho : ∀ x : H, x ∈ ρ.ker → ∀ m : ℕ, 0 < m → orderOf x ∣ m → m < 5 → x = 1 := by
    intro x hx m hm hdvd hlt
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hker ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hne
      have h5 : 5 ∣ 5 ^ k := dvd_pow_self 5 hne
      have := Nat.le_of_dvd hm (h5.trans hdvd)
      omega
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  have hb'2 : orderOf b' = 2 := by rw [Subgroup.orderOf_mk]; exact hb2
  have hsq : ∀ x : H, orderOf x = 2 → ρ x ^ 2 = 1 ∧ ρ x ≠ 1 := by
    intro x hx
    have hxp : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    refine ⟨by rw [← map_pow, hxp, map_one], fun h => ?_⟩
    have := ho x h 2 (by norm_num) (by rw [hx]) (by norm_num)
    rw [this, orderOf_one] at hx
    omega
  have hρ : ρ a' = ρ b' :=
    quat2_unique_involution _ _ (hsq a' ha'2).1 (hsq a' ha'2).2 (hsq b' hb'2).1 (hsq b' hb'2).2
  have hker' : a' * b'⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, mul_inv_cancel]
  have hc : Commute a' b' := Subtype.ext hcomm
  have ha'p : a' ^ 2 = 1 := ha'2 ▸ pow_orderOf_eq_one a'
  have hb'p : b' ^ 2 = 1 := hb'2 ▸ pow_orderOf_eq_one b'
  have hsq2 : (a' * b'⁻¹) ^ 2 = 1 := by
    rw [hc.inv_right.mul_pow, inv_pow, ha'p, hb'p, inv_one, mul_one]
  have := ho _ hker' 2 (by norm_num) (orderOf_dvd_of_pow_eq_one hsq2) (by norm_num)
  apply hab
  have h1 : a' = b' := by
    rw [mul_inv_eq_one] at this
    exact this
  exact congrArg Subtype.val h1

end CFSG.EvenSporadicStandard.RuStd.S2
