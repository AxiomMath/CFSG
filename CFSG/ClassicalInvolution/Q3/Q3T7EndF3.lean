module

public import CFSG.ClassicalInvolution.Q3.Q3T7EndF1
public import CFSG.ClassicalInvolution.Q3.Q3T7EndF2
public import CFSG.GH74.Uniqueness.Bender.SuzukiAut

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.GH74.Uniqueness.Bender
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Action

variable {G : Type} [Group G] {F : Subgroup G} [F.Normal]

theorem eq_of_conjNormal_eq (hFc : Subgroup.centralizer (F : Set G) = ⊥) {x : G} {r : ↥F}
    (h : ∀ k : ↥F, (MulAut.conjNormal x : MulAut ↥F) k = r * k * r⁻¹) : x = (r : G) := by
  have hc : (r : G)⁻¹ * x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have e := congrArg Subtype.val (h ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply] at e
    have e' : x * k = (r : G) * k * (r : G)⁻¹ * x := by
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = (r : G) * k * (r : G)⁻¹ * x := by rw [show x * k * x⁻¹ = (r : G) * k * (r : G)⁻¹ from e]
    calc k * ((r : G)⁻¹ * x) = (r : G)⁻¹ * ((r : G) * k * (r : G)⁻¹ * x) := by group
      _ = (r : G)⁻¹ * (x * k) := by rw [e']
      _ = (r : G)⁻¹ * x * k := by group
  rw [hFc, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

end Action

section TwoGroup

variable {K : Type} [Group K]

theorem orderOf_ne_three_of_mem_sylow {Q : Sylow 2 K} {r : K} (hr : r ∈ (Q : Subgroup K)) :
    orderOf r ≠ 3 := by
  intro h3
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨r, hr⟩
  have h1 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  rw [h3] at h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

end TwoGroup

section Bender

variable {G : Type} [Group G] [Finite G] {F : Subgroup G} [F.Normal]

theorem false_of_weakMember_of_benderType (hFc : Subgroup.centralizer (F : Set G) = ⊥)
    {n i e : ℕ} (hT : BenderType ↥F n i e) {z : G} (hzF : z ∈ F) {K : Subgroup G}
    (hK : Q3.IsClassicalMember3 K z) : False := by
  classical
  have hz2 : orderOf z = 2 := hK.orderOf_eq_two
  set Fz : ↥F := ⟨z, hzF⟩ with hFz
  have hFz2 : orderOf Fz = 2 := by rw [hFz, Subgroup.orderOf_mk]; exact hz2
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_orderOf_two hFz2)
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  have hFzQ : Fz ∈ (Q : Subgroup ↥F) := hzQ (Subgroup.mem_zpowers Fz)
  have hFzr : Fz ∈ rootCenter (Q : Subgroup ↥F) ∧ Fz ≠ 1 :=
    hc.involution_iff.mp ⟨le_borel _ hFzQ, hFz2⟩
  obtain ⟨x, hxK, hx3⟩ := hK.exists_orderOf_three
  have hx3' : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hKX : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hK.subnormal
  have hcz : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * z * g⁻¹ = z := by
    intro g hg
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [h]
    group
  set σ : MulAut ↥F := MulAut.conjNormal x with hσ
  set Qg : Subgroup G := (Q : Subgroup ↥F).map F.subtype with hQg
  set Zg : Subgroup G := (rootCenter (Q : Subgroup ↥F)).map F.subtype with hZg
  have hQnorm : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ w ∈ Qg, g * w * g⁻¹ ∈ Qg := by
    intro g hg w hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hσg : (MulAut.conjNormal g : MulAut ↥F) Fz = Fz :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hcz g hg)
    exact ⟨_, hc.mem_of_fixes_involution hFzQ hFzr.2 _ hσg s hs, MulAut.conjNormal_apply g s⟩
  have hQX : Qg ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((mem_rootCenter_iff.mp hFzr.1).2 s hs)
  have hZQ : Zg ≤ Qg := Subgroup.map_mono (rootCenter_le _)
  have hzZ : z ∈ Zg := ⟨Fz, hFzr.1, rfl⟩
  have hZsq : ∀ c ∈ Zg, c * c = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (hc.center_sq r hr)
  have hσFz : σ Fz = Fz :=
    Subtype.ext (by rw [hσ, MulAut.conjNormal_apply]; exact hcz x (hKX hxK))
  have hσQ : ∀ s ∈ (Q : Subgroup ↥F), σ s ∈ (Q : Subgroup ↥F) :=
    hc.mem_of_fixes_involution hFzQ hFzr.2 σ hσFz
  have hZnorm : ∀ c ∈ Zg, x * c * x⁻¹ ∈ Zg := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨σ r, hc.mem_rootCenter_of_mul_self (hσQ r (rootCenter_le _ hr)) ?_,
      MulAut.conjNormal_apply x r⟩
    rw [← map_mul, hc.center_sq r hr, map_one]
  have hcent : ∀ c ∈ Zg, x * c * x⁻¹ = c :=
    hK.centralizes_of_subnormal hQnorm hQX hZQ hzZ hZsq hZnorm hxK hx3'
  have hσZ : ∀ c ∈ rootCenter (Q : Subgroup ↥F), σ c = c := by
    intro c hc'
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply]
    exact hcent _ ⟨c, hc', rfl⟩
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx3', map_one]
  have hσ1 : σ ∉ Subgroup.map (MulAut.conj : ↥F →* MulAut ↥F) (Q : Subgroup ↥F) := by
    rintro ⟨r, hr, hσr⟩
    have hxr : x = (r : G) := eq_of_conjNormal_eq hFc (fun k => by
      rw [← hσ, ← hσr, MulAut.conj_apply])
    apply orderOf_ne_three_of_mem_sylow hr
    rw [← Subgroup.orderOf_coe, ← hxr]
    exact hx3
  rcases hT.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -⟩ | ⟨hi, he, hn2⟩
  ·
    subst hi
    have hQeq : rootCenter (Q : Subgroup ↥F) = (Q : Subgroup ↥F) :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _) (by rw [hc.card_eq, hc.card_center, pow_one])
    obtain ⟨r, hr, hσr⟩ := hT.lemma_3_6_a Q σ (fun s hs => hσZ s (by rw [hQeq]; exact hs))
    exact hσ1 ⟨r, rootCenter_le _ hr, MulEquiv.ext fun k => by
      rw [MulAut.conj_apply]
      exact (hσr k).symm⟩
  ·
    subst hi
    obtain ⟨r, hr, hσr⟩ := hT.exists_eq_conj_of_centralizes_center_suzuki Q σ hσZ
    exact hσ1 ⟨r, hr, hσr.symm⟩
  ·
    subst hi
    have hfpf := hT.fixedPointFree_of_orderThree_unitary Q hc hσZ hσ3 hσ1
    have hxQ : ∀ w ∈ Qg, x * w * x⁻¹ ∈ Qg := hQnorm x (hKX hxK)
    have hZc : ∀ c ∈ Zg, ∀ w ∈ Qg, c * w = w * c := by
      rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
      exact congrArg Subtype.val ((mem_rootCenter_iff.mp hr).2 s hs).symm
    have hcommQ : ∀ y ∈ Qg, ∀ y' ∈ Qg, y * y' * y⁻¹ * y'⁻¹ ∈ Zg := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      have := Subgroup.commutator_mem_commutator hs hs'
      rw [(hT.lemma_3_5_a_unitary Q).1, commutatorElement_def] at this
      exact ⟨_, this, rfl⟩
    have hfpfG : ∀ y ∈ Qg, x * y * x⁻¹ * y⁻¹ ∈ Zg → y ∈ Zg := by
      rintro _ ⟨s, hs, rfl⟩ ⟨r, hr, hre⟩
      have hre2 : (r : G) = x * (s : G) * x⁻¹ * (s : G)⁻¹ := hre
      have hre' : σ s * s⁻¹ = r := Subtype.ext (by
        rw [hre2, Subgroup.coe_mul, Subgroup.coe_inv, hσ, MulAut.conjNormal_apply])
      refine ⟨s, hfpf s hs ?_, rfl⟩
      rw [hre']
      exact hr
    obtain ⟨m, hm⟩ := exists_iterate_comm_mem hK.subnormal hQnorm hxK
    have hQle : Qg ≤ (K ⊓ Qg) ⊔ Zg := by
      intro y hy
      obtain ⟨w, hwQ, hw⟩ := exists_iterate_comm_map_eq_mod hxQ hZc hcommQ hcent hfpfG m y hy
      have hwK := hm w hwQ (hQX hwQ)
      have hwQ' := iterate_comm_mem hxQ m hwQ
      have hmem : (fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w ∈ K ⊓ Qg := ⟨hwK, hwQ'⟩
      have hy' : y = ((fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w) *
          (((fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w)⁻¹ * y) := by group
      rw [hy']
      exact Subgroup.mul_mem_sup hmem hw
    have hQgp : IsPGroup 2 ↥Qg :=
      Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ F.subtype F.subtype_injective)
    have hT08 : Nat.card ↥(K ⊓ Qg) ≤ 8 := hK.card_inf_le_eight hQgp
    have hZnormQ : (K ⊓ Qg) ≤ Subgroup.normalizer (Zg : Set G) := by
      intro w hw
      rw [Subgroup.mem_normalizer_iff]
      intro c
      constructor
      · intro hc'
        have h1 : w * c = c * w := (hZc c hc' w hw.2).symm
        have h2 : w * c * w⁻¹ = c := by rw [h1]; group
        rw [h2]; exact hc'
      · intro hc'
        have h : (w * c * w⁻¹) * w⁻¹ = w⁻¹ * (w * c * w⁻¹) :=
          hZc _ hc' w⁻¹ (Qg.inv_mem hw.2)
        have h2 : c = w * c * w⁻¹ := by
          calc c = w⁻¹ * (w * c * w⁻¹) * w := by group
            _ = ((w * c * w⁻¹) * w⁻¹) * w := by rw [← h]
            _ = w * c * w⁻¹ := by group
        rw [h2]; exact hc'
    have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hZnormQ
    obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
    have hq4 : 4 ≤ q := by
      rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hQcard : Nat.card ↥Qg = q ^ 3 := by
      rw [Subgroup.card_map_of_injective F.subtype_injective, hc.card_eq, hq]
    have hZcard : Nat.card ↥Zg = q := by
      rw [Subgroup.card_map_of_injective F.subtype_injective, hc.card_center, hq]
    have hS : q ^ 3 ≤ Nat.card ↥((K ⊓ Qg) ⊔ Zg) := by
      rw [← hQcard]
      exact Subgroup.card_le_of_le hQle
    have hzT : z ∈ (K ⊓ Qg) ⊓ Zg := ⟨⟨hK.mem, ⟨Fz, hFzQ, rfl⟩⟩, hzZ⟩
    have hinf2 : 2 ≤ Nat.card ↥((K ⊓ Qg) ⊓ Zg) := by
      have hd := Subgroup.orderOf_dvd_natCard _ hzT
      rw [hz2] at hd
      exact Nat.le_of_dvd Nat.card_pos hd
    have h1 := Nat.mul_le_mul hS hinf2
    rw [hprod, hZcard] at h1
    have h2 : Nat.card ↥(K ⊓ Qg) * q ≤ 8 * q := Nat.mul_le_mul_right q hT08
    have h3 : 16 ≤ q ^ 2 := by nlinarith
    have h4 : q * 16 ≤ q ^ 3 := by
      calc q * 16 ≤ q * q ^ 2 := Nat.mul_le_mul_left q h3
        _ = q ^ 3 := by ring
    nlinarith

end Bender

end CFSG.ClassicalInvolution.Q3.Q3T8
