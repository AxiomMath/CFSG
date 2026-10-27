module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Nine
public import Certificates.Certificate27584

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (twoF4H twoF4N)
open scoped Pointwise

namespace Model

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem s3Check_eq_true :
    Certificates.TitsAschbacherNThree.s3Check () = true :=
  Certificates.certificate27584

theorem parrottV_three_reeW₂
    : parrottV 3 ∈ titsN ∧ reeW₂ ∈ titsN ∧ parrottV 3 * parrottV 3 = 1 ∧ reeW₂ * reeW₂ = 1 ∧
      (parrottV 3 * reeW₂) ^ 3 = 1 ∧ parrottV 3 * reeW₂ ≠ 1 := by
  have h := s3Check_eq_true
  simp only [Certificates.TitsAschbacherNThree.s3Check, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have r3 : Rep 1755 (Certificates.TitsAschbacherParrott.vA 3) (parrottV 3) :=
    rep_vA (by norm_num)
  have r32 : Rep 1755 (Certificates.TitsAschbacherNThree.v3w2Arr ()) (parrottV 3 * reeW₂) :=
    rep_compA r3 rep_w2Arr
  obtain ⟨-, hw2, -, o2, -⟩ := reeW_orders
  refine ⟨?_, hw2, eq_of_eqA (rep_compA r3 r3) rep_idA h1, ?_,
    eq_of_eqA (rep_powA r32 3) rep_idA h3, fun he => ?_⟩
  · rw [← card_twoF4N.2.1]
    exact mem_inf.2 ⟨CFSG.Quasithin.twoF4S_le_twoF4N (parrottV_mem_twoF4S 3),
      (parrottV_mem_titsD_iff (by norm_num)).2 (by decide)⟩
  · rw [← sq, ← o2, pow_orderOf_eq_one]
  · rw [(eqA_iff r32 rep_idA).2 he] at h2
    exact absurd h2 (by decide)

end Model

theorem index_sylow_two_eq_three {K : Type*} [Group K] [Finite K] (P : Sylow 2 K) {k : ℕ}
    (h : Nat.card K = 2 ^ k * 3) : (P : Subgroup K).index = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := (P : Subgroup K).card_mul_index
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 P.isPGroup'
  rw [hm, h] at hidx
  have hc : Nat.Coprime (P : Subgroup K).index (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 P.not_dvd_index))
  have h3 : (P : Subgroup K).index ∣ 3 := hc.dvd_of_dvd_mul_left (Dvd.intro_left _ hidx)
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
  · rw [h1, mul_one] at hidx
    have h32 : 3 ∣ 2 ^ m := Dvd.intro_left _ hidx.symm
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
  · exact h1

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.card_M_N
    (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.M = 32 * Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G) ∧
      Nat.card d.N = 32 * Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  have key : ∀ {D : Subgroup G}, (D = d.A ∨ D = d.B) → Nat.card (D ⊓ d.L : Subgroup G) = 32 →
      Nat.card (normalizer (D : Set G)) =
        32 * Nat.card (normalizer (D : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
    intro D hD h32
    obtain ⟨h1, -, h3⟩ := hd.thm51 h49 hD
    have htD : d.t ∈ D := by
      rcases hD with rfl | rfl <;> exact mem_sup_right (mem_zpowers _)
    have horb : {y | ∃ n ∈ normalizer (D : Set G), n * d.t * n⁻¹ = y} = d.tG ∩ D := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, rfl⟩, (mem_normalizer_iff.1 hn _).1 htD⟩
      · intro hy
        exact h3 y hy
    have hcard : (d.tG ∩ D).ncard = 32 := by
      rw [h1, Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
      exact h32
    rw [card_eq_ncard_conj_mul (normalizer (D : Set G)) d.t, horb, hcard]
  refine ⟨key (Or.inl rfl) ?_, key (Or.inr rfl) ?_⟩
  · rw [hd.A_inf_L]
    exact hd.A_facts.1
  · rw [hd.B_inf_L]
    exact hd.B_facts.1

theorem Hyp.card_M_N_values
    (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (d.ρ.range = titsD.subgroupOf titsA ∧ Nat.card d.M = 2 ^ 17 * 5 ∧
        Nat.card d.N = 2 ^ 17 * 3) ∨
      (d.ρ.range = ⊤ ∧ Nat.card d.M = 2 ^ 18 * 5 ∧ Nat.card d.N = 2 ^ 18 * 3) := by
  obtain ⟨hM, hN⟩ := hd.card_M_N h49
  have hM' : Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
      2 * Nat.card (twoF4H.subgroupOf titsA ⊓ d.ρ.range : Subgroup titsA) :=
    hd.card_normalizer_tSup (Model.hatE_le_titsJ.trans titsJ_le_titsD)
      Model.titsA_inf_normalizer_hatE
  have hN' : Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
      2 * Nat.card (twoF4N.subgroupOf titsA ⊓ d.ρ.range : Subgroup titsA) :=
    hd.card_normalizer_tSup Model.parrottF_le_titsD Model.titsA_inf_normalizer_parrottF
  rcases hd.range_ρ with hR | hR
  · left
    rw [hR, card_inf_titsD Model.twoF4H_le_titsA, Model.twoF4H_inf_titsD,
      titsQH_facts.2.2.2] at hM'
    rw [hR, card_inf_titsD Model.twoF4N_le_titsA, Model.card_twoF4N.2.1,
      titsQN_facts.2.2.2] at hN'
    refine ⟨hR, ?_, ?_⟩
    · rw [hM, hM']
      norm_num
    · rw [hN, hN']
      norm_num
  · right
    rw [hR, card_inf_top Model.twoF4H_le_titsA, Model.card_twoF4H] at hM'
    rw [hR, card_inf_top Model.twoF4N_le_titsA, Model.card_twoF4N.1] at hN'
    refine ⟨hR, ?_, ?_⟩
    · rw [hM, hM']
      norm_num
    · rw [hN, hN']
      norm_num

theorem Hyp.index_sylow_N
    (h49 : d.Thm49Statement) (hd : d.Hyp) (P : Sylow 2 d.N) :
    (P : Subgroup d.N).index = 3 := by
  rcases hd.card_M_N_values h49 with ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact index_sylow_two_eq_three P h
  · exact index_sylow_two_eq_three P h

theorem Hyp.exists_involutions_C_N
    (hd : d.Hyp) :
    ∃ a ∈ d.N ⊓ centralizer ({d.t} : Set G), ∃ b ∈ d.N ⊓ centralizer ({d.t} : Set G),
      a * a = 1 ∧ b * b = 1 ∧ (a * b) ^ 3 = 1 ∧ a * b ≠ 1 := by
  obtain ⟨h3N, hwN, h33, hww, hp3, hp1⟩ := Model.parrottV_three_reeW₂
  have hmem : ∀ x ∈ titsN, d.lift x ∈ d.N ⊓ centralizer ({d.t} : Set G) := by
    intro x hx
    have hC : d.lift x ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem x)
    refine mem_inf.2 ⟨(hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD hC).2 ?_, hC⟩
    rw [hd.ρ_lift (titsN_le_titsD hx)]
    rw [← Model.titsD_inf_normalizer_parrottF] at hx
    exact (mem_inf.1 hx).2
  have h3D := titsN_le_titsD h3N
  have hwD := titsN_le_titsD hwN
  refine ⟨_, hmem _ h3N, _, hmem _ hwN, ?_, ?_, ?_, fun h => ?_⟩
  · rw [← d.lift_mul h3D h3D, h33, d.lift_one]
  · rw [← d.lift_mul hwD hwD, hww, d.lift_one]
  · rw [← d.lift_mul h3D hwD, pow_three, ← d.lift_mul (mul_mem h3D hwD) (mul_mem h3D hwD),
      ← d.lift_mul (mul_mem h3D hwD) (mul_mem (mul_mem h3D hwD) (mul_mem h3D hwD)), ← pow_three,
      hp3, d.lift_one]
  · rw [← d.lift_mul h3D hwD, ← d.lift_one] at h
    exact hp1 (d.lift_inj (mul_mem h3D hwD) (one_mem _) h)

theorem Hyp.thm511
    (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (((CFSG.pCore 2 ↥d.N).map d.N.subtype : Subgroup G) : Set G) *
        ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) = d.N ∧
      Nonempty (↥d.N ⧸ CFSG.pCore 2 ↥d.N ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, b, hb, ha2, hb2, hab3, hab1⟩ := hd.exists_involutions_C_N
  set C : Subgroup d.N := (d.N ⊓ centralizer ({d.t} : Set G)).subgroupOf d.N with hC
  set P₀ : Subgroup d.N := CFSG.pCore 2 ↥d.N with hP₀
  set a' : d.N := ⟨a, (mem_inf.1 ha).1⟩ with ha'
  set b' : d.N := ⟨b, (mem_inf.1 hb).1⟩ with hb'
  have ha'C : a' ∈ C := mem_subgroupOf.2 ha
  have hb'C : b' ∈ C := mem_subgroupOf.2 hb
  have ha'2 : a' * a' = 1 := Subtype.ext ha2
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hab'3 : (a' * b') ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
    exact hab3)
  have hab'1 : a' * b' ≠ 1 := fun h => hab1 (congrArg Subtype.val h)
  have hord : orderOf (a' * b') = 3 := orderOf_eq_prime hab'3 hab'1
  have habP : a' * b' ∉ P₀ := by
    intro h
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := d.N) ⟨_, h⟩
    have h1 : (a' * b') ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 d.N))
  have hP3 := hd.index_sylow_N h49 P
  have hP₀P : P₀ ≤ P := IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup P
  set φ := MulAction.toPermHom d.N (d.N ⧸ (P : Subgroup d.N)) with hφ
  have hker : φ.ker = P₀ := by
    rw [hφ, ← normalCore_eq_ker]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, P.isPGroup'.to_le (normalCore_le _)⟩
    · exact normal_le_normalCore.2 hP₀P
  have hperm : Nat.card (Equiv.Perm (d.N ⧸ (P : Subgroup d.N))) = 6 := by
    rw [Nat.card_perm]
    change (P : Subgroup d.N).index.factorial = 6
    rw [hP3]
    rfl
  have hcardq : Nat.card (d.N ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hidx6 : Nat.card (d.N ⧸ P₀) = 6 := by
    have h3 : 3 ∣ P₀.index := hP3 ▸ index_dvd_of_le hP₀P
    have h6 : Nat.card (d.N ⧸ P₀) ∣ 6 := by
      have h1 := Subgroup.card_subgroup_dvd_card φ.range
      rw [hperm, ← hcardq, hker] at h1
      exact h1
    have hne : P₀.index ≠ 3 := by
      intro h
      have hq : ∀ x : d.N, x * x = 1 → x ∈ P₀ := by
        intro x hx
        have h1 : orderOf (x : d.N ⧸ P₀) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by rw [sq, ← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one])
        have h2 : orderOf (x : d.N ⧸ P₀) ∣ 3 := h ▸ orderOf_dvd_natCard _
        have h3 : orderOf (x : d.N ⧸ P₀) = 1 :=
          Nat.dvd_one.1 ((Nat.dvd_gcd h1 h2).trans (by norm_num))
        rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
        exact h3
      exact habP (mul_mem (hq a' ha'2) (hq b' hb'2))
    obtain ⟨k, hk⟩ := h3
    change P₀.index ∣ 6 at h6
    rw [hk] at h6 hne
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) (h6.trans (by norm_num))
    rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
    · exact absurd rfl hne
    · change P₀.index = 6
      rw [hk]
  have hrange : φ.range = ⊤ := by
    apply eq_top_of_card_eq
    rw [hperm, ← hcardq, hker]
    exact hidx6
  have e1 : d.N ⧸ P₀ ≃* Equiv.Perm (d.N ⧸ (P : Subgroup d.N)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv))
  have e2 : (d.N ⧸ (P : Subgroup d.N)) ≃ Fin 3 := Finite.equivFinOfCardEq hP3
  refine ⟨?_, ⟨e1.trans (Equiv.permCongrHom e2)⟩⟩
  have hCbar : C.map (QuotientGroup.mk' P₀) = ⊤ := by
    have hdvd := Subgroup.card_subgroup_dvd_card (C.map (QuotientGroup.mk' P₀))
    rw [hidx6] at hdvd
    have h3 : 3 ∣ Nat.card (C.map (QuotientGroup.mk' P₀)) := by
      have hmem := mem_map_of_mem (QuotientGroup.mk' P₀) (mul_mem ha'C hb'C)
      have h1 := Subgroup.orderOf_dvd_natCard _ hmem
      have hord3 : orderOf (QuotientGroup.mk' P₀ (a' * b')) = 3 := by
        apply orderOf_eq_prime
        · rw [← map_pow, hab'3, map_one]
        · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
          exact habP
      rwa [hord3] at h1
    have h2 : 2 ∣ Nat.card (C.map (QuotientGroup.mk' P₀)) := by
      have key : ∀ x : d.N, x ∈ C → x * x = 1 → x ∉ P₀ →
          2 ∣ Nat.card (C.map (QuotientGroup.mk' P₀)) := by
        intro x hxC hx2 hxP
        have h1 := Subgroup.orderOf_dvd_natCard _ (mem_map_of_mem (QuotientGroup.mk' P₀) hxC)
        have hord2 : orderOf (QuotientGroup.mk' P₀ x) = 2 := by
          apply orderOf_eq_prime
          · rw [← map_pow, sq, hx2, map_one]
          · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
            exact hxP
        rwa [hord2] at h1
      by_cases haP : a' ∈ P₀
      · by_cases hbP : b' ∈ P₀
        · exact absurd (mul_mem haP hbP) habP
        · exact key b' hb'C hb'2 hbP
      · exact key a' ha'C ha'2 haP
    have h6 : 2 * 3 ∣ Nat.card (C.map (QuotientGroup.mk' P₀)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    apply eq_top_of_card_eq
    rw [hidx6]
    exact Nat.dvd_antisymm hdvd h6
  ext x
  constructor
  · rintro ⟨_, ⟨p, -, rfl⟩, c, hc, rfl⟩
    exact mul_mem p.2 (mem_inf.1 hc).1
  · intro hx
    have hmem : QuotientGroup.mk' P₀ ⟨x, hx⟩ ∈ C.map (QuotientGroup.mk' P₀) := hCbar ▸ mem_top _
    obtain ⟨c, hcC, hc⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc
    have h2 : ⟨x, hx⟩ * c⁻¹ ∈ P₀ := by
      have h1 := (CFSG.pCore_normal (p := 2) (G := d.N)).conj_mem _ hc c
      simpa [mul_assoc] using h1
    refine ⟨x * (c : G)⁻¹, ⟨⟨x, hx⟩ * c⁻¹, h2, rfl⟩, (c : G), mem_subgroupOf.1 hcC, ?_⟩
    simp

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
