module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316D

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_index_two_cosets {H K : Subgroup G} (hHK : H ≤ K)
    (hcard : Nat.card K = 2 * Nat.card H) {x : G} (hx : x ∈ K) (hxH : x ∉ H) :
    ∀ y ∈ K, y ∈ H ∨ x⁻¹ * y ∈ H := by
  haveI : Nonempty H := ⟨1⟩
  have hIdx : (H.subgroupOf K).index = 2 := by
    have hcardHK : Nat.card (H.subgroupOf K) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
    have hcm := Subgroup.card_mul_index (H.subgroupOf K)
    rw [hcardHK, hcard] at hcm
    exact Nat.mul_left_cancel Nat.card_pos (hcm.trans (by ring))
  intro y hy
  by_cases hyH : y ∈ H
  · exact Or.inl hyH
  · right
    have hmem : (⟨x⁻¹, K.inv_mem hx⟩ : K) * ⟨y, hy⟩ ∈ H.subgroupOf K := by
      rw [Subgroup.mul_mem_iff_of_index_two hIdx]
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false (fun h => hxH (inv_mem_iff.mp h)) hyH
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem fzl_coprime_decomp {Q : Subgroup G} {rho : G} (hQ2 : IsPGroup 2 Q) (hrho3 : rho ^ 3 = 1)
    (hQ : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q) {q : G} (hq : q ∈ Q) :
    ∃ c ∈ Q, rho * c * rho⁻¹ = c ∧ c⁻¹ * q ∈ ⁅Q, zpowers rho⁆ := by
  classical
  let P : Subgroup G := ⁅Q, zpowers rho⁆
  have hr3 : rho * rho * rho = 1 := by simpa [pow_succ, pow_two, mul_assoc] using hrho3
  have hrho2 : rho * rho = rho⁻¹ := eq_inv_of_mul_eq_one_left hr3
  have hrho_inv_Q : ∀ x ∈ Q, rho⁻¹ * x * rho ∈ Q := by
    intro x hx
    have h2 : rho * (rho * x * rho⁻¹) * rho⁻¹ ∈ Q := hQ _ (hQ x hx)
    have he : rho * (rho * x * rho⁻¹) * rho⁻¹ = rho⁻¹ * x * rho := by
      calc rho * (rho * x * rho⁻¹) * rho⁻¹
          = (rho * rho) * x * (rho * rho)⁻¹ := by group
        _ = rho⁻¹ * x * (rho⁻¹)⁻¹ := by rw [hrho2]
        _ = rho⁻¹ * x * rho := by rw [inv_inv]
    rwa [he] at h2
  have hPQ : P ≤ Q := by
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    have hb_norm : b ∈ Subgroup.normalizer (Q : Set G) := by
      have hrho_norm : rho ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.mem_normalizer_iff.mpr fun z => ⟨hQ z, fun hz => by
          have h := hrho_inv_Q (rho * z * rho⁻¹) hz
          rwa [show rho⁻¹ * (rho * z * rho⁻¹) * rho = z from by group] at h⟩
      exact Subgroup.zpowers_le.mpr hrho_norm hb
    have hba : b * a * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hb_norm a).mp ha
    show ⁅a, b⁆ ∈ Q
    rw [show ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ from by rw [commutatorElement_def]; group]
    exact Q.mul_mem ha (Q.inv_mem hba)
  have hPmap : P.map (MulAut.conj rho) = P := by
    have hQmap : Q.map (MulAut.conj rho) = Q := by
      ext z
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        change rho * y * rho⁻¹ ∈ Q
        exact hQ y hy
      · intro hz
        exact ⟨rho⁻¹ * z * rho, hrho_inv_Q z hz, by
          change rho * (rho⁻¹ * z * rho) * rho⁻¹ = z
          group⟩
    have hZmap : (Subgroup.zpowers rho).map (MulAut.conj rho) =
        Subgroup.zpowers rho := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change rho * rho * rho⁻¹ = rho
      group
    show (⁅Q, Subgroup.zpowers rho⁆).map (MulAut.conj rho) =
      ⁅Q, Subgroup.zpowers rho⁆
    rw [Subgroup.map_commutator, hQmap, hZmap]
  have hP_rho : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P := by
    intro p hp
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj rho : G →* G) hp
    rw [hPmap] at hmem
    exact hmem
  let S : Set G := {x | q⁻¹ * x ∈ P}
  have hS_inv : ∀ x ∈ S, rho * x * rho⁻¹ ∈ S := by
    intro x hx
    show q⁻¹ * (rho * x * rho⁻¹) ∈ P
    have h1 : q⁻¹ * (rho * x * rho⁻¹) = ⁅q⁻¹, rho⁆ * (rho * (q⁻¹ * x) * rho⁻¹) := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact P.mul_mem (Subgroup.commutator_mem_commutator (Q.inv_mem hq)
      (Subgroup.mem_zpowers rho)) (hP_rho _ hx)
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype P := Fintype.ofFinite P
  let f : Function.End S := fun x => ⟨rho * x.1 * rho⁻¹, hS_inv x.1 x.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext x; apply Subtype.ext
    change rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹ = (x : G)
    calc rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹
        = rho * rho * rho * (x : G) * (rho * rho * rho)⁻¹ := by group
      _ = (x : G) := by rw [hr3]; group
  have hcardS : Fintype.card S = Nat.card P := by
    have e : S ≃ P :=
      { toFun := fun x => ⟨q⁻¹ * x.1, x.2⟩
        invFun := fun p => ⟨q * p.1, by
          show q⁻¹ * (q * p.1) ∈ P
          rw [← mul_assoc, inv_mul_cancel, one_mul]
          exact p.2⟩
        left_inv := by intro x; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
    rw [Fintype.card_congr e]
    exact Nat.card_eq_fintype_card.symm
  have hnot3 : ¬ 3 ∣ Fintype.card S := by
    rw [hcardS]
    have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hfix_nonempty : (Function.fixedPoints f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1)
      (by simpa using hf3)
    have hzero : Fintype.card (Function.fixedPoints f) = 0 := by simp [h]
    rw [Nat.ModEq, hzero, Nat.zero_mod] at hmod
    exact hnot3 (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨x, hx⟩ := hfix_nonempty
  rw [Function.mem_fixedPoints_iff] at hx
  refine ⟨x.1, ?_, ?_, ?_⟩
  · have hxP : q⁻¹ * x.1 ∈ P := x.2
    have hxq : x.1 = q * (q⁻¹ * x.1) := by group
    rw [hxq]
    exact Q.mul_mem hq (hPQ hxP)
  · simpa [f] using congrArg Subtype.val hx
  · have hxP : q⁻¹ * x.1 ∈ P := x.2
    have he : x.1⁻¹ * q = (q⁻¹ * x.1)⁻¹ := by group
    show x.1⁻¹ * q ∈ P
    rw [he]
    exact P.inv_mem hxP

theorem fzl_cent_of_normal_two_group {R Z : Subgroup G} {rho : G} (hR2 : IsPGroup 2 R)
    (hrho3 : rho ^ 3 = 1) (hRr : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R)
    (hZc : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) (hZR : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z)
    (hZr : ∀ z ∈ Z, rho * z * rho⁻¹ ∈ Z) (hZ4 : Nat.card Z = 4) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hfix : ∀ z ∈ Z, z ≠ 1 → rho * z * rho⁻¹ ≠ z) : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ = z := by
  classical
  have hr3 : rho * rho * rho = 1 := by simpa [pow_succ, pow_two, mul_assoc] using hrho3
  have hrho2 : rho * rho = rho⁻¹ := eq_inv_of_mul_eq_one_left hr3
  have hRrho_inv : ∀ r ∈ R, rho⁻¹ * r * rho ∈ R := by
    intro r hr
    have h2 : rho * (rho * r * rho⁻¹) * rho⁻¹ ∈ R := hRr _ (hRr r hr)
    have he : rho * (rho * r * rho⁻¹) * rho⁻¹ = rho⁻¹ * r * rho := by
      calc rho * (rho * r * rho⁻¹) * rho⁻¹
          = (rho * rho) * r * (rho * rho)⁻¹ := by group
        _ = rho⁻¹ * r * (rho⁻¹)⁻¹ := by rw [hrho2]
        _ = rho⁻¹ * r * rho := by rw [inv_inv]
    rwa [he] at h2
  have hR_norm : ∀ r ∈ R, r ∈ Subgroup.normalizer (Z : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hZR r hr z hz
    · intro hz
      have h := hZR r⁻¹ (R.inv_mem hr) (r * z * r⁻¹) hz
      rwa [show r⁻¹ * (r * z * r⁻¹) * (r⁻¹)⁻¹ = z from by group] at h
  let Y : Subgroup G :=
    { carrier := {z | z ∈ Z ∧ ∀ r ∈ R, r * z * r⁻¹ = z}
      one_mem' := ⟨Z.one_mem, fun r _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haZ, ha⟩ ⟨hbZ, hb⟩
        refine ⟨Z.mul_mem haZ hbZ, fun r hr => ?_⟩
        calc r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
          _ = a * b := by rw [ha r hr, hb r hr]
      inv_mem' := by
        rintro a ⟨haZ, ha⟩
        refine ⟨Z.inv_mem haZ, fun r hr => ?_⟩
        calc r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [ha r hr] }
  have hYZ : Y ≤ Z := fun y hy => hy.1
  have hYr : ∀ y ∈ Y, rho * y * rho⁻¹ ∈ Y := by
    intro y hy
    refine ⟨hZr y hy.1, fun r hr => ?_⟩
    have hy' : (rho⁻¹ * r * rho) * y * (rho⁻¹ * r * rho)⁻¹ = y :=
      hy.2 _ (hRrho_inv r hr)
    calc r * (rho * y * rho⁻¹) * r⁻¹
        = rho * ((rho⁻¹ * r * rho) * y * (rho⁻¹ * r * rho)⁻¹) * rho⁻¹ := by group
      _ = rho * y * rho⁻¹ := by rw [hy']
  have hYfix : ∀ y ∈ Y, rho * y * rho⁻¹ = y → y = 1 := by
    intro y hy hye
    by_contra hy1
    exact hfix y hy.1 hy1 hye
  have hYmod : Nat.card Y % 3 = 1 := fzl_card_mod3_of_fpf hrho3 hYr hYfix
  have hYdvd : Nat.card Y ∣ 4 := by
    rw [← hZ4]; exact Subgroup.card_dvd_of_le hYZ
  let ψ : R →* Subgroup.normalizer (Z : Set G) :=
    { toFun := fun r => ⟨(r : G), hR_norm r.1 r.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  letI : MulAction R ↥Z := MulAction.compHom ↥Z ψ
  have hsmul : ∀ (r : R) (z : ↥Z),
      ((r • z : ↥Z) : G) = (r : G) * (z : G) * (r : G)⁻¹ := by
    intro r z
    rfl
  have hYeven : 2 ∣ Nat.card Y := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmod := hR2.card_modEq_card_fixedPoints ↥Z
    have hZeven : 2 ∣ Nat.card ↥Z := by rw [hZ4]; norm_num
    have hfixcard : Nat.card (MulAction.fixedPoints R ↥Z) = Nat.card Y := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨(x.1 : G), ?_⟩
          invFun := fun y => ⟨⟨(y.1 : G), hYZ y.2⟩, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · refine ⟨x.1.2, fun r hr => ?_⟩
        have h := congrArg Subtype.val (x.2 ⟨r, hr⟩)
        rw [hsmul] at h
        exact h
      · rw [MulAction.mem_fixedPoints]
        intro r
        apply Subtype.ext
        rw [hsmul]
        exact y.2.2 r r.2
      · intro x; apply Subtype.ext; rfl
      · intro y; apply Subtype.ext; rfl
    rw [← hfixcard]
    have h0 : Nat.card (MulAction.fixedPoints R ↥Z) % 2 = 0 := by
      have hmod' := hmod
      rw [Nat.ModEq] at hmod'
      rw [← hmod']
      exact Nat.dvd_iff_mod_eq_zero.mp hZeven
    exact Nat.dvd_of_mod_eq_zero h0
  have hYcard : Nat.card Y = 4 := by
    have hYdvd' : Nat.card Y ∣ 2 ^ 2 := by simpa using hYdvd
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hYdvd'
    have hj' : j < 3 := Nat.lt_succ_iff.mpr hjle
    interval_cases j
    · rw [hj] at hYeven
      norm_num at hYeven
    · rw [hj] at hYmod
      norm_num at hYmod
    · rw [hj]; norm_num
  have hYZeq : Y = Z := Subgroup.eq_of_le_of_card_ge hYZ (by rw [hZ4, hYcard])
  intro r hr z hz
  exact (hYZeq.symm ▸ hz).2 r hr

end CFSG.OddStandard.SmallF3.FritzII
