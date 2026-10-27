module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenOrders
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Nine

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

theorem sec3102_sylow_inter_eq {G : Type} [Group G] [Finite G] {S C M : Subgroup G}
    (hS : IsPGroup 2 S) (hsyl : IsSylowOf 2 (S ⊓ C) M) :
    S ⊓ C = S ⊓ M ∧ IsSylowOf 2 (S ⊓ M) M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : S ⊓ C ≤ S ⊓ M := le_inf inf_le_left hsyl.le
  have heq : S ⊓ M = S ⊓ C := hsyl.eq_of_le hle inf_le_right hS.to_inf_left
  refine ⟨heq.symm, ?_⟩
  rw [← heq] at hsyl
  exact hsyl

theorem sec3102_isSylowOf_of_card_mul {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hXM : X ≤ M) (hX : IsPGroup 2 X) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card M = Nat.card X * m) : IsSylowOf 2 X M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hXM, hX, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := X) (K := M)
  rw [inf_eq_left.2 hXM] at h1
  have hpos : 0 < Nat.card X := Nat.card_pos
  have h2 : X.relIndex M = m := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, hcard, mul_comm]
  rw [h2]
  obtain ⟨c, hc⟩ := hm
  omega

theorem sec3102_odd_card_ker_of {H H' : Type} [Group H] [Group H'] [Finite H]
    (θ : H →* H') (hker : Odd (Nat.card θ.ker)) (K : Subgroup H) {Y : Type} [Group Y]
    (φ : ↥K →* Y) (hφ : ∀ x : ↥K, φ x = 1 → θ x = 1) : Odd (Nat.card φ.ker) := by
  have hle : φ.ker.map K.subtype ≤ θ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφ x hx
  have h1 : Nat.card φ.ker = Nat.card (φ.ker.map K.subtype) :=
    (Subgroup.card_map_of_injective K.subtype_injective).symm
  rw [h1]
  exact hker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end Generic

section Z1

theorem sec3102_eq_one_of_pow_two_pow {H : Type} [Group H] [Finite H] {O : Subgroup H}
    (hO : Odd (Nat.card O)) {y : H} (hy : y ∈ O) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem sec3102_eq_of_map_eq {A B : Type} [Group A] [Group B] [Finite A] (κ : A →* B × B)
    (hker : Odd (Nat.card κ.ker)) (R : Sylow 2 A) {x y : A} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : κ x = κ y) : x = y := by
  have hmem : x⁻¹ * y ∈ R := MulMemClass.mul_mem (InvMemClass.inv_mem hx) hy
  have h1 : κ (x⁻¹ * y) = 1 := by
    rw [_root_.map_mul, _root_.map_inv, hxy, inv_mul_cancel]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp R.isPGroup' ⟨x⁻¹ * y, hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hpow : (x⁻¹ * y) ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  exact inv_mul_eq_one.mp (sec3102_eq_one_of_pow_two_pow hker (MonoidHom.mem_ker.mpr h1) hpow)

theorem sec3102_mem_mapSurjective_iff {A B : Type} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) (R : Sylow 2 A) (b : B) :
    b ∈ R.mapSurjective hf ↔ ∃ a ∈ R, f a = b := by
  have h := Sylow.coe_mapSurjective hf R
  constructor
  · intro hb
    have hb' : b ∈ Subgroup.map f (R : Subgroup A) := by
      rw [← h]
      exact hb
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hb'
    exact ⟨a, ha, hab⟩
  · rintro ⟨a, ha, rfl⟩
    have hfa : f a ∈ Subgroup.map f (R : Subgroup A) := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rw [← h] at hfa
    exact hfa

theorem sec3102_card_center_le_of_maps {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (κ : A →* B × B) (hker : Odd (Nat.card κ.ker)) (R : Sylow 2 A) (Q₁ Q₂ : Sylow 2 B)
    (h₁ : ∀ b : B, b ∈ Q₁ ↔ ∃ a ∈ R, (κ a).1 = b)
    (h₂ : ∀ b : B, b ∈ Q₂ ↔ ∃ a ∈ R, (κ a).2 = b) :
    Nat.card (Subgroup.center R) ≤
      Nat.card (Subgroup.center Q₁) * Nat.card (Subgroup.center Q₂) := by
  have hc : ∀ z : Subgroup.center R, ∀ r : A, r ∈ R → r * z.1.1 = z.1.1 * r := by
    intro z r hr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩)
  have hm₁ : ∀ z : Subgroup.center R, (κ z.1.1).1 ∈ Q₁ := fun z =>
    (h₁ _).mpr ⟨z.1.1, z.1.2, rfl⟩
  have hm₂ : ∀ z : Subgroup.center R, (κ z.1.1).2 ∈ Q₂ := fun z =>
    (h₂ _).mpr ⟨z.1.1, z.1.2, rfl⟩
  have hcen₁ : ∀ z : Subgroup.center R,
      (⟨(κ z.1.1).1, hm₁ z⟩ : ↥(Q₁ : Subgroup B)) ∈ Subgroup.center Q₁ := by
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨r, hr, hrg⟩ := (h₁ g.1).mp g.2
    apply Subtype.ext
    show g.1 * (κ z.1.1).1 = (κ z.1.1).1 * g.1
    rw [← hrg]
    have hk := congrArg Prod.fst
      (show κ r * κ z.1.1 = κ z.1.1 * κ r by
        rw [← _root_.map_mul, ← _root_.map_mul, hc z r hr])
    exact hk
  have hcen₂ : ∀ z : Subgroup.center R,
      (⟨(κ z.1.1).2, hm₂ z⟩ : ↥(Q₂ : Subgroup B)) ∈ Subgroup.center Q₂ := by
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨r, hr, hrg⟩ := (h₂ g.1).mp g.2
    apply Subtype.ext
    show g.1 * (κ z.1.1).2 = (κ z.1.1).2 * g.1
    rw [← hrg]
    have hk := congrArg Prod.snd
      (show κ r * κ z.1.1 = κ z.1.1 * κ r by
        rw [← _root_.map_mul, ← _root_.map_mul, hc z r hr])
    exact hk
  let ψ : Subgroup.center R → Subgroup.center Q₁ × Subgroup.center Q₂ := fun z =>
    (⟨⟨(κ z.1.1).1, hm₁ z⟩, hcen₁ z⟩, ⟨⟨(κ z.1.1).2, hm₂ z⟩, hcen₂ z⟩)
  have hinj : Function.Injective ψ := by
    intro z w hzw
    have e1 := congrArg
      (fun t : Subgroup.center Q₁ × Subgroup.center Q₂ => t.1.1.1) hzw
    have e2 := congrArg
      (fun t : Subgroup.center Q₁ × Subgroup.center Q₂ => t.2.1.1) hzw
    have e1' : (κ z.1.1).1 = (κ w.1.1).1 := e1
    have e2' : (κ z.1.1).2 = (κ w.1.1).2 := e2
    have hκeq : κ z.1.1 = κ w.1.1 := Prod.ext e1' e2'
    have hxy : z.1.1 = w.1.1 := sec3102_eq_of_map_eq κ hker R z.1.2 w.1.2 hκeq
    exact Subtype.ext (Subtype.ext hxy)
  calc Nat.card (Subgroup.center R)
      ≤ Nat.card (Subgroup.center Q₁ × Subgroup.center Q₂) :=
        Nat.card_le_card_of_injective ψ hinj
    _ = Nat.card (Subgroup.center Q₁) * Nat.card (Subgroup.center Q₂) :=
        Nat.card_prod _ _

theorem sec3102_card_center_le_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (κ : A →* B × B) (hκ : Function.Surjective κ) (hker : Odd (Nat.card κ.ker)) (n : ℕ)
    (hB : ∀ Q : Sylow 2 B, Nat.card (Subgroup.center Q) ≤ n) (R : Sylow 2 A) :
    Nat.card (Subgroup.center R) ≤ n ^ 2 := by
  have hf₁ : Function.Surjective ((MonoidHom.fst B B).comp κ) := by
    intro b
    obtain ⟨a, ha⟩ := hκ (b, 1)
    exact ⟨a, by simp [ha]⟩
  have hf₂ : Function.Surjective ((MonoidHom.snd B B).comp κ) := by
    intro b
    obtain ⟨a, ha⟩ := hκ (1, b)
    exact ⟨a, by simp [ha]⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q : Sylow 2 B, ∀ b : B, b ∈ Q ↔ ∃ a ∈ R, (κ a).1 = b :=
    ⟨R.mapSurjective hf₁, fun b => sec3102_mem_mapSurjective_iff hf₁ R b⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q : Sylow 2 B, ∀ b : B, b ∈ Q ↔ ∃ a ∈ R, (κ a).2 = b :=
    ⟨R.mapSurjective hf₂, fun b => sec3102_mem_mapSurjective_iff hf₂ R b⟩
  calc Nat.card (Subgroup.center R)
      ≤ Nat.card (Subgroup.center Q₁) * Nat.card (Subgroup.center Q₂) :=
        sec3102_card_center_le_of_maps κ hker R Q₁ Q₂ hQ₁ hQ₂
    _ ≤ n * n := Nat.mul_le_mul (hB Q₁) (hB Q₂)
    _ = n ^ 2 := (sq n).symm

end Z1

section Z2

theorem sec3102_finite_sylow (H : Type) [Group H] [Finite H] (p : ℕ) : Finite (Sylow p H) :=
  Finite.of_injective (fun P : Sylow p H => (P : Set H)) SetLike.coe_injective

theorem sec3102_centerIn_map_conj {G : Type} [Group G] (g : G) (P : Subgroup G) :
    CFSG.centerIn (P.map (MulAut.conj g).toMonoidHom) =
      (CFSG.centerIn P).map (MulAut.conj g).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  ext x
  simp only [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, fun h hh => hinj ?_⟩, rfl⟩
    simpa only [map_mul] using hc ((MulAut.conj g).toMonoidHom h) ⟨h, hh, rfl⟩
  · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hyc z hz]

open scoped Pointwise in
theorem sec3102_smul_map_subtype {G : Type} [Group G] (N : Subgroup G) (g : N)
    (S : Subgroup N) :
    (MulAut.conj g • S).map N.subtype =
      (S.map N.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact ⟨N.subtype s, ⟨s, hs, rfl⟩, by simp [MulAut.conj_apply]⟩
  · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨MulAut.conj g • s, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s, hs, rfl⟩,
      by simp [MulAut.conj_apply]⟩

open scoped Pointwise in
theorem sec3102_exists_conj_of_isSylowOf {G : Type} [Group G] [Finite G] {N P Q : Subgroup G}
    (hP : IsSylowOf 2 P N) (hQ : IsSylowOf 2 Q N) :
    ∃ g : G, Q = P.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 N) := sec3102_finite_sylow N 2
  obtain ⟨PS, rfl⟩ := hP
  obtain ⟨QS, rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N PS QS
  refine ⟨(g : G), ?_⟩
  have hQS : (QS : Subgroup N) = MulAut.conj g • (PS : Subgroup N) := by
    rw [← hg]
    exact Sylow.coe_subgroup_smul
  rw [hQS]
  exact sec3102_smul_map_subtype N g (PS : Subgroup N)

theorem sec3102_card_centerIn_le_of_isSylowOf {G : Type} [Group G] [Finite G]
    {N P Q : Subgroup G} (hP : IsSylowOf 2 P N) (hQ : IsSylowOf 2 Q N) (m : ℕ)
    (hm : Nat.card (CFSG.centerIn P) ≤ m) : Nat.card (CFSG.centerIn Q) ≤ m := by
  obtain ⟨g, rfl⟩ := sec3102_exists_conj_of_isSylowOf hP hQ
  rw [sec3102_centerIn_map_conj,
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact hm

theorem sec3102_isSylowOf_map_conj {G : Type} [Group G] [Finite G] {P K : Subgroup G} (g : G)
    (hP : IsSylowOf 2 P K) :
    IsSylowOf 2 (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  obtain ⟨hle, hP2, hdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hP
  refine (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨Subgroup.map_mono hle, hP2.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]
  exact hdvd

end Z2

section Z3

theorem sec3102_card_centerIn_eq_card_center {A : Type} [Group A] (P : Subgroup A) :
    Nat.card (CFSG.centerIn P) = Nat.card (Subgroup.center P) := by
  rw [CFSG.centerIn_eq_map_center, Subgroup.card_map_of_injective P.subtype_injective]

theorem sec3102_card_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem sec3102_eq_one_of_mem_of_pow_two_pow {H : Type} [Group H] {O : Subgroup H}
    (hO : Odd (Nat.card O)) {y : H} (hy : y ∈ O) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem sec3102_card_center_eq_centerIn {H : Type} [Group H] (K : Subgroup H) (P : Subgroup K) :
    Nat.card (Subgroup.center P) = Nat.card (CFSG.centerIn (P.map K.subtype)) := by
  rw [sec3102_card_centerIn_eq_card_center]
  exact sec3102_card_center_congr (P.equivMapOfInjective K.subtype K.subtype_injective)

theorem sec3102_card_centerIn_map_conj {H : Type} [Group H] (P : Subgroup H) (g : H) :
    Nat.card (CFSG.centerIn (P.map (MulAut.conj g).toMonoidHom)) = Nat.card (CFSG.centerIn P) := by
  rw [sec3102_card_centerIn_eq_card_center, sec3102_card_centerIn_eq_card_center]
  exact (sec3102_card_center_congr
    (P.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm

theorem sec3102_card_center_le_of_surj {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X →* Y) (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) (m : ℕ)
    (hX : ∀ P : Sylow 2 X, Nat.card (Subgroup.center P) ≤ m) (Q : Sylow 2 Y) :
    Nat.card (Subgroup.center Q) ≤ m := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hφ 2 Q
  have hinj : Function.Injective (φ.subgroupMap P.toSubgroup) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hφx : φ (x : X) = 1 := by
      simpa using congrArg Subtype.val hx
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have hk' : (x : X) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    exact Subtype.ext (sec3102_eq_one_of_mem_of_pow_two_pow hker (MonoidHom.mem_ker.2 hφx) hk')
  have key := sec3102_card_center_congr
    (MulEquiv.ofBijective (φ.subgroupMap P.toSubgroup)
      ⟨hinj, MonoidHom.subgroupMap_surjective φ P.toSubgroup⟩)
  change Nat.card (Subgroup.center (P.toSubgroup.map φ)) ≤ m
  rw [← key]
  exact hX P

end Z3

section Sec3102Model

open CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem sec3102_mem_patSub_sI₆_of_comm {g : hypSU h 2 1}
    (hg : g ∈ patSub h sI₂ isPattern_sI₂)
    (hcomm : ∀ y ∈ patSub h sI₂ isPattern_sI₂, g * y = y * g) :
    g ∈ patSub h sI₆ isPattern_sI₆ := by
  have := h.charP
  refine mem_patSub_sI₆_of hg ?_
  by_contra hu
  obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := 1) (by simp)
  obtain ⟨u', hu'⟩ : ∃ u' : K, mat g ιe₂ ιz * h.bar u' = c :=
    ⟨h.bar (c * (mat g ιe₂ ιz)⁻¹), by
      rw [h.bar_bar, mul_comm c, mul_inv_cancel_left₀ hu]⟩
  obtain ⟨s, hs⟩ := trace_surj (hK := h) (a := u' * h.bar u') (by
    rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨y, hy, hyu, -⟩ := exists_rootI₂ h hs
  have hgU := patSub_le_U _ _ hg
  have hyU := patSub_le_U _ _ hy
  have e : mat (g * y) ιe₂ ιf₂ = mat (y * g) ιe₂ ιf₂ := by rw [hcomm y hy]
  rw [mul_e₂f₂ hgU hyU, mul_e₂f₂ hyU hgU, (patSub_sI₂_rel hy).1, hyu,
    (patSub_sI₂_rel hg).1] at e
  have hbc : u' * h.bar (mat g ιe₂ ιz) = h.bar c := by
    rw [← hu', map_mul, h.bar_bar, mul_comm]
  have h1 : (1 : K) = 0 := by
    linear_combination -hu' + e + hbc + CharTwo.add_self_eq_zero (h.bar c) - hc
  exact one_ne_zero h1

end Sec3102Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3102_centerIn_CPI₂_le (d : Data G h) : CFSG.centerIn d.CPI₂ ≤ d.CPI₆ := by
  intro z hz
  simp only [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hz
  obtain ⟨hzC, hzc⟩ := hz
  obtain ⟨g, hg, hgz⟩ := Subgroup.mem_map.1 hzC
  have hcomm : ∀ y ∈ patSub h sI₂ isPattern_sI₂, g * y = y * g := by
    intro y hy
    have h1 := hzc (d.η y) (Subgroup.mem_map_of_mem d.η hy)
    rw [← hgz, ← map_mul, ← map_mul] at h1
    exact (d.η_injOn (mul_mem (patSub_le_U _ _ hy) (patSub_le_U _ _ hg))
      (mul_mem (patSub_le_U _ _ hg) (patSub_le_U _ _ hy)) h1).symm
  rw [← hgz]
  exact Subgroup.mem_map_of_mem d.η (sec3102_mem_patSub_sI₆_of_comm hg hcomm)

end Data

theorem sec3102_normalClosureIn_map_conj {G : Type} [Group G] (g : G) (M X : Subgroup G) :
    normalClosureIn (M.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) =
      (normalClosureIn M X).map (MulAut.conj g).toMonoidHom := by
  have hS : (X.map (MulAut.conj g).toMonoidHom).subgroupOf (M.map (MulAut.conj g).toMonoidHom) =
      (X.subgroupOf M).map ((MulAut.conj g).toMonoidHom.subgroupMap M) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hyX, hyx⟩
      obtain ⟨m, hmM, hmx⟩ := Subgroup.mem_map.1 x.2
      have hym : (MulAut.conj g) y = (MulAut.conj g) m := hyx.trans hmx.symm
      have hyM : y ∈ M := (MulAut.conj g).injective hym ▸ hmM
      exact ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.2 hyX, Subtype.ext hyx⟩
    · rintro ⟨z, hzX, hzx⟩
      exact ⟨(z : G), Subgroup.mem_subgroupOf.1 hzX, congrArg Subtype.val hzx⟩
  have hsurj : Function.Surjective ((MulAut.conj g).toMonoidHom.subgroupMap M) :=
    MonoidHom.subgroupMap_surjective _ _
  unfold normalClosureIn
  rw [hS, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ hsurj, Subgroup.map_map,
    Subgroup.map_map]
  congr 1

theorem sec3102_centralizer_map_conj {G : Type} [Group G] (g : G) (I : Subgroup G) :
    Subgroup.centralizer ((I.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (I : Set G)).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff]
    intro i hi
    have hy' := Subgroup.mem_centralizer_iff.1 hy ((MulAut.conj g) i)
      (Subgroup.mem_map.2 ⟨i, hi, rfl⟩)
    apply (MulAut.conj g).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy'
  · rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image _ _

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3102_M₄_eq (d : Data G h) : d.M₄ = d.M₁.map (MulAut.conj d.s).toMonoidHom := by
  have hI : d.I₄ = d.I₁.map (MulAut.conj d.s).toMonoidHom := (sec2_1_five d).2.2.2.1
  show normalClosureIn (centralizer (d.I₄ : Set G)) d.N₄ = _
  rw [hI, d.N₄_eq, sec3102_centralizer_map_conj, sec3102_normalClosureIn_map_conj]
  rfl

theorem sec3102_M₅_eq (d : Data G h) : d.M₅ = d.M₂.map (MulAut.conj d.r).toMonoidHom := by
  have hI : d.I₅ = d.I₂.map (MulAut.conj d.r).toMonoidHom := (sec2_1_five d).2.2.2.2.1
  show normalClosureIn (centralizer (d.I₅ : Set G)) d.N₅ = _
  rw [hI, d.N₅_eq, sec3102_centralizer_map_conj, sec3102_normalClosureIn_map_conj]
  rfl

end Data

section Layer

theorem sec3102_card_centerIn_le_of_layer {H H' : Type} [Group H] [Group H'] [Finite H]
    [Finite H'] (θ : H →* H') (hker : Odd (Nat.card θ.ker))
    {M N : Subgroup H} (hDl : M.map θ = normalClosure ((N.map θ : Subgroup H') : Set H'))
    (ψ : ↥(normalClosure ((N.map θ : Subgroup H') : Set H')) ≃* ↥(N.map θ) × ↥(N.map θ))
    (m : ℕ) (hN : ∀ P : Subgroup H, IsSylowOf 2 P N → Nat.card (CFSG.centerIn P) ≤ m)
    {R : Subgroup H} (hR : IsSylowOf 2 R M) : Nat.card (CFSG.centerIn R) ≤ m ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Jb : Subgroup H' := N.map θ with hJb
  set Dn : Subgroup H' := normalClosure (Jb : Set H') with hDn
  have hmem : ∀ x : ↥M, θ x ∈ Dn := fun x => by
    rw [← hDl]
    exact Subgroup.mem_map_of_mem θ x.2
  let κ₀ : ↥M →* ↥Dn := (θ.comp M.subtype).codRestrict Dn hmem
  let κ : ↥M →* ↥Jb × ↥Jb := ψ.toMonoidHom.comp κ₀
  have hκ : Function.Surjective κ := by
    rintro ⟨a, b⟩
    have hy : ((ψ.symm (a, b) : ↥Dn) : H') ∈ M.map θ := by
      rw [hDl]
      exact (ψ.symm (a, b)).2
    obtain ⟨x, hxM, hx⟩ := hy
    refine ⟨⟨x, hxM⟩, ?_⟩
    have e : κ₀ ⟨x, hxM⟩ = ψ.symm (a, b) := Subtype.ext hx
    show ψ (κ₀ ⟨x, hxM⟩) = (a, b)
    rw [e, MulEquiv.apply_symm_apply]
  have hκker : Odd (Nat.card κ.ker) := by
    refine sec3102_odd_card_ker_of θ hker M κ fun x hx => ?_
    have h1 : κ₀ x = 1 := (MulEquiv.map_eq_one_iff ψ).1 hx
    exact congrArg Subtype.val h1
  have hNker : Odd (Nat.card (θ.subgroupMap N).ker) := by
    refine sec3102_odd_card_ker_of θ hker N (θ.subgroupMap N) fun x hx => ?_
    exact congrArg Subtype.val hx
  have hB : ∀ Q : Sylow 2 ↥Jb, Nat.card (Subgroup.center Q) ≤ m := by
    refine sec3102_card_center_le_of_surj (θ.subgroupMap N) (θ.subgroupMap_surjective N) hNker m ?_
    intro P
    rw [sec3102_card_center_eq_centerIn N P]
    exact hN _ ⟨P, rfl⟩
  obtain ⟨Q, rfl⟩ := hR
  rw [← sec3102_card_center_eq_centerIn M Q]
  exact sec3102_card_center_le_prod κ hκ hκker m hB Q

end Layer

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3102_card_centerIn_map_subtype {H : Type} [Group H] (K' : Subgroup H)
    (P : Subgroup K') :
    Nat.card (CFSG.centerIn P) = Nat.card (CFSG.centerIn (P.map K'.subtype)) := by
  rw [← sec3102_card_center_eq_centerIn K' P, CFSG.centerIn_eq_map_center,
    Subgroup.card_map_of_injective P.subtype_injective]

theorem sec3102_card_centerIn_M₂ (hp : d.ProductCaseHyp) {R : Subgroup G}
    (hR : IsSylowOf 2 R d.M₂) : Nat.card (CFSG.centerIn R) ≤ (2 ^ f) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGMS := hp.gms
  have hd := hp.hyp
  obtain ⟨hout, hM⟩ := hd.sec3_3_two hGMS
  set H := centralizer (d.I₂ : Set G) with hH
  set O := standardComponentOddCore H with hO
  set θ := QuotientGroup.mk' O with hθ
  set J := d.N₂.subgroupOf H with hJ
  have hDE : normalClosure ((J.map θ : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) =
      CFSG.layer (↥H ⧸ O) := hout.1.2.2.2.1
  obtain ⟨ψ⟩ : Nonempty (↥(normalClosure ((J.map θ : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O))) ≃*
      ↥(J.map θ) × ↥(J.map θ)) := by
    rcases hout.1.2.2.2.2.2.1 with ⟨⟨hDs, -⟩, -⟩ | ⟨⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -,
      -, ψ, hψ, -⟩, -⟩
    · have hEs : IsSimpleGroup (CFSG.layer (↥H ⧸ O)) := hDE ▸ hDs
      exact absurd hEs hp.caseB
    · exact ⟨ψ⟩
  have hOodd : Odd (Nat.card O) := GMSK.odd_card_standardComponentOddCore H
  have hker : Odd (Nat.card θ.ker) := by
    rw [hθ, QuotientGroup.ker_mk']
    exact hOodd
  have hN₂H : d.N₂ ≤ H := d.N₂_le_centralizer_I₂
  have hM₂H : d.M₂ ≤ H := s2a2_M₂_le_centralizer_I₂ d
  have hJmap : J.map H.subtype = d.N₂ := by
    rw [hJ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hN₂H]
  have hMmap : (d.M₂.subgroupOf H).map H.subtype = d.M₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hM₂H]
  have hCP : Nat.card (CFSG.centerIn d.CPI₂) ≤ 2 ^ f := by
    refine (Subgroup.card_le_of_le (sec3102_centerIn_CPI₂_le d)).trans ?_
    rw [d.card_CPI₆]
  have hN : ∀ P : Subgroup ↥H, IsSylowOf 2 P J → Nat.card (CFSG.centerIn P) ≤ 2 ^ f := by
    intro P hP
    have hP' : IsSylowOf 2 (P.map H.subtype) d.N₂ := by
      rw [← hJmap]
      exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).2 hP
    rw [sec3102_card_centerIn_map_subtype H P]
    exact sec3102_card_centerIn_le_of_isSylowOf d.isSylowOf_N₂_inf_P.2 hP' _ hCP
  have hR' : IsSylowOf 2 (R.subgroupOf H) (d.M₂.subgroupOf H) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).1 ?_
    rw [hMmap, Subgroup.subgroupOf_map_subtype, inf_of_le_left (hR.le.trans hM₂H)]
    exact hR
  have key := sec3102_card_centerIn_le_of_layer θ hker (hM.trans hDE.symm) ψ (2 ^ f) hN hR'
  rw [sec3102_card_centerIn_map_subtype H, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (hR.le.trans hM₂H)] at key
  exact key

end Data

theorem sec3102_odd_two_pow_sub_one {n : ℕ} (hn : n ≠ 0) : Odd (2 ^ n - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hn⟩) odd_one

section Involution

theorem sec3102_map_conj_map_conj {G : Type} [Group G] {g : G} (hg : g * g = 1)
    (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have e : g * (g * y * g⁻¹) * g⁻¹ = y := by
      rw [hg']
      calc g * (g * y * g) * g = (g * g) * y * (g * g) := by group
        _ = y := by rw [hg, one_mul, mul_one]
    rwa [e]
  · intro hx
    refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, ?_⟩
    rw [hg']
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg, one_mul, mul_one]

end Involution

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec3102_le_card_F_inf_I₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : (2 ^ f) ^ 2 ≤ Nat.card ↥(d.F ⊓ centralizer (d.I₂ : Set G)) := by
  have hCP₆ : d.CPI₆ ≤ d.A₁ ⊓ centralizer (d.I₂ : Set G) := by
    refine le_inf ?_ ?_
    · obtain ⟨-, -, ⟨h3, -⟩, -⟩ := d.sec2_1_two hd.two_le
      rw [h3, ← hd.s4o_P_inf_I₆]
      exact le_sup_right
    · have h1 : d.CPI₆ ≤ d.CPI₂ := d.pull_mono patSub_sI₆_le_sI₂
      rw [← hd.s4o_P_inf_I₂] at h1
      exact h1.trans inf_le_right
  have h2 : 2 ^ f ≤ Nat.card ↥(d.A₁ ⊓ centralizer (d.I₂ : Set G)) := by
    rw [← d.card_CPI₆]
    exact Subgroup.card_le_of_le hCP₆
  rw [hd.s4o_cF hGMS d.I₂_le_I]
  exact Nat.pow_le_pow_left h2 2

theorem sec3102_main (hp : d.CaseHyp) (k : d.Know93) (hO : d.Sec3101OrdersAll)
    (hM₁ : ∃ m : ℕ, Odd m ∧ Nat.card d.M₁ = (2 ^ f) ^ 4 * m)
    (hZ : ∀ {R : Subgroup G}, IsSylowOf 2 R d.M₂ → Nat.card (CFSG.centerIn R) ≤ (2 ^ f) ^ 2) :
    d.Sec3_10_two := by
  intro S hS hPS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGMS := hp.gms
  have hd := hp.hyp
  have O := hO S hS hPS
  have sa := k.s9a S hS hPS
  have se := k.s9e
  obtain ⟨hSED, hEchar, hDchar⟩ := k.s9_1 S hS hPS
  obtain ⟨-, -, -, hZD, -⟩ := k.s9_2 S hS hPS
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hES : d.E ≤ S := hSED ▸ le_sup_left
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hFD : d.F ≤ d.D := hZD ▸ inf_le_left
  have hFS : d.F ≤ S := hFD.trans hDS
  have hV₁S : d.V₁ ≤ S := (hd.s4o_V₁_le_E hGMS).trans hES
  have hC₁ : S ⊓ centralizer (d.I₁ : Set G) = d.V₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hV₁S d.V₁_le_centralizer_I₁) ?_).symm
    rw [O.c₁, hd.card_V₁ hGMS]
  have hV₁M₁ : d.V₁ ≤ d.M₁ := hd.V₁_le_M₁ hGMS
  have hSM₁ : S ⊓ d.M₁ = d.V₁ :=
    le_antisymm ((inf_le_inf_left S d.M₁_le_centralizer_I₁).trans hC₁.le) (le_inf hV₁S hV₁M₁)
  have hV₁syl : IsSylowOf 2 d.V₁ d.M₁ := by
    obtain ⟨m, hm, hcard⟩ := hM₁
    exact sec3102_isSylowOf_of_card_mul hV₁M₁ (hS2.to_le hV₁S) hm
      (by rw [hcard, hd.card_V₁ hGMS])
  have hCF₄ : d.F ⊓ centralizer (d.I₄ : Set G) = S ⊓ centralizer (d.I₄ : Set G) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hFS) (by rw [O.c₄, hd.card_F_I₄ hGMS])
  have hV₁s : d.V₁.map (MulAut.conj d.s).toMonoidHom = S ⊓ centralizer (d.I₄ : Set G) := by
    rw [← hCF₄, Data.V₁, sec3102_map_conj_map_conj d.s_mul_s]
  have hM₄le : d.M₄ ≤ centralizer (d.I₄ : Set G) := normalClosureIn_le_self _ _
  have hSM₄ : S ⊓ d.M₄ = S ⊓ centralizer (d.I₄ : Set G) := by
    refine le_antisymm (inf_le_inf_left S hM₄le) (le_inf inf_le_left ?_)
    rw [← hV₁s, sec3102_M₄_eq d]
    exact Subgroup.map_mono hV₁M₁
  have hV₄syl : IsSylowOf 2 (S ⊓ d.M₄) d.M₄ := by
    rw [hSM₄, ← hV₁s, sec3102_M₄_eq d]
    exact sec3102_isSylowOf_map_conj d.s hV₁syl
  obtain ⟨hC₂, hSyl₂⟩ := sec3102_sylow_inter_eq hS2 sa.sylow₂
  obtain ⟨hC₅, hSyl₅⟩ := sec3102_sylow_inter_eq hS2 sa.sylow₅
  have hF₂ : d.F ⊓ d.M₂ = d.F ⊓ centralizer (d.I₂ : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (s2a2_M₂_le_centralizer_I₂ d))
      (le_inf inf_le_left ?_)
    have h1 : d.F ⊓ centralizer (d.I₂ : Set G) ≤ S ⊓ centralizer (d.I₂ : Set G) :=
      inf_le_inf_right _ hFS
    rw [hC₂] at h1
    exact h1.trans inf_le_right
  have hFle₂ : d.F ⊓ d.M₂ ≤ CFSG.centerIn (S ⊓ d.M₂) := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hFS (Subgroup.mem_inf.1 hz).1,
      (Subgroup.mem_inf.1 hz).2⟩, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ S ⊓ centralizer (d.I₂ : Set G) := by rw [hC₂]; exact hy
    rw [← sa.cD₂] at hy'
    have hzZ : z ∈ CFSG.centerIn d.D := by rw [hZD]; exact (Subgroup.mem_inf.1 hz).1
    exact mem_centralizer_iff.1 hzZ.2 y (Subgroup.mem_inf.1 hy').1
  have hcard₂ : Nat.card (CFSG.centerIn (S ⊓ d.M₂)) ≤ (2 ^ f) ^ 2 :=
    hZ hSyl₂
  have hFZ₂ : d.F ⊓ d.M₂ = CFSG.centerIn (S ⊓ d.M₂) := by
    refine Subgroup.eq_of_le_of_card_ge hFle₂ (hcard₂.trans ?_)
    rw [hF₂]
    exact hd.sec3102_le_card_F_inf_I₂ hGMS
  have hF₅ : d.F ⊓ d.M₅ = d.F ⊓ centralizer (d.I₅ : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (s2a2_M₅_le_centralizer_I₅ d))
      (le_inf inf_le_left ?_)
    have h1 : d.F ⊓ centralizer (d.I₅ : Set G) ≤ S ⊓ centralizer (d.I₅ : Set G) :=
      inf_le_inf_right _ hFS
    rw [hC₅] at h1
    exact h1.trans inf_le_right
  have hFle₅ : d.F ⊓ d.M₅ ≤ CFSG.centerIn (S ⊓ d.M₅) := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hFS (Subgroup.mem_inf.1 hz).1,
      (Subgroup.mem_inf.1 hz).2⟩, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ S ⊓ centralizer (d.I₅ : Set G) := by rw [hC₅]; exact hy
    rw [← sa.cD₅] at hy'
    have hzZ : z ∈ CFSG.centerIn d.D := by rw [hZD]; exact (Subgroup.mem_inf.1 hz).1
    exact mem_centralizer_iff.1 hzZ.2 y (Subgroup.mem_inf.1 hy').1
  have hcard₅ : Nat.card (CFSG.centerIn (S ⊓ d.M₅)) ≤ (2 ^ f) ^ 2 := by
    have h1 : IsSylowOf 2 ((S ⊓ d.M₅).map (MulAut.conj d.r).toMonoidHom) d.M₂ := by
      have e : d.M₅.map (MulAut.conj d.r).toMonoidHom = d.M₂ := by
        rw [sec3102_M₅_eq d, sec3102_map_conj_map_conj d.r_mul_r]
      rw [← e]
      exact sec3102_isSylowOf_map_conj d.r hSyl₅
    have h2 := hZ h1
    rwa [sec3102_card_centerIn_map_conj] at h2
  have hFZ₅ : d.F ⊓ d.M₅ = CFSG.centerIn (S ⊓ d.M₅) := by
    refine Subgroup.eq_of_le_of_card_ge hFle₅ (hcard₅.trans ?_)
    rw [hF₅, O.cF₅]
  have hSE : S ≤ normalizer (d.E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (by
      haveI : (d.E.subgroupOf S).Characteristic := hEchar
      infer_instance)
  have hSD : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 (by
      haveI : (d.D.subgroupOf S).Characteristic := hDchar
      infer_instance)
  have hV₁D : d.V₁ ≤ normalizer (d.D : Set G) := hV₁S.trans hSD
  have hDV : d.D ⊓ d.V₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
        d.V₁_le_centralizer_I₁ (Subgroup.mem_inf.1 hx).2⟩
    rw [se.centralizer_I₁] at hx'
    exact hx'
  have hSDV : S = d.D ⊔ d.V₁ := by
    have hle : d.D ⊔ d.V₁ ≤ S := sup_le hDS hV₁S
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have key := Common.card_sup_mul_card_inf_eq (A := d.D) (B := d.V₁) hV₁D
    rw [hDV, Subgroup.card_bot, se.card_D, hd.card_V₁ hGMS, mul_one] at key
    rw [O.card_S, key]
    ring_nf
    exact le_rfl
  have hL₁ : d.L₁ = d.D ⊔ d.M₁ := k.s9_3.1
  have hSL₁ : S ≤ d.L₁ := by
    rw [hSDV, hL₁]
    exact sup_le_sup_left hV₁M₁ _
  have hM₁N : d.M₁ ≤ normalizer (d.D : Set G) := by
    have h1 : d.M₁ ≤ d.L₁ := by rw [hL₁]; exact le_sup_right
    exact h1.trans hd.L₁_le_normalizer_D
  have hDM : d.D ⊓ d.M₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
        d.M₁_le_centralizer_I₁ (Subgroup.mem_inf.1 hx).2⟩
    rw [se.centralizer_I₁] at hx'
    exact hx'
  have hL₁syl : IsSylowOf 2 S d.L₁ := by
    obtain ⟨m, hm, hcard⟩ := hM₁
    refine sec3102_isSylowOf_of_card_mul hSL₁ hS2 hm ?_
    have key := Common.card_sup_mul_card_inf_eq (A := d.D) (B := d.M₁) hM₁N
    rw [hDM, Subgroup.card_bot, mul_one, ← hL₁, se.card_D, hcard] at key
    rw [key, O.card_S]
    ring
  exact ⟨⟨hC₁.trans hSM₁.symm, by rw [hSM₁]; exact hV₁syl⟩,
    ⟨hC₂, hSyl₂⟩, ⟨hSM₄.symm, hV₄syl⟩, ⟨hC₅, hSyl₅⟩, hFZ₂, hFZ₅, hL₁syl, hS⟩

end Data

section Certified


namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3102_exists_odd_card_M₁ (hp : d.CaseHyp) :
    ∃ m : ℕ, Odd m ∧ Nat.card d.M₁ = (2 ^ f) ^ 4 * m := by
  have hf : f ≠ 0 := by have := hp.hyp.two_le; omega
  rcases (hp.hyp.sec3_5_three_iso_all hp.gms hp.gmsL).or with
    ⟨k, _, _, hk, ψ, -, -, -⟩ | ⟨k₂, _, _, hk₂, ψ, -, -⟩
  · have hk' : Nat.card k = 2 ^ (2 * f) := by
      rw [Nat.card_eq_fintype_card, hk, ← pow_mul]; ring_nf
    have e : (2 ^ (2 * f)) ^ 2 = 2 ^ (4 * f) := by rw [← pow_mul]; ring_nf
    rw [Nat.card_congr ψ.toEquiv, Nat.card_prod,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk', e]
    refine ⟨(2 ^ (4 * f) - 1) * (2 ^ (4 * f) - 1), ?_, ?_⟩
    · exact (sec3102_odd_two_pow_sub_one (by omega)).mul (sec3102_odd_two_pow_sub_one (by omega))
    · generalize 2 ^ (4 * f) - 1 = w
      ring
  · have hk' : Nat.card k₂ = 2 ^ (4 * f) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]; ring_nf
    have e : (2 ^ (4 * f)) ^ 2 = 2 ^ (8 * f) := by rw [← pow_mul]; ring_nf
    rw [Nat.card_congr ψ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hk', e]
    refine ⟨2 ^ (8 * f) - 1, sec3102_odd_two_pow_sub_one (by omega), ?_⟩
    generalize 2 ^ (8 * f) - 1 = w
    ring

theorem sec3102_of_hyp (hp : d.CaseHyp) (k : d.Know93) (hO : d.Sec3101OrdersAll)
    (hZ : ∀ {R : Subgroup G}, IsSylowOf 2 R d.M₂ → Nat.card (CFSG.centerIn R) ≤ (2 ^ f) ^ 2) :
    d.Sec3_10_two :=
  sec3102_main hp k hO (sec3102_exists_odd_card_M₁ hp) hZ

end Data

namespace CaseBParts

theorem sec3102 : Sec3102Statement :=
  fun _ _ _ _ _ _ _ _ hp k hO =>
    Data.sec3102_of_hyp hp k hO (fun hR => Data.sec3102_card_centerIn_M₂ hp hR)

end CaseBParts

end Certified

end CFSG.LocalAnalysis.EvenBN.U5
