module

public import Certificates.Certificate4129
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.QuasithinUnique.L246.C123

open Equiv

theorem exists_conj_of_card_sylow_p {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) :
    ∃ g : G, ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P := by
  let SP : Sylow p G := Sylow.ofCard P hP
  let SQ : Sylow p G := Sylow.ofCard Q hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SP SQ
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • SP : Sylow p G) : Subgroup G) = (SQ : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have h2 : (SQ : Subgroup G) = Q := rfl
  have h3 : (SP : Subgroup G) = P := rfl
  rw [h2, h3] at h1
  rw [← h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : g⁻¹ * (MulAut.conj g • s) * g = s := by
      simp only [MulAut.smul_def, MulAut.conj_apply]; group
    rw [this]; exact hs
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp only [MulAut.smul_def, MulAut.conj_apply]; group⟩

section Explicit

theorem c5_sign : Perm.sign c5 = 1 :=
  Certificates.certificate4129.1
theorem c7_sign : Perm.sign c7 = 1 :=
  Certificates.certificate4129.2.1
theorem c5_pow : c5 ^ 5 = 1 :=
  Certificates.certificate4129.2.2.1
theorem c7_pow : c7 ^ 7 = 1 :=
  Certificates.certificate4129.2.2.2.1
theorem c5_ne : c5 ≠ 1 :=
  Certificates.certificate4129.2.2.2.2.1
theorem c7_ne : c7 ≠ 1 :=
  Certificates.certificate4129.2.2.2.2.2.1

theorem card_normSet5 :
    (Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧ g * c5 * g⁻¹ ∈ pset5).card =
      20 :=
  Certificates.certificate4129.2.2.2.2.2.2.1

theorem card_normSet7 :
    (Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧ g * c7 * g⁻¹ ∈ pset7).card =
      21 :=
  Certificates.certificate4129.2.2.2.2.2.2.2

@[expose] def c5A : A7 := ⟨c5, Equiv.Perm.mem_alternatingGroup.2 c5_sign⟩

@[expose] def c7A : A7 := ⟨c7, Equiv.Perm.mem_alternatingGroup.2 c7_sign⟩

theorem orderOf_c5A : orderOf c5A = 5 :=
  orderOf_eq_prime (p := 5) (hp := ⟨by norm_num⟩) (Subtype.ext c5_pow)
    (fun h => c5_ne (congrArg Subtype.val h))

theorem orderOf_c7A : orderOf c7A = 7 :=
  orderOf_eq_prime (p := 7) (hp := ⟨by norm_num⟩) (Subtype.ext c7_pow)
    (fun h => c7_ne (congrArg Subtype.val h))

theorem card_normalizer_zpowers {x : A7} {p : ℕ} (hx : orderOf x = p)
    (S : Finset (Perm (Fin 7)))
    (hS : ∀ y : Perm (Fin 7), y ∈ S ↔ ∃ k : ℕ, k < p ∧ y = (x : Perm (Fin 7)) ^ k) {m : ℕ}
    (hm : (Finset.univ.filter fun g : Perm (Fin 7) =>
      Perm.sign g = 1 ∧ g * (x : Perm (Fin 7)) * g⁻¹ ∈ S).card = m) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup A7) : Set A7)) = m := by
  classical
  have hp : 0 < p := by rw [← hx]; exact orderOf_pos x
  have hmemzp : ∀ y : A7, y ∈ Subgroup.zpowers x ↔ (y : Perm (Fin 7)) ∈ S := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_mod_orderOf, hx]
      have hk0 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have hk1 : k % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
      refine (hS _).2 ⟨(k % (p : ℤ)).toNat, by omega, ?_⟩
      have : x ^ (k % (p : ℤ)) = x ^ (k % (p : ℤ)).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hk0]
      rw [this]
      rfl
    · intro hy
      obtain ⟨k, -, hk⟩ := (hS _).1 hy
      have : y = x ^ k := Subtype.ext hk
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k
  have hnorm : ∀ n : A7, n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup A7) : Set A7) ↔
      (n : Perm (Fin 7)) * (x : Perm (Fin 7)) * (n : Perm (Fin 7))⁻¹ ∈ S := by
    intro n
    constructor
    · intro hn
      have h1 := (Subgroup.mem_normalizer_iff.1 hn x).1 (Subgroup.mem_zpowers x)
      exact (hmemzp _).1 h1
    · intro h
      have h1 : n * x * n⁻¹ ∈ Subgroup.zpowers x := (hmemzp _).2 h
      apply mem_normalizer_of_conj_le
      intro k hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      have e : n * x ^ j * n⁻¹ = (n * x * n⁻¹) ^ j := by
        rw [conj_zpow]
      rw [e]
      exact Subgroup.zpow_mem _ h1 j
  set nset : Finset (Perm (Fin 7)) := Finset.univ.filter fun g =>
      Perm.sign g = 1 ∧ g * (x : Perm (Fin 7)) * g⁻¹ ∈ S with hnset
  have himg : Subtype.val '' ((Subgroup.normalizer ((Subgroup.zpowers x : Subgroup A7) :
      Set A7) : Subgroup A7) : Set A7) = (nset : Set (Perm (Fin 7))) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_coe, hnset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Equiv.Perm.mem_alternatingGroup.1 n.2, (hnorm n).1 hn⟩
    · intro hg
      rw [Finset.mem_coe, hnset, Finset.mem_filter] at hg
      obtain ⟨-, hs, h1⟩ := hg
      exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.2 hs⟩, (hnorm _).2 h1, rfl⟩
  have h1 : Nat.card (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup A7) : Set A7)) =
      ((Subgroup.normalizer ((Subgroup.zpowers x : Subgroup A7) : Set A7) : Subgroup A7) :
        Set A7).ncard := Nat.card_coe_set_eq _
  rw [h1, ← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset]
  exact hm

theorem card_normalizer_P5 :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers c5A : Subgroup A7) : Set A7)) = 20 := by
  refine card_normalizer_zpowers orderOf_c5A pset5 (fun y => ?_) card_normSet5
  simp only [pset5, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp [c5A]⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
    · exact ⟨4, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; simp
    · right; left; simp [c5A]
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; rfl

theorem card_normalizer_P7 :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers c7A : Subgroup A7) : Set A7)) = 21 := by
  refine card_normalizer_zpowers orderOf_c7A pset7 (fun y => ?_) card_normSet7
  simp only [pset7, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp [c7A]⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
    · exact ⟨4, by norm_num, rfl⟩
    · exact ⟨5, by norm_num, rfl⟩
    · exact ⟨6, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; simp
    · right; left; simp [c7A]
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; rfl

end Explicit

theorem factorization_eq_one {p n k : ℕ} (hp : p.Prime) (h : n = p * k) (hk : ¬ p ∣ k)
    (hk0 : k ≠ 0) : n.factorization p = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [h, Nat.factorization_mul hp0 hk0, Finsupp.add_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hk]

theorem sylow_arith {p M : ℕ} [hp : Fact p.Prime] (H : Subgroup A7)
    (hHp : (Nat.card H).factorization p = 1)
    (hM : ∀ Q : Subgroup A7, Nat.card Q = p →
      Nat.card (Subgroup.normalizer (Q : Set A7)) = M) :
    ∃ n e : ℕ, n * e = Nat.card H ∧ e ∣ M ∧ p ∣ e ∧ n ≡ 1 [MOD p] := by
  obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hP : Nat.card (P : Subgroup ↥H) = p := by
    rw [P.card_eq_multiplicity, hHp, pow_one]
  set N : Subgroup ↥H := Subgroup.normalizer ((P : Subgroup ↥H) : Set ↥H) with hN
  refine ⟨Nat.card (Sylow p ↥H), Nat.card N, ?_, ?_, ?_, card_sylow_modEq_one p ↥H⟩
  · rw [P.card_eq_index_normalizer]
    exact N.index_mul_card
  · have hP' : Nat.card ((P : Subgroup ↥H).map H.subtype) = p := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hP]
    rw [← hM _ hP']
    have hle : N.map H.subtype ≤
        Subgroup.normalizer (((P : Subgroup ↥H).map H.subtype : Subgroup A7) : Set A7) := by
      rintro _ ⟨n, hn, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨n * q * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn q).1 hq, by simp⟩
      · rintro ⟨q, hq, hqy⟩
        refine ⟨n⁻¹ * q * n, ?_, ?_⟩
        · have h2 := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hn) q).1 hq
          rw [inv_inv] at h2
          exact h2
        · show (n : A7)⁻¹ * (H.subtype q) * (n : A7) = y
          rw [hqy]
          show (n : A7)⁻¹ * ((n : A7) * y * (n : A7)⁻¹) * (n : A7) = y
          group
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h1
  · rw [← hP]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer

theorem normalizer_card_of_card_five (Q : Subgroup A7) (hQ : Nat.card Q = 5) :
    Nat.card (Subgroup.normalizer (Q : Set A7)) = 20 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfac : (Nat.card A7).factorization 5 = 1 := by
    rw [card_A7]
    exact factorization_eq_one (by norm_num) (show (2520 : ℕ) = 5 * 504 by norm_num)
      (by norm_num) (by norm_num)
  have hzp : Nat.card (Subgroup.zpowers c5A) = 5 := by
    rw [Nat.card_zpowers, orderOf_c5A]
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow_p (p := 5) (P := Subgroup.zpowers c5A) (Q := Q)
    (by rw [hzp, hfac]; norm_num) (by rw [hQ, hfac]; norm_num)
  have hQeq : Q = conjSub g (Subgroup.zpowers c5A) :=
    Subgroup.ext fun x => by rw [mem_conjSub]; exact hg x
  rw [hQeq, card_normalizer_conjSub, card_normalizer_P5]

theorem normalizer_card_of_card_seven (Q : Subgroup A7) (hQ : Nat.card Q = 7) :
    Nat.card (Subgroup.normalizer (Q : Set A7)) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card A7).factorization 7 = 1 := by
    rw [card_A7]
    exact factorization_eq_one (by norm_num) (show (2520 : ℕ) = 7 * 360 by norm_num)
      (by norm_num) (by norm_num)
  have hzp : Nat.card (Subgroup.zpowers c7A) = 7 := by
    rw [Nat.card_zpowers, orderOf_c7A]
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow_p (p := 7) (P := Subgroup.zpowers c7A) (Q := Q)
    (by rw [hzp, hfac]; norm_num) (by rw [hQ, hfac]; norm_num)
  have hQeq : Q = conjSub g (Subgroup.zpowers c7A) :=
    Subgroup.ext fun x => by rw [mem_conjSub]; exact hg x
  rw [hQeq, card_normalizer_conjSub, card_normalizer_P7]

theorem no_subgroup_card_315 (H : Subgroup A7) (hH : Nat.card H = 315) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfac : (Nat.card H).factorization 5 = 1 := by
    rw [hH]
    exact factorization_eq_one (by norm_num) (show (315 : ℕ) = 5 * 63 by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨n, e, hne, hed, hpe, hmod⟩ :=
    sylow_arith (p := 5) (M := 20) H hfac normalizer_card_of_card_five
  have he20 : e ≤ 20 := Nat.le_of_dvd (by norm_num) hed
  unfold Nat.ModEq at hmod
  rw [hH] at hne
  interval_cases e <;> omega

theorem no_subgroup_card_280 (H : Subgroup A7) (hH : Nat.card H = 280) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card H).factorization 7 = 1 := by
    rw [hH]
    exact factorization_eq_one (by norm_num) (show (280 : ℕ) = 7 * 40 by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨n, e, hne, hed, hpe, hmod⟩ :=
    sylow_arith (p := 7) (M := 21) H hfac normalizer_card_of_card_seven
  have he21 : e ≤ 21 := Nat.le_of_dvd (by norm_num) hed
  unfold Nat.ModEq at hmod
  rw [hH] at hne
  interval_cases e <;> omega

section Fixed

variable {Ω : Type} [Finite Ω]

def orbΩ (σ : A7 →* Equiv.Perm Ω) (ω : Ω) : Set Ω := {v | ∃ g : A7, σ g ω = v}

def stabΩ (σ : A7 →* Equiv.Perm Ω) (ω : Ω) : Subgroup A7 where
  carrier := {g | σ g ω = ω}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show σ (a * b) ω = ω
    rw [map_mul, Equiv.Perm.mul_apply, show σ b ω = ω from hb, show σ a ω = ω from ha]
  inv_mem' := fun {a} ha => by
    show σ a⁻¹ ω = ω
    have h : σ a ω = ω := ha
    calc σ a⁻¹ ω = σ a⁻¹ (σ a ω) := by rw [h]
      _ = ω := by rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

omit [Finite Ω] in
theorem index_stabΩ (σ : A7 →* Equiv.Perm Ω) (ω : Ω) :
    (stabΩ σ ω).index = (orbΩ σ ω).ncard := by
  let _ : MulAction A7 Ω := MulAction.compHom Ω σ
  have h1 := MulAction.index_stabilizer A7 ω
  have h2 : MulAction.stabilizer A7 ω = stabΩ σ ω := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    rfl
  have h3 : MulAction.orbit A7 ω = orbΩ σ ω := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  rw [h2, h3] at h1
  exact h1

omit [Finite Ω] in
theorem mem_orbΩ_self (σ : A7 →* Equiv.Perm Ω) (ω : Ω) : ω ∈ orbΩ σ ω := ⟨1, by simp⟩

omit [Finite Ω] in
theorem orbΩ_eq_of_mem {σ : A7 →* Equiv.Perm Ω} {ω v : Ω} (h : v ∈ orbΩ σ ω) :
    orbΩ σ v = orbΩ σ ω := by
  obtain ⟨g, rfl⟩ := h
  ext w
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, by simp⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    simp [← Equiv.Perm.mul_apply, ← map_mul]

omit [Finite Ω] in
theorem disjoint_orbΩ {σ : A7 →* Equiv.Perm Ω} {ω₀ ω₁ : Ω} (h : ω₁ ∉ orbΩ σ ω₀) :
    Disjoint (orbΩ σ ω₀) (orbΩ σ ω₁) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  apply h
  have h1 := orbΩ_eq_of_mem hx0
  have h2 := orbΩ_eq_of_mem hx1
  have h3 : orbΩ σ ω₀ = orbΩ σ ω₁ := h1.symm.trans h2
  rw [h3]
  exact mem_orbΩ_self σ ω₁

omit [Finite Ω] in
theorem orbit_size_constraints (σ : A7 →* Equiv.Perm Ω) {ω : Ω} (hno : ∃ g : A7, σ g ω ≠ ω) :
    7 ≤ (orbΩ σ ω).ncard ∧ (orbΩ σ ω).ncard ≠ 8 ∧ (orbΩ σ ω).ncard ≠ 9 ∧
      (orbΩ σ ω).ncard ≠ 16 := by
  have hidx := index_stabΩ σ ω
  have hne : stabΩ σ ω ≠ ⊤ := by
    intro h
    obtain ⟨g, hg⟩ := hno
    apply hg
    have : g ∈ stabΩ σ ω := h ▸ Subgroup.mem_top g
    exact this
  have h7 := index_ge_seven hne
  have hmul := (stabΩ σ ω).index_mul_card
  rw [card_A7] at hmul
  refine ⟨hidx ▸ h7, ?_, ?_, ?_⟩
  · intro h
    rw [← hidx] at h
    rw [h] at hmul
    exact no_subgroup_card_315 (stabΩ σ ω) (by omega)
  · intro h
    rw [← hidx] at h
    rw [h] at hmul
    exact no_subgroup_card_280 (stabΩ σ ω) (by omega)
  · intro h
    rw [← hidx] at h
    rw [h] at hmul
    omega

theorem exists_fixed_of_card_sixteen (hΩ : Nat.card Ω = 16) (σ : A7 →* Equiv.Perm Ω) :
    ∃ ω : Ω, ∀ g : A7, σ g ω = ω := by
  by_contra hno
  push Not at hno
  have hne : Nonempty Ω := by
    have : 0 < Nat.card Ω := by rw [hΩ]; norm_num
    exact (Nat.card_pos_iff.1 this).1
  obtain ⟨ω₀⟩ := hne
  have hfin : ∀ ω : Ω, (orbΩ σ ω).Finite := fun ω => Set.toFinite _
  obtain ⟨c0, c1, c2, c3⟩ := orbit_size_constraints σ (hno ω₀)
  by_cases hall : orbΩ σ ω₀ = Set.univ
  · apply c3
    rw [hall, Set.ncard_univ, hΩ]
  · obtain ⟨ω₁, hω₁⟩ : ∃ ω₁, ω₁ ∉ orbΩ σ ω₀ := by
      by_contra h
      push Not at h
      exact hall (Set.eq_univ_of_forall h)
    obtain ⟨d0, d1, d2, d3⟩ := orbit_size_constraints σ (hno ω₁)
    have hdisj := disjoint_orbΩ hω₁
    have hcard01 : (orbΩ σ ω₀ ∪ orbΩ σ ω₁).ncard = (orbΩ σ ω₀).ncard + (orbΩ σ ω₁).ncard :=
      Set.ncard_union_eq hdisj (hfin _) (hfin _)
    by_cases hall2 : orbΩ σ ω₀ ∪ orbΩ σ ω₁ = Set.univ
    · rw [hall2, Set.ncard_univ, hΩ] at hcard01
      omega
    · obtain ⟨ω₂, hω₂⟩ : ∃ ω₂, ω₂ ∉ orbΩ σ ω₀ ∪ orbΩ σ ω₁ := by
        by_contra h
        push Not at h
        exact hall2 (Set.eq_univ_of_forall h)
      obtain ⟨e0, -, -, -⟩ := orbit_size_constraints σ (hno ω₂)
      have hω₂0 : ω₂ ∉ orbΩ σ ω₀ := fun h => hω₂ (Or.inl h)
      have hω₂1 : ω₂ ∉ orbΩ σ ω₁ := fun h => hω₂ (Or.inr h)
      have hdisj2 : Disjoint (orbΩ σ ω₀ ∪ orbΩ σ ω₁) (orbΩ σ ω₂) := by
        rw [Set.disjoint_union_left]
        refine ⟨?_, ?_⟩
        · exact disjoint_orbΩ hω₂0
        · exact disjoint_orbΩ hω₂1
      have hcard012 : ((orbΩ σ ω₀ ∪ orbΩ σ ω₁) ∪ orbΩ σ ω₂).ncard =
          (orbΩ σ ω₀ ∪ orbΩ σ ω₁).ncard + (orbΩ σ ω₂).ncard :=
        Set.ncard_union_eq hdisj2 ((hfin _).union (hfin _)) (hfin _)
      have hle : ((orbΩ σ ω₀ ∪ orbΩ σ ω₁) ∪ orbΩ σ ω₂).ncard ≤ 16 := by
        rw [← hΩ, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
      omega

end Fixed

end CFSG.QuasithinUnique.L246.C123
