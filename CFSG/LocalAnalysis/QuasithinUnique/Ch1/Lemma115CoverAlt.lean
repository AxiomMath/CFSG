module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverEven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import Certificates.Certificate4100
public import Certificates.Certificate4156

public section

namespace CFSG.QuasithinUnique.Ch1

structure AltFacts (A : Type) [Group A] [Finite A] : Prop where
  conj : ∀ s t : A, s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 → ∃ g, g * s * g⁻¹ = t
  dihedral : ∃ (a b : A) (m : ℕ), Odd m ∧ Nat.card A = 8 * m ∧ a * a = 1 ∧ b * b = 1 ∧
    orderOf (a * b) = 4 ∧ a ∉ Subgroup.zpowers (a * b)
  cyclic : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ∀ Q : Sylow q A, IsCyclic (Q : Subgroup A)
  three : ∀ Q : Sylow 3 A, CFSG.Open.IsElemAbelian 3 (Q : Subgroup A) ∧
    Nat.card (Q : Subgroup A) = 9

theorem card_ker_of_altFacts {A : Type} [Group A] [Finite A] (F : AltFacts A) (γ : A ≃* A)
    (hγ : ∀ a, γ (γ a) = a)
    (htwist : ∃ x₀ : A, (x₀⁻¹ * γ x₀) * (x₀⁻¹ * γ x₀) = 1 ∧ x₀⁻¹ * γ x₀ ≠ 1)
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] (π : L →* A)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L) (α : L ≃* L)
    (hα : ∀ x, α (α x) = x) (hact : ∀ x, π (α x) = γ (π x))
    (hP : ∃ P : Sylow 2 L, ∀ t ∈ (P : Subgroup L), α t = t) :
    Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 := by
  obtain ⟨a, b, m, hm, hA, ha, hb, hr, hnot⟩ := F.dihedral
  exact card_ker_eq_one_or_three F.cyclic F.three π hπ hker
    (odd_card_ker γ hγ F.conj htwist hm hA ha hb hr hnot π hπ hker α hα hact hP)

section Generic

variable {A : Type} [Group A] [Finite A]

theorem cyclic_sylow_of_not_sq_dvd {N : ℕ} (hN : Nat.card A = N)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ¬ q ^ 2 ∣ N) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ∀ Q : Sylow q A, IsCyclic (Q : Subgroup A) := by
  intro q hq hq2 hq3 Q
  have : Fact q.Prime := ⟨hq⟩
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hlt : (Nat.card A).factorization q < 2 := by
    by_contra hge
    apply h q hq hq2 hq3
    rw [← hN]
    exact (hq.pow_dvd_iff_le_factorization hA0).2 (not_lt.1 hge)
  have hdvd : Nat.card (Q : Subgroup A) ∣ q := by
    rw [Sylow.card_eq_multiplicity]
    have h1 : (Nat.card A).factorization q ≤ 1 := by omega
    calc q ^ (Nat.card A).factorization q ∣ q ^ 1 := pow_dvd_pow q h1
      _ = q := pow_one q
  exact isCyclic_of_card_dvd_prime hdvd

theorem three_sylow_of_card {N : ℕ} (hN : Nat.card A = N) (h2 : 3 ^ 2 ∣ N) (h3 : ¬ 3 ^ 3 ∣ N)
    (hexp : ∀ g : A, g ^ 9 = 1 → g ^ 3 = 1) :
    ∀ Q : Sylow 3 A, CFSG.Open.IsElemAbelian 3 (Q : Subgroup A) ∧
      Nat.card (Q : Subgroup A) = 9 := by
  intro Q
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card A).factorization 3 = 2 := by
    have h2' : 2 ≤ (Nat.card A).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hA0).1 (hN ▸ h2)
    have h3' : ¬ 3 ≤ (Nat.card A).factorization 3 := fun h =>
      h3 (hN ▸ (Nat.prime_three.pow_dvd_iff_le_factorization hA0).2 h)
    omega
  have hcard : Nat.card (Q : Subgroup A) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  refine ⟨⟨?_, ?_⟩, hcard⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := (Q : Subgroup A)) (p := 3)
      (by rw [hcard]; norm_num)
  · intro x hx
    apply hexp
    have := Subgroup.orderOf_dvd_natCard (Q : Subgroup A) hx
    rw [hcard] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this

end Generic

section Assembly

open Equiv Equiv.Perm

theorem conj_of_ref {A : Type} [Group A] (a : A)
    (h : ∀ t : A, t * t = 1 → t ≠ 1 → ∃ g, g * a * g⁻¹ = t) :
    ∀ s t : A, s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 → ∃ g, g * s * g⁻¹ = t := by
  intro s t hs hs1 ht ht1
  obtain ⟨g₁, h₁⟩ := h s hs hs1
  obtain ⟨g₂, h₂⟩ := h t ht ht1
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← h₂, ← h₁]
  group

theorem not_mem_zpowers_of_pow_four {G : Type*} [Group G] {a r : G} (h4 : r ^ 4 = 1)
    (h0 : a ≠ 1) (h1 : a ≠ r) (h2 : a ≠ r ^ 2) (h3 : a ≠ r ^ 3) : a ∉ Subgroup.zpowers r := by
  rintro ⟨k, hk⟩
  have h4' : r ^ (4 : ℤ) = 1 := by exact_mod_cast h4
  have hk' : r ^ (k % 4) = a := by rw [← zpow_eq_zpow_emod k h4']; exact hk
  have hc : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hc with hc | hc | hc | hc <;> rw [hc] at hk'
  · exact h0 (by rw [← hk', zpow_zero])
  · exact h1 (by rw [← hk', zpow_one])
  · exact h2 (by rw [← hk']; exact zpow_ofNat r 2)
  · exact h3 (by rw [← hk']; exact zpow_ofNat r 3)

@[expose] noncomputable def conjAlt {n : ℕ} (σ : Perm (Fin n)) :
    alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
  MulAut.conjNormal σ⁻¹

theorem coe_conjAlt {n : ℕ} (σ : Perm (Fin n)) (x : alternatingGroup (Fin n)) :
    ((conjAlt σ x : alternatingGroup (Fin n)) : Perm (Fin n)) = σ⁻¹ * x * σ := by
  simp [conjAlt]

theorem card_center_of_altFacts {n : ℕ} (F : AltFacts (alternatingGroup (Fin n)))
    (σ : Perm (Fin n)) (hσ : σ * σ = 1)
    (htwist : ∃ x : Perm (Fin n), Perm.sign x = 1 ∧
      (x⁻¹ * σ⁻¹ * x * σ) * (x⁻¹ * σ⁻¹ * x * σ) = 1 ∧ x⁻¹ * σ⁻¹ * x * σ ≠ 1)
    {L : Type} [Group L] [Finite L] (α : L ≃* L) (hdatum : InvDatum L α)
    (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) (hact : PermAction α φ σ) :
    Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 := by
  have : Group.IsPerfect L := hdatum.perfect
  set π : L →* alternatingGroup (Fin n) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hπ
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, hπ]
    change φ (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hγ : ∀ a, conjAlt σ (conjAlt σ a) = a := fun a => by
    apply Subtype.ext
    rw [coe_conjAlt, coe_conjAlt, hσinv]
    calc σ * (σ * (a : Perm (Fin n)) * σ) * σ = (σ * σ) * (a : Perm (Fin n)) * (σ * σ) := by group
      _ = a := by rw [hσ]; group
  have htw : ∃ x₀ : alternatingGroup (Fin n),
      (x₀⁻¹ * conjAlt σ x₀) * (x₀⁻¹ * conjAlt σ x₀) = 1 ∧ x₀⁻¹ * conjAlt σ x₀ ≠ 1 := by
    obtain ⟨x, hx, h2, h1⟩ := htwist
    refine ⟨⟨x, Equiv.Perm.mem_alternatingGroup.2 hx⟩, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAlt, Subgroup.coe_one]
      rw [← h2]
      group
    · intro h
      apply h1
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAlt, Subgroup.coe_one] at this
      rw [← this]
      group
  have hact' : ∀ x, π (α x) = conjAlt σ (π x) := fun x => by
    apply Subtype.ext
    rw [coe_conjAlt]
    exact hact x
  have := card_ker_of_altFacts F (conjAlt σ) hγ htw π hsurj hker.le α hdatum.involutory hact'
    hdatum.sylow
  rwa [hker] at this

end Assembly

section Alt

open Equiv Equiv.Perm

theorem not_sq_dvd_360 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ¬ q ^ 2 ∣ 360 := by
  intro q hq hq2 hq3 hdvd
  have hle : q ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) hdvd
  have hq18 : q ≤ 18 := by nlinarith
  interval_cases q <;> first | omega | (norm_num at hq)

theorem not_sq_dvd_2520 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ¬ q ^ 2 ∣ 2520 := by
  intro q hq hq2 hq3 hdvd
  have hle : q ^ 2 ≤ 2520 := Nat.le_of_dvd (by norm_num) hdvd
  have hq50 : q ≤ 50 := by nlinarith
  interval_cases q <;> first | omega | (norm_num at hq)

namespace Six

@[expose] def b6 : Perm (Fin 6) := swap 0 3 * swap 1 2

theorem a6_sign : Perm.sign a6 = 1 := by decide

theorem b6_sign : Perm.sign b6 = 1 := by decide

theorem a6_sq : a6 * a6 = 1 := by decide

theorem b6_sq : b6 * b6 = 1 := by decide

theorem r6_pow_four : (a6 * b6) ^ 4 = 1 := by decide

theorem r6_pow_two : (a6 * b6) ^ 2 ≠ 1 := by decide

theorem a6_ne : a6 ≠ 1 ∧ a6 ≠ a6 * b6 ∧ a6 ≠ (a6 * b6) ^ 2 ∧ a6 ≠ (a6 * b6) ^ 3 := by decide

theorem refConj6 :
    ∀ t : Perm (Fin 6), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
    ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * a6 * g⁻¹ = t :=
  Certificates.certificate4100.1

theorem exp6 : ∀ g : Perm (Fin 6), g ^ 9 = 1 → g ^ 3 = 1 :=
  Certificates.certificate4100.2.1

theorem twist6 :
    ∀ a b : Fin 6, a ≠ b → ∃ x : Perm (Fin 6), Perm.sign x = 1 ∧
    (x⁻¹ * (swap a b)⁻¹ * x * swap a b) * (x⁻¹ * (swap a b)⁻¹ * x * swap a b) = 1 ∧
    x⁻¹ * (swap a b)⁻¹ * x * swap a b ≠ 1 :=
  Certificates.certificate4100.2.2

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem altFacts : AltFacts (alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : alternatingGroup (Fin 6) := ⟨a6, Equiv.Perm.mem_alternatingGroup.2 a6_sign⟩
  let b : alternatingGroup (Fin 6) := ⟨b6, Equiv.Perm.mem_alternatingGroup.2 b6_sign⟩
  have hab : ((a * b : alternatingGroup (Fin 6)) : Perm (Fin 6)) = a6 * b6 := rfl
  refine ⟨?_, ?_, cyclic_sylow_of_not_sq_dvd card_alt6 not_sq_dvd_360,
    three_sylow_of_card card_alt6 (by norm_num) (by norm_num) (fun g hg => ?_)⟩
  · refine conj_of_ref a ?_
    intro t ht ht1
    have ht' : (t : Perm (Fin 6)) * t = 1 := by simpa using congrArg Subtype.val ht
    obtain ⟨g, hg, hgt⟩ := refConj6 t (Equiv.Perm.mem_alternatingGroup.1 t.2) ht'
      (fun h => ht1 (Subtype.ext h))
    exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.2 hg⟩, Subtype.ext hgt⟩
  · have hx4 : (a * b) ^ 4 = 1 := Subtype.ext (by simpa using r6_pow_four)
    have hx2 : ¬ (a * b) ^ 2 = 1 := fun h => r6_pow_two (by simpa using congrArg Subtype.val h)
    refine ⟨a, b, 45, by decide, by rw [card_alt6], Subtype.ext a6_sq, Subtype.ext b6_sq, ?_, ?_⟩
    · have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a * b) (by simpa using hx2)
        (by simpa using hx4)
      simpa using this
    · refine not_mem_zpowers_of_pow_four hx4 ?_ ?_ ?_ ?_
      · exact fun h => a6_ne.1 (congrArg Subtype.val h)
      · exact fun h => a6_ne.2.1 (congrArg Subtype.val h)
      · exact fun h => a6_ne.2.2.1 (by simpa using congrArg Subtype.val h)
      · exact fun h => a6_ne.2.2.2 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using exp6 g (by simpa using congrArg Subtype.val hg))

end Six

namespace Seven

@[expose] def b7 : Perm (Fin 7) := swap 0 3 * swap 1 2

theorem a7_sign : Perm.sign a7 = 1 := by decide

theorem b7_sign : Perm.sign b7 = 1 := by decide

theorem a7_sq : a7 * a7 = 1 := by decide

theorem b7_sq : b7 * b7 = 1 := by decide

theorem r7_pow_four : (a7 * b7) ^ 4 = 1 := by decide

theorem r7_pow_two : (a7 * b7) ^ 2 ≠ 1 := by decide

theorem a7_ne : a7 ≠ 1 ∧ a7 ≠ a7 * b7 ∧ a7 ≠ (a7 * b7) ^ 2 ∧ a7 ≠ (a7 * b7) ^ 3 := by decide

theorem refConj7 :
    ∀ t : Perm (Fin 7), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
    ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * a7 * g⁻¹ = t :=
  Certificates.certificate4156.1

theorem exp7 : ∀ g : Perm (Fin 7), g ^ 9 = 1 → g ^ 3 = 1 :=
  Certificates.certificate4156.2.1

theorem twist7 :
    ∀ σ : Perm (Fin 7), σ.cycleType = {2, 2, 2} → σ * σ = 1 ∧
    ∃ x : Perm (Fin 7), Perm.sign x = 1 ∧
      (x⁻¹ * σ⁻¹ * x * σ) * (x⁻¹ * σ⁻¹ * x * σ) = 1 ∧ x⁻¹ * σ⁻¹ * x * σ ≠ 1 :=
  Certificates.certificate4156.2.2

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem altFacts : AltFacts (alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : alternatingGroup (Fin 7) := ⟨a7, Equiv.Perm.mem_alternatingGroup.2 a7_sign⟩
  let b : alternatingGroup (Fin 7) := ⟨b7, Equiv.Perm.mem_alternatingGroup.2 b7_sign⟩
  have hab : ((a * b : alternatingGroup (Fin 7)) : Perm (Fin 7)) = a7 * b7 := rfl
  refine ⟨?_, ?_, cyclic_sylow_of_not_sq_dvd card_alt7 not_sq_dvd_2520,
    three_sylow_of_card card_alt7 (by norm_num) (by norm_num) (fun g hg => ?_)⟩
  · refine conj_of_ref a ?_
    intro t ht ht1
    have ht' : (t : Perm (Fin 7)) * t = 1 := by simpa using congrArg Subtype.val ht
    obtain ⟨g, hg, hgt⟩ := refConj7 t (Equiv.Perm.mem_alternatingGroup.1 t.2) ht'
      (fun h => ht1 (Subtype.ext h))
    exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.2 hg⟩, Subtype.ext hgt⟩
  · have hx4 : (a * b) ^ 4 = 1 := Subtype.ext (by simpa using r7_pow_four)
    have hx2 : ¬ (a * b) ^ 2 = 1 := fun h => r7_pow_two (by simpa using congrArg Subtype.val h)
    refine ⟨a, b, 315, by decide, by rw [card_alt7], Subtype.ext a7_sq, Subtype.ext b7_sq, ?_, ?_⟩
    · have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a * b) (by simpa using hx2)
        (by simpa using hx4)
      simpa using this
    · refine not_mem_zpowers_of_pow_four hx4 ?_ ?_ ?_ ?_
      · exact fun h => a7_ne.1 (congrArg Subtype.val h)
      · exact fun h => a7_ne.2.1 (congrArg Subtype.val h)
      · exact fun h => a7_ne.2.2.1 (by simpa using congrArg Subtype.val h)
      · exact fun h => a7_ne.2.2.2 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using exp7 g (by simpa using congrArg Subtype.val hg))

end Seven

theorem altOuterCover : AltOuterCover := by
  intro L _ _ α hdatum hcases
  rcases hcases with ⟨φ, σ, hσ, hact⟩ | ⟨φ, σ, hσ, hact⟩
  · obtain ⟨a, b, hab, rfl⟩ := hσ
    exact card_center_of_altFacts Six.altFacts (swap a b) (swap_mul_self a b)
      (Six.twist6 a b hab) α hdatum φ hact
  · obtain ⟨hσ2, htw⟩ := Seven.twist7 σ hσ
    exact card_center_of_altFacts Seven.altFacts σ hσ2 htw α hdatum φ hact

end Alt

end CFSG.QuasithinUnique.Ch1
