module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDefs

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

section Inn

variable {Y : Type*} [Group Y]

instance inn_normal : (inn Y).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ φ
    refine ⟨φ x, ?_⟩
    ext z
    simp [MulAut.conj_apply]

theorem pow_mem_inn_of_mul {a α : MulAut Y} (ha : a ∈ inn Y) {e : ℕ} (hα : α ^ e ∈ inn Y) :
    (a * α) ^ e ∈ inn Y := by
  have h : (QuotientGroup.mk (a * α) : MulAut Y ⧸ inn Y) = QuotientGroup.mk α := by
    rw [QuotientGroup.eq]
    have := (inn_normal (Y := Y)).conj_mem a⁻¹ (inv_mem ha) α⁻¹
    simpa [mul_assoc] using this
  rw [← QuotientGroup.eq_one_iff] at hα ⊢
  rw [QuotientGroup.mk_pow, h, ← QuotientGroup.mk_pow]
  exact hα

theorem OutPInner.of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card (MulAut Y ⧸ inn Y)) :
    OutPInner Y p := by
  intro P hP x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : (QuotientGroup.mk x : MulAut Y ⧸ inn Y) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [this, QuotientGroup.mk_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 := orderOf_dvd_natCard (QuotientGroup.mk x : MulAut Y ⧸ inn Y)
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi0 : i = 0 := by
    by_contra hne
    exact h ((dvd_pow_self p hne).trans (hio ▸ h3))
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hio
  exact (QuotientGroup.eq_one_iff x).1 hio

end Inn

section Tower

variable {A : Type*} [Group A]

theorem exists_gen_mod {D E P : Subgroup A} (hPE : P ≤ E)
    (hEN : E ≤ Subgroup.normalizer (D : Set A))
    (hE : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) :
    ∃ a ∈ P, ∀ x ∈ P, ∃ k : ℤ, (a ^ k)⁻¹ * x ∈ D := by
  classical
  have : (D.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  set ρ : ↥E →* ↥E ⧸ D.subgroupOf E := QuotientGroup.mk' _ with hρ
  obtain ⟨g, hgE, hg⟩ := hE
  have hcyc : IsCyclic (↥E ⧸ D.subgroupOf E) := by
    refine ⟨ρ ⟨g, hgE⟩, fun q => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hg x.1 x.2
    refine ⟨-k, ?_⟩
    change (ρ ⟨g, hgE⟩) ^ (-k) = ρ x
    rw [← map_zpow]
    refine (QuotientGroup.eq).2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hk
  set Q : Subgroup (↥E ⧸ D.subgroupOf E) := (P.subgroupOf E).map ρ with hQ
  have : IsCyclic ↥Q := Subgroup.isCyclic Q
  obtain ⟨g', hg'⟩ := IsCyclic.exists_generator (α := ↥Q)
  obtain ⟨a, haP, ha⟩ := g'.2
  refine ⟨a.1, haP, fun x hx => ?_⟩
  have hxQ : ρ ⟨x, hPE hx⟩ ∈ Q := ⟨⟨x, hPE hx⟩, hx, rfl⟩
  obtain ⟨k, hk⟩ := hg' ⟨_, hxQ⟩
  refine ⟨k, ?_⟩
  have h2 : ρ (a ^ k) = ρ ⟨x, hPE hx⟩ := by
    rw [map_zpow, ha]
    exact congrArg Subtype.val hk
  have h3 := (QuotientGroup.eq).1 h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem exists_two_gen_of_tower {I D E P : Subgroup A} (hPE : P ≤ E)
    (hEN : E ≤ Subgroup.normalizer (D : Set A)) (hDI : D ≤ Subgroup.normalizer (I : Set A))
    (hD : ∃ d ∈ D, ∀ x ∈ D, ∃ k : ℤ, d ^ k * x ∈ I)
    (hE : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) :
    ∃ a ∈ P, ∃ b ∈ P, P ≤ Subgroup.closure {a, b} ⊔ I := by
  obtain ⟨a, haP, ha⟩ := exists_gen_mod hPE hEN hE
  obtain ⟨b, hbPD, hb⟩ := exists_gen_mod (D := I) (E := D) (P := P ⊓ D) inf_le_right hDI hD
  refine ⟨a, haP, b, hbPD.1, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := ha x hx
  have hzP : (a ^ k)⁻¹ * x ∈ P := P.mul_mem (P.inv_mem (P.zpow_mem haP k)) hx
  obtain ⟨m, hm⟩ := hb _ ⟨hzP, hk⟩
  have hx' : x = (a ^ k * b ^ m) * ((b ^ m)⁻¹ * ((a ^ k)⁻¹ * x)) := by group
  rw [hx']
  refine Subgroup.mul_mem_sup (mul_mem (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) m)) hm

end Tower

theorem OutPTwoGen.of_tower {Y : Type*} [Group Y] {p : ℕ} (D E : Subgroup (MulAut Y))
    (hEN : E ≤ Subgroup.normalizer (D : Set (MulAut Y)))
    (hD : ∃ d ∈ D, ∀ x ∈ D, ∃ k : ℤ, d ^ k * x ∈ inn Y)
    (hE : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D)
    (hp : ∀ x : MulAut Y, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ E) : OutPTwoGen Y p := by
  intro P hP
  have hPE : P ≤ E := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact hp x ⟨k, congrArg Subtype.val hk⟩
  refine exists_two_gen_of_tower hPE hEN ?_ hD hE
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro i
  exact ⟨fun hi => (inn_normal (Y := Y)).conj_mem i hi d, fun hi => by
    simpa [mul_assoc] using (inn_normal (Y := Y)).conj_mem _ hi d⁻¹⟩

end CFSG.AGLEmbedding.ParabAutIrr
