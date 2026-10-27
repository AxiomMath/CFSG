module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup

section Perm5

theorem s3a_perm5_cent (n : Perm (Fin 5))
    (h : ∀ a ∈ alternatingGroup (Fin 5), n * a = a * n) : n = 1 := by
  have key : ∀ n : Perm (Fin 5), n * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * n →
      n * (finRotate 5) = (finRotate 5) * n → n = 1 := by decide +kernel
  exact key n (h _ (Perm.mem_alternatingGroup.2 (by decide +kernel)))
    (h _ (Perm.mem_alternatingGroup.2 (by decide +kernel)))

theorem s3a_perm5_center (k : Perm (Fin 5)) (hk : k ≠ 1) : ∃ x : Perm (Fin 5), k * x ≠ x * k := by
  by_contra hcon
  push Not at hcon
  exact hk (s3a_perm5_cent k fun a _ => hcon a)

theorem s3a_perm5_normal (N : Subgroup (Perm (Fin 5))) [N.Normal] (hN : N ≠ ⊥) :
    alternatingGroup (Fin 5) ≤ N := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5)))
    with h | h
  · exfalso
    apply hN
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply s3a_perm5_cent
    intro a ha
    have h1 : a * n * a⁻¹ * n⁻¹ ∈ N := by
      have := N.mul_mem (Normal.conj_mem inferInstance n hn a) (N.inv_mem hn)
      simpa [mul_assoc] using this
    have h2 : a * n * a⁻¹ * n⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Perm.mem_alternatingGroup] at ha ⊢
      simp [ha]
    have h3 : (⟨a * n * a⁻¹ * n⁻¹, h2⟩ : ↥(alternatingGroup (Fin 5))) ∈
        N.subgroupOf (alternatingGroup (Fin 5)) := h1
    rw [h] at h3
    have h4 : a * n * a⁻¹ * n⁻¹ = 1 := by simpa using congrArg Subtype.val (Subgroup.mem_bot.1 h3)
    calc n * a = (a * n * a⁻¹ * n⁻¹) * (n * a) := by rw [h4, one_mul]
      _ = a * n := by group
  · intro x hx
    have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 5))) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
      h ▸ Subgroup.mem_top _
    exact this

end Perm5

section Cent

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_zpowers_iff (ht : t * t = 1) {x : D} : x ∈ zpowers t ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
    have e : n = n % 2 + 2 * (n / 2) := (Int.emod_add_mul_ediv n 2).symm
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [e, h, zpow_add, zpow_mul, h2, one_zpow]
      simp
    · right
      rw [e, h, zpow_add, zpow_mul, h2, one_zpow]
      simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem s3a_K_comm (h : DShape D t K) {k : D} (hk : k ∈ K) : t * k = k * t := by
  have : k ∈ centralizer ({t} : Set D) := by
    rw [h.cent]
    exact Subgroup.mem_sup_right hk
  exact (mem_centralizer_iff.1 this) t rfl

theorem s3a_orderOf_t (h : DShape D t K) : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne

theorem s3a_hcomm (h : DShape D t K) :
    ∀ (m : ↥(zpowers t)) (n : ↥K), Commute ((zpowers t).subtype m) (K.subtype n) := by
  intro m n
  obtain ⟨a, ha⟩ := m
  obtain ⟨k, hk⟩ := n
  obtain ha' | ha' := (s3a_zpowers_iff h.t_sq).1 ha
  · show Commute a k
    rw [ha']
    exact Commute.one_left _
  · show Commute a k
    rw [ha']
    exact (s3a_K_comm h hk : t * k = k * t)

theorem s3a_cent_decomp (h : DShape D t K) {c : D} (hc : c ∈ centralizer ({t} : Set D)) :
    ∃ k ∈ K, c = k ∨ c = t * k := by
  have hcomm := s3a_hcomm h
  have hrange := MonoidHom.noncommCoprod_range (zpowers t).subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype, ← h.cent] at hrange
  have hc' : c ∈ (((zpowers t).subtype).noncommCoprod K.subtype hcomm).range := by
    rw [hrange]; exact hc
  obtain ⟨⟨⟨a, ha⟩, ⟨k, hk⟩⟩, hak⟩ := hc'
  refine ⟨k, hk, ?_⟩
  simp only [MonoidHom.noncommCoprod_apply] at hak
  obtain ha' | ha' := (s3a_zpowers_iff h.t_sq).1 ha
  · left
    rw [← hak]
    simp [ha']
  · right
    rw [← hak]
    simp [ha']

theorem s3a_card_cent_le (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) :
    Nat.card ↥(centralizer ({t} : Set D)) ≤ 240 := by
  have hcomm := s3a_hcomm h
  set F := ((zpowers t).subtype).noncommCoprod K.subtype hcomm with hF
  have hrange : F.range = centralizer ({t} : Set D) := by
    rw [hF, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, h.cent]
  have hsurj := Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective F)
  rw [hrange] at hsurj
  have h1 : Nat.card ↥(zpowers t) = 2 := by rw [Nat.card_zpowers]; exact s3a_orderOf_t h
  have h2 : Nat.card ↥K = 120 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have h3 : Nat.card (↥(zpowers t) × ↥K) = 240 := by rw [Nat.card_prod, h1, h2]
  rw [h3] at hsurj
  exact hsurj

@[expose] def s3a_iota (ψ : ↥K ≃* Perm (Fin 5)) : ↥(alternatingGroup (Fin 5)) →* D :=
  K.subtype.comp (ψ.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)

theorem s3a_iota_apply (ψ : ↥K ≃* Perm (Fin 5)) (a : ↥(alternatingGroup (Fin 5))) :
    s3a_iota ψ a = ((ψ.symm (a : Perm (Fin 5)) : ↥K) : D) := rfl

theorem s3a_cent_iota (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) {x : D}
    (hx : x ∈ centralizer ({t} : Set D))
    (hc : ∀ a : ↥(alternatingGroup (Fin 5)), x * s3a_iota ψ a = s3a_iota ψ a * x) :
    x = 1 ∨ x = t := by
  obtain ⟨k, hk, hxk⟩ := s3a_cent_decomp h hx
  have hk1 : (⟨k, hk⟩ : ↥K) = 1 := by
    apply ψ.injective
    rw [map_one]
    apply s3a_perm5_cent
    intro a ha
    have h1 := hc ⟨a, ha⟩
    rw [s3a_iota_apply] at h1
    have h2 : k * ((ψ.symm a : ↥K) : D) = ((ψ.symm a : ↥K) : D) * k := by
      rcases hxk with rfl | rfl
      · exact h1
      · have es := s3a_K_comm h (ψ.symm a).2
        have e2 : t * (k * ((ψ.symm a : ↥K) : D)) = t * (((ψ.symm a : ↥K) : D) * k) := by
          calc t * (k * ((ψ.symm a : ↥K) : D)) = (t * k) * ((ψ.symm a : ↥K) : D) := by
                rw [mul_assoc]
            _ = ((ψ.symm a : ↥K) : D) * (t * k) := h1
            _ = (((ψ.symm a : ↥K) : D) * t) * k := by rw [mul_assoc]
            _ = (t * ((ψ.symm a : ↥K) : D)) * k := by rw [es]
            _ = _ := by rw [mul_assoc]
        exact mul_left_cancel e2
    have h3 : (⟨k, hk⟩ : ↥K) * ψ.symm a = ψ.symm a * ⟨k, hk⟩ := Subtype.ext h2
    have h4 : ψ (⟨k, hk⟩ * ψ.symm a) = ψ (ψ.symm a * ⟨k, hk⟩) := congrArg ψ h3
    simpa using h4
  have : k = 1 := congrArg Subtype.val hk1
  rcases hxk with rfl | rfl
  · exact Or.inl this
  · right; rw [this, mul_one]

end Cent

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
