module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem eq_one_of_mem_fusionOddCore_of_sq {K : Type} [Group K] [Finite K] {x : K}
    (hx : x ∈ fusionOddCore K) (hx2 : x * x = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
  have hodd : Odd (orderOf x) :=
    (odd_natCard_fusionOddCore K).of_dvd_nat ((fusionOddCore K).orderOf_dvd_natCard hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · obtain ⟨m, hm⟩ := hodd
    rw [h] at hm
    exfalso
    omega

theorem dihedral_conj_pow {G : Type*} [Group G] {t u : G} (ht : t * t = 1) (hu : u * u = 1)
    {m : ℕ} (h : (t * u) ^ (2 * m + 1) = 1) : (t * u) ^ m * t * ((t * u) ^ m)⁻¹ = u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h1 : t * (t * u) * t⁻¹ = (t * u)⁻¹ := by
    rw [mul_inv_rev, hti, hui, ← mul_assoc, ht, one_mul]
  have h2 : t * (t * u) ^ m * t⁻¹ = ((t * u) ^ m)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : (t * u) ^ (2 * m) = (t * u)⁻¹ := by
    rw [pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h
  symm
  calc u = (t * u)⁻¹ * t := by rw [mul_inv_rev, hti, hui, mul_assoc, ht, mul_one]
    _ = (t * u) ^ m * (t * u) ^ m * t := by rw [← pow_add, ← two_mul, h3]
    _ = (t * u) ^ m * t * (t * (t * u) ^ m * t⁻¹) := by
        rw [hti]
        simp only [mul_assoc]
        rw [← mul_assoc t t, ht, one_mul]
    _ = (t * u) ^ m * t * ((t * u) ^ m)⁻¹ := by rw [h2]

theorem exists_conj_of_mk_conj {K : Type} [Group K] [Finite K] {z α : K} (hz : z * z = 1)
    (hα : α * α = 1) (hα1 : α ≠ 1) (k : K)
    (h : (QuotientGroup.mk (k * z * k⁻¹) : K ⧸ fusionOddCore K) = QuotientGroup.mk α) :
    ∃ g : K, g * z * g⁻¹ = α := by
  have hy : k * z * k⁻¹ * (k * z * k⁻¹) = 1 := by
    have e : k * z * k⁻¹ * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
    rw [e, hz]
    simp
  have hαy : α * (k * z * k⁻¹) ∈ fusionOddCore K := by
    have h1 := (fusionOddCore K).inv_mem (QuotientGroup.eq.1 h)
    rwa [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right hα] at h1
  obtain ⟨m, hm⟩ : Odd (orderOf (α * (k * z * k⁻¹))) :=
    (odd_natCard_fusionOddCore K).of_dvd_nat ((fusionOddCore K).orderOf_dvd_natCard hαy)
  have hpow : (α * (k * z * k⁻¹)) ^ (2 * m + 1) = 1 := by
    rw [← hm, pow_orderOf_eq_one]
  have hxy := dihedral_conj_pow hα hy hpow
  have key : ∀ x : K, x * α * x⁻¹ = k * z * k⁻¹ → (x⁻¹ * k) * z * (x⁻¹ * k)⁻¹ = α := by
    intro x hx
    calc (x⁻¹ * k) * z * (x⁻¹ * k)⁻¹ = x⁻¹ * (k * z * k⁻¹) * x := by group
      _ = x⁻¹ * (x * α * x⁻¹) * x := by rw [← hx]
      _ = α := by group
  exact ⟨((α * (k * z * k⁻¹)) ^ m)⁻¹ * k, key _ hxy⟩

theorem outerTable_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {z α t g₁ g₂ h₁ h₂ : X}
    (h : OuterTable z α t g₁ g₂ h₁ h₂) (hα1 : f α ≠ 1) (ht1 : f t ≠ 1) (hαt : f α ≠ f t) :
    OuterTable (f z) (f α) (f t) (f g₁) (f g₂) (f h₁) (f h₂) := by
  unfold OuterTable at h ⊢
  obtain ⟨hz, hα, ht, -, -, -, hcomm, hzα, hzt, hh1, hh2, hP, hcc, hg1, hg2, hr1, hr2, hr3, hr4,
    hc1, hc2⟩ := h
  refine ⟨?_, ?_, ?_, hα1, ht1, hαt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simpa only [map_mul, map_one] using congrArg f hz
  · simpa only [map_mul, map_one] using congrArg f hα
  · simpa only [map_mul, map_one] using congrArg f ht
  · simpa only [map_mul] using congrArg f hcomm
  · simpa only [map_mul, map_inv] using congrArg f hzα
  · simpa only [map_mul, map_inv] using congrArg f hzt
  · simpa only [map_mul, map_inv] using congrArg f hh1
  · simpa only [map_mul, map_inv] using congrArg f hh2
  · have e : ({f α, f t, f g₁, f g₂, f h₁, f h₂} : Set Y) =
        f '' ({α, t, g₁, g₂, h₁, h₂} : Set X) := by
      simp only [Set.image_insert_eq, Set.image_singleton]
    rw [e, ← MonoidHom.map_closure]
    exact hP.map f
  · have key : ∀ c ∈ ({g₁, g₂, h₁, h₂} : Set X),
        f c * f α = f α * f c ∧ f c * f t = f t * f c := by
      intro c hc
      obtain ⟨e1, e2⟩ := hcc c hc
      exact ⟨by simpa only [map_mul] using congrArg f e1,
        by simpa only [map_mul] using congrArg f e2⟩
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ : ∃ c0 ∈ ({g₁, g₂, h₁, h₂} : Set X), f c0 = c := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨g₁, by simp, rfl⟩
      · exact ⟨g₂, by simp, rfl⟩
      · exact ⟨h₁, by simp, rfl⟩
      · exact ⟨h₂, by simp, rfl⟩
    exact key c0 hc0
  · rcases hg1 with e | e
    · exact Or.inl (by simpa only [map_mul, map_one] using congrArg f e)
    · exact Or.inr (by simpa only [map_mul] using congrArg f e)
  · rcases hg2 with e | e
    · exact Or.inl (by simpa only [map_mul, map_one] using congrArg f e)
    · exact Or.inr (by simpa only [map_mul] using congrArg f e)
  · simpa only [map_mul, map_inv] using congrArg f hr1
  · simpa only [map_mul, map_inv] using congrArg f hr2
  · simpa only [map_mul, map_inv] using congrArg f hr3
  · simpa only [map_mul, map_inv] using congrArg f hr4
  · simpa only [map_mul] using congrArg f hc1
  · simpa only [map_mul] using congrArg f hc2

theorem table_mk {K : Type} [Group K] [Finite K] {z α t g₁ g₂ h₁ h₂ : K}
    (h : OuterTable z α t g₁ g₂ h₁ h₂) :
    OuterTable (QuotientGroup.mk z : K ⧸ fusionOddCore K) (QuotientGroup.mk α) (QuotientGroup.mk t)
      (QuotientGroup.mk g₁) (QuotientGroup.mk g₂) (QuotientGroup.mk h₁) (QuotientGroup.mk h₂) := by
  have h' := h
  unfold OuterTable at h'
  obtain ⟨-, hα, ht, hα1, ht1, hαt, hcomm, -⟩ := h'
  have hα1' : (QuotientGroup.mk α : K ⧸ fusionOddCore K) ≠ 1 := by
    intro hm
    rw [QuotientGroup.eq_one_iff] at hm
    exact hα1 (eq_one_of_mem_fusionOddCore_of_sq hm hα)
  have ht1' : (QuotientGroup.mk t : K ⧸ fusionOddCore K) ≠ 1 := by
    intro hm
    rw [QuotientGroup.eq_one_iff] at hm
    exact ht1 (eq_one_of_mem_fusionOddCore_of_sq hm ht)
  have hαt' : (QuotientGroup.mk α : K ⧸ fusionOddCore K) ≠ QuotientGroup.mk t := by
    intro he
    rw [QuotientGroup.eq, inv_eq_of_mul_eq_one_right hα] at he
    have hsq : α * t * (α * t) = 1 := by
      calc α * t * (α * t) = α * (t * α) * t := by group
        _ = α * (α * t) * t := by rw [← hcomm]
        _ = α * α * (t * t) := by group
        _ = 1 := by rw [hα, ht, one_mul]
    have h1 : α * t = 1 := eq_one_of_mem_fusionOddCore_of_sq he hsq
    exact hαt ((mul_eq_one_iff_eq_inv.1 h1).trans (inv_eq_of_mul_eq_one_right ht))
  exact outerTable_map (QuotientGroup.mk' (fusionOddCore K)) h hα1' ht1' hαt'

theorem outerNoTable_of_cases (hA : OuterTableU43) (hB : OuterTableWreath) : OuterNoTable := by
  unfold OuterNoTable
  intro K _ _ z α t g₁ g₂ h₁ h₂ hl96 htab hnconj
  have htab' := table_mk htab
  obtain ⟨hz, hα, -, hα1, -⟩ := htab
  unfold Lemma96Conclusion SolomonM10Conclusion at hl96
  obtain ⟨-, hcase⟩ := hl96
  rcases hcase with ⟨N, hN, hiso, hcent⟩ | hiso
  · exact hB (K ⧸ fusionOddCore K) N hN hiso hcent _ _ _ _ _ _ _ htab'
  · obtain ⟨kb, hkb⟩ := hA (K ⧸ fusionOddCore K) hiso _ _ _ _ _ _ _ htab'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
    have hmk : (QuotientGroup.mk (k * z * k⁻¹) : K ⧸ fusionOddCore K) = QuotientGroup.mk α := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hkb
    obtain ⟨g, hg⟩ := exists_conj_of_mk_conj hz hα hα1 k hmk
    exact hnconj g hg

end CFSG.EvenSporadicStandard.Fin76b
