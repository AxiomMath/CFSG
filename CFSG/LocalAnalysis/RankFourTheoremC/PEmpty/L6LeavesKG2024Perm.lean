module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Orbit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024CaseOne
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Hol

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Equiv Equiv.Perm Subgroup CFSG.Open

def omegaOneCenter {G : Type*} [Group G] (S : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ S ∧ (∀ s ∈ S, x * s = s * x) ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨haS, haC, ha2⟩ ⟨hbS, hbC, hb2⟩
    refine ⟨S.mul_mem haS hbS, fun s hs => ?_, ?_⟩
    · calc a * b * s = a * (b * s) := mul_assoc _ _ _
        _ = a * (s * b) := by rw [hbC s hs]
        _ = (a * s) * b := (mul_assoc _ _ _).symm
        _ = (s * a) * b := by rw [haC s hs]
        _ = s * (a * b) := mul_assoc _ _ _
    · have hba : b * a = a * b := (haC b hbS).symm
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨S.one_mem, fun s _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haS, haC, ha2⟩
    refine ⟨S.inv_mem haS, fun s hs => ?_, ?_⟩
    · have h1 := haC s hs
      calc a⁻¹ * s = a⁻¹ * (s * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * s) * a⁻¹ := by rw [h1]
        _ = s * a⁻¹ := by group
    · calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha2, inv_one]

section OmegaOne

variable {G : Type*} [Group G] {S : Subgroup G}

theorem omegaOneCenter_le : omegaOneCenter S ≤ S := fun _ hx => hx.1

theorem omegaOneCenter_ne_bot [Finite G] (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hS
  haveI : Nontrivial ↥(Subgroup.center ↥S) := hS2.center_nontrivial
  have hC2 : IsPGroup 2 ↥(Subgroup.center ↥S) := hS2.to_subgroup _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hC2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card ↥(Subgroup.center ↥S) = 1 := by simpa using hn
    exact (Finite.one_lt_card (α := ↥(Subgroup.center ↥S))).ne' this
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥S) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2 hdvd
  intro hbot
  have hcS : ((c : ↥S) : G) ∈ omegaOneCenter S := by
    refine ⟨(c : ↥S).2, fun s hs => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 c.2 ⟨s, hs⟩
      exact congrArg Subtype.val this.symm
    · have h2 : (c : ↥S) ^ 2 = 1 := by
        have : c ^ 2 = 1 := hc ▸ pow_orderOf_eq_one c
        simpa using congrArg Subtype.val this
      have h2' : ((c : ↥S) : G) ^ 2 = 1 := by
        simpa using congrArg Subtype.val h2
      simpa [pow_two] using h2'
  rw [hbot, Subgroup.mem_bot] at hcS
  have hc1 : c = 1 := Subtype.ext (Subtype.ext hcS)
  rw [hc1, orderOf_one] at hc
  omega

theorem conj_mem_omegaOneCenter {z x : G} (hz : z ∈ normalizer (S : Set G))
    (hx : x ∈ omegaOneCenter S) : z * x * z⁻¹ ∈ omegaOneCenter S := by
  obtain ⟨hxS, hxC, hx2⟩ := hx
  refine ⟨(Subgroup.mem_set_normalizer_iff.1 hz x).1 hxS, fun s hs => ?_, ?_⟩
  · have hs' : z⁻¹ * s * z ∈ S := (Subgroup.mem_set_normalizer_iff''.1 hz s).1 hs
    calc z * x * z⁻¹ * s = z * (x * (z⁻¹ * s * z)) * z⁻¹ := by group
      _ = z * ((z⁻¹ * s * z) * x) * z⁻¹ := by rw [hxC _ hs']
      _ = s * (z * x * z⁻¹) := by group
  · calc z * x * z⁻¹ * (z * x * z⁻¹) = z * (x * x) * z⁻¹ := by group
      _ = 1 := by rw [hx2]; group

theorem omegaOneCenter_inv {z : G} (hz : z ∈ normalizer (S : Set G)) :
    ∀ x, x ∈ omegaOneCenter S ↔ z * x * z⁻¹ ∈ omegaOneCenter S := by
  intro x
  refine ⟨conj_mem_omegaOneCenter hz, fun hx => ?_⟩
  have := conj_mem_omegaOneCenter ((normalizer (S : Set G)).inv_mem hz) hx
  have e : z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x := by group
  rwa [e] at this

end OmegaOne

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem sign_conj (z t : Perm Ω) : Perm.sign (z * t * z⁻¹) = Perm.sign t := by
  rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign z) (Perm.sign t), mul_assoc,
    mul_inv_cancel, mul_one]

theorem le_alternating_of_section {Y D : Subgroup (Perm Ω)} (hs : S622IsSimpleSection Y D)
    (hD : D ≤ alternatingGroup Ω) : Y ≤ alternatingGroup Ω := by
  obtain ⟨hDY, -, -, hmin, hnab⟩ := hs
  have hDN : D ≤ Y ⊓ alternatingGroup Ω := le_inf hDY hD
  have hNn : ((Y ⊓ alternatingGroup Ω).subgroupOf Y).Normal := by
    have e : (Y ⊓ alternatingGroup Ω).subgroupOf Y = (Perm.sign.comp Y.subtype).ker := by
      ext y
      simp [Subgroup.mem_subgroupOf, mem_alternatingGroup, MonoidHom.mem_ker]
    rw [e]
    infer_instance
  rcases hmin _ hDN inf_le_left hNn with h | h
  · exfalso
    apply hnab
    intro a ha b hb
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ Y ⊓ alternatingGroup Ω := by
      refine Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha))
        (Y.inv_mem hb), ?_⟩
      rw [mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (commutatorElement_eq_one_iff_mul_comm (g₁ := Perm.sign a)
        (g₂ := Perm.sign b)).2 (mul_comm _ _)
    rw [h] at hmem
    exact hmem
  · intro y hy
    have : y ∈ Y ⊓ alternatingGroup Ω := by rw [h]; exact hy
    exact this.2

theorem le_alternating_of_minimal {z : Perm Ω} {T : Subgroup (Perm Ω)}
    (hTinv : ∀ t, t ∈ T ↔ z * t * z⁻¹ ∈ T)
    (hTmin : ∀ T₁ : Subgroup (Perm Ω), T₁ ≤ T → (∀ t, t ∈ T₁ ↔ z * t * z⁻¹ ∈ T₁) →
      T₁ = ⊥ ∨ T₁ = T)
    (hcard : 3 ≤ Nat.card ↥T) : T ≤ alternatingGroup Ω := by
  have hT₁inv : ∀ t, t ∈ T ⊓ alternatingGroup Ω ↔ z * t * z⁻¹ ∈ T ⊓ alternatingGroup Ω := by
    intro t
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hTinv t, mem_alternatingGroup, mem_alternatingGroup,
      sign_conj]
  rcases hTmin _ inf_le_left hT₁inv with h | h
  · exfalso
    let φ : ↥T →* ℤˣ := Perm.sign.comp T.subtype
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro t ht
      have hmem : (t : Perm Ω) ∈ T ⊓ alternatingGroup Ω := ⟨t.2, mem_alternatingGroup.2 ht⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
    omega
  · intro t ht
    have : t ∈ T ⊓ alternatingGroup Ω := by rw [h]; exact ht
    exact this.2

theorem perm_level {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {z : Perm Ω} (hz : orderOf z = p)
    (hn : Fintype.card Ω < 2 * p) {S : Subgroup (Perm Ω)} (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set (Perm Ω))) :
    ∃ T Y D : Subgroup (Perm Ω), T ≤ S ∧ T ≠ ⊥ ∧ z ∈ normalizer (T : Set (Perm Ω)) ∧
      S ≤ normalizer (T : Set (Perm Ω)) ∧ Y ≤ normalizer (T : Set (Perm Ω)) ∧
      Y ≤ alternatingGroup Ω ∧ z ∈ Y ∧ S622IsSimpleSection Y D ∧ Nat.Coprime p (Nat.card D) ∧
      3 ∣ D.relIndex Y := by
  obtain ⟨T, hTU, hT0, hTinv, hTmin⟩ := exists_minimal_invariant z (omegaOneCenter S)
    (omegaOneCenter_ne_bot hS2 hS) (omegaOneCenter_inv hzS)
  have hTS : T ≤ S := hTU.trans omegaOneCenter_le
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => (hTU hs).2.1 t (hTS ht)
  have hTsq : ∀ t ∈ T, t * t = 1 := fun t ht => (hTU ht).2.2
  have hT2 : IsPGroup 2 T :=
    hS2.of_injective (Subgroup.inclusion hTS) (Subgroup.inclusion_injective hTS)
  have hTnorm : z ∈ normalizer (T : Set (Perm Ω)) := Subgroup.mem_set_normalizer_iff.2 hTinv
  have hSnorm : S ≤ normalizer (T : Set (Perm Ω)) := fun s hs =>
    mem_normalizer_of_commute fun t ht => ((hTU ht).2.1 s hs).symm
  have hp2 : p ≠ 2 := by omega
  by_cases hfix : ∀ x, z x ≠ x → ∀ t ∈ T, t x = x
  · obtain ⟨Y, hYalt, hYnorm, hzY, hsec, h3⟩ := case_one hp hp5 hz hn T hfix
    refine ⟨T, Y, ⊥, hTS, hT0, hTnorm, hSnorm, hYnorm, hYalt, hzY, hsec, ?_, ?_⟩
    · simp
    · rwa [Subgroup.relIndex_bot_left]
  · push Not at hfix
    have hset : OrbitSetting p z T := ⟨hp, hp5, hz, hn, hT2, hTcomm, hTsq, hTinv, hTmin⟩
    obtain ⟨o, hzo, hfree, hsub, hout⟩ := hset.orbit_structure hfix
    have hcard : 5 ≤ Nat.card ↥T := by
      classical
      haveI : Fintype ↥T := Fintype.ofFinite ↥T
      have hsubset : z.support ⊆
          (Finset.univ : Finset ↥T).image (fun s : ↥T => (s : Perm Ω) o) := by
        intro x hx
        obtain ⟨s, hs, hsx⟩ := hsub x (Equiv.Perm.mem_support.1 hx)
        exact Finset.mem_image.2 ⟨⟨s, hs⟩, Finset.mem_univ _, hsx⟩
      have h1 := Finset.card_le_card hsubset
      have h2 := Finset.card_image_le (s := (Finset.univ : Finset ↥T))
        (f := fun s : ↥T => (s : Perm Ω) o)
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
      rw [card_support_eq hp hz hn] at h1
      omega
    obtain ⟨Y, -, hYnorm, hzY, hsec, h3⟩ :=
      hol_exists T z o hTcomm hTsq hTinv hzo hfree hout hcard
    have hTalt : T ≤ alternatingGroup Ω := le_alternating_of_minimal hTinv hTmin (by omega)
    refine ⟨T, Y, T, hTS, hT0, hTnorm, hSnorm, hYnorm, le_alternating_of_section hsec hTalt, hzY,
      hsec, ?_, h3⟩
    obtain ⟨n, hn2⟩ := (IsPGroup.iff_card).1 hT2
    rw [hn2]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
