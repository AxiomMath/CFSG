module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPhi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartMove

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma sec5b_phi_zero {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) : φ 0 = 1 := by
  have hz : IsEvenVec (0 : Fin 8 → ZMod 2) := sec5b_isEvenVec_zero
  have hmul : φ 0 * φ 0 = φ 0 := by
    simpa using (hd.add 0 0 hz hz).symm
  exact mul_eq_right.mp hmul

private lemma sec5b_phi_one {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) : φ 1 = 1 := by
  have hz : IsEvenVec (0 : Fin 8 → ZMod 2) := sec5b_isEvenVec_zero
  simpa [sec5b_phi_zero hd] using hd.add_one 0 hz

theorem sec5b_weight_rep {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) {x : G} (hx : x ∈ A)
    (hx1 : x ≠ 1) : ∃ v, IsEvenVec v ∧ φ v = x ∧ (vecWeight v = 2 ∨ vecWeight v = 4) := by
  obtain ⟨v, hv, hvx⟩ := hd.surj x hx
  rcases sec5b_weight_cases hv with h0 | h2 | h4 | h6 | h8
  · exact absurd (by rw [← hvx, eq_zero_of_vecWeight_eq_zero h0, sec5b_phi_zero hd]) hx1
  · exact ⟨v, hv, hvx, Or.inl h2⟩
  · exact ⟨v, hv, hvx, Or.inr h4⟩
  · refine ⟨v + 1, sec5b_isEvenVec_add hv sec5b_isEvenVec_one, ?_, Or.inl ?_⟩
    · rw [hd.add_one v hv, hvx]
    · rw [sec5b_vecWeight_add_one v, h6]
  · exact absurd (by rw [← hvx, sec5b_eq_one_of_weight_eight h8, sec5b_phi_one hd]) hx1

theorem sec5b_conj_weight {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) {v w : Fin 8 → ZMod 2}
    (hv : IsEvenVec v) (hw : IsEvenVec w) (hy : φ w ∈ conjClassIn M (φ v)) :
    vecWeight w = vecWeight v ∨ vecWeight w = 8 - vecWeight v := by
  obtain ⟨σ, _hσ, hσw⟩ := (sec5b_mem_conj_iff hd hv).mp hy
  have hu : IsEvenVec (permVec σ v) := isEvenVec_permVec σ hv
  have hwu : vecWeight (permVec σ v) = vecWeight v := vecWeight_permVec σ v
  rcases hd.inj (permVec σ v) w hu hw hσw.symm with h | h
  · left; rw [h, hwu]
  · right; rw [h, sec5b_vecWeight_add_one, hwu]

theorem sec5b_conj_of_weight {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : alternatingGroup (Fin 8) ≤ Alt)
    (hd : HeartData φ A M Alt) {v w : Fin 8 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w)
    (h : vecWeight v = vecWeight w) : φ w ∈ conjClassIn M (φ v) := by
  obtain ⟨σ, hσ, hσv⟩ := sec5b_exists_alt h
  exact (sec5b_mem_conj_iff hd hv).mpr ⟨σ, hAlt hσ, by rw [hσv]⟩

theorem sec5b_pair_of_card {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : alternatingGroup (Fin 8) ≤ Alt)
    (hd : HeartData φ A M Alt) {v : Fin 8 → ZMod 2} (hv : IsEvenVec v)
    (hw : vecWeight v = 2 ∨ vecWeight v = 4) (hcard : Set.ncard (conjClassIn M (φ v)) = 28) :
    vecWeight v = 2 := by
  by_contra h2
  have h4 : vecWeight v = 4 := hw.resolve_left h2
  have hset : conjClassIn M (φ v) = φ '' {w | IsEvenVec w ∧ vecWeight w = 4} := by
    ext y
    constructor
    · intro hy
      obtain ⟨σ, _hσ, hy⟩ := (sec5b_mem_conj_iff hd hv).mp hy
      exact ⟨permVec σ v, ⟨isEvenVec_permVec σ hv, by rw [vecWeight_permVec, h4]⟩, hy.symm⟩
    · rintro ⟨w, ⟨hwE, hw4⟩, hwy⟩
      have := sec5b_conj_of_weight hAlt hd hv hwE (by rw [h4, hw4])
      rwa [hwy] at this
  rw [hset, sec5b_ncard_weight_four φ hd.add_one hd.inj] at hcard
  omega

theorem sec5b_exists_h {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : alternatingGroup (Fin 8) ≤ Alt)
    (hd : HeartData φ A M Alt) {t z p : G} (htA : t ∈ A) (hzA : z ∈ A) (hpA : p ∈ A)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (hcard : Set.ncard (conjClassIn M t) = 28)
    (hzt : z ∉ conjClassIn M t) (hp : p ∈ conjClassIn M t) (hpz : p * z ∈ conjClassIn M t)
    (htz : t * z ∈ conjClassIn M t) (hpt : p ≠ t) :
    ∃ h ∈ M, h * z * h⁻¹ = z ∧ h * t * h⁻¹ = p ∧ ∀ a ∈ A, (h * h) * a * (h * h)⁻¹ = a := by
  obtain ⟨a, haE, hat, haw⟩ := sec5b_weight_rep hd htA ht1
  have hcarda : Set.ncard (conjClassIn M (φ a)) = 28 := by rw [hat]; exact hcard
  have ha2 : vecWeight a = 2 := sec5b_pair_of_card hAlt hd haE haw hcarda
  obtain ⟨c, hcE, hcz, hcw⟩ := sec5b_weight_rep hd hzA hz1
  have hc4 : vecWeight c = 4 := by
    rcases hcw with hc2 | hc4
    · exfalso
      have hzcl : z ∈ conjClassIn M t := by
        rw [← hat, ← hcz]
        exact sec5b_conj_of_weight hAlt hd haE hcE (by rw [ha2, hc2])
      exact hzt hzcl
    · exact hc4
  have hp' : p ∈ conjClassIn M (φ a) := by rw [hat]; exact hp
  obtain ⟨τ, _hτ, hpτ⟩ := (sec5b_mem_conj_iff hd haE).mp hp'
  have hbE : IsEvenVec (permVec τ a) := isEvenVec_permVec τ haE
  have hb2 : vecWeight (permVec τ a) = 2 := by rw [vecWeight_permVec, ha2]
  have hpz' : p * z ∈ conjClassIn M (φ a) := by rw [hat]; exact hpz
  have hbc : vecWeight (permVec τ a + c) = 2 ∨ vecWeight (permVec τ a + c) = 6 := by
    have hcl : φ (permVec τ a + c) ∈ conjClassIn M (φ a) := by
      rw [hd.add (permVec τ a) c hbE hcE, ← hpτ, hcz]
      exact hpz'
    have := sec5b_conj_weight hd haE (sec5b_isEvenVec_add hbE hcE) hcl
    rcases this with h | h
    · exact Or.inl (by rw [h, ha2])
    · exact Or.inr (by rw [h, ha2])
  have hac : vecWeight (a + c) = 2 ∨ vecWeight (a + c) = 6 := by
    have hcl : φ (a + c) ∈ conjClassIn M (φ a) := by
      rw [hd.add a c haE hcE, hat, hcz]
      exact htz
    have := sec5b_conj_weight hd haE (sec5b_isEvenVec_add haE hcE) hcl
    rcases this with h | h
    · exact Or.inl (by rw [h, ha2])
    · exact Or.inr (by rw [h, ha2])
  have hab : a ≠ permVec τ a := by
    intro hab
    apply hpt
    rw [← hat, hpτ, ← hab]
  obtain ⟨σ, hσAlt, hσ2, hσc, hσa⟩ :=
    sec5b_heart_move ha2 hb2 hc4 hac hbc hab
  obtain ⟨h, hhM, hlift⟩ := hd.lift σ (hAlt hσAlt)
  refine ⟨h, hhM, ?_, ?_, ?_⟩
  ·
    have h1 : h * z * h⁻¹ = φ (permVec σ c) := by
      rw [← hcz]
      exact hlift c hcE
    rw [h1]
    rcases hσc with hc | hc
    · rw [hc, hcz]
    · rw [hc, hd.add_one c hcE, hcz]
  ·
    have h1 : h * t * h⁻¹ = φ (permVec σ a) := by
      rw [← hat]
      exact hlift a haE
    rw [h1, hσa, hpτ]
  ·
    intro x hxA
    obtain ⟨v, hv, hvx⟩ := hd.surj x hxA
    have hcentral : (h * h) * φ v * (h * h)⁻¹ = φ v := by
      have hassoc : (h * h) * φ v * (h * h)⁻¹ = h * (h * φ v * h⁻¹) * h⁻¹ := by
        rw [mul_inv_rev]; group
      rw [hassoc, hlift v hv, hlift (permVec σ v) (isEvenVec_permVec σ hv),
        ← sec5b_permVec_mul σ σ v, hσ2]
      rfl
    rw [← hvx, hcentral]

end CFSG.OddStandard.SmallF3.Omega
