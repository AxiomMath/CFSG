module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveP

public section

namespace CFSG.ComponentClassification.SolMax.DgF

open CFSG Equiv

noncomputable def embedEquiv {n k : ℕ} {D : Finset (Fin n)} (hD : D.card = k) : ↥D ≃ Fin k :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hD])

noncomputable def embedPerm {n k : ℕ} {D : Finset (Fin n)} (hD : D.card = k) :
    Perm (Fin k) →* Perm (Fin n) :=
  (Perm.ofSubtype : Perm (Subtype (· ∈ D)) →* Perm (Fin n)).comp
    (Equiv.permCongrHom (embedEquiv hD).symm).toMonoidHom

variable {n k : ℕ} {D : Finset (Fin n)} (hD : D.card = k)
include hD

theorem embedPerm_injective : Function.Injective (embedPerm hD) :=
  Perm.ofSubtype_injective.comp (MulEquiv.injective _)

theorem embedPerm_apply_of_notMem (x : Perm (Fin k)) {v : Fin n} (hv : v ∉ D) :
    embedPerm hD x v = v :=
  Perm.ofSubtype_apply_of_not_mem (p := (· ∈ D)) _ hv

theorem sign_embedPerm (x : Perm (Fin k)) : Perm.sign (embedPerm hD x) = Perm.sign x := by
  change Perm.sign (Perm.ofSubtype _) = _
  rw [Perm.sign_ofSubtype]
  exact Perm.sign_permCongr _ _

theorem embedPerm_apply_symm (x : Perm (Fin k)) (i : Fin k) :
    embedPerm hD x ((embedEquiv hD).symm i : Fin n) = ((embedEquiv hD).symm (x i) : Fin n) := by
  change Perm.ofSubtype _ _ = _
  rw [Perm.ofSubtype_apply_of_mem (p := (· ∈ D)) _ ((embedEquiv hD).symm i).2]
  simp [Equiv.permCongrHom, Equiv.permCongr_apply]

theorem exists_embedPerm {σ : Perm (Fin n)} (hσ : ∀ v ∉ D, σ v = v) :
    ∃ x : Perm (Fin k), embedPerm hD x = σ := by
  classical
  have hmem : σ ∈ (Perm.ofSubtype : Perm (Subtype (· ∈ D)) →* Perm (Fin n)).range := by
    rw [Perm.mem_range_ofSubtype_iff]
    intro v hv
    by_contra hvD
    exact (Perm.mem_support.mp hv) (hσ v hvD)
  obtain ⟨s, rfl⟩ := hmem
  obtain ⟨x, hx⟩ := (Equiv.permCongrHom (embedEquiv hD).symm).surjective s
  exact ⟨x, by rw [← hx]; rfl⟩

theorem ne_of_embedPerm {x : Perm (Fin k)} (hx : ∀ v ∈ D, embedPerm hD x v ≠ v) (i : Fin k) :
    x i ≠ i := by
  intro h
  have h1 := embedPerm_apply_symm hD x i
  rw [h] at h1
  exact hx _ ((embedEquiv hD).symm i).2 h1

omit hD

theorem perm4_fix : ∀ s : Perm (Fin 4), s * s = 1 → (∀ i, s i ≠ i) → ∀ x : Perm (Fin 4),
    x * s = s * x → x * x * x = 1 → x = 1 := by decide

theorem perm4_sqrt : ∀ s : Perm (Fin 4), s * s = 1 → (∀ i, s i ≠ i) →
    ∃ w : Perm (Fin 4), w * w = s ∧ Perm.sign w = -1 := by decide

theorem perm3_conj : ∀ p z : Perm (Fin 3), z * z * z = 1 →
    p * z * p⁻¹ = z ∨ p * z * p⁻¹ = z⁻¹ := by decide

theorem perm3_conj_odd : ∀ p z : Perm (Fin 3), z * z * z = 1 → Perm.sign p = -1 →
    p * z * p⁻¹ = z⁻¹ := by decide

theorem pow_card_perm_fin (k : ℕ) (x : Perm (Fin k)) : x ^ k.factorial = 1 := by
  have h1 := pow_card_eq_one' (G := Perm (Fin k)) (x := x)
  rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1

theorem pow_three_of_dvd {G : Type*} [Monoid G] {x : G} {m e : ℕ} (hxm : x ^ m = 1)
    (hxe : x ^ e = 1) (he : Nat.gcd m e ∣ 3) : x ^ 3 = 1 := by
  have h1 : x ^ Nat.gcd m e = 1 := pow_gcd_eq_one.mpr ⟨hxm, hxe⟩
  obtain ⟨d, hd⟩ := he
  rw [hd, pow_mul, h1, one_pow]

theorem gcd_dvd_three {m j : ℕ} (hm : Odd m) : Nat.gcd m (3 * 2 ^ j) ∣ 3 := by
  have h2 : Nat.Coprime (Nat.gcd m (3 * 2 ^ j)) (2 ^ j) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm))
  exact h2.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)

theorem fixes_of_odd_commute {σ ζ : Perm (Fin n)} (hσ2 : σ * σ = 1) (hσ4 : σ.support.card = 4)
    (hζσ : ζ * σ = σ * ζ) (hζ : Odd (orderOf ζ)) : ∀ v ∈ σ.support, ζ v = v := by
  classical
  obtain ⟨ζD, ζF, hsplit, hζD, hζF, -, -⟩ :=
    exists_split σ.support (apply_mem_support_iff_of_commute hζσ)
  have hσD : ∀ v ∉ σ.support, σ v = v := fun v hv => Perm.notMem_support.mp hv
  have hdisj : ∀ {f g : Perm (Fin n)}, (∀ v ∉ σ.support, f v = v) →
      (∀ v ∈ σ.support, g v = v) → f * g = g * f := fun {f g} hf hg =>
    (Perm.Disjoint.commute fun v => by
      by_cases hv : v ∈ σ.support
      · exact Or.inr (hg v hv)
      · exact Or.inl (hf v hv)).eq
  have hFσ : ζF * σ = σ * ζF := (hdisj hσD hζF).symm
  have hDσ : ζD * σ = σ * ζD := by
    have h1 : ζD * ζF * σ = σ * (ζD * ζF) := by rw [← hsplit]; exact hζσ
    have h2 : ζD * σ * ζF = σ * ζD * ζF := by
      calc ζD * σ * ζF = ζD * (σ * ζF) := by group
        _ = ζD * (ζF * σ) := by rw [hFσ]
        _ = σ * (ζD * ζF) := by rw [← mul_assoc, h1]
        _ = σ * ζD * ζF := by group
    exact mul_right_cancel h2
  have hDm : ζD ^ orderOf ζ = 1 := by
    have h1 : (ζD * ζF) ^ orderOf ζ = 1 := by rw [← hsplit]; exact pow_orderOf_eq_one ζ
    rw [(show Commute ζD ζF from hdisj hζD hζF).mul_pow] at h1
    refine Equiv.ext fun v => ?_
    by_cases hv : v ∈ σ.support
    · have h2 := congrArg (fun f : Perm (Fin n) => f v) h1
      simp only [Perm.mul_apply, Perm.one_apply] at h2
      rw [Perm.pow_apply_eq_self_of_apply_eq_self (hζF v hv)] at h2
      rw [Perm.one_apply]
      exact h2
    · rw [Perm.one_apply]
      exact Perm.pow_apply_eq_self_of_apply_eq_self (hζD v hv) _
  obtain ⟨s, hs⟩ := exists_embedPerm hσ4 hσD
  obtain ⟨x, hx⟩ := exists_embedPerm hσ4 hζD
  have hs2 : s * s = 1 := embedPerm_injective hσ4 (by rw [map_mul, hs, hσ2, map_one])
  have hsfix : ∀ i, s i ≠ i := ne_of_embedPerm hσ4 (by
    intro v hv
    rw [hs]
    exact Perm.mem_support.mp hv)
  have hxs : x * s = s * x := embedPerm_injective hσ4 (by rw [map_mul, map_mul, hs, hx, hDσ])
  have hxm : x ^ orderOf ζ = 1 := embedPerm_injective hσ4 (by rw [map_pow, hx, hDm, map_one])
  have hx3 : x ^ 3 = 1 := pow_three_of_dvd hxm (pow_card_perm_fin 4 x)
    (by have := gcd_dvd_three (j := 3) hζ; norm_num at this ⊢; exact this)
  have hx1 : x = 1 := perm4_fix s hs2 hsfix x hxs (by rw [← pow_three']; exact hx3)
  intro v hv
  rw [hsplit, Perm.mul_apply, hζF v hv, ← hx, hx1, map_one, Perm.one_apply]

theorem pow_three_of_odd {F : Finset (Fin n)} (hF : F.card = 3) {ζ : Perm (Fin n)}
    (hζF : ∀ v ∉ F, ζ v = v) (hζ : Odd (orderOf ζ)) : ζ ^ 3 = 1 := by
  obtain ⟨x, hx⟩ := exists_embedPerm hF hζF
  have hxm : x ^ orderOf ζ = 1 := embedPerm_injective hF (by rw [map_pow, hx,
    pow_orderOf_eq_one, map_one])
  have hx3 : x ^ 3 = 1 := pow_three_of_dvd hxm (pow_card_perm_fin 3 x)
    (by have := gcd_dvd_three (j := 1) hζ; norm_num at this ⊢; exact this)
  rw [← hx, ← map_pow, hx3, map_one]

theorem conj_eq_or_eq_inv {F : Finset (Fin n)} (hF : F.card = 3) {π ζ : Perm (Fin n)}
    (hπ : ∀ v, π v ∈ F ↔ v ∈ F) (hζF : ∀ v ∉ F, ζ v = v) (hζ3 : ζ ^ 3 = 1) :
    (π * ζ * π⁻¹ = ζ ∨ π * ζ * π⁻¹ = ζ⁻¹) ∧
      (∀ πF : Perm (Fin n), (∀ v ∉ F, πF v = v) → (∀ v ∈ F, πF v = π v) →
        Perm.sign πF = -1 → π * ζ * π⁻¹ = ζ⁻¹) := by
  classical
  obtain ⟨πF, πO, hsplit, hπF, hπO, hπFeq, -⟩ := exists_split F hπ
  have hdisj : πO * ζ = ζ * πO := (Perm.Disjoint.commute fun v => by
    by_cases hv : v ∈ F
    · exact Or.inl (hπO v hv)
    · exact Or.inr (hζF v hv)).eq
  have hconj : ∀ ρF : Perm (Fin n), (∀ v ∉ F, ρF v = v) → (∀ v ∈ F, ρF v = π v) →
      π * ζ * π⁻¹ = ρF * ζ * ρF⁻¹ := by
    intro ρF hρF hρFeq
    have hρ : ρF = πF := by
      ext v
      by_cases hv : v ∈ F
      · rw [hρFeq v hv, hπFeq v hv]
      · rw [hρF v hv, hπF v hv]
    rw [hρ, hsplit]
    calc πF * πO * ζ * (πF * πO)⁻¹ = πF * (πO * ζ) * πO⁻¹ * πF⁻¹ := by group
      _ = πF * (ζ * πO) * πO⁻¹ * πF⁻¹ := by rw [hdisj]
      _ = πF * ζ * πF⁻¹ := by group
  obtain ⟨p, hp⟩ := exists_embedPerm hF hπF
  obtain ⟨z, hz⟩ := exists_embedPerm hF hζF
  have hz3 : z * z * z = 1 := embedPerm_injective hF (by
    rw [map_mul, map_mul, hz, ← pow_three', hζ3, map_one])
  have hpz : π * ζ * π⁻¹ = embedPerm hF (p * z * p⁻¹) := by
    rw [hconj πF hπF hπFeq, map_mul, map_mul, map_inv, hp, hz]
  refine ⟨?_, fun ρF hρF hρFeq hsign => ?_⟩
  · rcases perm3_conj p z hz3 with h | h
    · left
      rw [hpz, h, hz]
    · right
      rw [hpz, h, map_inv, hz]
  · obtain ⟨q, hq⟩ := exists_embedPerm hF hρF
    have hqs : Perm.sign q = -1 := by rw [← sign_embedPerm hF, hq, hsign]
    have hqz : π * ζ * π⁻¹ = embedPerm hF (q * z * q⁻¹) := by
      rw [hconj ρF hρF hρFeq, map_mul, map_mul, map_inv, hq, hz]
    rw [hqz, perm3_conj_odd q z hz3 hqs, map_inv, hz]

theorem exists_sqrt {σ : Perm (Fin n)} (hσ2 : σ * σ = 1) (hσ4 : σ.support.card = 4)
    (hF : 2 ≤ σ.supportᶜ.card) :
    ∃ w : Perm (Fin n), Perm.sign w = 1 ∧ w * w = σ ∧
      ∃ wF : Perm (Fin n), (∀ v ∉ σ.supportᶜ, wF v = v) ∧ (∀ v ∈ σ.supportᶜ, wF v = w v) ∧
        Perm.sign wF = -1 := by
  classical
  have hσD : ∀ v ∉ σ.support, σ v = v := fun v hv => Perm.notMem_support.mp hv
  obtain ⟨s, hs⟩ := exists_embedPerm hσ4 hσD
  have hs2 : s * s = 1 := embedPerm_injective hσ4 (by rw [map_mul, hs, hσ2, map_one])
  have hsfix : ∀ i, s i ≠ i := ne_of_embedPerm hσ4 (by
    intro v hv
    rw [hs]
    exact Perm.mem_support.mp hv)
  obtain ⟨w₄, hw₄, hw₄s⟩ := perm4_sqrt s hs2 hsfix
  set wD := embedPerm hσ4 w₄ with hwDdef
  have hwD2 : wD * wD = σ := by rw [hwDdef, ← map_mul, hw₄, hs]
  have hwDsupp : ∀ v ∉ σ.support, wD v = v := fun v hv => embedPerm_apply_of_notMem hσ4 w₄ hv
  have hwDsign : Perm.sign wD = -1 := by rw [hwDdef, sign_embedPerm, hw₄s]
  obtain ⟨f₁, hf₁, f₂, hf₂, hf₁₂⟩ : ∃ f₁ ∈ σ.supportᶜ, ∃ f₂ ∈ σ.supportᶜ, f₁ ≠ f₂ :=
    Finset.one_lt_card.mp (by omega)
  set wF := swap f₁ f₂ with hwFdef
  have hwFsupp : ∀ v ∉ σ.supportᶜ, wF v = v := by
    intro v hv
    rw [hwFdef]
    refine swap_apply_of_ne_of_ne ?_ ?_
    · rintro rfl
      exact hv hf₁
    · rintro rfl
      exact hv hf₂
  have hwFsign : Perm.sign wF = -1 := Perm.sign_swap hf₁₂
  have hcomm : wD * wF = wF * wD := (Perm.Disjoint.commute fun v => by
    by_cases hv : v ∈ σ.support
    · right
      exact hwFsupp v (by rw [Finset.mem_compl]; exact not_not.mpr hv)
    · left
      exact hwDsupp v hv).eq
  refine ⟨wD * wF, by rw [Perm.sign_mul, hwDsign, hwFsign, Int.units_mul_self], ?_, wF, hwFsupp,
    ?_, hwFsign⟩
  · calc wD * wF * (wD * wF) = wD * (wF * wD) * wF := by group
      _ = wD * (wD * wF) * wF := by rw [hcomm]
      _ = wD * wD * (wF * wF) := by group
      _ = σ := by rw [hwD2, hwFdef, swap_mul_self, mul_one]
  · intro v hv
    rw [Perm.mul_apply, hwDsupp _ ?_]
    rw [Finset.mem_compl] at hv
    by_cases h : v = f₁
    · rw [h, hwFdef, swap_apply_left]
      exact fun h' => (Finset.mem_compl.mp hf₂) h'
    · by_cases h' : v = f₂
      · rw [h', hwFdef, swap_apply_right]
        exact fun h'' => (Finset.mem_compl.mp hf₁) h''
      · rw [hwFdef, swap_apply_of_ne_of_ne h h']
        exact hv

end CFSG.ComponentClassification.SolMax.DgF
