module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Cent

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

theorem eq_one_or_eq_of_card_two {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (hH : Nat.card H = 2) {z c : G} (hz : z ∈ H) (hz1 : z ≠ 1) (hc : c ∈ H) :
    c = 1 ∨ c = z := by
  by_contra h
  push Not at h
  obtain ⟨hc1, hcz⟩ := h
  let f : Fin 3 → H := ![⟨1, one_mem _⟩, ⟨z, hz⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hv : ((f i : H) : G) = f j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hv ⊢
    all_goals
      first
        | exact absurd hv.symm hz1
        | exact absurd hv hz1
        | exact absurd hv.symm hc1
        | exact absurd hv hc1
        | exact absurd hv.symm hcz
        | exact absurd hv hcz
  have h3 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hH] at h3
  omega

theorem exists_mul_self_of_mem_center {m : ℕ} (hm : 2 ≤ m) {c : DihedralGroup (2 ^ m)}
    (hc : c ∈ center (DihedralGroup (2 ^ m))) : ∃ w, w * w = c := by
  obtain ⟨t, ht1, htZ⟩ := dihedral_exists_sq_central hm
  have h2 : Nat.card (center (DihedralGroup (2 ^ m))) = 2 := by
    apply card_center_dihedral
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    · exact (Nat.even_pow' (by omega)).mpr even_two
  rcases eq_one_or_eq_of_card_two h2 htZ ht1 hc with h | h
  · exact ⟨1, by rw [h, mul_one]⟩
  · exact ⟨t, h.symm⟩

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

omit [Finite Y] in
include e in
theorem conj_injective_l2 : Function.Injective (MulAut.conj : Y →* MulAut Y) := fun y y' h => by
  have h1 := congrArg (autEquiv e) h
  rw [autEquiv_conj, autEquiv_conj] at h1
  exact e.injective (incl_injective F h1)

omit [Finite Y] in
include e in
theorem comap_conj_eq (R : Sylow 2 Y) (X : Subgroup (MulAut Y)) (hX : IsPGroup 2 X)
    (hRX : (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ X) :
    X.comap (MulAut.conj : Y →* MulAut Y) = R :=
  R.3 (hX.comap_of_injective _ (conj_injective_l2 e)) fun r hr => hRX ⟨r, hr, rfl⟩

theorem normalizes_of_mem (R : Sylow 2 Y) (X : Subgroup (MulAut Y)) (hX : IsPGroup 2 X)
    (hRX : (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ X) {w : MulAut Y}
    (hw : w ∈ X) : ∀ d ∈ (sylowMap e R : Subgroup (PSL2 F)), ∃ d' ∈ (sylowMap e R : Subgroup
      (PSL2 F)), autEquiv e w * incl F d * (autEquiv e w)⁻¹ = incl F d' := by
  intro d hd
  have h1 : e.symm d ∈ (R : Subgroup Y) := by
    rw [← mem_sylowMap_iff e R, MulEquiv.apply_symm_apply]
    exact hd
  have h2 : w (e.symm d) ∈ (R : Subgroup Y) := by
    rw [← comap_conj_eq e R X hX hRX]
    show MulAut.conj (w (e.symm d)) ∈ X
    rw [← mulAut_conj_conj]
    exact mul_mem (mul_mem hw (hRX ⟨_, h1, rfl⟩)) (inv_mem hw)
  refine ⟨e (w (e.symm d)), (mem_sylowMap_iff e R _).mpr h2, ?_⟩
  rw [conj_incl, ← semilinearAction_autEquiv_apply, MulEquiv.apply_symm_apply]

include e in
theorem center_le_l2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hL : Blueprint.LieModel Y .PSL 2 p f) (R : Sylow 2 Y)
    (hna : ∃ a ∈ (R : Subgroup Y), ∃ b ∈ (R : Subgroup Y), a * b ≠ b * a)
    (X : Subgroup (MulAut Y)) (hX : IsPGroup 2 X)
    (hRX : (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ X)
    (R₁ : Subgroup (MulAut Y)) (hR₁X : R₁ ≤ X) (hR₁ : Nonempty (R₁ ≃* (R : Subgroup Y)))
    (c : MulAut Y) (hc : c ∈ R₁) (hcZ : ∀ d ∈ R₁, c * d = d * c) :
    ∃ r ∈ (R : Subgroup Y), (∀ s ∈ (R : Subgroup Y), r * s = s * r) ∧ c = MulAut.conj r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hD8 := eight_le_of_noncomm e hodd R hna
  obtain ⟨m, -, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd R
  have hm2 : 2 ≤ m := by
    have hcard : Nat.card (sylowMap e R) = 2 ^ (m + 1) := by
      rw [card_sylowMap e R, Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card, pow_succ,
        mul_comm]
    by_contra h
    have : 2 ^ (m + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e₁⟩ := hR₁
  set ρ₁ := e₁.trans ρ with hρ₁
  have hc' : c ∈ ⁅R₁, R₁⁆ :=
    mem_commutator_of_dihedral ((by norm_num : (4 : ℕ) ∣ 2 ^ 2).trans (Nat.pow_dvd_pow 2 hm2))
      ρ₁ hc hcZ
  have hcInn : c ∈ innAut5 Y := by
    have hle : ⁅R₁, R₁⁆ ≤ innAut5 Y := by
      rw [commutator_le]
      intro x _ y _
      rw [commutatorElement_def]
      exact commutator_mem_l2 hp hp2 hf hL x y
    exact hle hc'
  obtain ⟨z, rfl⟩ := hcInn
  have hzR : z ∈ (R : Subgroup Y) := by
    rw [← comap_conj_eq e R X hX hRX]
    exact hR₁X hc
  by_cases hz1 : z = 1
  · exact ⟨z, hzR, fun s _ => by rw [hz1, one_mul, mul_one], rfl⟩
  have hcZ' : ρ₁ ⟨MulAut.conj z, hc⟩ ∈ center (DihedralGroup (2 ^ m)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := ρ₁.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcZ g' g'.2).symm
  have hcc : MulAut.conj z * MulAut.conj z = 1 := by
    have h2 : Nat.card (center (DihedralGroup (2 ^ m))) = 2 := by
      apply card_center_dihedral
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      · exact (Nat.even_pow' (by omega)).mpr even_two
    have h3 : (⟨_, hcZ'⟩ : center (DihedralGroup (2 ^ m))) ^ 2 = 1 := by
      have := orderOf_dvd_natCard (⟨_, hcZ'⟩ : center (DihedralGroup (2 ^ m)))
      rw [h2] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h4 : (ρ₁ ⟨MulAut.conj z, hc⟩) * ρ₁ ⟨MulAut.conj z, hc⟩ = 1 := by
      rw [← sq]
      exact congrArg Subtype.val h3
    rw [← map_mul, ← map_one ρ₁] at h4
    exact congrArg Subtype.val (ρ₁.injective h4)
  have hzz : z * z = 1 := conj_injective_l2 e (by rw [map_mul, hcc, map_one])
  have hezz : e z * e z = 1 := by rw [← map_mul, hzz, map_one]
  obtain ⟨t, ht⟩ := exists_mul_self_of_mem_center hm2 hcZ'
  obtain ⟨w, hwR₁, hww⟩ : ∃ w ∈ R₁, w * w = MulAut.conj z := by
    refine ⟨_, (ρ₁.symm t).2, ?_⟩
    have h1 : ρ₁.symm (t * t) = ⟨MulAut.conj z, hc⟩ := by rw [ht, MulEquiv.symm_apply_apply]
    rw [map_mul] at h1
    exact congrArg Subtype.val h1
  have hWnorm := normalizes_of_mem e R X hX hRX (hR₁X hwR₁)
  have hWnorm' := normalizes_of_mem e R X hX hRX (inv_mem (hR₁X hwR₁))
  simp only [map_inv, inv_inv] at hWnorm'
  have hWW : autEquiv e w * autEquiv e w = incl F (e z) := by
    rw [← map_mul, hww, autEquiv_conj]
  set W := autEquiv e w with hW
  have hW4 : W ^ 4 = 1 := by
    rw [show W ^ 4 = W * W * (W * W) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      hWW, ← map_mul, hezz, map_one]
  have hezD : e z ∈ (sylowMap e R : Subgroup (PSL2 F)) := (mem_sylowMap_iff e R z).mpr hzR
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  have hezZ : ∀ d ∈ (sylowMap e R : Subgroup (PSL2 F)), e z * d = d * e z := by
    by_cases hWr : W.right = 1
    ·
      obtain ⟨-, hZ⟩ := sylow_noncomm_center hodd (sylowMap e R) hD8
      have hZnt : Nontrivial ↥((sylowMap e R : Subgroup (PSL2 F)) ⊓
          centralizer ((sylowMap e R : Subgroup (PSL2 F)) : Set (PSL2 F))) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ]; norm_num)
      obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := exists_ne (1 : ↥((sylowMap e R : Subgroup (PSL2 F)) ⊓
          centralizer ((sylowMap e R : Subgroup (PSL2 F)) : Set (PSL2 F))))
      have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
      have hz₀C := mem_centralizer_iff.mp hz₀.2
      have hz₀2 : z₀ ^ 2 = 1 := by
        have h1 := orderOf_dvd_natCard (⟨z₀, hz₀⟩ : ↥((sylowMap e R : Subgroup (PSL2 F)) ⊓
          centralizer ((sylowMap e R : Subgroup (PSL2 F)) : Set (PSL2 F))))
        rw [hZ] at h1
        exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h1)
      obtain ⟨d', hd'D, hd'⟩ := hWnorm z₀ hz₀.1
      have hd'C : d' ∈ centralizer ((sylowMap e R : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
        rw [mem_centralizer_iff]
        intro d hd
        obtain ⟨d₁, hd₁D, hd₁⟩ := hWnorm' d hd
        have hd2 : incl F d = W * incl F d₁ * W⁻¹ := by
          rw [← hd₁]
          group
        apply incl_injective F
        rw [map_mul, map_mul, ← hd', hd2]
        have h1 := hz₀C d₁ hd₁D
        calc W * incl F d₁ * W⁻¹ * (W * incl F z₀ * W⁻¹) = W * incl F (d₁ * z₀) * W⁻¹ := by
              rw [map_mul]
              group
          _ = W * incl F (z₀ * d₁) * W⁻¹ := by rw [h1]
          _ = W * incl F z₀ * W⁻¹ * (W * incl F d₁ * W⁻¹) := by
              rw [map_mul]
              group
      have hd'1 : d' ≠ 1 := by
        rintro rfl
        apply hz₀1'
        apply incl_injective F
        rw [map_one] at hd' ⊢
        calc incl F z₀ = W⁻¹ * (W * incl F z₀ * W⁻¹) * W := by group
          _ = 1 := by rw [hd', mul_one, inv_mul_cancel]
      have hd'z₀ : d' = z₀ := by
        rcases eq_one_or_eq_of_card_two hZ hz₀ hz₀1' ⟨hd'D, hd'C⟩ with h | h
        · exact absurd h hd'1
        · exact h
      rw [hd'z₀] at hd'
      have hWz : W * incl F z₀ = incl F z₀ * W := by
        calc W * incl F z₀ = W * incl F z₀ * W⁻¹ * W := by group
          _ = incl F z₀ * W := by rw [hd']
      have hWg := eq_inl_of_right_eq_one hWr
      have hgg : W.left * W.left = Matrix.ProjectiveSpecialLinearGroup.toPGL (e z) := by
        have h1 : (SemidirectProduct.inl (W.left * W.left) : PGammaL2 F) =
            SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (e z)) := by
          rw [map_mul, ← hWg, hWW, incl_apply]
        exact SemidirectProduct.inl_injective h1
      have hg4 : orderOf W.left = 4 := by
        have h1 : ¬ W.left ^ 2 ^ 1 = 1 := by
          rw [pow_one, sq, hgg]
          intro h1
          exact hez1 (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by rw [h1, map_one]))
        have h2 : W.left ^ 2 ^ (1 + 1) = 1 := by
          rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq, sq, hgg, ← map_mul, hezz,
            map_one]
        exact (orderOf_eq_prime_pow h1 h2).trans (by norm_num)
      have hgv : W.left * Matrix.ProjectiveSpecialLinearGroup.toPGL z₀ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL z₀ * W.left := by
        have h1 : (SemidirectProduct.inl (W.left * Matrix.ProjectiveSpecialLinearGroup.toPGL z₀) :
            PGammaL2 F) = SemidirectProduct.inl
              (Matrix.ProjectiveSpecialLinearGroup.toPGL z₀ * W.left) := by
          rw [map_mul, map_mul, ← hWg, ← incl_apply, hWz]
        exact SemidirectProduct.inl_injective h1
      have hv2 : Matrix.ProjectiveSpecialLinearGroup.toPGL z₀ ^ 2 = 1 := by
        rw [← map_pow, hz₀2, map_one]
      rcases AschbacherKnownGroup.FactsL2.pgl2_eq_of_commute_orderOf_four hodd hg4 hv2 hgv with
        h | h
      · exact absurd (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (by rw [h, map_one])) hz₀1'
      · have hz : z₀ = e z :=
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by rw [h, sq, hgg])
        intro d hd
        rw [← hz]
        exact (hz₀C d hd).symm
    ·
      have hW4' : W ^ 2 ^ 2 = 1 := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hW4
      have hfe := even_of_right_ne_one hp hF W hW4' hWr
      obtain ⟨hsq, hq4, hn⟩ := model_hyps_of_even hp hp2 hf hF hfe
      obtain ⟨h, hh⟩ := exists_conj_stdT hodd hsq hq4 (sylowMap e R)
      have hW'n : ∀ g ∈ (stdT F).map (incl F), (incl F h)⁻¹ * W * incl F h * g *
          ((incl F h)⁻¹ * W * incl F h)⁻¹ ∈ (stdT F).map (incl F) := by
        rintro _ ⟨t, ht, rfl⟩
        have hd : h * t * h⁻¹ ∈ (sylowMap e R : Subgroup (PSL2 F)) := by
          rw [hh, show h⁻¹ * (h * t * h⁻¹) * h = t by group]
          exact ht
        obtain ⟨d', hd'D, hd'⟩ := hWnorm _ hd
        refine ⟨h⁻¹ * d' * h, (hh d').mp hd'D, ?_⟩
        rw [map_mul, map_mul, map_inv, ← hd', map_mul, map_mul, map_inv]
        group
      have hW'2 : (incl F h)⁻¹ * W * incl F h * ((incl F h)⁻¹ * W * incl F h) =
          incl F (h⁻¹ * e z * h) := by
        rw [map_mul, map_mul, map_inv, ← hWW]
        group
      have hW'4 : (incl F h)⁻¹ * W * incl F h * ((incl F h)⁻¹ * W * incl F h) *
          ((incl F h)⁻¹ * W * incl F h * ((incl F h)⁻¹ * W * incl F h)) = 1 := by
        rw [hW'2, ← map_mul, show h⁻¹ * e z * h * (h⁻¹ * e z * h) = h⁻¹ * (e z * e z) * h by
          group, hezz, mul_one, inv_mul_cancel, map_one]
      have hcomm := commute_of_sq_mem_stdT hodd hsq hn _ hW'n
        (by rw [hW'2]; exact ⟨_, (hh _).mp hezD, rfl⟩) hW'4
      intro d hd
      have h1 := hcomm _ ⟨_, (hh d).mp hd, rfl⟩
      rw [hW'2, ← map_mul, ← map_mul] at h1
      have h3 := incl_injective F h1
      calc e z * d = h * (h⁻¹ * e z * h * (h⁻¹ * d * h)) * h⁻¹ := by group
        _ = h * (h⁻¹ * d * h * (h⁻¹ * e z * h)) * h⁻¹ := by rw [h3]
        _ = d * e z := by group
  refine ⟨z, hzR, fun s hs => e.injective ?_, rfl⟩
  rw [map_mul, map_mul]
  exact hezZ (e s) ((mem_sylowMap_iff e R s).mpr hs)

end CFSG.ComponentClassification.FooteLit.Aut5L2
