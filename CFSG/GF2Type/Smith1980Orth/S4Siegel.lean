module

public import CFSG.LargeExtraspecial.Types
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LargeExtraspecial.OrthoF2PairsCases
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_conj eichler_mul)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

private theorem eichler_comm_of_singular {a u : V} (ha : Q a = 0) (hu : Q u = 0)
    (hau : polar Q a u = 0) : eichler Q a u = eichler Q u a := by
  have hua : polar Q u a = 0 := by rw [polar_comm, hau]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply_zmod2 ha hau, eichler_apply_zmod2 hu hua, ha, hu]
  simp only [zero_mul, add_zero]
  abel

section Finite

variable [FiniteDimensional (ZMod 2) V]

private theorem apply_eq_of_pow_two_pow {P : Submodule (ZMod 2) V}
    (hP2 : finrank (ZMod 2) P = 2) {θ c : V ≃ₗ[ZMod 2] V} (hθP : ∀ v ∈ P, θ v ∈ P)
    (hcP : ∀ v ∈ P, c v ∈ P) (hθ3 : θ ^ 3 = 1) (hfpf : ∀ v ∈ P, θ v = v → v = 0)
    (hcθ : c * θ = θ * c) {n : ℕ} (hc2 : c ^ (2 ^ n) = 1) : ∀ v ∈ P, c v = v := by
  have hθ3' : ∀ v, θ (θ (θ v)) = v := fun v => by
    have h := LinearEquiv.congr_fun hθ3 v
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    exact h
  have hθθ : ∀ p ∈ P, θ (θ p) = θ p + p := by
    intro p hp
    have hr : θ (θ p) + θ p + p ∈ P :=
      P.add_mem (P.add_mem (hθP _ (hθP p hp)) (hθP p hp)) hp
    have hθr : θ (θ (θ p) + θ p + p) = θ (θ p) + θ p + p := by
      rw [map_add, map_add, hθ3']
      abel
    have h0 := hfpf _ hr hθr
    rw [add_assoc] at h0
    rw [eq_neg_of_add_eq_zero_left h0, vec_neg]
  have hspan : ∀ p ∈ P, p ≠ 0 → Submodule.span (ZMod 2) {p, θ p} = P := by
    intro p hp hp0
    have hθp0 : θ p ≠ 0 := fun h => hp0 (θ.injective (by rw [h, map_zero]))
    have hli : LinearIndependent (ZMod 2) ![p, θ p] :=
      linearIndependent_pair_iff.mpr ⟨hp0, hθp0, fun h => hp0 (hfpf p hp h.symm)⟩
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, hP2])
    rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact hp
    · exact hθP p hp
  have hexh : ∀ p ∈ P, p ≠ 0 → ∀ x ∈ P, x = 0 ∨ x = p ∨ x = θ p ∨ x = θ (θ p) := by
    intro p hp hp0 x hx
    rw [← hspan p hp hp0] at hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inr (Or.inl (by simp)))
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (Or.inr (by rw [hθθ p hp, one_smul, one_smul, add_comm])))
  have hcomm : ∀ (j : ℕ) (x : V), c ((θ ^ j) x) = (θ ^ j) (c x) := fun j x =>
    LinearEquiv.congr_fun (Commute.pow_right hcθ j).eq x
  intro p hp
  by_cases hp0 : p = 0
  · rw [hp0, map_zero]
  have hcm : (c ^ (2 ^ n)) p = p := by
    have h := LinearEquiv.congr_fun hc2 p
    exact h
  have hpow : ∀ k : ℕ, c p = (θ ^ k) p → ∀ m : ℕ, (c ^ m) p = (θ ^ (k * m)) p := by
    intro k hk m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show k * (m + 1) = k * m + k by ring, pow_succ', LinearEquiv.mul_apply, ih, hcomm, hk,
        ← LinearEquiv.mul_apply, ← pow_add]
  have hperiod : ∀ j : ℕ, (θ ^ j) p = p → 3 ∣ j := by
    intro j hj
    have hθj : θ ^ j = θ ^ (j % 3) := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hθ3, one_pow, one_mul]
    rw [hθj] at hj
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
    · exact Nat.dvd_of_mod_eq_zero h
    · rw [h, pow_one] at hj
      exact absurd (hfpf p hp hj) hp0
    · rw [h, pow_two, LinearEquiv.mul_apply] at hj
      have h2 := hθ3' p
      rw [hj] at h2
      exact absurd (hfpf p hp h2) hp0
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hnot : ∀ k : ℕ, c p = (θ ^ k) p → 3 ∣ k := by
    intro k hk
    have h := hpow k hk (2 ^ n)
    rw [hcm] at h
    exact hcop.dvd_of_dvd_mul_right (hperiod _ h.symm)
  rcases hexh p hp hp0 (c p) (hcP p hp) with h0 | h1 | h2 | h3
  · exact absurd (c.injective (by rw [h0, map_zero])) hp0
  · exact h1
  · exfalso
    have := hnot 1 (by rw [pow_one]; exact h2)
    omega
  · exfalso
    have := hnot 2 (by rw [pow_two, LinearEquiv.mul_apply]; exact h3)
    omega

theorem exists_siegel_of_pow_three (hQ : Q.polarBilin.Nondegenerate) {ρ ρ' : V ≃ₗ[ZMod 2] V}
    (hρ : IsTypeA Q ρ 2) (hρ' : IsTypeA Q ρ' 2) (h3 : (ρ * ρ') ^ 3 = 1) (h1 : ρ * ρ' ≠ 1) :
    finrank (ZMod 2) (fixSpace (ρ * ρ')) + 4 = finrank (ZMod 2) V ∧
    ∃ e f : V, Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 0 ∧ LinearIndependent (ZMod 2) ![e, f] ∧
      eichler Q e f * ρ = ρ * eichler Q e f ∧ eichler Q e f * ρ' = ρ' * eichler Q e f ∧
      (∀ v, (ρ * ρ') v = v → polar Q v e = 0 ∧ polar Q v f = 0) ∧
      (∀ v ∈ Submodule.span (ZMod 2) {e, f}, (ρ * ρ') v = v → v = 0) ∧
      (ρ * ρ') e ∈ Submodule.span (ZMod 2) {e, f} ∧
        (ρ * ρ') f ∈ Submodule.span (ZMod 2) {e, f} := by
  have hρO : ρ ∈ orthogonalGroup Q := mem_orthogonalGroup_of_isTypeA hρ
  have hρ'O : ρ' ∈ orthogonalGroup Q := mem_orthogonalGroup_of_isTypeA hρ'
  have hord : orderOf (ρ * ρ') = 3 := orderOf_eq_prime h3 h1
  obtain ⟨hbot, hcomm, hdim4, -, hfix⟩ := commSpace_mul_of_orderOf_eq_three hQ hρ hρ' hord
  have hperp := (orderOf_mul_eq_three_iff_of_isTypeA hQ hρ hρ').mp hord
  refine ⟨?_, ?_⟩
  · have h := finrank_commSpace_add_finrank_fixSpace (ρ * ρ')
    omega
  obtain ⟨d, hd1, hd2⟩ := exists_pair_scalar hQ hρ hρ'
  have hd : d = 1 := by
    rcases zmod2_eq_zero_or_eq_one d with rfl | rfl
    · rw [zero_smul] at hd2
      exact absurd hperp (inf_orthogonal_ne_bot_of_scalar_zero hQ hρ hρ'O hd2)
    · rfl
  rw [hd, one_smul] at hd1
  have hkey : ∀ e ∈ commSpace ρ, ρ (ρ' e - e) - (ρ' e - e) = e := by
    intro e he
    obtain ⟨v, rfl⟩ := mem_commSpace.mp he
    have h := LinearMap.congr_fun hd1 v
    simpa only [Module.End.mul_apply, sub_one_apply] using h
  obtain ⟨e, heP, he0⟩ : ∃ e ∈ commSpace ρ, e ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
    have h2 := hρ.2.2.2.1
    rw [h, finrank_bot] at h2
    omega
  obtain ⟨f, hf⟩ : ∃ f, f = ρ' e - e := ⟨_, rfl⟩
  have hfP' : f ∈ commSpace ρ' := by
    rw [hf]
    exact sub_mem_commSpace ρ' e
  have hQe : Q e = 0 := hρ.2.2.2.2 e heP
  have hQf : Q f = 0 := hρ'.2.2.2.2 f hfP'
  have hef : polar Q e f = 0 := by
    have h0 : polar Q (ρ' e) e = 0 := by
      rw [← map_sub_eq_polar hρ'O e, ← hf]
      exact hQf
    rw [hf, QuadraticMap.polar_sub_right, polar_comm, h0, polar_self_eq_zero, sub_zero]
  have hfe : polar Q f e = 0 := by rw [polar_comm, hef]
  have hf0 : f ≠ 0 := by
    intro h0
    have hfix' : ρ' e = e := sub_eq_zero.mp (hf.symm.trans h0)
    have hmem : e ∈ commSpace ρ ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace ρ') :=
      Submodule.mem_inf.mpr ⟨heP, by
        rw [← fixSpace_eq_orthogonal_commSpace_of_mem hQ hρ'O]
        exact mem_fixSpace.mpr hfix'⟩
    rw [hperp, Submodule.mem_bot] at hmem
    exact he0 hmem
  have hne : e ≠ f := by
    intro h
    have hmem : e ∈ commSpace ρ ⊓ commSpace ρ' :=
      Submodule.mem_inf.mpr ⟨heP, by rw [h]; exact hfP'⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact he0 hmem
  have hli : LinearIndependent (ZMod 2) ![e, f] := linearIndependent_pair_iff.mpr ⟨he0, hf0, hne⟩
  have hρe : ρ e = e := mem_fixSpace.mp (commSpace_le_fixSpace hρ.2.2.1 heP)
  have hρ'f : ρ' f = f := mem_fixSpace.mp (commSpace_le_fixSpace hρ'.2.2.1 hfP')
  have hρ'e : ρ' e = e + f := eq_add_of_sub_eq' hf.symm
  have hρf : ρ f = f + e := by
    have h := hkey e heP
    rw [← hf] at h
    exact eq_add_of_sub_eq' h
  have hθe : (ρ * ρ') e = f := by
    rw [LinearEquiv.mul_apply, hρ'e, map_add, hρe, hρf, add_comm f e, ← add_assoc, vec_add_self,
      zero_add]
  have hθf : (ρ * ρ') f = f + e := by
    rw [LinearEquiv.mul_apply, hρ'f, hρf]
  obtain ⟨x, hli_x, hspan_x⟩ := exists_pair_of_mem_of_finrank_eq_two hρ.2.2.2.1 heP he0
  obtain ⟨-, -, hex, hρE⟩ := eq_eichler_of_isTypeA hQ hρ hli_x hspan_x.symm
  obtain ⟨y, hli_y, hspan_y⟩ := exists_pair_of_mem_of_finrank_eq_two hρ'.2.2.2.1 hfP' hf0
  obtain ⟨-, -, hfy, hρ'E⟩ := eq_eichler_of_isTypeA hQ hρ' hli_y hspan_y.symm
  refine ⟨e, f, hQe, hQf, hef, hli, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρE, eichler_mul hef hex, eichler_mul hex hef, add_comm]
  · rw [hρ'E, eichler_comm_of_singular hQe hQf hef, eichler_mul hfe hfy, eichler_mul hfy hfe,
      add_comm]
  · intro v hv
    have hvmem : v ∈ fixSpace ρ ⊓ fixSpace ρ' := by
      rw [← hfix]
      exact mem_fixSpace.mpr hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hvmem
    have hv1' := (fixSpace_eq_orthogonal_commSpace_of_mem hQ hρO).le hv1
    have hv2' := (fixSpace_eq_orthogonal_commSpace_of_mem hQ hρ'O).le hv2
    exact ⟨(mem_orthogonal_iff_polar.mp hv1') e heP, (mem_orthogonal_iff_polar.mp hv2') f hfP'⟩
  · intro v hv hθv
    have hle : Submodule.span (ZMod 2) {e, f} ≤ commSpace (ρ * ρ') := by
      rw [hcomm, Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.mem_sup_left heP
      · exact Submodule.mem_sup_right hfP'
    have hmem : v ∈ commSpace (ρ * ρ') ⊓ fixSpace (ρ * ρ') :=
      Submodule.mem_inf.mpr ⟨hle hv, mem_fixSpace.mpr hθv⟩
    rw [commSpace_inf_fixSpace_eq_bot_of_pow_three h3, Submodule.mem_bot] at hmem
    exact hmem
  · rw [hθe]
    exact Submodule.subset_span (by simp)
  · rw [hθf]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

theorem eq_one_or_eq_of_commute (hQ : Q.polarBilin.Nondegenerate) {σ θ c : V ≃ₗ[ZMod 2] V}
    (hσ : IsTypeA Q σ 2) (_hθ : ∀ v, Q (θ v) = Q v) (hθ3 : θ ^ 3 = 1) (hθσ : θ * σ = σ * θ)
    (hfpf : ∀ v ∈ commSpace σ, θ v = v → v = 0) (hfix : fixSpace θ ≤ fixSpace σ)
    (hdim : finrank (ZMod 2) (fixSpace θ) + 4 = finrank (ZMod 2) V)
    (hc : ∀ v, Q (c v) = Q v) (hcσ : c * σ = σ * c) (hcθ : c * θ = θ * c) {n : ℕ}
    (hc2 : c ^ (2 ^ n) = 1) (hcP : ∀ v ∈ fixSpace σ, c v - v ∈ commSpace σ) :
    c = 1 ∨ c = σ := by
  have hσO : σ ∈ orthogonalGroup Q := mem_orthogonalGroup_of_isTypeA hσ
  have hcO : c ∈ orthogonalGroup Q := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hc
  have hperp : LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace σ) = fixSpace σ :=
    (fixSpace_eq_orthogonal_commSpace_of_mem hQ hσO).symm
  have hθP : ∀ v ∈ commSpace σ, θ v ∈ commSpace σ := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have h : θ (σ w) = σ (θ w) := LinearEquiv.congr_fun hθσ w
    rw [map_sub, h]
    exact sub_mem_commSpace σ (θ w)
  have hcPP : ∀ v ∈ commSpace σ, c v ∈ commSpace σ := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have h : c (σ w) = σ (c w) := LinearEquiv.congr_fun hcσ w
    rw [map_sub, h]
    exact sub_mem_commSpace σ (c w)
  have hc1 : ∀ v ∈ commSpace σ, c v = v :=
    apply_eq_of_pow_two_pow hσ.2.2.2.1 hθP hcPP hθ3 hfpf hcθ hc2
  have hbot : commSpace σ ⊓ fixSpace θ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_bot]
    exact hfpf v hv1 (mem_fixSpace.mp hv2)
  have hsup : commSpace σ ⊔ fixSpace θ = fixSpace σ := by
    have h1 := finrank_commSpace_add_finrank_fixSpace σ
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace σ) (fixSpace θ)
    rw [hbot, finrank_bot, hσ.2.2.2.1] at h2
    rw [hσ.2.2.2.1] at h1
    exact Submodule.eq_of_le_of_finrank_eq (sup_le (commSpace_le_fixSpace hσ.2.2.1) hfix)
      (by omega)
  have hcfix : ∀ v ∈ fixSpace σ, c v = v := by
    intro v hv
    rw [← hsup] at hv
    obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hcy : c y = y := by
      have h1 : c y - y ∈ commSpace σ := hcP y (hfix hy)
      have h2 : θ (c y - y) = c y - y := by
        have h3 : c (θ y) = θ (c y) := LinearEquiv.congr_fun hcθ y
        rw [map_sub, ← h3, mem_fixSpace.mp hy]
      exact sub_eq_zero.mp (hfpf _ h1 h2)
    rw [map_add, hc1 p hp, hcy]
  have hcomm : commSpace c ≤ commSpace σ := by
    intro z hz
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hz
    have hmem : c x - x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin
        (LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace σ)) := by
      rw [mem_orthogonal_iff_polar]
      intro y hy
      have hy' : c y = y := hcfix y (hperp.le hy)
      rw [QuadraticMap.polar_sub_left,
        ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hcO x y, hy', sub_self]
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q)] at hmem
  obtain ⟨t, -, huniq⟩ := existsUnique_of_totallySingular_finrank_two hQ hσ.2.2.2.2 hσ.2.2.2.1
  by_cases hc1' : c = 1
  · exact Or.inl hc1'
  · exact Or.inr ((huniq c ⟨hcO, hc1', hcomm, fun x hx => hcfix x (hperp.le hx)⟩).trans
      (huniq σ ⟨hσO, hσ.2.1, le_rfl, fun x hx => mem_fixSpace.mp (hperp.le hx)⟩).symm)

theorem exists_omega_conj_eichler (hQ : Q.polarBilin.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V)
    {e f e' f' : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 0)
    (hi : LinearIndependent (ZMod 2) ![e, f]) (he' : Q e' = 0) (hf' : Q f' = 0)
    (hef' : polar Q e' f' = 0) (hi' : LinearIndependent (ZMod 2) ![e', f']) :
    ∃ g ∈ omegaGroup Q hQ, g * eichler Q e f * g⁻¹ = eichler Q e' f' := by
  have hfe : polar Q f e = 0 := by rw [polar_comm, hef]
  have hfe' : polar Q f' e' = 0 := by rw [polar_comm, hef']
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_apply_eq hQ ![e, f] ![e', f'] hi hi'
    (fun i => by fin_cases i <;> simp [he, hf, he', hf'])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [polar_self_eq_zero, hef, hef', hfe, hfe', he, he', hf, hf'])
  have hge : g e = e' := hg 0
  have hgf : g f = f' := hg 1
  by_cases hΩ : g ∈ omegaGroup Q hQ
  · exact ⟨g, hΩ, by rw [eichler_conj hgO, hge, hgf]⟩
  obtain ⟨r, hre, hrf, hQr⟩ : ∃ r, polar Q e r = 0 ∧ polar Q f r = 0 ∧ Q r ≠ 0 := by
    by_contra! h
    have hsing : ∀ x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin
        (Submodule.span (ZMod 2) {e, f}), Q x = 0 := fun x hx => by
      obtain ⟨h1, h2⟩ := mem_orthogonal_span_pair_iff.mp hx
      exact h x h1 h2
    have h1 := CFSG.LieType.BorelTits.QuadForm.IsTotallySingular.two_mul_finrank_le
      (Φ := toQuadForm Q hQ) hsing
    have h2 := LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod 2) {e, f})
    rw [finrank_span_pair hi] at h2
    omega
  letI : Invertible (Q r) := invertibleOfNonzero hQr
  have htO : TauCeti.QuadraticMap.reflection Q r ∈ orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q r
  have hte : TauCeti.QuadraticMap.reflection Q r e = e :=
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q r (by rw [polar_comm]; exact hre)
  have htf : TauCeti.QuadraticMap.reflection Q r f = f :=
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q r (by rw [polar_comm]; exact hrf)
  have hgtO : g * TauCeti.QuadraticMap.reflection Q r ∈ orthogonalGroup Q := mul_mem hgO htO
  refine ⟨g * TauCeti.QuadraticMap.reflection Q r, mem_omegaGroup.mpr ⟨hgtO, ?_⟩, ?_⟩
  ·
    have hodd : Odd (finrank (ZMod 2) (commSpace g)) :=
      Nat.not_even_iff_odd.mp fun h => hΩ (mem_omegaGroup.mpr ⟨hgO, h⟩)
    rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hgO htO,
      finrank_commSpace_reflection hQ r, (ZMod.natCast_eq_one_iff_odd).mpr hodd, Nat.cast_one]
    rfl
  · rw [eichler_conj hgtO, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hte, htf, hge, hgf]

end Finite

end CFSG.GF2Type.Smith1980Orth
