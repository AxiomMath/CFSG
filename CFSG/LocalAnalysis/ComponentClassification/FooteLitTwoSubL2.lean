module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubL2Std
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Cent

public section

namespace CFSG.ComponentClassification.FooteLit.TwoSub

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem twoSub_linear (hodd : IsOddPrimePower (Nat.card F)) (D : Sylow 2 (PSL2 F))
    {Q : Subgroup (PGammaL2 F)} (hQ : IsPGroup 2 Q)
    (hDQ : (D : Subgroup (PSL2 F)).map (incl F) ≤ Q) (hr : ∀ x ∈ Q, x.right = 1) :
    Nat.card Q ≤ 2 * Nat.card D ∧ AschbacherTheorem3.IsDihedralTwoGroup Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hinl : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
    SemidirectProduct.inl_injective
  have hpgl := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F)
  have hmap : (linearPart Q).map SemidirectProduct.inl = Q := by
    apply le_antisymm (map_comap_le _ _)
    intro x hx
    have hx' := Aut5L2.eq_inl_of_right_eq_one (hr x hx)
    refine ⟨x.left, ?_, hx'.symm⟩
    show SemidirectProduct.inl x.left ∈ Q
    rw [← hx']
    exact hx
  have eQ : linearPart Q ≃* Q :=
    (equivMapOfInjective _ _ hinl).trans (MulEquiv.subgroupCongr hmap)
  have hcard : Nat.card Q = Nat.card (linearPart Q) := (Nat.card_congr eQ.toEquiv).symm
  obtain ⟨S, hS⟩ := (hQ.of_equiv eQ.symm).exists_le_sylow
  have hSD : Nat.card S = 2 * Nat.card D := by
    have h1 := Sylow.card_eq_multiplicity D
    have h2 := Sylow.card_eq_multiplicity S
    rw [pgl2_card_eq_two_mul hodd, Nat.factorization_mul two_ne_zero Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one, ← h1]
      at h2
    rw [h2, mul_comm]
  set D₀ := (D : Subgroup (PSL2 F)).map
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hD₀def
  have hD₀ : D₀ ≤ linearPart Q := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDQ ⟨d, hd, rfl⟩
  have hD₀c : Nat.card D₀ = Nat.card D := card_map_of_injective hpgl
  obtain ⟨t, ht⟩ := card_dvd_of_le hD₀
  have hdvd := card_dvd_of_le hS
  rw [ht, hSD, hD₀c, mul_comm 2] at hdvd
  rw [hD₀c] at ht
  rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd) with
    rfl | rfl
  · rw [mul_one] at ht
    refine ⟨by rw [hcard, ht]; omega, ?_⟩
    have heq : D₀ = linearPart Q := eq_of_le_of_card_ge hD₀ (by rw [ht, hD₀c])
    obtain ⟨m, hm, ⟨ψ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hodd D
    refine ⟨m + 1, by omega, ⟨?_⟩⟩
    rw [Nat.add_sub_cancel]
    exact eQ.symm.trans ((MulEquiv.subgroupCongr heq.symm).trans
      ((equivMapOfInjective _ _ hpgl).symm.trans ψ))
  · have heq : linearPart Q = S := eq_of_le_of_card_ge hS (by rw [hSD, ht, mul_comm])
    refine ⟨by rw [hcard, ht, mul_comm], ?_⟩
    obtain ⟨m, hm, ⟨ψ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd S
    refine ⟨m + 1, by omega, ⟨?_⟩⟩
    rw [Nat.add_sub_cancel]
    exact eQ.symm.trans ((MulEquiv.subgroupCongr heq).trans ψ)

variable {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

include e in
theorem twoSub_l2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (R : Sylow 2 Y) (P : Subgroup (MulAut Y)) (hP : IsPGroup 2 P)
    (hRP : (R : Subgroup Y).map (MulAut.conj : Y →* MulAut Y) ≤ P) :
    (Nat.card P ≤ 2 * Nat.card R ∧ (AschbacherTheorem3.IsDihedralTwoGroup P ∨
      AschbacherTheorem3.IsSemidihedralTwoGroup P)) ∨
    ∃ β ∈ P, β * β = 1 ∧ β ∉ innAut5 Y ∧ ∃ R' : Sylow 2 Y, ∀ r ∈ (R' : Subgroup Y), β r = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set P' := P.map (autEquiv e).toMonoidHom with hP'def
  have eP : P ≃* P' := (autEquiv e).subgroupMap P
  have hP' : IsPGroup 2 P' := hP.map _
  set D := sylowMap e R with hDdef
  have hDP : (D : Subgroup (PSL2 F)).map (incl F) ≤ P' := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨MulAut.conj (e.symm d), hRP ⟨e.symm d, (Aut5L2.mem_sylowMap_iff e R _).mp (by
      rw [MulEquiv.apply_symm_apply]; exact hd), rfl⟩, ?_⟩
    show autEquiv e (MulAut.conj (e.symm d)) = incl F d
    rw [autEquiv_conj, MulEquiv.apply_symm_apply]
  have hcardD : Nat.card D = Nat.card R := card_sylowMap e R
  by_cases hlin : ∀ x ∈ P', x.right = 1
  · obtain ⟨h1, ⟨n, hn, ⟨ψ⟩⟩⟩ := twoSub_linear hodd D hP' hDP hlin
    refine Or.inl ⟨?_, Or.inl ⟨n, hn, ⟨eP.trans ψ⟩⟩⟩
    rw [Nat.card_congr eP.toEquiv, ← hcardD]
    exact h1
  push Not at hlin
  obtain ⟨x, hx, hxr⟩ := hlin
  obtain ⟨j, hj⟩ := hP' ⟨x, hx⟩
  have hfe : Even f :=
    Aut5L2.even_of_right_ne_one hp hF x (k := j) (congrArg Subtype.val hj) hxr
  obtain ⟨hsq, hq4, hn⟩ := Aut5L2.model_hyps_of_even hp hp2 hf hF hfe
  obtain ⟨h, hh⟩ := Aut5L2.exists_conj_stdT hodd hsq hq4 D
  set c := incl F h with hc
  set Q := P'.map (MulAut.conj c⁻¹).toMonoidHom with hQdef
  have eQ : P' ≃* Q := (MulAut.conj c⁻¹).subgroupMap P'
  have hQ : IsPGroup 2 Q := hP'.map _
  have hTQ : (stdT F).map (incl F) ≤ Q := by
    rintro _ ⟨t, ht, rfl⟩
    have hd : h * t * h⁻¹ ∈ (D : Subgroup (PSL2 F)) := by
      rw [hh, show h⁻¹ * (h * t * h⁻¹) * h = t by group]
      exact ht
    refine ⟨incl F (h * t * h⁻¹), hDP ⟨_, hd, rfl⟩, ?_⟩
    show MulAut.conj c⁻¹ (incl F (h * t * h⁻¹)) = incl F t
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hc]
    group
  have hnl : ∃ y ∈ Q, y.right ≠ 1 := by
    refine ⟨MulAut.conj c⁻¹ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [MulAut.conj_apply, right_conj]
    exact hxr
  have hDk : Nat.card D = 2 ^ twoVal F := by
    rw [Sylow.card_eq_multiplicity, psl2_factorization_two hodd hq4]
  rcases twoSub_std hp hp2 hF hodd hsq hq4 hn hQ hTQ hnl with ⟨h1, ⟨n, hn4, ⟨ψ⟩⟩⟩ |
    ⟨β, hβQ, hβ2, hβr, hβc⟩
  · refine Or.inl ⟨?_, Or.inr ⟨n, hn4, ⟨(eP.trans eQ).trans ψ⟩⟩⟩
    rw [Nat.card_congr (eP.trans eQ).toEquiv, ← hcardD, hDk]
    exact h1
  right
  obtain ⟨y, ⟨α, hαP, rfl⟩, rfl⟩ := hβQ
  set A := autEquiv e α with hA
  have hβ : (MulAut.conj c⁻¹).toMonoidHom ((autEquiv e).toMonoidHom α) = c⁻¹ * A * c := by
    change MulAut.conj c⁻¹ A = _
    rw [MulAut.conj_apply, inv_inv]
  rw [hβ] at hβ2 hβr hβc
  refine ⟨α, hαP, ?_, ?_, R, fun r hr => ?_⟩
  · apply (autEquiv e).injective
    rw [map_mul, map_one, ← hA]
    calc A * A = c * ((c⁻¹ * A * c) * (c⁻¹ * A * c)) * c⁻¹ := by group
      _ = 1 := by rw [hβ2]; group
  · intro hαI
    rw [Aut5L2.mem_innAut5_iff e, ← hA] at hαI
    apply hβr
    rw [show c⁻¹ * A * c = c⁻¹ * A * c⁻¹⁻¹ by rw [inv_inv], right_conj]
    exact ((mem_pslRange_iff A).mp hαI).1
  · rw [apply_eq_iff_commute e α r, ← hA]
    have ht : h⁻¹ * e r * h ∈ stdT F := (hh _).mp ((Aut5L2.mem_sylowMap_iff e R r).mpr hr)
    have h1 := hβc _ ⟨_, ht, rfl⟩
    rw [map_mul, map_mul, map_inv, ← hc] at h1
    calc A * incl F (e r) = c * ((c⁻¹ * A * c) * (c⁻¹ * incl F (e r) * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * incl F (e r) * c) * (c⁻¹ * A * c)) * c⁻¹ := by rw [h1]
      _ = incl F (e r) * A := by group

end CFSG.ComponentClassification.FooteLit.TwoSub
