module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Fischer CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec19

section Field

theorem triOdd_sigma_pow_three {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (q : ℕ)
    (hX : Nat.card X = q ^ 3) (hσ : ∀ c : X, σ c = c ^ q) : σ ^ 3 = 1 := by
  classical
  haveI := Fintype.ofFinite X
  refine RingEquiv.ext fun c => ?_
  show (σ ^ 3) c = c
  rw [nf1_pow_apply σ q hσ 3 c, ← hX, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem triOdd_sigma_ne_one {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (q : ℕ) (hq : 2 ≤ q)
    (hX : Nat.card X = q ^ 3) (hσ : ∀ c : X, σ c = c ^ q) : σ ≠ 1 := by
  intro h1
  have key : ∀ c : X, c ^ q = c := fun c => by
    have h := hσ c
    rw [h1] at h
    exact h.symm
  have hle : Nat.card X ≤ q := card_le_of_forall_pow_eq_self X q hq key
  rw [hX] at hle
  exact absurd hle (not_le.2 (nf1_lt_pow_three hq))

end Field

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_plane_shape {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) :
    ∃ x : C0 σ, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∃ g : C0 σ, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1 ∧
      Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e) ∧
      E = Subgroup.closure {MulAut.conj x, MulAut.conj g * tauAut σ ^ e} := by
  classical
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard3, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  haveI : Finite (X ≃+* X) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  have hσ2 : σ ^ 2 ≠ 1 := nf1_sq_ne_one σ hσ3 hσ1
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hsc : (Finset.univ : Finset E).card = 3 ^ 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  have hlt : ({1, σ, σ ^ 2} : Finset (X ≃+* X)).card < (Finset.univ : Finset E).card := by
    rw [hsc]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  have hmaps0 : ∀ a : E, Θ (a : MulAut (C0 σ)) ∈ ({1, σ, σ ^ 2} : Finset (X ≃+* X)) := by
    intro a
    have ha3 : (a : MulAut (C0 σ)) ^ 3 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) (a : MulAut (C0 σ)) a.2
    have hψ : Θ (a : MulAut (C0 σ)) ^ 3 = 1 := by
      rw [← map_pow Θ, ha3, map_one]
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hψ with h | h | h <;> rw [h] <;> simp
  obtain ⟨a, -, b, -, hab, hΘab0⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun a : E => Θ (a : MulAut (C0 σ))) fun a _ => Finset.mem_coe.2 (hmaps0 a)
  have hΘab : Θ (a : MulAut (C0 σ)) = Θ (b : MulAut (C0 σ)) := hΘab0
  obtain ⟨γ, hγE, hγ1, hγΘ⟩ : ∃ γ ∈ E, γ ≠ 1 ∧ Θ γ = 1 := by
    refine ⟨(a : MulAut (C0 σ)) * (b : MulAut (C0 σ))⁻¹,
      E.mul_mem a.2 (E.inv_mem b.2), fun h => hab (Subtype.ext (mul_inv_eq_one.1 h)), ?_⟩
    rw [map_mul, map_inv, hΘab, mul_inv_cancel]
  have hγker : γ ∈ Θ.ker := MonoidHom.mem_ker.2 hγΘ
  rw [hker] at hγker
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hγker
  have hγ3 : γ ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) γ hγE
  have hcx : MulAut.conj x ∈ E := by rw [hx]; exact hγE
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [hx]; exact hγ3
  have hcx1 : MulAut.conj x ≠ 1 := by rw [hx]; exact hγ1
  have hx3 : x ^ 3 = 1 := nf1_conj_injective hZ (by rw [map_pow, hx, hγ3, map_one])
  have hx1 : x ≠ 1 := fun h => hcx1 (by rw [h, map_one])
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, ∀ g : C0 σ, β ≠ MulAut.conj g := by
    by_contra hcon
    push Not at hcon
    exact hout fun φ hφ => by
      obtain ⟨g, hg⟩ := hcon φ hφ
      exact ⟨g, hg.symm⟩
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) β hβE
  have hβΘ3 : Θ β ^ 3 = 1 := by rw [← map_pow Θ, hβ3, map_one]
  have hβ1 : Θ β ≠ 1 := by
    intro h
    have hmem : β ∈ Θ.ker := MonoidHom.mem_ker.2 h
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hmem
    exact hβout g hg.symm
  obtain ⟨e, he12, hΘe⟩ : ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Θ β = σ ^ e := by
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hβΘ3 with h | h | h
    · exact absurd h hβ1
    · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨2, Or.inr rfl, h⟩
  obtain ⟨⟨g, δ⟩, hgδ⟩ := (hdec β).exists
  have hδ : δ = σ ^ e := (hΘ β g δ hgδ).symm.trans hΘe
  have hpow : fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e
  have hβeq : β = MulAut.conj g * tauAut σ ^ e := by
    rw [← hpow, ← hδ]
    exact hgδ
  have hcomm : ∀ u v : E, u * v = v * u := isMulCommutative_iff.1 inferInstance
  have hcomm' : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomm ⟨u, hu⟩ ⟨v, hv⟩)
  have hβ1' : β ≠ 1 := fun h =>
    hβout 1 (h.trans (map_one (MulAut.conj : C0 σ →* MulAut (C0 σ))).symm)
  have hβx : β ≠ MulAut.conj x := hβout x
  have hβx2 : β ≠ MulAut.conj x ^ 2 := fun h =>
    hβout (x ^ 2) (h.trans (map_pow (MulAut.conj : C0 σ →* MulAut (C0 σ)) x 2).symm)
  have hclos : E = Subgroup.closure ({MulAut.conj x, β} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hβE hcx1 hcx3 hβ1' hβx hβx2
  refine ⟨x, hx3, hx1, g, e, he12, ?_, ?_, ?_⟩
  · rw [← hβeq]
    exact hβ3
  · rw [← hβeq]
    exact hcomm' _ hcx _ hβE
  · rw [← hβeq]
    exact hclos

theorem triOdd_fieldActor_pow (e : ℕ) :
    fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
  map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e

theorem triOdd_tauAut_pow_three (hσ3 : σ ^ 3 = 1) : tauAut σ ^ 3 = 1 := by
  rw [← triOdd_fieldActor_pow σ 3, hσ3]
  exact fieldActor_one σ

@[expose] def TriOddIsGLine (β : MulAut (C0 σ)) : Prop :=
  ∃ φ : MulAut (C0 σ), φ * β * φ⁻¹ = tauAut σ ∨ φ * β * φ⁻¹ = (tauAut σ)⁻¹

@[expose] def TriOddHasGLine (E : Subgroup (MulAut (C0 σ))) : Prop :=
  ∃ β ∈ E, TriOddIsGLine σ β

end Model

section Statements


@[expose] def TriOddJPlanes : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ x : C0 σ, x ^ 3 = 1 → x ≠ 1 → tauAut σ x = x →
      Subgroup.closure (fixUnion (Subgroup.closure {MulAut.conj x, tauAut σ})) = ⊤

@[expose] def TriOddNoGLine : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (C0 σ)), CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ¬ E ≤ innerAut (C0 σ) → ¬ TriOddHasGLine σ E → Subgroup.closure (fixUnion E) = ⊤

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_tauAut_not_mem_innerAut {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) :
    tauAut σ ∉ innerAut (C0 σ) := by
  obtain ⟨-, hdec, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  intro hmem
  obtain ⟨g, hg⟩ := (mem_innerAut).1 hmem
  have h1 : tauAut σ = MulAut.conj (1 : C0 σ) * fieldActor (t := TwistTag.D4) σ σ := by
    rw [map_one, one_mul]
  have h2 : tauAut σ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ 1 := by
    rw [fieldActor_one, mul_one]
    exact hg.symm
  have := (hdec (tauAut σ)).unique (y₁ := (g, 1)) (y₂ := (1, σ)) h2 h1
  exact hσ1 (congrArg Prod.snd this).symm

theorem triOdd_exists_plane_with_tau {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (hτ : tauAut σ ∈ E) :
    ∃ x : C0 σ, x ^ 3 = 1 ∧ x ≠ 1 ∧ tauAut σ x = x ∧
      E = Subgroup.closure {MulAut.conj x, tauAut σ} := by
  classical
  obtain ⟨x, hx3, hx1, g, e, -, -, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hℓ2 hf hX hσ E hE hcard hout
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  have hcx : MulAut.conj x ∈ E := by
    rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hcx1 : MulAut.conj x ≠ 1 := fun h =>
    hx1 (nf1_conj_injective hZ (h.trans (map_one MulAut.conj).symm))
  have hτ3 : tauAut σ ^ 3 = 1 := by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) (tauAut σ) hτ
    exact this
  have hτin := triOdd_tauAut_not_mem_innerAut σ hℓ hℓ2 hf hX hσ
  have hτ1 : tauAut σ ≠ 1 := fun h => hτin (h ▸ one_mem _)
  have hτx : tauAut σ ≠ MulAut.conj x := fun h => hτin ⟨x, h.symm⟩
  have hτx2 : tauAut σ ≠ MulAut.conj x ^ 2 := fun h =>
    hτin ⟨x ^ 2, by rw [map_pow]; exact h.symm⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hclos : E = Subgroup.closure ({MulAut.conj x, tauAut σ} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hτ hcx1 hcx3 hτ1 hτx hτx2
  refine ⟨x, hx3, hx1, ?_, hclos⟩
  have hcomm : Commute (MulAut.conj x) (tauAut σ) := by
    have := elemAb_comm hE _ hcx _ hτ
    exact this
  have h1 : tauAut σ * MulAut.conj x * (tauAut σ)⁻¹ = MulAut.conj x := by
    rw [← hcomm.eq]; group
  rw [aut_conj_conj] at h1
  exact nf1_conj_injective hZ h1

theorem triOdd_closure_fixUnion_conj_iff (φ : MulAut (C0 σ)) (E : Subgroup (MulAut (C0 σ))) :
    Subgroup.closure (fixUnion (E.map (MulAut.congr φ).toMonoidHom)) = ⊤ ↔
      Subgroup.closure (fixUnion E) = ⊤ := by
  rw [← planeGen_iff_closure_fixUnion, ← planeGen_iff_closure_fixUnion]
  exact planeGen_map_congr φ E

theorem triOdd_closure_fixUnion_eq_top_of_gline (hJ : TriOddJPlanes) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) (hgl : TriOddHasGLine σ E) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  obtain ⟨β, hβE, φ, hφ⟩ := hgl
  set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr φ).toMonoidHom with hE'
  have hE'ab : CFSG.IsElementaryAbelian 3 E' := isElementaryAbelian_map_three hE (MulAut.congr φ)
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hout' : ¬ E' ≤ innerAut (C0 σ) := by
    intro hle
    apply hout
    intro ψ hψ
    have hmem : (MulAut.congr φ).toMonoidHom ψ ∈ innerAut (C0 σ) := hle ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg⟩ := hmem
    refine ⟨φ⁻¹ g, ?_⟩
    have h1 : φ * ψ * φ⁻¹ = MulAut.conj g := (congr_apply_eq φ ψ).symm.trans hg.symm
    have h2 : ψ = φ⁻¹ * MulAut.conj g * φ := by
      rw [← h1]; group
    rw [h2, show φ⁻¹ * MulAut.conj g * φ = MulAut.conj (φ⁻¹ g) by
      have := aut_conj_conj φ⁻¹ g
      rwa [inv_inv] at this]
  have hτE' : tauAut σ ∈ E' := by
    have hmem : φ * β * φ⁻¹ ∈ E' := ⟨β, hβE, congr_apply_eq φ β⟩
    rcases hφ with h | h
    · rw [← h]; exact hmem
    · have := E'.inv_mem hmem
      rw [h, inv_inv] at this
      exact this
  obtain ⟨x, hx3, hx1, hτx, hEeq⟩ :=
    triOdd_exists_plane_with_tau σ hℓ hℓ2 hf hX hσ E' hE'ab hcard' hout' hτE'
  have key := hJ ℓ f hℓ hℓ2 hℓ3 hf X hX σ hσ x hx3 hx1 hτx
  rw [← hEeq] at key
  exact (triOdd_closure_fixUnion_conj_iff σ φ E).mp key

theorem triOdd_trialityThreePlanesOdd_of_two (hJ : TriOddJPlanes) (hN : TriOddNoGLine) :
    TrialityThreePlanesOdd := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E hE hc hout
  by_cases hg : TriOddHasGLine σ E
  · exact triOdd_closure_fixUnion_eq_top_of_gline σ hJ hℓ hℓ2 hℓ3 hf hK hσ E hE hc hout hg
  · exact hN ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ E hE hc hout hg

end Statements

end CFSG.LieType.SeitzGeneration.ExcWideThree
