module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y2A
public import CFSG.ClassicalInvolution.Q3.Q3TLKAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Q3.Q3TD
open CFSG.ClassicalInvolution.ModelFacts hiding fundamentalSubgroups
open scoped MatrixGroups commutatorElement


local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 𝔽₃
local notation "θ₄" => spinAction (quadPlus 4 𝔽₃)

section Model3

section Frames

theorem fixes_span_of_commute {fr : OFrame Q₄}
    {g : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) (hg3 : g ^ 3 = 1)
    (hLa : ∀ A' : SL(2, 𝔽₃), g * fr.La A' = fr.La A' * g)
    (hsw : ∀ B' : SL(2, 𝔽₃), g * fr.swap.La B' = fr.swap.La B' * g) :
    ∀ x ∈ fr.span, g x = x := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr hLa hsw
  have hx : fr.incl 1 ∈ fr.span := ⟨1, rfl⟩
  have hQ : Q₄ (fr.incl 1) = 1 := by rw [Frame.Q_incl, Matrix.det_one]
  have hne : fr.incl 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hQ
    exact zero_ne_one hQ
  have hc2 : c * c = 1 := by
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO (fr.incl 1)
    rw [hc _ hx, QuadraticMap.map_smul, hQ] at this
    simpa using this
  have hc3 : c ^ 3 = 1 := by
    have h3 : (g ^ 3) (fr.incl 1) = fr.incl 1 := by rw [hg3]; rfl
    have h4 : (g ^ 3) (fr.incl 1) = c ^ 3 • fr.incl 1 := by
      have e1 : g (fr.incl 1) = c • fr.incl 1 := hc _ hx
      have e2 : g (c • fr.incl 1) = c • (c • fr.incl 1) := by rw [map_smul, e1]
      have e3 : g (c • (c • fr.incl 1)) = c • (c • (c • fr.incl 1)) := by rw [map_smul, e2]
      rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, e2]
      rw [e3]
      simp only [smul_smul]
      congr 1
      ring
    rw [h4] at h3
    have h5 : (c ^ 3 - 1) • fr.incl 1 = 0 := by rw [sub_smul, h3, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hne)
  have hc1 : c = 1 := by
    have : c ^ 3 = c := by calc c ^ 3 = c * (c * c) := by ring
      _ = c := by rw [hc2, mul_one]
    rw [← this, hc3]
  intro v hv
  rw [hc v hv, hc1, one_smul]


theorem involution_fixes_span3 {fr F : OFrame Q₄}
    (hLa : ∀ A' B' : SL(2, 𝔽₃), F.La A' * fr.La B' = fr.La B' * F.La A')
    (hsw : ∀ A' B' : SL(2, 𝔽₃), F.La A' * fr.swap.La B' = fr.swap.La B' * F.La A') :
    ∀ x ∈ fr.span, F.La (-1) x = x := by
  obtain ⟨a, b, ha, hb, hab⟩ := Q3TLK.sl2_eq_mul_three (K := 𝔽₃) card_gf3 (-1 : SL(2, 𝔽₃))
  have key : ∀ A' : SL(2, 𝔽₃), A' ^ 3 = 1 → ∀ x ∈ fr.span, F.La A' x = x := by
    intro A' hA3 x hx
    exact fixes_span_of_commute (fr := fr) (F.La_mem_orthogonalGroup A')
      (by rw [← map_pow, hA3, map_one]) (fun B' => hLa A' B') (fun B' => hsw A' B') x hx
  intro x hx
  have e : (-1 : SL(2, 𝔽₃)) = a * (a⁻¹ * (-1) * b⁻¹) * b := by group
  rw [e, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, key b hb x hx,
    key _ hab x hx, key a ha x hx]

theorem span_eq_perp_of_fix3 {fr F : OFrame Q₄} (hfix : ∀ x ∈ fr.span, F.La (-1) x = x) :
    F.span = fr.perp ∧ F.perp = fr.span := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by rw [finrank_plus]
  have hfr := finrank_perp_add_four fr
  have hF := finrank_perp_add_four F
  have hiO : F.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := F.La_mem_orthogonalGroup (-1)
  have hle : F.span ≤ fr.perp := by
    intro v hv
    have hiv : F.La (-1) v = -v := (Frame.mem_span_iff_inv F h2).mp hv
    rw [Frame.mem_perp_iff_forall_incl fr]
    intro X
    have hs : fr.incl X ∈ fr.span := ⟨X, rfl⟩
    have h1 : polar Q₄ (F.La (-1) v) (F.La (-1) (fr.incl X)) = polar Q₄ v (fr.incl X) :=
      polar_map_of_mem hiO v (fr.incl X)
    rw [hiv, hfix _ hs, polar_neg_left] at h1
    have h3 : (2 : 𝔽₃) * polar Q₄ v (fr.incl X) = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hspan : F.span = fr.perp := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [F.finrank_span]
    omega
  refine ⟨hspan, ?_⟩
  have hle' : fr.span ≤ F.perp := fun s hs => (Frame.mem_perp_iff_fix F h2).mpr (hfix s hs)
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle' ?_
  rw [fr.finrank_span]
  omega

theorem exists_second_frame3 {fr : OFrame Q₄}
    {L L' : Subgroup ((Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))}
    (hL : L ∈ fundSet Q₄) (hL' : L' ∈ fundSet Q₄) (hne : L ≠ L')
    (hcA : ∀ g ∈ L, ∀ A' : SL(2, 𝔽₃), g * fr.La A' = fr.La A' * g)
    (hcB : ∀ g ∈ L, ∀ B' : SL(2, 𝔽₃), g * fr.swap.La B' = fr.swap.La B' * g)
    (hcA' : ∀ g ∈ L', ∀ A' : SL(2, 𝔽₃), g * fr.La A' = fr.La A' * g)
    (hcB' : ∀ g ∈ L', ∀ B' : SL(2, 𝔽₃), g * fr.swap.La B' = fr.swap.La B' * g) :
    ∃ fr₂ : OFrame Q₄, L = fr₂.La.range ∧ L' = fr₂.swap.La.range ∧ fr.span = fr₂.perp := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  obtain ⟨i, F₂, hF₂, -⟩ := hL
  obtain ⟨i', F₃, hF₃, -⟩ := hL'
  have hfix₂ : ∀ x ∈ fr.span, F₂.La (-1) x = x :=
    involution_fixes_span3 (fr := fr) (F := F₂)
      (fun A' B' => hcA (F₂.La A') (hF₂ ▸ ⟨A', rfl⟩) B')
      (fun A' B' => hcB (F₂.La A') (hF₂ ▸ ⟨A', rfl⟩) B')
  have hfix₃ : ∀ x ∈ fr.span, F₃.La (-1) x = x :=
    involution_fixes_span3 (fr := fr) (F := F₃)
      (fun A' B' => hcA' (F₃.La A') (hF₃ ▸ ⟨A', rfl⟩) B')
      (fun A' B' => hcB' (F₃.La A') (hF₃ ▸ ⟨A', rfl⟩) B')
  obtain ⟨hs₂, hp₂⟩ := span_eq_perp_of_fix3 hfix₂
  obtain ⟨hs₃, -⟩ := span_eq_perp_of_fix3 hfix₃
  have hinv : F₃.La (-1) = F₂.La (-1) := by
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ fr.span ⊔ fr.perp := by
      rw [fr.isCompl_span_perp.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨s, hs, p, hp, rfl⟩ := Submodule.mem_sup.mp hv
    have hp₂' : p ∈ F₂.span := hs₂ ▸ hp
    have hp₃' : p ∈ F₃.span := hs₃ ▸ hp
    rw [map_add, map_add, hfix₂ s hs, hfix₃ s hs, (Frame.mem_span_iff_inv F₂ h2).mp hp₂',
      (Frame.mem_span_iff_inv F₃ h2).mp hp₃']
  rcases Frame.La_range_eq_or_eq_swap (F := F₂) (F' := F₃) h2 hinv with h | h
  · exact absurd (hF₂.trans (h.symm.trans hF₃.symm)) hne
  · exact ⟨F₂, hF₂, hF₃.trans h, hp₂.symm⟩

end Frames

section Kind

theorem orderOf_La_neg_one3 (F : OFrame Q₄) : orderOf (F.La (-1)) = 2 := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  refine orderOf_eq_prime (by rw [pow_two]; exact F.La_neg_one_mul_self) ?_
  intro h
  have : (-1 : SL(2, 𝔽₃)) = 1 := F.La_injective (by rw [h, map_one])
  have h' := congrArg (fun A : SL(2, 𝔽₃) => (A : Matrix (Fin 2) (Fin 2) 𝔽₃) 0 0) this
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
  simp at h'
  exact h2 (by linear_combination -h')

theorem commutes_involution_of_normalizes3 {F : OFrame Q₄}
    {g : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)}
    (hg : ∀ h ∈ F.La.range, g * h * g⁻¹ ∈ F.La.range) :
    g * F.La (-1) = F.La (-1) * g := by
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hmem : g * F.La (-1) * g⁻¹ ∈ F.La.range := hg _ ⟨-1, rfl⟩
  have hord : orderOf (g * F.La (-1) * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) (F.La (-1))
    rw [MulAut.conj_apply] at this
    rw [this]
    exact orderOf_La_neg_one3 F
  have := (IsFundamental.of_frame F).eq_of_orderOf_eq_two hodd hmem hord
  calc g * F.La (-1) = (g * F.La (-1) * g⁻¹) * g := by group
    _ = F.La (-1) * g := by rw [this]

theorem parity_model3 {X : Type} [Group X] (ψ : spinGroup Q₄ →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (τ : X ≃* X)
    (hτr : ∀ k, τ (ψ k) ∈ ψ.range) {A B C C' N : Subgroup (spinGroup Q₄)}
    (hA : A ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hB : B ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hC : C ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hC' : C' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hN : N ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hAB : A ≠ B) (hcAB : Commutes A B) (hCC' : C ≠ C')
    (hcAC : Commutes A C) (hcAC' : Commutes A C') (hcBC : Commutes B C) (hcBC' : Commutes B C')
    {n : spinGroup Q₄} (hn : n ∈ N) (hn2 : n * n = 1) (hn1 : n ≠ 1)
    (hnA : conjSub n A = A) (hnC : conjSub n C = C) (hτA : ∀ r ∈ A, τ (ψ r) = ψ r)
    (hτB : ∀ r ∈ B, τ (ψ r) = ψ r)
    (hτC : ∀ r ∈ C, τ (ψ r) = ψ (n * r * n⁻¹)) (hτC' : ∀ r ∈ C', τ (ψ r) = ψ (n * r * n⁻¹))
    {xC : spinGroup Q₄} (hxC : xC ∈ C) (hxC2 : xC * xC = 1) (hxC1 : xC ≠ 1) :
    (∀ r ∈ N, τ (ψ r) = ψ r) ∨ (∀ r ∈ N, τ (ψ (xC * r * xC⁻¹)) = ψ r) := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have cq := centralQuot3_plus (m := 4) le_rfl
  obtain ⟨ρ, fr, hρ, hρ', hA', hB'⟩ := exists_ordinary_pair3 hA hB hAB hcAB
  set ψ' : spinGroup Q₄ →* X := ψ.comp ρ.symm.toMonoidHom with hψ'
  have hψ'ρ : ∀ y, ψ' (ρ y) = ψ y := fun y => by simp [ψ']
  have hker' : ψ'.ker ≤ Subgroup.center (spinGroup Q₄) := by
    intro y hy
    have h1 : ρ.symm y ∈ ψ.ker := hy
    have := RouteD.TWS6.map_mem_center ρ (hψ h1)
    simpa using this
  have hτr' : ∀ k, τ (ψ' k) ∈ ψ'.range := by
    intro k
    obtain ⟨m, hm⟩ := hτr (ρ.symm k)
    exact ⟨ρ m, by rw [hψ'ρ, hm]; rfl⟩
  have hAf := hρ A hA
  have hBf := hρ B hB
  have hCf := hρ C hC
  have hC'f := hρ C' hC'
  have hNf := hρ N hN
  set A₁ := A.map ρ.toMonoidHom with hA₁
  set B₁ := B.map ρ.toMonoidHom with hB₁
  set C₁ := C.map ρ.toMonoidHom with hC₁
  set C₂ := C'.map ρ.toMonoidHom with hC₂
  set N₁ := N.map ρ.toMonoidHom with hN₁
  have hcomm : ∀ {P Q : Subgroup (spinGroup Q₄)}, Commutes P Q →
      ∀ g ∈ P.map θ₄, ∀ h ∈ Q.map θ₄, g * h = h * g := by
    rintro P Q hPQ _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hPQ a ha b hb]
  have hcAC₁ : Commutes A₁ C₁ := (RouteD.TWS6.commutes_map_equiv ρ).mpr hcAC
  have hcAC₂ : Commutes A₁ C₂ := (RouteD.TWS6.commutes_map_equiv ρ).mpr hcAC'
  have hcBC₁ : Commutes B₁ C₁ := (RouteD.TWS6.commutes_map_equiv ρ).mpr hcBC
  have hcBC₂ : Commutes B₁ C₂ := (RouteD.TWS6.commutes_map_equiv ρ).mpr hcBC'
  have hne : C₁.map θ₄ ≠ C₂.map θ₄ := by
    intro h
    have := eq_of_map_eq_of_pow3 θ₄ (ker_spinAction_le_center Q₄) cq.cop (cq.pow3 _ hCf)
      (cq.pow3 _ hC'f) h
    exact hCC' (Subgroup.map_injective ρ.injective this)
  obtain ⟨fr₂, hL₂, hL₂', hS⟩ := exists_second_frame3 (fr := fr) (cq.map_mem _ hCf)
    (cq.map_mem _ hC'f) hne
    (fun g hg A' => by
      have : fr.La A' ∈ A₁.map θ₄ := by rw [hA']; exact ⟨A', rfl⟩
      exact hcomm (Commutes.symm hcAC₁) g hg _ this)
    (fun g hg B' => by
      have : fr.swap.La B' ∈ B₁.map θ₄ := by rw [hB']; exact ⟨B', rfl⟩
      exact hcomm (Commutes.symm hcBC₁) g hg _ this)
    (fun g hg A' => by
      have : fr.La A' ∈ A₁.map θ₄ := by rw [hA']; exact ⟨A', rfl⟩
      exact hcomm (Commutes.symm hcAC₂) g hg _ this)
    (fun g hg B' => by
      have : fr.swap.La B' ∈ B₁.map θ₄ := by rw [hB']; exact ⟨B', rfl⟩
      exact hcomm (Commutes.symm hcBC₂) g hg _ this)
  have hρinj : ∀ a, ρ a = 1 → a = 1 := fun a ha => ρ.injective (by rw [ha, map_one])
  set n' := ρ n with hn'
  set xC' := ρ xC with hxC'
  have hn'N : n' ∈ N₁ := ⟨n, hn, rfl⟩
  have hxC'C : xC' ∈ C₁ := ⟨xC, hxC, rfl⟩
  have hn'2 : n' * n' = 1 := by rw [hn', ← map_mul, hn2, map_one]
  have hxC'2 : xC' * xC' = 1 := by rw [hxC', ← map_mul, hxC2, map_one]
  have hn'1 : n' ≠ 1 := fun h => hn1 (hρinj n h)
  have hxC'1 : xC' ≠ 1 := fun h => hxC1 (hρinj xC h)
  obtain ⟨iN, frN, hfrN, hiN⟩ := cq.map_mem _ hNf
  have hθn' : θ₄ n' = frN.La (-1) := by
    have hmem : θ₄ n' ∈ frN.La.range := hfrN ▸ Subgroup.mem_map_of_mem _ hn'N
    have hord : orderOf (θ₄ n') = 2 := by
      refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hn'2, map_one]) ?_
      intro h
      exact hn'1 (cq.inj _ hNf n' hn'N h)
    exact (IsFundamental.of_frame frN).eq_of_orderOf_eq_two hodd hmem hord
  have hθx : θ₄ xC' = fr₂.La (-1) := by
    have hmem : θ₄ xC' ∈ fr₂.La.range := hL₂ ▸ Subgroup.mem_map_of_mem _ hxC'C
    have hord : orderOf (θ₄ xC') = 2 := by
      refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hxC'2, map_one]) ?_
      intro h
      exact hxC'1 (cq.inj _ hCf xC' hxC'C h)
    exact (IsFundamental.of_frame fr₂).eq_of_orderOf_eq_two hodd hmem hord
  have hnorm : ∀ {P : Subgroup (spinGroup Q₄)}, conjSub n P = P →
      ∀ a ∈ P.map ρ.toMonoidHom, n' * a * n'⁻¹ ∈ P.map ρ.toMonoidHom := by
    intro P hP a ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have h1 : n * a₀ * n⁻¹ ∈ P := by
      rw [← hP]
      exact conj_mem_conjSub ha₀
    exact ⟨n * a₀ * n⁻¹, h1, by simp [hn']⟩
  have hnormθ : ∀ {P : Subgroup (spinGroup Q₄)} {F : OFrame Q₄},
      (P.map ρ.toMonoidHom).map θ₄ = F.La.range → conjSub n P = P →
      θ₄ n' * F.La (-1) = F.La (-1) * θ₄ n' := by
    intro P F hF hP
    refine commutes_involution_of_normalizes3 (fun h hh => ?_)
    rw [← hF] at hh ⊢
    obtain ⟨a, ha, rfl⟩ := hh
    exact ⟨n' * a * n'⁻¹, hnorm hP a ha, by rw [map_mul, map_mul, map_inv]⟩
  have hnA' : θ₄ n' * fr.La (-1) = fr.La (-1) * θ₄ n' := hnormθ hA' hnA
  have hnC' : θ₄ n' * fr₂.La (-1) = fr₂.La (-1) * θ₄ n' := hnormθ hL₂ hnC
  have hσA : ∀ r ∈ A₁, τ (ψ' r) = ψ' r := by
    rintro _ ⟨a, ha, rfl⟩
    show τ (ψ' (ρ a)) = ψ' (ρ a)
    rw [hψ'ρ]
    exact hτA a ha
  have hσB : ∀ r ∈ B₁, τ (ψ' r) = ψ' r := by
    rintro _ ⟨a, ha, rfl⟩
    show τ (ψ' (ρ a)) = ψ' (ρ a)
    rw [hψ'ρ]
    exact hτB a ha
  have hσC : ∀ r ∈ C₁, τ (ψ' r) = ψ' (n' * r * n'⁻¹) := by
    rintro _ ⟨c, hc, rfl⟩
    show τ (ψ' (ρ c)) = ψ' (ρ n * ρ c * (ρ n)⁻¹)
    rw [hψ'ρ, ← map_inv, ← map_mul, ← map_mul, hψ'ρ]
    exact hτC c hc
  have hσC' : ∀ r ∈ C₂, τ (ψ' r) = ψ' (n' * r * n'⁻¹) := by
    rintro _ ⟨c, hc, rfl⟩
    show τ (ψ' (ρ c)) = ψ' (ρ n * ρ c * (ρ n)⁻¹)
    rw [hψ'ρ, ← map_inv, ← map_mul, ← map_mul, hψ'ρ]
    exact hτC' c hc
  have hcore := parity_core3 ψ' hker' τ hτr' (fr := fr) (fr₂ := fr₂) (frN := frN) (A := A₁)
    (B := B₁) (C := C₁) (C' := C₂) (N := N₁) hA' hB' hL₂ hL₂' hfrN (cq.pow3 _ hAf)
    (cq.pow3 _ hBf) (cq.pow3 _ hCf) (cq.pow3 _ hC'f) (cq.pow3 _ hNf) hS (n := n') (xC := xC')
    hθn' hθx hnA' hnC' hσA hσB hσC hσC'
  rcases hcore with h | h
  · left
    intro r hr
    have := h (ρ r) ⟨r, hr, rfl⟩
    rwa [hψ'ρ] at this
  · right
    intro r hr
    have := h (ρ r) ⟨r, hr, rfl⟩
    rw [show xC' * ρ r * xC'⁻¹ = ρ (xC * r * xC⁻¹) by simp [hxC'], hψ'ρ, hψ'ρ] at this
    exact this

end Kind

end Model3

end CFSG.ClassicalInvolution.Q3.Q3P21
