module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupL2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteSolv
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Subgroup Equiv

@[expose] def a7Rho : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

@[expose] def a7Sigma : Perm (Fin 7) := swap 1 3 * swap 4 5

theorem a7Rho_mem : a7Rho ∈ alternatingGroup (Fin 7) := by
  change Perm.sign a7Rho = 1
  rw [a7Rho, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul,
    Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1), Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2),
    Perm.sign_swap (by decide : (2 : Fin 7) ≠ 3), Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

theorem a7Sigma_mem : a7Sigma ∈ alternatingGroup (Fin 7) := by
  change Perm.sign a7Sigma = 1
  rw [a7Sigma, Perm.sign_mul, Perm.sign_swap (by decide : (1 : Fin 7) ≠ 3),
    Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

theorem exists_noncomm_two_subgroup_a7 :
    ∃ H : Subgroup (alternatingGroup (Fin 7)), IsPGroup 2 H ∧
      ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  set ρ : alternatingGroup (Fin 7) := ⟨a7Rho, a7Rho_mem⟩
  set σ : alternatingGroup (Fin 7) := ⟨a7Sigma, a7Sigma_mem⟩
  have hσ2 : σ * σ = 1 := Subtype.ext (by decide)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by decide)
  have hne : ρ * σ ≠ σ * ρ := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hρ4 : orderOf ρ = 4 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf a7Rho = 4
    apply (orderOf_eq_iff (by norm_num)).mpr
    constructor
    · decide
    · intro m hm0 hm4
      interval_cases m <;> decide
  have hσU : σ ∉ zpowers ρ := by
    rintro ⟨k, hk⟩
    apply hne
    rw [← hk]
    exact ((Commute.refl ρ).zpow_left k).eq.symm
  have hinv : ∀ x ∈ zpowers ρ, σ * x * σ⁻¹ = x⁻¹ := by
    rintro _ ⟨k, rfl⟩
    have := map_zpow (MulAut.conj σ) ρ k
    simp only [MulAut.conj_apply] at this
    rw [this, hrel, inv_zpow]
  obtain ⟨d⟩ := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup (zpowers ρ) σ hσU hσ2
    hinv
  refine ⟨zpowers ρ ⊔ zpowers σ, IsPGroup.of_card (n := 3) ?_, ρ,
    mem_sup_left (mem_zpowers ρ), σ, mem_sup_right (mem_zpowers σ), hne⟩
  rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card, Nat.card_zpowers, hρ4]
  norm_num

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem exists_swap_centralizing_kleinFour {V : Subgroup (alternatingGroup (Fin 7))}
    (hV : IsKleinFour V) :
    ∃ a b : Fin 7, a ≠ b ∧ ∀ v ∈ V,
      (v : Perm (Fin 7)) * swap a b = swap a b * (v : Perm (Fin 7)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcard : Nat.card V = 4 := IsKleinFour.card_four
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : V)
  obtain ⟨y, hy1, hyx⟩ : ∃ y : V, y ≠ 1 ∧ y ≠ x := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset V) ⊆ {1, x} := by
      intro w _
      by_cases hw : w = 1
      · simp [hw]
      · simp [h w hw]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at this
    have h2 : ({1, x} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hall : ∀ v : V, v = x * y ∨ v = x ∨ v = y ∨ v = 1 := by
    intro v
    have h := IsKleinFour.eq_finset_univ hx1 hy1 hyx.symm
    have hv : v ∈ ({x * y, x, y, 1} : Finset V) := by rw [h]; exact Finset.mem_univ v
    simpa using hv
  set X : Perm (Fin 7) := ((x : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hX
  set Yp : Perm (Fin 7) := ((y : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hYp
  have hx2 : (x : alternatingGroup (Fin 7)) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self x)
  have hxa1 : (x : alternatingGroup (Fin 7)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hct := a7_involution_cycleType _ hx2 hxa1
  have hsupp : X.support.card = 4 := by
    rw [← Perm.sum_cycleType, hX, hct]
    rfl
  set Fx : Finset (Fin 7) := Finset.univ.filter (fun i => X i = i) with hFxdef
  have hFx : Fx.card = 3 := by
    have : Fx = Finset.univ \ X.support := by
      ext i
      simp [Fx, Perm.mem_support]
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hsupp]
  obtain ⟨a, b, c, hab, hac, hbc, hFxeq⟩ := Finset.card_eq_three.mp hFx
  have hmemF : ∀ i, X i = i ↔ i = a ∨ i = b ∨ i = c := by
    intro i
    have : i ∈ Fx ↔ X i = i := by simp [Fx]
    rw [← this, hFxeq]
    simp
  have hxa : X a = a := (hmemF a).mpr (Or.inl rfl)
  have hxb : X b = b := (hmemF b).mpr (Or.inr (Or.inl rfl))
  have hxc : X c = c := (hmemF c).mpr (Or.inr (Or.inr rfl))
  have hXY : X * Yp = Yp * X := by
    have := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm x y
    exact congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) this
  have hYF : ∀ i, X i = i → X (Yp i) = Yp i := fun i hi => by
    have := congrArg (· i) hXY
    simp only [Perm.mul_apply, hi] at this
    exact this
  have hY2 : ∀ i, Yp (Yp i) = i := fun i => by
    have h1 : Yp * Yp = 1 := by
      have := IsKleinFour.mul_self y
      exact congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) this
    have := congrArg (· i) h1
    simpa [Perm.mul_apply] using this
  have hYinj : Function.Injective Yp := Yp.injective
  obtain ⟨e₁, f₁, hef, hxe, hxf, hy⟩ : ∃ e₁ f₁ : Fin 7, e₁ ≠ f₁ ∧ X e₁ = e₁ ∧ X f₁ = f₁ ∧
      ((Yp e₁ = e₁ ∧ Yp f₁ = f₁) ∨ (Yp e₁ = f₁ ∧ Yp f₁ = e₁)) := by
    rcases (hmemF (Yp a)).mp (hYF a hxa) with h | h | h
    · refine ⟨b, c, hbc, hxb, hxc, ?_⟩
      rcases (hmemF (Yp b)).mp (hYF b hxb) with h1 | h1 | h1
      · exact absurd (hYinj (h1.trans h.symm)) hab.symm
      · left
        refine ⟨h1, ?_⟩
        rcases (hmemF (Yp c)).mp (hYF c hxc) with h2 | h2 | h2
        · exact absurd (hYinj (h2.trans h.symm)) hac.symm
        · exact absurd (hYinj (h2.trans h1.symm)) hbc.symm
        · exact h2
      · right
        exact ⟨h1, by rw [← h1, hY2]⟩
    · exact ⟨a, b, hab, hxa, hxb, Or.inr ⟨h, by rw [← h, hY2]⟩⟩
    · exact ⟨a, c, hac, hxa, hxc, Or.inr ⟨h, by rw [← h, hY2]⟩⟩
  refine ⟨e₁, f₁, hef, ?_⟩
  have hcx : X * swap e₁ f₁ = swap e₁ f₁ * X := by rw [Equiv.mul_swap_eq_swap_mul, hxe, hxf]
  have hcy : Yp * swap e₁ f₁ = swap e₁ f₁ * Yp := by
    rw [Equiv.mul_swap_eq_swap_mul]
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Equiv.swap_comm]
  intro v hv
  have hcoe : ∀ w : V, ((w : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((w : alternatingGroup (Fin 7)) : Perm (Fin 7)) := fun _ => rfl
  rcases hall ⟨v, hv⟩ with h | h | h | h
  · have hv' : (v : Perm (Fin 7)) = X * Yp :=
      congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    rw [hv', mul_assoc, hcy, ← mul_assoc, hcx, mul_assoc]
  · have hv' : (v : Perm (Fin 7)) = X :=
      congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    rw [hv', hcx]
  · have hv' : (v : Perm (Fin 7)) = Yp :=
      congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    rw [hv', hcy]
  · have hv' : (v : Perm (Fin 7)) = 1 :=
      congrArg (fun w : V => ((w : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    rw [hv', one_mul, mul_one]

abbrev a7Conj : Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal

theorem a7Conj_apply (π : Perm (Fin 7)) (g : alternatingGroup (Fin 7)) :
    ((a7Conj π g : alternatingGroup (Fin 7)) : Perm (Fin 7)) = π * g * π⁻¹ :=
  MulAut.conjNormal_apply π g

theorem exists_a7Conj_eq (f : MulAut (alternatingGroup (Fin 7))) : ∃ π, a7Conj π = f := by
  obtain ⟨π, hπ⟩ := CFSG.Milestones.alternating_automorphism_permutation (Or.inr le_rfl) f
  exact ⟨π, MulEquiv.ext fun g => Subtype.ext (by rw [a7Conj_apply, hπ])⟩

theorem a7Conj_of_mem {π : Perm (Fin 7)} (hπ : π ∈ alternatingGroup (Fin 7)) :
    a7Conj π = MulAut.conj (⟨π, hπ⟩ : alternatingGroup (Fin 7)) :=
  MulEquiv.ext fun g => Subtype.ext (by
    rw [a7Conj_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])

theorem mem_of_a7Conj_eq {π : Perm (Fin 7)} {h : alternatingGroup (Fin 7)}
    (hπ : a7Conj π = MulAut.conj h) : π ∈ alternatingGroup (Fin 7) := by
  have h1 : a7Conj (π * (h : Perm (Fin 7))⁻¹) = 1 := by
    rw [map_mul, map_inv, a7Conj_of_mem h.2, hπ, mul_inv_cancel]
  have h2 : π * (h : Perm (Fin 7))⁻¹ = 1 := by
    apply LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by rw [Fintype.card_fin]; norm_num)
    intro g hg
    have := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) =>
      ((φ ⟨g, hg⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7))) h1
    simp only [a7Conj_apply, MulAut.one_apply] at this
    calc π * (h : Perm (Fin 7))⁻¹ * g = π * (h : Perm (Fin 7))⁻¹ * g *
          (π * (h : Perm (Fin 7))⁻¹)⁻¹ * (π * (h : Perm (Fin 7))⁻¹) := by group
      _ = g * (π * (h : Perm (Fin 7))⁻¹) := by rw [this]
  rw [mul_inv_eq_one] at h2
  rw [h2]
  exact h.2

theorem congr_conj_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) (s : G) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) :=
  MulEquiv.ext fun g => by simp [MulAut.congr_apply, MulAut.conj_apply]

theorem fourgroupE8_alt7 {S : Type} [Group S] [Finite S] (e : S ≃* alternatingGroup (Fin 7))
    (E : Subgroup (MulAut S)) (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) :
    (∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x) ∧
      ∀ V : Subgroup S, IsKleinFour V →
        ∃ F : Subgroup (MulAut S), F ≤ E ⊔ (MulAut.conj : S →* MulAut S).range ∧
          (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 ∧ V.map (MulAut.conj : S →* MulAut S) ≤ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x := by
    intro P
    obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := exists_noncomm_two_subgroup_a7
    set H' := H.map e.symm.toMonoidHom
    have hH'2 : IsPGroup 2 H' := hH2.map _
    obtain ⟨Q, hQ⟩ := hH'2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P
    have hmem : ∀ z ∈ H, g * e.symm z * g⁻¹ ∈ (P : Subgroup S) := by
      intro z hz
      rw [← hg, mem_smul_sylow_iff_conj, show g⁻¹ * (g * e.symm z * g⁻¹) * g = e.symm z by
        group]
      exact hQ ⟨z, hz, rfl⟩
    refine ⟨_, hmem x hx, _, hmem y hy, fun h => hxy ?_⟩
    have h1 : e.symm (x * y) = e.symm (y * x) := by
      rw [map_mul, map_mul]
      calc e.symm x * e.symm y = g⁻¹ * (g * e.symm x * g⁻¹ * (g * e.symm y * g⁻¹)) * g := by
            group
        _ = g⁻¹ * (g * e.symm y * g⁻¹ * (g * e.symm x * g⁻¹)) * g := by rw [h]
        _ = e.symm y * e.symm x := by group
    exact e.symm.injective h1
  refine ⟨hi, fun V hV => ?_⟩
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (e.injective (hz'.trans (map_one _).symm))
  have hconj_inj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro a b h
    have hc : b⁻¹ * a ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      simp only [MulAut.conj_apply] at this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [this]
        _ = b⁻¹ * a * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  obtain ⟨e₁, he₁E, he₁⟩ : ∃ e₁ ∈ E, e₁ ∉ (MulAut.conj : S →* MulAut S).range := by
    by_contra h
    push Not at h
    set E' := E.comap (MulAut.conj : S →* MulAut S)
    have hE'map : E'.map MulAut.conj = E := Subgroup.map_comap_eq_self fun x hx => h x hx
    have hE'card : Nat.card E' = 8 := by
      rw [← Subgroup.card_map_of_injective hconj_inj, hE'map, hE8]
    have hS8 : 2 ^ (Nat.card S).factorization 2 = 8 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven,
        show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num, Nat.factorization_mul (by norm_num)
          (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    let P : Sylow 2 S := Sylow.ofCard E' (by rw [hE'card, hS8])
    obtain ⟨x, hx, y, hy, hxy⟩ := hi P
    have hx' : x ∈ E' := by simpa [P] using hx
    have hy' : y ∈ E' := by simpa [P] using hy
    have hsq : ∀ w ∈ E', w * w = 1 := fun w hw => hconj_inj (by
      rw [map_mul, map_one]; exact hE2 _ hw)
    apply hxy
    have h1 := hsq _ (mul_mem hx' hy')
    have h2 := hsq x hx'
    have h3 := hsq y hy'
    calc x * y = x * (x * y * (x * y)) * y := by rw [h1, mul_one]
      _ = (x * x) * y * x * (y * y) := by group
      _ = y * x := by rw [h2, h3, one_mul, mul_one]
  obtain ⟨π, hπ⟩ := exists_a7Conj_eq (MulAut.congr e e₁)
  have hπodd : π ∉ alternatingGroup (Fin 7) := by
    intro hπA
    apply he₁
    refine ⟨e.symm ⟨π, hπA⟩, (MulAut.congr e).injective ?_⟩
    rw [← hπ, a7Conj_of_mem hπA, congr_conj_eq, MulEquiv.apply_symm_apply]
  set V' := V.map e.toMonoidHom with hV'def
  have hV' : IsKleinFour V' := ⟨by
      rw [Subgroup.card_map_of_injective e.injective]
      exact IsKleinFour.card_four, by
      rw [← Monoid.exponent_eq_of_mulEquiv (V.equivMapOfInjective e.toMonoidHom e.injective)]
      exact IsKleinFour.exponent_two⟩
  obtain ⟨a, b, hab, hsw⟩ := exists_swap_centralizing_kleinFour hV'
  set τ : MulAut S := (MulAut.congr e).symm (a7Conj (swap a b)) with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, ← map_mul, swap_mul_self, map_one, map_one]
  have hτW : τ ∉ V.map (MulAut.conj : S →* MulAut S) := by
    rintro ⟨v, -, hv⟩
    have h1 : a7Conj (swap a b) = MulAut.conj (e v) := by
      have := congrArg (MulAut.congr e) hv
      rw [hτ, MulEquiv.apply_symm_apply, congr_conj_eq] at this
      exact this.symm
    have h2 := mem_of_a7Conj_eq h1
    rw [Perm.mem_alternatingGroup, Perm.sign_swap hab] at h2
    exact absurd h2 (by decide)
  have hτc : ∀ w ∈ V.map (MulAut.conj : S →* MulAut S), τ * w = w * τ := by
    rintro _ ⟨v, hv, rfl⟩
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, hτ, MulEquiv.apply_symm_apply, congr_conj_eq]
    refine MulEquiv.ext fun g => Subtype.ext ?_
    simp only [MulAut.mul_apply, a7Conj_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have h1 := hsw (e v) ⟨v, hv, rfl⟩
    calc swap a b * ((e v : Perm (Fin 7)) * g * (e v : Perm (Fin 7))⁻¹) * (swap a b)⁻¹ =
        (swap a b * (e v : Perm (Fin 7))) * g * (swap a b * (e v : Perm (Fin 7)))⁻¹ := by
          group
      _ = ((e v : Perm (Fin 7)) * swap a b) * g * ((e v : Perm (Fin 7)) * swap a b)⁻¹ := by
          rw [← h1]
      _ = (e v : Perm (Fin 7)) * (swap a b * g * (swap a b)⁻¹) * (e v : Perm (Fin 7))⁻¹ := by
          group
  have hτmem : τ ∈ E ⊔ (MulAut.conj : S →* MulAut S).range := by
    have heven : swap a b * π⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, Perm.sign_swap hab]
      rw [Perm.mem_alternatingGroup] at hπodd
      rcases Int.units_eq_one_or (Perm.sign π) with h | h
      · exact absurd h hπodd
      · rw [h]; decide
    have hτeq : τ = MulAut.conj (e.symm ⟨_, heven⟩) * e₁ := by
      apply (MulAut.congr e).injective
      rw [hτ, MulEquiv.apply_symm_apply, map_mul, congr_conj_eq, MulEquiv.apply_symm_apply,
        ← a7Conj_of_mem heven, ← hπ, ← map_mul, inv_mul_cancel_right]
    rw [hτeq]
    exact mul_mem (mem_sup_right ⟨_, rfl⟩) (mem_sup_left he₁E)
  have hW4 : Nat.card (V.map (MulAut.conj : S →* MulAut S)) = 4 := by
    rw [Subgroup.card_map_of_injective hconj_inj]
    exact IsKleinFour.card_four
  have hW2 : ∀ w ∈ V.map (MulAut.conj : S →* MulAut S), w * w = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul]
    have := IsKleinFour.mul_self (⟨v, hv⟩ : V)
    rw [show v * v = 1 from congrArg Subtype.val this, map_one]
  obtain ⟨F₈, hWF, -, hF₈le, hF₈2, hF₈8⟩ := exists_e8_of_centralizing _ hW2 hW4 hτ2 hτW hτc
  refine ⟨F₈, hF₈le.trans (sup_le ?_ ?_), hF₈2, hF₈8, hWF⟩
  · exact (Subgroup.map_le_range _ _).trans le_sup_right
  · exact (zpowers_le).mpr hτmem

theorem footeFourgroupE8 :
    ∀ (S : Type) [Group S] [Finite S],
      (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
      ∀ E : Subgroup (MulAut S), (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
        (∀ P : Sylow 2 S, ∃ x ∈ (P : Subgroup S), ∃ y ∈ (P : Subgroup S), x * y ≠ y * x) ∧
        ∀ V : Subgroup S, IsKleinFour V →
          ∃ F : Subgroup (MulAut S), F ≤ E ⊔ (MulAut.conj : S →* MulAut S).range ∧
            (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8 ∧ V.map (MulAut.conj : S →* MulAut S) ≤ F := by
  intro S _ _ hS E hE2 hE8
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact fourgroupE8_alt7 e E hE2 hE8
  · exact fourgroupE8_psl2 hp hp2 hf hL E hE2 hE8

end CFSG.ComponentClassification.AutL2Facts
