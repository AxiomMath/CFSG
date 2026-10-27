module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

theorem hom_stabilizer_trivial {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h4 : 4 ≤ Fintype.card Ω)
    (ω₀ : Ω) {N : Type*} [CommGroup N] (hN : ∀ x : N, x ^ 2 = 1)
    (φ : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀) →* N) : φ = 1 := by
  clear h4
  have key : ∀ y : N, y ^ 3 = y := fun y => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hN, one_mul]
  have claim : ∀ τ ∈ Subgroup.closure {σ : Equiv.Perm {x : Ω // x ≠ ω₀} | σ.IsThreeCycle},
      ∃ h : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀),
        h.1.1 = Equiv.Perm.ofSubtype τ ∧ φ h = 1 := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem c hc =>
      have hc' : c.IsThreeCycle := hc
      have hsgn : Equiv.Perm.sign (Equiv.Perm.ofSubtype c) = 1 := by
        rw [Equiv.Perm.sign_ofSubtype]
        exact Equiv.Perm.mem_alternatingGroup.mp hc'.mem_alternatingGroup
      have hfix : Equiv.Perm.ofSubtype c ω₀ = ω₀ :=
        Equiv.Perm.ofSubtype_apply_of_not_mem c (fun h => h rfl)
      have hmem : Equiv.Perm.ofSubtype c ∈ alternatingGroup Ω :=
        Equiv.Perm.mem_alternatingGroup.mpr hsgn
      have hstab : (⟨Equiv.Perm.ofSubtype c, hmem⟩ : ↥(alternatingGroup Ω)) ∈
          MulAction.stabilizer (alternatingGroup Ω) ω₀ :=
        MulAction.mem_stabilizer_iff.mpr hfix
      obtain ⟨h, hh⟩ : ∃ h : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀),
          h.1.1 = Equiv.Perm.ofSubtype c :=
        ⟨⟨⟨Equiv.Perm.ofSubtype c, hmem⟩, hstab⟩, rfl⟩
      have hc3 : c ^ 3 = 1 := by
        rw [← hc'.orderOf]
        exact pow_orderOf_eq_one c
      have h3 : h ^ 3 = 1 := by
        refine Subtype.ext (Subtype.ext ?_)
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [hh, ← map_pow, hc3, map_one]
      have h1 : φ h ^ 3 = 1 := by rw [← map_pow, h3, map_one]
      rw [key] at h1
      exact ⟨h, hh, h1⟩
    | one => exact ⟨1, by simp, map_one φ⟩
    | mul x y _ _ hx hy =>
      obtain ⟨h₁, hh₁, hφ₁⟩ := hx
      obtain ⟨h₂, hh₂, hφ₂⟩ := hy
      refine ⟨h₁ * h₂, ?_, ?_⟩
      · simp only [Subgroup.coe_mul]
        rw [hh₁, hh₂, map_mul]
      · rw [map_mul, hφ₁, hφ₂, one_mul]
    | inv x _ hx =>
      obtain ⟨h₁, hh₁, hφ₁⟩ := hx
      refine ⟨h₁⁻¹, ?_, ?_⟩
      · simp only [Subgroup.coe_inv]
        rw [hh₁, map_inv]
      · rw [map_inv, hφ₁, inv_one]
  refine MonoidHom.ext fun h => ?_
  rw [MonoidHom.one_apply]
  have hsfix : h.1.1 ω₀ = ω₀ := MulAction.mem_stabilizer_iff.mp h.2
  have hsgn : Equiv.Perm.sign h.1.1 = 1 := Equiv.Perm.mem_alternatingGroup.mp h.1.2
  have hiff : ∀ x : Ω, h.1.1 x = ω₀ ↔ x = ω₀ := fun x =>
    ⟨fun hx => h.1.1.injective (hx.trans hsfix.symm), fun hx => by rw [hx, hsfix]⟩
  have hp : ∀ x : Ω, h.1.1 x ≠ ω₀ ↔ x ≠ ω₀ := fun x => not_congr (hiff x)
  have hmove : ∀ x : Ω, h.1.1 x ≠ x → x ≠ ω₀ := fun x hx hx0 => hx (by rw [hx0, hsfix])
  have hofs : Equiv.Perm.ofSubtype (h.1.1.subtypePerm hp) = h.1.1 :=
    Equiv.Perm.ofSubtype_subtypePerm hp hmove
  have hτA : h.1.1.subtypePerm hp ∈ alternatingGroup {x : Ω // x ≠ ω₀} := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hofs]
    exact hsgn
  have hτC : h.1.1.subtypePerm hp ∈
      Subgroup.closure {σ : Equiv.Perm {x : Ω // x ≠ ω₀} | σ.IsThreeCycle} := by
    rw [Equiv.Perm.closure_three_cycles_eq_alternating]
    exact hτA
  obtain ⟨h', hh', hφ'⟩ := claim _ hτC
  have hEq : h' = h := Subtype.ext (Subtype.ext (hh'.trans hofs))
  rw [← hEq]
  exact hφ'

theorem deleted_odd_equivariant_section {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hodd : Odd (Fintype.card Ω)) (h5 : 5 ≤ Fintype.card Ω)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) ↥(alternatingGroup Ω) E)
    (π : E →ₗ[ZMod 2] ↥(evenWeight Ω)) (hπs : Function.Surjective π)
    (hπ : ∀ (s : ↥(alternatingGroup Ω)) (e : E),
      π (ρ s e) = deletedRep (alternatingGroup Ω) Ω s (π e))
    (hfix : ∀ (s : ↥(alternatingGroup Ω)) (e : E), π e = 0 → ρ s e = e) :
    ∃ j : ↥(evenWeight Ω) →ₗ[ZMod 2] E, (∀ x, π (j x) = x) ∧
      ∀ (s : ↥(alternatingGroup Ω)) (x : ↥(evenWeight Ω)),
        j (deletedRep (alternatingGroup Ω) Ω s x) = ρ s (j x) := by
  obtain ⟨ω₀⟩ : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  have hpt : MulAction.IsPretransitive (alternatingGroup Ω) Ω :=
    alternatingGroup.isPretransitive_of_three_le_card Ω (by rw [Nat.card_eq_fintype_card]; omega)
  have hex : ∀ ω : Ω, ∃ g : ↥(alternatingGroup Ω), g • ω₀ = ω :=
    (MulAction.isPretransitive_iff_base ω₀).mp hpt
  choose g hg using hex
  have hcardodd : ((Fintype.card Ω : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hodd
  have hdel1 : ∀ ω : Ω, ∑ i : Ω, delta ω i = 1 := fun ω => by
    simp [delta, Pi.single_apply]
  have hcmem : ∀ ω : Ω, ((fun _ : Ω => (1 : ZMod 2)) + delta ω) ∈ evenWeight Ω := fun ω => by
    show ∑ i : Ω, ((fun _ : Ω => (1 : ZMod 2)) + delta ω) i = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hdel1, hcardodd]
    decide
  let cD : Ω → ↥(evenWeight Ω) := fun ω => ⟨(fun _ : Ω => (1 : ZMod 2)) + delta ω, hcmem ω⟩
  have hcD : ∀ (s : ↥(alternatingGroup Ω)) (ω : Ω),
      deletedRep (alternatingGroup Ω) Ω s (cD ω) = cD (s • ω) := by
    intro s ω
    apply Subtype.ext
    rw [deletedRep_apply]
    show permAct (MulAction.toPerm s) ((fun _ : Ω => (1 : ZMod 2)) + delta ω) =
      (fun _ : Ω => (1 : ZMod 2)) + delta (s • ω)
    rw [permAct_add, permAct_one, permAct_delta]
    rfl
  obtain ⟨e₀, he₀⟩ := hπs (cD ω₀)
  have hdiff : ∀ s : ↥(alternatingGroup Ω), π (ρ s e₀) = cD (s • ω₀) := by
    intro s
    rw [hπ, he₀, hcD]
  have hne2 : ∀ z : E, z + z = 0 := fun z => by
    rw [← two_smul (ZMod 2) z, zmod2_two, zero_smul]
  have hDD : ∀ x : ↥(evenWeight Ω), x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, zmod2_two, zero_smul]
  have hker : ∀ h : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀),
      π (ρ h.1 e₀ - e₀) = 0 := by
    intro h
    have hsub : ρ h.1 e₀ - e₀ = ρ h.1 e₀ + e₀ := by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (hne2 e₀)]
    rw [hsub, map_add, hdiff, he₀, MulAction.mem_stabilizer_iff.mp h.2]
    exact hDD _
  have hcoc : ∀ a b : ↥(alternatingGroup Ω), π (ρ b e₀ - e₀) = 0 →
      ρ (a * b) e₀ - e₀ = (ρ a e₀ - e₀) + (ρ b e₀ - e₀) := by
    intro a b hb
    have h1 : ρ a (ρ b e₀ - e₀) = ρ b e₀ - e₀ := hfix a _ hb
    rw [map_sub] at h1
    have h2 : ρ (a * b) e₀ = ρ a (ρ b e₀) := by
      rw [map_mul, Module.End.mul_apply]
    rw [h2]
    calc ρ a (ρ b e₀) - e₀ = (ρ a (ρ b e₀) - ρ a e₀) + (ρ a e₀ - e₀) := by abel
      _ = (ρ b e₀ - e₀) + (ρ a e₀ - e₀) := by rw [h1]
      _ = (ρ a e₀ - e₀) + (ρ b e₀ - e₀) := add_comm _ _
  have hN : ∀ x : Multiplicative E, x ^ 2 = 1 := fun x => by
    rw [← toAdd_eq_zero, toAdd_pow, two_nsmul, hne2]
  let φ : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀) →* Multiplicative E :=
    { toFun := fun h => Multiplicative.ofAdd (ρ h.1 e₀ - e₀)
      map_one' := by
        show Multiplicative.ofAdd (ρ (1 : ↥(alternatingGroup Ω)) e₀ - e₀) = 1
        rw [map_one, Module.End.one_apply, sub_self, ofAdd_zero]
      map_mul' := fun h h' => by
        show Multiplicative.ofAdd (ρ (h.1 * h'.1) e₀ - e₀) =
          Multiplicative.ofAdd (ρ h.1 e₀ - e₀) * Multiplicative.ofAdd (ρ h'.1 e₀ - e₀)
        rw [← ofAdd_add, hcoc h.1 h'.1 (hker h')] }
  have hφ : φ = 1 := hom_stabilizer_trivial (show 4 ≤ Fintype.card Ω by omega) ω₀ hN φ
  have hstab : ∀ h : ↥(MulAction.stabilizer (alternatingGroup Ω) ω₀), ρ h.1 e₀ = e₀ := by
    intro h
    have h1 : φ h = 1 := by rw [hφ, MonoidHom.one_apply]
    have h2 : Multiplicative.ofAdd (ρ h.1 e₀ - e₀) = 1 := h1
    exact sub_eq_zero.mp (ofAdd_eq_one.mp h2)
  have hρ_eq : ∀ a b : ↥(alternatingGroup Ω), a • ω₀ = b • ω₀ → ρ a e₀ = ρ b e₀ := by
    intro a b hab
    have hk : b⁻¹ * a ∈ MulAction.stabilizer (alternatingGroup Ω) ω₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]
    have h1 : ρ (b⁻¹ * a) e₀ = e₀ := hstab ⟨b⁻¹ * a, hk⟩
    calc ρ a e₀ = ρ (b * (b⁻¹ * a)) e₀ := by rw [mul_inv_cancel_left]
      _ = ρ b (ρ (b⁻¹ * a) e₀) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ b e₀ := by rw [h1]
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : Ω → E, ∀ ω, ℓ ω = ρ (g ω) e₀ :=
    ⟨fun ω => ρ (g ω) e₀, fun ω => rfl⟩
  have hℓπ : ∀ ω, π (ℓ ω) = cD ω := fun ω => by
    rw [hℓdef, hdiff, hg ω]
  have hℓS : ∀ (s : ↥(alternatingGroup Ω)) (ω : Ω), ρ s (ℓ ω) = ℓ (s • ω) := by
    intro s ω
    rw [hℓdef, hℓdef, ← Module.End.mul_apply, ← map_mul]
    apply hρ_eq
    rw [mul_smul, hg ω, hg (s • ω)]
  obtain ⟨σ, hσ_apply⟩ : ∃ σ : ↥(evenWeight Ω) →ₗ[ZMod 2] E,
      ∀ v : ↥(evenWeight Ω), σ v = ∑ ω : Ω, (v : Ω → ZMod 2) ω • ℓ ω :=
    ⟨∑ ω : Ω, (LinearMap.proj ω ∘ₗ (evenWeight Ω).subtype).smulRight (ℓ ω),
      fun v => by simp [LinearMap.sum_apply]⟩
  have hsumdelta : ∀ v : Ω → ZMod 2, ∑ ω : Ω, v ω • delta ω = v := by
    intro v
    funext i
    simp [delta, Pi.single_apply, Finset.sum_apply]
  have hσπ : ∀ v : ↥(evenWeight Ω), π (σ v) = v := by
    intro v
    have hv : ∑ ω : Ω, (v : Ω → ZMod 2) ω = 0 := v.2
    have key : ∑ ω : Ω, (v : Ω → ZMod 2) ω • ((fun _ : Ω => (1 : ZMod 2)) + delta ω) =
        (v : Ω → ZMod 2) := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hv, zero_smul, zero_add]
      exact hsumdelta _
    rw [hσ_apply, map_sum]
    simp only [map_smul, hℓπ]
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact key
  have hσeq : ∀ (s : ↥(alternatingGroup Ω)) (x : ↥(evenWeight Ω)),
      σ (deletedRep (alternatingGroup Ω) Ω s x) = ρ s (σ x) := by
    intro s x
    rw [hσ_apply, hσ_apply, map_sum]
    simp only [map_smul, hℓS]
    refine (Equiv.sum_comp (MulAction.toPerm s) _).symm.trans ?_
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hperm : permAct (MulAction.toPerm s) (x : Ω → ZMod 2) (MulAction.toPerm s ω) =
        (x : Ω → ZMod 2) ω := by
      show (x : Ω → ZMod 2) ((MulAction.toPerm s).symm (MulAction.toPerm s ω)) = _
      rw [Equiv.symm_apply_apply]
    show ((deletedRep (alternatingGroup Ω) Ω s x : ↥(evenWeight Ω)) : Ω → ZMod 2)
        (MulAction.toPerm s ω) • ℓ (MulAction.toPerm s ω) = (x : Ω → ZMod 2) ω • ℓ (s • ω)
    rw [deletedRep_apply, hperm]
    rfl
  exact ⟨σ, hσπ, hσeq⟩

theorem deleted_odd_quotient_kernel_trivial {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hodd : Odd (Fintype.card Ω)) (h5 : 5 ≤ Fintype.card Ω)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) ↥(alternatingGroup Ω) E)
    (π : E →ₗ[ZMod 2] ↥(evenWeight Ω)) (hπs : Function.Surjective π)
    (hπ : ∀ (s : ↥(alternatingGroup Ω)) (e : E),
      π (ρ s e) = deletedRep (alternatingGroup Ω) Ω s (π e))
    (hfix : ∀ (s : ↥(alternatingGroup Ω)) (e : E), π e = 0 → ρ s e = e)
    (hgen : Submodule.span (ZMod 2)
      (Set.range fun p : ↥(alternatingGroup Ω) × E => ρ p.1 p.2 - p.2) = ⊤) :
    LinearMap.ker π = ⊥ ∧ Function.Bijective π := by
  obtain ⟨j, hj1, hj2⟩ := deleted_odd_equivariant_section hodd h5 ρ π hπs hπ hfix
  have hne2 : ∀ z : E, z + z = 0 := fun z => by
    rw [← two_smul (ZMod 2) z, zmod2_two, zero_smul]
  have hDD : ∀ x : ↥(evenWeight Ω), x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, zmod2_two, zero_smul]
  have hgenj : ∀ p : ↥(alternatingGroup Ω) × E, ρ p.1 p.2 - p.2 ∈ LinearMap.range j := by
    rintro ⟨s, e⟩
    refine ⟨deletedRep (alternatingGroup Ω) Ω s (π e) + π e, ?_⟩
    have hk : π (e + j (π e)) = 0 := by rw [map_add, hj1, hDD]
    have h1 := hfix s _ hk
    have hek : e = (e + j (π e)) + j (π e) := by rw [add_assoc, hne2, add_zero]
    show j (deletedRep (alternatingGroup Ω) Ω s (π e) + π e) = ρ s e - e
    rw [map_add, hj2]
    have h3 : ρ s e = (e + j (π e)) + ρ s (j (π e)) := by
      conv_lhs => rw [hek]
      rw [map_add, h1]
    rw [h3]
    abel
  have hrange : LinearMap.range j = ⊤ := by
    rw [eq_top_iff, ← hgen, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hgenj p
  have hall : ∀ e : E, ∃ x, j x = e := fun e => by
    have h1 : e ∈ LinearMap.range j := by
      rw [hrange]
      trivial
    exact h1
  refine ⟨?_, ?_, hπs⟩
  · rw [Submodule.eq_bot_iff]
    intro e he
    obtain ⟨x, rfl⟩ := hall e
    have h1 : π (j x) = 0 := he
    rw [hj1] at h1
    rw [h1, map_zero]
  · intro e e' hee
    obtain ⟨x, rfl⟩ := hall e
    obtain ⟨x', rfl⟩ := hall e'
    rw [hj1, hj1] at hee
    rw [hee]

end CFSG.QuasithinUnique.Setup.SL2Modules
