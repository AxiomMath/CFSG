module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3ExtExcludes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof

open CFSG.QuasithinUnique.Setup.Family CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

theorem ext_eq_of_eq_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b : M} (x : M)
    (h : a = b + (x + x)) : a = b := by
  rw [h, add_self_eq_zero_of_zmod_two x, add_zero]

theorem ext_eq_add_of_add_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b m : M}
    (h : a + b = m) : a = b + m := by
  subst h
  exact (ext_eq_of_eq_add_self b (by abel)).symm

theorem ext_nsmul_odd {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (n : ℕ) (hn : Odd n)
    (x : M) : n • x = x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hn.natCast_zmod_two, one_smul]

theorem ext_perfect_hom_eq_one {G M : Type*} [Group G] [Group.IsPerfect G] [CommMonoid M]
    (f : G →* M) (g : G) : f g = 1 := by
  have h := Abelianization.commutator_subset_ker f.toHomUnits
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hg : f.toHomUnits g = 1 := h (Subgroup.mem_top g)
  rw [← MonoidHom.coe_toHomUnits, hg, Units.val_one]

theorem ext_cocycle_one (c : GL32 → Mat3) (hc : ∀ g h, c (g * h) = c g + conjRep g (c h)) :
    c 1 = 0 := by
  have h := hc 1 1
  rw [one_mul, map_one] at h
  simpa using h

theorem ext_cocycle_trace_zero (c : GL32 → Mat3)
    (hc : ∀ g h, c (g * h) = c g + conjRep g (c h)) (g : GL32) : (c g).trace = 0 := by
  haveI : Group.IsPerfect GL32 := GL32_isPerfect
  have h1 : c 1 = 0 := ext_cocycle_one c hc
  let f : GL32 →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (c g).trace
      map_one' := by rw [h1]; simp
      map_mul' := fun g h => by
        rw [hc g h, Matrix.trace_add, conjRep_apply, trace_conj]
        rfl }
  have := ext_perfect_hom_eq_one f g
  exact ofAdd_eq_one.1 this

theorem ext_regular_coboundary {S : Type*} [Group S] (γ : S → S → ZMod 2)
    (hγ : ∀ s t x, γ (s * t) x = γ s x + γ t (s⁻¹ * x)) (s x : S) :
    γ s x = γ (s⁻¹ * x) (s⁻¹ * x) + γ x x := by
  have h := hγ s (s⁻¹ * x) x
  rw [mul_inv_cancel_left] at h
  exact (by decide : ∀ a b c : ZMod 2, a = b + c → b = c + a) _ _ _ h

theorem ext_sylow_coboundary (c : sylowT → Mat3) (hcA : ∀ s, c s ∈ traceZero)
    (hc : ∀ s t, c (s * t) = c s + conjRep (s : GL32) (c t)) :
    ∃ m : Mat3, ∀ s, c s = conjRep (s : GL32) m + m := by
  obtain ⟨-, -, hbij, hequiv⟩ := trace_zero_regular_Sylow_module
  set Φ := Fintype.linearCombination (ZMod 2) conjFamily
  choose γ hγ using fun s => hbij.2 ⟨c s, hcA s⟩
  have hγ' : ∀ s, ((Φ (γ s) : traceZero) : Mat3) = c s := fun s => congrArg Subtype.val (hγ s)
  have hcoc : ∀ s t x, γ (s * t) x = γ s x + γ t (s⁻¹ * x) := by
    intro s t x
    have h : γ (s * t) = γ s + fun y => γ t (s⁻¹ * y) := by
      apply hbij.1
      apply Subtype.ext
      rw [hγ', map_add, Submodule.coe_add, hγ', hequiv, hγ', hc, conjRep_apply]
    exact congrFun h x
  refine ⟨((Φ fun y => γ y y : traceZero) : Mat3), fun s => ?_⟩
  have h1 : γ s = (fun x => (fun y => γ y y) (s⁻¹ * x)) + fun y => γ y y := by
    funext x
    exact ext_regular_coboundary γ hcoc s x
  have h2 := congrArg (fun f => ((Φ f : traceZero) : Mat3)) h1
  simp only [map_add, Submodule.coe_add, hγ'] at h2
  have h3 := hequiv s (fun y => γ y y)
  rw [h2, h3, conjRep_apply]

theorem ext_index_sylowT : sylowT.index = 21 := by
  have h := Subgroup.card_mul_index sylowT
  rw [card_sylowT, Nat.card_eq_fintype_card (α := GL32)] at h
  have hc : Fintype.card GL32 = 168 := by
    rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
    simp [Fin.prod_univ_three, ZMod.card]
  rw [hc] at h
  omega

theorem ext_odd_index (c : GL32 → Mat3) (hc : ∀ g h, c (g * h) = c g + conjRep g (c h))
    (hS : ∀ s : GL32, s ∈ sylowT → c s = 0) : ∃ m : Mat3, ∀ x, c x = conjRep x m + m := by
  classical
  have hconst : ∀ (g s : GL32), s ∈ sylowT → c (g * s) = c g := by
    intro g s hs
    rw [hc, hS s hs, map_zero, add_zero]
  letI : Fintype (GL32 ⧸ sylowT) := Fintype.ofFinite _
  have hcard : Fintype.card (GL32 ⧸ sylowT) = 21 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, ext_index_sylowT]
  let C : GL32 ⧸ sylowT → Mat3 := fun q => c q.out
  have hC : ∀ g : GL32, C (QuotientGroup.mk g) = c g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul sylowT g
    exact (congrArg c hh).trans (hconst g h h.2)
  refine ⟨∑ q, C q, fun x => ?_⟩
  have hsum : ∑ q : GL32 ⧸ sylowT, C (x • q) = ∑ q, C q :=
    Equiv.sum_comp (MulAction.toPerm x) C
  have hstep : ∀ q : GL32 ⧸ sylowT, C (x • q) = c x + conjRep x (C q) := by
    intro q
    rw [← MulAction.Quotient.mk_smul_out, hC, smul_eq_mul, hc]
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
    ← map_sum] at hsum
  rw [ext_nsmul_odd (M := Mat3) 21 ⟨10, rfl⟩ (c x)] at hsum
  exact ext_eq_add_of_add_eq hsum

theorem ext_cocycle_coboundary (c : GL32 → Mat3)
    (hc : ∀ g h, c (g * h) = c g + conjRep g (c h)) :
    ∃ T : Mat3, ∀ g, c g = conjRep g T + T := by
  obtain ⟨m, hm⟩ := ext_sylow_coboundary (fun s => c s)
    (fun s => mem_traceZero_iff_trace.2 (ext_cocycle_trace_zero c hc s)) (fun s t => hc s t)
  have hc' : ∀ g h, c (g * h) + conjRep (g * h) m + m =
      (c g + conjRep g m + m) + conjRep g (c h + conjRep h m + m) := by
    intro g h
    refine (ext_eq_of_eq_add_self (conjRep g m) ?_).symm
    rw [hc g h, map_mul conjRep g h, LinearEquiv.mul_apply, map_add, map_add]
    abel
  have hS : ∀ s : GL32, s ∈ sylowT → c s + conjRep s m + m = 0 := by
    intro s hs
    have h : c s = conjRep s m + m := hm ⟨s, hs⟩
    rw [h]
    calc conjRep s m + m + conjRep s m + m = (conjRep s m + conjRep s m) + (m + m) := by abel
      _ = 0 := by rw [add_self_eq_zero_of_zmod_two, add_self_eq_zero_of_zmod_two, add_zero]
  obtain ⟨m', hm'⟩ := ext_odd_index (fun g => c g + conjRep g m + m) hc' hS
  refine ⟨m + m', fun g => ?_⟩
  have h3 : c g + conjRep g m + m = conjRep g m' + m' := hm' g
  rw [map_add]
  calc c g = c g + (conjRep g m + conjRep g m) + (m + m) := by
        rw [add_self_eq_zero_of_zmod_two, add_self_eq_zero_of_zmod_two, add_zero, add_zero]
    _ = (c g + conjRep g m + m) + conjRep g m + m := by abel
    _ = (conjRep g m' + m') + conjRep g m + m := by rw [h3]
    _ = conjRep g m + conjRep g m' + (m + m') := by abel

theorem ext_rep_mul {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : G →* Module.End (ZMod 2) E) (g h : G) (x : E) : ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul, Module.End.mul_apply]

theorem ext_repV_mul_inv (g : GL32) (v : Vec3) : repV g (repV g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem ext_repV_inv_mul (g : GL32) (v : Vec3) : repV g⁻¹ (repV g v) = v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem ext_repV_mul (g h : GL32) (v : Vec3) : repV (g * h) v = repV g (repV h v) := by
  rw [map_mul]
  rfl

theorem ext_conjRep_mulVec (g : GL32) (X : Mat3) (v : Vec3) :
    conjRep g X *ᵥ v = repV g (X *ᵥ repV g⁻¹ v) := by
  rw [conjRep_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rfl

theorem ext_exists_linear_section {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (π : E →ₗ[ZMod 2] Vec3) (hπ : Function.Surjective π) :
    ∃ s₀ : Vec3 →ₗ[ZMod 2] E, ∀ v, π (s₀ v) = v := by
  obtain ⟨s₀, hs₀⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.2 hπ)
  exact ⟨s₀, fun v => LinearMap.congr_fun hs₀ v⟩

theorem ext_exists_mat_of_range {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ι : Vec3 →ₗ[ZMod 2] E) (hι : Function.Injective ι) (f : Vec3 →ₗ[ZMod 2] E)
    (hf : ∀ v, f v ∈ LinearMap.range ι) : ∃ X : Mat3, ∀ v, ι (X *ᵥ v) = f v := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  refine ⟨LinearMap.toMatrix' (r ∘ₗ f), fun v => ?_⟩
  obtain ⟨w, hw⟩ := hf v
  have hrw : r (ι w) = w := LinearMap.congr_fun hr w
  rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, ← hw, hrw]

theorem ext_exists_cocycle_data {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : GL32 →* Module.End (ZMod 2) E) (ι : Vec3 →ₗ[ZMod 2] E) (hι : Function.Injective ι)
    (π : E →ₗ[ZMod 2] Vec3) (hπρ : ∀ g x, π (ρ g x) = repV g (π x))
    (hex : LinearMap.ker π = LinearMap.range ι) (s₀ : Vec3 →ₗ[ZMod 2] E)
    (hs₀ : ∀ v, π (s₀ v) = v) :
    ∃ D : GL32 → Mat3, ∀ g v, ι (D g *ᵥ v) = ρ g (s₀ (repV g⁻¹ v)) - s₀ v := by
  have h : ∀ g : GL32, ∃ X : Mat3, ∀ v, ι (X *ᵥ v) = ρ g (s₀ (repV g⁻¹ v)) - s₀ v := by
    intro g
    refine ext_exists_mat_of_range ι hι (ρ g ∘ₗ s₀ ∘ₗ (repV g⁻¹).toLinearMap - s₀) (fun v => ?_)
    rw [← hex, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub, hπρ, hs₀,
      ext_repV_mul_inv, sub_self]
  choose D hD using h
  exact ⟨D, hD⟩

theorem ext_cocycle_of_data {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : GL32 →* Module.End (ZMod 2) E) (ι : Vec3 →ₗ[ZMod 2] E) (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (repV g v) = ρ g (ι v)) (s₀ : Vec3 →ₗ[ZMod 2] E) (D : GL32 → Mat3)
    (hD : ∀ g v, ι (D g *ᵥ v) = ρ g (s₀ (repV g⁻¹ v)) - s₀ v) (g h : GL32) :
    D (g * h) = D g + conjRep g (D h) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  apply hι
  rw [Matrix.add_mulVec, ext_conjRep_mulVec, map_add, hιρ, hD, hD, hD, map_sub,
    _root_.mul_inv_rev, ext_repV_mul, ext_rep_mul]
  abel

theorem ext_section_of_coboundary {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : GL32 →* Module.End (ZMod 2) E) (ι : Vec3 →ₗ[ZMod 2] E)
    (hιρ : ∀ g v, ι (repV g v) = ρ g (ι v)) (π : E →ₗ[ZMod 2] Vec3)
    (hex : LinearMap.ker π = LinearMap.range ι) (s₀ : Vec3 →ₗ[ZMod 2] E)
    (hs₀ : ∀ v, π (s₀ v) = v) (D : GL32 → Mat3)
    (hD : ∀ g v, ι (D g *ᵥ v) = ρ g (s₀ (repV g⁻¹ v)) - s₀ v) (T : Mat3)
    (hT : ∀ g, D g = conjRep g T + T) :
    ∃ s : Vec3 →ₗ[ZMod 2] E, (∀ v, π (s v) = v) ∧ ∀ g v, s (repV g v) = ρ g (s v) := by
  have hπι : ∀ w, π (ι w) = 0 := by
    intro w
    have : ι w ∈ LinearMap.ker π := by
      rw [hex]
      exact LinearMap.mem_range_self ι w
    exact LinearMap.mem_ker.1 this
  refine ⟨s₀ + ι ∘ₗ Matrix.toLin' T, fun v => ?_, fun g v => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hs₀, hπι, add_zero]
  · have h1 := hD g (repV g v)
    rw [ext_repV_inv_mul, hT g, Matrix.add_mulVec, ext_conjRep_mulVec, ext_repV_inv_mul,
      map_add] at h1
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Matrix.toLin'_apply, map_add]
    rw [← hιρ g (T *ᵥ v)]
    have h2 : ρ g (s₀ v) = (ι (repV g (T *ᵥ v)) + ι (T *ᵥ repV g v)) + s₀ (repV g v) := by
      rw [h1]
      abel
    rw [h2]
    exact (ext_eq_of_eq_add_self (ι (repV g (T *ᵥ v))) (by abel)).symm

theorem exists_equivariant_section {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (ρ : GL32 →* Module.End (ZMod 2) E)
    (ι : Vec3 →ₗ[ZMod 2] E) (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (repV g v) = ρ g (ι v))
    (π : E →ₗ[ZMod 2] Vec3) (hπ : Function.Surjective π)
    (hπρ : ∀ g x, π (ρ g x) = repV g (π x))
    (hex : LinearMap.ker π = LinearMap.range ι) :
    ∃ s : Vec3 →ₗ[ZMod 2] E, (∀ v, π (s v) = v) ∧ ∀ g v, s (repV g v) = ρ g (s v) := by
  obtain ⟨s₀, hs₀⟩ := ext_exists_linear_section π hπ
  obtain ⟨D, hD⟩ := ext_exists_cocycle_data ρ ι hι π hπρ hex s₀ hs₀
  obtain ⟨T, hT⟩ := ext_cocycle_coboundary D (ext_cocycle_of_data ρ ι hι hιρ s₀ D hD)
  exact ext_section_of_coboundary ρ ι hιρ π hex s₀ hs₀ D hD T hT

theorem ext_repDual_tauHom (g : GL32) : repDual (tauHom g) = repV g := by
  change repV (tauHom (tauHom g)) = repV g
  rw [tauHom_tauHom]

theorem exists_equivariant_section_dual {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (ρ : GL32 →* Module.End (ZMod 2) E)
    (ι : Vec3 →ₗ[ZMod 2] E) (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (repDual g v) = ρ g (ι v))
    (π : E →ₗ[ZMod 2] Vec3) (hπ : Function.Surjective π)
    (hπρ : ∀ g x, π (ρ g x) = repDual g (π x))
    (hex : LinearMap.ker π = LinearMap.range ι) :
    ∃ s : Vec3 →ₗ[ZMod 2] E, (∀ v, π (s v) = v) ∧ ∀ g v, s (repDual g v) = ρ g (s v) := by
  obtain ⟨s, hs, hsρ⟩ := exists_equivariant_section (ρ.comp tauHom) ι hι
    (fun g v => by
      have h := hιρ (tauHom g) v
      rwa [ext_repDual_tauHom] at h)
    π hπ
    (fun g x => by
      have h := hπρ (tauHom g) x
      rwa [ext_repDual_tauHom] at h)
    hex
  refine ⟨s, hs, fun g v => ?_⟩
  have h := hsρ (tauHom g) v
  rw [MonoidHom.comp_apply, tauHom_tauHom] at h
  exact h

end CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof
