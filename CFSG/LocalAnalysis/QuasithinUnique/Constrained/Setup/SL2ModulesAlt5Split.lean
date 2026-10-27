module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section Averaging

variable {G : Type*} [Group G] [Finite G] {M E : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
  [AddCommMonoid E] [Module (ZMod 2) E]

theorem odd_nsmul_eq {n : ℕ} (hn : Odd n) (m : M) : n • m = m := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) n m]
  have : (n : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hn
  rw [this, one_smul]

theorem equivariant_section_of_odd_index (ρM : Representation (ZMod 2) G M)
    (ρE : Representation (ZMod 2) G E) (π : E →ₗ[ZMod 2] M)
    (hπ : ∀ g e, π (ρE g e) = ρM g (π e)) (T : Subgroup G) (hodd : Odd T.index)
    (σ : M →ₗ[ZMod 2] E) (hσ : ∀ m, π (σ m) = m)
    (hσT : ∀ t ∈ T, ∀ m, σ (ρM t m) = ρE t (σ m)) :
    ∃ j : M →ₗ[ZMod 2] E, (∀ m, π (j m) = m) ∧ ∀ g m, j (ρM g m) = ρE g (j m) := by
  classical
  have : Fintype (G ⧸ T) := Fintype.ofFinite _
  let term : G → M →ₗ[ZMod 2] E := fun g => (ρE g).comp (σ.comp (ρM g⁻¹))
  have hterm_apply : ∀ g m, term g m = ρE g (σ (ρM g⁻¹ m)) := fun g m => rfl
  have hρE_inv : ∀ (g : G) (y : E), ρE g (ρE g⁻¹ y) = y := by
    intro g y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hρM_inv : ∀ (g : G) (y : M), ρM g (ρM g⁻¹ y) = y := by
    intro g y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hterm : ∀ g, ∀ t ∈ T, ∀ m, term (g * t) m = term g m := by
    intro g t ht m
    rw [hterm_apply, hterm_apply, mul_inv_rev, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, hσT t⁻¹ (T.inv_mem ht), hρE_inv]
  have hrep : ∀ (g : G) (q : G ⧸ T), ∃ t ∈ T, g * q.out = (g • q).out * t := by
    intro g q
    have h1 : (↑((g • q).out) : G ⧸ T) = ↑(g * q.out) := by
      calc (↑((g • q).out) : G ⧸ T) = g • q := QuotientGroup.out_eq' _
        _ = g • (↑q.out : G ⧸ T) := by rw [QuotientGroup.out_eq']
        _ = ↑(g * q.out) := MulAction.Quotient.smul_mk T g q.out
    refine ⟨((g • q).out)⁻¹ * (g * q.out), QuotientGroup.eq.mp h1, ?_⟩
    group
  have hshift : ∀ (g : G) (q : G ⧸ T) (m : M), term (g * q.out) m = term (g • q).out m := by
    intro g q m
    obtain ⟨t, ht, e⟩ := hrep g q
    rw [e, hterm _ t ht]
  let j : M →ₗ[ZMod 2] E := ∑ q : G ⧸ T, term q.out
  have hj_apply : ∀ m, j m = ∑ q : G ⧸ T, term q.out m := by
    intro m
    simp [j, LinearMap.sum_apply]
  refine ⟨j, ?_, ?_⟩
  · intro m
    rw [hj_apply, map_sum]
    have h1 : ∀ q : G ⧸ T, π (term q.out m) = m := by
      intro q
      rw [hterm_apply, hπ, hσ, hρM_inv]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    have hc : Nat.card (G ⧸ T) = T.index := rfl
    rw [hc]
    exact odd_nsmul_eq hodd m
  · intro g m
    rw [hj_apply, hj_apply, map_sum]
    have h1 : ∀ q : G ⧸ T, term (g • q).out (ρM g m) = ρE g (term q.out m) := by
      intro q
      obtain ⟨t, ht, e⟩ := hrep g q
      have e' : (g • q).out = g * q.out * t⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact e.symm
      rw [e', hterm_apply, hterm_apply]
      have e2 : (g * q.out * t⁻¹)⁻¹ * g = t * q.out⁻¹ := by group
      have hh : ρM (g * q.out * t⁻¹)⁻¹ (ρM g m) = ρM t (ρM q.out⁻¹ m) := by
        calc ρM (g * q.out * t⁻¹)⁻¹ (ρM g m) = ρM ((g * q.out * t⁻¹)⁻¹ * g) m := by
              rw [map_mul, Module.End.mul_apply]
          _ = ρM (t * q.out⁻¹) m := by rw [e2]
          _ = ρM t (ρM q.out⁻¹ m) := by rw [map_mul, Module.End.mul_apply]
      rw [hh, hσT t ht]
      have e3 : g * q.out * t⁻¹ * t = g * q.out := by group
      calc ρE (g * q.out * t⁻¹) (ρE t (σ (ρM q.out⁻¹ m)))
          = ρE (g * q.out * t⁻¹ * t) (σ (ρM q.out⁻¹ m)) := by
            rw [← Module.End.mul_apply, ← map_mul]
        _ = ρE (g * q.out) (σ (ρM q.out⁻¹ m)) := by rw [e3]
        _ = ρE g (ρE q.out (σ (ρM q.out⁻¹ m))) := by rw [map_mul, Module.End.mul_apply]
    calc ∑ q : G ⧸ T, term q.out (ρM g m)
        = ∑ q : G ⧸ T, term (g • q).out (ρM g m) :=
          (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ T => term q.out (ρM g m))).symm
      _ = ∑ q : G ⧸ T, ρE g (term q.out m) := Finset.sum_congr rfl (fun q _ => h1 q)

end Averaging

section Stabilizers

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem natCard_stabilizer_pair (h5 : Fintype.card Ω = 5) {a b : Ω} (hab : a ≠ b) :
    Nat.card (MulAction.stabilizer (alternatingGroup Ω) (a, b)) = 3 := by
  classical
  have horb : MulAction.orbit (alternatingGroup Ω) (a, b) = {p : Ω × Ω | p.1 ≠ p.2} := by
    ext ⟨c, d⟩
    constructor
    · rintro ⟨g, hg⟩
      have h1 : (g : Equiv.Perm Ω) a = c := congrArg Prod.fst hg
      have h2 : (g : Equiv.Perm Ω) b = d := congrArg Prod.snd hg
      show c ≠ d
      rw [← h1, ← h2]
      exact fun h => hab ((g : Equiv.Perm Ω).injective h)
    · intro hcd
      obtain ⟨σ, hσ, h1, h2⟩ := alt_two_transitive h5 hab (show c ≠ d from hcd)
      exact ⟨⟨σ, hσ⟩, Prod.ext h1 h2⟩
  have hcard : Nat.card {p : Ω × Ω | p.1 ≠ p.2} = 20 := by
    have : Fintype.card {p : Ω × Ω // p.1 ≠ p.2} = 20 := by
      rw [Fintype.card_subtype]
      have h2 : Finset.univ.filter (fun p : Ω × Ω => p.1 ≠ p.2) =
          (Finset.univ : Finset Ω).offDiag := by
        ext p
        simp [Finset.mem_offDiag]
      rw [h2, Finset.offDiag_card, Finset.card_univ, h5]
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (alternatingGroup Ω) (a, b)
  simp only [← Nat.card_eq_fintype_card] at h
  have : Nontrivial Ω := ⟨⟨a, b, hab⟩⟩
  rw [horb, hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Ω), h5] at h
  have h120 : Nat.factorial 5 = 120 := by decide
  rw [h120] at h
  omega

@[expose] def bvecAt (o x : Ω) : ↥(evenWeight Ω) := ⟨delta o + delta x, delta_add_delta_mem o x⟩

theorem deletedRep_bvecAt {G : Type*} [Group G] [MulAction G Ω] (g : G) (o x : Ω) :
    deletedRep G Ω g (bvecAt o x) = bvecAt (g • o) (g • x) := by
  apply Subtype.ext
  rw [deletedRep_apply]
  show permAct (MulAction.toPerm g) (delta o + delta x) = delta (g • o) + delta (g • x)
  rw [permAct_add, permAct_delta, permAct_delta]
  rfl

theorem sum_bvecAt (o : Ω) (v : ↥(evenWeight Ω)) :
    ∑ x : {x : Ω // x ≠ o}, (v : Ω → ZMod 2) x.1 • bvecAt o x.1 = v := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bvecAt]
  conv_rhs => rw [eq_sum_pairs o v.2]
  rw [Finset.sum_subtype (Finset.univ.erase o) (p := fun x => x ≠ o)
    (fun x => by simp [Finset.mem_erase]) (fun L => (v : Ω → ZMod 2) L • (delta L + delta o))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [add_comm (delta o) (delta x)]

end Stabilizers

section Main

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem deleted_five_quotient_equivariant_section (h5 : Fintype.card Ω = 5)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) ↥(alternatingGroup Ω) E)
    (π : E →ₗ[ZMod 2] ↥(evenWeight Ω)) (hπs : Function.Surjective π)
    (hπ : ∀ (s : ↥(alternatingGroup Ω)) (e : E),
      π (ρ s e) = deletedRep (alternatingGroup Ω) Ω s (π e)) :
    ∃ j : ↥(evenWeight Ω) →ₗ[ZMod 2] E, (∀ x, π (j x) = x) ∧
      ∀ (s : ↥(alternatingGroup Ω)) (x : ↥(evenWeight Ω)),
        j (deletedRep (alternatingGroup Ω) Ω s x) = ρ s (j x) := by
  classical
  obtain ⟨ω₀⟩ : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁ : Ω, ω₁ ≠ ω₀ := by
    by_contra hcon
    push Not at hcon
    have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by rw [hcon x, hcon y])
    omega
  have : MulAction.IsPretransitive (alternatingGroup Ω) Ω := ⟨fun a b => by
    obtain ⟨σ, hσ, h⟩ := alt_transitive h5 a b
    exact ⟨⟨σ, hσ⟩, h⟩⟩
  let ρM := deletedRep (alternatingGroup Ω) Ω
  let H := MulAction.stabilizer (alternatingGroup Ω) ω₀
  have hHodd : Odd H.index := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, h5]
    decide
  let C := MulAction.stabilizer (alternatingGroup Ω) (ω₀, ω₁)
  have hCodd : Odd (Nat.card C) := by
    rw [natCard_stabilizer_pair h5 hω₁.symm]
    decide
  have hC : ∀ c : alternatingGroup Ω, c ∈ C ↔ c • ω₀ = ω₀ ∧ c • ω₁ = ω₁ := by
    intro c
    rw [MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
  obtain ⟨e, he⟩ := hπs (bvecAt ω₀ ω₁)
  have : Fintype ↥C := Fintype.ofFinite _
  let e' : E := ∑ c : ↥C, ρ c.1 e
  have he'fix : ∀ c ∈ C, ρ c e' = e' := by
    intro c hc
    let c₀ : ↥C := ⟨c, hc⟩
    have h1 : ρ c e' = ∑ c' : ↥C, ρ (c₀ * c').1 e := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [h1]
    exact Equiv.sum_comp (Equiv.mulLeft c₀) (fun c' : ↥C => ρ c'.1 e)
  have hπe' : π e' = bvecAt ω₀ ω₁ := by
    rw [map_sum]
    have h1 : ∀ c : ↥C, π (ρ c.1 e) = bvecAt ω₀ ω₁ := by
      intro c
      rw [hπ, he, deletedRep_bvecAt]
      obtain ⟨h0, h1⟩ := (hC c.1).mp c.2
      rw [h0, h1]
    rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact odd_nsmul_eq hCodd _
  have hg : ∀ x : {x : Ω // x ≠ ω₀}, ∃ g : ↥(alternatingGroup Ω), g • ω₀ = ω₀ ∧ g • ω₁ = x.1 := by
    intro x
    obtain ⟨σ, hσ, h1, h2⟩ := alt_two_transitive h5 (a := ω₀) (b := ω₁) (c := ω₀) (d := x.1)
      hω₁.symm x.2.symm
    exact ⟨⟨σ, hσ⟩, h1, h2⟩
  choose g hg0 hg1 using hg
  let s : {x : Ω // x ≠ ω₀} → E := fun x => ρ (g x) e'
  have hπs' : ∀ x : {x : Ω // x ≠ ω₀}, π (s x) = bvecAt ω₀ x.1 := by
    intro x
    show π (ρ (g x) e') = _
    rw [hπ, hπe', deletedRep_bvecAt, hg0 x, hg1 x]
  let σ : ↥(evenWeight Ω) →ₗ[ZMod 2] E :=
    ∑ x : {x : Ω // x ≠ ω₀}, (LinearMap.proj x.1 ∘ₗ (evenWeight Ω).subtype).smulRight (s x)
  have hσ_apply : ∀ v, σ v = ∑ x : {x : Ω // x ≠ ω₀}, (v : Ω → ZMod 2) x.1 • s x := by
    intro v
    simp [σ, LinearMap.sum_apply]
  have hσ : ∀ v, π (σ v) = v := by
    intro v
    rw [hσ_apply, map_sum]
    simp only [map_smul, hπs']
    exact sum_bvecAt ω₀ v
  have hσH : ∀ t ∈ H, ∀ v, σ (ρM t v) = ρ t (σ v) := by
    intro t ht v
    have ht0 : t • ω₀ = ω₀ := MulAction.mem_stabilizer_iff.mp ht
    let φ : {x : Ω // x ≠ ω₀} ≃ {x : Ω // x ≠ ω₀} :=
      Equiv.subtypeEquiv (MulAction.toPerm t) (fun x => by
        show x ≠ ω₀ ↔ t • x ≠ ω₀
        rw [ne_eq, ne_eq]
        apply not_congr
        constructor
        · rintro rfl
          exact ht0
        · intro h
          exact smul_left_cancel t (h.trans ht0.symm))
    have hs_equiv : ∀ y : {x : Ω // x ≠ ω₀}, s (φ y) = ρ t (s y) := by
      intro y
      have hc : (g (φ y))⁻¹ * (t * g y) ∈ C := by
        rw [hC]
        constructor
        · rw [mul_smul, mul_smul, hg0 y, ht0, inv_smul_eq_iff, hg0 (φ y)]
        · rw [mul_smul, mul_smul, hg1 y, inv_smul_eq_iff]
          exact (hg1 (φ y)).symm
      have e1 : t * g y = g (φ y) * ((g (φ y))⁻¹ * (t * g y)) := by group
      show ρ (g (φ y)) e' = ρ t (ρ (g y) e')
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, he'fix _ hc]
    rw [hσ_apply, hσ_apply, map_sum, ← Equiv.sum_comp φ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, ← hs_equiv y]
    congr 1
    show permAct (MulAction.toPerm t) (v : Ω → ZMod 2) (t • y.1) = (v : Ω → ZMod 2) y.1
    simp [permAct]
  obtain ⟨j, hj1, hj2⟩ := equivariant_section_of_odd_index ρM ρ π hπ H hHodd σ hσ hσH
  exact ⟨j, hj1, hj2⟩

theorem deleted_five_quotient_kernel_trivial (h5 : Fintype.card Ω = 5)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) ↥(alternatingGroup Ω) E)
    (π : E →ₗ[ZMod 2] ↥(evenWeight Ω)) (hπs : Function.Surjective π)
    (hπ : ∀ (s : ↥(alternatingGroup Ω)) (e : E),
      π (ρ s e) = deletedRep (alternatingGroup Ω) Ω s (π e))
    (hfix : ∀ (s : ↥(alternatingGroup Ω)) (e : E), π e = 0 → ρ s e = e)
    (hgen : Submodule.span (ZMod 2)
      (Set.range fun p : ↥(alternatingGroup Ω) × E => ρ p.1 p.2 - p.2) = ⊤) :
    LinearMap.ker π = ⊥ ∧ Function.Bijective π := by
  obtain ⟨j, hj1, hj2⟩ := deleted_five_quotient_equivariant_section h5 ρ π hπs hπ
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

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
