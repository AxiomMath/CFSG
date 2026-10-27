module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization

section Borel

variable {k : Type*} [Field k]

theorem borel_eq_mul (g : SL(2, k)) (h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0) :
    g = uElt ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 0 0) *
      dElt (Units.mk0 _ ha) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have h11 : (g : Matrix (Fin 2) (Fin 2) k) 1 1 = ((g : Matrix (Fin 2) (Fin 2) k) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uElt]
  have hd : ((dElt (Units.mk0 _ ha) : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![(g : Matrix (Fin 2) (Fin 2) k) 0 0, 0; 0, ((g : Matrix (Fin 2) (Fin 2) k) 0 0)⁻¹] := rfl
  rw [hd]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, ha]

theorem borel_a_ne_zero (g : SL(2, k)) (h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := by
  intro h0
  have h := g.property
  rw [Matrix.det_fin_two, h10, h0] at h
  simp at h

end Borel

section BorelFixed

variable {k : Type*} [Field k] [Fintype k]

theorem borel_fixed_vector (hk : Fintype.card k = 4)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, k) W) [Fact ρ.IsIrreducible] {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [Finite E] [CharP E 2]
    (ιF : k →+* E) (ιD : EndRing ρ →+* E)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor k E ({0, 1} : Finset ℕ)))) :
    ∃ w₀ : W, w₀ ≠ 0 ∧ ∀ g : SL(2, k), (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 → ρ g w₀ = w₀ := by
  classical
  let _ := ιF.toAlgebra
  have hF : Fintype.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hJn : ∀ i ∈ ({0, 1} : Finset ℕ), i < 2 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have hcard := natCard_fixW_rootGroup ρ hF b ιF ιD ({0, 1} : Finset ℕ) hJn Φ
  obtain ⟨w₁, hw₁fix, hw₁ne⟩ : ∃ w : W, (∀ t : k, ρ (uElt t) w = w) ∧ w ≠ 0 := by
    have h1 : 1 < Nat.card {w : W // ∀ t : k, ρ (uElt t) w = w} := by
      rw [hcard]
      exact Finite.one_lt_card
    obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩, hne⟩ := Finite.one_lt_card_iff_nontrivial.mp h1
    by_cases ha0 : a = 0
    · refine ⟨a', ha', fun h => hne (Subtype.ext (by simp [ha0, h]))⟩
    · exact ⟨a, ha, ha0⟩
  let ξ : W → ((↥({0, 1} : Finset ℕ) → Fin 2) → E) := fun w => Φ (fun i => ιD (b.equivFun w i))
  have hξinj : Function.Injective ξ := by
    intro w w' h
    have h1 := Φ.toLinearEquiv.injective h
    apply b.equivFun.injective
    funext i
    exact ιD.injective (congrFun h1 i)
  have hξ : ∀ (g : SL(2, k)) (w : W), ξ (ρ g w) = frobTensor k E ({0, 1} : Finset ℕ) g (ξ w) := by
    intro g w
    have hcoord : b.equivFun (ρ g w) = (matRep b g).mulVec (b.equivFun w) := by
      have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
      rw [repD_apply] at this
      exact this.symm
    have h1 : (fun i => ιD (b.equivFun (ρ g w) i)) =
        matRepE b ιD g (fun i => ιD (b.equivFun w i)) := by
      rw [matRepE_apply, hcoord]
      funext i
      exact RingHom.map_mulVec ιD (matRep b g) (b.equivFun w) i
    show Φ (fun i => ιD (b.equivFun (ρ g w) i)) = _
    rw [h1]
    exact equiv_apply Φ g _
  have htorus : ∀ z : kˣ, ρ (dElt z) w₁ = w₁ := by
    intro z
    have hy : ∀ t : k, tensorRep k E (fun i : ↥({0, 1} : Finset ℕ) => (i : ℕ)) (uElt t) (ξ w₁) =
        ξ w₁ := fun t => by
      have := hξ (uElt t) w₁
      rw [hw₁fix t] at this
      exact this.symm
    obtain ⟨c, hc⟩ := (tensorRep_fixed_iff hF (fun i : ↥({0, 1} : Finset ℕ) => (i : ℕ))
      Subtype.val_injective (fun i => hJn i i.2) (ξ w₁)).mp hy
    have hz3 : (z : k) ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (z : k) z.ne_zero
      rwa [hk] at this
    have hw : frobTensor k E ({0, 1} : Finset ℕ) (dElt z) (ξ w₁) = ξ w₁ := by
      rw [hc, map_smul, frobTensor_dElt_baseVec]
      have h3 : ∑ i ∈ ({0, 1} : Finset ℕ), 2 ^ i = 3 := by decide
      rw [h3, ← map_pow, hz3, map_one, one_smul]
    apply hξinj
    rw [hξ, hw]
  refine ⟨w₁, hw₁ne, fun g hg => ?_⟩
  have ha := borel_a_ne_zero g hg
  rw [borel_eq_mul g hg ha, map_mul, Module.End.mul_apply, htorus, hw₁fix]

end BorelFixed

section DeletedIso

variable {k : Type*} [Field k] [Fintype k]

open CFSG.GorensteinWalter Projectivization

theorem deleted_iso_of_borel_fixed (hk : Fintype.card k = 4) [Fintype (ℙ k (Fin 2 → k))]
    [DecidableEq (ℙ k (Fin 2 → k))]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, k) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (w₀ : W) (hw₀ne : w₀ ≠ 0)
    (hw₀ : ∀ g : SL(2, k), (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 → ρ g w₀ = w₀) :
    ∃ φ : W ≃+ ↥(evenWeight (ℙ k (Fin 2 → k))), ∀ (g : SL(2, k)) (w : W),
      (φ (ρ g w) : ℙ k (Fin 2 → k) → ZMod 2) =
        permAct (MulAction.toPerm g) (φ w : ℙ k (Fin 2 → k) → ZMod 2) := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have hΩ : Fintype.card (ℙ k (Fin 2 → k)) = 5 := by rw [card_projectiveLine, hk]
  have h2 : ∀ a b c d : ℙ k (Fin 2 → k), a ≠ b → c ≠ d →
      ∃ g : SL(2, k), g • a = c ∧ g • b = d :=
    fun a b c d hab hcd => MulAction.is_two_pretransitive_iff.mp inferInstance hab hcd
  have hΩ2 : ∀ a : ℙ k (Fin 2 → k), ∃ b : ℙ k (Fin 2 → k), b ≠ a := fun a => by
    by_contra hcon
    push Not at hcon
    have : Fintype.card (ℙ k (Fin 2 → k)) ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun x y => by rw [hcon x, hcon y])
    omega
  have htrans : ∀ a c : ℙ k (Fin 2 → k), ∃ g : SL(2, k), g • a = c := fun a c => by
    obtain ⟨b, hb⟩ := hΩ2 a
    obtain ⟨d, hd⟩ := hΩ2 c
    obtain ⟨g, hg1, -⟩ := h2 a b c d hb.symm hd.symm
    exact ⟨g, hg1⟩
  choose s hs using fun L : ℙ k (Fin 2 → k) => htrans (psl2ProjectiveInfinity k) L
  let f : ℙ k (Fin 2 → k) → W := fun L => ρ (s L) w₀
  have hf : ∀ (h : SL(2, k)) (L : ℙ k (Fin 2 → k)), ρ h (f L) = f (h • L) := by
    intro h L
    have hstab : ((s (h • L))⁻¹ * (h * s L)) • psl2ProjectiveInfinity k =
        psl2ProjectiveInfinity k := by
      rw [mul_smul, mul_smul, hs L, inv_smul_eq_iff, hs]
    have h10 := (sl2_mem_stabilizer_infinity_iff _).mp (MulAction.mem_stabilizer_iff.mpr hstab)
    have h3 := hw₀ _ h10
    have h4 : ρ (s (h • L)) (ρ ((s (h • L))⁻¹ * (h * s L)) w₀) = ρ (s (h • L)) w₀ := by rw [h3]
    rw [← rep_mul_apply, ← mul_assoc, mul_inv_cancel, one_mul] at h4
    show ρ h (ρ (s L) w₀) = ρ (s (h • L)) w₀
    rw [← rep_mul_apply]
    exact h4
  let π : (ℙ k (Fin 2 → k) → ZMod 2) →ₗ[ZMod 2] W :=
    ∑ L : ℙ k (Fin 2 → k), (LinearMap.proj L : (ℙ k (Fin 2 → k) → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight (f L)
  have hπ : ∀ x, π x = ∑ L, x L • f L := by
    intro x
    simp [π, LinearMap.sum_apply]
  have hπeq : ∀ (h : SL(2, k)) (x : ℙ k (Fin 2 → k) → ZMod 2),
      π (permAct (MulAction.toPerm h) x) = ρ h (π x) := by
    intro h x
    rw [hπ, hπ, map_sum]
    have h1 : ∀ L, ρ h (x L • f L) = x L • f (h • L) := fun L => by
      rw [map_smul, hf]
    simp_rw [h1]
    rw [← Equiv.sum_comp (MulAction.toPerm h)]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp [permAct]
  obtain ⟨hWnt, hWirr⟩ := (isIrreducible_iff ρ).mp Fact.out
  have hπδ : π (delta (psl2ProjectiveInfinity k)) = w₀ := by
    rw [hπ, Finset.sum_eq_single (psl2ProjectiveInfinity k)]
    · have h10 := (sl2_mem_stabilizer_infinity_iff (s (psl2ProjectiveInfinity k))).mp
        (MulAction.mem_stabilizer_iff.mpr (hs (psl2ProjectiveInfinity k)))
      simp [delta, f, hw₀ _ h10]
    · intro L _ hL
      simp [delta, hL]
    · simp
  have hrange : LinearMap.range π = ⊤ := by
    have hinv : ∀ g : SL(2, k), ∀ u ∈ LinearMap.range π, ρ g u ∈ LinearMap.range π := by
      rintro g _ ⟨x, rfl⟩
      exact ⟨permAct (MulAction.toPerm g) x, hπeq g x⟩
    rcases hWirr _ hinv with h | h
    · exfalso
      have : w₀ ∈ LinearMap.range π := ⟨_, hπδ⟩
      rw [h] at this
      exact hw₀ne ((Submodule.mem_bot _).mp this)
    · exact h
  have hπone : π (fun _ => (1 : ZMod 2)) = 0 := by
    have hfix : ∀ g : SL(2, k), ρ g (π (fun _ => (1 : ZMod 2))) = π (fun _ => (1 : ZMod 2)) := by
      intro g
      rw [← hπeq, permAct_one]
    have hZinv : ∀ g : SL(2, k), ∀ u ∈ Submodule.span (ZMod 2) {π (fun _ => (1 : ZMod 2))},
        ρ g u ∈ Submodule.span (ZMod 2) {π (fun _ => (1 : ZMod 2))} := by
      intro g u hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul, hfix]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rcases hWirr _ hZinv with h | h
    · exact Submodule.span_singleton_eq_bot.mp h
    · exfalso
      obtain ⟨g, hg⟩ := hnt
      apply hg
      apply LinearMap.ext
      intro w
      have hw : w ∈ Submodule.span (ZMod 2) {π (fun _ => (1 : ZMod 2))} := by rw [h]; trivial
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hfix]
      rfl
  have hsurj : ∀ w : W, ∃ x ∈ evenWeight (ℙ k (Fin 2 → k)), π x = w := by
    intro w
    have hw : w ∈ LinearMap.range π := by rw [hrange]; trivial
    obtain ⟨x, rfl⟩ := hw
    by_cases hx : ∑ L, x L = 0
    · exact ⟨x, hx, rfl⟩
    · have hx1 : ∑ L, x L = 1 := by
        rcases zmod2_cases (∑ L, x L) with h | h
        · exact absurd h hx
        · exact h
      refine ⟨x + fun _ => 1, ?_, ?_⟩
      · show ∑ L, (x L + 1) = 0
        rw [Finset.sum_add_distrib, hx1]
        simp [hΩ]
        decide
      · rw [map_add, hπone, add_zero]
  let K : Submodule (ZMod 2) (ℙ k (Fin 2 → k) → ZMod 2) :=
    LinearMap.ker π ⊓ evenWeight (ℙ k (Fin 2 → k))
  have hKinv : ∀ g : SL(2, k), ∀ x ∈ K, permAct (MulAction.toPerm g) x ∈ K := by
    intro g x hx
    refine ⟨?_, permAct_mem_evenWeight _ hx.2⟩
    show π (permAct (MulAction.toPerm g) x) = 0
    rw [hπeq, LinearMap.mem_ker.mp hx.1, map_zero]
  have hKbot : K = ⊥ := by
    rcases evenWeight_irreducible_five hΩ h2 K inf_le_right hKinv with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := (exists_ne (0 : W))
      obtain ⟨x, hxE, hxw⟩ := hsurj w
      have hxK : x ∈ K := by rw [h]; exact hxE
      exact hw (hxw ▸ LinearMap.mem_ker.mp hxK.1)
  let πΔ : ↥(evenWeight (ℙ k (Fin 2 → k))) →+ W :=
    (π.comp (evenWeight (ℙ k (Fin 2 → k))).subtype).toAddMonoidHom
  have hbij : Function.Bijective πΔ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hxK : (x : ℙ k (Fin 2 → k) → ZMod 2) ∈ K := ⟨hx, x.2⟩
      rw [hKbot] at hxK
      exact Subtype.ext (by
        have := (Submodule.mem_bot _).mp hxK
        simpa using this)
    · intro w
      obtain ⟨x, hxE, hxw⟩ := hsurj w
      exact ⟨⟨x, hxE⟩, hxw⟩
  let e := AddEquiv.ofBijective πΔ hbij
  refine ⟨e.symm, fun g w => ?_⟩
  have hx : πΔ (e.symm w) = w := e.apply_symm_apply w
  have hmem := permAct_mem_evenWeight (MulAction.toPerm g) (e.symm w).2
  have h1 : πΔ ⟨permAct (MulAction.toPerm g) (e.symm w : ℙ k (Fin 2 → k) → ZMod 2), hmem⟩ = ρ g w := by
    show π (permAct (MulAction.toPerm g) (e.symm w : ℙ k (Fin 2 → k) → ZMod 2)) = ρ g w
    rw [hπeq]
    congr 1
  have h2' : e.symm (ρ g w) = ⟨permAct (MulAction.toPerm g) (e.symm w : ℙ k (Fin 2 → k) → ZMod 2), hmem⟩ := by
    rw [← h1]
    exact e.symm_apply_apply _
  rw [h2']

end DeletedIso


section Embed

variable {k : Type*} [Field k] [Fintype k]

theorem exists_ringHom_of_even {D : Type*} [Field D] [Finite D] [CharP D 2] (hk : Fintype.card k = 4)
    {d : ℕ} (hD : Nat.card D = 2 ^ d) (hd : Even d) : Nonempty (k →+* D) := by
  have hchar : CharP k 2 := charP_two_of_card_eq (n := 2) (by rw [hk]; norm_num)
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  let _ : Algebra (ZMod 2) D := ZMod.algebra D 2
  have h1 : Module.finrank (ZMod 2) k = 2 := by
    have := FiniteField.pow_finrank_eq_card 2 k
    rw [hk] at this
    have h1' : 2 ^ Module.finrank (ZMod 2) k = 2 ^ 2 := by rw [this]; norm_num
    exact Nat.pow_right_injective le_rfl h1'
  have h2 : Module.finrank (ZMod 2) D = d := by
    have := FiniteField.pow_finrank_eq_natCard 2 D
    rw [hD] at this
    exact Nat.pow_right_injective le_rfl this
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := k) (L := D)
    (by rw [h1, h2]; exact even_iff_two_dvd.mp hd)
  exact ⟨f.toRingHom⟩

end Embed


section NaturalCase

theorem eq_subring_of_irreducible {G : Type*} [Monoid G] {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {D : Type*} [Field D] (Fp : Subring D) (θ : W ≃+ (Fin 2 → D))
    (A : G → Matrix (Fin 2) (Fin 2) D) (hA : ∀ g a c, A g a c ∈ Fp)
    (hθ : ∀ g w a, θ (ρ g w) a = ∑ c, A g a c * θ w c) : ∀ d : D, d ∈ Fp := by
  classical
  let W' : Submodule (ZMod 2) W :=
    { carrier := {w | ∀ a : Fin 2, θ w a ∈ Fp}
      add_mem' := by
        intro w w' hw hw' a
        have h1 : θ (w + w') a = θ w a + θ w' a := by simp
        rw [h1]
        exact Fp.add_mem (hw a) (hw' a)
      zero_mem' := by
        intro a
        simp
      smul_mem' := by
        intro c w hw a
        rcases zmod2_cases c with rfl | rfl
        · simp
        · simpa using hw a }
  have hinv : ∀ g, ∀ u ∈ W', ρ g u ∈ W' := by
    intro g u hu a
    show θ (ρ g u) a ∈ Fp
    rw [hθ]
    exact Fp.sum_mem fun c _ => Fp.mul_mem (hA g a c) (hu c)
  have hne : θ.symm (Pi.single 0 1) ∈ W' ∧ θ.symm (Pi.single 0 1) ≠ 0 := by
    refine ⟨fun a => ?_, fun h => ?_⟩
    · rw [AddEquiv.apply_symm_apply]
      fin_cases a
      · simp
      · simp
    · have := congrArg θ h
      rw [AddEquiv.apply_symm_apply, map_zero] at this
      have := congrFun this 0
      simp at this
  have htop : W' = ⊤ := by
    rcases hirr W' hinv with h | h
    · exact absurd ((Submodule.mem_bot _).mp (h ▸ hne.1)) hne.2
    · exact h
  intro d
  have hd : θ.symm (Pi.single 0 d) ∈ W' := by rw [htop]; trivial
  have := hd 0
  rwa [AddEquiv.apply_symm_apply, Pi.single_eq_same] at this

variable {k : Type*} [Field k] [Fintype k]

set_option synthInstance.maxHeartbeats 400000 in
theorem natural_iso_of_single (hk : Fintype.card k = 4)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, k) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) (hdeven : Even d)
    (hdim : Module.finrank (EndRing ρ) W = 2) :
    ∃ φ : W ≃+ (Fin 2 → k),
      ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) k).mulVec (φ w) := by
  classical
  have hF2 : Fintype.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hcharF : CharP k 2 := charP_two_of_card_eq hF2
  obtain ⟨ιF⟩ := exists_ringHom_of_even hk hDcard hdeven
  obtain ⟨j, θ, hθ⟩ := exists_coordinate_iso (n := 2) (by norm_num) hF2 ρ hnt hDcard hdim ιF
  obtain ⟨-, hWirr⟩ := (isIrreducible_iff ρ).mp Fact.out
  let Fp : Subring (EndRing ρ) := ((iterateFrobenius (EndRing ρ) 2 j).comp ιF).range
  have hDFp : ∀ x : EndRing ρ, x ∈ Fp :=
    eq_subring_of_irreducible ρ hWirr Fp θ
      (fun g a c => (ιF ((g : Matrix (Fin 2) (Fin 2) k) a c)) ^ (2 ^ j))
      (fun g a c => ⟨(g : Matrix (Fin 2) (Fin 2) k) a c, by simp [iterateFrobenius_def]⟩) hθ
  have hDle : Nat.card (EndRing ρ) ≤ Nat.card k := by
    refine Nat.card_le_card_of_surjective
      (fun x : k => (iterateFrobenius (EndRing ρ) 2 j) (ιF x)) ?_
    intro x
    obtain ⟨y, hy⟩ := hDFp x
    exact ⟨y, hy⟩
  have hd1 : 1 ≤ d := by
    by_contra hcon
    have hd0 : d = 0 := by omega
    have h2 : Nat.card (EndRing ρ) = 1 := by rw [hDcard, hd0]; rfl
    have h3 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
    omega
  have hD2 : Nat.card (EndRing ρ) = 2 ^ 2 := by
    have h1 : 2 ^ d ≤ 4 := by
      have := hDle
      rw [hDcard, Nat.card_eq_fintype_card, hk] at this
      exact this
    have h2 : d ≤ 2 := by
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨m, hm⟩ := hdeven
    have : d = 2 := by omega
    rw [hDcard, this]
  exact exists_natural_iso (n := 2) (by norm_num) hF2 ρ hnt hD2 hdim

end NaturalCase


section Classify

@[expose] def IsTrivialLine {G W : Type*} [Monoid G] [AddCommMonoid W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) : Prop :=
  ∃ φ : W ≃+ ZMod 2, ∀ g w, φ (ρ g w) = φ w

variable {k : Type*} [Field k]

@[expose] def IsNaturalModule {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, k) W) : Prop :=
  ∃ φ : W ≃+ (Fin 2 → k), ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) k).mulVec (φ w)

@[expose] def IsDeletedModule [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))]
    {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, k) W) : Prop :=
  ∃ φ : W ≃+ ↥(evenWeight (ℙ k (Fin 2 → k))), ∀ (g : SL(2, k)) w,
    (φ (ρ g w) : ℙ k (Fin 2 → k) → ZMod 2) =
      permAct (MulAction.toPerm g) (φ w : ℙ k (Fin 2 → k) → ZMod 2)

theorem isTrivialLine_of_trivial {G W : Type*} [Monoid G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hirr : ρ.IsIrreducible) (htriv : ∀ g, ρ g = 1) :
    IsTrivialLine ρ := by
  obtain ⟨hWnt, hWirr⟩ := (isIrreducible_iff ρ).mp hirr
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hspan : Submodule.span (ZMod 2) {w₀} = ⊤ := by
    rcases hWirr _ (fun g u hu => by rw [htriv g]; exact hu) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hw₀
    · exact h
  let ψ : ZMod 2 →+ W := (LinearMap.toSpanSingleton (ZMod 2) W w₀).toAddMonoidHom
  have hbij : Function.Bijective ψ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      rcases zmod2_cases c with rfl | rfl
      · rfl
      · exfalso
        apply hw₀
        simpa [ψ] using hc
    · intro w
      have : w ∈ Submodule.span (ZMod 2) {w₀} := by rw [hspan]; trivial
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
      exact ⟨c, hc⟩
  refine ⟨(AddEquiv.ofBijective ψ hbij).symm, fun g w => ?_⟩
  rw [htriv g]
  rfl

theorem natCard_evenWeight {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5) :
    Nat.card ↥(evenWeight Ω) = 16 := by
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  have hfin : Module.Finite (ZMod 2) ↥(evenWeight Ω) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(evenWeight Ω))
  rw [finrank_evenWeight, hΩ, Nat.card_zmod] at h
  rw [h]
  norm_num

variable [Fintype k]

theorem not_natural_and_deleted [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))]
    (hk : Fintype.card k = 4) {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, k) W) : ¬ (IsNaturalModule ρ ∧ IsDeletedModule ρ) := by
  rintro ⟨⟨φ₁, h₁⟩, ⟨φ₂, h₂⟩⟩
  apply natural_not_equiv_deleted hk
  refine ⟨φ₁.symm.trans φ₂, fun g v => ?_⟩
  have h3 : φ₁.symm ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) = ρ g (φ₁.symm v) := by
    apply φ₁.injective
    rw [h₁, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  show (φ₂ (φ₁.symm (g • v)) : ℙ k (Fin 2 → k) → ZMod 2) = _
  rw [smul_eq_mulVec', h3, h₂]
  rfl

theorem not_trivial_and_natural (hk : Fintype.card k = 4) {W : Type*} [AddCommMonoid W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) SL(2, k) W) :
    ¬ (IsTrivialLine ρ ∧ IsNaturalModule ρ) := by
  rintro ⟨⟨φ₁, -⟩, ⟨φ₂, -⟩⟩
  have h := Nat.card_congr (φ₁.symm.trans φ₂).toEquiv
  rw [Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk] at h
  norm_num at h

theorem not_trivial_and_deleted [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))]
    (hk : Fintype.card k = 4) {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, k) W) : ¬ (IsTrivialLine ρ ∧ IsDeletedModule ρ) := by
  rintro ⟨⟨φ₁, -⟩, ⟨φ₂, -⟩⟩
  have h := Nat.card_congr (φ₁.symm.trans φ₂).toEquiv
  rw [Nat.card_zmod, natCard_evenWeight (by rw [card_projectiveLine, hk])] at h
  norm_num at h

set_option synthInstance.maxHeartbeats 400000 in
theorem irreducible_binary_SL2_four_module_production (hk : Fintype.card k = 4)
    [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, k) W) (hirr : ρ.IsIrreducible) :
    (IsTrivialLine ρ ∨ IsNaturalModule ρ ∨ IsDeletedModule ρ) ∧
      ¬ (IsTrivialLine ρ ∧ IsNaturalModule ρ) ∧ ¬ (IsTrivialLine ρ ∧ IsDeletedModule ρ) ∧
      ¬ (IsNaturalModule ρ ∧ IsDeletedModule ρ) ∧
      (Nat.card (ZMod 2) = 2 ∧ Nat.card (Fin 2 → k) = 16 ∧
        Nat.card ↥(evenWeight (ℙ k (Fin 2 → k))) = 16) := by
  classical
  have hF2 : Fintype.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hΩ : Fintype.card (ℙ k (Fin 2 → k)) = 5 := by rw [card_projectiveLine, hk]
  refine ⟨?_, not_trivial_and_natural hk ρ, not_trivial_and_deleted hk ρ,
    not_natural_and_deleted hk ρ, Nat.card_zmod 2, ?_, natCard_evenWeight hΩ⟩
  swap
  · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk]
    norm_num
  have hcharF : CharP k 2 := charP_two_of_card_eq hF2
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  by_cases htriv : ∀ g, ρ g = 1
  · exact Or.inl (isTrivialLine_of_trivial ρ hirr htriv)
  right
  push Not at htriv
  have hnt : ∃ g, ρ g ≠ 1 := htriv
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 2) (by norm_num) hF2 ρ hnt
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  have hJle : J.card ≤ 2 := by
    calc J.card ≤ (Finset.range 2).card := Finset.card_le_card (fun i hi => Finset.mem_range.mpr (hJn i hi))
      _ = 2 := Finset.card_range 2
  have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
  rcases (by omega : J.card = 1 ∨ J.card = 2) with h1 | h2
  ·
    left
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, h1]; rfl
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    have hjd : (j + d) % 2 = j := by
      have h := hshift
      rw [Finset.image_singleton, Finset.singleton_inj] at h
      exact h
    have hdeven : Even d := by
      have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases Nat.even_or_odd d with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := h
        omega
    exact natural_iso_of_single hk ρ hnt hDcard hdeven hdim2
  ·
    right
    have hJeq : J = {0, 1} := by
      have hsub : J ⊆ ({0, 1} : Finset ℕ) := by
        intro i hi
        have := hJn i hi
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact Finset.eq_of_subset_of_card_le hsub (by rw [h2]; decide)
    subst hJeq
    obtain ⟨w₀, hw₀ne, hw₀⟩ := borel_fixed_vector hk ρ (Module.finBasis (EndRing ρ) W) ιF ιD Φ
    exact deleted_iso_of_borel_fixed hk ρ hnt w₀ hw₀ne hw₀

end Classify

end CFSG.QuasithinUnique.Setup.SL2Modules
