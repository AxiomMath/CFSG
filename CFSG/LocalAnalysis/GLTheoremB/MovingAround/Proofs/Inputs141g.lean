module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Lane

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g

open CFSG.LocalAnalysis.GLTheoremB.MovingAround

section Abstract

variable {G : Type} [Group G]

theorem twoGen_le_of_mem {A M R : Subgroup G}
    (h2 : ∀ g, g ∈ A → g ∈ M → IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ R) :
    Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)} ≤ R :=
  (Subgroup.closure_le _).2 fun g hg => h2 g hg.1 hg.2.1 hg.2.2

theorem conj_mem_twoGen {A M : Subgroup G} {h : G} (hA : h ∈ A) (hM : h ∈ M) {x : G}
    (hx : x ∈ Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)}) :
    h * x * h⁻¹ ∈ Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)} := by
  have hle : Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)} ≤
      (Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)}).comap
        (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgA, hgM, hg2⟩
    show (MulAut.conj h) g ∈ Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)}
    rw [MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨mul_mem (mul_mem hA hgA) (inv_mem hA),
      mul_mem (mul_mem hM hgM) (inv_mem hM), ?_⟩
    have h1 := hg2.map (MulAut.conj h).toMonoidHom
    rwa [MonoidHom.map_zpowers] at h1
  exact hle hx

theorem isPGroup_two_closure_of_commute {X : Set G} (hX : ∀ x ∈ X, IsPGroup 2 ↥(Subgroup.zpowers x))
    (hcomm : ∀ x ∈ Subgroup.closure X, ∀ y ∈ Subgroup.closure X, Commute x y) :
    IsPGroup 2 ↥(Subgroup.closure X) := by
  have key : ∀ x ∈ Subgroup.closure X, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Inputs141d.exists_pow_eq_one_of_isPGroup (hX x hx)
    | one => exact ⟨0, one_pow _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, ?_⟩
      rw [(hcomm x hx y hy).mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm (2 ^ a),
        pow_mul, hb, one_pow]
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
  intro g
  obtain ⟨k, hk⟩ := key g g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem twoGen_shape_of_hom {C : Type} [Group C] [Finite C] {A M : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (f : C →* G) (hfA : ∀ c, f c ∈ A) (hfM : ∀ c, f c ∈ M)
    (h2 : ∀ g, g ∈ A → g ∈ M → IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ f.range)
    (hC : CFSG.IsQuasisimple C ∨ Nat.Coprime p (Nat.card C)) :
    ⁅Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)},
        Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)}⁆ =
        Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)} ∨
      Nat.Coprime p (Nat.card (Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧
        IsPGroup 2 ↥(Subgroup.zpowers g)})) := by
  classical
  set T := Subgroup.closure {g | g ∈ A ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)} with hTdef
  have hTle : T ≤ f.range := twoGen_le_of_mem h2
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : Finite ↥T := Finite.of_injective (Subgroup.inclusion hTle) (Subgroup.inclusion_injective hTle)
  rcases hC with hq | hcop
  · haveI hN : (T.comap f).Normal := ⟨fun n hn c => by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact conj_mem_twoGen (hfA c) (hfM c) hn⟩
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (T.comap f) with hZ | htop
    ·
      right
      have hcomm : ∀ x ∈ T, ∀ y ∈ T, Commute x y := by
        intro x hx y hy
        obtain ⟨c, rfl⟩ := hTle hx
        obtain ⟨d, rfl⟩ := hTle hy
        have hc : c ∈ Subgroup.center C := hZ hx
        show f c * f d = f d * f c
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc d).symm]
      have hT2 : IsPGroup 2 ↥T := isPGroup_two_closure_of_commute (fun x hx => hx.2.2) hcomm
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT2
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    ·
      left
      have hTeq : T = f.range := by
        refine le_antisymm hTle ?_
        rintro _ ⟨c, rfl⟩
        have hc : c ∈ T.comap f := by rw [htop]; exact Subgroup.mem_top c
        exact hc
      haveI : Group.IsPerfect C := hq.1
      rw [hTeq, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
  · right
    exact Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_dvd_of_le hTle).trans (Subgroup.card_range_dvd f)) hcop

end Abstract

section Orbit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem ratTwo_shape_of_hom (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {C : Type} [Group C] [Finite C]
    (θ : C →* ModGL τ (AlgebraicClosure K))
    (hθS : ∀ c, θ c ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i))
    (hθfix : ∀ c, iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (θ c) = θ c)
    (hodd : ∀ y ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) y = y →
        ∃ m : ℕ, Odd m ∧ y ^ m ∈ θ.range)
    (hC : CFSG.IsQuasisimple C ∨ Nat.Coprime p (Nat.card C)) :
    ⁅Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hP0 : P.S 0 = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hPZ : P.Z = Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    show Subgroup.centralizer (P.A : Set (ModGL τ (AlgebraicClosure K))) = _
    rw [hPA]
  have hθ0 : ∀ c, θ c ∈ P.S 0 := fun c => by rw [hP0]; exact hθS c
  let θ' : C →* P.S 0 := θ.codRestrict (P.S 0) hθ0
  have hθ' : ∀ c, ((θ' c : P.S 0) : ModGL τ (AlgebraicClosure K)) = θ c := fun c => rfl
  let f : C →* ModGL τ (AlgebraicClosure K) := P.norm.comp θ'
  have hAadj : P.A ≤ adjointGroup τ (AlgebraicClosure K) := by
    rw [hPA]
    exact rootSpan_le_adjointGroup _ _
  have hfix : ∀ c, f c ∈ P.Afix := fun c => P.norm_mem_Afix (y := θ' c) (by rw [hθ']; exact hθfix c)
  unfold Inputs141f.ratTwo
  refine twoGen_shape_of_hom hp hp2 f (fun c => hPA ▸ (hfix c).1)
    (fun c => ⟨hAadj (hfix c).1, (hfix c).2⟩) (fun g hgA hgM hg2 => ?_) hC
  obtain ⟨k₂, hk₂⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
  have hgP : g ∈ P.A := hPA ▸ hgA
  have hgF : S.D.step g = g := hgM.2
  obtain ⟨y, hyY, ζ, hζZ, hζA, rfl⟩ := P.exists_eq_zeta_norm hgP hgF
  obtain ⟨Nζ, hNζ, hζN⟩ := Inputs141f.exists_odd_pow_of_mem_center_orbit S hK2 hT i (hPA ▸ hζA)
    (hPZ ▸ hζZ)
  obtain ⟨hy0, hyZ⟩ := P.mem_Y.1 hyY
  set c := iterHom S.D.step s (y : ModGL τ (AlgebraicClosure K)) *
    (y : ModGL τ (AlgebraicClosure K))⁻¹ with hc
  have hcA : c ∈ P.A := mul_mem (P.S_le_A 0 (P.iterHom_s_mem hy0)) (inv_mem (P.S_le_A 0 hy0))
  obtain ⟨Nc, hNc, hcN⟩ := Inputs141f.exists_odd_pow_of_mem_center_orbit S hK2 hT i (hPA ▸ hcA)
    (hPZ ▸ hyZ)
  have hcy : Commute c (y : ModGL τ (AlgebraicClosure K)) := ((P.mem_Z.1 hyZ) _ (P.S_le_A 0 hy0)).symm
  have hyfix : iterHom S.D.step s ((y : ModGL τ (AlgebraicClosure K)) ^ Nc) =
      (y : ModGL τ (AlgebraicClosure K)) ^ Nc := by
    have e : iterHom S.D.step s (y : ModGL τ (AlgebraicClosure K)) =
        c * (y : ModGL τ (AlgebraicClosure K)) := by rw [hc]; group
    rw [map_pow, e, hcy.mul_pow, hcN, one_mul]
  obtain ⟨m, hm, c₀, hc₀⟩ := hodd _ (by rw [← hP0]; exact pow_mem hy0 Nc) hyfix
  have hθc₀ : θ' c₀ = y ^ (Nc * m) := by
    apply Subtype.ext
    rw [hθ', hc₀, SubgroupClass.coe_pow, pow_mul]
  have hMo : Odd (Nζ * (Nc * m)) := hNζ.mul (hNc.mul hm)
  have key : (ζ * P.norm y) ^ (Nζ * (Nc * m)) = f (c₀ ^ Nζ) := by
    have hcomm : Commute ζ (P.norm y) := ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y)).symm
    rw [hcomm.mul_pow, show ζ ^ (Nζ * (Nc * m)) = 1 by rw [pow_mul, hζN, one_pow], one_mul, map_pow]
    show P.norm y ^ (Nζ * (Nc * m)) = (P.norm (θ' c₀)) ^ Nζ
    rw [hθc₀, map_pow, ← pow_mul, mul_comm (Nc * m) Nζ]
  exact Inputs141f.mem_of_two_of_odd_pow_mem hk₂ hMo ⟨c₀ ^ Nζ, key.symm⟩

end Orbit

section Layer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)



theorem ratTwo_shape_of_layer {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hfin : Finite ↥(rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ⊓ S.D.model))
    (hqs : CFSG.IsQuasisimple
      ↥(rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    ⁅Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) := by
  have hfinΨ : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hs1 := componentOrbitLength_eq_one hfinΨ hρ
  refine ratTwo_shape_of_hom S hK2 hp hp2 hT i
    (rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ⊓ S.D.model).subtype
    (fun c => c.2.1) (fun c => ?_) (fun y hy hyF => ⟨1, odd_one, ?_⟩) (Or.inl hqs)
  · rw [hs1]
    exact c.2.2.2
  · rw [hs1] at hyF
    rw [pow_one]
    exact ⟨⟨y, hy, rootSpan_le_adjointGroup _ _ hy, hyF⟩, rfl⟩

theorem layer_d4_outer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} [E6Sub τ]
    (hsearch : D4BaseSearch τ) (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    Finite ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  rw [hΨ]
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hπ1
  · exact rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact
  · exact rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact
  · exact rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact
  · exact rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4 hact
  · exact rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2 hact

theorem layer_d4_twE6 (hE6 : E6FixDNAll) {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    Finite ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  rw [hΨ]
  refine CFSG.HardMathSupport.Dickson.Sec6.ssTw_layer_tw S hq hFr hΦ' hn v (d4Nodes Tag.E6)
    (fun P => Finite ↥P ∧ CFSG.IsQuasisimple ↥P) (fun P g h => ?_) (fun n hn' hwn => ?_)
  · haveI := h.1
    exact ⟨Finite.of_equiv _ (P.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv,
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (P.equivMapOfInjective _ (MulAut.conj g).injective)
        h.2⟩
  · have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn'⟩ • permLattice e6Graph α = u • permLattice πJ α := by
      intro α hα
      rw [hwn, ← hw', hw₀, mul_smul, hlin α hα]
    rcases hπJleaf with hc | hc | hc | hc | hc | hc
    · exact absurd hc hπ1
    · rw [hc] at hact
      exact twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn' hu hact
    · rw [hc] at hact
      exact twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn' hu hact
    · rw [hc] at hact
      exact twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn' hu hact
    · rw [hc] at hact
      exact twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact
    · rw [hc] at hact
      exact twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact

theorem layer_e6 {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      Finite ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_rho_stable_e6 S haT i v hΨ
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  rw [hΨ] at hw
  obtain ⟨hfin, hqs⟩ := rootSpan_inf_model_quasisimple hτ' S hn v hw
  refine ⟨hρ, ?_, ?_⟩
  · rw [hΨ]
    exact hfin
  · rw [hΨ]
    exact hqs

theorem layer_d4class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      Finite ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  have hE6 : E6FixDNAll := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    refine ⟨hρ, ?_⟩
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact layer_d4_outer d4Base_E6 d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      exact layer_d4_twE6 hE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ⟨hρ, layer_d4_outer d4Base_E7 CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7
      (d4SwapLayer_E7 hE6) S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ
      hnin⟩
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ⟨hρ, layer_d4_outer d4Base_E8 CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
      (d4SwapLayer_E8 hE6) S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ
      hnin⟩

theorem layer_e6class {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc : (componentRoots (rootCharHom a) i).ncard = 72) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      Finite ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
  rw [hr] at hle
  cases τ with
  | G2 => exact absurd hle (by decide)
  | F4 => exact absurd hle (by decide)
  | D4 => exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hr hc
    exact layer_e6 S hT i v hv
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hr hc
    exact layer_e6 S hT i v hv

end Layer

section Unitary

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open scoped commutatorElement MatrixGroups


theorem exists_unitary_untwist {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a)) :
    ∃ (r e : ℕ) (σQ : L ≃+* L) (z : ModGL τ L), r.Prime ∧ CharP L r ∧ 0 < e ∧ S.D.q = r ^ e ∧
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      (∀ X : SL(ν, L), iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
        (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹) ∧
      ∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  refine ⟨r, e, σQ, z, hr, hchar, he, hq, hσc, fun X => ?_, hnorm⟩
  rw [← hstd X, map_mul, map_mul, map_inv, hz]
  group

theorem ratTwo_shape_suN {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .suN)
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    ⁅Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have hs := (outer_componentOrbitLength_spec S hT i).2.1
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) = σ (π b) (π a) := by
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exfalso
      apply hout
      obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
      refine ⟨w, ?_, fun γ hγ => ?_⟩
      · rw [hΨ]
        exact hw
      · rw [hΨ] at hγ
        obtain ⟨a, b, hab, rfl⟩ := hγ
        rw [hπ a b hab, hwσ]
    · exact ⟨π, hπ⟩
  obtain ⟨r, e, σQ, z, hr, hchar, he, hq, hσc, hconj, hnormz⟩ :=
    exists_unitary_untwist S hT i hν hψ hΨ π hπ
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  have hψS : ∀ X, ψ X ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, AlgebraicClosure K), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨hfinC, hqsC, hcardC⟩ :=
    stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  haveI := hfinC
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    obtain ⟨ε, hε⟩ := hψ.transv ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    have h1 : Matrix.SpecialLinearGroup.transvection
        (show (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ by simp) (1 : AlgebraicClosure K) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ (AlgebraicClosure K) (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ (AlgebraicClosure K) _ h1)
  have hkerZ : ψ.ker ≤ Subgroup.center SL(ν, AlgebraicClosure K) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
      (isQuasisimple_specialLinearGroup hν) ψ.ker with h | h
    · exact h
    · exact absurd h hker
  let θ : C →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  refine ratTwo_shape_of_hom S hK2 hp (by omega) hT i θ (fun c => ?_) (fun c => ?_)
    (fun y hy hyF => ?_) ?_
  · rw [hθ]
    exact (hnormz i _).1 (hψS c)
  · rw [hθ, hconj, (hCmem c).1 c.2]
  ·
    have h1 : z⁻¹ * y * z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
      (hnormz i _).2 (by
        have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
        rw [e]
        exact hy)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    have hyX : y = z * ψ X * z⁻¹ := by rw [hX]; group
    have h2 : ψ (stdUnitary σQ.toRingHom X) = ψ X := by
      have h3 := hconj X
      rw [← hyX, hyF] at h3
      have e : z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ = z * ψ X * z⁻¹ := by rw [← h3, hyX]
      exact mul_left_cancel (mul_right_cancel e)
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    have hcZ : c ∈ Subgroup.center SL(ν, AlgebraicClosure K) := hkerZ (by
      rw [MonoidHom.mem_ker, hcdef, map_mul, map_inv, h2, mul_inv_cancel])
    obtain ⟨l, hl, hlc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcZ
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin, zero_pow (by omega)] at hl
      exact zero_ne_one hl
    obtain ⟨m, hm, hlm'⟩ := Inputs141e.exists_odd_pow_eq_one hK2 (fun _ : Unit => Units.mk0 l hl0)
    have hlm : l ^ m = 1 := by
      have h4 := congrArg Units.val (hlm' ())
      simpa using h4
    have hcm : c ^ m = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hlc, ← map_pow, hlm, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hXc : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hcX : Commute c X := (Subgroup.mem_center_iff.1 hcZ X).symm
    have hXm : X ^ m ∈ C := by
      rw [hCmem, map_pow, hXc, hcX.mul_pow, hcm, one_mul]
    refine ⟨m, hm, ⟨X ^ m, hXm⟩, ?_⟩
    rw [hθ, hyX, conj_pow]
    simp only [SubgroupClass.coe_pow, map_pow]
  ·
    rw [hr2] at hqsC hcardC
    by_cases h32 : (ν, 2 ^ (e * s)) = (3, 2)
    · right
      rw [hcardC h32, show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num]
      exact Inputs2323b.coprime_two_pow_mul_three_pow hp hp5 3 3
    · exact Or.inl (hqsC h32)

end Unitary

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g

end
