module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryFrobenius
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT Matrix
open scoped MatrixGroups

section BaseChange

variable {τ : Tag} {K L : Type} [Field K] [Field L]

theorem baseChangeGL_pinnedWeyl' (f : K →+* L) (β : Fin τ.rank → ℤ) :
    baseChangeGL f (pinnedWeyl τ K β) = pinnedWeyl τ L β :=
  Units.ext ((baseChange_baseChangeEnd f _).unique
    (baseChange_prod_reverse_weylElt (τ := τ) f (pinnedData τ β).2.1))

theorem baseChangeGL_simpleRootSL2' (f : K →+* L) (i : Fin τ.rank) (A : SL2 K) :
    baseChangeGL f (simpleRootSL2 τ K i A) =
      simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f A) := by
  have h : (baseChangeGL f).comp (simpleRootSL2 τ K i) =
      (simpleRootSL2 τ L i).comp (Matrix.SpecialLinearGroup.map f) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change baseChangeGL f (simpleRootSL2 τ K i (uSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (uSL c))
        rw [simpleRootSL2_uSL, baseChangeGL_xUnit, map_uSL, simpleRootSL2_uSL]
      · change baseChangeGL f (simpleRootSL2 τ K i (vSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (vSL c))
        rw [simpleRootSL2_vSL, baseChangeGL_yUnit, map_vSL, simpleRootSL2_vSL]
  exact DFunLike.congr_fun h A

theorem baseChangeGL_rootSL2' (f : K →+* L) (β : Fin τ.rank → ℤ) (A : SL2 K) :
    baseChangeGL f (rootSL2 τ K β A) = rootSL2 τ L β (Matrix.SpecialLinearGroup.map f A) := by
  rw [rootSL2_apply, rootSL2_apply, map_mul, map_mul, map_inv, baseChangeGL_pinnedWeyl',
    baseChangeGL_simpleRootSL2']

end BaseChange

section Rational

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem iterateFrobenius_algClos (x : AlgClosGF p e) :
    iterateFrobenius (AlgClosGF p e) p e x = x ^ Nat.card (GaloisField p e) := by
  rw [iterateFrobenius_def, GaloisField.card p e (NeZero.ne e)]

theorem entrywiseFrobGL_baseChangeGL_algebraMap {τ : Tag} (c : ModGL τ (GaloisField p e)) :
    entrywiseFrobGL τ (AlgClosGF p e) p e
        (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) c) =
      baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) c :=
  units_map_entrywiseHom_baseChangeGL_algebraMap (iterateFrobenius (AlgClosGF p e) p e)
    iterateFrobenius_algClos _

theorem exists_rat_of_frobFixed {x : AlgClosGF p e}
    (hx : iterateFrobenius (AlgClosGF p e) p e x = x) :
    ∃ x₀ : GaloisField p e, algebraMap (GaloisField p e) (AlgClosGF p e) x₀ = x := by
  rw [iterateFrobenius_algClos] at hx
  exact mem_range_algebraMap_of_pow_card_eq hx

theorem exists_rootSL2_of_frobFixed {τ : Tag} {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hp2 : p ≠ 2) {A' : SL2 (AlgClosGF p e)}
    (hfix : entrywiseFrobGL τ (AlgClosGF p e) p e
      (rootSL2 τ (AlgClosGF p e) θ A') = rootSL2 τ (AlgClosGF p e) θ A') :
    ∃ A₀ : SL2 (GaloisField p e), rootSL2 τ (AlgClosGF p e) θ A' =
      baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
        (rootSL2 τ (GaloisField p e) θ A₀) := by
  have hk : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hinj : Function.Injective (rootSL2 τ (AlgClosGF p e) θ) :=
    ((exceptional_Lang_root_rank_one_data τ (AlgClosGF p e) θ).2.2.2.2.2.2.2.1 hk).1
  rw [entrywiseFrobGL_rootSL2 p e hθ] at hfix
  have hA := hinj hfix
  obtain ⟨a, b, c, d, hm, hdet⟩ := sl2_exists_entries A'
  have hent : ∀ i j : Fin 2, iterateFrobenius (AlgClosGF p e) p e
      ((A' : Matrix (Fin 2) (Fin 2) (AlgClosGF p e)) i j) =
        (A' : Matrix (Fin 2) (Fin 2) (AlgClosGF p e)) i j := fun i j => by
    have := congrArg (fun M : SL2 (AlgClosGF p e) =>
      (M : Matrix (Fin 2) (Fin 2) (AlgClosGF p e)) i j) hA
    simpa using this
  obtain ⟨a₀, ha₀⟩ := exists_rat_of_frobFixed (by simpa [hm] using hent 0 0)
  obtain ⟨b₀, hb₀⟩ := exists_rat_of_frobFixed (by simpa [hm] using hent 0 1)
  obtain ⟨c₀, hc₀⟩ := exists_rat_of_frobFixed (by simpa [hm] using hent 1 0)
  obtain ⟨d₀, hd₀⟩ := exists_rat_of_frobFixed (by simpa [hm] using hent 1 1)
  have hdet₀ : a₀ * d₀ - b₀ * c₀ = 1 := by
    apply (algebraMap (GaloisField p e) (AlgClosGF p e)).injective
    rw [map_sub, map_mul, map_mul, ha₀, hb₀, hc₀, hd₀, map_one]
    exact hdet
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : SL2 (GaloisField p e),
      (A₀ : Matrix (Fin 2) (Fin 2) (GaloisField p e)) = !![a₀, b₀; c₀, d₀] :=
    ⟨⟨!![a₀, b₀; c₀, d₀], by simp [Matrix.det_fin_two, hdet₀]⟩, rfl⟩
  refine ⟨A₀, ?_⟩
  rw [baseChangeGL_rootSL2']
  congr 1
  apply Subtype.ext
  rw [hm, Matrix.SpecialLinearGroup.map_apply_coe, hA₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha₀, hb₀, hc₀, hd₀]

end Rational

section Lift

theorem exists_lift_of_range {G K Y : Type*} [Group G] [Group K] [Group Y] (ψ : K →* Y)
    (hψ : Function.Injective ψ) (α : G →* Y) (h : ∀ y, α y ∈ ψ.range) :
    ∃ θ : G →* K, ∀ y, ψ (θ y) = α y := by
  refine ⟨((MonoidHom.ofInjective hψ).symm : ψ.range →* K).comp (α.codRestrict ψ.range h), ?_⟩
  intro y
  simp

end Lift

section NegOne

variable {E : Type} [Field E] [Finite E] {p e : ℕ} [Fact p.Prime] [CharP E p]

variable (E p e) in
@[expose] noncomputable def suNegOne : Su E p e 2 :=
  ⟨-1, by
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_fin_two]
    · have hm : ((-1 : Matrix (Fin 2) (Fin 2) E)).map (unitaryInvolution E p e) = -1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      simp only [Units.val_neg, Units.val_one]
      rw [conjTr, hm, Matrix.transpose_neg, Matrix.transpose_one]
      simp⟩

theorem suToSL_suNegOne :
    suToSL (unitaryInvolution E p e) 2 (suNegOne E p e) = HSL (-1 : Eˣ) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suNegOne, coe_suToSL, suMat, coe_HSL]

end NegOne

section Perfect

variable {E : Type} [Field E] [Finite E] {p e : ℕ} [Fact p.Prime] [CharP E p]

theorem su_three_perfect (hK : Nat.card E = (p ^ e) ^ 2) (hq : 5 ≤ p ^ e) :
    (⊤ : Subgroup (Su E p e 3)) ≤ ⁅(⊤ : Subgroup (Su E p e 3)), ⊤⁆ := by
  have h1 := CFSG.ClassicalInvolution.RouteD.B12_perfect_su (K := E) (p := p) (f := e) hK hq
  have h2 := CFSG.ClassicalInvolution.RouteD.B23_perfect_su (K := E) (p := p) (f := e) hK hq
  have htop := CFSG.ClassicalInvolution.Phan.B12_sup_B23 (K := E) (p := p) (f := e) hK
    (by omega)
  exact htop.symm.le.trans (sup_le (h1.trans (Subgroup.commutator_mono le_top le_top))
    (h2.trans (Subgroup.commutator_mono le_top le_top)))

theorem su_range_le_commutator {Y : Type*} [Group Y] (hK : Nat.card E = (p ^ e) ^ 2)
    (hq : 5 ≤ p ^ e) (α : Su E p e 3 →* Y) : α.range ≤ ⁅α.range, α.range⁆ := by
  have h := su_three_perfect (E := E) (p := p) (e := e) hK hq
  rw [MonoidHom.range_eq_map]
  have h2 := Subgroup.map_mono (f := α) h
  rwa [Subgroup.map_commutator] at h2

end Perfect

section Hom

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

omit [NeZero e] in
theorem nonempty_ringHom_galoisField_algClos (n : ℕ) :
    Nonempty (GaloisField p n →+* AlgClosGF p e) := by
  let _ : Algebra (ZMod p) (AlgClosGF p e) := ZMod.algebra (AlgClosGF p e) p
  have : Algebra.IsAlgebraic (ZMod p) (GaloisField p n) := Algebra.IsAlgebraic.of_finite _ _
  exact ⟨(IsAlgClosed.lift : GaloisField p n →ₐ[ZMod p] AlgClosGF p e).toRingHom⟩

theorem exists_unitary_hom {τ : Tag} {θ δ : Fin τ.rank → ℤ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (hpair : A2Pairing θ δ)
    (Em : A2Embedding τ θ δ (GaloisField p (2 * e)))
    {c : ↥(adjointGroup τ (GaloisField p e))} {v d : ModGL τ (AlgClosGF p e)}
    (hd : v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
        (c : ModGL τ (GaloisField p e)) * v⁻¹ = d)
    (hcocycle : ∃ Λ₀ Λ₁ Λ₂ Λ₃ : AlgClosGF p e, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) θ x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) (-θ) (Λ₀ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) (-θ) x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) θ (Λ₁ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) δ x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) (-δ) (Λ₂ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) (-δ) x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) δ (Λ₃ * x)))
    (hdt : ∀ t ∈ torusGroup τ (AlgClosGF p e), d * t = t * d)
    (hvadj : ∀ t ∈ torusGroup τ (AlgClosGF p e), t * v ∈ adjointGroup τ (AlgClosGF p e))
    (hvconj : ∀ t ∈ torusGroup τ (AlgClosGF p e), ∀ A : SL2 (AlgClosGF p e),
      ∃ A' : SL2 (AlgClosGF p e), (t * v)⁻¹ * rootSL2 τ (AlgClosGF p e) θ A * (t * v) =
        rootSL2 τ (AlgClosGF p e) θ A')
    (hsign : ∀ j : GaloisField p (2 * e) →+* AlgClosGF p e,
      baseChangeGL j (rootSL2 τ (GaloisField p (2 * e)) δ
        (HSL (-1 : (GaloisField p (2 * e))ˣ))) = d) :
    ∃ θ' : Su (GaloisField p (2 * e)) p e 3 →* ↥(adjointGroup τ (GaloisField p e)),
      Function.Injective θ' ∧
      (∀ A : Su (GaloisField p (2 * e)) p e 2, ∃ A₀ : SL2 (GaloisField p e),
        ((θ' (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) :
          ↥(adjointGroup τ (GaloisField p e))) : ModGL τ (GaloisField p e)) =
            rootSL2 τ (GaloisField p e) θ A₀) ∧
      θ' (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 0
        (suNegOne (GaloisField p (2 * e)) p e)) = c := by
  classical
  have hcardq : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (NeZero.ne e)
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hE2 : ringChar (GaloisField p (2 * e)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (2 * e)) p]
    exact hp2
  obtain ⟨j⟩ := nonempty_ringHom_galoisField_algClos (p := p) (e := e) (2 * e)
  have hj : ∀ x : GaloisField p (2 * e),
      j (unitaryInvolution (GaloisField p (2 * e)) p e x) = j x ^ p ^ e := fun x => by
    rw [unitaryInvolution_apply, map_pow]
  obtain ⟨Λ₀, Λ₁, Λ₂, Λ₃, e1, e2, a0, a1, a2, a3⟩ := hcocycle
  have sq : ∀ {x : GaloisField p (2 * e)}, x * x = 1 → j x * j x = 1 := fun {x} h => by
    rw [← map_mul, h, map_one]
  have s₀ := sq Em.sq₀
  have s₁ := sq Em.sq₁
  have s₂ := sq Em.sq₂
  have s₃ := sq Em.sq₃
  have hκ₀ : (-(j Em.m₁ * j Em.m₀)) * (-(j Em.m₁ * j Em.m₀)) = 1 := by
    linear_combination (j Em.m₁ * j Em.m₁) * s₀ + s₁
  have hκ₂ : (-(j Em.m₃ * j Em.m₂)) * (-(j Em.m₃ * j Em.m₂)) = 1 := by
    linear_combination (j Em.m₃ * j Em.m₃) * s₂ + s₃
  obtain ⟨t, ht, hmod⟩ := exists_torusMod hθ hδ hpair p e e1 e2 hκ₀ hκ₂
  set v' := t * v with hv'def
  set u := entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹ with hu
  set u' := entrywiseFrobGL τ (AlgClosGF p e) p e t * u * t⁻¹ with hu'
  obtain ⟨b₀, b₁, b₂, b₃⟩ := hmod u u' rfl a0 a1 a2 a3
  have hτ := conj_iota_eq_tau Em j b₀ b₁ b₂ b₃ rfl rfl
  have hv'adj : v' ∈ adjointGroup τ (AlgClosGF p e) := hvadj t ht
  have hd' : v' * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
      (c : ModGL τ (GaloisField p e)) * v'⁻¹ = d := by
    have hcomm : d * t = t * d :=
      hdt t ht
    calc v' * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          (c : ModGL τ (GaloisField p e)) * v'⁻¹ =
        t * (v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          (c : ModGL τ (GaloisField p e)) * v⁻¹) * t⁻¹ := by rw [hv'def]; group
      _ = t * d * t⁻¹ := by rw [hd]
      _ = d := by rw [← hcomm]; group
  have hFv' : entrywiseFrobGL τ (AlgClosGF p e) p e v' = u' * v' := by
    rw [hv'def, map_mul]
    have : entrywiseFrobGL τ (AlgClosGF p e) p e v = u * v := by rw [hu]; group
    rw [this, hu']
    group
  let α : Su (GaloisField p (2 * e)) p e 3 →* ModGL τ (AlgClosGF p e) :=
    (MulAut.conj v'⁻¹).toMonoidHom.comp (((baseChangeGL j).comp Em.ι).comp
      (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3))
  have hα : ∀ y, α y = v'⁻¹ * baseChangeGL j (Em.ι (suToSL (unitaryInvolution
      (GaloisField p (2 * e)) p e) 3 y)) * v' := fun y => by
    simp [α]
  have hαF : ∀ y, entrywiseFrobGL τ (AlgClosGF p e) p e (α y) = α y := fun y => by
    rw [hα]
    exact frob_alpha p e hp2 Em j
      ((unitaryInvolution (GaloisField p (2 * e)) p e : GaloisField p (2 * e) ≃+*
        GaloisField p (2 * e)) : GaloisField p (2 * e) →+* GaloisField p (2 * e)) hj hFv' hτ
      (map_suToSL_eq_tau y)
  have hKodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcardq]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hFrFun : ∀ x : AlgClosGF p e,
      iterateFrobenius (AlgClosGF p e) p e x = x ^ Nat.card (GaloisField p e) :=
    iterateFrobenius_algClos
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ
    (GaloisField p e) hKodd (AlgClosGF p e) (iterateFrobenius (AlgClosGF p e) p e) hFrFun
  have hαR : α.range ≤ adjointGroup τ (AlgClosGF p e) ⊓
      (Units.map (entrywiseHom (iterateFrobenius (AlgClosGF p e) p e))).eqLocus
        (MonoidHom.id _) := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, hαF y⟩
    rw [hα]
    exact mul_mem (mul_mem (inv_mem hv'adj) (baseChangeGL_mem_adjointGroup j (Em.mem _))) hv'adj
  have hrange : α.range ≤ (adjointGroup τ (GaloisField p e)).map
      (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))) := by
    rw [← hder]
    exact (su_range_le_commutator hcardE hq α).trans (Subgroup.commutator_mono hαR hαR)
  let ψ : ↥(adjointGroup τ (GaloisField p e)) →* ModGL τ (AlgClosGF p e) :=
    (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))).comp
      (adjointGroup τ (GaloisField p e)).subtype
  have hψinj : Function.Injective ψ := fun x y h =>
    Subtype.ext (baseChangeGL_injective _ h)
  have hψr : ψ.range = (adjointGroup τ (GaloisField p e)).map
      (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨φ, hφ⟩ := exists_lift_of_range ψ hψinj α
    (fun y => by rw [hψr]; exact hrange ⟨y, rfl⟩)
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : α y₁ = α y₂ := by rw [← hφ y₁, ← hφ y₂, h]
    rw [hα, hα] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact suToSL_injective (Em.inj (baseChangeGL_injective j h2))
  · intro A
    have h3 : suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3
        (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        blk (GaloisField p (2 * e)) 0
          (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) := by
      rw [embSUid_two_eq_blockEmb, suToSL_blockEmb]
      rfl
    obtain ⟨B₁, hB₁⟩ := Em.blk_zero_mem hθ
      (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A)
    obtain ⟨A', hA'⟩ := hvconj t ht (Matrix.SpecialLinearGroup.map j B₁)
    have hαy : α (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        rootSL2 τ (AlgClosGF p e) θ A' := by
      rw [hα, h3, ← hB₁, baseChangeGL_rootSL2', hA']
    have hfix := hαF (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A)
    rw [hαy] at hfix
    obtain ⟨A₀, hA₀⟩ := exists_rootSL2_of_frobFixed hθ hp2 hfix
    have hmem : rootSL2 τ (GaloisField p e) θ A₀ ∈ adjointGroup τ (GaloisField p e) :=
      rootSL2_mem_adjointGroup _ _
    have hφy : φ (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        ⟨rootSL2 τ (GaloisField p e) θ A₀, hmem⟩ := by
      apply hψinj
      rw [hφ, hαy, hA₀]
      rfl
    rw [hφy]
    exact ⟨A₀, rfl⟩
  · have h3 : suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3
        (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 0
          (suNegOne (GaloisField p (2 * e)) p e)) =
        blk (GaloisField p (2 * e)) 1 (HSL (-1 : (GaloisField p (2 * e))ˣ)) := by
      rw [embSUid_zero_eq_blockEmb, suToSL_blockEmb, suToSL_suNegOne]
      rfl
    apply hψinj
    rw [hφ, hα, h3, Em.blk_one_neg_one hE2 hδ, hsign j]
    change _ = baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
      (c : ModGL τ (GaloisField p e))
    have hd'' : d = v' * baseChangeGL
        (algebraMap (GaloisField p e) (AlgClosGF p e)) (c : ModGL τ (GaloisField p e)) * v'⁻¹ :=
      hd'.symm
    change v'⁻¹ * d * v' = _
    rw [hd'']
    group


end Hom

section NatCard

variable {p e : ℕ} [Fact p.Prime]

theorem natCard_rankOne {τ : Tag} {θ : Fin τ.rank → ℤ} (hp2 : p ≠ 2)
    [NeZero e] (R : Subgroup ↥(adjointGroup τ (GaloisField p e)))
    (hR : ∀ g : ↥(adjointGroup τ (GaloisField p e)), g ∈ R ↔
      ∃ A : SL2 (GaloisField p e), (g : ModGL τ (GaloisField p e)) =
        rootSL2 τ (GaloisField p e) θ A) :
    Nat.card R = p ^ e * ((p ^ e) ^ 2 - 1) := by
  have hK : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  have hinj : Function.Injective (rootSL2 τ (GaloisField p e) θ) :=
    ((exceptional_Lang_root_rank_one_data τ (GaloisField p e) θ).2.2.2.2.2.2.2.1 hK).1
  let f : SL2 (GaloisField p e) → ↥R := fun A =>
    ⟨⟨rootSL2 τ (GaloisField p e) θ A, rootSL2_mem_adjointGroup _ _⟩, (hR _).2 ⟨A, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun A B h => hinj (congrArg (fun x : ↥R =>
      (x.1 : ↥(adjointGroup τ (GaloisField p e))).1) h), fun x => ?_⟩
    obtain ⟨A, hA⟩ := (hR _).1 x.2
    exact ⟨A, Subtype.ext (Subtype.ext hA.symm)⟩
  rw [← Nat.card_eq_of_bijective f hf, card_specialLinearGroup_fin_two,
    GaloisField.card p e (NeZero.ne e)]

theorem natCard_B12 {E : Type} [Field E] [Finite E] [CharP E p]
    (hK : Nat.card E = (p ^ e) ^ 2) : Nat.card (Phan.B12 E p e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
  obtain ⟨eq⟩ := nonempty_sl2_mulEquiv_su_two (K := E) (p := p) (f := e) hK
  have h1 : Nat.card (Phan.B12 E p e) = Nat.card (Su E p e 2) := by
    rw [Phan.B12]
    exact (Nat.card_congr (MonoidHom.ofInjective (embSUid_injective
      (unitaryInvolution E p e) 2)).toEquiv).symm
  rw [h1, ← Nat.card_congr eq.toEquiv, card_specialLinearGroup_fin_two, card_fixedSubfield hK]

end NatCard

end CFSG.ClassicalInvolution.ModelFacts.Levi
