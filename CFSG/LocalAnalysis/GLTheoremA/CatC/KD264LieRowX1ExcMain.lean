module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus3

variable (τ : Tag) (L : Type) [Field L]

@[expose] def torus3 : Subgroup (ModGL τ L) where
  carrier := {x | ∃ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) ∧ x = rootDiagUnit τ a}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, fun i => ?_, (rootDiagUnit_mul a b).symm⟩
    rw [Pi.mul_apply, mul_pow, ha i, hb i, one_mul]
  one_mem' := ⟨1, fun i => by simp, rootDiagUnit_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, fun i => ?_, (rootDiagUnit_inv a).symm⟩
    rw [Pi.inv_apply, inv_pow, ha i, inv_one]

variable {τ L}

@[expose] noncomputable def psiG (τ : Tag) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin τ.rank → ZMod 3) →* ModGL τ L where
  toFun u := rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u))
  map_one' := by
    have : thetaTupleG τ ζ (Multiplicative.toAdd (1 : Multiplicative (Fin τ.rank → ZMod 3))) = 1 := by
      funext i
      exact theta_zero' ζ
    rw [this]
    exact rootDiagUnit_one
  map_mul' u v := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    exact theta_add' hζ _ _

theorem psiG_apply {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin τ.rank → ZMod 3)) :
    psiG (L := L) τ hζ u = rootDiagUnit τ (thetaTupleG τ ζ (Multiplicative.toAdd u)) := rfl

theorem psiG_injective {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Function.Injective (psiG (L := L) τ hζ) := by
  intro u v h
  have h' := CFSG.LieType.Chevalley.rootDiagUnit_injective h
  have : Multiplicative.toAdd u = Multiplicative.toAdd v := by
    funext i
    exact theta_injective' hζ' (congrFun h' i)
  exact this

theorem psiG_mem_torus3 {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin τ.rank → ZMod 3)) :
    psiG (L := L) τ hζ u ∈ torus3 τ L :=
  ⟨thetaTupleG τ ζ (Multiplicative.toAdd u), thetaTupleG_pow_three hζ _, rfl⟩

theorem range_psiG {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    (psiG (L := L) τ hζ).range = torus3 τ L := by
  refine le_antisymm (fun x ⟨u, hu⟩ => hu ▸ psiG_mem_torus3 hζ u) ?_
  rintro _ ⟨a, ha, rfl⟩
  choose m hm using fun i =>
    CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζ' (ha i)
  refine ⟨Multiplicative.ofAdd m, ?_⟩
  rw [psiG_apply]
  congr 1
  funext i
  exact hm i

theorem card_torus3 {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Nat.card (torus3 τ L) = 3 ^ τ.rank := by
  rw [← range_psiG hζ hζ', Nat.card_congr (MonoidHom.ofInjective (psiG_injective hζ hζ')).toEquiv.symm,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin τ.rank → ZMod 3) ≃ _)]
  simp [Nat.card_fun, ZMod.card]

theorem isElemAbelian_torus3 : IsElemAbelian 3 (torus3 τ L) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
    apply Subtype.ext
    show rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ b * rootDiagUnit τ a
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  · rintro _ ⟨a, ha, rfl⟩
    have h3 : a ^ 3 = 1 := funext fun i => by simpa using ha i
    have := map_pow (rootDiagUnitHom τ L) a 3
    rw [h3, map_one] at this
    exact this.symm

end Torus3

section Rank2

variable {τ : Tag} {L : Type} [Field L]

theorem ofAdd_smul_zmod3 (a : ZMod 3) (x : Fin τ.rank → ZMod 3) :
    Multiplicative.ofAdd (a • x) = Multiplicative.ofAdd x ^ a.val := by
  rw [← ofAdd_nsmul]
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact Nat.cast_smul_eq_nsmul (ZMod 3) a.val x

theorem exists_rank_two_subgroup {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u v : Fin τ.rank → ZMod 3)
    (hind : Function.Injective fun ab : Fin 2 → ZMod 3 => ab 0 • u + ab 1 • v) :
    ∃ U : Subgroup (ModGL τ L), U ≤ torus3 τ L ∧ Nat.card U = 9 ∧
      ∀ x : ModGL τ L, x ∈ Subgroup.centralizer (U : Set (ModGL τ L)) ↔
        (x ∈ Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ u)} : Set (ModGL τ L)) ∧
          x ∈ Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L))) := by
  classical
  let lin : (Fin 2 → ZMod 3) →+ (Fin τ.rank → ZMod 3) :=
    { toFun := fun ab => ab 0 • u + ab 1 • v
      map_zero' := by simp
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul]; abel }
  let φU : Multiplicative (Fin 2 → ZMod 3) →* ModGL τ L :=
    (psiG τ hζ).comp (AddMonoidHom.toMultiplicative lin)
  set du : ModGL τ L := psiG (L := L) τ hζ (Multiplicative.ofAdd u) with hdu_def
  set dv : ModGL τ L := psiG (L := L) τ hζ (Multiplicative.ofAdd v) with hdv_def
  have hdu : du = rootDiagUnit τ (thetaTupleG τ ζ u) := rfl
  have hdv : dv = rootDiagUnit τ (thetaTupleG τ ζ v) := rfl
  have hφU : ∀ ab : Fin 2 → ZMod 3, φU (Multiplicative.ofAdd ab) =
      du ^ (ab 0).val * dv ^ (ab 1).val := by
    intro ab
    show psiG (L := L) τ hζ (Multiplicative.ofAdd (ab 0 • u + ab 1 • v)) = _
    rw [ofAdd_add, map_mul, ofAdd_smul_zmod3, ofAdd_smul_zmod3, map_pow, map_pow]
  have hinj : Function.Injective φU := by
    intro x y hxy
    have h1 := psiG_injective hζ hζ' hxy
    have h2 : lin (Multiplicative.toAdd x) = lin (Multiplicative.toAdd y) := h1
    exact hind h2
  have hv1 : (1 : ZMod 3).val = 1 := by decide
  have hduU : du ∈ φU.range := ⟨Multiplicative.ofAdd (Pi.single 0 1), by
    rw [hφU]; simp [hv1]⟩
  have hdvU : dv ∈ φU.range := ⟨Multiplicative.ofAdd (Pi.single 1 1), by
    rw [hφU]; simp [hv1]⟩
  refine ⟨φU.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact psiG_mem_torus3 hζ _
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ _)]
    simp [Nat.card_fun, ZMod.card]
  · intro x
    rw [← hdu, ← hdv]
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨h du hduU, h dv hdvU⟩
    · rintro ⟨h1, h2⟩ y ⟨z, rfl⟩
      rw [show φU z = du ^ (Multiplicative.toAdd z 0).val * dv ^ (Multiplicative.toAdd z 1).val from
        hφU (Multiplicative.toAdd z)]
      have c1 : Commute du x := h1
      have c2 : Commute dv x := h2
      exact Commute.mul_left (c1.pow_left _) (c2.pow_left _)

end Rank2

section Assembly

@[expose] def ExcGood (τ : Tag) (u v : Fin τ.rank → ZMod 3) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup τ L 5), S.D.q = 2 → S.IsAlgebraic →
    (∀ γ, IsRoot τ γ → S.ρ γ = -γ) → ∀ ζ : Lˣ, ζ ^ 3 = 1 → orderOf ζ = 3 →
    (∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ∈ S.D.torus) →
      ∃ J : Subgroup (ModGL τ L),
        CFSG.Open.IsSubnormal J (S.Γ ⊓
          Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ u)} : Set (ModGL τ L)) ⊓
          Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L))) ∧
        CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)

@[expose] def ExcMaxRank (τ : Tag) (w : WeylGroup τ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup τ L 5) (Fr : L →+* L)
    (K : Type) [Field K] [Finite K], Nat.card K = 2 → Nonempty (adjointGroup τ K ≃* S.Γ) →
    (∀ c, Fr c = c ^ 2) → S.D.q = 2 → S.D.Φ = Units.map (entrywiseHom Fr) →
    S.D.n = canonicalRep (coxeterSystem τ) L w →
    (∀ P : Subgroup (ModGL τ L), P ≤ S.D.model → IsPGroup 3 P → P ≤ S.Γ) →
      torus3 τ L ≤ S.Γ ∧ ∀ E : Subgroup (ModGL τ L), E ≤ S.Γ → IsElemAbelian 3 E →
        3 ^ τ.rank ≤ Nat.card E →
          ∃ m ∈ S.D.model, E.map (MulAut.conj m).toMonoidHom = torus3 τ L

theorem natCast_three_ne_zero_of_q_two {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hq2 : S.D.q = 2) : ((3 : ℕ) : L) ≠ 0 := by
  have h2 : ((2 : ℕ) : L) = 0 := by
    have := S.hqpow.2
    rwa [hq2] at this
  have h3 : ((3 : ℕ) : L) = 1 := by
    push_cast at h2 ⊢
    linear_combination h2
  rw [h3]
  exact one_ne_zero

theorem exists_cube_root_unity (L : Type) [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) :
    ∃ ζ : Lˣ, ζ ^ 3 = 1 ∧ orderOf ζ = 3 := by
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hζu' : IsPrimitiveRoot hu.unit 3 := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact ⟨hu.unit, hζu'.pow_eq_one, hζu'.eq_orderOf.symm⟩

theorem exc_conclusion {τ : Tag} (d : ℕ) (hτ : (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (w : WeylGroup τ) (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x)
    (u v : Fin τ.rank → ZMod 3)
    (hind : Function.Injective fun ab : Fin 2 → ZMod 3 => ab 0 • u + ab 1 • v)
    (hgood : ExcGood τ u v) (hmax : ExcMaxRank τ w)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K))
    (hinn : ∀ α : MulAut ↥(adjointGroup τ K),
      α ∈ (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range)
    {C₀ : Type} [Group C₀] [Finite C₀] (e : C₀ ≃* ↥(adjointGroup τ K)) :
    X1Concl C₀ := by
  classical
  obtain ⟨L, _, _, _, _, S, Fr, hFr, hq2, hΦ, hn, hAlg, hρ, ⟨φ⟩, h3sub⟩ :=
    exists_exc_setup d hτ w K hK hperf
  have hρ' : ∀ γ, IsRoot τ γ → S.ρ γ = -γ := fun γ hγ => (hρ γ hγ).trans (hw γ)
  obtain ⟨hVΓ, hconj⟩ := hmax L S Fr K hK ⟨φ⟩ hFr hq2 hΦ hn h3sub
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root_unity L (natCast_three_ne_zero_of_q_two S hq2)
  have hTor : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ∈ S.D.torus :=
    fun a ha => rootDiagUnit_mem_langTorus S Fr hFr w hΦ hn hw ha
  obtain ⟨J, hJ, hJq, hJ3⟩ := hgood L S hq2 hAlg hρ' ζ hζ hζ' hTor
  obtain ⟨U, hUV, hUcard, hUcent⟩ := exists_rank_two_subgroup (L := L) (τ := τ) hζ hζ' u v hind
  have hΓM : ∀ m ∈ S.D.model, ∀ x ∈ S.Γ, m * x * m⁻¹ ∈ S.Γ := by
    intro m hm x hx
    have := Subgroup.normalizer_commutator_ge_left (H₁ := S.D.model) (H₂ := S.D.model) hm
    exact (Subgroup.mem_normalizer_iff.1 this x).1 hx
  have hJ' : CFSG.Open.IsSubnormal J (S.Γ ⊓ Subgroup.centralizer (U : Set (ModGL τ L))) := by
    have heq : S.Γ ⊓ Subgroup.centralizer (U : Set (ModGL τ L)) =
        S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ u)} : Set (ModGL τ L)) ⊓
          Subgroup.centralizer ({rootDiagUnit τ (thetaTupleG τ ζ v)} : Set (ModGL τ L)) := by
      ext x
      simp only [Subgroup.mem_inf]
      rw [hUcent]
      tauto
    rwa [heq]
  exact exc_final S.Γ S.D.model (torus3 τ L) U J τ.rank (e.trans φ) hΓM hVΓ isElemAbelian_torus3
    (card_torus3 hζ hζ') hconj hUV hUcard hJ' hJq hJ3
    (fun A _ α _ => mulAut_mem_range_conj_of_equiv e hinn α)
    (conj_injective_of_equiv e center_adjointGroup_eq_bot)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
