module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5LayerSurj
public import CFSG.RankThree.PartOne.KA5L.Final

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.LieType.SeitzGeneration
open scoped MatrixGroups commutatorElement

theorem exists_a5Std_data
    {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hΩ : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (n : ModGL Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n, hn⟩ • α = u • ((-1 : ℤ) • α))
    {q : TauCeti.PrimePower} (hqp : q.p = ℓ) (hqe : q.exponent = f)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) :
    ∃ Φ' : SL(6, L) ≃* SL(6, L),
      (∀ X, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) * n⁻¹ =
        a5Frame L (Φ' X)) ∧ Finite (fixSubgroup Φ') ∧ CFSG.IsQuasisimple (fixSubgroup Φ') ∧
      ∃ ρ : ((fixSubgroup Φ').map (a5Frame L)) →* Cat ⟨.twistedA 5 q, hv⟩,
        Function.Surjective ρ ∧ (∀ z ∈ ρ.ker, ∀ u : (fixSubgroup Φ').map (a5Frame L),
          z * u = u * z) ∧ Nat.card ρ.ker ∣ 6 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨k, _, _, hkc, hk⟩ := exists_isAlgClosure_subfield (L := L) (ℓ := ℓ) hf hΩ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  obtain ⟨u, hu, hu'⟩ := hact
  obtain ⟨π, hπ⟩ := exists_perm_neg_of_mem_parabolicWeylGroup hu
  have hπ' : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
      a5Root (π b) (π a) := fun a b hab => by
    rw [hu' _ (a5Root_mem_parabolicRoots hab), neg_one_zsmul, hπ]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_unitary Fr hFrbij n hn π hπ'
  have hshape' : ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
        Matrix (Fin 6) (Fin 6) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨hfin, hq, τ, hτs, hτk, hcard⟩ :=
    exists_surj_fix_unitary_six hℓ hf hk π Φ' b hshape' hqp hqe hv
  refine ⟨Φ', hΦ', hfin, hq, ?_⟩
  let π₁ : fixSubgroup Φ' →* (fixSubgroup Φ').map (a5Frame L) :=
    (a5Frame L).subgroupMap (fixSubgroup Φ')
  have hπ₁ : Function.Surjective π₁ := MonoidHom.subgroupMap_surjective _ _
  have hτker : τ.ker = Subgroup.center (fixSubgroup Φ') := Subgroup.ext fun x => hτk x
  have hker : π₁.ker ≤ τ.ker := by
    intro x hx
    have hx1 : (x : SL(6, L)) ∈ Subgroup.center SL(6, L) :=
      ker_a5Frame_le_center (MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx)))
    rw [hτker, Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (Subgroup.mem_center_iff.1 hx1 g)
  have hcent : ∀ z ∈ τ.ker, ∀ a : fixSubgroup Φ', z * a = a * z := fun z hz a => by
    rw [hτker] at hz
    exact (Subgroup.mem_center_iff.1 hz a).symm
  obtain ⟨ρ, hρs, hρc, hρd⟩ := exists_factor_of_surj π₁ hπ₁ τ hτs hker hcent
  exact ⟨ρ, hρs, hρc, hρd.trans (hτker ▸ hcard)⟩

theorem pow_six_mem_of_fixed {L : Type} [Field L] (Fr : L →+* L)
    (n : ModGL Tag.E7 L) (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X))
    {g : ModGL Tag.E7 L}
    (hgQ : g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)))
    (hg : n * Units.map (entrywiseHom Fr) g * n⁻¹ = g) :
    g ^ 6 ∈ (fixSubgroup Φ').map (a5Frame L) := by
  have hΓ : g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := Subgroup.mem_inf.2 ⟨hgQ, hg⟩
  rw [Gamma_eq_map Fr n Φ' hΦ'] at hΓ
  obtain ⟨X, hX, rfl⟩ := hΓ
  have hz := fixRho_central hX
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hz6 : (Φ' X * X⁻¹) ^ 6 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hzr, ← map_pow]
    simp only [Fintype.card_fin] at hr
    rw [hr]
    simp
  refine ⟨X ^ 6, ?_, by rw [map_pow]⟩
  refine (mem_fixSubgroup Φ').2 ?_
  rw [map_pow]
  have hc : Commute (Φ' X * X⁻¹) X := by
    have := (Subgroup.mem_center_iff.1 hz) X
    exact this.symm
  have : Φ' X = (Φ' X * X⁻¹) * X := by group
  rw [this, hc.mul_pow, hz6, one_mul]

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
