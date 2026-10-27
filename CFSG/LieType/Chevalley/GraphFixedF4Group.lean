module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_frobenius_of_ringChar (k L : Type) [Field k] [Finite k] (hk : ringChar k = 2)
    [Field L] [Algebra k L] : ∃ Fr : L →+* L, ∀ c, Fr c = c ^ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := ringChar.of_eq hk
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  refine ⟨iterateFrobenius L 2 n, fun c => ?_⟩
  rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hn]

theorem eq_of_f4OrbitUnit
    {K : Type} [Field K] {M : Type*} [Group M]
    {Φ Φ' : twistedFixedGroup TwistTag.E6 K (RingHom.id K) →* M}
    (hx : ∀ j c (hx : f4OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
      Φ ⟨_, hx⟩ = Φ' ⟨_, hx⟩)
    (hy : ∀ j c (hy : f4OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
      Φ ⟨_, hy⟩ = Φ' ⟨_, hy⟩)
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) : Φ g = Φ' g := by
  set H := MonoidHom.eqLocus Φ Φ'
  have hle : twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≤
      H.map (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subtype := by
    conv_lhs => rw [twistedFixedGroup_id_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, c, rfl | rfl⟩
    · exact ⟨⟨_, f4OrbitXUnit_mem j c⟩, hx j c _, rfl⟩
    · exact ⟨⟨_, f4OrbitYUnit_mem j c⟩, hy j c _, rfl⟩
  obtain ⟨h, hh, hgh⟩ := hle g.2
  rw [show g = h from Subtype.ext hgh.symm]
  exact hh

theorem even_E6_pure_graph_fixed_group_exact_F4
    (K : Type) [Field K] (hK : ringChar K = 2) :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) =
      graphFixedRootGroup TwistTag.E6 K (RingHom.id K) ∧
    (∀ g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K), ∀ v ∈ e6GraphFixedModule K,
      (g : Module.End K (RootModule TwistTag.E6.tag K)) v ∈ e6GraphFixedModule K) ∧
    (∀ g : twistedFixedGroup TwistTag.E6 K (RingHom.id K),
      f4ToE6Module K ∘ₗ (e6FixedToF4 K g : Module.End K (RootModule Tag.F4 K)) =
        ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) ∘ₗ
          f4ToE6Module K) ∧
    (∀ (j : Fin Tag.F4.rank) (c : K),
      f4OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ∧
      f4OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ∧
      ((f4OrbitXUnit K j c : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) = f4OrbitX K j c ∧
      ((f4OrbitYUnit K j c : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) = f4OrbitY K j c) ∧
    (∃ Ψ : twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≃* adjointGroup Tag.F4 K,
      (∀ g, (Ψ g : ModGL Tag.F4 K) = e6FixedToF4 K g) ∧
      (∀ (j : Fin Tag.F4.rank) (c : K)
        (hx : f4OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
        (Ψ ⟨_, hx⟩ : ModGL Tag.F4 K) = xUnit Tag.F4 K j c) ∧
      (∀ (j : Fin Tag.F4.rank) (c : K)
        (hy : f4OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
        (Ψ ⟨_, hy⟩ : ModGL Tag.F4 K) = yUnit Tag.F4 K j c) ∧
      ∀ Φ : twistedFixedGroup TwistTag.E6 K (RingHom.id K) →* ModGL Tag.F4 K,
        (∀ (j : Fin Tag.F4.rank) (c : K)
          (hx : f4OrbitXUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
          Φ ⟨_, hx⟩ = xUnit Tag.F4 K j c) →
        (∀ (j : Fin Tag.F4.rank) (c : K)
          (hy : f4OrbitYUnit K j c ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)),
          Φ ⟨_, hy⟩ = yUnit Tag.F4 K j c) →
        ∀ g, Φ g = Ψ g) ∧
    (∀ (L : Type) [Field L] (f : K →+* L),
      (∀ g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K),
        baseChangeGL f g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L)) ∧
      (∀ g ∈ adjointGroup Tag.F4 K, baseChangeGL f g ∈ adjointGroup Tag.F4 L) ∧
      ∀ (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K))
        (g' : twistedFixedGroup TwistTag.E6 L (RingHom.id L)),
        (g' : ModGL TwistTag.E6.tag L) = baseChangeGL f g →
          e6FixedToF4 L g' = baseChangeGL f (e6FixedToF4 K g)) ∧
    (∀ σ : K ≃+* K,
      (∀ g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K),
        Units.map (entrywiseHom σ.toRingHom) g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) ∧
      ∀ g g' : twistedFixedGroup TwistTag.E6 K (RingHom.id K),
        (g' : ModGL TwistTag.E6.tag K) = Units.map (entrywiseHom σ.toRingHom) g →
          e6FixedToF4 K g' = Units.map (entrywiseHom σ.toRingHom) (e6FixedToF4 K g)) ∧
    ∀ (k : Type) [Field k] [Finite k], ringChar k = 2 →
      ∀ (L : Type) [Field L] [Algebra k L] [IsAlgClosure k L],
        (∃ Fr : L →+* L, ∀ c, Fr c = c ^ Nat.card k) ∧
        ∀ Fr : L →+* L, (∀ c, Fr c = c ^ Nat.card k) →
          twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
              (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
            (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
              (baseChangeGL (algebraMap k L)) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_ringChar hK
  have hnat : ∀ (L : Type) [Field L] (f : K →+* L)
      (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K))
      (g' : twistedFixedGroup TwistTag.E6 L (RingHom.id L)),
      (g' : ModGL TwistTag.E6.tag L) = baseChangeGL f g →
        e6FixedToF4 L g' = baseChangeGL f (e6FixedToF4 K g) := by
    intro L _ f g g' hg'
    rw [show g' = ⟨baseChangeGL f g, baseChangeGL_mem_twistedFixedGroup f g.2⟩ from
      Subtype.ext hg']
    exact e6FixedToF4_baseChangeGL f g
  refine ⟨e6_twistedFixedGroup_id_eq_graphFixedRootGroup K,
    fun g hg v hv => e6EndHom_apply_mem hg hv, f4ToE6Module_comp_e6FixedToF4,
    fun j c => ⟨f4OrbitXUnit_mem j c, f4OrbitYUnit_mem j c, e6EndHom_f4OrbitXUnit j c,
      e6EndHom_f4OrbitYUnit j c⟩,
    ⟨e6FixedF4Equiv K h2, coe_e6FixedF4Equiv h2, fun j c _ => e6FixedToF4_f4OrbitXUnit h2 j c,
      fun j c _ => e6FixedToF4_f4OrbitYUnit h2 j c, fun Φ hΦx hΦy g => ?_⟩,
    fun L _ f => ⟨fun g hg => baseChangeGL_mem_twistedFixedGroup f hg,
      fun g hg => baseChangeGL_mem_adjointGroup f hg, hnat L f⟩,
    fun σ => ⟨fun g hg => baseChangeGL_mem_twistedFixedGroup σ.toRingHom hg,
      fun g g' hg' => hnat K σ.toRingHom g g' hg'⟩,
    fun k _ _ hk L _ _ _ => ⟨exists_frobenius_of_ringChar k L hk, fun Fr hFr => ?_⟩⟩
  ·
    refine eq_of_f4OrbitUnit (Φ' := (adjointGroup Tag.F4 K).subtype.comp
      (e6FixedF4Equiv K h2).toMonoidHom) (fun j c hx => ?_) (fun j c hy => ?_) g
    · rw [hΦx j c hx]
      exact (e6FixedToF4_f4OrbitXUnit h2 j c).symm
    · rw [hΦy j c hy]
      exact (e6FixedToF4_f4OrbitYUnit h2 j c).symm
  · have := IsAlgClosure.isAlgClosed k (K := L)
    exact e6_frobenius_fixed_eq_map hk Fr hFr

end CFSG.LieType.Chevalley
