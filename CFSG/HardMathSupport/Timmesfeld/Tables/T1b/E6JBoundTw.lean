module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Open CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Stabilizer


variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem exists_eq_rootDiagUnit_compatDiag (hσ : Function.Surjective σ)
    {h : graphFixedRootGroup t K σ}
    (hA : MulAut.conj h ∈ graphFixedUnipotentStabilizer t K σ) :
    ∃ u, (h : ModGL t.tag K) = rootDiagUnit t.tag (compatDiag t σ u) := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hV
  have hB : (h : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  have hC : (graphFixedRootGroup t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
        graphFixedRootGroup t K σ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  have e : graphFixedRootGroup t K σ ⊓
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) =
        (graphFixedRootBorel t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hC, Subgroup.map_equiv_normalizer_eq,
      map_conj_graphFixedPosUnipotent hw₀]
  have hB' : (h : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← e]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  have hH : (h : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hw₀]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  have hT : (h : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  have hΓ : (h : ModGL t.tag K) ∈ twistedFixedGroup t K σ :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hF := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hΓ).2
  rw [hb, twistHom_rootDiagUnit_eq] at hF
  have hb' : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
    intro i
    have h1 := congrFun (rootDiagUnit_injective hF) (t.perm i)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq hb'
  exact ⟨u, by rw [hb, hu]⟩

theorem compatDiagAutHom_mem_stabilizer
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    compatDiagAutHom t K σ u ∈ graphFixedUnipotentStabilizer t K σ :=
  ⟨map_compatDiagAutHom_subgroupOf (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) u
      (map_conj_rootDiagUnit_graphFixedPosUnipotent (compatDiag_perm u)),
    map_compatDiagAutHom_subgroupOf (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) u
      (map_conj_rootDiagUnit_graphFixedNegUnipotent (compatDiag_perm u))⟩

end Stabilizer

section Diag

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def twDiag
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    Fin Tag.E6.rank → Kˣ :=
  compatDiag TwistTag.E6 σ.toRingHom u

theorem twDiag_mul
    (u v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    twDiag σ (u * v) = twDiag σ u * twDiag σ v :=
  compatDiag_mul u v

theorem twDiag_one : twDiag σ 1 = 1 := compatDiag_one

end Diag

section Embed


variable {K : Type} [Field K] (σ : K ≃+* K)

theorem twistedE6RootGroup_le {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6RootGroup K σ) :
    x ∈ adjointGroup TwistTag.E6.tag K :=
  (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom)
    ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom) hx)

@[expose] noncomputable def twIncl : twistedE6RootGroup K σ →* adjointGroup Tag.E6 K where
  toFun g := ⟨g.1, twistedE6RootGroup_le σ g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable abbrev twJ : Subgroup (MulAut (twistedE6RootGroup K σ)) :=
  twistedE6Inn K σ ⊔ twistedE6Diag K σ

@[expose] noncomputable def twExt (g : twistedE6RootGroup K σ)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    MulAut (adjointGroup Tag.E6 K) :=
  MulAut.conj (twIncl σ g) * rootDiagAutHom Tag.E6 K (twDiag σ u)

theorem mem_twJ_iff {α : MulAut (twistedE6RootGroup K σ)} :
    α ∈ twJ σ ↔ ∃ (g : twistedE6RootGroup K σ)
      (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ),
      α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
  constructor
  · intro hα
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hα
    obtain ⟨_, ⟨g, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := hα
    exact ⟨g, u, rfl⟩
  · rintro ⟨g, u, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨u, rfl⟩)

theorem conj_twIncl_eq {h : twistedE6RootGroup K σ}
    {v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hv : (h : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v)) :
    MulAut.conj (twIncl σ h) = rootDiagAutHom Tag.E6 K (twDiag σ v) :=
  MulEquiv.ext fun y => Subtype.ext (by
    have hv' : ((twIncl σ h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 (twDiag σ v) := hv
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hv']
    exact (coe_rootDiagAut (twDiag σ v) y).symm)

theorem conj_eq_compatDiagAutHom {h : twistedE6RootGroup K σ}
    {v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hv : (h : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom v)) :
    MulAut.conj h = compatDiagAutHom TwistTag.E6 K σ.toRingHom v :=
  MulEquiv.ext fun y => Subtype.ext (by
    rw [MulAut.conj_apply, coe_compatDiagAutHom]
    change (h : ModGL TwistTag.E6.tag K) * y * (h : ModGL TwistTag.E6.tag K)⁻¹ = _
    rw [hv])

theorem twExt_eq_of_eq {g g' : twistedE6RootGroup K σ}
    {u u' : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (h : MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u =
      MulAut.conj g' * compatDiagAutHom TwistTag.E6 K σ.toRingHom u') :
    twExt σ g u = twExt σ g' u' := by
  have hc : MulAut.conj (g'⁻¹ * g) = compatDiagAutHom TwistTag.E6 K σ.toRingHom (u' * u⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h,
      mul_inv_cancel_right]
  obtain ⟨v, hv⟩ := exists_eq_rootDiagUnit_compatDiag σ.surjective
    (hc ▸ compatDiagAutHom_mem_stabilizer (u' * u⁻¹))
  have hvu : v = u' * u⁻¹ :=
    compatDiagAutHom_injective ((conj_eq_compatDiagAutHom σ hv).symm.trans hc)
  have hC : MulAut.conj (twIncl σ (g'⁻¹ * g)) = rootDiagAutHom Tag.E6 K (twDiag σ v) :=
    conj_twIncl_eq σ hv
  have hg : twIncl σ g = twIncl σ g' * twIncl σ (g'⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  have hvu' : twDiag σ v * twDiag σ u = twDiag σ u' := by
    rw [← twDiag_mul, hvu, inv_mul_cancel_right]
  unfold twExt
  rw [hg, map_mul, hC, mul_assoc, ← map_mul, hvu']

@[expose] noncomputable def twExtFun (α : twJ σ) : MulAut (adjointGroup Tag.E6 K) :=
  twExt σ (mem_twJ_iff σ |>.1 α.2).choose (mem_twJ_iff σ |>.1 α.2).choose_spec.choose

theorem twExtFun_eq (α : twJ σ) {g : twistedE6RootGroup K σ}
    {u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hα : (α : MulAut (twistedE6RootGroup K σ)) =
      MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) :
    twExtFun σ α = twExt σ g u :=
  twExt_eq_of_eq σ ((mem_twJ_iff σ |>.1 α.2).choose_spec.choose_spec.symm.trans hα)

theorem rootDiagAutHom_twIncl
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (g : twistedE6RootGroup K σ) :
    rootDiagAutHom Tag.E6 K (twDiag σ u) (twIncl σ g) =
      twIncl σ (compatDiagAutHom TwistTag.E6 K σ.toRingHom u g) :=
  Subtype.ext (by
    change rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        (g : ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
      ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K)
    rw [coe_compatDiagAutHom])

@[expose] noncomputable def twExtHom : twJ σ →* MulAut (adjointGroup Tag.E6 K) where
  toFun := twExtFun σ
  map_one' := by
    rw [twExtFun_eq σ 1 (g := 1) (u := 1) (by rw [Subgroup.coe_one, map_one, map_one, mul_one]),
      twExt, map_one, map_one, twDiag_one, map_one, mul_one]
  map_mul' α β := by
    obtain ⟨g₁, u₁, h₁⟩ := (mem_twJ_iff σ).1 α.2
    obtain ⟨g₂, u₂, h₂⟩ := (mem_twJ_iff σ).1 β.2
    have hαβ : ((α * β : twJ σ) : MulAut (twistedE6RootGroup K σ)) =
        MulAut.conj (g₁ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u₁ g₂) *
          compatDiagAutHom TwistTag.E6 K σ.toRingHom (u₁ * u₂) := by
      rw [Subgroup.coe_mul, h₁, h₂, map_mul, map_mul]
      calc MulAut.conj g₁ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u₁ *
            (MulAut.conj g₂ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u₂) =
          MulAut.conj g₁ * (compatDiagAutHom TwistTag.E6 K σ.toRingHom u₁ * MulAut.conj g₂) *
            compatDiagAutHom TwistTag.E6 K σ.toRingHom u₂ := by group
        _ = _ := by rw [mulAut_mul_conj]; group
    rw [twExtFun_eq σ _ hαβ, twExtFun_eq σ α h₁, twExtFun_eq σ β h₂]
    unfold twExt
    rw [map_mul, map_mul, twDiag_mul, map_mul, ← rootDiagAutHom_twIncl]
    calc MulAut.conj (twIncl σ g₁) *
          MulAut.conj (rootDiagAutHom Tag.E6 K (twDiag σ u₁) (twIncl σ g₂)) *
          (rootDiagAutHom Tag.E6 K (twDiag σ u₁) * rootDiagAutHom Tag.E6 K (twDiag σ u₂)) =
        MulAut.conj (twIncl σ g₁) *
          (MulAut.conj (rootDiagAutHom Tag.E6 K (twDiag σ u₁) (twIncl σ g₂)) *
            rootDiagAutHom Tag.E6 K (twDiag σ u₁)) *
          rootDiagAutHom Tag.E6 K (twDiag σ u₂) := by group
      _ = _ := by rw [← mulAut_mul_conj]; group

theorem twExtHom_apply (α : twJ σ) {g : twistedE6RootGroup K σ}
    {u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    (hα : (α : MulAut (twistedE6RootGroup K σ)) =
      MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) :
    twExtHom σ α = twExt σ g u :=
  twExtFun_eq σ α hα

theorem twExtHom_mem_diagJ (α : twJ σ) : twExtHom σ α ∈ diagJ K := by
  obtain ⟨g, u, hα⟩ := (mem_twJ_iff σ).1 α.2
  rw [twExtHom_apply σ α hα]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem twExtHom_injective : Function.Injective (twExtHom σ) := by
  rw [injective_iff_map_eq_one]
  intro α hα1
  obtain ⟨g, u, hα⟩ := (mem_twJ_iff σ).1 α.2
  rw [twExtHom_apply σ α hα] at hα1
  apply Subtype.ext
  rw [hα]
  refine MulEquiv.ext fun y => ?_
  have h := congrArg (fun β : MulAut (adjointGroup Tag.E6 K) => β (twIncl σ y)) hα1
  simp only [twExt, MulAut.mul_apply, MulAut.one_apply] at h
  rw [rootDiagAutHom_twIncl, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h
  have h2 := congrArg Subtype.val h
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  exact Subtype.ext h2

end Embed

theorem e6JBoundTw : E6JBoundTw := by
  intro r f _ _ h3 K _ _ hK
    σ _
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_sq_sub_one h3
  have hJ := e6JBoundUntw K h3K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  calc CFSG.Open.pRank 3 (twistedE6Inn K σ ⊔ twistedE6Diag K σ) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (twJ σ)) := pRank_eq_pRank_top_subgroup _
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (diagJ K)) :=
        pRank_top_le_of_injective (by norm_num)
          ((twExtHom σ).codRestrict (diagJ K) (twExtHom_mem_diagJ σ))
          (fun a b h => twExtHom_injective σ (congrArg Subtype.val h))
    _ = CFSG.Open.pRank 3 (diagJ K) := (pRank_eq_pRank_top_subgroup _).symm
    _ ≤ 6 := hJ

theorem e6RankUpper :
    E6RankUpper :=
  e6RankUpper_of_J e6JBoundUntw e6JBoundTw

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
