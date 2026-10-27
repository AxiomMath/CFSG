module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIReeSocleBasic
public import CFSG.Walter.Ree.Model.Fusion
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_socle_psi_structure (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (2 * m + 1)) :
    ∃ ψ : SL2 K →* ReeTag.G2.reeGamma K m,
      (∀ b : K, (ψ (uSL b) : ModGL ReeTag.G2.tag K) = smallReeU m K 0 b 0) ∧
      (∀ w₀ : WeylGroup ReeTag.G2.tag, (∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
          (coxeterSystem ReeTag.G2.tag).length w₀) →
        (ψ WSL : ModGL ReeTag.G2.tag K) = canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀) ∧
      (∀ r : Kˣ, (ψ (HSL r) : ModGL ReeTag.G2.tag K) = smallReeH m K (r ^ (3 + 3 * 3 ^ m))) ∧
      (∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) ∧ ψ.ker = center (SL2 K) ∧
      CFSG.Walter.JT.IsInternalDirectProduct
        (zpowers (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : ReeTag.G2.reeGamma K m)) ψ.range
        (centralizer {(⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : ReeTag.G2.reeGamma K m)}) ∧
      (∃ eB : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* ψ.range,
        ∀ g, (eB (QuotientGroup.mk g) : ReeTag.G2.reeGamma K m) = ψ g) ∧
      IsSimpleGroup ψ.range ∧ ∃ x y : ψ.range, x * y ≠ y * x := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set ψ : SL2 K →* ReeTag.G2.reeGamma K m :=
    (smallReePsi K m).codRestrict _ (smallReePsi_mem_reeGamma hK hw₀) with hψ
  have hψ1 : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1 := fun g => by
    rw [← smallReePsi_eq_one_iff hK hw₀ g]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : ψ.ker = center (SL2 K) := by
    rw [hψ, MonoidHom.ker_codRestrict, smallReePsi_ker hK hw₀]
  have hrange : (smallReePsi K m).range.subgroupOf (ReeTag.G2.reeGamma K m) = ψ.range := by
    ext x
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  set t : ReeTag.G2.reeGamma K m := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ with ht
  have hsup : zpowers t ⊔ ψ.range = centralizer {t} := by
    rw [← hrange]
    exact (centralizer_eq_zpowers_sup hK hw₀).symm
  have hdisj : Disjoint (zpowers t) ψ.range := by
    rw [Subgroup.disjoint_def]
    intro x hx hxB
    have h1 : (x : ModGL ReeTag.G2.tag K) ∈ zpowers (smallReeH m K (-1)) := by
      have := mem_map_of_mem (ReeTag.G2.reeGamma K m).subtype hx
      rwa [MonoidHom.map_zpowers] at this
    have h2 : (x : ModGL ReeTag.G2.tag K) ∈ (smallReePsi K m).range := by
      obtain ⟨g, rfl⟩ := hxB
      exact ⟨g, rfl⟩
    exact Subtype.ext (Subgroup.disjoint_def.mp (disjoint_zpowers_range hK hw₀) h1 h2)
  have hcent : zpowers t ≤ centralizer (ψ.range : Set (ReeTag.G2.reeGamma K m)) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp (smallReePsi_mem hK hw₀ g)).2)
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr hK2) (Or.inr hK3)
  set eB : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans (QuotientGroup.quotientKerEquivRange ψ)
    with heB
  have hBnab : ∃ x y : ψ.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K hK2 hK3
    refine ⟨eB x, eB y, fun h => hxy (eB.injective ?_)⟩
    rw [map_mul, map_mul, h]
  exact ⟨ψ, fun b => smallReePsi_uSL b, fun w₁ hw₁ => smallReePsi_WSL hw₁,
    fun r => smallReePsi_HSL hK r, hψ1, hker, ⟨hsup, hdisj, hcent⟩, ⟨eB, fun g => rfl⟩,
    eB.symm.isSimpleGroup, hBnab⟩

theorem ree_involution_fusion (hK : Nat.card K = 3 ^ (2 * m + 1))
    (x : ReeTag.G2.reeGamma K m) (hx : orderOf x = 2) :
    ∃ y : ReeTag.G2.reeGamma K m, y * x * y⁻¹ = ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hg, hgx⟩ := (small_Ree_prime_field_involution_fusion m K hK w₀ hw₀).2.2.2.2.2 x
    x.2 (by rw [Subgroup.orderOf_coe, hx])
  exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩

theorem reeGammaFieldAut_smallReeH (hK : Nat.card K = 3 ^ (2 * m + 1)) (σ : K ≃+* K) :
    ReeTag.G2.reeGammaFieldAut K m σ ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ =
      ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ := by
  apply Subtype.ext
  rw [ReeTag.coe_reeGammaFieldAut]
  have h1 : Units.map σ.toRingHom.toMonoidHom (-1 : Kˣ) = -1 := Units.ext (by simp)
  change Units.map (entrywiseHom σ.toRingHom) (smallReeTorusElt m K (-1)) =
    smallReeTorusElt m K (-1)
  rw [smallReeTorusElt, map_mul, CFSG.LieType.Chevalley.entrywise_torusElt,
    CFSG.LieType.Chevalley.entrywise_torusElt, map_pow, h1]

omit [CharP K ReeTag.G2.prime] in
theorem ree_socle_source (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (2 * m + 1)) {L : Type} [Group L]
    (eL : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) :
    p = 3 ∧ f = 2 * m + 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  have hq27 : 27 ≤ 3 ^ (2 * m + 1) :=
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr hK2) (Or.inr hK3)
  have : IsSimpleGroup L := eL.isSimpleGroup
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K hK2 hK3
    refine ⟨eL.symm x, eL.symm y, fun h => hxy (eL.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  have hX : StatedClassicalModel (L ⧸ center L) .PSL 2 3 (2 * m + 1) := by
    refine ⟨⟨Nat.prime_three, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(eZ.trans eL).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  obtain ⟨h1, h2, h3⟩ :=
    UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
  rcases hsrc with hpsl | e7 | h322
  · rcases h1 p f hp2 hpsl with ⟨⟨-, hp, hf⟩, -⟩ | ⟨⟨h32, -⟩, -⟩
    · exact ⟨hp.symm, hf.symm, hpsl, h2, h3⟩
    · omega
  · exact (not_nonempty_iff.mpr h2 e7).elim
  · exact (h3 h322).elim

theorem ree_socle_outer (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (2 * m + 1))
    {t : ReeTag.G2.reeGamma K m} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH m K (-1))
    {ψ : SL2 K →* ReeTag.G2.reeGamma K m}
    (hIDP : CFSG.Walter.JT.IsInternalDirectProduct (zpowers t) ψ.range (centralizer {t}))
    (hZ : center (ReeTag.G2.reeGamma K m) = ⊥) :
    let π := QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m))
    let Mt := centralizer {MulAut.conj t}
    let Nt := (centralizer {t}).map MulAut.conj
    let Fld := ReeTag.G2.reeGammaFld K m
    CFSG.Walter.JT.IsInternalDirectProduct ((zpowers t).map MulAut.conj)
        (ψ.range.map MulAut.conj) Nt ∧
      (∀ β : MulAut (ReeTag.G2.reeGamma K m), β ∈ Mt ↔ β t = t) ∧
      Mt ⊓ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m) = Nt ∧
      Mt.map π = ⊤ ∧ Mt ⊓ π.ker = Nt ∧
      (∀ (σ : K ≃+* K) (g : ReeTag.G2.reeGamma K m),
        ((ReeTag.G2.reeGammaFieldAut K m σ g : ReeTag.G2.reeGamma K m) :
          ModGL ReeTag.G2.tag K) = Units.map (entrywiseHom σ.toRingHom) (g : ModGL _ K)) ∧
      Nat.card Fld = 2 * m + 1 ∧ Nat.card (Fld.map π) = 2 * m + 1 ∧ Fld ≤ Mt ∧
      (∃ (R : Subgroup (Outer (ReeTag.G2.reeGamma K m)))
        (χ : Outer (ReeTag.G2.reeGamma K m) →* (K ≃+* K)), χ.ker = R ∧
        (∀ σ : K ≃+* K, χ (QuotientGroup.mk (ReeTag.G2.reeGammaFieldAut K m σ)) = σ) ∧
        R.Normal ∧ IsPGroup 3 R ∧ R.IsComplement' (Fld.map π)) ∧
      ∀ R : Subgroup (Outer (ReeTag.G2.reeGamma K m)), R.Normal →
        R.IsComplement' (Fld.map π) →
        let Tt := Mt ⊓ R.comap π
        Nt ≤ Tt ∧ (Nt.subgroupOf Tt).Normal ∧ (Tt.subgroupOf Mt).Normal ∧
          Tt.map π = R ∧ Tt ⊓ π.ker = Nt ∧ Tt ⊓ Fld = ⊥ ∧
          (∃ _ : (Nt.subgroupOf Tt).Normal, ∃ e : Tt ⧸ Nt.subgroupOf Tt ≃* R,
            ∀ v : Tt, (e (QuotientGroup.mk v) : Outer (ReeTag.G2.reeGamma K m)) = π v) ∧
          ∀ β ∈ Mt, ∃! vτ : Tt × Fld, (vτ.1 : MulAut (ReeTag.G2.reeGamma K m)) * vτ.2 = β := by
  have htt : t = ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ := Subtype.ext ht
  subst htt
  have hconj := conj_injective_of_center_eq_bot hZ
  have ht2 := orderOf_smallReeH_neg_one (a := m) hK
  have hfus := ree_involution_fusion (m := m) hK
  obtain ⟨hFact, hFcard, hFbar, hR, -, -⟩ := small_Ree_outer_three_kernel_field_complement m hm K hK
  have hFM : ReeTag.G2.reeGammaFld K m ≤ centralizer
      {MulAut.conj (⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ : ReeTag.G2.reeGamma K m)} := by
    rintro _ ⟨σ, rfl⟩
    rw [mem_centralizer_conj_iff hZ]
    exact reeGammaFieldAut_smallReeH hK σ
  have hFinj : Nat.card (ReeTag.G2.reeGammaFld K m) = Nat.card ((ReeTag.G2.reeGammaFld K m).map
      (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m)))) := by
    rw [hFcard, hFbar]
  have hR₀ := hR
  obtain ⟨R₀, -, -, -, hRn₀, -, hRF₀⟩ := hR₀
  obtain ⟨hMt, hinnN, hsurj, hker, -⟩ := fixed_outer_structure hZ hfus ht2 hFM hFinj hRn₀ hRF₀
  refine ⟨(isInternalDirectProduct_map_iff hconj).mpr hIDP, hMt, hinnN, hsurj, hker, hFact,
    hFcard, hFbar, hFM, hR, fun R hRn hRF => ?_⟩
  obtain ⟨-, -, -, -, hNT, hNTn, hTMn, hTmap, hTker, hTF, hfact⟩ :=
    fixed_outer_structure hZ hfus ht2 hFM hFinj hRn hRF
  exact ⟨hNT, hNTn, hTMn, hTmap, hTker, hTF, exists_quotient_mulEquiv_of_map _ hTmap hTker,
    hfact⟩

end CFSG.ComponentClassification.OutcomeLocal
