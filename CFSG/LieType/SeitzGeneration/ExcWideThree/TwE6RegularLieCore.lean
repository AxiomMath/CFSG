module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieAux
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularSA
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieSL2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieRad
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootTransport
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieHeis

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section Core

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint


local notation "θ₀" => CFSG.LieType.Chevalley.e6HighestRoot

theorem mem_map_conj_iff {Γ : Type*} [Group Γ] (H : Subgroup Γ) (g u : Γ) :
    u ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * u * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_mul {Γ : Type*} [Group Γ] (H : Subgroup Γ) (a b : Γ) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twE6InnerLineLie_core
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ) (hK3 : ringChar K ≠ 3)
    (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (D : TwLangData K σ q (twPlanePre K σ E)) (e : MulAut (twistedE6RootGroup K σ)) (heE : e ∈ E)
    (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ)
    (ha : ∃ g : ↥(twistedE6InndiagGL K σ), twistedE6InndiagConj K σ g = e ∧
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * (g : ModGL TwistTag.E6.tag K) * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0)
    (β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ) (hβ₁ : IsRoot TwistTag.E6.tag β₁)
    (hβ₂ : IsRoot TwistTag.E6.tag β₂) (hβ₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂))
    (hχ₁ : rootChar a β₁ = 1) (hχ₂ : rootChar a β₂ = 1)
    (hv₁ : D.v • permLattice TwistTag.E6.perm β₁ = -β₁)
    (hv₂ : D.v • permLattice TwistTag.E6.perm β₂ = -β₂) :
    ∃ X Xm : Subgroup (twistedE6RootGroup K σ), IsTwE6LongRootPair K σ X Xm ∧
      (∀ ε ∈ E, (twE6LongRootSL2 X Xm).map ε.toMonoidHom = twE6LongRootSL2 X Xm) ∧
      (∀ u ∈ twE6LongRootSL2 X Xm, e u = u) ∧
      ∃ R : Subgroup (twistedE6RootGroup K σ), R ≤ twE6LongRootRadical X ∧
        (∀ u ∈ R, e u = u) ∧ ¬ R ≤ X := by
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hSL2 : ∀ u : twistedE6RootGroup K σ,
      u ∈ twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ) ↔
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
          rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ₀, -θ₀} :=
    fun u => mem_twE6LongRootSL2_std_iff hpr hf1 hK3 K hK' σ hσ' u
  have hRad : ∀ u : twistedE6RootGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        rootSpan TwistTag.E6.tag (AlgebraicClosure K)
          (parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0)) →
        u ∈ twE6LongRootRadical (TwE6LongRoot.stdX σ) :=
    fun u hu => (mem_twE6LongRootRadical_std_iff K σ u).2 hu
  have hrad : TwistTag.E6.orbitUnion TwE6LongRoot.J0 = e6LeviNodes := by
    rw [orbitUnion_J0_eq]
    rfl
  obtain ⟨g, hge, hga⟩ := ha
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set Fr : L →+* L := iterateFrobenius L (ringChar K) f with hFrdef
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hFrEq : D.Fr = Fr := RingHom.ext fun c => by rw [D.hFr, hFrc, hqf]
  have hg0 : twistHom TwistTag.E6 L Fr D.g0 =
      D.g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L D.v := by
    have := D.hg0
    rwa [hFrEq] at this
  have hcmem : baseChangeGL ι D.c ∈ twistedFixedGroup TwistTag.E6 L Fr :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hpr hf1 hK' σ hσ' Fr hFrc
      (Subgroup.mem_map.2 ⟨D.c, D.hcI, rfl⟩)
  obtain ⟨hcA, hcF⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hcmem
  obtain ⟨g0c, hg0cdef⟩ : ∃ g0c : ModGL TwistTag.E6.tag L, g0c = (baseChangeGL ι D.c)⁻¹ * D.g0 :=
    ⟨_, rfl⟩
  have hg0cA : g0c ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hg0cdef]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcA) D.hg0C
  have hg0cF : twistHom TwistTag.E6 L Fr g0c =
      g0c * canonicalRep (coxeterSystem TwistTag.E6.tag) L D.v := by
    rw [hg0cdef, map_mul, map_inv, hcF, hg0]
    group
  have hdiag : ∀ x ∈ twPlanePre K σ E, ∃ d ∈ torusGroup TwistTag.E6.tag L,
      baseChangeGL ι x = g0c * d * g0c⁻¹ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (D.hc x hx)
    refine ⟨y, ((mem_twistedTorusOf).1 hy).1, ?_⟩
    have hyx' : D.g0 * y * D.g0⁻¹ = baseChangeGL ι D.c * baseChangeGL ι x * (baseChangeGL ι D.c)⁻¹ := by
      have := hyx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] at this
      exact this
    rw [hg0cdef]
    calc baseChangeGL ι x = (baseChangeGL ι D.c)⁻¹ * (baseChangeGL ι D.c * baseChangeGL ι x *
          (baseChangeGL ι D.c)⁻¹) * baseChangeGL ι D.c := by group
      _ = (baseChangeGL ι D.c)⁻¹ * (D.g0 * y * D.g0⁻¹) * baseChangeGL ι D.c := by rw [hyx']
      _ = (baseChangeGL ι D.c)⁻¹ * D.g0 * y * ((baseChangeGL ι D.c)⁻¹ * D.g0)⁻¹ := by group
  have hgd : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) =
      g0c * rootDiagUnit TwistTag.E6.tag a * g0c⁻¹ := by
    have : baseChangeGL ι (D.c * (g : ModGL TwistTag.E6.tag K) * D.c⁻¹ : ModGL TwistTag.E6.tag K) =
        D.g0 * rootDiagUnit TwistTag.E6.tag a * D.g0⁻¹ := by
      rw [hga]
      group
    rw [map_mul, map_mul, map_inv] at this
    rw [hg0cdef]
    calc baseChangeGL ι (g : ModGL TwistTag.E6.tag K) =
        (baseChangeGL ι D.c)⁻¹ * (baseChangeGL ι D.c * baseChangeGL ι (g : ModGL TwistTag.E6.tag K) *
          (baseChangeGL ι D.c)⁻¹) * baseChangeGL ι D.c := by group
      _ = (baseChangeGL ι D.c)⁻¹ * (D.g0 * rootDiagUnit TwistTag.E6.tag a * D.g0⁻¹) *
          baseChangeGL ι D.c := by rw [this]
      _ = _ := by group
  obtain ⟨w, uJ, κ, z, hw, hκ, hz, hhA, hhF, hFz, hu1, hu2, hu3, hconj⟩ :=
    exists_lie_frame (L := L) (ringChar K) f hf1 hK3 hg0cA hg0cF hβ₁ hβ₂ hβ₁₂ hv₁ hv₂
  obtain ⟨u₃, hu₃, t₃, ht₃, hdec⟩ := twE6_fixed_decomp hpr hf1 K hK' σ hσ' Fr hFrc hhA hhF
  obtain ⟨h, hh⟩ : ∃ h : ModGL TwistTag.E6.tag L,
      h = g0c * canonicalRep (coxeterSystem TwistTag.E6.tag) L w * κ * z := ⟨_, rfl⟩
  rw [← hh] at hhA hhF hdec hconj
  have hrootsθ : ∀ α ∈ ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact isRoot_e6HighestRoot
    · exact IsRoot.neg isRoot_e6HighestRoot
  have hrootsγ : ∀ α ∈ ({β₁ + β₂, -(β₁ + β₂)} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact hβ₁₂
    · exact IsRoot.neg hβ₁₂
  have hχγ : rootChar a (β₁ + β₂) = 1 := by rw [rootChar_add, hχ₁, hχ₂, mul_one]
  have hχγ' : rootChar a (-(β₁ + β₂)) = 1 := by
    have := rootChar_sub a 0 (β₁ + β₂)
    rw [zero_sub, rootChar_zero, hχγ] at this
    simpa using this
  obtain ⟨U₃, hU₃⟩ : ∃ U₃ : twistedE6RootGroup K σ, U₃ = ⟨u₃, hu₃⟩ := ⟨_, rfl⟩
  have hU₃c : ((U₃ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = u₃ := by rw [hU₃]
  have hSeq : twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
      ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) =
      (twE6LongRootSL2 (TwE6LongRoot.stdX σ) (TwE6LongRoot.stdXm σ)).map
        (MulAut.conj U₃).toMonoidHom :=
    TwE6LongRoot.twE6LongRootSL2_map (MulAut.conj U₃) _ _
  have hSbar : (rootSpan TwistTag.E6.tag L {θ₀, -θ₀}).map
      (MulAut.conj (baseChangeGL ι u₃)).toMonoidHom =
      (rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)}).map (MulAut.conj g0c).toMonoidHom := by
    rw [← hconj, hdec, map_conj_mul,
      map_conj_eq_of_mem_normalizer (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
        hrootsθ ht₃)]
  have hSchar : ∀ u : twistedE6RootGroup K σ,
      u ∈ twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
        ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) ↔
      baseChangeGL ι (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)}).map (MulAut.conj g0c).toMonoidHom := by
    intro u
    rw [hSeq, mem_map_conj_iff, hSL2, ← hSbar, mem_map_conj_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hU₃c]
    exact Iff.rfl
  refine ⟨(TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom,
    (TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom, ⟨U₃, rfl, rfl⟩, ?_, ?_, ?_⟩
  ·
    have hS_inv : ∀ ε ∈ E, ∀ u ∈ twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map
        (MulAut.conj U₃).toMonoidHom) ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom),
        ε u ∈ twE6LongRootSL2 ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom)
          ((TwE6LongRoot.stdXm σ).map (MulAut.conj U₃).toMonoidHom) := by
      intro ε hε u hu
      have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
        rw [range_twistedE6InndiagConj]
        exact hE hε
      obtain ⟨x, rfl⟩ := hεr
      have hxA : (x : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
        (mem_twPlanePre_iff K σ E _).2 ⟨x, rfl, hε⟩
      obtain ⟨d, hd, hxd⟩ := hdiag _ hxA
      rw [hSchar] at hu ⊢
      have hxu : baseChangeGL ι ((twistedE6InndiagConj K σ x u : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) = baseChangeGL ι (x : ModGL TwistTag.E6.tag K) *
            baseChangeGL ι (u : ModGL TwistTag.E6.tag K) *
            (baseChangeGL ι (x : ModGL TwistTag.E6.tag K))⁻¹ := by
        rw [twistedE6InndiagConj_apply]
        simp only [map_mul, map_inv]
      rw [hxu, hxd]
      obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 hu
      refine Subgroup.mem_map.2 ⟨d * s * d⁻¹,
        (Subgroup.mem_normalizer_iff.1 (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
          hrootsγ hd) s).1 hs, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsu ⊢
      rw [← hsu]
      group
    intro ε hε
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hS_inv ε hε u hu
    · intro u hu
      refine ⟨ε⁻¹ u, hS_inv ε⁻¹ (E.inv_mem hε) u hu, ?_⟩
      exact ε.apply_symm_apply u
  ·
    intro u hu
    rw [← hge]
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv, hgd]
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 ((hSchar u).1 hu)
    have hcomm : rootDiagUnit TwistTag.E6.tag a * s = s * rootDiagUnit TwistTag.E6.tag a := by
      have hle := torus_sup_rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {β₁ + β₂, -(β₁ + β₂)}) (by
          intro α hα
          rcases hα with rfl | rfl
          · exact ⟨hβ₁₂, hχγ⟩
          · exact ⟨IsRoot.neg hβ₁₂, hχγ'⟩)
      exact (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_sup_right hs))) _ rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsu
    rw [← hsu]
    calc g0c * rootDiagUnit TwistTag.E6.tag a * g0c⁻¹ * (g0c * s * g0c⁻¹) *
          (g0c * rootDiagUnit TwistTag.E6.tag a * g0c⁻¹)⁻¹
        = g0c * (rootDiagUnit TwistTag.E6.tag a * s * (rootDiagUnit TwistTag.E6.tag a)⁻¹) *
            g0c⁻¹ := by group
      _ = g0c * s * g0c⁻¹ := by rw [mul_inv_eq_iff_eq_mul.2 hcomm]
  ·
    obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ModGL TwistTag.E6.tag L,
        n₁ = canonicalRep (coxeterSystem TwistTag.E6.tag) L uJ := ⟨_, rfl⟩
    rw [← hn₁] at hFz
    obtain ⟨nw, hnw⟩ : ∃ nw : ModGL TwistTag.E6.tag L,
        nw = canonicalRep (coxeterSystem TwistTag.E6.tag) L w := ⟨_, rfl⟩
    rw [← hnw] at hh
    obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁, δ₁ = w⁻¹ • β₁ := ⟨_, rfl⟩
    obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, δ₂ = w⁻¹ • β₂ := ⟨_, rfl⟩
    obtain ⟨hpair₁, hpair₂, hsum⟩ := iform_theta_delta hβ₁ hβ₂ hβ₁₂ hw
    rw [← hδ₁] at hpair₁
    rw [← hδ₂] at hpair₂
    rw [← hδ₁, ← hδ₂] at hsum
    have hδ₁r : IsRoot TwistTag.E6.tag δ₁ := hδ₁ ▸ IsRoot.smul hβ₁ w⁻¹
    have hδ₂r : IsRoot TwistTag.E6.tag δ₂ := hδ₂ ▸ IsRoot.smul hβ₂ w⁻¹
    have hδ₁₂r : IsRoot TwistTag.E6.tag (δ₁ + δ₂) := by
      rw [hsum]
      exact isRoot_e6HighestRoot
    rw [← hδ₁, ← hδ₂] at hu1 hu2
    obtain ⟨a₁, ha₁, hψ₁⟩ := psi_pinnedX Fr uJ hδ₁r hu1
    obtain ⟨a₂, ha₂, hψ₂⟩ := psi_pinnedX Fr uJ hδ₂r hu2
    obtain ⟨a₃, ha₃, hψ₃⟩ := psi_pinnedX Fr uJ isRoot_e6HighestRoot hu3
    rw [← hn₁] at hψ₁ hψ₂ hψ₃
    let ψ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
      (MulAut.conj n₁).toMonoidHom.comp (twistHom TwistTag.E6 L Fr)
    have hψ : ∀ y, ψ y = n₁ * twistHom TwistTag.E6 L Fr y * n₁⁻¹ := fun y => by
      simp [ψ, MulAut.conj_apply]
    obtain ⟨y₀, hy₀S, hy₀F, hy₀p, hy₀U⟩ := exists_fixed_rootSpan_heis (L := L) (ringChar K) f
      hf1 hδ₁r hδ₂r hδ₁₂r ψ a₁ a₂ a₃ ha₁ ha₂ ha₃
      (fun c => by rw [hψ, hψ₁, hFrc])
      (fun c => by rw [hψ, hψ₂, hFrc])
      (fun c => by rw [hsum, hψ, hψ₃, hFrc])
    have hFy : twistHom TwistTag.E6 L Fr y₀ = n₁⁻¹ * y₀ * n₁ := by
      have := hy₀F
      rw [hψ] at this
      calc twistHom TwistTag.E6 L Fr y₀ =
          n₁⁻¹ * (n₁ * twistHom TwistTag.E6 L Fr y₀ * n₁⁻¹) * n₁ := by group
        _ = n₁⁻¹ * y₀ * n₁ := by rw [this]
    have hFz' : twistHom TwistTag.E6 L Fr z = n₁⁻¹ * z := hFz
    obtain ⟨xhat, hxhat⟩ : ∃ xhat : ModGL TwistTag.E6.tag L, xhat = z⁻¹ * y₀ * z := ⟨_, rfl⟩
    have hxhatF : twistHom TwistTag.E6 L Fr xhat = xhat := by
      rw [hxhat, map_mul, map_mul, map_inv, hFz', hFy]
      group
    obtain ⟨shat, hshat⟩ : ∃ shat : ModGL TwistTag.E6.tag L, shat = h * xhat * h⁻¹ := ⟨_, rfl⟩
    have hshatF : twistHom TwistTag.E6 L Fr shat = shat := by
      rw [hshat, map_mul, map_mul, map_inv, hhF, hxhatF]
    have hzA : z ∈ adjointGroup TwistTag.E6.tag L :=
      (sup_le torusGroup_le_adjoint_E6 (rootSpan_le_adjoint_E6 _)) hz
    have hy₀A : y₀ ∈ adjointGroup TwistTag.E6.tag L := rootSpan_le_adjoint_E6 _ hy₀S
    have hshatA : shat ∈ adjointGroup TwistTag.E6.tag L := by
      rw [hshat, hxhat]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhA (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) hy₀A) hzA)) (Subgroup.inv_mem _ hhA)
    have hshatp : shat ^ (ringChar K ^ 2) = 1 := by
      have : shat = (MulAut.conj (h * z⁻¹)).toMonoidHom y₀ := by
        rw [hshat, hxhat]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this, ← map_pow, hy₀p, map_one]
    obtain ⟨x, hxG, hxι⟩ :=
      twE6_descent_of_pow hpr hf1 K hK' σ hσ' Fr hFrc hpr hK3 hshatA hshatF ⟨2, hshatp⟩
    obtain ⟨xG, hxGdef⟩ : ∃ xG : twistedE6RootGroup K σ, xG = ⟨x, hxG⟩ := ⟨_, rfl⟩
    have hxGc : ((xG : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = x := by
      rw [hxGdef]
    have hdec' : h = baseChangeGL ι u₃ * t₃ := hdec
    have hconjι : baseChangeGL ι ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) = t₃ * xhat * t₃⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hU₃c, hxGc, map_mul, map_inv]
      have hι₃ : baseChangeGL ι u₃ = h * t₃⁻¹ := by rw [hdec']; group
      have hxι' : baseChangeGL ι x = shat := hxι
      rw [hι₃, hxι', hshat]
      group
    have hcoord₁ : δ₁ 1 = 1 := by
      have h := iform_e6HighestRoot δ₁
      rw [hpair₁] at h
      exact h.symm
    have hcoord₂ : δ₂ 1 = 1 := by
      have h := iform_e6HighestRoot δ₂
      rw [hpair₂] at h
      exact h.symm
    have hcoordθ : (δ₁ + δ₂) 1 = 2 := by
      rw [hsum]
      decide
    have hΦsub : ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
        parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion TwE6LongRoot.J0) := by
      intro α hα
      rw [mem_radicalRoots_std_iff]
      rcases hα with h | h | h
      · rw [h]
        exact ⟨hδ₁r, by omega⟩
      · rw [h]
        exact ⟨hδ₂r, by omega⟩
      · rw [h]
        exact ⟨hδ₁₂r, by omega⟩
    have hQroots : ∀ α ∈ parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes,
        IsRoot TwistTag.E6.tag α := fun _ hα => hα.1.1
    have hrootsδ : ∀ α ∈ ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag α := by
      intro α hα
      rcases hα with h | h | h
      · rw [h]; exact hδ₁r
      · rw [h]; exact hδ₂r
      · rw [h]; exact hδ₁₂r
    have hxQ : xG ∈ twE6LongRootRadical ((TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom) := by
      rw [TwE6LongRoot.twE6LongRootRadical_map (MulAut.conj U₃) (TwE6LongRoot.stdX σ),
        mem_map_conj_iff]
      apply hRad
      rw [hconjι, hrad]
      have hy₀Q : y₀ ∈ rootSpan TwistTag.E6.tag L
          (parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes) := by
        rw [← hrad]
        exact rootSpan_mono hΦsub hy₀S
      have hzN := torus_sup_rootSpan_parabolicRoots_le_normalizer_radical (L := L) e6LeviNodes hz
      have hxhatQ : xhat ∈ rootSpan TwistTag.E6.tag L
          (parabolicRadicalRoots TwistTag.E6.tag e6LeviNodes) := by
        rw [hxhat]
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hzN) y₀).1 hy₀Q
        rw [inv_inv] at this
        exact this
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hQroots ht₃) xhat).1 hxhatQ
    have htransport : ∀ S : Set (Fin TwistTag.E6.tag.rank → ℤ),
        (∀ α ∈ S, IsRoot TwistTag.E6.tag α) →
        (rootSpan TwistTag.E6.tag L S).map (MulAut.conj nw).toMonoidHom =
          rootSpan TwistTag.E6.tag L ((fun α => w • α) '' S) := by
      intro S hS
      rw [hnw]
      exact (canonical_weyl_root_transport TwistTag.E6.tag L).1 w S hS
    have hnwN : nw ∈ Subgroup.normalizer (torusGroup TwistTag.E6.tag L : Set (ModGL TwistTag.E6.tag L)) :=
      hnw ▸ canonicalRep_mem_normalizer w
    have himg1 : (fun α => w • α) '' ({θ₀, -θ₀} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
        {β₁ + β₂, -(β₁ + β₂)} := by
      ext α
      simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, smul_neg, hw]
    have himg2 : (fun α => w • α) '' ({δ₁, δ₂, δ₁ + δ₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
        {β₁, β₂, β₁ + β₂} := by
      ext α
      simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, smul_add, hδ₁, hδ₂, smul_inv_smul]
    have hk : nw * κ * nw⁻¹ ∈ torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L {β₁ + β₂, -(β₁ + β₂)} := by
      have hmem : nw * κ * nw⁻¹ ∈ (torusGroup TwistTag.E6.tag L ⊔
          rootSpan TwistTag.E6.tag L {θ₀, -θ₀}).map (MulAut.conj nw).toMonoidHom :=
        Subgroup.mem_map.2 ⟨κ, hκ, by simp [MulAut.conj_apply]⟩
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hnwN, htransport _ hrootsθ,
        himg1] at hmem
      exact hmem
    have hy₁ : nw * y₀ * nw⁻¹ ∈ rootSpan TwistTag.E6.tag L {β₁, β₂, β₁ + β₂} := by
      have hmem : nw * y₀ * nw⁻¹ ∈ (rootSpan TwistTag.E6.tag L {δ₁, δ₂, δ₁ + δ₂}).map
          (MulAut.conj nw).toMonoidHom := Subgroup.mem_map.2 ⟨y₀, hy₀S, by simp [MulAut.conj_apply]⟩
      rw [htransport _ hrootsδ, himg2] at hmem
      exact hmem
    have hSγ : ∀ α ∈ ({β₁ + β₂, -(β₁ + β₂)} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1 := by
      intro α hα
      rcases hα with h | h
      · rw [h]; exact ⟨hβ₁₂, hχγ⟩
      · rw [h]; exact ⟨IsRoot.neg hβ₁₂, hχγ'⟩
    have hS3 : ∀ α ∈ ({β₁, β₂, β₁ + β₂} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1 := by
      intro α hα
      rcases hα with h | h | h
      · rw [h]; exact ⟨hβ₁, hχ₁⟩
      · rw [h]; exact ⟨hβ₂, hχ₂⟩
      · rw [h]; exact ⟨hβ₁₂, hχγ⟩
    have hkc : rootDiagUnit TwistTag.E6.tag a * (nw * κ * nw⁻¹) =
        (nw * κ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a :=
      (Subgroup.mem_centralizer_iff.1 ((torus_sup_rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {β₁ + β₂, -(β₁ + β₂)}) hSγ) hk)) _ rfl
    have hy₁c : rootDiagUnit TwistTag.E6.tag a * (nw * y₀ * nw⁻¹) =
        (nw * y₀ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a :=
      (Subgroup.mem_centralizer_iff.1 ((rootSpan_le_centralizer_rootDiagUnit (L := L) a
        (S := {β₁, β₂, β₁ + β₂}) hS3) hy₁)) _ rfl
    have hcommY : rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) =
        (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a := by
      have hck : Commute (rootDiagUnit TwistTag.E6.tag a) (nw * κ * nw⁻¹) := hkc
      have hcy : Commute (rootDiagUnit TwistTag.E6.tag a) (nw * y₀ * nw⁻¹) := hy₁c
      have := ((hck.mul_right hcy).mul_right hck.inv_right).eq
      calc rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) =
          rootDiagUnit TwistTag.E6.tag a * (nw * κ * nw⁻¹ * (nw * y₀ * nw⁻¹) *
            (nw * κ * nw⁻¹)⁻¹) := by group
        _ = (nw * κ * nw⁻¹ * (nw * y₀ * nw⁻¹) * (nw * κ * nw⁻¹)⁻¹) *
            rootDiagUnit TwistTag.E6.tag a := this
        _ = (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * rootDiagUnit TwistTag.E6.tag a := by group
    have hshat' : shat = g0c * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0c⁻¹ := by
      rw [hshat, hxhat, hh]
      group
    have hxfix : e xG = xG := by
      rw [← hge]
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply, hxGc]
      apply baseChangeGL_injective ι
      have hxι' : baseChangeGL ι x = shat := hxι
      rw [map_mul, map_mul, map_inv, hgd, hxι', hshat']
      calc g0c * rootDiagUnit TwistTag.E6.tag a * g0c⁻¹ * (g0c * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0c⁻¹) *
          (g0c * rootDiagUnit TwistTag.E6.tag a * g0c⁻¹)⁻¹ =
          g0c * (rootDiagUnit TwistTag.E6.tag a * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) *
            (rootDiagUnit TwistTag.E6.tag a)⁻¹) * g0c⁻¹ := by group
        _ = g0c * (nw * κ * y₀ * κ⁻¹ * nw⁻¹) * g0c⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul.2 hcommY]
    have hxX : xG ∉ (TwE6LongRoot.stdX σ).map (MulAut.conj U₃).toMonoidHom := by
      intro hxmem
      rw [mem_map_conj_iff] at hxmem
      obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (show ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot from hxmem)
      have h1 : baseChangeGL ι ((U₃⁻¹ * xG * U₃ : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot := by
        rw [← hc, baseChangeGL_pinnedX]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      rw [hconjι] at h1
      have h2 : xhat ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot :=
        (Subgroup.mem_normalizer_iff.1
          (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot ht₃) xhat).2 h1
      have hzNU := torus_sup_rootSpan_levi_le_normalizer_rootSubgroup (L := L) hz
      have h3 : z * xhat * z⁻¹ ∈ rootSubgroup TwistTag.E6.tag L e6HighestRoot :=
        (Subgroup.mem_normalizer_iff.1 hzNU xhat).1 h2
      have h4 : z * xhat * z⁻¹ = y₀ := by rw [hxhat]; group
      rw [h4] at h3
      apply hy₀U
      rw [hsum]
      exact h3
    refine ⟨Subgroup.zpowers xG, (Subgroup.zpowers_le).2 hxQ, ?_, ?_⟩
    · intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [map_zpow, hxfix]
    · intro hle
      exact hxX (hle (Subgroup.mem_zpowers xG))

end Core

end CFSG.LieType.SeitzGeneration.ExcWideThree

