module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoMinusPolar

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1

section Transport

variable {Y Y₄ : Type} [Group Y] [Group Y₄]

theorem fixSub_props_of_frame (φ : MulAut Y) (φ₄ τ : MulAut Y₄) (ψ : Y →* Y₄)
    (hinj : Function.Injective ψ) (hint : ∀ y, ψ (φ y) = φ₄ (ψ y))
    (hfix : ∀ y₄, τ y₄ = y₄ ↔ y₄ ∈ Set.range ψ) {n : ℕ}
    (hA : ∀ F₀ : Subgroup ↥(foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄)), F₀.Normal →
      Nat.Coprime 3 (Nat.card F₀) → F₀ = ⊥)
    (hZ : ∀ z : ↥(foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄)), (∀ g, z * g = g * z) →
      z = 1)
    (hU : ∃ U₀ : Subgroup Y₄, U₀ ≤ foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄) ∧
      IsPGroup 2 U₀ ∧ n ≤ Nat.card U₀) :
    (∀ N : Subgroup Y, N ≤ fixSub φ → (∀ g ∈ fixSub φ, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      Nat.Coprime 3 (Nat.card N) → N = ⊥) ∧
    (∀ z ∈ fixSub φ, (∀ x ∈ fixSub φ, z * x = x * z) → z = 1) ∧
    ∃ U₀ : Subgroup Y, U₀ ≤ fixSub φ ∧ IsPGroup 2 U₀ ∧ n ≤ Nat.card U₀ := by
  obtain ⟨e, he⟩ := un_fixSub_equiv φ φ₄ τ ψ hinj hint hfix
  have hfx : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ = fixSub φ :=
    Subgroup.ext fun _ => Iff.rfl
  set e' := e.symm.trans (MulEquiv.subgroupCongr hfx) with he'
  refine ⟨fun N hNT hNn hcop => eq_bot_of_fixSub_equiv e' hA N hNT hNn hcop, ?_, ?_⟩
  · intro z hz hcomm
    have h1 := eq_one_of_central_of_equiv e' hZ ⟨z, hz⟩ fun g => Subtype.ext (hcomm g g.2)
    exact congrArg Subtype.val h1
  · obtain ⟨U₀, hU₀le, hU₀p, hU₀card⟩ := hU
    refine ⟨U₀.comap ψ, ?_, ?_, ?_⟩
    · intro y hy
      have h1 := Subgroup.mem_inf.1 (hU₀le hy)
      rw [mem_fixSub]
      apply hinj
      rw [hint]
      exact mem_foldFix.1 h1.1
    · exact hU₀p.of_injective (ψ.subgroupComap U₀) (fun a b hab =>
        Subtype.ext (hinj (congrArg Subtype.val hab)))
    · have hbij : Function.Bijective (ψ.subgroupComap U₀) := by
        refine ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)), ?_⟩
        rintro ⟨z, hz⟩
        obtain ⟨y, rfl⟩ := (hfix z).1 (mem_foldFix.1 (Subgroup.mem_inf.1 (hU₀le hz)).2)
        exact ⟨⟨y, hz⟩, rfl⟩
      rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
      exact hU₀card

end Transport

section Fold

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem unTauX_props_two (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {f : ℕ} [CharP K 2] (hq3 : (2 ^ f) % 3 = 2) (hf : 1 ≤ f) (hq : q = (2 ^ f) ^ 4)
    (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((2 ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    (∀ A : Subgroup ↥(foldFix (A2Core.unTauX h φ ε hcomm)), A.Normal →
        Nat.Coprime 3 (Nat.card A) → A = ⊥) ∧
      (∀ z : ↥(foldFix (A2Core.unTauX h φ ε hcomm)), (∀ g, z * g = g * z) → z = 1) ∧
      ∃ U₀ : Subgroup ↥(foldFix (A2Core.a2Phi h φ)), U₀ ≤ foldFix (A2Core.unTauX h φ ε hcomm) ∧
        IsPGroup 2 U₀ ∧ (2 ^ f) ^ 3 ≤ Nat.card U₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ' : ∀ c, σ c = c ^ ((2 ^ f) ^ 4) := fun c => by rw [h.frob c, hq]
  have hK : Nat.card K = ((2 ^ f) ^ 4) ^ 3 := by rw [h.card, hq]
  have hεσ : ∀ c, ε (σ c) = σ (ε c) := un_eps_sigma hσ' hε
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := un_eps_four hK hε
  have : CharP (UnK σ) 2 := un_charP_unK σ
  have hk : Nat.card (UnK σ) = (2 ^ f) ^ 4 := un_card_unK hf hK hσ'
  have hεk : ∀ a : UnK σ, unEps ε hεσ a = a ^ (2 ^ f) := un_eps_frob hσ' hε hεσ
  have hεε : ∀ c, (ε * ε) (σ c) = σ ((ε * ε) c) := fun c => by
    show ε (ε (σ c)) = σ (ε (ε c))
    rw [hεσ, hεσ]
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁', -⟩ := (A2Core.unD_spec h φ hφ).lifts
  have hn₁X : (n₁ : ↥(foldFix (A2Core.a2Phi h φ))) = A2Core.unSlFix h φ hφ unSL2W :=
    Subtype.ext (hn₁'.trans (A2Core.unSlFix_w h φ hφ).symm)
  obtain ⟨κ, hκ⟩ := A2Core.unRho_tau h φ hφ hn₂ ε hεσ hcomm
  have hτ := A2Core.un_isOpposition h φ hφ ε hεσ hcomm
  have hτe := A2Core.un_tauX_tauX h φ ε hcomm hcommε
  refine foldFix_opposition_two hq3 (by omega) (A2Core.unD h φ hφ)
    (A2Core.unTauX h φ ε hcomm) (A2Core.unFieldX h φ (ε * ε) hcommε) hτ hτe
    (fun b hb => by rw [← hτe b]; exact hτ.tau_sq_mem_B hb)
    (A2Core.un_tauX_four h φ ε hε4 hcomm) hk (unEps ε hεσ) hεk (A2Core.unRho h φ hφ n₂)
    (A2Core.unRho_injective h φ hφ n₂) κ (fun a => (hκ a).1) (fun a => (hκ a).2)
    (A2Core.unRho_upper_mem h φ hφ hn₂) (fun y hy => A2Core.unRho_upper_surj h φ hφ hn₂ hy)
    (A2Core.unRho_N h φ hφ hn₂ hn₁ hn₁X) (A2Core.unRho_H h φ hφ hn₂)
    (A2Core.unX1 h φ hφ) (A2Core.unX1_injective h φ hφ) (A2Core.unX1_mem h φ hφ)
    (fun y hy => A2Core.unX1_surj h φ hφ hy) (A2Core.unX1_torus h φ hφ) ?_
    (A2Core.un_hab h φ hφ (Or.inl rfl)) (A2Core.un_hab h φ hφ (Or.inr rfl))
    (A2Core.un_hTor h φ hφ)
  intro a
  rw [A2Core.unX1_field h φ hφ (ε * ε) hεε hcommε a, unEps_mul ε ε hεσ hεσ hεε a]

theorem unTau_props_two {f : ℕ} (hf : 1 ≤ f) (hq : (2 ^ f) % 3 = 2)
    {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ 2] (σ₄ ε : K₄ ≃+* K₄)
    (hε : ∀ c, ε c = c ^ ((2 ^ f) ^ 9)) (b : K₄ˣ) (hA : A2Core σ₄ b ((2 ^ f) ^ 4))
    (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    (∀ F₀ : Subgroup ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)),
      F₀.Normal → Nat.Coprime 3 (Nat.card F₀) → F₀ = ⊥) ∧
    (∀ z : ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)),
      (∀ g, z * g = g * z) → z = 1) ∧
    ∃ U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom),
      U₀ ≤ foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _) ∧
        IsPGroup 2 U₀ ∧ (2 ^ f) ^ 3 ≤ Nat.card U₀ := by
  have hσ₄ : ∀ c, σ₄ c = c ^ ((2 ^ f) ^ 4) := hA.frob
  have hb3 : b ^ 3 = 1 := hA.cube
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  obtain ⟨hNo, hZ, U₀, hU₀le, hU₀p, hU₀card⟩ :=
    unTauX_props_two hA _ hφ₄ hq hf rfl ε hε hcomm hcommε
  obtain ⟨e, he⟩ := A2Core.un_fixfix_equiv hA _ ε hcomm
  let f₀ : ↥(foldFix (A2Core.a2Phi hA (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄))) →*
      graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom :=
    (A2Core.a2Equiv hA).toMonoidHom.comp (foldFix (A2Core.a2Phi hA (MulAut.conj s₄ *
      fieldActor (t := TwistTag.D4) σ₄ σ₄))).subtype
  have hf₀ : Function.Injective f₀ := fun a b hab => Subtype.ext ((A2Core.a2Equiv hA).injective hab)
  refine ⟨normal_coprime_eq_bot_of_equiv e hNo, eq_one_of_central_of_equiv e hZ, U₀.map f₀, ?_,
    ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (he ⟨u, hU₀le hu⟩) ▸ (e ⟨u, hU₀le hu⟩).2
  · exact hU₀p.of_surjective (Subgroup.equivMapOfInjective U₀ f₀ hf₀).toMonoidHom
      (Subgroup.equivMapOfInjective U₀ f₀ hf₀).surjective
  · rw [Subgroup.card_map_of_injective hf₀]
    exact hU₀card

end Fold

end CFSG.HardMathSupport.Timmesfeld.CrossChar
