module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnRho
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnArith

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

section Comm

variable {K : Type} [Field K] [Finite K]

omit
  [Finite K] in
theorem unVec_aux' (δ : K ≃+* K) (b : Kˣ) (hb : Units.map δ.toRingHom.toMonoidHom b = b)
    (i : Fin 4) :
    Units.map δ.toRingHom.toMonoidHom (![1, 1, b, 1] i) = ![1, 1, b, 1] i := by
  fin_cases i
  · simp
  · simp
  · simpa using hb
  · simp

theorem unField_comm_phi (σ δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c)) (b : Kˣ)
    (hb : Units.map δ.toRingHom.toMonoidHom b = b)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1])
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    fieldActor (t := TwistTag.D4) σ δ ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y) =
      (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
        (fieldActor (t := TwistTag.D4) σ δ y) := by
  refine Subtype.ext ?_
  rw [coe_fieldActor, coe_toralPhi, coe_toralPhi, coe_fieldActor]
  have hcomp : Units.map (entrywiseHom δ.toRingHom)
      (Units.map (entrywiseHom σ.toRingHom) (y : ModGL TwistTag.D4.tag K)) =
      Units.map (entrywiseHom σ.toRingHom)
        (Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.D4.tag K)) := by
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp,
      show δ.toRingHom.comp σ.toRingHom = σ.toRingHom.comp δ.toRingHom from RingHom.ext hδσ]
  have hδs : Units.map (entrywiseHom δ.toRingHom) (s : ModGL TwistTag.D4.tag K) =
      (s : ModGL TwistTag.D4.tag K) := by
    obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.tag.rank → Kˣ, a = ![1, 1, b, 1] := ⟨_, rfl⟩
    have hs' : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag a := by
      rw [ha]; exact hs
    rw [hs', units_map_entrywiseHom_rootDiagUnit (t := TwistTag.D4)]
    congr 1
    funext i
    rw [ha]
    exact unVec_aux' δ b hb i
  simp only [map_mul, map_inv, hδs, hcomp]

end Comm

section Core

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

theorem A2Core.un_tauX_tauX (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y))
    (y : ↥(foldFix (a2Phi h φ))) :
    unTauX h φ ε hcomm (unTauX h φ ε hcomm y) = unFieldX h φ (ε * ε) hcommε y := by
  refine Subtype.ext ?_
  rw [coe_unTauX, coe_unTauX, coe_unFieldX]
  have : ∀ x : twistedGroup σ.toRingHom,
      a2Phi h (unTau σ ε) (a2Phi h (unTau σ ε) x) =
        a2Phi h (fieldActor (t := TwistTag.D4) σ (ε * ε)) x := fun x => by
    simp only [a2Phi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, unTau_sq_apply]
  exact this _

theorem un_tauX_tauX
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y))
    (y : ↥(foldFix (a2Phi h φ))) :
    unTauX h φ ε hcomm (unTauX h φ ε hcomm y) = unFieldX h φ (ε * ε) hcommε y :=
  A2Core.un_tauX_tauX h.toCore φ ε hcomm hcommε y

@[expose] def A2Core.a2PhiHom (h : A2Core σ d q) :
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* MulAut (twistedGroup σ.toRingHom)
    where
  toFun := a2Phi h
  map_one' := MulEquiv.ext fun x => (a2Equiv h).symm_apply_apply x
  map_mul' f g := MulEquiv.ext fun x => by
    show (a2Equiv h).symm (f (g (a2Equiv h x))) =
      (a2Equiv h).symm (f ((a2Equiv h) ((a2Equiv h).symm (g (a2Equiv h x)))))
    rw [MulEquiv.apply_symm_apply]

@[expose, reducible] def a2PhiHom (h : A2Std σ d q) :
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* MulAut (twistedGroup σ.toRingHom) :=
  A2Core.a2PhiHom h.toCore

theorem A2Core.un_tauX_four (ε : K ≃+* K) (hε4 : ∀ c, ε (ε (ε (ε c))) = c)
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) (y : ↥(foldFix (a2Phi h φ))) :
    unTauX h φ ε hcomm (unTauX h φ ε hcomm (unTauX h φ ε hcomm (unTauX h φ ε hcomm y))) = y := by
  refine Subtype.ext ?_
  rw [coe_unTauX, coe_unTauX, coe_unTauX, coe_unTauX]
  have h4 : (a2PhiHom h (unTau σ ε)) ^ 4 = 1 := by
    rw [← map_pow, unTau_pow_four σ ε hε4, map_one]
  have e : ∀ n : MulAut (twistedGroup σ.toRingHom), n ^ 4 = n * (n * (n * n)) := fun n => by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  rw [e] at h4
  have := congrArg (fun n : MulAut (twistedGroup σ.toRingHom) => n (y : twistedGroup σ.toRingHom))
    h4
  exact this

theorem un_tauX_four
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K) (hε4 : ∀ c, ε (ε (ε (ε c))) = c)
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) (y : ↥(foldFix (a2Phi h φ))) :
    unTauX h φ ε hcomm (unTauX h φ ε hcomm (unTauX h φ ε hcomm (unTauX h φ ε hcomm y))) = y :=
  A2Core.un_tauX_four h.toCore φ ε hε4 hcomm y

include hφ in
theorem A2Core.un_polarity_core {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hp3 : p % 3 = 2)
    (hf : 1 ≤ f) (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    (∀ A : Subgroup ↥(foldFix (unTauX h φ ε hcomm)), A.Normal →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥) ∧
      ∃ U₀ : Subgroup ↥(foldFix (a2Phi h φ)), U₀ ≤ foldFix (unTauX h φ ε hcomm) ∧
        IsPGroup p U₀ ∧ (p ^ f) ^ 3 ≤ Nat.card U₀ := by
  have hσ' : ∀ c, σ c = c ^ ((p ^ f) ^ 4) := fun c => by rw [h.frob c, hq]
  have hK : Nat.card K = ((p ^ f) ^ 4) ^ 3 := by rw [h.card, hq]
  have hεσ : ∀ c, ε (σ c) = σ (ε c) := un_eps_sigma hσ' hε
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := un_eps_four hK hε
  have : CharP (UnK σ) p := un_charP_unK σ
  have hk : Nat.card (UnK σ) = (p ^ f) ^ 4 := un_card_unK hf hK hσ'
  have hεk : ∀ a : UnK σ, unEps ε hεσ a = a ^ (p ^ f) := un_eps_frob hσ' hε hεσ
  have hεε : ∀ c, (ε * ε) (σ c) = σ ((ε * ε) c) := fun c => by
    show ε (ε (σ c)) = σ (ε (ε c))
    rw [hεσ, hεσ]
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁', -⟩ := (unD_spec h φ hφ).lifts
  have hn₁X : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W :=
    Subtype.ext (hn₁'.trans (unSlFix_w h φ hφ).symm)
  obtain ⟨κ, hκ⟩ := unRho_tau h φ hφ hn₂ ε hεσ hcomm
  have hτ := un_isOpposition h φ hφ ε hεσ hcomm
  have hτe := un_tauX_tauX h φ ε hcomm hcommε
  refine un_final hp2 hp3 (by omega) (unD h φ hφ)
    (un_isPGroup h φ hφ (n := f * 4) (by rw [hq, pow_mul])) (unTauX h φ ε hcomm)
    (unFieldX h φ (ε * ε) hcommε) hτ hτe
    (fun b hb => by rw [← hτe b]; exact hτ.tau_sq_mem_B hb)
    (un_tauX_four h φ ε hε4 hcomm) hk (unEps ε hεσ) hεk (unRho h φ hφ n₂)
    (unRho_injective h φ hφ n₂) κ (fun a => (hκ a).1) (fun a => (hκ a).2)
    (unRho_upper_mem h φ hφ hn₂) (fun y hy => unRho_upper_surj h φ hφ hn₂ hy)
    (unRho_lower_mem h φ hφ hn₂) (unRho_N h φ hφ hn₂ hn₁ hn₁X) (unRho_H h φ hφ hn₂)
    (unX1 h φ hφ) (unX1_injective h φ hφ) (unX1_mem h φ hφ) (fun y hy => unX1_surj h φ hφ hy)
    (unX1_torus h φ hφ) ?_ (un_hab h φ hφ (Or.inl rfl)) (un_hab h φ hφ (Or.inr rfl))
    (un_hTor h φ hφ) (un_chat_X h φ hφ ε hεσ hcomm)
  intro a
  rw [unX1_field h φ hφ (ε * ε) hεε hcommε a, unEps_mul ε ε hεσ hεσ hεε a]

theorem un_polarity_core
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hp3 : p % 3 = 2)
    (hf : 1 ≤ f) (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    (∀ A : Subgroup ↥(foldFix (unTauX h φ ε hcomm)), A.Normal →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥) ∧
      ∃ U₀ : Subgroup ↥(foldFix (a2Phi h φ)), U₀ ≤ foldFix (unTauX h φ ε hcomm) ∧
        IsPGroup p U₀ ∧ (p ^ f) ^ 3 ≤ Nat.card U₀ :=
  A2Core.un_polarity_core h.toCore φ hφ hp2 hp3 hf hq ε hε hcomm hcommε

end Core

section Transport

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))

theorem A2Core.un_fixfix_equiv (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ e : ↥(foldFix (unTauX h φ ε hcomm)) ≃*
        ↥(foldFix (φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _) ⊓
          foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _)),
      ∀ z, ((e z : _) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        a2Equiv h (((z : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom)) := by
  have hφ : ∀ g : twistedGroup σ.toRingHom, a2Phi h φ g = g ↔ φ (a2Equiv h g) = a2Equiv h g := by
    intro g
    change (a2Equiv h).symm (φ (a2Equiv h g)) = g ↔ _
    rw [MulEquiv.symm_apply_eq]
  have hτ : ∀ g : twistedGroup σ.toRingHom,
      a2Phi h (unTau σ ε) g = g ↔ unTau σ ε (a2Equiv h g) = a2Equiv h g := by
    intro g
    change (a2Equiv h).symm (unTau σ ε (a2Equiv h g)) = g ↔ _
    rw [MulEquiv.symm_apply_eq]
  let f : ↥(foldFix (unTauX h φ ε hcomm)) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (a2Equiv h).toMonoidHom.comp ((foldFix (a2Phi h φ)).subtype.comp
      (foldFix (unTauX h φ ε hcomm)).subtype)
  have hmem : ∀ z, f z ∈ foldFix (φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _) ⊓
      foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _) := fun z => by
    refine Subgroup.mem_inf.2 ⟨mem_foldFix.2 ?_, mem_foldFix.2 ?_⟩
    · exact (hφ _).1 (mem_foldFix.1 z.1.2)
    · have := congrArg Subtype.val (mem_foldFix.1 z.2)
      exact (hτ _).1 this
  have hfinj : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext ((a2Equiv h).injective hab))
  refine ⟨MulEquiv.ofBijective (f.codRestrict _ hmem)
    ⟨fun a b hab => hfinj (congrArg Subtype.val hab), ?_⟩, fun z => rfl⟩
  rintro ⟨y, hy⟩
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  have hg1 : a2Phi h φ ((a2Equiv h).symm y) = (a2Equiv h).symm y :=
    (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact mem_foldFix.1 hy1)
  have hg2 : a2Phi h (unTau σ ε) ((a2Equiv h).symm y) = (a2Equiv h).symm y :=
    (hτ _).2 (by rw [MulEquiv.apply_symm_apply]; exact mem_foldFix.1 hy2)
  refine ⟨⟨⟨(a2Equiv h).symm y, mem_foldFix.2 hg1⟩, mem_foldFix.2 (Subtype.ext hg2)⟩, ?_⟩
  refine Subtype.ext ?_
  change (a2Equiv h) ((a2Equiv h).symm y) = y
  exact (a2Equiv h).apply_symm_apply y

theorem un_fixfix_equiv
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ e : ↥(foldFix (unTauX h φ ε hcomm)) ≃*
        ↥(foldFix (φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _) ⊓
          foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* _)),
      ∀ z, ((e z : _) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        a2Equiv h (((z : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom)) :=
  A2Core.un_fixfix_equiv h.toCore φ ε hcomm

end Transport

theorem un_mod3_of_pow {p f : ℕ} (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) : p % 3 = 2 := by
  have h3 : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod] at hq
  interval_cases hp : p % 3
  · rw [Nat.zero_pow (by omega)] at hq
    omega
  · rw [Nat.one_pow] at hq
    omega
  · rfl


section Polarity

theorem un_polarity {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ p] (hK₄ : Nat.card K₄ = ((p ^ f) ^ 4) ^ 3)
    (σ₄ ε : K₄ ≃+* K₄) (hσ₄ : ∀ c, σ₄ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (b : K₄ˣ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    (∀ F₀ : Subgroup ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)),
      F₀.Normal → (∀ a ∈ F₀, ∀ b ∈ F₀, a * b = b * a) → F₀ = ⊥) ∧
    ∃ U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom),
      U₀ ≤ foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _) ∧
        IsPGroup p U₀ ∧ (p ^ f) ^ 3 ≤ Nat.card U₀ := by
  have hp3 : p % 3 = 2 := un_mod3_of_pow hf hq
  have hA : A2Std σ₄ b ((p ^ f) ^ 4) := un_a2Std hp2 hf hq hK₄ hσ₄ hb3 hb1
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  obtain ⟨hNo, U₀, hU₀le, hU₀p, hU₀card⟩ :=
    un_polarity_core hA _ hφ₄ hp2 hp3 hf rfl ε hε hcomm hcommε
  obtain ⟨e, he⟩ := un_fixfix_equiv hA _ ε hcomm
  let f₀ : ↥(foldFix (a2Phi hA (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄))) →*
      graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom :=
    (a2Equiv hA).toMonoidHom.comp (foldFix (a2Phi hA (MulAut.conj s₄ *
      fieldActor (t := TwistTag.D4) σ₄ σ₄))).subtype
  have hf₀ : Function.Injective f₀ := fun a b hab => Subtype.ext ((a2Equiv hA).injective hab)
  refine ⟨un_noAbel_of_equiv e hNo, U₀.map f₀, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (he ⟨u, hU₀le hu⟩) ▸ (e ⟨u, hU₀le hu⟩).2
  · exact hU₀p.of_surjective (Subgroup.equivMapOfInjective U₀ f₀ hf₀).toMonoidHom
      (Subgroup.equivMapOfInjective U₀ f₀ hf₀).surjective
  · rw [Subgroup.card_map_of_injective hf₀]
    exact hU₀card

end Polarity

end CFSG.GH74.GLS.Stage2.Bender.Thm1
