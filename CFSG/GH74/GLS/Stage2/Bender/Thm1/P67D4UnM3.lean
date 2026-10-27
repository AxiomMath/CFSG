module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolarDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnG2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPol

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

section Aux

theorem unM3_tau_lift₂ {G : Type*} [Group G] {T : Subgroup G} (τ : G ≃* G) {n₀ n₁ u : G}
    (h₁ : ∀ x ∈ T, n₁⁻¹ * x * n₁ ∈ T) (h₀ : ∀ x ∈ T, n₀ * x * n₀⁻¹ ∈ T)
    (hτ : ∀ x ∈ T, τ x ∈ T) (ha₀ : n₀⁻¹ * τ n₀ ∈ T) (ha₁ : n₁⁻¹ * τ n₁ ∈ T)
    (hu : (n₀ * n₁ * n₀⁻¹)⁻¹ * u ∈ T) : u⁻¹ * τ u ∈ T := by
  have hX : n₁⁻¹ * (n₀⁻¹ * τ n₀) * n₁ * (n₁⁻¹ * τ n₁) * (n₀⁻¹ * τ n₀)⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (h₁ _ ha₀) ha₁) (T.inv_mem ha₀)
  have hY := h₀ _ hX
  have key : u⁻¹ * τ u = ((n₀ * n₁ * n₀⁻¹)⁻¹ * u)⁻¹ *
      (n₀ * (n₁⁻¹ * (n₀⁻¹ * τ n₀) * n₁ * (n₁⁻¹ * τ n₁) * (n₀⁻¹ * τ n₀)⁻¹) * n₀⁻¹) *
        τ ((n₀ * n₁ * n₀⁻¹)⁻¹ * u) := by
    simp only [map_mul, map_inv]
    group
  rw [key]
  exact T.mul_mem (T.mul_mem (T.inv_mem hu) hY) (hτ _ hu)

theorem unM3_foldIdx_neg {k : ℤ} (hk : k ≠ 0) : foldIdx (-k) = -foldIdx k := by
  rcases lt_or_gt_of_ne hk with h | h
  · rw [foldIdx_of_neg h, foldIdx_of_pos (by omega : 0 < -k)]
    ring
  · rw [foldIdx_of_pos h, foldIdx_of_neg (by omega : -k < 0)]
    ring

end Aux

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

include hφ in
theorem A2Core.un_isPGroup {p n : ℕ} [Fact p.Prime] (hq : q = p ^ n) :
    IsPGroup p ↥(unD h φ hφ).U := by
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := (a2_foldData h φ hφ).exists_rgd2
  have hcard : Nat.card ↥((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
      foldFix (a2Phi h φ)) = p ^ (n * 3) := by
    rw [a2_card_U_fix h φ hφ R', hq, ← pow_mul]
  have hS := unD_spec h φ hφ
  have hmem : ∀ x : ↥(unD h φ hφ).U,
      ((x : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) ∈
        (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ) := fun x =>
    ⟨(hS.U _).1 x.2, x.1.2⟩
  refine (IsPGroup.of_card hcard).of_injective
    (((Subgroup.subtype (foldFix (a2Phi h φ))).comp (Subgroup.subtype (unD h φ hφ).U)).codRestrict
      _ hmem) ?_
  intro x y hxy
  have hxy' := Subtype.ext_iff.1 hxy
  exact Subtype.ext (Subtype.ext hxy')

include hφ in
theorem A2Core.un_isOpposition (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    (unD h φ hφ).IsOpposition (unTauX h φ ε hcomm) := by
  have hεσ' : ∀ c, σ (ε c) = ε (σ c) := fun c => (hεσ c).symm
  have hS := unD_spec h φ hφ
  obtain ⟨n₁, n₂, hn₁, hn₂, hc₁, hc₂⟩ := hS.lifts
  refine ⟨fun x hx => ?_, fun k hk x hx => ?_, ⟨n₁, hn₁, ?_⟩, ⟨n₂, hn₂, ?_⟩⟩
  · refine (hS.BN _).2 ?_
    rw [coe_unTauX]
    exact unTau_mem_torus h ε hεσ' ((hS.BN x).1 hx)
  · have hnk : CFSG.GH74.BNPair.IsRoot 3 (-k) := ⟨neg_ne_zero.2 hk.1, by simpa using hk.2⟩
    obtain ⟨hx1, -⟩ := mem_foldRoot.1 ((hS.root k hk x).1 hx)
    refine (hS.root (-k) hnk _).2 (mem_foldRoot.2 ⟨?_, mem_foldFix.1 (unTauX h φ ε hcomm x).2⟩)
    rw [coe_unTauX, unM3_foldIdx_neg hk.1]
    exact unTau_mem_hexGroup h ε hεσ' (isRoot_foldIdx hk) hx1
  · refine (hS.BN _).2 ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_unTauX, hc₁]
    exact unTau_nHat_mem h ε hεσ' 1
  · refine (hS.BN _).2 ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_unTauX, hc₂]
    have R := d4RGD2 σ.toRingHom h.cube_apply
    exact unM3_tau_lift₂ (a2Phi h (unTau σ ε)) (fun x hx => R.conj_H₁' hx) R.conj_H₂
      (fun x hx => unTau_mem_torus h ε hεσ' hx) (unTau_nHat_mem h ε hεσ' 0)
      (unTau_nHat_mem h ε hεσ' 1) (unM2_spec h φ hφ).2

theorem un_isOpposition
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    (unD h φ hφ).IsOpposition (unTauX h φ ε hcomm) :=
  A2Core.un_isOpposition h.toCore φ hφ ε hεσ hcomm

include hφ in
theorem A2Core.un_hab {k : ℤ} (hk : k = 1 ∨ k = 3) :
    ∀ a ∈ (unD h φ hφ).root k, ∀ b ∈ (unD h φ hφ).root k, a * b = b * a := by
  intro a ha b hb
  have hk' : CFSG.GH74.BNPair.IsRoot 3 k := by
    rcases hk with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  have hS := unD_spec h φ hφ
  obtain ⟨ha1, -⟩ := mem_foldRoot.1 ((hS.root k hk' a).1 ha)
  obtain ⟨hb1, -⟩ := mem_foldRoot.1 ((hS.root k hk' b).1 hb)
  exact Subtype.ext (un_hex_abelian h (isRoot_foldIdx hk') (foldIdx_odd hk'.1) ha1 hb1)

theorem un_hab
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {k : ℤ} (hk : k = 1 ∨ k = 3) :
    ∀ a ∈ (unD h φ hφ).root k, ∀ b ∈ (unD h φ hφ).root k, a * b = b * a :=
  A2Core.un_hab h.toCore φ hφ hk

include hφ in
theorem A2Core.un_hTor : ∀ t ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, ∀ y ∈ (unD h φ hφ).root 1, y ≠ 1 →
    ∀ z ∈ (unD h φ hφ).root 3, z ≠ 1 → t * y = y * t → t * z = z * t → t = 1 := by
  intro t ht y hy hy1 z hz hz1 hty htz
  have hS := unD_spec h φ hφ
  have hr1 : CFSG.GH74.BNPair.IsRoot 3 1 := ⟨by norm_num, by norm_num⟩
  have hr3 : CFSG.GH74.BNPair.IsRoot 3 3 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hy', hyfix⟩ := mem_foldRoot.1 ((hS.root 1 hr1 y).1 hy)
  obtain ⟨hz', hzfix⟩ := mem_foldRoot.1 ((hS.root 3 hr3 z).1 hz)
  rw [show foldIdx 1 = 1 by decide] at hy'
  rw [show foldIdx 3 = 5 by decide] at hz'
  have htH : ((t : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) ∈
      ⨆ i, hHat σ.toRingHom i := (hS.BN t).1 ht
  have htfix : a2Phi h φ ((t : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      ((t : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) := mem_foldFix.1 t.2
  have key := a2_torus_centralizer h (a2_mem_hHatE_iSup _ htH)
    ((a2Phi_eq_iff h φ hφ _).1 htfix) (by
      intro k hk
      rcases hk with rfl | rfl
      · exact ⟨(((y : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) : adjointGroup d4 K),
          hy', fun he => hy1 (Subtype.ext (Subtype.ext he)),
          (a2Phi_eq_iff h φ hφ _).1 hyfix,
          congrArg (fun w : ↥(foldFix (a2Phi h φ)) =>
            ((w : twistedGroup σ.toRingHom) : adjointGroup d4 K)) hty⟩
      · exact ⟨(((z : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) : adjointGroup d4 K),
          hz', fun he => hz1 (Subtype.ext (Subtype.ext he)),
          (a2Phi_eq_iff h φ hφ _).1 hzfix,
          congrArg (fun w : ↥(foldFix (a2Phi h φ)) =>
            ((w : twistedGroup σ.toRingHom) : adjointGroup d4 K)) htz⟩)
  exact Subtype.ext (Subtype.ext key)

theorem un_hTor
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : ∀ t ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, ∀ y ∈ (unD h φ hφ).root 1, y ≠ 1 →
    ∀ z ∈ (unD h φ hφ).root 3, z ≠ 1 → t * y = y * t → t * z = z * t → t = 1 :=
  A2Core.un_hTor h.toCore φ hφ

include hφ in
theorem A2Core.un_chat_X (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ c ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, unTauX h φ ε hcomm c = c ∧ c * c = 1 ∧
      ∀ y ∈ (unD h φ hφ).root (-2), c * y * c⁻¹ = y⁻¹ := by
  have hS := unD_spec h φ hφ
  obtain ⟨t, ht, htφ, htτ, htt, hty⟩ := un_chat h ε (fun c => (hεσ c).symm) φ hφ
  refine ⟨⟨t, mem_foldFix.2 htφ⟩, (hS.BN _).2 ht, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [coe_unTauX]
    exact htτ
  · exact Subtype.ext htt
  · intro y hy
    have hr : CFSG.GH74.BNPair.IsRoot 3 (-2) := ⟨by norm_num, by norm_num⟩
    obtain ⟨hy1, -⟩ := mem_foldRoot.1 ((hS.root (-2) hr y).1 hy)
    rw [show foldIdx (-2) = -3 by decide] at hy1
    exact Subtype.ext (hty _ hy1)

theorem un_chat_X
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ c ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, unTauX h φ ε hcomm c = c ∧ c * c = 1 ∧
      ∀ y ∈ (unD h φ hφ).root (-2), c * y * c⁻¹ = y⁻¹ :=
  A2Core.un_chat_X h.toCore φ hφ ε hεσ hcomm

end CFSG.GH74.GLS.Stage2.Bender.Thm1
