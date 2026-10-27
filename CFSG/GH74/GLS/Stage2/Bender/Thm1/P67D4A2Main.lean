module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Phi
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldCard
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Centralizer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutCrit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_hC (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∀ t ∈ (⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ),
      (∀ u ∈ (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ),
        t * u = u * t) → t = 1 := by
  intro t ht htc
  have htH : t ∈ ⨆ i, hHat σ.toRingHom i := ht.1
  have htfix : a2Phi h φ t = t := ht.2
  have hfd := a2_foldData h φ hφ
  apply Subtype.ext
  refine a2_torus_centralizer h (a2_mem_hHatE_iSup t htH) ((a2Phi_eq_iff h φ hφ t).1 htfix) ?_
  intro k hk
  have hk' : CFSG.GH74.BNPair.IsRoot 6 k := by
    rcases hk with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  have hk2 : k % 2 ≠ 0 := by rcases hk with rfl | rfl <;> norm_num
  obtain ⟨x, hx, hx1, hxfix⟩ := a2_odd_fix h φ hφ hk' hk2
  have hkU : hexGroup (twistedX σ.toRingHom) k ≤ posUnipotent (g2Shape (twistedX σ.toRingHom)) :=
    (d4RGD2 σ.toRingHom h.cube_apply).root_le_U (by rcases hk with rfl | rfl <;> norm_num)
      (by rcases hk with rfl | rfl <;> norm_num)
  have hcomm := htc x ⟨hkU hx, hxfix⟩
  refine ⟨((x : twistedGroup σ.toRingHom) : adjointGroup d4 K), hx, fun he => hx1 (Subtype.ext he),
    (a2Phi_eq_iff h φ hφ x).1 hxfix, congrArg Subtype.val hcomm⟩

theorem a2_hC (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∀ t ∈ (⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ),
      (∀ u ∈ (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ),
        t * u = u * t) → t = 1 :=
  A2Core.a2_hC h.toCore φ hφ



theorem A2Core.a2_noAbel_fixSub (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∀ N : Subgroup ↥(fixSub φ), N.Normal → (∀ x y : N, x * y = y * x) → N = ⊥ := by
  have hFD := a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  have hF : ∀ N : Subgroup ↥(foldFix (a2Phi h φ)), N.Normal → (∀ x y : N, x * y = y * x) →
      N = ⊥ := by
    intro N hN hc
    exact hFD.noAbel hgen (fun g _ hcomm => a2_hZ h hcomm) (fun x hx => a2_hz h φ hφ x hx)
      (a2_foldFix_not_solvable h φ hφ) (a2_hC h φ hφ) N (fun a ha b hb =>
        congrArg (fun z : N => (z : ↥(foldFix (a2Phi h φ)))) (hc ⟨a, ha⟩ ⟨b, hb⟩))
  let e : ↥(foldFix (a2Phi h φ)) ≃* ↥(fixSub φ) :=
    (MulEquiv.subgroupMap (a2Equiv h) (foldFix (a2Phi h φ))).trans
      (MulEquiv.subgroupCongr (a2_foldFix_map h φ hφ))
  exact noAbelNormal_of_equiv e.symm hF

theorem a2_noAbel_fixSub (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∀ N : Subgroup ↥(fixSub φ), N.Normal → (∀ x y : N, x * y = y * x) → N = ⊥ :=
  A2Core.a2_noAbel_fixSub h.toCore φ hφ


theorem A2Core.a2_card_H_fix (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ)) = (q - 1) ^ 2 := by
  rw [← a2_torus_card h]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ)) =>
      (⟨⟨((x.1 : twistedGroup σ.toRingHom) : adjointGroup d4 K), a2_mem_hHatE_iSup x.1 x.2.1⟩,
        (a2Phi_eq_iff h φ hφ x.1).1 x.2.2⟩ :
        {t : (⨆ i, hHatE σ.toRingHom i : Subgroup (adjointGroup d4 K)) //
          a2Conj σ d ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
            ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)})) ⟨?_, ?_⟩)
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => (z.1.1 : adjointGroup d4 K)) hxy
  · rintro ⟨t, ht⟩
    have hΓ : ∀ g : adjointGroup d4 K, g ∈ ⨆ i, hHatE σ.toRingHom i →
        ∃ hg : g ∈ twistedGroup σ.toRingHom,
          (⟨g, hg⟩ : twistedGroup σ.toRingHom) ∈ ⨆ i, hHat σ.toRingHom i := by
      intro g hg
      refine Subgroup.iSup_induction (C := fun g => ∃ hg : g ∈ twistedGroup σ.toRingHom,
        (⟨g, hg⟩ : twistedGroup σ.toRingHom) ∈ ⨆ i, hHat σ.toRingHom i)
        (fun i => hHatE σ.toRingHom i) hg ?_ ?_ ?_
      · intro i g hg
        have hle : g ∈ twistedGroup σ.toRingHom :=
          hHatE_le_twistedGroup h.cube_apply i hg
        exact ⟨hle, Subgroup.mem_iSup_of_mem i hg⟩
      · exact ⟨one_mem _, one_mem _⟩
      · rintro x y ⟨hx, hxH⟩ ⟨hy, hyH⟩
        exact ⟨mul_mem hx hy, mul_mem hxH hyH⟩
    obtain ⟨hg, hgH⟩ := hΓ t.1 t.2
    exact ⟨⟨⟨t.1, hg⟩, hgH, (a2Phi_eq_iff h φ hφ ⟨t.1, hg⟩).2 ht⟩, rfl⟩

theorem a2_card_H_fix (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi h φ)) = (q - 1) ^ 2 :=
  A2Core.a2_card_H_fix h.toCore φ hφ


theorem A2Core.a2_card_fixSub (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥(fixSub φ) = (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  have hFD := a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  have : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv _ (a2Equiv h).symm.toEquiv
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := hFD.exists_rgd2
  have hU := a2_card_U_fix h φ hφ R'
  have hcard := hFD.card_fixed hgen (fun g _ hcomm => a2_hZ h hcomm)
    (fun x hx => a2_hz h φ hφ x hx) (a2_hC h φ hφ)
    (fun k hk => a2_card_foldRoot h φ hφ hk) hU
  rw [a2_card_H_fix h φ hφ] at hcard
  let e : ↥(foldFix (a2Phi h φ)) ≃* ↥(fixSub φ) :=
    (MulEquiv.subgroupMap (a2Equiv h) (foldFix (a2Phi h φ))).trans
      (MulEquiv.subgroupCongr (a2_foldFix_map h φ hφ))
  rw [← Nat.card_congr e.toEquiv]
  exact hcard

theorem a2_card_fixSub (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥(fixSub φ) = (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) :=
  A2Core.a2_card_fixSub h.toCore φ hφ

theorem a2_card_dvd_bound {q : ℕ} (hq : 2 ≤ q) :
    (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) ∣
      6 * q ^ 6 * (q ^ 2 - 1) * (q ^ 6 - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h2 : (m + 1) ^ 2 - 1 = m * (m + 2) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h6 : (m + 1) ^ 6 - 1 =
      m * ((m + 1) ^ 5 + (m + 1) ^ 4 + (m + 1) ^ 3 + (m + 1) ^ 2 + (m + 1) + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [h2, h6, Nat.add_sub_cancel]
  exact Dvd.intro (6 * (m + 1) ^ 3 * ((m + 1) ^ 3 + 1)) (by ring)


theorem a2Std_of_class {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {d : Kˣ} (hd : Units.map σ.toRingHom.toMonoidHom d = d)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : A2Std σ d (p ^ f) := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hqge : 2 ≤ p ^ f :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  exact ⟨hqge, hK, hσ, hq, hodd, hd, hd3, hd1⟩

theorem a2_hφ_of_class {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ}
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y : ModGL TwistTag.D4.tag K) =
        a2Conj σ d (y : ModGL TwistTag.D4.tag K) := by
  intro y
  change ((s * (fieldActor (t := TwistTag.D4) σ σ y) * s⁻¹ :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor, hs]
  rfl


theorem d4OuterThreeA2Toral_thm : D4OuterThreeA2Toral := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ d hd hd3 hd1 s hs
  have hA : A2Std σ d (p ^ f) := a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  set φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφdef
  have hNoAbel : D4NoAbel φ := a2_noAbel_fixSub hA φ hφ
  unfold D4Out
  refine ⟨hNoAbel, ?_⟩
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := (a2_foldData hA φ hφ).exists_rgd2
  have hcardU := a2_card_U_fix hA φ hφ R'
  have hcardU₀ : Nat.card ↥(Subgroup.map (a2Equiv hA).toMonoidHom
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ))) = (p ^ f) ^ 3 := by
    rw [Subgroup.card_map_of_injective (a2Equiv hA).injective]
    exact hcardU
  refine d4PtKer_of_noAbel_pgroup hp hp2 hf K hK σ hσ φ hNoAbel
    (Subgroup.map (a2Equiv hA).toMonoidHom
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ))) ?_ ?_ ?_
  · rw [← a2_foldFix_map hA φ hφ]
    exact Subgroup.map_mono inf_le_right
  · have : Finite ↥(Subgroup.map (a2Equiv hA).toMonoidHom
        ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ))) :=
      Nat.finite_of_card_ne_zero (by rw [hcardU₀]; exact (pow_pos (pow_pos hp.pos f) 3).ne')
    exact IsPGroup.of_card (n := 3 * f) (by rw [hcardU₀, ← pow_mul, mul_comm])
  · rw [hcardU₀]

theorem d4OuterThreeA2Toral_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) {d : Kˣ}
    (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    Nat.card ↥(fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) =
      (p ^ f - 1) ^ 2 * (p ^ f) ^ 3 * ((p ^ f + 1) * ((p ^ f) ^ 2 + p ^ f + 1)) :=
  a2_card_fixSub (a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1) _ (a2_hφ_of_class hs)

theorem d4OuterThreeA2Toral_card_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) {d : Kˣ}
    (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    Nat.card ↥(fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) ∣
      6 * (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 6 - 1) := by
  rw [d4OuterThreeA2Toral_card hp hp2 hf hq hK hσ hd hd3 hd1 hs]
  exact a2_card_dvd_bound (by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
