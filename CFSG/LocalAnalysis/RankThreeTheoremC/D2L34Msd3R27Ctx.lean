module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.TwoOfThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PermuteNine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf3.toL34Ctx (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    L34Ctx M H R Rbar K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn : K.Normal := hc.almostSimple.normal
  have hcomp := hc.almostSimple.component
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hc.almostSimple.center_eq_bot).trans
      QuotientGroup.quotientBot).symm
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hcomp.2.2.2
  have hAR : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hc.rbar]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hc.esc.A_le (Subgroup.mem_subgroupOf.mp hx))
  refine
    { normal := hKn
      simple := e.isSimpleGroup
      nonab := ?_
      center := hc.almostSimple.center_eq_bot
      sylow := ?_
      rbar := hc.rbar
      inf_ne_bot := ?_
      mapX := ?_
      isPGroup := hc.esc.isPGroup
      le_inf := le_inf hc.esc.le_H hc.esc.le_M
      primeCore_le := hc.esc.primeCore_le
      twoCore_le := hc.esc.twoCore_le
      ne_top := fun htop => hc.esc.not_le
        (hc.esc.maxTwoLocal_M.2 H hc.esc.maxTwoLocal_H.1 (htop ▸ le_top)).le
      twoLocal := hc.esc.maxTwoLocal_H.1
      kProper := (D2Amb3.glob (G := G)).kProper
      charTwo := (D2Amb3.glob (G := G)).charTwo
      centralizer_eq_bot := hc.almostSimple.centralizer_eq_bot }
  · obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hcomp.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  · exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
      (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hcomp.2.1
        Subgroup.IsSubnormal.top)
  · intro h
    have hle : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤ ⊥ :=
      h ▸ le_inf hAR hc.le_K
    have hcard := hc.almostSimple.card_A
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at hcard
    norm_num at hcard
  · rw [map_d1LiftX, ← hc.rbar]

theorem D2L34BetaConf3.exists_char_cover_of_isSylowTwoOf' (hFF : CitedFFL34BestOffender)
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H)
    (hOD : GLBPrimeCore 3 H ≤ D₀) (hV : IsSylowTwoOf V D₀) :
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  have hx := hc.toL34Ctx
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hV1 : V ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_H.1
    (le_bot_iff.mp (h ▸ hx.twoCore_le_of_isSylowTwoOf hD₀H hOD hV))
  by_cases hα : ∀ A : Subgroup G, IsMaxElemAbelian V A → ∀ a ∈ A, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))
  · exact ⟨thompsonJ V, B6.thompsonJ_le V, Setup.thompsonJ_ne_bot hV.2.1 hV1,
      Setup.characteristic_thompsonJ V, hx.cover_thompsonJ hD₀H hOD hV hα⟩
  · push Not at hα
    obtain ⟨A', hA', a, haA, haC⟩ := hα
    exact ⟨omegaOneCenterOf V, Setup.omegaOneCenterOf_le V,
      Setup.omegaOneCenterOf_ne_bot hV.2.1 hV1, Setup.characteristic_omegaOneCenterOf V,
      hx.cover_omegaOneCenterOf hFF hL hD₀H hOD hV hA' haA haC⟩

theorem D2L34BetaConf3.exists_char_cover_syl' (hFF : CitedFFL34BestOffender)
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧ (C.subgroupOf T).Characteristic ∧
      ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k :=
  hc.exists_char_cover_of_isSylowTwoOf' hFF inf_le_left
    (le_inf (glbPrimeCore_le 3 H) hc.esc.primeCore_le) hT

omit [D2Amb3 G] in
private theorem D2L34BetaConf3.conj_le_inf_and (hc : D2L34BetaConf3 d P M A H R Rbar K) {g : G}
    (hg : g ∈ H ⊓ M) :
    A.map (MulAut.conj g).toMonoidHom ≤ H ⊓ M ∧
      IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (A.map (MulAut.conj g).toMonoidHom) = 9 := by
  have hAHM : A ≤ H ⊓ M :=
    le_inf (hc.esc.A_le.trans hc.esc.le_H) (hc.esc.A_le.trans hc.esc.le_M)
  refine ⟨?_, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hc.esc.elem _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (H ⊓ M).mul_mem ((H ⊓ M).mul_mem hg (hAHM ha)) ((H ⊓ M).inv_mem hg)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc.esc.card_A]
    norm_num

omit [D2Amb3 G] in
theorem D2L34BetaConf3.map_eq_of_conj (hc : D2L34BetaConf3 d P M A H R Rbar K) {g : G}
    (hg : g ∈ H ⊓ M) :
    ((A.map (MulAut.conj g).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hgN : π ⟨g, hg.1⟩ ∈
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  ext z
  constructor
  · rintro ⟨⟨x, hxH⟩, hx, rfl⟩
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_subgroupOf.mp hx
    have e : (⟨x, hxH⟩ : H) = ⟨g, hg.1⟩ * ⟨a, hAH ha⟩ * (⟨g, hg.1⟩ : H)⁻¹ := by
      apply Subtype.ext
      rw [← hax]
      rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp
      ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  · intro hz
    obtain ⟨⟨a, haH⟩, ha, he⟩ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z).mp hz
    refine ⟨⟨g, hg.1⟩ * ⟨a, haH⟩ * (⟨g, hg.1⟩ : H)⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    · rw [map_mul, map_mul, map_inv, he]
      group

omit [D2Amb3 G] in
theorem D2L34BetaConf3.exists_permuting_elemAbelian_map_eq
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ B : Subgroup G, (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
        (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ∧
      B ≤ H ⊓ M ∧ IsElemAbelian 3 B ∧ Nat.card B = 9 ∧
      B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G) := by
  obtain ⟨B, ⟨g, hg, rfl⟩, h⟩ := D2L34BetaConf3.exists_permuting_elemAbelian_conj hc hT
  exact ⟨_, hc.map_eq_of_conj hg, h⟩

omit [D2Amb3 G] in
theorem D2L34BetaConf3.cover_of_isSylowTwoOf_of_map_eq
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B Y : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M))
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hTY : T ≤ Y) (hBY : B ≤ Y) (hNTY : H ⊓ Subgroup.normalizer (T : Set G) ≤ Y) :
    ∀ k ∈ K, ∃ a ∈ Y, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hTbar := D2L34BetaConf3.isSylowTwoOf_map hc hT
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    rw [hc.almostSimple.card_A]
    norm_num
  have hNY : Subgroup.normalizer (((T.subgroupOf H).map π : Subgroup _) : Set _) ≤
      (Y.subgroupOf H).map π :=
    (normalizer_map_le_map_normalizer hc.esc.primeCore_le hT).trans
      (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
        (hNTY (Subgroup.mem_subgroupOf.mp hx))))
  have hAY : (A.subgroupOf H).map π ≤ (Y.subgroupOf H).map π := by
    rw [← hBA]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBY (Subgroup.mem_subgroupOf.mp hx)))
  have hKY := le_of_normalizer_sylowTwo_le hc.l34 hc.almostSimple.normal
    hc.almostSimple.centralizer_eq_bot hc.iso hc.le_K hc.almostSimple.elem hAbar9 hTbar
    (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hTY (Subgroup.mem_subgroupOf.mp hx)))) hAY hNY
  intro k hk
  obtain ⟨y, hy, rfl⟩ := hKY hk
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, rfl⟩

omit [D2Amb3 G] in
theorem D2L34BetaConf3.cover_of_isSylowTwoOf_of_conj
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B Y : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M))
    (hBg : ∃ g ∈ H ⊓ M, B = A.map (MulAut.conj g).toMonoidHom)
    (hTY : T ≤ Y) (hBY : B ≤ Y) (hNTY : H ⊓ Subgroup.normalizer (T : Set G) ≤ Y) :
    ∀ k ∈ K, ∃ a ∈ Y, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k := by
  obtain ⟨g, hg, rfl⟩ := hBg
  exact hc.cover_of_isSylowTwoOf_of_map_eq hT (hc.map_eq_of_conj hg) hTY hBY hNTY

omit [D2Amb3 G] in
theorem D2L34BetaConf3.exists_quaternion_le_autIn_of_map_eq
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) (hBH : B ≤ H)
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    ∃ Q : Subgroup (MulAut B),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set W := GLBPrimeCore 3 (H ⊓ M)
  set Abar := (A.subgroupOf H).map π with hAbar
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAHM : A ≤ H ⊓ M := le_inf hAH (hc.esc.A_le.trans hc.esc.le_M)
  have hX₀N : ((H ⊓ M).subgroupOf H).map π = Subgroup.normalizer (Abar : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hNA : ∀ g (hg : g ∈ H ⊓ M), π ⟨g, hg.1⟩ ∈ Subgroup.normalizer (Abar : Set _) := by
    intro g hg
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hAbar9 : Nat.card Abar = 9 := by
    rw [hAbar, hc.almostSimple.card_A]
    norm_num
  have hAbarc : ∀ x ∈ Abar, ∀ y ∈ Abar, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc.almostSimple.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hWHM : W ≤ H ⊓ M := glbPrimeCore_le 3 _
  have hHMW : H ⊓ M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glbPrimeCore 3 _
  have hAW : Abar ⊓ (W.subgroupOf H).map π = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hAbar9]
    have h1 : Nat.Coprime 9 (Nat.card (W.subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWHM.trans inf_le_left)).toEquiv]
      exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸
        Nat.Coprime.pow_left 2 (glbPrimeCore_coprime 3 _)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ π) h1
  have hcomm : ∀ (w : G) (hw : w ∈ W) (y : H ⧸ primeComplementCore (G := H) 3), y ∈ Abar →
      π ⟨w, (hWHM hw).1⟩ * y = y * π ⟨w, (hWHM hw).1⟩ := by
    intro w hw y hy
    obtain ⟨⟨a, haH⟩, ha, rfl⟩ := hy
    have haA : a ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hwN := hNA w (hWHM hw)
    have hc1 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ ∈
        Abar :=
      Abar.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN _).mp ⟨⟨a, haH⟩, ha, rfl⟩)
        (Abar.inv_mem ⟨⟨a, haH⟩, ha, rfl⟩)
    have hc2 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ ∈
        (W.subgroupOf H).map π := by
      have h1 : a * w⁻¹ * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHMW (hAHM haA)) _).mp (W.inv_mem hw)
      have hmem : w * (a * w⁻¹ * a⁻¹) ∈ W := W.mul_mem hw h1
      refine ⟨⟨w * (a * w⁻¹ * a⁻¹), (hWHM hmem).1⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
      have e : (⟨w * (a * w⁻¹ * a⁻¹), (hWHM hmem).1⟩ : H) =
          ⟨w, (hWHM hw).1⟩ * ⟨a, haH⟩ * (⟨w, (hWHM hw).1⟩ : H)⁻¹ * (⟨a, haH⟩ : H)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ =
        1 := by
      have := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
      rw [hAW, Subgroup.mem_bot] at this
      exact this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hψmem : ∀ b : B, (π.comp (Subgroup.inclusion hBH)) b ∈ Abar := by
    intro b
    rw [← hBA]
    exact ⟨⟨b, hBH b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  let ψ : B →* Abar := (π.comp (Subgroup.inclusion hBH)).codRestrict Abar hψmem
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hBA] at hy
    obtain ⟨⟨b, hbH⟩, hb, rfl⟩ := hy
    exact ⟨⟨b, Subgroup.mem_subgroupOf.mp hb⟩, Subtype.ext rfl⟩
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hB9, hAbar9])
  let φ : B ≃* Abar := MulEquiv.ofBijective ψ hψb
  have hφ : ∀ b : B, ((φ b : Abar) : H ⧸ primeComplementCore (G := H) 3) = π ⟨b, hBH b.2⟩ :=
    fun _ => rfl
  let Ψ : MulAut B ≃* MulAut Abar := MulAut.congr φ
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  obtain ⟨Q₈, hQ₈le, ⟨eQ⟩⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_quaternion_le_automizer hL hc.le_K
      hAbar9
  have hTbar := D2L34BetaConf3.isSylowTwoOf_map hc hT
  obtain ⟨hNKeq, -, -⟩ := normalizer_inf_eq_sup_of_l34 hc.l34 hc.almostSimple.normal hc.iso
    hc.le_K hAbar9 hTbar
  refine ⟨Q₈.map Ψ.symm.toMonoidHom, ?_,
    ⟨(Subgroup.equivMapOfInjective Q₈ Ψ.symm.toMonoidHom Ψ.symm.injective).symm.trans eQ⟩⟩
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := hQ₈le hσ
  have hkK' : k ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hk : k ∈ Subgroup.normalizer (Abar : Set _) ⊓ K := ⟨hkN, hkK'⟩
  rw [← hNKeq, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hTbar.1), Set.mem_mul]
    at hk
  obtain ⟨tbar, htbar, a, ha, rfl⟩ := hk
  obtain ⟨⟨t, htH⟩, ht, rfl⟩ := htbar.1
  have htT : t ∈ T := Subgroup.mem_subgroupOf.mp ht
  obtain ⟨u, hu, hut⟩ := exists_mul_mem_normalizer_of_sup (hT.2.1.to_le inf_le_left) hB9 hBU
    (hTBU htT)
  refine ⟨⟨u * t, hut⟩, Subgroup.mem_subgroupOf.mpr (T.mul_mem hu.1 htT), ?_⟩
  show B.normalizerMonoidHom ⟨u * t, hut⟩ = Ψ.symm _
  rw [MulEquiv.eq_symm_apply]
  ext y
  obtain ⟨b, rfl⟩ := φ.surjective y
  have huH : u ∈ H := hTH hu.1
  have hy1 : π ⟨t, htH⟩ * π ⟨b, hBH b.2⟩ * (π ⟨t, htH⟩)⁻¹ ∈ Abar := by
    have hbA : π ⟨b, hBH b.2⟩ ∈ Abar := (φ b).2
    exact (Subgroup.mem_normalizer_iff.mp (hNA t (hTHM htT)) _).mp hbA
  have hL1 : (((Ψ (B.normalizerMonoidHom ⟨u * t, hut⟩)) (φ b) : Abar) :
      H ⧸ primeComplementCore (G := H) 3) =
      π ⟨u, huH⟩ * (π ⟨t, htH⟩ * π ⟨b, hBH b.2⟩ * (π ⟨t, htH⟩)⁻¹) * (π ⟨u, huH⟩)⁻¹ := by
    show ((φ (B.normalizerMonoidHom ⟨u * t, hut⟩ (φ.symm (φ b))) : Abar) :
      H ⧸ primeComplementCore (G := H) 3) = _
    rw [MulEquiv.symm_apply_apply, hφ]
    have e : (⟨((B.normalizerMonoidHom ⟨u * t, hut⟩ b : B) : G),
        hBH (B.normalizerMonoidHom ⟨u * t, hut⟩ b).2⟩ : H) =
        ⟨u, huH⟩ * (⟨t, htH⟩ * ⟨b, hBH b.2⟩ * (⟨t, htH⟩ : H)⁻¹) * (⟨u, huH⟩ : H)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv,
        CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe]
      group
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [hL1, hcomm u hu.2 _ hy1, mul_inv_cancel_right]
  show _ = ((Abar.normalizerMonoidHom ⟨π ⟨t, htH⟩ * a, hkN⟩ (φ b) : Abar) :
    H ⧸ primeComplementCore (G := H) 3)
  rw [CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe, hφ]
  have hbA : π ⟨b, hBH b.2⟩ ∈ Abar := (φ b).2
  rw [mul_inv_rev, show π ⟨t, htH⟩ * a * π ⟨b, hBH b.2⟩ * (a⁻¹ * (π ⟨t, htH⟩)⁻¹) =
    π ⟨t, htH⟩ * (a * π ⟨b, hBH b.2⟩ * a⁻¹) * (π ⟨t, htH⟩)⁻¹ by group,
    hAbarc a ha _ hbA, mul_inv_cancel_right]

omit [D2Amb3 G] in
theorem D2L34BetaConf3.exists_quaternion_le_autIn_of_conj
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M))
    (hBg : ∃ g ∈ H ⊓ M, B = A.map (MulAut.conj g).toMonoidHom)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    ∃ Q : Subgroup (MulAut B),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  obtain ⟨g, hg, rfl⟩ := hBg
  obtain ⟨hBHM, -, hB9⟩ := hc.conj_le_inf_and hg
  exact hc.exists_quaternion_le_autIn_of_map_eq hT (hBHM.trans inf_le_left)
    (hc.map_eq_of_conj hg) hB9 hBU hTBU

theorem D2L34BetaConf3.two_of_three_normalized_of_map_eq
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) (hBH : B ≤ H)
    (hBA : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hBel : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hHc : CharTwo H := (D2Amb3.glob (G := G)).charTwo H hc.esc.maxTwoLocal_H.1
  have hO2 : pCoreOf 2 H ≤ T := by
    have hO2p : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    have hO2W : pCoreOf 2 H ≤ GLBPrimeCore 3 H := by
      refine le_glbPrimeCore (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) ?_
      obtain ⟨k, hk⟩ := hO2p.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hO2HM : pCoreOf 2 H ≤ H ⊓ M :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hO2W.trans hc.esc.primeCore_le)
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HM
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hO2p
    exact hle.trans (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hchar : CharTwo (T ⊔ B) :=
    charTwo_of_le_of_pCoreOf_le (sup_le hTH hBH) hHc (hO2.trans le_sup_left)
  exact CFSG.AGLEmbeddingD2.Tits.MsidePrelim.two_of_three_normalized hT.2.1 hBel hB9 inf_le_left
    hBU hTBU hchar
    (hc.exists_quaternion_le_autIn_of_map_eq hT hBH hBA hB9 hBU hTBU)

theorem D2L34BetaConf3.two_of_three_normalized_of_conj
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T B : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M))
    (hBg : ∃ g ∈ H ⊓ M, B = A.map (MulAut.conj g).toMonoidHom)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) := by
  obtain ⟨g, hg, rfl⟩ := hBg
  obtain ⟨hBHM, hBel, hB9⟩ := hc.conj_le_inf_and hg
  exact hc.two_of_three_normalized_of_map_eq hT (hBHM.trans inf_le_left) (hc.map_eq_of_conj hg)
    hBel hB9 hBU hTBU

end CFSG.LocalAnalysis.RankThreeTheoremC
