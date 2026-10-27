module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuaternionAutomizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_sup {B U : Subgroup G} (hU : IsPGroup 2 U)
    (hB9 : Nat.card B = 9) (hBU : B ≤ Subgroup.normalizer (U : Set G)) {t : G}
    (ht : t ∈ Subgroup.normalizer ((B ⊔ U : Subgroup G) : Set G)) :
    ∃ u ∈ U, u * t ∈ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBU
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hUB : U ⊓ B = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hk, hB9]
      exact Nat.Coprime.pow_left _ (by norm_num))).eq_bot
  rw [hUB, Subgroup.card_bot, mul_one, sup_comm, hB9, hk] at hcard
  have hBt : B.map (MulAut.conj t).toMonoidHom ≤ B ⊔ U := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ht b).mp (Subgroup.mem_sup_left hb)
  obtain ⟨g, hg, hgB⟩ := exists_conj_map_eq_of_card (p := 3) hBt le_sup_left (n := 2)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hB9]; norm_num)
    (by rw [hB9]; norm_num) (m := 2 ^ k) (by rw [hcard]; ring)
    (fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B U hBU, Set.mem_mul] at hg
  obtain ⟨b, hb, u, hu, rfl⟩ := hg
  refine ⟨u, hu, ?_⟩
  have hgt : b * u * t ∈ Subgroup.normalizer (B : Set G) := by
    apply mem_normalizer_of_map_conj_eq_self
    rw [map_conj_mul', hgB]
  have e : u * t = b⁻¹ * (b * u * t) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (B.inv_mem hb)) hgt

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_quaternion_le_autIn_of_nine
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {T B : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hBHM : B ≤ H ⊓ M) (hBp : IsPGroup 3 B)
    (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    ∃ Q : Subgroup (MulAut B),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set W := GLBPrimeCore 3 (H ⊓ M) with hWdef
  set Abar := (A.subgroupOf H).map π with hAbar
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hBH : B ≤ H := hBHM.trans inf_le_left
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAHM : A ≤ H ⊓ M := le_inf hAH (hc.esc.A_le.trans hc.esc.le_M)
  have hBA : (B.subgroupOf H).map π = Abar :=
    D2L34BetaConf3.map_eq_of_card_nine_of_nine hc hR9 hBHM hBp hB9
  have hX₀N : ((H ⊓ M).subgroupOf H).map π = Subgroup.normalizer (Abar : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hNA : ∀ g (hg : g ∈ H ⊓ M), π ⟨g, hg.1⟩ ∈ Subgroup.normalizer (Abar : Set _) := by
    intro g hg
    rw [← hX₀N]
    exact ⟨⟨g, hg.1⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hAbar9 : Nat.card Abar = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
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
      exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ Nat.Coprime.pow_left 2 (glbPrimeCore_coprime 3 _)
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
    have h1 : π ⟨w, (hWHM hw).1⟩ * π ⟨a, haH⟩ * (π ⟨w, (hWHM hw).1⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ = 1 := by
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
  have hψ : ∀ b : B, ((ψ b : Abar) : H ⧸ primeComplementCore (G := H) 3) = π ⟨b, hBH b.2⟩ :=
    fun _ => rfl
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
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_quaternion_le_automizer hL hc.le_K hAbar9
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

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
