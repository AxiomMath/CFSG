module

public import CFSG.GH74.Generic.S3.OnlyInvT5
public import CFSG.GH74.Generic.S3.PumpStep
public import CFSG.GH74.Generic.S3.BFreeDiag
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.E2 CFSG.GH74.Generic CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification Subgroup
open CFSG.LocalAnalysis.ComponentInitial (conjSub swapDiag)

theorem bar_isComponent_of_b2 (hB2 : B_B2_g4) {G : Type} [Group G] [Finite G]
    (hG : IsKProperSimple G) (hgen4 : Gen4 G)
    {z w : G} (hz : orderOf z = 2) (hw : orderOf w = 2) (hzw : z ∈ centralizer ({w} : Set G))
    {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G)) I) :
    IsComponent ((C3.Layer1.PumpCalc.bar w I).subgroupOf
      (centralizer ({C3.Layer1.PumpCalc.sbar z hzw} : Set (CentralizerBar w)))) := by
  set Y' := centralizer ({w} : Set G) with hY'
  have hY'ne : Y' ≠ ⊤ := centralizer_involution_ne_top hG.1 hG.2.1 hw
  have hX : IsKGroupNative (barQ ↥Y') :=
    isKGroupNative_of_surjective (X := ↥Y') (isKGroupNative_of_kProper hG.2.2 hY'ne) ⊤
      ((barMk ↥Y').comp (⊤ : Subgroup ↥Y').subtype)
      (barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hso : orderOf (⟨z, hzw⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzw hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hI).1 hzw
  have hΛ2 := isTwoComponent_centralizer_mk hI hzw
  have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
  have hle : C3.Layer1.PumpCalc.bar w I ≤
      centralizer ({C3.Layer1.PumpCalc.sbar z hzw} : Set (CentralizerBar w)) :=
    (Subgroup.map_mono (le_centralizer_mk (isPCompIn_two_iff.mp hI).1 hzw)).trans
      (map_centralizer_barMk (orderOf_mk_centralizer hzw hz)).le
  have hpc : IsPCompIn 2 (centralizer ({C3.Layer1.PumpCalc.sbar z hzw} : Set _))
      (C3.Layer1.PumpCalc.bar w I) :=
    isPCompIn_two_iff.mpr ⟨hle, hmap2⟩
  have hcore : pPrimeCore 2 (barQ ↥Y') = ⊥ := by
    have := oddCore_barQ (Y := ↥Y')
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hg4 : Gen4 (barQ ↥Y') := Gen4.quotient _ (Gen4.subgroup Y' hgen4)
  exact (hB2 _ hg4 hX hcore (C3.Layer1.PumpCalc.sbar z hzw)
    (C3.Layer1.PumpCalc.orderOf_sbar hz hzw) (C3.Layer1.PumpCalc.bar w I) hpc).2

theorem l3Cover_shape_cases_top
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G) {t : G}
    (ht2 : orderOf t = 2) {L : Subgroup (CentralizerBar t)} (hLc : IsComponent L)
    (hG2 : InG2 ↥L) {A : Subgroup ↥L} {K₀ : Type} [Group K₀] {p f : ℕ}
    (hc : IsL3Cover ↥A K₀ p f) :
    d2 ↥L ≤ 6 ∨ (d2 ↥L = 7 ∧ ∃ (p' f' : ℕ) (tL : StatedLieTag), (tL = .PSL ∨ tL = .PSU) ∧
      p'.Prime ∧ p' ≠ 2 ∧ 5 ≤ p' ^ f' ∧ LieModel ↥L tL 3 p' f' ∧ (A = ⊤ ∨ p ^ f < p' ^ f')) := by
  rcases generic_shapes_of_inG2 hF hs hn hgen hK ht2 hG2 with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (d2_le_six_of_shapeS1 hLc hG2 h1)
  · refine Or.inl (d2_le_six_of_shapeS2 hLc hG2 ?_ h2)
    intro hbot
    exact xbar_not_mem_of_center_eq_bot ht2 hbot h2.2
  · obtain ⟨⟨p', f', hp', hp2', hq', hmod⟩, hx⟩ := h3
    have hd7 := d2_eq_seven_of_shapeS3 hLc hG2 ⟨⟨p', f', hp', hp2', hq', hmod⟩, hx⟩
    by_cases hA : A = ⊤
    · rcases hmod with hm | hm
      · exact Or.inr ⟨hd7, p', f', .PSL, Or.inl rfl, hp', hp2', hq', hm, Or.inl hA⟩
      · exact Or.inr ⟨hd7, p', f', .PSU, Or.inr rfl, hp', hp2', hq', hm, Or.inl hA⟩
    · rcases hmod with hm | hm
      · exact Or.inr ⟨hd7, p', f', .PSL, Or.inl rfl, hp', hp2', hq', hm,
          Or.inr (l3Cover_lt_of_proper hA hc (Or.inl rfl) hp' hp2' hq' hm)⟩
      · exact Or.inr ⟨hd7, p', f', .PSU, Or.inr rfl, hp', hp2', hq', hm,
          Or.inr (l3Cover_lt_of_proper hA hc (Or.inr rfl) hp' hp2' hq' hm)⟩
  · obtain ⟨⟨f₀, hmod⟩, -⟩ := h4
    exact (l3Cover_false_of_ree hc hmod).elim
  · exact (l3Cover_false_of_J1 hc h5.1).elim

theorem l3Cover_table
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hFR : L3FRank)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hgen : Gen4 G) (hK : KGH G) {t : G} (ht2 : orderOf t = 2)
    {L : Subgroup (CentralizerBar t)} (hLc : IsComponent L) {A : Subgroup ↥L}
    {K₀ : Type} [Group K₀] {p f : ℕ} (hc : IsL3Cover ↥A K₀ p f) {tK : StatedLieTag}
    (htK : tK = .PSL ∨ tK = .PSU) (hmodK : LieModel K₀ tK 3 p f) (hPK : Gen4Comp K₀) :
    InG2 ↥L ∧ (d2 ↥L < 7 ∨ (d2 ↥L = 7 ∧ FRank K₀ < FRank ↥L) ∨
      (d2 ↥L = 7 ∧ Nonempty (↥L ≃* K₀))) := by
  have hKP : IsKProperSimple G := ⟨hs, hn, CFSG.GH74.kProper_of_kgh hK⟩
  have hLK : InCalK2 ↥L := inCalK2_of_isComponent hKP ht2 hLc
  have hPL : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hgen ht2) L
  have hG2L : InG2 ↥L := ⟨hLK, l3Cover_not_inC2 hG hE hPL hc, l3Cover_not_inT2 hLK hc⟩
  refine ⟨hG2L, ?_⟩
  have hp := hc.prime
  have hp2 := hc.ne_two
  have hq5 := hc.big
  rcases l3Cover_shape_cases_top hG hs hn hgen hK ht2 hLc hG2L hc with
    h6 | ⟨hd7', p', f', tL, htL, hp', hp2', hq', hmodL, hA⟩
  · exact Or.inl (by omega)
  · rcases hA with hA | hlt'
    ·
      subst hA
      refine Or.inr (Or.inr ⟨hd7', ?_⟩)
      have hcL : IsL3Cover ↥L K₀ p f := hc.of_mulEquiv Subgroup.topEquiv.symm
      have hLs : IsSimpleGroup ↥L := by
        rcases htL with rfl | rfl
        · exact isSimpleGroup_of_lieModel_L3' (Or.inl hmodL)
        · exact isSimpleGroup_of_lieModel_L3' (Or.inr hmodL)
      obtain ⟨π, hπs, -⟩ := hcL.cover
      have hnt := hcL.nontrivial
      have hker : π.ker = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h0 | h1
        · exact h0
        · exfalso
          have hsub : Subsingleton K₀ := by
            refine ⟨fun a b => ?_⟩
            obtain ⟨a', rfl⟩ := hπs a
            obtain ⟨b', rfl⟩ := hπs b
            have ha : a' ∈ π.ker := by rw [h1]; exact Subgroup.mem_top a'
            have hb : b' ∈ π.ker := by rw [h1]; exact Subgroup.mem_top b'
            rw [MonoidHom.mem_ker] at ha hb
            rw [ha, hb]
          exact (not_nontrivial_iff_subsingleton.2 hsub) hnt
      exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hker, hπs⟩⟩
    · refine Or.inr (Or.inl ⟨hd7', ?_⟩)
      have hF1 := hFR K₀ tK p f htK hp hp2 hq5 hPK hmodK
      have hF2 := hFR ↥L tL p' f' htL hp' hp2' hq' hPL hmodL
      rw [hF1, hF2]
      have := Nat.pow_lt_pow_left hlt' (by norm_num : 4 ≠ 0)
      omega

theorem lam_l3Cover (hB2 : B_B2_g4) {G : Type} [Group G] [Finite G] (hKP : IsKProperSimple G)
    (hgen : Gen4 G) {x t : G} (hx2 : orderOf x = 2) (ht2 : orderOf t = 2)
    (hxY : x ∈ centralizer ({t} : Set G)) {M Λ : Subgroup G}
    (hΛ : C3.Layer1.PumpCalc.IsLam x t M Λ) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) {tK : StatedLieTag} (htK : tK = .PSL ∨ tK = .PSU)
    (hmodK : LieModel (↥M ⧸ pPrimeCore 2 ↥M) tK 3 p f) :
    IsL3Cover ↥(C3.Layer1.PumpCalc.bar t Λ) (↥M ⧸ pPrimeCore 2 ↥M) p f := by
  have hcomp := bar_isComponent_of_b2 hB2 hKP hgen hx2 ht2 hxY hΛ.pcW
  have hle : C3.Layer1.PumpCalc.bar t Λ ≤
      centralizer ({C3.Layer1.PumpCalc.sbar x hxY} : Set _) := fun w hw => by
    rw [mem_centralizer_singleton_iff]
    have := C3.Layer1.PumpCalc.bar_lam_le_centralizer hxY hΛ w hw
    calc w * C3.Layer1.PumpCalc.sbar x hxY
        = C3.Layer1.PumpCalc.sbar x hxY * w * (C3.Layer1.PumpCalc.sbar x hxY)⁻¹ *
            C3.Layer1.PumpCalc.sbar x hxY := by rw [this]
      _ = C3.Layer1.PumpCalc.sbar x hxY * w := by group
  have hQq : IsQuasisimple ↥(C3.Layer1.PumpCalc.bar t Λ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hcomp.1
  have hΛK : Λ ≤ M := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, -, -⟩ := TwoThin.exists_phi hΛK hΛY hΛ.cover
  have hcard := (l3_card_bounds htK hp hp2 hq5 hmodK).1
  have hker : φ.ker ≤ Subgroup.center ↥(C3.Layer1.PumpCalc.bar t Λ) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQq (MonoidHom.normal_ker φ) with h | h
    · exfalso
      have hsub : Subsingleton (↥M ⧸ pPrimeCore 2 ↥M) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a', rfl⟩ := hφs a
        obtain ⟨b', rfl⟩ := hφs b
        have ha : a' ∈ φ.ker := by rw [h]; exact Subgroup.mem_top a'
        have hb : b' ∈ φ.ker := by rw [h]; exact Subgroup.mem_top b'
        rw [MonoidHom.mem_ker] at ha hb
        rw [ha, hb]
      have h1 : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
      omega
    · exact h
  exact ⟨hp, hp2, hq5, hQq.1, ⟨tK, htK, hmodK⟩, φ, hφs, hker⟩

noncomputable def conjSubEquiv {Z : Type} [Group Z] (g : Z) (L : Subgroup Z) :
    ↥L ≃* ↥(conjSub g L) :=
  Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem b_S3_pumpupStep_of_facts
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hFR : L3FRank) (hB2 : B_B2_g4) :
    B_S3_pumpupStep := by
  intro G _ _ hs hn hgen hK x t M M' hlt hd
  obtain ⟨-, hdisj⟩ := hd
  have hL3 : IsL3OddGt3 (↥M ⧸ pPrimeCore 2 ↥M) := by
    rcases hdisj with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    all_goals first | exact h | exact absurd h (by norm_num)
  obtain ⟨p, f, hp, hp2, hq3, hmod⟩ := hL3
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hq5 : 5 ≤ p ^ f := by omega
  obtain ⟨tK, htK, hmodK⟩ : ∃ tK : StatedLieTag, (tK = .PSL ∨ tK = .PSU) ∧
      LieModel (↥M ⧸ pPrimeCore 2 ↥M) tK 3 p f := by
    rcases hmod with h | h
    · exact ⟨.PSL, Or.inl rfl, h⟩
    · exact ⟨.PSU, Or.inr rfl, h⟩
  have hx2 : orderOf x = 2 := hlt.1.1
  have ht2 : orderOf t = 2 := hlt.2.1.1
  have hxY : x ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  have hKP : IsKProperSimple G := ⟨hs, hn, CFSG.GH74.kProper_of_kgh hK⟩
  have hMpc : IsPCompIn 2 (centralizer ({x} : Set G)) M := hlt.1.2.2
  obtain ⟨Λ, hΛ, hM'c, ⟨L, hLc, hM'L, hcases⟩, -, -, -⟩ := C3.Layer1.PumpRigid.step_core hlt hxY
  have hQcov := lam_l3Cover hB2 hKP hgen hx2 ht2 hxY hΛ hp hp2 hq5 htK hmodK
  have hcovL : ∃ A : Subgroup ↥L, IsL3Cover ↥A (↥M ⧸ pPrimeCore 2 ↥M) p f := by
    rcases hcases with ⟨-, hΛL⟩ | ⟨-, hAB, hΛd⟩
    · exact ⟨(C3.Layer1.PumpCalc.bar t Λ).subgroupOf L,
        hQcov.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΛL)⟩
    · exact exists_l3Cover_of_diag hAB (C3.Layer1.PumpCalc.bar_lam_perfect hΛ) hΛd hQcov
  obtain ⟨A, hA⟩ := hcovL
  obtain ⟨eM⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hMpc
  have hPK : Gen4Comp (↥M ⧸ pPrimeCore 2 ↥M) :=
    Gen4Comp.of_mulEquiv eM.symm (gen4Comp_of_gen4Cen (gen4Cen_barQ hgen hx2) _)
  obtain ⟨hG2L, hcl⟩ := l3Cover_table hG hE hFR hs hn hgen hK ht2 hLc hA htK hmodK hPK
  obtain ⟨eM'⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hM'c
  have eLn : Nonempty (↥L ≃* (↥M' ⧸ pPrimeCore 2 ↥M')) := by
    rcases hM'L with h | h
    · exact ⟨(MulEquiv.subgroupCongr h.symm).trans eM'.symm⟩
    · exact ⟨((conjSubEquiv _ L).trans (MulEquiv.subgroupCongr h.symm)).trans eM'.symm⟩
  obtain ⟨eL⟩ := eLn
  refine ⟨inG2_of_mulEquiv eL hG2L, ?_⟩
  rcases hcl with h6 | ⟨hd7, hF⟩ | ⟨hd7, ⟨e⟩⟩
  · exact Or.inl (by rw [← d2_congr eL]; omega)
  · exact Or.inr (Or.inl ⟨by rw [← d2_congr eL]; exact hd7, by rw [← fRank_congr eL]; exact hF⟩)
  · exact Or.inr (Or.inr ⟨eL.symm.trans e⟩)

end CFSG.GH74.Generic.S3
