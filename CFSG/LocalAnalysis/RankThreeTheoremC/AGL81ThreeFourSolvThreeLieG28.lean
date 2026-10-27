module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoGTwoEight
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsAut
import CFSG.GH74.Uniqueness.Bender.Aut

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.AGLEmbedding.KFactProofs.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (center_adjointGroup_eq_bot)
open SolvNone

private theorem isSolvable_of_symThree_solvG28 {I₀ : Type} [Group I₀] [Finite I₀]
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) : Group.IsSolvable I₀ := by
  haveI hQ : Group.IsSolvable (I₀ ⧸ CFSG.pCore 2 I₀) := by
    rcases hb with ⟨⟨f⟩⟩ | ⟨L, _, _, hL, ⟨f⟩⟩
    · haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [Fintype.card_perm, Fintype.card_fin]; rfl)
      exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP L 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card (f := 2) (by rw [hL]; norm_num)
      have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := L) (p := 2) (f := 1)
        (by rw [hL]; norm_num)
      rw [pow_one] at hc
      haveI : Finite ↥(StatedSU 3 2 L) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      haveI := Fintype.ofFinite ↥(StatedSU 3 2 L)
      haveI : Group.IsSolvable ↥(StatedSU 3 2 L) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
      exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 I₀) :=
    (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 I₀)).isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 I₀)

private theorem exists_mul_of_two_pow_solvG28 {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]
    (hidx : (MulAut.conj : ↥K →* MulAut ↥K).range.index = 3) {y : Y} {k : ℕ}
    (hy : y ^ 2 ^ k = 1) : ∃ g ∈ K, ∃ c ∈ centralizer (K : Set Y), y = g * c := by
  set θ : Y →* MulAut ↥K := MulAut.conjNormal with hθ
  haveI : (MulAut.conj : ↥K →* MulAut ↥K).range.Normal :=
    CFSG.GH74.Uniqueness.Bender.normal_range_conj ↥K
  have hmem : θ y ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    rw [← QuotientGroup.eq_one_iff]
    have h3 : orderOf ((θ y : MulAut ↥K) : MulAut ↥K ⧸ (MulAut.conj : ↥K →* MulAut ↥K).range) ∣
        3 := by
      rw [← hidx, Subgroup.index]
      exact orderOf_dvd_natCard _
    have h2 : orderOf ((θ y : MulAut ↥K) : MulAut ↥K ⧸ (MulAut.conj : ↥K →* MulAut ↥K).range) ∣
        2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, ← map_pow, hy, map_one, QuotientGroup.mk_one])
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right _ (by norm_num)) h3 h2)
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, g.2, (g : Y)⁻¹ * y, mem_centralizer_iff.mpr fun m hm => ?_, by group⟩
  have h1 := congrArg (fun a : MulAut ↥K => ((a ⟨m, hm⟩ : ↥K) : Y)) hg
  simp only [hθ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  calc m * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * m * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h1]
    _ = (g : Y)⁻¹ * y * m := by group


theorem threeFourSolvThreeNoneAt_g28 (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex)
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .G2 q) :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  obtain ⟨F, _, _, hF, ⟨e₁⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)
  rw [hq2, hq3] at hF
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨M⟩ := exists_model (K := F) hF8
  let e₂ : (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group ≃* adjointGroup .G2 F :=
    e₁.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hSU : SUStruct M := su_struct M hF8 (suHyp M hF8)
  refine ThreeFourSolvThreeNoneAt.of_mulEquiv e₂.symm ?_
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ _ _ _ hcomp hER hE hEc hcore _ _ _ hσs hb _ _
  classical
  haveI := hKn
  obtain ⟨e⟩ := hKX
  set C := centralizer (K : Set Y) with hCdef
  obtain ⟨ε, hε⟩ := exists_equiv_gElt_mem_g28 M hF8 e R hER hE (by rw [hEc]; norm_num) hcore
  set ι : adjointGroup .G2 F →* Y := K.subtype.comp ε.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hιK : ∀ g : ↥K, ι (ε g) = g := fun g => by simp [hιdef]
  have hrange : ι.range = K := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (ε.symm x).2
    · intro hy
      exact ⟨ε ⟨y, hy⟩, hιK ⟨y, hy⟩⟩
  haveI : Finite (adjointGroup .G2 F) := Finite.of_injective ι hι
  have hKY : ¬ K ≤ Y₀ := by
    haveI := isSimpleGroup_X_g28 hF8
    obtain ⟨a, b, hab⟩ := exists_ne_comm_X_g28 hF8
    haveI : IsSimpleGroup ↥K := e.isSimpleGroup
    haveI : Group.IsPerfect ↥K :=
      ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K ⟨e.symm a, e.symm b, fun h =>
        hab (by simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h)⟩⟩
    exact hcomp K ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩ le_rfl
  have hcomap : Y₀.comap ι = SX M := comap_eq_SX_g28 M hF8 ε hε hKY
  set V : Subgroup Y := (VX M).map ι with hVdef
  have hVK : V ≤ K := hrange ▸ Subgroup.map_le_range ι _
  have hVY₀ : V ≤ Y₀ := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ Y₀.comap ι := hcomap ▸ VX_le_SX M hv
    exact this
  have hSXeq : (SX M).map ι = K ⊓ Y₀ := by
    rw [← hcomap, Subgroup.map_comap_eq, hrange]
  have hVXeq : ⁅SX M, SX M⁆ = VX M := by
    refine le_antisymm (commutator_SX_le_VX_g28 M) ?_
    calc VX M = ⁅VX M, VX M⁆ := hSU.1.symm
      _ ≤ ⁅SX M, SX M⁆ := Subgroup.commutator_mono (VX_le_SX M) (VX_le_SX M)
  have hVeq : V = ⁅K ⊓ Y₀, K ⊓ Y₀⁆ := by
    rw [hVdef, ← hVXeq, Subgroup.map_commutator, hSXeq]
  have hVperf : ⁅V, V⁆ = V := by
    rw [hVdef, ← Subgroup.map_commutator, hSU.1]
  have hVne : V ≠ ⊥ := by
    intro h
    have h1 : ι (zE M) ∈ V := Subgroup.mem_map_of_mem ι (zE_mem_VX M)
    rw [h, Subgroup.mem_bot] at h1
    exact zE_ne_one M (hι (h1.trans (map_one ι).symm))
  have hA : ∀ y ∈ Y₀, (K ⊓ Y₀).map (MulAut.conj y).toMonoidHom ≤ K ⊓ Y₀ := by
    rintro y hy _ ⟨a, ⟨haK, haY⟩, rfl⟩
    change y * a * y⁻¹ ∈ K ⊓ Y₀
    exact ⟨hKn.conj_mem a haK y, Y₀.mul_mem (Y₀.mul_mem hy haY) (Y₀.inv_mem hy)⟩
  have hVnorm : Y₀ ≤ normalizer (V : Set Y) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, hVeq] at hv ⊢
    have h1 : y * v * y⁻¹ ∈ (⁅K ⊓ Y₀, K ⊓ Y₀⁆).map (MulAut.conj y).toMonoidHom := ⟨v, hv, rfl⟩
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono (hA y hy) (hA y hy) h1
  have hVprop : ∀ W : Subgroup Y, W ≤ Y₀ → V ≤ normalizer (W : Set Y) →
      V ≤ W ∨ ⁅W, V⁆ = ⊥ := by
    intro W hWY hVW
    have hWV : ⁅W, V⁆ ≤ W ⊓ V := by
      rw [Subgroup.commutator_le]
      intro w hw v hv
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have h1 : v * w⁻¹ * v⁻¹ ∈ W := (mem_normalizer_iff.mp (hVW hv) _).mp (W.inv_mem hw)
        have h2 : w * v * w⁻¹ * v⁻¹ = w * (v * w⁻¹ * v⁻¹) := by group
        rw [h2]
        exact W.mul_mem hw h1
      · have h1 : w * v * w⁻¹ ∈ V := (mem_normalizer_iff.mp (hVnorm (hWY hw)) _).mp hv
        exact V.mul_mem h1 (V.inv_mem hv)
    have hHn : VX M ≤ normalizer ((W.comap ι ⊓ VX M : Subgroup _) : Set (adjointGroup .G2 F)) := by
      intro u hu
      refine Subgroup.mem_normalizer_fintype fun h hh => ?_
      have hh' : h ∈ W.comap ι ∧ h ∈ VX M := hh
      have hv : u * h * u⁻¹ ∈ VX M :=
        (VX M).mul_mem ((VX M).mul_mem hu hh'.2) ((VX M).inv_mem hu)
      have hw : ι (u * h * u⁻¹) ∈ W := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp (hVW ⟨u, hu, rfl⟩) (ι h)).mp hh'.1
      exact (⟨hw, hv⟩ : u * h * u⁻¹ ∈ W.comap ι ∧ u * h * u⁻¹ ∈ VX M)
    rcases hSU.2.1 (W.comap ι ⊓ VX M) inf_le_right hHn with h | h | h
    rotate_left 2
    · left
      rintro _ ⟨u, hu, rfl⟩
      have h1 : u ∈ W.comap ι ⊓ VX M := by rw [h]; exact hu
      exact h1.1
    all_goals
      have hHz : W.comap ι ⊓ VX M ≤ Subgroup.zpowers (zE M) := by
        first | exact h | (rw [h]; exact bot_le)
      right
      have h1 : ⁅⁅W, V⁆, V⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro w hw
        rw [mem_centralizer_iff]
        rintro _ ⟨u, hu, rfl⟩
        obtain ⟨hwW, ⟨u', hu', rfl⟩⟩ := Subgroup.mem_inf.mp (hWV hw)
        have hu'H : u' ∈ W.comap ι ⊓ VX M := ⟨hwW, hu'⟩
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hHz hu'H)
        have hzu : Commute (zE M) u := by
          have := mem_centralizer_iff.mp hu (zE M) (Set.mem_singleton _)
          exact this
        have hcomm : u * u' = u' * u := by
          rw [← hn]
          exact ((hzu.zpow_left n).eq).symm
        rw [← map_mul, ← map_mul, hcomm]
      have h2 : ⁅⁅V, W⁆, V⁆ = ⊥ := by rw [Subgroup.commutator_comm V W]; exact h1
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
      rw [hVperf] at h3
      rw [Subgroup.commutator_comm]
      exact h3
  haveI := isSolvable_of_symThree_solvG28 hb
  have hDV : ⁅σ.range, V⁆ = ⊥ := by
    rcases le_or_commutator_eq_bot_of_isSubnormal hVY₀ hVprop hσs with hVD | h
    · exfalso
      have hDs : Group.IsSolvable σ.range := Group.isSolvable_of_surjective σ.rangeRestrict_surjective
      exact hVne (CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le hVD hDs hVperf)
    · exact h
  have hidx : (MulAut.conj : ↥K →* MulAut ↥K).range.index = 3 := by
    have hcA : Nat.card (MulAut ↥K) = 3 * Nat.card ↥K := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv, card_aut hF8, Nat.card_congr e.toEquiv]
    have hcI : Nat.card (MulAut.conj : ↥K →* MulAut ↥K).range = Nat.card ↥K :=
      Nat.card_range_of_injective (conj_injective_of_center_eq_bot hZ)
    have h := (MulAut.conj : ↥K →* MulAut ↥K).range.card_mul_index
    rw [hcI, hcA] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_comm _ _))
  have hKC : K ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have h1 : (⟨g, hg.1⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (mem_centralizer_iff.mp hg.2 k k.2)
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have h2C : ∀ i : I₀, (∃ k : ℕ, i ^ 2 ^ k = 1) → σ i ∈ C := by
    rintro i ⟨k, hk⟩
    have hx2 : σ i ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨g, hgK, c, hcC, hxgc⟩ := exists_mul_of_two_pow_solvG28 hidx hx2
    have hxV : ∀ v ∈ V, v * σ i = σ i * v := by
      have h1 : σ.range ≤ centralizer (V : Set Y) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hDV
      exact fun v hv => mem_centralizer_iff.mp (h1 (MonoidHom.mem_range.mpr ⟨i, rfl⟩)) v hv
    have hgV : ∀ v ∈ V, g * v = v * g := by
      intro v hv
      have hcv : v * c = c * v := mem_centralizer_iff.mp hcC v (hVK hv)
      have h1 : v * (g * c) = g * c * v := by rw [← hxgc]; exact hxV v hv
      have h2 : v * g * c = g * v * c := by
        calc v * g * c = v * (g * c) := by group
          _ = g * c * v := h1
          _ = g * (c * v) := by group
          _ = g * (v * c) := by rw [hcv]
          _ = g * v * c := by group
      exact (mul_right_cancel h2).symm
    set g' : adjointGroup .G2 F := ε ⟨g, hgK⟩ with hg'
    have hιg : ι g' = g := hιK ⟨g, hgK⟩
    have hg'c : ∀ u ∈ VX M, u * g' = g' * u := by
      intro u hu
      apply hι
      rw [map_mul, map_mul, hιg]
      exact (hgV (ι u) ⟨u, hu, rfl⟩).symm
    have hg'z : g' ∈ Subgroup.zpowers (zE M) := by
      refine hSU.2.2.1 ⟨?_, mem_centralizer_iff.mpr hg'c⟩
      change g' ∈ Subgroup.centralizer ({zE M} : Set (adjointGroup .G2 F))
      refine mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      exact hg'c _ (zE_mem_VX M)
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg'z
      have h1 : g' ^ 3 = 1 := by
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, zE_pow_three M,
          one_zpow]
      rw [← hιg, ← map_pow, h1, map_one]
    have hg2 : g ^ 2 ^ k = 1 := by
      have hgc : Commute g c := mem_centralizer_iff.mp hcC g hgK
      have h1 : g ^ 2 ^ k * c ^ 2 ^ k = 1 := by rw [← hgc.mul_pow, ← hxgc, hx2]
      have h2 : g ^ 2 ^ k ∈ K ⊓ C := by
        refine ⟨K.pow_mem hgK _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact C.inv_mem (C.pow_mem hcC _)
      rwa [hKC, Subgroup.mem_bot] at h2
    have hg1 : g = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) (orderOf_dvd_of_pow_eq_one hg3)
      (orderOf_dvd_of_pow_eq_one hg2))
    rw [hxgc, hg1, one_mul]
    exact hcC
  have hDC : σ.range ≤ C := by
    rw [MonoidHom.range_eq_map, ← closure_twoElements_eq_top hb, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact h2C i hi
  exact (Subgroup.map_le_range σ _).trans hDC

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
