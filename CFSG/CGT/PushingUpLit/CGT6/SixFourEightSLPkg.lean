module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightAltPkg
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSLNat
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSLFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem EightCtx.perfect_of_SL {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n) : ⁅Y, Y⁆ = Y := by
  have hY := h.hY.1
  rcases hY.quotient_type with hq | hp
  · exact inClassX_commutator_eq_self h.hY hq
  · exfalso
    obtain ⟨φ, -⟩ := hnat
    have hcard : Nat.card (↥Y ⧸ pCore 2 ↥Y) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := Nat.card_congr φ.toEquiv
    rw [hcard, card_SL2_eq, GaloisField.card 2 n (by omega)] at hp
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h3 : 2 ≤ (2 ^ n) ^ 2 - 1 := by omega
    exact Nat.not_prime_mul (by omega) (by omega) hp

theorem eight_sl_main {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) :
    ∃ 𝔘 : Subgroup (MulAut ↥(blockU Y)), 𝔘 ≤ autOn Y (blockU Y) ∧
      ∀ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A → ¬ A ≤ centralizerModCore Y →
        autOn A (blockU Y) = 𝔘 ∧
        (A ⊓ R).relIndex A = Nat.card (GaloisField 2 n) ∧
        (blockU Y ⊔ (omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) =
          omegaOneCenterIn R) ∧
        Nat.card (omegaOneCenterIn R) = wtG (omegaOneCenterIn R) A ∧
        (∀ a ∈ A, a ∉ R → omegaOneCenterIn R ⊓ Subgroup.centralizer ({a} : Set G) =
          omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) ∧
        (∀ a ∈ A, ∀ v ∈ omegaOneCenterIn R, ⁅a, v⁆ ∈ Subgroup.centralizer (A : Set G)) := by
  classical
  have hY := h.hY.1
  have hperf : ⁅Y, Y⁆ = Y := h.perfect_of_SL hn hnat
  have hV := isElemAbelian_omegaOneCenterIn R
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  have hU2 : CFSG.Open.IsElemAbelian 2 (blockU Y) := h.blockU_isElemAbelian
  have hXU : Y ≤ Subgroup.normalizer (blockU Y : Set G) := le_normalizer_blockU Y
  have hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq_SL hY hnat
  have hCUV : Subgroup.centralizer (omegaOneCenterIn R : Set G) ≤
      Subgroup.centralizer ((blockU Y) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV)
  let _ : CommGroup ↥(blockU Y) := commGroupOfElemAbelian hU2
  have hF : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨D⟩ := nonempty_slNatData_blockU hY hperf hnat hU2
  have hJN := h.jIn_le_normalizer
  have hJU : jIn (T : Subgroup G) ≤ Subgroup.normalizer (blockU Y : Set G) := fun g hg =>
    normalizer_le_normalizer_blockU Y (hJN hg)
  have hJ2 : IsPGroup 2 ↥(jIn (T : Subgroup G)) := T.isPGroup'.to_le (jIn_le _)
  have hQ2 : IsPGroup 2 ↥(autOn (jIn (T : Subgroup G)) (blockU Y)) :=
    hJ2.of_surjective (actOnRange (blockU Y) (jIn (T : Subgroup G)) hJU)
      (actOnRange_surjective _ _ hJU)
  have hQN : autOn (jIn (T : Subgroup G)) (blockU Y) ≤
      Subgroup.normalizer ((autOn Y (blockU Y) : Subgroup (MulAut ↥(blockU Y))) :
        Set (MulAut ↥(blockU Y))) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_autOn_iff.mp hg
    exact conjAct_mem_normalizer_autOn (hJN hj)
  have hgood : ∀ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A → ¬ A ≤ centralizerModCore Y →
      A ≤ jIn (T : Subgroup G) ∧
      (autOn A (blockU Y) ≤ Subgroup.normalizer ((autOn Y (blockU Y) :
        Subgroup (MulAut ↥(blockU Y))) : Set (MulAut ↥(blockU Y)))) ∧
      @IsElemAbelian2 ↥(blockU Y) (commGroupOfElemAbelian hU2) (autOn A (blockU Y)) ∧
      autOn A (blockU Y) ≠ ⊥ ∧
      Nat.card ↥(blockU Y) ≤ Nat.card ↥(autOn A (blockU Y)) *
        Nat.card ↥(@fixV ↥(blockU Y) (commGroupOfElemAbelian hU2) (autOn A (blockU Y))) := by
    intro A hA hnot
    have hAN : A ≤ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA
    have hAU : A ≤ Subgroup.normalizer (blockU Y : Set G) := fun g hg =>
      normalizer_le_normalizer_blockU Y (hAN hg)
    have hOff : IsOffG (omegaOneCenterIn R) A := h.isOffG hA hnot
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [jIn_eq_thompsonJ]
      exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
    · intro g hg
      obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
      exact conjAct_mem_normalizer_autOn (hAN ha₁)
    · refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
      · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
        obtain ⟨a₂, ha₂, rfl⟩ := mem_autOn_iff.mp hg'
        exact (conjAct_comm_eq_one_iff (blockU Y) a₁ a₂).mpr (hCUV (hOff.2.2.1 _ ha₁ _ ha₂))
      · obtain ⟨a₁, ha₁, rfl⟩ := mem_autOn_iff.mp hg
        rw [← map_pow, conjAct_eq_one_iff]
        exact hCUV (hOff.2.2.2.1 _ ha₁)
    · intro hbot
      apply hnot
      intro g hg
      refine EightCtx.mem_centralizerModCore_of_centralizer_blockU hC (hAN hg) ?_
      have h1 : conjAct (blockU Y) ⟨g, hAU hg⟩ ∈ autOn A (blockU Y) :=
        mem_autOn_iff.mpr ⟨⟨g, hAU hg⟩, hg, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (conjAct_eq_one_iff (blockU Y) _).mp h1
    · rw [card_autOn_eq_relIndex hAU, card_fixV_autOn_eq hU2 hAU]
      exact card_le_relIndex_mul_card_of_isOffG hV hOff hUV
  obtain ⟨A₀, hA₀, hnot₀⟩ := h.exists_isMax_not_le
  obtain ⟨𝔘, h𝔘E, h𝔘card, hall, -, -⟩ := sl_family D hF hQ2 hQN
    (𝒜 := {X | ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧
      ¬ A ≤ centralizerModCore Y ∧ autOn A (blockU Y) = X})
    ⟨autOn A₀ (blockU Y), A₀, hA₀, hnot₀, rfl⟩ (by
      rintro X ⟨A, hA, hnot, rfl⟩
      obtain ⟨hAJ, -, hAel, hne, hAw⟩ := hgood A hA hnot
      exact ⟨autOn_le_autOn (blockU Y) hAJ, hAel, hne, hAw⟩)
  refine ⟨𝔘, h𝔘E, fun A hA hnot => ?_⟩
  have hAeq : autOn A (blockU Y) = 𝔘 := hall _ ⟨A, hA, hnot, rfl⟩
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA
  have hAU : A ≤ Subgroup.normalizer (blockU Y : Set G) := fun g hg =>
    normalizer_le_normalizer_blockU Y (hAN hg)
  have hOff : IsOffG (omegaOneCenterIn R) A := h.isOffG hA hnot
  obtain ⟨-, hAnorm, hAel, hne, hAw⟩ := hgood A hA hnot
  obtain ⟨hAE, hcardA, hquad, hcardU⟩ := sl_core_of_ne_bot D hAnorm hAel hne hAw
  have hAU_R : A ⊓ Subgroup.centralizer (blockU Y : Set G) = A ⊓ R :=
    h.inf_centralizer_blockU_eq_inf hA hC
  have hrel : (A ⊓ R).relIndex A = Nat.card (GaloisField 2 n) := by
    rw [← hAU_R, ← card_autOn_eq_relIndex hAU]
    exact hcardA
  have hUcard : Nat.card ↥(blockU Y) =
      (A ⊓ R).relIndex A * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer (A : Set G)) := by
    have := hcardU
    rw [card_autOn_eq_relIndex hAU, card_fixV_autOn_eq hU2 hAU, hAU_R] at this
    exact this
  obtain ⟨hsupV, hwtEq⟩ := eight_vpart h hOff hUcard
  have hP3U : ∀ a ∈ A, a ∉ R → blockU Y ⊓ Subgroup.centralizer ({a} : Set G) =
      blockU Y ⊓ Subgroup.centralizer (A : Set G) := by
    intro a ha haR
    apply le_antisymm
    · intro u hu
      obtain ⟨huU, hua⟩ := Subgroup.mem_inf.mp hu
      refine Subgroup.mem_inf.mpr ⟨huU, ?_⟩
      have haN : a ∈ Subgroup.normalizer (blockU Y : Set G) := hAU ha
      set x : MulAut ↥(blockU Y) := conjAct (blockU Y) ⟨a, haN⟩ with hx
      have hxA : x ∈ autOn A (blockU Y) := mem_autOn_iff.mpr ⟨⟨a, haN⟩, ha, rfl⟩
      have hx1 : x ≠ 1 := by
        intro h1
        have h2 := (conjAct_eq_one_iff (blockU Y) _).mp h1
        have : a ∈ A ⊓ Subgroup.centralizer (blockU Y : Set G) := Subgroup.mem_inf.mpr ⟨ha, h2⟩
        rw [hAU_R] at this
        exact haR this.2
      have hw : x ⟨u, huU⟩ = ⟨u, huU⟩ := by
        apply Subtype.ext
        rw [hx, conjAct_apply']
        have := Subgroup.mem_centralizer_iff.mp hua a (Set.mem_singleton a)
        show a * u * a⁻¹ = u
        calc a * u * a⁻¹ = (u * a) * a⁻¹ := by rw [this]
          _ = u := by group
      have hfix := fixV_le_of_ne_one D hF hAE hne hcardA hcardU hxA hx1 hw
      have hfix' : (⟨u, huU⟩ : ↥(blockU Y)) ∈ fixOn hU2 A := hfix
      rw [fixOn_eq hU2 hAU, Subgroup.mem_subgroupOf] at hfix'
      exact hfix'
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  set CVA : Subgroup G := omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) with hCVA
  have hmul : ((blockU Y ⊔ CVA : Subgroup G) : Set G) = (blockU Y : Set G) * (CVA : Set G) := by
    refine Subgroup.coe_mul_of_left_le_normalizer_right (blockU Y) CVA (fun u hu => ?_)
    refine Subgroup.centralizer_le_normalizer (CVA : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact isElemAbelian_comm' hV hc.1 (hUV hu)
  have hdecomp : ∀ v ∈ omegaOneCenterIn R, ∃ u ∈ blockU Y, ∃ c ∈ CVA, v = u * c := by
    intro v hv
    have hvsup : v ∈ blockU Y ⊔ CVA := by rw [hsupV]; exact hv
    have hvmem : v ∈ (blockU Y : Set G) * (CVA : Set G) := by rw [← hmul]; exact hvsup
    obtain ⟨u, hu, c, hc, rfl⟩ := hvmem
    exact ⟨u, hu, c, hc, rfl⟩
  have hP3 : ∀ a ∈ A, a ∉ R → omegaOneCenterIn R ⊓ Subgroup.centralizer ({a} : Set G) = CVA := by
    intro a ha haR
    apply le_antisymm
    · intro v hv
      obtain ⟨hvV, hva⟩ := Subgroup.mem_inf.mp hv
      obtain ⟨u, hu, c, hc, rfl⟩ := hdecomp v hvV
      have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha
      have hua : a * u = u * a := by
        have h1 : a * (u * c) = (u * c) * a :=
          Subgroup.mem_centralizer_iff.mp hva a (Set.mem_singleton a)
        calc a * u = (a * (u * c)) * c⁻¹ := by group
          _ = ((u * c) * a) * c⁻¹ := by rw [h1]
          _ = u * (c * a) * c⁻¹ := by group
          _ = u * (a * c) * c⁻¹ := by rw [hca]
          _ = u * a := by group
      have huC : u ∈ blockU Y ⊓ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact hua⟩
      rw [hP3U a ha haR] at huC
      exact CVA.mul_mem ⟨hUV hu, huC.2⟩ hc
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hP4 : ∀ a ∈ A, ∀ v ∈ omegaOneCenterIn R, ⁅a, v⁆ ∈ Subgroup.centralizer (A : Set G) := by
    intro a ha v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := hdecomp v hv
    have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha
    have hcc : a * c * a⁻¹ = c := by rw [hca]; group
    have hcomm : ⁅a, u * c⁆ = ⁅a, u⁆ := by
      simp only [commutatorElement_def]
      calc a * (u * c) * a⁻¹ * (u * c)⁻¹
          = (a * u * a⁻¹) * (a * c * a⁻¹) * c⁻¹ * u⁻¹ := by group
        _ = a * u * a⁻¹ * u⁻¹ := by rw [hcc]; group
    rw [hcomm]
    have haN : a ∈ Subgroup.normalizer (blockU Y : Set G) := hAU ha
    have hxA : conjAct (blockU Y) ⟨a, haN⟩ ∈ autOn A (blockU Y) :=
      mem_autOn_iff.mpr ⟨⟨a, haN⟩, ha, rfl⟩
    have hgen : conjAct (blockU Y) ⟨a, haN⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(blockU Y))⁻¹ ∈
        @commV ↥(blockU Y) (commGroupOfElemAbelian hU2) (autOn A (blockU Y)) :=
      Subgroup.subset_closure ⟨_, hxA, ⟨u, hu⟩, rfl⟩
    have hfix : conjAct (blockU Y) ⟨a, haN⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(blockU Y))⁻¹ ∈
        fixOn hU2 A := hquad hgen
    rw [fixOn_eq hU2 hAU, Subgroup.mem_subgroupOf] at hfix
    have e : (((conjAct (blockU Y) ⟨a, haN⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(blockU Y))⁻¹ : ↥(blockU Y)) :
        G)) = ⁅a, u⁆ := by
      rw [Subgroup.coe_mul, conjAct_apply', Subgroup.coe_inv, commutatorElement_def]
    rw [← e]
    exact hfix
  exact ⟨hAeq, hrel, hsupV, hwtEq, hP3, hP4⟩

end CFSG.CGT.PushingUpLit.CGT6
