module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Ctx

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section TwoFix

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

omit [Finite G] in
theorem blkOf_mul (M L : Subgroup G) {a : G} (ha : a ∈ M) (b : G) :
    blkOf M L (a * b) =
      (blkOf M L b).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩)).toMonoidHom := by
  rw [blkOf, blkOf, map_conj_mul, barM_map_conj ha]

theorem Sp48Ctx.fix_two (c : Sp48Ctx P M H R X U A L) {k₁ : G} (hk₁ : k₁ ∈ H ⊓ M)
    (h01 : barM M L ≠ blkOf M L k₁)
    (h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁) {r : G}
    (hr : r ∈ R) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, c.h3.le_M hr⟩ ∈
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, c.h3.le_M hr⟩ ∈
        Subgroup.normalizer (blkOf M L k₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have h3 := c.h3
  have hrK : r ∈ H ⊓ M := h3.le_inf hr
  have hrM : r ∈ M := hrK.2
  set g := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ with hg
  have hinj : ∀ Y Z : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      Y.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj g).toMonoidHom → Y = Z :=
    fun Y Z h => Subgroup.map_injective (MulAut.conj g).injective h
  have e0 : (barM M L).map (MulAut.conj g).toMonoidHom = blkOf M L r := by
    rw [blkOf, barM_map_conj hrM]
  have e1 : (blkOf M L k₁).map (MulAut.conj g).toMonoidHom = blkOf M L (r * k₁) :=
    (blkOf_mul M L hrM k₁).symm
  have hrk₁ : r * k₁ ∈ H ⊓ M := (H ⊓ M).mul_mem hrK hk₁
  have hfix : (barM M L).map (MulAut.conj g).toMonoidHom = barM M L := by
    rcases h2 r hrK with h1 | h1
    · rw [e0, h1]
    · exfalso
      have hsw : (blkOf M L k₁).map (MulAut.conj g).toMonoidHom = barM M L := by
        rcases h2 (r * k₁) hrk₁ with h' | h'
        · rw [e1, h']
        · exfalso
          apply h01
          apply hinj
          rw [e0, e1, h1, h']
      have hg2 : g ^ 2 ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        show (barM M L).map (MulAut.conj (g ^ 2)).toMonoidHom = barM M L
        rw [pow_two, map_conj_mul, e0, h1, hsw]
      obtain ⟨a, ha⟩ := h3.isPGroup_R ⟨r, hr⟩
      have hra : (⟨r, hrM⟩ : M) ^ 3 ^ a = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val ha)
      have hga : g ^ 3 ^ a = 1 := by rw [hg, ← map_pow, hra, map_one]
      have hgN : (barM M L).map (MulAut.conj g).toMonoidHom = barM M L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_of_sq_mem hga hg2)
      rw [e0, h1] at hgN
      exact h01 hgN.symm
  have hfix₁ : (blkOf M L k₁).map (MulAut.conj g).toMonoidHom = blkOf M L k₁ := by
    rcases h2 (r * k₁) hrk₁ with h' | h'
    · exfalso
      apply h01
      apply hinj
      rw [hfix, e1, h']
    · rw [e1, h']
  exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix₁⟩

end TwoFix

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section TwoSmall

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.false_of_two_small (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3) {k₁ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (h01 : barM M L ≠ blkOf M L k₁)
    (h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁) : False := by
  have h3 := c.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  set Lb₁ := blkOf M L k₁ with hLb₁def
  set C₀ := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₀
  set C₁ := Subgroup.centralizer (Lb₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
  have hRM : R ≤ M := h3.le_M
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  have hLk₁ := h3.isWeakSBlock_map_conj c.block hk₁
  have hRN0 : barM M R ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    exact (c.fix_two hk₁ h01 h2 (Subgroup.mem_subgroupOf.mp hr)).1
  have hRN1 : barM M R ≤ Subgroup.normalizer (Lb₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    exact (c.fix_two hk₁ h01 h2 (Subgroup.mem_subgroupOf.mp hr)).2
  have hRL0 : R ≤ Subgroup.normalizer (L : Set G) :=
    c.block.toIsTwoPrimeComponent.le_normalizer hRN0 hRM
  have hRL1 : R ≤ Subgroup.normalizer ((L.map (MulAut.conj k₁).toMonoidHom : Subgroup G) :
      Set G) := hLk₁.toIsTwoPrimeComponent.le_normalizer hRN1 hRM
  have hUS : barM M R ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    Subgroup.map_mono (Subgroup.comap_mono ((hKeq ▸ h3.le_inf).trans inf_le_right))
  have hU3 : IsPGroup 3 (barM M R) := (hR3.comap_subtype (K := M)).map _
  have hPLK : blockParabolic M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
    (blockParabolic_le_barM hKeq c.block.le le_rfl).trans
      (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
  have hPLK1 :
      blockParabolic M (pCoreOf 2 H) (L.map (MulAut.conj k₁).toMonoidHom) ≤ barM M (H ⊓ M) :=
    (blockParabolic_conj_le_barPi hKeq c.block.le hk₁).trans
      (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
  have hγ0 := c.hOut G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp c.block
    (h3.nineThree c.h93 c.block)
    (h3.nineThree_not_one c.h85 c.hD2 c.block).1 (h3.not_isSylowTwoOf_inf c.h85 c.hD2 c.block)
    (fun W hW hWW => c.data.coprime_of_perfect (hW.trans hPLK) hWW) (barM M R) hUS hRN0 hU3
  have hγ1 := c.hOut G M (pCoreOf 2 H) _ h3.isKGroup.1 h3.asc81bHyp hLk₁ (h3.nineThree c.h93 hLk₁)
    (h3.nineThree_not_one c.h85 c.hD2 hLk₁).1 (h3.not_isSylowTwoOf_inf c.h85 c.hD2 hLk₁)
    (fun W hW hWW => c.data.coprime_of_perfect (hW.trans hPLK1) hWW) (barM M R) hUS hRN1 hU3
  set I₀ := barM M R ⊓ (Lb ⊔ C₀) with hI₀
  set I₁ := barM M R ⊓ (Lb₁ ⊔ C₁) with hI₁
  set RI := I₀ ⊓ I₁ with hRI
  have hidx : RI.relIndex (barM M R) ≤ 9 :=
    calc RI.relIndex (barM M R) ≤ I₀.relIndex (barM M R) * I₁.relIndex (barM M R) :=
          Subgroup.relIndex_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul hγ0 hγ1
  have hCR : R ⊓ blockCentralizer M L ⊓ blockCentralizer M (L.map (MulAut.conj k₁).toMonoidHom)
      = ⊥ := by
    by_contra hne
    obtain ⟨w, hwC, hwZ, hw1⟩ := exists_mem_inf_centerOf hR3 (inf_le_left.trans inf_le_left)
      (fun r hr => Subgroup.inf_normalizer_le_normalizer_inf ⟨
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr,
          mem_normalizer_blockCentralizer (hRM hr) (hRL0 hr)⟩,
        mem_normalizer_blockCentralizer (hRM hr) (hRL1 hr)⟩) hne
    have hwX := c.data.center_le hwZ
    have hXPi := (c.data.Pi_cases c.hB3 c.block).1
    have hwM : w ∈ M := hRM hwC.1.1
    have hwQ : mk ⟨w, hwM⟩ ∈ barM M (piOf M H L) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXPi hwX))
    have hw0 := (mem_blockCentralizer_iff ⟨w, hwM⟩).mp hwC.1.2
    have hw1' := (mem_blockCentralizer_iff ⟨w, hwM⟩).mp hwC.2
    have hw3 : IsPGroup 3 (Subgroup.zpowers (mk ⟨w, hwM⟩)) := by
      obtain ⟨a, ha⟩ := hR3 ⟨w, hwC.1.1⟩
      have hwa : (⟨w, hwM⟩ : M) ^ 3 ^ a = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val ha)
      exact isPGroup_zpowers_of_pow_prime_pow_eq_one (by rw [← map_pow, hwa, map_one])
    have h1 := c.eq_one hwQ hw3 fun k hk => by
      rcases h2 k hk with h | h
      · rw [h]; exact hw0
      · rw [h]; exact hw1'
    exact hw1 (eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) hR3 hwC.1.1
      (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))
  have hRIC : (C₀ ⊓ C₁) ⊓ RI = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hC0, hC1⟩, ⟨hxR, -⟩, -⟩ := hx
    obtain ⟨⟨r, hrM⟩, hr, rfl⟩ := hxR
    have hrC : r ∈ R ⊓ blockCentralizer M L ⊓
        blockCentralizer M (L.map (MulAut.conj k₁).toMonoidHom) :=
      ⟨⟨Subgroup.mem_subgroupOf.mp hr, (mem_blockCentralizer_iff ⟨r, hrM⟩).mpr hC0⟩,
        (mem_blockCentralizer_iff ⟨r, hrM⟩).mpr hC1⟩
    rw [hCR, Subgroup.mem_bot] at hrC
    subst hrC
    exact Subgroup.mem_bot.mpr (map_one _)
  have hRI3 : IsPGroup 3 RI := hU3.to_le (inf_le_left.trans inf_le_left)
  have hRIR : RI ≤ barM M R := inf_le_left.trans inf_le_left
  have hd0 : C₀.relIndex RI ≤ 3 := by
    have hdvd := relIndex_dvd_of_inner (Lb := Lb) (I := RI) (J := blockParabolic M (pCoreOf 2 H) L)
      (hRIR.trans hRN0) ((blockParabolic_le_barM' M (pCoreOf 2 H) L).trans Subgroup.le_normalizer)
      fun x hx => h3.exists_mem_blockParabolic c.h84 c.h86 c.hD2 c.hb c.block
        (hUS hx.1.1) hx.1.2
    have := relIndex_dvd_sylow hRI3 hdvd SL
    rw [hs] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hd1 : C₁.relIndex RI ≤ 3 := by
    have hdvd := h3.relIndex_centralizer_dvd' c.h84 c.h86 c.hD2 c.hb c.block hk₁
      (hRIR.trans hUS) (hRIR.trans hRN1) fun x hx => hx.2.2
    have := relIndex_dvd_sylow hRI3 hdvd SL
    rw [hs] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hRIcard : Nat.card RI ≤ 9 := by
    have e : (C₀ ⊓ C₁).relIndex RI = Nat.card RI := by
      rw [← Subgroup.inf_relIndex_right, hRIC, Subgroup.relIndex_bot_left]
    calc Nat.card RI = (C₀ ⊓ C₁).relIndex RI := e.symm
      _ ≤ C₀.relIndex RI * C₁.relIndex RI := Subgroup.relIndex_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul hd0 hd1
  have hcardR : Nat.card (barM M R) = 3 ^ 5 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hRM hR3, c.data.card_R]
  have hmul := (RI.subgroupOf (barM M R)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRIR).toEquiv, hcardR] at hmul
  have hidx' : (RI.subgroupOf (barM M R)).index ≤ 9 := hidx
  have := Nat.mul_le_mul hRIcard hidx'
  rw [hmul] at this
  norm_num at this

end TwoSmall

end CFSG.AGLEmbedding
