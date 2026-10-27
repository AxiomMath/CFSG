module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieSpSwap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicOvergroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHPSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.Open (pCoreOf)

theorem eq_bot_of_le_normalizer_psp {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr0 : 0 < r)
    (hc : StatedClassicalModel Y .PSp r 2 1) (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) : V = ⊥ := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hc
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  exact eq_bot_of_le_normalizer_borel (borelQuotient_sp e) (torus_sp_eq_bot hK2)
    ⟨⟨0, by show 0 < r; omega⟩⟩ T V hV hV3

theorem noSwap_of_psp {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (hpar : IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (hsolv : BlockPLThreeSolv M S L) {r : ℕ} (hr3 : 3 ≤ r) (hr4 : r ≤ 4)
    (hc : StatedClassicalModel (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) .PSp r 2 1)
    (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))))
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE9 : Nat.card E = 9)
    (hEP : E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :
    ¬ IrreducibleOn
      (Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer
          (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E := by
  classical
  intro hirr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := barM M L with hLb
  set P := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hP
  have hPL : P ≤ Lb := barM_mono inf_le_right
  have hperfLb : ⁅Lb, Lb⁆ = Lb := barM_perfect hL.le hL.perfect
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hEL : E ≤ Lb := hEP.trans hPL
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  have hE'3 : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEL).symm
  have hinj : ∀ x ∈ E', ρ x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hE'3 ⟨x, hx⟩
    have h3 : orderOf x ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥Lb) := Subgroup.orderOf_dvd_natCard _ hxc
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hZ3) h3 h2)
  have hcardE : Nat.card (E'.map ρ) = 9 := by
    rw [card_map_eq_of_inj_on ρ hinj, hE', ← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hEJ : E'.map ρ ≤ P'.map ρ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hEP (Subgroup.mem_subgroupOf.mp hx))
  have hNE : Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := inf_le_left.trans inf_le_left
  have hNP : Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := inf_le_left.trans inf_le_right
  have hNLb : Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := inf_le_right
  by_cases hsyl : IsSylowTwoOf (pCoreOf 2 P) Lb
  ·
    have hT' : IsSylowTwoOf ((pCoreOf 2 P).subgroupOf Lb) ⊤ := by
      have := L246C127.isSylowTwoOf_top_map_subgroupOf (MulEquiv.refl ↥Lb) hsyl
      simpa using this
    obtain ⟨S2, hS2⟩ := exists_sylow_of_isSylowTwoOf_top hT'
    have hPN : P' ≤ Subgroup.normalizer ((S2 : Subgroup ↥Lb) : Set ↥Lb) := by
      intro x hx
      rw [hS2, Subgroup.mem_normalizer_iff]
      intro z
      have hx' := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P
        (Subgroup.mem_subgroupOf.mp hx)) (z : ↥M ⧸ CFSG.pCore 2 ↥M)
      simpa [Subgroup.mem_subgroupOf] using hx'
    have hbot := eq_bot_of_le_normalizer_psp (by omega) hc (S2.mapSurjective hρs) (E'.map ρ)
      (by
        rw [Sylow.coe_mapSurjective]
        exact hEJ.trans ((Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map ρ)))
      (hE'3.map ρ)
    rw [hbot, Subgroup.card_bot] at hcardE
    omega
  · obtain ⟨T0, hT0, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hsyl hsolv
    obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT0
    rw [← hT'] at hNJ
    obtain ⟨E₁, hE₁E, hE₁c, hE₁N⟩ := sp_lines_Y (by omega) hr4 hc T' hNJ hJperf hEJ hcardE
    have hself := normalizer_le_of_normalizer_sylow_le T' hNJ
    have hX : AutInner (↥Lb ⧸ Subgroup.center ↥Lb) := autInner_psp_two hr3 hc
    obtain ⟨W, hWE, hW3, hWN⟩ := exists_line_of_cover hPL hEP hperfLb hX hZ3 hE3 hNLb hNE hNP
      hself E₁ hE₁E hE₁c hE₁N
    rcases hirr W hWE hWN with h | h
    · rw [h, Subgroup.card_bot] at hW3
      omega
    · rw [h, hE9] at hW3
      omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
