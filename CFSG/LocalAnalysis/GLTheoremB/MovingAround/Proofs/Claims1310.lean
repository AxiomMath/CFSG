module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.GL83PartI.I_22_5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open Prop1310a5b (Good2319 IsAltOrChev IsPumpupOrSelf Agrp Kstar Input25_6A5)

@[expose] def Rank3CuM : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 → ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Good2319 (barOf 3 Kc) →
        Kc ≤ M

@[expose] def Rank3CuRes : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          Kc ≤ M

section Rank

variable {G : Type} [Group G] [Finite G]

theorem pRank_B_eq {m : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m 3 B M E A D T R L0 d) : CFSG.Open.pRank 3 B = m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pRank_eq_of_card h.bOne.1.1 (h.standing.card_eq h.bOne)

end Rank

section Cases

variable {G : Type} [Group G] [Finite G]

theorem isChevSimple_of_isLieChar {X : Type} [Group X] {q : ℕ} (h : IsLieChar (· = q) X) :
    q.Prime ∧ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (X ⧸ Subgroup.center X) := by
  obtain ⟨idx, ⟨e⟩, hc⟩ := h
  refine ⟨?_, Or.inl ⟨.lie idx, hc, ⟨e⟩⟩⟩
  have := idx.1.characteristic_prime
  rwa [hc] at this

theorem gamma_of_aut {B : Subgroup G} {u : G} {Kc : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBC : B ≤ Cg u) (hKc : GLAPComponent 3 (Cg u) Kc)
    (haut : 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) ≤ CFSG.Open.pRank 3 B) :
    barX 3 (Cg u) Kc ≤ GLBCore 3 2 (barX 3 (Cg u) B) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcoreX : GLAPPrimeCore 3 (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) = ⊥ :=
    Lemma1311.glaPPrimeCore_quot_eq_bot 3 ↥(Cg u)
  have hBel' : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBp : IsPGroup 3 ↥B := CFSG.LocalAnalysis.GLTheoremB.isPGroup_of_isElemAbelian' hBel
  have hrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp hBp hBC
  have e : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hautEq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(barX 3 (Cg u) Kc))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)).symm
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(barX 3 (Cg u) Kc))) <
      CFSG.Open.pRank 3 (barX 3 (Cg u) B) := by
    rw [hautEq, hrk]
    omega
  have h2 : 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(barX 3 (Cg u) Kc))) ≤
      CFSG.Open.pRank 3 (barX 3 (Cg u) B) := by
    rw [hautEq, hrk]
    exact haut
  exact GL83.I_22_5_proved _ 3 hp hcoreX _ hKc.2.2.1 _ hBel' h1 2 (by norm_num) h2

theorem gamma_of_rank (hI : Lemma1315b.Input23_19) {B : Subgroup G} {u : G} {Kc : Subgroup G}
    (hKG : CFSG.Open.IsKGroup ↥(Cg u)) (hBel : IsElemAbelian 3 B) (huB : u ∈ B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) ≤
      CFSG.Open.pRank 3 B)
    (hKc : GLAPComponent 3 (Cg u) Kc) (hgood : Good2319 (barOf 3 Kc)) :
    barX 3 (Cg u) Kc ≤ GLBCore 3 2 (barX 3 (Cg u) B) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBp : IsPGroup 3 ↥B := CFSG.LocalAnalysis.GLTheoremB.isPGroup_of_isElemAbelian' hBel
  have hBel' : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp hBp hBC
  have hKQ : CFSG.Open.IsKGroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) := isKGroup_barX_quotient hKG
  have hgood' : Good2319 ↥(barX 3 (Cg u) Kc) :=
    Prop1310a5b.good2319_of_equiv (quotEquivBarX hp hKc.1 hKc.2.1) hgood
  have hle : CFSG.Open.pRank 3 (barX 3 (Cg u) B) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  have htype : (∃ n : ℕ, IsAltType n (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 3 ∧ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q
        (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) ∨
      (∀ A : Subgroup (MulAut ↥(barX 3 (Cg u) Kc)), IsElemAbelian 3 A → CFSG.Open.pRank 3 A ≤ 2) := by
    rcases hgood' with ha | ⟨q, hq, hL⟩ | hc
    · exact Or.inl ha
    · obtain ⟨hqp, hch⟩ := isChevSimple_of_isLieChar hL
      exact Or.inr (Or.inl ⟨q, hqp, hq, hch⟩)
    · exact Or.inr (Or.inr hc)
  exact hI _ hKQ 3 hp (by norm_num) (barX 3 (Cg u) B) hBel' (by omega) (by omega) _ hKc.2.2.1 htype

theorem gamma_of_cent {B : Subgroup G} {u : G} {Kc : Subgroup G}
    (h2 : 2 ≤ CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))))) :
    barX 3 (Cg u) Kc ≤ GLBCore 3 2 (barX 3 (Cg u) B) := by
  have hKQ : barX 3 (Cg u) Kc ≤ Subgroup.centralizer ((barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
      Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    Subgroup.le_centralizer_iff.2 inf_le_right
  exact (hKQ.trans (Subgroup.centralizer_le_normalizer _)).trans (normalizer_le_glbCore inf_le_left h2)

theorem rank3CuM_of_res (hI : Lemma1315b.Input23_19)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hres : Rank3CuRes) : Rank3CuM := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 Kc hKc hgood
  have h139b' := h139b
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : GLStanding G m 3 := h.standing
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBm : CFSG.Open.pRank 3 B = m := pRank_B_eq h
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := hBm ▸ hS.four_le
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  by_cases hbal : IsStronglyLocallyOneBalanced 3 B u Kc
  swap
  · have h1 : Kc ≤ lambdaOf 3 B u := le_sSup ⟨hKc, hbal⟩
    have h2 : lambdaOf 3 B u ≤ lambdaStar 3 B u := le_sup_left.trans le_sup_left
    have h3 : lambdaStar 3 B u ≤ lambdaStarGroup 3 B :=
      le_iSup_of_le u (le_iSup_of_le huB (le_iSup_of_le hu1 le_rfl))
    exact h1.trans (h2.trans (h3.trans h.pre.2.1))
  by_cases hpi : IsPiGroup 3 (barOf 3 Kc)
  · have h1 : Kc ≤ piOf 3 u :=
      le_iSup₂_of_le (f := fun L (_ : GLAPComponent 3 (Cg u) L ∧
        IsPiGroup 3 (↥L ⧸ GLAPPrimeCore 3 ↥L)) => L) Kc ⟨hKc, hpi⟩ le_rfl
    exact h1.trans (le_sup_right.trans (h.uniq.clause_a u huB hu1))
  by_cases haut : 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) ≤ CFSG.Open.pRank 3 B
  · exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc (gamma_of_aut hBel hBC hKc haut)
  by_cases hN : B ≤ Subgroup.normalizer (Kc : Set G)
  swap
  · exfalso
    have hX : GLATwoLocalRank 3 ↥(Cg u) ≤ CFSG.Open.pRank 3 B :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three
        (Cg u)).trans (hS.rank_eq.trans hBm.symm).le
    have := (h112 G m 3 hS (Cg u) B Kc hBel hBC hX hKc hN).2.2
    omega
  by_cases hcen : 2 ≤ CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))))
  · exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc (gamma_of_cent hcen)
  by_cases hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) ≤
      CFSG.Open.pRank 3 B
  · exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
      (gamma_of_rank hI (Prop1310a5b.isKGroup_centralizer_of_standing hS hu1) hBel huB hB4 hrk hKc
        hgood)
  exact hres h h139b' hU u hu hu1 (by omega) Kc hKc hgood hN (by omega) (by omega) hpi hbal

end Cases

section Consumer

variable {G : Type} [Group G] [Finite G]

structure Cfg' (G : Type) [Group G] [Finite G] (m : ℕ) (B M L0 L L0b : Subgroup G) (d b u0 : G) :
    Prop where
  standing : GLStanding G m 3
  hBel : IsElemAbelian 3 B
  hM : ∀ u ∈ Subgroup.closure {u0, b}, u ≠ 1 → ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc →
    Good2319 (barOf 3 Kc) → Kc ≤ M
  hdord : orderOf d = 3
  hbB : b ∈ B
  hb1 : b ≠ 1
  hdb : d * b = b * d
  hu0B : u0 ∈ B
  hu01 : u0 ≠ 1
  hdu0 : d * u0 = u0 * d
  hbu0 : b * u0 = u0 * b
  hu0L0 : u0 ∈ L0
  hbL0 : GLBConj b L0 = L0
  hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 L0
  hq0 : CFSG.Open.IsQuasisimple (barOf 3 L0)
  hL0M : GLAPComponent 3 (M ⊓ Cg d) L0
  hL05 : IsAltType 5 (barOf 3 L0)
  hL0b : L0b = GLAPLayer 3 (L0 ⊓ Cg b)
  hL : L = ⨆ g ∈ GLAPLayer 3 (Cg d), GLBConj g L0b
  hLc : GLAPComponent 3 (Cg d) L
  hL0bc : GLAPComponent 3 (L ⊓ Cg b) L0b
  hL0b5 : IsAltType 5 (barOf 3 L0b)
  hnotPi : ¬ IsPiGroup 3 (barOf 3 L)

namespace Cfg'

variable {m : ℕ} {B M L0 L L0b : Subgroup G} {d b u0 : G}

theorem hbord (c : Cfg' G m B M L0 L L0b d b u0) : orderOf b = 3 :=
  orderOf_eq_prime (c.hBel.2 b c.hbB) c.hb1

theorem hu0ord (c : Cfg' G m B M L0 L L0b d b u0) : orderOf u0 = 3 :=
  orderOf_eq_prime (c.hBel.2 u0 c.hu0B) c.hu01

theorem hb3 (c : Cfg' G m B M L0 L L0b d b u0) : b ^ 3 = 1 := c.hbord ▸ pow_orderOf_eq_one b

theorem hL0bL (c : Cfg' G m B M L0 L L0b d b u0) : L0b ≤ L := by
  rw [c.hL]
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer 3 (Cg d)) => GLBConj g L0b) (1 : G) (one_mem _)
    (le_of_eq (gLBConj_one L0b).symm)

theorem hL0bY (c : Cfg' G m B M L0 L L0b d b u0) : L0b ≤ L0 ⊓ Cg b := by
  rw [c.hL0b]
  unfold GLAPLayer
  exact sSup_le fun K hK => hK.1

theorem hu0Y (c : Cfg' G m B M L0 L L0b d b u0) : u0 ∈ L0 ⊓ Cg b :=
  ⟨c.hu0L0, Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact c.hbu0⟩

theorem hu0L0b (c : Cfg' G m B M L0 L L0b d b u0) : u0 ∈ L0b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [c.hL0b]
  exact Prop1310a5b.mem_layer_of_three_element c.hbord c.hbL0 c.hcomm c.hq0 c.hu0Y c.hu0ord

theorem hu0L (c : Cfg' G m B M L0 L L0b d b u0) : u0 ∈ L := c.hL0bL c.hu0L0b

theorem bN0 (c : Cfg' G m B M L0 L L0b d b u0) : b ∈ Subgroup.normalizer (L0b : Set G) := by
  have hc : ∀ z ∈ L0b, b * z * b⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_iff.1 ((c.hL0bY hz).2) b (Set.mem_singleton b)
    rw [this]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [hc z hz]
    exact hz
  · intro h
    have hw : b * (b * z * b⁻¹) * b⁻¹ = b * z * b⁻¹ := hc _ h
    have hz : z = b⁻¹ * (b * z * b⁻¹) * b := by group
    have hw' : b⁻¹ * (b * z * b⁻¹) * b = b * z * b⁻¹ := by
      calc b⁻¹ * (b * z * b⁻¹) * b = b⁻¹ * (b * (b * z * b⁻¹) * b⁻¹) * b := by rw [hw]
        _ = b * z * b⁻¹ := by group
    have hzw : z = b * z * b⁻¹ := hz.trans hw'
    have h2 := h
    rw [← hzw] at h2
    exact h2

theorem u0N0 (c : Cfg' G m B M L0 L L0b d b u0) : u0 ∈ Subgroup.normalizer (L0b : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, c.hL0b, ← Prop1310a5b.glaPLayer_gLBConj',
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer c.hu0Y)]

theorem bN (c : Cfg' G m B M L0 L L0b d b u0) : b ∈ Subgroup.normalizer (L : Set G) := by
  rw [c.hL]
  exact Prop1310a5b.mem_normalizer_hull c.bN0 (Prop1310a5b.Cfg.normalizer_layer c.hdb)

theorem u0N (c : Cfg' G m B M L0 L L0b d b u0) : u0 ∈ Subgroup.normalizer (L : Set G) := by
  rw [c.hL]
  exact Prop1310a5b.mem_normalizer_hull c.u0N0 (Prop1310a5b.Cfg.normalizer_layer c.hdu0)

theorem hUN (c : Cfg' G m B M L0 L L0b d b u0) :
    Subgroup.closure {u0, b} ≤ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact c.u0N
  · exact c.bN

theorem hU1B (c : Cfg' G m B M L0 L L0b d b u0) : Subgroup.closure {u0, b} ≤ B := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact c.hu0B
  · exact c.hbB

theorem hU1d (c : Cfg' G m B M L0 L L0b d b u0) : ∀ u ∈ Subgroup.closure {u0, b}, d * u = u * d := by
  intro u hu
  have h : Subgroup.closure {u0, b} ≤ Cg d := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact c.hdu0
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact c.hdb
  exact Subgroup.mem_centralizer_iff.1 (h hu) d (Set.mem_singleton d)

end Cfg'

namespace Cfg'

variable {m : ℕ} {B M L0 L L0b : Subgroup G} {d b u0 : G}

noncomputable def xOf (c : Cfg' G m B M L0 L L0b d b u0) : MulAut (barOf 3 L) :=
  barAut 3 L ⟨b, c.bN⟩

noncomputable def yOf (c : Cfg' G m B M L0 L L0b d b u0) : barOf 3 L :=
  QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨u0, c.hu0L⟩

theorem hLq (c : Cfg' G m B M L0 L L0b d b u0) : CFSG.Open.IsQuasisimple (barOf 3 L) :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Lemma1313.isQuasisimple_barOf_of_pComp c.hLc

theorem hdne (c : Cfg' G m B M L0 L L0b d b u0) : d ≠ 1 := by
  rintro rfl
  have := c.hdord
  simp at this

theorem hKhat (c : Cfg' G m B M L0 L L0b d b u0) :
    CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf 3 L) :=
  Prop1310a5b.isKHat_barOf_of_comp (Prop1310a5b.isKGroup_centralizer_of_standing c.standing c.hdne) c.hLc

theorem xne (c : Cfg' G m B M L0 L L0b d b u0) : c.xOf ≠ 1 :=
  Prop1310a5b.barAut_ne_one c.bN c.hb3 c.hLq c.hL0bc c.hL0b5 c.hnotPi

theorem xorder (c : Cfg' G m B M L0 L L0b d b u0) : orderOf c.xOf = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime _ c.xne
  unfold xOf
  rw [← map_pow]
  have : (⟨b, c.bN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext c.hb3
  rw [this, map_one]

theorem hxA (c : Cfg' G m B M L0 L L0b d b u0) : c.xOf ∈ Agrp c.xOf c.yOf :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem hyL' (c : Cfg' G m B M L0 L L0b d b u0) : c.yOf ∈ barX 3 L L0b :=
  ⟨⟨u0, c.hu0L⟩, Subgroup.mem_subgroupOf.2 c.hu0L0b, rfl⟩

theorem yorder (c : Cfg' G m B M L0 L L0b d b u0) : orderOf c.yOf = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : c.yOf ^ 3 = 1 := by
    unfold yOf
    rw [← map_pow]
    have : (⟨u0, c.hu0L⟩ : ↥L) ^ 3 = 1 := Subtype.ext (c.hu0ord ▸ pow_orderOf_eq_one u0)
    rw [this, map_one]
  apply orderOf_eq_prime hy3
  intro hy1
  unfold yOf at hy1
  have hmem : (⟨u0, c.hu0L⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 hy1
  have hO : u0 ∈ GLAPPrimeCoreOf 3 L := ⟨⟨u0, c.hu0L⟩, hmem, rfl⟩
  exact Prop115.orderOf_ne_of_coprime_card Nat.prime_three hO
    (Lemma1313.coprime_card_glaPPrimeCoreOf 3 L) c.hu0ord

theorem hL'comp (c : Cfg' G m B M L0 L L0b d b u0) :
    GLAPComponent 3 (Prop1310a5.fixedSub c.xOf) (barX 3 L L0b) := by
  have hfix : Prop1310a5.fixedSub (barAut 3 L ⟨b, c.bN⟩) = barX 3 L (L ⊓ Cg b) := by
    have h := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub_barAut_eq c.hb3 c.bN
    rw [← h]
    exact Subgroup.ext fun _ => Iff.rfl
  unfold xOf
  rw [hfix]
  exact Prop115b.barX_glaPComponent_of_le Nat.prime_three (inf_le_left : L ⊓ Cg b ≤ L) c.hL0bc

theorem hL'5 (c : Cfg' G m B M L0 L L0b d b u0) : IsAltType 5 (barOf 3 (barX 3 L L0b)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f⟩ := c.hL0b5
  exact ⟨(Prop115.barOfIso (p := 3) c.hL0bL).symm.trans f⟩

theorem hconjyA (c : Cfg' G m B M L0 L L0b d b u0) : MulAut.conj c.yOf ∈ Agrp c.xOf c.yOf :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem exists_u_of_mem_A (c : Cfg' G m B M L0 L L0b d b u0) :
    ∀ a ∈ Agrp c.xOf c.yOf, ∃ (u : G) (hu : u ∈ Subgroup.closure {u0, b}),
      barAut 3 L ⟨u, c.hUN hu⟩ = a := by
  intro a ha
  have hu0U : u0 ∈ Subgroup.closure {u0, b} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbU : b ∈ Subgroup.closure {u0, b} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Prop1310a5b.closure_pair_induction (P := fun a => ∃ (u : G) (hu : u ∈ Subgroup.closure {u0, b}),
    barAut 3 L ⟨u, c.hUN hu⟩ = a) (a := c.xOf) (b := MulAut.conj c.yOf) ?_ ?_ ?_ ?_ ?_ ha
  · exact ⟨b, hbU, rfl⟩
  · exact ⟨u0, hu0U, Prop1310a5b.barAut_inner c.hu0L (c.hUN hu0U)⟩
  · exact ⟨1, one_mem _, map_one _⟩
  · rintro a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u * u', mul_mem hu hu', map_mul (barAut 3 L)
      (⟨u, c.hUN hu⟩ : ↥(Subgroup.normalizer (L : Set G))) ⟨u', c.hUN hu'⟩⟩
  · rintro a ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, inv_mem hu, map_inv (barAut 3 L)
      (⟨u, c.hUN hu⟩ : ↥(Subgroup.normalizer (L : Set G)))⟩

theorem barAut_mem_A (c : Cfg' G m B M L0 L L0b d b u0) :
    ∀ (u : G) (hu : u ∈ Subgroup.closure {u0, b}), barAut 3 L ⟨u, c.hUN hu⟩ ∈ Agrp c.xOf c.yOf := by
  intro u hu
  have key : ∃ hN : u ∈ Subgroup.normalizer (L : Set G), barAut 3 L ⟨u, hN⟩ ∈ Agrp c.xOf c.yOf := by
    refine Prop1310a5b.closure_pair_induction (P := fun u => ∃ hN : u ∈ Subgroup.normalizer (L : Set G),
      barAut 3 L ⟨u, hN⟩ ∈ Agrp c.xOf c.yOf) (a := u0) (b := b) ?_ ?_ ?_ ?_ ?_ hu
    · refine ⟨c.u0N, ?_⟩
      rw [Prop1310a5b.barAut_inner c.hu0L c.u0N]
      exact c.hconjyA
    · exact ⟨c.bN, c.hxA⟩
    · exact ⟨one_mem _, by
        have : barAut 3 L ⟨1, one_mem _⟩ = 1 := map_one _
        rw [this]
        exact one_mem _⟩
    · rintro u u' ⟨hN, h1⟩ ⟨hN', h2⟩
      refine ⟨mul_mem hN hN', ?_⟩
      have := mul_mem h1 h2
      rwa [← map_mul] at this
    · rintro u ⟨hN, h1⟩
      refine ⟨inv_mem hN, ?_⟩
      have := inv_mem h1
      rwa [← map_inv] at this
  obtain ⟨hN, h⟩ := key
  exact h

theorem bU1 (c : Cfg' G m B M L0 L L0b d b u0) : b ∈ Subgroup.closure {u0, b} :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem hL0bL0 (c : Cfg' G m B M L0 L L0b d b u0) : L0b ≤ L0 := c.hL0bY.trans inf_le_left

def Tfam (c : Cfg' G m B M L0 L L0b d b u0) (S : MulAut (barOf 3 L) → Set (Subgroup (barOf 3 L))) :
    Set (Subgroup G) :=
  {K0 | ∃ (u : G) (hu : u ∈ Subgroup.closure {u0, b}), barAut 3 L ⟨u, c.hUN hu⟩ ≠ 1 ∧
    GLAPComponent 3 (L ⊓ Cg u) K0 ∧ barX 3 L K0 ∈ S (barAut 3 L ⟨u, c.hUN hu⟩)}

def Jstar (c : Cfg' G m B M L0 L L0b d b u0) (S : MulAut (barOf 3 L) → Set (Subgroup (barOf 3 L))) :
    Subgroup G :=
  ⨆ K0 ∈ c.Tfam S, K0

theorem tfam_le_L (c : Cfg' G m B M L0 L L0b d b u0) {S : MulAut (barOf 3 L) → Set (Subgroup (barOf 3 L))}
    {K0 : Subgroup G} (hK0 : K0 ∈ c.Tfam S) : K0 ≤ L := by
  obtain ⟨u, hu, -, hc, -⟩ := hK0
  exact hc.1.trans inf_le_left

theorem Ks_eq (c : Cfg' G m B M L0 L L0b d b u0) (S : MulAut (barOf 3 L) → Set (Subgroup (barOf 3 L)))
    (hS0 : ∀ a ∈ Agrp c.xOf c.yOf, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) :
    Kstar (Agrp c.xOf c.yOf) S = barX 3 L (c.Jstar S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun J => iSup_le fun hJ => ?_
    obtain ⟨haA, ha1⟩ := ha
    obtain ⟨u, hu, rfl⟩ := c.exists_u_of_mem_A a haA
    have huB : u ∈ B := c.hU1B hu
    have hu3 : u ^ 3 = 1 := c.hBel.2 u huB
    have hJc := hS0 _ haA ha1 J hJ
    have hfix : Prop1310a5.fixedSub (barAut 3 L ⟨u, c.hUN hu⟩) = barX 3 L (L ⊓ Cg u) := by
      have h := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub_barAut_eq hu3 (c.hUN hu)
      rw [← h]
      exact Subgroup.ext fun _ => Iff.rfl
    rw [hfix] at hJc
    obtain ⟨K0, hK0c, hK0bar, -⟩ := Prop1310a5b.exists_lift (inf_le_left : L ⊓ Cg u ≤ L) hJc
    have hmemT : K0 ∈ c.Tfam S := ⟨u, hu, ha1, hK0c, by rw [hK0bar]; exact hJ⟩
    have hK0J : K0 ≤ c.Jstar S := le_iSup₂_of_le K0 hmemT le_rfl
    rw [← hK0bar]
    exact CFSG.LocalAnalysis.GLTheoremB.barX_mono 3 hK0J
  · have e : (⨆ K0 ∈ c.Tfam S, K0 : Subgroup G) = ⨆ k : c.Tfam S, (k : Subgroup G) := iSup_subtype'
    unfold Jstar
    rw [e]
    refine (barX_iSup_le_iSup (p := 3) (C := L) (ι := c.Tfam S) (fun k => (k : Subgroup G))
      (fun k => c.tfam_le_L k.2)).trans ?_
    refine iSup_le fun k => ?_
    obtain ⟨u, hu, hne, hK0c, hmem⟩ := k.2
    exact le_iSup_of_le (barAut 3 L ⟨u, c.hUN hu⟩) (le_iSup_of_le ⟨c.barAut_mem_A u hu, hne⟩
      (le_iSup_of_le (barX 3 L k.1) (le_iSup_of_le hmem le_rfl)))

end Cfg'

end Consumer

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310

end
