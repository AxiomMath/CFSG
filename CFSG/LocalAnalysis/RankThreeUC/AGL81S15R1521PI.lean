module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open scoped Pointwise

theorem exists_conj_centralized_aux_card {X : Type} [Group X] [Finite X] {E N : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (N : Set X)) (hdisj : E ⊓ N = ⊥) :
    Nat.card (N ⊔ E : Subgroup X) = Nat.card E * Nat.card N := by
  have hn1 := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have hn2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hEN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN
  rw [sup_comm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (E ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ E ⊔ N)).toEquiv]
  have hbot : N.subgroupOf E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : X) ∈ E ⊓ N := ⟨x.2, hx⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hc : Nat.card ↥(N.subgroupOf E) = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf E)
  rw [hc, mul_one] at h2
  rw [← h2]

theorem exists_conj_centralized_aux_main {X : Type} [Group X] [Finite X] {L N E P₀ : Subgroup X}
    {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hN : IsPGroup 2 N) (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set X))
    (hE : IsPGroup r E) (hEL : E ≤ L) (hP₀ : IsPGroup q P₀)
    (hcomm : ∀ y ∈ P₀, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ N) :
    ∃ x ∈ N, ∀ e ∈ E, ∀ y ∈ P₀, y * (x * e * x⁻¹) = (x * e * x⁻¹) * y := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : E ≤ Subgroup.normalizer (N : Set X) := hEL.trans hLN
  have hdisj : E ⊓ N = ⊥ := disjoint_iff.1 (IsPGroup.disjoint_of_ne r 2 hr2 E N hE hN)
  set F : Subgroup X := N ⊔ E with hF
  have hNF : N ≤ F := le_sup_left
  have hEF : E ≤ F := le_sup_right
  have hPN : ∀ y ∈ P₀, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    have h1 := hcomm y hy n (hNL hn)
    have h2 : y * n * y⁻¹ = (y * n * y⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact N.mul_mem h1 hn
  have hPF : P₀ ≤ Subgroup.normalizer (F : Set X) := by
    have key : ∀ y ∈ P₀, ∀ f ∈ F, y * f * y⁻¹ ∈ F := by
      intro y hy f hf
      have hle : F ≤ F.comap (MulAut.conj y).toMonoidHom := by
        refine sup_le ?_ ?_
        · intro n hn
          exact hNF (hPN y hy n hn)
        · intro e he
          show y * e * y⁻¹ ∈ F
          have h1 := hcomm y hy e (hEL he)
          have h2 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
          rw [h2]
          exact F.mul_mem (hNF h1) (hEF he)
      exact hle hf
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨key y hy f, fun h => ?_⟩
    have h1 := key y⁻¹ (P₀.inv_mem hy) _ h
    simpa [mul_assoc] using h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥N)).1 hN
  have hcardF : Nat.card F = Nat.card E * Nat.card N :=
    exists_conj_centralized_aux_card hEN hdisj
  have hEcard : Nat.card ↥(E.subgroupOf F) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv
  have hidx : (E.subgroupOf F).index = 2 ^ k := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf F)
    rw [hEcard, hcardF, hk] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hnd2 : ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ (E.subgroupOf F).index := by
    intro s hs hs2 hdvd
    rw [hidx] at hdvd
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 (hs.dvd_of_dvd_pow hdvd))
  have hE' : IsPGroup r (E.subgroupOf F) := hE.comap_subtype
  let S0 : Sylow r ↥F := hE'.toSylow (hnd2 r hr hr2)
  letI : MulDistribMulAction ↥P₀ ↥F := MulDistribMulAction.compHom ↥F (Subgroup.inclusion hPF)
  have hfix := hP₀.card_modEq_card_fixedPoints (Sylow r ↥F)
  have hnd : ¬ q ∣ Nat.card (Sylow r ↥F) := fun h =>
    hnd2 q hq hq2 (h.trans (Sylow.card_dvd_index S0))
  have hne : Nonempty (MulAction.fixedPoints ↥P₀ (Sylow r ↥F)) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Nat.card (MulAction.fixedPoints ↥P₀ (Sylow r ↥F)) = 0 := Nat.card_of_isEmpty
    rw [h0] at hfix
    exact hnd (Nat.modEq_zero_iff_dvd.1 hfix)
  obtain ⟨⟨S1, hS1⟩⟩ := hne
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥F S0 S1
  set E1 : Subgroup X := (S1 : Subgroup ↥F).map F.subtype with hE1
  have hE1p : IsPGroup r E1 := S1.isPGroup'.map F.subtype
  have hinv : ∀ y ∈ P₀, ∀ z ∈ E1, y * z * y⁻¹ ∈ E1 := by
    intro y hy z hz
    obtain ⟨f, hf, rfl⟩ := hz
    have h1 : (⟨y, hy⟩ : ↥P₀) • f ∈ (⟨y, hy⟩ : ↥P₀) • (S1 : Subgroup ↥F) :=
      Subgroup.smul_mem_pointwise_smul f _ _ hf
    rw [← Sylow.pointwise_smul_def, hS1 ⟨y, hy⟩] at h1
    exact ⟨_, h1, rfl⟩
  have hmem : ∀ e ∈ E, ∃ f ∈ S1, (f : X) = (g : X) * e * (g : X)⁻¹ := by
    intro e he
    have h1 : (MulAut.conj g) ⟨e, hEF he⟩ ∈ (MulAut.conj g) • (S0 : Subgroup ↥F) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (show (⟨e, hEF he⟩ : ↥F) ∈ S0 from he)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact ⟨_, h1, rfl⟩
  have hgF : (g : X) ∈ (↑(N ⊔ E) : Set X) := g.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N E hEN] at hgF
  obtain ⟨n, hn, e₀, he₀, hne₀⟩ := hgF
  refine ⟨n, hn, fun e he y hy => ?_⟩
  have hnL : n ∈ L := hNL hn
  have he'' : n * e * n⁻¹ ∈ E1 := by
    have he' : e₀⁻¹ * e * e₀ ∈ E := E.mul_mem (E.mul_mem (E.inv_mem he₀) he) he₀
    obtain ⟨f, hf, hfe⟩ := hmem _ he'
    refine ⟨f, hf, ?_⟩
    rw [Subgroup.coe_subtype] at *
    rw [hfe, ← hne₀]
    group
  have hl : n * e * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hnL (hEL he)) (L.inv_mem hnL)
  have h1 : y * (n * e * n⁻¹) * y⁻¹ ∈ E1 := hinv y hy _ he''
  have h2 : y * (n * e * n⁻¹) * y⁻¹ * (n * e * n⁻¹)⁻¹ ∈ E1 := E1.mul_mem h1 (E1.inv_mem he'')
  have h3 : y * (n * e * n⁻¹) * y⁻¹ * (n * e * n⁻¹)⁻¹ ∈ N := hcomm y hy _ hl
  have hE1N : E1 ⊓ N = ⊥ := disjoint_iff.1 (IsPGroup.disjoint_of_ne r 2 hr2 E1 N hE1p hN)
  have h4 : y * (n * e * n⁻¹) * y⁻¹ * (n * e * n⁻¹)⁻¹ = 1 := by
    have h5 : y * (n * e * n⁻¹) * y⁻¹ * (n * e * n⁻¹)⁻¹ ∈ E1 ⊓ N := ⟨h2, h3⟩
    rwa [hE1N, Subgroup.mem_bot] at h5
  calc y * (n * e * n⁻¹)
      = (y * (n * e * n⁻¹) * y⁻¹ * (n * e * n⁻¹)⁻¹) * (n * e * n⁻¹) * y := by group
    _ = (n * e * n⁻¹) * y := by rw [h4, one_mul]

theorem exists_conj_centralized_aux_commutator {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {y : X} (hy : y ∈ cMHat L) {l : X} (hl : l ∈ L) : y * l * y⁻¹ * l⁻¹ ∈ CFSG.pCore 2 X := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) y ∈ cMBar L := hy
  have h2 := Subgroup.mem_centralizer_iff.1 h1 (QuotientGroup.mk' (CFSG.pCore 2 X) l) ⟨l, hl, rfl⟩
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 X) (y * l * y⁻¹ * l⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
    group
  exact (QuotientGroup.eq_one_iff _).1 h3

theorem exists_conj_centralized_aux_conj {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsC2 L) {y : X} (hy : y ∈ cMHat L) {l : X} (hl : l ∈ L) : y * l * y⁻¹ ∈ L := by
  have hle : L ≤ L.comap (MulAut.conj y).toMonoidHom := by
    calc L = oddHull L := hL.2.1.symm
      _ ≤ L.comap (MulAut.conj y).toMonoidHom := by
        unfold oddHull
        refine (Subgroup.closure_le _).2 ?_
        rintro h ⟨hhL, hodd⟩
        show y * h * y⁻¹ ∈ L
        have hc : y * h * y⁻¹ * h⁻¹ ∈ CFSG.pCore 2 X :=
          exists_conj_centralized_aux_commutator hy hhL
        have hx : y * h * y⁻¹ ∈ L ⊔ CFSG.pCore 2 X := by
          have h2 : y * h * y⁻¹ = (y * h * y⁻¹ * h⁻¹) * h := by group
          rw [h2, sup_comm]
          exact Subgroup.mul_mem_sup hc hhL
        have hord : orderOf (y * h * y⁻¹) = orderOf h :=
          orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective h
        exact isC2_eq_of_barO2_eq_aux2 hL hx (hord ▸ hodd)
  exact hle hl

theorem exists_conj_centralized {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : IsC2 L)
    {P₀ : Subgroup X} {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hP₀ : IsPGroup q P₀) (hcomm : P₀ ≤ cMHat L) {E : Subgroup X} (hE : IsPGroup r E) (hEL : E ≤ L) :
    ∃ x ∈ O2In L, ∀ e ∈ E, ∀ y ∈ P₀, y * (x * e * x⁻¹) = (x * e * x⁻¹) * y := by
  have hN2 : IsPGroup 2 (O2In L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := X)).to_le inf_le_right
  have hNL : O2In L ≤ L := inf_le_left
  have hconj : ∀ l ∈ L, ∀ n ∈ O2In L, l * n * l⁻¹ ∈ O2In L := fun l hl n hn =>
    ⟨L.mul_mem (L.mul_mem hl (hNL hn)) (L.inv_mem hl),
      (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem n hn.2 l⟩
  have hLN : L ≤ Subgroup.normalizer (O2In L : Set X) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hconj l hl n, fun h => ?_⟩
    have h1 := hconj l⁻¹ (L.inv_mem hl) _ h
    simpa [mul_assoc] using h1
  have hcomm' : ∀ y ∈ P₀, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ O2In L := fun y hy l hl =>
    ⟨L.mul_mem (exists_conj_centralized_aux_conj hL (hcomm hy) hl) (L.inv_mem hl),
      exists_conj_centralized_aux_commutator (hcomm hy) hl⟩
  exact exists_conj_centralized_aux_main hq hq2 hr hr2 hN2 hNL hLN hE hEL hP₀ hcomm'

theorem gamma_le_of_le_lift_aux_mem_map_conj {G : Type} [Group G] (R : Subgroup G) (a h : G) :
    h ∈ R.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * h * a ∈ R := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ht
  · intro h1
    exact ⟨a⁻¹ * h * a, h1, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem gamma_le_of_le_lift_aux_conj {G : Type} [Group G] [Finite G] {M R : Subgroup G} {a : G}
    (ha : a ∈ M) {r : ℕ} (hr : r.Prime)
    (h : rankThreeGamma 1 r (R.map (MulAut.conj a).toMonoidHom) ≤ M) :
    rankThreeGamma 1 r R ≤ M := by
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q hQR hQk g hg
  have hQ'R : Q.map (MulAut.conj a).toMonoidHom ≤ R.map (MulAut.conj a).toMonoidHom :=
    Subgroup.map_mono hQR
  have hk : 1 ≤ CFSG.Open.pRank r (Q.map (MulAut.conj a).toMonoidHom) :=
    hQk.trans (CFSG.SectionRank.pRank_le_map hr.one_lt _ (MulAut.conj a).injective Q)
  have hN : Subgroup.normalizer ((Q.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) ≤
      rankThreeGamma 1 r (R.map (MulAut.conj a).toMonoidHom) :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQ'R hk
  have hnorm : a * g * a⁻¹ ∈
      Subgroup.normalizer ((Q.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [gamma_le_of_le_lift_aux_mem_map_conj, gamma_le_of_le_lift_aux_mem_map_conj]
    have e1 : a⁻¹ * (a * g * a⁻¹ * t * (a * g * a⁻¹)⁻¹) * a = g * (a⁻¹ * t * a) * g⁻¹ := by group
    rw [e1]
    exact Subgroup.mem_normalizer_iff.1 hg (a⁻¹ * t * a)
  have h1 : a * g * a⁻¹ ∈ M := h (hN hnorm)
  have h2 : g = a⁻¹ * (a * g * a⁻¹) * a := by group
  rw [h2]
  exact M.mul_mem (M.mul_mem (M.inv_mem ha) h1) ha

theorem gamma_le_of_le_lift_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hO1217 : O1217At G M) {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup ↥M} (hEL : E ≤ L) (hEa : IsElemAbelian r E)
    (hE : Nat.card E = r ^ 2) : rankThreeGamma 1 r (E.map M.subtype) ≤ M := by
  obtain ⟨q, hq⟩ := ctx.p_mem
  have hqP : q.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1
  have hq2 : q ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd q hq.1
  have hq3 : q ≠ 3 := fun h => h11 (h ▸ hq)
  have hq5 : 5 ≤ q := by
    have h2 := hqP.two_le
    by_contra hlt
    have h4 : q = 4 := by omega
    rw [h4] at hqP
    exact absurd hqP (by norm_num)
  have hrk : 1 < CFSG.Open.pRank q (cMBar L) := (h20 q hq Ls L hLs hL).2.1
  have hrk2 : 2 ≤ CFSG.Open.pRank q (cMHat L) := by
    refine two_le_pRank_of_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hqP hq2 (cMHat L) ?_
    have h1 : (cMHat L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (cMBar L)
    rw [h1]
    exact hrk
  obtain ⟨P₀, hP₀le, hP₀a, hP₀c⟩ := CFSG.SectionRank.exists_pRank hqP.one_lt (cMHat L)
  have hP₀p : IsPGroup q P₀ := IsPGroup.of_card hP₀c
  have hP₀rk : 2 ≤ CFSG.Open.pRank q P₀ :=
    hrk2.trans (CFSG.SectionRank.le_pRank hqP.one_lt le_rfl hP₀a hP₀c)
  have hEp : IsPGroup r E := IsPGroup.of_card hE
  obtain ⟨x, hxN, hx⟩ := exists_conj_centralized hL.1 hqP hq2 hr hr2 hP₀p hP₀le hEp hEL
  set xG : G := (x : G) with hxG
  have hxM : xG ∈ M := x.2
  set E1 : Subgroup G := (E.map M.subtype).map (MulAut.conj xG).toMonoidHom with hE1
  set PG : Subgroup G := P₀.map M.subtype with hPG
  have hE1M : E1 ≤ M := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact M.mul_mem (M.mul_mem hxM e.2) (M.inv_mem hxM)
  have hE1a : IsElemAbelian r E1 :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hEa M.subtype) _
  have hE1c : Nat.card E1 = r ^ 2 := by
    rw [hE1, Subgroup.card_map_of_injective (MulAut.conj xG).injective,
      Subgroup.card_map_of_injective M.subtype_injective, hE]
  have hPGc : PG ≤ Subgroup.centralizer (E1 : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have h1 := congrArg (fun w : ↥M => (w : G)) (hx e he y hy)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    simpa [MulAut.conj_apply] using h1.symm
  have hPGM : PG ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hdvd : q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E1 : Set G)) := by
    have h1 : Nat.card PG ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E1 : Set G)) :=
      Subgroup.card_dvd_of_le (le_inf hPGM hPGc)
    have h2 : Nat.card PG = q ^ CFSG.Open.pRank q (cMHat L) := by
      rw [hPG, Subgroup.card_map_of_injective M.subtype_injective, hP₀c]
    refine dvd_trans ?_ h1
    rw [h2]
    exact dvd_pow_self q (by omega)
  have hA : ∀ A : Subgroup G, A ≤ E1 → Nat.card A = r →
      2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G)) := by
    intro A hAE _
    have hPGA : PG ≤ Subgroup.centralizer (A : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.2 fun a ha =>
        Subgroup.mem_centralizer_iff.1 (hPGc hz) a (hAE ha)
    calc 2 ≤ CFSG.Open.pRank q P₀ := hP₀rk
      _ ≤ CFSG.Open.pRank q PG :=
        CFSG.SectionRank.pRank_le_map hqP.one_lt M.subtype M.subtype_injective P₀
      _ ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G)) :=
        CFSG.SectionRank.pRank_mono hqP.one_lt
          (le_inf hPGM (hPGA.trans (Subgroup.centralizer_le_normalizer _)))
  have hΓ : rankThreeGamma 1 r E1 ≤ M :=
    hO1217 q r hq hq5 hr hr2 E1 hE1M hE1a hE1c hdvd hA
  exact gamma_le_of_le_lift_aux_conj hxM hr hΓ

theorem gamma_le_of_le_lift (o1217 : O1217) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup ↥M} (hEL : E ≤ L) (hEa : IsElemAbelian r E)
    (hE : Nat.card E = r ^ 2) : rankThreeGamma 1 r (E.map M.subtype) ≤ M :=
  gamma_le_of_le_lift_gen (O1217At.of_ctx2 o1217 ctx) (S15CtxGen.of_ctx2 ctx) h11 h20 hLs hL hr
    hr2 hEL hEa hE

theorem pRank_lift_eq_one_of_isLThreeOdd_gen (hT : LieOddRankTable) (hKSML3 : KSML3) {X : Type}
    [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (h : IsLThreeOdd ↥Ls) : CFSG.Open.pRank 3 L = 1 := by
  have hLs : CFSG.Open.IsComponentOf Ls ⊤ := hl.comp.1
  have hsimple : IsSimpleGroup ↥Ls :=
    R1511C.isSimpleGroup_of_isLThreeTwoPow (R1511C.isLThreeTwoPow_of_isLThreeOdd h)
  have hZ : Subgroup.center ↥Ls = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Ls) with h0 | h0
    · exact h0
    · exfalso
      have hs : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.2.2.2
      have hsub : Subsingleton (↥Ls ⧸ Subgroup.center ↥Ls) := ⟨fun a b => by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        exact QuotientGroup.eq.2 (by rw [h0]; exact Subgroup.mem_top _)⟩
      obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
      exact hab (Subsingleton.elim a b)
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hl.gn hLs hl.lift
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hl.lift.1.component.2.2
  have e1 : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* ↥Ls :=
    eQ.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hodd := centre_barO2_odd hl.lift.1
  have hrank : CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barO2 L)) :=
    (pRank_barO2_eq hl.lift.1 Nat.prime_three (by norm_num)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))
  rw [hrank]
  obtain ⟨n, hn, hn'⟩ := h
  rcases hn' with ⟨-, d, q, hq, hd, ⟨e⟩⟩ | ⟨-, d, Q, hQp, hQe, hd, ⟨e⟩⟩
  · have := (hT.small _ hK 3 Nat.prime_three (by norm_num)).1 ⟨q, d, hq, hd, ⟨e1.trans e⟩⟩
    simpa using this
  · have hz : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
      (hKSML3 _ hK d ⟨e1.trans e⟩ hodd).1 (Or.inl ⟨Q, hQp, hQe ▸ hn, hd⟩)
    have hd' : IsClassicalOrG2Index d.1 := by rw [hd]; exact hQp
    have h1 := hT.chev _ hK d hd' ⟨e1.trans e⟩ 3 Nat.prime_three (by norm_num)
    rw [h1, hz, hd]
    have hQc : Q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def, hQp, hQe]
    simp only [mRankChev, rkLin, hQc, eP_two_pow_three, if_neg (Nat.not_even_iff_odd.2 hn)]
    norm_num

theorem pRank_lift_eq_one_of_isLThreeOdd (hT : LieOddRankTable) (hKSML3 : KSML3) {X : Type}
    [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtx X T T₁ T₂ Ls L) (h : IsLThreeOdd ↥Ls) : CFSG.Open.pRank 3 L = 1 :=
  pRank_lift_eq_one_of_isLThreeOdd_gen hT hKSML3 hl.toGen h

end CFSG.LocalAnalysis.RankThreeUC.S15
