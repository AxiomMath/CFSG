module

public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
import CFSG.LocalAnalysis.AGLEmbedding.EscapeRankBar
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section A9MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}

theorem D1A9DataCore.le_normalizer (h : D1A9DataCore P M H R X σ z) :
    R ≤ Subgroup.normalizer (X : Set G) := fun _ hr =>
  h.normalizer_le ⟨h.surv.ph3.le_inf hr, Subgroup.le_normalizer hr⟩

theorem D1A9DataCore.orderOf_z (h : D1A9DataCore P M H R X σ z) : orderOf z = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (h.elem.2 z h.z_mem) h.z_ne

theorem D1A9DataCore.centerOf_le (h : D1A9DataCore P M H R X σ z) : centerOf R ≤ X :=
  h.center_le.trans ((Subgroup.zpowers_le).mpr h.z_mem)

theorem D1A9DataCore.sup_zpowers_eq (h : D1A9DataCore P M H R X σ z) :
    X ⊔ Subgroup.zpowers σ = R := by
  have hle : X ⊔ Subgroup.zpowers σ ≤ R :=
    sup_le h.surv.le_R ((Subgroup.zpowers_le).mpr h.σ_mem)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hdvd : Nat.card (X ⊔ Subgroup.zpowers σ : Subgroup G) ∣ 3 ^ 4 := by
    rw [← h.card_R]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h27 : 3 ^ 3 ∣ 3 ^ k := by
    rw [← hk, ← h.card_X]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h27
  have hk3' : k ≠ 3 := by
    rintro rfl
    have he : X = X ⊔ Subgroup.zpowers σ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, h.card_X])
    exact h.σ_not_mem (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
  rw [h.card_R, hk]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem D1A9DataCore.le_sup_blockCentralizer (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) : X ≤ L ⊔ blockCentralizer M L :=
  h.surv.le_sup_blockCentralizer hB3 hL

theorem D1A9DataCore.exists_map_conj_eq (h : D1A9DataCore P M H R X σ z) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') :
    ∃ k ∈ H ⊓ M, L.map (MulAut.conj k).toMonoidHom = L' :=
  h.surv.exists_map_conj_eq h84 hD2 hB3 hO hL hL'

theorem D1A9DataCore.eq_of_not_mem_normalizer (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') (hσL : σ ∉ Subgroup.normalizer (L : Set G)) :
    L' = L ∨ L' = L.map (MulAut.conj σ).toMonoidHom ∨
      L' = (L.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ).toMonoidHom := by
  have hσK : σ ∈ H ⊓ M := h.surv.ph3.le_inf h.σ_mem
  have hσS : σ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h.surv.ph3.inf_eq_inf_normalizer_twoCore ▸ hσK).2
  have hL₁ := hL.map_conj hσK.2 hσS
  have hL₂ := hL₁.map_conj hσK.2 hσS
  have h01 : L ≠ L.map (MulAut.conj σ).toMonoidHom := fun he =>
    hσL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h12 : L.map (MulAut.conj σ).toMonoidHom ≠
      (L.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ).toMonoidHom := fun he =>
    h01 (Subgroup.map_injective (MulAut.conj σ).injective he)
  have h02 : L ≠ (L.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj σ).toMonoidHom := by
    intro he
    rw [← map_conj_mul_eq] at he
    have hσ2 : σ * σ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm
    have hσ4 : σ = (σ * σ) * (σ * σ) := by
      calc σ = σ ^ 3 * σ := by rw [h.σ_pow, one_mul]
        _ = (σ * σ) * (σ * σ) := by rw [pow_three']; simp only [mul_assoc]
    exact hσL (by rw [hσ4]; exact Subgroup.mul_mem _ hσ2 hσ2)
  exact h.surv.ph3.eq_or_eq_or_eq_of_isWeakSBlock h.pRank_le hB3 hL hL₁ hL₂ hL' h01 h02 h12

theorem D1A9DataCore.faithful (h : D1A9DataCore P M H R X σ z) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {r : G} (hr : r ∈ R)
    (hrC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → r ∈ blockCentralizer M L) :
    r = 1 :=
  h.surv.faithful h.centerOf_le h84 hD2 hB3 hO hr hrC

theorem D1A9DataCore.exists_not_mem_blockCentralizer (h : D1A9DataCore P M H R X σ z)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) :
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ z ∉ blockCentralizer M L := by
  by_contra hne
  push Not at hne
  exact h.z_ne (h.surv.eq_one_of_forall_mem h84 hD2 hB3 hO h.z_mem hne)

theorem D1A9DataCore.z_mem_of_le (h : D1A9DataCore P M H R X σ z) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : Y ≠ ⊥) (hσY : σ ∈ Subgroup.normalizer (Y : Set G)) : z ∈ Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := Y ⊔ Subgroup.zpowers σ with hQ
  have hQR : Q ≤ R := sup_le (hYX.trans h.surv.le_R) ((Subgroup.zpowers_le).mpr h.σ_mem)
  have : Group.IsNilpotent ↥Q := (h.surv.ph3.isPGroup_R.to_le hQR).isNilpotent
  have hYQ : Y ≤ Q := le_sup_left
  have hYn : (Y.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYQ).mpr
    (sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).mpr hσY))
  have hY1 : Y.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYQ hy⟩ : Q) ∈ Y.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hy
    rw [hbot, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy')
  obtain ⟨⟨y, hyY, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hY1)
  have hyσ : σ * (y : G) * σ⁻¹ = y := by
    have h2 : σ * (y : G) = y * σ := congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ
      ⟨σ, Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)⟩)
    rw [h2, mul_inv_cancel_right]
  have hyX : (y : G) ∈ X := hYX (Subgroup.mem_subgroupOf.mp hyY)
  have hy1' : (y : G) ≠ 1 := fun he => hy1 (Subtype.ext (Subtype.ext he))
  have hoy : orderOf (y : G) = 3 := orderOf_eq_prime (h.elem.2 _ hyX) hy1'
  have heq : Subgroup.zpowers (y : G) = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr (h.fix _ hyX hyσ))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hoy, h.orderOf_z])
  exact (Subgroup.zpowers_le).mpr (Subgroup.mem_subgroupOf.mp hyY)
    (heq ▸ Subgroup.mem_zpowers z)

theorem D1A9DataCore.inf_blockCentralizer_eq_bot (h : D1A9DataCore P M H R X σ z) {L : Subgroup G}
    (hσL : σ ∈ Subgroup.normalizer (L : Set G)) (hzL : z ∉ blockCentralizer M L) :
    X ⊓ blockCentralizer M L = ⊥ := by
  by_contra hne
  have hσN : σ ∈ Subgroup.normalizer ((X ⊓ blockCentralizer M L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.le_normalizer h.σ_mem,
      mem_normalizer_blockCentralizer (h.surv.ph3.le_M h.σ_mem) hσL⟩
  exact hzL (h.z_mem_of_le inf_le_left hne hσN).2

theorem D1A9DataCore.exists_inf_blockCentralizer_eq_bot (h : D1A9DataCore P M H R X σ z)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hσ : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      σ ∈ Subgroup.normalizer (L : Set G)) :
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ X ⊓ blockCentralizer M L = ⊥ := by
  obtain ⟨L, hL, hzL⟩ := h.exists_not_mem_blockCentralizer h84 hD2 hB3 hO
  exact ⟨L, hL, h.inf_blockCentralizer_eq_bot (hσ L hL) hzL⟩

theorem D1A9DataCore.exists_isElemAbelian_le_barM (h : D1A9DataCore P M H R X σ z)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hXL : X ⊓ blockCentralizer M L = ⊥) :
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 3 := by
  obtain ⟨E, hE, hEe, hEc⟩ := h.surv.ph3.exists_isElemAbelian_le_barM h84 h86 hD2 hO hL h.elem
    (h.surv.le_R.trans h.surv.ph3.le_inf) (h.le_sup_blockCentralizer hB3 hL) hXL
  exact ⟨E, hE, hEe, hEc.trans h.card_X⟩

theorem D1A9DataCore.exists_card_le_barM (h : D1A9DataCore P M H R X σ z) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hRL : R ≤ L ⊔ blockCentralizer M L) (hRC : R ⊓ blockCentralizer M L = ⊥) :
    ∃ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ IsPGroup 3 U ∧
        Nat.card U = 3 ^ 4 := by
  obtain ⟨U, hU, ⟨e⟩⟩ := h.surv.ph3.exists_mulEquiv_le_barM h84 h86 hD2 hO hL
    h.surv.ph3.isPGroup_R h.surv.ph3.le_inf hRL hRC
  have hcard : Nat.card U = 3 ^ 4 := (Nat.card_congr e.toEquiv).trans h.card_R
  exact ⟨U, hU, IsPGroup.of_card hcard, hcard⟩

theorem D1A9DataCore.two_le_pRank_closure (h : D1A9DataCore P M H R X σ z) :
    2 ≤ Open.pRank 3 (Subgroup.closure ({σ, z} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Subgroup.closure ({σ, z} : Set G) with hD
  have hσz : σ * z = z * σ := Subgroup.mem_centralizer_iff.mp h.z_center σ h.σ_mem
  have hcomm : ({σ, z} : Set G).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first | exact Commute.refl _ | exact hσz | exact hσz.symm
  have hDc : IsMulCommutative D := Subgroup.isMulCommutative_closure hcomm
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      exacts [h.σ_pow, h.elem.2 _ h.z_mem]
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := congrArg Subtype.val
        ((isMulCommutative_iff.mp hDc) ⟨a, ha⟩ ⟨b, hb⟩)
      rw [(Commute.mul_pow hab 3), iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  have hDR : D ≤ R := (Subgroup.closure_le R).mpr
    (Set.insert_subset_iff.mpr ⟨h.σ_mem, Set.singleton_subset_iff.mpr (h.surv.le_R h.z_mem)⟩)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.surv.ph3.isPGroup_R.to_le hDR)
  have hσD : σ ∈ D := Subgroup.subset_closure (Set.mem_insert σ {z})
  have hzD : Subgroup.zpowers z ≤ D :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Set.mem_insert_of_mem σ rfl))
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers z) := by
      rw [hk, Nat.card_zpowers, h.orderOf_z]
      exact (Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 1)).trans (by norm_num)
    have he := Subgroup.eq_of_le_of_card_ge hzD hle
    exact h.σ_not_mem ((Subgroup.zpowers_le).mpr h.z_mem (he ▸ hσD))
  exact hk2.trans (le_csSup (pRank_bddAbove 3 Nat.prime_three D) ⟨D, le_rfl, ⟨hDc, hD3⟩, hk⟩)

theorem D1A9DataCore.pRank_centralizer_le_two (h : D1A9DataCore P M H R X σ z) :
    Open.pRank 3 (Subgroup.centralizer ((barM M (Subgroup.closure {σ, z}) :
      Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ≤ 2 := by
  have hDR : Subgroup.closure ({σ, z} : Set G) ≤ R := (Subgroup.closure_le R).mpr
    (Set.insert_subset_iff.mpr ⟨h.σ_mem, Set.singleton_subset_iff.mpr (h.surv.le_R h.z_mem)⟩)
  exact pRank_centralizer_barM_le_two Nat.prime_three (by decide) P h.surv.ph3.sylow_le
    h.surv.ph3.weakCore_le (hDR.trans h.surv.ph3.le_M) (h.surv.ph3.isPGroup_R.to_le hDR)
    h.two_le_pRank_closure h.escape

theorem D1A9DataCore.pRank_inf_centralizer_le_two (h : D1A9DataCore P M H R X σ z) (s t : M)
    (hs : (s : G) = σ) (ht : (t : G) = z) :
    Open.pRank 3 (Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) s} :
      Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) t} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ≤ 2 := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hD : Subgroup.closure ({σ, z} : Set G) = (Subgroup.closure ({s, t} : Set M)).map
      M.subtype := by
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.coe_subtype, hs, ht]
  have hbar : barM M (Subgroup.closure ({σ, z} : Set G)) =
      Subgroup.closure ({mk s, mk t} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [hD, barM_map_subtype, MonoidHom.map_closure, Set.image_pair]
  refine (pRank_mono 3 Nat.prime_three fun g hg => ?_).trans h.pRank_centralizer_le_two
  rw [hbar, Subgroup.mem_centralizer_iff]
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    exacts [Subgroup.mem_centralizer_iff.mp hg.1 _ rfl,
      Subgroup.mem_centralizer_iff.mp hg.2 _ rfl]
  | one => rw [one_mul, mul_one]
  | mul a b _ _ ha hb => exact Commute.mul_left ha hb
  | inv a _ ha => exact Commute.inv_left ha

theorem D1A9DataCore.coprime_card_of_perfect (h : D1A9DataCore P M H R X σ z) {Y : Subgroup G}
    (hY : Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) (hYp : ⁅Y, Y⁆ = Y) :
    Nat.Coprime 3 (Nat.card Y) := by
  have hYK : Y ≤ H ⊓ M := h.surv.ph3.inf_eq_inf_normalizer_twoCore ▸ hY
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (h.perfect_le Y hYK hYp))
    (glbPrimeCore_coprime 3 H)

theorem D1A9DataCore.pRank_barM_le_three (h : D1A9DataCore P M H R X σ z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    Open.pRank 3 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≤ 3 := by
  have hle : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M :=
    h.surv.ph3.inf_eq_inf_normalizer_twoCore ▸ fun x hx => ⟨hL.le hx.2, hx.1⟩
  exact (pRank_barM_le Nat.prime_three (by decide) M _ (hle.trans inf_le_right)).trans
    ((pRank_mono 3 Nat.prime_three hle).trans h.pRank_le)

theorem D1A9DataCore.isWeakSBlock_map_conj (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {g : G} (hg : g ∈ M) :
    IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj g).toMonoidHom) := by
  have hLg := hL.toIsTwoPrimeComponent.map_conj hg
  refine ⟨hLg, fun hle => ?_⟩
  have hLgK : L.map (MulAut.conj g).toMonoidHom ≤ H ⊓ M :=
    h.surv.ph3.inf_eq_inf_normalizer_twoCore ▸ le_inf hLg.le hle
  have hN := h.perfect_le _ hLgK hLg.perfect
  obtain ⟨y, ⟨-, hyL⟩, hy3, l, -, hlQ⟩ := hB3 h.surv.ph3 hL
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hlQ
    simp
  obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hya : y ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hyg : g * y * g⁻¹ ∈ GLBPrimeCore 3 H := hN ⟨y, hyL, rfl⟩
  have hya' : (g * y * g⁻¹) ^ 3 ^ a = 1 := by rw [conj_pow, hya, mul_one, mul_inv_cancel]
  have h1 : orderOf (g * y * g⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left a (glbPrimeCore_coprime 3 H)) (orderOf_dvd_of_pow_eq_one hya')
    (Subgroup.orderOf_dvd_natCard _ hyg)
  apply hy1
  calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
    _ = 1 := by rw [orderOf_eq_one_iff.mp h1, mul_one, inv_mul_cancel]

end A9MSide

end CFSG.AGLEmbedding
