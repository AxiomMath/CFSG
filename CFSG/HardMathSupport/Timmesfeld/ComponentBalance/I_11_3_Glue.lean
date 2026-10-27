module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Core
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i113g_isL2_of_equiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : IsL2TwoPowOdd L) : IsL2TwoPowOdd L' := by
  obtain ⟨n, hn, hn1, ⟨f⟩⟩ := h
  exact ⟨n, hn, hn1, ⟨e.symm.trans f⟩⟩

theorem i113g_card_barX {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C B : Subgroup G} (hB : IsPGroup p B) (hBC : B ≤ C) :
    Nat.card (barX p C B) = Nat.card B := by
  have hfi := injective_barX_comp hp hB hBC
  have hrange : ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (B.subgroupOf C).subtype).range
      = barX p C B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]


section Bar

theorem i113g_barX_le_gLBConj {G : Type*} [Group G] (p : ℕ) {C : Subgroup G} {j : G} (hj : j ∈ C)
    (T : Subgroup G) :
    barX p C (GLBConj j T) ≤
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨j, hj⟩) (barX p C T) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ GLBConj j T := (Subgroup.mem_subgroupOf).1 hc
  rw [mem_gLBConj, ← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹, ?_, rfl⟩
  show (⟨j, hj⟩ * c * ⟨j, hj⟩⁻¹ : ↥C) ∈ T.subgroupOf C
  rw [Subgroup.mem_subgroupOf]
  simpa using mem_gLBConj.1 hc'

theorem i113g_barX_gLBConj_eq {G : Type*} [Group G] (p : ℕ) {M : Subgroup G} {g : G} (hg : g ∈ M)
    (K : Subgroup G) :
    barX p M (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) (barX p M K) := by
  refine le_antisymm (i113g_barX_le_gLBConj p hg K) ?_
  have h := i113g_barX_le_gLBConj p (M.inv_mem hg) (GLBConj g K)
  rw [gLBConj_inv_gLBConj] at h
  have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) h
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨g⁻¹, M.inv_mem hg⟩ : ↥M) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, gLBConj_gLBConj_inv] at h2
  exact h2

end Bar

theorem i113g_mem_normalizer_of_bar {G : Type*} [Group G] [Finite G] {p : ℕ} {K : Subgroup G}
    (hK : GLAPComponent p ⊤ K) {g : G}
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup G)) ⟨g, Subgroup.mem_top g⟩ ∈
      Subgroup.normalizer ((barX p ⊤ K : Subgroup (↥(⊤ : Subgroup G) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup G))) : Set (↥(⊤ : Subgroup G) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup G)))) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have htop : GLBConj g (⊤ : Subgroup G) = ⊤ :=
    eq_top_iff.2 fun x _ => mem_gLBConj.2 (Subgroup.mem_top _)
  have hK' : GLAPComponent p ⊤ (GLBConj g K) := by
    have := glaPComponent_gLBConj hK g
    rwa [htop] at this
  have hbar : barX p ⊤ (GLBConj g K) = barX p ⊤ K := by
    rw [i113g_barX_gLBConj_eq p (Subgroup.mem_top g)]
    exact mem_normalizer_iff_gLBConj_eq.1 h
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hK' hK hbar)

theorem i113g_relIndex_barX {X : Type} [Group X] [Finite X] {p : ℕ}
    {B L : Subgroup X} (hL : GLAPComponent p ⊤ L) :
    (Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X))) : Set (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X)))).relIndex (barX p ⊤ B) =
      (Subgroup.normalizer (L : Set X)).relIndex B := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))).comp
    (B.subgroupOf ⊤).subtype with hf
  have hrange : f.range = barX p ⊤ B := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have key : (Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X))) : Set (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X)))).comap f =
      ((Subgroup.normalizer (L : Set X)).subgroupOf ⊤).subgroupOf (B.subgroupOf ⊤) := by
    ext b
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact i113g_mem_normalizer_of_bar hL h
    · intro h
      have h1 : ((b : ↥(⊤ : Subgroup X))) ∈ Subgroup.normalizer
          ((L.subgroupOf ⊤ : Subgroup ↥(⊤ : Subgroup X)) : Set ↥(⊤ : Subgroup X)) := by
        rw [normalizer_subgroupOf_eq le_top]
        exact h
      exact Subgroup.le_normalizer_map _ ⟨_, h1, rfl⟩
  calc _ = (Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X))) : Set (↥(⊤ : Subgroup X) ⧸
        GLAPPrimeCore p ↥(⊤ : Subgroup X)))).relIndex (Subgroup.map f ⊤) := by
        rw [Subgroup.map_top, hrange]
    _ = _ := by
        rw [← Subgroup.relIndex_comap, key, Subgroup.relIndex_top_right]
        exact Subgroup.relIndex_subgroupOf le_top


theorem i113g_card_le_of_normalizes {X : Type*} [Group X] [Finite X] {E T : Subgroup X}
    (hE : IsElemAbelian 3 E) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set X)) :
    Nat.card E ≤ 3 ^ GLATwoLocalRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt H
    have h1 : CFSG.Open.pRank 3 H < 3 ^ CFSG.Open.pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : 3 ^ CFSG.Open.pRank 3 H ≤ Nat.card X := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank 3 H ≤ Nat.card X
    omega
  have hEp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (T : Set X)) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hET hE hk
  have h2 : CFSG.Open.pRank 3 (Subgroup.normalizer (T : Set X)) ≤ GLATwoLocalRank 3 X :=
    le_csSup hbdd ⟨_, ⟨T, hT, hT2, rfl⟩, rfl⟩
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans h2)

theorem i113g_lift_bound {X Z : Type*} [Group X] [Finite X] [Group Z] [Finite Z] (ι : Z →* X)
    (hι : Function.Injective ι) {S W : Subgroup Z} (hS : IsElemAbelian 3 S)
    (hSW : S ≤ Subgroup.normalizer (W : Set Z)) (hW3 : ¬ 3 ∣ Nat.card W)
    (hW2 : 2 ∣ Nat.card W) : Nat.card S ≤ 3 ^ GLATwoLocalRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 3 S := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hS.2 g.1 g.2)⟩
  obtain ⟨P, hPS⟩ := exists_sylow_normalized (r := 2) hSW hSp hW3
  set P' : Subgroup Z := (P : Subgroup W).map W.subtype with hP'
  have hP'2 : IsPGroup 2 P' := (P.isPGroup').map _
  have hPne : P' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P' = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hP', Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity] at h1
    have h2 : 0 < (Nat.card W).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hW2
    have := Nat.one_lt_pow h2.ne' (by norm_num : 1 < 2)
    omega
  have hPmap : P'.map ι ≠ ⊥ := fun h =>
    hPne ((Subgroup.map_eq_bot_iff_of_injective P' hι).1 h)
  refine le_of_eq_of_le ?_ (i113g_card_le_of_normalizes (E := S.map ι) (T := P'.map ι)
    (CFSG.SectionRank.isElemAbelian_map hS ι) hPmap (hP'2.map _) ?_)
  · exact (Subgroup.card_map_of_injective hι).symm
  · exact (Subgroup.map_mono hPS).trans (Subgroup.le_normalizer_map ι)


section QuotBound

variable {X Z : Type*} [Group X] [Finite X] [Group Z] [Finite Z]

theorem i113g_quot_bound_even (ι : Z →* X) (hι : Function.Injective ι) (N : Subgroup Z)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (h2 : 2 ∣ Nat.card N) {E : Subgroup (Z ⧸ N)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ GLATwoLocalRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSel, -, hScard⟩ := exists_elemAbelian_lift N hN hE
  rw [← hScard]
  refine i113g_lift_bound ι hι hSel ?_ hN h2
  rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
  exact le_top

theorem i113g_quot_bound_normalizes (ι : Z →* X) (hι : Function.Injective ι) (N : Subgroup Z)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {E T : Subgroup (Z ⧸ N)} (hE : IsElemAbelian 3 E)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set (Z ⧸ N))) :
    Nat.card E ≤ 3 ^ GLATwoLocalRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift N hN hE
  rw [← hScard]
  set W : Subgroup Z := T.comap (QuotientGroup.mk' N) with hW
  have hSW : S ≤ Subgroup.normalizer (W : Set Z) := by
    intro s hs
    have hsb : QuotientGroup.mk' N s ∈ Subgroup.normalizer (T : Set (Z ⧸ N)) :=
      hET (hSmap ▸ ⟨s, hs, rfl⟩)
    have h := Subgroup.mem_normalizer_iff.1 hsb
    rw [Subgroup.mem_normalizer_iff]
    intro w
    change QuotientGroup.mk' N w ∈ T ↔ QuotientGroup.mk' N (s * w * s⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact h _
  obtain ⟨j, hj⟩ := hT2.exists_card_eq
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hT (Subgroup.eq_bot_of_card_eq T (by simpa using hj))
  have hWcard : Nat.card W = Nat.card N * 2 ^ j := by
    rw [← hj]
    exact QuotientGroup.card_preimage_mk N (T : Set (Z ⧸ N))
  have hWp : ¬ 3 ∣ Nat.card W := by
    rw [hWcard]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hdvd with h | h
    · exact hN h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  have hW2 : 2 ∣ Nat.card W := by
    rw [hWcard]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hj1) _
  exact i113g_lift_bound ι hι hSel hSW hWp hW2

end QuotBound


theorem kernel11_3a_of_core (h112 : I112) (hC : NoL2RankBound) (hD : NoL2Reduced) :
    Kernel11_3a := by
  intro X _ _ hX B hB L hL hnL hidx hiso
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 3 B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.1.2 g.1 g.2)⟩
  set N : Subgroup ↥(⊤ : Subgroup X) := GLAPPrimeCore 3 ↥(⊤ : Subgroup X) with hNdef
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp3).1 CFSG.pPrimeCore_coprime_card
  set ι : ↥(⊤ : Subgroup X) →* X := (⊤ : Subgroup X).subtype with hιdef
  have hι : Function.Injective ι := Subtype.val_injective
  have hBel : IsElemAbelian 3 (barX 3 ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :=
    isElemAbelian_barX hB.1
  have hBcard : Nat.card (barX 3 ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) =
      3 ^ GLATwoLocalRank 3 X := (i113g_card_barX hp3 hBp le_top).trans hB.2.1
  have hQcore : GLAPPrimeCore 3 (↥(⊤ : Subgroup X) ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp3
  have hLcomp : IsComponentOf (barX 3 ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) ⊤ := hL.2.2.1
  have hL2 : IsL2TwoPowOdd ↥(barX 3 ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :=
    i113g_isL2_of_equiv (quotEquivBarX hp3 le_top hL.2.1) hiso
  have hrel : (Subgroup.normalizer ((barX 3 ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :
      Set (↥(⊤ : Subgroup X) ⧸ N))).relIndex (barX 3 ⊤ B) = 3 := by
    rw [i113g_relIndex_barX hL]
    exact hidx
  have hidx_all : ∀ M : Subgroup (↥(⊤ : Subgroup X) ⧸ N), IsComponentOf M ⊤ →
      (Subgroup.normalizer (M : Set (↥(⊤ : Subgroup X) ⧸ N))).relIndex (barX 3 ⊤ B) ∣ 3 := by
    intro M hM
    obtain ⟨L', hL', rfl⟩ := exists_glaPComponent_barX_eq (p := 3) (⊤ : Subgroup X) hM
    rw [i113g_relIndex_barX hL']
    by_cases h : B ≤ Subgroup.normalizer (L' : Set X)
    · rw [Subgroup.relIndex_eq_one.2 h]
      exact one_dvd _
    · rw [(h112 X hX 3 hp3 (by norm_num) B hB.1 (i113_rank_of_isBmax hp3 hB) L' hL' h).2.1]
  by_cases h2 : 2 ∣ Nat.card N
  · exact hC _ hQcore _ _ hBel hLcomp hL2 hrel fun E hE _ =>
      (i113g_quot_bound_even ι hι N hN h2 hE).trans_eq hBcard.symm
  by_cases hR : ∀ R : Subgroup (↥(⊤ : Subgroup X) ⧸ N), IsPGroup 2 R →
      barX 3 ⊤ B ≤ Subgroup.normalizer (R : Set (↥(⊤ : Subgroup X) ⧸ N)) →
      R ≤ Subgroup.centralizer ((⨆ g ∈ (barX 3 ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)),
        GLBConj g (barX 3 ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) : Subgroup
        (↥(⊤ : Subgroup X) ⧸ N)) : Set (↥(⊤ : Subgroup X) ⧸ N)) → R = ⊥
  · refine hD _ hQcore _ _ hBel hLcomp hL2 hrel hidx_all ?_ ?_ hR
    · rintro E hE ⟨S, hS, hS2, hES⟩
      exact (i113g_quot_bound_normalizes ι hι N hN hE hS hS2 hES).trans_eq hBcard.symm
    · obtain ⟨U, hU, hU2, hBU⟩ := hB.2.2
      have hUZ2 : IsPGroup 2 (U.subgroupOf (⊤ : Subgroup X)) :=
        hU2.of_equiv (Subgroup.subgroupOfEquivOfLe le_top).symm
      refine ⟨barX 3 ⊤ U, ?_, hUZ2.map _, ?_⟩
      · intro hbot
        have hle : U.subgroupOf (⊤ : Subgroup X) ≤ N := by
          intro u hu
          have : QuotientGroup.mk' N u ∈ (barX 3 ⊤ U : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :=
            ⟨u, hu, rfl⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact (QuotientGroup.eq_one_iff u).1 this
        have hd : Nat.card (U.subgroupOf (⊤ : Subgroup X)) ∣ Nat.card N :=
          Subgroup.card_dvd_of_le hle
        obtain ⟨k, hk⟩ := hU2.exists_card_eq
        have hk0 : k ≠ 0 := by
          rintro rfl
          exact hU (Subgroup.eq_bot_of_card_eq U (by simpa using hk))
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : U ≤ ⊤)).toEquiv, hk] at hd
        exact h2 ((dvd_pow_self 2 hk0).trans hd)
      · have h1 : (B.subgroupOf (⊤ : Subgroup X)) ≤
            Subgroup.normalizer ((U.subgroupOf (⊤ : Subgroup X) : Subgroup ↥(⊤ : Subgroup X)) :
              Set ↥(⊤ : Subgroup X)) := by
          rw [normalizer_subgroupOf_eq le_top]
          intro b hb
          exact hBU hb
        exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  · push Not at hR
    obtain ⟨R, hR2, hBR, hRC, hRne⟩ := hR
    refine hC _ hQcore _ _ hBel hLcomp hL2 hrel fun E hE hEK => ?_
    have hKR : (⨆ g ∈ (barX 3 ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)),
        GLBConj g (barX 3 ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N))) ≤
        Subgroup.normalizer (R : Set (↥(⊤ : Subgroup X) ⧸ N)) :=
      (Subgroup.le_centralizer_iff.1 hRC).trans (Subgroup.centralizer_le_normalizer _)
    exact (i113g_quot_bound_normalizes ι hι N hN hE hRne hR2
      (hEK.trans (sup_le hKR hBR))).trans_eq hBcard.symm

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
