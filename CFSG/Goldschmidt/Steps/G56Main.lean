module

public import CFSG.Goldschmidt.Steps.G56Setup
import CFSG.Walter.Bender1970.S5.Normalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom

public section

namespace CFSG.Goldschmidt.G55

open CFSG.GorensteinWalter CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreOf_fitting_eq_self {X : Subgroup G} (hnil : Group.IsNilpotent X)
    (hodd : Odd (Nat.card X)) : CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) = X := by
  rw [fittingSubgroupOf_eq_self_of_isNilpotent hnil, oddCoreOf_eq]
  have htop : CFSG.pPrimeCore 2 X = ⊤ := by
    rw [eq_top_iff]
    refine le_sSup ⟨Subgroup.normal_top, ?_⟩
    rw [Subgroup.card_top]
    exact Nat.coprime_two_left.mpr hodd
  rw [CFSG.GorensteinWalter.oddCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite G] in
theorem eq_componentLayerOf_sup_oddCoreOf_of_odd {X : Subgroup G} (hnil : Group.IsNilpotent X)
    (hodd : Odd (Nat.card X)) :
    X = componentLayerOf X ⊔ CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
  rw [componentLayerOf_eq_bot_of_isSolvable inferInstance, bot_sup_eq,
    oddCoreOf_fitting_eq_self hnil hodd]

omit [Finite G] in
theorem isCyclic_quotient_of_le {U C : Subgroup G} [(C.subgroupOf U).Normal] {y : G}
    (hyU : y ∈ U) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hle : U ≤ Subgroup.zpowers y ⊔ C) : IsCyclic (U ⧸ C.subgroupOf U) := by
  refine ⟨⟨QuotientGroup.mk' (C.subgroupOf U) ⟨y, hyU⟩, fun z => ?_⟩⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf U) z
  obtain ⟨w, hw, c, hc, hwc⟩ :=
    mem_sup_of_le_normalizer (Subgroup.zpowers_le.mpr hyC) (hle u.2)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨k, ?_⟩
  have hcU : c ∈ U := by
    have : c = (y ^ k)⁻¹ * u := by rw [← hwc]; group
    rw [this]
    exact U.mul_mem (U.inv_mem (U.zpow_mem hyU k)) u.2
  simp only
  rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  have : ((((⟨y, hyU⟩ : U) ^ k)⁻¹ * u : U) : G) = c := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
    rw [← hwc]
    group
  rw [this]
  exact hc

namespace Gold37

variable (S : Gold37 G)

theorem W_le_centralizer_of_le_V {R : Subgroup G} (hRV : R ≤ S.V) :
    S.W ≤ Subgroup.centralizer (R : Set G) :=
  S.W_le_centralizer_V.trans (Subgroup.centralizer_le hRV)

theorem W_le_centralizer_singleton {v : G} (hv : v ∈ S.V) :
    S.W ≤ Subgroup.centralizer ({v} : Set G) :=
  S.W_le_centralizer_V.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))

include S in
theorem center_eq_bot : Subgroup.center G = ⊥ := by
  have := S.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := S.hS.nonabelian
    have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp hx) y).symm

include S in
theorem centralizer_ne_top {R : Subgroup G} (hR : R ≠ ⊥) :
    Subgroup.centralizer (R : Set G) ≠ ⊤ := by
  intro h
  apply hR
  rw [eq_bot_iff]
  intro r hr
  have hc : r ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (R : Set G) := h ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) r hr).symm
  rwa [S.center_eq_bot] at hc

include S in
theorem centralizer_singleton_ne_top {v : G} (hv : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≠ ⊤ := by
  rw [← centralizer_zpowers_eq']
  exact S.centralizer_ne_top (by rwa [Ne, Subgroup.zpowers_eq_bot])

include S in
theorem normalizer_ne_top {M : Subgroup G} (hM1 : M ≠ ⊥) (hMt : M ≠ ⊤) :
    Subgroup.normalizer (M : Set G) ≠ ⊤ := by
  have := S.isSimpleGroup
  intro h
  have hn : M.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h' | h'
  · exact hM1 h'
  · exact hMt h'

theorem ne_bot_of_card {R : Subgroup G} (hR2 : S.p ^ 2 ≤ Nat.card R) : R ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hR2
  have := S.hp.one_lt
  nlinarith

theorem not_isCyclic {R : Subgroup G} (hRV : R ≤ S.V) (hR2 : S.p ^ 2 ≤ Nat.card R) :
    ¬ IsCyclic R := by
  intro hcyc
  have h1 : Monoid.exponent R ∣ S.p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (S.hVexp x (hRV x.2))
  rw [IsCyclic.exponent_eq_card] at h1
  have h2 := Nat.le_of_dvd S.hp.pos h1
  have := S.hp.one_lt
  nlinarith

theorem isMulCommutative_of_le_V {R : Subgroup G} (hRV : R ≤ S.V) : IsMulCommutative R := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := congrArg Subtype.val (S.hVcomm.is_comm.comm ⟨a, hRV a.2⟩ ⟨b, hRV b.2⟩)
  exact h

theorem sup_W_ne_top {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) : K ⊔ S.W ≠ ⊤ := by
  have := S.isSimpleGroup
  intro h
  have hN : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h]
    exact sup_le Subgroup.le_normalizer hK.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h' | h'
  · exact hK1 h'
  · exact hK.1 h'

theorem qCoreOf_inf_mem_U {X : Subgroup G} (hWX : S.W ≤ X) (hX : X ≠ ⊤) {q : ℕ} (hq : q.Prime)
    (hqπ : q ∉ S.primes) {Y : Subgroup G} (hWY : S.W ≤ Subgroup.normalizer (Y : Set G)) :
    qCoreOf X q ⊓ Y ∈ S.U := by
  obtain ⟨hinv, -, hodd, -, -⟩ := S.qCoreOf_props hWX hq hqπ
  have hWN : S.W ≤ Subgroup.normalizer ((qCoreOf X q ⊓ Y : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q) (hWX hw)) (hWY hw)
  refine ⟨fun h => hX (eq_top_iff.mpr (h ▸ inf_le_left.trans (Subgroup.map_subtype_le _))), hWN,
    commutator_zpowers_eq_self_of_conj_eq_inv (hWN S.a_mem_W) (fun x hx => hinv x hx.1)
      (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))⟩

theorem not_dvd_card_qCoreOf {X : Subgroup G} {q : ℕ} (hq : q.Prime) (hqπ : q ∉ S.primes) :
    ¬ S.p ∣ Nat.card (qCoreOf X q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro h
  obtain ⟨k, hk⟩ := (qCoreOf_isPGroup X q).exists_card_eq
  rw [hk] at h
  exact S.ne_p_of_not_mem_primes hqπ ((Nat.prime_dvd_prime_iff_eq S.hp hq).mp
    (S.hp.dvd_of_dvd_pow h)).symm

theorem V_component {X : Subgroup G} (hWX : S.W ≤ X) (hX : X ≠ ⊤) {L : Subgroup G}
    (hL : IsComponentOf L X) :
    S.V ≤ Subgroup.normalizer (L : Set G) ∧
      (∀ R ≤ S.V, ¬ R ≤ Subgroup.centralizer (L : Set G) → ∀ w ∈ S.V,
        ∃ r ∈ R, r⁻¹ * w ∈ Subgroup.centralizer (L : Set G)) ∧
      (∀ R ≤ S.V, Nat.card R ≤
        S.p * Nat.card (R ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)) := by
  obtain ⟨g, hAg, hSS⟩ := S.hS.sstar X hX
  have haX := S.a_mem hWX
  have haA₁ : S.a ∈ conjSub g S.A ⊓ X := ⟨hAg ⟨S.haA, haX⟩, haX⟩
  set C := X ⊓ Subgroup.centralizer ({S.a} : Set G) with hCdef
  set U₀ := GorensteinWalter.oddCoreOf (CFSG.fittingSubgroupOf C) with hU₀def
  have hU₀F : U₀ ≤ CFSG.fittingSubgroupOf C := Subgroup.map_subtype_le _
  have hU₀C : U₀ ≤ C := hU₀F.trans (fittingSubgroupOf_isNormalIn C).1
  have hU₀X : U₀ ≤ X := hU₀C.trans inf_le_left
  have hU₀nil : Group.IsNilpotent U₀ :=
    isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent C) hU₀F
  have hU₀odd : Odd (Nat.card U₀) := CFSG.Walter.odd_card_oddCoreOf _
  have hCU₀ : X ⊓ Subgroup.centralizer ({S.a} : Set G) ≤ Subgroup.normalizer (U₀ : Set G) :=
    le_normalizer_of_isNormalIn (oddCoreOf_fittingSubgroupOf_isNormalIn C)
  have hVU₀ : S.V ≤ U₀ := S.V_le_oddCoreOf hWX
  obtain ⟨-, -, -, h3⟩ := S.h37 G X (conjSub g S.A ⊓ X) hSS
    (isElemAbelian_conjSub_inf S.hS.elem g X) S.a haA₁ S.ha1 U₀ hU₀X hCU₀
    (eq_componentLayerOf_sup_oddCoreOf_of_odd hU₀nil hU₀odd)
  simp only [oddCoreOf_fitting_eq_self hU₀nil hU₀odd] at h3
  by_cases hUL : U₀ ≤ Subgroup.centralizer (L : Set G)
  · have hVL := hVU₀.trans hUL
    refine ⟨hVL.trans (Subgroup.centralizer_le_normalizer _),
      fun R hRV hRL => absurd (hRV.trans hVL) hRL, fun R hRV => ?_⟩
    rw [inf_of_le_left (hRV.trans hVL)]
    exact Nat.le_mul_of_pos_left _ S.hp.pos
  · obtain ⟨-, -, hUN, ⟨y, hyU, hyle⟩, -⟩ := h3 L hL hUL
    have hU₀N : U₀ ≤ Subgroup.normalizer (L : Set G) :=
      hUN.trans (sup_le Subgroup.le_normalizer
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
    have hnorm : ((Subgroup.centralizer (L : Set G)).subgroupOf U₀).Normal := by
      refine ⟨fun n hn u => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (Bender35.mem_normalizer_centralizer (hU₀N u.2))
        _).mp hn
    have hcyc := isCyclic_quotient_of_le hyU (Bender35.mem_normalizer_centralizer (hU₀N hyU)) hyle
    exact ⟨hVU₀.trans hU₀N, fun R hRV hRL w hw =>
      exists_mem_inv_mul_mem_of_isCyclic hcyc hVU₀ S.hp S.hVexp hRV hRL hw,
      fun R hRV => card_le_mul_card_inf_of_isCyclic hcyc (hRV.trans hVU₀) S.hp
        (fun x hx => S.hVexp x (hRV hx))⟩

theorem Q_centralizer_le_normalizer
    {R : Subgroup G} (hRV : R ≤ S.V) {v : G} (hvR : v ∈ R)
    (hv1 : v ≠ 1) :
    S.Q (Subgroup.centralizer ({v} : Set G)) ≤
      Subgroup.normalizer (S.Q (Subgroup.centralizer (R : Set G)) : Set G) := by
  set Xv := Subgroup.centralizer ({v} : Set G) with hXv
  set XR := Subgroup.centralizer (R : Set G) with hXR
  set M := S.Q XR with hM
  have hR1 : R ≠ ⊥ := fun h => hv1 (by rw [h] at hvR; exact Subgroup.mem_bot.mp hvR)
  have hWXR : S.W ≤ XR := S.W_le_centralizer_of_le_V hRV
  have hXRt : XR ≠ ⊤ := S.centralizer_ne_top hR1
  have hXRXv : XR ≤ Xv := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvR)
  have hWXv : S.W ≤ Xv := hWXR.trans hXRXv
  have hXvt : Xv ≠ ⊤ := S.centralizer_singleton_ne_top hv1
  have hMU : M ∈ S.U := S.Q_mem_U hWXR hXRt
  have hMXv : M ≤ S.Q Xv := S.le_Q_of_mem_U hWXv hXvt hMU (S.Q_le.trans hXRXv)
  refine sSup_le fun L hP => ?_
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  ·
    have hcent : S.Q Xv ≤ Subgroup.centralizer (qCoreOf Xv q : Set G) := by
      refine sSup_le fun P' hP' => ?_
      rcases hP' with ⟨r, hr, hrπ, rfl⟩ | ⟨hL', -⟩
      · by_cases hrq : r = q
        · subst hrq
          have hab := (S.qCoreOf_props hWXv hr hrπ).2.1
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
        · exact qCoreOf_centralizer_of_ne Xv hq hr (Ne.symm hrq)
      · exact (le_sSup (s := {E : Subgroup G | IsComponentOf E Xv}) hL').trans
          ((componentLayerOf_le_centralizer_fitting Xv).trans
            (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf Xv q hq)))
    exact (Subgroup.le_centralizer_iff.mp (hMXv.trans hcent)).trans
      (Subgroup.centralizer_le_normalizer _)
  ·
    obtain ⟨hVL, hVRL, -⟩ := S.V_component hWXv hXvt hL
    by_cases hRL : R ≤ Subgroup.centralizer (L : Set G)
    · have hLXR : L ≤ XR := Subgroup.le_centralizer_iff.mp hRL
      exact (S.le_Q_of_mem_pieces (X := XR)
        (Or.inr ⟨IsComponentOf.of_le hL hLXR hXRXv, hLH⟩)).trans Subgroup.le_normalizer
    ·
      have hMV : M ≤ ⁅M, S.V⁆ := by
        refine sSup_le fun P' hP' => ?_
        refine le_trans ?_ (Subgroup.commutator_mono (S.le_Q_of_mem_pieces hP') le_rfl)
        rcases hP' with ⟨q, hq, hqπ, rfl⟩ | ⟨hL', hL'H⟩
        · have hVN : S.V ≤ Subgroup.normalizer (qCoreOf XR q : Set G) :=
            (S.V_le_W.trans hWXR).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in XR q))
          have : Fact q.Prime := ⟨hq⟩
          have hsolv : Group.IsSolvable (qCoreOf XR q) := by
            have := (qCoreOf_isPGroup XR q).isNilpotent
            infer_instance
          have hcop : Nat.Coprime (Nat.card S.V) (Nat.card (qCoreOf XR q)) := by
            have : Fact S.p.Prime := ⟨S.hp⟩
            obtain ⟨a, ha⟩ := S.V_isPGroup.exists_card_eq
            obtain ⟨b, hb⟩ := (qCoreOf_isPGroup XR q).exists_card_eq
            rw [ha, hb]
            exact Nat.Coprime.pow a b ((Nat.coprime_primes S.hp hq).mpr
              (Ne.symm (S.ne_p_of_not_mem_primes hqπ)))
          have h1 := le_sup_commutator_of_coprime hVN hsolv hcop
          have h2 : qCoreOf XR q ⊓ Subgroup.centralizer (S.V : Set G) = ⊥ :=
            le_bot_iff.mp ((inf_le_inf_left _ S.hCV).trans (S.qCoreOf_inf_H hWXR hq hqπ).le)
          rwa [h2, bot_sup_eq] at h1
        · obtain ⟨hVL', -, -⟩ := S.V_component hWXR hXRt hL'
          rcases commutator_eq_bot_or_le_of_isComponentOf hL' hVL' with h | h
          · exfalso
            exact hL'H ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans S.hCV)
          · exact h
      have hMVL : ⁅M, S.V⁆ ≤ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.commutator_le]
        intro m hm w hw
        obtain ⟨r, hrR, hrw⟩ := hVRL R hRV hRL w hw
        set c := r⁻¹ * w with hc
        have hmR : m ∈ XR := S.Q_le hm
        have hmr : r * m = m * r := (Subgroup.mem_centralizer_iff.mp hmR) r hrR
        have hmL : m ∈ Subgroup.normalizer (L : Set G) :=
          Bender37.generalizedFitting_le_normalizer_component hL
            (S.Q_le_generalizedFitting (hMXv hm))
        have hmc : ⁅m, c⁆ ∈ Subgroup.centralizer (L : Set G) := by
          refine commutatorElement_mem_centralizer_of_conj hmL (Or.inl fun n hn => ?_)
          have := (Subgroup.mem_centralizer_iff.mp hrw) n hn
          rw [← this]
          group
        have hrN : r ∈ Subgroup.normalizer
            ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
          Bender35.mem_normalizer_centralizer (hVL (hRV hrR))
        have heq : ⁅m, w⁆ = r * ⁅m, c⁆ * r⁻¹ := by
          have hw' : w = r * c := by rw [hc]; group
          rw [hw']
          simp only [commutatorElement_def]
          calc m * (r * c) * m⁻¹ * (r * c)⁻¹ = (m * r) * c * m⁻¹ * c⁻¹ * r⁻¹ := by group
            _ = (r * m) * c * m⁻¹ * c⁻¹ * r⁻¹ := by rw [hmr]
            _ = r * (m * c * m⁻¹ * c⁻¹) * r⁻¹ := by group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp hrN _).mp hmc
      exact (Subgroup.le_centralizer_iff.mp (hMV.trans hMVL)).trans
        (Subgroup.centralizer_le_normalizer _)

theorem le_iSup_Q {K : Subgroup G} (hK : K ∈ S.U) {R : Subgroup G} (hRV : R ≤ S.V)
    (hR2 : S.p ^ 2 ≤ Nat.card R) :
    K ≤ ⨆ (v : G) (_ : v ∈ R) (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G)) := by
  set J := ⨆ (v : G) (_ : v ∈ R) (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G))
  have hJ : ∀ v ∈ R, v ≠ 1 → S.Q (Subgroup.centralizer ({v} : Set G)) ≤ J := fun v hv hv1 =>
    le_iSup₂_of_le (f := fun (v : G) (_ : v ∈ R) =>
      ⨆ (_ : v ≠ 1), S.Q (Subgroup.centralizer ({v} : Set G))) v hv (le_iSup_of_le hv1 le_rfl)
  by_cases hK1 : K = ⊥
  · rw [hK1]
    exact bot_le
  set X := K ⊔ S.W with hXdef
  have hWX : S.W ≤ X := le_sup_right
  have hX : X ≠ ⊤ := S.sup_W_ne_top hK hK1
  refine (S.le_Q_of_mem_U hWX hX hK le_sup_left).trans (sSup_le fun L hP => ?_)
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · have hRN : R ≤ Subgroup.normalizer (qCoreOf X q : Set G) :=
      (hRV.trans (S.V_le_W.trans hWX)).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q))
    refine (le_iSup_inf_centralizer S.hp (S.isMulCommutative_of_le_V hRV)
      (fun x hx => S.hVexp x (hRV hx)) hR2 hRN (S.not_dvd_card_qCoreOf hq hqπ)).trans
      (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    have hWe := S.W_le_centralizer_singleton (hRV he)
    exact (S.le_Q_of_mem_U hWe (S.centralizer_singleton_ne_top he1)
      (S.qCoreOf_inf_mem_U hWX hX hq hqπ (hWe.trans Subgroup.le_normalizer)) inf_le_right).trans
      (hJ e he he1)
  ·
    obtain ⟨-, -, hcard⟩ := S.V_component hWX hX hL
    have hCR : R ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
      intro h
      have h1 := hcard R hRV
      rw [h, Subgroup.card_bot, mul_one] at h1
      have := S.hp.one_lt
      nlinarith
    obtain ⟨u', hu'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCR
    set u : G := (u' : G) with hudef
    have huR : u ∈ R := u'.2.1
    have huL : u ∈ Subgroup.centralizer (L : Set G) := u'.2.2
    have hu1 : u ≠ 1 := fun h => hu' (Subtype.ext h)
    have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp huL) l hl)
    have hWu := S.W_le_centralizer_singleton (hRV huR)
    exact (S.le_orbit L).trans ((S.le_Q_of_mem_U hWu (S.centralizer_singleton_ne_top hu1)
      (S.orbit_mem_U hWX hX hL hLH) (S.orbit_le hLu (hWu.trans Subgroup.le_normalizer))).trans
      (hJ u huR hu1))

theorem exists_Q_ne_bot
    {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) :
    ∃ R ≤ S.V, S.p ^ 2 ≤ Nat.card R ∧ S.Q (Subgroup.centralizer (R : Set G)) ≠ ⊥ := by
  set X := K ⊔ S.W with hXdef
  have hWX : S.W ≤ X := le_sup_right
  have hX : X ≠ ⊤ := S.sup_W_ne_top hK hK1
  have hQ : S.Q X ≠ ⊥ := fun h =>
    hK1 (le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWX hX hK le_sup_left))
  obtain ⟨L, hP, hP1⟩ : ∃ P ∈ S.pieces X, P ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hQ (le_bot_iff.mp (sSup_le fun P hP => (hcon P hP).le))
  rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
  · have hVN : S.V ≤ Subgroup.normalizer (qCoreOf X q : Set G) :=
      (S.V_le_W.trans hWX).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in X q))
    obtain ⟨B, hBV, hcard, hB⟩ := exists_inf_centralizer_ne_bot S.hp S.hVcomm S.hVexp
      S.V_ne_bot hVN (S.not_dvd_card_qCoreOf hq hqπ) hP1
    have hB2 : S.p ^ 2 ≤ Nat.card B := by
      have h3 := S.hV3
      rw [hcard, pow_succ, mul_comm] at h3
      exact Nat.le_of_mul_le_mul_left h3 S.hp.pos
    refine ⟨B, hBV, hB2, fun h => hB ?_⟩
    have hWB := S.W_le_centralizer_of_le_V hBV
    exact le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWB (S.centralizer_ne_top (S.ne_bot_of_card hB2))
      (S.qCoreOf_inf_mem_U hWX hX hq hqπ (hWB.trans Subgroup.le_normalizer)) inf_le_right)
  · obtain ⟨-, -, hcard⟩ := S.V_component hWX hX hL
    set R := S.V ⊓ Subgroup.centralizer (L : Set G) with hR
    have hR2 : S.p ^ 2 ≤ Nat.card R := by
      have h3 := S.hV3.trans (hcard S.V le_rfl)
      rw [pow_succ, mul_comm] at h3
      exact Nat.le_of_mul_le_mul_left h3 S.hp.pos
    refine ⟨R, inf_le_left, hR2, fun h => ?_⟩
    have hWR := S.W_le_centralizer_of_le_V (inf_le_left : R ≤ S.V)
    have hLR : L ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.le_centralizer_iff.mp inf_le_right
    have hO := S.le_Q_of_mem_U hWR (S.centralizer_ne_top (S.ne_bot_of_card hR2))
      (S.orbit_mem_U hWX hX hL hLH) (S.orbit_le hLR (hWR.trans Subgroup.le_normalizer))
    rw [h] at hO
    exact Bender37.ne_bot_of_isComponentOf hL (le_bot_iff.mp ((S.le_orbit L).trans hO))

theorem exists_max_U
    {K : Subgroup G} (hK : K ∈ S.U) (hK1 : K ≠ ⊥) :
    ∃ M₀ ∈ S.U, M₀ ≠ ⊥ ∧ ∀ K' ∈ S.U, K' ≤ M₀ := by
  obtain ⟨R, hRV, hR2, hM⟩ := S.exists_Q_ne_bot hK hK1
  set M := S.Q (Subgroup.centralizer (R : Set G)) with hMdef
  have hWR := S.W_le_centralizer_of_le_V hRV
  have hMU : M ∈ S.U := S.Q_mem_U hWR (S.centralizer_ne_top (S.ne_bot_of_card hR2))
  have hall : ∀ K' ∈ S.U, K' ≤ Subgroup.normalizer (M : Set G) := fun K' hK' =>
    (S.le_iSup_Q hK' hRV hR2).trans (iSup₂_le fun v hv => iSup_le fun hv1 =>
      S.Q_centralizer_le_normalizer hRV hv hv1)
  set X := Subgroup.normalizer (M : Set G) with hXdef
  have hWX : S.W ≤ X := hMU.2.1
  have hX : X ≠ ⊤ := S.normalizer_ne_top hM hMU.1
  refine ⟨S.Q X, S.Q_mem_U hWX hX, fun h => hK1 ?_,
    fun K' hK' => S.le_Q_of_mem_U hWX hX hK' (hall K' hK')⟩
  exact le_bot_iff.mp (h ▸ S.le_Q_of_mem_U hWX hX hK (hall K hK))

theorem H_le_normalizer {M₀ : Subgroup G} (hM₀ : M₀ ∈ S.U) (hM₀1 : M₀ ≠ ⊥)
    (hmax : ∀ K ∈ S.U, K ≤ M₀) : S.H ≤ Subgroup.normalizer (M₀ : Set G) := by
  set X := Subgroup.normalizer (M₀ : Set G) with hXdef
  have hWX : S.W ≤ X := hM₀.2.1
  have hX : X ≠ ⊤ := S.normalizer_ne_top hM₀1 hM₀.1
  have hQ : S.Q X = M₀ :=
    le_antisymm (hmax _ (S.Q_mem_U hWX hX)) (S.le_Q_of_mem_U hWX hX hM₀ Subgroup.le_normalizer)
  have step : ∀ A : Subgroup G, S.W ≤ A → A ≤ X → ∀ k ∈ S.H,
      k ∈ Subgroup.normalizer (A : Set G) → k ∈ X := by
    intro A hWA hAX k hkH hkA
    have h1 := S.map_conj_Q (X := X) hkH
    rw [hQ] at h1
    have hWXk : S.W ≤ X.map (MulAut.conj k).toMonoidHom := by
      intro w hw
      have hwA : w ∈ A.map (MulAut.conj k).toMonoidHom := by
        rw [Bender37.map_conj_eq_of_mem_normalizer hkA]
        exact hWA hw
      exact Subgroup.map_mono hAX hwA
    have hXk : X.map (MulAut.conj k).toMonoidHom ≠ ⊤ := by
      intro h
      apply hX
      have h2 := map_conj_map_conj_inv k X
      rw [h, Subgroup.map_top_of_surjective _ (MulAut.conj k⁻¹).surjective] at h2
      exact h2.symm
    have h2 : M₀.map (MulAut.conj k).toMonoidHom ≤ M₀ := h1 ▸ hmax _ (S.Q_mem_U hWXk hXk)
    have h3 : M₀.map (MulAut.conj k).toMonoidHom = M₀ :=
      Subgroup.eq_of_le_of_card_ge h2
        (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
    exact Bender35.mem_normalizer_of_map_conj_eq h3
  suffices key : ∀ A : Subgroup S.H, A.IsSubnormal → S.W.subgroupOf S.H ≤ A →
      A.map S.H.subtype ≤ X → S.H ≤ X by
    refine key _ S.W_isSubnormal_H le_rfl ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left S.W_le_H]
    exact hWX
  intro A hA
  induction hA with
  | top =>
    intro _ h
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  | step A K hAK _ hN ih =>
    intro hWA hAX
    refine ih (hWA.trans hAK) ?_
    rintro _ ⟨k, hk, rfl⟩
    refine step (A.map S.H.subtype) ?_ hAX k k.2 ?_
    · intro w hw
      exact ⟨⟨w, S.W_le_H hw⟩, hWA (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
    · have hkN : k ∈ Subgroup.normalizer (A : Set S.H) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mp hN) hk
      exact Subgroup.le_normalizer_map S.H.subtype ⟨k, hkN, rfl⟩

theorem forall_U_eq_bot :
    ∀ K ∈ S.U, K = ⊥ := by
  have := S.isSimpleGroup
  intro K hK
  by_contra hK1
  obtain ⟨M₀, hM₀, hM₀1, hmax⟩ := S.exists_max_U hK hK1
  have hHN := S.H_le_normalizer hM₀ hM₀1 hmax
  rcases S.hH.le_iff.mp hHN with h | h
  · have hn : M₀.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₀ with h' | h'
    · exact hM₀1 h'
    · exact hM₀.1 h'
  ·
    have hM₀H : M₀ ≤ S.H := h ▸ Subgroup.le_normalizer
    set X := Subgroup.normalizer (M₀ : Set G) with hXdef
    have hWX : S.W ≤ X := hM₀.2.1
    have hX : X ≠ ⊤ := S.normalizer_ne_top hM₀1 hM₀.1
    have hQ : S.Q X = M₀ :=
      le_antisymm (hmax _ (S.Q_mem_U hWX hX)) (S.le_Q_of_mem_U hWX hX hM₀ Subgroup.le_normalizer)
    apply hM₀1
    rw [← hQ, eq_bot_iff]
    refine sSup_le fun P hP => ?_
    have hPH : P ≤ S.H := (hQ ▸ S.le_Q_of_mem_pieces hP).trans hM₀H
    rcases hP with ⟨q, hq, hqπ, rfl⟩ | ⟨hL, hLH⟩
    · exact (le_inf le_rfl hPH).trans (S.qCoreOf_inf_H hWX hq hqπ).le
    · exact absurd hPH hLH

theorem qCoreOf_two_le_H {B : Subgroup G} (hWB : S.W ≤ B) : qCoreOf B 2 ≤ S.H := by
  have h17 := bender1970_1_7_ii_commutator_pResidual S.isSimpleGroup S.H S.hH S.W
    S.W_le_F S.W_isSubnormal S.inf_centralizer_W_le hWB 2 Nat.prime_two S.two_mem_primes
  set R := pResidualOf (generalizedFittingSubgroupOf S.H) 2 with hRdef
  have hVR : S.V ≤ R := fun v hv => mem_pResidualOf_of_order_coprime _ 2 Nat.prime_two
    (S.V_le_F hv) (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard S.V hv)
      (Nat.coprime_two_left.mpr S.odd_card_V))
  have hR1 : R ≠ ⊥ := fun h => S.V_ne_bot (le_bot_iff.mp (h ▸ hVR))
  have hRH : IsNormalIn R S.H := pResidualOf_generalizedFitting_isNormalIn S.H 2
  have hNR : Subgroup.normalizer (R : Set G) = S.H :=
    normalizer_eq_of_nontrivial_normal_in_coatom S.isSimpleGroup S.hH hRH.1 hR1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRH.1).mpr (le_normalizer_of_isNormalIn hRH))
  rw [← hNR]
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h17).trans
    (Subgroup.centralizer_le_normalizer _)

theorem eq_H_of_forall_U_eq_bot (hU : ∀ K ∈ S.U, K = ⊥) {B : Subgroup G} (hB : IsCoatom B)
    (hWB : S.W ≤ B) : S.H = B := by
  have hQB : S.Q B = ⊥ := hU _ (S.Q_mem_U hWB hB.1)
  have hFB : generalizedFittingSubgroupOf B ≤ S.H := by
    refine sup_le ?_ ?_
    · rw [fittingSubgroupOf_eq_iSup_qCoreOf B]
      refine iSup_le fun q => ?_
      have hq := Nat.prime_of_mem_primeFactors q.1.2
      by_cases hq2 : q.1.1 = 2
      · have h := S.qCoreOf_two_le_H hWB
        rwa [← hq2] at h
      · by_cases hqπ : q.1.1 ∈ S.primes
        · exact (S.qCoreOf_le_centralizer hWB hq hq2 hqπ).trans S.hCH
        · exact (S.le_Q_of_mem_pieces (Or.inl ⟨_, hq, hqπ, rfl⟩)).trans (hQB ▸ bot_le)
    · refine sSup_le fun L hL => ?_
      by_contra hLH
      exact Bender37.ne_bot_of_isComponentOf hL
        (le_bot_iff.mp (hQB ▸ S.le_Q_of_mem_pieces (Or.inr ⟨hL, hLH⟩)))
  refine bender1970_1_7_iii_equalityOfMaximal S.isSimpleGroup S.H S.hH S.W S.W_le_F
    S.W_isSubnormal S.inf_centralizer_W_le hWB hB (Or.inl S.two_le_card_primes_F)
    ⟨generalizedFittingSubgroupOf B, hFB, le_rfl, ?_, inf_le_left⟩
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.IsSubnormal.top

theorem eq_H_of_le
    {B : Subgroup G} (hB : IsCoatom B) (hWB : S.W ≤ B) : S.H = B :=
  S.eq_H_of_forall_U_eq_bot S.forall_U_eq_bot hB hWB

theorem zpowers_mem_goldA
    {v : G} (hv : v ∈ S.V) (hv1 : v ≠ 1) :
    Subgroup.zpowers v ∈ goldA S.a S.H := by
  have hzP : Subgroup.zpowers v ≤ qCoreOf S.H S.p := Subgroup.zpowers_le.mpr (S.hVP hv)
  obtain ⟨hF, hsn⟩ := Bender35.le_and_isSubnormal S.hp hzP
  refine ⟨by rwa [Ne, Subgroup.zpowers_eq_bot], hF, hsn, ?_, fun M hM hNM => Or.inl ?_⟩
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (S.qCoreOf_le_centralizer_a (S.hVP hv))).symm
  · have hWv : S.W ≤ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      refine (S.W_le_centralizer_singleton hv).trans ?_
      rw [← centralizer_zpowers_eq']
      exact Subgroup.centralizer_le_normalizer _
    exact (S.eq_H_of_le hM (hWv.trans hNM)).symm

end Gold37

end CFSG.Goldschmidt.G55
