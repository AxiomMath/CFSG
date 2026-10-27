module

public import CFSG.Goldschmidt.Steps.G37CoreSetup

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)

section XStructure

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddFit_le (X : Subgroup G) : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ X :=
  (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)

theorem odd_card_oddFit (X : Subgroup G) :
    Odd (Nat.card (oddCoreOf (CFSG.fittingSubgroupOf X))) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.Goldschmidt.SStarTransport.odd_card_goldschmidtOddCore _

theorem isNilpotent_oddFit (X : Subgroup G) :
    Group.IsNilpotent (oddCoreOf (CFSG.fittingSubgroupOf X)) := by
  set F := CFSG.fittingSubgroupOf X
  have hF : Group.IsNilpotent F := CFSG.fittingSubgroupOf_isNilpotent X
  have hYF : oddCoreOf F ≤ F := Subgroup.map_subtype_le _
  have : Group.IsNilpotent ((oddCoreOf F).subgroupOf F) := inferInstance
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYF)

omit [Finite G] in
theorem normalizer_le_normalizer_fitting (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.fittingSubgroupOf X : Set G) :=
  CFSG.Walter.normalizer_le_normalizer_map_of_characteristic (CFSG.fittingSubgroup X)

omit [Finite G] in
theorem normalizer_le_normalizer_oddFit (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (oddCoreOf (CFSG.fittingSubgroupOf X) : Set G) := by
  have : (goldschmidtOddCore (CFSG.fittingSubgroupOf X)).Characteristic := by
    rw [goldschmidtOddCore_eq_pPrimeCore]
    infer_instance
  exact (normalizer_le_normalizer_fitting X).trans
    (CFSG.Walter.normalizer_le_normalizer_map_of_characteristic _)

omit [Finite G] in
theorem normalizer_le_normalizer_componentLayerOf (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (componentLayerOf X : Set G) := fun _ hg =>
  CFSG.Walter.mem_normalizer_sSup_of_map_mem
    (fun _ hK => CFSG.Walter.isComponentOf_map_conj hK hg)
    (fun _ hK => CFSG.Walter.isComponentOf_map_conj hK (Subgroup.inv_mem _ hg))

omit [Finite G] in
theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

omit [Finite G] in
theorem isPerfect_componentLayerOf (X : Subgroup G) : Group.IsPerfect (componentLayerOf X) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (commutator_self_le _) (sSup_le fun K hK => ?_)
  have hK' : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.2.2.2.1)
  rw [← hK']
  exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem inf_eq_bot_of_odd_of_isPGroup {Y R : Subgroup G} (hY : Odd (Nat.card Y))
    (hR : IsPGroup 2 R) : Y ⊓ R = ⊥ := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card R) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hY)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

variable {X : Subgroup G}

theorem pResidualOf_eq_self_X
    (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) :
    pResidualOf X 2 = X :=
  pResidualOf_eq_self_of_sup hXE (isPerfect_componentLayerOf X) (odd_card_oddFit X)

theorem le_centralizer_of_isPGroup_X
    (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) {R : Subgroup G}
    (hRX : R ≤ X) (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 R) :
    X ≤ Subgroup.centralizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : componentLayerOf X ≤ Subgroup.centralizer (R : Set G) := by
    refine sSup_le fun K hK => ?_
    have hRs : Group.IsSolvable R := by
      have := hR.isNilpotent
      infer_instance
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hK hRs hRX hXR)
  have hY : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (R : Set G) := by
    set Y := oddCoreOf (CFSG.fittingSubgroupOf X)
    have hYX : Y ≤ X := oddFit_le X
    have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
      hRX.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddFit X))
    have h1 : ⁅Y, R⁆ ≤ Y ⊓ R := by
      rw [Subgroup.commutator_le]
      intro y hy r hr
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have : r * y⁻¹ * r⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hRY hr) y⁻¹).mp (Y.inv_mem hy)
        rw [show y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) by group]
        exact Y.mul_mem hy this
      · have : y * r * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hXR (hYX hy)) r).mp hr
        exact R.mul_mem this (R.inv_mem hr)
    rw [inf_eq_bot_of_odd_of_isPGroup (odd_card_oddFit X) hR, le_bot_iff] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have h2 := sup_le hE hY
  rwa [← hXE] at h2

end XStructure

section Thompson

variable {M : Type} [Group M] [Finite M]

theorem le_centralizer_fitting (hO : goldschmidtOddCore M = ⊥) {a : M}
    (ha : a ∈ generalizedFittingSubgroupOf (⊤ : Subgroup M)) {X : Subgroup M}
    (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
    (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) :
    X ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf (⊤ : Subgroup M) : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.fittingSubgroupOf (⊤ : Subgroup M) with hF
  have hF2 : IsPGroup 2 F := isPGroup_fitting hO
  have hFn : F.Normal := by
    rw [hF, fittingSubgroupOf_top_eq]
    exact CFSG.fittingSubgroup_normal
  set Q₀ := F ⊓ Subgroup.centralizer ({a} : Set M) with hQ₀
  have hQ₀X : Q₀ ≤ Subgroup.normalizer (X : Set M) := inf_le_right.trans hXa
  have hXF : X ≤ Subgroup.normalizer (F : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hFn]
    exact le_top
  have hXQF : ⁅X, Q₀⁆ ≤ X ⊓ F := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : q * x⁻¹ * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hQ₀X hq) x⁻¹).mp (X.inv_mem hx)
      rw [show x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) by group]
      exact X.mul_mem hx this
    · exact F.mul_mem (hFn.conj_mem q (Subgroup.mem_inf.mp hq).1 x)
        (F.inv_mem (Subgroup.mem_inf.mp hq).1)
  have hXC : X ≤ Subgroup.centralizer ((X ⊓ F : Subgroup M) : Set M) := by
    refine le_centralizer_of_isPGroup_X hXE inf_le_left ?_ (hF2.to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, hXF hx⟩)
  have hXQ₀ : X ≤ Subgroup.centralizer (Q₀ : Set M) := by
    have hE : componentLayerOf X ≤ Subgroup.centralizer (Q₀ : Set M) := by
      refine sSup_le fun K hK => ?_
      have hKX : K ≤ X := hK.1
      have h1 : ⁅⁅K, Q₀⁆, K⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅K, Q₀⁆, K⁆ ≤ ⁅X ⊓ F, X⁆ :=
              Subgroup.commutator_mono ((Subgroup.commutator_mono hKX le_rfl).trans hXQF) hKX
          _ = ⊥ := by
              rw [Subgroup.commutator_comm]
              exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXC
          _ ≤ ⊥ := le_rfl
      have h2 := CFSG.LocalCores.perfect_double_commutator
        (Group.isPerfect_def.mpr hK.2.2.2.1) h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    have hY : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (Q₀ : Set M) := by
      set Y := oddCoreOf (CFSG.fittingSubgroupOf X)
      have hQ₀Y : Q₀ ≤ Subgroup.normalizer (Y : Set M) :=
        hQ₀X.trans (normalizer_le_normalizer_oddFit X)
      have h1 : ⁅Y, Q₀⁆ ≤ Y ⊓ F := by
        rw [Subgroup.commutator_le]
        intro y hy q hq
        rw [commutatorElement_def]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : q * y⁻¹ * q⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.mp (hQ₀Y hq) y⁻¹).mp (Y.inv_mem hy)
          rw [show y * q * y⁻¹ * q⁻¹ = y * (q * y⁻¹ * q⁻¹) by group]
          exact Y.mul_mem hy this
        · exact F.mul_mem (hFn.conj_mem q (Subgroup.mem_inf.mp hq).1 y)
            (F.inv_mem (Subgroup.mem_inf.mp hq).1)
      rw [inf_eq_bot_of_odd_of_isPGroup (odd_card_oddFit X) hF2, le_bot_iff] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have h2 := sup_le hE hY
    rwa [← hXE] at h2
  obtain ⟨z, hzF, e, he, rfl⟩ := exists_mul_of_mem_fstar ha
  have heF : e ∈ Subgroup.centralizer (F : Set M) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (layer_centralizes_fitting ⊤) he
  have hCa : ∀ m ∈ F, m ∈ Subgroup.centralizer ({z * e} : Set M) ↔
      m ∈ Subgroup.centralizer ({z} : Set M) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hem : e * m = m * e := (Subgroup.mem_centralizer_iff.mp heF m hm).symm
    constructor
    · intro h
      have h1 : m * z * e = z * m * e := by
        calc m * z * e = m * (z * e) := by group
          _ = z * e * m := h
          _ = z * (e * m) := by group
          _ = z * (m * e) := by rw [hem]
          _ = z * m * e := by group
      exact mul_right_cancel h1
    · intro h
      calc m * (z * e) = (m * z) * e := by group
        _ = (z * m) * e := by rw [h]
        _ = z * (m * e) := by group
        _ = z * (e * m) := by rw [hem]
        _ = z * e * m := by group
  have hzQ₀ : z ∈ Q₀ :=
    Subgroup.mem_inf.mpr ⟨hzF, (hCa z hzF).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    hF2.to_le (Subgroup.zpowers_le.mpr hzF)
  have hPK : ⁅Subgroup.zpowers z, X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    rw [CFSG.Walter.centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hXQ₀ hx) z hzQ₀).symm
  have hCBK : ⁅F ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup M) : Set M), X⁆ = ⊥ := by
    rw [CFSG.Walter.centralizer_zpowers_eq']
    have hQ : F ⊓ Subgroup.centralizer ({z} : Set M) = Q₀ := by
      ext m
      constructor
      · rintro ⟨hm, hmz⟩
        exact Subgroup.mem_inf.mpr ⟨hm, (hCa m hm).mpr hmz⟩
      · rintro ⟨hm, hma⟩
        exact Subgroup.mem_inf.mpr ⟨hm, (hCa m hm).mp hma⟩
    rw [hQ, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXQ₀
  exact CFSG.GorensteinWalter.bender1970_1_1_thompson 2 Nat.prime_two (Subgroup.zpowers z) X F
    hzp hF2 (pResidualOf_eq_self_X hXE)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hFn]; exact le_top) hXF hPK hCBK

end Thompson

section Normalizes

variable {M : Type} [Group M] [Finite M]

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {L : Subgroup G} {g : G}
    (h : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rwa [← this]

theorem centralizer_le_normalizer_component {A L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hAL : ¬ A ⊓ L ≤ Subgroup.centralizer (L : Set M)) :
    Subgroup.centralizer (A : Set M) ≤ Subgroup.normalizer (L : Set M) := by
  intro g hg
  obtain ⟨b, hb, hbC⟩ := Set.not_subset.mp hAL
  obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
  have hLg := CFSG.Walter.isComponentOf_map_conj hL (Subgroup.mem_top (G := M)
    (x := g) |> fun h => by rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top]; exact h)
  rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hLg hL with h | h
  · exact mem_normalizer_of_map_conj_eq h
  · exfalso
    apply hbC
    have hbg : b ∈ L.map (MulAut.conj g).toMonoidHom := by
      refine ⟨b, hbL, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← (Subgroup.mem_centralizer_iff.mp hg) b hbA, mul_inv_cancel_right]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hbg

theorem le_normalizer_component (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {a : M} (haA : a ∈ A) {X : Subgroup M}
    (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
    (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) {L : Subgroup M}
    (hL : IsComponentOf L ⊤) (hLK : L ≤ normalClosureIn ⊤ A) :
    X ≤ Subgroup.normalizer (L : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAc := hS.2.1
  have hAa : A ≤ Subgroup.centralizer ({a} : Set M) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAc.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩)
  have hAX : A ≤ Subgroup.normalizer (X : Set M) := hAa.trans hXa
  have hKN : normalClosureIn ⊤ A ≤ Subgroup.normalizer (L : Set M) :=
    (normalClosureIn_le_fstar h31 hO hS).trans (fstar_le_normalizer hL)
  have hCN : Subgroup.centralizer (A : Set M) ≤ Subgroup.normalizer (L : Set M) :=
    centralizer_le_normalizer_component hL (not_inf_le_centralizer h31 hO hS hL hLK)
  have hKn := normalClosureIn_top_normal A
  have hcommK : ∀ B : Subgroup M, ⁅B, A⁆ ≤ normalClosureIn ⊤ A := fun B =>
    (Subgroup.commutator_mono le_rfl (le_normalClosureIn_top A)).trans
      (Subgroup.commutator_le_right B _)
  have hE : componentLayerOf X ≤ Subgroup.normalizer (L : Set M) := by
    refine sSup_le fun K hK => ?_
    rcases le_commutator_or_commutator_eq_bot hK hAX with h | h
    · exact h.trans ((hcommK K).trans hKN)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h) |> fun h' =>
          (Subgroup.le_centralizer_iff.mp h')).trans hCN
  have hY : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.normalizer (L : Set M) := by
    set Y := oddCoreOf (CFSG.fittingSubgroupOf X)
    have hAY : A ≤ Subgroup.normalizer (Y : Set M) := hAX.trans (normalizer_le_normalizer_oddFit X)
    have hYs : Group.IsSolvable Y := by
      have := isNilpotent_oddFit X
      infer_instance
    have hA2 : IsPGroup 2 A := by
      obtain ⟨-, -, T, hT, hAT, -⟩ := hS
      exact hT.2.1.to_le hAT
    have hcop : Nat.Coprime (Nat.card A) (Nat.card Y) := by
      obtain ⟨k, hk⟩ := hA2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_oddFit X))
    have h1 := CFSG.Walter.le_sup_commutator_of_coprime hAY hYs hcop
    refine h1.trans (sup_le (inf_le_right.trans hCN) ((hcommK Y).trans hKN))
  have h2 := sup_le hE hY
  rwa [← hXE] at h2

end Normalizes

end CFSG.Goldschmidt.G37
