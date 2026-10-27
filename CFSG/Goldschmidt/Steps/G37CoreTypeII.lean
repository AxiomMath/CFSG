module

public import CFSG.Goldschmidt.Steps.G37CoreTypeI

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

theorem isTypeL2Odd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Walter.IsTypeL2Odd X) : CFSG.Walter.IsTypeL2Odd Y := by
  obtain ⟨p, f, hp, h1, h2, h3, h4, ⟨φ⟩⟩ := h
  exact ⟨p, f, hp, h1, h2, h3, h4, ⟨e.symm.trans φ⟩⟩

section Prelim

variable {M : Type} [Group M] [Finite M]

theorem eq_bot_of_odd_of_le_normalizer {L W : Subgroup M}
    (hLq : GorensteinWalter.IsQuasisimple L) (hLC : L ⊓ Subgroup.centralizer (L : Set M) = ⊥)
    (hWL : W ≤ L) (hLW : L ≤ Subgroup.normalizer (W : Set M)) (hWodd : Odd (Nat.card W)) :
    W = ⊥ := by
  rcases eq_or_le_centralizer_of_le_normalizer hLq hWL hLW with h | h
  · exfalso
    have h2 := CFSG.Walter.IsQuasisimple.two_dvd_card hLq
    rw [← h] at h2
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  · rw [← le_bot_iff, ← hLC]
    exact le_inf hWL h

theorem center_eq_bot_typeII (hO : goldschmidtOddCore M = ⊥) {L : Subgroup M}
    (hL : IsComponentOf L ⊤) (hII : IsGoldTypeII L) : Subgroup.center L = ⊥ := by
  obtain ⟨k, hk⟩ := (isPGroup_center hO hL).exists_card_eq
  have hodd := hII.1
  apply Subgroup.eq_bot_of_card_eq
  rw [hk] at hodd ⊢
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero]

omit [Finite M] in
theorem inf_centralizer_eq_bot_of_center {L : Subgroup M} (hZ : Subgroup.center L = ⊥) :
    L ⊓ Subgroup.centralizer (L : Set M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  have h1 : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := (mem_center_iff_mem_centralizer _).mpr hxC
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

omit [Finite M] in
theorem isSimpleGroup_of_center_eq_bot {L : Subgroup M} (hLq : GorensteinWalter.IsQuasisimple L)
    (hZ : Subgroup.center L = ⊥) : IsSimpleGroup L := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end Prelim

section Core

variable {M : Type} [Group M] [Finite M]

variable (h31 : S_G31) (h34 : S_G34) (h35 : S_G35) (hO : goldschmidtOddCore M = ⊥)
  {A : Subgroup M} (hS : IsSStarIn ⊤ A) (hE : CFSG.Open.IsElemAbelian 2 A) {a : M} (haA : a ∈ A)
  {X : Subgroup M}
  (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
  (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) {L : Subgroup M}
  (hL : IsComponentOf L ⊤) (hLK : L ≤ normalClosureIn ⊤ A) (hII : IsGoldTypeII L)
  (hLa : ¬ L ≤ Subgroup.centralizer ({a} : Set M))

include h31 h34 h35 hO hS hE haA hXa hXE hL hLK hII hLa

omit h34 h35 hE in
theorem typeII_data :
    ∃ b ∈ A ⊓ L, ∃ c ∈ A ⊓ Subgroup.centralizer (L : Set M), b * c = a ∧
      b ∉ Subgroup.centralizer (L : Set M) ∧
      L ⊓ Subgroup.centralizer ({a} : Set M) = L ⊓ Subgroup.centralizer ({b} : Set M) ∧
      Subgroup.center L = ⊥ ∧ L ⊓ Subgroup.centralizer (L : Set M) = ⊥ ∧ IsSimpleGroup L ∧
      IsSStarIn L (A ⊓ L) ∧ A ⊓ L ≠ ⊥ ∧ X ≤ Subgroup.normalizer (L : Set M) := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab⟩ := exists_inner_typeI h31 hO hS haA hL hLK hLa
  have hZ := center_eq_bot_typeII hO hL hII
  refine ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, inf_centralizer_eq_bot_of_center hZ,
    isSimpleGroup_of_center_eq_bot hL.2.2 hZ, (componentFacts31 h31 hO hS hL hLK).1, ?_,
    le_normalizer_component h31 hO hS haA hXa hXE hL hLK⟩
  intro h
  apply hbZ
  have : b ∈ A ⊓ L := hb
  rw [h, Subgroup.mem_bot] at this
  rw [this]
  exact Subgroup.one_mem _

omit h34 hE in
theorem typeII_component_not_le {K : Subgroup M} (hK : IsComponentOf K X) (hKL : ¬ K ≤ L) :
    ⁅K, L⁆ = ⊥ := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, hLC, hLs, hSL, hAL, hXL⟩ :=
    typeII_data h31 hO hS haA hXa hXE hL hLK hII hLa
  have hCaX : L ⊓ Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M) :=
    inf_le_right.trans hXa
  have hKN : K ≤ Subgroup.normalizer (L : Set M) := hK.1.trans hXL
  rcases le_commutator_or_commutator_eq_bot hK hCaX with h | h
  · exfalso
    apply hKL
    refine h.trans ?_
    rw [Subgroup.commutator_le]
    intro k hk ℓ hℓ
    rw [commutatorElement_def]
    have hℓL := (Subgroup.mem_inf.mp hℓ).1
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hk) ℓ).mp hℓL) (L.inv_mem hℓL)
  have hKC : K ≤ Subgroup.centralizer
      ((L ⊓ Subgroup.centralizer ({b} : Set M) : Subgroup M) : Set M) := by
    rw [← hCab]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hALb : A ⊓ L ≤ L ⊓ Subgroup.centralizer ({b} : Set M) := by
    intro x hx
    obtain ⟨hxA, hxL⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (hS.2.1.is_comm.comm ⟨x, hxA⟩ ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
  have hKA : ⁅K, A ⊓ L⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact hKC.trans (Subgroup.centralizer_le hALb)
  obtain ⟨h1, -⟩ := g35_subgroup h35 (open_isQuasisimple_iff.mpr hL.2.2) hII hSL hAL hKN
  obtain ⟨y, hy, hKy⟩ := h1 hKA
  have hKp : Group.IsPerfect K := Group.isPerfect_def.mpr hK.2.2.2.1
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer
      ((L ⊔ Subgroup.centralizer (L : Set M) : Subgroup M) : Set M) := by
    rw [Subgroup.zpowers_le]
    exact CFSG.Walter.mem_normalizer_sup (hKN hy)
      (normalizer_le_normalizer_centralizer' L (hKN hy))
  have hKLC : K ≤ L ⊔ Subgroup.centralizer (L : Set M) :=
    le_of_perfect_of_le_sup hKp hKy hyN (by
      have : IsMulCommutative (Subgroup.zpowers y) := inferInstance
      infer_instance)
  have hWab : IsMulCommutative (proj L K) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxC := proj_le_centralizer inf_le_left hKC x.2
    have hyC := proj_le_centralizer inf_le_left hKC y.2
    have hyL := proj_le L K y.2
    have hyb : (y : M) ∈ L ⊓ Subgroup.centralizer ({b} : Set M) := by
      refine Subgroup.mem_inf.mpr ⟨hyL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbC : b ∈ L ⊓ Subgroup.centralizer ({b} : Set M) :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).2,
          Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      exact ((Subgroup.mem_centralizer_iff.mp hyC) b hbC).symm
    exact ((Subgroup.mem_centralizer_iff.mp hxC) y hyb).symm
  have hKC' : K ≤ Subgroup.centralizer (L : Set M) :=
    le_of_perfect_of_le_sup hKp (le_proj_sup_centralizer hKLC)
      ((proj_le L K).trans (le_normalizer_centralizer L)) inferInstance
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKC'

omit h35 in
theorem typeII_component_le {K : Subgroup M} (hK : IsComponentOf K X) (hKL : K ≤ L) :
    K = L ∨ (K ≤ Subgroup.centralizer ({a} : Set M) ∧ IsGoldL2 K ∧ IsGoldJR L) := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, hLC, hLs, hSL, hAL, hXL⟩ :=
    typeII_data h31 hO hS haA hXa hXE hL hLK hII hLa
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).2
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Subgroup.one_mem _)
  have hCaX : L ⊓ Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M) :=
    inf_le_right.trans hXa
  set E := layerIn X L with hE'
  have hEN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (E : Set M) := by
    intro g hg
    rw [← hCab] at hg
    exact mem_normalizer_layerIn (hCaX hg) (Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1)
  have hKE : K ≤ E := le_layerIn hK hKL
  have hEne : E ≠ ⊥ := by
    intro hE0
    apply (Subgroup.nontrivial_iff_ne_bot K).mp hK.2.2.1
    exact le_bot_iff.mp (hE0 ▸ hKE)
  have hEp : Group.IsPerfect E := isPerfect_layerIn X L
  by_cases hM : L ⊓ Subgroup.normalizer (E : Set M) = L
  · left
    have hLE : L ≤ Subgroup.normalizer (E : Set M) := hM ▸ inf_le_right
    rcases eq_or_le_centralizer_of_le_normalizer hL.2.2 (layerIn_le X L) hLE with h | h
    · have hLX : IsComponentOf L X := isComponentOf_of_le hL (h ▸ layerIn_le_X X L) le_top
      exact eq_of_isComponentOf_of_le hK hLX hKL
    · exact absurd (hKE.trans h |>.trans (Subgroup.centralizer_le hKL))
        (not_le_centralizer_self hK.2.2)
  have hEM : E ≤ L ⊓ Subgroup.normalizer (E : Set M) :=
    le_inf (layerIn_le X L) Subgroup.le_normalizer
  rcases hII.2 with hL2 | hJR
  · exfalso
    obtain ⟨h4, hL2p⟩ := g34_subgroup h34 hLs hZ hII hSL hAL
    obtain ⟨-, hperfN, hloc⟩ := hL2p hL2
    rcases h4 b hb hb1 _ inf_le_left (le_inf inf_le_left hEN) hM with h | h
    · exact hEne ((hloc b hb hb1).2 E (h ▸ hEM) hEp)
    · exact hEne (hperfN E (le_inf (layerIn_le X L) (hEM.trans h)) hEp)
  · right
    have hJR' : CFSG.Walter.IsTypeJR L := CFSG.Walter.IsTypeJR.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hJR
    set b' : L := ⟨b, hbL⟩ with hb'
    have hb2 : orderOf b' = 2 := by
      have hsq : b' ^ 2 = 1 := Subtype.ext (hE.2 b (Subgroup.mem_inf.mp hb).1)
      exact orderOf_eq_prime hsq (fun h => hb1 (congrArg Subtype.val h))
    have hco := (hJR'.2.2 b' hb2).1
    have hCa : ∀ x : L, x ∈ Subgroup.centralizer ({b'} : Set L) ↔
        (x : M) ∈ Subgroup.centralizer ({b} : Set M) := by
      intro x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hCbM : Subgroup.centralizer ({b'} : Set L) ≤
        (L ⊓ Subgroup.normalizer (E : Set M)).subgroupOf L := fun x hx =>
      Subgroup.mem_inf.mpr ⟨x.2, hEN (Subgroup.mem_inf.mpr ⟨x.2, (hCa x).mp hx⟩)⟩
    have hMtop : (L ⊓ Subgroup.normalizer (E : Set M)).subgroupOf L ≠ ⊤ := by
      intro h
      apply hM
      apply le_antisymm inf_le_left
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ (L ⊓ Subgroup.normalizer (E : Set M)).subgroupOf L :=
        h ▸ Subgroup.mem_top _
      exact this
    have hMeq := (hco.le_iff.mp hCbM).resolve_left hMtop
    have hEC : E ≤ Subgroup.centralizer ({b} : Set M) := by
      intro x hx
      have h1 : (⟨x, layerIn_le X L hx⟩ : L) ∈ (L ⊓ Subgroup.normalizer (E : Set M)).subgroupOf L :=
        hEM hx
      rw [hMeq] at h1
      exact (hCa _).mp h1
    have hKa : K ≤ Subgroup.centralizer ({a} : Set M) := by
      intro x hx
      have hxb := Subgroup.mem_centralizer_singleton_iff.mp (hEC (hKE hx))
      have hxc : x * c = c * x :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x (hKL hx)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hbc]
      calc x * (b * c) = (x * b) * c := by group
        _ = (b * x) * c := by rw [hxb]
        _ = b * (x * c) := by group
        _ = b * (c * x) := by rw [hxc]
        _ = b * c * x := by group
    refine ⟨hKa, ?_, hJR⟩
    have hEL : E ≤ L := layerIn_le X L
    have hAC : E.subgroupOf L ≤ Subgroup.centralizer ({b'} : Set L) :=
      fun x hx => (hCa x).mpr (hEC hx)
    have hCA : Subgroup.centralizer ({b'} : Set L) ≤
        Subgroup.normalizer ((E.subgroupOf L : Subgroup L) : Set L) := by
      intro x hx
      rw [← Subgroup.subgroupOf_normalizer_eq hEL]
      exact hEN (Subgroup.mem_inf.mpr ⟨x.2, (hCa x).mp hx⟩)
    have hBA : K.subgroupOf L ≤ E.subgroupOf L := fun x hx => hKE hx
    have hBq : GorensteinWalter.IsQuasisimple (K.subgroupOf L) :=
      CFSG.Walter.isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKL).symm hK.2.2
    have hBsn : ((K.subgroupOf L).subgroupOf (E.subgroupOf L)).IsSubnormal := by
      have hKE' : IsComponentOf K E := isComponentOf_of_le hK hKE (layerIn_le_X X L)
      have h1 := hKE'.2.1.comap (Subgroup.subgroupOfEquivOfLe hEL).toMonoidHom
      have h2 : (K.subgroupOf L).subgroupOf (E.subgroupOf L) =
          (K.subgroupOf E).comap (Subgroup.subgroupOfEquivOfLe hEL).toMonoidHom := by
        ext x
        rfl
      rw [h2]
      exact h1
    obtain ⟨h1, h2⟩ := hJR'.isTypeL2Odd_of_isSubnormal hb2 hAC hCA hBA hBq hBsn
    let φ : K ≃* K.subgroupOf L := (Subgroup.subgroupOfEquivOfLe hKL).symm
    have hZK : Subgroup.center K = ⊥ := by
      have h3 : (Subgroup.center K).map (φ : K →* K.subgroupOf L) = ⊥ := by
        rw [Subgroup.map_center_eq φ, h2]
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h3
    let e : K ⧸ Subgroup.center K ≃* K.subgroupOf L :=
      ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot).trans φ
    exact isTypeL2Odd_of_mulEquiv e.symm h1

omit h34 hE in
theorem typeII_oddFit_le_sup :
    oddCoreOf (CFSG.fittingSubgroupOf X) ≤ L ⊔ Subgroup.centralizer (L : Set M) := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, hLC, hLs, hSL, hAL, hXL⟩ :=
    typeII_data h31 hO hS haA hXa hXE hL hLK hII hLa
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Subgroup.one_mem _)
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYX : Y ≤ X := oddFit_le X
  have hCaY : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (Y : Set M) := by
    rw [← hCab]
    exact inf_le_right.trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  have hFY : CFSG.fittingSubgroupOf Y = Y := by
    have : Group.IsNilpotent Y := isNilpotent_oddFit X
    have htop : CFSG.fittingSubgroup Y = ⊤ := le_antisymm le_top
      (le_sSup ⟨Subgroup.normal_top, (Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm)⟩)
    rw [CFSG.fittingSubgroupOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hFY, (show CFSG.fittingSubgroupOf Y = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf Y)]
  refine iSup_le fun q => ?_
  have hp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  have hpY : q.1.1 ∣ Nat.card Y := Nat.dvd_of_mem_primeFactors q.1.2
  have hp2 : q.1.1 ≠ 2 := by
    intro h
    rw [h] at hpY
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddFit X)) (even_iff_two_dvd.mpr hpY)
  have hQN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤
      Subgroup.normalizer (qCoreOf Y q.1.1 : Set M) := by
    have : Fact q.1.1.Prime := ⟨hp⟩
    exact hCaY.trans (CFSG.Walter.normalizer_le_normalizer_map_of_characteristic _)
  have hQL : qCoreOf Y q.1.1 ≤ Subgroup.normalizer (L : Set M) :=
    (qCoreOf_le Y _).trans (hYX.trans hXL)
  exact ((g35_subgroup h35 (open_isQuasisimple_iff.mpr hL.2.2) hII hSL hAL hQL).2 b hb hb1 hQN
    ⟨q.1.1, hp, hp2, qCoreOf_isPGroup Y _⟩).1

omit h34 in
theorem typeII_JR_oddFit (hJR : IsGoldJR L) :
    oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set M) := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, hLC, hLs, hSL, hAL, hXL⟩ :=
    typeII_data h31 hO hS haA hXa hXE hL hLK hII hLa
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).2
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Subgroup.one_mem _)
  have hYLC := typeII_oddFit_le_sup h31 h35 hO hS haA hXa hXE hL hLK hII hLa
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYX : Y ≤ X := oddFit_le X
  have hCaY : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (Y : Set M) := by
    rw [← hCab]
    exact inf_le_right.trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  set W := proj L Y with hW
  have hWodd : Odd (Nat.card W) := odd_card_proj (hYX.trans hXL) hLC (odd_card_oddFit X)
  have hWN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (W : Set M) :=
    fun g hg => proj_le_normalizer (Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1) (hCaY hg)
  suffices hW0 : W = ⊥ from le_centralizer_of_proj_eq_bot hYLC hW0
  by_cases hM : L ⊓ Subgroup.normalizer (W : Set M) = L
  · exact eq_bot_of_odd_of_le_normalizer hL.2.2 hLC (proj_le L Y) (hM ▸ inf_le_right) hWodd
  have hJR' : CFSG.Walter.IsTypeJR L := CFSG.Walter.IsTypeJR.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hJR
  set b' : L := ⟨b, hbL⟩ with hb'
  have hbsq : b' ^ 2 = 1 := Subtype.ext (hE.2 b (Subgroup.mem_inf.mp hb).1)
  have hb2 : orderOf b' = 2 := orderOf_eq_prime hbsq (fun h => hb1 (congrArg Subtype.val h))
  have hco := (hJR'.2.2 b' hb2).1
  have hCa : ∀ x : L, x ∈ Subgroup.centralizer ({b'} : Set L) ↔
      (x : M) ∈ Subgroup.centralizer ({b} : Set M) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hCbM : Subgroup.centralizer ({b'} : Set L) ≤
      (L ⊓ Subgroup.normalizer (W : Set M)).subgroupOf L := fun x hx =>
    Subgroup.mem_inf.mpr ⟨x.2, hWN (Subgroup.mem_inf.mpr ⟨x.2, (hCa x).mp hx⟩)⟩
  have hMtop : (L ⊓ Subgroup.normalizer (W : Set M)).subgroupOf L ≠ ⊤ := by
    intro h
    apply hM
    apply le_antisymm inf_le_left
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ (L ⊓ Subgroup.normalizer (W : Set M)).subgroupOf L :=
      h ▸ Subgroup.mem_top _
    exact this
  have hMeq := (hco.le_iff.mp hCbM).resolve_left hMtop
  have hWL : W ≤ L := proj_le L Y
  have hRC : W.subgroupOf L ≤ Subgroup.centralizer ({b'} : Set L) := by
    intro x hx
    have h1 : x ∈ (L ⊓ Subgroup.normalizer (W : Set M)).subgroupOf L :=
      Subgroup.mem_inf.mpr ⟨x.2, Subgroup.le_normalizer hx⟩
    rwa [hMeq] at h1
  have hCR : Subgroup.centralizer ({b'} : Set L) ≤
      Subgroup.normalizer ((W.subgroupOf L : Subgroup L) : Set L) := by
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hWL]
    exact hWN (Subgroup.mem_inf.mpr ⟨x.2, (hCa x).mp hx⟩)
  have hRodd : Odd (Nat.card (W.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
    exact hWodd
  have h2L : 2 ∣ Nat.card L := CFSG.Walter.IsQuasisimple.two_dvd_card hL.2.2
  have hR := (CFSG.Walter.odd_normal_subgroup_centralizer h2L (Or.inr hJR') hbsq hRodd hRC
    hCR).2 (Or.inr hJR')
  have h3 := congrArg (Subgroup.map L.subtype) hR
  rwa [Subgroup.map_subgroupOf_eq_of_le hWL, Subgroup.map_bot] at h3

omit hE in
theorem typeII_L2 (hL2 : IsGoldL2 L) :
    (∀ y ∈ oddCoreOf (CFSG.fittingSubgroupOf X), ⁅y, a⁆ ∈ Subgroup.centralizer (L : Set M)) ∧
    (∀ Y₀ : Subgroup M, Y₀ ≤ oddCoreOf (CFSG.fittingSubgroupOf X) →
      ∃ y ∈ Y₀, Y₀ ≤ Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set M)) ∧
    (∀ Y₀ : Subgroup M, Y₀ ≤ oddCoreOf (CFSG.fittingSubgroupOf X) → ⁅A ⊓ L, Y₀⁆ = ⊥ →
      Y₀ ≤ Subgroup.centralizer (L : Set M)) := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab, hZ, hLC, hLs, hSL, hAL, hXL⟩ :=
    typeII_data h31 hO hS haA hXa hXE hL hLK hII hLa
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).2
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Subgroup.one_mem _)
  have hYLC := typeII_oddFit_le_sup h31 h35 hO hS haA hXa hXE hL hLK hII hLa
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYX : Y ≤ X := oddFit_le X
  have hYL : Y ≤ Subgroup.normalizer (L : Set M) := hYX.trans hXL
  have hCaY : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (Y : Set M) := by
    rw [← hCab]
    exact inf_le_right.trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  set W := proj L Y with hW
  have hWL : W ≤ L := proj_le L Y
  have hWodd : Odd (Nat.card W) := odd_card_proj hYL hLC (odd_card_oddFit X)
  have hWN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (W : Set M) :=
    fun g hg => proj_le_normalizer (Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1) (hCaY hg)
  obtain ⟨h4, hL2p⟩ := g34_subgroup h34 hLs hZ hII hSL hAL
  obtain ⟨hCAL, -, hloc⟩ := hL2p hL2
  have hAL2 : A ⊓ L ≤ L ⊓ Subgroup.centralizer ({b} : Set M) := by
    intro x hx
    obtain ⟨hxA, hxL⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (hS.2.1.is_comm.comm ⟨x, hxA⟩ ⟨b, (Subgroup.mem_inf.mp hb).1⟩)
  have hA2 : IsPGroup 2 (A ⊓ L : Subgroup M) := by
    obtain ⟨-, -, T, hT, hAT, -⟩ := hS
    exact hT.2.1.to_le (inf_le_left.trans hAT)
  have hcentAL : ∀ V : Subgroup M, V ≤ L → Odd (Nat.card V) →
      V ≤ Subgroup.centralizer ((A ⊓ L : Subgroup M) : Set M) → V = ⊥ := by
    intro V hVL hVodd hVC
    have h1 : V ≤ A ⊓ L := fun x hx => hCAL (Subgroup.mem_inf.mpr ⟨hVL hx, hVC hx⟩)
    have h2 := inf_eq_bot_of_odd_of_isPGroup hVodd hA2
    rwa [inf_eq_left.mpr h1] at h2
  have hWb : W ≤ L ⊓ Subgroup.centralizer ({b} : Set M) := by
    by_cases hM : L ⊓ Subgroup.normalizer (W : Set M) = L
    · rw [eq_bot_of_odd_of_le_normalizer hL.2.2 hLC hWL (hM ▸ inf_le_right) hWodd]
      exact bot_le
    rcases h4 b hb hb1 _ inf_le_left (le_inf inf_le_left hWN) hM with h | h
    · rw [← h]
      exact le_inf hWL Subgroup.le_normalizer
    · have hWA : W ≤ Subgroup.normalizer ((A ⊓ L : Subgroup M) : Set M) := fun x hx =>
        h (Subgroup.mem_inf.mpr ⟨hWL hx, Subgroup.le_normalizer hx⟩)
      have hAW : A ⊓ L ≤ Subgroup.normalizer (W : Set M) := hAL2.trans hWN
      have hcomm : ⁅W, A ⊓ L⁆ ≤ W ⊓ (A ⊓ L) := by
        rw [Subgroup.commutator_le]
        intro w hw x hx
        rw [commutatorElement_def]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : x * w⁻¹ * x⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hAW hx) w⁻¹).mp (W.inv_mem hw)
          rw [show w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) by group]
          exact W.mul_mem hw this
        · exact (A ⊓ L).mul_mem ((Subgroup.mem_normalizer_iff.mp (hWA hw) x).mp hx)
            ((A ⊓ L).inv_mem hx)
      rw [inf_eq_bot_of_odd_of_isPGroup hWodd hA2, le_bot_iff] at hcomm
      rw [hcentAL W hWL hWodd (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)]
      exact bot_le
  refine ⟨fun y hy => ?_, fun Y₀ hY₀ => ?_, fun Y₀ hY₀ hcomm => ?_⟩
  ·
    obtain ⟨w, hw, c', hc', hwc⟩ := mem_sup_of_le_normalizer
      (hWL.trans (le_normalizer_centralizer L)) (le_proj_sup_centralizer hYLC hy)
    have hcL : c ∈ Subgroup.centralizer (L : Set M) := (Subgroup.mem_inf.mp hc).2
    refine commutator_mem_centralizer_of_inner (ℓ := w) (m := b) ?_ ?_ (hWL hw) hbL ?_
    · intro x hx
      rw [← hwc]
      have hxc : x * c' = c' * x := Subgroup.mem_centralizer_iff.mp hc' x hx
      calc w * c' * x * (w * c')⁻¹ = w * (c' * x) * c'⁻¹ * w⁻¹ := by group
        _ = w * (x * c') * c'⁻¹ * w⁻¹ := by rw [hxc]
        _ = w * x * w⁻¹ := by group
    · intro x hx
      rw [← hbc]
      have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcL x hx
      calc b * c * x * (b * c)⁻¹ = b * (c * x) * c⁻¹ * b⁻¹ := by group
        _ = b * (x * c) * c⁻¹ * b⁻¹ := by rw [hxc]
        _ = b * x * b⁻¹ := by group
    · exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hWb hw)).2
  · have hY₀L : Y₀ ≤ Subgroup.normalizer (L : Set M) := hY₀.trans hYL
    have hY₀odd : Odd (Nat.card Y₀) := (odd_card_oddFit X).of_dvd_nat (Subgroup.card_dvd_of_le hY₀)
    have hP : proj L Y₀ ≤ L ⊓ Subgroup.centralizer ({b} : Set M) := (proj_mono hY₀).trans hWb
    have hcyc := (hloc b hb hb1).1 _ hP (odd_card_proj hY₀L hLC hY₀odd)
    exact exists_zpowers_of_isCyclic_proj hY₀L (hY₀.trans hYLC) hcyc
  · have hY₀L : Y₀ ≤ Subgroup.normalizer (L : Set M) := hY₀.trans hYL
    have hY₀odd : Odd (Nat.card Y₀) := (odd_card_oddFit X).of_dvd_nat (Subgroup.card_dvd_of_le hY₀)
    have hY₀C : Y₀ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup M) : Set M) := by
      rw [Subgroup.commutator_comm] at hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hP0 := hcentAL _ (proj_le L Y₀) (odd_card_proj hY₀L hLC hY₀odd)
      (proj_le_centralizer inf_le_right hY₀C)
    exact le_centralizer_of_proj_eq_bot (hY₀.trans hYLC) hP0

end Core

end CFSG.Goldschmidt.G37
