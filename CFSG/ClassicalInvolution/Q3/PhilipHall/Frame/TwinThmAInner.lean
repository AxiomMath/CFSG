module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8Twin
public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace Inner

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_of_orderOf_eq_two (hd : Q8TwinDatum R S t) {u : Y} (hu : u ∈ R)
    (hu2 : orderOf u = 2) : u = t := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact CFSG.ClassicalInvolution.Nobq.eq_of_orderOf_eq_two_of_datum S e hd.mem hd.order hd.cent hu
    hu2

theorem mem_of_ne_bot (hd : Q8TwinDatum R S t) {P : Subgroup Y} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 ↥P) (hP : P ≠ ⊥) : t ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
  have h2 : 2 ∣ Nat.card ↥P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have hu' : orderOf (u : Y) = 2 := by rwa [Subgroup.orderOf_coe]
  have := eq_of_orderOf_eq_two hd (hPR u.2) hu'
  rw [← this]
  exact u.2

theorem S₀_mem_RSet (hd : Q8TwinDatum R S t) :
    (S : Subgroup R).map R.subtype ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hd.sylow_core

theorem commute_of_normal_two (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {N : Subgroup Y}
    (hN : N.Normal) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) {n : Y} (hn : n ∈ N) : s * n = n * s := by
  have hSN : (S : Subgroup R).map R.subtype ⊓ N = ⊥ := by
    by_contra hne
    exact htN (Subgroup.mem_inf.mp (mem_of_ne_bot hd (inf_le_left.trans
      (Subgroup.map_subtype_le _)) ((hd.sylow_core.2.1).to_le inf_le_left) hne)).2
  have hcomm := comm613Gen_normal hΩ (S₀_mem_RSet hd) hN hSN
  have hodd : oddCoreOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hN2.to_le (Subgroup.zpowers_le.mpr (oddCoreOf_le_self N hx))
    rw [Subgroup.mem_bot]
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard N) hx hx2
  rw [hodd, le_bot_iff] at hcomm
  have := Subgroup.commutator_mem_commutator hs hn
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem q8_center (hd : Q8TwinDatum R S t) (e : ↥(S : Subgroup R) ≃* QuaternionGroup 2) :
    (((e.symm (QuaternionGroup.a 2) : ↥(S : Subgroup R)) : ↥R) : Y) = t := by
  set u : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 2) with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, q8_central_sq, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h
    exact q8_a2_ne (by simpa using congrArg e h)
  have hord : orderOf (((u : ↥R) : Y)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) hu2
      simpa using this
    · intro h
      apply hu1
      exact Subtype.ext (Subtype.ext h)
  exact eq_of_orderOf_eq_two hd (u : ↥R).2 hord

theorem S₀_cases (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) : s = 1 ∨ s = t ∨ s * s = t := by
  obtain ⟨e⟩ := hq8
  obtain ⟨x, hx, rfl⟩ := hs
  have hct := q8_center hd e
  rcases q8_cases (e ⟨x, hx⟩) with h | h | h
  · left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = 1 := e.injective (by rw [h, map_one])
    have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) this
    simpa using this
  · right; left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm (QuaternionGroup.a 2) := by
      rw [← h, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl
  · right; right
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) * ⟨x, hx⟩ = e.symm (QuaternionGroup.a 2) := by
      rw [← h, ← map_mul, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl

theorem q8_inverting (q : QuaternionGroup 2) (hq : q * q = QuaternionGroup.a 2) :
    ∃ q' : QuaternionGroup 2, q' * q * q'⁻¹ = q⁻¹ := by
  revert q
  decide

theorem exists_inverting (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {r : Y}
    (hrS : r ∈ (S : Subgroup R).map R.subtype) (hrr : r * r = t) :
    ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹ := by
  obtain ⟨e⟩ := hq8
  have hct := q8_center hd e
  obtain ⟨x, hx, rfl⟩ := hrS
  have hxx : (⟨x, hx⟩ : ↥(S : Subgroup R)) * ⟨x, hx⟩ = e.symm (QuaternionGroup.a 2) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hct]
    exact hrr
  have hq : e ⟨x, hx⟩ * e ⟨x, hx⟩ = QuaternionGroup.a 2 := by
    rw [← map_mul, hxx, MulEquiv.apply_symm_apply]
  obtain ⟨q', hq'⟩ := q8_inverting _ hq
  refine ⟨(((e.symm q' : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm q').2, rfl⟩, ?_⟩
  have h1 : e.symm q' * ⟨x, hx⟩ * (e.symm q')⁻¹ = (⟨x, hx⟩ : ↥(S : Subgroup R))⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hq'
  have h2 := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) h1
  simpa using h2

theorem exists_noncomm (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {r : Y}
    (hrS : r ∈ (S : Subgroup R).map R.subtype) (hrr : r * r = t) :
    ∃ s ∈ (S : Subgroup R).map R.subtype, s * r ≠ r * s := by
  obtain ⟨s, hs, hsr⟩ := exists_inverting hd hq8 hrS hrr
  refine ⟨s, hs, fun h => ?_⟩
  have h1 : s * r * s⁻¹ = r := by rw [h]; group
  rw [h1] at hsr
  have : r * r = 1 := by simpa using congrArg (· * r) hsr
  rw [hrr] at this
  have h' := hd.order
  rw [this, orderOf_one] at h'
  norm_num at h'

theorem exists_inner (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrA : conjSub r A ≠ A) :
    ∃ a ∈ A, ∃ e : Y, (∀ x ∈ A, x * e = e * x) ∧ t = a * e := by
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  set E₀ : Subgroup Y := ⨆ g : ↥S₀, conjSub (g : Y) A with hE₀
  have hAE : A ≤ E₀ := by
    have := le_iSup (fun g : ↥S₀ => conjSub (g : Y) A) 1
    simpa using this
  have hSN : S₀ ≤ Subgroup.normalizer (E₀ : Set Y) := by
    intro s hs
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have e1 : conjSub s E₀ = ⨆ g : ↥S₀, conjSub (s * (g : Y)) A := by
      rw [hE₀, conjSub, Subgroup.map_iSup]
      congr 1
      ext g : 1
      rw [conjSub_mul]
      rfl
    rw [e1]
    exact Equiv.iSup_comp (g := fun g : ↥S₀ => conjSub (g : Y) A)
      (Equiv.mulLeft (⟨s, hs⟩ : ↥S₀))
  have hEN : E₀ ≤ Subgroup.normalizer (E₀ : Set Y) := Subgroup.le_normalizer
  set Y' : Subgroup Y := S₀ ⊔ E₀ with hY'
  have hY'N : ∀ y ∈ Y', conjSub y E₀ = E₀ := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hSN hEN) hy)
  have hnb : S₀ ⊓ E₀ ≠ ⊥ := by
    intro hbot
    have h613 := comm613Gen hΩ (S₀_mem_RSet hd) le_sup_left le_sup_right hY'N hbot
    have hsolv : Group.IsSolvable ↥(oddCoreOf E₀) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (oddCoreOf_odd_natCard E₀)
    have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
    refine TightA.false_of_solvable_covers hA.1 hsolv fun x hx => ⟨x * r * x⁻¹ * r⁻¹, ?_, ?_⟩
    · have hc : ⁅x, r⁆ ∈ ⁅E₀, S₀⁆ := Subgroup.commutator_mem_commutator (hAE hx) hrS
      rw [Subgroup.commutator_comm] at hc
      have := h613 hc
      rwa [commutatorElement_def] at this
    · intro a ha
      have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
      have hc := comm_of_ne hAr hA hrA hu ha
      calc x * r * x⁻¹ * r⁻¹ * a * (x * r * x⁻¹ * r⁻¹)⁻¹
          = x * ((r * x⁻¹ * r⁻¹) * a) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by group
        _ = x * a * x⁻¹ := by rw [hc]; group
  have htE : t ∈ E₀ := (Subgroup.mem_inf.mp (mem_of_ne_bot hd
    (inf_le_left.trans (Subgroup.map_subtype_le _))
    ((hd.sylow_core.2.1).to_le inf_le_left) hnb)).2
  set E' : Subgroup Y := ⨆ g : {g : ↥S₀ // conjSub (g : Y) A ≠ A}, conjSub ((g : ↥S₀) : Y) A
    with hE'
  have hE'C : E' ≤ Subgroup.centralizer (A : Set Y) := by
    refine iSup_le fun g => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (comm_of_ne (AscThmA.isComponent_conjSub hA _) hA g.2 hy hx).symm
  have hE₀le : E₀ ≤ A ⊔ E' := by
    refine iSup_le fun g => ?_
    by_cases h : conjSub (g : Y) A = A
    · rw [h]; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup_of_le (⟨g, h⟩ : {g : ↥S₀ // conjSub (g : Y) A ≠ A})
        le_rfl)
  have htAE : t ∈ A ⊔ E' := hE₀le htE
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A E'
    (hE'C.trans (Subgroup.centralizer_le_normalizer _))] at htAE
  obtain ⟨a, ha, e, he, hae⟩ := htAE
  refine ⟨a, ha, e, fun x hx => ?_, hae.symm⟩
  exact (Subgroup.mem_centralizer_iff.mp (hE'C he) x hx)

omit [Finite Y] in
theorem t_mul_t (hd : Q8TwinDatum R S t) : t * t = 1 := by
  rw [← pow_two, ← hd.order, pow_orderOf_eq_one]

theorem isUniqueInvolution_core (hd : Q8TwinDatum R S t) :
    IsUniqueInvolution (tightCore R) t := by
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  have htR : t ∈ R := Subgroup.map_subtype_le _ hd.mem
  refine ⟨Subgroup.subset_closure ⟨htR, ht2⟩, ?_, ?_, ?_⟩
  · intro h1
    have := hd.order
    rw [h1, orderOf_one] at this
    norm_num at this
  · rw [← pow_two]
    exact hd.order ▸ pow_orderOf_eq_one t
  · intro y hy hyy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
      exact eq_of_orderOf_eq_two hd (tightCore_le R hy) hord

theorem mem_core_of_mem_S₀ (hd : Q8TwinDatum R S t) {r : Y}
    (hrS : r ∈ (S : Subgroup R).map R.subtype) : r ∈ tightCore R :=
  hd.sylow_core.1 hrS

theorem no_twin (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) {a : Y} (haA : a ∈ A)
    (hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹) (ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a))
    {w : Y} (hw : w ∈ A)
    (hc : ∀ y ∈ A, (w * a * w⁻¹ * a⁻¹) * y = y * (w * a * w⁻¹ * a⁻¹)) : w * a = a * w := by
  set c : Y := w * a * w⁻¹ * a⁻¹ with hcdef
  have hcA : c ∈ A := A.mul_mem (A.mul_mem (A.mul_mem hw haA) (A.inv_mem hw)) (A.inv_mem haA)
  have hca : c * a = a * c := hc a haA
  have hc2 : c * c = 1 := by
    have e1 : (c * a) * (c * a) = a * a := by
      have : c * a = w * a * w⁻¹ := by rw [hcdef]; group
      rw [this]
      calc w * a * w⁻¹ * (w * a * w⁻¹) = w * (a * a) * w⁻¹ := by group
        _ = (a * a) * w * w⁻¹ := by rw [ha2 w hw]
        _ = a * a := by group
    have e2 : (c * a) * (c * a) = (c * c) * (a * a) := by
      calc (c * a) * (c * a) = c * (a * c) * a := by group
        _ = c * (c * a) * a := by rw [hca]
        _ = (c * c) * (a * a) := by group
    rw [e2] at e1
    calc c * c = (c * c) * (a * a) * (a * a)⁻¹ := by group
      _ = 1 := by rw [e1]; group
  have hcZ : c ∈ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) :=
    TightA.mem_centerLayer_of_mem_center hA hcA fun y hy => (hc y hy).symm
  have htZ : t ∉ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) := fun h =>
    hE2 ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup hO, h⟩
  have hcomN : ∀ {s : Y}, s ∈ (S : Subgroup R).map R.subtype → s * c = c * s := fun {s} hs =>
    commute_of_normal_two hd hΩ TightA.centerLayer_normal (TightA.centerLayer_isPGroup hO) htZ
      hs hcZ
  have hrc : r * c = c * r := hcomN hrS
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hwB : r * w * r⁻¹ ∈ conjSub r A := conj_mem_conjSub hw
  have hwtA : t * w⁻¹ * t⁻¹ ∈ A := by
    rw [hta _ (A.inv_mem hw)]
    exact A.mul_mem (A.mul_mem haA (A.inv_mem hw)) (A.inv_mem haA)
  have hcomm := comm_of_ne hB hA hrA hwB hwtA
  set v : Y := w * (r * w * r⁻¹) with hvdef
  have hvr : v * r * v⁻¹ = c * r := by
    have e1 : v * r * v⁻¹ * r⁻¹ =
        w * ((r * w * r⁻¹) * (t * w⁻¹ * t⁻¹)) * (r * w⁻¹ * r⁻¹) := by
      rw [hvdef, ← hrr]; group
    rw [hcomm] at e1
    have e2 : w * ((t * w⁻¹ * t⁻¹) * (r * w * r⁻¹)) * (r * w⁻¹ * r⁻¹) = w * (t * w⁻¹ * t⁻¹) := by
      group
    rw [e2, hta _ (A.inv_mem hw)] at e1
    calc v * r * v⁻¹ = (v * r * v⁻¹ * r⁻¹) * r := by group
      _ = c * r := by rw [e1, hcdef]; group
  have hvt : v * t = t * v := by
    have e : v * t * v⁻¹ = t := by
      calc v * t * v⁻¹ = (v * r * v⁻¹) * (v * r * v⁻¹) := by rw [← hrr]; group
        _ = (c * r) * (c * r) := by rw [hvr]
        _ = c * (r * c) * r := by group
        _ = c * (c * r) * r := by rw [hrc]
        _ = (c * c) * (r * r) := by group
        _ = t := by rw [hc2, hrr, one_mul]
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [e]
  have hc1 : c = 1 := by
    by_contra hc1
    have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
      CoreAssembly.mem_conjClass_self _
    have hJ : conjSub v (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨v, rfl⟩
    have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
    have huJ : c * r ∈ conjSub v (tightCore R) := by
      rw [← hvr]
      exact conj_mem_conjSub hrK
    have hzK := isUniqueInvolution_core hd
    by_cases hJK : conjSub v (tightCore R) = tightCore R
    ·
      have hcK : c ∈ tightCore R := by
        have := (tightCore R).mul_mem (hJK ▸ huJ) ((tightCore R).inv_mem hrK)
        simpa using this
      have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
      exact htZ (eq_of_orderOf_eq_two hd (tightCore_le R hcK) hord ▸ hcZ)
    · have hzJ : IsUniqueInvolution (conjSub v (tightCore R)) t := by
        have := hzK.conj v
        have hvt' : v * t * v⁻¹ = t := by
          calc v * t * v⁻¹ = t * v * v⁻¹ := by rw [hvt]
            _ = t := by group
        rwa [hvt'] at this
      have hodd := (Disconnected.AschTight.Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ (Ne.symm hJK)
        hzK hzJ)
      obtain ⟨s, hsS, hsr⟩ := exists_inverting hd hq8 hrS hrr
      have hsK : s ∈ tightCore R := mem_core_of_mem_S₀ hd hsS
      have hcomm2 : ⁅s, c * r⁆ ∈ ⁅tightCore R, conjSub v (tightCore R)⁆ :=
        Subgroup.commutator_mem_commutator hsK huJ
      have hsc := hcomN hsS
      have htc : c * t = t * c := by rw [← hrr]; calc c * (r * r) = (c * r) * r := by group
        _ = (r * c) * r := by rw [hrc]
        _ = r * (c * r) := by group
        _ = r * (r * c) := by rw [hrc]
        _ = (r * r) * c := by group
      have hcomval : ⁅s, c * r⁆ = t := by
        rw [commutatorElement_def]
        have e1 : s * (c * r) * s⁻¹ = c * r⁻¹ := by
          calc s * (c * r) * s⁻¹ = (s * c) * (r * s⁻¹) := by group
            _ = (c * s) * (r * s⁻¹) := by rw [hsc]
            _ = c * (s * r * s⁻¹) := by group
            _ = c * r⁻¹ := by rw [hsr]
        have e2 : r⁻¹ * r⁻¹ = t⁻¹ := by rw [← hrr]; group
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (t_mul_t hd)
        calc s * (c * r) * s⁻¹ * (c * r)⁻¹ = (s * (c * r) * s⁻¹) * (r⁻¹ * c⁻¹) := by group
          _ = c * (r⁻¹ * r⁻¹) * c⁻¹ := by rw [e1]; group
          _ = c * t * c⁻¹ := by rw [e2, htinv]
          _ = t := by rw [htc]; group
      rw [hcomval] at hcomm2
      have ht1 : t ∈ oddCoreOf (tightCore R) := (hodd hcomm2).1
      have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
      have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (tightCore R)) ht1 ht2
      have h' := hd.order
      rw [this, orderOf_one] at h'
      norm_num at h'
  calc w * a = c * (a * w) := by rw [hcdef]; group
    _ = a * w := by rw [hc1, one_mul]

end Inner

section ZStar

theorem exists_conj_comm_ne {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {i : G} (hi2 : i * i = 1) (hi1 : i ≠ 1) :
    ∃ g : G, (g * i * g⁻¹) * i = i * (g * i * g⁻¹) ∧ g * i * g⁻¹ ≠ i := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hN, hodd, hNg⟩ := CFSG.ZStar.glauberman_zStar G i hi1 hi2 hcon
  have hcent : ∀ g : G, g * i = i * g := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ _ N hN with h | h
    · intro g
      have := hNg g
      rw [h, Subgroup.mem_bot] at this
      calc g * i = (g * i * g⁻¹ * i⁻¹) * (i * g) := by group
        _ = i * g := by rw [this, one_mul]
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card G := by
        have hord : orderOf i = 2 := orderOf_eq_prime (by rw [pow_two]; exact hi2) hi1
        exact hord ▸ orderOf_dvd_natCard i
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hZ : i ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => hcent g
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hZ
    exact hi1 hZ
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_comm_conj {A : Subgroup Y} (hA : CFSG.IsQuasisimple ↥A) (a : ↥A)
    (hi2 : MulAut.conj a * MulAut.conj a = 1) (hi1 : MulAut.conj a ≠ 1) :
    ∃ g : ↥A, MulAut.conj ((g * a * g⁻¹ * a⁻¹) * a * (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹) = 1 ∧
      MulAut.conj ((g * a * g⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹)) = 1 ∧
      MulAut.conj (g * a * g⁻¹ * a⁻¹) ≠ 1 ∧
      MulAut.conj (g * a * g⁻¹ * a⁻¹) ≠ MulAut.conj a := by
  classical
  have := TightA.inn_isSimpleGroup hA
  have : Finite ↥(TightA.inn A) := inferInstance
  have hnab := TightA.inn_nonabelian hA
  set i : ↥(TightA.inn A) := ⟨MulAut.conj a, a, rfl⟩ with hi
  have hi2' : i * i = 1 := Subtype.ext hi2
  have hi1' : i ≠ 1 := fun h => hi1 (congrArg Subtype.val h)
  obtain ⟨gb, hc, hne⟩ := exists_conj_comm_ne hnab hi2' hi1'
  obtain ⟨g, hg⟩ := gb.2
  refine ⟨g, ?_⟩
  have hc' : (MulAut.conj g * MulAut.conj a * (MulAut.conj g)⁻¹) * MulAut.conj a =
      MulAut.conj a * (MulAut.conj g * MulAut.conj a * (MulAut.conj g)⁻¹) := by
    have := congrArg Subtype.val hc
    simpa [hi, hg] using this
  have hne' : MulAut.conj g * MulAut.conj a * (MulAut.conj g)⁻¹ ≠ MulAut.conj a := by
    intro h
    apply hne
    apply Subtype.ext
    simpa [hi, hg] using h
  set H : MulAut ↥A := MulAut.conj g * MulAut.conj a * (MulAut.conj g)⁻¹ with hH
  set j : MulAut ↥A := MulAut.conj a with hj
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hi2
  have hHH : H * H = 1 := by
    rw [hH]
    calc MulAut.conj g * j * (MulAut.conj g)⁻¹ * (MulAut.conj g * j * (MulAut.conj g)⁻¹)
        = MulAut.conj g * (j * j) * (MulAut.conj g)⁻¹ := by group
      _ = 1 := by rw [hi2]; group
  have hH1 : H ≠ 1 := by
    intro h
    apply hi1
    have : (MulAut.conj g)⁻¹ * H * MulAut.conj g = j := by
      rw [hH]; group
    rw [← this, h]
    group
  have hX : MulAut.conj (g * a * g⁻¹ * a⁻¹) = H * j := by
    have h1 : MulAut.conj (g * a * g⁻¹ * a⁻¹) = H * j⁻¹ := by
      simp only [map_mul, map_inv, hH, hj]
    rw [h1, hjinv]
  have hXc : (H * j) * j = j * (H * j) := by
    calc (H * j) * j = (H * j) * j := rfl
      _ = j * (H * j) := by
        calc H * j * j = j * H * j := by rw [hc']
          _ = j * (H * j) := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (g * a * g⁻¹ * a⁻¹) * a * (g * a * g⁻¹ * a⁻¹)⁻¹ * a⁻¹ =
        ⁅g * a * g⁻¹ * a⁻¹, a⁆ := by rw [commutatorElement_def]
    rw [this, map_commutatorElement, hX, commutatorElement_eq_one_iff_mul_comm]
    exact hXc
  · rw [map_mul, hX]
    calc H * j * (H * j) = H * (j * H) * j := by group
      _ = H * (H * j) * j := by rw [← hc']
      _ = (H * H) * (j * j) := by group
      _ = 1 := by rw [hHH, hi2, one_mul]
  · rw [hX]
    intro h
    apply hne'
    have : H = (H * j) * j⁻¹ := by group
    rw [this, h, one_mul, hjinv]
  · rw [hX]
    intro h
    apply hH1
    have : H = (H * j) * j⁻¹ := by group
    rw [this, h, hjinv, hi2]

end ZStar

namespace Inner

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem commute_center_component (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) {z : Y}
    (hzA : z ∈ A) (hz : ∀ y ∈ A, y * z = z * y) : s * z = z * s := by
  have hcZ : z ∈ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) :=
    TightA.mem_centerLayer_of_mem_center hA hzA hz
  have htZ : t ∉ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) := fun h =>
    hE2 ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup hO, h⟩
  exact commute_of_normal_two hd hΩ TightA.centerLayer_normal (TightA.centerLayer_isPGroup hO) htZ
    hs hcZ

theorem mem_normalizer_core_of_comm (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) {a : Y} (haA : a ∈ A)
    (hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹) {g₁ : Y} (hg₁ : g₁ ∈ A)
    (hxt : (g₁ * a * g₁⁻¹ * a⁻¹) * t = t * (g₁ * a * g₁⁻¹ * a⁻¹)) :
    g₁ * a * g₁⁻¹ * a⁻¹ ∈ Subgroup.normalizer (tightCore R : Set Y) := by
  set x : Y := g₁ * a * g₁⁻¹ * a⁻¹ with hx
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  set g₂ : Y := r * g₁ * r⁻¹ with hg₂
  set h : Y := t * g₁⁻¹ * t⁻¹ with hh
  have hg₂B : g₂ ∈ conjSub r A := conj_mem_conjSub hg₁
  have hhA : h ∈ A := by
    rw [hh, hta _ (A.inv_mem hg₁)]
    exact A.mul_mem (A.mul_mem haA (A.inv_mem hg₁)) (A.inv_mem haA)
  have hcomm : g₂ * h = h * g₂ := comm_of_ne hB hA hrA hg₂B hhA
  set G : Y := g₁ * g₂ with hG
  have hconj : G * r * G⁻¹ = x * r := by
    have e1 : G * r * G⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * r := by
      rw [hG, hg₂, hh, ← hrr]; group
    have e2 : g₂ * h * g₂⁻¹ = h := by rw [hcomm]; group
    rw [e1, e2, hh, hta _ (A.inv_mem hg₁), hx]; group
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub G (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨G, rfl⟩
  have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
  have huJ : x * r ∈ conjSub G (tightCore R) := by
    rw [← hconj]
    exact conj_mem_conjSub hrK
  by_cases hJK : conjSub G (tightCore R) = tightCore R
  · have h1 : x * r ∈ tightCore R := hJK ▸ huJ
    have hx' : x ∈ tightCore R := by
      simpa using (tightCore R).mul_mem h1 ((tightCore R).inv_mem hrK)
    exact Subgroup.le_normalizer hx'
  · have hxrN : x * r ∈ Subgroup.normalizer (tightCore R : Set Y) := by
      refine hΩ.omega5 _ hK _ hJ (Ne.symm hJK) t (isUniqueInvolution_core hd) (x * r) huJ ?_ ?_ ?_
      · intro hall
        obtain ⟨s, hsS, hsr⟩ := exists_noncomm hd hq8 hrS hrr
        have hsK := mem_core_of_mem_S₀ hd hsS
        have hw : G * s * G⁻¹ ∈ conjSub G (tightCore R) := conj_mem_conjSub hsK
        have h2 := hall _ hw
        rw [← hconj] at h2
        apply hsr
        have e : G * (r * s) * G⁻¹ = G * (s * r) * G⁻¹ := by
          calc G * (r * s) * G⁻¹ = (G * r * G⁻¹) * (G * s * G⁻¹) := by group
            _ = (G * s * G⁻¹) * (G * r * G⁻¹) := h2
            _ = G * (s * r) * G⁻¹ := by group
        exact (mul_left_cancel (mul_right_cancel e)).symm
      · have hr2 : IsPGroup 2 ↥(Subgroup.zpowers r) :=
          (hd.sylow_core.2.1).to_le (Subgroup.zpowers_le.mpr hrS)
        rw [← hconj]
        have e : Subgroup.zpowers (G * r * G⁻¹) =
            (Subgroup.zpowers r).map (MulAut.conj G).toMonoidHom := by
          rw [MonoidHom.map_zpowers]
          rfl
        rw [e]
        exact hr2.map _
      · calc x * r * t = x * (r * t) := by group
          _ = x * (t * r) := by rw [mul_t_comm_of_sq hrr]
          _ = (x * t) * r := by group
          _ = (t * x) * r := by rw [hxt]
          _ = t * (x * r) := by group
    have := (Subgroup.normalizer (tightCore R : Set Y)).mul_mem hxrN
      ((Subgroup.normalizer (tightCore R : Set Y)).inv_mem (Subgroup.le_normalizer hrK))
    simpa using this

omit [Finite Y] in
theorem central_of_conj_eq_one {A : Subgroup Y} {c : ↥A} (h : MulAut.conj c = 1) :
    ∀ y ∈ A, (c : Y) * y = y * (c : Y) := by
  intro y hy
  have hc : c ∈ (MulAut.conj : ↥A →* MulAut ↥A).ker := h
  rw [TightA.ker_conj, Subgroup.mem_center_iff] at hc
  exact (congrArg Subtype.val (hc ⟨y, hy⟩)).symm

omit [Finite Y] in
theorem conj_eq_one_of_central {A : Subgroup Y} {c : ↥A}
    (h : ∀ y ∈ A, (c : Y) * y = y * (c : Y)) : MulAut.conj c = 1 := by
  have : c ∈ (MulAut.conj : ↥A →* MulAut ↥A).ker := by
    rw [TightA.ker_conj, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2).symm
  exact this

theorem false_of_inner (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) (hnc : ¬ ∀ x ∈ A, x * t = t * x) : False := by
  classical
  have ht2 : t * t = 1 := t_mul_t hd
  obtain ⟨a, haA, e, he, hae⟩ := exists_inner hd hΩ hA hrS hrA
  have hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹ := by
    intro x hx
    rw [hae, mul_inv_rev]
    calc a * e * x * (e⁻¹ * a⁻¹) = a * (e * x) * e⁻¹ * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [← he x hx]; group
  have ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a) := by
    intro y hy
    have h1 : t * (t * y * t⁻¹) * t⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by
      rw [hta y hy, hta _ (A.mul_mem (A.mul_mem haA hy) (A.inv_mem haA))]
    have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [ht2]; group
    rw [h2] at h1
    calc a * a * y = a * (a * y * a⁻¹) * a⁻¹ * (a * a) := by group
      _ = y * (a * a) := by rw [← h1]
  have hanc : ∃ y ∈ A, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro x hx
    have h1 : t * x * t⁻¹ = x := by rw [hta x hx, hcon x hx]; group
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  set a' : ↥A := ⟨a, haA⟩ with ha'
  have hi2 : MulAut.conj a' * MulAut.conj a' = 1 := by
    rw [← map_mul]
    exact conj_eq_one_of_central fun y hy => ha2 y hy
  have hi1 : MulAut.conj a' ≠ 1 := by
    intro h
    obtain ⟨y, hyA, hay⟩ := hanc
    exact hay (central_of_conj_eq_one h y hyA)
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_comm_conj hA.1 a' hi2 hi1
  set x' : ↥A := g * a' * g⁻¹ * a'⁻¹ with hx'
  set x : Y := (x' : Y) with hx
  have hxA : x ∈ A := x'.2
  have hxdef : x = (g : Y) * a * (g : Y)⁻¹ * a⁻¹ := rfl
  have hxa : x * a = a * x := by
    refine no_twin hd hΩ hq8 hO hE2 hA hrS hrr hrA haA hta ha2 hxA ?_
    exact fun y hy => central_of_conj_eq_one h1 y hy
  have hxt : x * t = t * x := by
    have h5 : t * x * t⁻¹ = x := by rw [hta x hxA, ← hxa]; group
    calc x * t = t * x * t⁻¹ * t := by rw [h5]
      _ = t * x := by group
  have hxN := mem_normalizer_core_of_comm hd hΩ hq8 hA hrS hrr hrA haA hta g.2 (by
    rw [← hxdef]; exact hxt)
  rw [← hxdef] at hxN
  have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
  have hrR : r ∈ R := tightCore_le R hrK
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  set ξ : Y := x * r * x⁻¹ * r⁻¹ with hξ
  have hξR : ξ ∈ R := by
    have h1 : x * r * x⁻¹ ∈ tightCore R := (Subgroup.mem_normalizer_iff.mp hxN r).mp hrK
    exact R.mul_mem (tightCore_le R h1) (R.inv_mem hrR)
  have hacts : ∀ y ∈ A, ξ * y * ξ⁻¹ = x * y * x⁻¹ := by
    intro y hy
    have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hxA)
    have hc := comm_of_ne hB hA hrA hu hy
    calc ξ * y * ξ⁻¹
        = x * ((r * x⁻¹ * r⁻¹) * y) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by rw [hξ]; group
      _ = x * y * x⁻¹ := by rw [hc]; group
  have hc0 : r * (x * x) = (x * x) * r :=
    commute_center_component hd hΩ hO hE2 hA hrS (A.mul_mem hxA hxA)
      fun y hy => (central_of_conj_eq_one h2 y hy).symm
  have hy'x : (r * x⁻¹ * r⁻¹) * x = x * (r * x⁻¹ * r⁻¹) :=
    comm_of_ne hB hA hrA (conj_mem_conjSub (A.inv_mem hxA)) hxA
  have hξξ : ξ * ξ = 1 := by
    have e1 : ξ * ξ = x * ((r * x⁻¹ * r⁻¹) * x) * (r * x⁻¹ * r⁻¹) := by rw [hξ]; group
    have e2 : r * (x * x)⁻¹ * r⁻¹ = (x * x)⁻¹ := by
      have : r * (x * x)⁻¹ = (x * x)⁻¹ * r := (show Commute r (x * x) from hc0).inv_right
      rw [this]; group
    rw [e1, hy'x]
    calc x * (x * (r * x⁻¹ * r⁻¹)) * (r * x⁻¹ * r⁻¹) = (x * x) * (r * (x * x)⁻¹ * r⁻¹) := by group
      _ = 1 := by rw [e2]; group
  by_cases hξ1 : ξ = 1
  · apply h3
    refine conj_eq_one_of_central (c := x') fun y hy => ?_
    have := hacts y hy
    rw [hξ1, inv_one, one_mul, mul_one] at this
    show x * y = y * x
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [← this]
  · have hord : orderOf ξ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hξξ) hξ1
    have hξt : ξ = t := eq_of_orderOf_eq_two hd hξR hord
    apply h4
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have := hacts y y.2
    rw [hξt, hta _ y.2] at this
    simp only [MulAut.conj_apply]
    exact this.symm

end Inner

section Wrappers

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem _root_.CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8TwinDatum.conjSub_component_eq_of_cases
    (hd : Q8TwinDatum R S t) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) (htA : conjSub t A = A)
    (hcent : ∀ r ∈ (S : Subgroup R).map R.subtype, conjSub r A ≠ A →
      (∀ x ∈ A, x * t = t * x) → False)
    {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) : conjSub s A = A := by
  by_contra hsA
  rcases Inner.S₀_cases hd hq8 hs with h | h | h
  · subst h
    exact hsA (conjSub_one A)
  · rw [h] at hsA
    exact hsA htA
  · by_cases hc : ∀ x ∈ A, x * t = t * x
    · exact hcent s hs hsA hc
    · exact Inner.false_of_inner hd hΩ hO hE2 hq8 hA hs h hsA hc

end Wrappers

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
