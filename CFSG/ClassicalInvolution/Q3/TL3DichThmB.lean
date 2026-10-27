module

public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.exists_inner (hd : TightDatum R S t) {A : Subgroup Y}
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
    have h613 := comm613Gen hd.hypOmegaGen hd.S₀_mem_RSet le_sup_left le_sup_right hY'N hbot
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
  have htE : t ∈ E₀ := (Subgroup.mem_inf.mp (hd.mem_of_ne_bot (inf_le_left.trans hd.S₀_le)
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

theorem TightDatum.no_twin (hd : TightDatum R S t) (hO : classicalInvolutionOddCore Y = ⊥)
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
  have hrc : r * c = c * r := hd.commute_of_normal_two TightA.centerLayer_normal
    (TightA.centerLayer_isPGroup hO) htZ hrS hcZ
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
  have hrR : r ∈ R := hd.S₀_le hrS
  have hcrR : c * r ∈ R := by
    rw [← hvr]
    exact (Subgroup.mem_normalizer_iff.mp (hd.mem_normalizer_R_of_comm hvt) r).mp hrR
  have hcR : c ∈ R := by
    have := R.mul_mem hcrR (R.inv_mem hrR)
    simpa using this
  have hc1 : c = 1 := by
    by_contra hc1
    have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
    exact htZ (hd.eq_of_orderOf_eq_two hcR hord ▸ hcZ)
  calc w * a = c * (a * w) := by rw [hcdef]; group
    _ = a * w := by rw [hc1, one_mul]

theorem TightA.isCyclic_of_natCard_le_four {X : Subgroup Y} (h2 : IsPGroup 2 ↥X)
    (h4 : Nat.card ↥X ≤ 4) {z : Y} (hu : ∀ x ∈ X, x * x = 1 → x = 1 ∨ x = z) :
    IsCyclic ↥X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · exact isCyclic_of_orderOf_eq_card (1 : ↥X) (by rw [orderOf_one, hn, pow_zero])
  · exact isCyclic_of_prime_card (p := 2) (by rw [hn, pow_one])
  · by_contra hnc
    have hall : ∀ x : ↥X, (x : Y) * x = 1 := by
      intro x
      have hdvd : orderOf x ∣ 2 ^ 2 := hn ▸ orderOf_dvd_natCard x
      obtain ⟨m, hm, hmx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hm1 : m ≤ 1 := by
        by_contra h
        have hm2 : m = 2 := by omega
        exact hnc (isCyclic_of_orderOf_eq_card x (by rw [hmx, hm2, hn]))
      have h2x : orderOf x ∣ 2 := by
        rw [hmx]
        exact (pow_dvd_pow 2 hm1).trans (by norm_num)
      have : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2x
      rw [pow_two] at this
      exact congrArg Subtype.val this
    have hinj : Function.Injective (fun x : ↥X => decide ((x : Y) = 1)) := by
      intro x y hxy
      by_cases hx : (x : Y) = 1
      · have hy : (y : Y) = 1 := by simpa [hx] using hxy.symm
        exact Subtype.ext (hx.trans hy.symm)
      · have hy : (y : Y) ≠ 1 := by simpa [hx] using hxy.symm
        have hx' := (hu x x.2 (hall x)).resolve_left hx
        have hy' := (hu y y.2 (hall y)).resolve_left hy
        exact Subtype.ext (hx'.trans hy'.symm)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hn] at hle
    omega

theorem TightDatum.false_of_inner (hd : TightDatum R S t) (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) (hnc : ¬ ∀ x ∈ A, x * t = t * x) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := t_mul_t hd
  obtain ⟨a, haA, e, he, hae⟩ := hd.exists_inner hA hrS hrA
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
  have hZ2 := TightA.isPGroup_center_component hO hA
  have htwin : ∀ w ∈ A, (∀ y ∈ A, (w * a * w⁻¹ * a⁻¹) * y = y * (w * a * w⁻¹ * a⁻¹)) →
      w * a = a * w := fun w hw hc =>
    hd.no_twin hO hE2 hA hrS hrr hrA haA hta ha2 hw hc
  set CA : Subgroup Y := A ⊓ Subgroup.centralizer ({t} : Set Y) with hCA
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (P := CA) (T := ⊥) IsPGroup.of_bot bot_le
  have hCAa : CA = A ⊓ Subgroup.centralizer ({a} : Set Y) := by
    ext x
    simp only [hCA, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxt⟩
      refine ⟨hx, ?_⟩
      have h1 : a * x * a⁻¹ = x := by rw [← hta x hx, ← hxt]; group
      calc x * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨hx, hxa⟩
      refine ⟨hx, ?_⟩
      have h1 : t * x * t⁻¹ = x := by rw [hta x hx, ← hxa]; group
      calc x * t = t * x * t⁻¹ * t := by rw [h1]
        _ = t * x := by group
  have hV : IsSylow2In V₀ (A ⊓ Subgroup.centralizer ({a} : Set Y)) := hCAa ▸ hV₀
  have hV0A : V₀ ≤ A := hV₀.1.trans inf_le_left
  have hV0t : ∀ x ∈ V₀, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV₀.1 hx).2
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  set W : Subgroup Y := V₀ ⊔ conjSub r V₀ with hW
  have hVrc : V₀ ≤ Subgroup.normalizer (conjSub r V₀ : Set Y) := by
    intro x hx
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    refine conjSub_eq_of_mem_of_commutes (K := V₀) hx fun u hu v hv => ?_
    exact comm_of_ne hA hAr hrA.symm (hV0A hu) (conjSub_mono hV0A hv)
  have hW2 : IsPGroup 2 ↥W := IsPGroup.to_sup_of_normal_right' hV₀.2.1 (hV₀.2.1.map _) hVrc
  have hrW : conjSub r W = W := by
    have h1 : conjSub r (conjSub r V₀) = V₀ := by
      rw [← conjSub_mul, hrr]
      ext x
      rw [mem_conjSub_iff]
      constructor
      · intro hx
        have : t * (t⁻¹ * x * t) * t⁻¹ ∈ V₀ := by
          have e : t⁻¹ * x * t = t * (t⁻¹ * x * t) * t⁻¹ := by
            have := hV0t _ hx
            calc t⁻¹ * x * t = t⁻¹ * x * t * t * t⁻¹ := by group
              _ = t * (t⁻¹ * x * t) * t⁻¹ := by rw [this]
          rw [← e]
          exact hx
        simpa [mul_assoc] using this
      · intro hx
        have e : t⁻¹ * x * t = x := by
          calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
            _ = x := by rw [hV0t x hx]; group
        rw [e]
        exact hx
    rw [hW, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, sup_comm]
  have hrN : Subgroup.zpowers r ≤ Subgroup.normalizer (W : Set Y) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hrW)
  have hr2 : IsPGroup 2 ↥(Subgroup.zpowers r) :=
    (hd.sylow_core.2.1).to_le (Subgroup.zpowers_le.mpr hrS)
  set P : Subgroup Y := W ⊔ Subgroup.zpowers r with hP
  have hP2 : IsPGroup 2 ↥P := IsPGroup.to_sup_of_normal_left' hW2 hr2 hrN
  set X : Subgroup Y := (P ⊓ R) ⊓ Subgroup.normalizer (A : Set Y) with hX
  have hXle : X ≤ P ⊓ R := inf_le_left
  have hrPR : r ∈ P ⊓ R := ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers r), hd.S₀_le hrS⟩
  have hrX : r ∉ X := fun h => hrA (mem_normalizer_iff_conjSub_eq.mp h.2)
  have hPR8 : Nat.card ↥(P ⊓ R) ≤ 8 := by
    have hsyl := isSylow2In_map_sylow R S
    have h1 := hsyl.natCard_le (hP2.to_le inf_le_left) inf_le_right
    obtain ⟨φ⟩ := hq8
    have h2 : Nat.card ↥((S : Subgroup R).map R.subtype) = 8 := by
      rw [Nat.card_congr ((S : Subgroup R).equivMapOfInjective R.subtype
        R.subtype_injective).toEquiv.symm, Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card,
        QuaternionGroup.card]
    omega
  have hX4 : Nat.card ↥X ≤ 4 := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hXle
    have hpos : 0 < Nat.card ↥(P ⊓ R) := Nat.card_pos
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · exact absurd (Subgroup.eq_of_le_of_card_ge hXle (by rw [hk, mul_one])) fun h =>
            hrX (h ▸ hrPR)
      · exact h
    have : Nat.card ↥X * 2 ≤ Nat.card ↥X * k := Nat.mul_le_mul_left _ hk2
    omega
  have hXcyc : IsCyclic ↥X := TightA.isCyclic_of_natCard_le_four (hP2.to_le (hXle.trans
    inf_le_left)) hX4 (z := t) fun x hx hxx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hd.eq_of_orderOf_eq_two (hXle hx).2
          (orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1))
  have hcov : ∀ x ∈ V₀, ∃ ξ ∈ X, ∀ y ∈ A, ξ * y * ξ⁻¹ = x * y * x⁻¹ := by
    intro x hx
    have hacts : ∀ y ∈ A, x * r * x⁻¹ * r⁻¹ * y * (x * r * x⁻¹ * r⁻¹)⁻¹ = x * y * x⁻¹ := by
      intro y hy
      have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem (hV0A hx))
      have hc := comm_of_ne hAr hA hrA hu hy
      calc x * r * x⁻¹ * r⁻¹ * y * (x * r * x⁻¹ * r⁻¹)⁻¹
          = x * ((r * x⁻¹ * r⁻¹) * y) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hc]; group
    have hxP : x ∈ P := Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
    have hrP : r ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
    refine ⟨x * r * x⁻¹ * r⁻¹, ⟨⟨?_, hd.comm_mem (hV0t x hx) (hd.S₀_le hrS)⟩,
      TightA.mem_normalizer_of_acts (hV0A hx) hacts⟩, hacts⟩
    exact P.mul_mem (P.mul_mem (P.mul_mem hxP hrP) (P.inv_mem hxP)) (P.inv_mem hrP)
  exact TightA.false_of_cyclic_cover hA.1 hZ2 haA hanc ha2 htwin hV hXcyc hcov

theorem TightDatum.conjSub_component_eq (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) :
    conjSub s A = A := by
  by_contra hsA
  have htA := hd.conjSub_t_eq hq8 hA
  rcases hd.S₀_cases hq8 hs with h | h | h
  · subst h
    exact hsA (conjSub_one A)
  · rw [h] at hsA
    exact hsA htA
  · by_cases hc : ∀ x ∈ A, x * t = t * x
    · exact hd.not_centralizes hA hs hsA hc
    · exact hd.false_of_inner hO hE2 hq8 hA hs h hsA hc

end CFSG.ClassicalInvolution.Q3
