module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinTwo
public import CFSG.RankThree.PartOne.TCX.Plane
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Proving Subgroup
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped commutatorElement

section Extraspecial

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mul_right_of_comm {c e₀ e : G} (h : ⁅c, e⁆ * e₀ = e₀ * ⁅c, e⁆) :
    ⁅c, e₀ * e⁆ = ⁅c, e₀⁆ * ⁅c, e⁆ := by
  have h' : e₀ * ⁅c, e⁆ * e₀⁻¹ = ⁅c, e⁆ := by rw [← h]; group
  calc ⁅c, e₀ * e⁆ = c * e₀ * c⁻¹ * e₀⁻¹ * (e₀ * ⁅c, e⁆ * e₀⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅c, e₀⁆ * ⁅c, e⁆ := by rw [h']; simp only [commutatorElement_def]

theorem comm_of_comm_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsPGroup 2 E) (hcen : ∀ x ∈ E, ∀ y ∈ E, ∀ e ∈ E, ⁅x, y⁆ * e = e * ⁅x, y⁆)
    (huniq : ∀ x ∈ E, ∀ y ∈ E, ∀ x' ∈ E, ∀ y' ∈ E, ⁅x, y⁆ ≠ 1 → ⁅x', y'⁆ ≠ 1 →
      ⁅x, y⁆ = ⁅x', y'⁆)
    {s : G} (hs : s ^ p = 1) (hsE : ∀ e ∈ E, s * e * s⁻¹ ∈ E) {c : G} (hcE : c ∈ E)
    (hcs : c * s = s * c) (hc : ∀ e ∈ E, e * s = s * e → c * e = e * c) :
    ∀ e ∈ E, c * e = e * c := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  push Not at hne
  obtain ⟨e₀, he₀E, he₀⟩ := hne
  have he₀1 : ⁅c, e₀⁆ ≠ 1 := fun h => he₀ ((commutatorElement_eq_one_iff_mul_comm).1 h)
  set X : Set G := {e | e ∈ E ∧ ⁅c, e⁆ ≠ 1} with hX
  set K : Subgroup G := E ⊓ Subgroup.centralizer ({c} : Set G) with hK
  have hmemK : ∀ e, e ∈ K ↔ e ∈ E ∧ ⁅c, e⁆ = 1 := by
    intro e
    rw [hK, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  have himage : X = (fun e => e₀ * e) '' (K : Set G) := by
    ext x
    constructor
    · rintro ⟨hxE, hx1⟩
      refine ⟨e₀⁻¹ * x, (hmemK _).2 ⟨E.mul_mem (E.inv_mem he₀E) hxE, ?_⟩, by group⟩
      have h1 := commutatorElement_mul_right_of_comm (e₀ := e₀) (e := e₀⁻¹ * x)
        (hcen c hcE _ (E.mul_mem (E.inv_mem he₀E) hxE) e₀ he₀E)
      rw [show e₀ * (e₀⁻¹ * x) = x by group, huniq c hcE x hxE c hcE e₀ he₀E hx1 he₀1] at h1
      have h2 := congrArg (fun t => ⁅c, e₀⁆⁻¹ * t) h1
      simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
      exact h2.symm
    · rintro ⟨e, he, rfl⟩
      obtain ⟨heE, he1⟩ := (hmemK e).1 he
      refine ⟨E.mul_mem he₀E heE, ?_⟩
      rw [commutatorElement_mul_right_of_comm (hcen c hcE e heE e₀ he₀E), he1, mul_one]
      exact he₀1
  have hXcard : X.ncard = Nat.card K := by
    rw [himage, Set.ncard_image_of_injective _ (mul_right_injective e₀),
      ← Nat.card_coe_set_eq]
    rfl
  have hKp : IsPGroup 2 K := hE.to_le inf_le_left
  obtain ⟨k, hk⟩ := hKp.exists_card_eq
  have hpX : ¬ p ∣ X.ncard := by
    rw [hXcard, hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    exact hp2 this
  have hconjX : ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
    rintro x ⟨hxE, hx1⟩
    refine ⟨hsE x hxE, ?_⟩
    have hsc : s⁻¹ * c * s = c := by
      calc s⁻¹ * c * s = s⁻¹ * (c * s) := by group
        _ = s⁻¹ * (s * c) := by rw [hcs]
        _ = c := by group
    have : ⁅c, s * x * s⁻¹⁆ = s * ⁅c, x⁆ * s⁻¹ := by
      calc ⁅c, s * x * s⁻¹⁆ = s * ⁅s⁻¹ * c * s, x⁆ * s⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = s * ⁅c, x⁆ * s⁻¹ := by rw [hsc]
    rw [this]
    intro h
    apply hx1
    calc ⁅c, x⁆ = s⁻¹ * (s * ⁅c, x⁆ * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  have : Fintype ↥X := Fintype.ofFinite _
  let f : ↥X → ↥X := fun x => ⟨s * x * s⁻¹, hconjX x x.2⟩
  have hfp : ∀ (n : ℕ) (x : ↥X), (f^[n] x).1 = s ^ n * x.1 * (s ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show s * (f^[n] x).1 * s⁻¹ = _
      rw [ih]
      group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥X) (f := (f : Function.End ↥X)) (p := p)
    (n := 1) (by
      rw [pow_one]
      funext x
      show f^[p] x = x
      apply Subtype.ext
      rw [hfp, hs]
      group)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hmod
  have hfix : (Function.fixedPoints (f : Function.End ↥X)).Nonempty := by
    by_contra hemp
    have hz : Nat.card (Function.fixedPoints (f : Function.End ↥X)) = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨x, hx⟩ => hemp ⟨x, hx⟩⟩
    rw [hz] at hmod
    exact hpX ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨x, hxE, hx1⟩, hxfix⟩ := hfix
  have hxs : s * x * s⁻¹ = x := congrArg Subtype.val hxfix
  have hxs' : x * s = s * x := by
    calc x * s = (s * x * s⁻¹) * s := by rw [hxs]
      _ = s * x := by group
  exact hx1 ((commutatorElement_eq_one_iff_mul_comm).2 (hc x hxE hxs'))

end Extraspecial

section TwoB

variable {G : Type} [Group G]

@[expose] noncomputable def twoCoreIn (v : G) : Subgroup G :=
  (CFSG.pCore 2 ↥(cent v)).map (cent v).subtype

theorem isPGroup_twoCoreIn (v : G) : IsPGroup 2 ↥(twoCoreIn v) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(cent v))).map _

theorem mem_cent_of_mem_twoCoreIn {v x : G} (hx : x ∈ twoCoreIn v) : x ∈ cent v := by
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact y.2

theorem mem_twoCoreIn_self {v : G} (hv : orderOf v = 2) : v ∈ twoCoreIn v := by
  have hvC : v ∈ cent v := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set v' : ↥(cent v) := ⟨v, hvC⟩ with hv'
  have hnorm : (Subgroup.zpowers v').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * v' = v' * g := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.1 g.2)
    rw [show g * v' ^ k * g⁻¹ = v' ^ k by
      rw [(Commute.zpow_right (show Commute g v' from hc) k).eq]; group]
    exact Subgroup.zpow_mem_zpowers v' k
  have hp : IsPGroup 2 ↥(Subgroup.zpowers v') :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one, hv', Subgroup.orderOf_mk, hv])
  have hle : Subgroup.zpowers v' ≤ CFSG.pCore 2 ↥(cent v) :=
    le_sSup (show Subgroup.zpowers v' ∈ {K : Subgroup ↥(cent v) | K.Normal ∧ IsPGroup 2 K} from
      ⟨hnorm, hp⟩)
  exact ⟨v', hle (Subgroup.mem_zpowers v'), rfl⟩

theorem twoCoreIn_facts [Finite G] {v : G}
    (hext : IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(cent v))) :
    (∀ x ∈ twoCoreIn v, ∀ y ∈ twoCoreIn v, ∀ e ∈ twoCoreIn v, ⁅x, y⁆ * e = e * ⁅x, y⁆) ∧
    (∀ x ∈ twoCoreIn v, ∀ y ∈ twoCoreIn v, ⁅x, y⁆ ∈ twoCoreIn v) ∧
    (∀ a ∈ twoCoreIn v, ∀ b ∈ twoCoreIn v, (∀ e ∈ twoCoreIn v, a * e = e * a) →
      (∀ e ∈ twoCoreIn v, b * e = e * b) → a ≠ 1 → b ≠ 1 → a = b) := by
  obtain ⟨-, hcomm, -, hZ⟩ := hext
  set P := CFSG.pCore 2 ↥(cent v) with hP
  have hlift : ∀ x ∈ twoCoreIn v, ∃ x' : ↥P, ((x' : ↥(cent v)) : G) = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcenter : ∀ x' y' : ↥P, ⁅x', y'⁆ ∈ Subgroup.center ↥P := by
    intro x' y'
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x') (Subgroup.mem_top y')
  have hval : ∀ x' : ↥P, ((x' : ↥(cent v)) : G) ∈ twoCoreIn v := fun x' =>
    ⟨x', x'.2, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy e he
    obtain ⟨x', rfl⟩ := hlift x hx
    obtain ⟨y', rfl⟩ := hlift y hy
    obtain ⟨e', rfl⟩ := hlift e he
    have h := Subgroup.mem_center_iff.1 (hcenter x' y') e'
    have h2 := congrArg (fun t : ↥P => ((t : ↥(cent v)) : G)) h
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    exact h2.symm
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := hlift x hx
    obtain ⟨y', rfl⟩ := hlift y hy
    have := hval ⁅x', y'⁆
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
    exact this
  · intro a ha b hb hac hbc ha1 hb1
    obtain ⟨a', rfl⟩ := hlift a ha
    obtain ⟨b', rfl⟩ := hlift b hb
    have hcen : ∀ c' : ↥P, (∀ e ∈ twoCoreIn v, ((c' : ↥(cent v)) : G) * e = e * c') →
        c' ∈ Subgroup.center ↥P := by
      intro c' hc'
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      apply Subtype.ext
      exact (hc' _ (hval g)).symm
    have ha' : (⟨a', hcen a' hac⟩ : ↥(Subgroup.center ↥P)) ≠ 1 := by
      intro h
      apply ha1
      have := congrArg (fun t : ↥(Subgroup.center ↥P) => (((t : ↥P) : ↥(cent v)) : G)) h
      simpa using this
    have hb' : (⟨b', hcen b' hbc⟩ : ↥(Subgroup.center ↥P)) ≠ 1 := by
      intro h
      apply hb1
      have := congrArg (fun t : ↥(Subgroup.center ↥P) => (((t : ↥P) : ↥(cent v)) : G)) h
      simpa using this
    have := eq_of_ne_one_of_card_le_two (le_of_eq hZ) ha' hb'
    have h2 := congrArg (fun t : ↥(Subgroup.center ↥P) => (((t : ↥P) : ↥(cent v)) : G)) this
    simpa using h2

variable [Finite G]

theorem eq_one_of_mem_twoB {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1) {s v r : G}
    (hs : orderOf s = p) (hv : orderOf v = 2) (hvs : v * s = s * v) (hB : IsTwoBCentralizer v)
    (hrs : r * s = s * r) (hr : orderOf r = p) (hvr : v * r * v⁻¹ = r⁻¹) :
    ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)), q * v = v * q → q = 1 := by
  obtain ⟨hext, hcardR, -, ⟨e⟩, -⟩ := hB
  have hN : Nat.Coprime p (Nat.card ↥(CFSG.pCore 2 ↥(cent v))) := by
    rw [hcardR]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set G) := GLAPPrimeCoreOf_le _
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp _
  have hsH : s ∈ cent v := Subgroup.mem_centralizer_singleton_iff.2 hvs.symm
  have key := @mem_of_oPrimeCoreTrivial_quotient G _ _ p hp (cent v)
    (CFSG.pCore 2 ↥(cent v)) _ hN CFSG.Blueprint.NativeSporadic.Co1 Units.instGroup e hCo s hsH hs
    (Q ⊓ cent v) inf_le_right
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hQC hy.1))
    (fun g hg hgs y hy => ⟨GLAPPrimeCoreOf_conj_mem g
      (Subgroup.mem_centralizer_singleton_iff.2 hgs) y hy.1, by
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hg
        have h2 := Subgroup.mem_centralizer_singleton_iff.1 hy.2
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc g * y * g⁻¹ * v = g * y * (g⁻¹ * v) := by group
          _ = g * y * (v * g⁻¹) := by
            rw [(Commute.inv_left (show Commute g v from h1)).eq]
          _ = g * (y * v) * g⁻¹ := by group
          _ = g * (v * y) * g⁻¹ := by rw [h2]
          _ = (g * v) * y * g⁻¹ := by group
          _ = v * (g * y * g⁻¹) := by rw [h1]; group⟩)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
  set E := twoCoreIn v with hE
  have hYE : ∀ y ∈ Q ⊓ cent v, y ∈ E := fun y hy => ⟨⟨y, hy.2⟩, key y hy, rfl⟩
  obtain ⟨hcen, -, huniq⟩ := twoCoreIn_facts hext
  have hEp := isPGroup_twoCoreIn v
  have hvE : v ∈ E := mem_twoCoreIn_self hv
  have hvZ : ∀ x ∈ E, v * x = x * v := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (mem_cent_of_mem_twoCoreIn hx)).symm
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv; omega
  have hsE : ∀ x ∈ E, s * x * s⁻¹ ∈ E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hn := (CFSG.pCore_normal (p := 2) (G := ↥(cent v))).conj_mem y hy ⟨s, hsH⟩
    exact ⟨_, hn, rfl⟩
  have hs7 : s ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  set K : Subgroup G := E ⊓ Subgroup.centralizer ({s} : Set G) with hKdef
  set Y : Subgroup G := Q ⊓ cent v with hYdef
  have hYK : Y ≤ K := fun y hy => ⟨hYE y hy, hQC hy.1⟩
  have hKp : IsPGroup 2 ↥K := hEp.to_le inf_le_left
  intro q hq hqv
  by_contra hq1
  have hqY : q ∈ Y := ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqv⟩
  have : Group.IsNilpotent ↥K := hKp.isNilpotent
  have hYn : (Y.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnQ, hnv⟩ := hn
    have hgs : (g : G) ∈ Subgroup.centralizer ({s} : Set G) := g.2.2
    have hgv : (g : G) ∈ cent v := mem_cent_of_mem_twoCoreIn g.2.1
    refine ⟨?_, ?_⟩
    · simpa using GLAPPrimeCoreOf_conj_mem (g : G) hgs (n : G) hnQ
    · have h1 := Subgroup.mem_centralizer_singleton_iff.1 hgv
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hnv
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : G) * n * (g : G)⁻¹ * v = g * n * ((g : G)⁻¹ * v) := by group
        _ = g * n * (v * (g : G)⁻¹) := by
          rw [(Commute.inv_left (show Commute (g : G) v from h1)).eq]
        _ = g * (n * v) * (g : G)⁻¹ := by group
        _ = g * (v * n) * (g : G)⁻¹ := by rw [h2]
        _ = (g * v) * n * (g : G)⁻¹ := by group
        _ = v * (g * n * (g : G)⁻¹) := by rw [h1]; group
  have hYne : Y.subgroupOf K ≠ ⊥ := by
    intro h
    have : (⟨q, hYK hqY⟩ : ↥K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.2 hqY
    rw [h, Subgroup.mem_bot] at this
    exact hq1 (congrArg Subtype.val this)
  have hint := Group.IsNilpotent.inf_center_ne_bot_of_normal hYne
  obtain ⟨c0, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hint
  set c : ↥K := (c0 : ↥K) with hcdef
  obtain ⟨hcY, hcZ⟩ := Subgroup.mem_inf.1 c0.2
  have hcY' : ((c : ↥K) : G) ∈ Y := Subgroup.mem_subgroupOf.1 hcY
  have hcK : ((c : ↥K) : G) ∈ K := (c : ↥K).2
  have hc1' : ((c : ↥K) : G) ≠ 1 := by
    intro h
    apply hc1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hcE := comm_of_comm_fixed hp hp2 hEp (fun x hx y hy e he => hcen x hx y hy e he)
    (fun x hx y hy x' hx' y' hy' h1 h2 => huniq ⁅x, y⁆ ((twoCoreIn_facts hext).2.1 x hx y hy)
      ⁅x', y'⁆ ((twoCoreIn_facts hext).2.1 x' hx' y' hy')
      (fun e he => hcen x hx y hy e he) (fun e he => hcen x' hx' y' hy' e he) h1 h2)
    hs7 hsE hcK.1
    ((Subgroup.mem_centralizer_singleton_iff.1 hcK.2))
    (fun e he hes => by
      have hek : e ∈ K := ⟨he, Subgroup.mem_centralizer_singleton_iff.2 hes⟩
      have := Subgroup.mem_center_iff.1 hcZ ⟨e, hek⟩
      have h2 := congrArg (fun t : ↥K => (t : G)) this
      simpa using h2.symm)
  have hcv : ((c : ↥K) : G) = v :=
    huniq _ hcK.1 v hvE hcE hvZ hc1' hv1
  have hvQ : v ∈ Q := hcv ▸ hcY'.1
  have hrC : r ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hrs
  have hrv : r * v * r⁻¹ ∈ Q := GLAPPrimeCoreOf_conj_mem r hrC v hvQ
  have hr2 : (r ^ 2)⁻¹ ∈ Q := by
    have h := Q.mul_mem hvQ (Q.inv_mem hrv)
    have he : v * (r * v * r⁻¹)⁻¹ = (r ^ 2)⁻¹ := by
      calc v * (r * v * r⁻¹)⁻¹ = (v * r * v⁻¹) * r⁻¹ := by group
        _ = (r ^ 2)⁻¹ := by rw [hvr]; group
    rwa [he] at h
  have hord : orderOf (r ^ 2)⁻¹ = p := by
    have hg : Nat.gcd p 2 = 1 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    rw [orderOf_inv, orderOf_pow' r (by norm_num : (2 : ℕ) ≠ 0), hr, hg, Nat.div_one]
  have hdvd : orderOf (⟨(r ^ 2)⁻¹, hr2⟩ : ↥Q) ∣ Nat.card ↥Q := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem eq_one_of_twoB_sylow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCoP : ∀ P : Subgroup CFSG.Blueprint.NativeSporadic.Co1, Nat.card P = p ^ 2 →
      IsPGroup p ↥(Subgroup.centralizer (P : Set CFSG.Blueprint.NativeSporadic.Co1)))
    {w f₁ f₂ x : G} (hB : IsTwoBCentralizer w) (hf₁ : orderOf f₁ = p) (hf₂ : orderOf f₂ = p)
    (hf₁₂ : f₁ * f₂ = f₂ * f₁) (hind : f₂ ∉ Subgroup.zpowers f₁)
    (hwf₁ : f₁ * w = w * f₁) (hwf₂ : f₂ * w = w * f₂)
    (hxw : x * w = w * x) (hx₁ : x * f₁ = f₁ * x) (hx₂ : x * f₂ = f₂ * x)
    (hxp : Nat.Coprime p (orderOf x)) (hx2 : Odd (orderOf x)) : x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcardR, -, ⟨e⟩, -⟩ := hB
  set H := cent w with hH
  set N := CFSG.pCore 2 ↥H with hN
  let φ : ↥H →* CFSG.Blueprint.NativeSporadic.Co1 :=
    (@MulEquiv.toMonoidHom _ _ _ Units.instGroup.toMulOneClass e).comp (QuotientGroup.mk' N)
  have hker : φ.ker = N := by
    ext y
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' N y) = 1 ↔ y ∈ N
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff y
  set f₁' : ↥H := ⟨f₁, Subgroup.mem_centralizer_singleton_iff.2 hwf₁⟩
  set f₂' : ↥H := ⟨f₂, Subgroup.mem_centralizer_singleton_iff.2 hwf₂⟩
  set x' : ↥H := ⟨x, Subgroup.mem_centralizer_singleton_iff.2 hxw⟩
  set F := Subgroup.closure ({f₁', f₂'} : Set ↥H) with hF
  have hFc : Nat.card F = p ^ 2 := by
    refine CFSG.RankThree.PartOne.TCX.card_closure_pair hp (show Commute f₁' f₂' from
      Subtype.ext hf₁₂) (by rw [Subgroup.orderOf_mk, hf₁]) (by rw [Subgroup.orderOf_mk, hf₂]) ?_
    intro h
    apply hind
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hFp : IsPGroup p F := IsPGroup.of_card hFc
  have hNp : IsPGroup 2 N := CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have hFN : F ⊓ N = ⊥ := by
    rw [hN] at hNp
    have hcop : Nat.Coprime 2 (Nat.card F) := by
      rw [hFc]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    exact inf_eq_bot_of_coprime_isPGroup Nat.prime_two hcop hNp
  have hinj : ∀ y₁ y₂ : ↥F, φ y₁ = φ y₂ → y₁ = y₂ := by
    intro y₁ y₂ h
    have hmem : (y₁ : ↥H)⁻¹ * y₂ ∈ F ⊓ N := by
      refine ⟨F.mul_mem (F.inv_mem y₁.2) y₂.2, ?_⟩
      have : (y₁ : ↥H)⁻¹ * y₂ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      rwa [hker] at this
    rw [hFN, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hFmap : Nat.card (F.map φ) = p ^ 2 := by
    rw [← hFc]
    refine (Nat.card_congr (Equiv.ofBijective (fun y : ↥F => (⟨φ y, Subgroup.mem_map_of_mem φ y.2⟩ :
      ↥(F.map φ))) ⟨fun y₁ y₂ h => hinj y₁ y₂ (congrArg Subtype.val h), ?_⟩)).symm
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hxF : ∀ y ∈ F, y * x' = x' * y := by
    have hle : F ≤ Subgroup.centralizer ({x'} : Set ↥H) := by
      rw [hF, Subgroup.closure_le]
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | rfl
      · exact Subtype.ext hx₁.symm
      · exact Subtype.ext hx₂.symm
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
  have hmem : φ x' ∈ Subgroup.centralizer ((F.map φ : Subgroup _) :
      Set CFSG.Blueprint.NativeSporadic.Co1) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hxF y hy]
  obtain ⟨k, hk⟩ := hCoP (F.map φ) hFmap ⟨φ x', hmem⟩
  have hk' : (φ x') ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hox : orderOf x' = orderOf x := Subgroup.orderOf_mk _ _
  have hk2 : (φ x') ^ (orderOf x) = 1 := by rw [← map_pow, ← hox, pow_orderOf_eq_one, map_one]
  have hφx : φ x' = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    have h2 := orderOf_dvd_of_pow_eq_one hk2
    have hc : Nat.Coprime (p ^ k) (orderOf x) := Nat.Coprime.pow_left k hxp
    rw [← orderOf_eq_one_iff]
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
  have hx'N : x' ∈ N := by rw [← hker]; exact hφx
  obtain ⟨m, hm⟩ := hNp ⟨x', hx'N⟩
  have hm' : x ^ (2 ^ m) = 1 := by
    have := congrArg (fun t : ↥N => (((t : ↥H)) : G)) hm
    simpa using this
  have hd := orderOf_dvd_of_pow_eq_one hm'
  have hodd : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.2 hx2
  have h1 : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left m hodd))
      dvd_rfl
  exact orderOf_eq_one_iff.1 h1

theorem gLAPPrimeCoreOf_eq_bot_of_twoB_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1) {s a b : G}
    (hs : orderOf s = p) (has : a * s = s * a) (hbs : b * s = s * b)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab2 : orderOf (a * b) = 2)
    (hA : IsTwoBCentralizer a) (hB : IsTwoBCentralizer b) (hAB : IsTwoBCentralizer (a * b))
    {ra rb rab : G} (hras : ra * s = s * ra) (hra : orderOf ra = p) (hrai : a * ra * a⁻¹ = ra⁻¹)
    (hrbs : rb * s = s * rb) (hrb : orderOf rb = p) (hrbi : b * rb * b⁻¹ = rb⁻¹)
    (hrabs : rab * s = s * rab) (hrab : orderOf rab = p)
    (hrabi : (a * b) * rab * (a * b)⁻¹ = rab⁻¹) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have haC : a ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 has
  have hbC : b ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hbs
  have habs : a * b * s = s * (a * b) := by
    calc a * b * s = a * (b * s) := by group
      _ = a * (s * b) := by rw [hbs]
      _ = (a * s) * b := by group
      _ = s * a * b := by rw [has]
      _ = s * (a * b) := by group
  have hsq : ∀ t : G, orderOf t = 2 → t * t = 1 := fun t ht => by
    rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hfix : ∀ t : G, orderOf t = 2 → t * s = s * t → IsTwoBCentralizer t → ∀ r : G,
      r * s = s * r → orderOf r = p → t * r * t⁻¹ = r⁻¹ → ∀ x ∈ Q, t * x * t⁻¹ = x → x = 1 := by
    intro t ht hts hT r hrs hr htr x hx hxt
    refine eq_one_of_mem_twoB hp hp2 hCo hs ht hts hT hrs hr htr x hx ?_
    calc x * t = (t * x * t⁻¹) * t := by rw [hxt]
      _ = t * x := by group
  have hext := eq_one_of_klein_fixedPointFree (hsq a ha) (hsq b hb) (Q := Q)
    (fun x hx => GLAPPrimeCoreOf_conj_mem a haC x hx)
    (fun x hx => GLAPPrimeCoreOf_conj_mem b hbC x hx)
    (hfix a ha has hA ra hras hra hrai) (hfix b hb hbs hB rb hrbs hrb hrbi)
    (hfix (a * b) hab2 habs hAB rab hrabs hrab hrabi)
  exact (Subgroup.eq_bot_iff_forall _).2 hext

@[expose] def zConjClosure (y z : G) : Subgroup G :=
  Subgroup.closure (insert y {x | ∃ g ∈ Subgroup.centralizer ({y} : Set G), x = z * (g * z * g⁻¹)})

omit [Finite G] in
theorem mem_zConjClosure_of_inv {y z h : G} {k : ℕ} (hz : z * z = 1) (hhy : h * y = y * h)
    (hzh : z * h * z⁻¹ = h⁻¹) (hh : h ^ (2 * k + 1) = 1) : h ∈ zConjClosure y z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hg : h ^ k ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.pow_mem _ (Subgroup.mem_centralizer_singleton_iff.2 hhy) k
  refine Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨h ^ k, hg, ?_⟩)
  have h1 : z * h ^ k * z⁻¹ = (h ^ k)⁻¹ := by rw [← conj_pow, hzh, inv_pow]
  rw [hzinv] at h1
  have h2 : h = (h ^ k)⁻¹ * (h ^ k)⁻¹ := by
    rw [← mul_inv_rev, ← pow_add, eq_inv_iff_mul_eq_one, ← pow_succ']
    rw [show k + k + 1 = 2 * k + 1 by ring]
    exact hh
  calc h = (h ^ k)⁻¹ * (h ^ k)⁻¹ := h2
    _ = (z * h ^ k * z) * (h ^ k)⁻¹ := by rw [h1]
    _ = z * (h ^ k * z * (h ^ k)⁻¹) := by group

theorem gLAPPrimeCoreOf_eq_bot_of_twoB_dihedral {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1)
    (hCoP : ∀ P : Subgroup CFSG.Blueprint.NativeSporadic.Co1, Nat.card P = p ^ 2 →
      IsPGroup p ↥(Subgroup.centralizer (P : Set CFSG.Blueprint.NativeSporadic.Co1)))
    {y z w r : G} (hy : orderOf y = p) (hz : orderOf z = 2) (hzy : z * y = y * z)
    (hZ : IsTwoBCentralizer z) (hry : r * y = y * r) (hr : orderOf r = p)
    (hzr : z * r * z⁻¹ = r⁻¹) (hw : orderOf w = 2) (hwy : w * y * w⁻¹ = y⁻¹)
    (hW : IsTwoBCentralizer w) (hZW : IsTwoBCentralizer (z * w))
    {f₁ f₂ f₃ f₄ : G} (hf₁ : f₁ ∈ zConjClosure y z) (hf₂ : f₂ ∈ zConjClosure y z)
    (hf₃ : f₃ ∈ zConjClosure y z) (hf₄ : f₄ ∈ zConjClosure y z)
    (ho₁ : orderOf f₁ = p) (ho₂ : orderOf f₂ = p) (ho₃ : orderOf f₃ = p) (ho₄ : orderOf f₄ = p)
    (hc₁₂ : f₁ * f₂ = f₂ * f₁) (hc₃₄ : f₃ * f₄ = f₄ * f₃)
    (hi₁₂ : f₂ ∉ Subgroup.zpowers f₁) (hi₃₄ : f₄ ∉ Subgroup.zpowers f₃)
    (hw₁ : f₁ * w = w * f₁) (hw₂ : f₂ * w = w * f₂)
    (hw₃ : f₃ * (z * w) = (z * w) * f₃) (hw₄ : f₄ * (z * w) = (z * w) * f₄) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) with hQ
  have hsq : ∀ t : G, orderOf t = 2 → t * t = 1 := fun t ht => by
    rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hzC : z ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hzy
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp _
  have hfz : ∀ x ∈ Q, z * x * z⁻¹ = x → x = 1 := by
    intro x hx hxz
    refine eq_one_of_mem_twoB hp hp2 hCo hy hz hzy hZ hry hr hzr x hx ?_
    calc x * z = (z * x * z⁻¹) * z := by rw [hxz]
      _ = z * x := by group
  have hzQ : ∀ x ∈ Q, z * x * z⁻¹ ∈ Q := fun x hx => GLAPPrimeCoreOf_conj_mem z hzC x hx
  have hinv := inv_of_fixedPointFree_involution (hsq z hz) hzQ hfz
  have hcl : zConjClosure y z ≤ Subgroup.centralizer (Q : Set G) := by
    rw [zConjClosure, Subgroup.closure_le]
    rintro _ (rfl | ⟨g, hg, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ hq)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := GLAPPrimeCoreOf_conj_mem g⁻¹ (Subgroup.inv_mem _ hg) q hq
      simpa using this
    have h1 : z * (g⁻¹ * q * g) * z⁻¹ = (g⁻¹ * q * g)⁻¹ := hinv _ hq'
    have h2 : z * q * z⁻¹ = q⁻¹ := hinv q hq
    have h3 : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ = q⁻¹ := by
      calc (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ = g * (z * (g⁻¹ * q * g) * z⁻¹) * g⁻¹ := by group
        _ = q⁻¹ := by rw [h1]; group
    set u := g * z * g⁻¹ with hu
    have h4 : (z * u) * q * (z * u)⁻¹ = q := by
      calc (z * u) * q * (z * u)⁻¹ = z * (u * q * u⁻¹) * z⁻¹ := by group
        _ = z * q⁻¹ * z⁻¹ := by rw [h3]
        _ = (z * q * z⁻¹)⁻¹ := by group
        _ = q := by rw [h2, inv_inv]
    calc q * (z * u) = ((z * u) * q * (z * u)⁻¹) * (z * u) := by rw [h4]
      _ = (z * u) * q := by group
  have hwQ : ∀ x ∈ Q, w * x * w⁻¹ ∈ Q := by
    set ψ := (MulAut.conj w).toMonoidHom with hψ
    have hψi : Function.Injective ψ := (MulAut.conj w).injective
    have hmap := map_glaPPrimeCoreOf_of_injective p ψ hψi (Subgroup.centralizer ({y} : Set G))
    have hc := map_inf_centralizer_of_injective ψ hψi ⊤ y
    rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj w).surjective, top_inf_eq] at hc
    have hψy : ψ y = y⁻¹ := by
      rw [hψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwy]
    have hCinv : Subgroup.centralizer ({y⁻¹} : Set G) = Subgroup.centralizer ({y} : Set G) := by
      ext g
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc g * y = y * (y⁻¹ * g) * y := by group
          _ = y * (g * y⁻¹) * y := by rw [h]
          _ = y * g := by group
      · intro h
        calc g * y⁻¹ = y⁻¹ * (y * g) * y⁻¹ := by group
          _ = y⁻¹ * (g * y) * y⁻¹ := by rw [← h]
          _ = y⁻¹ * g := by group
    rw [hc, hψy, hCinv] at hmap
    intro x hx
    have : ψ x ∈ (GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G))).map ψ :=
      Subgroup.mem_map_of_mem ψ hx
    rw [hmap] at this
    simpa [hψ, MulAut.conj_apply] using this
  have hoddQ : ∀ x ∈ Q, Odd (orderOf x) := by
    intro x hx
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ orderOf x := by omega
    obtain ⟨k, hk⟩ := h2'
    set u := x ^ k with hu
    have huQ : u ∈ Q := Q.pow_mem hx k
    have hu2 : u * u = 1 := by
      rw [hu, ← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one (show x ^ k = 1 from h)
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk
          exact absurd hk (orderOf_pos x).ne'
        · exact h0
      have := Nat.le_of_dvd hk0 this
      omega
    apply hu1
    refine hfz u huQ ?_
    have := hinv u huQ
    rw [this]
    exact inv_eq_of_mul_eq_one_right hu2
  have hpQ : ∀ x ∈ Q, Nat.Coprime p (orderOf x) := by
    intro x hx
    have hd : orderOf (⟨x, hx⟩ : ↥Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Nat.Coprime.coprime_dvd_right hd hcop
  have hfw : ∀ x ∈ Q, w * x * w⁻¹ = x → x = 1 := by
    intro x hx hxw
    have hxw' : x * w = w * x := by
      calc x * w = (w * x * w⁻¹) * w := by rw [hxw]
        _ = w * x := by group
    have hxf : ∀ f ∈ zConjClosure y z, x * f = f * x := fun f hf =>
      (Subgroup.mem_centralizer_iff.1 (hcl hf)) x hx
    exact eq_one_of_twoB_sylow hp hp2 hCoP hW ho₁ ho₂ hc₁₂ hi₁₂ hw₁ hw₂ hxw' (hxf f₁ hf₁)
      (hxf f₂ hf₂) (hpQ x hx) (hoddQ x hx)
  have hfzw : ∀ x ∈ Q, (z * w) * x * (z * w)⁻¹ = x → x = 1 := by
    intro x hx hxw
    have hxw' : x * (z * w) = (z * w) * x := by
      calc x * (z * w) = ((z * w) * x * (z * w)⁻¹) * (z * w) := by rw [hxw]
        _ = (z * w) * x := by group
    have hxf : ∀ f ∈ zConjClosure y z, x * f = f * x := fun f hf =>
      (Subgroup.mem_centralizer_iff.1 (hcl hf)) x hx
    exact eq_one_of_twoB_sylow hp hp2 hCoP hZW ho₃ ho₄ hc₃₄ hi₃₄ hw₃ hw₄ hxw' (hxf f₃ hf₃)
      (hxf f₄ hf₄) (hpQ x hx) (hoddQ x hx)
  have hext := eq_one_of_klein_fixedPointFree (hsq z hz) (hsq w hw) (Q := Q) hzQ hwQ hfz hfw hfzw
  exact (Subgroup.eq_bot_iff_forall _).2 hext

end TwoB

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
