module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeS
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Central

theorem normal_sylow_of_central_prime {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) {s : G} (hs : orderOf s = p) (hsc : ∀ g : G, g * s = s * g)
    (hG : Nat.card G < 2 * (p * q)) (hqG : q ∣ Nat.card G) (P : Sylow q G) :
    (P : Subgroup G).Normal := by
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hN
  have hsN : s ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have : s * h * s⁻¹ = h := by
      rw [← hsc h]; group
    rw [this]
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hpN : p ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hsN
    rwa [hs] at this
  have hPcard : Nat.card P = q ^ (Nat.card G).factorization q := P.card_eq_multiplicity
  have hPN' : Nat.card P ∣ Nat.card N := Subgroup.card_dvd_of_le hPN
  have hcop : Nat.Coprime p (Nat.card P) := by
    rw [hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 hpq)
  have hpP : p * Nat.card P ∣ Nat.card N := hcop.mul_dvd_of_dvd_of_dvd hpN hPN'
  have hqP : q ≤ Nat.card P := by
    rw [hPcard]
    exact Nat.le_self_pow (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqG).ne' q
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hge : p * q ≤ Nat.card N :=
    (Nat.mul_le_mul_left p hqP).trans (Nat.le_of_dvd hNpos hpP)
  have hidx : N.index * Nat.card N = Nat.card G := Subgroup.index_mul_card N
  have hlt : N.index < 2 := by
    by_contra h
    have h' : 2 ≤ N.index := not_lt.1 h
    have := Nat.mul_le_mul h' hge
    omega
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hone : N.index = 1 := by omega
  have : N = ⊤ := Subgroup.index_eq_one.1 hone
  exact Subgroup.normalizer_eq_top_iff.1 this

variable {C : Type*} [Group C] [Finite C]

theorem isPGroup_of_small_central {p : ℕ} (hp : p.Prime) {Z : Subgroup C} [Z.Normal] {s : C}
    (hsZ : s ∈ Z) (hs : orderOf s = p) (hsc : ∀ c : C, c * s = s * c)
    (hcard : Nat.card Z < 4 * p)
    (hO : ∀ N : Subgroup C, N.Normal → Nat.Coprime p (Nat.card N) → N = ⊥) : IsPGroup p Z := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnot
  obtain ⟨q, hq, hqd, hqp⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card Z ∧ q ≠ p := by
    by_contra h'
    push Not at h'
    apply hnot
    rw [IsPGroup.iff_card]
    exact ⟨(Nat.card Z).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => h' d hd hdd⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q Z) := inferInstance
  have hs' : orderOf (⟨s, hsZ⟩ : Z) = p := by rwa [Subgroup.orderOf_mk]
  have hs'c : ∀ g : Z, g * ⟨s, hsZ⟩ = ⟨s, hsZ⟩ * g := fun g => Subtype.ext (hsc g)
  have hlt : Nat.card Z < 2 * (p * q) := by
    have h2 := hq.two_le
    have : p * 2 ≤ p * q := Nat.mul_le_mul_left p h2
    omega
  have hPn : (P : Subgroup Z).Normal :=
    normal_sylow_of_central_prime (Ne.symm hqp) hs' hs'c hlt hqd P
  have hPchar : (P : Subgroup Z).Characteristic := Sylow.characteristic_of_normal P hPn
  have hP'n : ((P : Subgroup Z).map Z.subtype).Normal := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ c
    have hc : (MulAut.conjNormal c : MulAut Z) x ∈ (P : Subgroup Z) := by
      have := hPchar.fixed (MulAut.conjNormal c)
      have hx' : x ∈ (P : Subgroup Z).comap (MulAut.conjNormal c).toMonoidHom := by
        rw [this]; exact hx
      exact hx'
    exact ⟨_, hc, by simp [MulAut.conjNormal_apply]⟩
  have hcard' : Nat.card ((P : Subgroup Z).map Z.subtype) = Nat.card P :=
    Subgroup.card_map_of_injective Z.subtype_injective
  have hPcard : Nat.card P = q ^ (Nat.card Z).factorization q := P.card_eq_multiplicity
  have hcop : Nat.Coprime p (Nat.card ((P : Subgroup Z).map Z.subtype)) := by
    rw [hcard', hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  have hbot := hO _ hP'n hcop
  have h1 : Nat.card P = 1 := by
    rw [← hcard', hbot]; simp
  have hqP : q ≤ Nat.card P := by
    rw [hPcard]
    exact Nat.le_self_pow (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqd).ne' q
  have := hq.two_le
  omega

end Central

section Invariance

variable {Q : Type} [Group Q]

theorem centralizer_zpowers_eq_singleton (c : Q) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({c} : Set Q) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_singleton_eq_of_zpowers_eq {c d : Q}
    (h : Subgroup.zpowers c = Subgroup.zpowers d) :
    Subgroup.centralizer ({c} : Set Q) = Subgroup.centralizer ({d} : Set Q) := by
  rw [← centralizer_zpowers_eq_singleton, h, centralizer_zpowers_eq_singleton]

theorem shapeRkAt'_of_zpowers_eq {p : ℕ} {Good Rk : ∀ (T : Type) [Group T], Prop} {k k' : Q}
    (hz : Subgroup.zpowers k = Subgroup.zpowers k') (h : ShapeRkAt' p Good Rk k) :
    ShapeRkAt' p Good Rk k' := by
  unfold ShapeRkAt' at h ⊢
  rwa [← centralizer_singleton_eq_of_zpowers_eq hz]

variable [Finite Q]

theorem shapeRkAt'_conj {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') (g k : Q)
    (h : ShapeRkAt' p Good Rk k) : ShapeRkAt' p Good Rk (g * k * g⁻¹) := by
  have := ShapeRkAt'.of_equiv hp hGood hRk (MulAut.conj g) h
  simpa [MulAut.conj_apply] using this

end Invariance

section SmallIndex

variable {Q : Type} [Group Q] [Finite Q]

theorem shapeRkAt'_of_simple_small_index_five {Good Rk : ∀ (T : Type) [Group T], Prop} {t : Q}
    (ht5 : orderOf t = 5)
    (hO : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({t} : Set Q)) = ⊥)
    (E : Subgroup Q) (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (hs : IsSimpleGroup ↥E) (hnab : ∃ a b : ↥E, a * b ≠ b * a) (h5 : 5 ∣ Nat.card ↥E)
    (hnd : ∀ n ≤ 14, ¬ Nat.card ↥E ∣ n.factorial)
    (hC : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 15 * Nat.card ↥E)
    (hG : Good (PSimple 5 E)) (hR : Rk (PQuot 5 E)) : ShapeRkAt' 5 Good Rk t := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := Subgroup.centralizer ({t} : Set Q) with hCdef
  have hEZ : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple_nonab hnab
  set E' : Subgroup ↥C := E.subgroupOf C with hE'def
  have eE : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup ↥E' := eE.isSimpleGroup_congr.2 hs
  have hcardE' : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hidx : E'.index ≤ 14 := by
    have h1 : E'.index * Nat.card E' = Nat.card C := Subgroup.index_mul_card E'
    rw [hcardE'] at h1
    by_contra h
    have : 15 ≤ E'.index := by omega
    nlinarith
  have hnormE' : E'.Normal := by
    refine normal_of_simple_not_dvd_factorial E' ?_
    rw [hcardE']
    exact hnd _ hidx
  have hLn : ∀ g ∈ C, ∀ l ∈ E, g * l * g⁻¹ ∈ E := by
    intro g hg l hl
    have := hnormE'.conj_mem ⟨l, hEC hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hLq : CFSG.Open.IsQuasisimple ↥E := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hEZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  have hcore : GLAPPrimeCore 5 ↥E = ⊥ := by
    haveI := hs
    exact glaPPrimeCore_eq_bot_of_simple Nat.prime_five h5
  have hcent : IsPGroup 5 ↥(C ⊓ Subgroup.centralizer (E : Set Q)) := by
    set Z : Subgroup Q := C ⊓ Subgroup.centralizer (E : Set Q) with hZdef
    have hZC : Z ≤ C := inf_le_left
    set Z0 : Subgroup ↥C := Z.subgroupOf C with hZ0def
    have eZ : ↥Z0 ≃* ↥Z := Subgroup.subgroupOfEquivOfLe hZC
    haveI hZ0n : Z0.Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨C.mul_mem (C.mul_mem g.2 x.2) (C.inv_mem g.2), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro e he
      have he' : (g : Q)⁻¹ * e * g ∈ E := by
        simpa using hLn _ (C.inv_mem g.2) e he
      have h1 := Subgroup.mem_centralizer_iff.1 hx.2 _ he'
      calc e * (g * x * g⁻¹ : ↥C) = g * ((g : Q)⁻¹ * e * g * x) * (g : Q)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = g * (x * ((g : Q)⁻¹ * e * g)) * (g : Q)⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹ : ↥C) * e := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have htZ : t ∈ Z := ⟨htC, Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.1 (hEC hh)⟩
    have hs0Z : (⟨t, htC⟩ : ↥C) ∈ Z0 := Subgroup.mem_subgroupOf.2 htZ
    have hs0c : ∀ c : ↥C, c * (⟨t, htC⟩ : ↥C) = (⟨t, htC⟩ : ↥C) * c := fun c =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
    have hs05 : orderOf (⟨t, htC⟩ : ↥C) = 5 := by rw [Subgroup.orderOf_mk]; exact ht5
    have hinj : Function.Injective ((QuotientGroup.mk' E').comp Z0.subtype) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hzE : (z : ↥C) ∈ E' := (QuotientGroup.eq_one_iff _).1 hz
      have hzE2 : ((z : ↥C) : Q) ∈ E := Subgroup.mem_subgroupOf.1 hzE
      have hzZ : ((z : ↥C) : Q) ∈ Subgroup.centralizer (E : Set Q) :=
        (Subgroup.mem_subgroupOf.1 z.2).2
      have hmem : (⟨((z : ↥C) : Q), hzE2⟩ : ↥E) ∈ Subgroup.center ↥E := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzZ b b.2))
      rw [hEZ, Subgroup.mem_bot] at hmem
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hmem
      simpa using this
    have hZ0card : Nat.card Z0 < 4 * 5 := by
      have h1 := Subgroup.card_dvd_of_injective _ hinj
      have h2 : Nat.card (↥C ⧸ E') = E'.index := rfl
      rw [h2] at h1
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
      omega
    have hO' := normal_coprime_eq_bot_of_gla hO
    have hp := isPGroup_of_small_central Nat.prime_five hs0Z hs05 hs0c hZ0card hO'
    exact hp.of_equiv eZ
  exact (shapeRkAt_of_normal_quasisimple Nat.prime_five hEC hLn hLq h5 (by
    simpa [inf_comm] using hcent) hG hR).toWeak Nat.prime_five

end SmallIndex

section Classes

variable {Q : Type} [Group Q] [Finite Q]

theorem zpowers_pow_eq_of_orderOf_five {y : Q} (hy : orderOf y = 5) {c : ℕ} (hc : ¬ 5 ∣ c) :
    Subgroup.zpowers (y ^ c) = Subgroup.zpowers y := by
  have hco : (orderOf y).Coprime c := by
    rw [hy]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hc
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) c)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hco.orderOf_pow]

theorem centShapeRk'_of_two_classes {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    {z s : Q} (hz : orderOf z = 5) (hs : orderOf s = 5)
    (hconj : ∀ y : Q, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : Q,
      g * z ^ c * g⁻¹ = y ∨ g * s ^ c * g⁻¹ = y)
    (hzS : ShapeRkAt' 5 Good Rk z) (hsS : ShapeRkAt' 5 Good Rk s) :
    CentShapeRk' 5 Good Rk Q := by
  intro k hk1 hk5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk : orderOf k = 5 := orderOf_eq_prime hk5 hk1
  obtain ⟨c, hc, g, hg | hg⟩ := hconj k hk
  · subst hg
    exact shapeRkAt'_conj Nat.prime_five hGood hRk g _
      (shapeRkAt'_of_zpowers_eq (zpowers_pow_eq_of_orderOf_five hz hc).symm hzS)
  · subst hg
    exact shapeRkAt'_conj Nat.prime_five hGood hRk g _
      (shapeRkAt'_of_zpowers_eq (zpowers_pow_eq_of_orderOf_five hs hc).symm hsS)

end Classes

end CFSG.HardMathSupport.Dickson.I271
