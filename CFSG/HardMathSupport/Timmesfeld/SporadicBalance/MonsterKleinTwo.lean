module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKlein
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.Monster.Existence.Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Proving Subgroup


theorem exists_fixed_lift {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {N : Subgroup H}
    (hN : Nat.Coprime p (Nat.card N)) {K : Type*} [Group K] (φ : H →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker = N) {s : H} (hs : s ^ p = 1) {g : K}
    (hg : φ s * g = g * φ s) : ∃ x : H, φ x = g ∧ s * x = x * s := by
  classical
  have := Fintype.ofFinite H
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x0, hx0⟩ := hφ g
  let X := {x : H // φ x = g}
  let f : X → X := fun x => ⟨s * x * s⁻¹, by
    rw [map_mul, map_mul, map_inv, x.2]
    calc φ s * g * (φ s)⁻¹ = (g * φ s) * (φ s)⁻¹ := by rw [hg]
      _ = g := by group⟩
  have hfp : ∀ (k : ℕ) (x : X), (f^[k] x).1 = s ^ k * x.1 * (s ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show s * (f^[k] x).1 * s⁻¹ = _
      rw [ih]
      group
  have hcardX : Nat.card X = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x0⁻¹ * x.1, ?_⟩
        invFun := fun n => ⟨x0 * n.1, ?_⟩
        left_inv := fun x => ?_
        right_inv := fun n => ?_ }
    · rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hx0, x.2]; group
    · rw [map_mul, hx0, show φ n.1 = 1 from (hker ▸ n.2 : n.1 ∈ φ.ker), mul_one]
    · apply Subtype.ext; simp
    · apply Subtype.ext; simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := X) (f := (f : Function.End X)) (p := p)
    (n := 1) (by
      rw [pow_one]
      funext x
      show f^[p] x = x
      apply Subtype.ext
      rw [hfp, hs]
      group)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  by_contra hno
  push Not at hno
  have hz : Nat.card (Function.fixedPoints (f : Function.End X)) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have := hno x.1 x.2
    apply this
    have h2 : s * x.1 * s⁻¹ = x.1 := congrArg Subtype.val hx
    calc s * x.1 = (s * x.1 * s⁻¹) * s := by group
      _ = x.1 * s := by rw [h2]
  rw [hz, hcardX] at hmod
  exact (Nat.Prime.one_lt hp).ne' (Nat.Coprime.eq_one_of_dvd hN ((Nat.modEq_zero_iff_dvd).1 hmod))

theorem mem_of_oPrimeCoreTrivial_quotient {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} {N : Subgroup ↥H} [N.Normal] (hN : Nat.Coprime p (Nat.card N))
    {K : Type*} [Group K] (e : ↥H ⧸ N ≃* K) (hK : OPrimeCoreTrivialAt p K)
    {s : G} (hsH : s ∈ H) (hs : orderOf s = p) {Y : Subgroup G} (hYH : Y ≤ H)
    (hYs : ∀ y ∈ Y, y * s = s * y)
    (hYn : ∀ g ∈ H, g * s = s * g → ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hYc : Nat.Coprime p (Nat.card Y)) :
    ∀ (y : G) (hy : y ∈ Y), (⟨y, hYH hy⟩ : ↥H) ∈ N := by
  set φ : ↥H →* K := e.toMonoidHom.comp (QuotientGroup.mk' N) with hφ
  have hφsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' N x) = 1 ↔ x ∈ N
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  set s' : ↥H := ⟨s, hsH⟩ with hs'
  have hs'ord : orderOf s' = p := by rw [hs', Subgroup.orderOf_mk, hs]
  have hs'pow : s' ^ p = 1 := by rw [← hs'ord]; exact pow_orderOf_eq_one s'
  have hσpow : (φ s') ^ p = 1 := by rw [← map_pow, hs'pow, map_one]
  have hσne : φ s' ≠ 1 := by
    intro h
    have hmem : s' ∈ N := by rw [← hker]; exact h
    have hd : orderOf (⟨s', hmem⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hs'ord] at hd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hN hd)
  have hσ : orderOf (φ s') = p :=
    ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hσpow)).resolve_left
      (fun h => hσne (orderOf_eq_one_iff.1 h))
  set Yb : Subgroup K := (Y.subgroupOf H).map φ with hYb
  have hSC : Yb ≤ Subgroup.centralizer ({φ s'} : Set K) := by
    rintro _ ⟨y', hy', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYs y' (Subgroup.mem_subgroupOf.1 hy'))
  have hSn : ∀ g' ∈ Subgroup.centralizer ({φ s'} : Set K), ∀ x ∈ Yb, g' * x * g'⁻¹ ∈ Yb := by
    intro g' hg' x hx
    obtain ⟨y', hy', rfl⟩ := hx
    obtain ⟨x1, hx1, hx1s⟩ := exists_fixed_lift hp hN φ hφsurj hker hs'pow
      (g := g') (Subgroup.mem_centralizer_singleton_iff.1 hg').symm
    refine ⟨x1 * y' * x1⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hx1]⟩
    refine Subgroup.mem_subgroupOf.2 ?_
    exact hYn (x1 : G) x1.2 (by simpa using (congrArg Subtype.val hx1s).symm) y'
      (Subgroup.mem_subgroupOf.1 hy')
  have hScop : Nat.Coprime p (Nat.card Yb) := by
    refine Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_map_dvd (Y.subgroupOf H) φ).trans ?_) hYc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
  have hle := le_GLAPPrimeCoreOf_of_normal hSC hSn hScop
  rw [hK (φ s') hσ] at hle
  intro y hy
  have hmem : φ ⟨y, hYH hy⟩ ∈ Yb := ⟨⟨y, hYH hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have h1 := Subgroup.mem_bot.1 (hle hmem)
  rw [← hker]
  exact h1

section Monster

variable {G : Type} [Group G]

theorem klein_data_of_existence (hE : MonsterExistenceStatement G) :
    Finite G ∧ ∃ a z : G, (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧
      (∀ t : G, IsConj a t → IsTwoACentralizer t) ∧ (∀ t : G, IsConj z t → IsTwoBCentralizer t) ∧
      (∀ α : G, orderOf α = 2 →
        Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder → IsConj a α) := by
  obtain ⟨hdata, a, z, ha, hz, hnc, hcls, hA, hB, -⟩ := hE
  refine ⟨hdata.1, a, z, hcls, hA, hB, fun α hα hαc => ?_⟩
  rcases hcls α hα with h | h
  · exact h
  · exfalso
    have h2 := (hB α h).2.2.2.2.1
    rw [hαc] at h2
    norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2

theorem eq_or_eq_of_mem_twoA [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B) {s v : G} (hs : orderOf s = p)
    (hv : orderOf v = 2) (hvs : v * s = s * v) (hA : IsTwoACentralizer v) :
    ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * v = v * q → q = 1 ∨ q = v := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA
  have hcard : Nat.card ↥(Subgroup.center ↥(cent v)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent v).subtype_injective, hZ, Nat.card_zpowers, hv]
  have hN : Nat.Coprime p (Nat.card ↥(Subgroup.center ↥(cent v))) := by
    rw [hcard]
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set G) := GLAPPrimeCoreOf_le _
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp _
  have hsH : s ∈ cent v := Subgroup.mem_centralizer_singleton_iff.2 hvs.symm
  have key := @mem_of_oPrimeCoreTrivial_quotient G _ _ p hp (cent v)
    (Subgroup.center ↥(cent v)) _ hN CFSG.Blueprint.NativeSporadic.B Units.instGroup e hB s hsH hs
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
  intro q hq hqv
  have hqY : q ∈ Q ⊓ cent v := ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqv⟩
  have hmem := key q hqY
  have hmem' : q ∈ (Subgroup.center ↥(cent v)).map (cent v).subtype :=
    ⟨⟨q, hqY.2⟩, hmem, rfl⟩
  rw [hZ] at hmem'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem'
  have h := zpow_mod_orderOf v k
  rw [hv] at h
  push_cast at h
  rw [← hk, ← h]
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · left
    rw [h2, zpow_zero]
  · right
    rw [h2, zpow_one]

theorem exists_pow_two_eq_one_of_mem_twoB [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1) {s v : G}
    (hs : orderOf s = p) (hvs : v * s = s * v) (hB : IsTwoBCentralizer v) :
    ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * v = v * q → ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
  obtain ⟨-, hcardR, -, ⟨e⟩, -⟩ := hB
  have hN : Nat.Coprime p (Nat.card ↥(pCore 2 ↥(cent v))) := by
    rw [hcardR]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set G) := GLAPPrimeCoreOf_le _
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp _
  have hsH : s ∈ cent v := Subgroup.mem_centralizer_singleton_iff.2 hvs.symm
  have key := @mem_of_oPrimeCoreTrivial_quotient G _ _ p hp (cent v)
    (pCore 2 ↥(cent v)) _ hN CFSG.Blueprint.NativeSporadic.Co1 Units.instGroup e hCo s hsH hs
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
  intro q hq hqv
  have hqY : q ∈ Q ⊓ cent v := ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqv⟩
  have hmem := key q hqY
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥(cent v))) ⟨⟨q, hqY.2⟩, hmem⟩
  have := congrArg (fun x : ↥(pCore 2 ↥(cent v)) => (((x : ↥(cent v)) : G))) hk
  exact ⟨k, by simpa using this⟩

theorem gLAPPrimeCoreOf_eq_bot_of_two_twoA_of_third (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    {s a b : G} (hs : orderOf s = p) (haC : a ∈ Subgroup.centralizer ({s} : Set G))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set G)) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b)
    (hca : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder)
    (hcb : Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder)
    (h3 : ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * (a * b) = (a * b) * q → ∃ k : ℕ, q ^ (2 ^ k) = 1) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  obtain ⟨hfin, a0, z0, hcls, hA, hB', hA'⟩ := klein_data_of_existence hE
  have := hfin
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, sq] at this
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have has : a * s = s * a := Subgroup.mem_centralizer_singleton_iff.1 haC
  have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.1 hbC
  exact gLAPPrimeCoreOf_eq_bot_of_klein haC hbC haa hbb hab ha1 hb1 hne
    (eq_or_eq_of_mem_twoA hp hp2 hB hs ha has (hA a (hA' a ha hca)))
    (eq_or_eq_of_mem_twoA hp hp2 hB hs hb hbs (hA b (hA' b hb hcb))) h3

theorem gLAPPrimeCoreOf_eq_bot_of_two_twoA (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1) {s a b : G}
    (hs : orderOf s = p) (haC : a ∈ Subgroup.centralizer ({s} : Set G))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set G)) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b)
    (hca : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder)
    (hcb : Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  obtain ⟨hfin, a0, z0, hcls, hA, hB', hA'⟩ := klein_data_of_existence hE
  have := hfin
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, sq] at this
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have has : a * s = s * a := Subgroup.mem_centralizer_singleton_iff.1 haC
  have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.1 hbC
  have habs : (a * b) * s = s * (a * b) := by
    calc (a * b) * s = a * (b * s) := by group
      _ = a * (s * b) := by rw [hbs]
      _ = (a * s) * b := by group
      _ = (s * a) * b := by rw [has]
      _ = s * (a * b) := by group
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, mul_one]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hbb])
  have habo : orderOf (a * b) = 2 := orderOf_eq_prime (by rw [sq]; exact hab2) hab1
  refine gLAPPrimeCoreOf_eq_bot_of_two_twoA_of_third hE hp hp2 hB hs haC hbC ha hb hab hne hca hcb
    ?_
  intro q hq hqc
  rcases hcls (a * b) habo with h | h
  · rcases eq_or_eq_of_mem_twoA hp hp2 hB hs habo habs (hA _ h) q hq hqc with h1 | h1
    · exact ⟨0, by rw [h1]; simp⟩
    · exact ⟨1, by rw [h1, pow_one, sq]; exact hab2⟩
  · exact exists_pow_two_eq_one_of_mem_twoB hp hp2 hCo hs habs (hB' _ h) q hq hqc

theorem gLAPPrimeCoreOf_eq_bot_of_three_twoA (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    {s a b : G} (hs : orderOf s = p) (haC : a ∈ Subgroup.centralizer ({s} : Set G))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set G)) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b)
    (hca : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder)
    (hcb : Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder)
    (hcab : Nat.card ↥(Subgroup.centralizer ({a * b} : Set G)) = 2 * monsterBabyOrder) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  obtain ⟨hfin, a0, z0, hcls, hA, hB', hA'⟩ := klein_data_of_existence hE
  have := hfin
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, sq] at this
  have has : a * s = s * a := Subgroup.mem_centralizer_singleton_iff.1 haC
  have hbs : b * s = s * b := Subgroup.mem_centralizer_singleton_iff.1 hbC
  have habs : (a * b) * s = s * (a * b) := by
    calc (a * b) * s = a * (b * s) := by group
      _ = a * (s * b) := by rw [hbs]
      _ = (a * s) * b := by group
      _ = (s * a) * b := by rw [has]
      _ = s * (a * b) := by group
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, mul_one]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hbb])
  have habo : orderOf (a * b) = 2 := orderOf_eq_prime (by rw [sq]; exact hab2) hab1
  refine gLAPPrimeCoreOf_eq_bot_of_two_twoA_of_third hE hp hp2 hB hs haC hbC ha hb hab hne hca hcb
    ?_
  intro q hq hqc
  rcases eq_or_eq_of_mem_twoA hp hp2 hB hs habo habs (hA _ (hA' _ habo hcab)) q hq hqc with h1 | h1
  · exact ⟨0, by rw [h1]; simp⟩
  · exact ⟨1, by rw [h1, pow_one, sq]; exact hab2⟩

end Monster

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
