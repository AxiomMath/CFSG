module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma36
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l93c_conj_comm {g x h : G} (hg : g * x = x * g) :
    h * x = x * h ↔ (g * h * g⁻¹) * x = x * (g * h * g⁻¹) := by
  have hgi : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [← hg]
      _ = x * g⁻¹ := by group
  have e1 : (g * h * g⁻¹) * x = g * (h * x) * g⁻¹ := by
    calc (g * h * g⁻¹) * x = g * h * (g⁻¹ * x) := by group
      _ = g * h * (x * g⁻¹) := by rw [hgi]
      _ = g * (h * x) * g⁻¹ := by group
  have e2 : x * (g * h * g⁻¹) = g * (x * h) * g⁻¹ := by
    calc x * (g * h * g⁻¹) = (x * g) * h * g⁻¹ := by group
      _ = (g * x) * h * g⁻¹ := by rw [← hg]
      _ = g * (x * h) * g⁻¹ := by group
  rw [e1, e2]
  simp only [mul_left_inj, mul_right_inj]

private theorem l93c_centralizer_le_normalizer (x g : G)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact l93c_conj_comm (Subgroup.mem_centralizer_singleton_iff.1 hg)

private theorem l93c_mk_eq_one_of_mem {p : ℕ} {X : Subgroup G} {z : G} (hz : z ∈ X)
    (h : z ∈ GLAPPrimeCoreOf p X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨z, hz⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = 1 := by
  obtain ⟨w, hw, hwz⟩ := h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hw' : w = ⟨z, hz⟩ := Subtype.ext hwz
  rw [← hw']
  exact hw

private theorem l93c_mem_of_mk_eq_one {p : ℕ} {X : Subgroup G} {z : G} (hz : z ∈ X)
    (h : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨z, hz⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = 1) :
    z ∈ GLAPPrimeCoreOf p X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact ⟨⟨z, hz⟩, h, rfl⟩

private theorem l93c_mk_commute {p : ℕ} {X : Subgroup G} {l y : G} (hlX : l ∈ X) (hyX : y ∈ X)
    (h : ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ := by
  have hzX : ⁅l, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hlX hyX) (X.inv_mem hlX)) (X.inv_mem hyX)
  have h1 := l93c_mk_eq_one_of_mem hzX h
  have e : (⟨⁅l, y⁆, hzX⟩ : ↥X) = ⟨l, hlX⟩ * ⟨y, hyX⟩ * ⟨l, hlX⟩⁻¹ * ⟨y, hyX⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 := mul_inv_eq_one.1 h1
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = a at h2 ⊢
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = b at h2 ⊢
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h2]

private theorem l93c_barX_gLBConj {p : ℕ} {X L : Subgroup G} {y : G} (hLX : L ≤ X) (hyX : y ∈ X)
    (hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) :
    barX p X (GLBConj y L) = barX p X L := by
  have key : ∀ (l : G) (hl : l ∈ L) (k : ↥X), (k : G) = y⁻¹ * l * y →
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) k =
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hLX hl⟩ := by
    intro l hl k hk
    have hlX : l ∈ X := hLX hl
    have hc := l93c_mk_commute hlX hyX (hyc l hl)
    have hk' : k = ⟨y, hyX⟩⁻¹ * ⟨l, hlX⟩ * ⟨y, hyX⟩ := Subtype.ext (by simp [hk])
    rw [hk', map_mul, map_mul, map_inv]
    generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = a at hc ⊢
    generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = b at hc ⊢
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (b * a) := by rw [hc]
      _ = a := by group
  ext q
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk1 : (k : G) ∈ GLBConj y L := Subgroup.mem_subgroupOf.1 hk
    rw [mem_gLBConj] at hk1
    have hwX : y * k * y⁻¹ ∈ X := by
      have hkX : (k : G) ∈ X := k.2
      exact X.mul_mem (X.mul_mem hyX hkX) (X.inv_mem hyX)
    refine ⟨⟨y * k * y⁻¹, hwX⟩, (Subgroup.mem_subgroupOf).2 hk1, ?_⟩
    exact (key (y * k * y⁻¹) hk1 k (by group)).symm
  · rintro ⟨w, hw, rfl⟩
    have hw1 : (w : G) ∈ L := Subgroup.mem_subgroupOf.1 hw
    have hkX : y⁻¹ * (w : G) * y ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hyX) w.2) hyX
    refine ⟨⟨y⁻¹ * (w : G) * y, hkX⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
    · rw [mem_gLBConj]
      have e : y * (y⁻¹ * (w : G) * y) * y⁻¹ = w := by group
      rw [e]
      exact hw1
    · exact key (w : G) hw1 ⟨y⁻¹ * (w : G) * y, hkX⟩ rfl

private theorem l93c_comm_of_ne {p : ℕ} {X L L' : Subgroup G} (hL : GLAPComponent p X L)
    (hL' : GLAPComponent p X L') (hne : L ≠ L') {l y : G} (hl : l ∈ L) (hy : y ∈ L') :
    ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X := by
  have hbar : barX p X L ≠ barX p X L' := fun h => hne (glaPComponent_unique hL hL' h)
  have hcomm : ⁅barX p X L, barX p X L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 hL'.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hlX : l ∈ X := hL.1 hl
  have hyX : y ∈ X := hL'.1 hy
  have ha : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      barX p X L := ⟨⟨l, hlX⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
  have hb : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      barX p X L' := ⟨⟨y, hyX⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
  have hab := Subgroup.mem_centralizer_iff.1 (hcen ha) _ hb
  have hzX : ⁅l, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hlX hyX) (X.inv_mem hlX)) (X.inv_mem hyX)
  refine l93c_mem_of_mk_eq_one hzX ?_
  have e : (⟨⁅l, y⁆, hzX⟩ : ↥X) = ⟨l, hlX⟩ * ⟨y, hyX⟩ * ⟨l, hlX⟩⁻¹ * ⟨y, hyX⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = a at hab ⊢
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = b at hab ⊢
  rw [← hab]
  group

private theorem l93c_gLBConj_eq {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) {y : G}
    (hyX : y ∈ X) (hyN : y ∈ Subgroup.normalizer (X : Set G))
    (hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) : GLBConj y L = L := by
  have hXy : GLBConj y X = X := mem_normalizer_iff_gLBConj_eq.1 hyN
  have h1 := glaPComponent_gLBConj hL y
  rw [hXy] at h1
  exact glaPComponent_unique h1 hL (l93c_barX_gLBConj hL.1 hyX hyc)

private theorem l93c_isElemAbelian_pair {p : ℕ} {x y : G} (hxy : x * y = y * x) (hx : x ^ p = 1)
    (hy : y ^ p = 1) : IsElemAbelian p (Subgroup.closure ({x, y} : Set G)) := by
  have hpair : ({x, y} : Set G).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact hxy
    · exact hxy.symm
    · exact absurd rfl hab
  have hcomm := Subgroup.isMulCommutative_closure hpair
  have hcl : ∀ a ∈ Subgroup.closure ({x, y} : Set G), ∀ b ∈ Subgroup.closure ({x, y} : Set G),
      a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : Subgroup.closure ({x, y} : Set G))
      ⟨b, hb⟩)
  refine ⟨hcomm, ?_⟩
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (hcl a ha b hb)), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

private theorem l93c_false_of_elem {p : ℕ} (hp : p.Prime) {x : G} {L : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    {y : G} (hyC : y ∈ Subgroup.centralizer ({x} : Set G))
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hxo : orderOf x = p) (hyo : y ^ p = 1) (hyx : y ∉ Subgroup.zpowers x)
    (hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) : False := by
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hsn : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hL.2.1
  have hxM : x ∈ centModSubgroup p L := by
    rw [mem_centModSubgroup]
    refine ⟨hxN, fun l hl => ?_⟩
    have hlC : l ∈ Subgroup.centralizer ({x} : Set G) := hL.1 hl
    have hcomm : ⁅l, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hlC)
    rw [hcomm]
    exact Subgroup.one_mem _
  have hyM : y ∈ centModSubgroup p L := by
    rw [mem_centModSubgroup]
    refine ⟨hyN, fun l hl => ?_⟩
    have h1 : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hyN l⁻¹).1 (L.inv_mem hl)
    have h2 : ⁅l, y⁆ ∈ L := by
      have e : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem hl h1
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    exact Subgroup.mem_inf.2 ⟨h2, hyc l hl⟩
  set A : Subgroup G := Subgroup.closure ({x, y} : Set G) with hAdef
  have hAle : A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L := by
    rw [hAdef, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_inf.2 ⟨hxC, hxM⟩
    · exact Subgroup.mem_inf.2 ⟨hyC, hyM⟩
  have hAel : IsElemAbelian p A := l93c_isElemAbelian_pair hxy hxp hyo
  have hcard : Nat.card A ≤ p := hspade A hAle hAel
  have hzA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxo]
  have heq : Subgroup.zpowers x = A := Subgroup.eq_of_le_of_card_ge hzA (by rw [hcardx]; exact hcard)
  have hyA : y ∈ A := Subgroup.subset_closure (by simp)
  rw [← heq] at hyA
  exact hyx hyA

private theorem l93c_lift {p : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H]
    (q : H ⧸ GLAPPrimeCore p H) (hq : q ^ p = 1) :
    ∃ y : H, y ^ p = 1 ∧ (QuotientGroup.mk y : H ⧸ GLAPPrimeCore p H) = q := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p H)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p H
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' p hp.ne_one
  have hmcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  have hmod : m ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hmcop
    rwa [Nat.totient_prime hp] at this
  have hez : m ^ (p - 1) = p * (m ^ (p - 1) / p) + 1 := by
    have h1 : m ^ (p - 1) % p = 1 := by
      unfold Nat.ModEq at hmod
      rw [hmod, Nat.mod_eq_of_lt hp.one_lt]
    have := Nat.div_add_mod (m ^ (p - 1)) p
    omega
  have hqe : (QuotientGroup.mk u : H ⧸ GLAPPrimeCore p H) ^ (m ^ (p - 1)) =
      QuotientGroup.mk u := by
    rw [hez, pow_add, pow_mul, hq, one_pow, one_mul, pow_one]
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hdvd : orderOf u ∣ m ^ (p - 1) * p ^ a := by
    rw [hord, mul_comm (m ^ (p - 1)) (p ^ a)]
    exact mul_dvd_mul_left (p ^ a) (dvd_pow_self m hp1)
  have hzpow : (u ^ (m ^ (p - 1))) ^ (p ^ a) = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    exact hdvd
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    refine ⟨u ^ (m ^ (p - 1)), ?_, ?_⟩
    · rw [pow_zero, pow_one] at hzpow
      rw [hzpow, one_pow]
    · rw [QuotientGroup.mk_pow, hqe]
  · refine ⟨u ^ (m ^ (p - 1)), ?_, ?_⟩
    · set z := u ^ (m ^ (p - 1)) with hz
      have hwO : z ^ p ∈ GLAPPrimeCore p H := by
        have h1 : (QuotientGroup.mk (z ^ p) : H ⧸ GLAPPrimeCore p H) = 1 := by
          rw [QuotientGroup.mk_pow, hz, QuotientGroup.mk_pow, hqe]
          exact hq
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hwp : (z ^ p) ^ (p ^ (a - 1)) = 1 := by
        rw [← pow_mul]
        have : p * p ^ (a - 1) = p ^ a := by
          rw [← pow_succ']
          congr 1
          omega
        rw [this]
        exact hzpow
      have hord1 : orderOf (⟨z ^ p, hwO⟩ : GLAPPrimeCore p H) ∣ p ^ (a - 1) := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        exact hwp
      have hord2 : orderOf (⟨z ^ p, hwO⟩ : GLAPPrimeCore p H) ∣ Nat.card (GLAPPrimeCore p H) :=
        orderOf_dvd_natCard _
      have hgcd : orderOf (⟨z ^ p, hwO⟩ : GLAPPrimeCore p H) = 1 := by
        have := Nat.dvd_gcd hord1 hord2
        rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left (a - 1) hcop)] at this
        exact Nat.dvd_one.1 this
      have hone : (⟨z ^ p, hwO⟩ : GLAPPrimeCore p H) = 1 := orderOf_eq_one_iff.1 hgcd
      have : z ^ p = 1 := congrArg Subtype.val hone
      exact this
    · rw [QuotientGroup.mk_pow, hqe]

theorem l93_cx_le_normalizer_L {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 p B x L)
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := h.comp
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := h.norm h.mem
  have hxp : x ^ p = 1 := h.bmax.1.2 x h.mem
  have hxo : orderOf x = p := orderOf_eq_prime hxp h.ne_one
  intro g hg
  by_contra hgN
  have hgNX := l93c_centralizer_le_normalizer x g hg
  have hXg : GLBConj g (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({x} : Set G) :=
    mem_normalizer_iff_gLBConj_eq.1 hgNX
  have hL' : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) (GLBConj g L) := by
    have := glaPComponent_gLBConj hL g
    rwa [hXg] at this
  have hne : L ≠ GLBConj g L := fun e => hgN (mem_normalizer_iff_gLBConj_eq.2 e.symm)
  obtain ⟨y, hyL', hyo, hyx⟩ : ∃ y ∈ GLBConj g L, y ^ p = 1 ∧ y ∉ Subgroup.zpowers x := by
    haveI : Fintype (PQuot p (GLBConj g L)) := Fintype.ofFinite _
    obtain ⟨P⟩ : Nonempty (Sylow p (PQuot p (GLBConj g L))) := inferInstance
    obtain ⟨q, -, hqo, hqc⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S3.exists_order_p_not_central hp hp2 hL' P
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hv, hvu⟩ := l93c_lift hp _ hqo
    refine ⟨(v : G), v.2, ?_, ?_⟩
    · rw [← Subgroup.coe_pow, hv, Subgroup.coe_one]
    · intro hvx
      apply hqc
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g'
      have hwX : (w : G) ∈ Subgroup.centralizer ({x} : Set G) := hL'.1 w.2
      have hwx : Commute (w : G) x := Subgroup.mem_centralizer_singleton_iff.1 hwX
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hvx
      have hcomm : (w : G) * (v : G) = (v : G) * (w : G) := by
        rw [← hk]
        exact (hwx.zpow_right k).eq
      have hcomm' : w * v = v * w := Subtype.ext hcomm
      rw [← hvu, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm']
  have hyX : (y : G) ∈ Subgroup.centralizer ({x} : Set G) := hL'.1 hyL'
  have hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    fun l hl => l93c_comm_of_ne hL hL' hne hl hyL'
  have hyNX := l93c_centralizer_le_normalizer x y hyX
  have hyNL : y ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (l93c_gLBConj_eq hL hyX hyNX hyc)
  exact l93c_false_of_elem hp hL hyX hyNL hxN hxo hyo hyx hyc hspade

private theorem l93c_eq_one_of_coprime {Y : Type} [Group Y] [Finite Y] {p n : ℕ} {K : Subgroup Y}
    (hK : Nat.Coprime p (Nat.card K)) {w : Y} (hw : w ∈ K) (h : w ^ (p ^ n) = 1) : w = 1 := by
  have h1 : orderOf (⟨w, hw⟩ : K) ∣ p ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using h
  have h2 : orderOf (⟨w, hw⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n hK)] at h3
  have h4 : orderOf (⟨w, hw⟩ : K) = 1 := Nat.dvd_one.1 h3
  have h5 : (⟨w, hw⟩ : K) = 1 := orderOf_eq_one_iff.1 h4
  exact congrArg Subtype.val h5

private theorem l93c_pPrimeCore_map_normal {Y : Type} [Group Y] [Finite Y] (p : ℕ)
    {R : Subgroup Y} [hR : R.Normal] :
    ((GLAPPrimeCore p ↥R).map R.subtype).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hn
  let e : ↥R ≃* ↥R :=
    { toFun := fun r => ⟨g * r * g⁻¹, hR.conj_mem r.1 r.2 g⟩
      invFun := fun r => ⟨g⁻¹ * r * g, by simpa using hR.conj_mem r.1 r.2 g⁻¹⟩
      left_inv := fun r => Subtype.ext (by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]; group)
      right_inv := fun r => Subtype.ext (by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have he : (GLAPPrimeCore p ↥R).map e.toMonoidHom = GLAPPrimeCore p ↥R :=
    CFSG.pPrimeCore_map_iso p e
  have hek : e k ∈ GLAPPrimeCore p ↥R := by
    rw [← he]
    exact Subgroup.mem_map_of_mem _ hk
  refine Subgroup.mem_map.2 ⟨e k, hek, ?_⟩
  simp only [e, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_subtype, MonoidHom.coe_coe]

private theorem l93c_pPrimeCore_eq_bot_of_normal {Y : Type} [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime]
    {R : Subgroup Y} [hR : R.Normal] (hY : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCore p ↥R = ⊥ := by
  have hN := l93c_pPrimeCore_map_normal (R := R) p
  have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCore p ↥R).map R.subtype)) := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥R
  have hle : (GLAPPrimeCore p ↥R).map R.subtype ≤ GLAPPrimeCore p Y := le_sSup ⟨hN, hcop⟩
  rw [hY] at hle
  apply Subgroup.map_injective (f := R.subtype) R.subtype_injective
  rw [Subgroup.map_bot]
  exact le_bot_iff.1 hle

private theorem l93c_isPGroup_of_cyclic {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (P : Subgroup H) [hPn : P.Normal] (hPp : IsPGroup p P) (hPc : IsCyclic P) {z : H}
    (hzP : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ r : H, r * z = z * r)
    (hbend : ∀ r : H, (∀ s ∈ P, r * s = s * r) → r ∈ P) : IsPGroup p H := by
  classical
  haveI := Fact.mk hp
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hPp
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := ↥P)
  have hord : orderOf c = p ^ m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, hm]
  set γ : H := (c : H) with hγdef
  have hγord : orderOf γ = p ^ m := by
    rw [hγdef, Subgroup.orderOf_coe, hord]
  have hPγ : ∀ y ∈ P, y ∈ Subgroup.zpowers γ := by
    intro y hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨y, hy⟩)
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [hγdef, ← Subgroup.coe_zpow, hj]
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 (hPγ z hzP)
  have hm0 : m ≠ 0 := by
    intro h0
    apply hz1
    rw [← ht]
    have hγ1 : γ = 1 := orderOf_eq_one_iff.1 (by rw [hγord, h0, pow_zero])
    rw [hγ1, one_zpow]
  have hγP : γ ∈ P := c.2
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcong : ∀ r : H, ∃ a : ℤ, r * γ * r⁻¹ = γ ^ a ∧ (p : ℤ) ∣ a - 1 := by
    intro r
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hPγ _ (hPn.conj_mem γ hγP r))
    refine ⟨a, ha.symm, ?_⟩
    have hz : r * z * r⁻¹ = z := by
      rw [hzc r]
      group
    have hfix : γ ^ (a * t) = γ ^ t := by
      calc γ ^ (a * t) = (γ ^ a) ^ t := zpow_mul γ a t
        _ = (r * γ * r⁻¹) ^ t := by rw [ha.symm]
        _ = r * γ ^ t * r⁻¹ := conj_zpow
        _ = r * z * r⁻¹ := by rw [ht]
        _ = z := hz
        _ = γ ^ t := ht.symm
    have h1 : γ ^ ((a - 1) * t) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, hfix, mul_inv_cancel]
    have hdiv : ((p ^ m : ℕ) : ℤ) ∣ (a - 1) * t := by
      have := orderOf_dvd_iff_zpow_eq_one.2 h1
      rw [hγord] at this
      exact this
    by_contra hnd
    have hcop : IsCoprime ((p : ℤ) ^ m) (a - 1) :=
      IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hpint.irreducible).2 hnd)
    have ht' : ((p : ℤ) ^ m) ∣ t := by
      push_cast at hdiv
      exact hcop.dvd_of_dvd_mul_left hdiv
    apply hz1
    rw [← ht]
    exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hγord]; exact_mod_cast ht')
  intro r
  obtain ⟨a, ha, hpa⟩ := hcong r
  have hk : ∀ j : ℕ, r ^ j * γ * (r ^ j)⁻¹ = γ ^ (a ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc r ^ (j + 1) * γ * (r ^ (j + 1))⁻¹ = r * (r ^ j * γ * (r ^ j)⁻¹) * r⁻¹ := by
            rw [pow_succ']
            group
        _ = r * γ ^ (a ^ j) * r⁻¹ := by rw [ih]
        _ = (r * γ * r⁻¹) ^ (a ^ j) := conj_zpow.symm
        _ = (γ ^ a) ^ (a ^ j) := by rw [ha]
        _ = γ ^ (a ^ (j + 1)) := by rw [← zpow_mul, pow_succ']
  set k : ℕ := p ^ (m - 1) with hkdef
  have hdvdk : ((p : ℤ) ^ m) ∣ a ^ k - 1 := by
    have h := dvd_sub_pow_of_dvd_sub hpa (m - 1)
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1, one_pow] at h
    exact h
  have hγk : γ ^ (a ^ k) = γ := by
    have h1 : γ ^ (a ^ k - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.1 (by rw [hγord]; exact_mod_cast hdvdk)
    rw [zpow_sub_one, mul_inv_eq_one] at h1
    exact h1
  have hrk : r ^ k * γ = γ * r ^ k := by
    have h2 := hk k
    rw [hγk, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hmem : r ^ k ∈ P := by
    refine hbend (r ^ k) fun s hs => ?_
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hPγ s hs)
    rw [← hj]
    exact (Commute.zpow_right (show Commute (r ^ k) γ from hrk) j).eq
  obtain ⟨n, hn⟩ := hPp ⟨r ^ k, hmem⟩
  have h3 : (r ^ k) ^ (p ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨m - 1 + n, ?_⟩
  rw [pow_add, pow_mul]
  exact h3

private theorem l93c_isCyclic_of_elemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type}
    [Group Y] [Finite Y] {C : Subgroup Y} (hC : IsPGroup p C)
    (h : ∀ F : Subgroup Y, F ≤ C → IsElemAbelian p F → Nat.card F ≤ p) : IsCyclic C := by
  have hr : CFSG.pRank p C ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.SectionRank.pRank_le hp.one_lt fun F _ hF => ?_
    have hmap := CFSG.SectionRank.isElemAbelian_map hF C.subtype
    have := h (F.map C.subtype) (Subgroup.map_subtype_le F) hmap
    rw [Subgroup.card_map_of_injective C.subtype_injective] at this
    rw [pow_one]
    exact this
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp hC).mp hr with
    hcyc | ⟨h2, -⟩
  · exact hcyc
  · exact absurd h2 hp2

private theorem l93c_comm_mem {p : ℕ} {X : Subgroup G} {l y : G} (hlX : l ∈ X) (hyX : y ∈ X)
    (hab : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩) :
    ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X := by
  have hzX : ⁅l, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hlX hyX) (X.inv_mem hlX)) (X.inv_mem hyX)
  refine l93c_mem_of_mk_eq_one hzX ?_
  have e : (⟨⁅l, y⁆, hzX⟩ : ↥X) = ⟨l, hlX⟩ * ⟨y, hyX⟩ * ⟨l, hlX⟩⁻¹ * ⟨y, hyX⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = a at hab ⊢
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = b at hab ⊢
  rw [hab]
  group

private theorem l93c_mk_comm_of_centMod {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) {g : G} (hg : g ∈ centModSubgroup p L) (hgX : g ∈ X) (l : G)
    (hl : l ∈ L) (hlX : l ∈ X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ := by
  have hc : ⁅l, g⁆ ∈ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 ((mem_centModSubgroup.1 hg).2 l hl)
  exact l93c_mk_commute hlX hgX hc

abbrev l93cR (p : ℕ) (X L : Subgroup G) : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
  Subgroup.centralizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X))

private theorem l93c_mem_barX {p : ℕ} {X L : Subgroup G} {l : G} (hl : l ∈ L) (hlX : l ∈ X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ barX p X L :=
  ⟨⟨l, hlX⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩

private theorem l93c_mem_cR {p : ℕ} {X L : Subgroup G} {g : G} (hgX : g ∈ X)
    (hc : ∀ l ∈ L, ∀ hlX : l ∈ X,
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hgX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      l93cR p X L := by
  rw [Subgroup.mem_centralizer_iff]
  rintro h ⟨⟨l, hlX⟩, hk, rfl⟩
  have hl : l ∈ L := Subgroup.mem_subgroupOf.1 hk
  exact hc l hl hlX

private theorem l93c_comm_of_mem_cR {p : ℕ} {X L : Subgroup G} {w : G} (hwX : w ∈ X)
    (hw : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨w, hwX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      l93cR p X L) (l : G) (hl : l ∈ L) (hlX : l ∈ X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨w, hwX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨w, hwX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ :=
  Subgroup.mem_centralizer_iff.1 hw _ (l93c_mem_barX hl hlX)

private theorem l93c_centMod_of_comm {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hN : X ≤ Subgroup.normalizer (L : Set G)) {s : G} (hsX : s ∈ X)
    (hc : ∀ l ∈ L, ∀ hlX : l ∈ X,
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) *
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hsX⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hsX⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩) :
    s ∈ centModSubgroup p L := by
  rw [mem_centModSubgroup]
  refine ⟨hN hsX, fun l hl => ?_⟩
  have hlX : l ∈ X := hL.1 hl
  have hO : ⁅l, s⁆ ∈ GLAPPrimeCoreOf p X := l93c_comm_mem hlX hsX (hc l hl hlX)
  have hLs : ⁅l, s⁆ ∈ L := by
    have e : ⁅l, s⁆ = l * (s * l⁻¹ * s⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.1 (hN hsX) l⁻¹).1 (L.inv_mem hl))
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
  exact Subgroup.mem_inf.2 ⟨hLs, hO⟩

private theorem l93c_pow_card_eq_one {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {w : Y}
    (hw : w ∈ K) : w ^ (Nat.card K) = 1 := by
  have h := orderOf_dvd_natCard (⟨w, hw⟩ : K)
  have h2 : orderOf w = orderOf (⟨w, hw⟩ : K) := Subgroup.orderOf_coe (⟨w, hw⟩ : K)
  rw [← orderOf_dvd_iff_pow_eq_one, h2]
  exact h

private theorem l93c_card_le_of_elemAbelian {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hN : X ≤ Subgroup.normalizer (L : Set G))
    (hspade : ∀ A : Subgroup G, A ≤ X ⊓ centModSubgroup p L → IsElemAbelian p A → Nat.card A ≤ p)
    {E : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hER : E ≤ l93cR p X L) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥X
  set π : ↥X →* (↥X ⧸ GLAPPrimeCore p ↥X) := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set W : Subgroup ↥X := E.comap π with hWdef
  have hWM : ∀ w ∈ W, (w : G) ∈ X ⊓ centModSubgroup p L := by
    intro w hw
    have hwR : π w ∈ E := hw
    refine Subgroup.mem_inf.2 ⟨w.2, l93c_centMod_of_comm hp hL hN w.2 ?_⟩
    intro l hl hlX
    exact l93c_comm_of_mem_cR w.2 (hER hwR) l hl hlX
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hE)
  have hWcard : Nat.card W = Nat.card E * Nat.card (GLAPPrimeCore p ↥X) := by
    have hidx : W.index = E.index := Subgroup.index_comap_of_surjective E hπsurj
    have h1 := Subgroup.card_mul_index W
    have h2 := Subgroup.card_mul_index E
    have h3 := Subgroup.card_mul_index (GLAPPrimeCore p ↥X)
    have hi : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hO : (GLAPPrimeCore p ↥X).index = Nat.card (↥X ⧸ GLAPPrimeCore p ↥X) := rfl
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    calc Nat.card W * E.index = Nat.card W * W.index := by rw [hidx]
      _ = Nat.card ↥X := h1
      _ = Nat.card (GLAPPrimeCore p ↥X) * (GLAPPrimeCore p ↥X).index := h3.symm
      _ = Nat.card (GLAPPrimeCore p ↥X) * (Nat.card E * E.index) := by rw [hO, ← h2]
      _ = Nat.card E * Nat.card (GLAPPrimeCore p ↥X) * E.index := by ring
  have hdvd : p ^ n ∣ Nat.card W := ⟨Nat.card (GLAPPrimeCore p ↥X), by rw [hWcard, hn]⟩
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W) p hdvd
  set S : Subgroup ↥X := S₀.map W.subtype with hSdef
  have hScard : Nat.card S = p ^ n := by
    rw [hSdef, Subgroup.card_map_of_injective W.subtype_injective, hS₀]
  have hSW : ∀ s ∈ S, s ∈ W := by
    intro s hs
    obtain ⟨s₀, -, rfl⟩ := Subgroup.mem_map.1 hs
    exact s₀.2
  clear_value S
  have hpowS : ∀ w ∈ S, w ^ (p ^ n) = 1 := fun w hw => by
    rw [← hScard]
    exact l93c_pow_card_eq_one hw
  have hinj : ∀ s ∈ S, ∀ t ∈ S, π s = π t → s = t := by
    intro s hs t ht hst
    have hst' : s⁻¹ * t ∈ S := S.mul_mem (S.inv_mem hs) ht
    have h2 : π (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, hst, inv_mul_cancel]
    have h3 : s⁻¹ * t ∈ GLAPPrimeCore p ↥X := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    have h4 : s⁻¹ * t = 1 := l93c_eq_one_of_coprime hcop h3 (hpowS _ hst')
    exact inv_mul_eq_one.1 h4
  have hSle : S.map π ≤ E := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSW s hs
  have hcardmap : Nat.card (S.map π) = Nat.card S :=
    (Nat.card_congr (Equiv.ofBijective
      (fun s : S => (⟨π s.1, Subgroup.mem_map_of_mem π s.2⟩ : S.map π))
      ⟨fun a b hab => Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab)),
        fun y => by
          obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 y.2
          exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩⟩)).symm
  have hEeq : S.map π = E :=
    Subgroup.eq_of_le_of_card_ge hSle (by rw [hcardmap, hScard, hn])
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    apply hinj _ (S.mul_mem hs ht) _ (S.mul_mem ht hs)
    rw [map_mul, map_mul]
    exact hEcomm _ (hSle (Subgroup.mem_map_of_mem π hs)) _ (hSle (Subgroup.mem_map_of_mem π ht))
  have hSexp : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    apply hinj _ (S.pow_mem hs p) 1 S.one_mem
    rw [map_pow, map_one]
    exact hE.2 _ (hSle (Subgroup.mem_map_of_mem π hs))
  have hSel : IsElemAbelian p S :=
    ⟨Subgroup.le_centralizer_iff_isMulCommutative.1
      (fun s hs => Subgroup.mem_centralizer_iff.2 (fun t ht => (hScomm s hs t ht).symm)),
      hSexp⟩
  have hS'el : IsElemAbelian p (S.map X.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hSel X.subtype
  have hS'le : S.map X.subtype ≤ X ⊓ centModSubgroup p L := by
    rintro _ ⟨s, hs, rfl⟩
    exact hWM s (hSW s hs)
  have hcardS' : Nat.card (S.map X.subtype) = Nat.card S := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
  have hbound := hspade _ hS'le hS'el
  rw [hcardS', hScard] at hbound
  rw [hn]
  exact hbound

private theorem l93c_top_le_pPrimeCore {Z : Type} [Group Z] [Finite Z] (p : ℕ) (K : Subgroup Z)
    (hcop : Nat.Coprime p (Nat.card K)) : (⊤ : Subgroup ↥K) ≤ CFSG.pPrimeCore p ↥K := by
  refine le_sSup ?_
  exact ⟨Subgroup.normal_top, by simpa [Subgroup.card_top] using hcop⟩

private theorem l93c_top_eq_bot {H : Type} [Group H] [Finite H] {p : ℕ}
    (hO : GLAPPrimeCore p H = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup H) = ⊥ := by
  unfold GLAPPrimeCore at hO
  have h1 := CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
  rw [hO] at h1
  have h2 : CFSG.pPrimeCore p ↥(⊤ : Subgroup H) = ⊥ := by
    apply Subgroup.map_injective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).toMonoidHom)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).injective
    rw [h1, Subgroup.map_bot]
  unfold GLAPPrimeCoreOf GLAPPrimeCore
  rw [h2, Subgroup.map_bot]

private theorem l93c_layer_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {L : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hxo : orderOf x = p)
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p)
    (hO : GLAPPrimeCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) = ⊥)
    {K : Subgroup ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)}
    (hK : CFSG.Open.IsComponentOf K ⊤) : K = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hKsn, hKq⟩ := hK
  by_contra hK0
  have hdvd : p ∣ Nat.card ↥K := by
    by_contra hnd
    have hcop : Nat.Coprime p (Nat.card ↥K) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    have hKp : (⊤ : Subgroup ↥K) ≤ GLAPPrimeCore p ↥K := l93c_top_le_pPrimeCore p K hcop
    have hKle : K ≤ GLAPPrimeCoreOf p K := by
      intro k hk
      exact Subgroup.mem_map.2 ⟨⟨k, hk⟩, hKp (Subgroup.mem_top _), rfl⟩
    have h1 := glaPPrimeCoreOf_le_of_isSubnormal hp hKsn
    have h2 := l93c_top_eq_bot hO
    exact hK0 (le_bot_iff.1 (hKle.trans (h1.trans h2.le)))
  obtain ⟨q, hqo, hqc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hKq hp hp2 hdvd
  have hqpow : q ^ p = 1 := by
    have h := pow_orderOf_eq_one q
    rwa [hqo] at h
  have hqb_pow : ((q : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) :
      (↥(Subgroup.centralizer ({x} : Set G)) ⧸ GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))))
        ^ p = 1 := by
    have h := congrArg (fun z : ↥K => ((z : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) :
      (↥(Subgroup.centralizer ({x} : Set G)) ⧸ GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G)))))
      hqpow
    simpa using h
  obtain ⟨y, hyp, hyq⟩ := l93c_lift hp _ hqb_pow
  have hyX : (y : G) ∈ Subgroup.centralizer ({x} : Set G) := y.2
  have hqR : ((q : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) :
      (↥(Subgroup.centralizer ({x} : Set G)) ⧸ GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))))
        ∈ l93cR p (Subgroup.centralizer ({x} : Set G)) L := (q : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)).2
  have hyc : ∀ l ∈ L, ⁅l, (y : G)⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
    intro l hl
    have hlX : l ∈ Subgroup.centralizer ({x} : Set G) := hL.1 hl
    apply l93c_comm_mem hlX hyX
    have hc := Subgroup.mem_centralizer_iff.1 hqR _ (l93c_mem_barX hl hlX)
    rw [← hyq] at hc
    exact hc
  have hyN : (y : G) ∈ Subgroup.normalizer (L : Set G) := hN hyX
  have hyo : (y : G) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
  have hyx : (y : G) ∉ Subgroup.zpowers x := by
    intro hmem
    apply hqc
    have hcentral : ∀ z : (↥(Subgroup.centralizer ({x} : Set G)) ⧸
        GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))),
        z * (((q : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) :
          (↥(Subgroup.centralizer ({x} : Set G)) ⧸
            GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))))) =
        ((q : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) :
          (↥(Subgroup.centralizer ({x} : Set G)) ⧸
            GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G)))) * z := by
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← hyq]
      have hwx : Commute (w : G) x := Subgroup.mem_centralizer_singleton_iff.1 w.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hwy : (w : G) * (y : G) = (y : G) * (w : G) := by
        rw [← hk]
        exact (hwx.zpow_right k).eq
      have hwy' : w * y = y * w := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hwy)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hwy']
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcentral _
  exact l93c_false_of_elem hp hL hyX hyN hxN hxo hyo hyx hyc hspade

private theorem l93c_bender {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hO : GLAPPrimeCore p H = ⊥) (hE : CFSG.ComponentClassification.Layer.subgroup H = ⊥)
    (r : H) (hr : ∀ s ∈ CFSG.pCore p H, r * s = s * r) : r ∈ CFSG.pCore p H := by
  have hF : CFSG.ComponentClassification.Fitting.subgroup H = CFSG.pCore p H := by
    unfold CFSG.ComponentClassification.Fitting.subgroup
    exact CFSG.Fitting_eq_pcore H p hO
  have hsub : CFSG.ComponentClassification.GeneralizedFitting.subgroup H = CFSG.pCore p H := by
    rw [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, hE, sup_bot_eq, hF]
  have h1 := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting H
  have hr' : r ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hsub] at hs
    exact (hr s hs).symm
  have h2 := h1 hr'
  rw [hF] at h2
  exact h2

theorem l93_pow_mem_core_of_centMod {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : H92 p B x L)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L,
      ∃ n : ℕ, g ^ (p ^ n) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := h.comp
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := h.norm h.mem
  have hxp : x ^ p = 1 := h.bmax.1.2 x h.mem
  have hxo : orderOf x = p := orderOf_eq_prime hxp h.ne_one
  have hxX : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxmemX : ∀ w ∈ Subgroup.centralizer ({x} : Set G), w * x = x * w :=
    fun w hw => Subgroup.mem_centralizer_singleton_iff.1 hw
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G)))) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p _
  have hOX : GLAPPrimeCore p (↥(Subgroup.centralizer ({x} : Set G)) ⧸
      GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).2 hN
  haveI hLbarn : (barX p (Subgroup.centralizer ({x} : Set G)) L).Normal :=
    Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  haveI hRn : (l93cR p (Subgroup.centralizer ({x} : Set G)) L).Normal := inferInstance
  have hOR : GLAPPrimeCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) = ⊥ :=
    l93c_pPrimeCore_eq_bot_of_normal p hOX
  have hlayer : CFSG.ComponentClassification.Layer.subgroup
      ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) = ⊥ := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    apply le_antisymm _ bot_le
    apply sSup_le
    intro K hK
    exact (l93c_layer_eq_bot hp hp2 hL hN hxN hxo hspade hOR hK).le
  have hbend : ∀ r : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L),
      (∀ s ∈ CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L), r * s = s * r) →
        r ∈ CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) :=
    fun r hr => l93c_bender hOR hlayer r hr
  have hPc : IsCyclic ↥(CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)) := by
    apply l93c_isCyclic_of_elemAbelian hp hp2 (CFSG.pCore_isPGroup)
    intro F hFP hF
    have hE : IsElemAbelian p (F.map (l93cR p (Subgroup.centralizer ({x} : Set G)) L).subtype) :=
      CFSG.SectionRank.isElemAbelian_map hF _
    have hER : F.map (l93cR p (Subgroup.centralizer ({x} : Set G)) L).subtype ≤
        l93cR p (Subgroup.centralizer ({x} : Set G)) L := by
      rintro _ ⟨r, -, rfl⟩
      exact r.2
    have hb := l93c_card_le_of_elemAbelian hp hL hN hspade hER hE
    rwa [Subgroup.card_map_of_injective
      (l93cR p (Subgroup.centralizer ({x} : Set G)) L).subtype_injective] at hb
  set z0 : (↥(Subgroup.centralizer ({x} : Set G)) ⧸ GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) :=
    QuotientGroup.mk' (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) ⟨x, hxX⟩ with hz0def
  have hcommX : ∀ w : ↥(Subgroup.centralizer ({x} : Set G)),
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) w * z0 =
        z0 * QuotientGroup.mk' (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) w := by
    intro w
    rw [hz0def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxmemX w w.2)
  have hz0R : z0 ∈ l93cR p (Subgroup.centralizer ({x} : Set G)) L := by
    apply l93c_mem_cR hxX
    intro l hl hlX
    exact hcommX ⟨l, hlX⟩
  have hz0pow : z0 ^ p = 1 := by
    rw [hz0def, ← map_pow]
    have : (⟨x, hxX⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ^ p = 1 :=
      Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have hz0ne : z0 ≠ 1 := by
    intro h1
    have hw : (⟨x, hxX⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈
        GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G)) := by
      rw [hz0def, QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hpow : (⟨x, hxX⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ^ (p ^ 1) = 1 :=
      Subtype.ext (by simp [hxp])
    exact h.ne_one (congrArg Subtype.val (l93c_eq_one_of_coprime hcop hw hpow))
  set zR : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) := ⟨z0, hz0R⟩ with hzRdef
  have hzR1 : zR ≠ 1 := by
    intro h1
    apply hz0ne
    exact congrArg Subtype.val h1
  have hzRc : ∀ r : ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L), r * zR = zR * r := by
    intro r
    apply Subtype.ext
    obtain ⟨w, hwr⟩ := QuotientGroup.mk'_surjective
      (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G))) (r : _)
    show (r : _) * z0 = z0 * (r : _)
    rw [← hwr]
    exact hcommX w
  have hzPnorm : (Subgroup.zpowers zR).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc' : Commute g zR := hzRc g
    have e : g * zR ^ k * g⁻¹ = zR ^ k := by
      rw [(hc'.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zR) k
  have hzPp : IsPGroup p (Subgroup.zpowers zR) := by
    refine (IsPGroup.iff_card).2 ⟨1, ?_⟩
    have hzRord : orderOf zR = p := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        simpa using hz0pow
      · exact hzR1
    rw [Nat.card_zpowers, hzRord, pow_one]
  have hzP : zR ∈ CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) := by
    have hle : Subgroup.zpowers zR ≤ CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) := by
      unfold CFSG.pCore
      exact le_sSup ⟨hzPnorm, hzPp⟩
    exact hle (Subgroup.mem_zpowers zR)
  haveI : (CFSG.pCore p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L)).Normal :=
    CFSG.pCore_normal
  have hRp : IsPGroup p ↥(l93cR p (Subgroup.centralizer ({x} : Set G)) L) :=
    l93c_isPGroup_of_cyclic hp _ (CFSG.pCore_isPGroup) hPc hzP hzR1 hzRc hbend
  intro g hg
  obtain ⟨hgX, hgM⟩ := Subgroup.mem_inf.1 hg
  have hgR : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Subgroup.centralizer ({x} : Set G)))
      ⟨g, hgX⟩ : _) ∈ l93cR p (Subgroup.centralizer ({x} : Set G)) L :=
    l93c_mem_cR hgX (fun l hl hlX => l93c_mk_comm_of_centMod hp hL hgM hgX l hl hlX)
  obtain ⟨n, hn⟩ := hRp ⟨_, hgR⟩
  have hz : g ^ (p ^ n) ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.pow_mem _ hgX _
  refine ⟨n, l93c_mem_of_mk_eq_one hz ?_⟩
  have hn' := congrArg Subtype.val hn
  have hpow : (⟨g, hgX⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ^ (p ^ n) = ⟨g ^ (p ^ n), hz⟩ :=
    Subtype.ext (by simp)
  rw [← hpow, map_pow]
  simpa using hn'

end CFSG.LocalAnalysis.GLTheoremA.S9
