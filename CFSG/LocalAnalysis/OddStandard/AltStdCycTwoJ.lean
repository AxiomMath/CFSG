module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv.Perm AltStdBal
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

private theorem cycJ_le_inf (d : Cyc L Q z) :
    Q ≤ centralizer (L : Set G) ⊓ centralizer ({z} : Set G) :=
  le_inf d.le (le_centralizer_of_mem_isCyclic d.cyclic d.mem)

private theorem cycJ_odd_relIndex (d : Cyc L Q z) :
    ¬ 2 ∣ Q.relIndex (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  intro h2
  apply d.odd_index
  exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q _ (centralizer (L : Set G))
    (cycJ_le_inf d) inf_le_left))

private theorem cycJ_zpowers_eq (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) : zpowers z = Q :=
  Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem) (by rw [hQ2, Nat.card_zpowers, d.order])

private theorem cycJ_ne_one (d : Cyc L Q z) : z ≠ 1 := by
  intro hz
  have := d.order
  rw [hz, orderOf_one] at this
  omega

private theorem cycJ_conj_mem_centralizer {c x : G} (hc : c ∈ normalizer (L : Set G))
    (hx : x ∈ centralizer (L : Set G)) : c * x * c⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have h' : c⁻¹ * h * c ∈ L := by
    have := (mem_normalizer_iff.1 (inv_mem hc) h).1 hh
    simpa using this
  have hxh := mem_centralizer_iff.1 hx _ h'
  calc h * (c * x * c⁻¹) = c * ((c⁻¹ * h * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * h * c)) * c⁻¹ := by rw [hxh]
    _ = c * x * c⁻¹ * h := by group

private theorem cycJ_oddPart_conj_mem (hS : StandardSetting G L) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) {c : G} (hc : c ∈ centralizer ({z} : Set G)) {x : G}
    (hx : x ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))) :
    c * x * c⁻¹ ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G)
  obtain ⟨hXM, -, hXodd, hXQ, hXmul⟩ :=
    oddPart_spec (cycJ_le_inf d) d.pgroup (cycJ_odd_relIndex d) d.cyclic
  have hxM : x ∈ M := hXM hx
  have hyK : c * x * c⁻¹ ∈ centralizer (L : Set G) :=
    cycJ_conj_mem_centralizer (cent_le_normalizer hS d hc) hxM.1
  have hyC : c * x * c⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem hc hxM.2) (inv_mem hc)
  obtain ⟨x', hx', q, hq, hyq⟩ := hXmul _ ⟨hyK, hyC⟩
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with h | h
  · rw [hyq, h, mul_one]
    exact hx'
  · exfalso
    rw [h] at hyq
    have hodd : Odd (orderOf (c * x * c⁻¹)) := by
      have h1 : orderOf x ∣ Nat.card (oddPart M) := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : oddPart M)
        rwa [Subgroup.orderOf_mk] at this
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact Odd.of_dvd_nat hXodd h1
    obtain ⟨j, hj⟩ := hodd
    have hpow : (x' * z) ^ (2 * j + 1) = 1 := by
      rw [← hyq, ← hj]
      exact pow_orderOf_eq_one _
    have hcomm : Commute x' z := mem_centralizer_singleton_iff.1 (hXM hx').2
    have hz2 : z ^ 2 = 1 := by
      rw [← d.order]
      exact pow_orderOf_eq_one z
    have hzm : z ^ (2 * j + 1) = z := by rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [hcomm.mul_pow, hzm] at hpow
    have hzX : z ∈ oddPart M := by
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact inv_mem (pow_mem hx' _)
    have hz1 : z ∈ oddPart M ⊓ Q := ⟨hzX, d.mem⟩
    rw [hXQ] at hz1
    exact cycJ_ne_one d hz1

theorem commutator_centralizer_le_sup (hS : StandardSetting G L)
    (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤
      L ⊔ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G)
  obtain ⟨-, -, -, -, hXmul⟩ :=
    oddPart_spec (cycJ_le_inf d) d.pgroup (cycJ_odd_relIndex d) d.cyclic
  have hCN := cent_le_normalizer hS d
  have hLC := le_cent_single hS d
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G)) hKN
  have caseA : ∀ w ∈ centralizer ({z} : Set G), w ∈ L ⊔ centralizer (L : Set G) →
      ∀ c' ∈ centralizer ({z} : Set G), ⁅w, c'⁆ ∈ L ⊔ oddPart M := by
    intro w hw hwK c' hc'
    have hw' : w ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
      rw [← hm]
      exact hwK
    obtain ⟨l, hl, k, hk, rfl⟩ := Set.mem_mul.1 hw'
    have hkC : k ∈ centralizer ({z} : Set G) := by
      have : k = l⁻¹ * (l * k) := by group
      rw [this]
      exact mul_mem (inv_mem (hLC hl)) hw
    obtain ⟨x, hx, q, hq, rfl⟩ := hXmul k ⟨hk, hkC⟩
    have hqc : q * c' * q⁻¹ = c' := by
      rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with h | h
      · rw [h]
        group
      · rw [h, ← mem_centralizer_singleton_iff.1 hc']
        group
    have h1 : ⁅l * (x * q), c'⁆ = l * (x * (c' * x⁻¹ * c'⁻¹)) * (c' * l⁻¹ * c'⁻¹) := by
      calc ⁅l * (x * q), c'⁆ = l * x * (q * c' * q⁻¹) * x⁻¹ * l⁻¹ * c'⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = l * x * c' * x⁻¹ * l⁻¹ * c'⁻¹ := by rw [hqc]
        _ = l * (x * (c' * x⁻¹ * c'⁻¹)) * (c' * l⁻¹ * c'⁻¹) := by group
    rw [h1]
    refine mul_mem (mul_mem (mem_sup_left hl) (mem_sup_right (mul_mem hx ?_))) (mem_sup_left ?_)
    · exact cycJ_oddPart_conj_mem hS d hQ2 hc' (inv_mem hx)
    · exact (mem_normalizer_iff.1 (hCN hc') l⁻¹).1 (inv_mem hl)
  have hsgn : ∀ y (hy : y ∈ centralizer ({z} : Set G)), y ∉ L ⊔ centralizer (L : Set G) →
      sign (rho θ hn ⟨y, hCN hy⟩) = -1 := by
    intro y hy hyK
    rcases Int.units_eq_one_or (sign (rho θ hn ⟨y, hCN hy⟩)) with h | h
    · exact absurd (mem_sup_of_rho_mem θ hn (hCN hy) (mem_alternatingGroup.2 h)) hyK
    · exact h
  rw [Subgroup.commutator_le]
  intro c hc c' hc'
  by_cases hcK : c ∈ L ⊔ centralizer (L : Set G)
  · exact caseA c hc hcK c' hc'
  by_cases hcK' : c' ∈ L ⊔ centralizer (L : Set G)
  · rw [← commutatorElement_inv]
    exact inv_mem (caseA c' hc' hcK' c hc)
  have hwC : c' * c⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hc' (inv_mem hc)
  have hwK : c' * c⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
    refine mem_sup_of_rho_mem θ hn (hCN hwC) ?_
    have h1 : (⟨c' * c⁻¹, hCN hwC⟩ : normalizer (L : Set G)) =
        ⟨c', hCN hc'⟩ * ⟨c, hCN hc⟩⁻¹ := rfl
    rw [mem_alternatingGroup, h1, map_mul, map_inv, map_mul, map_inv, hsgn c' hc' hcK',
      hsgn c hc hcK]
    decide
  have h2 : ⁅c, c'⁆ = ⁅c' * c⁻¹, c⁆⁻¹ := by
    rw [commutatorElement_inv]
    simp only [commutatorElement_def]
    group
  rw [h2]
  exact inv_mem (caseA _ hwC hwK c hc)

theorem not_J_z (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) : ¬ J z := by
  intro hJ
  have hzX := commutator_centralizer_le_sup hS θ hn d hQ2 hJ
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G)
  obtain ⟨hXM, -, -, hXQ, -⟩ :=
    oddPart_spec (cycJ_le_inf d) d.pgroup (cycJ_odd_relIndex d) d.cyclic
  have hXN : oddPart M ≤ normalizer (L : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _ (hXM hx).1
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (oddPart M) hXN
  have hz' : z ∈ (L : Set G) * (oddPart M : Set G) := by
    rw [← hm]
    exact hzX
  obtain ⟨l, hl, x, hx, hlx⟩ := Set.mem_mul.1 hz'
  have hlK : l ∈ centralizer (L : Set G) := by
    have : l = z * x⁻¹ := by rw [← hlx]; group
    rw [this]
    exact mul_mem (d.le d.mem) (inv_mem (hXM hx).1)
  have hl1 : l = 1 := eq_one_of_mem_of_mem_centralizer θ (by omega) hl hlK
  rw [hl1, one_mul] at hlx
  have hzO : z ∈ oddPart M := by
    rw [← hlx]
    exact hx
  have hz1 : z ∈ oddPart M ⊓ Q := ⟨hzO, d.mem⟩
  rw [hXQ] at hz1
  exact cycJ_ne_one d hz1

private theorem cycJ_J_of_mem (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {y : G}
    (hy : y ∈ L) (hy2 : orderOf y = 2) : J y := by
  have ha2 : orderOf (θ ⟨y, hy⟩ : alternatingGroup (Fin n)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
  have hJ := mem_commutator_centralizer_of_involution (α := Fin n) (by simpa using hn) ha2
  have := J_map (L.subtype.comp θ.symm.toMonoidHom) hJ
  simpa using this

theorem not_conj_mem_L (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (g : G) : g * z * g⁻¹ ∉ L := by
  intro hg
  have h2 : orderOf (g * z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact d.order
  exact not_J_z hS θ hn d hQ2 ((J_conj g).1 (cycJ_J_of_mem θ hn hg h2))

theorem exists_eq_of_two_pow (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hcL : c ∈ L ⊔ centralizer (L : Set G)) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) : ∃ l ∈ L, c = l ∨ c = l * z := by
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G)) hKN
  have hc' : c ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hm]
    exact hcL
  obtain ⟨l, hl, w, hw, rfl⟩ := Set.mem_mul.1 hc'
  have hwC : w ∈ centralizer ({z} : Set G) := by
    have : w = l⁻¹ * (l * w) := by group
    rw [this]
    exact mul_mem (inv_mem (le_cent_single hS d hl)) hc
  have hlw : Commute l w := mem_centralizer_iff.1 hw l hl
  rw [hlw.mul_pow] at hck
  have hw1 : w ^ 2 ^ k = 1 := by
    have hlK : l ^ 2 ^ k ∈ centralizer (L : Set G) := by
      rw [eq_inv_of_mul_eq_one_left hck]
      exact inv_mem (pow_mem hw _)
    have h1 := eq_one_of_mem_of_mem_centralizer θ (by omega) (pow_mem hl _) hlK
    rw [h1, one_mul] at hck
    exact hck
  have hwz := mem_zpowers_of_two_pow d hQ2 ⟨hw, hwC⟩ hw1
  rw [cycJ_zpowers_eq d hQ2] at hwz
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hwz with h | h
  · exact ⟨l, hl, Or.inl (by rw [h, mul_one])⟩
  · exact ⟨l, hl, Or.inr (by rw [h])⟩

end CFSG.OddStandard.AltStdCycTwo
