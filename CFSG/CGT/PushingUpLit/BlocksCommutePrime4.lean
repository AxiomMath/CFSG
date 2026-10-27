module

public import CFSG.CGT.PushingUpLit.BlocksCommutePrime3
public import CFSG.CGT.PushingUpLit.BlocksCommutePrime2

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_aux_left {a b x : G} (hb : b * x = x * b) : ⁅a * b⁻¹, x⁆ = ⁅a, x⁆ := by
  have h := (show Commute b⁻¹ x from (show Commute b x from hb).inv_left).eq
  simp only [commutatorElement_def]
  calc a * b⁻¹ * x * (a * b⁻¹)⁻¹ * x⁻¹ = a * (b⁻¹ * x) * b * a⁻¹ * x⁻¹ := by group
    _ = a * (x * b⁻¹) * b * a⁻¹ * x⁻¹ := by rw [h]
    _ = a * x * a⁻¹ * x⁻¹ := by group

theorem comm_aux_right {a b x : G} (ha : a * x = x * a) (hac : a * ⁅b, x⁆ = ⁅b, x⁆ * a) :
    ⁅a * b, x⁆ = ⁅b, x⁆ := by
  have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅a, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 ha
  rw [e, h1, mul_one, hac]
  group

theorem comm_aux_both {a b x : G} (ha : a * x = x * a) (hb : b * x = x * b) : ⁅a * b⁻¹, x⁆ = 1 := by
  rw [comm_aux_left hb]
  exact commutatorElement_eq_one_iff_mul_comm.2 ha

variable [Finite G]

theorem commutator_pCore_mem_blockU {Y : Subgroup G} (hY : IsBlockOf Y) {q : G}
    (hq : q ∈ pCore 2 G) : ∀ l ∈ Y, ⁅q, l⁆ ∈ blockU Y :=
  commutator_mem_blockU hY (fun _ hl => commutator_mem_oTwoIn hY hq hl)

theorem blockU_le_pCore {X : Subgroup G} (hX : IsBlockOf X) : blockU X ≤ pCore 2 G :=
  (blockU_le_oTwoIn X).trans (oTwoIn_le_pCore hX.1)

theorem normalizes_of_prime {X Y : Subgroup G} (hX : IsBlockOf X) (hY : IsBlockOf Y) {p : ℕ}
    (hprime : p.Prime) (hXp : Nat.card (↥X ⧸ pCore 2 ↥X) = p)
    (hYp : Nat.card (↥Y ⧸ pCore 2 ↥Y) = p)
    (hcomm : ∀ g₁ ∈ Y, ∀ g₂ ∈ Y, conjSub g₁ X ≠ conjSub g₂ X → ⁅conjSub g₁ X, conjSub g₂ X⁆ = ⊥)
    {y : G} (hy : y ∈ Y) (hyo : orderOf y = p) : y ∈ Subgroup.normalizer (X : Set G) := by
  by_contra hyn
  obtain ⟨x, hx, hxo⟩ := exists_orderOf_eq_of_prime_top hprime hXp
  have dX := isPrimeBlockData_of hX.2 hprime hXp hx hxo
  have dY := isPrimeBlockData_of hY.2 hprime hYp hy hyo
  have hp3 : 3 ≤ p := by
    have := hprime.two_le
    have := dX.odd
    omega
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hc1 : ∀ i : ℕ, i % p ≠ 0 → ∀ a ∈ conjSub (y ^ i) X, ∀ g ∈ X, a * g = g * a := by
    intro i hi a ha g hg
    exact orbit_commute hprime hy hyo hyn hcomm (i := i) (j := 0)
      (by simpa using hi) a ha g (by rw [pow_zero, conjSub_one]; exact hg)
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have h1ne : 1 % p ≠ 0 := by rw [hmod1]; exact one_ne_zero
  have hsucc : ∀ i : ℕ, i % p = 0 → (i + 1) % p = 1 := fun i h0 => by
    rw [Nat.add_mod, h0, hmod1, zero_add, hmod1]
  obtain ⟨u, huU, hune⟩ : ∃ u ∈ blockU X, y * u * y⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    have hUle : blockU X ≤ Subgroup.centralizer (X : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hu1 : y * u * y⁻¹ ∈ conjSub y X := conj_mem_conjSub (blockU_le X hu)
      rw [hcon u hu] at hu1
      have hu2 : u ∈ conjSub (y ^ 1) X := by rw [pow_one]; exact hu1
      exact (hc1 1 h1ne u hu2 g hg).symm
    have hle : blockU X ≤ blockZ X := fun u hu => Subgroup.mem_inf.2 ⟨hu, hUle hu⟩
    rw [dX.blockZ_eq] at hle
    exact blockU_ne_bot_of_short hX.2 (le_bot_iff.1 hle)
  obtain ⟨w, hwdef⟩ : ∃ w, w = u * (y * u * y⁻¹)⁻¹ := ⟨_, rfl⟩
  have hw1 : w ≠ 1 := by
    intro h
    rw [hwdef, mul_inv_eq_one] at h
    exact hune h.symm
  have hwW : w ∈ blockU Y := by
    have := commutator_pCore_mem_blockU hY (blockU_le_pCore hX huU) y hy
    have e : u * (y * u * y⁻¹)⁻¹ = ⁅u, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hwdef, e]
    exact this
  let N : Subgroup G := Subgroup.closure (Set.range fun i : ℕ => y ^ i * w * (y ^ i)⁻¹)
  have hNW : N ≤ blockU Y := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact conj_mem_blockU (Subgroup.le_normalizer (pow_mem hy i)) hwW
  have hNy : ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine Subgroup.subset_closure ⟨i + 1, ?_⟩
      group
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ha
  have hwN : w ∈ N := Subgroup.subset_closure ⟨0, by simp⟩
  have hNeq : N = blockU Y := by
    rcases dY.irr N hNW hNy with h | h
    · exfalso
      apply hw1
      have : w ∈ (⊥ : Subgroup G) := h ▸ hwN
      exact this
    · exact h
  obtain ⟨ui, huidef⟩ : ∃ ui : ℕ → G, ∀ i, ui i = y ^ i * u * (y ^ i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hui_conjSub : ∀ i, ui i ∈ conjSub (y ^ i) X := fun i => by
    rw [huidef]
    exact conj_mem_conjSub (blockU_le X huU)
  have hcX : ∀ i, i % p ≠ 0 → ∀ g ∈ X, ui i * g = g * ui i :=
    fun i hi g hg => hc1 i hi _ (hui_conjSub i) g hg
  have hui0 : ∀ i, i % p = 0 → ui i = u := by
    intro i hi
    have : y ^ i = 1 := by rw [← pow_mod_orderOf, hyo, hi, pow_zero]
    rw [huidef, this]
    simp
  have hcU : ∀ i, ∀ v ∈ blockU X, ui i * v = v * ui i := by
    intro i v hv
    by_cases hi : i % p = 0
    · rw [hui0 i hi]
      exact blockU_commute hX.2 huU hv
    · exact hcX i hi v (blockU_le X hv)
  have hgen : ∀ i : ℕ, y ^ i * w * (y ^ i)⁻¹ = ui i * (ui (i + 1))⁻¹ := by
    intro i
    rw [huidef, huidef, hwdef]
    group
  have hWU : ∀ v ∈ blockU Y, ∀ u' ∈ blockU X, v * u' = u' * v := by
    intro v hv u' hu'
    have hle : N ≤ Subgroup.centralizer (blockU X : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro t ht
      show t * (y ^ i * w * (y ^ i)⁻¹) = (y ^ i * w * (y ^ i)⁻¹) * t
      rw [hgen i]
      have c1 : Commute (ui i) t := hcU i t (SetLike.mem_coe.1 ht)
      have c2 : Commute (ui (i + 1)) t := hcU (i + 1) t (SetLike.mem_coe.1 ht)
      exact (c1.mul_left c2.inv_left).eq.symm
    rw [← hNeq] at hv
    exact (Subgroup.mem_centralizer_iff.1 (hle hv) u' hu').symm
  obtain ⟨e₀, he₀def⟩ : ∃ e₀, e₀ = ⁅u, x⁆ := ⟨_, rfl⟩
  have he₀U : e₀ ∈ blockU X := he₀def ▸ commutator_mem_blockU_left huU hx
  have hQ : ∀ v ∈ blockU Y, ∀ g ∈ X, ⁅v, g⁆ ∈ blockU X :=
    fun v hv g hg => commutator_pCore_mem_blockU hX (blockU_le_pCore hY hv) g hg
  let S : Subgroup G :=
    { carrier := {v | v ∈ blockU Y ∧ ⁅v, x⁆ ∈ Subgroup.zpowers e₀}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro v v' ⟨hv, hvz⟩ ⟨hv', hv'z⟩
        refine ⟨mul_mem hv hv', ?_⟩
        have hc : v * ⁅v', x⁆ = ⁅v', x⁆ * v := hWU v hv _ (hQ v' hv' x hx)
        have e : ⁅v * v', x⁆ = v * ⁅v', x⁆ * v⁻¹ * ⁅v, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hc]
        have e' : ⁅v', x⁆ * v * v⁻¹ * ⁅v, x⁆ = ⁅v', x⁆ * ⁅v, x⁆ := by group
        rw [e']
        exact mul_mem hv'z hvz
      inv_mem' := by
        rintro v ⟨hv, hvz⟩
        refine ⟨inv_mem hv, ?_⟩
        have hc : v * ⁅v, x⁆ = ⁅v, x⁆ * v := hWU v hv _ (hQ v hv x hx)
        have e : ⁅v⁻¹, x⁆ = v⁻¹ * ⁅v, x⁆⁻¹ * v := by
          simp only [commutatorElement_def]
          group
        have e2 : v⁻¹ * ⁅v, x⁆⁻¹ * v = ⁅v, x⁆⁻¹ := by
          have h2 : v * ⁅v, x⁆⁻¹ = ⁅v, x⁆⁻¹ * v :=
            (show Commute v ⁅v, x⁆ from hc).inv_right.eq
          calc v⁻¹ * ⁅v, x⁆⁻¹ * v = v⁻¹ * (⁅v, x⁆⁻¹ * v) := by group
            _ = v⁻¹ * (v * ⁅v, x⁆⁻¹) := by rw [h2]
            _ = ⁅v, x⁆⁻¹ := by group
        rw [e, e2]
        exact inv_mem hvz }
  have hgenS : ∀ i : ℕ, y ^ i * w * (y ^ i)⁻¹ ∈ S := by
    intro i
    refine ⟨conj_mem_blockU (Subgroup.le_normalizer (pow_mem hy i)) hwW, ?_⟩
    rw [hgen i]
    by_cases h0 : i % p = 0
    · have h1 : (i + 1) % p ≠ 0 := by rw [hsucc i h0]; exact one_ne_zero
      rw [hui0 i h0, comm_aux_left (hcX (i + 1) h1 x hx), ← he₀def]
      exact Subgroup.mem_zpowers _
    · by_cases h1 : (i + 1) % p = 0
      · rw [hui0 (i + 1) h1]
        have hxi : ui i * x = x * ui i := hcX i h0 x hx
        have hcu : ui i * ⁅u⁻¹, x⁆ = ⁅u⁻¹, x⁆ * ui i :=
          hcU i _ (commutator_mem_blockU_left (inv_mem huU) hx)
        have e1 : ⁅u⁻¹, x⁆ = e₀⁻¹ := by
          have hc : u * e₀ = e₀ * u := blockU_commute hX.2 huU he₀U
          have e3 : ⁅u⁻¹, x⁆ = u⁻¹ * ⁅u, x⁆⁻¹ * u := by
            simp only [commutatorElement_def]
            group
          rw [e3, ← he₀def]
          have h2 : u * e₀⁻¹ = e₀⁻¹ * u := (show Commute u e₀ from hc).inv_right.eq
          calc u⁻¹ * e₀⁻¹ * u = u⁻¹ * (e₀⁻¹ * u) := by group
            _ = u⁻¹ * (u * e₀⁻¹) := by rw [h2]
            _ = e₀⁻¹ := by group
        rw [comm_aux_right hxi hcu, e1]
        exact inv_mem (Subgroup.mem_zpowers _)
      · rw [comm_aux_both (hcX i h0 x hx) (hcX (i + 1) h1 x hx)]
        exact one_mem _
  have hWS : blockU Y ≤ S := by
    rw [← hNeq]
    exact (Subgroup.closure_le S).2 (by rintro _ ⟨i, rfl⟩; exact hgenS i)
  have hall : ∀ u' ∈ blockU X, ⁅u', x⁆ ∈ Subgroup.zpowers e₀ := by
    intro u' hu'
    have hyW : ⁅u', y⁆ ∈ blockU Y :=
      commutator_pCore_mem_blockU hY (blockU_le_pCore hX hu') y hy
    have hS : ⁅u', y⁆ ∈ S := hWS hyW
    have hb : (y * u' * y⁻¹) * x = x * (y * u' * y⁻¹) := by
      have hmem : y * u' * y⁻¹ ∈ conjSub (y ^ 1) X := by
        rw [pow_one]
        exact conj_mem_conjSub (blockU_le X hu')
      exact hc1 1 h1ne _ hmem x hx
    have e : ⁅u', y⁆ = u' * (y * u' * y⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have := hS.2
    rw [e, comm_aux_left hb] at this
    exact this
  have hUle : blockU X ≤ Subgroup.zpowers e₀ := by
    intro v hv
    obtain ⟨u', hu', rfl⟩ := dX.surj v hv
    exact hall u' hu'
  exact dX.not_le_zpowers e₀ he₀U hUle

end CFSG.CGT.PushingUpLit
