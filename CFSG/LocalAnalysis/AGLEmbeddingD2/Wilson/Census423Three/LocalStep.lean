module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LocalBasic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

structure GoodAt (d : X) : Prop where
  rad : ∀ N : Subgroup X, N ≤ qRes d → (∀ g ∈ qRes d, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    Group.IsSolvable N → ∀ n ∈ N, ∀ y ∈ qRes d, n * y = y * n
  elt3 : ∃ q ∈ qRes d, q ≠ 1 ∧ q ^ 3 = 1
  noCentral3 : ∀ z ∈ qRes d, (∀ y ∈ qRes d, z * y = y * z) → z ^ 3 = 1 → z = 1
  conj3 : ∀ x ∈ qRes d, ∀ y ∈ qRes d, x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 3 = 1 →
    ∃ g ∈ qRes d, Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers y
  inner3 : ∀ e : X, e ^ 3 = 1 → e ∈ Subgroup.centralizer ({d} : Set X) →
    ∃ q ∈ qRes d, ∀ y ∈ qRes d, ∀ w ∈ qRes d,
      ((q * y * q⁻¹)⁻¹ * (e * y * e⁻¹)) * w = w * ((q * y * q⁻¹)⁻¹ * (e * y * e⁻¹))

theorem step1 (hR : Rank2 X) {D : Subgroup X} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDexp : ∀ x ∈ D, x ^ 3 = 1) (hD9 : Nat.card D = 9) {d : X} (hd : d ∈ D) (hd1 : d ≠ 1)
    (G : GoodAt d) : ∃ e ∈ D, e ∈ qRes d ∧ e ∉ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hDexp d hd) hd1]
  obtain ⟨e₀, he₀, he₀d⟩ : ∃ e₀ ∈ D, e₀ ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers d := hcon
    have := Subgroup.card_le_of_le hle
    omega
  set C := Subgroup.centralizer ({d} : Set X) with hC
  set Q := qRes d with hQ
  have hQC : Q ≤ C := qRes_le d
  have hCmem : ∀ x : X, x ∈ C ↔ x * d = d * x := fun x => Subgroup.mem_centralizer_singleton_iff
  have hDC : ∀ x ∈ D, x ∈ C := fun x hx => (hCmem x).mpr (hDc x hx d hd)
  have he₀C : e₀ ∈ C := hDC e₀ he₀
  have he₀3 : e₀ ^ 3 = 1 := hDexp e₀ he₀
  obtain ⟨q, hq, hqz⟩ := G.inner3 e₀ he₀3 he₀C
  have he₀Q : ∀ y ∈ Q, e₀ * y * e₀⁻¹ ∈ Q := fun y hy => qRes_normalized he₀C hy
  set h : X := q⁻¹ * e₀ with hh
  have hhC : h ∈ C := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQC hq)) he₀C
  have hhfix : ∀ y ∈ Q, h * y * h⁻¹ = y := by
    have key := fixes_of_perfect (MulAut.conj h) Q (qRes_commutator d) ?_ ?_
    · intro y hy
      simpa [MulAut.conj_apply] using key y hy
    · intro y hy
      simp only [MulAut.conj_apply]
      have : h * y * h⁻¹ = q⁻¹ * (e₀ * y * e₀⁻¹) * q := by rw [hh]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq) (he₀Q y hy)) hq
    · intro y hy w hw
      set z := (q * y * q⁻¹)⁻¹ * (e₀ * y * e₀⁻¹) with hzdef
      have hzc : ∀ w' ∈ Q, z * w' = w' * z := fun w' hw' => hqz y hy w' hw'
      have e1 : e₀ * y * e₀⁻¹ = (q * y * q⁻¹) * z := by rw [hzdef]; group
      have hzq : z * q = q * z := hzc q hq
      have hqzq : q⁻¹ * z * q = z := by
        calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
          _ = q⁻¹ * (q * z) := by rw [hzq]
          _ = z := by group
      have e2 : h * y * h⁻¹ = y * z := by
        calc h * y * h⁻¹ = q⁻¹ * (e₀ * y * e₀⁻¹) * q := by rw [hh]; group
          _ = q⁻¹ * ((q * y * q⁻¹) * z) * q := by rw [e1]
          _ = y * (q⁻¹ * z * q) := by group
          _ = y * z := by rw [hqzq]
      have e3 : (MulAut.conj h) y * y⁻¹ = z := by
        simp only [MulAut.conj_apply]
        rw [e2]
        calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [hzc y hy]
          _ = z := by group
      rw [e3]
      exact hzc w hw
  have hhc : ∀ y ∈ Q, h * y = y * h := by
    intro y hy
    have := hhfix y hy
    calc h * y = (h * y * h⁻¹) * h := by group
      _ = y * h := by rw [this]
  have hqh : q * h = h * q := (hhc q hq).symm
  have he₀eq : e₀ = q * h := by rw [hh]; group
  have hcomm : Commute q h := hqh
  have hqh3 : q ^ 3 * h ^ 3 = 1 := by
    have h1 : (q * h) ^ 3 = q ^ 3 * h ^ 3 := hcomm.mul_pow 3
    rw [← h1, ← he₀eq, he₀3]
  set z : X := q ^ 3 with hzdef
  have hzQ : z ∈ Q := Subgroup.pow_mem _ hq 3
  have hzinv : z = (h ^ 3)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact hqh3
  have hzcomm : ∀ y ∈ Q, z * y = y * z := by
    intro y hy
    have hc : Commute (h ^ 3) y := Commute.pow_left (show Commute h y from hhc y hy) 3
    rw [hzinv]
    exact (hc.inv_left).eq
  have ho3 : ¬ 3 ∣ orderOf z := by
    intro h3
    obtain ⟨m, hm⟩ := h3
    set w := z ^ m with hwdef
    have hwQ : w ∈ Q := Subgroup.pow_mem _ hzQ m
    have hwc : ∀ y ∈ Q, w * y = y * w := fun y hy =>
      (Commute.pow_left (hzcomm y hy : z * y = y * z) m)
    have hw3 : w ^ 3 = 1 := by
      rw [hwdef, ← pow_mul, mul_comm, ← hm]
      exact pow_orderOf_eq_one z
    have hw1 : w ≠ 1 := by
      intro h1
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      have hpos := orderOf_pos z
      rw [hm] at hdvd hpos
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    exact hw1 (G.noCentral3 w hwQ hwc hw3)
  set o := orderOf z with ho
  have hmod : o % 3 = 1 ∨ o % 3 = 2 := by omega
  set x : X := q ^ o with hxdef
  set y : X := h ^ o with hydef
  set e₁ : X := e₀ ^ o with he₁def
  have he₁xy : e₁ = x * y := by
    rw [he₁def, he₀eq, hcomm.mul_pow]
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← pow_mul, mul_comm, pow_mul, ← hzdef, ho]
    exact pow_orderOf_eq_one z
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, ← pow_mul, mul_comm, pow_mul, show h ^ 3 = z⁻¹ by rw [hzinv, inv_inv], inv_pow, ho,
      pow_orderOf_eq_one, inv_one]
  have he₀e₁ : e₁ ^ o = e₀ := by
    rw [he₁def, ← pow_mul, pow_eq_pow_mod (o * o) he₀3]
    have : o * o % 3 = 1 := by
      rcases hmod with h1 | h1 <;> simp [Nat.mul_mod, h1]
    rw [this, pow_one]
  have hxQ : x ∈ Q := Subgroup.pow_mem _ hq o
  have hyC : y ∈ C := Subgroup.pow_mem _ hhC o
  have hyc : ∀ w ∈ Q, y * w = w * y := fun w hw =>
    Commute.pow_left (hhc w hw : h * w = w * h) o
  have hyd : y ∈ Subgroup.zpowers d := by
    by_contra hyd
    obtain ⟨q₀, hq₀Q, hq₀1, hq₀3⟩ := G.elt3
    have hdc : ∀ w ∈ Q, d * w = w * d := fun w hw => ((hCmem w).mp (hQC hw)).symm
    have hyd' : d * y = y * d := ((hCmem y).mp hyC).symm
    refine not_rank2_of_three hR (a := d) (b := y) (c := q₀) hyd' (hdc q₀ hq₀Q) (hyc q₀ hq₀Q)
      (hDexp d hd) hy3 hq₀3 hd1 hyd ?_
    intro hmem
    have hcl : Subgroup.closure {d, y} ≤ Subgroup.centralizer (Q : Set X) := by
      rw [Subgroup.closure_le]
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rcases ht with rfl | rfl
      · intro w hw
        exact (hdc w hw).symm
      · intro w hw
        exact (hyc w hw).symm
    have hq₀c := Subgroup.mem_centralizer_iff.mp (hcl hmem)
    exact hq₀1 (G.noCentral3 q₀ hq₀Q (fun w hw => (hq₀c w hw).symm) hq₀3)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyd
  have hyD : y ∈ D := by
    rw [← hk]
    exact Subgroup.zpow_mem _ hd k
  have he₁D : e₁ ∈ D := Subgroup.pow_mem _ he₀ o
  have hxD : x ∈ D := by
    have : x = e₁ * y⁻¹ := by rw [he₁xy]; group
    rw [this]
    exact Subgroup.mul_mem _ he₁D (Subgroup.inv_mem _ hyD)
  refine ⟨x, hxD, hxQ, ?_⟩
  intro hxd
  apply he₀d
  have : e₁ ∈ Subgroup.zpowers d := by
    rw [he₁xy]
    exact Subgroup.mul_mem _ hxd hyd
  rw [← he₀e₁]
  exact Subgroup.pow_mem _ this o

theorem step1_le (hR : Rank2 X) {D : Subgroup X} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDexp : ∀ x ∈ D, x ^ 3 = 1) (hD9 : Nat.card D = 9) {d : X} (hd : d ∈ D) (hd1 : d ≠ 1)
    (G : GoodAt d) : D ≤ Subgroup.zpowers d ⊔ qRes d := by
  obtain ⟨e, heD, heQ, hed⟩ := step1 hR hDc hDexp hD9 hd hd1 G
  rw [← sup_zpowers_eq hDexp hD9 hd hd1 heD hed]
  exact sup_le_sup_left ((Subgroup.zpowers_le).mpr heQ) _

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
