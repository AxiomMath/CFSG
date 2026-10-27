module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.GLS.Stage4.Q9

namespace Sylow5

open Subgroup

section General

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g
    (show SemiconjBy g x (g * x * g⁻¹) by simp [SemiconjBy, mul_assoc])).symm

theorem eq_one_of_cube_eq_one (v : ZMod 5) (h : v * v * v = 1) : v = 1 := by
  revert v h; decide

theorem aut3 {x δ : G} (hx : orderOf x = 5) (hδ : δ ^ 3 = 1) {s t : ℕ} (hs : ¬ 5 ∣ s)
    (h : δ * x ^ s * δ⁻¹ = x ^ t) : δ * x * δ⁻¹ = x := by
  have hcop : s.Coprime (orderOf x) := by
    rw [hx]; exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hs).symm
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  have h1 : δ * x * δ⁻¹ = x ^ (t * u) := by
    calc δ * x * δ⁻¹ = δ * (x ^ s) ^ u * δ⁻¹ := by rw [hu]
      _ = (δ * x ^ s * δ⁻¹) ^ u := conj_pow.symm
      _ = x ^ (t * u) := by rw [h, ← pow_mul]
  generalize t * u = w at h1
  have h2 : δ * x ^ w * δ⁻¹ = x ^ (w * w) := by
    rw [← conj_pow, h1, ← pow_mul]
  have h3 : δ * x ^ (w * w) * δ⁻¹ = x ^ (w * w * w) := by
    rw [← conj_pow, h1, ← pow_mul, mul_assoc]
  have h4 : δ * (δ * (δ * x * δ⁻¹) * δ⁻¹) * δ⁻¹ = x := by
    have e : δ * δ * δ = 1 := by rw [← pow_three']; exact hδ
    have : δ * (δ * (δ * x * δ⁻¹) * δ⁻¹) * δ⁻¹ = (δ * δ * δ) * x * (δ * δ * δ)⁻¹ := by group
    rw [this, e]; simp
  rw [h1, h2, h3] at h4
  have h6 : (1 : ℕ) ≡ w * w * w [MOD orderOf x] := by
    rw [← pow_eq_pow_iff_modEq]; simpa using h4.symm
  rw [hx] at h6
  have h7 : ((w : ℕ) : ZMod 5) = 1 := by
    apply eq_one_of_cube_eq_one
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h6.symm
    simpa using this
  have h8 : w ≡ 1 [MOD 5] := by
    rw [← ZMod.natCast_eq_natCast_iff]; simpa using h7
  rw [h1, show x ^ w = x ^ 1 from (pow_eq_pow_iff_modEq.2 (by rw [hx]; exact h8))]
  simp

theorem not_commute_of_mem_zpowers [Finite G] {a δ h : G} (ha3 : orderOf a = 3)
    (hδ : δ ∈ zpowers a) (hδ1 : δ ≠ 1) (hh : a * h * a⁻¹ ≠ h) : δ * h * δ⁻¹ ≠ h := by
  intro hc
  apply hh
  have hdvd : orderOf δ ∣ 3 := ha3 ▸ orderOf_dvd_of_mem_zpowers hδ
  have hne : orderOf δ ≠ 1 := fun h1 => hδ1 (orderOf_eq_one_iff.1 h1)
  have h3 : orderOf δ = 3 := ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left hne
  have hle : zpowers δ ≤ zpowers a := (Subgroup.zpowers_le).2 hδ
  have heq : zpowers δ = zpowers a := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, h3, ha3]
  have ha : a ∈ zpowers δ := heq ▸ mem_zpowers a
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hcomm : Commute δ h := by
    show δ * h = h * δ
    calc δ * h = δ * h * δ⁻¹ * δ := by group
      _ = h * δ := by rw [hc]
  rw [← he]
  exact (hcomm.zpow_left e).mul_inv_cancel

theorem card_dvd_of_le_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {H U : Subgroup G} (hU : U ≤ H)
    (hp : IsPGroup p U) : Nat.card U ∣ p ^ (Nat.card H).factorization p := by
  have hp' : IsPGroup p (U.subgroupOf H) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hU).symm
  obtain ⟨Q, hQ⟩ := hp'.exists_le_sylow
  have h1 : Nat.card (U.subgroupOf H) ∣ Nat.card Q := Subgroup.card_dvd_of_le hQ
  rw [Q.card_eq_multiplicity] at h1
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv] at h1

theorem exists_mem_normalizer {p : ℕ} [Fact p.Prime] [Finite G] {R T : Subgroup G}
    (hT : IsPGroup p T) (hRT : R < T) :
    ∃ n ∈ T, n ∉ R ∧ ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hlt : R.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    have : T ≤ R := by
      intro t ht
      have : (⟨t, ht⟩ : T) ∈ R.subgroupOf T := h ▸ mem_top _
      exact this
    exact absurd hRT (not_lt_of_ge this)
  have hnc := (Group.normalizerCondition_of_isNilpotent (G := T)) _ hlt
  obtain ⟨n, hn, hn'⟩ := IsConcreteLE.exists_of_lt hnc
  refine ⟨(n : G), n.2, hn', ?_⟩
  intro r hr
  exact (Subgroup.mem_normalizer_iff.1 hn ⟨r, hRT.le hr⟩).1 hr

theorem pow_not_mem_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {R T : Subgroup G}
    (hT : IsPGroup p T) {n : G} (hn : n ∈ T) (hnR : n ∉ R) {e : ℕ} (he0 : 0 < e) (hep : e < p) :
    n ^ e ∉ R := by
  intro hpow
  obtain ⟨k, hk⟩ := hT.exists_orderOf_eq_pow ⟨n, hn⟩
  have hk' : orderOf n = p ^ k := by rw [← Subgroup.orderOf_mk n hn]; exact hk
  have hcop : e.Coprime (orderOf n) := by
    rw [hk']
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 (Nat.not_dvd_of_pos_of_lt he0 hep)).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hnR (hm ▸ R.pow_mem hpow m)

theorem conj_rewrite {g₁ g₂ y y' : G} (E : g₁ * y * g₁⁻¹ = g₂ * y' * g₂⁻¹) :
    y = (g₁⁻¹ * g₂) * y' * (g₁⁻¹ * g₂)⁻¹ := by
  calc y = g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ := by group
    _ = g₁⁻¹ * (g₂ * y' * g₂⁻¹) * g₁ := by rw [E]
    _ = (g₁⁻¹ * g₂) * y' * (g₁⁻¹ * g₂)⁻¹ := by group

theorem pow_conj_mem {a : G} {R : Subgroup G} (hRa : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (m : ℕ) :
    ∀ r ∈ R, a ^ m * r * (a ^ m)⁻¹ ∈ R := by
  induction m with
  | zero => intro r hr; simpa using hr
  | succ m ih =>
    intro r hr
    have := hRa _ (ih r hr)
    rwa [show a * (a ^ m * r * (a ^ m)⁻¹) * a⁻¹ = a ^ (m + 1) * r * (a ^ (m + 1))⁻¹ by
      rw [pow_succ']; group] at this

theorem injective_option {R ι : Type*} [One R] (f : ι → R) (hf : Function.Injective f)
    (h1 : ∀ p, f p ≠ 1) : Function.Injective (fun o : Option ι => o.elim 1 f) := by
  intro o o' h
  rcases o with _ | p <;> rcases o' with _ | p'
  · rfl
  · exact absurd h.symm (h1 p')
  · exact absurd h (h1 p)
  · exact congrArg some (hf h)

theorem exists_eq_of_injective_of_card {R ι : Type*} [One R] [Finite R] [Fintype ι] (f : ι → R)
    (hf : Function.Injective f) (h1 : ∀ p, f p ≠ 1) (hc : Fintype.card ι + 1 = Nat.card R)
    (r : R) (hr : r ≠ 1) : ∃ p, f p = r := by
  have hbij : Function.Bijective (fun o : Option ι => o.elim 1 f) := by
    apply (injective_option f hf h1).bijective_of_nat_card_le
    rw [Nat.card_eq_fintype_card (α := Option ι), Fintype.card_option, hc]
  obtain ⟨o, ho⟩ := hbij.2 r
  rcases o with _ | p
  · exact absurd ho.symm hr
  · exact ⟨p, ho⟩

theorem false_of_injective_of_card {R ι : Type*} [One R] [Finite R] [Fintype ι] (f : ι → R)
    (hf : Function.Injective f) (h1 : ∀ p, f p ≠ 1) (hc : Nat.card R ≤ Fintype.card ι) :
    False := by
  have := Nat.card_le_card_of_injective _ (injective_option f hf h1)
  rw [Nat.card_eq_fintype_card, Fintype.card_option] at this
  omega

theorem card_five_torsion :
    Nat.card {m : Multiplicative (ZMod 10) × Multiplicative (ZMod 10) // m ^ 5 = 1} = 25 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem exists_R {Hs : Subgroup G}
    (hHs : Nonempty (↥Hs ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10))) :
    ∃ R : Subgroup G, R ≤ Hs ∧ Nat.card R = 25 ∧ (∀ r ∈ R, r ^ 5 = 1) ∧
      (∀ g ∈ Hs, g ^ 5 = 1 → g ∈ R) := by
  obtain ⟨φ⟩ := hHs
  have hcomm : ∀ g ∈ Hs, ∀ h ∈ Hs, g * h = h * g := by
    intro g hg h hh
    have := φ.injective (a₁ := (⟨g, hg⟩ : Hs) * ⟨h, hh⟩) (a₂ := (⟨h, hh⟩ : Hs) * ⟨g, hg⟩)
      (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val this
  let R : Subgroup G :=
    { carrier := {g | g ∈ Hs ∧ g ^ 5 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha5⟩ ⟨hb, hb5⟩
        exact ⟨Hs.mul_mem ha hb, by rw [Commute.mul_pow (hcomm a ha b hb), ha5, hb5, one_mul]⟩
      one_mem' := ⟨Hs.one_mem, one_pow _⟩
      inv_mem' := by
        rintro a ⟨ha, ha5⟩
        exact ⟨Hs.inv_mem ha, by rw [inv_pow, ha5, inv_one]⟩ }
  refine ⟨R, fun g hg => hg.1, ?_, fun r hr => hr.2, fun g hg h5 => ⟨hg, h5⟩⟩
  rw [← card_five_torsion]
  refine Nat.card_congr
    { toFun := fun r => ⟨φ ⟨r.1, r.2.1⟩, by
        rw [← map_pow]
        have : (⟨r.1, r.2.1⟩ : Hs) ^ 5 = 1 := Subtype.ext r.2.2
        rw [this, map_one]⟩
      invFun := fun m => ⟨((φ.symm m.1 : Hs) : G), (φ.symm m.1).2, by
        have : (φ.symm m.1) ^ 5 = 1 := by rw [← map_pow, m.2, map_one]
        exact congrArg Subtype.val this⟩
      left_inv := fun r => Subtype.ext (by simp)
      right_inv := fun m => Subtype.ext (by simp) }

theorem exists_conj_mem_sylow {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G) {g : G}
    (hg : IsPGroup p (zpowers g)) : ∃ h s : G, s ∈ (P : Subgroup G) ∧ h * s * h⁻¹ = g := by
  obtain ⟨P', hP'⟩ := hg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P P'
  have hgP' : g ∈ (P' : Subgroup G) := hP' (mem_zpowers g)
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hgP'
  obtain ⟨s, hs, hsg⟩ := hgP'
  exact ⟨h, s, hs, hsg⟩

end General

section TISection

variable {G : Type*} [Group G]

structure TI (z : G) (K : Fin 2 → Subgroup G) : Prop where
  orderOf_z : orderOf z = 2
  le : ∀ i, K i ≤ centralizer {z}
  inter : K 0 ⊓ K 1 = zpowers z
  norm : ∀ i, ∀ c ∈ centralizer {z}, ∀ k ∈ K i, c * k * c⁻¹ ∈ K i
  cent : ∀ x : G, (∃ i, x ∈ K i) → orderOf x = 5 →
    centralizer {x} ≤ centralizer {z} ∧
    ∀ e : G, e ∈ centralizer {x} → orderOf e = 2 → (∀ c ∈ centralizer {x}, e * c = c * e) → e = z

theorem TI.conj {z : G} {K : Fin 2 → Subgroup G} (hT : TI z K) {i i' : Fin 2} {u g : G}
    (hu : u ∈ K i) (h5 : orderOf u = 5) (hv : g * u * g⁻¹ ∈ K i') :
    i = i' ∧ g ∈ centralizer {z} := by
  have huC : u ∈ centralizer {z} := hT.le i hu
  obtain ⟨hu1, -⟩ := hT.cent u ⟨i, hu⟩ h5
  have hv5 : orderOf (g * u * g⁻¹) = 5 := by rw [orderOf_conj_eq]; exact h5
  obtain ⟨-, hv2⟩ := hT.cent (g * u * g⁻¹) ⟨i', hv⟩ hv5
  have hgz : g * z * g⁻¹ = z := by
    apply hv2
    · rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 huC
      calc g * z * g⁻¹ * (g * u * g⁻¹) = g * (z * u) * g⁻¹ := by group
        _ = g * (u * z) * g⁻¹ := by rw [this]
        _ = g * u * g⁻¹ * (g * z * g⁻¹) := by group
    · rw [orderOf_conj_eq, hT.orderOf_z]
    · intro c hc
      rw [mem_centralizer_singleton_iff] at hc
      have hw : g⁻¹ * c * g ∈ centralizer {u} := by
        rw [mem_centralizer_singleton_iff]
        calc g⁻¹ * c * g * u = g⁻¹ * (c * (g * u * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * u * g⁻¹) * c) * g := by rw [hc]
          _ = u * (g⁻¹ * c * g) := by group
      have hwz : g⁻¹ * c * g ∈ centralizer {z} := hu1 hw
      have := mem_centralizer_singleton_iff.1 hwz
      calc g * z * g⁻¹ * c = g * (z * (g⁻¹ * c * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * c * g) * z) * g⁻¹ := by rw [this]
        _ = c * (g * z * g⁻¹) := by group
  have hgC : g ∈ centralizer {z} := by
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hgz]
  refine ⟨?_, hgC⟩
  by_contra hne
  have h1 : g * u * g⁻¹ ∈ K i := hT.norm i g hgC u hu
  have hmem : g * u * g⁻¹ ∈ K 0 ⊓ K 1 := by
    fin_cases i <;> fin_cases i'
    · exact absurd rfl hne
    · exact ⟨h1, hv⟩
    · exact ⟨hv, h1⟩
    · exact absurd rfl hne
  rw [hT.inter] at hmem
  have hd := orderOf_dvd_of_mem_zpowers hmem
  rw [hv5, hT.orderOf_z] at hd
  omega

structure Data (z : G) (K : Fin 2 → Subgroup G) (x : Fin 2 → G) (R : Subgroup G) : Prop where
  ti : TI z K
  mem : ∀ i, x i ∈ K i
  order : ∀ i, orderOf (x i) = 5
  memR : ∀ i, x i ∈ R
  card : Nat.card R = 25

section DataLemmas

variable {z : G} {K : Fin 2 → Subgroup G} {x : Fin 2 → G} {R : Subgroup G}

theorem Data.orderOf_pow (D : Data z K x R) (i : Fin 2) (j : Fin 4) :
    orderOf (x i ^ ((j : ℕ) + 1)) = 5 := by
  have hj := j.2
  have hc : (orderOf (x i)).Coprime ((j : ℕ) + 1) := by
    rw [D.order i, Nat.Prime.coprime_iff_not_dvd Nat.prime_five]; omega
  rw [Nat.Coprime.orderOf_pow hc, D.order i]

theorem Data.pow_ne_one (D : Data z K x R) (i : Fin 2) (j : Fin 4) :
    x i ^ ((j : ℕ) + 1) ≠ 1 := by
  intro h
  have := D.orderOf_pow i j
  rw [h, orderOf_one] at this
  omega

theorem Data.pow_mem (D : Data z K x R) (i : Fin 2) (j : Fin 4) : x i ^ ((j : ℕ) + 1) ∈ K i :=
  (K i).pow_mem (D.mem i) _

theorem Data.ne_one (D : Data z K x R) (i : Fin 2) : x i ≠ 1 := by
  intro h
  have := D.order i
  rw [h, orderOf_one] at this
  omega

theorem Data.pow_injective (D : Data z K x R) (i : Fin 2) {j j' : Fin 4}
    (h : x i ^ ((j : ℕ) + 1) = x i ^ ((j' : ℕ) + 1)) : j = j' := by
  have hj := j.2
  have hj' := j'.2
  have := pow_injOn_Iio_orderOf (x := x i)
    (by simp only [Set.mem_Iio, D.order i]; omega) (by simp only [Set.mem_Iio, D.order i]; omega) h
  exact Fin.ext (by omega)

theorem Data.conj_pow (D : Data z K x R) {i i' : Fin 2} {j j' : Fin 4} {g : G}
    (h : g * x i ^ ((j : ℕ) + 1) * g⁻¹ = x i' ^ ((j' : ℕ) + 1)) :
    i = i' ∧ g ∈ centralizer {z} :=
  D.ti.conj (D.pow_mem i j) (D.orderOf_pow i j) (h ▸ D.pow_mem i' j')

theorem Data.le_centralizer [Finite G] (D : Data z K x R) : R ≤ centralizer {z} := by
  let θ : Fin 5 × Fin 5 → R := fun p =>
    ⟨x 0 ^ (p.1 : ℕ) * x 1 ^ (p.2 : ℕ),
      R.mul_mem (R.pow_mem (D.memR 0) _) (R.pow_mem (D.memR 1) _)⟩
  have hinj : Function.Injective θ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have E : x 0 ^ (i : ℕ) * x 1 ^ (j : ℕ) = x 0 ^ (i' : ℕ) * x 1 ^ (j' : ℕ) :=
      congrArg Subtype.val h
    obtain ⟨w, hw⟩ : ∃ w : G, w = (x 0 ^ (i' : ℕ))⁻¹ * x 0 ^ (i : ℕ) := ⟨_, rfl⟩
    have hw0 : w ∈ zpowers (x 0) := by
      rw [hw]
      exact mul_mem (inv_mem (_root_.pow_mem (mem_zpowers _) _)) (_root_.pow_mem (mem_zpowers _) _)
    have hw0K : w ∈ K 0 := by
      rw [hw]
      exact mul_mem (inv_mem ((K 0).pow_mem (D.mem 0) _)) ((K 0).pow_mem (D.mem 0) _)
    have hw1 : w = x 1 ^ (j' : ℕ) * (x 1 ^ (j : ℕ))⁻¹ := by
      rw [hw]
      calc (x 0 ^ (i' : ℕ))⁻¹ * x 0 ^ (i : ℕ)
          = (x 0 ^ (i' : ℕ))⁻¹ * (x 0 ^ (i : ℕ) * x 1 ^ (j : ℕ)) * (x 1 ^ (j : ℕ))⁻¹ := by group
        _ = (x 0 ^ (i' : ℕ))⁻¹ * (x 0 ^ (i' : ℕ) * x 1 ^ (j' : ℕ)) * (x 1 ^ (j : ℕ))⁻¹ := by
          rw [E]
        _ = x 1 ^ (j' : ℕ) * (x 1 ^ (j : ℕ))⁻¹ := by group
    have hw1K : w ∈ K 1 := by
      rw [hw1]
      exact mul_mem ((K 1).pow_mem (D.mem 1) _) (inv_mem ((K 1).pow_mem (D.mem 1) _))
    have hwz : w ∈ zpowers z := by rw [← D.ti.inter]; exact ⟨hw0K, hw1K⟩
    have hd5 : orderOf w ∣ 5 := (D.order 0) ▸ orderOf_dvd_of_mem_zpowers hw0
    have hd2 : orderOf w ∣ 2 := D.ti.orderOf_z ▸ orderOf_dvd_of_mem_zpowers hwz
    have hw1' : w = 1 := by
      have h1 : orderOf w ∣ Nat.gcd 5 2 := Nat.dvd_gcd hd5 hd2
      have h2 : orderOf w = 1 := Nat.dvd_one.1 (by simpa using h1)
      exact orderOf_eq_one_iff.1 h2
    have hi : i = i' := by
      have : x 0 ^ (i : ℕ) = x 0 ^ (i' : ℕ) := by
        rw [hw] at hw1'
        exact (inv_mul_eq_one.1 hw1').symm
      exact Fin.ext (pow_injOn_Iio_orderOf (x := x 0)
        (by simp only [Set.mem_Iio, D.order 0]; exact i.2)
        (by simp only [Set.mem_Iio, D.order 0]; exact i'.2) this)
    have hj : j = j' := by
      have : x 1 ^ (j' : ℕ) = x 1 ^ (j : ℕ) := by
        rw [hw1'] at hw1
        exact mul_inv_eq_one.1 hw1.symm
      exact Fin.ext (pow_injOn_Iio_orderOf (x := x 1)
        (by simp only [Set.mem_Iio, D.order 1]; exact j'.2)
        (by simp only [Set.mem_Iio, D.order 1]; exact j.2) this).symm
    rw [hi, hj]
  have hbij : Function.Bijective θ :=
    hinj.bijective_of_nat_card_le (by rw [D.card]; simp)
  intro r hr
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨r, hr⟩
  have : x 0 ^ (i : ℕ) * x 1 ^ (j : ℕ) = r := congrArg Subtype.val hij
  rw [← this]
  exact mul_mem (_root_.pow_mem (D.ti.le 0 (D.mem 0)) _) (_root_.pow_mem (D.ti.le 1 (D.mem 1)) _)

theorem Data.conj_into_K [Finite G] (D : Data z K x R) {a : G} (ha3 : orderOf a = 3)
    (hRa : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (hatns : ∀ r ∈ R, r ≠ 1 → a * r * a⁻¹ ≠ r) :
    ∀ r ∈ R, r ≠ 1 → ∃ (h : G) (i : Fin 2), h * r * h⁻¹ ∈ K i := by
  intro r hr hr1
  have hmem : ∀ (m : ℕ) (i : Fin 2) (j : Fin 4),
      a ^ m * x i ^ ((j : ℕ) + 1) * (a ^ m)⁻¹ ∈ R :=
    fun m i j => pow_conj_mem hRa m _ (R.pow_mem (D.memR i) _)
  let Φ : Fin 3 × Fin 2 × Fin 4 → R := fun p =>
    ⟨a ^ (p.1 : ℕ) * x p.2.1 ^ ((p.2.2 : ℕ) + 1) * (a ^ (p.1 : ℕ))⁻¹, hmem _ _ _⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨m, i, j⟩ ⟨m', i', j'⟩ h
    have E : a ^ (m : ℕ) * x i ^ ((j : ℕ) + 1) * (a ^ (m : ℕ))⁻¹ =
        a ^ (m' : ℕ) * x i' ^ ((j' : ℕ) + 1) * (a ^ (m' : ℕ))⁻¹ := congrArg Subtype.val h
    obtain ⟨γ, hγdef⟩ : ∃ γ : G, γ = (a ^ (m : ℕ))⁻¹ * a ^ (m' : ℕ) := ⟨_, rfl⟩
    have hy : x i ^ ((j : ℕ) + 1) = γ * x i' ^ ((j' : ℕ) + 1) * γ⁻¹ := by
      rw [hγdef]; exact conj_rewrite E
    obtain ⟨hii, -⟩ := D.conj_pow hy.symm
    obtain rfl := hii.symm
    have hγ : γ ∈ zpowers a := by
      rw [hγdef]
      exact mul_mem (inv_mem (_root_.pow_mem (mem_zpowers a) _))
        (_root_.pow_mem (mem_zpowers a) _)
    have hγ3 : γ ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (ha3 ▸ orderOf_dvd_of_mem_zpowers hγ)
    have hj' := j'.2
    have hfix : γ * x i * γ⁻¹ = x i := aut3 (D.order i) hγ3 (by omega) hy.symm
    have hγ1 : γ = 1 := by
      by_contra hne
      exact not_commute_of_mem_zpowers ha3 hγ hne (hatns _ (D.memR i) (D.ne_one i)) hfix
    have hmm : m = m' := by
      have h1 : a ^ (m : ℕ) = a ^ (m' : ℕ) := by
        rw [hγdef] at hγ1
        exact inv_mul_eq_one.1 hγ1
      exact Fin.ext (pow_injOn_Iio_orderOf (x := a)
        (by simp only [Set.mem_Iio, ha3]; exact m.2)
        (by simp only [Set.mem_Iio, ha3]; exact m'.2) h1)
    subst hmm
    have hjj : j = j' := D.pow_injective i (by simpa [hγ1] using hy)
    subst hjj
    rfl
  have h1 : ∀ p, Φ p ≠ 1 := by
    rintro ⟨m, i, j⟩ h
    have h2 : a ^ (m : ℕ) * x i ^ ((j : ℕ) + 1) * (a ^ (m : ℕ))⁻¹ = 1 := congrArg Subtype.val h
    have h3 : x i ^ ((j : ℕ) + 1) = 1 := by
      have := conj_rewrite (g₁ := a ^ (m : ℕ)) (g₂ := 1) (y := x i ^ ((j : ℕ) + 1)) (y' := 1)
        (by rw [h2]; group)
      simpa using this
    exact D.pow_ne_one i j h3
  obtain ⟨⟨m, i, j⟩, hp⟩ := exists_eq_of_injective_of_card Φ hinj h1
    (by rw [D.card]; rfl) ⟨r, hr⟩ (fun h => hr1 (congrArg Subtype.val h))
  have hp' : a ^ (m : ℕ) * x i ^ ((j : ℕ) + 1) * (a ^ (m : ℕ))⁻¹ = r := congrArg Subtype.val hp
  refine ⟨(a ^ (m : ℕ))⁻¹, i, ?_⟩
  rw [← hp']
  have : (a ^ (m : ℕ))⁻¹ * (a ^ (m : ℕ) * x i ^ ((j : ℕ) + 1) * (a ^ (m : ℕ))⁻¹) *
      ((a ^ (m : ℕ))⁻¹)⁻¹ = x i ^ ((j : ℕ) + 1) := by group
  rw [this]
  exact D.pow_mem i j

theorem Data.le_of_isPGroup [Finite G] (D : Data z K x R) (hRC : R ≤ centralizer {z})
    (hcard : ∀ U : Subgroup G, U ≤ centralizer {z} → IsPGroup 5 U → Nat.card U ∣ 25)
    {T : Subgroup G} (hT : IsPGroup 5 T) (hRT : R ≤ T) : T ≤ R := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hTR
  have hlt : R < T := lt_of_le_of_ne hRT (fun h => hTR (h ▸ le_refl _))
  obtain ⟨n, hnT, hnR, hnorm⟩ := exists_mem_normalizer hT hlt
  have hTC : T ⊓ centralizer {z} ≤ R := by
    have hU : IsPGroup 5 (T ⊓ centralizer {z} : Subgroup G) := hT.to_le inf_le_left
    have hd := hcard _ inf_le_right hU
    have hle : Nat.card (T ⊓ centralizer {z} : Subgroup G) ≤ Nat.card R := by
      rw [D.card]; exact Nat.le_of_dvd (by norm_num) hd
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hRT hRC) hle).symm.le
  have hmemR : ∀ (k : ℕ) (i : Fin 2) (j : Fin 4),
      n ^ k * x i ^ ((j : ℕ) + 1) * (n ^ k)⁻¹ ∈ R :=
    fun k i j => pow_conj_mem hnorm k _ (R.pow_mem (D.memR i) _)
  let Ψ : Fin 5 × Fin 2 × Fin 4 → R := fun p =>
    ⟨n ^ (p.1 : ℕ) * x p.2.1 ^ ((p.2.2 : ℕ) + 1) * (n ^ (p.1 : ℕ))⁻¹, hmemR _ _ _⟩
  have hinj : Function.Injective Ψ := by
    rintro ⟨k, i, j⟩ ⟨k', i', j'⟩ h
    have E : n ^ (k : ℕ) * x i ^ ((j : ℕ) + 1) * (n ^ (k : ℕ))⁻¹ =
        n ^ (k' : ℕ) * x i' ^ ((j' : ℕ) + 1) * (n ^ (k' : ℕ))⁻¹ := congrArg Subtype.val h
    obtain ⟨γ, hγdef⟩ : ∃ γ : G, γ = (n ^ (k : ℕ))⁻¹ * n ^ (k' : ℕ) := ⟨_, rfl⟩
    have hy : x i ^ ((j : ℕ) + 1) = γ * x i' ^ ((j' : ℕ) + 1) * γ⁻¹ := by
      rw [hγdef]; exact conj_rewrite E
    obtain ⟨hii, hγC⟩ := D.conj_pow hy.symm
    obtain rfl := hii.symm
    have hγT : γ ∈ T := by
      rw [hγdef]
      exact mul_mem (inv_mem (_root_.pow_mem hnT _)) (_root_.pow_mem hnT _)
    have hγR : γ ∈ R := hTC ⟨hγT, hγC⟩
    have hkk : (k : ℕ) = k' := by
      have hk := k.2
      have hk' := k'.2
      rcases lt_trichotomy (k : ℕ) k' with hlt | heq | hgt
      · obtain ⟨d, hd⟩ : ∃ d, (k' : ℕ) = k + d := ⟨k' - k, by omega⟩
        have hγd : γ = n ^ d := by rw [hγdef, hd, pow_add, inv_mul_cancel_left]
        exact absurd (hγd ▸ hγR) (pow_not_mem_of_isPGroup hT hnT hnR (by omega) (by omega))
      · exact heq
      · obtain ⟨d, hd⟩ : ∃ d, (k : ℕ) = k' + d := ⟨k - k', by omega⟩
        have hγd : γ⁻¹ = n ^ d := by
          rw [hγdef, mul_inv_rev, inv_inv, hd, pow_add, inv_mul_cancel_left]
        exact absurd (hγd ▸ R.inv_mem hγR)
          (pow_not_mem_of_isPGroup hT hnT hnR (by omega) (by omega))
    have hkk' : k = k' := Fin.ext hkk
    subst hkk'
    have hγ1 : γ = 1 := by rw [hγdef]; group
    have hjj : j = j' := D.pow_injective i (by simpa [hγ1] using hy)
    subst hjj
    rfl
  have h1 : ∀ p, Ψ p ≠ 1 := by
    rintro ⟨k, i, j⟩ h
    have h2 : n ^ (k : ℕ) * x i ^ ((j : ℕ) + 1) * (n ^ (k : ℕ))⁻¹ = 1 := congrArg Subtype.val h
    have h3 : x i ^ ((j : ℕ) + 1) = 1 := by
      have := conj_rewrite (g₁ := n ^ (k : ℕ)) (g₂ := 1) (y := x i ^ ((j : ℕ) + 1)) (y' := 1)
        (by rw [h2]; group)
      simpa using this
    exact D.pow_ne_one i j h3
  exact false_of_injective_of_card Ψ hinj h1 (by rw [D.card]; decide)

end DataLemmas

end TISection

theorem sylow_setup {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (K₁ K₂ : Subgroup G) (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (hC5 : (Nat.card (Subgroup.centralizer {z})).factorization 5 = 2)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z)
    (x₁ x₂ : G) (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (ho₁ : orderOf x₁ = 5) (ho₂ : orderOf x₂ = 5)
    (Hs : Subgroup G) (hx₁H : x₁ ∈ Hs) (hx₂H : x₂ ∈ Hs)
    (hHs : Nonempty (↥Hs ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10)))
    (a : G) (ha3 : orderOf a = 3) (haN : ∀ h ∈ Hs, a * h * a⁻¹ ∈ Hs)
    (hatns : ∀ h ∈ Hs, h ≠ 1 → a * h * a⁻¹ ≠ h) :
    ∃ P : Sylow 5 G, Nat.card (P : Subgroup G) = 25 ∧ (∀ r ∈ (P : Subgroup G), r ^ 5 = 1) ∧
      ∀ r ∈ (P : Subgroup G), r ≠ 1 → ∃ h : G, h * r * h⁻¹ ∈ K₁ ∨ h * r * h⁻¹ ∈ K₂ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨R, hRH, hR25, hR5, hRmem⟩ := exists_R hHs
  let K : Fin 2 → Subgroup G := ![K₁, K₂]
  let x : Fin 2 → G := ![x₁, x₂]
  have hTI : TI z K :=
    { orderOf_z := hz
      le := fun i => by fin_cases i; exacts [hK₁, hK₂]
      inter := hinter
      norm := fun i => by fin_cases i; exacts [hn₁, hn₂]
      cent := fun y ⟨i, hy⟩ h5 =>
        hK5 y (by fin_cases i; exacts [Or.inl hy, Or.inr hy]) h5 }
  have hxR : ∀ i, x i ∈ R := fun i => by
    fin_cases i
    · exact hRmem x₁ hx₁H (by rw [← ho₁]; exact pow_orderOf_eq_one x₁)
    · exact hRmem x₂ hx₂H (by rw [← ho₂]; exact pow_orderOf_eq_one x₂)
  have D : Data z K x R :=
    { ti := hTI
      mem := fun i => by fin_cases i; exacts [hx₁, hx₂]
      order := fun i => by fin_cases i; exacts [ho₁, ho₂]
      memR := hxR
      card := hR25 }
  have hRC : R ≤ centralizer {z} := D.le_centralizer
  have hcard : ∀ U : Subgroup G, U ≤ centralizer {z} → IsPGroup 5 U → Nat.card U ∣ 25 :=
    fun U hU hp => by
      have := card_dvd_of_le_isPGroup hU hp
      rwa [hC5] at this
  have hRp : IsPGroup 5 R := IsPGroup.of_card (n := 2) (by rw [hR25]; norm_num)
  have hRa : ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun r hr =>
    hRmem _ (haN r (hRH hr)) (by rw [conj_pow, hR5 r hr]; simp)
  have hatns' : ∀ r ∈ R, r ≠ 1 → a * r * a⁻¹ ≠ r := fun r hr hr1 => hatns r (hRH hr) hr1
  obtain ⟨P, hP⟩ := hRp.exists_le_sylow
  have hPR : (P : Subgroup G) = R :=
    (D.le_of_isPGroup hRC hcard P.isPGroup' hP).antisymm hP
  refine ⟨P, by rw [hPR]; exact hR25, by rw [hPR]; exact hR5, ?_⟩
  intro s hs hs1
  rw [hPR] at hs
  obtain ⟨h', i, hi⟩ := D.conj_into_K ha3 hRa hatns' s hs hs1
  refine ⟨h', ?_⟩
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

end Sylow5

open Subgroup in
theorem card5_and_conj5 {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (K₁ K₂ : Subgroup G) (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (_hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hC5 : (Nat.card (Subgroup.centralizer {z})).factorization 5 = 2)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z)
    (x₁ x₂ : G) (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (ho₁ : orderOf x₁ = 5) (ho₂ : orderOf x₂ = 5)
    (Hs : Subgroup G) (hx₁H : x₁ ∈ Hs) (hx₂H : x₂ ∈ Hs)
    (hHs : Nonempty (↥Hs ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10)))
    (a : G) (ha3 : orderOf a = 3) (haN : ∀ h ∈ Hs, a * h * a⁻¹ ∈ Hs)
    (hatns : ∀ h ∈ Hs, h ≠ 1 → a * h * a⁻¹ ≠ h) :
    (Nat.card G).factorization 5 = 2 ∧
      ∀ g : G, orderOf g = 5 → ∃ h : G, h * g * h⁻¹ ∈ K₁ ∨ h * g * h⁻¹ ∈ K₂ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, hP25, -, hPconj⟩ := Sylow5.sylow_setup hz K₁ K₂ hK₁ hK₂ hinter hn₁ hn₂ hC5 hK5 x₁ x₂ hx₁
    hx₂ ho₁ ho₂ Hs hx₁H hx₂H hHs a ha3 haN hatns
  refine ⟨?_, ?_⟩
  · have h1 : Nat.card (P : Subgroup G) = 5 ^ (Nat.card G).factorization 5 :=
      P.card_eq_multiplicity
    rw [hP25] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) (h1.symm.trans (by norm_num))
  · intro g hg5
    have hgp : IsPGroup 5 (zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg5]; norm_num)
    obtain ⟨h, s, hs, hsg⟩ := Sylow5.exists_conj_mem_sylow P hgp
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [mul_one, mul_inv_cancel] at hsg
      rw [← hsg, orderOf_one] at hg5
      omega
    obtain ⟨h', hh'⟩ := hPconj s hs hs1
    refine ⟨h' * h⁻¹, ?_⟩
    have : h' * h⁻¹ * g * (h' * h⁻¹)⁻¹ = h' * s * h'⁻¹ := by rw [← hsg]; group
    rwa [this]

open Subgroup in
theorem pElement5_order {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (K₁ K₂ : Subgroup G) (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (_hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hC5 : (Nat.card (Subgroup.centralizer {z})).factorization 5 = 2)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z)
    (x₁ x₂ : G) (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (ho₁ : orderOf x₁ = 5) (ho₂ : orderOf x₂ = 5)
    (Hs : Subgroup G) (hx₁H : x₁ ∈ Hs) (hx₂H : x₂ ∈ Hs)
    (hHs : Nonempty (↥Hs ≃* Multiplicative (ZMod 10) × Multiplicative (ZMod 10)))
    (a : G) (ha3 : orderOf a = 3) (haN : ∀ h ∈ Hs, a * h * a⁻¹ ∈ Hs)
    (hatns : ∀ h ∈ Hs, h ≠ 1 → a * h * a⁻¹ ≠ h) :
    ∀ g : G, (∃ k : ℕ, orderOf g = 5 ^ k) → orderOf g = 1 ∨ orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, -, hP5, -⟩ := Sylow5.sylow_setup hz K₁ K₂ hK₁ hK₂ hinter hn₁ hn₂ hC5 hK5 x₁ x₂ hx₁
    hx₂ ho₁ ho₂ Hs hx₁H hx₂H hHs a ha3 haN hatns
  rintro g ⟨k, hk⟩
  have hgp : IsPGroup 5 (zpowers g) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨h, s, hs, hsg⟩ := Sylow5.exists_conj_mem_sylow P hgp
  have hdvd : orderOf g ∣ 5 := by
    rw [← hsg, Sylow5.orderOf_conj_eq]
    exact orderOf_dvd_of_pow_eq_one (hP5 s hs)
  exact (Nat.dvd_prime Nat.prime_five).1 hdvd

end CFSG.GH74.GLS.Stage4.Q9
