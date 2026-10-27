module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LieType.OutStructure

open scoped commutatorElement

section Conjugates

variable {Y : Type} [Group Y]

private theorem commute_conj_of_notMem_normalizer [Finite Y] {C : Subgroup Y}
    (hC : CFSG.IsComponent C) {k : Y} (hk : k ∉ Subgroup.normalizer (C : Set Y)) {a b : Y}
    (ha : a ∈ C) (hb : b ∈ C) : Commute a (k * b * k⁻¹) := by
  have hC' : CFSG.IsComponent (C.map (MulAut.conj k).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj k) hC
  rcases CFSG.LocalCores.distinct_components_commute hC hC' with h | h
  · exfalso
    apply hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  · have hmem : k * b * k⁻¹ ∈ C.map (MulAut.conj k).toMonoidHom :=
      ⟨b, hb, by simp [MulAut.conj_apply]⟩
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
    exact ((Subgroup.mem_centralizer_iff.mp this) _ hmem).symm

private theorem commute_conj_conj_of_notMem_normalizer [Finite Y] {C : Subgroup Y}
    (hC : CFSG.IsComponent C) {g h : Y} (hgh : g⁻¹ * h ∉ Subgroup.normalizer (C : Set Y))
    {a b : Y} (ha : a ∈ C) (hb : b ∈ C) : Commute (g * a * g⁻¹) (h * b * h⁻¹) := by
  have := (commute_conj_of_notMem_normalizer hC hgh ha hb).map (MulAut.conj g)
  simpa [MulAut.conj_apply, mul_assoc] using this

private theorem mem_of_pow_mem_of_prime {x : Y} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1) {m : ℕ}
    (hm0 : 0 < m) (hmp : m < p) {H : Subgroup Y} (h : x ^ m ∈ H) : x ∈ H := by
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hm0 hmp))
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx) hcop)
  rw [← ht]
  exact H.pow_mem h t

private theorem exists_ne_one_commute_of_dvd_card [Finite Y] {p : ℕ} (hp : p.Prime)
    {C : Subgroup Y} {y : Y} (hy : y ^ p = 1) (hyN : y ∈ Subgroup.normalizer (C : Set Y))
    (hpC : p ∣ Nat.card C) : ∃ w ∈ C, w ≠ 1 ∧ y * w = w * y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype C := Fintype.ofFinite C
  let g : Subgroup.normalizer (C : Set Y) := ⟨y, hyN⟩
  let σ : Equiv.Perm C := MulAut.toPerm C (Subgroup.normalizerMonoidHom C g)
  have hσ : σ ^ p ^ 1 = 1 := by
    have hg : g ^ p = 1 := Subtype.ext (by simpa [g] using hy)
    calc σ ^ p ^ 1 = MulAut.toPerm C (Subgroup.normalizerMonoidHom C (g ^ p)) := by
          simp [σ, map_pow]
      _ = 1 := by rw [hg]; simp
  have hcard : p ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact hpC
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (a := (1 : C)) hcard hσ
    (by
      change (Subgroup.normalizerMonoidHom C g) (1 : C) = 1
      exact map_one _)
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have h2 : ((σ b : C) : Y) = y * (b : Y) * y⁻¹ := rfl
  rw [hb] at h2
  exact (eq_mul_inv_iff_mul_eq.mp h2).symm

end Conjugates

section Diagonal

variable {Y : Type} [Group Y]

private def conjPow (x c : Y) (i : ℕ) : Y := x ^ i * c * (x ^ i)⁻¹

@[simp] private theorem conjPow_zero (x c : Y) : conjPow x c 0 = c := by simp [conjPow]

private theorem conj_conjPow (x c : Y) (i : ℕ) :
    x * conjPow x c i * x⁻¹ = conjPow x c (i + 1) := by
  simp only [conjPow, pow_succ', mul_inv_rev]
  group

private theorem conjPow_of_pow_eq_one {x : Y} {n : ℕ} (c : Y) (hx : x ^ n = 1) :
    conjPow x c n = c := by
  simp [conjPow, hx]

private def diagProd (x c : Y) : ℕ → Y
  | 0 => 1
  | n + 1 => diagProd x c n * conjPow x c n

private def shiftProd (x c : Y) : ℕ → Y
  | 0 => 1
  | n + 1 => shiftProd x c n * conjPow x c (n + 1)

private theorem diagProd_succ_eq (x c : Y) (n : ℕ) :
    diagProd x c (n + 1) = c * shiftProd x c n := by
  induction n with
  | zero => simp [diagProd, shiftProd]
  | succ n ih => rw [diagProd, ih, shiftProd, mul_assoc]

private theorem conj_diagProd (x c : Y) (n : ℕ) :
    x * diagProd x c n * x⁻¹ = shiftProd x c n := by
  induction n with
  | zero => simp [diagProd, shiftProd]
  | succ n ih =>
    rw [diagProd, shiftProd, ← ih, ← conj_conjPow]
    group

private theorem commute_shiftProd {x c z : Y} {n : ℕ}
    (h : ∀ i, 0 < i → i ≤ n → Commute z (conjPow x c i)) : Commute z (shiftProd x c n) := by
  induction n with
  | zero => exact Commute.one_right z
  | succ n ih =>
    rw [shiftProd]
    exact (ih fun i hi hin => h i hi (by omega)).mul_right (h (n + 1) (by omega) le_rfl)

private theorem conj_diagProd_self {x c : Y} {n : ℕ} (hx : x ^ (n + 1) = 1)
    (h : ∀ i, 0 < i → i ≤ n → Commute c (conjPow x c i)) :
    x * diagProd x c (n + 1) * x⁻¹ = diagProd x c (n + 1) := by
  rw [conj_diagProd, shiftProd, conjPow_of_pow_eq_one c hx, diagProd_succ_eq]
  exact (commute_shiftProd h).eq.symm

private theorem diagProd_conj_eq {x a t : Y} {n : ℕ}
    (h : ∀ i, 0 < i → i ≤ n → Commute t (conjPow x a i)) :
    diagProd x a (n + 1) * t * (diagProd x a (n + 1))⁻¹ = a * t * a⁻¹ := by
  rw [diagProd_succ_eq]
  have hW : shiftProd x a n * t = t * shiftProd x a n := (commute_shiftProd h).symm.eq
  calc a * shiftProd x a n * t * (a * shiftProd x a n)⁻¹
      = a * (shiftProd x a n * t) * (shiftProd x a n)⁻¹ * a⁻¹ := by group
    _ = a * t * a⁻¹ := by rw [hW]; group

private theorem commutator_mul_mul {a b u v : Y} (hub : Commute b u) (huv : Commute u v)
    (hav : Commute a v) : ⁅a * u, b * v⁆ = ⁅a, b⁆ := by
  have h1 : u * b = b * u := hub.symm.eq
  have h2 : u * v = v * u := huv.eq
  simp only [commutatorElement_def]
  calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹
      = a * (u * b) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = a * b * (u * v) * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [h1]; group
    _ = a * b * (v * a⁻¹) * v⁻¹ * b⁻¹ := by rw [h2]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hav.inv_left.eq]; group

private theorem commutator_diagProd {x y a b : Y} {n : ℕ}
    (hxb : ∀ i, 0 < i → i ≤ n → Commute b (conjPow x a i))
    (hya : ∀ j, 0 < j → j ≤ n → Commute a (conjPow y b j))
    (hxy : ∀ i j, 0 < i → i ≤ n → 0 < j → j ≤ n → Commute (conjPow x a i) (conjPow y b j)) :
    ⁅diagProd x a (n + 1), diagProd y b (n + 1)⁆ = ⁅a, b⁆ := by
  rw [diagProd_succ_eq, diagProd_succ_eq]
  have hub : Commute b (shiftProd x a n) := commute_shiftProd hxb
  have hav : Commute a (shiftProd y b n) := commute_shiftProd hya
  have huv : Commute (shiftProd x a n) (shiftProd y b n) := by
    refine commute_shiftProd fun j hj hjn => ?_
    exact (commute_shiftProd fun i hi hin => (hxy i j hi hin hj hjn).symm).symm
  exact commutator_mul_mul hub huv hav

end Diagonal

section Generation

variable {Y : Type} [Group Y]

private theorem diagProd_mem [Finite Y] {C : Subgroup Y} (hC : CFSG.IsComponent C)
    {Γ : Subgroup Y} {x : Y} {n : ℕ} (hx : x ^ (n + 1) = 1)
    (hxi : ∀ i, 0 < i → i ≤ n → x ^ i ∉ Subgroup.normalizer (C : Set Y))
    (hxΓ : Subgroup.centralizer {x} ≤ Γ) {a : Y} (ha : a ∈ C) : diagProd x a (n + 1) ∈ Γ := by
  apply hxΓ
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  exact mul_inv_eq_iff_eq_mul.mp (conj_diagProd_self hx fun i hi hin =>
    commute_conj_of_notMem_normalizer hC (hxi i hi hin) ha ha)

private theorem le_of_mem_normalizer_case [Finite Y] {p : ℕ} (hp : p.Prime) {C : Subgroup Y}
    (hC : CFSG.IsComponent C) (hZ : Subgroup.center ↥C = ⊥) (hpC : p ∣ Nat.card C)
    {Γ : Subgroup Y} {x y : Y} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxN : x ∉ Subgroup.normalizer (C : Set Y)) (hyN : y ∈ Subgroup.normalizer (C : Set Y))
    (hxΓ : Subgroup.centralizer {x} ≤ Γ) (hyΓ : Subgroup.centralizer {y} ≤ Γ) : C ≤ Γ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  obtain ⟨w, hwC, hw1, hyw⟩ := exists_ne_one_commute_of_dvd_card hp hy hyN hpC
  have hwΓ : w ∈ Γ := hyΓ (Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hyw)
  have hxi : ∀ i, 0 < i → i ≤ n → x ^ i ∉ Subgroup.normalizer (C : Set Y) := fun i hi hin hmem =>
    hxN (mem_of_pow_mem_of_prime hp hx hi (by omega) hmem)
  let T : Subgroup C := Γ.comap C.subtype
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    have hd := diagProd_mem hC hx hxi hxΓ g.2
    have h := diagProd_conj_eq (x := x) (a := (g : Y)) (t := (t : Y)) (n := n) fun i hi hin =>
      commute_conj_of_notMem_normalizer hC (hxi i hi hin) t.2 g.2
    show (g : Y) * (t : Y) * (g : Y)⁻¹ ∈ Γ
    rw [← h]
    exact Γ.mul_mem (Γ.mul_mem hd ht) (Γ.inv_mem hd)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.1 hTn with hT | hT
  · intro c hc
    have : (⟨c, hc⟩ : C) ∈ T := hT ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have := hT (show (⟨w, hwC⟩ : C) ∈ T from hwΓ)
    rw [hZ, Subgroup.mem_bot] at this
    exact hw1 (congrArg Subtype.val this)

private theorem commutator_le_of_cross [Finite Y] {p : ℕ} (hp : p.Prime) {C : Subgroup Y}
    (hC : CFSG.IsComponent C) {Γ : Subgroup Y} {x y : Y} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : ∀ i j : ℕ, i < p → j < p → (i ≠ 0 ∨ j ≠ 0) →
      (x ^ i)⁻¹ * y ^ j ∉ Subgroup.normalizer (C : Set Y))
    (hxΓ : Subgroup.centralizer {x} ≤ Γ) (hyΓ : Subgroup.centralizer {y} ≤ Γ) : ⁅C, C⁆ ≤ Γ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hxi : ∀ i, 0 < i → i ≤ n → x ^ i ∉ Subgroup.normalizer (C : Set Y) := by
    intro i hi hin hmem
    apply hxy i 0 (by omega) (by omega) (Or.inl hi.ne')
    simpa using (Subgroup.normalizer (C : Set Y)).inv_mem hmem
  have hyj : ∀ j, 0 < j → j ≤ n → y ^ j ∉ Subgroup.normalizer (C : Set Y) := by
    intro j hj hjn hmem
    apply hxy 0 j (by omega) (by omega) (Or.inr hj.ne')
    simpa using hmem
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := commutator_diagProd (x := x) (y := y) (n := n)
    (fun i hi hin => commute_conj_of_notMem_normalizer hC (hxi i hi hin) hb ha)
    (fun j hj hjn => commute_conj_of_notMem_normalizer hC (hyj j hj hjn) ha hb)
    (fun i j hi hin hj hjn => commute_conj_conj_of_notMem_normalizer hC
      (hxy i j (by omega) (by omega) (Or.inl hi.ne')) ha hb)
  rw [← h]
  have h1 := diagProd_mem hC hx hxi hxΓ ha
  have h2 := diagProd_mem hC hy hyj hyΓ hb
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem h1 h2) (Γ.inv_mem h1)) (Γ.inv_mem h2)

private theorem component_le_of_forall_centralizer_le [Finite Y] {p : ℕ} (hp : p.Prime)
    {C : Subgroup Y} (hC : CFSG.IsComponent C) (hZ : Subgroup.center ↥C = ⊥)
    (hpC : p ∣ Nat.card C) {E : Subgroup Y} (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2)
    (hgen : E ≤ Subgroup.normalizer (C : Set Y) → (∀ x ∈ E, x ≠ 1 → ∃ c ∈ C, x * c ≠ c * x) →
      C ≤ Subgroup.closure {c | c ∈ C ∧ ∃ x ∈ E, x ≠ 1 ∧ x * c = c * x})
    {Γ : Subgroup Y} (hΓ : ∀ z ∈ E, z ≠ 1 → Subgroup.centralizer {z} ≤ Γ) : C ≤ Γ := by
  have hmemc : ∀ {x c : Y}, x * c = c * x → c ∈ Subgroup.centralizer {x} := fun {x c} h =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]
      exact h
  by_cases hN : E ≤ Subgroup.normalizer (C : Set Y)
  ·
    by_cases h1 : ∃ x ∈ E, x ≠ 1 ∧ ∀ c ∈ C, x * c = c * x
    · obtain ⟨x, hxE, hx1, hxc⟩ := h1
      exact fun c hc => hΓ x hxE hx1 (hmemc (hxc c hc))
    · push Not at h1
      refine (hgen hN fun x hx hx1 => h1 x hx hx1).trans ((Subgroup.closure_le Γ).mpr ?_)
      rintro c ⟨-, x, hxE, hx1, hxc⟩
      exact hΓ x hxE hx1 (hmemc hxc)
  ·
    obtain ⟨x, hxE, hxN⟩ : ∃ x ∈ E, x ∉ Subgroup.normalizer (C : Set Y) := by
      by_contra h
      push Not at h
      exact hN h
    have hx1 : x ≠ 1 := fun h => hxN (h ▸ one_mem _)
    by_cases h2 : ∃ y ∈ E, y ≠ 1 ∧ y ∈ Subgroup.normalizer (C : Set Y)
    · obtain ⟨y, hyE, hy1, hyN⟩ := h2
      exact le_of_mem_normalizer_case hp hC hZ hpC (hE.2 x hxE) (hE.2 y hyE) hxN hyN
        (hΓ x hxE hx1) (hΓ y hyE hy1)
    ·
      push Not at h2
      have hnle : ¬ E ≤ Subgroup.zpowers x := by
        intro hle
        have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, hEc] at h1
        have h2 : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hE.2 x hxE))
        nlinarith [hp.two_le]
      obtain ⟨y, hyE, hyx⟩ := SetLike.not_le_iff_exists.mp hnle
      have hyxpow : ∀ j : ℕ, 0 < j → j < p → y ^ j ∉ Subgroup.zpowers x := fun j hj0 hjp hmem =>
        hyx (mem_of_pow_mem_of_prime hp (hE.2 y hyE) hj0 hjp hmem)
      have hxy : ∀ i j : ℕ, i < p → j < p → (i ≠ 0 ∨ j ≠ 0) →
          (x ^ i)⁻¹ * y ^ j ∉ Subgroup.normalizer (C : Set Y) := by
        intro i j hi hj hij
        have hzE : (x ^ i)⁻¹ * y ^ j ∈ E :=
          E.mul_mem (E.inv_mem (E.pow_mem hxE i)) (E.pow_mem hyE j)
        refine h2 _ hzE fun hz => ?_
        have hxy : x ^ i = y ^ j := inv_mul_eq_one.mp hz
        by_cases hj0 : j = 0
        · subst hj0
          have hi0 : i ≠ 0 := hij.resolve_right (by simp)
          rw [pow_zero] at hxy
          have := mem_of_pow_mem_of_prime hp (hE.2 x hxE) (Nat.pos_of_ne_zero hi0) hi
            (H := ⊥) (by rw [hxy]; exact one_mem _)
          exact hx1 (Subgroup.mem_bot.mp this)
        · exact hyxpow j (Nat.pos_of_ne_zero hj0) hj (by
            rw [← hxy]
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i)
      have hcomm := commutator_le_of_cross hp hC (hE.2 x hxE) (hE.2 y hyE) hxy
        (hΓ x hxE hx1) (hΓ y hyE (fun h => hyx (h ▸ one_mem _)))
      calc C = ⁅C, C⁆ := (Subgroup.isPerfect_iff.mp hC.1.1).symm
        _ ≤ Γ := hcomm

end Generation

theorem component_le_iSup_centralizer {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {C : Subgroup Y} (hC : CFSG.IsComponent C) (hZ : Subgroup.center ↥C = ⊥)
    (hpC : p ∣ Nat.card C) {E : Subgroup Y} (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2)
    (hgen : E ≤ Subgroup.normalizer (C : Set Y) → (∀ x ∈ E, x ≠ 1 → ∃ c ∈ C, x * c ≠ c * x) →
      C ≤ Subgroup.closure {c | c ∈ C ∧ ∃ x ∈ E, x ≠ 1 ∧ x * c = c * x}) :
    C ≤ ⨆ (x : Y) (_ : x ∈ E) (_ : x ≠ 1), Subgroup.centralizer {x} :=
  component_le_of_forall_centralizer_le hp hC hZ hpC hE hEc hgen fun z hz hz1 =>
    le_iSup₂_of_le z hz (le_iSup (fun _ : z ≠ 1 => Subgroup.centralizer {z}) hz1)

end CFSG.LieType.OutStructure
