module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem ka_commutator_top_of_perfect {G : Type*} [Group G] (R : Subgroup G) (hR : ⁅R, R⁆ = R) :
    commutator ↥R = ⊤ := by
  have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup R)) (H₂ := ⊤) (f := R.subtype)
  have h2 : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h2, hR] at h1
  rw [commutator_def]
  exact Subgroup.map_injective R.subtype_injective (h1.trans h2.symm)

theorem ka_perfect_closure_odd {R : Type*} [Group R] [Finite R] (hR : commutator R = ⊤) :
    Subgroup.closure {x : R | Odd (orderOf x)} = ⊤ := by
  classical
  set S : Set R := {x : R | Odd (orderOf x)} with hS
  have hSconj : ∀ g x : R, x ∈ S → g * x * g⁻¹ ∈ S := by
    intro g x hx
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    have h2 : orderOf (g * x * g⁻¹) = orderOf x := by simpa [MulAut.conj_apply] using h1
    show Odd (orderOf (g * x * g⁻¹))
    rw [h2]
    exact hx
  let N : Subgroup R := Subgroup.closure S
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hSconj g x hx)
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using N.mul_mem hx hy
    | inv x _ hx => simpa [mul_inv_rev, mul_assoc] using N.inv_mem hx
  have hpg : IsPGroup 2 (R ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x) (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    have hodd : Odd (orderOf (x ^ (2 ^ k))) := by
      rw [orderOf_pow' _ (pow_ne_zero k two_ne_zero), hn]
      have : Nat.gcd (2 ^ k * m) (2 ^ k) = 2 ^ k := Nat.gcd_eq_right (dvd_mul_right _ _)
      rw [this, Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
      exact hm
    have hmem : x ^ (2 ^ k) ∈ N := Subgroup.subset_closure hodd
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (R ⧸ N) := hpg.isNilpotent
  have hsol : Group.IsSolvable (R ⧸ N) := inferInstance
  have hperfQ : commutator (R ⧸ N) = ⊤ := by
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup R)) (H₂ := ⊤)
      (f := QuotientGroup.mk' N)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    rw [commutator_def]
    rw [← h1, ← commutator_def, hR,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hsub : Subsingleton (R ⧸ N) := by
    by_contra hne
    rw [not_subsingleton_iff_nontrivial] at hne
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial (R ⧸ N)
    rw [hperfQ] at this
    exact lt_irrefl _ this
  rw [eq_top_iff]
  intro x _
  have : (QuotientGroup.mk x : R ⧸ N) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff x).1 this

theorem ka_perfect_le_of_odd {G : Type*} [Group G] [Finite G] (R : Subgroup G)
    (hR : ⁅R, R⁆ = R) (H : Subgroup G) (h : ∀ x ∈ R, Odd (orderOf x) → x ∈ H) : R ≤ H := by
  have hcl := ka_perfect_closure_odd (R := ↥R) (ka_commutator_top_of_perfect R hR)
  have hle : Subgroup.closure {x : ↥R | Odd (orderOf x)} ≤ H.comap R.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    refine h x x.2 ?_
    rw [Subgroup.orderOf_coe]
    exact hx
  rw [hcl] at hle
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : ↥R))

theorem ka_le_of_gen_odd {G : Type*} [Group G] (R : Subgroup G)
    (hR : Subgroup.closure {x : G | x ∈ R ∧ Odd (orderOf x)} = R) (H : Subgroup G)
    (h : ∀ x ∈ R, Odd (orderOf x) → x ∈ H) : R ≤ H := by
  rw [← hR, Subgroup.closure_le]
  rintro x ⟨hx, hodd⟩
  exact h x hx hodd

theorem ka_gen_odd_of_perfect {G : Type*} [Group G] [Finite G] (R : Subgroup G)
    (hR : ⁅R, R⁆ = R) : Subgroup.closure {x : G | x ∈ R ∧ Odd (orderOf x)} = R := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx
  · refine ka_perfect_le_of_odd R hR _ fun x hx hodd => ?_
    exact Subgroup.subset_closure ⟨hx, hodd⟩

theorem ka_odd_mem_of_sq_mem {G : Type*} [Group G] {R : Subgroup G} {c : G}
    (hc : c * c ∈ R) (hodd : Odd (orderOf c)) : c ∈ R := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  have h2 : c = (c * c) ^ (k + 1) := by
    calc c = c ^ (2 * k + 1) * c := by rw [h1, one_mul]
      _ = c ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (c * c) ^ (k + 1) := by rw [pow_mul, sq]
  rw [h2]
  exact R.pow_mem hc _

section Gen

variable {Y : Type} [Group Y]

@[expose] def kaInner (E : Subgroup (MulAut Y)) : Subgroup Y :=
  E.comap (MulAut.conj : Y →* MulAut Y)

theorem mem_kaInner {E : Subgroup (MulAut Y)} {y : Y} : y ∈ kaInner E ↔ MulAut.conj y ∈ E :=
  Iff.rfl

theorem conj_apply_aut (α : MulAut Y) (y : Y) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext z
  simp [MulAut.conj_apply]

theorem kaInner_le_fixSub (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} {E : Subgroup (MulAut Y)} (hE : ∀ e ∈ E, e * α = α * e) :
    kaInner E ≤ fixSub α := by
  intro y hy
  rw [mem_fixSub]
  have h1 : α * MulAut.conj y = MulAut.conj y * α := (hE _ hy).symm
  have h2 : MulAut.conj (α y) = MulAut.conj y := by
    rw [← conj_apply_aut, h1]
    group
  exact hinj h2

theorem mem_normalizer_kaInner {E : Subgroup (MulAut Y)} {c : Y}
    (hc : MulAut.conj c ∈ normalizer (E : Set (MulAut Y))) :
    c ∈ normalizer (kaInner E : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hc ⊢
  intro y
  rw [mem_kaInner, mem_kaInner, map_mul, map_mul, map_inv]
  exact hc _

theorem kaInner_isPGroup (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {p : ℕ}
    {E : Subgroup (MulAut Y)} (hE : IsPGroup p E) : IsPGroup p (kaInner E) :=
  hE.comap_of_injective _ hinj

theorem ka_fix_of_perfect [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {p : ℕ} (hp : p.Prime)
    {P : Subgroup (MulAut Y)} (hPp : IsPGroup p P)
    (R : Subgroup Y) (hR : ⁅R, R⁆ = R)
    (hRN : ∀ r ∈ R, MulAut.conj r ∈ normalizer (P : Set (MulAut Y)))
    (hX : ∀ x ∈ kaInner P, ∀ r ∈ R, x * r = r * x) :
    ∀ e ∈ P, ∀ r ∈ R, e r = r := by
  intro e he
  have hx : ∀ r ∈ R, r * (e r)⁻¹ ∈ kaInner P := by
    intro r hr
    rw [mem_kaInner, map_mul, map_inv]
    have h1 : e * MulAut.conj r * e⁻¹ = MulAut.conj (e r) := conj_apply_aut e r
    have h2 : MulAut.conj r * (MulAut.conj (e r))⁻¹ =
        (MulAut.conj r * e * (MulAut.conj r)⁻¹) * e⁻¹ := by
      rw [← h1]; group
    rw [h2]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hRN r hr) e).1 he) (P.inv_mem he)
  have hxmul : ∀ r ∈ R, ∀ s ∈ R, (r * s) * (e (r * s))⁻¹ =
      (s * (e s)⁻¹) * (r * (e r)⁻¹) := by
    intro r hr s hs
    have hc : (s * (e s)⁻¹) * r = r * (s * (e s)⁻¹) := hX _ (hx s hs) r hr
    have hcs : r * (s * (e s)⁻¹) * r⁻¹ = s * (e s)⁻¹ := by
      rw [← hc]; group
    calc (r * s) * (e (r * s))⁻¹ = r * (s * (e s)⁻¹) * (e r)⁻¹ := by
          rw [map_mul, mul_inv_rev]; group
      _ = (r * (s * (e s)⁻¹) * r⁻¹) * (r * (e r)⁻¹) := by group
      _ = (s * (e s)⁻¹) * (r * (e r)⁻¹) := by rw [hcs]
  let θ : ↥R →* ↥(kaInner P) :=
    MonoidHom.mk' (fun r => ⟨(r * (e r)⁻¹)⁻¹, (kaInner P).inv_mem (hx r r.2)⟩) (by
      intro r s
      apply Subtype.ext
      show ((r * s : ↥R) * (e ((r * s : ↥R) : Y))⁻¹)⁻¹ = _
      rw [Subgroup.coe_mul, hxmul r r.2 s s.2, mul_inv_rev]
      rfl)
  have hpg : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent ↥(kaInner P) := hpg.isNilpotent
  have hsol : Group.IsSolvable ↥(kaInner P) := inferInstance
  have hperf : ⁅θ.range, θ.range⁆ = θ.range := by
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥R)) (H₂ := (⊤ : Subgroup ↥R)) (f := θ)
    have h2 : (⊤ : Subgroup ↥R).map θ = θ.range := by
      rw [← MonoidHom.range_eq_map]
    have h3 : ⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆ = (⊤ : Subgroup ↥R) := by
      rw [← commutator_def]
      exact ka_commutator_top_of_perfect R hR
    rw [h3, h2] at h1
    exact h1.symm
  have hbot : θ.range = ⊥ := by
    by_contra hne
    have := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [hperf] at this
    exact lt_irrefl _ this
  intro r hr
  have h1 : θ ⟨r, hr⟩ = 1 := by
    have : θ ⟨r, hr⟩ ∈ θ.range := ⟨⟨r, hr⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have h2 : (r * (e r)⁻¹)⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : r * (e r)⁻¹ = 1 := inv_eq_one.1 h2
  exact (mul_inv_eq_one.1 h3).symm

end Gen

section Main

variable {Y : Type} [Group Y]

@[expose] def KAHyp (α : MulAut Y) (p : ℕ) (P : Subgroup (MulAut Y)) : Prop :=
  IsPGroup p ↥P ∧ P ≠ ⊥ ∧ (∀ e ∈ P, e * α = α * e) ∧
    ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))

@[expose] def KAConcl (α : MulAut Y) (P : Subgroup (MulAut Y)) : Prop :=
  (∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) ∧ IsCyclic ↥P

@[expose] def KAAll (α : MulAut Y) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), KAHyp α p P → KAConcl α P

@[expose] def KAOutCyc (Y : Type) [Group Y] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
    (∀ e ∈ P, e ∈ innSub Y → e = 1) → IsCyclic ↥P

@[expose] def KARigid (L : Subgroup Y) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ e : MulAut Y, IsPGroup p ↥(Subgroup.zpowers e) →
    (∀ r ∈ L, e r = r) → e ∈ innSub Y

@[expose] def KARigidTriv (L : Subgroup Y) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ e : MulAut Y, IsPGroup p ↥(Subgroup.zpowers e) →
    (∀ r ∈ L, e r = r) → e = 1

@[expose] def KARigidComm (α : MulAut Y) (L : Subgroup Y) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ e : MulAut Y, IsPGroup p ↥(Subgroup.zpowers e) →
    e * α = α * e → (∀ r ∈ L, e r = r) → e = 1

theorem ka_normalizes_of_gen {α : MulAut Y} {P : Subgroup (MulAut Y)}
    (hP : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y)))
    {R : Subgroup Y} (hRC : R ≤ fixSub α)
    (hRgen : Subgroup.closure {x : Y | x ∈ R ∧ Odd (orderOf x)} = R) :
    ∀ r ∈ R, MulAut.conj r ∈ normalizer (P : Set (MulAut Y)) := by
  let H : Subgroup Y := (normalizer (P : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
  have hle : R ≤ H := ka_le_of_gen_odd R hRgen H fun x hx hodd => hP x (hRC hx) hodd
  exact fun r hr => hle hr

theorem ka_odd_of_mem_pGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup Y}
    (hX : IsPGroup p ↥X) {x : Y} (hx : x ∈ X) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hd : orderOf (⟨x, hx⟩ : ↥X) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
  have h1 : orderOf x = p ^ j := by
    rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥X)] at hj
    exact hj
  rw [h1]
  exact (hp.odd_of_ne_two hp2).pow

theorem ka_kaInner_eq_bot (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {α : MulAut Y}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut Y)} (hPp : IsPGroup p ↥P)
    (hcomm : ∀ e ∈ P, e * α = α * e)
    (hP : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y)))
    (R : Subgroup Y) (hRC : R ≤ fixSub α)
    (hRgen : Subgroup.closure {x : Y | x ∈ R ∧ Odd (orderOf x)} = R)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R)
    (hRp : ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ R →
      (∀ r ∈ R, r ∈ normalizer (X : Set Y)) → X = ⊥) : kaInner P = ⊥ := by
  have hRN := ka_normalizes_of_gen hP hRC hRgen
  have hXp : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hXC := kaInner_le_fixSub hinj hcomm
  have hXR : kaInner P ≤ R := fun x hx => hodd x (hXC hx) (ka_odd_of_mem_pGroup hp hp2 hXp hx)
  exact hRp _ hXp hXR fun r hr => mem_normalizer_kaInner (hRN r hr)

theorem ka_all_of_oddcore (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R : Subgroup Y) (hRC : R ≤ fixSub α)
    (hRgen : Subgroup.closure {x : Y | x ∈ R ∧ Odd (orderOf x)} = R)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R)
    (hRp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ R →
      (∀ r ∈ R, r ∈ normalizer (X : Set Y)) → X = ⊥)
    (hOutCyc : KAOutCyc Y) (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, -, hcomm, hnorm⟩ := hP
  have hbot := ka_kaInner_eq_bot hinj hp hp2 hPp hcomm hnorm R hRC hRgen hodd (hRp p hp hp2)
  refine ⟨hOut, hOutCyc p hp hp2 P hPp ?_⟩
  rintro e he ⟨y, rfl⟩
  have hy : y ∈ kaInner P := he
  rw [hbot, Subgroup.mem_bot] at hy
  rw [hy, map_one]

theorem ka_all_of_rigid [Finite Y] (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R : Subgroup Y) (hRC : R ≤ fixSub α) (hRperf : ⁅R, R⁆ = R)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R)
    (hRp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ R →
      (∀ r ∈ R, r ∈ normalizer (X : Set Y)) → X = ⊥)
    (hrig : KARigid R) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  exfalso
  have hRgen := ka_gen_odd_of_perfect R hRperf
  have hbot := ka_kaInner_eq_bot hinj hp hp2 hPp hcomm hnorm R hRC hRgen hodd (hRp p hp hp2)
  have hRN := ka_normalizes_of_gen hnorm hRC hRgen
  have hX0c : ∀ x ∈ kaInner P, ∀ r ∈ R, x * r = r * x := by
    intro x hx r _
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  have hfix := ka_fix_of_perfect hinj hp hPp R hRperf hRN hX0c
  apply hP1
  rw [eq_bot_iff]
  intro e he
  have hinn : e ∈ innSub Y :=
    hrig p hp hp2 e (IsPGroup.to_le hPp ((Subgroup.zpowers_le).2 he)) (hfix e he)
  obtain ⟨y, rfl⟩ := hinn
  have hy : y ∈ kaInner P := he
  rw [hbot, Subgroup.mem_bot] at hy
  rw [hy, map_one]
  exact Subgroup.one_mem _

end Main

section Quasi

variable {Y : Type} [Group Y]

theorem ka_centralizes_of_perfect {p : ℕ} (L X : Subgroup Y) (hL : ⁅L, L⁆ = L)
    (hLX : ∀ l ∈ L, l ∈ normalizer (X : Set Y)) (hXL : ∀ x ∈ X, x ∈ normalizer (L : Set Y))
    (hXp : IsPGroup p ↥X)
    (hLp : ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m) :
    ∀ x ∈ X, ∀ l ∈ L, x * l = l * x := by
  intro x hx
  set M : Subgroup Y := X ⊓ L with hM
  have hMp : IsPGroup p ↥M := hXp.to_le inf_le_left
  have hML : M ≤ L := inf_le_right
  have hMn : ∀ l ∈ L, l ∈ normalizer (M : Set Y) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.1 (hLX l hl) h
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) h
    simp only [hM, Subgroup.mem_inf]
    rw [h1, h2]
  have hMc := hLp M hML hMp hMn
  have hcomm : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ M := by
    intro l hl
    refine ⟨?_, ?_⟩
    · have h1 : l * x⁻¹ * l⁻¹ ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 (hLX l hl) x⁻¹).1 (X.inv_mem hx)
        exact this
      have h2 : x * (l * x⁻¹ * l⁻¹) ∈ X := X.mul_mem hx h1
      simpa [mul_assoc] using h2
    · have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hXL x hx) l).1 hl
      exact L.mul_mem h1 (L.inv_mem hl)
  let f : ↥L →* ↥M :=
    MonoidHom.mk' (fun l => ⟨x * l * x⁻¹ * (l : Y)⁻¹, hcomm l l.2⟩) (by
      intro a b
      apply Subtype.ext
      show x * ((a * b : ↥L) : Y) * x⁻¹ * (((a * b : ↥L) : Y))⁻¹ = _
      have hcen : (a : Y) * (x * b * x⁻¹ * (b : Y)⁻¹) =
          (x * b * x⁻¹ * (b : Y)⁻¹) * (a : Y) :=
        (hMc _ (hcomm b b.2) a a.2).symm
      show x * ((a : Y) * b) * x⁻¹ * ((a : Y) * b)⁻¹ =
        (x * a * x⁻¹ * (a : Y)⁻¹) * (x * b * x⁻¹ * (b : Y)⁻¹)
      calc x * ((a : Y) * b) * x⁻¹ * ((a : Y) * b)⁻¹
          = (x * a * x⁻¹ * (a : Y)⁻¹) * ((a : Y) * (x * b * x⁻¹ * (b : Y)⁻¹) * (a : Y)⁻¹) := by
            group
        _ = (x * a * x⁻¹ * (a : Y)⁻¹) * (x * b * x⁻¹ * (b : Y)⁻¹) := by
            rw [hcen]; group)
  have hker : commutator ↥L ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have h1 : ((f a : ↥M) : Y) * (f b : Y) = (f b : Y) * (f a : Y) :=
      hMc _ (f a).2 _ (hML (f b).2)
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [h1]
    group
  intro l hl
  have hft : f.ker = ⊤ := by
    rw [eq_top_iff, ← ka_commutator_top_of_perfect L hL]
    exact hker
  have h1 : f ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : ↥L) ∈ f.ker := by rw [hft]; trivial
    exact this
  have h2 : x * l * x⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : x * l * x⁻¹ = l := mul_inv_eq_one.1 h2
  calc x * l = (x * l * x⁻¹) * x := by group
    _ = l * x := by rw [h3]

end Quasi

theorem ka_central_of_quasisimple_image {Q Y : Type} [Group Q] [Group Y] [Finite Y] (φ : Q →* Y)
    (hQ : CFSG.IsQuasisimple Q) {p : ℕ} (hp : p.Prime) (M : Subgroup Y) (hMR : M ≤ φ.range)
    (hMp : IsPGroup p ↥M) (hMn : ∀ l ∈ φ.range, l ∈ normalizer (M : Set Y)) :
    ∀ m ∈ M, ∀ l ∈ φ.range, m * l = l * m := by
  classical
  let N : Subgroup Q := M.comap φ
  have hNn : N.Normal := ⟨fun n hn g => by
    show φ (g * n * g⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hMn (φ g) ⟨g, rfl⟩) (φ n)).1 hn⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with hN | hN
  · intro m hm l hl
    obtain ⟨q, rfl⟩ := hMR hm
    obtain ⟨q', rfl⟩ := hl
    have hq : q ∈ center Q := hN hm
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hq q')]
  · have hRM : φ.range ≤ M := by
      rintro _ ⟨q, rfl⟩
      have : q ∈ N := hN ▸ Subgroup.mem_top q
      exact this
    have : Fact p.Prime := ⟨hp⟩
    have hRp : IsPGroup p ↥φ.range := hMp.to_le hRM
    have hQperf : Group.IsPerfect Q := hQ.1
    have hperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hnil : Group.IsNilpotent ↥φ.range := hRp.isNilpotent
    have hbot : φ.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isNilpotent ↥φ.range hnil
    have hMb : M = ⊥ := by
      rw [eq_bot_iff]
      exact hMR.trans hbot.le
    intro m hm l _
    rw [hMb, Subgroup.mem_bot] at hm
    rw [hm, one_mul, mul_one]

section Torus

variable {Y : Type} [Group Y] [Finite Y]

theorem ka_all_of_torus (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R₀ L : Subgroup Y) (hR₀C : R₀ ≤ fixSub α)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R₀) (hLR₀ : L ≤ R₀)
    (hLn : ∀ x ∈ R₀, x ∈ normalizer (L : Set Y)) (hLperf : ⁅L, L⁆ = L)
    (hLp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m)
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ R₀ →
      (∀ x ∈ X, ∀ l ∈ L, x * l = l * x) → IsCyclic ↥X)
    (hrig : KARigid L) (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, -, hcomm, hnorm⟩ := hP
  have hLC : L ≤ fixSub α := hLR₀.trans hR₀C
  have hLN : ∀ l ∈ L, MulAut.conj l ∈ normalizer (P : Set (MulAut Y)) := by
    let H : Subgroup Y := (normalizer (P : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
    have hle : L ≤ H := ka_perfect_le_of_odd L hLperf H fun x hx hodd' => hnorm x (hLC hx) hodd'
    exact fun l hl => hle hl
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0R : kaInner P ≤ R₀ := fun x hx =>
    hodd x (hX0C hx) (ka_odd_of_mem_pGroup hp hp2 hX0p hx)
  have hX0c : ∀ x ∈ kaInner P, ∀ l ∈ L, x * l = l * x :=
    ka_centralizes_of_perfect L (kaInner P) hLperf (fun l hl => mem_normalizer_kaInner (hLN l hl))
      (fun x hx => hLn x (hX0R hx)) hX0p (hLp p hp hp2)
  have hfix := ka_fix_of_perfect hinj hp hPp L hLperf hLN hX0c
  have hPinn : P ≤ innSub Y := fun e he =>
    hrig p hp hp2 e (IsPGroup.to_le hPp ((Subgroup.zpowers_le).2 he)) (hfix e he)
  refine ⟨hOut, ?_⟩
  have hcX := hcyc p hp hp2 (kaInner P) hX0p hX0R hX0c
  let φ : ↥(kaInner P) →* ↥P :=
    ((MulAut.conj : Y →* MulAut Y).comp (kaInner P).subtype).codRestrict P (fun y => y.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨e, he⟩
    obtain ⟨y, hy⟩ := hPinn he
    exact ⟨⟨y, by rw [mem_kaInner, hy]; exact he⟩, Subtype.ext hy⟩
  exact isCyclic_of_surjective φ hsurj

theorem ka_all_of_torus_fix (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R₀ L : Subgroup Y) (hR₀C : R₀ ≤ fixSub α)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R₀) (hLR₀ : L ≤ R₀)
    (hLn : ∀ x ∈ R₀, x ∈ normalizer (L : Set Y)) (hLperf : ⁅L, L⁆ = L)
    (hLp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m)
    (hfix : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut Y), IsPGroup p ↥P' →
      (∀ e ∈ P', ∀ r ∈ L, e r = r) → IsCyclic ↥P')
    (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, -, hcomm, hnorm⟩ := hP
  have hLC : L ≤ fixSub α := hLR₀.trans hR₀C
  have hLN : ∀ l ∈ L, MulAut.conj l ∈ normalizer (P : Set (MulAut Y)) := by
    let H : Subgroup Y := (normalizer (P : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
    have hle : L ≤ H := ka_perfect_le_of_odd L hLperf H fun x hx hodd' => hnorm x (hLC hx) hodd'
    exact fun l hl => hle hl
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0R : kaInner P ≤ R₀ := fun x hx =>
    hodd x (hX0C hx) (ka_odd_of_mem_pGroup hp hp2 hX0p hx)
  have hX0c : ∀ x ∈ kaInner P, ∀ l ∈ L, x * l = l * x :=
    ka_centralizes_of_perfect L (kaInner P) hLperf (fun l hl => mem_normalizer_kaInner (hLN l hl))
      (fun x hx => hLn x (hX0R hx)) hX0p (hLp p hp hp2)
  have hfixL := ka_fix_of_perfect hinj hp hPp L hLperf hLN hX0c
  exact ⟨hOut, hfix p hp hp2 P hPp hfixL⟩

end Torus

section Transport

theorem ka_congr_conj {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem KAAll.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {α : MulAut Y}
    (h : KAAll α) : KAAll (MulAut.congr e α) := by
  intro p hp hp2 P' hP'
  let f : MulAut Y →* MulAut Y' := (MulAut.congr e).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.congr e).injective
  have hfsurj : Function.Surjective f := (MulAut.congr e).surjective
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP'
  let P : Subgroup (MulAut Y) := P'.comap f
  have hPKA : KAHyp α p P := by
    refine ⟨IsPGroup.comap_of_injective hPp f hfinj, ?_, ?_, ?_⟩
    · intro hbot
      apply hP1
      have := Subgroup.map_comap_eq_self_of_surjective hfsurj P'
      rw [← this]
      change Subgroup.map f P = ⊥
      rw [hbot, Subgroup.map_bot]
    · intro x hx
      apply hfinj
      have h1 := hcomm (f x) hx
      show (MulAut.congr e) (x * α) = (MulAut.congr e) (α * x)
      rw [map_mul, map_mul]
      exact h1
    · intro c hc hodd
      have h1 : (MulAut.congr e α) (e c) = e (α c) := by simp [MulAut.congr_apply]
      have hc' : e c ∈ fixSub (MulAut.congr e α) := by
        rw [mem_fixSub, h1, (mem_fixSub.1 hc)]
      have h2 : orderOf (e c) = orderOf c := orderOf_injective e.toMonoidHom e.injective c
      have hN := hnorm (e c) hc' (by rw [h2]; exact hodd)
      have hconj : f (MulAut.conj c) = MulAut.conj (e c) := ka_congr_conj e c
      rw [Subgroup.mem_normalizer_iff] at hN ⊢
      intro x
      show f x ∈ P' ↔ f (MulAut.conj c * x * (MulAut.conj c)⁻¹) ∈ P'
      rw [map_mul, map_mul, map_inv, hconj]
      exact hN _
  obtain ⟨hOut, hcyc⟩ := h p hp hp2 P hPKA
  refine ⟨?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := hfsurj x'
    obtain ⟨y, hy⟩ := hOut x
    refine ⟨e y, ?_⟩
    rw [← ka_congr_conj, hy]
    exact map_commutatorElement (MulAut.congr e) x α
  · let g : ↥P →* ↥P' := (f.comp P.subtype).codRestrict P' (fun x => x.2)
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hfsurj y
      exact ⟨⟨x, hy⟩, rfl⟩
    exact isCyclic_of_surjective g hg

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
