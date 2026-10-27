module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalGroups.PCoreSection

open CFSG.Open

section PCoreOf

variable {G : Type*} [Group G]

theorem isPGroup_pCoreOf (p : ℕ) (X : Subgroup G) : IsPGroup p (pCoreOf p X) :=
  CFSG.pCore_isPGroup.map _

theorem conj_mem_pCoreOf {p : ℕ} {X : Subgroup G} {g o : G} (hg : g ∈ X)
    (ho : o ∈ pCoreOf p X) : g * o * g⁻¹ ∈ pCoreOf p X := by
  unfold pCoreOf at ho ⊢
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem pCoreOf_le (p : ℕ) (X : Subgroup G) : pCoreOf p X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_pCoreOf {p : ℕ} {X N : Subgroup G} (hNX : N ≤ X)
    (hn : ∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hp : IsPGroup p N) : N ≤ pCoreOf p X := by
  have hnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hNX).2 fun h k hh hk => hn k hk h hh
  have hp' : IsPGroup p (N.subgroupOf X) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hle : N.subgroupOf X ≤ CFSG.pCore p ↥X := le_sSup ⟨hnorm, hp'⟩
  intro x hx
  exact ⟨⟨x, hNX hx⟩, hle (show (⟨x, hNX hx⟩ : ↥X) ∈ N.subgroupOf X from hx), rfl⟩

end PCoreOf

section Action

structure IsLinearAction (K : Type*) {V G : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [Monoid G] (app : G → V → V) : Prop where
  one : ∀ x, app 1 x = x
  mul : ∀ g h x, app (g * h) x = app g (app h x)
  add : ∀ g x y, app g (x + y) = app g x + app g y
  smul : ∀ (g : G) (c : K) x, app g (c • x) = c • app g x

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G] {app : G → V → V}

theorem IsLinearAction.map_zero (h : IsLinearAction K app) (g : G) : app g 0 = 0 := by
  simpa using h.add g 0 0

theorem IsLinearAction.map_sub (h : IsLinearAction K app) (g : G) (x y : V) :
    app g (x - y) = app g x - app g y := by
  rw [eq_sub_iff_add_eq, ← h.add, sub_add_cancel]

theorem IsLinearAction.pow_apply (h : IsLinearAction K app) (t : G) (n : ℕ) {u : V} {c : K}
    (hu : app t u = c • u) : app (t ^ n) u = c ^ n • u := by
  induction n with
  | zero => rw [pow_zero, h.one, pow_zero, one_smul]
  | succ n ih => rw [pow_succ, h.mul, hu, h.smul, ih, smul_smul, pow_succ, mul_comm]

theorem eq_one_of_apply_eq_smul [CharP K 2] (h : IsLinearAction K app) {t : G} {k : ℕ}
    (ht : t ^ 2 ^ k = 1) {u : V} (hu : u ≠ 0) {c : K} (htu : app t u = c • u) : c = 1 := by
  have h1 : c ^ 2 ^ k • u = u := by
    rw [← h.pow_apply t (2 ^ k) htu, ht, h.one]
  have h2 : c ^ 2 ^ k = 1 := by
    have h3 : (c ^ 2 ^ k - 1) • u = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu)
  have h3 : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h2, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.mp h3)

section Section

variable [Finite K] [CharP K 2] [Finite V]

theorem exists_fixed_mem_of_isPGroup (h : IsLinearAction K app) {T : Subgroup G}
    (hT : IsPGroup 2 T) {L P : Submodule K V} (hLP : L ≤ P)
    (hP : ∀ t ∈ T, ∀ x ∈ P, app t x ∈ P) (hL : ∀ t ∈ T, ∀ x ∈ L, app t x ∈ L)
    (hne : L ≠ P) : ∃ x ∈ P, x ∉ L ∧ ∀ t ∈ T, app t x - x ∈ L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let r : T → (P →ₗ[K] P) := fun t =>
    { toFun := fun x => ⟨app t x, hP t t.2 x x.2⟩
      map_add' := fun x y => Subtype.ext (h.add t x y)
      map_smul' := fun c x => Subtype.ext (h.smul t c x) }
  let L' : Submodule K P := L.comap P.subtype
  have hr : ∀ t : T, L' ≤ L'.comap (r t) := fun t x hx => hL t t.2 x hx
  letI : MulAction T (P ⧸ L') :=
    { smul := fun t w => L'.mapQ L' (r t) (hr t) w
      one_smul := fun w => Submodule.Quotient.induction_on L' w fun x =>
        congrArg (Submodule.Quotient.mk (p := L')) (Subtype.ext (h.one x))
      mul_smul := fun a b w => Submodule.Quotient.induction_on L' w fun x =>
        congrArg (Submodule.Quotient.mk (p := L')) (Subtype.ext (h.mul a b x)) }
  obtain ⟨x₀, hx₀P, hx₀L⟩ : ∃ x ∈ P, x ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hLP hcon)
  have hW : Nontrivial (P ⧸ L') := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    have : (⟨x₀, hx₀P⟩ : P) ∈ L' := by rw [htop]; trivial
    exact hx₀L this
  haveI : Finite P := Subtype.finite
  haveI : Module.Finite K P := Module.Finite.of_finite
  haveI : Finite (P ⧸ L') := Module.finite_of_finite K
  have hdvd : 2 ∣ Nat.card (P ⧸ L') := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := P ⧸ L')]
    have hK : 2 ∣ Nat.card K := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    exact dvd_pow hK (Module.finrank_pos (R := K) (M := P ⧸ L')).ne'
  have h0 : (0 : P ⧸ L') ∈ MulAction.fixedPoints T (P ⧸ L') := fun t =>
    map_zero (L'.mapQ L' (r t) (hr t))
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (P ⧸ L') hdvd h0
  obtain ⟨⟨x, hxP⟩, rfl⟩ := Submodule.Quotient.mk_surjective L' b
  refine ⟨x, hxP, ?_, fun t ht => ?_⟩
  · intro hxL
    exact hb0 ((Submodule.Quotient.mk_eq_zero L').mpr hxL).symm
  · exact (Submodule.Quotient.eq L').mp (MulAction.mem_fixedPoints.mp hb ⟨t, ht⟩)

theorem apply_sub_mem_of_isPGroup (h : IsLinearAction K app) {S T : Subgroup G} (hTS : T ≤ S)
    (hT : IsPGroup 2 T) (hTn : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) {L P : Submodule K V}
    (hLP : L ≤ P) (hP : ∀ s ∈ S, ∀ x ∈ P, app s x ∈ P) (hL : ∀ s ∈ S, ∀ x ∈ L, app s x ∈ L)
    (hirr : ∀ X : Submodule K V, L ≤ X → X ≤ P → (∀ s ∈ S, ∀ x ∈ X, app s x ∈ X) →
      X = L ∨ X = P) :
    ∀ t ∈ T, ∀ x ∈ P, app t x - x ∈ L := by
  let X : Submodule K V :=
    { carrier := {x | x ∈ P ∧ ∀ t ∈ T, app t x - x ∈ L}
      add_mem' := fun {a b} ha hb => ⟨P.add_mem ha.1 hb.1, fun t ht => by
        have := L.add_mem (ha.2 t ht) (hb.2 t ht)
        rw [h.add]
        convert this using 1
        abel⟩
      zero_mem' := ⟨P.zero_mem, fun t _ => by rw [h.map_zero, sub_zero]; exact L.zero_mem⟩
      smul_mem' := fun c {a} ha => ⟨P.smul_mem c ha.1, fun t ht => by
        have := L.smul_mem c (ha.2 t ht)
        rw [h.smul, ← smul_sub]
        exact this⟩ }
  have hLX : L ≤ X := fun x hx => ⟨hLP hx, fun t ht => L.sub_mem (hL t (hTS ht) x hx) hx⟩
  have hXP : X ≤ P := fun x hx => hx.1
  have hXinv : ∀ s ∈ S, ∀ x ∈ X, app s x ∈ X := by
    intro s hs x hx
    refine ⟨hP s hs x hx.1, fun t ht => ?_⟩
    have ht' : s⁻¹ * t * s ∈ T := by
      simpa using hTn s⁻¹ (inv_mem hs) t ht
    have key : app t (app s x) = app s (app (s⁻¹ * t * s) x) := by
      rw [← h.mul, ← h.mul]
      congr 1
      group
    rw [key, ← h.map_sub]
    exact hL s hs _ (hx.2 _ ht')
  have hX : X = P := by
    rcases hirr X hLX hXP hXinv with hXL | hXP'
    · by_contra hne
      obtain ⟨y, hyP, hyL, hy⟩ := exists_fixed_mem_of_isPGroup h hT hLP
        (fun t ht => hP t (hTS ht)) (fun t ht => hL t (hTS ht)) (fun hLP' => hne (hXL.trans hLP'))
      exact hyL (hXL ▸ (show y ∈ X from ⟨hyP, hy⟩))
    · exact hXP'
  intro t ht x hx
  exact (show x ∈ X from hX ▸ hx).2 t ht

theorem eq_pCoreOf_of_section (h : IsLinearAction K app) {S N : Subgroup G} {u : V}
    (hu : u ≠ 0) (hS : ∀ s ∈ S, ∃ c : K, app s u = c • u) (hNS : N ≤ S)
    (hNn : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN : IsPGroup 2 N) {L P : Submodule K V}
    (hLP : L ≤ P) (hP : ∀ s ∈ S, ∀ x ∈ P, app s x ∈ P) (hL : ∀ s ∈ S, ∀ x ∈ L, app s x ∈ L)
    (hirr : ∀ X : Submodule K V, L ≤ X → X ≤ P → (∀ s ∈ S, ∀ x ∈ X, app s x ∈ X) →
      X = L ∨ X = P)
    (hmem : ∀ g ∈ S, app g u = u → (∀ x ∈ P, app g x - x ∈ L) → g ∈ N) :
    N = pCoreOf 2 S := by
  refine le_antisymm (le_pCoreOf hNS hNn hN) fun t ht => ?_
  have htS : t ∈ S := pCoreOf_le 2 S ht
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_pCoreOf 2 S ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨c, hc⟩ := hS t htS
  have hc1 : c = 1 := eq_one_of_apply_eq_smul h hk hu hc
  rw [hc1, one_smul] at hc
  exact hmem t htS hc (apply_sub_mem_of_isPGroup h (pCoreOf_le 2 S) (isPGroup_pCoreOf 2 S)
    (fun s hs t' ht' => conj_mem_pCoreOf hs ht') hLP hP hL hirr t ht)

end Section

end Action

end CFSG.ClassicalGroups.PCoreSection
