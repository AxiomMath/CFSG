module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup

namespace CoprimeCompl

variable {Q : Type*} [Group Q]

@[expose] def normProd (δ : MulAut Q) : ℕ → Q → Q
  | 0, _ => 1
  | n + 1, q => normProd δ n q * (δ ^ n) q

variable (δ : MulAut Q)

theorem normProd_zero (q : Q) : normProd δ 0 q = 1 := rfl

theorem normProd_succ (n : ℕ) (q : Q) : normProd δ (n + 1) q = normProd δ n q * (δ ^ n) q := rfl

variable (hcomm : ∀ a b : Q, a * b = b * a)
include hcomm

theorem normProd_mul (n : ℕ) (q r : Q) :
    normProd δ n (q * r) = normProd δ n q * normProd δ n r := by
  induction n with
  | zero => simp [normProd_zero]
  | succ n ih =>
    rw [normProd_succ, normProd_succ, normProd_succ, ih, map_mul]
    rw [mul_assoc, ← mul_assoc (normProd δ n r), hcomm (normProd δ n r) ((δ ^ n) q)]
    simp only [mul_assoc]

omit hcomm in
theorem normProd_one (n : ℕ) : normProd δ n (1 : Q) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [normProd_succ, ih, map_one, one_mul]

theorem normProd_inv (n : ℕ) (q : Q) : normProd δ n q⁻¹ = (normProd δ n q)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← normProd_mul δ hcomm, inv_mul_cancel, normProd_one]

omit hcomm in
theorem apply_normProd (n : ℕ) (q : Q) : δ (normProd δ n q) = normProd δ n (δ q) := by
  induction n with
  | zero => simp [normProd_zero]
  | succ n ih =>
    rw [normProd_succ, normProd_succ, map_mul, ih]
    congr 1
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ', pow_succ]

omit hcomm in
theorem normProd_succ' (n : ℕ) (q : Q) : normProd δ (n + 1) q = q * normProd δ n (δ q) := by
  induction n with
  | zero => simp [normProd_succ, normProd_zero]
  | succ n ih =>
    rw [normProd_succ, ih, normProd_succ, mul_assoc]
    congr 2

theorem apply_normProd_eq {m : ℕ} (hm : δ ^ m = 1) (q : Q) :
    δ (normProd δ m q) = normProd δ m q := by
  rw [apply_normProd]
  have h1 := normProd_succ' δ m q
  rw [normProd_succ, hm, MulAut.one_apply] at h1
  have h2 : normProd δ m q = q * normProd δ m (δ q) * q⁻¹ := by
    rw [← h1, mul_inv_cancel_right]
  rw [h2, hcomm q, mul_inv_cancel_right]

omit hcomm in
theorem pow_apply_of_fixed {c : Q} (hc : δ c = c) (n : ℕ) : (δ ^ n) c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hc, ih]

omit hcomm in
theorem normProd_of_fixed {c : Q} (hc : δ c = c) (n : ℕ) : normProd δ n c = c ^ n := by
  induction n with
  | zero => rw [normProd_zero, pow_zero]
  | succ n ih => rw [normProd_succ, ih, pow_apply_of_fixed δ hc, pow_succ]

@[expose] def normHom (m : ℕ) : Q →* Q where
  toFun := normProd δ m
  map_one' := normProd_one δ m
  map_mul' := normProd_mul δ hcomm m

theorem normHom_apply (m : ℕ) (q : Q) : normHom δ hcomm m q = normProd δ m q := rfl

variable {m : ℕ} (hm : δ ^ m = 1) (hodd : Odd m) (hsq : ∀ q : Q, q * q = 1)
include hm

omit hm in
theorem apply_mem_ker {q : Q} (hq : q ∈ (normHom δ hcomm m).ker) :
    δ q ∈ (normHom δ hcomm m).ker := by
  rw [MonoidHom.mem_ker, normHom_apply] at hq ⊢
  rw [← apply_normProd, hq, map_one]

include hodd hsq

theorem eq_one_of_mem_ker {c : Q} (hc : δ c = c) (hk : c ∈ (normHom δ hcomm m).ker) : c = 1 := by
  rw [MonoidHom.mem_ker, normHom_apply, normProd_of_fixed δ hc] at hk
  obtain ⟨k, rfl⟩ := hodd
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hk
  exact hk

theorem exists_mul_eq (q : Q) :
    ∃ k ∈ (normHom δ hcomm m).ker, ∃ c, δ c = c ∧ q = k * c := by
  refine ⟨q * (normProd δ m q)⁻¹, ?_, normProd δ m q, apply_normProd_eq δ hcomm hm q,
    (inv_mul_cancel_right q (normProd δ m q)).symm⟩
  rw [MonoidHom.mem_ker, normHom_apply, normProd_mul δ hcomm, normProd_inv δ hcomm,
    normProd_of_fixed δ (apply_normProd_eq δ hcomm hm q)]
  obtain ⟨k, rfl⟩ := hodd
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul, mul_inv_cancel]

omit hodd hsq in
theorem le_ker {U : Subgroup Q} (hU : ∀ u ∈ U, δ u ∈ U) (hUC : ∀ u ∈ U, δ u = u → u = 1) :
    U ≤ (normHom δ hcomm m).ker := by
  have hpow : ∀ (n : ℕ) {u : Q}, u ∈ U → (δ ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => intro u hu; exact hu
    | succ n ih => intro u hu; rw [pow_succ, MulAut.mul_apply]; exact ih (hU u hu)
  have hnorm : ∀ (n : ℕ) {u : Q}, u ∈ U → normProd δ n u ∈ U := by
    intro n
    induction n with
    | zero => intro u _; exact U.one_mem
    | succ n ih => intro u hu; exact U.mul_mem (ih hu) (hpow n hu)
  intro u hu
  rw [MonoidHom.mem_ker, normHom_apply]
  exact hUC _ (hnorm m hu) (apply_normProd_eq δ hcomm hm u)

end CoprimeCompl

section Group

variable {G : Type*} [Group G]

structure ComplData (P A Z : Subgroup G) (d : G) : Prop where
  A_le : A ≤ Z
  Z_le : Z ≤ P
  normal : ∀ p ∈ P, ∀ a ∈ A, p * a * p⁻¹ ∈ A
  comm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ A
  sq : ∀ x ∈ P, x * x ∈ A
  normP : d ∈ Subgroup.normalizer (P : Set G)
  normA : d ∈ Subgroup.normalizer (A : Set G)
  odd : Odd (orderOf d)
  fix : ∀ x ∈ P, d * x * d⁻¹ * x⁻¹ ∈ A ↔ x ∈ Z

open CoprimeCompl in
theorem exists_compl {P A Z : Subgroup G} {d : G} (hD : ComplData P A Z d) :
    ∃ U : Subgroup G, A ≤ U ∧ U ≤ P ∧ U ⊓ Z = A ∧ (∀ x ∈ P, ∃ u ∈ U, ∃ z ∈ Z, x = u * z) ∧
      (∀ u ∈ U, d * u * d⁻¹ ∈ U) ∧
      ∀ U' : Subgroup G, A ≤ U' → U' ≤ P → U' ⊓ Z = A → (∀ u ∈ U', d * u * d⁻¹ ∈ U') →
        U' ≤ U := by
  classical
  have hAP : A ≤ P := hD.A_le.trans hD.Z_le
  set A' := A.subgroupOf P with hA'
  have hAn : A'.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hD.normal g g.2 n hn⟩
  set Q := ↥P ⧸ A'
  set π : ↥P →* Q := QuotientGroup.mk' A' with hπ
  have hπeq : ∀ x y : ↥P, π x = π y ↔ (x : G)⁻¹ * y ∈ A := fun x y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp
  have hπone : ∀ x : ↥P, π x = 1 ↔ (x : G) ∈ A := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A' a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective A' b
    rw [← map_mul, ← map_mul]
    refine (hπeq _ _).mpr ?_
    have := hD.comm _ (inv_mem y.2) _ (inv_mem x.2)
    simpa [mul_assoc] using this
  have hsq : ∀ q : Q, q * q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A' q
    rw [← map_mul]
    exact (hπone _).mpr (hD.sq _ x.2)
  set e : MulAut ↥P := P.normalizerMonoidHom ⟨d, hD.normP⟩ with he
  have heapp : ∀ x : ↥P, ((e x : ↥P) : G) = d * x * d⁻¹ := fun x =>
    normalizerMonoidHom_apply_apply_coe P ⟨d, hD.normP⟩ x
  have hemap : A'.map (e : ↥P →* ↥P) = A' := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_subgroupOf] at hy ⊢
      change ((e y : ↥P) : G) ∈ A
      rw [heapp]
      exact (mem_normalizer_iff.mp hD.normA y).mp hy
    · intro hx
      rw [mem_subgroupOf] at hx
      have h1 : d⁻¹ * (x : G) * d ∈ P := by
        have := (mem_normalizer_iff.mp (inv_mem hD.normP) x).mp x.2
        simpa using this
      have h2 : d⁻¹ * (x : G) * d ∈ A := by
        have := (mem_normalizer_iff.mp (inv_mem hD.normA) x).mp hx
        simpa using this
      refine ⟨⟨d⁻¹ * x * d, h1⟩, mem_subgroupOf.mpr h2, Subtype.ext ?_⟩
      change ((e ⟨d⁻¹ * x * d, h1⟩ : ↥P) : G) = x
      rw [heapp]
      group
  set δ : MulAut Q := QuotientGroup.congr A' A' e hemap with hδ
  have hδπ : ∀ x : ↥P, δ (π x) = π (e x) := fun x => QuotientGroup.congr_mk' _ _ _ _ x
  set m := orderOf d with hmdef
  have hpowP : ∀ (n : ℕ) (x : ↥P), d ^ n * (x : G) * (d ^ n)⁻¹ ∈ P := fun n x => by
    simpa using (mem_normalizer_iff.mp (pow_mem hD.normP n) x).mp x.2
  have hδpow : ∀ (n : ℕ) (x : ↥P), (δ ^ n) (π x) = π ⟨d ^ n * x * (d ^ n)⁻¹, hpowP n x⟩ := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, MulAut.one_apply]
      exact congrArg π (Subtype.ext (by simp))
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hδπ, ih]
      refine congrArg π (Subtype.ext ?_)
      simp only [heapp]
      group
  have hm : δ ^ m = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A' q
    change (δ ^ m) (π x) = π x
    rw [hδpow]
    refine congrArg π (Subtype.ext ?_)
    simp [hmdef, pow_orderOf_eq_one]
  have hfixQ : ∀ x : ↥P, δ (π x) = π x ↔ (x : G) ∈ Z := by
    intro x
    rw [hδπ, eq_comm, hπeq, heapp, ← hD.fix _ x.2]
    constructor
    · intro h1
      have h2 := hD.normal _ x.2 _ h1
      have e1 : (x : G) * ((x : G)⁻¹ * (d * x * d⁻¹)) * (x : G)⁻¹ = d * x * d⁻¹ * (x : G)⁻¹ := by
        group
      rwa [e1] at h2
    · intro h1
      have h2 := hD.normal _ (inv_mem x.2) _ h1
      have e1 : (x : G)⁻¹ * (d * x * d⁻¹ * (x : G)⁻¹) * (x : G)⁻¹⁻¹ =
          (x : G)⁻¹ * (d * x * d⁻¹) := by
        group
      rwa [e1] at h2
  set K := (normHom δ hcomm m).ker with hK
  have hAU : ∀ a ∈ A, a ∈ (K.comap π).map P.subtype := fun a ha =>
    ⟨⟨a, hAP ha⟩, show π ⟨a, hAP ha⟩ ∈ K by rw [(hπone _).mpr ha]; exact K.one_mem, rfl⟩
  refine ⟨(K.comap π).map P.subtype, hAU, map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm _ (le_inf hAU hD.A_le)
    rintro _ ⟨⟨x, hxK, rfl⟩, hxZ⟩
    have h1 := eq_one_of_mem_ker δ hcomm hm hD.odd hsq ((hfixQ x).mpr hxZ) hxK
    exact (hπone x).mp h1
  · intro x hx
    obtain ⟨k, hk, c, hc, hkc⟩ := exists_mul_eq δ hcomm hm hD.odd hsq (π ⟨x, hx⟩)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective A' k
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective A' c
    have hzZ := (hfixQ z).mp hc
    have h1 : π ⟨x, hx⟩ = π (u * z) := by rw [hkc, map_mul]
    rw [hπeq] at h1
    have h2 : ((u * z : ↥P) : G)⁻¹ * x ∈ A := by
      have := inv_mem h1
      simpa [mul_inv_rev] using this
    refine ⟨u, ⟨u, hk, rfl⟩, z * (((u * z : ↥P) : G)⁻¹ * x), ?_, ?_⟩
    · exact mul_mem hzZ (hD.A_le h2)
    · simp only [coe_mul]
      group
  · rintro _ ⟨x, hxK, rfl⟩
    refine ⟨e x, ?_, heapp x⟩
    show π (e x) ∈ K
    rw [← hδπ]
    exact apply_mem_ker δ hcomm (show π x ∈ K from hxK)
  · intro U' hAU' hU'P hU'Z hU'd
    set Ū := (U'.subgroupOf P).map π
    have hŪ : Ū ≤ K := by
      apply le_ker δ hcomm hm
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨e x, ?_, (hδπ x).symm⟩
        rw [SetLike.mem_coe, mem_subgroupOf] at hx ⊢
        rw [heapp]
        exact hU'd _ hx
      · rintro _ ⟨x, hx, rfl⟩ hfx
        have hxZ := (hfixQ x).mp hfx
        rw [SetLike.mem_coe, mem_subgroupOf] at hx
        have : (x : G) ∈ U' ⊓ Z := mem_inf.mpr ⟨hx, hxZ⟩
        rw [hU'Z] at this
        exact (hπone x).mpr this
    intro u hu
    exact ⟨⟨u, hU'P hu⟩, hŪ ⟨⟨u, hU'P hu⟩, mem_subgroupOf.mpr hu, rfl⟩, rfl⟩

end Group

end CFSG.ComponentClassification.GMS78
