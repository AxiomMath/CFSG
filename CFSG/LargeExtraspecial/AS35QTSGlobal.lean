module

public import CFSG.LargeExtraspecial.AS35QTSLocal
public import CFSG.LargeExtraspecial.AS35JFiveNine

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type} [Group G] (S : Setting G)

theorem isConj_conj {x : G} (g : G) (hx : IsConj S.z x) : IsConj S.z (g * x * g⁻¹) :=
  hx.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem conj_mem_lineSet {d c y : G} (g : G) (hy : y ∈ lineSet S d c) :
    g * y * g⁻¹ ∈ lineSet S (g * d * g⁻¹) (g * c * g⁻¹) := by
  obtain ⟨hyz, hyd, hyc⟩ := hy
  refine ⟨isConj_conj S g hyz, ?_, ?_⟩
  · calc g * y * g⁻¹ * (g * d * g⁻¹) = g * (y * d) * g⁻¹ := by group
      _ = g * (d * y) * g⁻¹ := by rw [hyd]
      _ = g * d * g⁻¹ * (g * y * g⁻¹) := by group
  · calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [hyc]
      _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group

theorem lineSet_conj (d c g : G) :
    lineSet S (g * d * g⁻¹) (g * c * g⁻¹) = (fun y => g * y * g⁻¹) '' lineSet S d c := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have := conj_mem_lineSet S g⁻¹ hy
    simpa [mul_assoc] using this
  · rintro ⟨y', hy', rfl⟩
    exact conj_mem_lineSet S g hy'

theorem commute_conj {a b : G} (g : G) (h : a * b = b * a) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem commute_conj_inv {a b : G} (g : G) (h : g * a * g⁻¹ * (g * b * g⁻¹) =
    g * b * g⁻¹ * (g * a * g⁻¹)) : a * b = b * a := by
  have := commute_conj g⁻¹ h
  simpa [mul_assoc] using this

theorem conj_inv_mem_M {g c : G} (hc : c * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * c) :
    g⁻¹ * c * g ∈ S.M := by
  rw [S.mem_M_iff]
  have := commute_conj_inv (a := g⁻¹ * c * g) (b := S.z) g (by simpa [mul_assoc] using hc)
  exact this

theorem lineSet_eq_image {g c : G} :
    lineSet S (g * S.z * g⁻¹) c = (fun y => g * y * g⁻¹) '' lineSet S S.z (g⁻¹ * c * g) := by
  rw [← lineSet_conj]
  congr 1
  group

theorem conj_inv_mem_lineSet {g c y : G} (hy : y ∈ lineSet S (g * S.z * g⁻¹) c) :
    g⁻¹ * y * g ∈ lineSet S S.z (g⁻¹ * c * g) := by
  have := conj_mem_lineSet S g⁻¹ hy
  simpa [mul_assoc] using this

theorem self_mem_lineSet {d c : G} (hd : IsConj S.z d) (hcd : c * d = d * c) :
    d ∈ lineSet S d c :=
  ⟨hd, rfl, hcd.symm⟩

theorem mem_lineSet_right {d c : G} (hc : IsConj S.z c) (hcd : c * d = d * c) :
    c ∈ lineSet S d c :=
  ⟨hc, hcd, rfl⟩

theorem lineSet_symm (d c : G) : lineSet S d c = lineSet S c d := by
  ext y
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩

theorem exists_fixed_of_involutive {α : Type*} {s : Set α} (hfin : s.Finite)
    (hodd : Odd s.ncard) (f : α → α) (hf : ∀ x ∈ s, f x ∈ s) (hff : ∀ x ∈ s, f (f x) = x) :
    ∃ c ∈ s, f c = c := by
  classical
  have : Fintype s := hfin.fintype
  let σ : Equiv.Perm s :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      invFun := fun x => ⟨f x, hf x x.2⟩
      left_inv := fun x => Subtype.ext (hff x x.2)
      right_inv := fun x => Subtype.ext (hff x x.2) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Equiv.ext fun x => Subtype.ext (hff x x.2)
  have hcard : ¬ 2 ∣ Fintype.card s := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem conj_pow_of_dihedral {d u : G} (hd : d * d = 1) (hu : u * u = 1) (k : ℕ) :
    d * (d * u) ^ k * d = ((d * u) ^ k)⁻¹ := by
  have h1 : d * (d * u) * d = (d * u)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hd, ← mul_assoc,
      hd, one_mul]
  induction k with
  | zero => simp [hd]
  | succ k ih =>
    calc d * (d * u) ^ (k + 1) * d = (d * (d * u) ^ k * d) * (d * (d * u) * d) := by
          rw [pow_succ, show d * ((d * u) ^ k * (d * u)) * d =
            d * (d * u) ^ k * (d * d) * (d * u) * d by rw [hd]; group]
          group
      _ = ((d * u) ^ k)⁻¹ * (d * u)⁻¹ := by rw [ih, h1]
      _ = ((d * u) ^ (k + 1))⁻¹ := by rw [← mul_inv_rev, ← pow_succ']

theorem isConj_reflection {d u : G} (hd : d * d = 1) (hu : u * u = 1) (j : ℕ) :
    IsConj d (d * (d * u) ^ (2 * j)) ∧ IsConj u (d * (d * u) ^ (2 * j + 1)) := by
  set r := d * u with hr
  have key : ∀ k : ℕ, d * r ^ k = (r ^ k)⁻¹ * d := by
    intro k
    calc d * r ^ k = d * r ^ k * d * d := by rw [mul_assoc _ d d, hd, mul_one]
      _ = (r ^ k)⁻¹ * d := by rw [conj_pow_of_dihedral hd hu k]
  constructor
  · refine isConj_iff.mpr ⟨(r ^ j)⁻¹, ?_⟩
    calc (r ^ j)⁻¹ * d * (r ^ j)⁻¹⁻¹ = (r ^ j)⁻¹ * (d * r ^ j) := by group
      _ = (r ^ j)⁻¹ * ((r ^ j)⁻¹ * d) := by rw [key j]
      _ = (r ^ j * r ^ j)⁻¹ * d := by group
      _ = (r ^ (2 * j))⁻¹ * d := by rw [← pow_add, two_mul]
      _ = d * r ^ (2 * j) := (key (2 * j)).symm
  · refine isConj_iff.mpr ⟨(r ^ j)⁻¹, ?_⟩
    have hdu : u = d * r := by rw [hr, ← mul_assoc, hd, one_mul]
    calc (r ^ j)⁻¹ * u * (r ^ j)⁻¹⁻¹ = (r ^ j)⁻¹ * (d * (r * r ^ j)) := by rw [hdu]; group
      _ = (r ^ j)⁻¹ * (d * r ^ (j + 1)) := by rw [← pow_succ']
      _ = (r ^ j)⁻¹ * ((r ^ (j + 1))⁻¹ * d) := by rw [key (j + 1)]
      _ = (r ^ (j + 1) * r ^ j)⁻¹ * d := by group
      _ = (r ^ (2 * j + 1))⁻¹ * d := by rw [← pow_add]; ring_nf
      _ = d * r ^ (2 * j + 1) := (key (2 * j + 1)).symm

theorem commute_of_sq_eq_one {d u : G} (hd : d * d = 1) (hu : u * u = 1)
    (h : (d * u) ^ 2 = 1) : d * u = u * d := by
  rw [pow_two] at h
  calc d * u = d * u * (d * u) * (u * d) := by
        rw [show d * u * (d * u) * (u * d) = d * u * d * (u * u) * d by group, hu, mul_one,
          mul_assoc, hd, mul_one]
    _ = u * d := by rw [h, one_mul]

theorem exists_conj_mem_M [Finite G] {y : G} (hy : y * y = 1) : ∃ g : G, g⁻¹ * y * g ∈ S.M := by
  obtain ⟨P₀, -, hP₀⟩ := S.exists_sylow_le_M
  have hp : IsPGroup 2 (zpowers y) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨x, k, rfl⟩ := x
    apply Subtype.ext
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hy, one_zpow]
  obtain ⟨P', hP'⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P'
  have hyP : y ∈ (P' : Subgroup G) := hP' (mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def] at hyP
  refine ⟨g, hP₀ ?_⟩
  simpa [MulAut.conj_apply] using hyP

namespace Chart

variable {S} [Finite G] (T : Chart S)

include T in
theorem ncard_lineSet_at (hS : S.SixHyp) {d c : G} (hd : IsConj S.z d) (hc : IsConj S.z c)
    (hcd : c * d = d * c) (hne : c ≠ d) : (lineSet S d c).ncard = 5 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have hcM := conj_inv_mem_M S hcd
  have hcz : IsConj S.z (g⁻¹ * c * g) := by simpa using isConj_conj S g⁻¹ hc
  have hcne : g⁻¹ * c * g ≠ S.z := by
    intro h
    apply hne
    rw [← h]
    group
  rw [lineSet_eq_image S, Set.InjOn.ncard_image]
  · exact T.ncard_lineSet hS hcM hcz hcne
  · intro x _ y _ h
    simpa using h

include T in
theorem commute_of_mem_lineSet_at (hS : S.SixHyp) {d c : G} (hd : IsConj S.z d)
    (hc : IsConj S.z c) (hcd : c * d = d * c) (hne : c ≠ d) {a b : G} (ha : a ∈ lineSet S d c)
    (hb : b ∈ lineSet S d c) : a * b = b * a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have hcM := conj_inv_mem_M S hcd
  have hcz : IsConj S.z (g⁻¹ * c * g) := by simpa using isConj_conj S g⁻¹ hc
  have hcne : g⁻¹ * c * g ≠ S.z := fun h => hne (by rw [← h]; group)
  have h := T.commute_of_mem_lineSet hS hcM hcz hcne (conj_inv_mem_lineSet S ha)
    (conj_inv_mem_lineSet S hb)
  have := commute_conj g h
  simpa [mul_assoc] using this

include T in
theorem lineSet_eq_at (hS : S.SixHyp) {d c p : G} (hd : IsConj S.z d) (hc : IsConj S.z c)
    (hcd : c * d = d * c) (hne : c ≠ d) (hp : p ∈ lineSet S d c) (hpd : p ≠ d) :
    lineSet S d p = lineSet S d c := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have hcM := conj_inv_mem_M S hcd
  have hcz : IsConj S.z (g⁻¹ * c * g) := by simpa using isConj_conj S g⁻¹ hc
  have hcne : g⁻¹ * c * g ≠ S.z := fun h => hne (by rw [← h]; group)
  have hpz : g⁻¹ * p * g ≠ S.z := fun h => hpd (by rw [← h]; group)
  rw [lineSet_eq_image S (c := p), lineSet_eq_image S (c := c),
    T.lineSet_eq hS hcM hcz hcne (conj_inv_mem_lineSet S hp) hpz]

include T in
theorem eq_of_mul_eq_at (hS : S.SixHyp) {d c : G} (hd : IsConj S.z d) (hc : IsConj S.z c)
    (hcd : c * d = d * c) (hne : c ≠ d) {a b a' b' : G} (ha : a ∈ lineSet S d c)
    (hb : b ∈ lineSet S d c) (ha' : a' ∈ lineSet S d c) (hb' : b' ∈ lineSet S d c)
    (hab : a ≠ b) (hab' : a' ≠ b') (he : a * b = a' * b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have hcM := conj_inv_mem_M S hcd
  have hcz : IsConj S.z (g⁻¹ * c * g) := by simpa using isConj_conj S g⁻¹ hc
  have hcne : g⁻¹ * c * g ≠ S.z := fun h => hne (by rw [← h]; group)
  have hinj : ∀ x y : G, g⁻¹ * x * g = g⁻¹ * y * g → x = y := fun x y h => by
    simpa using h
  have he' : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * a' * g * (g⁻¹ * b' * g) := by
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (a' * b') * g := by rw [he]
      _ = g⁻¹ * a' * g * (g⁻¹ * b' * g) := by group
  rcases T.eq_of_mul_eq hS hcM hcz hcne (conj_inv_mem_lineSet S ha) (conj_inv_mem_lineSet S hb)
    (conj_inv_mem_lineSet S ha') (conj_inv_mem_lineSet S hb')
    (fun h => hab (hinj _ _ h)) (fun h => hab' (hinj _ _ h)) he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hinj _ _ h1, hinj _ _ h2⟩
  · exact Or.inr ⟨hinj _ _ h1, hinj _ _ h2⟩

include T in
theorem lineSet_eq_of_mem (hS : S.SixHyp) {d c p p' : G} (hd : IsConj S.z d)
    (hc : IsConj S.z c) (hcd : c * d = d * c) (hne : c ≠ d) (hp : p ∈ lineSet S d c)
    (hp' : p' ∈ lineSet S d c) (hpp : p ≠ p') : lineSet S p p' = lineSet S d c := by
  by_cases hpd : p = d
  · subst hpd
    exact T.lineSet_eq_at hS hd hc hcd hne hp' (Ne.symm hpp)
  · have h1 : lineSet S d p = lineSet S d c := T.lineSet_eq_at hS hd hc hcd hne hp hpd
    have hpdc : p * d = d * p := hp.2.1
    rw [← h1, lineSet_symm S d p] at hp' ⊢
    exact T.lineSet_eq_at hS hp.1 hd hpdc.symm (Ne.symm hpd) hp' (Ne.symm hpp)

include T in
theorem orderOf_mul_dvd_at (hS : S.SixHyp) {d a b : G} (hd : IsConj S.z d)
    (ha : IsConj S.z a) (hb : IsConj S.z b) (had : a * d = d * a) (hbd : b * d = d * b) :
    (a * b) ^ 2 = 1 ∨ (a * b) ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have haM := conj_inv_mem_M S had
  have hbM := conj_inv_mem_M S hbd
  have haz : IsConj S.z (g⁻¹ * a * g) := by simpa using isConj_conj S g⁻¹ ha
  have hbz : IsConj S.z (g⁻¹ * b * g) := by simpa using isConj_conj S g⁻¹ hb
  have hpow : ∀ n : ℕ, (g⁻¹ * a * g * (g⁻¹ * b * g)) ^ n = g⁻¹ * (a * b) ^ n * g := by
    intro n
    rw [show g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g⁻¹⁻¹ by group, conj_pow, inv_inv]
  have hback : ∀ x : G, g⁻¹ * x * g = 1 → x = 1 := fun x h => by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases T.orderOf_mul_dvd hS haM hbM haz hbz with h | h
  · left
    rw [hpow] at h
    exact hback _ h
  · right
    rw [hpow] at h
    exact hback _ h

include T in
theorem ncard_DC (hS : S.SixHyp) {d : G} (hd : IsConj S.z d) :
    {x | IsConj S.z x ∧ x * d = d * x}.ncard = 37 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have e : {x | IsConj S.z x ∧ x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x} =
      (fun y => g * y * g⁻¹) '' {x | IsConj S.z x ∧ x ∈ S.M} := by
    ext x
    constructor
    · rintro ⟨hxz, hxd⟩
      refine ⟨g⁻¹ * x * g, ⟨by simpa using isConj_conj S g⁻¹ hxz, conj_inv_mem_M S hxd⟩, ?_⟩
      group
    · rintro ⟨y, ⟨hyz, hyM⟩, rfl⟩
      exact ⟨isConj_conj S g hyz, commute_conj g (S.mem_M_iff.mp hyM)⟩
  rw [e, Set.InjOn.ncard_image (fun x _ y _ h => by simpa using h)]
  exact T.ncard_DM hS

include T in
theorem sq_eq_one_of_pow_four (hS : S.SixHyp) {d u : G} (hd : IsConj S.z d) (hu : IsConj S.z u)
    (h4 : (d * u) ^ 4 = 1) : (d * u) ^ 2 = 1 := by
  by_contra h2
  have hdd := S.mul_self_of_isConj hd
  have huu := S.mul_self_of_isConj hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  set d' := u * d * u⁻¹ with hd'
  have hd'z : IsConj S.z d' := isConj_conj S u hd
  have hsq : (d * u) ^ 2 = d * d' := by
    rw [hd', huinv, pow_two]
    group
  have hcomm : d' * d = d * d' := by
    have h := h4
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq] at h
    have hd'd' := S.mul_self_of_isConj hd'z
    calc d' * d = (d * d') * (d * d') * (d' * d) := by rw [← pow_two, h, one_mul]
      _ = d * d' * d * (d' * d') * d := by group
      _ = d * d' := by rw [hd'd', mul_one, mul_assoc, hdd, mul_one]
  have hne : d' ≠ d := by
    intro h
    apply h2
    rw [hsq, h, hdd]
  set ℓ := lineSet S d d' with hℓ
  have hud : u * d' * u⁻¹ = d := by
    rw [hd', huinv]
    calc u * (u * d * u) * u = (u * u) * d * (u * u) := by group
      _ = d := by rw [huu, one_mul, mul_one]
  have hmaps : ∀ y ∈ ℓ, u * y * u⁻¹ ∈ ℓ := by
    intro y hy
    have := conj_mem_lineSet S u hy
    rw [← hd', hud, lineSet_symm] at this
    exact this
  have hinv : ∀ y ∈ ℓ, u * (u * y * u⁻¹) * u⁻¹ = y := by
    intro y _
    rw [huinv]
    calc u * (u * y * u) * u = (u * u) * y * (u * u) := by group
      _ = y := by rw [huu, one_mul, mul_one]
  have hodd : Odd ℓ.ncard := by
    rw [T.ncard_lineSet_at hS hd hd'z hcomm hne]
    decide
  obtain ⟨c, hc, hcu⟩ := exists_fixed_of_involutive (Set.toFinite ℓ) hodd
    (fun y => u * y * u⁻¹) hmaps hinv
  have hcd : c ≠ d := by
    intro h
    rw [h] at hcu
    exact hne hcu
  have huc : u * c = c * u := by
    calc u * c = u * c * u⁻¹ * u := by group
      _ = c * u := by rw [hcu]
  have hdc : d * c = c * d :=
    T.commute_of_mem_lineSet_at hS hd hd'z hcomm hne (self_mem_lineSet S hd hcomm) hc
  rcases T.orderOf_mul_dvd_at hS hc.1 hd hu hdc huc with h | h
  · exact h2 h
  · apply h2
    have h1 : d * u = 1 := by
      calc d * u = (d * u) ^ 4 * ((d * u) ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, h]; group
    rw [h1, one_pow]

include T in
theorem sq_eq_one_of_pow_two_pow (hS : S.SixHyp) {d u : G} (hd : IsConj S.z d)
    (hu : IsConj S.z u) : ∀ n : ℕ, (d * u) ^ 2 ^ n = 1 → (d * u) ^ 2 = 1 := by
  intro n
  induction n with
  | zero => intro h; rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | succ n ih =>
    intro h
    rcases n with _ | n
    · simpa using h
    ·
      have hdd := S.mul_self_of_isConj hd
      have huu := S.mul_self_of_isConj hu
      obtain ⟨j, hj⟩ | ⟨j, hj⟩ := Nat.even_or_odd (2 ^ n)
      · have hu' : IsConj S.z (d * (d * u) ^ (2 ^ n)) := by
          rw [hj, ← two_mul]
          exact hd.trans (isConj_reflection hdd huu j).1
        have hpow : (d * (d * (d * u) ^ (2 ^ n))) = (d * u) ^ (2 ^ n) := by
          rw [← mul_assoc, hdd, one_mul]
        have h4 := T.sq_eq_one_of_pow_four hS hd hu' (by
          rw [hpow, ← pow_mul]
          rw [show 2 ^ n * 4 = 2 ^ (n + 1 + 1) by ring]
          exact h)
        rw [hpow, ← pow_mul, show 2 ^ n * 2 = 2 ^ (n + 1) by ring] at h4
        exact ih h4
      · have hu' : IsConj S.z (d * (d * u) ^ (2 ^ n)) := by
          rw [hj]
          exact hu.trans (isConj_reflection hdd huu j).2
        have hpow : (d * (d * (d * u) ^ (2 ^ n))) = (d * u) ^ (2 ^ n) := by
          rw [← mul_assoc, hdd, one_mul]
        have h4 := T.sq_eq_one_of_pow_four hS hd hu' (by
          rw [hpow, ← pow_mul]
          rw [show 2 ^ n * 4 = 2 ^ (n + 1 + 1) by ring]
          exact h)
        rw [hpow, ← pow_mul, show 2 ^ n * 2 = 2 ^ (n + 1) by ring] at h4
        exact ih h4


include T in
theorem commute_of_commute_zt (hS : S.SixHyp) {t₀ : G} (ht₀ : t₀ ∈ S.DSet) {u : G}
    (hu : IsConj S.z u) (hcu : u * (S.z * t₀) = S.z * t₀ * u) :
    u * S.z = S.z * u ∧ u * t₀ = t₀ * u := by
  have hR := S.fiveNineOne_J hS ht₀
  have huc : u ∈ centralizer ({S.z * t₀} : Set G) := mem_centralizer_singleton_iff.mpr hcu
  have huu := S.mul_self_of_isConj hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have h1 : S.z * (u * S.z * u⁻¹) ∈ oTwoCent (S.z * t₀) :=
    (oTwoCent _).mul_mem hR (conj_mem_oTwoCent huc hR)
  have h2 : S.z * (u * S.z * u⁻¹) = (S.z * u) ^ 2 := by
    rw [huinv, pow_two]
    group
  obtain ⟨k, hk⟩ := isPGroup_oTwoCent (S.z * t₀) ⟨_, h1⟩
  have hk' : (S.z * u) ^ 2 ^ (k + 1) = 1 := by
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [h2, ← pow_mul, ← pow_succ'] at this
    exact this
  have hsq := T.sq_eq_one_of_pow_two_pow hS (IsConj.refl S.z) hu (k + 1) hk'
  have hzu := (commute_of_sq_eq_one S.z_mul_z huu hsq).symm
  refine ⟨hzu, ?_⟩
  have : S.z * (u * t₀) = S.z * (t₀ * u) := by
    calc S.z * (u * t₀) = u * S.z * t₀ := by rw [← mul_assoc, ← hzu]
      _ = S.z * t₀ * u := by rw [mul_assoc, hcu]
      _ = S.z * (t₀ * u) := by group
  exact mul_left_cancel this

include T in
theorem eq_or_eq_of_commute_zt (hS : S.SixHyp) {t₀ : G} (ht₀ : t₀ ∈ S.DSet) {c : G}
    (hc : c * (S.z * t₀) = S.z * t₀ * c) : c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t₀ := by
  have ht₀M := S.mem_M_of_mem_ESet hS.sixFour ht₀.1
  have ht₀z := S.isConj_of_mem_ESet ht₀.1
  have ht₀ne := S.ne_z_of_mem_ESet ht₀.1
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have hconj : c * (S.z * t₀) * c⁻¹ = S.z * t₀ := by rw [hc]; group
  have hcomm : ∀ x : G, x * (S.z * t₀) = S.z * t₀ * x →
      c * x * c⁻¹ * (S.z * t₀) = S.z * t₀ * (c * x * c⁻¹) := by
    intro x hx
    have := commute_conj c hx
    rwa [hconj] at this
  have hz1 : S.z * (S.z * t₀) = S.z * t₀ * S.z := by rw [mul_assoc S.z t₀ S.z, hzt]
  have ht1 : t₀ * (S.z * t₀) = S.z * t₀ * t₀ := by rw [← mul_assoc, hzt]
  set a := c * S.z * c⁻¹
  set b := c * t₀ * c⁻¹
  have haz : IsConj S.z a := isConj_conj S c (IsConj.refl _)
  have hbz : IsConj S.z b := isConj_conj S c ht₀z
  obtain ⟨ha1, ha2⟩ := T.commute_of_commute_zt hS ht₀ haz (hcomm _ hz1)
  obtain ⟨hb1, hb2⟩ := T.commute_of_commute_zt hS ht₀ hbz (hcomm _ ht1)
  have hmem : ∀ x, IsConj S.z x → x * S.z = S.z * x → x * t₀ = t₀ * x →
      x ∈ lineSet S S.z t₀ := fun x h1 h2 h3 => ⟨h1, h2, h3⟩
  have hab : a * b = S.z * t₀ := by
    rw [← hconj]
    simp only [a, b]
    group
  have hne : a ≠ b := fun h => ht₀ne (by
    simp only [a, b] at h
    exact (mul_left_cancel (mul_right_cancel h)).symm)
  rcases T.eq_of_mul_eq_at hS (IsConj.refl S.z) ht₀z hzt ht₀ne (hmem a haz ha1 ha2)
    (hmem b hbz hb1 hb2) (self_mem_lineSet S (IsConj.refl S.z) hzt)
    (mem_lineSet_right S ht₀z hzt) hne ht₀ne.symm hab with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

include T in
theorem isConj_or_isConj (hS : S.SixHyp) {t₀ : G} (ht₀M : t₀ ∈ S.M) (ht₀z : IsConj S.z t₀)
    (ht₀ne : t₀ ≠ S.z) {y : G} (hy : y * y = 1) (hy1 : y ≠ 1) :
    IsConj S.z y ∨ IsConj (S.z * t₀) y := by
  obtain ⟨g, hg⟩ := exists_conj_mem_M S hy
  set y' := g⁻¹ * y * g with hy'
  have hyy : y' * y' = 1 := by
    calc y' * y' = g⁻¹ * (y * y) * g := by rw [hy']; group
      _ = 1 := by rw [hy]; group
  have hy'1 : y' ≠ 1 := fun h => hy1 (by
    calc y = g * y' * g⁻¹ := by rw [hy']; group
      _ = 1 := by rw [h]; group)
  have hback : ∀ x : G, IsConj x y' → IsConj x y := fun x h =>
    h.trans (isConj_iff.mpr ⟨g, by rw [hy']; group⟩)
  rcases qts_inv _ (T.th_mem_il hg hyy hy'1) with h | h | ⟨a, ha, b, hb, hab, hcomm, he⟩
  · left
    rw [← T.th_z] at h
    exact hback _ (by rw [T.th_injOn _ hg S.z (z_mem_M S) h])
  · left
    exact hback _ ((T.mem_D_iff hS hg).mpr (List.mem_cons_of_mem _ h))
  · right
    obtain ⟨x₁, hx₁, rfl⟩ := T.th_surj a (mem_dl_codes ha)
    obtain ⟨x₂, hx₂, rfl⟩ := T.th_surj b (mem_dl_codes hb)
    have hx₁z := (T.mem_D_iff hS hx₁).mpr ha
    have hx₂z := (T.mem_D_iff hS hx₂).mpr hb
    have hx12 : x₁ * x₂ = x₂ * x₁ := (T.th_comm hx₁ hx₂).mpr hcomm
    have hy'e : y' = x₁ * x₂ := T.th_injOn _ hg _ (S.M.mul_mem hx₁ hx₂)
      (by rw [T.th_mul _ hx₁ _ hx₂, he])
    obtain ⟨h, rfl⟩ := isConj_iff.mp hx₁z
    have hx₂M : h⁻¹ * x₂ * h ∈ S.M := conj_inv_mem_M S hx12.symm
    have hx₂z' : IsConj S.z (h⁻¹ * x₂ * h) := by simpa using isConj_conj S h⁻¹ hx₂z
    have hx₂ne : h⁻¹ * x₂ * h ≠ S.z := fun h' => hab (by rw [← h']; group)
    obtain ⟨m, hm, hmx⟩ := T.exists_conj_of_mem_sl hx₂M (T.th_mem_sl hS.weak hx₂M hx₂z' hx₂ne)
      ht₀M (T.th_mem_sl hS.weak ht₀M ht₀z ht₀ne)
    have hmz' : m⁻¹ * S.z * m = S.z := by
      have := S.conj_z_of_mem_M (S.M.inv_mem hm)
      rwa [inv_inv] at this
    have hmt : m⁻¹ * t₀ * m = h⁻¹ * x₂ * h := by rw [← hmx]; group
    refine hback _ (isConj_iff.mpr ⟨h * m⁻¹, ?_⟩)
    rw [hy'e]
    calc h * m⁻¹ * (S.z * t₀) * (h * m⁻¹)⁻¹ =
        h * (m⁻¹ * S.z * m) * (m⁻¹ * t₀ * m) * h⁻¹ := by group
      _ = h * S.z * h⁻¹ * x₂ := by rw [hmz', hmt]; group

include T in
theorem not_isConj_both (hS : S.SixHyp) {t₀ : G} (ht₀M : t₀ ∈ S.M) (ht₀z : IsConj S.z t₀)
    (ht₀ne : t₀ ≠ S.z) {y : G} (h1 : IsConj S.z y) (h2 : IsConj (S.z * t₀) y) : False :=
  T.not_isConj_mul hS ht₀M ht₀z ht₀ne (h1.trans h2.symm)

end Chart

end CFSG.LargeExtraspecial.AS35QTS
