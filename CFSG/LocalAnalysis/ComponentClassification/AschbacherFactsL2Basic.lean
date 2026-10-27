module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {u w : C} (hu : u ^ 2 = 1) (hw : w ^ 2 = 1) (hu1 : u ≠ 1) (hw1 : w ≠ 1) : u = w := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  by_contra huw
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have hsub : ({1, u, w} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [hu, hw]
  have hcard : ({1, u, w} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huw]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu1, Ne.symm hw1⟩
  have := Finset.card_le_card hsub
  omega

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {x : G} {a : ℕ} (hx : x ^ 2 ^ a = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨a, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hk]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isPGroup_zpowers_sup {G : Type*} [Group G] {x y : G} {a b : ℕ} (hx : x ^ 2 ^ a = 1)
    (hy : y ^ 2 ^ b = 1) {m m' : ℤ} (hyx : y * x * y⁻¹ = x ^ m)
    (hyx' : y⁻¹ * x * y = x ^ m') :
    IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) := by
  refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow hx)
    (isPGroup_zpowers_of_pow hy) ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hyx, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers x _
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hconj : (y⁻¹ * x * y) ^ k = y⁻¹ * x ^ k * y := by
      have := conj_zpow (i := k) (a := y⁻¹) (b := x)
      rwa [inv_inv] at this
    have hh' : h = (y⁻¹ * x * y) ^ k := by
      rw [hconj, hk]
      group
    rw [hh', hyx', ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers x _

theorem not_isCyclic_sylow_of_commuting_involutions {G : Type*} [Group G] [Finite G]
    {u w : G} (hu : u ^ 2 = 1) (hw : w ^ 2 = 1) (hu1 : u ≠ 1) (hw1 : w ≠ 1) (huw : u ≠ w)
    (hc : u * w = w * u) (P : Sylow 2 G) : ¬ IsCyclic (P : Subgroup G) := by
  intro hP
  have hV := isPGroup_zpowers_sup (a := 1) (b := 1) (m := 1) (m' := 1)
    (by simpa using hu) (by simpa using hw)
    (by rw [← hc]; group) (by rw [mul_assoc, hc]; group)
  obtain ⟨Q, hQ⟩ := hV.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmem : ∀ x : G, x ∈ (Q : Subgroup G) → g * x * g⁻¹ ∈ (P : Subgroup G) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, rfl⟩
  have huQ : u ∈ (Q : Subgroup G) :=
    hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hwQ : w ∈ (Q : Subgroup G) :=
    hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  let u' : (P : Subgroup G) := ⟨g * u * g⁻¹, hmem u huQ⟩
  let w' : (P : Subgroup G) := ⟨g * w * g⁻¹, hmem w hwQ⟩
  have hconj_sq : ∀ x : G, x ^ 2 = 1 → (g * x * g⁻¹) ^ 2 = 1 := by
    intro x hx
    rw [pow_two, show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, ← pow_two, hx]
    group
  have hconj_ne : ∀ x : G, x ≠ 1 → g * x * g⁻¹ ≠ 1 := by
    intro x hx h
    apply hx
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have huw' : u' = w' := eq_of_sq_eq_one_of_isCyclic (Subtype.ext (hconj_sq u hu))
    (Subtype.ext (hconj_sq w hw)) (fun h => hconj_ne u hu1 (congrArg Subtype.val h))
    (fun h => hconj_ne w hw1 (congrArg Subtype.val h))
  apply huw
  have h' : g * u * g⁻¹ = g * w * g⁻¹ := congrArg Subtype.val huw'
  calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
    _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [h']
    _ = w := by group

theorem not_hasCyclicSylowTwo_of_commuting_involutions {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) {u w : G} (huH : u ∈ H) (hwH : w ∈ H) (hu : u ^ 2 = 1) (hw : w ^ 2 = 1)
    (hu1 : u ≠ 1) (hw1 : w ≠ 1) (huw : u ≠ w) (hc : u * w = w * u) :
    ¬ HasCyclicSylowTwo H := by
  rintro ⟨P, hP⟩
  exact not_isCyclic_sylow_of_commuting_involutions (u := (⟨u, huH⟩ : H))
    (w := (⟨w, hwH⟩ : H)) (Subtype.ext hu) (Subtype.ext hw)
    (fun h => hu1 (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
    (fun h => huw (congrArg Subtype.val h)) (Subtype.ext hc) P hP

theorem zmod_eq_of_two_mul_eq_zero {n : ℕ} [NeZero n] {x y : ZMod n} (hx : 2 * x = 0)
    (hy : 2 * y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  classical
  by_contra hxy
  have hle := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod n) (n := 2) two_pos
  have hsub : ({0, x, y} : Finset (ZMod n)) ⊆
      Finset.univ.filter (fun a : ZMod n => 2 • a = 0) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [hx, hy]
  have hcard : ({0, x, y} : Finset (ZMod n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx0, Ne.symm hy0⟩
  have := Finset.card_le_card hsub
  omega

theorem zmod_eq_of_two_mul_eq_zero' {n : ℕ} {x y : ZMod n} (hx : 2 * x = 0)
    (hy : 2 * y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply hx0
    have hx' : (2 : ℤ) * (show ℤ from x) = 0 := hx
    show (show ℤ from x) = 0
    omega
  · have : NeZero n := ⟨hn.ne'⟩
    exact zmod_eq_of_two_mul_eq_zero hx hy hx0 hy0

theorem dihedral_half_turn {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) ^ 2 = 1 ∧
      DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ≠ 1 ∧
      ∀ x : DihedralGroup n, DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * x =
        x * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  obtain ⟨k, hk⟩ := hn
  have hk2 : n / 2 = k := by omega
  have h2 : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [hk2, two_mul, ← Nat.cast_add, ← hk]
    exact ZMod.natCast_self n
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_two, DihedralGroup.r_mul_r, ← two_mul, h2, DihedralGroup.r_zero]
  · intro h
    rw [← DihedralGroup.r_zero] at h
    have h' := DihedralGroup.r.inj h
    rw [hk2, ZMod.natCast_eq_zero_iff] at h'
    have hkpos : 0 < k := by omega
    have := Nat.le_of_dvd hkpos h'
    omega
  · intro x
    cases x with
    | r i => rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    | sr i =>
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      linear_combination -h2

theorem dihedral_exists_commuting_involutions {n : ℕ} (hn : Even n) (hn0 : n ≠ 0)
    (l : DihedralGroup n) (hl : l ^ 2 = 1) :
    ∃ u w : DihedralGroup n, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧
      u * w = w * u ∧ u * l = l * u ∧ w * l = l * w := by
  obtain ⟨hh2, hh1, hhc⟩ := dihedral_half_turn hn hn0
  have hsr2 : ∀ j : ZMod n, (DihedralGroup.sr j) ^ 2 = 1 := fun j => by
    rw [pow_two, DihedralGroup.sr_mul_self]
  have hsr1 : ∀ j : ZMod n, DihedralGroup.sr j ≠ 1 := fun j h => by
    rw [DihedralGroup.one_def] at h
    cases h
  have hne : ∀ j : ZMod n,
      DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ≠ DihedralGroup.sr j := fun j => by simp
  cases l with
  | r k =>
    refine ⟨_, DihedralGroup.sr 0, hh2, hsr2 0, hh1, hsr1 0, hne 0, hhc _, hhc _, ?_⟩
    have hk : (2 : ZMod n) * k = 0 := by
      rw [pow_two, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero] at hl
      rw [two_mul]
      exact DihedralGroup.r.inj hl
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    linear_combination hk
  | sr k => exact ⟨_, DihedralGroup.sr k, hh2, hsr2 k, hh1, hsr1 k, hne k, hhc _, hhc _, rfl⟩

theorem sq_ne_one_of_orderOf_eq_four {G : Type*} [Monoid G] {c : G} (hc : orderOf c = 4) :
    c ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hc] at this
  omega

theorem dihedral_eq_of_commute_orderOf_four {n : ℕ} {c v : DihedralGroup n}
    (hc : orderOf c = 4) (hv : v ^ 2 = 1) (hcv : c * v = v * c) : v = 1 ∨ v = c ^ 2 := by
  have hc2 := sq_ne_one_of_orderOf_eq_four hc
  have hc4 : c ^ 4 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  cases c with
  | sr i => rw [DihedralGroup.orderOf_sr] at hc; omega
  | r i =>
    have h2i : (2 : ZMod n) * (2 * i) = 0 := by
      rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero] at hc4
      have := DihedralGroup.r.inj hc4
      push_cast at this
      linear_combination this
    have h2i0 : 2 * i ≠ 0 := by
      intro h
      apply hc2
      rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero]
      congr 1
      push_cast
      linear_combination h
    cases v with
    | sr j =>
      exfalso
      rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hcv
      have h := DihedralGroup.sr.inj hcv
      exact h2i0 (by linear_combination -h)
    | r j =>
      have h2j : 2 * j = 0 := by
        rw [pow_two, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero] at hv
        rw [two_mul]
        exact DihedralGroup.r.inj hv
      by_cases hj : j = 0
      · left
        rw [hj, DihedralGroup.r_zero]
      · right
        have hji := zmod_eq_of_two_mul_eq_zero' h2j h2i hj h2i0
        rw [DihedralGroup.r_pow, hji]
        congr 1
        push_cast
        ring

theorem dihedral_not_quaternion_pair {n : ℕ} {c d : DihedralGroup n} (hc : orderOf c = 4)
    (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) : False := by
  have hc2 := sq_ne_one_of_orderOf_eq_four hc
  cases c with
  | sr i => rw [DihedralGroup.orderOf_sr] at hc; omega
  | r i =>
    cases d with
    | sr j =>
      apply hc2
      rw [← hd, pow_two, DihedralGroup.sr_mul_self]
    | r j =>
      apply hc2
      rw [DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r,
        DihedralGroup.inv_r] at hdc
      have h := DihedralGroup.r.inj hdc
      rw [pow_two, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero]
      congr 1
      linear_combination h

theorem exists_injective_dihedral {Y : Type*} [Group Y] [Finite Y] {N : ℕ} (S : Sylow 2 Y)
    (e : (S : Subgroup Y) ≃* DihedralGroup N) (V : Subgroup Y) (hV : IsPGroup 2 V) :
    ∃ f : V →* DihedralGroup N, Function.Injective f := by
  obtain ⟨Q, hVQ⟩ := hV.exists_le_sylow
  let eQ : (Q : Subgroup Y) ≃* (S : Subgroup Y) := Sylow.equiv Q S
  refine ⟨(e.toMonoidHom.comp eQ.toMonoidHom).comp (Subgroup.inclusion hVQ), ?_⟩
  exact e.injective.comp (eQ.injective.comp (Subgroup.inclusion_injective hVQ))

theorem eq_of_commute_orderOf_four_of_dihedral {Y : Type*} [Group Y] [Finite Y] {N : ℕ}
    (S : Sylow 2 Y) (e : (S : Subgroup Y) ≃* DihedralGroup N) {c v : Y}
    (hc : orderOf c = 4) (hv : v ^ 2 = 1) (hcv : c * v = v * c) : v = 1 ∨ v = c ^ 2 := by
  have hc4 : c ^ 2 ^ 2 = 1 := by rw [show 2 ^ 2 = 4 by norm_num, ← hc]; exact pow_orderOf_eq_one c
  have hV := isPGroup_zpowers_sup (a := 2) (b := 1) (m := 1) (m' := 1) hc4
    (by simpa using hv) (by rw [← hcv]; group) (by rw [mul_assoc, hcv]; group)
  obtain ⟨f, hf⟩ := exists_injective_dihedral S e _ hV
  let c' : (Subgroup.zpowers c ⊔ Subgroup.zpowers v : Subgroup Y) :=
    ⟨c, Subgroup.mem_sup_left (Subgroup.mem_zpowers c)⟩
  let v' : (Subgroup.zpowers c ⊔ Subgroup.zpowers v : Subgroup Y) :=
    ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v)⟩
  have hc' : orderOf (f c') = 4 := by
    rw [orderOf_injective f hf, Subgroup.orderOf_mk, hc]
  have hv' : (f v') ^ 2 = 1 := by
    rw [← map_pow, show v' ^ 2 = 1 from Subtype.ext hv, map_one]
  have hcv' : f c' * f v' = f v' * f c' := by
    rw [← map_mul, ← map_mul, show c' * v' = v' * c' from Subtype.ext hcv]
  rcases dihedral_eq_of_commute_orderOf_four hc' hv' hcv' with h | h
  · left
    have : v' = 1 := hf (h.trans (map_one f).symm)
    exact congrArg Subtype.val this
  · right
    have : v' = c' ^ 2 := hf (h.trans (map_pow f c' 2).symm)
    exact congrArg Subtype.val this

theorem not_quaternion_pair_of_dihedral {Y : Type*} [Group Y] [Finite Y] {N : ℕ}
    (S : Sylow 2 Y) (e : (S : Subgroup Y) ≃* DihedralGroup N) {c d : Y}
    (hc : orderOf c = 4) (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) : False := by
  have hc4 : c ^ 2 ^ 2 = 1 := by rw [show 2 ^ 2 = 4 by norm_num, ← hc]; exact pow_orderOf_eq_one c
  have hd4 : d ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, hd, ← pow_mul]
    exact hc4
  have hdc' : d⁻¹ * c * d = c ^ (-1 : ℤ) := by
    have h1 : d⁻¹ * c⁻¹ * d = c := by rw [← hdc]; group
    rw [zpow_neg_one]
    calc d⁻¹ * c * d = (d⁻¹ * c⁻¹ * d)⁻¹ := by group
      _ = c⁻¹ := by rw [h1]
  have hV := isPGroup_zpowers_sup (a := 2) (b := 2) (m := -1) (m' := -1) hc4 hd4
    (by rw [hdc, zpow_neg_one]) hdc'
  obtain ⟨f, hf⟩ := exists_injective_dihedral S e _ hV
  let c' : (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup Y) :=
    ⟨c, Subgroup.mem_sup_left (Subgroup.mem_zpowers c)⟩
  let d' : (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup Y) :=
    ⟨d, Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩
  have hc' : orderOf (f c') = 4 := by
    rw [orderOf_injective f hf, Subgroup.orderOf_mk, hc]
  have hd' : (f d') ^ 2 = (f c') ^ 2 := by
    rw [← map_pow, ← map_pow, show d' ^ 2 = c' ^ 2 from Subtype.ext hd]
  have hdc'' : f d' * f c' * (f d')⁻¹ = (f c')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      show d' * c' * d'⁻¹ = c'⁻¹ from Subtype.ext hdc]
  exact dihedral_not_quaternion_pair hc' hd' hdc''

theorem exists_commuting_involutions_of_dihedral {Y : Type*} [Group Y] [Finite Y] {N : ℕ}
    (hN : Even N) (hN0 : N ≠ 0) (S : Sylow 2 Y) (e : (S : Subgroup Y) ≃* DihedralGroup N)
    {l : Y} (hl : l ^ 2 = 1) :
    ∃ u w : Y, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      u * l = l * u ∧ w * l = l * w := by
  obtain ⟨Q, hlQ⟩ := (isPGroup_zpowers_of_pow (a := 1) (by simpa using hl)).exists_le_sylow
  let eQ : (Q : Subgroup Y) ≃* DihedralGroup N := (Sylow.equiv Q S).trans e
  have hlQ' : l ∈ (Q : Subgroup Y) := hlQ (Subgroup.mem_zpowers l)
  let l' : (Q : Subgroup Y) := ⟨l, hlQ'⟩
  have hl' : (eQ l') ^ 2 = 1 := by
    rw [← map_pow, show l' ^ 2 = 1 from Subtype.ext hl, map_one]
  obtain ⟨u, w, hu, hw, hu1, hw1, huw, hc, hul, hwl⟩ :=
    dihedral_exists_commuting_involutions hN hN0 _ hl'
  have hmap : ∀ x y : DihedralGroup N, x * y = y * x →
      ((eQ.symm x : Q) : Y) * ((eQ.symm y : Q) : Y) =
        ((eQ.symm y : Q) : Y) * ((eQ.symm x : Q) : Y) := by
    intro x y hxy
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hxy]
  have hsq : ∀ x : DihedralGroup N, x ^ 2 = 1 → ((eQ.symm x : Q) : Y) ^ 2 = 1 := by
    intro x hx
    rw [← Subgroup.coe_pow, ← map_pow, hx, map_one, OneMemClass.coe_one]
  have hne1 : ∀ x : DihedralGroup N, x ≠ 1 → ((eQ.symm x : Q) : Y) ≠ 1 := by
    intro x hx h
    apply hx
    have : eQ.symm x = 1 := Subtype.ext h
    simpa using congrArg eQ this
  have hl'' : ((eQ.symm (eQ l') : Q) : Y) = l := by simp [l']
  refine ⟨(eQ.symm u : Q), (eQ.symm w : Q), hsq u hu, hsq w hw, hne1 u hu1, hne1 w hw1,
    ?_, hmap u w hc, ?_, ?_⟩
  · intro h
    apply huw
    have : eQ.symm u = eQ.symm w := Subtype.ext h
    exact eQ.symm.injective this
  · have := hmap u (eQ l') hul
    rwa [hl''] at this
  · have := hmap w (eQ l') hwl
    rwa [hl''] at this

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
