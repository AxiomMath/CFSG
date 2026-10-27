module

public import CFSG.LieType.Chevalley.EvenRootCommutatorRows
public import CFSG.LieType.Chevalley.ParabolicRootFactorData

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem classKill_quot_commute {Q : Type*} [Group Q] {V : Subgroup G} (π : V →* Q) {a b : V}
    (h : π ⁅a, b⁆ = 1) : Commute (π a) (π b) := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
  exact h

theorem classKill_rel_cocycle {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ m ∈ N, v * m * v⁻¹ ∈ N)
    {A z y x w n : G} (hA : A ∈ V) (hz : z ∈ V) (hy : y ∈ V) (hx : x ∈ V) (hw : w ∈ V)
    (hn : n ∈ N) (hAA : A * A = 1) (hAz : A * z = z * A) (hyy : y * y = 1) (hxx : x * x = 1)
    (h1 : (w * y)⁻¹ * (A * y * A) ∈ N) (h2 : x⁻¹ * (A * x * A) ∈ N)
    (hzy : ⁅z, y⁆ ∈ N) (hzx : ⁅z, x⁆ ∈ N) (hxy : ⁅x, y⁆ ∈ N)
    (hcoc : A * (z * (y * x * n)) * A = (z * (y * x * n))⁻¹) :
    z * z * w ∈ N := by
  have hnormal : (N.subgroupOf V).Normal :=
    ⟨fun a ha b => Subgroup.mem_subgroupOf.2 (hnorm b.1 b.2 a.1 (Subgroup.mem_subgroupOf.1 ha))⟩
  set π : V →* V ⧸ N.subgroupOf V := QuotientGroup.mk' (N.subgroupOf V) with hπ
  have key : ∀ a : V, π a = 1 ↔ (a : G) ∈ N := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have keq : ∀ a b : V, ((a⁻¹ * b : V) : G) ∈ N → π a = π b := fun a b h => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.2 h
  set A' : V := ⟨A, hA⟩
  set z' : V := ⟨z, hz⟩
  set y' : V := ⟨y, hy⟩
  set x' : V := ⟨x, hx⟩
  set w' : V := ⟨w, hw⟩
  set n' : V := ⟨n, hNV hn⟩
  have hcom : ∀ a b : V, ((⁅a, b⁆ : V) : G) ∈ N → Commute (π a) (π b) := fun a b h =>
    classKill_quot_commute π ((key _).2 h)
  have czy := hcom z' y' hzy
  have czx := hcom z' x' hzx
  have cxy := hcom x' y' hxy
  have haa : π A' * π A' = 1 := by rw [← map_mul]; exact (key _).2 (by simp [A', hAA])
  have haz : π A' * π z' = π z' * π A' := by
    rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hAz
  have hyy' : π y' * π y' = 1 := by rw [← map_mul]; exact (key _).2 (by simp [y', hyy])
  have hxx' : π x' * π x' = 1 := by rw [← map_mul]; exact (key _).2 (by simp [x', hxx])
  have hn1 : π n' = 1 := (key _).2 hn
  have h1' : π (A' * y' * A') = π (w' * y') := (keq _ _ (by simpa using h1)).symm
  have h2' : π (A' * x' * A') = π x' := (keq _ _ (by simpa using h2)).symm
  have hcoc' : π (A' * (z' * (y' * x' * n')) * A') = π ((z' * (y' * x' * n'))⁻¹) := by
    congr 1; exact Subtype.ext hcoc
  simp only [map_mul, map_inv, hn1, mul_one] at hcoc' h1' h2'
  set a := π A'
  have hconj : ∀ g h : V ⧸ N.subgroupOf V, a * (g * h) * a = (a * g * a) * (a * h * a) :=
    fun g h => by
      calc a * (g * h) * a = a * g * (a * a) * h * a := by rw [haa]; group
        _ = (a * g * a) * (a * h * a) := by group
  have hza : a * π z' * a = π z' := by rw [haz, mul_assoc, haa, mul_one]
  rw [hconj, hconj, hza, h1', h2'] at hcoc'
  have hxinv : (π x')⁻¹ = π x' := inv_eq_of_mul_eq_one_right hxx'
  have hyinv : (π y')⁻¹ = π y' := inv_eq_of_mul_eq_one_right hyy'
  rw [mul_inv_rev, mul_inv_rev, hxinv, hyinv] at hcoc'
  have e1 : π x' * π y' * (π z')⁻¹ = (π z')⁻¹ * (π y' * π x') := by
    rw [cxy.eq]; exact ((czy.mul_right czx).inv_left).eq.symm
  rw [e1] at hcoc'
  have e2 : π z' * (π w' * π y' * π x') = π z' * π w' * (π y' * π x') := by group
  rw [e2] at hcoc'
  have e3 : π z' * π w' = (π z')⁻¹ := mul_right_cancel hcoc'
  have : π (z' * z' * w') = 1 := by
    rw [map_mul, map_mul, mul_assoc, e3, mul_inv_cancel]
  exact (key _).1 this

theorem classKill_rel_kill {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ m ∈ N, v * m * v⁻¹ ∈ N)
    {A z p x n : G} (hA : A ∈ V) (hz : z ∈ V) (hp : p ∈ V) (hx : x ∈ V)
    (hn : n ∈ N) (hxx : x * x = 1)
    (h1 : (x * p)⁻¹ * (A * p * A) ∈ N)
    (hzp : ⁅z, p⁆ ∈ N) (hzx : ⁅z, x⁆ ∈ N) (hpx : ⁅p, x⁆ ∈ N) :
    z⁻¹ * (A * p * A * (z * (x * n)) * p⁻¹) ∈ N := by
  have hnormal : (N.subgroupOf V).Normal :=
    ⟨fun a ha b => Subgroup.mem_subgroupOf.2 (hnorm b.1 b.2 a.1 (Subgroup.mem_subgroupOf.1 ha))⟩
  set π : V →* V ⧸ N.subgroupOf V := QuotientGroup.mk' (N.subgroupOf V) with hπ
  have key : ∀ a : V, π a = 1 ↔ (a : G) ∈ N := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have keq : ∀ a b : V, ((a⁻¹ * b : V) : G) ∈ N → π a = π b := fun a b h => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.2 h
  set A' : V := ⟨A, hA⟩
  set z' : V := ⟨z, hz⟩
  set p' : V := ⟨p, hp⟩
  set x' : V := ⟨x, hx⟩
  set n' : V := ⟨n, hNV hn⟩
  have hcom : ∀ a b : V, ((⁅a, b⁆ : V) : G) ∈ N → Commute (π a) (π b) := fun a b h =>
    classKill_quot_commute π ((key _).2 h)
  have czp := hcom z' p' hzp
  have czx := hcom z' x' hzx
  have cpx := hcom p' x' hpx
  have hxx' : π x' * π x' = 1 := by rw [← map_mul]; exact (key _).2 (by simp [x', hxx])
  have hn1 : π n' = 1 := (key _).2 hn
  have h1' : π (A' * p' * A') = π (x' * p') := (keq _ _ (by simpa using h1)).symm
  have h1'' : π A' * π p' * π A' = π x' * π p' := by simpa only [map_mul] using h1'
  have goal : π (z'⁻¹ * (A' * p' * A' * (z' * (x' * n')) * p'⁻¹)) = 1 := by
    simp only [map_mul, map_inv, hn1, mul_one]
    rw [h1'']
    have e : π x' * π p' * (π z' * π x') * (π p')⁻¹ = π z' := by
      calc _ = π x' * (π p' * π z') * π x' * (π p')⁻¹ := by group
        _ = π x' * π z' * (π p' * π x') * (π p')⁻¹ := by rw [← czp.eq]; group
        _ = π z' * π x' * (π x' * π p') * (π p')⁻¹ := by rw [← czx.eq, cpx.eq]
        _ = π z' * (π x' * π x') := by group
        _ = π z' := by rw [hxx', mul_one]
    rw [e, inv_mul_cancel]
  exact (key _).1 goal

theorem classKill_tw_cocycle {A u p : G} (hAA : A * A = 1) (hu : A * u * A = u⁻¹) :
    A * (A * p * A * u * p⁻¹) * A = (A * p * A * u * p⁻¹)⁻¹ := by
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
  have hu' : u⁻¹ = A * u * A := hu.symm
  calc A * (A * p * A * u * p⁻¹) * A = (A * A) * p * A * u * p⁻¹ * A := by group
    _ = p * A * u * (A * A) * p⁻¹ * A := by rw [hAA]; group
    _ = (A * p * A * u * p⁻¹)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, hu', hAi, inv_inv]; group

theorem classKill_tw_comp {A u p p' : G} (hAA : A * A = 1) :
    A * p' * A * (A * p * A * u * p⁻¹) * p'⁻¹ = A * (p' * p) * A * u * (p' * p)⁻¹ := by
  calc A * p' * A * (A * p * A * u * p⁻¹) * p'⁻¹ = A * p' * (A * A) * p * A * u * p⁻¹ * p'⁻¹ := by
        group
    _ = A * (p' * p) * A * u * (p' * p)⁻¹ := by rw [hAA]; group

end Group

theorem classKill_intCast_eq_one {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {C : ℤ}
    (hC : C % 2 = 1) : (C : R) = 1 := by
  obtain ⟨k, rfl⟩ := Int.odd_iff.2 hC
  push_cast
  rw [h2, zero_mul, zero_add]

@[expose] def classKillRowOK (τ : Tag) (r : PairRow) : Bool :=
  (r.2.2.2.all fun f => decide (1 ≤ f.1) && decide (1 ≤ f.2.1)) &&
  (isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) || r.2.2.2.isEmpty) &&
  (!isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) ||
    match r.2.2.2 with
    | [] => false
    | f :: L => decide (f.1 = 1) && decide (f.2.1 = 1) &&
        (L.all fun g => !(decide (g.1 = 1) && decide (g.2.1 = 1))) &&
        (isRootB τ (orbitCertRoot τ r.2.1 - orbitCertRoot τ r.1) || decide (f.2.2.2 % 2 = 1)))

theorem classKillRowOK_pairTable : ∀ τ : Tag, ∀ r ∈ pairTable τ, classKillRowOK τ r = true := by
  intro τ
  cases τ <;> decide +kernel

variable {τ : Tag}

@[expose] def classKillDeg (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, if j = i then 0 else v j

@[expose] def classKillPair (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, τ.cartan i j * v j

theorem classKillDeg_add (i : Fin τ.rank) (v w : Fin τ.rank → ℤ) :
    classKillDeg i (v + w) = classKillDeg i v + classKillDeg i w := by
  simp only [classKillDeg, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem classKillDeg_zsmul (i : Fin τ.rank) (m : ℤ) (v : Fin τ.rank → ℤ) :
    classKillDeg i (m • v) = m * classKillDeg i v := by
  simp only [classKillDeg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem classKillDeg_nsmul (i : Fin τ.rank) (m : ℕ) (v : Fin τ.rank → ℤ) :
    classKillDeg i (m • v) = m * classKillDeg i v := by
  rw [← natCast_zsmul, classKillDeg_zsmul]

theorem classKillDeg_single (i : Fin τ.rank) :
    classKillDeg i (Pi.single i 1 : Fin τ.rank → ℤ) = 0 := by
  simp only [classKillDeg]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · rfl
  · simp [Pi.single_eq_of_ne h]

theorem classKillDeg_add_smul_single (i : Fin τ.rank) (v : Fin τ.rank → ℤ) (m : ℤ) :
    classKillDeg i (v + m • Pi.single i 1) = classKillDeg i v := by
  rw [classKillDeg_add, classKillDeg_zsmul, classKillDeg_single, mul_zero, add_zero]

theorem classKillDeg_add_single (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    classKillDeg i (v + Pi.single i 1) = classKillDeg i v := by
  rw [classKillDeg_add, classKillDeg_single, add_zero]

theorem classKillPair_add (i : Fin τ.rank) (v w : Fin τ.rank → ℤ) :
    classKillPair i (v + w) = classKillPair i v + classKillPair i w := by
  simp only [classKillPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem classKillPair_nsmul (i : Fin τ.rank) (m : ℕ) (v : Fin τ.rank → ℤ) :
    classKillPair i (m • v) = m * classKillPair i v := by
  simp only [classKillPair, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem classKillPair_single (i : Fin τ.rank) :
    classKillPair i (Pi.single i 1 : Fin τ.rank → ℤ) = 2 :=
  sum_cartan_mul_single τ i

theorem classKill_exists_pos_coord
    {i : Fin τ.rank} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hpos : 0 < height δ)
    (hne : δ ≠ Pi.single i 1) : ∃ j, j ≠ i ∧ 0 < δ j := by
  have hnn := (IsRoot.height_pos_iff hδ).1 hpos
  by_contra! h
  have hδ' : δ = δ i • Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj, le_antisymm (h j hj) (hnn j)]
  have hroot : IsRoot τ (δ i • Pi.single i 1) := by
    rw [← hδ']
    exact hδ
  rcases (isRoot_smul_single_iff i (δ i)).1 hroot with h1 | h1
  · exact hne (by rw [hδ', h1, one_smul])
  · have := hnn i
    omega

theorem classKillDeg_nonneg
    {i : Fin τ.rank} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hpos : 0 < height δ) :
    0 ≤ classKillDeg i δ := by
  have hnn := (IsRoot.height_pos_iff hδ).1 hpos
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact le_rfl
  · exact hnn j

theorem one_le_classKillDeg
    {i : Fin τ.rank} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hpos : 0 < height δ)
    (hne : δ ≠ Pi.single i 1) : 1 ≤ classKillDeg i δ := by
  have hnn := (IsRoot.height_pos_iff hδ).1 hpos
  obtain ⟨j, hji, hj⟩ := classKill_exists_pos_coord hδ hpos hne
  have hle : (if j = i then 0 else δ j) ≤ classKillDeg i δ :=
    Finset.single_le_sum (f := fun l => if l = i then 0 else δ l)
      (fun l _ => by
        split_ifs
        · exact le_rfl
        · exact hnn l) (Finset.mem_univ j)
  simp only [hji, ite_false] at hle
  omega

theorem classKill_parabolicPosRoots_closed {J : Set (Fin τ.rank)} {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicPosRoots τ J) (hδ : δ ∈ parabolicPosRoots τ J) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hr : IsRoot τ (a • γ + b • δ)) : a • γ + b • δ ∈ parabolicPosRoots τ J := by
  refine ⟨⟨hr, fun l hl => ?_⟩, hr, ?_⟩
  · simp [hγ.1.2 l hl, hδ.1.2 l hl]
  · rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [hγ.2.2, hδ.2.2]

theorem classKill_add_smul_single_mem
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ parabolicPosRoots τ J \ {Pi.single i 1}) {m : ℤ}
    (hr : IsRoot τ (δ + m • Pi.single i 1)) :
    δ + m • Pi.single i 1 ∈ parabolicPosRoots τ J \ {Pi.single i 1} := by
  obtain ⟨⟨⟨hδr, hδJ⟩, -, hδp⟩, hne⟩ := hδ
  have hne' : δ ≠ Pi.single i 1 := hne
  obtain ⟨j, hji, hj⟩ := classKill_exists_pos_coord hδr hδp hne'
  have hj' : (δ + m • Pi.single i 1 : Fin τ.rank → ℤ) j = δ j := by simp [Pi.single_eq_of_ne hji]
  have hpos : 0 < height (δ + m • Pi.single i 1) := by
    rcases hr.nonneg_or_nonpos with h | h
    · exact (IsRoot.height_pos_iff hr).2 h
    · have := h j
      omega
  refine ⟨⟨⟨hr, fun l hl => ?_⟩, hr, hpos⟩, fun h => ?_⟩
  · have hli : l ≠ i := fun h => hl (h ▸ hi)
    simp [hδJ l hl, Pi.single_eq_of_ne hli]
  · have h' : (δ + m • Pi.single i 1 : Fin τ.rank → ℤ) j = (Pi.single i 1 : Fin τ.rank → ℤ) j := by
      rw [Set.mem_singleton_iff.1 h]
    rw [hj', Pi.single_eq_of_ne hji] at h'
    omega

@[expose] def classKillPerp (τ : Tag) (J : Set (Fin τ.rank)) (i : Fin τ.rank) :
    Set (Fin τ.rank → ℤ) :=
  {δ | δ ∈ parabolicPosRoots τ J ∧ classKillPair i δ = 0}

structure ClassKillAdmissible (τ : Tag) (J : Set (Fin τ.rank)) (i : Fin τ.rank)
    (R : Set (Fin τ.rank → ℤ)) : Prop where
  subset : R ⊆ parabolicPosRoots τ J \ {Pi.single i 1}
  ideal : ∀ γ ∈ parabolicPosRoots τ J, ∀ δ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot τ (a • γ + b • δ) → a • γ + b • δ ∈ R
  down : ∀ δ ∈ R, IsRoot τ (δ - Pi.single i 1) → δ - Pi.single i 1 ∈ R

theorem classKillPerp_subset {J : Set (Fin τ.rank)}
    {i : Fin τ.rank} : classKillPerp τ J i ⊆ parabolicPosRoots τ J \ {Pi.single i 1} := by
  rintro δ ⟨hδ, hp⟩
  refine ⟨hδ, fun h => ?_⟩
  rw [Set.mem_singleton_iff.1 h, classKillPair_single] at hp
  omega

theorem classKillPerp_closed {J : Set (Fin τ.rank)} {i : Fin τ.rank} :
    ∀ γ ∈ classKillPerp τ J i, ∀ δ ∈ classKillPerp τ J i, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • γ + b • δ) → a • γ + b • δ ∈ classKillPerp τ J i := by
  rintro γ ⟨hγ, hγp⟩ δ ⟨hδ, hδp⟩ a b ha hb hr
  refine ⟨classKill_parabolicPosRoots_closed hγ hδ ha hb hr, ?_⟩
  rw [classKillPair_add, classKillPair_nsmul, classKillPair_nsmul, hγp, hδp]
  ring

theorem classKillAdmissible_top
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    ClassKillAdmissible τ J i (parabolicPosRoots τ J \ {Pi.single i 1}) := by
  refine ⟨subset_rfl, fun γ hγ δ hδ a b ha hb hr => ?_, fun δ hδ hr => ?_⟩
  · refine ⟨classKill_parabolicPosRoots_closed hγ hδ.1 ha hb hr, fun h => ?_⟩
    have hdeg := congrArg (classKillDeg i) (Set.mem_singleton_iff.1 h)
    rw [classKillDeg_add, classKillDeg_nsmul, classKillDeg_nsmul, classKillDeg_single] at hdeg
    have h1 := classKillDeg_nonneg (i := i) hγ.2.1 hγ.2.2
    have h2 := one_le_classKillDeg hδ.1.2.1 hδ.1.2.2 hδ.2
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  · have := classKill_add_smul_single_mem (m := -1) hi hδ (by simpa [sub_eq_add_neg] using hr)
    simpa [sub_eq_add_neg] using this

theorem classKill_eq_of_combo
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} {R : Set (Fin τ.rank → ℤ)}
    (hR : ClassKillAdmissible τ J i R) {δ : Fin τ.rank → ℤ}
    (hM1 : ∀ δ' ∈ R, classKillDeg i δ ≤ classKillDeg i δ')
    (hM2 : ∀ δ' ∈ R, classKillDeg i δ' = classKillDeg i δ → δ i ≤ δ' i)
    {γ δ' : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicPosRoots τ J) (hδ' : δ' ∈ R) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) {m : ℤ} (hm : m ≤ 1)
    (heq : a • γ + b • δ' = δ + m • Pi.single i 1) : δ' = δ ∧ m = 1 := by
  have hdeg := congrArg (classKillDeg i) heq
  rw [classKillDeg_add, classKillDeg_nsmul, classKillDeg_nsmul, classKillDeg_add_smul_single]
    at hdeg
  have hγ0 := classKillDeg_nonneg (i := i) hγ.2.1 hγ.2.2
  have hδ'Ψ := hR.subset hδ'
  have hδ'1 := one_le_classKillDeg hδ'Ψ.1.2.1 hδ'Ψ.1.2.2 hδ'Ψ.2
  have hle := hM1 δ' hδ'
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hγdeg : classKillDeg i γ = 0 := by nlinarith
  have hbeq : (b : ℤ) = 1 := by nlinarith
  have hb1 : b = 1 := by exact_mod_cast hbeq
  have hdδ : classKillDeg i δ' = classKillDeg i δ := by nlinarith
  have hγe : γ = Pi.single i 1 := by
    by_contra hne
    have := one_le_classKillDeg hγ.2.1 hγ.2.2 hne
    omega
  subst hγe hb1
  have hδ'v : δ' = δ + m • Pi.single i 1 - a • Pi.single i 1 := by
    rw [← heq]
    simp
  have hi' : δ' i = δ i + m - a := by
    rw [hδ'v]
    simp
  have := hM2 δ' hδ' hdδ
  have hm1 : m = 1 := by omega
  have ha1 : (a : ℤ) = 1 := by omega
  refine ⟨?_, hm1⟩
  rw [hδ'v, hm1, ← natCast_zsmul, ha1]
  simp

theorem classKill_exists_min {J : Set (Fin τ.rank)}
    {i : Fin τ.rank} {R : Set (Fin τ.rank → ℤ)} (hR : ClassKillAdmissible τ J i R)
    (hne : R.Nonempty) :
    ∃ δ ∈ R, (∀ δ' ∈ R, classKillDeg i δ ≤ classKillDeg i δ') ∧
      ∀ δ' ∈ R, classKillDeg i δ' = classKillDeg i δ → δ i ≤ δ' i := by
  have hfin : R.Finite := (finite_setOf_isRoot τ).subset fun β hβ => (hR.subset hβ).1.2.1
  obtain ⟨δ, hδR, hmin⟩ := hfin.toFinset.exists_min_image
    (fun δ => toLex (classKillDeg i δ, δ i)) ((hfin.toFinset_nonempty).2 hne)
  have hmin' : ∀ δ' ∈ R, classKillDeg i δ < classKillDeg i δ' ∨
      (classKillDeg i δ = classKillDeg i δ' ∧ δ i ≤ δ' i) := fun δ' hδ' =>
    Prod.Lex.toLex_le_toLex.1 (hmin δ' (hfin.mem_toFinset.2 hδ'))
  refine ⟨δ, hfin.mem_toFinset.1 hδR, fun δ' hδ' => ?_, fun δ' hδ' he => ?_⟩
  · rcases hmin' δ' hδ' with h | h
    · exact h.le
    · exact h.1.le
  · rcases hmin' δ' hδ' with h | h
    · omega
    · exact h.2

@[expose] def classKillStrCheck (τ : Tag) (I : List (Fin τ.rank)) : Bool :=
  I.all fun i => (List.range τ.rootCertificate.roots.length).all fun k =>
    !decide (0 < height (τ.rootCertificate.root k)) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) ||
      decide (τ.stringData.up k i ≤ 1)

@[expose] def classKillLongSimple : (τ : Tag) → List (Fin τ.rank)
  | .G2 => [⟨0, by decide⟩]
  | .F4 => [⟨0, by decide⟩, ⟨1, by decide⟩]
  | .D4 => List.finRange 4
  | .E6 => List.finRange 6
  | .E7 => List.finRange 7
  | .E8 => List.finRange 8

theorem classKillStrCheck_longSimple :
    ∀ τ : Tag, classKillStrCheck τ (classKillLongSimple τ) = true := by
  intro τ
  cases τ <;> decide +kernel

theorem classKill_hstr_of_check
    {I : List (Fin τ.rank)} (h : classKillStrCheck τ I = true) {i : Fin τ.rank} (hi : i ∈ I)
    (J : Set (Fin τ.rank)) :
    ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1) := by
  intro δ hδ hr
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hδ.2.1
  unfold classKillStrCheck at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq, decide_eq_true_eq] at h
  by_cases he : τ.rootCertificate.root k = Pi.single i 1
  · rw [he] at hr
    have h3 : IsRoot τ ((3 : ℤ) • Pi.single i 1) := by
      have e : (Pi.single i 1 : Fin τ.rank → ℤ) + (2 : ℤ) • Pi.single i 1 =
          (3 : ℤ) • Pi.single i 1 := by
        rw [show (3 : ℤ) = 1 + 2 by norm_num, add_smul, one_smul]
      rwa [e] at hr
    rcases (isRoot_smul_single_iff i 3).1 h3 with h | h <;> norm_num at h
  · have hne' : τ.rootCertificate.root k ≠ -Pi.single i 1 := by
      intro h'
      have hh := hδ.2.2
      rw [h', height_neg, height_single] at hh
      omega
    obtain ⟨-, hiff⟩ := StringData.isRoot_root_add_iff τ.rootCertificate_check
      τ.stringData_check hk i he hne'
    have h2 := (hiff 2).1 hr
    rcases h i hi k hk with (h1 | h1) | h1
    · exact h1 hδ.2.2
    · exact he (List.ofFn_injective h1)
    · omega

theorem classKill_hstr_of_mem_longSimple
    {i : Fin τ.rank} (hi : i ∈ classKillLongSimple τ)
    (J : Set (Fin τ.rank)) :
    ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1) :=
  classKill_hstr_of_check (classKillStrCheck_longSimple τ) hi J

theorem mem_classKillLongSimple_of_simplyLaced (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i : Fin τ.rank) : i ∈ classKillLongSimple τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> exact List.mem_finRange i


theorem classKill_not_isRoot_add_smul_single {i : Fin τ.rank} {δ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hne : δ ≠ Pi.single i 1) (hne' : δ ≠ -Pi.single i 1)
    (h2 : ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1)) {m : ℤ} (hm : 2 ≤ m) :
    ¬ IsRoot τ (δ + m • Pi.single i 1) := by
  obtain ⟨-, hiff⟩ := isRoot_add_smul_single_iff hδ i hne hne'
  intro hr
  have := (hiff m).1 hr
  exact h2 ((hiff 2).2 ⟨by omega, by omega⟩)

theorem classKillPair_eq_zero {i : Fin τ.rank} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hne : δ ≠ Pi.single i 1) (hne' : δ ≠ -Pi.single i 1)
    (h1 : ¬ IsRoot τ (δ + Pi.single i 1)) (h2 : ¬ IsRoot τ (δ - Pi.single i 1)) :
    classKillPair i δ = 0 := by
  obtain ⟨-, hiff⟩ := isRoot_add_smul_single_iff hδ i hne hne'
  have hp : ¬ (1 : ℤ) ≤ stringUp τ i δ := fun h =>
    h1 (by simpa using (hiff 1).2 ⟨by omega, h⟩)
  have hq : ¬ -(stringDown τ i δ : ℤ) ≤ -1 := fun h =>
    h2 (by simpa [sub_eq_add_neg] using (hiff (-1)).2 ⟨h, by omega⟩)
  rw [classKillPair, (root_string_reflection hδ i).1]
  omega

theorem not_isRoot_add_sub_of_classKillPair {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J)
    (hstr : ∀ δ ∈ parabolicPosRoots τ J, ¬ IsRoot τ (δ + (2 : ℤ) • Pi.single i 1))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ parabolicPosRoots τ J) (hp : classKillPair i δ = 0) :
    ¬ IsRoot τ (δ + Pi.single i 1) ∧ ¬ IsRoot τ (δ - Pi.single i 1) := by
  have hne : δ ≠ Pi.single i 1 := by
    rintro rfl
    rw [classKillPair_single] at hp
    omega
  have hne' : δ ≠ -Pi.single i 1 := by
    rintro rfl
    have := hδ.2.2
    simp at this
  obtain ⟨-, hiff⟩ := isRoot_add_smul_single_iff hδ.1.1 i hne hne'
  have hpq := (root_string_reflection hδ.1.1 i).1
  rw [← classKillPair, hp] at hpq
  by_cases hq : stringDown τ i δ = 0
  · have hu : stringUp τ i δ = 0 := by omega
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (hiff 1).1 (by simpa using h)
      omega
    · have := (hiff (-1)).1 (by simpa [sub_eq_add_neg] using h)
      omega
  · exfalso
    set q : ℤ := (stringDown τ i δ : ℤ) with hqdef
    have hbot : IsRoot τ (δ + (-q) • Pi.single i 1) := (hiff (-q)).2 ⟨le_rfl, by omega⟩
    have hmem := classKill_add_smul_single_mem hi ⟨hδ, hne⟩ hbot
    apply hstr _ hmem.1
    rw [add_assoc, ← add_smul]
    exact (hiff (-q + 2)).2 ⟨by omega, by omega⟩


variable {K : Type} [Field K]

theorem classKill_pinnedX_mem {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβ : β ∈ S)
    (c : K) : pinnedX τ K β c ∈ rootSpan τ K S :=
  (le_iSup₂_of_le β hβ le_rfl : rootSubgroup τ K β ≤ rootSpan τ K S)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem classKill_rootSpan_mono {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) :
    rootSpan τ K S ≤ rootSpan τ K T :=
  iSup₂_le fun β hβ => le_iSup₂_of_le β (h hβ) le_rfl

theorem classKill_pinnedX_mul_self [CharP K 2] (β : Fin τ.rank → ℤ) (c : K) :
    pinnedX τ K β c * pinnedX τ K β c = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem classKill_list_prod_mem {S : Set (Fin τ.rank → ℤ)} {ι : Type*} (L : List ι)
    (γ : ι → Fin τ.rank → ℤ) (e : ι → K) (hL : ∀ f ∈ L, γ f ∈ S) :
    (L.map fun f => pinnedX τ K (γ f) (e f)).prod ∈ rootSpan τ K S := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
  exact classKill_pinnedX_mem (hL f hf) _



theorem classKill_commutator_factors {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ L : List (ℕ × ℕ × ℕ × ℤ),
      (∀ f ∈ L, 1 ≤ f.1 ∧ 1 ≤ f.2.1 ∧ IsRoot τ (f.1 • α + f.2.1 • β)) ∧
      (¬ IsRoot τ (α + β) → L = []) ∧
      (IsRoot τ (α + β) → ∃ f L', L = f :: L' ∧ f.1 = 1 ∧ f.2.1 = 1 ∧
          (∀ g ∈ L', ¬ (g.1 = 1 ∧ g.2.1 = 1)) ∧ (¬ IsRoot τ (β - α) → (f.2.2.2 : R) = 1)) ∧
      ∀ x y : R, ⁅pinnedX τ R α x, pinnedX τ R β y⁆ =
        (L.map fun f => pinnedX τ R (f.1 • α + f.2.1 • β)
          ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod := by
  obtain ⟨r, hr, w, hwa, hwb, hroots, hform⟩ :=
    exists_pairTable_commutatorElement_of_two_eq_zero hα hβ hne hne'
  have hok := classKillRowOK_pairTable τ r hr
  have hab : isRootB τ (orbitCertRoot τ r.1 + orbitCertRoot τ r.2.1) = true ↔
      IsRoot τ (α + β) := by
    rw [isRootB_iff, ← isRoot_smul_iff w, smul_add, hwa, hwb]
  have hba : isRootB τ (orbitCertRoot τ r.2.1 - orbitCertRoot τ r.1) = true ↔
      IsRoot τ (β - α) := by
    rw [isRootB_iff, ← isRoot_smul_iff w, smul_sub, hwa, hwb]
  unfold classKillRowOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨hpos, hemp⟩, hhead⟩ := hok
  refine ⟨r.2.2.2, fun f hf => ⟨(hpos f hf).1, (hpos f hf).2, hroots f hf⟩, fun h => ?_,
    fun h => ?_, hform R h2⟩
  · rcases hemp with h' | h'
    · exact absurd (hab.1 h') h
    · simpa using h'
  · rcases hhead with h' | h'
    · rw [hab.2 h] at h'
      exact absurd h' (by decide)
    · revert h'
      cases hL : r.2.2.2 with
      | nil => simp
      | cons f L' =>
        intro h'
        simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h'
        obtain ⟨⟨⟨hf1, hf2⟩, hL'⟩, hC⟩ := h'
        refine ⟨f, L', rfl, hf1, hf2, fun g hg ⟨hg1, hg2⟩ => ?_, fun hn => ?_⟩
        · rcases hL' g hg with h'' | h''
          · exact h'' hg1
          · exact h'' hg2
        · rcases hC with hC | hC
          · exact absurd (hba.1 hC) hn
          · exact classKill_intCast_eq_one h2 hC

theorem classKill_split {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    {k : ℕ} (ρ : Fin k → Fin τ.rank → ℤ) (hρ : Function.Injective ρ) (hρS : ∀ j, ρ j ∈ S)
    {n : ModGL τ K} (hn : n ∈ rootSpan τ K S) :
    ∃ d : Fin k → K, ((List.ofFn fun j => pinnedX τ K (ρ j) (d j)).prod)⁻¹ * n ∈
      rootSpan τ K (S \ Set.range ρ) := by
  classical
  obtain ⟨m, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset
    fun β (hβ : β ∈ S \ Set.range ρ) => (hS β hβ.1).1).fin_embedding
  have hγS : ∀ j, γ j ∈ S \ Set.range ρ := fun j => hγ ▸ Set.mem_range_self j
  have hinj : Function.Injective (Fin.append ρ γ) :=
    Fin.append_injective_iff.2 ⟨hρ, γ.injective, fun a b hab => (hγS b).2 ⟨a, hab⟩⟩
  have hrange : Set.range (Fin.append ρ γ) = S := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j => rw [Fin.append_left]; exact hρS j
      | right j => rw [Fin.append_right]; exact (hγS j).1
    · intro hβ
      by_cases hβρ : β ∈ Set.range ρ
      · obtain ⟨j, rfl⟩ := hβρ
        exact ⟨Fin.castAdd m j, Fin.append_left ρ γ j⟩
      · obtain ⟨j, hj⟩ : β ∈ Set.range γ := hγ ▸ ⟨hβ, hβρ⟩
        exact ⟨Fin.natAdd k j, by rw [Fin.append_right, hj]⟩
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX K hS hSc _ hinj hrange).surjOn hn
  refine ⟨fun j => c (Fin.castAdd m j), ?_⟩
  have hsplit : (List.ofFn fun j => pinnedX τ K (Fin.append ρ γ j) (c j)).prod =
      (List.ofFn fun j => pinnedX τ K (ρ j) (c (Fin.castAdd m j))).prod *
        (List.ofFn fun j => pinnedX τ K (γ j) (c (Fin.natAdd k j))).prod := by
    have e : (fun j => pinnedX τ K (Fin.append ρ γ j) (c j)) =
        Fin.append (fun j => pinnedX τ K (ρ j) (c (Fin.castAdd m j)))
          (fun j => pinnedX τ K (γ j) (c (Fin.natAdd k j))) := by
      funext j
      induction j using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right]
    rw [e, List.ofFn_fin_append, List.prod_append]
  have hc' : (List.ofFn fun j => pinnedX τ K (Fin.append ρ γ j) (c j)).prod = n := hc
  rw [← hc', hsplit, inv_mul_cancel_left]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact classKill_pinnedX_mem (hγS j) _

theorem classKill_rootSpan_inf_le_inter {S T : Set (Fin τ.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    {x : ModGL τ K} (hxS : x ∈ rootSpan τ K S) (hxT : x ∈ rootSpan τ K T) :
    x ∈ rootSpan τ K (S ∩ T) := by
  classical
  obtain ⟨k, ρ, hρ⟩ := ((finite_setOf_isRoot τ).subset
    fun β (hβ : β ∈ S \ T) => (hS β hβ.1).1).fin_embedding
  have hρST : ∀ j, ρ j ∈ S \ T := fun j => hρ ▸ Set.mem_range_self j
  obtain ⟨d, hd⟩ := classKill_split hS hSc ρ ρ.injective (fun j => (hρST j).1) hxS
  rw [hρ, Set.sdiff_sdiff_right_self] at hd
  set y := (List.ofFn fun j => pinnedX τ K (ρ j) (d j)).prod with hy
  have hyT : y ∈ rootSpan τ K T := by
    have e : y = x * (y⁻¹ * x)⁻¹ := by group
    rw [e]
    exact mul_mem hxT (inv_mem (classKill_rootSpan_mono Set.inter_subset_right hd))
  obtain ⟨l, t, ht⟩ :=
    ((finite_setOf_isRoot τ).subset fun β (hβ : β ∈ T) => (hT β hβ).1).fin_embedding
  have htT : ∀ j, t j ∈ T := fun j => ht ▸ Set.mem_range_self j
  obtain ⟨e, -, he⟩ := (bijOn_prod_pinnedX K hT hTc t t.injective ht).surjOn hyT
  have he' : (List.ofFn fun j => pinnedX τ K (t j) (e j)).prod = y := he
  have hinj : Function.Injective (Fin.append (⇑ρ) (⇑t)) :=
    Fin.append_injective_iff.2 ⟨ρ.injective, t.injective, fun a b hab =>
      (hρST a).2 (hab ▸ htT b)⟩
  have hpos : ∀ j, IsRoot τ (Fin.append (⇑ρ) (⇑t) j) ∧ 0 < height (Fin.append (⇑ρ) (⇑t) j) := by
    intro j
    induction j using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hS _ (hρST j).1
    | right j => rw [Fin.append_right]; exact hT _ (htT j)
  have hsplit : ∀ (d₁ : Fin k → K) (d₂ : Fin l → K),
      (List.ofFn fun j => pinnedX τ K (Fin.append (⇑ρ) (⇑t) j) (Fin.append d₁ d₂ j)).prod =
        (List.ofFn fun j => pinnedX τ K (ρ j) (d₁ j)).prod *
          (List.ofFn fun j => pinnedX τ K (t j) (d₂ j)).prod := by
    intro d₁ d₂
    have e : (fun j => pinnedX τ K (Fin.append (⇑ρ) (⇑t) j) (Fin.append d₁ d₂ j)) =
        Fin.append (fun j => pinnedX τ K (ρ j) (d₁ j)) (fun j => pinnedX τ K (t j) (d₂ j)) := by
      funext j
      induction j using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right]
    rw [e, List.ofFn_fin_append, List.prod_append]
  have hone : ∀ {m : ℕ} (γ : Fin m → Fin τ.rank → ℤ),
      (List.ofFn fun j => pinnedX τ K (γ j) ((0 : Fin m → K) j)).prod = 1 := by
    intro m γ
    simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 : (List.ofFn fun j => pinnedX τ K (Fin.append (⇑ρ) (⇑t) j) (Fin.append d 0 j)).prod =
      y := by
    rw [hsplit, hone, mul_one]
  have h2 : (List.ofFn fun j => pinnedX τ K (Fin.append (⇑ρ) (⇑t) j) (Fin.append 0 e j)).prod =
      y := by
    rw [hsplit, hone, one_mul, he']
  have hde := (positive_root_product_injectivity τ K _ hinj hpos).2 (h1.trans h2.symm)
  have hd0 : d = 0 := funext fun j => by
    have := congrFun hde (Fin.castAdd l j)
    simpa only [Fin.append_left] using this
  have hy1 : y = 1 := by rw [hy, hd0, hone]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e, hy1, one_mul]
  rw [hy1, inv_one, one_mul] at hd
  exact hd

theorem classKill_conj_mem {J : Set (Fin τ.rank)} {R : Set (Fin τ.rank → ℤ)}
    (hRsub : R ⊆ parabolicPosRoots τ J)
    (hideal : ∀ γ ∈ parabolicPosRoots τ J, ∀ δ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • γ + b • δ) → a • γ + b • δ ∈ R)
    {v : ModGL τ K} (hv : v ∈ rootSpan τ K (parabolicPosRoots τ J))
    {m : ModGL τ K} (hm : m ∈ rootSpan τ K R) : v * m * v⁻¹ ∈ rootSpan τ K R := by
  have h := positive_root_ideal_normality τ K hRsub (fun γ hγ => hγ.2) hideal
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer h.1).1 h.2
  exact (Subgroup.mem_normalizer_iff.1 (hle hv) m).1 hm

theorem classKill_commutator_mem {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    {R' : Set (Fin τ.rank → ℤ)}
    (hnorm : ∀ v ∈ rootSpan τ K (parabolicPosRoots τ J), ∀ m ∈ rootSpan τ K R',
      v * m * v⁻¹ ∈ rootSpan τ K R')
    {β : Fin τ.rank → ℤ} (hβ : β ∈ parabolicPosRoots τ J)
    (hβR : ∀ γ ∈ parabolicPosRoots τ J \ {Pi.single i 1}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • γ + b • β) → a • γ + b • β ∈ R')
    {z : ModGL τ K} (hz : z ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1})) (e : K) :
    ⁅z, pinnedX τ K β e⁆ ∈ rootSpan τ K R' := by
  have hle : ⁅Subgroup.closure {g | ∃ γ ∈ parabolicPosRoots τ J \ {Pi.single i 1}, ∃ c : K,
      pinnedX τ K γ c = g}, Subgroup.closure (Set.range (pinnedX τ K β))⁆ ≤ rootSpan τ K R' := by
    refine commutator_closure_le_of_le_normalizer (G₀ := rootSpan τ K (parabolicPosRoots τ J))
      ?_ ?_ ?_ ?_
    · rw [← rootSpan_eq_closure]
      exact classKill_rootSpan_mono Set.sdiff_subset
    · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ parabolicPosRoots τ J) => rootSubgroup τ K γ)
        β hβ le_rfl
    · intro v hv
      refine Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => hnorm v hv m hm, fun hm => ?_⟩
      have := hnorm v⁻¹ (inv_mem hv) _ hm
      simpa [mul_assoc] using this
    · rintro _ ⟨γ, hγ, c, rfl⟩ _ ⟨e', rfl⟩
      by_cases hγβ : γ = β
      · subst hγβ
        rw [commutatorElement_def, rootSubgroup_mul_comm K (Subgroup.subset_closure ⟨c, rfl⟩)
          (Subgroup.subset_closure ⟨e', rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have hmem := commutator_rootSubgroup_le K hγ.1.2.1 hβ.2.1 hγ.1.2.2 hβ.2.2 hγβ
          (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
            (Subgroup.subset_closure ⟨e', rfl⟩))
        have hle' : (⨆ (ε : Fin τ.rank → ℤ) (_ : IsRoot τ ε ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
            ε = a • γ + b • β), rootSubgroup τ K ε) ≤ rootSpan τ K R' := by
          refine iSup₂_le fun ε hε => ?_
          obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
          exact le_iSup₂_of_le _ (hβR γ hγ a b ha hb hεr) le_rfl
        exact hle' hmem
  exact hle (Subgroup.commutator_mem_commutator (by rw [← rootSpan_eq_closure]; exact hz)
    (Subgroup.subset_closure ⟨e, rfl⟩))

end CFSG.SeitzReduction
