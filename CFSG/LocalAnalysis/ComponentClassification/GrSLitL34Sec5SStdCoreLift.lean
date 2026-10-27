module

public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem map_centralizer_subtype {J : Subgroup G} {a : G} (haJ : a ∈ J) :
    (centralizer ({⟨a, haJ⟩} : Set ↥J)).map J.subtype =
      J ⊓ centralizer ({a} : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨j.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hj (⟨a, haJ⟩ : ↥J) rfl)
  · intro hx
    obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC a rfl)

private theorem lift_setup {J : Subgroup G} (hZ : Odd (Nat.card (center ↥J)))
    {a : G} (haJ : a ∈ J) (ha : orderOf a = 2)
    {L : Subgroup (↥J ⧸ center ↥J)}
    (hL : ⁅centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)),
        centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J))⁆ = L)
    (hLp : ⁅L, L⁆ = L)
    {Cj : Subgroup ↥J} (hCj_def : Cj = centralizer ({⟨a, haJ⟩} : Set ↥J))
    {Kj : Subgroup ↥J} (hKj_def : Kj = ⁅⁅Cj, Cj⁆, ⁅Cj, Cj⁆⁆) :
    (Cj.map J.subtype = J ⊓ centralizer ({a} : Set G)) ∧
    (Kj.map J.subtype =
      ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆) ∧
    Group.IsPerfect ↥Kj ∧
    ∃ φ : ↥Kj →* ↥L, Function.Surjective φ ∧ φ.ker ≤ center ↥Kj ∧
      (center ↥L).comap φ = center ↥Kj ∧
      ∀ x : ↥Kj, L.subtype (φ x) = QuotientGroup.mk' (center ↥J) (x : ↥J) := by
  classical
  let π : ↥J →* ↥J ⧸ center ↥J := QuotientGroup.mk' (center ↥J)
  let ā : ↥J ⧸ center ↥J := QuotientGroup.mk ⟨a, haJ⟩
  have hL' : ⁅centralizer ({ā} : Set (↥J ⧸ center ↥J)),
      centralizer ({ā} : Set (↥J ⧸ center ↥J))⁆ = L := hL
  have ha2 : (⟨a, haJ⟩ : ↥J) ^ 2 = 1 := by
    have h : orderOf (⟨a, haJ⟩ : ↥J) = 2 := by
      rw [Subgroup.orderOf_mk a haJ, ha]
    rw [← h, pow_orderOf_eq_one]
  have hCjmap : Cj.map π = centralizer ({ā} : Set (↥J ⧸ center ↥J)) := by
    rw [hCj_def]
    have hcop : Nat.Coprime 2 (Nat.card (center ↥J)) := Nat.coprime_two_left.mpr hZ
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq
      (H := ↥J) (p := 2) Nat.prime_two (W := ⊤) (N := center ↥J) le_top hcop ha2
    rw [top_inf_eq, Subgroup.map_top_of_surjective (QuotientGroup.mk' (center ↥J))
      (QuotientGroup.mk'_surjective (center ↥J)), top_inf_eq] at h
    simpa [π, ā] using h
  have hCj : Cj.map J.subtype = J ⊓ centralizer ({a} : Set G) := by
    rw [hCj_def]
    exact map_centralizer_subtype haJ
  let C1 : Subgroup ↥J := ⁅Cj, Cj⁆
  have hC1map : C1.map π = L := by
    change ⁅Cj, Cj⁆.map π = L
    rw [Subgroup.map_commutator, hCjmap, hL']
  have hKjπ : Kj.map π = L := by
    rw [hKj_def]
    change ⁅C1, C1⁆.map π = L
    rw [Subgroup.map_commutator, hC1map, hLp]
  have hKjmap : Kj.map J.subtype =
      ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ := by
    rw [hKj_def]
    change ⁅C1, C1⁆.map J.subtype =
      ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆
    rw [Subgroup.map_commutator]
    have hC1J : C1.map J.subtype =
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ := by
      change ⁅Cj, Cj⁆.map J.subtype = _
      rw [Subgroup.map_commutator, hCj]
    rw [hC1J]
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  let φ₁ : ↥C1 →* ↥L :=
    { toFun := fun x => ⟨π (x : ↥J), by
        have hx : π (x : ↥J) ∈ C1.map π := Subgroup.mem_map_of_mem π x.2
        rwa [hC1map] at hx⟩
      map_one' := by apply Subtype.ext; exact map_one π
      map_mul' := fun x y => by apply Subtype.ext; exact map_mul π _ _ }
  have hφ₁surj : Function.Surjective φ₁ := by
    intro l
    have hl : (l : ↥J ⧸ center ↥J) ∈ C1.map π := by rw [hC1map]; exact l.2
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hl
    exact ⟨⟨x, hx⟩, Subtype.ext hxval⟩
  have hφ₁ker : φ₁.ker ≤ center ↥C1 := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : π (x : ↥J) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      simpa [φ₁] using h
    have hxZ : (x : ↥J) ∈ center ↥J := by
      rw [← QuotientGroup.ker_mk' (center ↥J)]
      exact MonoidHom.mem_ker.mpr hx1
    exact Subgroup.mem_center_iff.mp hxZ (y : ↥J)
  have hperfC1 : Group.IsPerfect ↥(commutator ↥C1) :=
    (CFSG.LocalCores.central_extension_derived_of_surjective φ₁ hφ₁surj hφ₁ker hLperf).2.1
  have hperfKj : Group.IsPerfect ↥Kj := by
    have hcommap : (commutator ↥C1).map C1.subtype = Kj := by
      rw [Subgroup.map_subtype_commutator, hKj_def]
    have : Group.IsPerfect ↥(commutator ↥C1) := hperfC1
    have hmap : Group.IsPerfect ↥((commutator ↥C1).map C1.subtype) :=
      Group.IsPerfect.map C1.subtype
    rwa [hcommap] at hmap
  let φ : ↥Kj →* ↥L :=
    { toFun := fun x => ⟨π (x : ↥J), by
        have hx : π (x : ↥J) ∈ Kj.map π := Subgroup.mem_map_of_mem π x.2
        rwa [hKjπ] at hx⟩
      map_one' := by apply Subtype.ext; exact map_one π
      map_mul' := fun x y => by apply Subtype.ext; exact map_mul π _ _ }
  have hφval : ∀ x : ↥Kj, L.subtype (φ x) = QuotientGroup.mk' (center ↥J) (x : ↥J) :=
    fun _ => rfl
  have hφsurj : Function.Surjective φ := by
    intro l
    have hl : (l : ↥J ⧸ center ↥J) ∈ Kj.map π := by rw [hKjπ]; exact l.2
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hl
    exact ⟨⟨x, hx⟩, Subtype.ext hxval⟩
  have hφker : φ.ker ≤ center ↥Kj := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : π (x : ↥J) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      have h2 := hφval x
      rw [h] at h2
      exact h2.symm
    have hxZ : (x : ↥J) ∈ center ↥J := by
      rw [← QuotientGroup.ker_mk' (center ↥J)]
      exact MonoidHom.mem_ker.mpr hx1
    exact Subgroup.mem_center_iff.mp hxZ (y : ↥J)
  have hφcenter : (center ↥L).comap φ = center ↥Kj :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfKj φ hφsurj hφker
  exact ⟨hCj, hKjmap, hperfKj, φ, hφsurj, hφker, hφcenter, hφval⟩

theorem isQuasisimple_centralizerCore_of_quotient {J : Subgroup G}
    (hZ : Odd (Nat.card (center ↥J))) {a : G} (haJ : a ∈ J) (ha : orderOf a = 2)
    {L : Subgroup (↥J ⧸ center ↥J)}
    (hL : ⁅centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)),
        centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J))⁆ = L)
    (hLp : ⁅L, L⁆ = L)
    (hLL : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 2)
    {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ = K) :
    IsQuasisimple ↥K ∧ Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 3 2 2 := by
  classical
  let Cj : Subgroup ↥J := centralizer ({⟨a, haJ⟩} : Set ↥J)
  let Kj : Subgroup ↥J := ⁅⁅Cj, Cj⁆, ⁅Cj, Cj⁆⁆
  obtain ⟨-, hKjmap, hKjperf, φ, hφsurj, hφker, hφcenter, -⟩ :=
    lift_setup hZ haJ ha hL hLp (Cj := Cj) (Kj := Kj) rfl rfl
  have hKjeq : Kj.map J.subtype = K := hKjmap.trans hK
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect ↥L := hLperf
  have hLsimple : IsSimpleGroup (↥L ⧸ center ↥L) :=
    Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLL
  have hLnonab : ∃ x y : ↥L ⧸ center ↥L, x * y ≠ y * x := by
    have : Nontrivial (↥L ⧸ center ↥L) := hLsimple.toNontrivial
    have h := Group.IsPerfect.not_isMulCommutative (↥L ⧸ center ↥L)
    simpa only [isMulCommutative_iff, not_forall] using h
  have hLq : IsQuasisimple ↥L := ⟨hLperf, hLsimple, hLnonab⟩
  have hKjq : IsQuasisimple ↥Kj :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hKjperf φ hφsurj hφker).mpr hLq
  have hKq : IsQuasisimple ↥K := by
    have e : ↥Kj ≃* ↥K :=
      (Subgroup.equivMapOfInjective Kj J.subtype J.subtype_injective).trans
        (MulEquiv.subgroupCongr hKjeq)
    exact CFSG.IsQuasisimple.of_mulEquiv e.symm hKjq
  refine ⟨hKq, ?_⟩
  have hc : center ↥Kj = ((QuotientGroup.mk' (center ↥L)).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hφcenter]
  let e : ↥Kj ⧸ center ↥Kj ≃* ↥L ⧸ center ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hφsurj))
  have hLieKj : Blueprint.LieModel (↥Kj ⧸ center ↥Kj) .PSL 3 2 2 :=
    Blueprint.LieModel.of_mulEquiv e.symm hLL
  have eKjK : ↥Kj ≃* ↥K :=
    (Subgroup.equivMapOfInjective Kj J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hKjeq)
  exact Blueprint.LieModel.quotient_center_of_mulEquiv eKjK hLieKj

theorem exists_center_centralizerCore_of_quotient {J : Subgroup G}
    (hZ : Odd (Nat.card (center ↥J))) {a : G} (haJ : a ∈ J) (ha : orderOf a = 2)
    {L : Subgroup (↥J ⧸ center ↥J)}
    (hL : ⁅centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)),
        centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J))⁆ = L)
    (hLp : ⁅L, L⁆ = L)
    (hq : ∃ q : ↥J ⧸ center ↥J, orderOf q = 4 ∧ q * q = (QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J) ∧
      (center ↥L).map L.subtype = zpowers q)
    {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ = K) :
    ∃ w ∈ K, orderOf w = 4 ∧ w * w = a ∧ (∀ k ∈ K, w * k = k * w) ∧
      ∀ c ∈ K, (∀ k ∈ K, c * k = k * c) → (∃ n : ℕ, c ^ 2 ^ n = 1) → c ∈ zpowers w := by
  classical
  let Cj : Subgroup ↥J := centralizer ({⟨a, haJ⟩} : Set ↥J)
  let Kj : Subgroup ↥J := ⁅⁅Cj, Cj⁆, ⁅Cj, Cj⁆⁆
  obtain ⟨-, hKjmap, -, φ, hφsurj, hφker, hφcenter, hφval⟩ :=
    lift_setup hZ haJ ha hL hLp (Cj := Cj) (Kj := Kj) rfl rfl
  have hKjeq : Kj.map J.subtype = K := hKjmap.trans hK
  let π : ↥J →* ↥J ⧸ center ↥J := QuotientGroup.mk' (center ↥J)
  have ha2 : (⟨a, haJ⟩ : ↥J) ^ 2 = 1 := by
    have h : orderOf (⟨a, haJ⟩ : ↥J) = 2 := by
      rw [Subgroup.orderOf_mk a haJ, ha]
    rw [← h, pow_orderOf_eq_one]
  have hā2 : (QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J) ^ 2 = 1 := by
    have h : (QuotientGroup.mk' (center ↥J)) ((⟨a, haJ⟩ : ↥J) ^ 2) = 1 := by
      rw [ha2, map_one]
    rwa [map_pow] at h
  obtain ⟨q, hqord, hqq, hqcenter⟩ := hq
  have hq4 : q ^ 4 = 1 := by rw [← hqord, pow_orderOf_eq_one]
  have hqmem : q ∈ (center ↥L).map L.subtype := by
    rw [hqcenter]
    exact Subgroup.mem_zpowers q
  obtain ⟨cq, hcqcen, hcqval⟩ := Subgroup.mem_map.mp hqmem
  obtain ⟨k0, hk0⟩ := hφsurj cq
  have hk0cen : k0 ∈ center ↥Kj := by
    rw [← hφcenter, Subgroup.mem_comap, hk0]
    exact hcqcen
  obtain ⟨e, m, hm, hk0ord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k0).ne'
  let wJ : ↥Kj := k0 ^ m
  have hwJcen : wJ ∈ center ↥Kj := Subgroup.pow_mem _ hk0cen m
  have hπwJ : π (wJ : ↥J) = q ^ m := by
    have hφw : φ wJ = cq ^ m := by
      change φ (k0 ^ m) = cq ^ m
      rw [map_pow, hk0]
    have h1 : L.subtype (cq ^ m) = q ^ m := by rw [map_pow, hcqval]
    have h2 := hφval wJ
    rw [hφw] at h2
    rw [← h2]
    exact h1
  have hwJ2e : (wJ : ↥J) ^ 2 ^ e = 1 := by
    have h : (wJ : ↥Kj) ^ 2 ^ e = 1 := by
      change (k0 ^ m) ^ 2 ^ e = 1
      rw [← pow_mul, Nat.mul_comm m (2 ^ e), ← hk0ord, pow_orderOf_eq_one]
    have := congrArg (fun z : ↥Kj => (z : ↥J)) h
    simpa using this
  have hwJ4_center : (wJ : ↥J) ^ 4 ∈ center ↥J := by
    have hπ4 : π ((wJ : ↥J) ^ 4) = 1 := by
      rw [map_pow, hπwJ, ← pow_mul, Nat.mul_comm m 4, pow_mul, hq4, one_pow]
    rw [← QuotientGroup.ker_mk' (center ↥J)]
    exact MonoidHom.mem_ker.mpr hπ4
  have hwJ4 : (wJ : ↥Kj) ^ 4 = 1 := by
    have hodd : Odd (orderOf ((wJ : ↥J) ^ 4)) :=
      hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard (center ↥J) hwJ4_center)
    have h2 : ((wJ : ↥J) ^ 4) ^ 2 ^ e = 1 := by
      rw [← pow_mul, Nat.mul_comm 4 (2 ^ e), pow_mul, hwJ2e, one_pow]
    have h1 := (pow_eq_one_iff_of_coprime
      (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hodd))).mp ⟨pow_orderOf_eq_one _, h2⟩
    apply Subtype.ext
    simpa using h1
  have hwJ2_ne : (wJ : ↥Kj) ^ 2 ≠ 1 := by
    intro h
    have hcoe : (wJ : ↥J) ^ 2 = 1 := by
      have := congrArg (fun z : ↥Kj => (z : ↥J)) h
      simpa using this
    have hπ2 : π ((wJ : ↥J) ^ 2) = 1 := by rw [hcoe, map_one]
    rw [map_pow, hπwJ] at hπ2
    have hq2m : q ^ (2 * m) = 1 := by
      rwa [← pow_mul, Nat.mul_comm m 2] at hπ2
    have hdvd : 4 ∣ 2 * m := by
      rw [← hqord]
      exact orderOf_dvd_of_pow_eq_one hq2m
    have h2m : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
      (by simpa [mul_assoc] using hdvd)
    exact hm.not_two_dvd_nat h2m
  have hord_wJ : orderOf wJ = 4 := by
    have hdvd : orderOf wJ ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hwJ4
    rcases (Nat.dvd_prime_pow Nat.prime_two (m := 2) (i := orderOf wJ)).mp
      (by simpa using hdvd) with ⟨k, hk2, hk⟩
    have hne1 : orderOf wJ ≠ 1 := by
      intro h
      exact hwJ2_ne (by rw [orderOf_eq_one_iff.mp h]; exact one_pow 2)
    have hne2 : orderOf wJ ≠ 2 := by
      intro h
      exact hwJ2_ne (by rw [← h]; exact pow_orderOf_eq_one wJ)
    interval_cases k
    · rw [hk] at hne1; norm_num at hne1
    · rw [hk] at hne2; norm_num at hne2
    · rw [hk]; norm_num
  have hπwJ2 : π ((wJ : ↥J) ^ 2) = (QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J) := by
    rw [map_pow, hπwJ, ← pow_mul, Nat.mul_comm m 2, pow_mul, pow_two, hqq]
    obtain ⟨t, ht⟩ := hm
    rw [ht, pow_add, pow_mul, hā2, one_pow, one_mul, pow_one]
  have hCj_le : Kj ≤ Cj :=
    (Subgroup.commutator_le_self ⁅Cj, Cj⁆).trans (Subgroup.commutator_le_self Cj)
  have hwJ2_eq : (wJ : ↥J) ^ 2 = (⟨a, haJ⟩ : ↥J) := by
    have hc_mem : (wJ : ↥J) ^ 2 * (⟨a, haJ⟩ : ↥J)⁻¹ ∈ center ↥J := by
      have hπc : π ((wJ : ↥J) ^ 2 * (⟨a, haJ⟩ : ↥J)⁻¹) = 1 := by
        rw [map_mul, map_inv, hπwJ2]
        rw [show π (⟨a, haJ⟩ : ↥J) = (QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J) from rfl]
        group
      rw [← QuotientGroup.ker_mk' (center ↥J)]
      exact MonoidHom.mem_ker.mpr hπc
    have hcomm : Commute ((wJ : ↥J) ^ 2) ((⟨a, haJ⟩ : ↥J)⁻¹) := by
      have hmemCj : (wJ : ↥J) ∈ Cj := hCj_le wJ.2
      have hcomm' : Commute ((wJ : ↥J) ^ 2) (⟨a, haJ⟩ : ↥J) :=
        Commute.pow_left
          (Subgroup.mem_centralizer_iff.mp hmemCj (⟨a, haJ⟩ : ↥J) rfl).symm 2
      exact Commute.inv_right hcomm'
    have h4 : (wJ : ↥J) ^ 4 = 1 := by
      have := congrArg (fun z : ↥Kj => (z : ↥J)) hwJ4
      simpa using this
    have hc2 : ((wJ : ↥J) ^ 2 * (⟨a, haJ⟩ : ↥J)⁻¹) ^ 2 = 1 := by
      rw [hcomm.mul_pow, show ((wJ : ↥J) ^ 2) ^ 2 = (wJ : ↥J) ^ 4 by rw [← pow_mul],
        h4, inv_pow, ha2, inv_one, mul_one]
    have hodd : Odd (orderOf ((wJ : ↥J) ^ 2 * (⟨a, haJ⟩ : ↥J)⁻¹)) :=
      hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard (center ↥J) hc_mem)
    have hc1 : (wJ : ↥J) ^ 2 * (⟨a, haJ⟩ : ↥J)⁻¹ = 1 :=
      (pow_eq_one_iff_of_coprime (Nat.coprime_two_right.mpr hodd)).mp ⟨pow_orderOf_eq_one _, hc2⟩
    exact mul_inv_eq_one.mp hc1
  let w : G := (wJ : G)
  have hwK : w ∈ K := by
    rw [← hKjeq]
    exact Subgroup.mem_map_of_mem J.subtype wJ.2
  have hword : orderOf w = 4 := by
    have h1 : orderOf ((wJ : ↥Kj) : ↥J) = orderOf wJ := Subgroup.orderOf_coe (wJ : ↥Kj)
    have h2 : orderOf (((wJ : ↥Kj) : ↥J) : G) = orderOf ((wJ : ↥Kj) : ↥J) :=
      Subgroup.orderOf_coe ((wJ : ↥Kj) : ↥J)
    rw [show w = (((wJ : ↥Kj) : ↥J) : G) from rfl, h2, h1]
    exact hord_wJ
  have hwsq : w * w = a := by
    have := congrArg (fun z : ↥J => (z : G)) hwJ2_eq
    simpa [w, pow_two] using this
  have hwcentral : ∀ k ∈ K, w * k = k * w := by
    intro k hk
    rw [← hKjeq, Subgroup.mem_map] at hk
    obtain ⟨kJ, hkJ, rfl⟩ := hk
    have h := congrArg (fun z : ↥Kj => (z : G))
      (Subgroup.mem_center_iff.mp hwJcen ⟨kJ, hkJ⟩)
    simpa [w] using h.symm
  refine ⟨w, hwK, hword, hwsq, hwcentral, ?_⟩
  intro c hcK hcC hc2
  rw [← hKjeq, Subgroup.mem_map] at hcK
  obtain ⟨cJ, hcJ, hcval⟩ := hcK
  let cK : ↥Kj := ⟨cJ, hcJ⟩
  have hcKcen : cK ∈ center ↥Kj := by
    rw [Subgroup.mem_center_iff]
    intro kJ
    apply Subtype.ext
    have hkK : (kJ : G) ∈ K := by
      rw [← hKjeq]
      exact Subgroup.mem_map_of_mem J.subtype kJ.2
    have h := hcC (kJ : G) hkK
    rw [← hcval] at h
    apply Subtype.ext
    simpa [cK] using h.symm
  have hφcKcen : φ cK ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨kJ, rfl⟩ := hφsurj l
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subgroup.mem_center_iff.mp hcKcen kJ)
  have hqc : π (cK : ↥J) ∈ Subgroup.zpowers q := by
    rw [← hqcenter]
    have h := Subgroup.mem_map_of_mem L.subtype hφcKcen
    rw [hφval cK] at h
    exact h
  have hq_mem : q ∈ Subgroup.zpowers (q ^ m) := by
    rw [mem_zpowers_pow_iff, hqord]
    exact Nat.coprime_iff_gcd_eq_one.mp
      (by simpa using Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hm))
  have hπc_mem : π (cK : ↥J) ∈ Subgroup.zpowers (q ^ m) :=
    (Subgroup.zpowers_le.mpr hq_mem) hqc
  have hπc_zpow : π (cK : ↥J) ∈ Subgroup.zpowers (π (wJ : ↥J)) := by
    rwa [hπwJ]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hπc_zpow
  have hzker : cK * (wJ ^ j)⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change L.subtype (φ (cK * (wJ ^ j)⁻¹)) = 1
    rw [hφval]
    change π ((cK * (wJ ^ j)⁻¹ : ↥Kj) : ↥J) = 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, map_mul, map_inv,
      map_zpow]
    rw [hj]
    simp
  have hz2 : ∃ n : ℕ, (cK * (wJ ^ j)⁻¹) ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hc2
    refine ⟨n + 2, ?_⟩
    have hcK2 : cK ^ 2 ^ n = 1 := by
      have h : (cK : ↥J) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        have hcJG : ((cK : ↥J) : G) = c := hcval
        rw [hcJG]
        exact hn
      exact Subtype.ext (by simpa using h)
    have hwJj4 : (wJ ^ j) ^ 4 = 1 := by
      have h := zpow_pow_orderOf (x := wJ) (i := j)
      rwa [hord_wJ] at h
    have hpow : 2 ^ (n + 2) = 2 ^ n * 4 := by
      rw [pow_add]
      norm_num
    have hcomm : Commute cK ((wJ ^ j)⁻¹) :=
      Commute.inv_right (Subgroup.mem_center_iff.mp hcKcen (wJ ^ j)).symm
    rw [hcomm.mul_pow]
    have h1 : cK ^ 2 ^ (n + 2) = 1 := by
      rw [hpow, pow_mul, hcK2, one_pow]
    have h2 : ((wJ ^ j)⁻¹) ^ 2 ^ (n + 2) = 1 := by
      rw [inv_pow, hpow, pow_mul', hwJj4, one_pow, inv_one]
    rw [h1, h2, mul_one]
  have hz_odd : Odd (orderOf (cK * (wJ ^ j)⁻¹)) := by
    have hz_center : ((cK * (wJ ^ j)⁻¹ : ↥Kj) : ↥J) ∈ center ↥J := by
      have h1 : π ((cK * (wJ ^ j)⁻¹ : ↥Kj) : ↥J) = 1 := by
        have := congrArg (fun z : ↥L => L.subtype z) (MonoidHom.mem_ker.mp hzker)
        rwa [hφval] at this
      rw [← QuotientGroup.ker_mk' (center ↥J)]
      exact MonoidHom.mem_ker.mpr h1
    rw [← Subgroup.orderOf_coe (cK * (wJ ^ j)⁻¹)]
    exact hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard (center ↥J) hz_center)
  have hz1 : cK * (wJ ^ j)⁻¹ = 1 := by
    obtain ⟨n, hn⟩ := hz2
    exact (pow_eq_one_iff_of_coprime
      (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hz_odd))).mp ⟨pow_orderOf_eq_one _, hn⟩
  have hcK_eq : cK = wJ ^ j := mul_inv_eq_one.mp hz1
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  have hcval' : (cK : G) = c := hcval
  have h := congrArg (fun z : ↥Kj => (z : G)) hcK_eq
  rw [hcval'] at h
  simpa [w] using h.symm

theorem exists_noncentral_involution_centralizerCore_of_quotient {J : Subgroup G}
    (hZ : Odd (Nat.card (center ↥J))) {a : G} (haJ : a ∈ J) (ha : orderOf a = 2)
    {L : Subgroup (↥J ⧸ center ↥J)}
    (hL : ⁅centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)),
        centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J))⁆ = L)
    (hLp : ⁅L, L⁆ = L)
    (hu : ∃ u ∈ L, orderOf u = 2 ∧ ∃ x ∈ L, u * x ≠ x * u)
    {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ = K) :
    ∃ u ∈ K, orderOf u = 2 ∧ ∃ k ∈ K, u * k ≠ k * u := by
  classical
  let Cj : Subgroup ↥J := centralizer ({⟨a, haJ⟩} : Set ↥J)
  let Kj : Subgroup ↥J := ⁅⁅Cj, Cj⁆, ⁅Cj, Cj⁆⁆
  obtain ⟨-, hKjmap, -, φ, hφsurj, hφker, hφcenter, hφval⟩ :=
    lift_setup hZ haJ ha hL hLp (Cj := Cj) (Kj := Kj) rfl rfl
  have hKjeq : Kj.map J.subtype = K := hKjmap.trans hK
  let π : ↥J →* ↥J ⧸ center ↥J := QuotientGroup.mk' (center ↥J)
  obtain ⟨u, huL, huord, x, hxL, hux⟩ := hu
  obtain ⟨u0, hu0⟩ := hφsurj ⟨u, huL⟩
  have hπu0 : π (u0 : ↥J) = u := by
    have h := hφval u0
    rw [hu0] at h
    simpa [π] using h.symm
  have hu2 : u ^ 2 = 1 := by rw [← huord, pow_orderOf_eq_one]
  have hu0sq_center : (u0 : ↥J) ^ 2 ∈ center ↥J := by
    have h1 : π ((u0 : ↥J) ^ 2) = 1 := by rw [map_pow, hπu0, hu2]
    rw [← QuotientGroup.ker_mk' (center ↥J)]
    exact MonoidHom.mem_ker.mpr h1
  let n : ℕ := orderOf ((u0 : ↥J) ^ 2)
  have hn_odd : Odd n :=
    hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard (center ↥J) hu0sq_center)
  let u1 : ↥Kj := u0 ^ n
  have hπu1 : π ((u1 : ↥Kj) : ↥J) = u := by
    change π ((u0 : ↥J) ^ n) = u
    rw [map_pow, hπu0]
    obtain ⟨t, ht⟩ := hn_odd
    rw [ht, pow_add, pow_mul, hu2, one_pow, one_mul, pow_one]
  have hu1sq : u1 ^ 2 = 1 := by
    have h : ((u0 : ↥J) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      exact pow_orderOf_eq_one ((u0 : ↥J) ^ 2)
    exact Subtype.ext (by simpa [u1] using h)
  have hu1ne : u1 ≠ 1 := by
    intro h
    have h1 : π ((u1 : ↥Kj) : ↥J) = 1 := by rw [h]; simp
    rw [hπu1] at h1
    have h2 : orderOf u = 1 := orderOf_eq_one_iff.mpr h1
    rw [huord] at h2
    norm_num at h2
  have hord_u1 : orderOf u1 = 2 := by
    have hdvd : orderOf u1 ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu1sq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1ne
    · exact h
  obtain ⟨x0, hx0⟩ := hφsurj ⟨x, hxL⟩
  have hπx0 : π ((x0 : ↥Kj) : ↥J) = x := by
    have h := hφval x0
    rw [hx0] at h
    simpa [π] using h.symm
  have hnoncomm : u1 * x0 ≠ x0 * u1 := by
    intro h
    have h' := congrArg (fun z : ↥Kj => π ((z : ↥Kj) : ↥J)) h
    simp only [Subgroup.coe_mul, map_mul, hπu1, hπx0] at h'
    exact hux h'
  refine ⟨(u1 : G), ?_, ?_, (x0 : G), ?_, ?_⟩
  · rw [← hKjeq]
    exact Subgroup.mem_map_of_mem J.subtype u1.2
  · have h1 : orderOf ((u1 : ↥Kj) : ↥J) = orderOf u1 := Subgroup.orderOf_coe (u1 : ↥Kj)
    have h2 : orderOf (((u1 : ↥Kj) : ↥J) : G) = orderOf ((u1 : ↥Kj) : ↥J) :=
      Subgroup.orderOf_coe ((u1 : ↥Kj) : ↥J)
    rw [h2, h1]
    exact hord_u1
  · rw [← hKjeq]
    exact Subgroup.mem_map_of_mem J.subtype x0.2
  · intro h
    exact hnoncomm (by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h)

theorem mul_self_mem_centralizerCore_of_quotient {J : Subgroup G}
    (hZ : Odd (Nat.card (center ↥J))) {a : G} (haJ : a ∈ J) (ha : orderOf a = 2)
    {L : Subgroup (↥J ⧸ center ↥J)}
    (hL : ⁅centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)),
        centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J))⁆ = L)
    (hLp : ⁅L, L⁆ = L)
    (hsq : ∀ y ∈ centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)), y * y ∈ L)
    {K : Subgroup G}
    (hK : ⁅(⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆ : Subgroup G),
        ⁅J ⊓ centralizer ({a} : Set G), J ⊓ centralizer ({a} : Set G)⁆⁆ = K)
    {y : G} (hy : y ∈ J ⊓ centralizer ({a} : Set G)) (hy2 : ∃ n : ℕ, (y * y) ^ 2 ^ n = 1) :
    y * y ∈ K := by
  classical
  let Cj : Subgroup ↥J := centralizer ({⟨a, haJ⟩} : Set ↥J)
  let Kj : Subgroup ↥J := ⁅⁅Cj, Cj⁆, ⁅Cj, Cj⁆⁆
  obtain ⟨hCjmap, hKjmap, -, φ, hφsurj, hφker, hφcenter, hφval⟩ :=
    lift_setup hZ haJ ha hL hLp (Cj := Cj) (Kj := Kj) rfl rfl
  have hKjeq : Kj.map J.subtype = K := hKjmap.trans hK
  let π : ↥J →* ↥J ⧸ center ↥J := QuotientGroup.mk' (center ↥J)
  let yj : ↥J := ⟨y, hy.1⟩
  have hyjCj : yj ∈ Cj := by
    show yj ∈ centralizer ({⟨a, haJ⟩} : Set ↥J)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 a rfl)
  have hπyjC : π (yj : ↥J) ∈
      centralizer ({(QuotientGroup.mk ⟨a, haJ⟩ : ↥J ⧸ center ↥J)} : Set (↥J ⧸ center ↥J)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hcomm : (⟨a, haJ⟩ : ↥J) * yj = yj * ⟨a, haJ⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 a rfl)
    have := congrArg π hcomm
    simpa [π] using this
  have hmemL : π (yj : ↥J) * π (yj : ↥J) ∈ L :=
    hsq (π (yj : ↥J)) hπyjC
  obtain ⟨k, hk⟩ := hφsurj ⟨π (yj : ↥J) * π (yj : ↥J), hmemL⟩
  have hπk : π (k : ↥J) = π (yj : ↥J) * π (yj : ↥J) := by
    have h := hφval k
    rw [hk] at h
    simpa [π] using h.symm
  let kJ : ↥J := k
  have hkKj : kJ ∈ Kj := k.2
  have hc_center : (kJ⁻¹ * (yj * yj) : ↥J) ∈ center ↥J := by
    have h1 : π (kJ⁻¹ * (yj * yj) : ↥J) = 1 := by
      rw [map_mul, map_inv, hπk, map_mul]
      group
    rw [← QuotientGroup.ker_mk' (center ↥J)]
    exact MonoidHom.mem_ker.mpr h1
  have hc_odd : Odd (orderOf (kJ⁻¹ * (yj * yj))) :=
    hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard (center ↥J) hc_center)
  have hyj2_eq : yj * yj = kJ * (kJ⁻¹ * (yj * yj)) := by group
  obtain ⟨n, hn⟩ := hy2
  have hyj2_pow : (yj * yj) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    simpa using hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hyj2_one : yj * yj = 1 := by simpa [hn0] using hyj2_pow
    have hG : y * y = 1 := by
      have := congrArg (fun z : ↥J => (z : G)) hyj2_one
      simpa [yj] using this
    rw [hG]
    exact K.one_mem
  · have h2n1 : 1 < 2 ^ n := Nat.one_lt_pow (Nat.ne_of_gt hnpos) (by norm_num)
    have hcop : Nat.Coprime (Nat.card (center ↥J)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hZ)
    obtain ⟨t, -, htmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2n1
    set e : ℕ := Nat.card (center ↥J) * t with he
    have he_mod : e % 2 ^ n = 1 := by rw [he]; exact htmod
    have he_dvd : Nat.card (center ↥J) ∣ e := ⟨t, by rw [he]⟩
    have hdiv : e = 2 ^ n * (e / 2 ^ n) + 1 := by
      have h := Nat.div_add_mod e (2 ^ n)
      rw [he_mod] at h
      exact h.symm
    have hyj2_e : (yj * yj) ^ e = yj * yj := by
      rw [hdiv, pow_add, pow_mul, hyj2_pow, one_pow, one_mul, pow_one]
    have hcomm : Commute kJ (kJ⁻¹ * (yj * yj)) :=
      Subgroup.mem_center_iff.mp hc_center kJ
    have hce : (kJ⁻¹ * (yj * yj)) ^ e = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (Subgroup.orderOf_dvd_natCard (center ↥J) hc_center).trans he_dvd
    have hkpow : (yj * yj) ^ e = kJ ^ e := by
      rw [hyj2_eq, hcomm.mul_pow, hce, mul_one]
    have hyj2_mem : yj * yj ∈ Kj := by
      rw [← hyj2_e, hkpow]
      exact Kj.pow_mem hkKj e
    rw [← hKjeq]
    exact Subgroup.mem_map_of_mem J.subtype (by simpa [yj] using hyj2_mem)

end Lift

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
