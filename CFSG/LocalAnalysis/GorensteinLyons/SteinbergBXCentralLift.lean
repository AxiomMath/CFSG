module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLocal
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {L S : Type*} [Group L] [Group S]

theorem conj_commutatorElement_eq (g x y : L) :
    g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_left_of_mem_center {a b y : L} (h : ⁅b, y⁆ ∈ center L) :
    ⁅a * b, y⁆ = ⁅b, y⁆ * ⁅a, y⁆ := by
  have hc := mem_center_iff.mp h a
  rw [commutatorElement_def, commutatorElement_def]
  calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y * b⁻¹ * y⁻¹) * (y * a⁻¹ * y⁻¹) := by group
    _ = (b * y * b⁻¹ * y⁻¹) * a * (y * a⁻¹ * y⁻¹) := by rw [← commutatorElement_def, hc]
    _ = (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group

theorem commutatorElement_inv_left_of_mem_center {x y : L} (h : ⁅x, y⁆ ∈ center L) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have hc := mem_center_iff.mp (inv_mem h) x
  calc ⁅x⁻¹, y⁆ = x⁻¹ * (⁅x, y⁆⁻¹ * x) := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆⁻¹ := by rw [← hc, inv_mul_cancel_left]

theorem commutatorElement_pow_left_of_mem_center {x y : L} (h : ⁅x, y⁆ ∈ center L) (m : ℕ) :
    ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', commutatorElement_mul_left_of_mem_center (ih ▸ pow_mem h m), ih, pow_succ]

theorem commutatorElement_zpow_left_of_mem_center {x y : L} (h : ⁅x, y⁆ ∈ center L) (m : ℤ) :
    ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m := by
  rcases m with m | m
  · simp only [Int.ofNat_eq_natCast, zpow_natCast, commutatorElement_pow_left_of_mem_center h]
  · rw [zpow_negSucc, zpow_negSucc, commutatorElement_inv_left_of_mem_center
      ((commutatorElement_pow_left_of_mem_center h (m + 1)).symm ▸ pow_mem h (m + 1)),
      commutatorElement_pow_left_of_mem_center h]

theorem commutatorElement_zpow_right_of_mem_center {x y : L} (h : ⁅x, y⁆ ∈ center L) (m : ℤ) :
    ⁅x, y ^ m⁆ = ⁅x, y⁆ ^ m := by
  have h' : ⁅y, x⁆ ∈ center L := by rw [← commutatorElement_inv]; exact inv_mem h
  rw [← commutatorElement_inv, commutatorElement_zpow_left_of_mem_center h', ←
    commutatorElement_inv y x, inv_zpow]

theorem commutatorElement_zpow_zpow_of_mem_center {x y : L} (h : ⁅x, y⁆ ∈ center L) (a b : ℤ) :
    ⁅x ^ a, y ^ b⁆ = ⁅x, y⁆ ^ (a * b) := by
  have hb : ⁅x, y ^ b⁆ ∈ center L := by
    rw [commutatorElement_zpow_right_of_mem_center h]; exact zpow_mem h b
  rw [commutatorElement_zpow_left_of_mem_center hb, commutatorElement_zpow_right_of_mem_center h,
    ← zpow_mul, mul_comm]

theorem commutatorElement_eq_one_of_conj {p : ℕ} [hp : Fact p.Prime] {x y g : L}
    (hxp : x ^ p = 1) (hc : ⁅x, y⁆ ∈ center L) {e : ℤ} (he : ¬ (p : ℤ) ∣ e - 1)
    (hg : g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ e) : ⁅x, y⁆ = 1 := by
  have hw : g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ := by rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
  have h1 : ⁅x, y⁆ ^ (e - 1) = 1 := by rw [zpow_sub_one, ← hg, hw, mul_inv_cancel]
  have h2 : ⁅x, y⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left_of_mem_center hc, hxp, commutatorElement_one_left]
  rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ orderOf_dvd_iff_zpow_eq_one.mpr h1) he

theorem exists_pElement_lift [Finite L] {p : ℕ} [hp : Fact p.Prime] (π : L →* S) (x : L)
    (hx : π x ^ p = 1) : ∃ y : L, π y = π x ∧ ∃ N : ℕ, y ^ p ^ N = 1 := by
  obtain ⟨N, b, hb, hxb⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.out.ne_one
  have hcop : Nat.Coprime b p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
  obtain ⟨b', -, hb'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  refine ⟨x ^ (b * b'), ?_, N, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hx, hb', pow_one]
  · rw [← pow_mul, show b * b' * p ^ N = orderOf x * b' by rw [hxb]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem exists_mul_pow_eq_one_of_conj {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup L}
    (hZ : Z ≤ center L) {y g : L} {N : ℕ} (hyN : y ^ p ^ N = 1) (hyp : y ^ p ∈ Z) {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ 1 - a) (hg : (y ^ a)⁻¹ * (g * y * g⁻¹) ∈ Z) :
    ∃ z ∈ Z, (y * z) ^ p = 1 := by
  set z₀ := (y ^ a)⁻¹ * (g * y * g⁻¹) with hz₀
  set u := y ^ p with hu
  have hz₀c := mem_center_iff.mp (hZ hg)
  have huc := mem_center_iff.mp (hZ hyp)
  have hgy : g * y * g⁻¹ = y ^ a * z₀ := by rw [hz₀, mul_inv_cancel_left]
  have h1 : (y ^ a * z₀) ^ p = u := by
    rw [← hgy, conj_pow, ← hu, huc g, mul_inv_cancel_right]
  have h2 : z₀ ^ p = u ^ (1 - a) := by
    have hcz : Commute (y ^ a) z₀ := hz₀c (y ^ a)
    rw [hcz.mul_pow] at h1
    have h3 : (y ^ a) ^ p = u ^ a := by
      rw [hu, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h3] at h1
    calc z₀ ^ p = (u ^ a)⁻¹ * (u ^ a * z₀ ^ p) := by group
      _ = (u ^ a)⁻¹ * u := by rw [h1]
      _ = u ^ (1 - a) := by group
  have huN : u ^ p ^ N = 1 := by rw [hu, ← pow_mul, mul_comm, pow_mul, hyN, one_pow]
  have hcop : IsCoprime (1 - a) ((p : ℤ) ^ N) :=
    (((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)).mpr ha).pow_left).symm
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨z₀ ^ (-s), zpow_mem hg _, ?_⟩
  have hcomm : Commute y (z₀ ^ (-s)) := mem_center_iff.mp (zpow_mem (hZ hg) (-s)) y
  rw [hcomm.mul_pow, ← hu, ← zpow_natCast (z₀ ^ (-s)), ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h2, ← zpow_mul]
  have h4 : u ^ ((1 - a) * -s) = u⁻¹ := by
    have h5 : (1 - a) * -s = -1 + (p : ℤ) ^ N * t := by linear_combination -hst
    have h6 : u ^ ((p : ℤ) ^ N) = 1 := by rw [← Int.natCast_pow, zpow_natCast, huN]
    rw [h5, zpow_add, zpow_neg_one, zpow_mul, h6, one_zpow, mul_one]
  rw [h4, mul_inv_cancel]

section Independent

variable {ι : Type*}

theorem iSup_zpowers_eq_closure_range {G : Type*} [Group G] (g : ι → G) :
    ⨆ i, zpowers (g i) = closure (Set.range g) := by
  rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
  simp only [zpowers_eq_closure]

variable [Fintype ι]

theorem card_closure_range_of_iSupIndep {G : Type*} [Group G] (g : ι → G)
    (hcomm : ∀ i j, Commute (g i) (g j)) (hind : iSupIndep fun i => zpowers (g i)) :
    Nat.card (closure (Set.range g)) = ∏ i, orderOf (g i) := by
  have hH : Pairwise fun i j : ι => ∀ x y : G, x ∈ zpowers (g i) → y ∈ zpowers (g j) →
      Commute x y := by
    intro i j _ x y hx hy
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hcomm i j).zpow_zpow m l
  have hinj := injective_noncommPiCoprod_of_iSupIndep (hcomm := hH) hind
  rw [← iSup_zpowers_eq_closure_range, ← noncommPiCoprod_range (hcomm := hH),
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
  simp only [Nat.card_zpowers]

theorem elementaryAbelian_of_iSupIndep {p : ℕ} [hp : Fact p.Prime] (π : L →* S) (v : ι → L)
    (hcomm : ∀ i j, Commute (v i) (v j)) (hvp : ∀ i, v i ^ p = 1) (hc1 : ∀ i, π (v i) ≠ 1)
    (hind : iSupIndep fun i => zpowers (π (v i))) :
    CFSG.IsElementaryAbelian p (closure (Set.range v)) ∧
      Nat.card (closure (Set.range v)) = p ^ Fintype.card ι ∧
      Set.InjOn π (closure (Set.range v)) ∧
      (closure (Set.range v)).map π = closure (Set.range (π ∘ v)) := by
  have hord : ∀ i, orderOf (π (v i)) = p := fun i =>
    orderOf_eq_prime (by rw [← map_pow, hvp, map_one]) (hc1 i)
  have hordv : ∀ i, orderOf (v i) = p := fun i =>
    orderOf_eq_prime (hvp i) fun h => hc1 i (by rw [h, map_one])
  have hinjH : ∀ i, ∀ x ∈ zpowers (v i), π x = 1 → x = 1 := by
    intro i x hx h1
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow, ← orderOf_dvd_iff_zpow_eq_one, hord] at h1
    rw [← orderOf_dvd_iff_zpow_eq_one, hordv]
    exact h1
  have hindv : iSupIndep fun i => zpowers (v i) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_def]
    intro x hx hx'
    apply hinjH i x hx
    have h1 : π x ∈ zpowers (π (v i)) := by
      rw [← MonoidHom.map_zpowers]; exact mem_map_of_mem π hx
    have h2 : π x ∈ ⨆ (j) (_ : j ≠ i), zpowers (π (v j)) := by
      have hle : (⨆ (j) (_ : j ≠ i), zpowers (v j)) ≤
          (⨆ (j) (_ : j ≠ i), zpowers (π (v j))).comap π := by
        refine iSup₂_le fun j hj => ?_
        rw [← map_le_iff_le_comap, MonoidHom.map_zpowers]
        exact le_iSup₂ (f := fun j (_ : j ≠ i) => zpowers (π (v j))) j hj
      exact hle hx'
    exact (disjoint_def.mp ((iSupIndep_def.mp hind) i)) h1 h2
  have hcommv : ∀ i j, Commute (π (v i)) (π (v j)) := fun i j => (hcomm i j).map π
  have hcardV : Nat.card (closure (Set.range v)) = p ^ Fintype.card ι := by
    rw [card_closure_range_of_iSupIndep v hcomm hindv]
    simp [hordv]
  have hcardA : Nat.card (closure (Set.range (π ∘ v))) = p ^ Fintype.card ι := by
    rw [card_closure_range_of_iSupIndep (π ∘ v) hcommv hind]
    simp [hord]
  have hmap : (closure (Set.range v)).map π = closure (Set.range (π ∘ v)) := by
    rw [MonoidHom.map_closure, Set.range_comp]
  have hVcomm : IsMulCommutative (closure (Set.range v)) := by
    refine isMulCommutative_closure ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hcomm i j
  have hfin : Finite (closure (Set.range v)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp.out.ne_zero)
  refine ⟨{ toIsMulCommutative := hVcomm, exponent_dvd_p := ?_ }, hcardV, ?_, hmap⟩
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun ⟨x, hx⟩ => Subtype.ext ?_
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    induction hx using closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hvp i
    | one => exact one_pow p
    | mul y z hy hz ihy ihz =>
      have hyz : Commute y z := by
        have := (hVcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
        exact congrArg Subtype.val this
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    | inv y _ ihy => rw [inv_pow, ihy, inv_one]
  ·
    have hsurj : Function.Surjective (π.subgroupMap (closure (Set.range v))) :=
      π.subgroupMap_surjective _
    have hbij := hsurj.bijective_of_nat_card_le (by rw [hmap, hcardV, hcardA])
    intro x hx y hy hxy
    have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
    exact congrArg Subtype.val this

end Independent

theorem commute_of_mem_comap_map {V : Subgroup L} (hV : ∀ x ∈ V, ∀ y ∈ V, Commute x y)
    (π : L →* S) (hZ : π.ker ≤ center L) {x y : L} (hx : x ∈ (V.map π).comap π)
    (hy : y ∈ (V.map π).comap π) : Commute x y := by
  obtain ⟨x', hx', hxx⟩ := mem_map.mp hx
  obtain ⟨y', hy', hyy⟩ := mem_map.mp hy
  have hzx : x'⁻¹ * x ∈ center L := hZ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hxx,
    inv_mul_cancel])
  have hzy : y'⁻¹ * y ∈ center L := hZ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hyy,
    inv_mul_cancel])
  rw [← mul_inv_cancel_left x' x, ← mul_inv_cancel_left y' y]
  refine Commute.mul_left (Commute.mul_right (hV x' hx' y' hy') ?_) ?_
  · exact mem_center_iff.mp hzy x'
  · exact (mem_center_iff.mp hzx _).symm

theorem exists_lift_of_weyl [Finite L] {ι : Type*} [Fintype ι] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (π : L →* S) (hπ : Function.Surjective π) (hZ : π.ker ≤ center L) (c : ι → S)
    (hcp : ∀ i, c i ^ p = 1) (hc1 : ∀ i, c i ≠ 1) (hcomm : ∀ i j, Commute (c i) (c j))
    (hind : iSupIndep fun i => zpowers (c i))
    (hinv : ∀ i, ∃ g : S, ∃ a : ℤ, ¬ (p : ℤ) ∣ 1 - a ∧ g * c i * g⁻¹ = c i ^ a)
    (hpair : ∀ i j, i ≠ j → ∃ g : S,
      (∃ a b : ℤ, ¬ (p : ℤ) ∣ a * b - 1 ∧ g * c i * g⁻¹ = c i ^ a ∧ g * c j * g⁻¹ = c j ^ b) ∨
        (g * c i * g⁻¹ = c j ∧ g * c j * g⁻¹ = c i)) :
    ∃ v : ι → L, (∀ i, π (v i) = c i) ∧ (∀ i, orderOf (v i) = p) ∧
      (∀ i j, Commute (v i) (v j)) ∧ CFSG.IsElementaryAbelian p (closure (Set.range v)) ∧
      Nat.card (closure (Set.range v)) = p ^ Fintype.card ι ∧
      Set.InjOn π (closure (Set.range v)) ∧ (closure (Set.range v)).map π = closure (Set.range c) ∧
      ∀ x ∈ (closure (Set.range c)).comap π, ∀ y ∈ (closure (Set.range c)).comap π,
        Commute x y := by
  have hlift : ∀ i, ∃ v : L, π v = c i ∧ v ^ p = 1 := by
    intro i
    obtain ⟨x, hx⟩ := hπ (c i)
    obtain ⟨y, hy, N, hyN⟩ := exists_pElement_lift π x (by rw [hx, hcp])
    rw [hx] at hy
    obtain ⟨g₀, a, ha, hg₀⟩ := hinv i
    obtain ⟨g, rfl⟩ := hπ g₀
    obtain ⟨z, hz, hyz⟩ := exists_mul_pow_eq_one_of_conj (g := g) hZ hyN
      (by rw [MonoidHom.mem_ker, map_pow, hy, hcp]) ha
      (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, map_mul, map_mul, map_inv, hy, hg₀,
        inv_mul_cancel])
    exact ⟨y * z, by rw [map_mul, hy, MonoidHom.mem_ker.mp hz, mul_one], hyz⟩
  choose v hvc hvp using hlift
  have hv1 : ∀ i, v i ≠ 1 := fun i h => hc1 i (by rw [← hvc i, h, map_one])
  have hker : ∀ {x : L} {y : S}, π x = y → ∀ {g : L} {e : ℤ}, π g * y * (π g)⁻¹ = y ^ e →
      g * x * g⁻¹ = x ^ e * ((x ^ e)⁻¹ * (g * x * g⁻¹)) ∧
        (x ^ e)⁻¹ * (g * x * g⁻¹) ∈ center L := by
    intro x y hxy g e hge
    refine ⟨(mul_inv_cancel_left _ _).symm, hZ ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, map_mul, map_mul, map_inv, hxy, hge,
      inv_mul_cancel]
  have hcommv : ∀ i j, Commute (v i) (v j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have hw : ⁅v i, v j⁆ ∈ center L := hZ (by
      rw [MonoidHom.mem_ker, map_commutatorElement, hvc, hvc,
        commutatorElement_eq_one_iff_commute.mpr (hcomm i j)])
    rw [← commutatorElement_eq_one_iff_commute]
    obtain ⟨g₀, hg₀⟩ := hpair i j hij
    obtain ⟨g, rfl⟩ := hπ g₀
    rcases hg₀ with ⟨a, b, hab, hgi, hgj⟩ | ⟨hgi, hgj⟩
    · obtain ⟨hi1, hi2⟩ := hker (hvc i) hgi
      obtain ⟨hj1, hj2⟩ := hker (hvc j) hgj
      refine commutatorElement_eq_one_of_conj (g := g) (hvp i) hw hab ?_
      rw [conj_commutatorElement_eq, hi1, hj1,
        CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_left hi2,
        CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_right _ hj2,
        commutatorElement_zpow_zpow_of_mem_center hw]
    · have hgi' : π g * c i * (π g)⁻¹ = c j ^ (1 : ℤ) := by rw [zpow_one, hgi]
      have hgj' : π g * c j * (π g)⁻¹ = c i ^ (1 : ℤ) := by rw [zpow_one, hgj]
      have hzi : (v j ^ (1 : ℤ))⁻¹ * (g * v i * g⁻¹) ∈ center L := hZ (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, map_mul, map_mul, map_inv, hvc, hvc,
          hgi', inv_mul_cancel])
      have hzj : (v i ^ (1 : ℤ))⁻¹ * (g * v j * g⁻¹) ∈ center L := hZ (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, map_mul, map_mul, map_inv, hvc, hvc,
          hgj', inv_mul_cancel])
      have he : ¬ (p : ℤ) ∣ -1 - 1 := by
        intro h
        have h2 : (p : ℤ) ∣ 2 := by
          have := dvd_neg.mpr h
          norm_num at this
          exact this
        have := Int.le_of_dvd (by norm_num) h2
        have h2' : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2')
      refine commutatorElement_eq_one_of_conj (g := g) (hvp i) hw he ?_
      rw [conj_commutatorElement_eq, ← mul_inv_cancel_left (v j ^ (1 : ℤ)) (g * v i * g⁻¹),
        ← mul_inv_cancel_left (v i ^ (1 : ℤ)) (g * v j * g⁻¹),
        CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_left hzi,
        CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_right _ hzj,
        zpow_one, zpow_one, ← commutatorElement_inv, zpow_neg_one]
  have hind' : iSupIndep fun i => zpowers (π (v i)) := by
    simpa only [hvc] using hind
  obtain ⟨hEA, hcard, hinj, hmap⟩ :=
    elementaryAbelian_of_iSupIndep π v hcommv hvp (fun i => (hvc i).symm ▸ hc1 i) hind'
  have hπv : π ∘ v = c := funext hvc
  rw [hπv] at hmap
  refine ⟨v, hvc, fun i => orderOf_eq_prime (hvp i) (hv1 i), hcommv, hEA, hcard, hinj, hmap, ?_⟩
  intro x hx y hy
  rw [← hmap] at hx hy
  refine commute_of_mem_comap_map (fun x hx y hy => ?_) π hZ hx hy
  have := hEA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem exists_fixed_lift [Finite L] {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (α : T →* MulAut L) (π : L →* S) (hZ : π.ker ≤ center L)
    (hker : ∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : L}
    (hxp : x ^ p = 1) (hfix : ∀ t, π (α t x) = π x) :
    ∃ y : L, π y = π x ∧ y ^ p = 1 ∧ ∀ t, α t y = y := by
  let Ω : Subgroup L :=
    { carrier := {z | z ∈ π.ker ∧ z ^ p = 1}
      mul_mem' := by
        rintro z z' ⟨hz, hzp⟩ ⟨hz', hz'p⟩
        refine ⟨mul_mem hz hz', ?_⟩
        rw [(show Commute z z' from mem_center_iff.mp (hZ hz') z).mul_pow, hzp, hz'p, one_mul]
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := by
        rintro z ⟨hz, hzp⟩
        exact ⟨inv_mem hz, by rw [inv_pow, hzp, inv_one]⟩ }
  have hΩ : ∀ {z : L}, z ∈ Ω ↔ z ∈ π.ker ∧ z ^ p = 1 := Iff.rfl
  have hcard : ¬ 2 ∣ Nat.card Ω := by
    have hpg : IsPGroup p Ω := fun z => ⟨1, by
      apply Subtype.ext
      simpa only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one] using (hΩ.mp z.2).2⟩
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    rw [hk]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  obtain ⟨y, hy, hyfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hT α Ω hcard x).2 (by
      intro t w hw
      obtain ⟨hwk, hwp⟩ := hΩ.mp hw
      have h1 : x⁻¹ * α t x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, inv_mul_cancel]
      have h1p : (x⁻¹ * α t x) ^ p = 1 := by
        have hc : Commute x (x⁻¹ * α t x) := mem_center_iff.mp (hZ h1) x
        have : (x * (x⁻¹ * α t x)) ^ p = 1 := by
          rw [mul_inv_cancel_left, ← map_pow, hxp, map_one]
        rwa [hc.mul_pow, hxp, one_mul] at this
      have h2 : α t (x⁻¹ * w) ∈ Ω :=
        hΩ.mpr ⟨hker t _ hwk, by rw [← map_pow, hwp, map_one]⟩
      have : x⁻¹ * α t w = (x⁻¹ * α t x) * α t (x⁻¹ * w) := by
        rw [map_mul, map_inv]; group
      rw [this]
      exact mul_mem (hΩ.mpr ⟨h1, h1p⟩) h2)
  obtain ⟨hyk, hyp⟩ := hΩ.mp hy
  refine ⟨y, ?_, ?_, hyfix⟩
  · have := MonoidHom.mem_ker.mp hyk
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  · have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp (hZ hyk) x
    have : (x * (x⁻¹ * y)) ^ p = 1 := by rw [hc.mul_pow, hxp, hyp, one_mul]
    rwa [mul_inv_cancel_left] at this

theorem exists_fixed_lift_of_weyl [Finite L] {ι : Type*} [Fintype ι] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (π : L →* S) (hπ : Function.Surjective π) (hZ : π.ker ≤ center L) (c : ι → S)
    (hcp : ∀ i, c i ^ p = 1) (hc1 : ∀ i, c i ≠ 1) (hcomm : ∀ i j, Commute (c i) (c j))
    (hind : iSupIndep fun i => zpowers (c i))
    (hinv : ∀ i, ∃ g : S, ∃ a : ℤ, ¬ (p : ℤ) ∣ 1 - a ∧ g * c i * g⁻¹ = c i ^ a)
    (hpair : ∀ i j, i ≠ j → ∃ g : S,
      (∃ a b : ℤ, ¬ (p : ℤ) ∣ a * b - 1 ∧ g * c i * g⁻¹ = c i ^ a ∧ g * c j * g⁻¹ = c j ^ b) ∨
        (g * c i * g⁻¹ = c j ∧ g * c j * g⁻¹ = c i))
    {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T) (α : T →* MulAut L)
    (hker : ∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker)
    (hfix : ∀ t, ∀ x ∈ (closure (Set.range c)).comap π, π (α t x) = π x) :
    ∃ v : ι → L, (∀ i, π (v i) = c i) ∧ (∀ i, orderOf (v i) = p) ∧
      (∀ t i, α t (v i) = v i) ∧ CFSG.IsElementaryAbelian p (closure (Set.range v)) ∧
      Nat.card (closure (Set.range v)) = p ^ Fintype.card ι ∧
      Set.InjOn π (closure (Set.range v)) ∧
      (closure (Set.range v)).map π = closure (Set.range c) := by
  obtain ⟨w, hwc, hwo, -, -, -, -, -, hab⟩ :=
    exists_lift_of_weyl hp2 π hπ hZ c hcp hc1 hcomm hind hinv hpair
  have hwA : ∀ i, w i ∈ (closure (Set.range c)).comap π := fun i =>
    mem_comap.mpr (hwc i ▸ subset_closure (Set.mem_range_self i))
  have hlift : ∀ i, ∃ v : L, π v = c i ∧ v ^ p = 1 ∧ ∀ t, α t v = v := by
    intro i
    obtain ⟨y, hy, hyp, hyfix⟩ := exists_fixed_lift hT α π hZ hker hp2
      (by rw [← hwo i, pow_orderOf_eq_one]) (fun t => hfix t (w i) (hwA i))
    exact ⟨y, hy.trans (hwc i), hyp, hyfix⟩
  choose v hvc hvp hvfix using hlift
  have hvA : ∀ i, v i ∈ (closure (Set.range c)).comap π := fun i =>
    mem_comap.mpr (hvc i ▸ subset_closure (Set.mem_range_self i))
  have hcommv : ∀ i j, Commute (v i) (v j) := fun i j => hab _ (hvA i) _ (hvA j)
  have hind' : iSupIndep fun i => zpowers (π (v i)) := by
    simpa only [hvc] using hind
  obtain ⟨hEA, hcard, hinj, hmap⟩ :=
    elementaryAbelian_of_iSupIndep π v hcommv hvp (fun i => (hvc i).symm ▸ hc1 i) hind'
  have hπv : π ∘ v = c := funext hvc
  rw [hπv] at hmap
  exact ⟨v, hvc, fun i => orderOf_eq_prime (hvp i) fun h => hc1 i (by rw [← hvc i, h, map_one]),
    fun t i => hvfix i t, hEA, hcard, hinj, hmap⟩

theorem exists_involution_commute [Finite L] {ι : Type*} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (π : L →* S) (hπ : Function.Surjective π) (hZ : π.ker ≤ center L) (v : ι → L)
    (hvp : ∀ i, v i ^ p = 1) {s : S} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    (hsv : ∀ i, Commute s (π (v i))) : ∃ u : L, orderOf u = 2 ∧ ∀ i, Commute u (v i) := by
  obtain ⟨x, hx⟩ := hπ s
  obtain ⟨y, hy, N, hyN⟩ := exists_pElement_lift (p := 2) π x (by rw [hx, hs2])
  rw [hx] at hy
  have hyv : ∀ i, Commute y (v i) := by
    intro i
    have hw : ⁅v i, y⁆ ∈ center L := hZ (by
      rw [MonoidHom.mem_ker, map_commutatorElement, hy,
        commutatorElement_eq_one_iff_commute.mpr (hsv i).symm])
    have h1 : ⁅v i, y⁆ ^ p = 1 := by
      rw [← commutatorElement_pow_left_of_mem_center hw, hvp, commutatorElement_one_left]
    have h2 : ⁅v i, y⁆ ^ (2 ^ N) = 1 := by
      rw [← zpow_natCast, ← commutatorElement_zpow_right_of_mem_center hw, zpow_natCast, hyN,
        commutatorElement_one_right]
    have hcop : Nat.Coprime p (2 ^ N) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have h3 : orderOf ⁅v i, y⁆ = 1 := Nat.dvd_one.mp (hcop.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
    exact (commutatorElement_eq_one_iff_commute.mp (orderOf_eq_one_iff.mp h3)).symm
  have hy1 : y ≠ 1 := fun h => hs1 (by rw [← hy, h, map_one])
  obtain ⟨e, he, hye⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyN)
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hye, pow_zero]))
  refine ⟨y ^ 2 ^ (e - 1), ?_, fun i => (hyv i).pow_left _⟩
  have h2e : 2 ^ e = 2 ^ (e - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hye]; exact pow_dvd_pow 2 (by omega)),
    hye, h2e, Nat.mul_div_cancel_left _ (by positivity)]

end CFSG.LocalAnalysis.GorensteinLyons
