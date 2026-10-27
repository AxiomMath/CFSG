module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover
public import CFSG.LocalAnalysis.SectionRank.SignLift
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.ShultStronglyClosedTI
open scoped commutatorElement

variable {E : Type*} [Group E]

theorem commutatorElement_pow_right_of_central (hc : ∀ x y z : E, Commute ⁅x, y⁆ z)
    (x y : E) (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  rw [← commutatorElement_inv, commutatorElement_pow_left_of_central hc, ← inv_pow,
    commutatorElement_inv]

theorem commutatorElement_basis_of_central (hc : ∀ x y z : E, Commute ⁅x, y⁆ z) (x y : E)
    (a b c d : ℕ) :
    ⁅x ^ a * y ^ c, x ^ b * y ^ d⁆ = ⁅x, y⁆ ^ (a * d) * ⁅y, x⁆ ^ (c * b) := by
  rw [commutatorElement_mul_left_of_central hc, commutatorElement_mul_right_of_central hc,
    commutatorElement_mul_right_of_central hc]
  have hxx : ⁅x ^ a, x ^ b⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 (Commute.pow_pow_self x a b)
  have hyy : ⁅y ^ c, y ^ d⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 (Commute.pow_pow_self y c d)
  rw [hxx, hyy, one_mul, mul_one, commutatorElement_pow_left_of_central hc,
    commutatorElement_pow_right_of_central hc, commutatorElement_pow_left_of_central hc,
    commutatorElement_pow_right_of_central hc, ← pow_mul, ← pow_mul, mul_comm d a,
    mul_comm b c]

theorem closure_preimage_eq_top {K : Type*} [Group K] {H : Subgroup K} {s : Set K}
    (hs : Subgroup.closure s = H) :
    Subgroup.closure ((Subtype.val : H → K) ⁻¹' s) = ⊤ := by
  have hsH : s ⊆ H := hs ▸ Subgroup.subset_closure
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have himg : (H.subtype : H → K) '' ((Subtype.val : H → K) ⁻¹' s) = s := by
    rw [Subgroup.coe_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact Set.inter_eq_left.2 hsH
  rw [himg, hs]

section LocalClassTwo

variable {x y z : E} (hzx : Commute z x) (hzy : Commute z y) (hxy : x * y = z * y * x)
include hzx hzy hxy

omit hzy in
theorem pow_mul_eq_of_comm (n : ℕ) : x ^ n * y = z ^ n * y * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * y = x * (x ^ n * y) := by rw [pow_succ', mul_assoc]
      _ = x * (z ^ n * y * x ^ n) := by rw [ih]
      _ = z ^ n * (x * y) * x ^ n := by
        rw [← mul_assoc, ← mul_assoc, ← (hzx.pow_left n).eq]; group
      _ = z ^ (n + 1) * y * x ^ (n + 1) := by
        rw [hxy, pow_succ, pow_succ']; group

theorem pow_mul_pow_eq_of_comm (n m : ℕ) : x ^ n * y ^ m = z ^ (n * m) * y ^ m * x ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x ^ n * y ^ (m + 1) = x ^ n * y ^ m * y := by rw [pow_succ, mul_assoc]
      _ = z ^ (n * m) * y ^ m * (x ^ n * y) := by rw [ih]; group
      _ = z ^ (n * m) * y ^ m * (z ^ n * y * x ^ n) := by rw [pow_mul_eq_of_comm hzx hxy]
      _ = z ^ (n * m) * (y ^ m * z ^ n) * y * x ^ n := by group
      _ = z ^ (n * m) * (z ^ n * y ^ m) * y * x ^ n := by
        rw [((hzy.pow_left n).pow_right m).eq]
      _ = z ^ (n * (m + 1)) * y ^ (m + 1) * x ^ n := by
        rw [mul_add, mul_one, pow_add, pow_succ]; group

theorem commutatorElement_pow_mul_pow_of_comm (a b c d : ℕ) :
    ⁅x ^ a * y ^ c, x ^ b * y ^ d⁆ = (z ^ (b * c))⁻¹ * z ^ (a * d) := by
  have h1 : y ^ c * x ^ b = (z ^ (b * c))⁻¹ * (x ^ b * y ^ c) := by
    rw [pow_mul_pow_eq_of_comm hzx hzy hxy b c]; group
  have h2 : y ^ d * x ^ a = (z ^ (a * d))⁻¹ * (x ^ a * y ^ d) := by
    rw [pow_mul_pow_eq_of_comm hzx hzy hxy a d]; group
  have hzX : ∀ (k : ℕ) (w : E), (w = x ∨ w = y) → Commute (z ^ k) w := by
    rintro k w (rfl | rfl)
    · exact hzx.pow_left k
    · exact hzy.pow_left k
  have hgh : x ^ a * y ^ c * (x ^ b * y ^ d) =
      (z ^ (b * c))⁻¹ * (x ^ a * x ^ b * (y ^ c * y ^ d)) := by
    calc x ^ a * y ^ c * (x ^ b * y ^ d) = x ^ a * (y ^ c * x ^ b) * y ^ d := by group
      _ = x ^ a * ((z ^ (b * c))⁻¹ * (x ^ b * y ^ c)) * y ^ d := by rw [h1]
      _ = (x ^ a * (z ^ (b * c))⁻¹) * x ^ b * y ^ c * y ^ d := by group
      _ = ((z ^ (b * c))⁻¹ * x ^ a) * x ^ b * y ^ c * y ^ d := by
        rw [((hzX _ x (Or.inl rfl)).pow_right a).inv_left.eq]
      _ = _ := by group
  have hhg : x ^ b * y ^ d * (x ^ a * y ^ c) =
      (z ^ (a * d))⁻¹ * (x ^ a * x ^ b * (y ^ c * y ^ d)) := by
    calc x ^ b * y ^ d * (x ^ a * y ^ c) = x ^ b * (y ^ d * x ^ a) * y ^ c := by group
      _ = x ^ b * ((z ^ (a * d))⁻¹ * (x ^ a * y ^ d)) * y ^ c := by rw [h2]
      _ = (x ^ b * (z ^ (a * d))⁻¹) * x ^ a * y ^ d * y ^ c := by group
      _ = ((z ^ (a * d))⁻¹ * x ^ b) * x ^ a * y ^ d * y ^ c := by
        rw [((hzX _ x (Or.inl rfl)).pow_right b).inv_left.eq]
      _ = (z ^ (a * d))⁻¹ * (x ^ b * x ^ a * (y ^ d * y ^ c)) := by group
      _ = (z ^ (a * d))⁻¹ * (x ^ a * x ^ b * (y ^ c * y ^ d)) := by
        rw [(Commute.pow_pow_self x b a).eq, (Commute.pow_pow_self y d c).eq]
  have hcomm_def : ⁅x ^ a * y ^ c, x ^ b * y ^ d⁆ =
      (x ^ a * y ^ c * (x ^ b * y ^ d)) * (x ^ b * y ^ d * (x ^ a * y ^ c))⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hcomm_def, hgh, hhg, mul_inv_rev, inv_inv]
  group

end LocalClassTwo

section Kernel

variable [Finite E] [Group.IsPerfect E] {K : Type*} [Group K] {p : ℕ} [hp : Fact p.Prime]

theorem sylow_kernel_eq_bot_of_det (π : E →* K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (Q : Sylow p K) (hQ : IsElemAbelian p (Q : Subgroup K))
    (α : E ≃* E) (β : K ≃* K) (hαβ : ∀ e, π (α e) = β (π e)) (hαC : ∀ c ∈ π.ker, α c = c)
    {x y : K} (hgen : Subgroup.closure ({x, y} : Set K) = Q) {a b c d : ℕ}
    (hβx : β x = x ^ a * y ^ c) (hβy : β y = x ^ b * y ^ d)
    (hdet : ((a * d - b * c : ℤ) : ZMod p) ≠ 1) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ p Q
  have hmap : (P : Subgroup E).map π = (Q : Subgroup K) := by
    rw [← Sylow.coe_mapSurjective hπ P, hP]
  have hxQ : x ∈ (Q : Subgroup K) := hgen ▸ Subgroup.subset_closure (by simp)
  have hyQ : y ∈ (Q : Subgroup K) := hgen ▸ Subgroup.subset_closure (by simp)
  obtain ⟨x', hx'P, hx'⟩ := Subgroup.mem_map.1 (hmap.symm ▸ hxQ)
  obtain ⟨y', hy'P, hy'⟩ := Subgroup.mem_map.1 (hmap.symm ▸ hyQ)
  have hcen : ∀ e : E, π e = 1 → e ∈ Subgroup.center E := fun e he => hC he
  have hQcomm : ∀ u ∈ (Q : Subgroup K), ∀ v ∈ (Q : Subgroup K), u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hQ.1.1.1 ⟨u, hu⟩ ⟨v, hv⟩)
  set z : E := ⁅x', y'⁆ with hzdef
  have hzker : π z = 1 := by
    rw [hzdef, map_commutatorElement, hx', hy', commutatorElement_eq_one_iff_mul_comm]
    exact hQcomm x hxQ y hyQ
  have hzc := hcen z hzker
  have hzx : Commute z x' := (Subgroup.mem_center_iff.1 hzc x').symm
  have hzy : Commute z y' := (Subgroup.mem_center_iff.1 hzc y').symm
  have hxy : x' * y' = z * y' * x' := by rw [hzdef, commutatorElement_def]; group
  have hzp : z ^ p = 1 := by
    have h1 := pow_mul_eq_of_comm hzx hxy p
    have hxp : x' ^ p ∈ Subgroup.center E := hcen _ (by rw [map_pow, hx']; exact hQ.2 x hxQ)
    have h2 : x' ^ p * y' = y' * x' ^ p := (Subgroup.mem_center_iff.1 hxp y').symm
    rw [h2] at h1
    have h3 := congrArg (· * (y' * x' ^ p)⁻¹) h1
    simp only [mul_inv_cancel] at h3
    rw [show z ^ p * y' * x' ^ p * (y' * x' ^ p)⁻¹ = z ^ p by group] at h3
    exact h3.symm
  set u := (x' ^ a * y' ^ c)⁻¹ * α x' with hudef
  set v := (x' ^ b * y' ^ d)⁻¹ * α y' with hvdef
  have hu : u ∈ Subgroup.center E := hcen u (by
    rw [hudef, map_mul, map_inv, hαβ, hx', hβx, map_mul, map_pow, map_pow, hx', hy',
      inv_mul_cancel])
  have hv : v ∈ Subgroup.center E := hcen v (by
    rw [hvdef, map_mul, map_inv, hαβ, hy', hβy, map_mul, map_pow, map_pow, hx', hy',
      inv_mul_cancel])
  have hαx : α x' = x' ^ a * y' ^ c * u := by rw [hudef]; group
  have hαy : α y' = x' ^ b * y' ^ d * v := by rw [hvdef]; group
  have hαz : z = (z ^ (b * c))⁻¹ * z ^ (a * d) := by
    have h := hαC z hzker
    rw [hzdef, map_commutatorElement, hαx, hαy, commutatorElement_mul_central_left hu,
      commutatorElement_mul_central_right hv,
      commutatorElement_pow_mul_pow_of_comm hzx hzy hxy] at h
    exact h.symm
  have hz1 : z = 1 := by
    by_contra hz
    have hord : orderOf z = p :=
      (hp.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hzp)).resolve_left
        (fun h => hz (orderOf_eq_one_iff.1 h))
    have heq : z ^ (a * d) = z ^ (b * c + 1) := by
      rw [pow_succ]
      calc z ^ (a * d) = z ^ (b * c) * ((z ^ (b * c))⁻¹ * z ^ (a * d)) := by group
        _ = z ^ (b * c) * z := by rw [← hαz]
    rw [pow_eq_pow_iff_modEq, hord] at heq
    apply hdet
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 heq
    push_cast at this ⊢
    rw [this]
    ring
  have hQc : IsMulCommutative (Q : Subgroup K) := hQ.1
  let f : (P : Subgroup E) →* (Q : Subgroup K) :=
    (π.comp (P : Subgroup E).subtype).codRestrict (Q : Subgroup K) fun e =>
      hmap ▸ Subgroup.mem_map_of_mem π e.2
  have hfker : f.ker ≤ Subgroup.center (P : Subgroup E) := fun e he => by
    have he' : π e = 1 := congrArg Subtype.val he
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hC he') g)
  have hfgen : Subgroup.closure ({f ⟨x', hx'P⟩, f ⟨y', hy'P⟩} : Set (Q : Subgroup K)) = ⊤ := by
    have h := closure_preimage_eq_top hgen
    convert h using 2
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · left; exact hx'
      · right; exact hy'
    · rintro (h | h)
      · left; exact Subtype.ext (h.trans hx'.symm)
      · right; exact Subtype.ext (h.trans hy'.symm)
  have hPder := central_two_generator_derived_eq_zpowers f hfker ⟨x', hx'P⟩ ⟨y', hy'P⟩ hfgen
  have hzP : ⁅(⟨x', hx'P⟩ : ↥(P : Subgroup E)), (⟨y', hy'P⟩ : ↥(P : Subgroup E))⁆ = 1 :=
    Subtype.ext hz1
  rw [hzP, Subgroup.zpowers_one_eq_bot] at hPder
  have hle := central_kernel_sylow_restriction_le_derived π hC Cp P
  rw [hPder] at hle
  rw [eq_bot_iff]
  intro k hk
  have hkP : (k : E) ∈ (P : Subgroup E) := central_pSubgroup_le_sylow P
    ((Cp : Subgroup π.ker).map π.ker.subtype)
    ((Subgroup.map_subtype_le (Cp : Subgroup π.ker)).trans hC)
    (Cp.isPGroup'.map π.ker.subtype) (Subgroup.mem_map.2 ⟨k, hk, rfl⟩)
  have hker : (⟨(k : E), hkP⟩ : (P : Subgroup E)) ∈ (π.subgroupMap (P : Subgroup E)).ker :=
    Subtype.ext k.2
  have h1 := Subgroup.mem_bot.1 (hle hker)
  have h2 : (k : E) = 1 := congrArg Subtype.val h1
  exact Subgroup.mem_bot.2 (Subtype.ext h2)

theorem sylow_kernel_eq_bot_of_normalizer_det (π : E →* K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (Q : Sylow p K) (hQ : IsElemAbelian p (Q : Subgroup K))
    {x y : K} (hgen : Subgroup.closure ({x, y} : Set K) = Q) (h : K) {a b c d : ℕ}
    (hx : h * x * h⁻¹ = x ^ a * y ^ c) (hy : h * y * h⁻¹ = x ^ b * y ^ d)
    (hdet : ((a * d - b * c : ℤ) : ZMod p) ≠ 1) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨e, he⟩ := hπ h
  refine sylow_kernel_eq_bot_of_det π hπ hC Q hQ (MulAut.conj e) (MulAut.conj h) (fun g => ?_)
    (fun c hc => ?_) hgen ?_ ?_ hdet Cp
  · rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, he]
  · rw [MulAut.conj_apply, Subgroup.mem_center_iff.1 (hC hc) e]
    group
  · rw [MulAut.conj_apply, hx]
  · rw [MulAut.conj_apply, hy]

end Kernel

theorem commute_of_perfect_of_central_commutator {G : Type*} [Group G] (D : Subgroup G)
    [Group.IsPerfect D] (w : G) (hw : ∀ d ∈ D, ⁅w, d⁆ ∈ Subgroup.center G) :
    ∀ d ∈ D, Commute w d := by
  let φ : D →* Subgroup.center G :=
    { toFun := fun d => ⟨⁅w, (d : G)⁆, hw d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun d₁ d₂ => Subtype.ext (by
        change ⁅w, (d₁ : G) * d₂⁆ = ⁅w, (d₁ : G)⁆ * ⁅w, (d₂ : G)⁆
        have hc := Subgroup.mem_center_iff.1 (hw d₂ d₂.2)
        calc ⁅w, (d₁ : G) * d₂⁆ = w * d₁ * (w⁻¹ * ⁅w, (d₂ : G)⁆) * (d₁ : G)⁻¹ := by
              rw [commutatorElement_def, commutatorElement_def]; group
          _ = w * d₁ * w⁻¹ * (⁅w, (d₂ : G)⁆ * (d₁ : G)⁻¹) := by group
          _ = w * d₁ * w⁻¹ * ((d₁ : G)⁻¹ * ⁅w, (d₂ : G)⁆) := by rw [hc]
          _ = ⁅w, (d₁ : G)⁆ * ⁅w, (d₂ : G)⁆ := by rw [commutatorElement_def]; group) }
  have h1 : φ = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
  intro d hd
  have h2 : ⁅w, d⁆ = 1 := congrArg (fun f : D →* Subgroup.center G => (f ⟨d, hd⟩ : G)) h1
  exact commutatorElement_eq_one_iff_commute.1 h2

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem perfect_local_det_cover_rank {S : Type*} [Group S] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (K : Subgroup S) [Group.IsPerfect K] (Q : Sylow p K) (hQ : IsElemAbelian p (Q : Subgroup K))
    (hQcard : Nat.card (Q : Subgroup K) = p ^ 2)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ R : Sylow r K, IsCyclic (R : Subgroup K))
    (h : S) (hhK : h ∈ Subgroup.normalizer (K : Set S)) {x y : K}
    (hgen : Subgroup.closure ({x, y} : Set K) = Q) {a b c d : ℕ}
    (hx : h * x * h⁻¹ = (x : S) ^ a * (y : S) ^ c) (hy : h * y * h⁻¹ = (x : S) ^ b * (y : S) ^ d)
    (hdet : ((a * d - b * c : ℤ) : ZMod p) ≠ 1) (cc : S) (hcK : ∀ k ∈ K, Commute cc k)
    (hcc : orderOf cc = p) (hcK1 : Subgroup.zpowers cc ⊓ K = ⊥)
    {G : Type*} [Group G] [Finite G] (π : G →* S) (hπ : Function.Surjective π)
    (hA : π.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card π.ker)) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  classical
  set R : Subgroup G := K.comap π with hRdef
  set D : Subgroup G := perfectResidualOf R with hDdef
  have : Group.IsPerfect D := finite_perfectResidualOf_isPerfect R
  have hDK : ∀ e ∈ D, π e ∈ K := fun e he => by
    obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.1 he
    exact r.2
  let πD : D →* K := (π.comp D.subtype).codRestrict K fun e => hDK e e.2
  have hπD : ∀ e : D, (πD e : S) = π e := fun e => rfl
  have hπDsurj : Function.Surjective πD := by
    let ρ : R →* K := (π.comp R.subtype).codRestrict K fun r => r.2
    have hρ : Function.Surjective ρ := fun k => by
      obtain ⟨g, hg⟩ := hπ k
      exact ⟨⟨g, show π g ∈ K by rw [hg]; exact k.2⟩, Subtype.ext hg⟩
    have hmap := finite_perfectResidual_surjects_to_perfect_image ρ hρ
    intro k
    have hk : k ∈ (perfectResidual R).map ρ := hmap ▸ Subgroup.mem_top k
    obtain ⟨r, hr, hrk⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨r, Subgroup.mem_map.2 ⟨r, hr, rfl⟩⟩, Subtype.ext (congrArg Subtype.val hrk)⟩
  have hker_c : πD.ker ≤ Subgroup.center D := fun e he => by
    have he' : π e = 1 := congrArg Subtype.val he
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 (hA he') g)
  obtain ⟨g, hg⟩ := hπ h
  have hgD : g ∈ Subgroup.normalizer (D : Set G) :=
    normalizer_preimage_le_normalizer_perfectResidualOf π K
      (show π g ∈ Subgroup.normalizer (K : Set S) by rw [hg]; exact hhK)
  have hg1 : ∀ e ∈ D, g * e * g⁻¹ ∈ D := fun e he => (Subgroup.mem_normalizer_iff.1 hgD e).1 he
  have hg2 : ∀ e ∈ D, g⁻¹ * e * g ∈ D := fun e he =>
    (Subgroup.mem_normalizer_iff.1 hgD _).2 (by rw [show g * (g⁻¹ * e * g) * g⁻¹ = e by group]; exact he)
  have hh1 : ∀ k ∈ K, h * k * h⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.1 hhK k).1 hk
  have hh2 : ∀ k ∈ K, h⁻¹ * k * h ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 hhK _).2 (by rw [show h * (h⁻¹ * k * h) * h⁻¹ = k by group]; exact hk)
  let α : D ≃* D := conjRestrict D g hg1 hg2
  let β : K ≃* K := conjRestrict K h hh1 hh2
  have hαβ : ∀ e, πD (α e) = β (πD e) := fun e => Subtype.ext (by
    rw [hπD, conjRestrict_apply, conjRestrict_apply, hπD, map_mul, map_mul, map_inv, hg])
  have hαC : ∀ e ∈ πD.ker, α e = e := fun e he => Subtype.ext (by
    have he' : π e = 1 := congrArg Subtype.val he
    rw [conjRestrict_apply, Subgroup.mem_center_iff.1 (hA he') g]
    group)
  have hβx : β x = x ^ a * y ^ c := Subtype.ext (by
    rw [conjRestrict_apply, hx, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow])
  have hβy : β y = x ^ b * y ^ d := Subtype.ext (by
    rw [conjRestrict_apply, hy, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow])
  have hker : πD.ker = ⊥ := by
    by_contra hne
    have hnt : Nontrivial πD.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hkodd : Odd (Nat.card πD.ker) := by
      have hle : πD.ker.map D.subtype ≤ π.ker := by
        rintro _ ⟨e, he, rfl⟩
        exact congrArg Subtype.val he
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective D.subtype_injective] at hdvd
      exact Odd.of_dvd_nat hodd hdvd
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
    have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hkodd) (even_iff_two_dvd.2 hrd)
    obtain ⟨Cr⟩ := (inferInstance : Nonempty (Sylow r πD.ker))
    have hne' := Sylow.ne_bot_of_dvd_card Cr hrd
    by_cases hrp : r = p
    · subst hrp
      exact hne' (sylow_kernel_eq_bot_of_det πD hπDsurj hker_c Q hQ α β hαβ hαC hgen hβx hβy
        hdet Cr)
    · obtain ⟨Rr⟩ := (inferInstance : Nonempty (Sylow r K))
      exact hne' (central_cover_cyclic_sylow_kernel_eq_bot πD hπDsurj hker_c Cr Rr
        (hcyc r hr hr2 hrp Rr))
  have hinj : Function.Injective πD := (MonoidHom.ker_eq_bot_iff πD).1 hker
  obtain ⟨y₀, hy₀⟩ := hπ cc
  obtain ⟨k, n, hpn, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := G)).ne' p hp.out.ne_one
  set w := y₀ ^ n with hwdef
  have hw : w ^ (p ^ k) = 1 := by
    rw [hwdef, ← pow_mul, mul_comm, ← hcard, pow_card_eq_one']
  have hπw : π w = cc ^ n := by rw [hwdef, map_pow, hy₀]
  have hw1 : w ≠ 1 := fun h1 => by
    have h2 : cc ^ n = 1 := by rw [← hπw, h1, map_one]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hcc] at h3
    exact hpn h3
  have hpw : p ∣ orderOf w := by
    obtain ⟨j, -, hjw⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hw)
    rcases j with _ | j
    · rw [pow_zero] at hjw
      exact absurd (orderOf_eq_one_iff.1 hjw) hw1
    · rw [hjw]
      exact dvd_pow_self p (Nat.succ_ne_zero j)
  have hwD : ∀ e ∈ D, Commute w e := by
    refine commute_of_perfect_of_central_commutator D w fun e he => hA ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hπw, commutatorElement_eq_one_iff_commute]
    exact (hcK _ (hDK e he)).pow_left n
  have := Fintype.ofFinite (Subgroup.zpowers w)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.zpowers w) p (by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact hpw)
  set zv : G := (z : G) with hzv
  have hzvo : orderOf zv = p := by rw [hzv, Subgroup.orderOf_coe, hz]
  obtain ⟨m, hm⟩ := z.2
  have hzw : zv = w ^ m := hm.symm
  have hzD : ∀ e ∈ D, Commute zv e := fun e he => by rw [hzw]; exact (hwD e he).zpow_left m
  have hzint : Subgroup.zpowers zv ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨⟨i, rfl⟩, ht⟩
    have hπt : π (zv ^ i) ∈ Subgroup.zpowers cc ⊓ K := by
      refine ⟨?_, hDK _ ht⟩
      rw [hzw, map_zpow, map_zpow, hπw, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      exact Subgroup.zpow_mem_zpowers _ _
    rw [hcK1, Subgroup.mem_bot] at hπt
    have h1 : (⟨zv ^ i, ht⟩ : D) ∈ πD.ker := Subtype.ext hπt
    rw [hker, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  let eD : D ≃* K := MulEquiv.ofBijective πD ⟨hinj, hπDsurj⟩
  set Q₁ : Subgroup G := ((Q : Subgroup K).map eD.symm.toMonoidHom).map D.subtype with hQ₁
  have hQ₁D : Q₁ ≤ D := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hQ₁e : IsElemAbelian p Q₁ := isElemAbelian_map (isElemAbelian_map hQ _) _
  have hQ₁card : Nat.card Q₁ = p ^ 2 := by
    rw [hQ₁, Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.card_map_of_injective eD.symm.injective, hQcard]
  have hcomm : ∀ (q : Q₁) (t : Subgroup.zpowers zv),
      Commute (Q₁.subtype q) ((Subgroup.zpowers zv).subtype t) := by
    rintro q ⟨_, i, rfl⟩
    exact ((hzD q (hQ₁D q.2)).zpow_left i).symm
  let φ : Q₁ × Subgroup.zpowers zv →* G := MonoidHom.noncommCoprod _ _ hcomm
  have hφ : ∀ q t, φ (q, t) = (q : G) * t := fun q t => rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨q, t⟩ h1
    rw [MonoidHom.mem_ker, hφ] at h1
    have hq : (q : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : (t : G)⁻¹ ∈ Subgroup.zpowers zv ⊓ D :=
      ⟨Subgroup.inv_mem _ t.2, hq ▸ hQ₁D q.2⟩
    rw [hzint, Subgroup.mem_bot] at hmem
    have ht : (t : G) = 1 := inv_eq_one.1 hmem
    have hq1 : (q : G) = 1 := by rw [hq, ht, inv_one]
    exact Subgroup.mem_bot.2 (Prod.ext (Subtype.ext hq1) (Subtype.ext ht))
  have hQ₁comm := hQ₁e.1
  refine ⟨φ.range, ⟨⟨⟨fun u v => ?_⟩⟩, fun g hg => ?_⟩, ?_⟩
  · obtain ⟨⟨q₁, t₁⟩, h₁⟩ := MonoidHom.mem_range.1 u.2
    obtain ⟨⟨q₂, t₂⟩, h₂⟩ := MonoidHom.mem_range.1 v.2
    apply Subtype.ext
    change (u : G) * v = v * u
    rw [← h₁, ← h₂, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (mul_comm' q₁ q₂) ?_
    obtain ⟨i, hi⟩ := t₁.2
    obtain ⟨j, hj⟩ := t₂.2
    exact Subtype.ext (by
      rw [Prod.snd_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self zv i j).eq)
  · obtain ⟨⟨q, t⟩, rfl⟩ := MonoidHom.mem_range.1 hg
    have h1 : (q, t) ^ p = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [Prod.pow_fst, Subgroup.coe_pow, Prod.fst_one, Subgroup.coe_one]
        exact hQ₁e.2 _ q.2
      · rw [Prod.pow_snd, Subgroup.coe_pow, Prod.snd_one, Subgroup.coe_one]
        obtain ⟨i, hi⟩ := t.2
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzvo,
          pow_orderOf_eq_one, one_zpow]
    rw [← map_pow, h1, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, hQ₁card,
      Nat.card_zpowers, hzvo]
    ring

end CFSG.SectionRank
