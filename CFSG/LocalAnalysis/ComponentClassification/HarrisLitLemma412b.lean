module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem exists_mem_normalizer_not_mem {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P R : Subgroup G} (hR : IsPGroup p R) (hPR : P < R) :
    ∃ x ∈ R, x ∉ P ∧ x ∈ normalizer (P : Set G) := by
  have hIPlt : P.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => not_le_of_gt hPR fun x hx => ?_
    have : (⟨x, hx⟩ : ↥R) ∈ P.subgroupOf R := by rw [htop]; exact mem_top _
    exact this
  have := hR.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (P.subgroupOf R) hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot hx, ?_⟩
  have hxsub : x ∈ (normalizer (P : Set G)).subgroupOf R := by
    rw [subgroupOf_normalizer_eq hPR.le]
    exact hxN
  exact hxsub

theorem eq_of_forall_isConj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P R : Subgroup G} (hR : IsPGroup p R) (hPR : P ≤ R) {t : G}
    (hC : R ⊓ centralizer {t} ≤ P)
    (hconj : ∀ x ∈ R, x ∈ normalizer (P : Set G) → ∃ y ∈ P, y * t * y⁻¹ = x * t * x⁻¹) :
    P = R := by
  by_contra hne
  obtain ⟨x, hxR, hxP, hxN⟩ := exists_mem_normalizer_not_mem hR (lt_of_le_of_ne hPR hne)
  obtain ⟨y, hyP, hy⟩ := hconj x hxR hxN
  have h1 : y⁻¹ * x ∈ R ⊓ centralizer {t} := by
    refine ⟨R.mul_mem (R.inv_mem (hPR hyP)) hxR, mem_centralizer_singleton_iff.mpr ?_⟩
    calc y⁻¹ * x * t = y⁻¹ * (x * t * x⁻¹) * x := by group
      _ = y⁻¹ * (y * t * y⁻¹) * x := by rw [hy]
      _ = t * (y⁻¹ * x) := by group
  apply hxP
  have := P.mul_mem hyP (hC h1)
  rwa [mul_inv_cancel_left] at this

theorem mul_comm_of_mem_closure_pair {G : Type*} [Group G] {a b x y : G} (hab : a * b = b * a)
    (hx : x ∈ closure {a, b}) (hy : y ∈ closure {a, b}) : x * y = y * x := by
  have h1 : closure ({a, b} : Set G) ≤ centralizer ({a, b} : Set G) := by
    rw [closure_le]
    rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
      rintro h (rfl | rfl)
    · rfl
    · exact hab.symm
    · exact hab
    · rfl
  have h2 : closure ({a, b} : Set G) ≤ centralizer ({x} : Set G) := by
    rw [closure_le]
    intro g hg
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (h1 hx) g hg)
  exact (mem_centralizer_singleton_iff.mp (h2 hy)).symm

open CFSG.Semidihedral in
theorem sd_r_mul_s_ne {n : ℕ} (hn : 4 ≤ n) :
    r n * s n ≠ s n * r n := by
  have hn3 : 3 ≤ n := by omega
  rw [rotation_generator_eq_element n hn3, s_eq_element n hn3, element_rotation_mul,
    element_reflection_mul]
  intro h
  rw [element_eq_iff] at h
  apply twist_ne_one n hn
  have := h.1
  rw [zero_add, mul_one, add_zero] at this
  exact this.symm

theorem sd_isConj_of_involution {n : ℕ} (hn : 4 ≤ n) {g h : CFSG.Open.SemidihedralGroup n}
    (hg : orderOf g = 2) (hh : orderOf h = 2) (hgc : g ∉ center (CFSG.Open.SemidihedralGroup n))
    (hhc : h ∉ center (CFSG.Open.SemidihedralGroup n)) : IsConj g h := by
  rcases QuasiDihedralFusion.sd_involution_cases hn g hg with h1 | h1
  · exact absurd (h1 ▸ Semidihedral.z_mem_center n hn) hgc
  rcases QuasiDihedralFusion.sd_involution_cases hn h hh with h2 | h2
  · exact absurd (h2 ▸ Semidihedral.z_mem_center n hn) hhc
  exact h1.symm.trans h2

open DihedralGroup

theorem dihedral_exists_sr {m : ℕ} (hm : 1 ≤ m) {g : DihedralGroup (2 ^ m)} (hg : g ^ 2 = 1)
    (hgc : g ∉ center (DihedralGroup (2 ^ m))) : ∃ a, g = sr a := by
  rcases (dihedral_sq_eq_one_iff hm g).mp hg with rfl | rfl | h
  · exact absurd (one_mem _) hgc
  · exact absurd (r_mem_center_of_two_mul _
      ((zmod_two_mul_eq_zero_iff hm _).mpr (Or.inr rfl))) hgc
  · exact h

theorem dihedral_conj_sr {n : ℕ} {a b d : ZMod n} (h : b - a = 2 * d) :
    r (-d) * sr a * (r (-d))⁻¹ = sr b := by
  rw [r_mul_sr, inv_r, neg_neg, sr_mul_r]
  congr 1
  linear_combination -h

theorem dihedral_zpowers_r_eq {m : ℕ} {c : ZMod (2 ^ m)} (hc : c.val % 2 = 1) :
    zpowers (r c) = zpowers (r 1 : DihedralGroup (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hle : zpowers (r c) ≤ zpowers (r 1 : DihedralGroup (2 ^ m)) := by
    rw [zpowers_le]
    refine ⟨(c.val : ℤ), ?_⟩
    simp only [zpow_natCast, r_one_pow, ZMod.natCast_zmod_val]
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_r_one, orderOf_r c]
  have hcop : Nat.Coprime (2 ^ m) c.val :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hc))
  rw [hcop.gcd_eq_one, Nat.div_one]

theorem exists_conj_of_semidihedral {G : Type*} [Group G] {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (e : ↥P ≃* CFSG.Open.SemidihedralGroup n) {u v : G} (hu : u ∈ P) (hv : v ∈ P)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (huc : ∃ y ∈ P, y * u ≠ u * y)
    (hvc : ∃ y ∈ P, y * v ≠ v * y) : ∃ y ∈ P, y * u * y⁻¹ = v := by
  have hnc : ∀ {x : G} (hx : x ∈ P), (∃ y ∈ P, y * x ≠ x * y) →
      e ⟨x, hx⟩ ∉ center (CFSG.Open.SemidihedralGroup n) := by
    rintro x hx ⟨y, hy, hyx⟩ hc
    apply hyx
    have h1 := mem_center_iff.mp hc (e ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hord : ∀ {x : G} (hx : x ∈ P), orderOf x = 2 → orderOf (e ⟨x, hx⟩) = 2 := by
    intro x hx h2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h2]
  obtain ⟨c, hc⟩ := isConj_iff.mp (sd_isConj_of_involution hn (hord hu hu2) (hord hv hv2)
    (hnc hu huc) (hnc hv hvc))
  refine ⟨(e.symm c : G), (e.symm c).2, ?_⟩
  have h1 := congrArg e.symm hc
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  exact congrArg Subtype.val h1

theorem exists_conj_of_dihedral {G : Type*} [Group G] [Finite G] {P O : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) (e : ↥P ≃* DihedralGroup (2 ^ m)) (hOP : O ≤ P)
    (hidx : (O.subgroupOf P).index = 2) (hO : ¬ IsCyclic ↥O) {u v : G} (hu : u ∈ P)
    (hv : v ∈ P) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (huO : u ∉ O) (hvO : v ∉ O)
    (huc : ∃ y ∈ P, y * u ≠ u * y) (hvc : ∃ y ∈ P, y * v ≠ v * y) :
    ∃ y ∈ P, y * u * y⁻¹ = v := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hnc : ∀ {x : G} (hx : x ∈ P), (∃ y ∈ P, y * x ≠ x * y) →
      e ⟨x, hx⟩ ∉ center (DihedralGroup (2 ^ m)) := by
    rintro x hx ⟨y, hy, hyx⟩ hc
    apply hyx
    have h1 := mem_center_iff.mp hc (e ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hsq : ∀ {x : G} (hx : x ∈ P), x ^ 2 = 1 → e ⟨x, hx⟩ ^ 2 = 1 := by
    intro x hx h2
    rw [← map_pow, show (⟨x, hx⟩ : ↥P) ^ 2 = 1 from Subtype.ext (by simpa using h2), map_one]
  obtain ⟨a, ha⟩ := dihedral_exists_sr hm (hsq hu hu2) (hnc hu huc)
  obtain ⟨b, hb⟩ := dihedral_exists_sr hm (hsq hv hv2) (hnc hv hvc)
  have huv : (⟨u, hu⟩ : ↥P)⁻¹ * ⟨v, hv⟩ ∈ O.subgroupOf P := by
    rw [mul_mem_iff_of_index_two hidx, inv_mem_iff]
    exact iff_of_false huO hvO
  have he : e ((⟨u, hu⟩ : ↥P)⁻¹ * ⟨v, hv⟩) = r (b - a) := by
    rw [map_mul, map_inv, ha, hb, inv_sr, sr_mul_sr]
  by_cases hodd : (b - a).val % 2 = 1
  ·
    exfalso
    apply hO
    set O' := (O.subgroupOf P).map e.toMonoidHom with hO'
    have hle : zpowers (r 1 : DihedralGroup (2 ^ m)) ≤ O' := by
      rw [← dihedral_zpowers_r_eq hodd, zpowers_le, ← he]
      exact ⟨_, huv, rfl⟩
    have hcard : Nat.card O' = Nat.card (O.subgroupOf P) :=
      card_map_of_injective e.injective
    have hidx' : O'.index = 2 := by
      rw [hO', index_map_of_injective (f := e.toMonoidHom) (O.subgroupOf P) e.injective,
        MonoidHom.range_eq_top.mpr e.surjective, index_top, mul_one, hidx]
    have heq : zpowers (r 1 : DihedralGroup (2 ^ m)) = O' := by
      refine eq_of_le_of_card_ge hle ?_
      have h1 := O'.card_mul_index
      have h2 := (zpowers (r 1 : DihedralGroup (2 ^ m))).card_mul_index
      rw [hidx'] at h1
      rw [index_zpowers_r_one] at h2
      omega
    have hcyc : IsCyclic ↥O' := heq ▸ inferInstance
    have e₁ : ↥O ≃* ↥O' := (subgroupOfEquivOfLe hOP).symm.trans
      ((O.subgroupOf P).equivMapOfInjective e.toMonoidHom e.injective)
    exact isCyclic_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective
  ·
    have heven : (b - a).val % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, (b - a).val = 2 * k := ⟨(b - a).val / 2, by omega⟩
    have hd : b - a = 2 * (k : ZMod (2 ^ m)) := by
      rw [← ZMod.natCast_zmod_val (b - a), hk]
      push_cast
      ring
    refine ⟨(e.symm (r (-(k : ZMod (2 ^ m)))) : G), (e.symm _).2, ?_⟩
    have h1 := congrArg e.symm (dihedral_conj_sr hd)
    rw [map_mul, map_mul, map_inv, ← ha, ← hb, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply] at h1
    exact congrArg Subtype.val h1

end CFSG.ComponentClassification.HarrisLit
