module

public import CFSG.GH74.Uniqueness.Section123

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Reduction

theorem A2.exists_conj_commute_t (S : ZDSetup X Z M) (c : Ctx12 Z M) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) : ∃ d ∈ c.D, (d⁻¹ * u * d) * c.t = c.t * (d⁻¹ * u * d) := by
  classical
  have hZ := S.invariant
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx, -⟩ := S.prodDisc.prop36d hZ c.ht c.htM c.hz c.hzM
  have hodd : Odd ((centralizer ({c.t} : Set X)).relIndex c.D) := hidx ▸ S.odd_zNum
  have huu : u * u = 1 := mul_self_of_orderOf_eq_two hu2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  let H : Subgroup ↥c.D := (centralizer ({c.t} : Set X)).subgroupOf c.D
  have : Fintype (↥c.D ⧸ H) := Fintype.ofFinite _
  let u' : ↥c.D := ⟨u, hu⟩
  let σ : Equiv.Perm (↥c.D ⧸ H) := MulAction.toPermHom ↥c.D (↥c.D ⧸ H) u'
  have hσ : σ ^ 2 ^ 1 = 1 := by
    have hu'2 : u' ^ 2 = 1 := Subtype.ext (by simp [u', pow_two, huu])
    change (MulAction.toPermHom ↥c.D (↥c.D ⧸ H) u') ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, hu'2, map_one]
  have hnd : ¬ 2 ∣ Fintype.card (↥c.D ⧸ H) := by
    rw [← Nat.card_eq_fintype_card]
    intro hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : u' • (QuotientGroup.mk d : ↥c.D ⧸ H) = QuotientGroup.mk d := hq
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hq'
  have hmem : (((u' * d)⁻¹ * d : ↥c.D) : X) ∈ centralizer ({c.t} : Set X) := hq'
  have e : (((u' * d)⁻¹ * d : ↥c.D) : X) = (d : X)⁻¹ * u * d := by
    change ((u : X) * d)⁻¹ * d = (d : X)⁻¹ * u * d
    rw [mul_inv_rev, hui]
  rw [e, mem_centralizer_singleton_iff] at hmem
  exact ⟨d, d.2, hmem⟩

theorem A2.not_centralizer_le (S : ZDSetup X Z M) (c : Ctx12 Z M) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) : ¬ centralizer ({u} : Set X) ≤ M := by
  obtain ⟨d, hd, hdu⟩ := A2.exists_conj_commute_t S c hu hu2
  have hdM : d ∈ M := (mem_inf.mp hd).1
  intro hle
  apply c.htM
  have hmem : d * c.t * d⁻¹ ∈ centralizer ({u} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc d * c.t * d⁻¹ * u = d * (c.t * (d⁻¹ * u * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * u * d) * c.t) * d⁻¹ := by rw [hdu]
      _ = u * (d * c.t * d⁻¹) := by group
  have h1 := hle hmem
  have e : c.t = d⁻¹ * (d * c.t * d⁻¹) * d := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hdM) h1) hdM

end Reduction

section Counting

theorem A2.mzero_comm {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {x y : X}
    (hx : x ∈ zHull Z M) (hy : y ∈ zHull Z M) : x * y = y * x := by
  have h1 := h.m_abelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h1

omit [Finite X] in
theorem A2.odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, hk⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact ⟨k - 1, by omega⟩

theorem A2.inter_centralizer_eq {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) (u : X) :
    Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X) =
      ((centralizer ({u} : Set X) ⊓ zHull Z M : Subgroup X) : Set X) \ {1} := by
  have hzM : Z ∩ (M : Set X) = (zHull Z M : Set X) \ {1} := h.zM_eq
  ext x
  constructor
  · rintro ⟨hxZ, hxCM⟩
    obtain ⟨hxC, hxM⟩ := mem_inf.mp hxCM
    have hx : x ∈ (zHull Z M : Set X) \ {1} := by
      rw [← hzM]
      exact ⟨hxZ, hxM⟩
    exact ⟨mem_inf.mpr ⟨hxC, hx.1⟩, hx.2⟩
  · rintro ⟨hxCM, hx1⟩
    obtain ⟨hxC, hxM⟩ := mem_inf.mp hxCM
    have hx : x ∈ Z ∩ (M : Set X) := by
      rw [hzM]
      exact ⟨hxM, hx1⟩
    exact ⟨hx.1, mem_inf.mpr ⟨hxC, hx.2⟩⟩

theorem A2.ncard_inter_centralizer {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) (u : X) :
    (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = qU Z M u - 1 := by
  rw [A2.inter_centralizer_eq h u, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _),
    ← Nat.card_coe_set_eq]
  rfl

theorem A2.odd_ncard_inter_centralizer (S : ZDSetup X Z M) {u : X} (huM : u ∈ M)
    (hu2 : orderOf u = 2) :
    Odd (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard := by
  classical
  have : Fintype ↥(Z ∩ (M : Set X)) := Fintype.ofFinite _
  have huu : u * u = 1 := mul_self_of_orderOf_eq_two hu2
  have hσ : (Cor714.permHom S.invariant M ⟨u, huM⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have h1 : (⟨u, huM⟩ : M) ^ 2 = 1 := Subtype.ext (by simp [pow_two, huu])
    rw [h1, map_one]
  have h2 := Equiv.Perm.two_dvd_card_support hσ
  have hfix : Function.fixedPoints (Cor714.permHom S.invariant M ⟨u, huM⟩) =
      (((Cor714.permHom S.invariant M ⟨u, huM⟩).supportᶜ : Finset _) : Set _) := by
    ext x
    simp [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.Perm.mem_support]
  rw [← Cor714.ncard_fixedPoints_permHom S.invariant huM, hfix, Set.ncard_coe_finset,
    Finset.card_compl]
  have hm : Odd (Fintype.card ↥(Z ∩ (M : Set X))) := by
    rw [← Nat.card_eq_fintype_card]
    exact S.odd_zNum
  have hle : (Cor714.permHom S.invariant M ⟨u, huM⟩).support.card ≤
      Fintype.card ↥(Z ∩ (M : Set X)) := Finset.card_le_univ _
  obtain ⟨k, hk⟩ := h2
  obtain ⟨j, hj⟩ := hm
  exact ⟨j - k, by omega⟩

theorem A2.three_le_ncard_inter_centralizer
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ}
    (h : LData c n i) {u : X} (huM : u ∈ M) (hu2 : orderOf u = 2) :
    3 ≤ (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard := by
  have hodd := A2.odd_ncard_inter_centralizer S huM hu2
  have hne1 : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard ≠ 1 := by
    intro h1
    have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
    have hf₂ : (Z ∩ ((centralizer ({c.z} : Set X) ⊓ M : Subgroup X) : Set X)).ncard =
        2 ^ n - 1 := by
      rw [← A2.ncard_zM h]
      congr 1
      ext x
      constructor
      · rintro ⟨hxZ, hxCM⟩
        exact ⟨hxZ, (mem_inf.mp hxCM).2⟩
      · rintro ⟨hxZ, hxM⟩
        refine ⟨hxZ, mem_inf.mpr ⟨?_, hxM⟩⟩
        rw [mem_centralizer_singleton_iff]
        exact A2.mzero_comm h (subset_closure ⟨hxZ, hxM⟩) (subset_closure ⟨c.hz, c.hzM⟩)
    exact S.cor714_false_of_parity hu2 hz2 huM c.hzM h1 h.hn hf₂
  obtain ⟨k, hk⟩ := hodd
  omega

theorem A2.four_le_qU
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {u : X}
    (huM : u ∈ M) (hu2 : orderOf u = 2) : 4 ≤ qU Z M u := by
  have h1 := A2.three_le_ncard_inter_centralizer S h huM hu2
  rw [A2.ncard_inter_centralizer h u] at h1
  omega

end Counting

section Structure

omit [Finite X] in
theorem A2.ne_one_of_orderOf_eq_two {u : X} (hu2 : orderOf u = 2) : u ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hu2
  exact absurd hu2 (by norm_num)

omit [Finite X] in
theorem A2.inter_cenHull_eq (u : X) :
    Z ∩ ((cenHull Z u ⊓ M : Subgroup X) : Set X) =
      Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨hxZ, hxLM⟩
    obtain ⟨hxL, hxM⟩ := mem_inf.mp hxLM
    exact ⟨hxZ, mem_inf.mpr ⟨Cor713.zHull_le _ hxL, hxM⟩⟩
  · rintro ⟨hxZ, hxCM⟩
    obtain ⟨hxC, hxM⟩ := mem_inf.mp hxCM
    exact ⟨hxZ, mem_inf.mpr ⟨subset_closure ⟨hxZ, hxC⟩, hxM⟩⟩

theorem A2.not_solvable_cenHull
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i)
    {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) :
    ¬ Group.IsSolvable ↥(zHull Z (centralizer ({u} : Set X))) := by
  have huM : u ∈ M := (mem_inf.mp hu).1
  have h3 := A2.three_le_ncard_inter_centralizer S h huM hu2
  have h1 : 1 < (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).ncard := by omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
  exact S.not_solvable_zHull_of_ne (A2.centralizer_ne_top S (A2.ne_one_of_orderOf_eq_two hu2))
    (A2.not_centralizer_le S c hu hu2) ha hb hab

theorem A2.benderSub_cenHull
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i)
    {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) :
    ∃ m j e : ℕ, 2 ≤ m ∧ qU Z M u = 2 ^ m ∧ BenderSub Z M (cenHull Z u) m j e := by
  have huM : u ∈ M := (mem_inf.mp hu).1
  have h3 := A2.three_le_ncard_inter_centralizer S h huM hu2
  have hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨m, j, e, hB⟩ := S.benderSub_exists
    (A2.centralizer_ne_top S (A2.ne_one_of_orderOf_eq_two hu2)) (A2.not_centralizer_le S c hu hu2)
    hne (A2.not_solvable_cenHull S h hu hu2)
  have hB : BenderSub Z M (cenHull Z u) m j e := hB
  have h1 := A2.ncard_inter_of_benderSub S hB
  rw [A2.inter_cenHull_eq u, A2.ncard_inter_centralizer h u] at h1
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h4 := A2.four_le_qU S h huM hu2
  exact ⟨m, j, e, hB.bender.two_le.2, by omega, hB⟩

theorem A2.delta_conj
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {u : X}
    {m j e : ℕ} (hB : BenderSub Z M (cenHull Z u) m j e) :
    ∀ x ∈ deltaSet Z M u, ∀ y ∈ deltaSet Z M u, x ≠ u → y ≠ u →
      ∃ g ∈ M ⊓ cenHull Z u, g⁻¹ * x * g = y := by
  intro x hx y hy hxu hyu
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hmem : ∀ w ∈ centralizer ({u} : Set X) ⊓ zHull Z M, w * u ≠ u →
      w ∈ Z ∩ ((cenHull Z u ⊓ M : Subgroup X) : Set X) := by
    intro w hw hwu
    have hw1 : w ≠ 1 := by
      rintro rfl
      exact hwu (one_mul u)
    rw [A2.inter_cenHull_eq u, A2.inter_centralizer_eq h u]
    exact ⟨hw, hw1⟩
  obtain ⟨g, hg, hgab⟩ := A2.exists_conj_of_benderSub S hB (hmem a ha hxu) (hmem b hb hyu)
  refine ⟨g, hg, ?_⟩
  have hgC : g ∈ centralizer ({u} : Set X) := Cor713.zHull_le _ (mem_inf.mp hg).2
  have hgu' : g * u = u * g := mem_centralizer_singleton_iff.mp hgC
  have hgu : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [hgu']
      _ = u := by group
  calc g⁻¹ * (a * u) * g = (g⁻¹ * a * g) * (g⁻¹ * u * g) := by group
    _ = b * u := by rw [hgab, hgu]

theorem A2.centralizer_eq_mul
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i)
    {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) :
    ((centralizer ({u} : Set X) : Subgroup X) : Set X) =
      (cenHull Z u : Set X) * ((centralizer ({u} : Set X) ⊓ c.D : Subgroup X) : Set X) := by
  have huM : u ∈ M := (mem_inf.mp hu).1
  have hut : u ∈ conjugate M c.t := (mem_inf.mp hu).2
  have h3 := A2.three_le_ncard_inter_centralizer S h huM hu2
  have hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨-, hsol | hbend⟩ := S.corollary713 (centralizer ({u} : Set X))
    (A2.centralizer_ne_top S (A2.ne_one_of_orderOf_eq_two hu2)) (A2.not_centralizer_le S c hu hu2)
    hne
  · exact absurd hsol.1 (A2.not_solvable_cenHull S h hu hu2)
  obtain ⟨-, -, -, hfr⟩ := hbend
  have hβ : conjugate M c.t ∈ alphaOrbit M (centralizer ({u} : Set X)) := by
    obtain ⟨g, hg, hgβ⟩ := S.exists_centralizer_conj hu2 (self_mem_omega M) ⟨c.t, rfl⟩
      ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr huM)
      ((S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr hut)
    exact ⟨g, hg, hgβ⟩
  have hβM : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  rw [hfr _ hβ hβM, inf_assoc]

end Structure

end CFSG.GH74.Uniqueness
