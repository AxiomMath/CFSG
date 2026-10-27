module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma41
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedral

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem map_subtype_center {G : Type*} [Group G] (D : Subgroup G) :
    (center ↥D).map D.subtype = D ⊓ centralizer (D : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    have := (mem_center_iff.mp hy) ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxD, hxc⟩
    refine ⟨⟨x, hxD⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.mp hxc) g g.2

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

@[expose] def rhoD (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : ↥(S ⊓ L) →* MulAut (Bar L) :=
  h.rho.comp (Subgroup.inclusion (inf_le_left.trans hS.le))

theorem rhoD_injective [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : Function.Injective (h.rhoD hS) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  exact Subtype.ext (h.eq_one_of_mem_zpowers_of_mem (h.mem_zpowers_of_rho_eq_one hS d.2.1 hd)
    d.2.2)

theorem range_rhoD [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    (h.rhoD hS).range =
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
  rw [h.map_rho_inf_innAut hS, rhoD, MonoidHom.range_comp, Subgroup.inclusion_range]

@[expose] def equivD [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    ↥(S ⊓ L) ≃* ↥((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) :=
  (MonoidHom.ofInjective (h.rhoD_injective hS)).trans
    (MulEquiv.subgroupCongr (h.range_rhoD hS))

theorem exists_dihedral [Finite X] (h : Standing t L p f) {S : Subgroup X}
    {hS : IsSylowOf 2 S (centralizer ({t} : Set X))} {w : X} (hL : Lift h hS w) :
    ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hL.data.dihedral
  exact ⟨m, hm, ⟨(h.equivD hS).trans e⟩⟩

end Standing

section DihedralSubgroup

variable {D : Subgroup X} {m : ℕ}

theorem exists_center_eq_zpowers (e : ↥D ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) :
    ∃ z ∈ D, orderOf z = 2 ∧ D ⊓ centralizer (D : Set X) = zpowers z := by
  set z' : ↥D := e.symm (DihedralGroup.r ((2 ^ m / 2 : ℕ) : ZMod (2 ^ m)))
  refine ⟨z', z'.2, ?_, ?_⟩
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hk : 2 ^ m / 2 = 2 ^ (m - 1) := by
      rw [show m = m - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos, Nat.add_sub_cancel]
    have hdvd : 2 ^ m / 2 ∣ orderOf (DihedralGroup.r (1 : ZMod (2 ^ m))) := by
      rw [DihedralGroup.orderOf_r_one, hk]
      exact pow_dvd_pow 2 (Nat.sub_le m 1)
    have hk0 : 2 ^ m / 2 ≠ 0 := by
      rw [hk]
      positivity
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← DihedralGroup.r_one_pow,
      orderOf_pow_of_dvd hk0 hdvd, DihedralGroup.orderOf_r_one, hk,
      Nat.pow_div (Nat.sub_le m 1) two_pos, show m - (m - 1) = 1 by omega, pow_one]
  · rw [← map_subtype_center, dihedral_center_eq e hm, MonoidHom.map_zpowers]
    rfl


theorem eq_one_or_eq_of_mem_zpowers {z x : X} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    rw [zpow_mul, show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2, one_zpow, one_mul,
      zpow_one]

theorem normal_le_zpowers (e : ↥D ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) {z : X}
    (hz : D ⊓ centralizer (D : Set X) = zpowers z) {N : Subgroup X} (hND : N ≤ D)
    (hN : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (h2 : ∀ n ∈ N, n ^ 2 = 1) : N ≤ zpowers z := by
  have hNn : (N.subgroupOf D).Normal :=
    ⟨fun n hn d => hN d d.2 n hn⟩
  have h1 := dihedral_normal_le_center' e hm (N.subgroupOf D) (fun x hx => Subtype.ext (by
    simpa using h2 _ hx))
  intro x hx
  rw [← hz, ← map_subtype_center]
  exact ⟨⟨x, hND hx⟩, h1 hx, rfl⟩

theorem mem_of_normal_ne_bot [Finite X] (e : ↥D ≃* DihedralGroup (2 ^ m)) {z : X}
    (hz2 : orderOf z = 2) (hz : D ⊓ centralizer (D : Set X) = zpowers z) {N : Subgroup X}
    (hND : N ≤ D) (hN : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hne : N ≠ ⊥) : z ∈ N := by
  have hp : IsPGroup 2 ↥D := IsPGroup.of_card (n := m + 1) (by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm])
  have : Group.IsNilpotent ↥D := hp.isNilpotent
  have hNn : (N.subgroupOf D).Normal := ⟨fun n hn d => hN d d.2 n hn⟩
  have hne' : N.subgroupOf D ≠ ⊥ := by
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hND hx⟩ : ↥D) ∈ N.subgroupOf D := hx
    rw [hb, mem_bot] at this
    exact congrArg Subtype.val this
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨x, hxN, hxc⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have hxz : (x : X) ∈ zpowers z := by
    rw [← hz, ← map_subtype_center]
    exact ⟨x, hxc, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hz2 hxz with h | h
  · exact absurd (Subtype.ext (Subtype.ext (by simpa using h))) hx1
  · rw [← h]
    exact hxN

theorem mem_zpowers_of_comm_le (e : ↥D ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) {z : X}
    (hz : D ⊓ centralizer (D : Set X) = zpowers z) {d : X} (hdD : d ∈ D) (hd2 : d ^ 2 = 1)
    (h : ∀ d' ∈ D, d⁻¹ * d'⁻¹ * d * d' ∈ zpowers z) : d ∈ zpowers z := by
  have hc : ∀ x : X, x ∈ zpowers z → ∀ hx : x ∈ D, (⟨x, hx⟩ : ↥D) ∈ center ↥D := by
    intro x hx hxD
    rw [← hz, ← map_subtype_center] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hxD⟩ := Subtype.ext hyx
    rwa [← this]
  have h1 := dihedral_involution_mem_center' e hm ⟨d, hdD⟩
    (Subtype.ext (by rw [Subgroup.coe_pow, hd2, Subgroup.coe_one]))
    (fun g => hc _ (h g g.2) _)
  rw [← hz, ← map_subtype_center]
  exact ⟨_, h1, rfl⟩

end DihedralSubgroup

end CFSG.ComponentClassification.HarrisLit
