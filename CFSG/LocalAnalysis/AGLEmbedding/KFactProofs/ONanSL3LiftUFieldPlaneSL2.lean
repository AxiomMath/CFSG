module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.Dihedral.Glauberman.DicksonMaxList
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open scoped MatrixGroups commutatorElement
open CFSG.BenderSuzuki.MatrixGroups

section Arith

private theorem not_dvd_of_dvd_pow_sub_one {p n r : ℕ} (hp : 0 < p) (hn : n ≠ 0) (hr : r.Prime)
    (h : r ∣ p ^ n - 1) : ¬ r ∣ p := by
  intro hrp
  have h1 : r ∣ p ^ n := dvd_pow hrp hn
  have h2 : p ^ n - 1 + 1 = p ^ n := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)
  have h3 : r ∣ 1 := (Nat.dvd_add_right h).1 (by rw [h2]; exact h1)
  exact hr.one_lt.ne' (Nat.dvd_one.1 h3)

private theorem dvd_pow_sub_one_of_prime {p r : ℕ} (hr : r.Prime) (hrp : ¬ r ∣ p) :
    r ∣ p ^ (r - 1) - 1 := by
  have hcop : Nat.Coprime p r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hrp).symm
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hr] at h
  have hpos : 1 ≤ p ^ (r - 1) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => hrp (h0 ▸ dvd_zero r))
  exact (Nat.modEq_iff_dvd' hpos).1 h.symm

private theorem two_mul_le_sub_one {p f r : ℕ} (hr : r.Prime) (hrp : ¬ r ∣ p)
    (hrk : ∀ k, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) : 2 * f ≤ r - 1 := by
  by_contra hlt
  exact hrk (r - 1) (by have := hr.two_le; omega) (by omega) (dvd_pow_sub_one_of_prime hr hrp)

private theorem not_dvd_sixty {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r) : ¬ r ∣ 60 := by
  intro h
  have h60 := Nat.le_of_dvd (by norm_num) h
  interval_cases r <;> first | omega | exact absurd hr (by decide)

end Arith

section Central

variable {G : Type*} [Group G]

private theorem commutatorElement_mul_central_left {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.1 hz
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [← hz' b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_central_right {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.1 hz
  simp only [commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [← hz' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem eq_top_of_sup_center_eq_top [Group.IsPerfect G] {H : Subgroup G}
    (h : H ⊔ Subgroup.center G = ⊤) : H = ⊤ := by
  rw [eq_top_iff]
  have hc : (commutator G : Subgroup G) ≤ H := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h ▸ Subgroup.mem_top g₁)
    obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h ▸ Subgroup.mem_top g₂)
    rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hz']
    exact H.mul_mem (H.mul_mem (H.mul_mem hy hy') (H.inv_mem hy)) (H.inv_mem hy')
  rw [Group.IsPerfect.commutator_eq_top] at hc
  exact hc

end Central

section SL

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem eq_top_of_primitive_prime (hF : Nat.card F = p ^ f)
    (hf : 3 ≤ f) {r : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ (2 * f) - 1)
    (hrk : ∀ k, 0 < k → k < 2 * f → ¬ r ∣ p ^ k - 1) (H : Subgroup SL(2, F))
    (hH : ¬ Group.IsSolvable H) {x : SL(2, F)} (hx : x ∈ H) (hxr : orderOf x = r) :
    H = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have hf0 : f ≠ 0 := by omega
  have hrp : ¬ r ∣ p := not_dvd_of_dvd_pow_sub_one hp.pos (by omega) hr hrq
  have hr7 : 7 ≤ r := by
    have := two_mul_le_sub_one hr hrp hrk
    omega
  let π : SL(2, F) →* PSL2MatrixGroup F := QuotientGroup.mk' (Subgroup.center SL(2, F))
  have hxz : x ∉ Subgroup.center SL(2, F) := by
    intro hxz
    obtain ⟨c, hc, hcx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxz
    have hx2 : x ^ 2 = 1 := by
      rw [Fintype.card_fin] at hc
      ext1
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hcx, ← map_pow, hc, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hr2 : r ∣ 2 := hxr ▸ orderOf_dvd_of_pow_eq_one hx2
    have := Nat.le_of_dvd (by norm_num) hr2
    omega
  have hπx : orderOf (π x) = r := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hxr, pow_orderOf_eq_one, map_one]
    · intro h1
      exact hxz ((QuotientGroup.eq_one_iff x).1 h1)
  let Hb : Subgroup (PSL2MatrixGroup F) := H.map π
  have hrHb : r ∣ Nat.card Hb :=
    hπx ▸ Subgroup.orderOf_dvd_natCard Hb (Subgroup.mem_map_of_mem π hx)
  have hns : ¬ Group.IsSolvable ↥Hb := by
    intro hs
    apply hH
    let g : ↥H →* ↥Hb := π.subgroupMap H
    have hker : ∀ a b : g.ker, a * b = b * a := by
      intro a b
      have hz : ((b : H) : SL(2, F)) ∈ Subgroup.center SL(2, F) := by
        have hb := b.2
        rw [MonoidHom.mem_ker] at hb
        exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hb)
      exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.1 hz _)))
    have : Group.IsSolvable g.ker := Group.isSolvable_of_comm hker
    exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  have htop : Hb = ⊤ := by
    rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF Hb with
      ⟨m, -, hmc, -⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, htq, E, C, hE, -, hEcard, -, hCcard, hdisj, hsup, -, -, -, -⟩ |
      ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
    · exfalso
      rw [hmc] at hrHb
      exact hrp (hr.dvd_of_dvd_pow hrHb)
    · exfalso
      exact hns (Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup (α := ↥Hb)).mul_comm a b)
    · exfalso
      have : NeZero z := ⟨by omega⟩
      have := CFSG.LinearGroups.isSolvable_dihedralGroup z
      exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exfalso
      have : Group.IsSolvable (alternatingGroup (Fin 4)) :=
        alternatingGroup.isSolvable (by simp)
      exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exfalso
      have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
      exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exfalso
      have hc : Nat.card Hb = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      exact not_dvd_sixty hr hr7 (hc ▸ hrHb)
    · exfalso
      have hcomp : E.IsComplement' C := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
      have hcardHb : Nat.card Hb = p ^ m * t := by
        rw [← hEcard, ← hCcard, hcomp.card_mul_card]
      rcases (Nat.Prime.dvd_mul hr).1 (hcardHb ▸ hrHb) with h | h
      · exact hrp (hr.dvd_of_dvd_pow h)
      · have htq' : t ∣ p ^ f - 1 := htq.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
        exact hrk f (by omega) (by omega) (h.trans htq')
    · have hm0 : m ≠ 0 := by
        rintro rfl
        exact hf0 (zero_dvd_iff.1 hmf)
      have hcardGal : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
      have hcardHb : Nat.card Hb = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_congr e.toEquiv
      have hdvd : Nat.card Hb ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [hcardHb]
        refine (Subgroup.card_quotient_dvd_card (Subgroup.center SL(2, GaloisField p m))).trans ?_
        rw [CFSG.GorensteinWalter.sl2_card_formula, hcardGal]
      have hr2 : r ∣ (p ^ m) ^ 2 - 1 := by
        rcases (Nat.Prime.dvd_mul hr).1 (hrHb.trans hdvd) with h | h
        · exact absurd (hr.dvd_of_dvd_pow h) hrp
        · exact h
      rw [← pow_mul, mul_comm m 2] at hr2
      have hfm : f ≤ m := by
        by_contra hlt
        exact hrk (2 * m) (by omega) (by omega) hr2
      have hmf' : m = f := le_antisymm (Nat.le_of_dvd (by omega) hmf) hfm
      refine Subgroup.eq_top_of_card_eq Hb ?_
      rw [hcardHb]
      let : Fintype F := Fintype.ofFinite F
      let : Fintype (GaloisField p m) := Fintype.ofFinite _
      refine Nat.card_congr
        (CFSG.Glauberman.Dickson.h826_pslEquiv (FiniteField.ringEquivOfCardEq ?_)).toEquiv
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hcardGal, hmf']
    · exfalso
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hf0 (zero_dvd_iff.1 (by simpa using hmf))
      have hcardGal : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
      have hcardHb : Nat.card Hb = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, hcardGal]
      have hr2 : r ∣ (p ^ m) ^ 2 - 1 := by
        rcases (Nat.Prime.dvd_mul hr).1 (hcardHb ▸ hrHb) with h | h
        · exact absurd (hr.dvd_of_dvd_pow h) hrp
        · exact h
      rw [← pow_mul, mul_comm m 2] at hr2
      have hfm : f ≤ m := by
        by_contra hlt
        exact hrk (2 * m) (by omega) (by omega) hr2
      have := Nat.le_of_dvd (by omega) hmf
      omega
  have hsup : H ⊔ Subgroup.center SL(2, F) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨h, hh, hhg⟩ : π g ∈ Hb := htop ▸ Subgroup.mem_top _
    have hmem : h⁻¹ * g ∈ Subgroup.center SL(2, F) := QuotientGroup.eq.1 hhg
    have hg : g = h * (h⁻¹ * g) := by group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hmem)
  have : Group.IsPerfect SL(2, F) := by
    refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
    let : Fintype F := Fintype.ofFinite F
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  exact eq_top_of_sup_center_eq_top hsup

end SL

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
