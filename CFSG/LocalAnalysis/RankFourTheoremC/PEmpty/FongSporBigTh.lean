module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQGF2InvolutionCentralizer
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup CFSG.Open

theorem card_mul_le_of_normalizing_extraspecial {G : Type*} [Group G] [Finite G] {Q E S : Subgroup G}
    {w e m : ℕ} (hQ : IsExtraspecialPGroup 2 Q) (hQcard : Nat.card Q = 2 ^ (1 + 2 * w))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : IsPGroup 2 E)
    (hEQ : E ≤ normalizer (Q : Set G)) (hQS : Q ≤ S) (hES : E ≤ S)
    (hSc : Nat.card S = 2 ^ e * m) (hm : Odd m) :
    Nat.card E * 2 ^ (1 + 2 * w) ≤ 2 ^ e * 2 ^ (w + 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf (A := Q) (B := E) hEQ
  have hinf : Nat.card ↥(Q ⊓ E) ≤ 2 ^ (w + 1) := by
    have h := CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.HigherCenter.card_le_of_commute_extraspecial
      hQ hQcard (A := (Q ⊓ E).subgroupOf Q) (fun a ha b hb => by
        have ha' := (mem_inf.1 (mem_subgroupOf.1 ha)).2
        have hb' := (mem_inf.1 (mem_subgroupOf.1 hb)).2
        exact Subtype.ext (hEc _ ha' _ hb'))
    rwa [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : Q ⊓ E ≤ Q)).toEquiv] at h
  obtain ⟨a, ha⟩ := hE2.exists_card_eq
  have hTdvd : Nat.card ↥(Q ⊔ E) ∣ 2  ^ (1 + 2 * w + a) := by
    refine ⟨Nat.card ↥(Q ⊓ E), ?_⟩
    rw [pow_add, ← hQcard, ← ha, ← hprod]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hTdvd
  have hTS : Nat.card ↥(Q ⊔ E) ∣ Nat.card S := Subgroup.card_dvd_of_le (sup_le hQS hES)
  have hbe : b ≤ e := by
    rw [hb, hSc] at hTS
    have hcop : Nat.Coprime (2 ^ b) m := Nat.Coprime.pow_left b (Nat.coprime_two_left.2 hm)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hTS)
  calc Nat.card E * 2 ^ (1 + 2 * w) = Nat.card ↥(Q ⊔ E) * Nat.card ↥(Q ⊓ E) := by
        rw [hprod, hQcard, mul_comm]
    _ ≤ 2 ^ e * 2 ^ (w + 1) := by
        rw [hb]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hbe) hinf

theorem card_mul_le_of_elemAbelian_of_centralizer {G : Type} [Group G] [Finite G] {a : G}
    {Q M : Subgroup G} {w e m : ℕ} (hconj : ∀ u : G, orderOf u = 2 → IsConj a u)
    (hcent : centralizer ({a} : Set G) ≤ M) (hQ : IsExtraspecialPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (1 + 2 * w)) (hQM : Q ≤ M) (hMQ : M ≤ normalizer (Q : Set G))
    (hMc : Nat.card M = 2 ^ e * m) (hm : Odd m) (hwe : w ≤ e) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : Nat.card E * 2 ^ (1 + 2 * w) ≤ 2 ^ e * 2 ^ (w + 1) := by
  by_cases hE1 : ∀ x ∈ E, x = 1
  · rw [(Subgroup.eq_bot_iff_forall E).2 hE1, Subgroup.card_bot, one_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  push Not at hE1
  obtain ⟨u, huE, hu1⟩ := hE1
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hE.2 u huE) hu1
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj u hu2)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE' : IsElemAbelian 2 (E.map (MulAut.conj g⁻¹).toMonoidHom) := hE.map _
  have hcard : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine hcent ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyu : y * (g * a * g⁻¹) = (g * a * g⁻¹) * y := by rw [hg]; exact hEc y hy u huE
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (g⁻¹ * y * g) * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hyu]
      _ = a * (g⁻¹ * y * g) := by group
  have hEc' : ∀ x ∈ E.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g⁻¹).toMonoidHom,
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h := card_mul_le_of_normalizing_extraspecial (Q := Q) (S := M) hQ hQcard hEc' hE'.isPGroup
    (hle.trans hMQ) hQM hle hMc hm
  rwa [hcard] at h

theorem not_commute_of_centralizer_le {G : Type*} [Group G] {a : G} {M : Subgroup G} {p : ℕ}
    (hconj : ∀ u : G, orderOf u = 2 → IsConj a u) (hcent : centralizer ({a} : Set G) ≤ M)
    (hp : ¬ p ∣ Nat.card M) (t z : G) (ht : orderOf t = 2) (hz : orderOf z = p) :
    t * z ≠ z * t := by
  intro htz
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj t ht)
  have hw : g⁻¹ * z * g ∈ M := by
    refine hcent ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hg] at htz
    calc (g⁻¹ * z * g) * a = g⁻¹ * (z * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * z) * g := by rw [htz]
      _ = a * (g⁻¹ * z * g) := by group
  have hord : orderOf (g⁻¹ * z * g) = p := by
    rw [← hz]
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
  apply hp
  rw [← hord, ← Subgroup.orderOf_mk _ hw]
  exact orderOf_dvd_natCard _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
