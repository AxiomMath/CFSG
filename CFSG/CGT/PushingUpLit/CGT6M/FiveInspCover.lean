module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspL4
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLift
public import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.RankThree.PartOne.S11c.Sec68
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG CFSG.Open
open scoped commutatorElement

theorem isQuasisimple_of_open {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    CFSG.IsQuasisimple L := by
  refine ⟨⟨hq.1⟩, hq.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : commutator L ≤ Subgroup.center L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : QuotientGroup.mk' (Subgroup.center L) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (hcon _ _)
    have h2 : ⁅x, y⁆ ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_center_iff.mp h2 g
  have hcen : Subgroup.center L = ⊤ := by
    rw [eq_top_iff, ← hq.1]
    exact hle
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  apply hx
  rw [QuotientGroup.eq_one_iff, hcen]
  exact Subgroup.mem_top g

@[expose] def HeisInv (Q : Type*) [Group Q] (w : Q) : Prop :=
  ∃ X Y : Q, X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute ⁅Y, X⁆ X ∧ Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧
    w * X * w⁻¹ = X⁻¹

@[expose] def InvData (Q : Type*) [Group Q] (w : Q) : Prop :=
  (∃ Φ : C55 →* Q, Function.Injective Φ ∧ ∀ u : C55, w * Φ u * w⁻¹ = (Φ u)⁻¹) ∨ HeisInv Q w

theorem invData_of_equiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') {w : Q}
    (h : InvData Q' (e w)) : InvData Q w := by
  rcases h with ⟨Φ, hΦ, hinv⟩ | ⟨X, Y, hX5, hY5, hZX, hZY, hZ1, hinv⟩
  · refine Or.inl ⟨e.symm.toMonoidHom.comp Φ, e.symm.injective.comp hΦ, fun u => ?_⟩
    have := congrArg e.symm (hinv u)
    simpa using this
  · refine Or.inr ⟨e.symm X, e.symm Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_pow, hX5, map_one]
    · rw [← map_pow, hY5, map_one]
    · rw [← map_commutatorElement]
      exact hZX.map e.symm
    · rw [← map_commutatorElement]
      exact hZY.map e.symm
    · rw [← map_commutatorElement]
      intro h1
      exact hZ1 (e.symm.injective (h1.trans (map_one e.symm).symm))
    · have := congrArg e.symm hinv
      simpa using this

section Lift

variable {L Q : Type*} [Group L] [Finite L] [Group Q]

theorem commute_of_map_commute {ν : L →* Q} (hK : ν.ker ≤ Subgroup.center L)
    (hK5 : ¬ 5 ∣ Nat.card ν.ker) {a x : L} (hx : x ^ 5 = 1) (h : ν a * ν x = ν x * ν a) :
    a * x = x * a := by
  set c : L := a * x * a⁻¹ * x⁻¹ with hc
  have hcker : c ∈ ν.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcc : Commute c x := (Subgroup.mem_center_iff.mp (hK hcker) x).symm
  have h1 : a * x * a⁻¹ = c * x := by rw [hc]; group
  have h2 : (a * x * a⁻¹) ^ 5 = 1 := by rw [conj_pow, hx]; group
  have h3 : c ^ 5 = 1 := by
    have := h2
    rw [h1, hcc.mul_pow, hx, mul_one] at this
    exact this
  have h4 : c = 1 := eq_one_of_pow_eq_one_of_mem_ker Nat.prime_five hK5 hcker h3
  rw [h4, one_mul] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem heisInv_lift {ν : L →* Q} (hν : Function.Surjective ν) (hK : ν.ker ≤ Subgroup.center L)
    (hK5 : ¬ 5 ∣ Nat.card ν.ker) {z : L} (h : HeisInv Q (ν z)) : HeisInv L z := by
  obtain ⟨X, Y, hX5, hY5, hZX, hZY, hZ1, hinv⟩ := h
  obtain ⟨x, hxν, hx5⟩ := exists_lift_of_pow_eq_one hν Nat.prime_five hK5 hX5
  obtain ⟨y, hyν, hy5⟩ := exists_lift_of_pow_eq_one hν Nat.prime_five hK5 hY5
  have hZν : ν ⁅y, x⁆ = ⁅Y, X⁆ := by rw [map_commutatorElement, hxν, hyν]
  refine ⟨x, y, hx5, hy5, ?_, ?_, ?_, ?_⟩
  · refine commute_of_map_commute hK hK5 hx5 ?_
    rw [hZν, hxν]
    exact hZX.eq
  · refine commute_of_map_commute hK hK5 hy5 ?_
    rw [hZν, hyν]
    exact hZY.eq
  · intro h1
    rw [h1, map_one] at hZν
    exact hZ1 hZν.symm
  · refine eq_of_map_eq_of_pow_eq_one hK Nat.prime_five hK5 ?_ ?_ ?_
    · rw [conj_pow, hx5]
      group
    · rw [inv_pow, hx5, inv_one]
    · rw [map_mul, map_mul, map_inv, map_inv, hxν]
      exact hinv

theorem invData_lift {ν : L →* Q} (hν : Function.Surjective ν) (hK : ν.ker ≤ Subgroup.center L)
    (hK5 : ¬ 5 ∣ Nat.card ν.ker) {z : L} (hz2 : z * z = 1) (h : InvData Q (ν z)) :
    InvData L z :=
  h.elim (fun ⟨_, hΦ, hinv⟩ => Or.inl (exists_inverted_c55_of_cover hν hK hK5 hΦ hz2 hinv))
    (fun hh => Or.inr (heisInv_lift hν hK hK5 hh))

end Lift

@[expose] def CoverInv (Q : Type) [Group Q] : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    Odd (Nat.card (Subgroup.center L)) → Nonempty (L ⧸ Subgroup.center L ≃* Q) →
      ∀ z : L, z ≠ 1 → z * z = 1 → InvData L z

theorem not_mem_center_of_involution {L : Type*} [Group L] [Finite L]
    (hodd : Odd (Nat.card (Subgroup.center L))) {z : L} (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    z ∉ Subgroup.center L := by
  intro hz
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
  have h2 : orderOf z ∣ Nat.card (Subgroup.center L) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center L)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf z ∣ 1 := by
    have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center L)) :=
      (Nat.coprime_two_left).mpr hodd
    exact hcop ▸ Nat.dvd_gcd h1 h2
  exact hz1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

theorem coverInv_of_data {Q : Type} [Group Q]
    (hQ : ∀ w : Q, w ≠ 1 → w * w = 1 → InvData Q w)
    (h5 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
      Odd (Nat.card (Subgroup.center L)) → Nonempty (L ⧸ Subgroup.center L ≃* Q) →
        ¬ 5 ∣ Nat.card (Subgroup.center L)) : CoverInv Q := by
  intro L _ _ hq hodd he z hz1 hz2
  obtain ⟨e⟩ := he
  let ν : L →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hνs : Function.Surjective ν := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hνk : ν.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' (Subgroup.center L) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hzc := not_mem_center_of_involution hodd hz1 hz2
  have hνz : ν z ≠ 1 := by
    intro h
    apply hzc
    rw [← hνk, MonoidHom.mem_ker]
    exact h
  have hνz2 : ν z * ν z = 1 := by rw [← map_mul, hz2, map_one]
  refine invData_lift hνs hνk.le ?_ hz2 (hQ _ hνz hνz2)
  rw [hνk]
  exact h5 L hq hodd ⟨e⟩

theorem five_not_dvd_center_psl4 (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 5 1) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  intro h5
  have hmod' : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 5 1 :=
    hmod
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod'
  rcases CFSG.RankThree.PartOne.prime_dvd_table Nat.prime_five (by norm_num) (h5.trans hd) with
    ⟨-, h, -⟩ | ⟨ht, -, -⟩
  · norm_num at h
  · exact absurd ht (by decide)

theorem coverInv_psl4 (hGA : CFSG.Open.GriessAllModelsStatement) (Q : Type) [Group Q]
    (hQ : StatedClassicalModel Q .PSL 4 5 1) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hQ
  have hK5 : Nat.card K = 5 := by simpa using hKc
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    obtain ⟨Φ, hΦ, hinv⟩ := psl4_five_inverts hK5 (e w) hew1 hew2
    refine Or.inl ⟨e.symm.toMonoidHom.comp Φ, e.symm.injective.comp hΦ, fun u => ?_⟩
    have := congrArg e.symm (hinv u)
    simpa using this
  · have hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 5 1 :=
      ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e⟩⟩
    exact five_not_dvd_center_psl4 hGA (isQuasisimple_of_open hq) hmod

end CFSG.CGT.PushingUpLit.CGT6M
