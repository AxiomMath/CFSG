module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

structure QFixedRootDatum (D : Type) [Group D] (n : ℕ) (α : MulAut D) (J : Subgroup D) : Prop where
  orderOf_eq : orderOf α = 2
  le_fixed : J ≤ α.toMonoidHom.eqLocus (MonoidHom.id D)
  normal : (J.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal
  quasisimple : CFSG.Open.IsQuasisimple ↥J
  model : LieModel (↥J ⧸ center ↥J) .PSU 3 2 n
  rankOne : FixedRootRankOne α J

@[expose] def QFixedRootSelector (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D →
    ∀ (n : ℕ) (α : MulAut D) (J : Subgroup D), QFixedRootDatum D n α J → center J = ⊥

theorem center_eq_bot_of_mulEquiv_aux {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center A = ⊥) : center B = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  have hz : e.symm b ∈ center A := by
    rw [mem_center_iff] at hb ⊢
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hb (e x)
  rw [h, mem_bot] at hz
  rw [mem_bot]
  simpa using congrArg e hz

theorem isQuasisimple_open_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native B).mpr
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native A).mp h))

theorem lieModel_quotient_center_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ}
    (h : LieModel (A ⧸ center A) t m p f) : LieModel (B ⧸ center B) t m p f :=
  LieModel.of_mulEquiv (QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)) h

namespace QFixedRootDatum

variable {D : Type} [Group D] {n : ℕ} {α : MulAut D} {J : Subgroup D}

theorem two_le (d : QFixedRootDatum D n α J) : 2 ≤ n :=
  two_le_of_lieModel_PSU3 d.model

theorem nonabelian (d : QFixedRootDatum D n α J) : ∃ a b : J, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hZ : center J = ⊤ := eq_top_iff.2 fun x _ => mem_center_iff.2 fun g => hcon g x
  have h1 := d.quasisimple.2.toNontrivial
  have h2 : Subsingleton (J ⧸ center J) := by
    rw [hZ]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton _) h2

theorem nonabelian_ambient (d : QFixedRootDatum D n α J) : ∃ a b : D, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := d.nonabelian
  exact ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem isComponent (d : QFixedRootDatum D n α J) :
    CFSG.IsComponent (J.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) := by
  have hq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp d.quasisimple
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe d.le_fixed).symm hq,
    d.normal.isSubnormal⟩

theorem card_quotient_center_dvd (d : QFixedRootDatum D n α J) :
    Nat.card (J ⧸ center J) ∣ Nat.card J :=
  Subgroup.card_quotient_dvd_card (center J)

theorem two_pow_dvd_card (d : QFixedRootDatum D n α J) : 2 ^ (3 * n) ∣ Nat.card J := by
  have hd := Nat.ordProj_dvd (Nat.card (J ⧸ center J)) 2
  rw [factorization_two_card_of_lieModel_PSU3 d.model] at hd
  exact hd.trans d.card_quotient_center_dvd

theorem card_quotient_dvd_card_fixed (d : QFixedRootDatum D n α J) :
    Nat.card (J ⧸ center J) ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) :=
  d.card_quotient_center_dvd.trans (Subgroup.card_dvd_of_le d.le_fixed)

theorem toFixedRootDatumOf (d : QFixedRootDatum D n α J) (hZ : center J = ⊥) :
    FixedRootDatumOf T_U3 D n α J := by
  refine ⟨d.orderOf_eq, d.le_fixed, d.normal, ⟨d.two_le, ?_⟩, d.rankOne⟩
  exact LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) d.model

end QFixedRootDatum

end CFSG.LocalAnalysis.EvenBN.GMSK
