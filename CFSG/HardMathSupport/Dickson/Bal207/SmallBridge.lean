module

public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Small

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271

section Bridge

variable {X : Type} [Group X]

noncomputable def barMap (p : ℕ) {C J : Subgroup X} (hJC : J ≤ C) : ↥J →* ↥(barX p C J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hJC)).codRestrict
    (barX p C J) fun j => ⟨Subgroup.inclusion hJC j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩

theorem barMap_surjective (p : ℕ) {C J : Subgroup X} (hJC : J ≤ C) :
    Function.Surjective (barMap p hJC) := by
  rintro ⟨y, c, hc, rfl⟩
  exact ⟨⟨(c : X), Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩

theorem barX_centralQuotient {p : ℕ} [Finite X] {C J : Subgroup X} (hJ : GLAPComponent p C J)
    (hT : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J)) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J))) ∧
      Nat.card (Subgroup.center ↥(barX p C J)) ∣ Nat.card (Subgroup.center ↥J) := by
  have hJC : J ≤ C := hJ.1
  have hperf : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)).1
  have hq : CFSG.Open.IsQuasisimple ↥J := ⟨hperf, hT⟩
  have hq' : CFSG.Open.IsQuasisimple ↥(barX p C J) := hJ.2.2.1.2.2
  have hker : (barMap p hJC).ker ≤ Subgroup.center ↥J := by
    rcases i253_normal_le_center_or_top hq (barMap p hJC).ker with h | h
    · exact h
    · exfalso
      haveI : Nontrivial (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J)) := hq'.2.toNontrivial
      obtain ⟨u, v, huv⟩ := exists_pair_ne (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J))
      obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨ju, rfl⟩ := barMap_surjective p hJC u'
      obtain ⟨jv, rfl⟩ := barMap_surjective p hJC v'
      have h1 : barMap p hJC ju = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : barMap p hJC jv = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      exact huv (by rw [h1, h2])
  exact ⟨LieComp.nonempty_centralQuotient_mulEquiv hperf (barMap p hJC)
      (barMap_surjective p hJC) hker,
    LieComp.card_center_dvd_of_surjective hperf (barMap p hJC) (barMap_surjective p hJC) hker⟩

end Bridge

section Data

variable {X : Type} [Group X] [Finite X]

theorem le_centralizer_of_mem {p : ℕ} {B : Subgroup X} (hB : IsSCp p ⊤ B) {a : X} (haB : a ∈ B) :
    B ≤ Subgroup.centralizer ({a} : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hc := hB.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨h, haB⟩
  have := congrArg Subtype.val hc
  exact this.symm

theorem compHyp_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C J B : Subgroup X}
    (hJ : GLAPComponent p C J) (hBC : B ≤ C) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hB : IsSCp p ⊤ B) : CompHyp p (barX p C J) (barX p C B) := by
  obtain ⟨h1, h2, h3, h4⟩ := recursionData hp hJ hBC hBJ hB
  exact ⟨hp, hp2, h1, h2, h3, h4⟩

theorem small_data {G : ∀ (S : Type) [Group S], MulAut S → Prop} {p : ℕ} {K B A J : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A) {a : X} (haA : a ∈ A)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) :
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({a} : Set X)) ∧
      GLAPComponent p (Subgroup.centralizer ({a} : Set X)) J ∧
      CompHyp p (barX p (Subgroup.centralizer ({a} : Set X)) J)
        (barX p (Subgroup.centralizer ({a} : Set X)) B) := by
  have hJC : GLAPComponent p (Subgroup.centralizer ({a} : Set X)) J :=
    glaPComponent_centralizer ctx.prime ctx.comp.2.1 hJ
  exact ⟨Glue.isSubnormal_centralizer_of_glaPComponent a ctx.comp.2.1 hJ, hJC,
    compHyp_bar ctx.prime ctx.odd hJC (le_centralizer_of_mem ctx.scp (ctx.le haA)) hBJ ctx.scp⟩

end Data

end CFSG.HardMathSupport.Dickson.Bal207.Small

end
