module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem psiL_surjective (h : IvSetting m p M D L) : Function.Surjective (psiL h) := by
  intro z
  have hz : (z : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
      (L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) := z.2
  obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 hz
  have hmt : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m : Mt M) ∈ tl M L :=
    Subgroup.mem_map.2 ⟨m, hm, rfl⟩
  refine ⟨⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmt⟩, Subtype.ext ?_⟩
  rw [← hmz]
  rfl

theorem psiL_comp_toTl (h : IvSetting m p M D L) :
    (psiL h).comp (toTl M L h.hL.1) = barMap p h.hL.1 := by
  refine MonoidHom.ext fun ℓ => ?_
  apply Subtype.ext
  rfl

theorem ker_psiL_le_center (h : IvSetting m p M D L) :
    ∀ x ∈ (psiL h).ker, x ∈ Subgroup.center ↥(tl M L) := by
  have hcomm : ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ = ⊥ :=
    commutator_tl_L_glaPPrimeCore_eq_bot (prime_of_standing h.standing) h.hyp h.hL h.hn h.hnc h.hQ
  intro x hx
  have hx1 : projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)
      (x : Mt M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have hx' : (x : Mt M) ∈ (L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := x.2
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx'
  have hmQ : m ∈ GLAPPrimeCore p ↥M := by
    rw [← hmx] at hx1
    exact (QuotientGroup.eq_one_iff m).1 hx1
  have hxQ : (x : Mt M) ∈ tl M (GLAPPrimeCoreOf p M) := by
    rw [← hmx]
    exact Subgroup.mem_map.2
      ⟨m, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, hmQ, rfl⟩), rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hmem' : ⁅(g : Mt M), (x : Mt M)⁆ ∈ ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ :=
    Subgroup.commutator_mem_commutator g.2 hxQ
  rw [hcomm, Subgroup.mem_bot] at hmem'
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem'

theorem ker_comp_center_eq (h : IvSetting m p M D L) :
    ((QuotientGroup.mk' (Subgroup.center ↥(barX p M L))).comp (psiL h)).ker =
      Subgroup.center ↥(tl M L) := by
  have hp : p.Prime := prime_of_standing h.standing
  have hperf : commutator ↥(tl M L) = ⊤ :=
    (isComponentOf_tl hp (ne_two_of_standing h.standing) h.hyp h.hL h.hn h.hnc h.hQ).2.2.1
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact mem_center_of_image_mem_center hperf (ker_psiL_le_center h) hx
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := psiL_surjective h g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]

@[expose] noncomputable def psiHat (h : IvSetting m p M D L) :
    (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃*
      (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_comp_center_eq h)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (psiL_surjective h)))

theorem psiL_bijective_of_center_eq_bot (h : IvSetting m p M D L)
    (hZ : Subgroup.center ↥(tl M L) = ⊥) : Function.Bijective (psiL h) :=
  ⟨(injective_iff_map_eq_one (psiL h)).2 fun x hx => by
    have := ker_psiL_le_center h x hx
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this, psiL_surjective h⟩

theorem chev_psiL_bijective {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (hZ : Subgroup.center ↥(StatedOmega Q) = ⊥) (h : IvSetting m p M D L)
    (e : ↥(tl M L) ≃* ↥(StatedOmega Q)) : Function.Bijective (psiL h) := by
  refine psiL_bijective_of_center_eq_bot h ?_
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hx' : e x ∈ Subgroup.center ↥(StatedOmega Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [hZ, Subgroup.mem_bot] at hx'
  exact e.injective (hx'.trans (map_one e).symm)

theorem not_tl_gammaD_le_centralizer (h : IvSetting m p M D L) :
    ¬ tl M (gammaD D) ≤ Subgroup.centralizer (↑(tl M L) : Set (Mt M)) := by
  intro hle
  apply h.hnc
  intro g hg
  rw [← map_projQ_tl h (gammaD D)] at hg
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  have hℓ' : ℓ ∈ (tl M L).map
      (projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)) := by
    rw [map_projQ_tl h L]
    exact hℓ
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hℓ'
  have hst : s * t = t * s := Subgroup.mem_centralizer_iff.1 (hle ht) s hs
  rw [← map_mul, ← map_mul, hst]

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
