module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Gen
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Fit

variable {G : Type} [Group G] [Finite G]

theorem Fpi_le_Fpi_of_normal {σ : Set ℕ} (hσ : ∀ q ∈ σ, q.Prime) {K N : Subgroup G} (hKN : K ≤ N)
    (hn : N ≤ normalizer (K : Set G)) : Fpi σ K ≤ Fpi σ N := by
  refine iSup₂_le fun q hq => ?_
  rw [Op_Fm_eq (hσ q hq) K]
  have hnormOp : N ≤ normalizer ((Op q K : Subgroup G) : Set G) := by
    intro n hn'
    refine mem_normalizer_of_cj_eq ?_
    unfold cj
    rw [← Op_map q (MulAut.conj n)]
    have : K.map (MulAut.conj n).toMonoidHom = K := cj_eq_of_mem_normalizer (hn hn')
    rw [this]
  have hle : Op q K ≤ Op q N :=
    le_Op_of_normal ((Op_le q K).trans hKN) hnormOp (isPGroup_Op q (hσ q hq) K)
  rw [← Op_Fm_eq (hσ q hq) N] at hle
  exact hle.trans (le_iSup₂_of_le q hq le_rfl)

omit [Finite G] in
theorem prime_of_mem_piF {M : Subgroup G} {q : ℕ} (hq : q ∈ piF M) : q.Prime := hq.1

omit [Finite G] in
theorem prime_of_mem_piF' {M : Subgroup G} {q : ℕ} (hq : q ∈ piF' M) : q.Prime := hq.1

theorem bender_apply (hB12 : Bender12) (hkps : IsKProperSimple G) {M N Y : Subgroup G}
    (hMc : IsCoatom M) (hnq : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Fs M)) (hY : Y ≤ Fm M)
    (hN : Fs M ⊓ normalizer (Y : Set G) ≤ N) :
    Fpi (piF' M) N ⊓ M = ⊥ ∧ Fpi (piF M) N ≤ M := by
  obtain ⟨ha, hb, -⟩ := hB12 G hkps M N hMc Y hY hN
  exact ⟨ha, hb.resolve_left hnq⟩

end Fit

section Ctx

structure S5Facts {G : Type} [Group G] [Finite G] (z : G) (M : Subgroup G) (p : ℕ)
    (E : Subgroup G) : Prop where
  hMz : M = centralizer {z}
  hMc : IsCoatom M
  hkps : IsKProperSimple G
  hz2 : orderOf z = 2
  hzF : z ∈ Fm M
  hVF : Vof M E ≤ Fm M
  hEV : E ≤ Vof M E
  h2pi : 2 ∈ piF M
  hppi : p ∈ piF M
  hnq : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Fs M)

variable {G : Type} [Group G] [Finite G]

theorem S5Facts.of_ctx (h171 : Prop17_1) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) : S5Facts z M p E := by
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hMz : M = centralizer {z} := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hz2 : orderOf z = 2 := hS2.orderOf_z
  have hp : p.Prime := hctx.prime
  have hzM : z ∈ M := hMz ▸ Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hz2g : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hzOp : zpowers z ≤ Op 2 M := by
    refine le_Op_of_normal (Subgroup.zpowers_le.2 hzM) ?_ hz2g
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hmc : m ∈ centralizer ({z} : Set G) := hMz ▸ hm
    have hc : m * z = z * m := Subgroup.mem_centralizer_singleton_iff.1 hmc
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have : m * z ^ n * m⁻¹ = z ^ n := by
        have hcomm : Commute m z := hc
        rw [(hcomm.zpow_right n).eq]
        group
      rw [this]
      exact Subgroup.zpow_mem_zpowers z n
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hcomm : Commute m z := hc
      have hx' : x = z ^ n := by
        calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
          _ = m⁻¹ * z ^ n * m := by rw [← hn]
          _ = z ^ n := by
            rw [((hcomm.zpow_right n).inv_left).eq]
            group
      rw [hx']
      exact Subgroup.zpow_mem_zpowers z n
  have hzF : z ∈ Fm M := (Op_le_Fm 2 Nat.prime_two M) (hzOp (Subgroup.mem_zpowers z))
  have htF : t ∈ Fm M := (Op_le_Fm p hp M) (hctx.t_mem)
  have hVF : Vof M E ≤ Fm M := inf_le_left
  have hEV : E ≤ Vof M E := by
    refine le_inf (hctx.E_le.trans (Op_le_Fm p hp M)) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := congrArg Subtype.val
      ((hctx.E_elem.toIsMulCommutative.is_comm).comm (⟨g, hg⟩ : ↥E) ⟨e, he⟩)
    exact this
  have h2pi : 2 ∈ piF M := by
    refine ⟨Nat.prime_two, ?_⟩
    have := orderOf_dvd_natCard (⟨z, hzF⟩ : ↥(Fm M))
    rwa [Subgroup.orderOf_mk, hz2] at this
  have hppi : p ∈ piF M := by
    refine ⟨hp, ?_⟩
    have := orderOf_dvd_natCard (⟨t, htF⟩ : ↥(Fm M))
    rwa [Subgroup.orderOf_mk, hctx.t_ord] at this
  have hnq : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Fs M) := by
    rintro ⟨q, hq, hQ⟩
    have : Fact q.Prime := ⟨hq⟩
    have hFs : Fm M ≤ Fs M := by
      rw [Fs_eq_sup]
      exact le_sup_left
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨z, hFs hzF⟩
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨t, hFs htF⟩
    rw [Subgroup.orderOf_mk, hz2] at ha
    rw [Subgroup.orderOf_mk, hctx.t_ord] at hb
    have hq2 : q = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).1 ha.symm).1
    subst hq2
    have := ((Nat.Prime.pow_eq_iff hp).1 hb.symm).1
    exact hctx.odd this.symm
  exact ⟨hMz, hctx.base.ctx.mem.1, hctx.base.ctx.ctx.std.kps, hz2, hzF, hVF, hEV, h2pi, hppi, hnq⟩

end Ctx

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
