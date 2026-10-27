module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11b
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Aux11

variable {G : Type} [Group G]

theorem pLayerOf_le_self' (p : ℕ) (X : Subgroup G) : pLayerOf p X ≤ X := sSup_le fun _ hL => hL.1

theorem mem_normalizer_centralizer_singleton {c t : G} (hc : c * t = t * c) :
    c ∈ normalizer ((centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  have h1 : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) :=
    le_antisymm (centralizer_zpowers_le t) (cen_le_centralizer_zpowers t)
  have h2 := normalizer_le_normalizer_centralizer (zpowers t) (mem_normalizer_zpowers_of_comm hc)
  rwa [h1] at h2

theorem mem_of_map_conj_eq {M : Subgroup G} (hs : IsSimpleGroup G) (hM : IsCoatom M) (hM1 : M ≠ ⊥) {g : G}
    (h : M.map (MulAut.conj g⁻¹).toMonoidHom = M) : g ∈ M := by
  have hg : g ∈ normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx : g * x * g⁻¹ ∈ M ↔ x ∈ M := by
      have := mem_map_conj_iff M g⁻¹ x
      rw [h, inv_inv] at this
      exact this.symm
    exact hx.symm
  rcases hM.le_iff.mp (Subgroup.le_normalizer (H := M)) with htop | heq
  · have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hb | ht
    · exact absurd hb hM1
    · exact absurd ht hM.1
  · rw [heq] at hg
    exact hg

end Aux11

section Prop111

variable {G : Type} [Group G] [Finite G]

theorem prop_11_1 (h104 : Prop10_4) (hstar : Lemma11_1_star) : Prop11_1 := by
  intro G _ _ z k S M p Q T U t g ctx hT
  have hp := ctx.ctx9.prime
  have hp2 := ctx.ctx9.odd
  by_cases hone : TypeOneCase G k
  ·
    have hTS : T = S := ctx.T_eq_S hone
    have hSC : S ≤ centralizer (U : Set G) := hTS ▸ hT
    have htS : t ∈ S := ctx.choice.U_le ctx.t_mem_U
    have hcen : ∀ s ∈ S, s * t = t * s := fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (hSC hs) t ctx.t_mem_U).symm
    have hord : orderOf t = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact ctx.t_mul_t) ctx.t_ne_one
    exact ctx.t_ne_z (ctx.ctx9.ctx.data.base.zcen t htS hcen hord)
  ·
    obtain ⟨hTdef, -, -, -, hzCt⟩ := ctx.choice.T_two hone
    have hzN : z ∈ normalizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (ctx.M_le_normalizer_Q ctx.ctx9.z_mem)
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr ctx.z_comm_t))
    have hBp : IsPGroup p ↥(Q ⊓ centralizer ({t} : Set G)) := ctx.Q_pgroup.to_le inf_le_left
    have hstar' : ¬ Q ⊓ centralizer ({t} : Set G) ≤ Cen z :=
      hstar G p hp hp2 z t Q ctx.ctx9.z_mul_z ctx.t_mul_t ctx.z_comm_t ctx.Q_pgroup
        (fun c hc => ctx.M_le_normalizer_Q (ctx.ctx9.cen_le hc)) hzCt ctx.not_Q_le_Cen
    have hRne : ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ ≠ ⊥ := fun hb =>
      hstar' (commutator_zpowers_eq_bot_iff.mp hb)
    have hRB : ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ ≤ Q ⊓ centralizer ({t} : Set G) :=
      commutator_le_of_normalizes (Subgroup.zpowers_le.mpr hzN)
    have hRQ : ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ ≤ Q := hRB.trans inf_le_left
    have hRCt : ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ ≤ centralizer ({t} : Set G) := hRB.trans inf_le_right
    have hRp : IsPGroup p ↥(⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆) := ctx.Q_pgroup.to_le hRQ
    have hRM : ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ ≤ M :=
      hRQ.trans (ctx.Q_le_P.trans (Op_le' p M))
    have hRR : ⁅⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆, zpowers z⁆ =
        ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ :=
      commutator_zpowers_idem ctx.ctx9.orderOf_z hp hp2 hBp hzN
    set R : Subgroup G := ⁅Q ⊓ centralizer ({t} : Set G), zpowers z⁆ with hRdef
    have hNormR : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer (R : Set G) := by
      intro c hc
      have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.mp hc t ctx.t_mem_U).symm
      have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc z ctx.z_mem_U).symm
      exact mem_normalizer_commutator (mem_normalizer_inf (ctx.M_le_normalizer_Q (ctx.cenU_le_M hc))
        (mem_normalizer_centralizer_singleton hct)) (mem_normalizer_zpowers_of_comm hcz)
    have hTR : T ≤ normalizer (R : Set G) := fun x hx => by
      rw [hTdef] at hx
      exact hNormR x hx.2
    have hI : Iof U ≤ centralizer (U : Set G) := pLayerOf_le_self' 2 _
    have hcov : ∀ N : Subgroup G, centralizer (U : Set G) ≤ N → Cov10 k U (N ⊓ normalizer (R : Set G)) :=
      fun N hN _ x hx => Subgroup.mem_sup_left ⟨⟨hN (hI hx), hNormR x (hI hx)⟩, hx⟩
    have hRp' : Rp z k p T U Q M R := by
      refine ⟨⟨hRne, hRp, hRM, hTR, hcov M ctx.cenU_le_M⟩, fun hb => hRne ?_⟩
      have h1 : ⁅R, zpowers z⁆ ≤ ⁅Q ⊓ normalizer (R : Set G), zpowers z⁆ :=
        Subgroup.commutator_mono (le_inf hRQ Subgroup.le_normalizer) le_rfl
      rw [hRR, hb] at h1
      exact le_bot_iff.mp h1
    set N : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom with hNdef
    have hCtN : centralizer ({t} : Set G) ≤ N := by
      intro x hx
      rw [hNdef, mem_map_conj_iff, inv_inv]
      apply ctx.ctx9.cen_le
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hz' : z = g * t * g⁻¹ := by rw [ctx.choice.t_conj]; group
      calc g * x * g⁻¹ * z = g * (x * t) * g⁻¹ := by rw [hz']; group
        _ = g * (t * x) * g⁻¹ := by rw [hx']
        _ = z * (g * x * g⁻¹) := by rw [hz']; group
    have hCUN : centralizer (U : Set G) ≤ N :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ctx.t_mem_U)).trans hCtN
    have hRN : R ≤ N := hRCt.trans hCtN
    have hTN : T ≤ N := fun x hx => by
      rw [hTdef] at hx
      exact hCUN hx.2
    have hFs : Fs N = Op p N := by
      rw [hNdef, Fs_map, Op_map, ctx.ctx9.fstar]
    have hcoatom : IsCoatom N :=
      (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g⁻¹)) M).mpr ctx.ctx9.coatom
    have hnQR : ¬ Q ⊓ R ≤ Cen z := by
      intro hle
      have hb : ⁅R, zpowers z⁆ = ⊥ := commutator_zpowers_eq_bot_iff.mpr fun x hx => hle ⟨hRQ hx, hx⟩
      rw [hRR] at hb
      exact hRne hb
    rcases h104 G z k S M p Q T U t g ctx N R hcoatom hRp' hRN hTN
        ⟨hRne, hRp, hRN, hTR, hcov N hCUN⟩ hFs hnQR with hMN | ⟨-, hky⟩
    · have hM1 : M ≠ ⊥ := fun hb => z_ne_one_of_ctx ctx.ctx9.ctx (by
        have := ctx.ctx9.z_mem
        rw [hb] at this
        exact Subgroup.mem_bot.mp this)
      exact ctx.g_not_mem (mem_of_map_conj_eq ctx.ctx9.simple ctx.ctx9.coatom hM1 hMN)
    · have hcl := Signalizer.Stage2Ctx.isClassicalKind_of_not_typeOneCase ctx.ctx9.ctx hone
      rw [hky] at hcl
      rcases hcl with h | ⟨ε, h⟩ <;> cases h

end Prop111

end CFSG.GH74.GLS.Stage2.Bender.Thm2
