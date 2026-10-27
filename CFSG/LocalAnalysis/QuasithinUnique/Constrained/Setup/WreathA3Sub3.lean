module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Lift3

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

namespace A3SubHyp

variable {X T N R P L : Subgroup G} (h : A3SubHyp X T N R P L)

include h

theorem a3LiftHyp {r : ℕ} {Lf : Fin r → Subgroup G} (E : ConjEnum T L Lf)
    (hsub : (((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))).IsSubnormal) :
    A3LiftHyp (blockQ (N ⊔ R) ⊔ N) (blockQ (N ⊔ R)) Lf := by
  have hN_eq : N = ⨆ i, Lf i := by
    rw [← E.iSup_eq]
    exact (h.block_centrality).1
  have hLfN : ∀ i, Lf i ≤ N := fun i => by
    rw [hN_eq]
    exact le_iSup Lf i
  have hHNR : blockQ (N ⊔ R) ⊔ N ≤ N ⊔ R := sup_le (C1.blockQ_le _) le_sup_left
  refine
    { Q_le := le_sup_left
      Q_norm := sup_le Subgroup.le_normalizer fun n hn => NR_norm_Q ((le_sup_left : N ≤ N ⊔ R) hn)
      Q_two := Q_two
      cent_le := fun x hx => h.charTwo ⟨hHNR hx.1, hx.2⟩
      inj := E.inj
      short := fun i => by
        obtain ⟨t, ht, hi⟩ := E.mem i
        rw [hi]; exact h.conj_short t
      L_le := fun i => (hLfN i).trans le_sup_right
      ord3 := fun i => by
        obtain ⟨t, ht, hi⟩ := E.mem i
        rw [hi]; exact h.conj_ord3 t
      Q_norm_L := fun i => by
        obtain ⟨t, ht, hi⟩ := E.mem i
        rw [hi]; exact (h.conj_facts ht).2.2
      comm_eq := fun i => by
        obtain ⟨t, ht, hi⟩ := E.mem i
        rw [hi]; exact (h.conj_facts ht).1
      U_le_Z := fun i => by
        obtain ⟨t, ht, hi⟩ := E.mem i
        rw [hi]; exact (h.conj_facts ht).2.1
      gen := by
        rw [← hN_eq]
      three := h.three_of_subnormal E hsub }


omit [Finite G] in
theorem map_conj_thompsonJ {t : G} (ht : t ∈ T) :
    (CFSG.Quasithin.thompsonJ R).map (MulAut.conj t).toMonoidHom = CFSG.Quasithin.thompsonJ R := by
  have := GammaExtra.thompsonJ_map_equiv (MulAut.conj t) R
  rw [GammaExtra.map_conj_eq_self_of_mem_normalizer (h.T_norm_R ht)] at this
  exact this.symm

omit [Finite G] in
theorem conj_L_J {t : G} (ht : t ∈ T) :
    ⁅L.map (MulAut.conj t).toMonoidHom, CFSG.Quasithin.thompsonJ R⁆ =
      L.map (MulAut.conj t).toMonoidHom := by
  conv_lhs => rw [← h.map_conj_thompsonJ ht]
  rw [← Subgroup.map_commutator, h.L_J]

omit [Finite G] in
theorem conj_P_le_normalizer {t : G} : P.map (MulAut.conj t).toMonoidHom ≤
    normalizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [normalizer_map_equiv]
  exact Subgroup.map_mono h.L_norm

end A3SubHyp

theorem subnormal_A3_quotient_actor_residual_family {X T N R P L : Subgroup G}
    (h : A3SubHyp X T N R P L) (_hR1 : R ≠ ⊥)
    (hsub : (((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))).IsSubnormal)
    {r : ℕ} {Lf : Fin r → Subgroup G} (E : ConjEnum T L Lf) :
    N = ⨆ i, Lf i ∧ iSupIndep Lf ∧ (∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) ∧
      (∀ i, ((Lf i).subgroupOf (blockQ (N ⊔ R) ⊔ N)).Normal) ∧
      (∀ i, ((Lf i).subgroupOf X).IsSubnormal) ∧
      (∀ t ∈ T, ∀ i, ∃ j, (Lf i).map (MulAut.conj t).toMonoidHom = Lf j) ∧
      (∀ i j, ∃ t ∈ T, (Lf i).map (MulAut.conj t).toMonoidHom = Lf j) ∧
      (∀ i, Nonempty (↥(Lf i) ≃* alternatingGroup (Fin 4)) ∧ IsChi0Block X (Lf i) ∧
        ⁅Lf i, CFSG.Quasithin.thompsonJ R⁆ = Lf i) ∧
      (IsElemAbelian 2 (⨆ i, blockQ (Lf i) : Subgroup G) ∧
        iSupIndep (fun i => blockQ (Lf i)) ∧
        X ≤ normalizer ((⨆ i, blockQ (Lf i) : Subgroup G) : Set G) ∧
        (⨆ i, blockQ (Lf i) : Subgroup G) = ⁅blockQ (N ⊔ R), N⁆ ∧
        ⁅blockQ (N ⊔ R), N⁆ ≤ centerTorsion 2 (blockQ (N ⊔ R)) ∧
        centerTorsion 2 (blockQ (N ⊔ R)) ≤ R) ∧
      (N ⊔ T = X ∧ IsSylowTwoOf R (N ⊔ R)) := by
  classical
  have hL := h.a3LiftHyp E hsub
  have hN_eq : N = ⨆ i, Lf i := by
    rw [← E.iSup_eq]
    exact (h.block_centrality).1
  have hLfN : ∀ i, Lf i ≤ N := fun i => by
    rw [hN_eq]
    exact le_iSup Lf i
  have hHX : blockQ (N ⊔ R) ⊔ N ≤ X :=
    sup_le (h.Q_le_R.trans h.R_le_X) h.N_le
  have hHnorm : X ≤ normalizer ((blockQ (N ⊔ R) ⊔ N : Subgroup G) : Set G) := fun g hg =>
    C1.mem_normalizer_sup (h.X_norm_Q hg) (h.N_norm hg)
  have hnormal : ∀ i, ((Lf i).subgroupOf (blockQ (N ⊔ R) ⊔ N)).Normal := fun i =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.L_le i)).2 (hL.H_le_normalizer_L i)
  have hsubn : ∀ i, ((Lf i).subgroupOf X).IsSubnormal := fun i =>
    CFSG.QuasithinUnique.Setup.Layer.isSubnormal_trans (hL.L_le i) hHX (hnormal i).isSubnormal
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHX).2 hHnorm).isSubnormal
  have hmapmap : ∀ t t' : G, (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t').toMonoidHom =
      L.map (MulAut.conj (t' * t)).toMonoidHom := by
    intro t t'
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hJ : ∀ t ∈ T, (CFSG.Quasithin.thompsonJ R).map (MulAut.conj t).toMonoidHom =
      CFSG.Quasithin.thompsonJ R := by
    intro t ht
    have := GammaExtra.thompsonJ_map_equiv (MulAut.conj t) R
    rw [GammaExtra.map_conj_eq_self_of_mem_normalizer (h.T_norm_R ht)] at this
    exact this.symm
  have hU : (⨆ i, blockQ (Lf i) : Subgroup G) = ⁅blockQ (N ⊔ R), N⁆ := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [← hL.comm_eq i]
      exact Subgroup.commutator_mono le_rfl (hLfN i)
    · rw [Subgroup.commutator_le]
      intro q hq n hn
      have hn' : n ∈ ⨆ i, Lf i := by rw [← hN_eq]; exact hn
      refine (Subgroup.iSup_induction Lf
        (C := fun n => n ∈ N ∧ ⁅q, n⁆ ∈ (⨆ i, blockQ (Lf i) : Subgroup G)) hn' ?_ ?_ ?_).2
      · intro i l hl
        refine ⟨hLfN i hl, ?_⟩
        have h1 : ⁅q, l⁆ ∈ ⁅blockQ (N ⊔ R), Lf i⁆ := Subgroup.commutator_mem_commutator hq hl
        rw [hL.comm_eq i] at h1
        exact Subgroup.mem_iSup_of_mem i h1
      · exact ⟨N.one_mem, by simp⟩
      · rintro n n' ⟨hnN, hn1⟩ ⟨hn'N, hn2⟩
        refine ⟨N.mul_mem hnN hn'N, ?_⟩
        have e : ⁅q, n * n'⁆ = ⁅q, n⁆ * (n * ⁅q, n'⁆ * n⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        refine Subgroup.mul_mem _ hn1 ?_
        exact (Subgroup.mem_normalizer_iff.mp
          (hL.H_le_normalizer_U ((le_sup_right : N ≤ blockQ (N ⊔ R) ⊔ N) hnN)) _).mp hn2
  refine ⟨hN_eq, hL.L_indep, hL.L_commute, hnormal, hsubn, ?_, ?_, ?_, ?_, h.X_eq, h.R_sylow⟩
  · intro t ht i
    obtain ⟨s, hs, hi⟩ := E.mem i
    rw [hi, hmapmap]
    exact E.all (t * s) (T.mul_mem ht hs)
  · intro i j
    obtain ⟨s, hs, hi⟩ := E.mem i
    obtain ⟨s', hs', hj⟩ := E.mem j
    refine ⟨s' * s⁻¹, T.mul_mem hs' (T.inv_mem hs), ?_⟩
    rw [hi, hj, hmapmap, inv_mul_cancel_right]
  · intro i
    refine ⟨(hL.block i).2.2.2.1, ⟨⟨hL.short i, (hLfN i).trans h.N_le, hsubn i⟩,
      Or.inr (Or.inl (hL.block i).2.2.2.2)⟩, ?_⟩
    obtain ⟨t, ht, hi⟩ := E.mem i
    rw [hi]
    conv_lhs => rw [← hJ t ht]
    rw [← Subgroup.map_commutator, h.L_J]
  · refine ⟨hL.U_elem, hL.U_indep, ?_, hU, (h.block_centrality).2.2.2.2.1,
      (centerTorsion_le 2 _).trans h.Q_le_R⟩
    rw [hU]
    exact (h.block_centrality).2.2.2.1

end CFSG.QuasithinUnique.Setup.Wreath
