module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_quot_pCore_map_equiv (f : G ≃* G) (L : Subgroup G) :
    Nat.card (↥(L.map f.toMonoidHom) ⧸ CFSG.pCore 2 ↥(L.map f.toMonoidHom)) =
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  let e : (L ⧸ CFSG.pCore 2 L) ≃* ((L.map f.toMonoidHom : Subgroup G) ⧸
      CFSG.pCore 2 (L.map f.toMonoidHom : Subgroup G)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  exact (Nat.card_congr e.toEquiv).symm

section Hyp

variable [Finite G]

structure A3SubHyp (X T N R P L : Subgroup G) : Prop where
  T_sylow : IsSylowTwoOf T X
  N_le : N ≤ X
  N_norm : X ≤ normalizer (N : Set G)
  X_eq : N ⊔ T = X
  N_noTwo : NoPQuotient 2 ↥N
  R_le_T : R ≤ T
  T_norm_R : T ≤ normalizer (R : Set G)
  R_sylow : IsSylowTwoOf R (N ⊔ R)
  charTwo : CharTwo (N ⊔ R)
  R_le_P : R ≤ P
  P_le : P ≤ N ⊔ R
  X_eq_P : P ⊔ T = X
  L_le : L ≤ P
  L_norm : P ≤ normalizer (L : Set G)
  short : IsShort2 L
  ord3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3
  P_eq : P = L ⊔ R
  L_J : ⁅L, CFSG.Quasithin.thompsonJ R⁆ = L

namespace A3SubHyp

variable {X T N R P L : Subgroup G} (h : A3SubHyp X T N R P L)

include h

omit [Finite G] in
theorem T_le_X : T ≤ X := h.T_sylow.1

omit [Finite G] h in
theorem N_le_NR : N ≤ N ⊔ R := le_sup_left

omit [Finite G] in
theorem T_norm_N : T ≤ normalizer (N : Set G) := fun _ ht => h.N_norm (h.T_le_X ht)

omit [Finite G] in
theorem X_norm_NR : X ≤ normalizer ((N ⊔ R : Subgroup G) : Set G) := by
  rw [← h.X_eq]
  refine sup_le (fun n hn => Subgroup.le_normalizer (N_le_NR hn)) fun t ht => ?_
  exact C1.mem_normalizer_sup (h.T_norm_N ht) (h.T_norm_R ht)

omit [Finite G] in
theorem Q_le_R : blockQ (N ⊔ R) ≤ R := h.R_sylow.pCoreOf_le

omit h in
theorem Q_two : IsPGroup 2 (blockQ (N ⊔ R)) := C1.blockQ_isPGroup _

omit h in
theorem NR_norm_Q : N ⊔ R ≤ normalizer (blockQ (N ⊔ R) : Set G) := C1.le_normalizer_blockQ _

omit [Finite G] in
theorem X_norm_Q : X ≤ normalizer (blockQ (N ⊔ R) : Set G) := fun _ hg =>
  C1.mem_normalizer_blockQ (h.X_norm_NR hg)

omit [Finite G] in
theorem R_le_X : R ≤ X := h.R_le_T.trans h.T_le_X

omit [Finite G] in
theorem conj_P_le {t : G} (ht : t ∈ T) : P.map (MulAut.conj t).toMonoidHom ≤ N ⊔ R := by
  rintro _ ⟨p, hp, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (h.X_norm_NR (h.T_le_X ht)) p).mp (h.P_le hp)
  simpa using this

omit [Finite G] in
theorem R_le_conj_P {t : G} (ht : t ∈ T) : R ≤ P.map (MulAut.conj t).toMonoidHom := by
  intro r hr
  refine ⟨t⁻¹ * r * t, h.R_le_P ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (h.T_norm_R (T.inv_mem ht)) r).mp hr
    simpa using this
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem block_P : IsBlock2 P L :=
  ⟨h.short, h.L_le, ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.L_norm).isSubnormal⟩

omit [Finite G] in
theorem conj_block {t : G} : IsBlock2 (P.map (MulAut.conj t).toMonoidHom)
    (L.map (MulAut.conj t).toMonoidHom) := isBlock2_map_conj h.block_P t

omit [Finite G] in
theorem conj_short (t : G) : IsShort2 (L.map (MulAut.conj t).toMonoidHom) :=
  Lin2.IsShort2.map_equiv h.short (MulAut.conj t)

omit [Finite G] in
theorem conj_ord3 (t : G) :
    Nat.card (↥(L.map (MulAut.conj t).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(L.map (MulAut.conj t).toMonoidHom)) = 3 := by
  rw [card_quot_pCore_map_equiv]
  exact h.ord3

theorem propagation {t : G} (ht : t ∈ T) :
    blockU (L.map (MulAut.conj t).toMonoidHom) ≤ centerTorsion 2 (blockQ (N ⊔ R)) ∧
      ⁅blockQ (N ⊔ R), L.map (MulAut.conj t).toMonoidHom⁆ =
        blockU (L.map (MulAut.conj t).toMonoidHom) :=
  let hp := full_Sylow_short_core_propagation (G₀ := N ⊔ R) (H := P.map (MulAut.conj t).toMonoidHom)
    (S := R) h.charTwo h.R_sylow (h.R_le_conj_P ht) (h.conj_P_le ht) h.conj_block
  ⟨hp.1, hp.2.1⟩

theorem conj_facts {t : G} (ht : t ∈ T) :
    ⁅blockQ (N ⊔ R), L.map (MulAut.conj t).toMonoidHom⁆ =
        blockQ (L.map (MulAut.conj t).toMonoidHom) ∧
      blockQ (L.map (MulAut.conj t).toMonoidHom) ≤ centerTorsion 2 (blockQ (N ⊔ R)) ∧
      blockQ (N ⊔ R) ≤ normalizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨hU, hc⟩ := h.propagation ht
  have hb := (short_order_three_is_alternating_four (h.conj_short t) (h.conj_ord3 t)).1
  refine ⟨hc.trans hb.symm, hb ▸ hU, ?_⟩
  rw [Subgroup.le_normalizer_iff_commutator_le_right, hc]
  exact C1.blockU_le_blockQ (h.conj_short t) |>.trans (C1.blockQ_le _)

theorem block_centrality :
    N = conjJoin T L ∧ ⁅blockQ (N ⊔ R), N⁆ ≠ ⊥ ∧ IsElemAbelian 2 (⁅blockQ (N ⊔ R), N⁆ : Subgroup G) ∧
      X ≤ normalizer ((⁅blockQ (N ⊔ R), N⁆ : Subgroup G) : Set G) ∧
      ⁅blockQ (N ⊔ R), N⁆ ≤ centerTorsion 2 (blockQ (N ⊔ R)) ∧
      ⁅⁅blockQ (N ⊔ R), N⁆, N⁆ = ⁅blockQ (N ⊔ R), N⁆ := by
  have := normal_Sylow_part_block_centrality (X := X) (T := T) (N := N) (R := R) (P := P)
    h.T_sylow h.N_le h.N_norm h.X_eq h.N_noTwo h.R_le_T h.T_norm_R h.R_sylow h.charTwo
    h.R_le_P h.P_le h.X_eq_P (s := 1) le_rfl (fun _ => L) (fun _ => h.block_P)
    (by rw [iSup_const, sup_comm]; exact h.P_eq.symm)
  simpa using this

end A3SubHyp

structure ConjEnum (T L : Subgroup G) {r : ℕ} (Lf : Fin r → Subgroup G) : Prop where
  inj : Function.Injective Lf
  mem : ∀ i, ∃ t ∈ T, Lf i = L.map (MulAut.conj t).toMonoidHom
  all : ∀ t ∈ T, ∃ i, L.map (MulAut.conj t).toMonoidHom = Lf i

omit [Finite G] in
theorem ConjEnum.iSup_eq {T L : Subgroup G} {r : ℕ} {Lf : Fin r → Subgroup G}
    (E : ConjEnum T L Lf) : conjJoin T L = ⨆ i, Lf i := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    obtain ⟨i, hi⟩ := E.all s s.2
    rw [hi]
    exact le_iSup Lf i
  · refine iSup_le fun i => ?_
    obtain ⟨t, ht, hi⟩ := E.mem i
    rw [hi]
    exact le_iSup (fun s : ↥T => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩

omit [Finite G] in
theorem map_normalizerMonoidHom_subgroupOf {K S : Subgroup G} (hSK : S ≤ K)
    (g : normalizer (K : Set G)) :
    (S.subgroupOf K).map (K.normalizerMonoidHom g) =
      (S.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : G), hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe K g x).symm
  · intro hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨⟨s, hSK hs⟩, hs, Subtype.ext ?_⟩
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe K g ⟨s, hSK hs⟩).trans
      (by simpa using hsy)

omit [Finite G] in
theorem cube_mem_blockQ {L : Subgroup G} (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) {l : G}
    (hl : l ∈ L) : l ^ 3 ∈ blockQ L := by
  have := pow_card_eq_one' (G := ↥L ⧸ CFSG.pCore 2 ↥L) (x := QuotientGroup.mk ⟨l, hl⟩)
  rw [h3, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  rw [blockQ_eq_map]
  exact ⟨⟨l, hl⟩ ^ 3, this, by simp⟩

end Hyp

end CFSG.QuasithinUnique.Setup.Wreath
