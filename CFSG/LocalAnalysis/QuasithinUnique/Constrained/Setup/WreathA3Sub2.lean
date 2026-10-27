module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteSub

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

namespace A3SubHyp

variable {X T N R P L : Subgroup G} (h : A3SubHyp X T N R P L)

include h

omit [Finite G] h in
theorem blockQ_subgroupOf_eq : (blockQ (N ⊔ R)).subgroupOf (N ⊔ R) = CFSG.pCore 2 ↥(N ⊔ R) := by
  rw [blockQ_eq_map]
  exact Subgroup.comap_map_eq_self_of_injective (N ⊔ R).subtype_injective _

omit [Finite G] in
theorem L_le_NR : L ≤ N ⊔ R := h.L_le.trans h.P_le

omit [Finite G] in
theorem L_sup_Q_le : L ⊔ blockQ (N ⊔ R) ≤ N ⊔ R :=
  sup_le h.L_le_NR (C1.blockQ_le _)

omit [Finite G] h in
theorem subnormal_NR
    (hsub : (((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))).IsSubnormal) :
    ((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).IsSubnormal := by
  have h1 := hsub.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hle : CFSG.pCore 2 ↥(N ⊔ R) ≤ (L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R) := by
    intro x hx
    have hx' : x ∈ (blockQ (N ⊔ R)).subgroupOf (N ⊔ R) := by rw [blockQ_subgroupOf_eq]; exact hx
    exact (le_sup_right : blockQ (N ⊔ R) ≤ L ⊔ blockQ (N ⊔ R)) (Subgroup.mem_subgroupOf.mp hx')
  rwa [sup_eq_left.2 hle] at h1

omit [Finite G] in
theorem subnormal_NR_conj
    (hsub : (((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))).IsSubnormal) {t : G} (ht : t ∈ T) :
    (((L.map (MulAut.conj t).toMonoidHom) ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).IsSubnormal := by
  have hn : t ∈ normalizer ((N ⊔ R : Subgroup G) : Set G) := h.X_norm_NR (h.T_le_X ht)
  have h1 := (subnormal_NR hsub).map
    (f := ((N ⊔ R : Subgroup G).normalizerMonoidHom ⟨t, hn⟩).toMonoidHom)
    (MulEquiv.surjective _)
  have h2 : ((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (((N ⊔ R : Subgroup G).normalizerMonoidHom ⟨t, hn⟩).toMonoidHom) =
      ((L.map (MulAut.conj t).toMonoidHom) ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R) := by
    have := map_normalizerMonoidHom_subgroupOf (K := N ⊔ R) (S := L ⊔ blockQ (N ⊔ R))
      h.L_sup_Q_le ⟨t, hn⟩
    rw [Subgroup.map_sup, GammaExtra.map_conj_eq_self_of_mem_normalizer
      (h.X_norm_Q (h.T_le_X ht))] at this
    exact this
  rw [h2] at h1
  exact h1

theorem three_of_subnormal {r : ℕ} {Lf : Fin r → Subgroup G} (E : ConjEnum T L Lf)
    (hsub : (((L ⊔ blockQ (N ⊔ R)).subgroupOf (N ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ R)))).IsSubnormal) :
    ∀ x ∈ blockQ (N ⊔ R) ⊔ N, ∃ k : ℕ, x ^ 3 ^ k ∈ blockQ (N ⊔ R) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set NR : Subgroup G := N ⊔ R with hNR
  set Q : Subgroup G := blockQ NR with hQ
  set Q' : Subgroup ↥NR := CFSG.pCore 2 ↥NR with hQ'
  let π : ↥NR →* ↥NR ⧸ Q' := QuotientGroup.mk' Q'
  have hQsub : Q.subgroupOf NR = Q' := blockQ_subgroupOf_eq
  have hN_eq : N = ⨆ i, Lf i := by
    rw [← E.iSup_eq]
    exact (h.block_centrality).1
  have hKle : ∀ t ∈ T, ∀ l ∈ L.map (MulAut.conj t).toMonoidHom, ∀ hl : l ∈ NR,
      π ⟨l, hl⟩ ∈ CFSG.pCore 3 (↥NR ⧸ Q') := by
    intro t ht l hlt hl
    set K : Subgroup (↥NR ⧸ Q') :=
      (((L.map (MulAut.conj t).toMonoidHom) ⊔ Q).subgroupOf NR).map π with hK
    have hKs : K.IsSubnormal := (h.subnormal_NR_conj hsub ht).map (QuotientGroup.mk'_surjective Q')
    have hLt3 := h.conj_ord3 t
    have hK3 : IsPGroup 3 ↥K := by
      rintro ⟨_, y, hy, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      have hyG : (y : G) ∈ (L.map (MulAut.conj t).toMonoidHom) ⊔ Q := hy
      obtain ⟨l', hl', q, hq, hyq⟩ := CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul
        (h.conj_facts ht).2.2 hyG
      have hl'NR : l' ∈ NR := h.conj_P_le ht ((Subgroup.map_mono h.L_le) hl')
      have hqNR : q ∈ NR := C1.blockQ_le _ hq
      have hy_eq : y = ⟨l', hl'NR⟩ * ⟨q, hqNR⟩ := Subtype.ext hyq
      have hqQ : (⟨q, hqNR⟩ : ↥NR) ∈ Q' := by
        rw [← hQsub]; exact hq
      have hl3Q : l' ^ 3 ∈ Q :=
        centerTorsion_le 2 Q ((h.conj_facts ht).2.1 (cube_mem_blockQ hLt3 hl'))
      have h3 : (⟨l', hl'NR⟩ : ↥NR) ^ 3 ∈ Q' := by
        rw [← hQsub, Subgroup.mem_subgroupOf]
        exact hl3Q
      have hπq : π ⟨q, hqNR⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hqQ
      have hπl : π (⟨l', hl'NR⟩ ^ 3) = 1 := (QuotientGroup.eq_one_iff _).2 h3
      show (π y) ^ 3 ^ 1 = 1
      rw [pow_one, hy_eq, map_mul, hπq, mul_one, ← map_pow]
      exact hπl
    have hKpc : K ≤ CFSG.Open.pCore 3 (↥NR ⧸ Q') :=
      CFSG.Quasithin.S14110.Commute.le_pCore_of_isSubnormal 3 hKs le_rfl
        (by rw [Subgroup.subgroupOf_self]; infer_instance) hK3
    exact hKpc (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : L.map (MulAut.conj t).toMonoidHom ≤ L.map (MulAut.conj t).toMonoidHom ⊔ Q) hlt)))
  let D' : Subgroup G := ((CFSG.pCore 3 (↥NR ⧸ Q')).comap π).map NR.subtype
  have hQD : Q ≤ D' := by
    intro q hq
    have hqNR : q ∈ NR := C1.blockQ_le _ hq
    refine ⟨⟨q, hqNR⟩, ?_, rfl⟩
    show π ⟨q, hqNR⟩ ∈ CFSG.pCore 3 _
    have : (⟨q, hqNR⟩ : ↥NR) ∈ Q' := by rw [← hQsub]; exact hq
    have hπq : π ⟨q, hqNR⟩ = 1 := (QuotientGroup.eq_one_iff _).2 this
    rw [hπq]
    exact Subgroup.one_mem _
  have hND : N ≤ D' := by
    rw [hN_eq]
    refine iSup_le fun i => ?_
    obtain ⟨t, ht, hi⟩ := E.mem i
    intro l hl
    rw [hi] at hl
    have hlNR : l ∈ NR := h.conj_P_le ht ((Subgroup.map_mono h.L_le) hl)
    exact ⟨⟨l, hlNR⟩, hKle t ht l hl hlNR, rfl⟩
  intro x hx
  have hxD : x ∈ D' := (sup_le hQD hND) hx
  obtain ⟨p, hp, rfl⟩ := hxD
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥NR ⧸ Q')) ⟨π p, hp⟩
  refine ⟨k, ?_⟩
  have h1 : π (p ^ 3 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  have h2 : p ^ 3 ^ k ∈ Q' := (QuotientGroup.eq_one_iff _).1 h1
  rw [← hQsub, Subgroup.mem_subgroupOf] at h2
  simpa using h2

end A3SubHyp

end CFSG.QuasithinUnique.Setup.Wreath
