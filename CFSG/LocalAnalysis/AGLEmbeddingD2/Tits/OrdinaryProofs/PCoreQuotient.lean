module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

instance pCore_normal_inst (p : ℕ) (G : Type*) [Group G] :
    (CFSG.Open.pCore p G).Normal :=
  CFSG.LieType.BorelTits.pCore_normal p

theorem nonempty_quotient_pCore_mulEquiv_perm_three {X : Type*} [Group X] [Finite X]
    {T : Subgroup X} (hT : IsPGroup 2 T) (hidx : T.index = 3) (hnn : ¬ T.Normal) :
    Nonempty (X ⧸ CFSG.Open.pCore 2 X ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : Nat.card (X ⧸ T) = 3 := hidx
  have hPerm : Nat.card (Equiv.Perm (X ⧸ T)) = 6 := by
    rw [Nat.card_perm, hcardQ]; rfl
  have hTX : Nat.card T * 3 = Nat.card X := by
    have h := Subgroup.card_mul_index T
    rwa [hidx] at h
  have hNT : T.normalCore ≤ T := Subgroup.normalCore_le T
  have hTsyl : ¬ 2 ∣ T.index := by rw [hidx]; decide
  have hpc : CFSG.Open.pCore 2 X = T.normalCore := by
    rw [CFSG.pCore_eq_iSup]
    apply le_antisymm
    · refine iSup_le fun M => iSup_le fun hMn => iSup_le fun hMp => ?_
      have : M.Normal := hMn
      have hMT : M ≤ T := by
        intro x hx
        have hsyl := IsPGroup.le_sylow_of_normal hMp (hT.toSylow hTsyl)
        exact (IsPGroup.mem_toSylow hT hTsyl).mp (hsyl hx)
      exact Subgroup.normal_le_normalCore.mpr hMT
    · exact le_iSup_of_le T.normalCore (le_iSup_of_le inferInstance
        (le_iSup_of_le (hT.to_le hNT) le_rfl))
  have hkerφ : (MulAction.toPermHom X (X ⧸ T)).ker = T.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
  have ha : T.normalCore.relIndex T * Nat.card T.normalCore = Nat.card T := by
    have h := Subgroup.relIndex_mul_card (H := T.normalCore) (K := T)
    rwa [inf_eq_left.mpr hNT] at h
  have hb : T.normalCore.index * Nat.card T.normalCore = Nat.card X := by
    rw [mul_comm]; exact Subgroup.card_mul_index _
  have hNpos : 0 < Nat.card T.normalCore := Nat.card_pos
  have hbA : T.normalCore.index = 3 * T.normalCore.relIndex T := by
    have h1 : T.normalCore.index * Nat.card T.normalCore =
        (3 * T.normalCore.relIndex T) * Nat.card T.normalCore := by
      rw [hb, ← hTX, ← ha]; ring
    exact Nat.eq_of_mul_eq_mul_right hNpos h1
  have ha0 : T.normalCore.relIndex T ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha
    have := Nat.card_pos (α := T)
    omega
  have ha1 : T.normalCore.relIndex T ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    apply hnn
    have hTN : T = T.normalCore := le_antisymm h hNT
    rw [hTN]
    infer_instance
  have ha2 : 2 ≤ T.normalCore.relIndex T := by omega
  have hcard_range : Nat.card (MulAction.toPermHom X (X ⧸ T)).range = T.normalCore.index := by
    rw [← hkerφ]
    exact (Subgroup.index_ker _).symm
  have hbdvd : T.normalCore.index ∣ 6 := by
    have hdvd : Nat.card (MulAction.toPermHom X (X ⧸ T)).range ∣
        Nat.card (Equiv.Perm (X ⧸ T)) := Subgroup.card_subgroup_dvd_card _
    rw [hcard_range, hPerm] at hdvd
    exact hdvd
  have hb6 : T.normalCore.index = 6 := by
    have hle : T.normalCore.index ≤ 6 := Nat.le_of_dvd (by decide) hbdvd
    omega
  have htop : (MulAction.toPermHom X (X ⧸ T)).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard_range, hb6, hPerm]
  have hsurj : Function.Surjective (MulAction.toPermHom X (X ⧸ T)) :=
    MonoidHom.range_eq_top.mp htop
  have e1 : X ⧸ (MulAction.toPermHom X (X ⧸ T)).ker ≃* Equiv.Perm (X ⧸ T) :=
    QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  have e2 : X ⧸ T.normalCore ≃* X ⧸ (MulAction.toPermHom X (X ⧸ T)).ker :=
    QuotientGroup.quotientMulEquivOfEq hkerφ.symm
  have e3 : X ⧸ CFSG.Open.pCore 2 X ≃* X ⧸ T.normalCore :=
    QuotientGroup.quotientMulEquivOfEq hpc
  have : Fintype (X ⧸ T) := Fintype.ofFinite _
  have hcardF : Fintype.card (X ⧸ T) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardQ
  let e : (X ⧸ T) ≃ Fin 3 := Fintype.equivFinOfCardEq hcardF
  exact ⟨e3.trans (e2.trans (e1.trans e.permCongrHom))⟩

theorem nonempty_quotient_pCore_mulEquiv_perm_three_of_le {G : Type*} [Group G] [Finite G]
    {T I : Subgroup G} (hTI : T ≤ I) (hT : IsPGroup 2 T) (hidx : T.relIndex I = 3)
    (hnn : ¬ I ≤ Subgroup.normalizer (T : Set G)) :
    Nonempty (↥I ⧸ CFSG.Open.pCore 2 ↥I ≃* Equiv.Perm (Fin 3)) := by
  have hT' : IsPGroup 2 (T.subgroupOf I) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTI).symm
  have hidx' : (T.subgroupOf I).index = 3 := hidx
  have hnn' : ¬ (T.subgroupOf I).Normal := by
    rwa [Subgroup.normal_subgroupOf_iff_le_normalizer hTI]
  exact nonempty_quotient_pCore_mulEquiv_perm_three hT' hidx' hnn'

theorem isSylowTwoOf_of_relIndex_three {G : Type*} [Group G] {T I : Subgroup G}
    (hTI : T ≤ I) (hT : IsPGroup 2 T) (hidx : T.relIndex I = 3) :
    CFSG.QuasithinUnique.IsSylowTwoOf T I := by
  refine ⟨hTI, hT, ?_⟩
  have h3 : (T.subgroupOf I).index = 3 := hidx
  rw [h3]
  decide

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
