module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesTwisted
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaPieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (coordEmbedGL)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair spinMinusModel
  minusLongBlock shortBlock finOne)
open CFSG.LieType.Universal.Spin.Twisted (fact_shortField)

section Transport

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kOmM_map_subtype_perfectCore_centralizer {r f : ℕ} (hr3 : 3 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (P : Subgroup (Fin r → Kˣ)) :
    (perfectCore (centralizer ((((P.map (diagSp K r)).map (kOmMIota hr3 hirr hKc hf) :
      Subgroup (StatedOmega (StatedQuadMinus (r + 1) K b c))) :
        Set (StatedOmega (StatedQuadMinus (r + 1) K b c)))))).map
          (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype =
      perfectCore (StatedOmega (StatedQuadMinus (r + 1) K b c) ⊓
        centralizer (kOmMDiag K r '' (P : Set (Fin r → Kˣ)))) := by
  rw [← F4Pilot.perfectCore_range_inf_centralizer_map
    (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype_injective, range_subtype]
  congr 3
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
    exact ⟨t, ht, (coe_kOmMIota_diagSp hr3 hirr hKc hf t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, coe_kOmMIota_diagSp hr3 hirr hKc hf t⟩

end Transport

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem kOmM_pieceCore_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr3 : 3 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1)) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmMIota hr3 hirr hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {J : Finset (Fin (r + 1))} (hk : k ∉ spSupport J) :
    pieceCore e J = (perfectCore (centralizer ((((kOmegaTorusParam k J).map (diagSp K r)).map
      (kOmMIota hr3 hirr hKc hf) : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K b c))) :
        Set (StatedOmega (StatedQuadMinus (r + 1) K b c))))).map
      ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  set P := kOmegaTorusParam (K := K) k J with hP
  set lamG : StatedSp r K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) with hlamG
  have hcomp : ((neighbourCore e k).subtype.comp Φ.toMonoidHom).comp
      (kOmMIota hr3 hirr hKc hf) = lamG.comp (fieldSp r K σ).toMonoidHom := by
    ext1 x
    exact hΦ x
  have hS : ((P.map (diagSp K r)).map (kOmMIota hr3 hirr hKc hf)).map
      ((neighbourCore e k).subtype.comp Φ.toMonoidHom) =
        modelToG e ((P.map (diagSp K r)).map
          ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_fieldSp_kOmegaTorusParam,
      UnitaryPilot.modelToG, hlamG]
    simp only [Subgroup.map_map]
    rfl
  have hXE : modelToG e (rootTorusSp K k) ≤ centralizer (neighbourCore e k : Set G) :=
    le_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _)
  rw [pieceCore_eq e hk]
  refine F4Pilot.perfectCore_inf_centralizer_eq_map_mulEquiv Φ ?_
  rw [hS, kOmega_leviTorusSp_eq_sup hk, UnitaryPilot.modelToG_sup, sup_comm (modelToG e _),
    sup_assoc, sup_eq_right.2 hXE]

theorem kOmM_pieceCore_short_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1)) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmMIota hr3 hirr hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {j : Fin (r + 1)} (hj : j.val + 1 < r + 1) {a a' : Fin r} (ha : k.succAbove a = j)
    (ha' : k.succAbove a' = ⟨j.val + 1, hj⟩) :
    pieceCore e ({j} : Finset (Fin (r + 1))) =
      (((OmegaPilot.siegelBlockGL K {a, a'}).map
        (coordEmbedGL (kOmMEmb r) kOmMEmb_injective)).subgroupOf
          (StatedOmega (StatedQuadMinus (r + 1) K b c))).map
            ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hab : a ≠ a' := fun h => by
    have := congrArg Fin.val (ha.symm.trans ((congrArg k.succAbove h).trans ha'))
    simp at this
  have hkj : k ≠ j := fun h => Fin.succAbove_ne k a (ha.trans h.symm)
  have hkj1 : k ≠ ⟨j.val + 1, hj⟩ := fun h => Fin.succAbove_ne k a' (ha'.trans h.symm)
  have hk : k ∉ spSupport ({j} : Finset (Fin (r + 1))) := by
    rw [mem_spSupport]
    rintro (h | ⟨j', hj', h⟩)
    · exact hkj (Finset.mem_singleton.1 h)
    · rw [Finset.mem_singleton.1 hj'] at h
      exact hkj1 (Fin.ext h.symm)
  have hP : ∀ t : Fin r → Kˣ, t ∈ kOmegaTorusParam (K := K) k {j} ↔ t a = t a' := by
    intro t
    have e1 : kOmegaInsert K k t j = t a := by
      rw [kOmegaInsert_apply, ← ha]
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t a
    have e2 : kOmegaInsert K k t ⟨j.val + 1, hj⟩ = t a' := by
      rw [kOmegaInsert_apply, ← ha']
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t a'
    rw [mem_kOmegaTorusParam, mem_leviTorusParam]
    constructor
    · intro h
      have h2 := (h j (Finset.mem_singleton_self _)).1 hj
      rwa [e1, e2] at h2
    · intro h j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
      rw [e1, e2, h]
  have hshort := kOmM_perfectCore_short hK4 hirr hab
    (Ts := (kOmegaTorusParam (K := K) k {j} : Set (Fin r → Kˣ))) hP
  have hle : (OmegaPilot.siegelBlockGL K {a, a'}).map
      (coordEmbedGL (kOmMEmb r) kOmMEmb_injective) ≤
        StatedOmega (StatedQuadMinus (r + 1) K b c) := by
    rw [← hshort]
    exact (perfectCore_le _).trans inf_le_left
  rw [kOmM_pieceCore_eq_map hKc hf hr3 e k hirr Φ σ hΦ hk]
  congr 1
  apply Subgroup.map_injective (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype_injective
  rw [kOmM_map_subtype_perfectCore_centralizer, hshort, kOmega_map_subtype_subgroupOf hle]

theorem kOmM_pieceCore_long_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1)) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmMIota hr3 hirr hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {c' : Fin r} (hc : k.succAbove c' = Fin.last r) :
    pieceCore e ({Fin.last r} : Finset (Fin (r + 1))) =
      (((StatedOmega (StatedQuadMinus 2 K b c)).map
        (coordEmbedGL (kOmMLongEmb r c') (kOmMLongEmb_injective c'))).subgroupOf
          (StatedOmega (StatedQuadMinus (r + 1) K b c))).map
            ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hkl : k ≠ Fin.last r := fun h => Fin.succAbove_ne k c' (hc.trans h.symm)
  have hk : k ∉ spSupport ({Fin.last r} : Finset (Fin (r + 1))) := by
    rw [mem_spSupport]
    rintro (h | ⟨j', hj', h⟩)
    · exact hkl (Finset.mem_singleton.1 h)
    · rw [Finset.mem_singleton.1 hj', Fin.val_last] at h
      have := k.isLt
      omega
  have hP : ∀ t : Fin r → Kˣ, t ∈ kOmegaTorusParam (K := K) k {Fin.last r} ↔ t c' = 1 := by
    intro t
    have hins : kOmegaInsert K k t (Fin.last r) = t c' := by
      rw [kOmegaInsert_apply, ← hc]
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t c'
    rw [mem_kOmegaTorusParam, mem_leviTorusParam]
    constructor
    · intro h
      have h3 := (h (Fin.last r) (Finset.mem_singleton_self _)).2 (by rw [Fin.val_last])
      rwa [hins] at h3
    · intro h j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      refine ⟨fun h' => absurd h' (by rw [Fin.val_last]; omega), fun _ => ?_⟩
      rw [hins, h]
  have hlong := kOmM_perfectCore_long hK4 hirr (l := c')
    (Ts := (kOmegaTorusParam (K := K) k {Fin.last r} : Set (Fin r → Kˣ))) hP
  have hle : (StatedOmega (StatedQuadMinus 2 K b c)).map
      (coordEmbedGL (kOmMLongEmb r c') (kOmMLongEmb_injective c')) ≤
        StatedOmega (StatedQuadMinus (r + 1) K b c) := by
    rw [← hlong]
    exact (perfectCore_le _).trans inf_le_left
  rw [kOmM_pieceCore_eq_map hKc hf hr3 e k hirr Φ σ hΦ hk]
  congr 1
  apply Subgroup.map_injective (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype_injective
  rw [kOmM_map_subtype_perfectCore_centralizer, hlong, kOmega_map_subtype_subgroupOf hle]

end Pieces

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def KOmMParams {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp (m + 2) K) : Prop :=
  ∀ k : Fin (m + 2), ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Φ : StatedOmega (StatedQuadMinus (m + 2) K b c) ≃* neighbourCore e k) (σ : K ≃+* K),
      ∀ x : StatedSp (m + 1) K,
        ((Φ (kOmMIota (r := m + 1) (by omega) hirr hKc hf x) : neighbourCore e k) : G) =
          ((e.symm (complSpEquiv k (fieldSp (m + 1) K σ x)) : L) : G)

omit [Finite K] [CharP K 2] in
theorem kOmM_short_le_statedOmega [Finite K] (hK : 4 ≤ Nat.card K) {r : ℕ} (b c : K)
    {a a' : Fin r} (hab : a ≠ a') :
    (OmegaPilot.siegelBlockGL K {a, a'}).map (coordEmbedGL (kOmMEmb r) kOmMEmb_injective) ≤
      StatedOmega (StatedQuadMinus (r + 1) K b c) :=
  (map_mono (OmegaPilot.siegelBlockGL_le_statedOmega hK (by rw [Finset.card_pair hab]))).trans
    ((kOmM_isCoordSplit_hyp r b c).map_statedOmega_le kOmMEmb_injective)

theorem kOmM_pieceCore_short_eq_modelToG {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) (hpar : KOmMParams hm hKc hf e)
    (j : Fin (m + 2)) (hj : j.val + 1 < m + 2) :
    pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hcard : ∀ (k : Fin (m + 2)) (a a' : Fin (m + 1)), k.succAbove a = j →
      k.succAbove a' = ⟨j.val + 1, hj⟩ →
      Nat.card (pieceCore e ({j} : Finset (Fin (m + 2)))) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro k a a' ha ha'
    obtain ⟨b, c, hirr, Φ, σ, hΦ⟩ := hpar k
    have hab : a ≠ a' := fun h => by
      have := congrArg Fin.val (ha.symm.trans ((congrArg k.succAbove h).trans ha'))
      simp at this
    rw [kOmM_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) e k hirr Φ σ hΦ hj ha ha',
      kOmega_card_map_subgroupOf (kOmM_short_le_statedOmega hK4 b c hab)
        ((neighbourCore e k).subtype_injective.comp Φ.injective),
      kOmM_card_short hab]
  have hc : Nat.card (pieceCore e ({j} : Finset (Fin (m + 2)))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    by_cases hj0 : j.val = 0
    · refine hcard (Fin.last (m + 1)) ⟨0, by omega⟩ ⟨1, by omega⟩ ?_ ?_
      · rw [Fin.succAbove_last]
        exact Fin.ext (by simp [hj0])
      · rw [Fin.succAbove_last]
        exact Fin.ext (by simp [hj0])
    · refine hcard 0 ⟨j.val - 1, by omega⟩ ⟨j.val, by omega⟩ ?_ ?_
      · rw [Fin.succAbove_zero]
        exact Fin.ext (by simp; omega)
      · rw [Fin.succAbove_zero]
        exact Fin.ext (by simp)
  refine (Subgroup.eq_of_le_of_card_ge
    (modelToG_simpleRootSL2_le_pieceCore e hK4 (Finset.mem_singleton_self j)) ?_).symm
  rw [hc, UnitaryPilot.card_modelToG, kOmega_card_simpleRootSL2]

theorem kOmM_simpleRootSL2_le_centralizer_long {m f : ℕ} (hm : 2 ≤ m)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K)
    (hpar : KOmMParams hm hKc hf e)
    (hshort : ∀ j : Fin (m + 2), j.val + 1 < m + 2 →
      pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j))
    (i : Fin (m + 2)) (hi : i.val + 3 ≤ m + 2) :
    modelToG e (simpleRootSL2 K i) ≤
      centralizer (pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) : Set G) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hiv : i.val + 1 < m + 2 := by omega
  rw [← hshort i hiv]
  set k : Fin (m + 2) := if i.val = 0 then ⟨2, by omega⟩ else 0 with hkdef
  obtain ⟨a, a', ha, ha', ha_lt, ha'_lt⟩ : ∃ a a' : Fin (m + 1), k.succAbove a = i ∧
      k.succAbove a' = ⟨i.val + 1, hiv⟩ ∧ a.val < m ∧ a'.val < m := by
    by_cases hi0 : i.val = 0
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, by simp; omega, by simp; omega⟩
      · rw [hkdef, ite_eq_left hi0]
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
        exact Fin.ext (by simp [hi0])
      · rw [hkdef, ite_eq_left hi0]
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
        exact Fin.ext (by simp [hi0])
    · refine ⟨⟨i.val - 1, by omega⟩, ⟨i.val, by omega⟩, ?_, ?_, by simp; omega, by simp; omega⟩
      · rw [hkdef, ite_eq_right hi0, Fin.succAbove_zero]
        exact Fin.ext (by simp; omega)
      · rw [hkdef, ite_eq_right hi0, Fin.succAbove_zero]
        exact Fin.ext (by simp)
  have hkl : k ≠ Fin.last (m + 1) := by
    rw [hkdef]
    split_ifs <;> intro h <;> have := congrArg Fin.val h <;> simp at this
    omega
  obtain ⟨b, c, hirr, Φ, σ, hΦ⟩ := hpar k
  obtain ⟨c', hc⟩ := Fin.exists_succAbove_eq hkl.symm
  have hcm : c'.val = m := by
    by_contra hcm
    have hc' := congrArg Fin.val hc
    rw [Fin.val_last] at hc'
    by_cases hck : c'.castSucc < k
    · rw [Fin.succAbove_of_castSucc_lt _ _ hck] at hc'
      simp at hc'
      omega
    · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hck)] at hc'
      simp at hc'
      omega
  have hab : a ≠ a' := fun h => by
    have := congrArg Fin.val (ha.symm.trans ((congrArg k.succAbove h).trans ha'))
    simp at this
  rw [kOmM_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) e k hirr Φ σ hΦ hiv ha ha',
    kOmM_pieceCore_long_eq_map (r := m + 1) hKc hf (by omega) e k hirr Φ σ hΦ hc]
  refine kOmega_map_subgroupOf_le_centralizer (fun x hx y hy => ?_) _
  have hdisj : Disjoint (kOmMEmb (m + 1) '' planeCoords ({a, a'} : Finset (Fin (m + 1))))
      (Set.range (kOmMLongEmb (m + 1) c')) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    rw [kOmM_mem_range_longEmb_iff] at hz
    rw [mem_planeCoords] at hy
    have hyc : planeOf y = c' := by
      rcases y with p | p
      · rcases hz with h | h | ⟨j, h⟩
        · exact Sum.inl_injective h
        · exact absurd h Sum.inl_ne_inr
        · exact absurd h Sum.inl_ne_inr
      · rcases hz with h | h | ⟨j, h⟩
        · exact absurd h Sum.inr_ne_inl
        · exact Sum.inl_injective (Sum.inr_injective h)
        · exact absurd (Sum.inr_injective h) Sum.inl_ne_inr
    rw [hyc] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h
    · have := congrArg Fin.val h
      omega
    · have := congrArg Fin.val h
      omega
  exact OmegaPilot.commute_of_mem_suppGL_of_disjoint hdisj (kOmM_short_le_suppGL a a' hx)
    (kOmM_long_le_suppGL b c c' hy)

end Assembly

section Twisted

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem kOmM_twistedPair {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp (m + 2) K) (hpar : KOmMParams hm hKc hf e)
    (hshort : ∀ j : Fin (m + 2), j.val + 1 < m + 2 →
      pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j)) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
      TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K (Fin.last m).castSucc))
        (pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2)))) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨b, c, hirr, Φ₀, σ₀, hΦ₀⟩ := hpar 0
  have := fact_shortField hirr
  set κ₀ : Fin (m + 1) := ⟨m - 1, by omega⟩ with hκ₀
  have hk3 : κ₀.val + 3 = m + 1 + 1 := by simp only [hκ₀]; omega
  obtain ⟨Θ, hΘ, hΘl, hΘs, hlb, hsb⟩ :=
    kOmM_exists_twisted_model (r := m + 1) hK4 (by omega) hirr hk3
  set Ψ₀ : StatedOmega (StatedQuadMinus (m + 2) K b c) →* G :=
    (neighbourCore e 0).subtype.comp Φ₀.toMonoidHom with hΨ₀
  have hΨ₀inj : Function.Injective Ψ₀ :=
    (neighbourCore e 0).subtype_injective.comp Φ₀.injective
  have hjm : (Fin.last m).castSucc.val + 1 < m + 2 := by simp
  have hU : modelToG e (simpleRootSL2 K (Fin.last m).castSucc) =
      (((OmegaPilot.siegelBlockGL K {κ₀, ⟨κ₀.val + 1, by omega⟩}).map
        (coordEmbedGL (kOmMEmb (m + 1)) kOmMEmb_injective)).subgroupOf
          (StatedOmega (StatedQuadMinus (m + 2) K b c))).map Ψ₀ := by
    rw [← hshort _ hjm, kOmM_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) e 0 hirr Φ₀ σ₀
      hΦ₀ hjm (a := κ₀) (a' := ⟨κ₀.val + 1, by omega⟩)
      (by rw [Fin.succAbove_zero]; exact Fin.ext (by simp [hκ₀]; omega))
      (by rw [Fin.succAbove_zero]; exact Fin.ext (by simp [hκ₀]; omega))]
  have hV : pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) =
      (((StatedOmega (StatedQuadMinus 2 K b c)).map
        (coordEmbedGL (kOmMLongEmb (m + 1) ⟨κ₀.val + 1, by omega⟩)
          (kOmMLongEmb_injective _))).subgroupOf
          (StatedOmega (StatedQuadMinus (m + 2) K b c))).map Ψ₀ :=
    kOmM_pieceCore_long_eq_map (r := m + 1) hKc hf (by omega) e 0 hirr Φ₀ σ₀ hΦ₀
      (c' := ⟨κ₀.val + 1, by omega⟩)
      (by rw [Fin.succAbove_zero]; exact Fin.ext (by simp [hκ₀]; omega))
  have hsub : ∀ (H : Subgroup (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 3 K b c)))
      (S : Subgroup (GL (Fin (m + 2 - 1) ⊕ Fin (m + 2 - 1) ⊕ Fin 2) K)),
      (H.map Θ).map (StatedOmega (StatedQuadMinus (m + 2) K b c)).subtype = S →
        H.map Θ = S.subgroupOf (StatedOmega (StatedQuadMinus (m + 2) K b c)) := by
    intro H S hS
    have hSM : S ≤ StatedOmega (StatedQuadMinus (m + 2) K b c) := hS ▸ map_subtype_le _
    apply Subgroup.map_injective (StatedOmega (StatedQuadMinus (m + 2) K b c)).subtype_injective
    rw [hS, kOmega_map_subtype_subgroupOf hSM]
  refine ⟨b, c, hirr, (Ψ₀.comp Θ).range, Ψ₀.comp Θ, rfl, ?_, hΨ₀inj.comp hΘl, hΨ₀inj.comp hΘs,
    ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff (Ψ₀.comp Θ)).2 (hΨ₀inj.comp hΘ)]
    exact bot_le
  · change (minusLongBlock b c).range.map (Ψ₀.comp Θ) = _
    rw [← Subgroup.map_map, hsub _ _ hlb, hU]
  · change (shortBlock hirr 3 finOne).range.map (Ψ₀.comp Θ) = _
    rw [← Subgroup.map_map, hsub _ _ hsb, hV]

theorem spOmegaMinusPieces_of_params {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) (hpar : KOmMParams hm hKc hf e) :
    SpOmegaMinusPieces e := by
  have hshort := kOmM_pieceCore_short_eq_modelToG hm hKc hf e hpar
  exact ⟨hshort, kOmM_simpleRootSL2_le_centralizer_long hm hKc hf e hpar hshort,
    kOmM_twistedPair hm hKc hf e hpar hshort⟩

theorem kOmMParams_of_rootKind (hset : SeitzSetting G L) {m f : ℕ} (hm : 2 ≤ m)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin (m + 2), RootKindSp e t f k .omegaMinus) : KOmMParams hm hKc hf e := by
  intro k
  obtain ⟨b, c, hirr, Φ, σ, -, hΦ⟩ := exists_kOmMParam (r := m + 1) hset hKc hf (by omega) e
    htC ht k (hroot k)
  exact ⟨b, c, hirr, Φ, σ, hΦ⟩

theorem spOmegaMinusPieceInput_holds : SpOmegaMinusPieceInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact spOmegaMinusPieces_of_params hm hKc hf e
    (kOmMParams_of_rootKind hset hm hKc hf e htC ht hroot)

end Twisted

end CFSG.SeitzReduction.SymplecticPilot
