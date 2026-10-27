module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaIota

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin (perfectCore)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Insert

variable (K : Type) [Field K] {r : ℕ}

@[expose] def kOmegaInsert (k : Fin (r + 1)) : (Fin r → Kˣ) →* (Fin (r + 1) → Kˣ) where
  toFun t := Fin.insertNth k 1 t
  map_one' := by
    funext i
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · rw [Fin.insertNth_apply_same]
      rfl
    · rw [Fin.insertNth_apply_succAbove]
      rfl
  map_mul' t s := by
    rw [← Fin.insertNth_mul, one_mul]

variable {K}

theorem kOmegaInsert_apply (k : Fin (r + 1)) (t : Fin r → Kˣ) :
    kOmegaInsert K k t = Fin.insertNth k 1 t := rfl

theorem kOmega_coe_complSpEquiv_diagSp (k : Fin (r + 1)) (t : Fin r → Kˣ) :
    ((complSpEquiv k (diagSp K r t) : complSp K k) : StatedSp (r + 1) K) =
      diagSp K (r + 1) (kOmegaInsert K k t) := by
  rw [coe_complSpEquiv_apply]
  apply mat_injective
  rw [mat_spEmbed, mat_diagSp, mat_diagSp]
  ext a b
  have hinj : Function.Injective (Sum.map k.succAbove k.succAbove : Fin r ⊕ Fin r → _) :=
    Sum.map_injective.2 ⟨Fin.succAbove_right_injective, Fin.succAbove_right_injective⟩
  by_cases h : a ∈ Set.range (Sum.map k.succAbove k.succAbove) ∧
      b ∈ Set.range (Sum.map k.succAbove k.succAbove)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image Fin.succAbove_right_injective, diagonal_apply, diagonal_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, ite_eq_left rfl]
      rcases x with x | x <;> simp [kOmegaInsert_apply, Fin.insertNth_apply_succAbove]
    · rw [ite_eq_right hxy, ite_eq_right (fun h => hxy (hinj h))]
  · rw [spEmbedMat_apply_of_not_mem _ h, diagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [one_apply_eq, ite_eq_left rfl]
      have ha : a ∉ Set.range (Sum.map k.succAbove k.succAbove) := fun ha => h ⟨ha, ha⟩
      rcases a with i | i
      · have hik : i = k := by
          by_contra hik
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
          exact ha ⟨Sum.inl j, rfl⟩
        subst hik
        simp [kOmegaInsert_apply, Fin.insertNth_apply_same]
      · have hik : i = k := by
          by_contra hik
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
          exact ha ⟨Sum.inr j, rfl⟩
        subst hik
        simp [kOmegaInsert_apply, Fin.insertNth_apply_same]
    · rw [one_apply_ne hab, ite_eq_right hab]

theorem kOmega_diagSp_eq_rootTorusHom_mul (k : Fin (r + 1)) (t : Fin (r + 1) → Kˣ) :
    diagSp K (r + 1) t =
      rootTorusHom K (r + 1) k (t k) * diagSp K (r + 1) (kOmegaInsert K k (Fin.removeNth k t)) := by
  rw [rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
  · simp [kOmegaInsert_apply]
  · simp [kOmegaInsert_apply]

end Insert

section Param

variable {K : Type} [Field K] {r : ℕ}

@[expose] def kOmegaTorusParam (k : Fin (r + 1)) (J : Finset (Fin (r + 1))) :
    Subgroup (Fin r → Kˣ) :=
  (leviTorusParam K J).comap (kOmegaInsert K k)

theorem mem_kOmegaTorusParam {k : Fin (r + 1)} {J : Finset (Fin (r + 1))} {t : Fin r → Kˣ} :
    t ∈ kOmegaTorusParam k J ↔ kOmegaInsert K k t ∈ leviTorusParam K J := Iff.rfl

theorem kOmega_map_units_mem_leviTorusParam (σ : K ≃+* K) {n : ℕ} {J : Finset (Fin n)}
    {t : Fin n → Kˣ} (ht : t ∈ leviTorusParam K J) :
    (fun i => Units.map (σ : K →* K) (t i)) ∈ leviTorusParam K J :=
  fun j hj => ⟨fun h => by simp only [(ht j hj).1 h], fun h => by simp only [(ht j hj).2 h,
    map_one]⟩

theorem map_units_mem_kOmegaTorusParam (σ : K ≃+* K) {k : Fin (r + 1)}
    {J : Finset (Fin (r + 1))} {t : Fin r → Kˣ} (ht : t ∈ kOmegaTorusParam k J) :
    (fun i => Units.map (σ : K →* K) (t i)) ∈ kOmegaTorusParam k J := by
  rw [mem_kOmegaTorusParam] at ht ⊢
  have h1 : kOmegaInsert K k (fun i => Units.map (σ : K →* K) (t i)) =
      fun i => Units.map (σ : K →* K) (kOmegaInsert K k t i) := by
    funext i
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
    · simp [kOmegaInsert_apply]
    · simp [kOmegaInsert_apply]
  rw [h1]
  exact kOmega_map_units_mem_leviTorusParam σ ht

theorem kOmega_mem_leviTorusParam_of_eq_off {n : ℕ} {k : Fin n} {J : Finset (Fin n)}
    (hk : k ∉ spSupport J) {s t : Fin n → Kˣ} (hst : ∀ i, i ≠ k → s i = t i)
    (ht : t ∈ leviTorusParam K J) : s ∈ leviTorusParam K J := by
  intro j hj
  have hjk : j ≠ k := fun e => hk (mem_spSupport.2 (Or.inl (e ▸ hj)))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hj1 : (⟨j.val + 1, h⟩ : Fin n) ≠ k := fun e =>
      hk (mem_spSupport.2 (Or.inr ⟨j, hj, by rw [← e]⟩))
    rw [hst j hjk, hst _ hj1]
    exact (ht j hj).1 h
  · rw [hst j hjk]
    exact (ht j hj).2 h

theorem kOmega_leviTorusSp_eq_sup {k : Fin (r + 1)} {J : Finset (Fin (r + 1))}
    (hk : k ∉ spSupport J) :
    leviTorusSp K J = rootTorusSp K k ⊔ (((kOmegaTorusParam k J).map (diagSp K r)).map
      ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    rw [kOmega_diagSp_eq_rootTorusHom_mul k t]
    refine mul_mem (mem_sup_left (rootTorusHom_mem_rootTorusSp k _)) (mem_sup_right ?_)
    refine ⟨diagSp K r (Fin.removeNth k t), ⟨Fin.removeNth k t, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_kOmegaTorusParam]
      refine kOmega_mem_leviTorusParam_of_eq_off hk (fun i hi => ?_) ht
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simp [kOmegaInsert_apply, Fin.removeNth]
    · change ((complSpEquiv k (diagSp K r (Fin.removeNth k t)) : complSp K k) :
        StatedSp (r + 1) K) = _
      rw [kOmega_coe_complSpEquiv_diagSp]
  · refine sup_le (rootTorusSp_le_leviTorusSp hk) ?_
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    change ((complSpEquiv k (diagSp K r t) : complSp K k) : StatedSp (r + 1) K) ∈ _
    rw [kOmega_coe_complSpEquiv_diagSp]
    exact diagSp_mem_leviTorusSp ht

theorem map_fieldSp_kOmegaTorusParam (σ : K ≃+* K) (k : Fin (r + 1))
    (J : Finset (Fin (r + 1))) :
    ((kOmegaTorusParam k J).map (diagSp K r)).map (fieldSp r K σ).toMonoidHom =
      (kOmegaTorusParam k J).map (diagSp K r) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨_, map_units_mem_kOmegaTorusParam σ ht, ?_⟩
    change _ = fieldSp r K σ (diagSp K r t)
    rw [fieldSp_diagSp]
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨diagSp K r (fun i => Units.map (σ.symm : K →* K) (t i)),
      ⟨_, map_units_mem_kOmegaTorusParam σ.symm ht, rfl⟩, ?_⟩
    change fieldSp r K σ (diagSp K r _) = _
    rw [fieldSp_diagSp]
    congr 1
    funext i
    ext
    simp

end Param

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem kOmega_pieceCore_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1))
    (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmegaIota hr hr3 hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {J : Finset (Fin (r + 1))} (hk : k ∉ spSupport J) :
    pieceCore e J = (perfectCore (centralizer ((((kOmegaTorusParam k J).map (diagSp K r)).map
      (kOmegaIota hr hr3 hKc hf) : Subgroup (StatedOmega (StatedQuadPlus (r + 1) K))) :
        Set (StatedOmega (StatedQuadPlus (r + 1) K))))).map
      ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  set P := kOmegaTorusParam (K := K) k J with hP
  set lamG : StatedSp r K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) with hlamG
  have hcomp : ((neighbourCore e k).subtype.comp Φ.toMonoidHom).comp (kOmegaIota hr hr3 hKc hf) =
      lamG.comp (fieldSp r K σ).toMonoidHom := by
    ext1 x
    exact hΦ x
  have hS : ((P.map (diagSp K r)).map (kOmegaIota hr hr3 hKc hf)).map
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
    sup_assoc,
    sup_eq_right.2 hXE]

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
