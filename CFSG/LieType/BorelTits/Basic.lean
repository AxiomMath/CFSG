module

public import Mathlib
public import CFSG.Open.Defs

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

universe u v

section PCore

variable {G : Type u} [Group G] (r : ℕ)

theorem pCore_normal : (pCore r G).Normal := by
  rw [CFSG.pCore_eq_iSup]
  rw [← sSup_range]
  refine Subgroup.sSup_normal _ ?_
  rintro _ ⟨N, rfl⟩
  change (⨆ (_ : N.Normal), ⨆ (_ : IsPGroup r N), N).Normal
  rw [← sSup_range]
  refine Subgroup.sSup_normal _ ?_
  rintro _ ⟨hN, rfl⟩
  change (⨆ (_ : IsPGroup r N), N).Normal
  rw [← sSup_range]
  refine Subgroup.sSup_normal _ ?_
  rintro _ ⟨_, rfl⟩
  exact hN

theorem le_pCore {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup r N) : N ≤ pCore r G :=
  le_sSup ⟨hN, hp⟩

theorem pCore_isPGroup [Finite G] [Fact r.Prime] : IsPGroup r (pCore r G) := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r G))
  have hle : pCore r G ≤ (P : Subgroup G) := by
    rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_
    exact hp.le_sylow_of_normal P
  exact P.isPGroup'.to_le hle

theorem map_pCore_le {H : Type v} [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (pCore r G).map f ≤ pCore r H := by
  rw [CFSG.pCore_eq_iSup r G, CFSG.pCore_eq_iSup r H]
  rw [Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hN => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hp => ?_
  exact le_iSup_of_le (N.map f) (le_iSup_of_le (hN.map f hf) (le_iSup_of_le (hp.map f) le_rfl))

theorem map_pCore_mulEquiv {H : Type v} [Group H] (e : G ≃* H) :
    (pCore r G).map e.toMonoidHom = pCore r H := by
  refine le_antisymm (map_pCore_le r e.toMonoidHom e.surjective) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom)
    (map_pCore_le r e.symm.toMonoidHom e.symm.surjective)
  rw [Subgroup.map_map] at h
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x; simp
  rwa [hid, Subgroup.map_id] at h

theorem pCore_characteristic : (pCore r G).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun φ => ?_
  exact map_pCore_mulEquiv r φ

theorem pCoreOf_le (H : Subgroup G) : pCoreOf r H ≤ H :=
  Subgroup.map_subtype_le _

theorem pCoreOf_isPGroup [Finite G] [Fact r.Prime] (H : Subgroup G) :
    IsPGroup r (pCoreOf r H) :=
  (pCore_isPGroup (G := H) r).map H.subtype

theorem le_pCoreOf {N H : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hp : IsPGroup r N) : N ≤ pCoreOf r H := by
  have hsub : IsPGroup r (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ pCore r H := le_pCore r hN hsub
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

theorem le_pCoreOf_of_le_normalizer {N H : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) (hp : IsPGroup r N) : N ≤ pCoreOf r H := by
  refine le_pCoreOf r hNH ?_ hp
  refine ⟨fun x hx h => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hnorm h.2) x).mp hx
  simpa using this

theorem normalizer_le_normalizer_map_of_characteristic {H : Subgroup G} (K : Subgroup H)
    [hK : K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ x ∈ K.map H.subtype,
      g * x * g⁻¹ ∈ K.map H.subtype := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : H ≃* H := H.normalizerMonoidHom ⟨g, hg⟩
    have hfix := Subgroup.characteristic_iff_map_eq.mp hK φ
    have hyK : φ y ∈ K := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    refine Subgroup.mem_map.mpr ⟨φ y, hyK, ?_⟩
    exact H.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem hg
    have := key g⁻¹ hginv _ hx
    simpa [mul_assoc] using this

theorem le_normalizer_pCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf r H : Set G) := by
  have : (pCore r H).Characteristic := pCore_characteristic r
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_map_of_characteristic _)

theorem normalizer_le_normalizer_pCoreOf (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (pCoreOf r H : Set G) := by
  have : (pCore r H).Characteristic := pCore_characteristic r
  exact normalizer_le_normalizer_map_of_characteristic _

theorem le_pCoreOf_normalizer [Finite G] (U : Subgroup G) (hU : IsPGroup r U) :
    U ≤ pCoreOf r (Subgroup.normalizer (U : Set G)) :=
  le_pCoreOf_of_le_normalizer r Subgroup.le_normalizer le_rfl hU

theorem pCoreOf_map_mulEquiv {H' : Type v} [Group H'] (e : G ≃* H') (H : Subgroup G) :
    pCoreOf r (H.map e.toMonoidHom) = (pCoreOf r H).map e.toMonoidHom := by
  unfold pCoreOf
  let φ : H ≃* H.map e.toMonoidHom := e.subgroupMap H
  rw [← map_pCore_mulEquiv r φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

end PCore

variable {X : Type u} [Group X]

@[expose] def Conclusion (r : ℕ) (U : Subgroup X) : Prop :=
  ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
    Subgroup.normalizer (U : Set X) ≤ P ∧
    pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ pCoreOf r P ∧
    U ≤ pCoreOf r P ∧
    Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P

variable (X) in
@[expose] def Holds (r : ℕ) : Prop :=
  ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup r U → Conclusion r U

theorem conclusion_of_core [Finite X] (r : ℕ) (U : Subgroup X) (hU : IsPGroup r U)
    (S : Sylow r X) (P : Subgroup X) (hP : P ≠ ⊤)
    (hN : Subgroup.normalizer (U : Set X) ≤ P)
    (hcore : pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ pCoreOf r P)
    (hS : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) : Conclusion r U :=
  ⟨S, P, hP, hN, hcore, (le_pCoreOf_normalizer r U hU).trans hcore, hS⟩

theorem Conclusion.map_mulEquiv {Y : Type v} [Group Y] [Finite X] {r : ℕ} [Fact r.Prime]
    (e : X ≃* Y) {U : Subgroup X} (h : Conclusion r U) :
    Conclusion r (U.map e.toMonoidHom) := by
  obtain ⟨S, P, hP, hN, hcore, hU, hS⟩ := h
  have hmap : ∀ A B : Subgroup X, A ≤ B → A.map e.toMonoidHom ≤ B.map e.toMonoidHom :=
    fun A B h => Subgroup.map_mono h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨Sylow.mapSurjective hsurj S, P.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    apply hP
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by ext x; simp
    rw [hid, Subgroup.map_id] at this
    rw [this]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact hmap _ _ hN
  · rw [← Subgroup.map_equiv_normalizer_eq, pCoreOf_map_mulEquiv, pCoreOf_map_mulEquiv]
    exact hmap _ _ hcore
  · rw [pCoreOf_map_mulEquiv]
    exact hmap _ _ hU
  · rw [Sylow.coe_mapSurjective]
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact hmap _ _ hS

theorem Holds.of_mulEquiv {Y : Type v} [Group Y] [Finite X] {r : ℕ} [Fact r.Prime]
    (e : X ≃* Y) (h : Holds X r) : Holds Y r := by
  intro V hV hVp
  have hVeq : (V.map e.symm.toMonoidHom).map e.toMonoidHom = V := by
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
    rw [hid, Subgroup.map_id]
  have hne : V.map e.symm.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVeq, hbot, Subgroup.map_bot]
  have := (h _ hne (hVp.map e.symm.toMonoidHom)).map_mulEquiv e
  rwa [hVeq] at this

end CFSG.LieType.BorelTits
