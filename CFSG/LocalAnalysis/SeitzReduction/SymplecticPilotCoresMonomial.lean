module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective ne_succ')
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono modelToG_map_conj)

section Tori

variable (K : Type) [Field K] {n : ℕ}

@[expose] noncomputable def diagTorusSp (P : Subgroup (Fin n → Kˣ)) : Subgroup (StatedSp n K) :=
  P.map (diagSp K n)

@[expose] def permParam (π : Equiv.Perm (Fin n)) : (Fin n → Kˣ) →* (Fin n → Kˣ) where
  toFun t := t ∘ π.symm
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def planeTorusParam (I : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {t | ∀ i ∈ I, t i = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {t s} ht hs i hi => by
    simp only [Pi.mul_apply, ht i hi, hs i hi, mul_one]
  inv_mem' := fun {t} ht i hi => by
    simp only [Pi.inv_apply, ht i hi, inv_one]

@[expose] noncomputable def planeTorusSp (I : Finset (Fin n)) : Subgroup (StatedSp n K) :=
  diagTorusSp K (planeTorusParam K I)

variable {K}

theorem mem_diagTorusSp {P : Subgroup (Fin n → Kˣ)} {x : StatedSp n K} :
    x ∈ diagTorusSp K P ↔ ∃ t ∈ P, diagSp K n t = x :=
  Iff.rfl

theorem diagSp_mem_diagTorusSp {P : Subgroup (Fin n → Kˣ)} {t : Fin n → Kˣ} (ht : t ∈ P) :
    diagSp K n t ∈ diagTorusSp K P :=
  ⟨t, ht, rfl⟩

theorem diagTorusSp_mono {P Q : Subgroup (Fin n → Kˣ)} (h : P ≤ Q) :
    diagTorusSp K P ≤ diagTorusSp K Q :=
  map_mono h

theorem diagTorusSp_le_range (P : Subgroup (Fin n → Kˣ)) :
    diagTorusSp K P ≤ (diagSp K n).range := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨t, rfl⟩

theorem leviTorusSp_eq_diagTorusSp (J : Finset (Fin n)) :
    leviTorusSp K J = diagTorusSp K (leviTorusParam K J) :=
  rfl

theorem rootTorusSp_eq_diagTorusSp (k : Fin n) :
    rootTorusSp K k = diagTorusSp K (MonoidHom.mulSingle (fun _ : Fin n => Kˣ) k).range := by
  rw [rootTorusSp, rootTorusHom, MonoidHom.range_comp, diagTorusSp]

theorem siegelTorus_eq_diagTorusSp :
    siegelTorus K n = diagTorusSp K (Pi.constMonoidHom (Fin n) Kˣ).range := by
  rw [siegelTorus, MonoidHom.range_comp, diagTorusSp]

theorem coe_permParam (π : Equiv.Perm (Fin n)) (t : Fin n → Kˣ) : permParam K π t = t ∘ π.symm :=
  rfl

theorem mem_planeTorusParam {I : Finset (Fin n)} {t : Fin n → Kˣ} :
    t ∈ planeTorusParam K I ↔ ∀ i ∈ I, t i = 1 :=
  Iff.rfl

theorem planeTorusSp_anti {I N : Finset (Fin n)} (h : I ⊆ N) :
    planeTorusSp K N ≤ planeTorusSp K I :=
  diagTorusSp_mono fun _ ht i hi => ht i (h hi)

theorem rootTorusSp_eq_planeTorusSp (k : Fin n) :
    rootTorusSp K k = planeTorusSp K ({k}ᶜ : Finset (Fin n)) := by
  ext x
  constructor
  · rintro ⟨κ, rfl⟩
    refine ⟨Pi.mulSingle k κ, fun i hi => ?_, rfl⟩
    have hik : i ≠ k := by simpa using hi
    simp [hik]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t k, ?_⟩
    rw [rootTorusHom_apply]
    congr 1
    funext i
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Pi.mulSingle_eq_of_ne hik, ht i (by simpa using hik)]

theorem leviTorusParam_tail_eq (a : ℕ) :
    leviTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  ext t
  rw [mem_leviTorusParam, mem_planeTorusParam]
  constructor
  · intro ht
    have key : ∀ d : ℕ, ∀ j : Fin n, a ≤ j.val → j.val + d + 1 = n → t j = 1 := by
      intro d
      induction d with
      | zero =>
        intro j hj hjn
        exact (ht j (by simpa using hj)).2 (by omega)
      | succ d ih =>
        intro j hj hjn
        have h1 : j.val + 1 < n := by omega
        rw [(ht j (by simpa using hj)).1 h1]
        exact ih ⟨j.val + 1, h1⟩ (by simp; omega) (by simp; omega)
    intro j hj
    have hj' : a ≤ j.val := by simpa using hj
    exact key (n - 1 - j.val) j hj' (by omega)
  · intro ht j hj
    have hj' : a ≤ j.val := by simpa using hj
    refine ⟨fun h => ?_, fun _ => ht j hj⟩
    rw [ht j hj, ht ⟨j.val + 1, h⟩ (by simp; omega)]

theorem leviTorusSp_tail_eq_planeTorusSp (a : ℕ) :
    leviTorusSp K (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeTorusSp K (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  rw [leviTorusSp_eq_diagTorusSp, leviTorusParam_tail_eq, planeTorusSp]

end Tori

section Perm

variable {K : Type} [Field K] {n : ℕ}

theorem conj_permSp_comp_diagSp (π : Equiv.Perm (Fin n)) :
    (MulAut.conj (permSp K π)).toMonoidHom.comp (diagSp K n) =
      (diagSp K n).comp (permParam K π) :=
  MonoidHom.ext fun t => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_permSp_diagSp π t

theorem map_conj_permSp_diagTorusSp (π : Equiv.Perm (Fin n)) (P : Subgroup (Fin n → Kˣ)) :
    (diagTorusSp K P).map (MulAut.conj (permSp K π)).toMonoidHom =
      diagTorusSp K (P.map (permParam K π)) := by
  rw [diagTorusSp, diagTorusSp, Subgroup.map_map, Subgroup.map_map, conj_permSp_comp_diagSp]

theorem map_permParam_planeTorusParam (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    (planeTorusParam K I).map (permParam K π) = planeTorusParam K (I.map π.toEmbedding) := by
  ext t
  rw [mem_map, mem_planeTorusParam]
  constructor
  · rintro ⟨s, hs, rfl⟩ j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    simp only [coe_permParam, Function.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    exact hs i hi
  · intro ht
    refine ⟨t ∘ π, fun i hi => ht (π i) (Finset.mem_map_of_mem _ hi), ?_⟩
    funext j
    simp [coe_permParam]

theorem map_conj_permSp_planeTorusSp (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    (planeTorusSp K I).map (MulAut.conj (permSp K π)).toMonoidHom =
      planeTorusSp K (I.map π.toEmbedding) := by
  rw [planeTorusSp, map_conj_permSp_diagTorusSp, map_permParam_planeTorusParam, planeTorusSp]

end Perm

section TorusCores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

@[expose] noncomputable def torusCore (P : Subgroup (Fin n → Kˣ)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (diagTorusSp K P))

@[expose] noncomputable def planeCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (planeTorusSp K I))

theorem planeCore_def (I : Finset (Fin n)) :
    planeCore e I = centralizerPerfectCore (modelToG e (planeTorusSp K I)) :=
  rfl

theorem pieceCore_eq_torusCore (J : Finset (Fin n)) :
    pieceCore e J = torusCore e (leviTorusParam K J) :=
  rfl

theorem planeCore_eq_torusCore (I : Finset (Fin n)) :
    planeCore e I = torusCore e (planeTorusParam K I) :=
  rfl

theorem neighbourCore_eq_torusCore (k : Fin n) :
    neighbourCore e k = torusCore e (MonoidHom.mulSingle (fun _ : Fin n => Kˣ) k).range := by
  rw [neighbourCore_def, torusCore, rootTorusSp_eq_diagTorusSp]

theorem siegelCore_eq_torusCore :
    siegelCore e = torusCore e (Pi.constMonoidHom (Fin n) Kˣ).range := by
  rw [siegelCore_def, torusCore, siegelTorus_eq_diagTorusSp]

theorem neighbourCore_eq_planeCore (k : Fin n) :
    neighbourCore e k = planeCore e ({k}ᶜ : Finset (Fin n)) := by
  rw [neighbourCore_def, planeCore_def, rootTorusSp_eq_planeTorusSp]

theorem pieceCore_tail_eq (a : ℕ) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val) =
      planeCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val) := by
  rw [pieceCore_def, planeCore_def, leviTorusSp_tail_eq_planeTorusSp]

theorem planeCore_mono {I N : Finset (Fin n)} (h : I ⊆ N) : planeCore e I ≤ planeCore e N :=
  centralizerPerfectCore_anti (modelToG_mono e (planeTorusSp_anti h))

theorem planeCore_le_neighbourCore {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    planeCore e I ≤ neighbourCore e k := by
  rw [neighbourCore_eq_planeCore]
  exact planeCore_mono e fun i hi => by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun h => hk (h ▸ hi)

theorem modelToG_le_planeCore {I : Finset (Fin n)} {A : Subgroup (StatedSp n K)}
    (hA : A ≤ centralizer (planeTorusSp K I : Set (StatedSp n K))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ planeCore e I :=
  UnitaryPilot.modelToG_le_centralizerPerfectCore e hA hperf

theorem le_normalizer_planeCore {t : G} (ht : t ∈ centralizer (L : Set G)) (I : Finset (Fin n)) :
    t ∈ normalizer (planeCore e I : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem symm_mem_normalizer_planeCore {I : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ normalizer (planeTorusSp K I : Set (StatedSp n K))) :
    ((e.symm x : L) : G) ∈ normalizer (planeCore e I : Set G) :=
  UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e hx

theorem diagSp_mem_normalizer_planeCore (I : Finset (Fin n)) (s : Fin n → Kˣ) :
    ((e.symm (diagSp K n s) : L) : G) ∈ normalizer (planeCore e I : Set G) :=
  symm_mem_normalizer_planeCore e
    (centralizer_le_normalizer _ (diagSp_mem_centralizer_of_le (diagTorusSp_le_range _) s))

end TorusCores

section Pair

variable {K : Type} [Field K] {n : ℕ}

variable (K) in
@[expose] def pairTorusParam (a b : Fin n) : Subgroup (Fin n → Kˣ) where
  carrier := {t | t a = t b}
  one_mem' := rfl
  mul_mem' := fun {t s} ht hs => by
    change t a * s a = t b * s b
    rw [ht.out, hs.out]
  inv_mem' := fun {t} ht => by
    change (t a)⁻¹ = (t b)⁻¹
    rw [ht.out]

theorem mem_pairTorusParam {a b : Fin n} {t : Fin n → Kˣ} :
    t ∈ pairTorusParam K a b ↔ t a = t b :=
  Iff.rfl

theorem leviTorusParam_singleton_of_lt {j : Fin n} (h : j.val + 1 < n) :
    leviTorusParam K {j} = pairTorusParam K j ⟨j.val + 1, h⟩ := by
  ext t
  rw [mem_leviTorusParam, mem_pairTorusParam]
  constructor
  · intro ht
    exact (ht j (Finset.mem_singleton_self j)).1 h
  · intro ht i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨fun _ => ht, fun h' => absurd h' (by omega)⟩

theorem map_permParam_pairTorusParam (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    (pairTorusParam K a b).map (permParam K π) = pairTorusParam K (π a) (π b) := by
  ext t
  rw [mem_map, mem_pairTorusParam]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_pairTorusParam] at hs
    simp only [coe_permParam, Function.comp_apply, Equiv.symm_apply_apply]
    exact hs
  · intro ht
    refine ⟨t ∘ π, ?_, ?_⟩
    · rw [mem_pairTorusParam]
      exact ht
    · funext j
      simp [coe_permParam]

end Pair

section Transport

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* StatedSp n K)

theorem planeCore_eq_perfectCore_inf {X : Subgroup G} {I : Finset (Fin n)}
    (hX : X ≤ modelToG e (planeTorusSp K I)) :
    planeCore e I = perfectCore (centralizerPerfectCore X ⊓
      centralizer (modelToG e (planeTorusSp K I) : Set G)) :=
  UnitaryPilot.centralizerPerfectCore_modelToG_eq_perfectCore_inf e hX

theorem planeCore_eq {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    planeCore e I = perfectCore (neighbourCore e k ⊓
      centralizer (modelToG e (planeTorusSp K I) : Set G)) := by
  refine planeCore_eq_perfectCore_inf e (modelToG_mono e ?_)
  rw [rootTorusSp_eq_planeTorusSp]
  exact planeTorusSp_anti fun i hi => by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun h => hk (h ▸ hi)

theorem torusCore_map_permParam (π : Equiv.Perm (Fin n)) (P : Subgroup (Fin n → Kˣ)) :
    torusCore e (P.map (permParam K π)) =
      (torusCore e P).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [torusCore, torusCore, ← map_conj_permSp_diagTorusSp,
    UnitaryPilot.centralizerPerfectCore_modelToG_map_conj]

theorem planeCore_map_eq (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    planeCore e (I.map π.toEmbedding) =
      (planeCore e I).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [planeCore_eq_torusCore, planeCore_eq_torusCore, ← map_permParam_planeTorusParam,
    torusCore_map_permParam]

theorem neighbourCore_map_eq (π : Equiv.Perm (Fin n)) (k : Fin n) :
    neighbourCore e (π k) =
      (neighbourCore e k).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [neighbourCore_def, neighbourCore_def, ← map_conj_permSp_rootTorusSp,
    UnitaryPilot.centralizerPerfectCore_modelToG_map_conj]

omit [Finite G] in
theorem modelToG_complSp_map_eq (π : Equiv.Perm (Fin n)) (k : Fin n) :
    modelToG e (complSp K (π k)) =
      (modelToG e (complSp K k)).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  rw [← map_conj_permSp_complSp, modelToG_map_conj]

theorem siegelCore_map_eq (π : Equiv.Perm (Fin n)) :
    siegelCore e =
      (siegelCore e).map (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom := by
  conv_lhs => rw [siegelCore_def, ← map_conj_permSp_siegelTorus π]
  rw [UnitaryPilot.centralizerPerfectCore_modelToG_map_conj, siegelCore_def]

theorem exists_planeCore_map_conj (π : Equiv.Perm (Fin n)) :
    ∃ w ∈ L, (∀ I : Finset (Fin n),
        planeCore e (I.map π.toEmbedding) = (planeCore e I).map (MulAut.conj w).toMonoidHom) ∧
      (∀ k : Fin n,
        neighbourCore e (π k) = (neighbourCore e k).map (MulAut.conj w).toMonoidHom ∧
        modelToG e (complSp K (π k)) =
          (modelToG e (complSp K k)).map (MulAut.conj w).toMonoidHom) ∧
      siegelCore e = (siegelCore e).map (MulAut.conj w).toMonoidHom :=
  ⟨((e.symm (permSp K π) : L) : G), (e.symm (permSp K π)).2, planeCore_map_eq e π,
    fun k => ⟨neighbourCore_map_eq e π k, modelToG_complSp_map_eq e π k⟩, siegelCore_map_eq e π⟩

theorem exists_neighbourCore_eq_map_conj (k l : Fin n) :
    ∃ w ∈ L, neighbourCore e l = (neighbourCore e k).map (MulAut.conj w).toMonoidHom ∧
      modelToG e (complSp K l) = (modelToG e (complSp K k)).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨w, hw, -, hN, -⟩ := exists_planeCore_map_conj e (Equiv.swap k l)
  refine ⟨w, hw, ?_⟩
  simpa only [Equiv.swap_apply_left] using hN k

theorem exists_pieceCore_short_eq_map_conj {j l : Fin n} (hj : j.val + 1 < n)
    (hl : l.val + 1 < n) :
    ∃ w ∈ L, pieceCore e {l} = (pieceCore e {j}).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨π, hπj, hπj'⟩ := LinearPilot.exists_perm_apply_eq_apply_eq (ne_succ' hj) (ne_succ' hl)
  refine ⟨((e.symm (permSp K π) : L) : G), (e.symm (permSp K π)).2, ?_⟩
  rw [pieceCore_eq_torusCore, pieceCore_eq_torusCore, leviTorusParam_singleton_of_lt hj,
    leviTorusParam_singleton_of_lt hl, ← torusCore_map_permParam, map_permParam_pairTorusParam,
    hπj, hπj']

end Transport

end CFSG.SeitzReduction.SymplecticPilot
