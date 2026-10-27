module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreFreeInvolutionLayer
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.QuasithinUnique.ComponentEmbedding

open Subgroup CFSG.LocalCores CFSG.ComponentClassification OuterAutomorphisms
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem inv_mul_mul_mem_of_mem_normalizer {S : Subgroup H} {t : H}
    (ht : t ∈ normalizer (S : Set H)) {k : H} (hk : k ∈ S) : t⁻¹ * k * t ∈ S := by
  have := (mem_normalizer_iff.1 ((normalizer (S : Set H)).inv_mem ht) k).1 hk
  simpa using this

theorem layerMul_fixed_coord_commute {t : H}
    (ht : ∀ K : ComponentIndex H, t ∈ normalizer (K.1 : Set H)) {a : ∀ K : ComponentIndex H, K.1}
    (hfix : t⁻¹ * layerMul H a * t = layerMul H a) (K : ComponentIndex H) :
    ∀ k ∈ K.1, Commute k ((a K : H)⁻¹ * (t⁻¹ * (a K : H) * t)) := by
  intro k hk
  set x' : H := layerMul H (Function.update a K 1) with hx'
  have h1 : layerMul H a = (a K : H) * x' := layerMul_eq_mul_update a K
  have hcomm1 : ∀ k ∈ K.1, Commute k x' := fun k hk => commute_layerMul_update a K hk
  have hcomm2 : ∀ k ∈ K.1, Commute k (t⁻¹ * x' * t) := by
    intro k hk
    have hk' : t * k * t⁻¹ ∈ K.1 := (mem_normalizer_iff.1 (ht K) k).1 hk
    have h := (hcomm1 _ hk').eq
    calc k * (t⁻¹ * x' * t) = t⁻¹ * ((t * k * t⁻¹) * x') * t := by group
      _ = t⁻¹ * (x' * (t * k * t⁻¹)) * t := by rw [h]
      _ = (t⁻¹ * x' * t) * k := by group
  have h2 : (t⁻¹ * (a K : H) * t) * (t⁻¹ * x' * t) = (a K : H) * x' := by
    calc _ = t⁻¹ * ((a K : H) * x') * t := by group
      _ = _ := by rw [← h1]; exact hfix
  have hu : (a K : H)⁻¹ * (t⁻¹ * (a K : H) * t) = x' * (t⁻¹ * x' * t)⁻¹ := by
    calc (a K : H)⁻¹ * (t⁻¹ * (a K : H) * t)
        = (a K : H)⁻¹ * ((t⁻¹ * (a K : H) * t) * (t⁻¹ * x' * t)) * (t⁻¹ * x' * t)⁻¹ := by group
      _ = (a K : H)⁻¹ * ((a K : H) * x') * (t⁻¹ * x' * t)⁻¹ := by rw [h2]
      _ = x' * (t⁻¹ * x' * t)⁻¹ := by group
  rw [hu]
  exact (hcomm1 k hk).mul_right (hcomm2 k hk).inv_right

omit [Finite H] in
theorem commutatorElement_mul_mul_of_commute {x y u w : H} (hu : Commute u y) (hw : Commute x w)
    (huw : Commute u w) : ⁅x * u, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, (hw.mul_left huw).commutator_eq,
    commutatorElement_mul_left_eq_conj_mul, hu.commutator_eq]
  group

theorem commutator_layerMul_mem {t : H}
    (ht : ∀ K : ComponentIndex H, t ∈ normalizer (K.1 : Set H)) {a b : ∀ K : ComponentIndex H, K.1}
    (ha : t⁻¹ * layerMul H a * t = layerMul H a) (hb : t⁻¹ * layerMul H b * t = layerMul H b) :
    ⁅layerMul H a, layerMul H b⁆ ∈
      ⨆ K : ComponentIndex H, (K.1 ⊓ centralizer ({t} : Set H)) := by
  rw [← map_commutatorElement (layerMul H) a b]
  refine layerMul_mem _ fun K => ?_
  have hc : (((⁅a, b⁆ : ∀ K : ComponentIndex H, K.1) K : K.1) : H) =
      ⁅(a K : H), (b K : H)⁆ := by
    simp [commutatorElement_def]
  refine mem_iSup_of_mem K (mem_inf.2 ⟨(⁅a, b⁆ K).2, ?_⟩)
  rw [hc, mem_centralizer_singleton_iff]
  have hu := layerMul_fixed_coord_commute ht ha K
  have hw := layerMul_fixed_coord_commute ht hb K
  set u : H := (a K : H)⁻¹ * (t⁻¹ * (a K : H) * t) with hu_def
  set w : H := (b K : H)⁻¹ * (t⁻¹ * (b K : H) * t) with hw_def
  have hwK : w ∈ K.1 :=
    K.1.mul_mem (K.1.inv_mem (b K).2)
      (inv_mul_mul_mem_of_mem_normalizer (ht K) (b K).2)
  have hak : t⁻¹ * (a K : H) * t = (a K : H) * u := by rw [hu_def]; group
  have hbk : t⁻¹ * (b K : H) * t = (b K : H) * w := by rw [hw_def]; group
  have hconj : t⁻¹ * ⁅(a K : H), (b K : H)⁆ * t =
      ⁅(a K : H) * u, (b K : H) * w⁆ := by
    rw [← hak, ← hbk]
    have := conjugate_commutatorElement (a K : H) (b K : H) t⁻¹
    rwa [inv_inv] at this
  have hcomm : ⁅(a K : H) * u, (b K : H) * w⁆ = ⁅(a K : H), (b K : H)⁆ :=
    commutatorElement_mul_mul_of_commute (hu _ (b K).2).symm (hw _ (a K).2) (hu _ hwK).symm
  have hfix : t⁻¹ * ⁅(a K : H), (b K : H)⁆ * t = ⁅(a K : H), (b K : H)⁆ := hconj.trans hcomm
  calc ⁅(a K : H), (b K : H)⁆ * t = t * (t⁻¹ * ⁅(a K : H), (b K : H)⁆ * t) := by group
    _ = t * ⁅(a K : H), (b K : H)⁆ := by rw [hfix]

theorem commutator_layer_inf_le {t : H}
    (ht : ∀ K : Subgroup H, CFSG.IsComponent K → t ∈ normalizer (K : Set H)) :
    ⁅CFSG.layer H ⊓ centralizer ({t} : Set H), CFSG.layer H ⊓ centralizer ({t} : Set H)⁆ ≤
      ⨆ K : ComponentIndex H, (K.1 ⊓ centralizer ({t} : Set H)) := by
  rw [commutator_le]
  rintro x ⟨hxE, hxC⟩ y ⟨hyE, hyC⟩
  obtain ⟨a, rfl⟩ := exists_layerMul_eq hxE
  obtain ⟨b, rfl⟩ := exists_layerMul_eq hyE
  have hfix : ∀ z : H, z ∈ centralizer ({t} : Set H) → t⁻¹ * z * t = z := by
    intro z hz
    rw [mem_centralizer_singleton_iff] at hz
    rw [mul_assoc, hz, inv_mul_cancel_left]
  exact commutator_layerMul_mem (fun K => ht K.1 K.2) (hfix _ hxC) (hfix _ hyC)

theorem exists_component_le_of_le_layer {t : H}
    (ht : ∀ K : Subgroup H, CFSG.IsComponent K → t ∈ normalizer (K : Set H))
    {C : Subgroup H} (hC : C = centralizer ({t} : Set H)) {L : Subgroup C}
    (hL : CFSG.IsComponent L) (hLE : L.map C.subtype ≤ CFSG.layer H) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ L.map C.subtype ≤ K := by
  by_contra hno
  set Lg : Subgroup H := L.map C.subtype with hLg
  have hno' : ∀ K : Subgroup H, CFSG.IsComponent K → ¬ Lg ≤ K := fun K hK hle =>
    hno ⟨K, hK, hle⟩
  have hperf : ⁅Lg, Lg⁆ = Lg := by
    rw [hLg, ← Subgroup.map_commutator, isPerfect_iff.1 hL.1.1]
  have hLgD : Lg ≤ ⨆ K : ComponentIndex H, (K.1 ⊓ C) := by
    have hLgC : Lg ≤ C := map_subtype_le L
    have hD := commutator_layer_inf_le ht
    rw [← hC] at hD
    calc Lg = ⁅Lg, Lg⁆ := hperf.symm
      _ ≤ ⁅CFSG.layer H ⊓ C, CFSG.layer H ⊓ C⁆ :=
          commutator_mono (le_inf hLE hLgC) (le_inf hLE hLgC)
      _ ≤ _ := hD
  have hcomm : ∀ K : ComponentIndex H, ∀ x ∈ Lg, ∀ y ∈ K.1 ⊓ C, y * x = x * y := by
    intro K x hx y hy
    rcases component_subnormal_subgroup (G := C) hL (U := K.1.subgroupOf C)
      K.2.2.subgroupOf with h | h
    · refine absurd ?_ (hno' K.1 K.2)
      have h' := map_mono (f := C.subtype) h
      rw [subgroupOf_map_subtype] at h'
      exact h'.trans inf_le_left
    · have h' := congrArg (map C.subtype) h
      rw [Subgroup.map_commutator, subgroupOf_map_subtype, Subgroup.map_bot] at h'
      exact mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h' hx) y hy
  have hab : ∀ x ∈ Lg, ∀ y ∈ Lg, y * x = x * y := by
    intro x hx y hy
    have hD : (⨆ K : ComponentIndex H, (K.1 ⊓ C)) ≤ centralizer ({x} : Set H) :=
      iSup_le fun K y hy => mem_centralizer_singleton_iff.2 (hcomm K x hx y hy)
    exact mem_centralizer_singleton_iff.1 (hD (hLgD hy))
  have hLgbot : Lg = ⊥ := by
    rw [← hperf, commutator_eq_bot_iff_le_centralizer.2]
    exact fun x hx => mem_centralizer_iff.2 fun y hy => hab x hx y hy
  have hLbot : L = ⊥ := (Subgroup.map_eq_bot_iff_of_injective L C.subtype_injective).1 hLgbot
  have : Nontrivial L := isQuasisimple_nontrivial hL.1
  exact (nontrivial_iff_ne_bot L).1 this hLbot

theorem odd_core_free_involution_Schreier_component_embedding
    (hcore : CFSG.oddCore H = ⊥) {t : H} (ht : orderOf t = 2)
    (htK : ∀ K : Subgroup H, CFSG.IsComponent K → t ∈ normalizer (K : Set H))
    (hout : ∀ K : Subgroup H, CFSG.IsComponent K → Group.IsSolvable (Outer (K ⧸ center K)))
    {L : Subgroup (centralizer ({t} : Set H))} (hL : CFSG.IsComponent L) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ L.map (centralizer ({t} : Set H)).subtype ≤ K := by
  have hcore' : CFSG.pPrimeCore 2 H = ⊥ := by
    rw [← EscapingLocal.oddCore_eq_pPrimeCore]
    exact hcore
  exact exists_component_le_of_le_layer htK rfl hL
    (LocalAnalysis.ComponentInitial.odd_core_free_Schreier_involution_component_enters_layer
      hcore' ht hout L hL)

theorem odd_core_free_involution_Schreier_component_embedding_of_eq
    (hcore : CFSG.oddCore H = ⊥) {t : H} (ht : orderOf t = 2)
    (htK : ∀ K : Subgroup H, CFSG.IsComponent K → t ∈ normalizer (K : Set H))
    (hout : ∀ K : Subgroup H, CFSG.IsComponent K → Group.IsSolvable (Outer (K ⧸ center K)))
    {C : Subgroup H} (hC : C = centralizer ({t} : Set H)) {L : Subgroup C}
    (hL : CFSG.IsComponent L) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ L.map C.subtype ≤ K := by
  subst hC
  exact odd_core_free_involution_Schreier_component_embedding hcore ht htK hout hL

end CFSG.QuasithinUnique.ComponentEmbedding
