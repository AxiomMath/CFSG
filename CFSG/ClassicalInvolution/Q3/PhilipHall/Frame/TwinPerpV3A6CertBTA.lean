module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBTri
public import Certificates.Certificate517533

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.EvenSmallLie.OmegaEight Certificates.AE6CertB

theorem word_append' (a b : List (Fin 8)) : ae6Word (a ++ b) = ae6Word a * ae6Word b := by
  simp [ae6Word, List.prod_append]

theorem word_flatMap (F : Fin 8 → List (Fin 8)) :
    ∀ w : List (Fin 8), ae6Word (w.flatMap F) = (w.map fun c => ae6Word (F c)).prod
  | [] => by simp [ae6Word]
  | c :: w => by
    rw [List.flatMap_cons, word_append', word_flatMap F w, List.map_cons, List.prod_cons]

theorem rep_flat (e : Fin 3) (j : Fin 6) (w : List (Fin 8)) :
    ae6TriRep e j w = w.flatMap fun c => ae6TriRep e j [c] := by
  obtain ⟨j, hj⟩ := j
  interval_cases j
  · change w = w.flatMap fun c => [c]
    simp
  · change ae6DeltaW _ w = w.flatMap fun c => ae6DeltaW _ [c]
    simp [ae6DeltaW]
  · change ae6DeltaW _ w = w.flatMap fun c => ae6DeltaW _ [c]
    simp [ae6DeltaW]
  · change ae6DeltaW _ (ae6DeltaW _ w) = w.flatMap fun c => ae6DeltaW _ (ae6DeltaW _ [c])
    simp [ae6DeltaW, List.flatMap_assoc]
  · change ae6DeltaW _ (ae6DeltaW _ w) = w.flatMap fun c => ae6DeltaW _ (ae6DeltaW _ [c])
    simp [ae6DeltaW, List.flatMap_assoc]
  · change ae6DeltaW _ (ae6DeltaW _ (ae6DeltaW _ w)) =
      w.flatMap fun c => ae6DeltaW _ (ae6DeltaW _ (ae6DeltaW _ [c]))
    simp [ae6DeltaW, List.flatMap_assoc]

theorem gen0_letters : ∀ i : Fin 6, ∀ c ∈ ae6TriGen₀ i, c ∈ ae6EdgeLetters 0 1 := by decide

theorem gen_eq0 : ∀ i : Fin 6, ae6TriGen 0 i = ae6TriGen₀ i := by decide

section TA


theorem K0_le_E0 : ae6ModelK ≤ (ae6LetterSub ↑(ae6EdgeLetters 0 1)) := by
  rw [ae6ModelK, Subgroup.closure_le]
  have h1 : ∀ i ∈ ([2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : List (Fin 8)),
      i ∈ ae6EdgeLetters 0 1 := by
    decide
  have h2 : ∀ i ∈ ([0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : List (Fin 8)),
      i ∈ ae6EdgeLetters 0 1 := by
    decide
  rintro _ (rfl | rfl)
  · exact ae6Word_mem fun i hi => Finset.mem_coe.mpr (h1 i hi)
  · exact ae6Word_mem fun i hi => Finset.mem_coe.mpr (h2 i hi)

theorem quat0_le {z : AE6Om} (hz : z ∈ Certificates.ae6TriQuat0) :
    z ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1) := by
  obtain ⟨_, ⟨g, hg, rfl⟩, hzJ, -⟩ := hz
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (K0_le_E0 (mem_conjSub_iff.mp hzJ)))
    (Subgroup.inv_mem _ hg)
  rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this

theorem quat0_eq : ae6EdgeQuat (ae6EdgeK 0) (ae6EdgeL 0) = Certificates.ae6TriQuat0 := by
  unfold ae6EdgeQuat Certificates.ae6TriQuat0
  rw [edge_model_eq 0]
  rfl

theorem stab_iff {a : AE6Om} (ha : a ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1)) :
    a ∈ Certificates.ae6TriStab 2 ↔ a ∈ ae6ModelM := by
  rw [M_eq_edge_stab 0, Subgroup.mem_inf, stabB_eq]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

theorem gen0_mem (i : Fin 6) : ae6Word (ae6TriGen₀ i) ∈ (ae6LetterSub ↑(ae6EdgeLetters 0 1)) :=
  ae6Word_mem fun c hc => Finset.mem_coe.mpr (gen0_letters i c hc)

theorem ta_of (e : Fin 3) (φ : AE6Om ≃* AE6Om) (π : Fin 6 → Fin 6)
    (hQ : ∀ z, z ∈ Certificates.ae6TriQuat0 ↔ φ z ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))
    (hM : ∀ a, a ∈ ae6ModelM ↔ φ a ∈ ae6ModelM)
    (hG : ∀ i, φ (ae6Word (ae6TriGen₀ i)) = ae6Word (ae6TriGen e i))
    (hR : ∀ j i, φ (ae6Word (ae6TriRep 0 j (ae6TriGen₀ i))) =
      ae6Word (ae6TriRep e (π j) (ae6TriGen e i))) :
    (∀ i, ae6Word (ae6TriGen e i) ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) ∧
    ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) →
      (∀ u ∈ ae6TriProf,
        orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen e i)).prod ∧
        ((u.map y).prod ∈ ae6ModelM ↔ (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6ModelM) ∧
        ((u.map y).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) ↔
          (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))) →
      ∃ m ∈ ae6ModelM, ∃ j : Fin 6,
        ∀ i, y i = m * ae6Word (ae6TriRep e j (ae6TriGen e i)) * m⁻¹ := by
  obtain ⟨⟨hgen, hsearch⟩, -, -⟩ := Certificates.certificate517533
  refine ⟨fun i => by rw [← hG]; exact (hQ _).1 (hgen i), ?_⟩
  intro y hy hprof
  have hy' : ∀ i, φ.symm (y i) ∈ Certificates.ae6TriQuat0 := fun i => by
    rw [hQ, MulEquiv.apply_symm_apply]
    exact hy i
  have hord : ∀ a : AE6Om, orderOf (φ a) = orderOf a := fun a =>
    orderOf_injective φ.toMonoidHom φ.injective a
  have hP : ∀ u : List (Fin 6), φ (u.map fun i => φ.symm (y i)).prod = (u.map y).prod := by
    intro u
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => MulEquiv.apply_symm_apply φ (y i)
  have hPG : ∀ u : List (Fin 6),
      φ (u.map fun i => ae6Word (ae6TriGen₀ i)).prod =
        (u.map fun i => ae6Word (ae6TriGen e i)).prod := by
    intro u
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => hG i
  have hE : ∀ u : List (Fin 6),
      (u.map fun i => φ.symm (y i)).prod ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1) := fun u =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact quat0_le (hy' i)
  have hEG : ∀ u : List (Fin 6),
      (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1) := fun u =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact gen0_mem i
  obtain ⟨m, hm, j, hj⟩ := hsearch (fun i => φ.symm (y i)) hy' fun u hu => by
    obtain ⟨h1, h2, h3⟩ := hprof u hu
    refine ⟨?_, ?_, ?_⟩
    · rw [← hord (u.map fun i => φ.symm (y i)).prod, hP, h1, ← hPG, hord]
    · rw [stab_iff (hE u), stab_iff (hEG u), hM (u.map fun i => φ.symm (y i)).prod,
        hM (u.map fun i => ae6Word (ae6TriGen₀ i)).prod, hP, hPG]
      exact h2
    · rw [hQ (u.map fun i => φ.symm (y i)).prod, hQ (u.map fun i => ae6Word (ae6TriGen₀ i)).prod,
        hP, hPG]
      exact h3
  have hm' : m ∈ ae6ModelM := by
    rw [tri_TM_M]
    exact hm
  refine ⟨φ m, (hM m).1 hm', π j, fun i => ?_⟩
  have h := congrArg φ (hj i)
  rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hR] at h
  exact h

theorem mLetters_image (e : Fin 3) : ae6MLetters.image (ae6EdgeMap e) = ae6MLetters := by
  revert e
  decide

theorem edgeC_letters : ∀ e : Fin 3, ∀ i ∈ Certificates.ae6TriEdgeC e,
    i ∈ ae6EdgeLetters (triEK e) (triEL2 e) := by
  decide

theorem ta_succ (e : Fin 3) (he : e ≠ 0) :
    (∀ i, ae6Word (ae6TriGen e i) ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) ∧
    ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) →
      (∀ u ∈ ae6TriProf,
        orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen e i)).prod ∧
        ((u.map y).prod ∈ ae6ModelM ↔ (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6ModelM) ∧
        ((u.map y).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) ↔
          (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))) →
      ∃ m ∈ ae6ModelM, ∃ j : Fin 6,
        ∀ i, y i = m * ae6Word (ae6TriRep e j (ae6TriGen e i)) * m⁻¹ := by
  obtain ⟨-, hrep, hk⟩ := Certificates.certificate517533
  obtain ⟨x, τ, hx, hy⟩ := conj_edge e
  have hw := conjAut_word hx hy
  have hL := map_letterSub_conj hx hy
  have hC := card_map_conj hx hy
  generalize conjAut hx hy = φ at hw hL hC
  have hmap : ∀ (H : Subgroup AE6Om) (a : AE6Om), φ a ∈ H.map φ.toMonoidHom ↔ a ∈ H := fun H a =>
    Subgroup.mem_map_iff_mem φ.injective
  have hEm : (ae6LetterSub ↑(ae6EdgeLetters 0 1)).map φ.toMonoidHom =
      ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) := by
    rw [hL, edgeLetters_image]
  have hE : ∀ g, g ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1) ↔
      φ g ∈ ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) := fun g => by
    rw [← hEm, hmap]
  have hM : ∀ a, a ∈ ae6ModelM ↔ φ a ∈ ae6ModelM := fun a => by
    rw [tri_TM_M, ← hmap, hL, mLetters_image]
  set c := ae6Word (Certificates.ae6TriEdgeC e)
  have hc : c ∈ ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) :=
    ae6Word_mem fun i hi => Finset.mem_coe.mpr (edgeC_letters e i hi)
  have hKle : ae6ModelK.map φ.toMonoidHom ≤ conjSub c ae6ModelK := by
    rw [ae6ModelK, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [MulEquiv.coe_toMonoidHom, hw]
      exact hk e he 0
    · rw [MulEquiv.coe_toMonoidHom, hw]
      exact hk e he 1
  have hKeq : ae6ModelK.map φ.toMonoidHom = conjSub c ae6ModelK := by
    refine Subgroup.eq_of_le_of_card_ge hKle ?_
    rw [hC, conjSub, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hK : ∀ q, φ q ∈ conjSub c ae6ModelK ↔ q ∈ ae6ModelK := fun q => by
    rw [← hKeq, hmap]
  have hord : ∀ a : AE6Om, orderOf (φ a) = orderOf a := fun a =>
    orderOf_injective φ.toMonoidHom φ.injective a
  have hQ : ∀ z, z ∈ Certificates.ae6TriQuat0 ↔ φ z ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) := by
    intro z
    unfold ae6EdgeQuat
    rw [edge_model_eq e]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, hzJ, ho⟩
      refine ⟨conjSub (φ g * c) ae6ModelK, ⟨φ g * c, Subgroup.mul_mem _ ((hE g).1 hg) hc, rfl⟩,
        ?_, by rw [hord]; exact ho⟩
      rw [mem_conjSub_iff] at hzJ ⊢
      have h := (hK _).2 hzJ
      rw [mem_conjSub_iff] at h
      have e1 : (φ g * c)⁻¹ * φ z * (φ g * c) = c⁻¹ * φ (g⁻¹ * z * g) * c := by
        simp only [map_mul, map_inv]
        group
      rw [e1]
      exact h
    · rintro ⟨_, ⟨g', hg', rfl⟩, hJ, ho⟩
      set h := φ.symm (g' * c⁻¹)
      have hφh : φ h = g' * c⁻¹ := MulEquiv.apply_symm_apply φ _
      have hh : h ∈ (ae6LetterSub ↑(ae6EdgeLetters 0 1)) := by
        rw [hE, hφh]
        exact Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hc)
      refine ⟨conjSub h ae6ModelK, ⟨h, hh, rfl⟩, ?_, by rw [← hord]; exact ho⟩
      rw [mem_conjSub_iff, ← hK, mem_conjSub_iff]
      have e1 : c⁻¹ * φ (h⁻¹ * z * h) * c = g'⁻¹ * φ z * g' := by
        simp only [map_mul, map_inv, hφh]
        group
      rw [e1]
      exact mem_conjSub_iff.mp hJ
  have hG : ∀ i, φ (ae6Word (ae6TriGen₀ i)) = ae6Word (ae6TriGen e i) := fun i =>
    hw _
  have hR : ∀ j i, φ (ae6Word (ae6TriRep 0 j (ae6TriGen₀ i))) =
      ae6Word (ae6TriRep e (Certificates.ae6RepSwap j) (ae6TriGen e i)) := by
    intro j i
    rw [rep_flat 0 j, word_flatMap, map_list_prod, List.map_map,
      rep_flat e (Certificates.ae6RepSwap j), word_flatMap, ae6TriGen, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc => ?_
    simp only [Function.comp_apply]
    rw [hw]
    exact hrep e he j c (gen0_letters i c hc)
  exact ta_of e φ Certificates.ae6RepSwap hQ hM hG hR

end TA

end CertB

theorem ae6TriFin_proved : AE6TriFin := by
  have hta : ∀ e : Fin 3,
      (∀ i, ae6Word (ae6TriGen e i) ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) ∧
      ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) →
        (∀ u ∈ ae6TriProf,
          orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen e i)).prod ∧
          ((u.map y).prod ∈ ae6ModelM ↔
            (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6ModelM) ∧
          ((u.map y).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) ↔
            (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈
              ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))) →
        ∃ m ∈ ae6ModelM, ∃ j : Fin 6,
          ∀ i, y i = m * ae6Word (ae6TriRep e j (ae6TriGen e i)) * m⁻¹ := by
    intro e
    by_cases he : e = 0
    · subst he
      refine CertB.ta_of 0 (MulEquiv.refl _) id (fun z => by rw [CertB.quat0_eq]; rfl)
        (fun a => Iff.rfl) (fun i => by rw [CertB.gen_eq0]; rfl) (fun j i => ?_)
      rw [CertB.gen_eq0]
      rfl
    · exact CertB.ta_succ e he
  exact ⟨CertB.tri_TM_M, CertB.tri_TM_edges, CertB.tri_TZ, fun k => ⟨CertB.card_V k,
    CertB.tri_TD_graph k, CertB.tri_TD_gen k, CertB.tri_TD_letters k, CertB.tri_TD_K0 k⟩,
    CertB.tri_TQ_norm, CertB.tri_TQ_dist, CertB.tri_TQ_delta, fun e => ⟨CertB.tri_TA_gen e,
    (hta e).1, (hta e).2⟩⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
