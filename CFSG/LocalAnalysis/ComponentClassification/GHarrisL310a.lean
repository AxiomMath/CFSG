module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusExt
public import Certificates.Certificate22608
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL39

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem badPairs_a
    (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a) {j : ℕ}
    (haj : D.FusN 7 j) (Fx : List (ℕ × ℕ)) (hFx : ∀ p ∈ Fx, ¬ D.FusN p.1 p.2)
    (B : List (ℕ × ℕ))
    (hB : ∀ b ∈ B, ∃ p ∈ [(5, 0), (5, 1), (5, 2), (5, 3), (5, 7)] ++ Fx,
      ((fun i => if i = 7 then j else i) p.1 = (fun i => if i = 7 then j else i) b.1 ∧
        (fun i => if i = 7 then j else i) p.2 = (fun i => if i = 7 then j else i) b.2) ∨
      ((fun i => if i = 7 then j else i) p.1 = (fun i => if i = 7 then j else i) b.2 ∧
        (fun i => if i = 7 then j else i) p.2 = (fun i => if i = 7 then j else i) b.1)) :
    ∀ b ∈ B, ¬ D.FusN b.1 b.2 := by
  refine Fus.not_bad (R := D.FusN) (fun i j h => D.fusN_symm h)
    (fun i j k h1 h2 => D.fusN_trans h1 h2)
    (fun i => if i = 7 then j else i) (fun i => ?_) _ ?_ B hB
  · by_cases h : i = 7
    · subst h; simp only [ite_true]; exact haj
    · simp only [h, ite_false]; exact D.fusN_refl i
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hx := D.not_fusN_x hxa
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact (hx 0 (by simp)).1
      · exact (hx 1 (by simp)).1
      · exact (hx 2 (by simp)).1
      · exact (hx 3 (by simp)).1
      · exact (hx 7 (by simp)).1
    · exact hFx p hp



omit [Finite G] in
theorem badPairs_aZ : Fus.aZ.badPairs =
    [(0, 5), (1, 5), (2, 5), (3, 5), (5, 0), (5, 1), (5, 2), (5, 3), (5, 7), (7, 5)] := rfl

theorem a_fusion
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a) :
    (∃ g : G, g⁻¹ * D.a * g = D.z ∧ Fus.aZ.good (· * ·) (D.fusQ Fus.aZ g) = true ∧
      ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a} : Set G), g⁻¹ * c * g ∈ (D.S : Subgroup G)) ∨
    (∃ g : G, g⁻¹ * D.a * g = D.a3a4 ∧ Fus.aA34.good (· * ·) (D.fusQ Fus.aA34 g) = true ∧
      (∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a} : Set G),
        g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G)) ∧
      IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G))
        (centralizer ({D.a3a4} : Set G))) := by
  obtain ⟨hcls, hZ, hT, hA1L, hA34⟩ := Certificates.certificate22608
  have haS : D.a ∈ (D.S : Subgroup G) := D.toG_mem _
  have hS2 : D.a ∉ D.S2 := by rw [D.toG_mem_S2_iff]; decide
  have hne := D.not_isSylowOf_of_not_mem_S2 hidx haS (D.toG_invRep_mul_self 7)
    (D.toG_invRep_ne_one 7) hS2
  obtain ⟨j, g, hjext, hlt, hgu, hC⟩ := D.exists_extremal_rep haS (D.toG_invRep_mul_self 7)
    (D.toG_invRep_ne_one 7) hne
  have h32 : Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({D.a} : Set G)) = 32 :=
    D.card_centralizer_invRep_G 7
  rw [h32] at hlt
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by
    have key : ∀ i : Fin 9, 32 < SE.invRepCent i → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 := by
      decide
    exact key j hlt
  have haj : D.FusN (7 : Fin 9) j := D.fusN_of_conj_rep (i := 7) hgu
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · left
    rw [show SE.invRep 0 = SE.gen 0 by decide] at hgu hC
    refine ⟨g, hgu, D.good_of_rep (Fus.checkList_sound hZ (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.aZ.source = SE.invRep 7))
      (by decide : Fus.aZ.target = SE.gen 0) hgu hC ?_ rfl rfl,
      fun c hc => (mem_inf.mp (hC c hc)).1⟩
    rw [badPairs_aZ]
    exact D.badPairs_a hxa haj [] (by simp) _ (by decide)
  · exfalso
    have := D.good_of_rep (Fus.checkList_sound hT (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.aT.source = SE.invRep 7)) (by decide) hgu hC ?_ rfl rfl
    · exact Bool.false_ne_true this
    · have hz := (D.not_fusN_of_lt hjext (j := 0) (by decide)).1
      exact D.badPairs_a hxa haj [(1, 0)] (by simpa using hz) _ (by decide)
  · exfalso
    have := D.good_of_rep (Fus.checkList_sound hA1L (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.aA1L.source = SE.invRep 7)) (by decide) hgu hC ?_ rfl rfl
    · exact Bool.false_ne_true this
    · have hz := (D.not_fusN_of_lt hjext (j := 0) (by decide)).1
      have ht := (D.not_fusN_of_lt hjext (j := 1) (by decide)).1
      exact D.badPairs_a hxa haj [(2, 0), (2, 1)] (by simpa using ⟨hz, ht⟩) _ (by decide)
  · right
    refine ⟨g, hgu, D.good_of_rep (Fus.checkList_sound hA34 (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.aA34.source = SE.invRep 7)) (by decide) hgu hC ?_ rfl rfl,
      hC, hjext⟩
    have hz := (D.not_fusN_of_lt hjext (j := 0) (by decide)).1
    have ht := (D.not_fusN_of_lt hjext (j := 1) (by decide)).1
    have hl := (D.not_fusN_of_lt hjext (j := 2) (by decide)).1
    exact D.badPairs_a hxa haj [(3, 0), (3, 1), (3, 2)] (by simpa using ⟨hz, ht, hl⟩) _
      (by decide)
  · exfalso
    rw [show SE.invRep 5 = SE.gen 6 by decide] at hgu
    exact hxa ⟨g⁻¹, by
      calc g⁻¹⁻¹ * D.x * g⁻¹ = g * (g⁻¹ * D.a * g) * g⁻¹ := by rw [hgu]; group
        _ = D.a := by group⟩



omit [Finite G] in
theorem aZ_decode {g : G} (hgu : g⁻¹ * D.a * g = D.z)
    (hgC : ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a} : Set G), g⁻¹ * c * g ∈ (D.S : Subgroup G))
    (hgood : Fus.aZ.good (· * ·) (D.fusQ Fus.aZ g) = true) :
    D.FusN 1 7 ∧ D.FusN 7 3 ∧
      (∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
        g⁻¹ * (s₁⁻¹ * D.x * s₁) * g = s₂⁻¹ * D.al * s₂) ∧
      ∃ s ∈ (D.S : Subgroup G), (g * s)⁻¹ * D.t * (g * s) = D.t ∧
        ((g * s)⁻¹ * D.x * (g * s) = D.x ∨ (g * s)⁻¹ * (D.x * D.z) * (g * s) = D.x * D.z) := by
  obtain ⟨hcls, hZ, -⟩ := Certificates.certificate22608
  have hA := Fus.checkList_sound hZ (List.mem_singleton_self _)
  have hsrc : Fus.aZ.source = SE.invRep 7 := by decide
  have htgt : Fus.aZ.target = SE.gen 0 := by decide
  have hgu' : g⁻¹ * D.toG Fus.aZ.source * g = D.toG Fus.aZ.target := by rw [hsrc, htgt]; exact hgu
  have hgC' : ∀ s : SE, s * Fus.aZ.source = Fus.aZ.source * s →
      g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
    intro s hs
    refine hgC _ (mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr ?_⟩)
    rw [hsrc] at hs
    rw [← map_mul, ← map_mul, hs]
  have egood : Fus.aZ.good = Fus.goodAZ := rfl
  rw [egood] at hgood
  have hgood' := hgood
  unfold Fus.goodAZ at hgood'
  simp only [Bool.and_eq_true] at hgood'
  obtain ⟨⟨⟨e17, e73⟩, e58⟩, hs⟩ := hgood'
  have edge := fun {i j : ℕ} (h : Fus.aZ.hasEdge (· * ·) (D.fusQ Fus.aZ g) i j = true) =>
    D.hasEdge_conj hA hcls hgu' hgC' h
  refine ⟨D.fusN_of_edge (edge e17), D.fusN_of_edge (edge e73), ?_, ?_⟩
  · obtain ⟨s₁, hs₁, s₂, hs₂, h⟩ := edge e58
    refine ⟨s₁, hs₁, s₂, hs₂, ?_⟩
    rw [show SE.invRep (Fin.ofNat 9 5) = SE.gen 6 by decide,
      show Fin.ofNat 9 8 = 8 by decide] at h
    exact h
  · obtain ⟨s, -, hs⟩ := List.any_eq_true.mp hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    obtain ⟨ht, hx⟩ := hs
    have hi := fun {k : ℕ} (hk : k < 32) => D.img_conj hA hgu' hgC' hk
    have hel : Fus.aZ.elt (· * ·) 26 = SE.invRep 1 ∧ Fus.aZ.elt (· * ·) 4 = SE.gen 6 ∧
        Fus.aZ.elt (· * ·) 2 = SE.gen 0 := by decide
    have ht' := congrArg D.toG ht
    rw [map_mul, map_mul, show Fus.aZBase.img (· * ·) (D.fusQ Fus.aZ g) 26 =
      Fus.aZ.img (· * ·) (D.fusQ Fus.aZ g) 26 from rfl, hi (by norm_num), hel.1] at ht'
    refine ⟨D.toG s, D.toG_mem s, ?_, ?_⟩
    · calc (g * D.toG s)⁻¹ * D.t * (g * D.toG s) =
            (D.toG s)⁻¹ * (g⁻¹ * D.toG (SE.invRep 1) * g * D.toG s) := by group
        _ = D.t := by rw [ht']; group
    · rcases hx with hx | hx
      · left
        have hx' := congrArg D.toG hx
        rw [map_mul, map_mul, show Fus.aZBase.img (· * ·) (D.fusQ Fus.aZ g) 4 =
          Fus.aZ.img (· * ·) (D.fusQ Fus.aZ g) 4 from rfl, hi (by norm_num), hel.2.1] at hx'
        calc (g * D.toG s)⁻¹ * D.x * (g * D.toG s) =
              (D.toG s)⁻¹ * (g⁻¹ * D.toG (SE.gen 6) * g * D.toG s) := by group
          _ = D.x := by rw [hx']; group
      · right
        have hx' := congrArg D.toG hx
        rw [map_mul, map_mul, map_mul, map_mul, show Fus.aZBase.img (· * ·) (D.fusQ Fus.aZ g) 4 =
          Fus.aZ.img (· * ·) (D.fusQ Fus.aZ g) 4 from rfl,
          show Fus.aZBase.img (· * ·) (D.fusQ Fus.aZ g) 2 =
          Fus.aZ.img (· * ·) (D.fusQ Fus.aZ g) 2 from rfl, hi (by norm_num), hi (by norm_num),
          hel.2.1, hel.2.2] at hx'
        calc (g * D.toG s)⁻¹ * (D.x * D.z) * (g * D.toG s) =
              (D.toG s)⁻¹ * ((g⁻¹ * D.toG (SE.gen 6) * g) * (g⁻¹ * D.toG (SE.gen 0) * g) *
                D.toG s) := by group
          _ = D.x * D.z := by rw [hx']; group



omit [Finite G] in
theorem aA34_decode {g : G} (hgu : g⁻¹ * D.a * g = D.a3a4)
    (hgC : ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a} : Set G),
      g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G))
    (hgood : Fus.aA34.good (· * ·) (D.fusQ Fus.aA34 g) = true) :
    D.FusN 1 0 ∧
      (∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
        g⁻¹ * (s₁⁻¹ * D.x * s₁) * g = s₂⁻¹ * D.al * s₂ ∨
          g⁻¹ * (s₁⁻¹ * D.al * s₁) * g = s₂⁻¹ * D.x * s₂) ∧
      ∃ s ∈ (D.S : Subgroup G), (g * s)⁻¹ * D.a * (g * s) = D.a3a4 ∧
        (g * s)⁻¹ * D.t * (g * s) = D.z ∧
        ((g * s)⁻¹ * D.z * (g * s) = D.t ∨ (g * s)⁻¹ * D.z * (g * s) = D.t * D.z) ∧
        ∃ w ∈ Fus.A1list, (g * s)⁻¹ * D.a3a4 * (g * s) = D.toG w := by
  obtain ⟨hcls, -, -, -, hA34⟩ := Certificates.certificate22608
  have hA := Fus.checkList_sound hA34 (List.mem_singleton_self _)
  have hsrc : Fus.aA34.source = SE.invRep 7 := by decide
  have htgt : Fus.aA34.target = SE.invRep 3 := by decide
  have hgu' : g⁻¹ * D.toG Fus.aA34.source * g = D.toG Fus.aA34.target := by
    rw [hsrc, htgt]; exact hgu
  have hgC' : ∀ s : SE, s * Fus.aA34.source = Fus.aA34.source * s →
      g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
    intro s hs
    refine (mem_inf.mp (hgC _ (mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr ?_⟩))).1
    rw [hsrc] at hs
    rw [← map_mul, ← map_mul, hs]
  have egood : Fus.aA34.good = Fus.goodA34 := rfl
  rw [egood] at hgood
  have hgood' := hgood
  unfold Fus.goodA34 at hgood'
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hgood'
  obtain ⟨⟨⟨e10, e58⟩, -⟩, hs⟩ := hgood'
  have edge := fun {i j : ℕ} (h : Fus.aA34.hasEdge (· * ·) (D.fusQ Fus.aA34 g) i j = true) =>
    D.hasEdge_conj hA hcls hgu' hgC' h
  refine ⟨?_, ?_, ?_⟩
  · rcases e10 with h | h
    · exact D.fusN_of_edge (edge h)
    · exact D.fusN_symm (D.fusN_of_edge (edge h))
  · rcases e58 with h | h
    · obtain ⟨s₁, hs₁, s₂, hs₂, h⟩ := edge h
      refine ⟨s₁, hs₁, s₂, hs₂, Or.inl ?_⟩
      rw [show SE.invRep (Fin.ofNat 9 5) = SE.gen 6 by decide,
        show Fin.ofNat 9 8 = 8 by decide] at h
      exact h
    · obtain ⟨s₁, hs₁, s₂, hs₂, h⟩ := edge h
      refine ⟨s₁, hs₁, s₂, hs₂, Or.inr ?_⟩
      rw [show SE.invRep (Fin.ofNat 9 5) = SE.gen 6 by decide,
        show Fin.ofNat 9 8 = 8 by decide] at h
      exact h
  · obtain ⟨s, -, hs⟩ := List.any_eq_true.mp hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨hsc, ht⟩, hz⟩, hw⟩ := hs
    have hi := fun {k : ℕ} (hk : k < 32) => D.img_conj hA hgu' hgC' hk
    have hel : Fus.aA34.elt (· * ·) 26 = SE.invRep 1 ∧ Fus.aA34.elt (· * ·) 2 = SE.gen 0 ∧
        Fus.aA34.elt (· * ·) 3 = SE.invRep 3 := by decide
    have eimg : ∀ k, Fus.aA34Base.img (· * ·) (D.fusQ Fus.aA34 g) k =
        Fus.aA34.img (· * ·) (D.fusQ Fus.aA34 g) k := fun _ => rfl
    have hsc' := congrArg D.toG hsc
    rw [map_mul, map_mul] at hsc'
    have ht' := congrArg D.toG ht
    rw [map_mul, map_mul, eimg, hi (by norm_num), hel.1] at ht'
    refine ⟨D.toG s, D.toG_mem s, ?_, ?_, ?_, ?_⟩
    · calc (g * D.toG s)⁻¹ * D.a * (g * D.toG s) = (D.toG s)⁻¹ * (g⁻¹ * D.a * g) * D.toG s := by
            group
        _ = D.a3a4 := by
            rw [hgu]
            calc (D.toG s)⁻¹ * D.toG (SE.invRep 3) * D.toG s =
                  (D.toG s)⁻¹ * (D.toG s * D.toG (SE.invRep 3)) := by rw [hsc']; group
              _ = D.a3a4 := by group
    · calc (g * D.toG s)⁻¹ * D.t * (g * D.toG s) =
            (D.toG s)⁻¹ * (g⁻¹ * D.toG (SE.invRep 1) * g * D.toG s) := by group
        _ = D.z := by rw [ht']; group
    · have hz' : ∀ w : SE, Fus.aA34Base.img (· * ·) (D.fusQ Fus.aA34 g) 2 * s = s * w →
          (g * D.toG s)⁻¹ * D.z * (g * D.toG s) = D.toG w := by
        intro w hw
        have hw' := congrArg D.toG hw
        rw [map_mul, map_mul, eimg, hi (by norm_num), hel.2.1] at hw'
        calc (g * D.toG s)⁻¹ * D.z * (g * D.toG s) =
              (D.toG s)⁻¹ * (g⁻¹ * D.toG (SE.gen 0) * g * D.toG s) := by group
          _ = D.toG w := by rw [hw']; group
      rcases hz with hz | hz
      · left; exact hz' _ hz
      · right; rw [hz' _ hz, map_mul]
    · obtain ⟨w, hwm, hw⟩ := List.any_eq_true.mp hw
      refine ⟨w, hwm, ?_⟩
      have hw' := congrArg D.toG (beq_iff_eq.mp hw)
      rw [map_mul, map_mul, eimg, hi (by norm_num), hel.2.2] at hw'
      calc (g * D.toG s)⁻¹ * D.a3a4 * (g * D.toG s) =
            (D.toG s)⁻¹ * (g⁻¹ * D.toG (SE.invRep 3) * g * D.toG s) := by group
        _ = D.toG w := by rw [hw']; group

end GHSylow

end CFSG.ComponentClassification.GHarris
