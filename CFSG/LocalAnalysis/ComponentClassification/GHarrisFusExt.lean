module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusRel
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL33

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem not_fusN_x_32 :
    ∀ j ∈ [0, 1, 2, 3], ¬ D.FusN 5 j ∧ ¬ D.FusN j 5 := by
  have e5 : SE.invRep (Fin.ofNat 9 5) = SE.gen 6 := by decide
  have key : ∀ j ∈ [0, 1, 2, 3], ¬ D.FusN 5 j := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> rintro ⟨g, hg⟩ <;> rw [e5] at hg
    · rw [show SE.invRep (Fin.ofNat 9 0) = SE.gen 0 by decide] at hg
      exact D.not_conj_x_z ⟨g, hg⟩
    · rw [show Fin.ofNat 9 1 = 1 by decide] at hg
      exact D.not_conj_x_t ⟨g, hg⟩
    · rw [show Fin.ofNat 9 2 = 2 by decide] at hg
      exact D.not_conj_x_a1l ⟨g, hg⟩
    · rw [show Fin.ofNat 9 3 = 3 by decide] at hg
      exact D.not_conj_x_a3a4 ⟨g, hg⟩
  exact fun j hj => ⟨key j hj, fun h => key j hj (D.fusN_symm h)⟩

theorem not_fusN_x
    (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a) :
    ∀ j ∈ [0, 1, 2, 3, 7], ¬ D.FusN 5 j ∧ ¬ D.FusN j 5 := by
  have key7 : ¬ D.FusN 5 7 := by
    rintro ⟨g, hg⟩
    rw [show SE.invRep (Fin.ofNat 9 5) = SE.gen 6 by decide,
      show Fin.ofNat 9 7 = 7 by decide] at hg
    exact hxa ⟨g, hg⟩
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact D.not_fusN_x_32 0 (by simp)
  · exact D.not_fusN_x_32 1 (by simp)
  · exact D.not_fusN_x_32 2 (by simp)
  · exact D.not_fusN_x_32 3 (by simp)
  · exact ⟨key7, fun h => key7 (D.fusN_symm h)⟩

theorem card_le_of_extremal {v w : G}
    (hv : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({v} : Set G)) (centralizer ({v} : Set G)))
    {g : G} (hg : g⁻¹ * v * g = w) :
    Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({w} : Set G)) ≤
      Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({v} : Set G)) := by
  set Q := ((D.S : Subgroup G) ⊓ centralizer ({w} : Set G)).map (MulAut.conj g).toMonoidHom
  have hQ : Q ≤ centralizer ({v} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcw := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    rw [mem_centralizer_singleton_iff]
    change g * c * g⁻¹ * v = v * (g * c * g⁻¹)
    rw [← hg] at hcw
    calc g * c * g⁻¹ * v = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by rw [hcw]
      _ = v * (g * c * g⁻¹) := by group
  have hQ2 : IsPGroup 2 Q := (D.S.isPGroup'.to_le inf_le_left).map _
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hv hQ hQ2
  have hle : Q.map (MulAut.conj c).toMonoidHom ≤
      (D.S : Subgroup G) ⊓ centralizer ({v} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hc q hq
  have hcard := card_le_of_le hle
  rwa [card_map_of_injective (MulAut.conj c).injective,
    card_map_of_injective (MulAut.conj g).injective] at hcard

theorem exists_extremal_rep {u : G}
    (hu : u ∈ (D.S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hne : ¬ IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G))
      (centralizer ({u} : Set G))) :
    ∃ j : Fin 9, ∃ g : G,
      IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G))
        (centralizer ({D.toG (SE.invRep j)} : Set G)) ∧
      Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) < SE.invRepCent j ∧
      g⁻¹ * u * g = D.toG (SE.invRep j) ∧
      ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G) := by
  obtain ⟨g, hvS, hvext, hlt, hC⟩ := exists_extremal_conj_lt (isSylowOf_top D.S) hu hne
  set v := g⁻¹ * u * g with hv
  have hv2 : v * v = 1 := by
    rw [hv, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2]; group
  have hv1 : v ≠ 1 := fun h => hu1 (by
    calc u = g * v * g⁻¹ := by rw [hv]; group
      _ = 1 := by rw [h]; group)
  obtain ⟨j, c, hcS, hc⟩ := D.exists_conj_invRep_G hvS hv2 hv1
  have hcard := D.card_inf_centralizer_conj hcS v
  rw [hc, D.card_centralizer_invRep_G] at hcard
  refine ⟨j, g * c, ?_, by rw [hcard]; exact hlt, by rw [← hc, hv]; group, ?_⟩
  · refine isSylowOf_of_card_le (isSylowOf_top D.S) (D.toG_mem _) fun k hk => ?_
    rw [D.card_centralizer_invRep_G, hcard]
    exact D.card_le_of_extremal hvext (show (c * k)⁻¹ * v * (c * k) = _ by
      rw [show (c * k)⁻¹ * v * (c * k) = k⁻¹ * (c⁻¹ * v * c) * k by group, hc])
  · intro x hx
    have h1 := hC x hx
    rw [← hc, show (g * c)⁻¹ * x * (g * c) = c⁻¹ * (g⁻¹ * x * g) * c by group]
    obtain ⟨h1S, h1C⟩ := mem_inf.mp h1
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hcS) h1S) hcS, ?_⟩
    have := mem_centralizer_singleton_iff.mp h1C
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * (g⁻¹ * x * g) * c * (c⁻¹ * v * c) = c⁻¹ * ((g⁻¹ * x * g) * v) * c := by group
      _ = c⁻¹ * (v * (g⁻¹ * x * g)) * c := by rw [this]
      _ = c⁻¹ * v * c * (c⁻¹ * (g⁻¹ * x * g) * c) := by group



omit [Finite G] in
theorem fusN_of_conj_rep {i j : Fin 9} {g : G}
    (h : g⁻¹ * D.toG (SE.invRep i) * g = D.toG (SE.invRep j)) : D.FusN i j := by
  have hi : Fin.ofNat 9 i.val = i := Fin.ext (by simp)
  have hj : Fin.ofNat 9 j.val = j := Fin.ext (by simp)
  exact ⟨g, by rw [hi, hj]; exact h⟩

omit [Finite G] in
theorem fusN_of_edge {i j : ℕ} {g : G}
    (h : ∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
      g⁻¹ * (s₁⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 i)) * s₁) * g =
        s₂⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 j)) * s₂) : D.FusN i j := by
  obtain ⟨s₁, -, s₂, -, h⟩ := h
  refine ⟨s₁ * g * s₂⁻¹, ?_⟩
  calc (s₁ * g * s₂⁻¹)⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 i)) * (s₁ * g * s₂⁻¹) =
        s₂ * (g⁻¹ * (s₁⁻¹ * D.toG (SE.invRep (Fin.ofNat 9 i)) * s₁) * g) * s₂⁻¹ := by group
    _ = _ := by rw [h]; group

omit [Finite G] in
theorem good_of_rep {A : Fus.Data} (hA : A.checkM (· * ·) = true) (hcls : SE.clsOk = true)
    {u : G} {v : SE} {g : G} (hsrc : D.toG A.source = u) (htgt : A.target = v)
    (hgu : g⁻¹ * u * g = D.toG v)
    (hC : ∀ c ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G),
      g⁻¹ * c * g ∈ (D.S : Subgroup G) ⊓ centralizer ({D.toG v} : Set G))
    (hbad : ∀ p ∈ A.badPairs, ¬ D.FusN p.1 p.2) (hE : A.useE = false) (hF : A.useF = false) :
    A.good (· * ·) (D.fusQ A g) = true := by
  refine D.fus_good hA hcls (by rw [hsrc, htgt]; exact hgu) (fun s hs => ?_) hbad
    (fun h => absurd (hE ▸ h) Bool.false_ne_true) (fun h => absurd (hF ▸ h) Bool.false_ne_true)
  have hsu : D.toG s ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    refine mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hsrc, ← map_mul, ← map_mul, hs]
  exact (mem_inf.mp (hC _ hsu)).1

end GHSylow

end CFSG.ComponentClassification.GHarris
