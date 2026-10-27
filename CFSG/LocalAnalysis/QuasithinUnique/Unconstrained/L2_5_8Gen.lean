module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Red
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Sylow

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter

theorem sylowFourData_of_checks {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hsyl : IsSylowTwoOf P ⊤)
    (hshape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨
      Nonempty (↥P ≃* SemidihedralGroup 4))
    (hnorm : ∀ g : X, (∀ p ∈ P, g * p * g⁻¹ ∈ P) → g ∈ P)
    (hfour : ∀ t s : X, t ∈ P → s ∈ P → t ≠ 1 → s ≠ 1 → t ≠ s → t * t = 1 → s * s = 1 →
      t * s = s * t →
      (∀ g : X, g * t = t * g → g * s = s * g → g = 1 ∨ g = t ∨ g = s ∨ g = t * s) ∧
      ∃ w : X, w ^ 3 = 1 ∧ w ≠ 1 ∧ (∃ u ∈ [1, t, s, t * s], w * t = u * w) ∧
        (∃ u ∈ [1, t, s, t * s], w * s = u * w)) :
    SylowFourData P where
  sylow := hsyl
  shape := hshape
  normalizer_le := fun g hg => hnorm g fun p hp => (Subgroup.mem_normalizer_iff.mp hg p).mp hp
  four := by
    intro F hFP hF
    obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, rfl⟩ := exists_kleinFour_gens hF
    have hmem := Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht hs hc
    have htF : t ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      (hmem t).mpr (Or.inr (Or.inl rfl))
    have hsF : s ∈ kleinFourOfCommutingInvolutions t s ht hs hc :=
      (hmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨hcent, w, hw3, hw1, ⟨u1, hu1, hwt⟩, ⟨u2, hu2, hws⟩⟩ :=
      hfour t s (hFP htF) (hFP hsF) ht1 hs1 hts ht hs hc.eq
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · intro g hg
        have hgt : g * t = t * g := (Subgroup.mem_centralizer_iff.mp hg t htF).symm
        have hgs : g * s = s * g := (Subgroup.mem_centralizer_iff.mp hg s hsF).symm
        rw [hmem]
        rcases hcent g hgt hgs with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
      · intro f hf
        have := hF.1.1
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact setLike_mul_comm hg hf
    · have hlist : ∀ u ∈ [1, t, s, t * s], u ∈ kleinFourOfCommutingInvolutions t s ht hs hc := by
        intro u hu
        rw [hmem]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
      have hWt : w * t * w⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc := by
        rw [mul_inv_eq_iff_eq_mul.mpr hwt]
        exact hlist u1 hu1
      have hWs : w * s * w⁻¹ ∈ kleinFourOfCommutingInvolutions t s ht hs hc := by
        rw [mul_inv_eq_iff_eq_mul.mpr hws]
        exact hlist u2 hu2
      have hnorm' : w ∈ Subgroup.normalizer
          ((kleinFourOfCommutingInvolutions t s ht hs hc : Subgroup X) : Set X) := by
        refine mem_normalizer_of_conj_le fun f hf => ?_
        rw [hmem] at hf
        rcases hf with h | h | h | h
        · have : w * f * w⁻¹ = (w * t * w⁻¹) * (w * s * w⁻¹) := by rw [h]; group
          rw [this]
          exact Subgroup.mul_mem _ hWt hWs
        · rw [h]
          exact hWt
        · rw [h]
          exact hWs
        · rw [h, mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact ⟨w, hnorm', orderOf_eq_prime hw3 hw1⟩

theorem normalizer_preserved {X : Type} [Group X] [Finite X] (β : MulAut X) (F : Subgroup X)
    (h : ∀ f ∈ F, β f ∈ F) :
    ∀ y, β y ∈ Subgroup.normalizer (F : Set X) ↔ y ∈ Subgroup.normalizer (F : Set X) := by
  have hFiff := mem_iff_of_map_le β h
  have hmap : F.map β.toMonoidHom = F := by
    ext z
    obtain ⟨y, rfl⟩ := β.surjective z
    rw [mem_map_iff β y]
    exact (hFiff y).symm
  have hN := normalizer_map β F
  rw [hmap] at hN
  intro y
  rw [← mem_map_iff β y, hN]

@[expose] def DynkinAt (X : Type) [Group X] (P : Subgroup X) : Prop :=
  ∀ B : Subgroup (MulAut X), (∀ β ∈ B, ∀ y : X, β y ∈ P ↔ y ∈ P) →
    (∀ Y : Subgroup X, P ≤ Y → (∀ β ∈ B, ∀ y : X, β y ∈ Y ↔ y ∈ Y) → Y = P ∨ Y = ⊤) →
      ∀ α : MulAut X, (∀ y ∈ P, α y = y) → (∀ β ∈ B, α * β = β * α) → α ∈ innerAut X

theorem DynkinAt.map {X Z : Type} [Group X] [Group Z] (e : X ≃* Z) {P : Subgroup X}
    (h : DynkinAt X P) : DynkinAt Z (P.map e.toMonoidHom) := by
  intro B' hB1 hB2 α' hα' hcomm
  let c : MulAut X ≃* MulAut Z := MulAut.congr e
  let B : Subgroup (MulAut X) := B'.comap c.toMonoidHom
  have hBmem : ∀ β : MulAut X, β ∈ B ↔ c β ∈ B' := fun β => Iff.rfl
  have hc_apply : ∀ (β : MulAut X) (x : X), c β (e x) = e (β x) := by
    intro β x
    simp [c, MulAut.congr_apply]
  have hB1' : ∀ β ∈ B, ∀ x : X, β x ∈ P ↔ x ∈ P := by
    intro β hβ x
    have := hB1 (c β) hβ (e x)
    rw [hc_apply, mem_map_iff, mem_map_iff] at this
    exact this
  have hB2' : ∀ Y' : Subgroup X, P ≤ Y' → (∀ β ∈ B, ∀ y : X, β y ∈ Y' ↔ y ∈ Y') →
      Y' = P ∨ Y' = ⊤ := by
    intro Y' hPY hinv
    have hPY' : P.map e.toMonoidHom ≤ Y'.map e.toMonoidHom := Subgroup.map_mono hPY
    have hinv' : ∀ β' ∈ B', ∀ y : Z, β' y ∈ Y'.map e.toMonoidHom ↔ y ∈ Y'.map e.toMonoidHom := by
      intro β' hβ' y
      obtain ⟨x, rfl⟩ := e.surjective y
      have hβ : c.symm β' ∈ B := by
        rw [hBmem, c.apply_symm_apply]
        exact hβ'
      have h1 := hinv (c.symm β') hβ x
      have e1 : β' (e x) = e ((c.symm β') x) := by
        have := hc_apply (c.symm β') x
        rwa [c.apply_symm_apply] at this
      rw [e1, mem_map_iff, mem_map_iff]
      exact h1
    rcases hB2 (Y'.map e.toMonoidHom) hPY' hinv' with h1 | h1
    · left
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    · right
      rw [eq_top_iff]
      intro x _
      have hx : e x ∈ Y'.map e.toMonoidHom := by
        rw [h1]
        exact Subgroup.mem_top _
      exact (mem_map_iff e x).mp hx
  have hα : ∀ x ∈ P, c.symm α' x = x := by
    intro x hx
    have h1 := hα' (e x) ((mem_map_iff e x).mpr hx)
    show e.symm (α' (e x)) = x
    rw [h1, MulEquiv.symm_apply_apply]
  have hcomm' : ∀ β ∈ B, c.symm α' * β = β * c.symm α' := by
    intro β hβ
    apply c.injective
    rw [map_mul, map_mul, c.apply_symm_apply]
    exact hcomm (c β) hβ
  have hin := h B hB1' hB2' (c.symm α') hα hcomm'
  have h2 := congr_mem_innerAut e hin
  have h3 : MulAut.congr e (c.symm α') = α' := c.apply_symm_apply α'
  rwa [h3] at h2

theorem a6DynkinCentral_of_dynkinAt {X : Type} [Group X] [Finite X] {P₀ : Subgroup X}
    (hP₀ : IsSylowTwoOf P₀ ⊤) (h : DynkinAt X P₀) : A6DynkinCentral X := by
  intro P hP B hB1 hB2 α hα hcomm
  obtain ⟨g, -, hg⟩ := hP₀.exists_conj hP
  have := DynkinAt.map (MulAut.conj g) h
  rw [← hg] at this
  exact this B hB1 hB2 α hα hcomm

end CFSG.QuasithinUnique.Unc25Small
