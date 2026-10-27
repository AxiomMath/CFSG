module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Setup.X35

open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsUniqueMaxOver (S M X : Subgroup G) : Prop :=
  S ≤ M ∧ M < X ∧ ∀ Y : Subgroup G, S ≤ Y → Y < X → Y ≤ M

theorem not_isUniqueMaxOver_of_two_gen {P D : Subgroup G}
    (h : ∃ D₁ D₂ : Subgroup G, P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧ D₁ ⊔ D₂ = D) :
    ¬ ∃ M, IsUniqueMaxOver P M D := by
  rintro ⟨M, -, hMD, hM⟩
  obtain ⟨D₁, D₂, h1, h2, hD1, hD2, hgen⟩ := h
  exact absurd (hgen ▸ sup_le (hM D₁ h1 hD1) (hM D₂ h2 hD2)) (not_le_of_gt hMD)

theorem IsUniqueMaxOver.map {G' : Type*} [Group G'] {φ : G →* G'} (hφ : Function.Injective φ)
    {S M X : Subgroup G} (h : IsUniqueMaxOver S M X) :
    IsUniqueMaxOver (S.map φ) (M.map φ) (X.map φ) := by
  obtain ⟨hSM, hMX, hY⟩ := h
  refine ⟨Subgroup.map_mono hSM, (Subgroup.map_lt_map_iff_of_injective hφ).mpr hMX, ?_⟩
  intro Y hSY hYX
  set Y' := Y.comap φ with hY'
  have hY'X : Y' ≤ X := fun y hy => by
    have : φ y ∈ Y := hy
    obtain ⟨a, ha, hay⟩ := hYX.le this
    rw [← hφ hay]; exact ha
  have hmapY' : Y'.map φ = Y := by
    refine le_antisymm (Subgroup.map_comap_le φ Y) fun y hy => ?_
    obtain ⟨a, -, rfl⟩ := hYX.le hy
    exact ⟨a, hy, rfl⟩
  have hSY' : S ≤ Y' := fun s hs => hSY ⟨s, hs, rfl⟩
  have hY'lt : Y' < X := by
    refine lt_of_le_of_ne hY'X fun h => ?_
    rw [h] at hmapY'
    exact hYX.ne hmapY'.symm
  have := hY Y' hSY' hY'lt
  rw [← hmapY']
  exact Subgroup.map_mono this

section Sylow

variable [Finite G]

theorem isSylowTwoOf_map_of_injective {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Injective φ) {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map φ) (H.map φ) := by
  obtain ⟨hSH, hS, hc⟩ := isSylowTwoOf_iff.mp h
  refine isSylowTwoOf_iff.mpr ⟨Subgroup.map_mono hSH, hS.map φ, ?_⟩
  rw [Subgroup.card_map_of_injective hφ, hc, twoPart, twoPart, Subgroup.card_map_of_injective hφ]

end Sylow

section Aut

variable {Q : Type*} [Group Q]

theorem aut_mul_conj_mul_inv (σ : MulAut Q) (g : Q) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  ext x
  simp [MulAut.conj_apply]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  intro g h hgh
  have : h⁻¹ * g ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun φ : MulAut Q => φ z) hgh
    simp only [MulAut.conj_apply] at h1
    have h2 : g * z = h * z * h⁻¹ * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = (h * z * h⁻¹) * g := by rw [h1]
    calc z * (h⁻¹ * g) = h⁻¹ * (h * z * h⁻¹ * g) := by group
      _ = h⁻¹ * (g * z) := by rw [h2]
      _ = h⁻¹ * g * z := by group
  rw [hZ, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.mp this).symm

theorem mem_sup_zpowers_iff (Y : Subgroup G) (σ : G) (hσ : σ * σ = 1)
    (hn : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y) (x : G) :
    x ∈ Y ⊔ Subgroup.zpowers σ ↔ x ∈ Y ∨ ∃ y ∈ Y, x = y * σ := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | x ∈ Y ∨ ∃ y ∈ Y, x = y * σ}
        one_mem' := Or.inl Y.one_mem
        mul_mem' := by
          rintro a b (ha | ⟨y, hy, rfl⟩) (hb | ⟨z, hz, rfl⟩)
          · exact Or.inl (Y.mul_mem ha hb)
          · exact Or.inr ⟨a * z, Y.mul_mem ha hz, by group⟩
          · refine Or.inr ⟨y * (σ * b * σ⁻¹), Y.mul_mem hy (hn b hb), ?_⟩
            group
          · refine Or.inl ?_
            have : y * σ * (z * σ) = y * (σ * z * σ⁻¹) := by
              rw [hσinv]; simp only [mul_assoc]
            rw [this]
            exact Y.mul_mem hy (hn z hz)
        inv_mem' := by
          rintro a (ha | ⟨y, hy, rfl⟩)
          · exact Or.inl (Y.inv_mem ha)
          · refine Or.inr ⟨σ * y⁻¹ * σ⁻¹, hn _ (Y.inv_mem hy), ?_⟩
            calc (y * σ)⁻¹ = σ⁻¹ * y⁻¹ := mul_inv_rev _ _
              _ = σ * y⁻¹ := by rw [hσinv]
              _ = σ * y⁻¹ * σ⁻¹ * σ := by group }
    have hle : Y ⊔ Subgroup.zpowers σ ≤ S := by
      refine sup_le (fun y hy => Or.inl hy) ?_
      rw [Subgroup.zpowers_le]
      exact Or.inr ⟨1, Y.one_mem, by simp⟩
    exact hle hx
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))

theorem exists_orderOf_eq_two_pow_of_sq_mem {Y : Subgroup G} (hY : IsPGroup 2 Y) {x : G}
    (h : x ^ 2 ∈ Y) : ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hY ⟨x ^ 2, h⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : (x ^ 2) ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have h2 : x ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, mul_comm, pow_mul]; exact h1
  have hdvd : orderOf x ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, hj⟩

theorem exists_orderOf_eq_two_pow_of_mem {Y : Subgroup G} (hY : IsPGroup 2 Y) {x : G}
    (h : x ∈ Y) : ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hY ⟨x, h⟩
  rw [Subgroup.orderOf_mk] at hk
  exact ⟨k, hk⟩

theorem sigma_normalizes {σ : MulAut Q} {X : Subgroup Q} (hX : X.map σ.toMonoidHom = X) :
    ∀ y ∈ X.map (MulAut.conj : Q →* MulAut Q),
      σ * y * σ⁻¹ ∈ X.map (MulAut.conj : Q →* MulAut Q) := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨σ g, ?_, (aut_mul_conj_mul_inv σ g).symm⟩
  rw [← hX]
  exact ⟨g, hg, rfl⟩

theorem index_inn_eq_two {σ : MulAut Q} (hσin : σ ∉ (MulAut.conj : Q →* MulAut Q).range)
    (hAut : ∀ α : MulAut Q, α ∈ (MulAut.conj : Q →* MulAut Q).range ∨
      ∃ i ∈ (MulAut.conj : Q →* MulAut Q).range, α = i * σ) (hσ : σ * σ = 1) :
    (MulAut.conj : Q →* MulAut Q).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨σ, fun b => ?_⟩
  rcases hAut b with hb | ⟨i, hi, rfl⟩
  · refine Or.inr ⟨hb, fun h => ?_⟩
    exact hσin ((Subgroup.mul_mem_cancel_left _ hb).mp h)
  · refine Or.inl ⟨?_, fun h => ?_⟩
    · have : i * σ * σ = i := by rw [mul_assoc, hσ, mul_one]
      rw [this]; exact hi
    · exact hσin ((Subgroup.mul_mem_cancel_left _ hi).mp h)

theorem card_mulAut_eq {σ : MulAut Q} (hZ : Subgroup.center Q = ⊥)
    (hσin : σ ∉ (MulAut.conj : Q →* MulAut Q).range)
    (hAut : ∀ α : MulAut Q, α ∈ (MulAut.conj : Q →* MulAut Q).range ∨
      ∃ i ∈ (MulAut.conj : Q →* MulAut Q).range, α = i * σ) (hσ : σ * σ = 1) :
    Nat.card (MulAut Q) = 2 * Nat.card Q := by
  have h1 := index_inn_eq_two hσin hAut hσ
  have h2 := Subgroup.card_mul_index (MulAut.conj : Q →* MulAut Q).range
  rw [h1, Nat.card_congr
    (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).toEquiv.symm] at h2
  omega

end Aut

section Transport

variable [Finite G]

theorem two_gen_transport {D P P' D₁' D₂' : Subgroup G} (hP' : IsSylowTwoOf P' D)
    (hP : IsSylowTwoOf P D) (h1 : P' ≤ D₁') (h2 : P' ≤ D₂') (hD1 : D₁' < D) (hD2 : D₂' < D)
    (hgen : D₁' ⊔ D₂' = D) :
    ∃ D₁ D₂ : Subgroup G, P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧ D₁ ⊔ D₂ = D := by
  obtain ⟨h, hhD, hPe⟩ := IsSylowTwoOf.exists_conj hP' hP
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have hDe : D.map (MulAut.conj h).toMonoidHom = D := map_conj_eq_self_of_mem hhD
  refine ⟨D₁'.map (MulAut.conj h).toMonoidHom, D₂'.map (MulAut.conj h).toMonoidHom,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPe]; exact Subgroup.map_mono h1
  · rw [hPe]; exact Subgroup.map_mono h2
  · rw [← hDe]; exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hD1
  · rw [← hDe]; exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hD2
  · rw [← Subgroup.map_sup, hgen, hDe]

end Transport

section AutSylow

variable {Q : Type} [Group Q] [Finite Q]

theorem isSylowTwoOf_map_conj_inn (hZ : Subgroup.center Q = ⊥) {P₀ : Subgroup Q}
    (hP₀ : IsSylowTwoOf P₀ ⊤) :
    IsSylowTwoOf (P₀.map (MulAut.conj : Q →* MulAut Q)) (MulAut.conj : Q →* MulAut Q).range := by
  have hinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨-, hP2, hcard⟩ := isSylowTwoOf_iff.mp hP₀
  rw [isSylowTwoOf_iff]
  refine ⟨Subgroup.map_le_range _ _, hP2.map _, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, hcard, twoPart, twoPart]
  congr 2
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Subgroup.card_top]

theorem isSylowTwoOf_sup_zpowers (hZ : Subgroup.center Q = ⊥) {P₀ : Subgroup Q}
    (hP₀ : IsSylowTwoOf P₀ ⊤) {σ : MulAut Q} (hσ : σ * σ = 1)
    (hσin : σ ∉ (MulAut.conj : Q →* MulAut Q).range)
    (hσP : P₀.map σ.toMonoidHom = P₀)
    (hAut : ∀ α : MulAut Q, α ∈ (MulAut.conj : Q →* MulAut Q).range ∨
      ∃ i ∈ (MulAut.conj : Q →* MulAut Q).range, α = i * σ) :
    IsSylowTwoOf (P₀.map (MulAut.conj : Q →* MulAut Q) ⊔ Subgroup.zpowers σ) ⊤ := by
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hinj : Function.Injective c := conj_injective_of_center_eq_bot hZ
  obtain ⟨-, hP2, hcard⟩ := isSylowTwoOf_iff.mp hP₀
  have hn := sigma_normalizes hσP
  set Y := P₀.map c with hY
  set P' := Y ⊔ Subgroup.zpowers σ with hP'
  have hmem := mem_sup_zpowers_iff Y σ hσ hn
  have hσmem : σ ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hYσ : ∀ y ∈ Y, y * σ ∉ Y := fun y hy h => hσin (by
    have := (Subgroup.mul_mem_cancel_left Y hy).mp h
    exact Subgroup.map_le_range _ _ this)
  have hY2 : IsPGroup 2 Y := hP2.map c
  have hP2' : IsPGroup 2 P' := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hx⟩
    rw [Subgroup.orderOf_mk]
    rcases (hmem x).mp hx with hxY | ⟨y, hy, rfl⟩
    · exact exists_orderOf_eq_two_pow_of_mem hY2 hxY
    · have hsq : (y * σ) ^ 2 = y * (σ * y * σ⁻¹) := by
        rw [pow_two, hσinv]
        simp only [mul_assoc]
      exact exists_orderOf_eq_two_pow_of_sq_mem hY2 (by rw [hsq]; exact Y.mul_mem hy (hn y hy))
  refine isSylowTwoOf_iff.mpr ⟨le_top, hP2', ?_⟩
  have hle : Y ≤ P' := le_sup_left
  have hidx : (Y.subgroupOf P').index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨σ, hσmem⟩, ?_⟩
    rintro ⟨b, hb⟩
    rcases (hmem b).mp hb with hbY | ⟨y, hy, rfl⟩
    · refine Or.inr ⟨by simpa [Subgroup.mem_subgroupOf] using hbY, ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      exact hYσ b hbY
    · refine Or.inl ⟨?_, ?_⟩
      · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
        have : y * σ * σ = y := by rw [mul_assoc, hσ, mul_one]
        rw [this]; exact hy
      · simp only [Subgroup.mem_subgroupOf]
        exact hYσ y hy
  have h1 := Subgroup.card_mul_index (Y.subgroupOf P')
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have h3 : Nat.card Y = Nat.card P₀ := Subgroup.card_map_of_injective hinj
  have h4 := card_mulAut_eq hZ hσin hAut hσ
  rw [twoPart, Subgroup.card_top, h4, Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
  have hf : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  rw [twoPart, Subgroup.card_top] at hcard
  simp only [Finsupp.add_apply, hf]
  rw [← h1, h3, hcard]
  ring

theorem exists_two_gen_overgroups_of_aut (hZ : Subgroup.center Q = ⊥)
    {X₁ X₂ P₀ : Subgroup Q} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤) (hgen : X₁ ⊔ X₂ = ⊤)
    (hP₁ : P₀ ≤ X₁) (hP₂ : P₀ ≤ X₂) (hP₀ : IsSylowTwoOf P₀ ⊤)
    {σ : MulAut Q} (hσ : σ * σ = 1) (hσin : σ ∉ (MulAut.conj : Q →* MulAut Q).range)
    (hσ₁ : X₁.map σ.toMonoidHom = X₁) (hσ₂ : X₂.map σ.toMonoidHom = X₂)
    (hσP : P₀.map σ.toMonoidHom = P₀)
    (hAut : ∀ α : MulAut Q, α ∈ (MulAut.conj : Q →* MulAut Q).range ∨
      ∃ i ∈ (MulAut.conj : Q →* MulAut Q).range, α = i * σ)
    {D : Subgroup (MulAut Q)} (hD : (MulAut.conj : Q →* MulAut Q).range ≤ D)
    {P : Subgroup (MulAut Q)} (hP : IsSylowTwoOf P D) :
    ∃ D₁ D₂ : Subgroup (MulAut Q), P ≤ D₁ ∧ P ≤ D₂ ∧ D₁ < D ∧ D₂ < D ∧ D₁ ⊔ D₂ = D := by
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hinj : Function.Injective c := conj_injective_of_center_eq_bot hZ
  have hrange : (⊤ : Subgroup Q).map c = c.range := (MonoidHom.range_eq_map c).symm
  by_cases hσD : σ ∈ D
  · have hDtop : D = ⊤ := eq_top_iff.mpr fun α _ => by
      rcases hAut α with h | ⟨i, hi, rfl⟩
      · exact hD h
      · exact D.mul_mem (hD hi) hσD
    subst hDtop
    have key : ∀ X : Subgroup Q, X ≠ ⊤ → X.map σ.toMonoidHom = X →
        X.map c ⊔ Subgroup.zpowers σ < ⊤ := by
      intro X hX hσX
      refine lt_top_iff_ne_top.mpr fun htop => hX ?_
      rw [eq_top_iff]
      intro g _
      have hg : c g ∈ X.map c ⊔ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top _
      rcases (mem_sup_zpowers_iff _ σ hσ (sigma_normalizes hσX) _).mp hg with
        ⟨x, hx, hxg⟩ | ⟨y, hy, hgy⟩
      · rw [← hinj hxg]; exact hx
      · exfalso
        apply hσin
        have hyr : y ∈ c.range := Subgroup.map_le_range _ _ hy
        have : σ = y⁻¹ * c g := by rw [hgy]; group
        rw [this]
        exact c.range.mul_mem (c.range.inv_mem hyr) ⟨g, rfl⟩
    refine two_gen_transport (isSylowTwoOf_sup_zpowers hZ hP₀ hσ hσin hσP hAut) hP
      (sup_le_sup_right (Subgroup.map_mono hP₁) _) (sup_le_sup_right (Subgroup.map_mono hP₂) _)
      (key X₁ hX₁ hσ₁) (key X₂ hX₂ hσ₂) ?_
    rw [eq_top_iff]
    intro α _
    have hinn : c.range ≤ (X₁.map c ⊔ Subgroup.zpowers σ) ⊔ (X₂.map c ⊔ Subgroup.zpowers σ) := by
      rw [← hrange, ← hgen, Subgroup.map_sup]
      exact sup_le_sup le_sup_left le_sup_left
    have hσm : σ ∈ (X₁.map c ⊔ Subgroup.zpowers σ) ⊔ (X₂.map c ⊔ Subgroup.zpowers σ) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
    rcases hAut α with h | ⟨i, hi, rfl⟩
    · exact hinn h
    · exact Subgroup.mul_mem _ (hinn hi) hσm
  · have hDinn : D = c.range := le_antisymm (fun α hα => by
        rcases hAut α with h | ⟨i, hi, rfl⟩
        · exact h
        · exact absurd (by simpa using D.mul_mem (D.inv_mem (hD hi)) hα) hσD) hD
    subst hDinn
    refine two_gen_transport (isSylowTwoOf_map_conj_inn hZ hP₀) hP (Subgroup.map_mono hP₁)
      (Subgroup.map_mono hP₂) ?_ ?_ ?_
    · rw [← hrange]
      exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr (lt_top_iff_ne_top.mpr hX₁)
    · rw [← hrange]
      exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr (lt_top_iff_ne_top.mpr hX₂)
    · rw [← Subgroup.map_sup, hgen, hrange]

end AutSylow

end CFSG.QuasithinUnique.Setup.X35
