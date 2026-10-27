module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDG

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeDG

section Omega

variable {G H : Type} [Group G] [Group H]

@[expose] def omega (Y : Subgroup G) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : Subgroup G where
  carrier := {y | y ∈ Y ∧ y * y = 1}
  one_mem' := ⟨one_mem _, mul_one 1⟩
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨mul_mem hx hy, ?_⟩
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hY y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hx2, inv_one]

theorem mem_omega {Y : Subgroup G} {hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x} {y : G} :
    y ∈ omega Y hY ↔ y ∈ Y ∧ y * y = 1 := Iff.rfl

theorem omega_le (Y : Subgroup G) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) : omega Y hY ≤ Y :=
  fun _ h => h.1

theorem card_le_card_omega [Finite G] (Y : Subgroup G) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (f : G →* H) (hf : ∀ y ∈ Y, f y * f y = 1) (hker : f.ker ≤ Y) :
    Nat.card (Y.map f) ≤ Nat.card (omega Y hY) := by
  let sq : ↥Y →* G :=
    { toFun := fun y => (y : G) * y
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [coe_mul]
        calc (x : G) * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hY y y.2 x x.2]
          _ = x * x * (y * y) := by group }
  have hsqker : Nat.card sq.ker = Nat.card (omega Y hY) := by
    have h : sq.ker = (omega Y hY).subgroupOf Y := by
      ext y
      rw [MonoidHom.mem_ker, mem_subgroupOf, mem_omega]
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    rw [h]
    exact Nat.card_congr (subgroupOfEquivOfLe (omega_le Y hY)).toEquiv
  have hsqrange : sq.range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    show f ((y : G) * y) = 1
    rw [map_mul]
    exact hf y y.2
  have hY1 : Nat.card ↥Y = Nat.card sq.range * Nat.card sq.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup sq.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange sq).toEquiv]
  let fY : ↥Y →* H := f.comp Y.subtype
  have hfYrange : fY.range = Y.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  have hfYker : Nat.card fY.ker = Nat.card f.ker := by
    have h : fY.ker = f.ker.subgroupOf Y := by
      ext y
      rfl
    rw [h]
    exact Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv
  have hY2 : Nat.card ↥Y = Nat.card fY.range * Nat.card fY.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup fY.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange fY).toEquiv]
  have hle : Nat.card sq.range ≤ Nat.card f.ker := card_le_of_le hsqrange
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  rw [hfYrange, hfYker] at hY2
  rw [hsqker] at hY1
  have h3 : Nat.card (Y.map f) * Nat.card f.ker ≤ Nat.card (omega Y hY) * Nat.card f.ker := by
    rw [← hY2, hY1, mul_comm]
    exact Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right h3 hpos

end Omega

variable {Q : Type} [Group Q] {A B : Subgroup Q} {α : Q}

theorem exists_elem_eight [Finite Q] (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A)
    (hAq : IsQuasisimple ↥A) {B₈ V : Subgroup Q} (hB₈T : B₈ ≤ gsFixedLayer (A ⊔ B) α)
    (hB₈e : IsElemTwo B₈) (hB₈ : Nat.card B₈ = 8) (hVB : V ≤ B₈) (hV4 : Nat.card V = 4)
    (hVZ : V ≤ (Open.fusionZStar ↥(gsFixedLayer (A ⊔ B) α)).map
      (gsFixedLayer (A ⊔ B) α).subtype) :
    ∃ E : Subgroup Q, IsElemTwo E ∧ 8 ≤ Nat.card E ∧ E ≤ B ∧
      (∀ e ∈ E, ∀ g ∈ A, e * g = g * e) ∧ ∀ b ∈ B₈, ∀ e ∈ E, b * e = e * b := by
  have h8ne : B₈ ≠ ⊥ := fun h0 => by
    rw [h0, card_bot] at hB₈
    norm_num at hB₈
  have hTne : gsFixedLayer (A ⊔ B) α ≠ ⊥ := fun h => h8ne (le_bot_iff.mp (h ▸ hB₈T))
  set δ := HeDQ.delta hAB hαA with hδ
  have hTδ : gsFixedLayer (A ⊔ B) α = δ.range := gsFixedLayer_eq_range hα hAB hαA hαB hAq hTne
  have hBR : B₈ ≤ δ.range := hTδ ▸ hB₈T
  have hRq : IsQuasisimple ↥δ.range := isQuasisimple_range hAB hαA hAq
  have hRO : pPrimeCore 2 ↥δ.range ≤ center ↥δ.range := by
    rcases LocalCores.quasisimple_normal_subgroups hRq
        (inferInstance : (pPrimeCore 2 ↥δ.range).Normal) with h | h
    · exfalso
      obtain ⟨b, hb, hb1⟩ := (bot_or_exists_ne_one B₈).resolve_left h8ne
      have hmem : (⟨b, hBR hb⟩ : ↥δ.range) ∈ pPrimeCore 2 ↥δ.range := h ▸ mem_top _
      have h2 : orderOf (⟨⟨b, hBR hb⟩, hmem⟩ : pPrimeCore 2 ↥δ.range) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (Subtype.ext (hB₈e.2 b hb)))
          (fun h1 => hb1 (congrArg (fun x : pPrimeCore 2 ↥δ.range => ((x : ↥δ.range) : Q)) h1))
      have h3 := orderOf_dvd_natCard (⟨⟨b, hBR hb⟩, hmem⟩ : pPrimeCore 2 ↥δ.range)
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr h3)
    · exact h
  have hZR : Open.fusionZStar ↥δ.range = center ↥δ.range :=
    GrS5.fusionZStar_eq_center_of_le hRq.1.commutator_eq_top hRO
  rw [hTδ, hZR] at hVZ
  have hYc : ∀ x : ↥A, δ x ∈ V → x ∈ center ↥A := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hVZ hx
    apply mem_center_of_delta hAB hαA hAq
    intro y
    have h := mem_center_iff.mp hc ⟨δ y, ⟨y, rfl⟩⟩
    have h' := congrArg Subtype.val h
    simp only [coe_mul] at h'
    rw [← hcx]
    exact h'.symm
  have hidx : (V.subgroupOf B₈).index = 2 := by
    have h := (V.subgroupOf B₈).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv, hV4, hB₈] at h
    omega
  set Y := B₈.comap δ with hY
  have hYcomm : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁ := by
    intro y₁ hy₁ y₂ hy₂
    have hcen : ∀ y : ↥A, y ∈ center ↥A → ∀ z : ↥A, y * z = z * y := fun y hy z =>
      (mem_center_iff.mp hy z).symm
    by_cases h1 : δ y₁ ∈ V
    · exact hcen y₁ (hYc y₁ h1) y₂
    by_cases h2 : δ y₂ ∈ V
    · exact (hcen y₂ (hYc y₂ h2) y₁).symm
    have h12 : δ (y₁ * y₂) ∈ V := by
      rw [map_mul]
      exact (mul_mem_iff_of_index_two hidx (a := ⟨δ y₁, hy₁⟩) (b := ⟨δ y₂, hy₂⟩)).mpr
        ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    have h3 := hcen _ (hYc _ h12) y₁
    calc y₁ * y₂ = y₁⁻¹ * (y₁ * (y₁ * y₂)) := by group
      _ = y₁⁻¹ * ((y₁ * y₂) * y₁) := by rw [h3]
      _ = y₂ * y₁ := by group
  have hfY : ∀ y ∈ Y, δ y * δ y = 1 := fun y hy => hB₈e.2 _ hy
  have hker : δ.ker ≤ Y := by
    intro k hk
    show δ k ∈ B₈
    rw [MonoidHom.mem_ker.mp hk]
    exact one_mem _
  have hΩ8 : 8 ≤ Nat.card (omega Y hYcomm) := by
    have h := card_le_card_omega Y hYcomm δ hfY hker
    rwa [map_comap_eq_self hBR, hB₈] at h
  let φ : ↥A →* Q := (MulAut.conj α).toMonoidHom.comp A.subtype
  have hφinj : Function.Injective φ := (MulAut.conj α).injective.comp A.subtype_injective
  have hφa : ∀ x : ↥A, φ x = α * x * α⁻¹ := fun x => rfl
  refine ⟨(omega Y hYcomm).map φ, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hYcomm x (mem_omega.mp hx).1 y (mem_omega.mp hy).1]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, (mem_omega.mp hx).2, map_one]
  · rw [card_map_of_injective hφinj]
    exact hΩ8
  · rintro _ ⟨x, -, rfl⟩
    exact hαA x x.2
  · rintro _ ⟨x, -, rfl⟩ g hg
    rw [hφa]
    exact (hAB g hg _ (hαA x x.2)).symm
  · rintro b hb _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hBR hb
    have hyY : y ∈ Y := by
      show δ y ∈ B₈
      rw [hy]
      exact hb
    rw [← hy, hφa]
    exact delta_commute_conj hAB hαA (hYcomm x (mem_omega.mp hx).1 y hyY)

end HeDG

end CFSG.ComponentClassification.GrSLit
