module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypPCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Open

theorem pCoreOf_centralizer_dod₂ (hcls : Co0ClassData) :
    pCoreOf 2 (Subgroup.centralizer {gO dod₂}) = signSub := by
  rw [centralizer_gO_dod₂ hcls]
  exact le_antisymm pCoreOf_monoSub_le
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (monoSub_mono bot_le)
      (le_normalizer_signSub (monoSub_mono le_top)) isPGroup_signSub)

theorem centralizer_conj_singleton {G : Type*} [Group G] (c x : G) :
    Subgroup.centralizer ({c * x * c⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨c⁻¹ * g * c, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * g) * c := by rw [h]
      _ = x * (c⁻¹ * g * c) := by group
  · rintro ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * k * c⁻¹ * (c * x * c⁻¹) = c * (k * x) * c⁻¹ := by group
      _ = c * (x * k) * c⁻¹ := by rw [hk]
      _ = c * x * c⁻¹ * (c * k * c⁻¹) := by group

theorem card_centralizer_conj_singleton {G : Type*} [Group G] (c x : G) :
    Nat.card (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  rw [centralizer_conj_singleton]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem centralizer_negOneO_mul_typ (z : latticeO) :
    Subgroup.centralizer ({negOneO * z} : Set latticeO) =
      Subgroup.centralizer ({z} : Set latticeO) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have h1 : g * (negOneO * z) = negOneO * (g * z) := by
    rw [← mul_assoc, ← negOneO_mul_comm g, mul_assoc]
  rw [h1, mul_assoc, mul_right_inj]

theorem negOneO_mul_conj (c g : latticeO) :
    negOneO * (c * g * c⁻¹) = c * (negOneO * g) * c⁻¹ := by
  rw [← mul_assoc, ← mul_assoc, negOneO_mul_comm c, mul_assoc c negOneO g]

theorem typeC_form (hcls : Co0ClassData) {y : latticeO}
    (hy : InvType (⊤ : Subgroup latticeO) negOneO co0C3 y) :
    ∃ (c : latticeO) (d₁ : C), (d₁ = dod₂ ∨ d₁ = ΩC + dod₂) ∧ y = c * gO d₁ * c⁻¹ := by
  obtain ⟨-, h2, hne, -, hcard⟩ := hy
  have hy2 : y * y = 1 := by rw [← pow_two]; exact h2 ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, d, hd, h⟩ := hcls.involution_classes y hy2 hy1 hne
  have hd' : d = oct₁ ∨ d = dod₂ := by simpa using hd
  obtain ⟨d₁, hd₁, hyc⟩ : ∃ d₁, (d₁ = d ∨ d₁ = ΩC + d) ∧ y = c * gO d₁ * c⁻¹ := by
    rcases h with h | h
    · exact ⟨d, Or.inl rfl, h⟩
    · exact ⟨ΩC + d, Or.inr rfl, by rw [h, gO_add, gO_ΩC, negOneO_mul_conj]⟩
  have hcent : Nat.card (Subgroup.centralizer ({y} : Set latticeO)) =
      Nat.card (Subgroup.centralizer ({gO d} : Set latticeO)) := by
    rw [hyc, card_centralizer_conj_singleton]
    rcases hd₁ with rfl | rfl
    · rfl
    · rw [gO_add, gO_ΩC, centralizer_negOneO_mul_typ]
  rcases hd' with rfl | rfl
  · exfalso
    rw [centIn, top_inf_eq, hcent, hcls.card_cent_oct] at hcard
    exact absurd hcard (by norm_num [co0C2, co0C3])
  · exact ⟨c, d₁, hd₁, hyc⟩

theorem pCoreOf_centIn_eq (hcls : Co0ClassData) {y c : latticeO}
    {d₁ : C} (hd₁ : d₁ = dod₂ ∨ d₁ = ΩC + dod₂) (hyc : y = c * gO d₁ * c⁻¹) :
    pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) = signSub.map (MulAut.conj c).toMonoidHom := by
  have h1 : centIn (⊤ : Subgroup latticeO) y =
      (Subgroup.centralizer {gO dod₂}).map (MulAut.conj c).toMonoidHom := by
    rw [centIn, top_inf_eq, hyc, centralizer_conj_singleton]
    rcases hd₁ with rfl | rfl
    · rfl
    · rw [gO_add, gO_ΩC, centralizer_negOneO_mul_typ]
  rw [h1, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj c),
    pCoreOf_centralizer_dod₂ hcls]

theorem signSub_map_conj_props (hcls : Co0ClassData)
    (c : latticeO) :
    negOneO ∈ signSub.map (MulAut.conj c).toMonoidHom ∧
    (∀ a ∈ signSub.map (MulAut.conj c).toMonoidHom, ∀ b ∈ signSub.map (MulAut.conj c).toMonoidHom,
      a * b = b * a) ∧
    (∀ a ∈ signSub.map (MulAut.conj c).toMonoidHom, a ^ 2 = 1) ∧
    Nat.card (signSub.map (MulAut.conj c).toMonoidHom) = 2 ^ 12 ∧
    (⊤ : Subgroup latticeO) ⊓
        Subgroup.centralizer ((signSub.map (MulAut.conj c).toMonoidHom : Subgroup latticeO) :
          Set latticeO) ≤ signSub.map (MulAut.conj c).toMonoidHom := by
  refine ⟨⟨negOneO, mem_signSub.2 ⟨ΩC, gO_ΩC.symm⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← negOneO_mul_comm c, mul_assoc, mul_inv_cancel, mul_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul]
    obtain ⟨a, rfl⟩ := mem_signSub.1 hx
    obtain ⟨b, rfl⟩ := mem_signSub.1 hx'
    rw [gO_comm]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    obtain ⟨a, rfl⟩ := mem_signSub.1 hx
    rw [pow_two, gO_mul_self, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, natCard_signSub]
  · rintro g ⟨-, hg⟩
    have hmem : c⁻¹ * g * c ∈ signSub := by
      refine centralizer_signSub_le hcls (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)
      have := Subgroup.mem_centralizer_iff.1 hg (c * v * c⁻¹) ⟨v, hv, rfl⟩
      calc v * (c⁻¹ * g * c) = c⁻¹ * (c * v * c⁻¹ * g) * c := by group
        _ = c⁻¹ * (g * (c * v * c⁻¹)) * c := by rw [this]
        _ = c⁻¹ * g * c * v := by group
    exact ⟨c⁻¹ * g * c, hmem, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem lat_pCore_typeC (hcls : Co0ClassData) :
    ∀ y, InvType (⊤ : Subgroup latticeO) negOneO co0C3 y →
      negOneO ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) ∧
      pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) ≤ (⊤ : Subgroup latticeO) ∧
      (∀ a ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y),
        ∀ b ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y), a * b = b * a) ∧
      (∀ a ∈ pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y), a ^ 2 = 1) ∧
      Nat.card (pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y)) = 2 ^ 12 ∧
      (⊤ : Subgroup latticeO) ⊓
          Subgroup.centralizer ((pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) :
            Subgroup latticeO) : Set latticeO) ≤
        pCoreOf 2 (centIn (⊤ : Subgroup latticeO) y) := by
  intro y hy
  obtain ⟨c, d₁, hd₁, hyc⟩ := typeC_form hcls hy
  rw [pCoreOf_centIn_eq hcls hd₁ hyc]
  obtain ⟨h1, h2, h3, h4, h5⟩ := signSub_map_conj_props hcls c
  exact ⟨h1, le_top, h2, h3, h4, h5⟩

end CFSG.EvenSporadicStandard.TwoCo1
