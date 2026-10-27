module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LE25Shape
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseES2
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseES3

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Struct

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem caseES_mem_iff_of_map_eq {n : V ≃ₗ[ZMod 2] V} {W W' : Submodule (ZMod 2) V}
    (hW : W.map (n : V →ₗ[ZMod 2] V) = W') (v : V) : n v ∈ W' ↔ v ∈ W := by
  rw [← hW]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = v := n.injective hwv
    rwa [← this]
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem e25_struct (H : HypYW ρ t u x h) (hsh : E25Shape ρ x t) :
    Nonempty (normalClosure ({x} : Set Y) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) ∧
    (∀ S : Sylow 2 Y, t ∈ S → ∀ g : Y, g * t * g⁻¹ ∈ S → ∃ s ∈ S, s * t * s⁻¹ = g * t * g⁻¹) ∧
    Nat.card Y ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 ∧
    (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F ≤ 8) := by
  obtain ⟨h25, V₁, V₂, hd₁, hcompl, -, hstab, hperm, -, K₁, K₂, hK₁J, hK₂J, hbot, hsup, hc₁, hc₂,
    hfix₁, hfix₂⟩ := hsh
  have hx5 : x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one x
  have D : E25Data (Jbar ρ x) (ρ x) K₁ K₂ V₁ V₂ :=
    { dim := H.dim
      card := h25
      mem_x := E25_rho_mem_Jbar ρ x
      pow_x := by rw [← map_pow, hx5, map_one]
      fix_x := H.fix
      dim₁ := hd₁
      compl := hcompl
      stab := hstab
      le₁ := hK₁J
      le₂ := hK₂J
      bot := hbot
      sup := hsup
      card₁ := hc₁
      card₂ := hc₂
      fix₁ := hfix₁
      fix₂ := hfix₂ }
  have hZ : Nonempty (normalClosure ({x} : Set Y) ≃*
      Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) := by
    obtain ⟨e⟩ := D.equivZMod
    exact ⟨(Subgroup.equivMapOfInjective _ ρ H.inj).trans e⟩
  have hnorm : ∀ y : Y, ρ y ∈ normalizer ((Jbar ρ x : Subgroup (V ≃ₗ[ZMod 2] V)) : Set _) := by
    intro y
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · have := E25_Jbar_conj ρ x y⁻¹ hg
      simpa using this
    · have := E25_Jbar_conj ρ x y hg
      simpa [mul_assoc] using this
  have hswap : ∀ y : Y, ρ y ∈ caseES_fixPair V₁ V₂ ∨
      ((∀ v, ρ y v ∈ V₁ ↔ v ∈ V₂) ∧ (∀ v, ρ y v ∈ V₂ ↔ v ∈ V₁)) := by
    intro y
    rcases hperm y with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl fun v => ⟨caseES_mem_iff_of_map_eq e1 v, caseES_mem_iff_of_map_eq e2 v⟩
    · exact Or.inr ⟨caseES_mem_iff_of_map_eq e2, caseES_mem_iff_of_map_eq e1⟩
  set J : Subgroup (V ≃ₗ[ZMod 2] V) := Jbar ρ x
  let N : Subgroup (V ≃ₗ[ZMod 2] V) := normalizer (J : Set (V ≃ₗ[ZMod 2] V)) ⊓ caseES_fixPair V₁ V₂
  let Y₀ : Subgroup Y := N.comap ρ
  let C : Subgroup Y := (centralizer (J : Set (V ≃ₗ[ZMod 2] V))).comap ρ
  have hY₀ : ∀ a b : Y, a ∉ Y₀ → b ∉ Y₀ → a * b ∈ Y₀ := by
    intro a b ha hb
    have ha' : ¬ ρ a ∈ caseES_fixPair V₁ V₂ := fun h' => ha ⟨hnorm a, h'⟩
    have hb' : ¬ ρ b ∈ caseES_fixPair V₁ V₂ := fun h' => hb ⟨hnorm b, h'⟩
    obtain ⟨ha1, ha2⟩ := (hswap a).resolve_left ha'
    obtain ⟨hb1, hb2⟩ := (hswap b).resolve_left hb'
    refine ⟨hnorm (a * b), fun v => ?_⟩
    rw [map_mul]
    exact ⟨(ha1 (ρ b v)).trans (hb2 v), (ha2 (ρ b v)).trans (hb1 v)⟩
  obtain ⟨Φ, hΦ⟩ := D.exists_phi
  let φ : Y₀ →* (ZMod 5)ˣ × (ZMod 5)ˣ := Φ.comp (ρ.subgroupComap N)
  have hker : ∀ y : Y₀, φ y = 1 ↔ (y : Y) ∈ C := fun y => (hΦ (ρ.subgroupComap N y)).trans Iff.rfl
  have hCY₀ : C ≤ Y₀ := by
    intro c hc
    have hc' : ρ c ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V)) := hc
    exact ⟨hnorm c, fun v => ⟨D.iff₁ hc' v, D.swap.iff₁ hc' v⟩⟩
  haveI hCnormal : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    have hc' : ∀ j ∈ J, j * ρ c = ρ c * j := mem_centralizer_iff.mp hc
    show ρ (g * c * g⁻¹) ∈ centralizer (J : Set (V ≃ₗ[ZMod 2] V))
    rw [mem_centralizer_iff]
    intro j hj
    have hj' : (ρ g)⁻¹ * j * ρ g ∈ J := E25_Jbar_conj ρ x g hj
    have hcomm := hc' _ hj'
    rw [map_mul, map_mul, map_inv]
    calc j * (ρ g * ρ c * (ρ g)⁻¹) = ρ g * (((ρ g)⁻¹ * j * ρ g) * ρ c) * (ρ g)⁻¹ := by group
      _ = ρ g * (ρ c * ((ρ g)⁻¹ * j * ρ g)) * (ρ g)⁻¹ := by rw [hcomm]
      _ = ρ g * ρ c * (ρ g)⁻¹ * j := by group
  have hC225 : Nat.card C ∣ 225 := by
    have h1 : Nat.card C = Nat.card (C.map ρ) := (Subgroup.card_map_of_injective H.inj).symm
    have h2 : C.map ρ ≤ centralizer (J : Set (V ≃ₗ[ZMod 2] V)) := Subgroup.map_comap_le _ _
    rw [h1]
    exact (Subgroup.card_dvd_of_le h2).trans D.card_centralizer_dvd
  have hCodd : Odd (Nat.card C) := Odd.of_dvd_nat (by decide) hC225
  have hidx : C.index ∣ 2 ^ 5 := caseES_index_dvd_two_pow_five hCY₀ hY₀ φ hker
  refine ⟨hZ, fun S ht g hg => caseES_p3_of_odd_normal C hCodd ?_ S ht hg,
    caseES_card_dvd (by rw [show 3 ^ 2 * 5 ^ 2 = 225 by norm_num]; exact hC225) hidx,
    fun F hF => caseES_card_elemAb_le_eight hCodd hY₀ φ (fun y hy => (hker y).mp hy) F hF⟩
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx
  exact ⟨n, hn⟩

end Struct

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
