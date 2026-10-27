module

public import CFSG.LargeExtraspecial.GLRElimMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem false_of_sq_eq_z_of_inv [IsSimpleGroup G] {σ : G} (hσM : σ ∈ S.M) (hσX : σ ∉ C.X)
    (hσz : σ * σ = S.z) (hβ : IsGoodForm (C.formOf (S.ρ ⟨σ, hσM⟩)))
    (hinv : ∀ y ∈ S.M, y * y = 1 → y ∈ C.X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizer {σ} ≤ S.M := by
    intro g hg
    have h1 := mem_centralizer_singleton_iff.mp hg
    rw [S.mem_M_iff, ← hσz]
    calc g * (σ * σ) = (g * σ) * σ := by group
      _ = (σ * g) * σ := by rw [h1]
      _ = σ * (g * σ) := by group
      _ = σ * (σ * g) := by rw [h1]
      _ = σ * σ * g := by group
  obtain ⟨S₁, -, hS₁⟩ := exists_isSylowIn_le (H := centralizer {σ}) bot_le IsPGroup.of_bot
  have hσ4 : σ ^ 4 = 1 := by
    rw [show σ ^ 4 = (σ * σ) * (σ * σ) by
      rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one, mul_assoc],
      hσz, S.z_mul_z]
  have hσS₁ : σ ∈ S₁ := by
    have hle := SylowIn.le_of_normal hS₁ (N := zpowers σ)
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (fun g => by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
        refine ⟨2, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
          zpow_mul', show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, hσ4,
          one_zpow])
      (fun g hg y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        have h1 : Commute g σ := mem_centralizer_singleton_iff.mp hg
        rw [(h1.zpow_right k).eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers σ) k)
    exact hle (mem_zpowers σ)
  obtain ⟨T, hS₁T, hT⟩ := exists_isSylowIn_le (H := S.M) ((SylowIn.le hS₁).trans hCM)
    (SylowIn.isPGroup hS₁)
  have hTG := Config.sylowIn_top hT
  have hσT := hS₁T hσS₁
  have hTM : T ≤ S.M := SylowIn.le hT
  have hUidx := C.relIndex_inf_X hTM hσT hσX
  obtain ⟨x, hxU, hext⟩ := exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup C.exists_mul_ne
    (SylowIn.isPGroup hTG) (not_dvd_index_of_sylowIn_top hTG) inf_le_left hUidx hσT
    (fun h => hσX h.2) hσz S.z_mul_z (fun x hx => ⟨hx, hinv _ (hTM hx) (by
      calc x⁻¹ * S.z * x * (x⁻¹ * S.z * x) = x⁻¹ * (S.z * S.z) * x := by group
        _ = 1 := by rw [S.z_mul_z, mul_one, inv_mul_cancel])⟩)
  set y := x⁻¹ * σ * x with hy
  let K : Subgroup G := S₁.map (MulAut.conj x⁻¹).toMonoidHom
  have hKC : K ≤ centralizer {y} := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp ((SylowIn.le hS₁) hs)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mem_centralizer_singleton_iff]
    calc x⁻¹ * s * x * y = x⁻¹ * (s * σ) * x := by rw [hy]; group
      _ = x⁻¹ * (σ * s) * x := by rw [h1]
      _ = y * (x⁻¹ * s * x) := by rw [hy]; group
  obtain ⟨c, hc, hcK⟩ := exists_conj_into_sylow hKC ((SylowIn.isPGroup hS₁).map _) hext.1
    hext.2.1 hext.2.2
  set g := x * c with hg
  have hgS : ∀ s ∈ S₁, g⁻¹ * s * g ∈ T ⊓ centralizer {y} := fun s hs => by
    have := hcK _ ⟨s, hs, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    rw [hg, show (x * c)⁻¹ * s * (x * c) = c⁻¹ * (x⁻¹ * s * x) * c by group]
    exact this
  let K' : Subgroup G := S₁.map (MulAut.conj g⁻¹).toMonoidHom
  have hK'le : K' ≤ T ⊓ centralizer {y} := by
    rintro _ ⟨s, hs, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hgS s hs
  have hK'card : Nat.card (T ⊓ centralizer {y} : Subgroup G) ≤ Nat.card K' := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, card_eq_of_sylowIn hext,
      card_eq_of_sylowIn hS₁, hy, card_centralizer_conj]
  have hK'eq := Subgroup.eq_of_le_of_card_ge hK'le hK'card
  have hzT : S.z ∈ T ⊓ centralizer {y} :=
    ⟨Config.QG_le_of_sylowIn hT S.z_mem_QG,
      mem_centralizer_singleton_iff.mpr (S.z_comm (hTM hxU.1)).symm⟩
  rw [← hK'eq] at hzT
  obtain ⟨w₀, hw₀, hw₀z⟩ := hzT
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hw₀z
  have hw : g * S.z * g⁻¹ ∈ S₁ := by
    rw [← hw₀z, show g * (g⁻¹ * w₀ * g) * g⁻¹ = w₀ by group]
    exact hw₀
  have hwc : ∀ s ∈ S₁, (g * S.z * g⁻¹) * s = s * (g * S.z * g⁻¹) := by
    intro s hs
    have h1 := S.z_comm (hTM (hgS s hs).1)
    calc g * S.z * g⁻¹ * s = g * (S.z * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * S.z) * g⁻¹ := by rw [h1]
      _ = s * (g * S.z * g⁻¹) := by group
  have hwM : g * S.z * g⁻¹ ∈ S.M := hCM (SylowIn.le hS₁ hw)
  have hwX : g * S.z * g⁻¹ ∈ C.X := hinv _ hwM (by
    calc g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z, mul_one, mul_inv_cancel])
  have hCQ : S.QG ⊓ centralizer {σ} ≤ S₁ := SylowIn.le_of_normal hS₁ inf_le_right
    ((Config.isPGroup_QG S).to_le inf_le_left) (fun g' hg' q hq => mem_inf.mpr
      ⟨S.conj_mem_QG (hCM hg') hq.1, mem_centralizer_singleton_iff.mpr (by
        have h1 := mem_centralizer_singleton_iff.mp hg'
        have h2 := mem_centralizer_singleton_iff.mp hq.2
        calc g' * q * g'⁻¹ * σ = g' * q * (g'⁻¹ * (σ * g')) * g'⁻¹ := by group
          _ = g' * q * (g'⁻¹ * (g' * σ)) * g'⁻¹ := by rw [h1]
          _ = g' * (q * σ) * g'⁻¹ := by group
          _ = g' * (σ * q) * g'⁻¹ := by rw [h2]
          _ = (g' * σ) * q * g'⁻¹ := by group
          _ = (σ * g') * q * g'⁻¹ := by rw [h1]
          _ = σ * (g' * q * g'⁻¹) := by group)⟩)
  have hwQ : g * S.z * g⁻¹ ∈ S.QG := Config.mem_QG_of_commute hσM hσX (Or.inr hσz) hβ hwX
    fun q hq hqσ => hwc q (hCQ ⟨hq, mem_centralizer_singleton_iff.mpr hqσ.symm⟩)
  have hwz := Config.conj_eq_z_of_commute hσM hσX hwQ (hwc σ hσS₁).symm
  have hgM : g ∈ S.M := S.mem_M_iff.mpr (by
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [hwz])
  have hcy := mem_centralizer_singleton_iff.mp hc
  have hyg : g⁻¹ * σ * g = y := by
    calc g⁻¹ * σ * g = c⁻¹ * y * c := by rw [hg, hy]; group
      _ = c⁻¹ * (c * y) := by rw [mul_assoc, ← hcy]
      _ = y := by group
  apply hσX
  have := C.conj_mem_X hgM hxU.2
  rwa [← hyg, show g * (g⁻¹ * σ * g) * g⁻¹ = σ by group] at this

end CFSG.LargeExtraspecial.GLW4
