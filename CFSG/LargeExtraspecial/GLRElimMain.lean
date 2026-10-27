module

public import CFSG.LargeExtraspecial.GLRElimBound
public import CFSG.LargeExtraspecial.GLRElimOrder
public import CFSG.LargeExtraspecial.GLRElimComm
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_centralizer_conj (x g : G) :
    Nat.card (centralizer {x⁻¹ * g * x}) = Nat.card (centralizer {g}) := by
  have h : (centralizer {g}).map (MulAut.conj x⁻¹).toMonoidHom = centralizer {x⁻¹ * g * x} := by
    ext c
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨d, hd, rfl⟩
      calc x⁻¹ * d * x * (x⁻¹ * g * x) = x⁻¹ * (d * g) * x := by group
        _ = x⁻¹ * (g * d) * x := by rw [hd]
        _ = _ := by group
    · intro hc
      refine ⟨x * c * x⁻¹, ?_, by group⟩
      calc x * c * x⁻¹ * g = x * (c * (x⁻¹ * g * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * g * x) * c) * x⁻¹ := by rw [hc]
        _ = _ := by group
  rw [← h, card_map_of_injective (MulAut.conj x⁻¹).injective]

theorem card_eq_of_sylowIn {T H : Subgroup G} (hT : IsSylowIn 2 T H) :
    Nat.card T = 2 ^ (Nat.card H).factorization 2 := by
  obtain ⟨k, hk⟩ := (SylowIn.isPGroup hT).exists_card_eq
  rw [SylowIn.factorization_eq hT, hk, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]

omit [Finite G] in
theorem not_dvd_index_of_sylowIn_top {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) :
    ¬ 2 ∣ T.index := by
  have := hT.2.2
  rwa [relIndex_top_right] at this

variable {S : Setting G}

namespace Config

variable (C : Config S)

include C in
theorem exists_mul_ne : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := C.At) (by
    intro h
    have := C.finrank_At
    rw [h, finrank_bot] at this
    have := C.four_le_width
    omega)
  by_contra! hall
  apply hv0
  refine C.eq_zero_of_mem_At_of_forall_polar hv fun w hw => ?_
  obtain ⟨x, hx, rfl⟩ := S.exists_cl w
  obtain ⟨y, hy, rfl⟩ := S.exists_cl v
  exact (S.polar_cl_eq_zero_iff hx hy).mpr (hall x y)

end Config

namespace Levi

variable {C : Config S} (Λ : Levi C)

theorem false_of_involution [IsSimpleGroup G] (h5 : 5 ≤ S.width) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hτL : Λ.Normalizes τ) (hττ : τ * τ = 1)
    (hβ : IsGoodForm (C.formOf (S.ρ ⟨τ, hτM⟩))) : False := by
  obtain ⟨S₁, hS₁, hzS₁⟩ := Λ.exists_sylowIn_z_mem_commutator hτM hτX hτL hττ hβ
  have hS₁G := sylowIn_centralizer hτM hτX hττ hβ hS₁ hzS₁
  have hcard := card_le_of_sylowIn hτM hτX hττ hβ hS₁
  have hv : (Nat.card (centralizer {τ})).factorization 2 ≤
      2 + 2 * (S.width / 2) + (S.width / 2) ^ 2 := by
    rw [card_eq_of_sylowIn hS₁G] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hτS₁ := mem_of_sylowIn hτM hττ hS₁
  obtain ⟨T, hS₁T, hT⟩ := exists_isSylowIn_le (H := S.M) (fun t ht => (SylowIn.le hS₁ ht).2)
    (SylowIn.isPGroup hS₁)
  have hTG := Config.sylowIn_top hT
  have hτT := hS₁T hτS₁
  have hUidx := C.relIndex_inf_X (SylowIn.le hT) hτT hτX
  obtain ⟨x, hxU, -⟩ := exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup C.exists_mul_ne
    (SylowIn.isPGroup hTG) (not_dvd_index_of_sylowIn_top hTG) inf_le_left hUidx hτT
    (fun h => hτX h.2) hττ (mul_one 1) (fun x _ => by simp)
  have hyX : x⁻¹ * τ * x ∈ C.X := hxU.2
  have hyy : (x⁻¹ * τ * x) * (x⁻¹ * τ * x) = 1 := by
    calc (x⁻¹ * τ * x) * (x⁻¹ * τ * x) = x⁻¹ * (τ * τ) * x := by group
      _ = 1 := by rw [hττ, mul_one, inv_mul_cancel]
  have h34 := C.lt_factorization_card_centralizer h5 (C.X_le_normalizer hyX) hyy
  rw [card_centralizer_conj] at h34
  omega

theorem false_of_sq_eq_z [IsSimpleGroup G] {σ : G} (hσM : σ ∈ S.M) (hσX : σ ∉ C.X)
    (hσL : Λ.Normalizes σ) (hσz : σ * σ = S.z) (hβ : IsGoodForm (C.formOf (S.ρ ⟨σ, hσM⟩))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ y ∈ S.M, y * y = 1 → y ∈ C.X := fun y hy hyy => by
    by_contra hyX
    exact Λ.mul_self_ne_one hσM hσX hσL hσz hy hyX hyy
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

end Levi

theorem false_of_config {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G}
    (C : Config S) (h5 : 5 ≤ S.width) : False := by
  obtain ⟨Λ⟩ := C.nonempty_levi h5
  obtain ⟨β, hβ⟩ := exists_isGoodForm (V := C.At) (by
    rw [C.finrank_At]
    omega)
  obtain ⟨σ, hσM, hσX, hσL, hσ2, hσβ⟩ := Λ.exists_sigma_formOf_eq β hβ.symm
    fun a' ha' => hβ.nondeg a' fun a => (hβ.symm a' a).trans (ha' a)
  rw [← hσβ] at hβ
  rcases hσ2 with h1 | hz
  · exact Λ.false_of_involution h5 hσM hσX hσL h1 hβ
  · exact Λ.false_of_sq_eq_z hσM hσX hσL hz hβ

end CFSG.LargeExtraspecial.GLR
