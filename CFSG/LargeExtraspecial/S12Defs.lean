module

public import CFSG.LargeExtraspecial.S12Good
public import CFSG.LargeExtraspecial.S12Cent
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

theorem s12_isTypeA_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V} {t g : V ≃ₗ[ZMod 2] V} {l : ℕ}
    (ht : IsTypeA q t l) (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) :
    IsTypeA q (g * t * g⁻¹) l := by
  obtain ⟨hiso, hne, hinv, hdim, hsing⟩ := ht
  have hg' : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup q := inv_mem hg
  refine ⟨fun v => ?_, fun h => hne ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hiso,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg']
  · calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hinv, mul_one, mul_inv_cancel]
  · rw [finrank_commSpace_conj, hdim]
  · intro x hx
    rw [commSpace_conj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change q (g y) = 0
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hsing y hy]

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def Ebar12 (g : G) : Set S.O :=
  {τ | τ ∈ S.Mbar ∧ IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
    ∃ m ∈ S.Mbar, m * τ * m⁻¹ ∈ S.Lbar g}

@[expose] noncomputable def Xbar12 (g : G) : Subgroup S.O := closure (S.Ebar12 g)

variable {S}

theorem Ebar12_subset_Mbar {g : G} : S.Ebar12 g ⊆ S.Mbar := fun _ h => h.1

theorem Xbar12_le_Mbar {g : G} : S.Xbar12 g ≤ S.Mbar :=
  (closure_le _).mpr Ebar12_subset_Mbar

theorem subset_Xbar12 {g : G} : S.Ebar12 g ⊆ S.Xbar12 g := subset_closure

theorem isTypeA_of_mem_Ebar12 {g : G} {τ : S.O} (h : τ ∈ S.Ebar12 g) :
    IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := h.2.1

theorem conj_mem_Ebar12 {g : G} {m τ : S.O} (hm : m ∈ S.Mbar) (hτ : τ ∈ S.Ebar12 g) :
    m * τ * m⁻¹ ∈ S.Ebar12 g := by
  obtain ⟨hτM, hA, m', hm', hL⟩ := hτ
  refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hm hτM) (S.Mbar.inv_mem hm), ?_, m' * m⁻¹,
    S.Mbar.mul_mem hm' (S.Mbar.inv_mem hm), ?_⟩
  · exact s12_isTypeA_conj hA m.2
  · rw [show m' * m⁻¹ * (m * τ * m⁻¹) * (m' * m⁻¹)⁻¹ = m' * τ * m'⁻¹ by group]
    exact hL

theorem Mbar_le_normalizer_Xbar12 {g : G} : S.Mbar ≤ normalizer (S.Xbar12 g : Set S.O) := by
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : ∀ {m : S.O}, m ∈ S.Mbar →
      (S.Xbar12 g).map (MulAut.conj m).toMonoidHom ≤ S.Xbar12 g := by
    intro m hm
    rw [Xbar12, MonoidHom.map_closure, closure_le]
    rintro _ ⟨τ, hτ, rfl⟩
    exact subset_closure (conj_mem_Ebar12 hm hτ)
  refine le_antisymm (hle hm) ?_
  intro x hx
  refine ⟨m⁻¹ * x * m, hle (S.Mbar.inv_mem hm) ⟨x, hx, ?_⟩, ?_⟩
  · simp
  · simp [mul_assoc]

theorem mem_Ebar12_of_mem_Lbar {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (hA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) : t ∈ S.Ebar12 g :=
  ⟨S.Lbar_le_Mbar g ht, hA, 1, S.Mbar.one_mem, by simpa using ht⟩

variable (S)

omit [Finite G] in
theorem s12_conj_mem {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (h : S.M) :
    ((h : G) * g) * S.z * ((h : G) * g)⁻¹ ∈ S.QG ∧
      ((h : G) * g) * S.z * ((h : G) * g)⁻¹ ≠ S.z := by
  rw [S.s12_mul_conj_z]
  refine ⟨S.conj_mem_QG h.2 haQ, fun h' => hne ?_⟩
  calc g * S.z * g⁻¹ = (h : G)⁻¹ * ((h : G) * (g * S.z * g⁻¹) * (h : G)⁻¹) * h := by group
    _ = (h : G)⁻¹ * S.z * (h : G)⁻¹⁻¹ := by rw [h']; group
    _ = S.z := S.s12_conj_z_of_mem_M (S.M.inv_mem h.2)

theorem s12_exists_Lbar_of_mem_Ebar12 {g : G} {τ : S.O} (hτ : τ ∈ S.Ebar12 g) :
    ∃ h : S.M, τ ∈ S.Lbar ((h : G) * g) := by
  obtain ⟨-, -, m, hm, hL⟩ := hτ
  obtain ⟨h₀, rfl⟩ := hm
  refine ⟨h₀⁻¹, ?_⟩
  rw [S.s12_Lbar_mul]
  refine ⟨S.ρ h₀ * τ * (S.ρ h₀)⁻¹, hL, ?_⟩
  simp [map_inv, mul_assoc]

theorem s12_Ebar12_mul (g : G) (h : S.M) : S.Ebar12 ((h : G) * g) = S.Ebar12 g := by
  ext τ
  simp only [Ebar12, Set.mem_ofPred_eq, S.s12_Lbar_mul]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨m, hm, x, hx, hxe⟩
    refine ⟨(S.ρ h)⁻¹ * m, S.Mbar.mul_mem (S.Mbar.inv_mem ⟨h, rfl⟩) hm, ?_⟩
    have e : (S.ρ h)⁻¹ * m * τ * ((S.ρ h)⁻¹ * m)⁻¹ = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
      rw [show (S.ρ h)⁻¹ * m * τ * ((S.ρ h)⁻¹ * m)⁻¹ =
        (S.ρ h)⁻¹ * (m * τ * m⁻¹) * S.ρ h by group, ← hxe]
      group
    rw [e]
    exact hx
  · rintro ⟨m, hm, hx⟩
    refine ⟨S.ρ h * m, S.Mbar.mul_mem ⟨h, rfl⟩ hm, m * τ * m⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem s12_eq_bot_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {K : Subgroup S.O} (hK : S12NoNormalTwo K) (hKM : K ≤ S.Mbar)
    (hfix : ∀ k ∈ K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hLK : S.Lbar g ≤ normalizer (K : Set S.O)) : K = ⊥ := by
  have hKN : K ≤ normalizer (S.Lbar g : Set S.O) := by
    intro k hk
    obtain ⟨h, hh⟩ := hKM hk
    rw [← hh] at hk ⊢
    exact (S.timmesfeld_12_4_1 haQ hne hn h).mpr (hfix _ hk)
  have hLp : IsPGroup 2 (S.Lbar g) := by
    intro x
    have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
    exact ⟨1, Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian _ x.2)⟩
  have hdisj : S.Lbar g ⊓ K = ⊥ := by
    refine hK _ inf_le_right (hLp.to_le inf_le_left) ?_
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxL, hxK⟩
      exact ⟨(mem_normalizer_iff.mp (hKN hk) x).mp hxL, K.mul_mem (K.mul_mem hk hxK)
        (K.inv_mem hk)⟩
    · rintro ⟨hxL, hxK⟩
      refine ⟨(mem_normalizer_iff.mp (hKN hk) x).mpr hxL, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      simpa [mul_assoc] using this
  have hcomm : K ≤ S.Mbar ⊓ centralizer (S.Lbar g : Set S.O) := by
    intro k hk
    refine ⟨hKM hk, mem_centralizer_iff.mpr fun ℓ hℓ => ?_⟩
    have h1 : k * ℓ * k⁻¹ * ℓ⁻¹ ∈ S.Lbar g ⊓ K := by
      refine ⟨(S.Lbar g).mul_mem ((mem_normalizer_iff.mp (hKN hk) ℓ).mp hℓ)
        ((S.Lbar g).inv_mem hℓ), ?_⟩
      have h2 : ℓ * k⁻¹ * ℓ⁻¹ ∈ K := (mem_normalizer_iff.mp (hLK hℓ) _).mp (K.inv_mem hk)
      have e : k * ℓ * k⁻¹ * ℓ⁻¹ = k * (ℓ * k⁻¹ * ℓ⁻¹) := by group
      rw [e]
      exact K.mul_mem hk h2
    rw [hdisj, mem_bot] at h1
    calc ℓ * k = (k * ℓ * k⁻¹ * ℓ⁻¹)⁻¹ * (k * ℓ) := by group
      _ = k * ℓ := by rw [h1, inv_one, one_mul]
  have hKp : IsPGroup 2 K := (S.timmesfeld_12_4_2 haQ hne hn).to_le hcomm
  exact hK K le_rfl hKp (le_normalizer)

end Setting

end CFSG.LargeExtraspecial
