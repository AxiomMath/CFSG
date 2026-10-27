module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Odd
public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.good_of_gl2 (hD : TightDatum R S t) {N H : Subgroup Y} [N.Normal]
    (hHN : H ≤ N) (hHt : H ≤ Subgroup.centralizer {t}) (hHp : ⁅H, H⁆ = H)
    (hmax : ∀ M : Subgroup Y, M ≤ N → M ≤ Subgroup.centralizer {t} → ⁅M, M⁆ = M → M ≤ H)
    (hRH : R ≤ Subgroup.centralizer (H : Set Y)) {θ : GL (Fin 2) (ZMod 3) →* Y}
    (hθ : Function.Injective θ)
    (hθr : θ.range = N ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer (H : Set Y))
    (hθ1 : θ (-1) = t) {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    GoodThreeElement R t := by
  have hNn : N.Normal := inferInstance
  have hθm : ∀ A, θ A ∈ N ∧ θ A ∈ Subgroup.centralizer ({t} : Set Y) ∧
      θ A ∈ Subgroup.centralizer (H : Set Y) := fun A => by
    have : θ A ∈ θ.range := ⟨A, rfl⟩
    rw [hθr] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hpull : ∀ g ∈ N, g ∈ Subgroup.centralizer ({t} : Set Y) →
      g ∈ Subgroup.centralizer (H : Set Y) → ∃ A, θ A = g := fun g hgN hgt hgH => by
    have : g ∈ N ⊓ Subgroup.centralizer {t} ⊓ Subgroup.centralizer (H : Set Y) := ⟨⟨hgN, hgt⟩, hgH⟩
    rw [← hθr] at this
    exact this
  have hO : ∀ o ∈ oddCoreImg R, o ∈ N → o = 1 := fun o ho hoN =>
    TightDatum.oddCore_eq_one_of_gl2 hD hRH hθ hθr hθ1 ho hoN
  have hcN : ∀ a b : Y, a ∈ N → ⁅b, a⁆ ∈ N := fun a b ha => by
    rw [commutatorElement_def]
    exact N.mul_mem (hNn.conj_mem a ha b) (N.inv_mem ha)
  obtain ⟨S₀, rfl⟩ := hpull s hsN (hD.cent hsR) (hRH hsR)
  have hS4 : orderOf S₀ = 4 := by rwa [orderOf_injective θ hθ] at hs4
  obtain ⟨hxN, hxt, hxH⟩ := hθm X₃
  refine ⟨θ X₃, 1, hxt, by rw [pow_one, ← map_pow, X₃_pow_three, map_one],
    ⟨θ S₀, hsR, fun hc => ?_⟩, fun y hyt hyR => ?_⟩
  · have h1 := hO _ hc (by
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hxN hsN) (N.inv_mem hxN)) (N.inv_mem hsN))
    exact not_comm_X₃ hS4 (hθ (by
      rw [map_mul, map_mul]
      exact commutatorElement_eq_one_iff_mul_comm.mp h1))
  have hyH : ∀ y' ∈ Subgroup.centralizer ({t} : Set Y), ∀ h ∈ H, y' * h * y'⁻¹ ∈ H := by
    intro y' hy' h hh
    refine hmax (H.map (MulAut.conj y').toMonoidHom) ?_ ?_ ?_ ⟨h, hh, rfl⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact hNn.conj_mem k (hHN hk) y'
    · rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy' (hHt hk)) (Subgroup.inv_mem _ hy')
    · rw [← Subgroup.map_commutator, hHp]
  have hyq : ∀ q ∈ R, q ∈ N → y * q = q * y := fun q hq hqN =>
    commutatorElement_eq_one_iff_mul_comm.mp (hO _ (hyR q hq) (hcN q y hqN))
  have hxq : ∀ q ∈ R, q ∈ N → θ X₃ * q * (θ X₃)⁻¹ ∈ R ∧ θ X₃ * q * (θ X₃)⁻¹ ∈ N :=
    fun q hq hqN => ⟨(Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hxt) q).mp hq,
      hNn.conj_mem q hqN _⟩
  set z := y * θ X₃ * y⁻¹ with hz
  have hg₀N : (θ X₃)⁻¹ * z ∈ N := N.mul_mem (N.inv_mem hxN) (hNn.conj_mem _ hxN y)
  have hg₀t : (θ X₃)⁻¹ * z ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxt)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyt hxt) (Subgroup.inv_mem _ hyt))
  have hzH : ∀ h ∈ H, h * z = z * h := fun h hh => by
    have h1 := Subgroup.mem_centralizer_iff.mp hxH _ (hyH _ (Subgroup.inv_mem _ hyt) h hh)
    rw [inv_inv] at h1
    calc h * z = y * (y⁻¹ * h * y * θ X₃) * y⁻¹ := by rw [hz]; group
      _ = y * (θ X₃ * (y⁻¹ * h * y)) * y⁻¹ := by rw [h1]
      _ = z * h := by rw [hz]; group
  have hg₀H : (θ X₃)⁻¹ * z ∈ Subgroup.centralizer (H : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hxc : Commute h (θ X₃) := Subgroup.mem_centralizer_iff.mp hxH h hh
    exact (hxc.inv_right.mul_right (hzH h hh : Commute h z)).eq
  have hg₀q : ∀ q ∈ R, q ∈ N → (θ X₃)⁻¹ * z * q = q * ((θ X₃)⁻¹ * z) := by
    intro q hq hqN
    have h1 := hyq q hq hqN
    have h2 := hyq _ (hxq q hq hqN).1 (hxq q hq hqN).2
    have hzq : z * q * z⁻¹ = θ X₃ * q * (θ X₃)⁻¹ := by
      calc z * q * z⁻¹ = y * θ X₃ * (y⁻¹ * q * y) * (θ X₃)⁻¹ * y⁻¹ := by rw [hz]; group
        _ = y * (θ X₃ * q * (θ X₃)⁻¹) * y⁻¹ := by
            rw [show y⁻¹ * q * y = q by rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel,
              one_mul]]
            group
        _ = θ X₃ * q * (θ X₃)⁻¹ := by rw [h2, mul_inv_cancel_right]
    calc (θ X₃)⁻¹ * z * q = (θ X₃)⁻¹ * (z * q * z⁻¹) * z := by group
      _ = q * ((θ X₃)⁻¹ * z) := by rw [hzq]; group
  obtain ⟨A₀, hA₀⟩ := hpull _ hg₀N hg₀t hg₀H
  have h1 : A₀ * S₀ = S₀ * A₀ := hθ (by rw [map_mul, map_mul, hA₀]; exact hg₀q _ hsR hsN)
  have h2 : A₀ * (X₃ * S₀ * X₃⁻¹) = X₃ * S₀ * X₃⁻¹ * A₀ := hθ (by
    simp only [map_mul, map_inv, hA₀]
    exact hg₀q _ (hxq _ hsR hsN).1 (hxq _ hsR hsN).2)
  have hz3 : z ^ 3 = 1 := by
    rw [hz, conj_pow, ← map_pow, X₃_pow_three, map_one, mul_one, mul_inv_cancel]
  rcases eq_or_of_comm_q8 hS4 h1 h2 with rfl | rfl
  · rw [map_one] at hA₀
    have hzx : z = θ X₃ := by rw [← mul_one (θ X₃), hA₀]; group
    have : ⁅θ X₃, y⁆ = 1 := by
      rw [commutatorElement_def]
      rw [hz] at hzx
      calc θ X₃ * y * (θ X₃)⁻¹ * y⁻¹ = θ X₃ * (y * θ X₃ * y⁻¹)⁻¹ := by group
        _ = 1 := by rw [hzx, mul_inv_cancel]
    rw [this]
    exact Subgroup.one_mem _
  · exfalso
    have hzx : z = θ (X₃ * -1) := by rw [map_mul, hA₀]; group
    rw [hzx, ← map_pow] at hz3
    exact X₃_neg_pow_three (hθ (hz3.trans (map_one θ).symm))

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
