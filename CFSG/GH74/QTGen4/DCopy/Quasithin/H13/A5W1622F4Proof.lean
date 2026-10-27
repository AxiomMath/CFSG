module

public import CFSG.Quasithin.H13.A5W1622F4P2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622F4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622F4L45C

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem c134Case4F_of_lemma45_F4 (h45 : C134Case4Lemma45Corr_F4) : C134Case4F_F4 := by
  intro G _ _ G₀ R L hMS hL hset h4 c hc y hy hyc
  have hyΦ := h45 G G₀ R L hMS hL hset h4 y hy fun x hx =>
    (Subgroup.zpowers_le.mpr hc) (hyc x hx)
  obtain ⟨⟨n, F, _, _, α, hF, hα, hCE, hZ, -, -, hΦ, -, hQ⟩, -⟩ := h4
  set Q := c134Q G₀ L with hQdef
  set Φ := frattiniIn Q with hΦdef

  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    omega
  have h2 : (2 : F) = 0 := by
    have h1 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h1
    exact pow_eq_zero_iff hn |>.mp h1

  have hcZ : c ∈ centerOf Q := hZ ▸ Subgroup.mem_sup_left hc
  have hcc : c * c = 1 := by
    obtain ⟨e⟩ := hCE
    have h1 : e (⟨c, hc⟩ * ⟨c, hc⟩) = e 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      show Multiplicative.toAdd (e ⟨c, hc⟩) i + Multiplicative.toAdd (e ⟨c, hc⟩) i = 0
      generalize Multiplicative.toAdd (e ⟨c, hc⟩) i = a
      revert a
      decide
    exact congrArg Subtype.val (e.injective h1)
  have hcQ : ∀ x ∈ Q, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hcZ.2 x hx
  have hcL : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hc.2 l hl
  have hZc : ∀ z ∈ centerOf Q, ∀ x ∈ Q, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hcen : ∀ g ∈ Subgroup.zpowers c, ∀ x ∈ Q, g * x = x * g := by
    intro g hg x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (hcQ x hx).symm m)).eq

  let X : Subgroup G :=
    { carrier := {φ | φ ∈ Φ ∧ ∀ x ∈ Q, φ * x * φ⁻¹ * x⁻¹ ∈ Subgroup.zpowers c}
      one_mem' := ⟨Φ.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro φ φ' ⟨hφ, h1⟩ ⟨hφ', h1'⟩
        refine ⟨Φ.mul_mem hφ hφ', fun x hx => ?_⟩
        have e : φ * φ' * x * (φ * φ')⁻¹ * x⁻¹ =
            (φ * (φ' * x * φ'⁻¹ * x⁻¹)) * φ⁻¹ * (φ * x * φ⁻¹ * x⁻¹) := by group
        rw [e, ← hcen _ (h1' x hx) φ (hΦQ hφ), mul_inv_cancel_right]
        exact Subgroup.mul_mem _ (h1' x hx) (h1 x hx)
      inv_mem' := by
        rintro φ ⟨hφ, h1⟩
        refine ⟨Φ.inv_mem hφ, fun x hx => ?_⟩
        have hk := hcen _ (h1 x hx) φ⁻¹ (Q.inv_mem (hΦQ hφ))
        have e : φ⁻¹ * x * φ⁻¹⁻¹ * x⁻¹ =
            φ⁻¹ * (φ * x * φ⁻¹ * x⁻¹)⁻¹ * φ := by group
        rw [e, ← hcen _ (Subgroup.inv_mem _ (h1 x hx)) φ⁻¹ (Q.inv_mem (hΦQ hφ)),
          inv_mul_cancel_right]
        exact Subgroup.inv_mem _ (h1 x hx) }
  have hyX : y ∈ X := ⟨hyΦ, hyc⟩
  have hZX : centerOf Q ≤ X := by
    intro z hz
    refine ⟨hΦ.2.1 hz, fun x hx => ?_⟩
    rw [hZc z hz x hx, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hXΦ : X ≤ Φ := fun _ hφ => hφ.1

  have hconj : ∀ l ∈ L, ∀ φ ∈ X, l * φ * l⁻¹ ∈ X := by
    rintro l hl φ ⟨hφ, h1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hΦ.1 hl) φ).mp hφ, fun x hx => ?_⟩
    have hx' : l⁻¹ * x * l ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQ.1 (L.inv_mem hl)) x).mp hx
      simpa using this
    have hk := h1 _ hx'
    have e : l * φ * l⁻¹ * x * (l * φ * l⁻¹)⁻¹ * x⁻¹ =
        l * (φ * (l⁻¹ * x * l) * φ⁻¹ * (l⁻¹ * x * l)⁻¹) * l⁻¹ := by group
    rw [e]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← hm, ((Commute.zpow_right (hcL l hl) m)).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c m
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := fun l hl =>
    Subgroup.mem_normalizer_iff.mpr fun φ =>
      ⟨hconj l hl φ, fun hφ => by
        have := hconj l⁻¹ (L.inv_mem hl) _ hφ
        simpa [mul_assoc] using this⟩

  by_contra hyZ
  have hXeq : X = Φ := F4P.eq_of_not_le hα.1 hΦ hZX hXΦ hLX fun h => hyZ (h hyX)
  refine F4P.false_of_comm_mem h2 hΦ hQ hΦQ hZc (fun x hx hxφ => ⟨hx, ?_⟩) hcc hcQ
    fun φ hφ x hx => (hXeq ▸ hφ : φ ∈ X).2 x hx
  exact Subgroup.mem_centralizer_iff.mpr fun φ hφ => hxφ φ hφ

end CFSG.Quasithin.H13.A5
