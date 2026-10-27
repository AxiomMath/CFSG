module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61L34M
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Mod

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.GH74.Uniqueness.SU.K.R4.L34M

theorem l34_fixed_cases
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) (α : MulAut K)
    (hα : α ^ 2 = 1) :
    (∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4) ∨
      9 ∣ Nat.card ↥(fixedSub K α) := by
  classical
  have : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv
  obtain ⟨M, hMP, hMA⟩ := autModel e
  have hMP' : ∀ g : Equiv.Perm (Fin 42), g ∈ M.P → g ∈ QP.originalSubgroup := fun g hg => by
    rw [← hMP]
    exact hg
  have hMP'' : ∀ g : Equiv.Perm (Fin 42), g ∈ QP.originalSubgroup → g ∈ M.P := fun g hg => by
    rw [hMP]
    exact hg
  have hMA' : ∀ g : Equiv.Perm (Fin 42), g ∈ M.A → g ∈ QA.originalSubgroup := fun g hg => by
    rw [← hMA]
    exact hg
  obtain ⟨g, hgdef⟩ : ∃ g : Equiv.Perm (Fin 42), g = (M.Φ α : Equiv.Perm (Fin 42)) := ⟨_, rfl⟩
  have hgA : g ∈ QA.originalSubgroup := hMA' _ (hgdef ▸ (M.Φ α).2)
  have hg2 : g ^ 2 = 1 := by rw [hgdef, ← M.Φ_pow, hα, M.Φ_one]
  have hspec : ∀ x : K, ((M.e (α x) : M.P) : Equiv.Perm (Fin 42)) =
      g * (M.e x : Equiv.Perm (Fin 42)) * g⁻¹ := fun x => by
    rw [hgdef]
    exact M.spec α x
  have hfix : ∀ x : K, α x = x ↔
      g * (M.e x : Equiv.Perm (Fin 42)) = (M.e x : Equiv.Perm (Fin 42)) * g := by
    intro x
    constructor
    · intro h
      have h1 := hspec x
      rw [h] at h1
      calc g * (M.e x : Equiv.Perm (Fin 42)) =
            (g * (M.e x : Equiv.Perm (Fin 42)) * g⁻¹) * g := by group
        _ = (M.e x : Equiv.Perm (Fin 42)) * g := by rw [← h1]
    · intro h
      apply M.e.injective
      apply Subtype.ext
      rw [hspec x]
      calc g * (M.e x : Equiv.Perm (Fin 42)) * g⁻¹ =
            (M.e x : Equiv.Perm (Fin 42)) * g * g⁻¹ := by rw [h]
        _ = (M.e x : Equiv.Perm (Fin 42)) := by group
  rcases l34_involution_cases g hgA hg2 with ⟨u, v, hE⟩ | h9
  · left
    obtain ⟨hu, hv, hu1, hv1, huv, hu2, hv2, huv', hgu, hgv⟩ := hE
    obtain ⟨x, hx⟩ := M.e.surjective ⟨u, hMP'' u hu⟩
    obtain ⟨y, hy⟩ := M.e.surjective ⟨v, hMP'' v hv⟩
    have hxu : (M.e x : Equiv.Perm (Fin 42)) = u := congrArg Subtype.val hx
    have hyv : (M.e y : Equiv.Perm (Fin 42)) = v := congrArg Subtype.val hy
    have hxsq : x ^ 2 = 1 := by
      apply M.e.injective
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow, hxu, hu2, map_one, Subgroup.coe_one]
    have hysq : y ^ 2 = 1 := by
      apply M.e.injective
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow, hyv, hv2, map_one, Subgroup.coe_one]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hu1
      rw [← hxu, map_one, Subgroup.coe_one]
    have hxy : x ≠ y := by
      rintro rfl
      exact huv (by rw [← hxu, ← hyv])
    have hcomm : x * y = y * x := by
      apply M.e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hxu, hyv]
      exact huv'
    have hya : y ∉ zpowers x := by
      intro hmem
      rcases eq_one_or_eq_of_mem_zpowers_sq hxsq hmem with h | h
      · apply hv1
        rw [← hyv, h, map_one, Subgroup.coe_one]
      · exact hxy h.symm
    have hxf : α x = x := (hfix x).2 (by rw [hxu]; exact hgu)
    have hyf : α y = y := (hfix y).2 (by rw [hyv]; exact hgv)
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := x) (y := y)
      hxsq hysq hx1 hya hcomm
    have hle : zpowers x ⊔ zpowers y ≤ fixedSub K α :=
      sup_le (Subgroup.zpowers_le.2 hxf) (Subgroup.zpowers_le.2 hyf)
    exact ⟨zpowers x ⊔ zpowers y, fun v hv => hle hv, hel, by rw [hcard]; norm_num⟩
  · right
    have hcard : Nat.card ↥(fixedSub K α) =
        Nat.card ↥(QP.originalSubgroup ⊓
          Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 42)))) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun k : ↥(fixedSub K α) => (⟨(M.e k.1 : Equiv.Perm (Fin 42)),
          Subgroup.mem_inf.2 ⟨hMP' _ (M.e k.1).2, by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact ((hfix k.1).1 k.2).symm⟩⟩ :
          ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 42))))))
        ⟨?_, ?_⟩)
      · intro a b hab
        have h0 := congrArg Subtype.val hab
        have h1 : (M.e a.1 : Equiv.Perm (Fin 42)) = (M.e b.1 : Equiv.Perm (Fin 42)) := h0
        exact Subtype.ext (M.e.injective (Subtype.ext h1))
      · intro z
        obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 z.2
        obtain ⟨k, hk⟩ := M.e.surjective ⟨z.1, hMP'' z.1 hz1⟩
        have hkz : (M.e k : Equiv.Perm (Fin 42)) = z.1 := congrArg Subtype.val hk
        have hkfix : α k = k := (hfix k).2 (by
          rw [hkz]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hz2).symm)
        exact ⟨⟨k, hkfix⟩, Subtype.ext hkz⟩
    rw [hcard]
    exact h9

end CFSG.GH74.Uniqueness.SU.K.R4
