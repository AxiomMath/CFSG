module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix
open CFSG.AGLEmbedding (centerQuotientAction centerQuotientAction_mulVec)

theorem exists_basis_mulVec_zmod_three : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3),
    M * M * M = 1 → M ≠ 1 → ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧
      ∀ u : Fin 2 → ZMod 3, ∃ i j : ZMod 3, u = i • v + j • (M *ᵥ v) := by
  decide

theorem zmod_three_val_nsmul_eq_smul (i : ZMod 3) (v : Fin 2 → ZMod 3) : i.val • v = i • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem commute_conj_of_pow_three {G : Type*} [Group G] {a b : G} (hb : b ^ 3 = 1)
    (hab : (a * b⁻¹) ^ 3 = 1) (hba : (b * a) ^ 3 = 1) : Commute a (b⁻¹ * a * b) := by
  have hb2 : b * b = b⁻¹ := by
    have : b * b * b = 1 := by rw [← pow_three']; exact hb
    exact eq_inv_of_mul_eq_one_left this
  have h1' : a * (b⁻¹ * a * b) * (b * a * b⁻¹) = 1 := by
    calc a * (b⁻¹ * a * b) * (b * a * b⁻¹) = a * b⁻¹ * a * (b * b) * a * b⁻¹ := by group
      _ = a * b⁻¹ * a * b⁻¹ * a * b⁻¹ := by rw [hb2]
      _ = (a * b⁻¹) ^ 3 := by rw [pow_three']; group
      _ = 1 := hab
  have h1 : a * (b⁻¹ * a * b) = b * a⁻¹ * b⁻¹ := by
    rw [mul_eq_one_iff_eq_inv.mp h1']
    group
  have h2' : b * a * (b * a) = a⁻¹ * b⁻¹ := by
    have h3 : b * a * (b * a) * (b * a) = 1 := by rw [← pow_three']; exact hba
    rw [mul_eq_one_iff_eq_inv.mp h3]
    group
  have h2 : b⁻¹ * a * b * a = b * a⁻¹ * b⁻¹ := by
    calc b⁻¹ * a * b * a = b * (b * a * (b * a)) := by rw [← hb2]; group
      _ = b * (a⁻¹ * b⁻¹) := by rw [h2']
      _ = b * a⁻¹ * b⁻¹ := by group
  exact h1.trans h2.symm

theorem false_of_pow_three_transvection {G : Type*} [Group G] {E : Subgroup G}
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod 3)) {k : G}
    (hkN : k ∈ Subgroup.normalizer (E : Set G))
    (hk : centerQuotientAction E e ⟨k, hkN⟩ ≠ 1) (hk3 : k ^ 3 = 1)
    (hbk : ∀ b ∈ E, (b * k) ^ 3 = 1) (hkb : ∀ b ∈ E, (k⁻¹ * b) ^ 3 = 1) : False := by
  set A := centerQuotientAction E e ⟨k, hkN⟩ with hAdef
  have hA3 : A ^ 3 = 1 := by
    rw [hAdef, ← map_pow]
    have : (⟨k, hkN⟩ : Subgroup.normalizer (E : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  have hM3 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A * A = 1 := by
    have := congrArg (fun g : GL (Fin 2) (ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) hA3
    simpa [pow_succ, mul_assoc] using this
  have hM1 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h => hk (Units.ext h)
  obtain ⟨v, hv0, hspan⟩ := exists_basis_mulVec_zmod_three _ hM3 hM1
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : E, Multiplicative.toAdd (e (b₀ : E ⧸ Subgroup.center E)) = v := by
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd v)
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨b₀, by rw [hq]; rfl⟩
  have hc : (k : G) * b₀ * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hkN b₀).mp b₀.2
  set c₀ : E := ⟨k * b₀ * k⁻¹, hc⟩ with hc₀
  have hAc : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v =
      Multiplicative.toAdd (e (c₀ : E ⧸ Subgroup.center E)) := by
    rw [← hb₀]
    exact centerQuotientAction_mulVec E e ⟨k, hkN⟩ rfl
  have hcomm : b₀ * c₀ = c₀ * b₀ := by
    have hk3' : (k⁻¹) ^ 3 = 1 := by rw [inv_pow, hk3, inv_one]
    have := commute_conj_of_pow_three (a := (b₀ : G)) (b := k⁻¹) hk3'
      (by simpa using hbk b₀ b₀.2) (hkb b₀ b₀.2)
    exact Subtype.ext (by simpa using this.eq)
  have hall : ∀ u : E, u * b₀ = b₀ * u := by
    intro u
    obtain ⟨i, j, hij⟩ := hspan (Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E)))
    obtain ⟨x, hx⟩ : ∃ x : E, x = b₀ ^ i.val * c₀ ^ j.val := ⟨_, rfl⟩
    have hbx : Commute b₀ x := by
      rw [hx]
      exact ((Commute.refl b₀).pow_right i.val).mul_right
        ((show Commute b₀ c₀ from hcomm).pow_right j.val)
    have hxu : (x : E ⧸ Subgroup.center E) = u := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hij, hx]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow, toAdd_mul,
        toAdd_pow]
      rw [hb₀, ← hAc, zmod_three_val_nsmul_eq_smul, zmod_three_val_nsmul_eq_smul]
    have hz : x⁻¹ * u ∈ Subgroup.center E := by
      rw [← QuotientGroup.eq]
      exact hxu
    have hu : u = x * (x⁻¹ * u) := by group
    have hzc := Subgroup.mem_center_iff.mp hz b₀
    calc u * b₀ = x * (x⁻¹ * u) * b₀ := by rw [← hu]
      _ = x * (b₀ * (x⁻¹ * u)) := by rw [mul_assoc, hzc]
      _ = (x * b₀) * (x⁻¹ * u) := by rw [mul_assoc]
      _ = (b₀ * x) * (x⁻¹ * u) := by rw [hbx.eq.symm]
      _ = b₀ * u := by rw [mul_assoc, ← hu]
  have hb₀Z : b₀ ∈ Subgroup.center E := Subgroup.mem_center_iff.mpr fun g => hall g
  have h1 : (b₀ : E ⧸ Subgroup.center E) = 1 := (QuotientGroup.eq_one_iff _).mpr hb₀Z
  rw [h1, map_one, toAdd_one] at hb₀
  exact hv0 hb₀.symm

end CFSG.LocalAnalysis.RankThreeTheoremC
