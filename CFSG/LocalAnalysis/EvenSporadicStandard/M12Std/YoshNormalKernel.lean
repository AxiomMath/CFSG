module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

section Kernel

theorem mem_of_normal_of_center {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {z : P}
    (hz : ∀ y ∈ Subgroup.center P, y = 1 ∨ y = z) (K : Subgroup P) [K.Normal] (hK : K ≠ ⊥) :
    z ∈ K := by
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hK
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (p := 2) K
  rcases hz _ hxc with h | h
  · exact absurd (Subtype.ext h) hx1
  · rw [← h]
    exact x.2

theorem mem_of_normal_of_selfCentralizing {M : Type*} [Group M] [Finite M] (E : Subgroup M)
    [E.Normal] (hp : IsPGroup 2 E) (hcen : ∀ m : M, (∀ y ∈ E, m * y = y * m) → m ∈ E) {z : M}
    (hzE : z ∈ E) (hz : ∀ y ∈ E, (∀ y' ∈ E, y * y' = y' * y) → y = 1 ∨ y = z)
    (K : Subgroup M) [K.Normal] (hK : K ≠ ⊥) : z ∈ K := by
  by_cases hKE : K ⊓ E = ⊥
  · exfalso
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have hkE : k ∈ E := by
      apply hcen
      intro y hy
      have h1 : k * y * k⁻¹ * y⁻¹ ∈ E := by
        have := E.mul_mem (Normal.conj_mem ‹E.Normal› y hy k) (E.inv_mem hy)
        exact this
      have h2 : k * y * k⁻¹ * y⁻¹ ∈ K := by
        have := K.mul_mem hk (Normal.conj_mem ‹K.Normal› k⁻¹ (K.inv_mem hk) y)
        simpa [mul_assoc] using this
      have h3 : k * y * k⁻¹ * y⁻¹ ∈ K ⊓ E := ⟨h2, h1⟩
      rw [hKE, Subgroup.mem_bot] at h3
      calc k * y = k * y * k⁻¹ * y⁻¹ * (y * k) := by group
        _ = y * k := by rw [h3, one_mul]
    have : k ∈ K ⊓ E := ⟨hk, hkE⟩
    rw [hKE] at this
    exact this
  ·
    let P := E
    let K' : Subgroup E := (K ⊓ E).subgroupOf E
    haveI : K'.Normal := by
      refine ⟨fun k hk g => ?_⟩
      have hk' : (k : M) ∈ K ⊓ E := hk
      have : (g : M) * (k : M) * (g : M)⁻¹ ∈ K ⊓ E :=
        ⟨Normal.conj_mem ‹K.Normal› _ hk'.1 _, E.mul_mem (E.mul_mem g.2 k.2) (E.inv_mem g.2)⟩
      exact this
    have hK' : K' ≠ ⊥ := by
      intro h
      apply hKE
      rw [eq_bot_iff]
      intro x hx
      have hxE : x ∈ E := hx.2
      have : (⟨x, hxE⟩ : E) ∈ K' := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext_iff.1 this
    have hz' : ∀ y ∈ Subgroup.center E, y = 1 ∨ y = (⟨z, hzE⟩ : E) := by
      intro y hy
      have hy' := Subgroup.mem_center_iff.1 hy
      rcases hz (y : M) y.2 (fun y' hy'' => by
        have := congrArg Subtype.val (hy' ⟨y', hy''⟩)
        exact this.symm) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    have := mem_of_normal_of_center hp hz' K' hK'
    exact this.1

end Kernel

end CFSG.EvenSporadicStandard.M12Std.Yosh
