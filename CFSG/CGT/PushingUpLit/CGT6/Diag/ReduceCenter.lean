module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ReduceDiag

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce

open CFSG CFSG.LocalCores
open scoped commutatorElement

variable {M : Type} [Group M]

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S] {a b : S}
    (hab : a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    apply hab
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem ker_diagHom_le_center {K : Subgroup M} {t : M}
    (hc : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a) :
    (diagHom K t hc).ker ≤ Subgroup.center ↥K := by
  intro u hu
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 : (u : M) * (t * (u : M) * t⁻¹) = 1 := hu
  have h2 : (u : M)⁻¹ = t * (u : M) * t⁻¹ := (eq_inv_of_mul_eq_one_right h1).symm
  have hu' : (u : M) ∈ cj t K := by
    have : (u : M)⁻¹ ∈ cj t K := h2 ▸ cj_mul_mem u.2
    simpa using (cj t K).inv_mem this
  exact Subtype.ext (hc (x : M) x.2 (u : M) hu')


theorem mem_center_diag {K Y : Subgroup M} {t : M} (hKq : IsQuasisimple K)
    (hc : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a)
    (hY : ∀ y : M, y ∈ Y ↔ ∃ k ∈ K, y = k * (t * k * t⁻¹)) {w : M}
    (hw : w ∈ (Subgroup.center ↥Y).map Y.subtype) :
    ∃ z ∈ Subgroup.center ↥K, w = (z : M) * (t * (z : M) * t⁻¹) := by
  obtain ⟨y, hyc, rfl⟩ := hw
  obtain ⟨k, hk, hyk⟩ := (hY y).1 y.2
  have hker := ker_diagHom_le_center hc
  have hδY : ∀ x : ↥K, diagHom K t hc x ∈ Y := fun x => (hY _).2 ⟨x, x.2, rfl⟩
  have hδk : diagHom K t hc ⟨k, hk⟩ = (y : M) := hyk.symm
  generalize diagHom K t hc = δ at hker hδY hδk
  have hcomm : ∀ x : ↥K, (⟨k, hk⟩ : ↥K) * x * ⟨k, hk⟩⁻¹ * x⁻¹ ∈ Subgroup.center ↥K := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : (⟨δ x, hδY x⟩ : ↥Y) * y = y * ⟨δ x, hδY x⟩ := Subgroup.mem_center_iff.mp hyc _
    have h2 : δ x * (y : M) = (y : M) * δ x := congrArg Subtype.val h1
    have h2' : δ ⟨k, hk⟩ * δ x = δ x * δ ⟨k, hk⟩ := by
      rw [hδk]
      exact h2.symm
    simp only [map_mul, map_inv]
    rw [h2']
    group
  have hkc : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
    obtain ⟨-, hs, a, b, hab⟩ := hKq
    have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hs
    have hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_eq_bot_of_simple hab
    have hmem : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ Subgroup.center ↥K) ∈
        Subgroup.center (↥K ⧸ Subgroup.center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      have e : (QuotientGroup.mk (⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ * x⁻¹ : ↥K) :
          ↥K ⧸ Subgroup.center ↥K) = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm x)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at e
      have e' : ⁅(QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ Subgroup.center ↥K),
          (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K)⁆ = 1 := by
        rw [commutatorElement_def]
        exact e
      exact (commutatorElement_eq_one_iff_mul_comm.mp e').symm
    rw [hcen, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff _).1 hmem
  exact ⟨⟨k, hk⟩, hkc, hyk⟩

theorem odd_card_center_diag {K Y : Subgroup M} {t : M} (hKq : IsQuasisimple K)
    (hc : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a)
    (hY : ∀ y : M, y ∈ Y ↔ ∃ k ∈ K, y = k * (t * k * t⁻¹))
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥K))) : Odd (Nat.card ↥(Subgroup.center ↥Y)) := by
  have h1 : (Subgroup.center ↥Y).map Y.subtype ≤ (Subgroup.center ↥K).map (diagHom K t hc) := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := mem_center_diag hKq hc hY hw
    exact ⟨z, hz, hzw.symm⟩
  have h2 : Nat.card ↥(Subgroup.center ↥Y) =
      Nat.card ↥((Subgroup.center ↥Y).map Y.subtype) :=
    (Subgroup.card_map_of_injective Y.subtype_injective).symm
  rw [h2]
  exact Odd.of_dvd_nat hodd ((Subgroup.card_dvd_of_le h1).trans (Subgroup.card_map_dvd _ _))

end CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce
