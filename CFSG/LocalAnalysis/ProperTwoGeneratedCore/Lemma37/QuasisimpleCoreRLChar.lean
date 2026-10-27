module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRLCyclic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u : G}

theorem mem_right_of_commute (hc : PartC T Q P₁ e u) {x : G} (hxT : x ∈ T)
    (hx : ∀ q ∈ Q, x * q = q * x) : x ∈ P₁ := by
  by_cases hxs : x ∈ Q ⊔ P₁
  · obtain ⟨q₀, hq₀, p₀, hp₀, rfl⟩ := hc.mem_sup_iff.mp hxs
    have hq₀c : ∀ q ∈ Q, q₀ * q = q * q₀ := by
      intro q hq
      have h2 := hc.commute q hq p₀ hp₀
      calc q₀ * q = q₀ * (p₀ * q) * p₀⁻¹ := by rw [← h2]; group
        _ = q * (q₀ * p₀) * p₀⁻¹ := by rw [← mul_assoc, hx q hq]
        _ = q * q₀ := by group
    by_cases hq₀Z : q₀ = 1 ∨ q₀ = e
    · rcases hq₀Z with rfl | rfl
      · rw [one_mul]
        exact hp₀
      · exact P₁.mul_mem hc.mem_right hp₀
    exfalso
    push Not at hq₀Z
    have hq₀q₀ := hc.mul_self_of_ne hq₀ hq₀Z.1 hq₀Z.2
    obtain ⟨q₁, hq₁, q₂, hq₂, h11, h22, h21, h21e⟩ :=
      quaternion_exists_pair hc.quaternion.some hc.mem_left hc.order
    have key : ∀ m ∈ Q, m * m = e → m ≠ q₀ → m ≠ q₀ * e → False := by
      intro m hm hmm h1 h2
      have h := hc.anticomm hq₀ hm hq₀q₀ hmm h1 h2
      rw [hq₀c m hm] at h
      exact hc.centralElt_ne_one (mul_eq_left.mp h.symm)
    by_cases h1 : q₁ = q₀ ∨ q₁ = q₀ * e
    · refine key q₂ hq₂ h22 (fun h => ?_) (fun h => ?_)
      · rcases h1 with h1 | h1
        · exact h21 (h.trans h1.symm)
        · exact h21e (by rw [h, h1, hc.mul_centralElt_mul_centralElt])
      · rcases h1 with h1 | h1
        · exact h21e (by rw [h, h1])
        · exact h21 (h.trans h1.symm)
    · push Not at h1
      exact key q₁ hq₁ h11 h1.1 h1.2
  · obtain ⟨m, hm, hm1, -⟩ := hc.outer x hxT hxs
    exact (hm1 (by rw [hx m hm, mul_inv_cancel_right])).elim

theorem commute_left_of_commute_involutions (hc : PartC T Q P₁ e u) {x : G}
    (hx : ∀ t ∈ T, orderOf t = 2 → x * t = t * x) : ∀ q ∈ Q, x * q = q * x := by
  obtain ⟨q₁, hq₁, q₂, hq₂, h11, h22, h21, h21e⟩ :=
    quaternion_exists_pair hc.quaternion.some hc.mem_left hc.order
  have hxq : ∀ q ∈ Q, q * q = e → Commute x (q * u) := fun q hq hqq =>
    hx _ (hc.sup_le (mul_mem_sup hq hc.self_mem)) (hc.orderOf_mul_eq_two hq hc.self_mem hqq hc.sq)
  have h33 : q₁ * q₂ * (q₁ * q₂) = e := by
    refine hc.mul_self_of_ne (Q.mul_mem hq₁ hq₂) (fun h => h21e ?_) (fun h => h21 ?_)
    · rw [eq_inv_of_mul_eq_one_right h, hc.inv_eq_mul_centralElt h11]
    · calc q₂ = q₁⁻¹ * (q₁ * q₂) := by group
        _ = q₁ := by rw [h, hc.inv_eq_mul_centralElt h11, hc.mul_centralElt_mul_centralElt]
  have hu : Commute x u := by
    have h := ((hxq q₁ hq₁ h11).mul_right (hxq q₂ hq₂ h22)).mul_right
      (hxq _ (Q.mul_mem hq₁ hq₂) h33).inv_right
    rwa [show q₁ * u * (q₂ * u) * (q₁ * q₂ * u)⁻¹ = q₁ * u * q₁⁻¹ by group,
      hc.commute q₁ hq₁ u hc.self_mem, mul_inv_cancel_right] at h
  have h1 : Commute x q₁ := by
    have h := (hxq q₁ hq₁ h11).mul_right hu.inv_right
    rwa [mul_inv_cancel_right] at h
  have h2 : Commute x q₂ := by
    have h := (hxq q₂ hq₂ h22).mul_right hu.inv_right
    rwa [mul_inv_cancel_right] at h
  have he : Commute x e := hc.commute_centralElt x
  intro w hw
  rcases hc.enum hq₁ hq₂ hw h11 h22 h21 h21e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Commute.one_right x).eq
  · exact he.eq
  · exact h1.eq
  · exact (h1.mul_right he).eq
  · exact h2.eq
  · exact (h2.mul_right he).eq
  · exact (h1.mul_right h2).eq
  · exact ((h1.mul_right h2).mul_right he).eq

theorem commute_self_of_isCyclic (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁) {t : G}
    (ht : t ∈ T) (ht2 : orderOf t = 2) : u * t = t * u := by
  have hPc : ∀ p ∈ P₁, ∀ p' ∈ P₁, p * p' = p' * p := fun p hp p' hp' => by
    let : CommGroup P₁ := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨p, hp⟩ : P₁) ⟨p', hp'⟩)
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hc.involution_mem t ht ht2)
  calc u * (q * p) = u * q * p := by group
    _ = q * u * p := by rw [hc.commute q hq u hc.self_mem]
    _ = q * (u * p) := by group
    _ = q * (p * u) := by rw [hPc u hc.self_mem p hp]
    _ = q * p * u := by group

theorem normalizer_le_normalizer_zpowers_of_isCyclic [Finite G] (hc : PartC T Q P₁ e u)
    (hcyc : IsCyclic P₁) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  intro g hg
  have hconj : ∀ {g' : G}, g' ∈ Subgroup.normalizer (T : Set G) → ∀ t ∈ T, g' * t * g'⁻¹ ∈ T :=
    fun hg' t ht => (Subgroup.mem_normalizer_iff.mp hg' t).mp ht
  have hginv := (Subgroup.normalizer (T : Set G)).inv_mem hg
  set x := g * u * g⁻¹ with hxdef
  have hxT : x ∈ T := hconj hg u (hc.right_le hc.self_mem)
  have hxinv : ∀ t ∈ T, orderOf t = 2 → x * t = t * x := by
    intro t ht ht2
    have ht' : g⁻¹ * t * g ∈ T := by simpa using hconj hginv t ht
    have ht2' : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, ht2]
    have h := hc.commute_self_of_isCyclic hcyc ht' ht2'
    calc x * t = g * (u * (g⁻¹ * t * g)) * g⁻¹ := by rw [hxdef]; group
      _ = g * ((g⁻¹ * t * g) * u) * g⁻¹ := by rw [h]
      _ = t * x := by rw [hxdef]; group
  have hxP : x ∈ P₁ := hc.mem_right_of_commute hxT (hc.commute_left_of_commute_involutions hxinv)
  have hord : orderOf x = orderOf u := by
    rw [hxdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have heq : Subgroup.zpowers (⟨u, hc.self_mem⟩ : P₁) = Subgroup.zpowers ⟨x, hxP⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
  have hmem : (⟨x, hxP⟩ : P₁) ∈ Subgroup.zpowers (⟨u, hc.self_mem⟩ : P₁) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxu : x ∈ Subgroup.zpowers u := ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine mem_normalizer_of_conj_mem fun w hw => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hxu j

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
