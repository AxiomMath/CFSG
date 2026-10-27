module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QZ
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem mem_zpowers_of_commute_shape {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape Y F₁ F₂) {n : Y} (hc₁ : ∀ x ∈ S.I₁, n * x = x * n)
    (hc₂ : ∀ x ∈ S.I₂, n * x = x * n) : n ∈ zpowers S.z := by
  have : S.I₁.Normal := S.normal₁
  have : S.I₂.Normal := S.normal₂
  have htop : (zpowers S.t ⊔ (S.I₁ ⊔ S.I₂) : Subgroup Y) = ⊤ := by
    rw [← S.gen]
    exact sup_comm _ _
  have hy : n ∈ (zpowers S.t ⊔ (S.I₁ ⊔ S.I₂) : Subgroup Y) := htop ▸ mem_top n
  rw [← SetLike.mem_coe, mul_normal] at hy
  obtain ⟨k, hk, m, hm, hkm⟩ := hy
  rw [mul_normal] at hm
  obtain ⟨a, ha, b, hb, rfl⟩ := hm
  dsimp only at hkm
  have hab₁ : ∀ x ∈ S.I₁, a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := fun x hx => by
    have := S.comm x hx b hb
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [this]
      _ = a * x * a⁻¹ := by group
  rcases mem_zpowers_of_sq S.t_sq hk with rfl | rfl
  ·
    rw [one_mul] at hkm
    subst hkm
    have haZ : (⟨a, ha⟩ : S.I₁) ∈ center S.I₁ := by
      rw [mem_center_iff]
      intro x
      refine Subtype.ext ?_
      change (x : Y) * a = a * x
      have h1 := hc₁ x x.2
      have h2 := hab₁ x x.2
      have h3 : a * b * x * (a * b)⁻¹ = x := by
        calc a * b * x * (a * b)⁻¹ = x * (a * b) * (a * b)⁻¹ := by rw [h1]
          _ = x := by group
      rw [h2] at h3
      calc (x : Y) * a = a * x * a⁻¹ * a := by rw [h3]
        _ = a * x := by group
    have hbZ : (⟨b, hb⟩ : S.I₂) ∈ center S.I₂ := by
      rw [mem_center_iff]
      intro x
      refine Subtype.ext ?_
      change (x : Y) * b = b * x
      have h1 := hc₂ x x.2
      have h2 := S.comm a ha x x.2
      have h3 : a * (b * x) = a * (x * b) := by
        calc a * (b * x) = a * b * x := by group
          _ = x * (a * b) := h1
          _ = (x * a) * b := by group
          _ = (a * x) * b := by rw [h2]
          _ = a * (x * b) := by group
      exact (mul_left_cancel h3).symm
    have hza : ∀ {c : Y} (hc : c ∈ S.I₁), (⟨c, hc⟩ : S.I₁) ∈ center S.I₁ →
        c = 1 ∨ c = S.z := by
      intro c hc hcZ
      have hex : S.e₁ ⟨c, hc⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2) F₁) := by
        rw [mem_center_iff]
        intro B
        obtain ⟨y, rfl⟩ := S.e₁.surjective B
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hcZ) y]
      rcases eq_one_or_neg_one_of_mem_center hex with h | h
      · exact Or.inl (congrArg Subtype.val (S.e₁.injective (h.trans (map_one S.e₁).symm)))
      · exact Or.inr (congrArg Subtype.val (S.e₁.injective (h.trans S.e₁_z.symm)))
    have hzb : ∀ {c : Y} (hc : c ∈ S.I₂), (⟨c, hc⟩ : S.I₂) ∈ center S.I₂ →
        c = 1 ∨ c = S.z := by
      intro c hc hcZ
      have hex : S.e₂ ⟨c, hc⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2) F₂) := by
        rw [mem_center_iff]
        intro B
        obtain ⟨y, rfl⟩ := S.e₂.surjective B
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hcZ) y]
      rcases eq_one_or_neg_one_of_mem_center hex with h | h
      · exact Or.inl (congrArg Subtype.val (S.e₂.injective (h.trans (map_one S.e₂).symm)))
      · exact Or.inr (congrArg Subtype.val (S.e₂.injective (h.trans S.e₂_z.symm)))
    have hz : S.z ∈ zpowers S.z := mem_zpowers _
    rcases hza ha haZ with rfl | rfl <;> rcases hzb hb hbZ with rfl | rfl
    · simp
    · simp
    · simp
    · exact mul_mem hz hz
  ·
    exfalso
    subst hkm
    obtain ⟨A, hA⟩ : ∃ A, S.e₁ ⟨a, ha⟩ = A := ⟨_, rfl⟩
    have hact : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F₁,
        conjSLAut S.g₁ M = A⁻¹ * M * A⁻¹⁻¹ := by
      intro M
      set x : S.I₁ := S.e₁.symm (A⁻¹ * M * A) with hx
      have hxM : S.e₁ x = A⁻¹ * M * A := by rw [hx, MulEquiv.apply_symm_apply]
      set y : S.I₁ := ⟨a, ha⟩ * x * (⟨a, ha⟩ : S.I₁)⁻¹ with hy
      have hyM : S.e₁ y = M := by
        rw [hy, map_mul, map_mul, map_inv, hxM, hA]
        group
      obtain ⟨y', hy'Y, hy'M⟩ := S.act₁ y
      have hty : S.t * (y : Y) * S.t⁻¹ = x := by
        have h1 := hc₁ x x.2
        have h2 := hab₁ x x.2
        have h3 : S.t * (a * b) * x * (S.t * (a * b))⁻¹ = x := by
          calc S.t * (a * b) * x * (S.t * (a * b))⁻¹ =
              x * (S.t * (a * b)) * (S.t * (a * b))⁻¹ := by rw [h1]
            _ = x := by group
        have h4 : S.t * (a * b) * x * (S.t * (a * b))⁻¹ =
            S.t * (a * b * x * (a * b)⁻¹) * S.t⁻¹ := by group
        rw [h4, h2] at h3
        simpa [hy] using h3
      have hy'x : y' = x := Subtype.ext (hy'Y.trans hty)
      have hm := hy'M
      rw [hy'x, hxM, hyM] at hm
      apply Subtype.ext
      rw [conjSLAut_coe]
      have hM : ((A⁻¹ * M * A⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F₁) :
          Matrix (Fin 2) (Fin 2) F₁) = ((A⁻¹ * M * A : Matrix.SpecialLinearGroup (Fin 2) F₁) :
            Matrix (Fin 2) (Fin 2) F₁) := by rw [inv_inv]
      rw [hM, hm]
    exact S.ns₁ (isSquare_det_of_conjSLAut_eq S.g₁ A⁻¹ hact)

theorem even_card_of_involution_mem {G : Type*} [Group G] {I : Subgroup G} {z : G}
    (hzI : z ∈ I) (hz1 : z ≠ 1) (hz2 : z * z = 1) : Even (Nat.card I) := by
  have h : orderOf (⟨z, hzI⟩ : I) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have h2 := orderOf_dvd_natCard (⟨z, hzI⟩ : I)
  rw [h] at h2
  exact even_iff_two_dvd.2 h2

theorem fAt_of_shape {X : Type} [Group X] {z : X} (hz : orderOf z = 2) {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape (centralizer ({z} : Set X)) F₁ F₂) (hSz : (S.z : X) = z)
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂) : FAt X z := by
  have hc₁ : IsComponent S.I₁ :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h₁),
      S.normal₁.isSubnormal⟩
  have hc₂ : IsComponent S.I₂ :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm (GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h₂),
      S.normal₂.isSubnormal⟩
  have he₁ : Even (Nat.card S.I₁) := even_card_of_involution_mem S.z_mem₁ S.z_ne S.z_sq
  have he₂ : Even (Nat.card S.I₂) := even_card_of_involution_mem S.z_mem₂ S.z_ne S.z_sq
  refine fAt_of_commute_mem_zpowers hz fun g hg hcomm => ?_
  have hn : (⟨g, hg⟩ : centralizer ({z} : Set X)) ∈ zpowers S.z :=
    mem_zpowers_of_commute_shape S (fun x hx => Subtype.ext (hcomm S.I₁ hc₁ he₁ x hx).symm)
      fun x hx => Subtype.ext (hcomm S.I₂ hc₂ he₂ x hx).symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← hSz]
  exact congrArg Subtype.val hk

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
