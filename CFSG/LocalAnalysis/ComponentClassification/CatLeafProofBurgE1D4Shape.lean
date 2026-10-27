module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

variable {Y : Type} [Group Y]

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {x : G} (hx : Odd (orderOf x))
    (hx2 : x ^ 2 = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hx
    exact absurd hx (by decide)

theorem sq_eq_one_of_mem_center_of_mulEquiv_SL2 {G : Type*} {F : Type} [Group G] [Field F]
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) {x : G} (hx : x ∈ Subgroup.center G) :
    x ^ 2 = 1 := by
  have hex : e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨y, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y]
  apply e.injective
  rw [map_pow, map_one]
  rcases eq_one_or_neg_one_of_mem_center hex with h | h <;> rw [h] <;> simp [sq]

theorem pPrimeCore_inf_eq_bot_of_mulEquiv_SL2
    [Finite Y] {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {I : Subgroup Y}
    (e : I ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    pPrimeCore 2 Y ⊓ I = ⊥ := by
  set N := pPrimeCore 2 Y with hNdef
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hD : (N.subgroupOf I).Normal := hNn.subgroupOf I
  have hcard : Nat.card (N.subgroupOf I) ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective I.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hodd : Nat.Coprime 2 (Nat.card (N.subgroupOf I)) :=
    Nat.coprime_two_left.mpr (Odd.of_dvd_nat hNodd hcard)
  have hZ := le_center_of_odd_normal_of_mulEquiv_SL2 hF e (N.subgroupOf I) hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hxI⟩ := Subgroup.mem_inf.1 hx
  have hxc : (⟨x, hxI⟩ : I) ∈ Subgroup.center I := hZ hxN
  have h2 : (⟨x, hxI⟩ : I) ^ 2 = 1 := sq_eq_one_of_mem_center_of_mulEquiv_SL2 e hxc
  have h2' : x ^ 2 = 1 := by
    have := congrArg Subtype.val h2
    simpa using this
  have hxodd : Odd (orderOf x) := by
    have h1 : orderOf (⟨x, hxN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hNodd h1
  exact (Subgroup.mem_bot).2 (eq_one_of_sq_eq_one_of_odd hxodd h2')

theorem pPrimeCore_eq_bot_of_shape
    [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (h₁ : ringChar F₁ ≠ 2) (h₂ : ringChar F₂ ≠ 2) (S : Shape Y F₁ F₂) :
    pPrimeCore 2 Y = ⊥ := by
  classical
  set N := pPrimeCore 2 Y with hNdef
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have : S.I₁.Normal := S.normal₁
  have : S.I₂.Normal := S.normal₂
  have hd₁ : Disjoint N S.I₁ := disjoint_iff.2 (pPrimeCore_inf_eq_bot_of_mulEquiv_SL2 h₁ S.e₁)
  have hd₂ : Disjoint N S.I₂ := disjoint_iff.2 (pPrimeCore_inf_eq_bot_of_mulEquiv_SL2 h₂ S.e₂)
  have hc₁ : ∀ n ∈ N, ∀ x ∈ S.I₁, n * x = x * n := fun n hn x hx =>
    (Subgroup.commute_of_normal_of_disjoint _ _ hNn S.normal₁ hd₁ n x hn hx).eq
  have hc₂ : ∀ n ∈ N, ∀ x ∈ S.I₂, n * x = x * n := fun n hn x hx =>
    (Subgroup.commute_of_normal_of_disjoint _ _ hNn S.normal₂ hd₂ n x hn hx).eq
  have hle : N ≤ Subgroup.zpowers S.z := by
    intro n hn
    have htop : (Subgroup.zpowers S.t ⊔ (S.I₁ ⊔ S.I₂) : Subgroup Y) = ⊤ := by
      rw [← S.gen]
      exact sup_comm _ _
    have hy : n ∈ (Subgroup.zpowers S.t ⊔ (S.I₁ ⊔ S.I₂) : Subgroup Y) :=
      htop ▸ Subgroup.mem_top n
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hy
    obtain ⟨k, hk, m, hm, hkm⟩ := hy
    rw [Subgroup.mul_normal] at hm
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
      have haZ : (⟨a, ha⟩ : S.I₁) ∈ Subgroup.center S.I₁ := by
        rw [Subgroup.mem_center_iff]
        intro x
        refine Subtype.ext ?_
        change (x : Y) * a = a * x
        have h1 := hc₁ (a * b) hn x x.2
        have h2 := hab₁ x x.2
        have h3 : a * b * x * (a * b)⁻¹ = x := by
          calc a * b * x * (a * b)⁻¹ = x * (a * b) * (a * b)⁻¹ := by rw [h1]
            _ = x := by group
        rw [h2] at h3
        calc (x : Y) * a = a * x * a⁻¹ * a := by rw [h3]
          _ = a * x := by group
      have hbZ : (⟨b, hb⟩ : S.I₂) ∈ Subgroup.center S.I₂ := by
        rw [Subgroup.mem_center_iff]
        intro x
        refine Subtype.ext ?_
        change (x : Y) * b = b * x
        have h1 := hc₂ (a * b) hn x x.2
        have h2 := S.comm a ha x x.2
        have h3 : a * (b * x) = a * (x * b) := by
          calc a * (b * x) = a * b * x := by group
            _ = x * (a * b) := h1
            _ = (x * a) * b := by group
            _ = (a * x) * b := by rw [h2]
            _ = a * (x * b) := by group
        exact (mul_left_cancel h3).symm
      have hza : ∀ {c : Y} (hc : c ∈ S.I₁), (⟨c, hc⟩ : S.I₁) ∈ Subgroup.center S.I₁ →
          c = 1 ∨ c = S.z := by
        intro c hc hcZ
        have hex : S.e₁ ⟨c, hc⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁) := by
          rw [Subgroup.mem_center_iff]
          intro B
          obtain ⟨y, rfl⟩ := S.e₁.surjective B
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcZ) y]
        rcases eq_one_or_neg_one_of_mem_center hex with h | h
        · left
          have := S.e₁.injective (h.trans (map_one S.e₁).symm)
          exact congrArg Subtype.val this
        · right
          have := S.e₁.injective (h.trans S.e₁_z.symm)
          exact congrArg Subtype.val this
      have hzb : ∀ {c : Y} (hc : c ∈ S.I₂), (⟨c, hc⟩ : S.I₂) ∈ Subgroup.center S.I₂ →
          c = 1 ∨ c = S.z := by
        intro c hc hcZ
        have hex : S.e₂ ⟨c, hc⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₂) := by
          rw [Subgroup.mem_center_iff]
          intro B
          obtain ⟨y, rfl⟩ := S.e₂.surjective B
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcZ) y]
        rcases eq_one_or_neg_one_of_mem_center hex with h | h
        · left
          have := S.e₂.injective (h.trans (map_one S.e₂).symm)
          exact congrArg Subtype.val this
        · right
          have := S.e₂.injective (h.trans S.e₂_z.symm)
          exact congrArg Subtype.val this
      have hz : S.z ∈ Subgroup.zpowers S.z := Subgroup.mem_zpowers _
      rcases hza ha haZ with rfl | rfl <;> rcases hzb hb hbZ with rfl | rfl
      · simp
      · simp
      · simp
      · exact Subgroup.mul_mem _ hz hz
    ·
      exfalso
      subst hkm
      obtain ⟨A, hA⟩ : ∃ A, S.e₁ ⟨a, ha⟩ = A := ⟨_, rfl⟩
      have hact : ∀ X : Matrix.SpecialLinearGroup (Fin 2) F₁,
          conjSLAut S.g₁ X = A⁻¹ * X * A⁻¹⁻¹ := by
        intro X
        set x : S.I₁ := S.e₁.symm (A⁻¹ * X * A) with hx
        have hxX : S.e₁ x = A⁻¹ * X * A := by rw [hx, MulEquiv.apply_symm_apply]
        set y : S.I₁ := ⟨a, ha⟩ * x * (⟨a, ha⟩ : S.I₁)⁻¹ with hy
        have hyX : S.e₁ y = X := by
          rw [hy, map_mul, map_mul, map_inv, hxX, hA]
          group
        obtain ⟨y', hy'Y, hy'M⟩ := S.act₁ y
        have hty : S.t * (y : Y) * S.t⁻¹ = x := by
          have h1 := hc₁ (S.t * (a * b)) hn x x.2
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
        rw [hy'x, hxX, hyX] at hm
        apply Subtype.ext
        rw [conjSLAut_coe]
        have hX : ((A⁻¹ * X * A⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F₁) :
            Matrix (Fin 2) (Fin 2) F₁) = ((A⁻¹ * X * A : Matrix.SpecialLinearGroup (Fin 2) F₁) :
              Matrix (Fin 2) (Fin 2) F₁) := by rw [inv_inv]
        rw [hX, hm]
      exact S.ns₁ (isSquare_det_of_conjSLAut_eq S.g₁ A⁻¹ hact)
  have hdvd : Nat.card N ∣ 2 := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact S.z_sq)
  have h1 : Nat.card N = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hNodd
      exact absurd hNodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ h1

end CFSG.ComponentClassification.CatLeafProof
