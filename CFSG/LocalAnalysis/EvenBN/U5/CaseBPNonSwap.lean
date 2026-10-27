module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEnd

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEnd.Endgame
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem nonSwap_comm_of_sq_eq_one {E : Subgroup G} (hsq : ∀ y ∈ E, y * y = 1) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have h1 := hsq (x * y) (E.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hx', hy'] at hxy
  exact hxy.symm

theorem nonSwap_quotient_conj {M : Type} [Group M] {X : Subgroup G} (φ : G ≃* G)
    (e : X ⧸ center X ≃* M) :
    Nonempty ((X.map φ.toMonoidHom) ⧸ center (X.map φ.toMonoidHom) ≃* M) := by
  set e1 : X ≃* X.map φ.toMonoidHom := X.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc : (center X).map (e1 : X →* X.map φ.toMonoidHom) =
      center (X.map φ.toMonoidHom) := Subgroup.map_center_eq e1
  exact ⟨(QuotientGroup.congr _ _ e1 hc).symm.trans e⟩

theorem nonSwap_odd_center_conj {X : Subgroup G} (φ : G ≃* G)
    (hZ : Odd (Nat.card (center X))) :
    Odd (Nat.card (center (X.map φ.toMonoidHom))) := by
  set e1 : X ≃* X.map φ.toMonoidHom := X.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc : (center X).map (e1 : X →* X.map φ.toMonoidHom) =
      center (X.map φ.toMonoidHom) := Subgroup.map_center_eq e1
  rw [← hc, Subgroup.card_map_of_injective e1.injective]
  exact hZ

theorem nonSwap_eq_one_of_odd_center {A : Subgroup G} (hZ : Odd (Nat.card (center A)))
    {z : G} (hzA : z ∈ A) (hcomm : ∀ a ∈ A, a * z = z * a) (hz2 : z * z = 1) : z = 1 := by
  have hzc : (⟨z, hzA⟩ : A) ∈ center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2)
  have hu2 : (⟨⟨z, hzA⟩, hzc⟩ : center A) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp [sq, hz2]
  have hdvd1 := orderOf_dvd_natCard (⟨⟨z, hzA⟩, hzc⟩ : center A)
  have hdvd2 : orderOf (⟨⟨z, hzA⟩, hzc⟩ : center A) ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
  · have hu1 : (⟨⟨z, hzA⟩, hzc⟩ : center A) = 1 := orderOf_eq_one_iff.1 h1
    exact congrArg (fun u : center A => (u : A).1) hu1
  · exfalso
    have h2d : 2 ∣ Nat.card (center A) := by
      rw [← h2]
      exact hdvd1
    obtain ⟨k, hk⟩ := hZ
    omega

theorem nonSwap_mul_comm_of {a₁ a₂ b₁ b₂ : G} (ha : a₁ * a₂ = a₂ * a₁) (hb : b₁ * b₂ = b₂ * b₁)
    (h21 : b₁ * a₂ = a₂ * b₁) (h12 : a₁ * b₂ = b₂ * a₁) :
    a₁ * b₁ * (a₂ * b₂) = a₂ * b₂ * (a₁ * b₁) := by
  calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
    _ = a₁ * (a₂ * b₁) * b₂ := by rw [h21]
    _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
    _ = a₂ * a₁ * (b₁ * b₂) := by rw [ha]
    _ = a₂ * a₁ * (b₂ * b₁) := by rw [hb]
    _ = a₂ * (a₁ * b₂) * b₁ := by simp only [mul_assoc]
    _ = a₂ * (b₂ * a₁) * b₁ := by rw [h12]
    _ = a₂ * b₂ * (a₁ * b₁) := by simp only [mul_assoc]

theorem nonSwap_exists_elemAb_cent_of_cover (hN3 : CaseBParts.InvolutoryFixedElemAbStatement)
    (hf : 2 ≤ f) {X : Subgroup G} (hZ : Odd (Nat.card (center X)))
    (e : X ⧸ center X ≃* hypPSU h 2 1) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    ∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ (∀ y ∈ E, y * y = 1) ∧
      (2 ^ f) ^ 3 ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) with hα
  have hα2 : α * α = 1 := quotientCenterConj_mul_self hxX hx2
  set θ : MulAut (hypPSU h 2 1) := (MulAut.congr e) α with hθ
  have hθ2 : θ * θ = 1 := by
    rw [hθ, ← map_mul, hα2, map_one]
  obtain ⟨E, hEel, hEfix, hE8⟩ := hN3 f K h hf θ hθ2
  haveI : CFSG.IsElementaryAbelian 2 ↥E := hEel
  have hEsq : ∀ y ∈ E, y * y = 1 := by
    intro y hy
    have hy2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) y hy
    rwa [sq] at hy2
  haveI : Finite (hypPSU h 2 1) := Finite.of_equiv (X ⧸ center X) e.toEquiv
  have hEp : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hEp
  set E₀ : Subgroup (X ⧸ center X) := E.map e.symm.toMonoidHom with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ m := by
    rw [← hm]
    exact Subgroup.card_map_of_injective e.symm.injective
  have hfix : ∀ b ∈ E₀, α b = b := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : e (α (e.symm y)) = y := hEfix y hy
    simp only [MulEquiv.coe_toMonoidHom]
    have h2 : e (α (e.symm y)) = e (e.symm y) := by rw [h1, e.apply_symm_apply]
    exact e.injective h2
  have hsq : ∀ b ∈ E₀, b * b = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hEsq y hy, map_one]
  obtain ⟨E', hE'X, hE'c, hE'sq, hE'card⟩ :=
    exists_exp_two_le_centralizer_of_fixed hZ hxX hx2 E₀ hfix hsq hE₀card
  refine ⟨E', hE'X, hE'c, hE'sq, ?_⟩
  rw [hE'card, ← hm]
  exact hE8

theorem not_swap (hN3 : CaseBParts.InvolutoryFixedElemAbStatement) (hB : d.CaseBHyp)
    (c : d.CaseBData) (h52 : CaseBData.Sec52 c) (g : G)
    (h1 : d.t ∈ normalizer ((c.Nc.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (h2 : d.t ∈ normalizer (((c.Nt).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    False := by
  have hf : 2 ≤ f := hB.hyp.two_le
  have hq4 : 4 ≤ 2 ^ f := hB.hyp.four_le
  have ht2 : d.t * d.t = 1 := hB.hyp.t_mul_t
  obtain ⟨e0⟩ := h52.iso
  have hZA : Odd (Nat.card (center (c.Nc.map (MulAut.conj g).toMonoidHom))) :=
    nonSwap_odd_center_conj (MulAut.conj g) h52.odd_center
  obtain ⟨eA⟩ := nonSwap_quotient_conj (MulAut.conj g) e0
  have hZt : Odd (Nat.card (center c.Nt)) :=
    nonSwap_odd_center_conj (MulAut.conj d.t) h52.odd_center
  obtain ⟨et⟩ := nonSwap_quotient_conj (MulAut.conj d.t) e0
  have hZA' : Odd (Nat.card (center (c.Nt.map (MulAut.conj g).toMonoidHom))) :=
    nonSwap_odd_center_conj (MulAut.conj g) hZt
  obtain ⟨eA'⟩ := nonSwap_quotient_conj (MulAut.conj g) et
  have hcomm : ∀ a ∈ c.Nc.map (MulAut.conj g).toMonoidHom,
      ∀ b ∈ c.Nt.map (MulAut.conj g).toMonoidHom, a * b = b * a := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    have key : n * n' = n' * n := Subgroup.mem_centralizer_iff.1 (h52.commute hn') n hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * n * g⁻¹ * (g * n' * g⁻¹) = g * (n * n') * g⁻¹ := by group
      _ = g * (n' * n) * g⁻¹ := by rw [key]
      _ = g * n' * g⁻¹ * (g * n * g⁻¹) := by group
  obtain ⟨E₁, hE₁A, hE₁c, hE₁sq, hE₁card⟩ :=
    nonSwap_exists_elemAb_cent_of_cover hN3 hf hZA eA h1 ht2
  obtain ⟨E₂, hE₂A, hE₂c, hE₂sq, hE₂card⟩ :=
    nonSwap_exists_elemAb_cent_of_cover hN3 hf hZA' eA' h2 ht2
  have hab : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a :=
    fun a ha b hb => hcomm a (hE₁A ha) b (hE₂A hb)
  let ψ : (↥E₁ × ↥E₂) →* G :=
    MonoidHom.noncommCoprod E₁.subtype E₂.subtype (fun x y => hab x.1 x.2 y.1 y.2)
  have hψapp : ∀ p, ψ p = p.1.1 * p.2.1 := fun p => rfl
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 ?_
    rintro ⟨x, y⟩ hxy
    rw [hψapp] at hxy
    have hxy' : x.1 = y.1⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxE2 : x.1 ∈ E₂ := by
      rw [hxy']
      exact E₂.inv_mem y.2
    have hx1 : x.1 = 1 :=
      nonSwap_eq_one_of_odd_center hZA (hE₁A x.2)
        (fun a ha => hcomm a ha x.1 (hE₂A hxE2)) (hE₁sq x.1 x.2)
    have hy1 : y.1 = 1 := by
      rw [hx1] at hxy'
      exact inv_eq_one.1 hxy'.symm
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  have hcardF : Nat.card ↥ψ.range = Nat.card E₁ * Nat.card E₂ := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hFc : ψ.range ≤ centralizer ({d.t} : Set G) := by
    intro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [hψapp]
    exact Subgroup.mul_mem _ (hE₁c p.1.2) (hE₂c p.2.2)
  have hFcomm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [hψapp, hψapp]
    exact nonSwap_mul_comm_of (nonSwap_comm_of_sq_eq_one hE₁sq p.1.2 q.1.2)
      (nonSwap_comm_of_sq_eq_one hE₂sq p.2.2 q.2.2)
      (hab q.1.1 q.1.2 p.2.1 p.2.2).symm (hab p.1.1 p.1.2 q.2.1 q.2.2)
  have hsqF : ∀ x ∈ ψ.range, x * x = 1 := by
    intro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [hψapp]
    have hab' := hab p.1.1 p.1.2 p.2.1 p.2.2
    have ha := hE₁sq p.1.1 p.1.2
    have hb := hE₂sq p.2.1 p.2.2
    calc p.1.1 * p.2.1 * (p.1.1 * p.2.1) = p.1.1 * (p.2.1 * p.1.1) * p.2.1 := by
          simp only [mul_assoc]
      _ = p.1.1 * (p.1.1 * p.2.1) * p.2.1 := by rw [← hab']
      _ = p.1.1 * p.1.1 * (p.2.1 * p.2.1) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have hFel : CFSG.IsElementaryAbelian 2 ψ.range := isElementaryAbelian_of_forall hFcomm hsqF
  have hbound : Nat.card ↥ψ.range ≤ 2 * (2 ^ f) ^ 4 :=
    hB.hyp.card_le_of_le_centralizer hFc hFel
  have hprod : (2 ^ f) ^ 3 * (2 ^ f) ^ 3 ≤ Nat.card E₁ * Nat.card E₂ :=
    Nat.mul_le_mul hE₁card hE₂card
  rw [← hcardF] at hprod
  have hfin : (2 ^ f) ^ 3 * (2 ^ f) ^ 3 ≤ 2 * (2 ^ f) ^ 4 := le_trans hprod hbound
  generalize 2 ^ f = q at hfin hq4
  have h16 : 16 ≤ q ^ 2 := by nlinarith
  have hq4pos : 0 < q ^ 4 := pow_pos (by omega) 4
  have h6 : q ^ 4 * 16 ≤ q ^ 4 * q ^ 2 := Nat.mul_le_mul (le_refl _) h16
  have h6' : q ^ 3 * q ^ 3 = q ^ 4 * q ^ 2 := by ring
  nlinarith

end CaseBData

end Data

namespace CaseBParts

theorem nonSwap : NonSwapStatement :=
  fun hN3 _ _ _ _ _ _ _ _ hB c h52 g h1 h2 => Data.CaseBData.not_swap hN3 hB c h52 g h1 h2

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
