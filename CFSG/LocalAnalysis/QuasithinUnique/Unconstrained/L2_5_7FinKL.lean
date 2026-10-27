module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.QuasithinUnique.Fin257

open scoped commutatorElement
open CFSG.Open

theorem inner_of_cocycle {M : Type} [Group M] [Finite M] (α : MulAut M) {U N R : Subgroup M}
    (hodd : ¬ 2 ∣ U.relIndex N) (hR : IsElemAbelian 2 R)
    (hRN : ∀ x ∈ N, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hαU : ∀ u ∈ U, α u = u)
    (hκ : ∀ x ∈ N, α x * x⁻¹ ∈ R) :
    ∃ r ∈ R, ∀ x ∈ N, α x = r * x * r⁻¹ := by
  classical
  let _ : CommGroup ↥R := { (inferInstance : Group ↥R) with
    mul_comm := fun a b => hR.1.is_comm.comm a b }
  set U' : Subgroup ↥N := U.subgroupOf N with hU'
  have : Fintype (↥N ⧸ U') := Fintype.ofFinite _
  let κ : M → M := fun x => α x * x⁻¹
  have hκmul : ∀ x y : M, κ (x * y) = κ x * (x * κ y * x⁻¹) := by
    intro x y
    simp only [κ, map_mul]
    group
  have hκU : ∀ (y : M) (u : M), u ∈ U → κ (y * u) = κ y := by
    intro y u hu
    simp only [κ, map_mul, hαU u hu]
    group
  let κR : ↥N → ↥R := fun x => ⟨κ x, hκ x x.2⟩
  let cx : ↥N → ↥R →* ↥R := fun x =>
    { toFun := fun r => ⟨x * r * x⁻¹, hRN x x.2 r r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  let t : (↥N ⧸ U') → ↥N := fun q => Quotient.out q
  let s : ↥R := ∏ q : ↥N ⧸ U', κR (t q)
  have hcoset : ∀ (x : ↥N) (q : ↥N ⧸ U'), κR (t (x • q)) = κR x * cx x (κR (t q)) := by
    intro x q
    have h1 : (↑(t (x • q)) : ↥N ⧸ U') = x • q := QuotientGroup.out_eq' _
    have h2 : (↑(t q) : ↥N ⧸ U') = q := QuotientGroup.out_eq' _
    have h3 : (↑(x * t q) : ↥N ⧸ U') = ↑(t (x • q)) :=
      calc (↑(x * t q) : ↥N ⧸ U') = x • (↑(t q) : ↥N ⧸ U') := rfl
        _ = x • q := by rw [h2]
        _ = ↑(t (x • q)) := h1.symm
    have h4 := QuotientGroup.eq.mp h3.symm
    have h5 : (((t (x • q))⁻¹ * (x * t q) : ↥N) : M) ∈ U := h4
    apply Subtype.ext
    show κ (t (x • q)) = κ x * ((x : M) * κ (t q) * (x : M)⁻¹)
    have e : (x : M) * (t q : M) = (t (x • q) : M) * (((t (x • q))⁻¹ * (x * t q) : ↥N) : M) := by
      simp
    rw [← hκmul, e, hκU _ _ h5]
  have hprod : ∀ x : ↥N, s = κR x ^ (Fintype.card (↥N ⧸ U')) * cx x s := by
    intro x
    have h1 : ∏ q : ↥N ⧸ U', κR (t (x • q)) = s :=
      Equiv.prod_comp (MulAction.toPerm x) (fun q => κR (t q))
    calc s = ∏ q : ↥N ⧸ U', κR (t (x • q)) := h1.symm
      _ = ∏ q : ↥N ⧸ U', (κR x * cx x (κR (t q))) :=
        Finset.prod_congr rfl fun q _ => hcoset x q
      _ = κR x ^ (Fintype.card (↥N ⧸ U')) * cx x s := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod]
  have hm : Odd (Fintype.card (↥N ⧸ U')) := by
    have : Fintype.card (↥N ⧸ U') = U.relIndex N := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [this]
    exact Nat.not_even_iff_odd.mp (fun he => hodd (even_iff_two_dvd.mp he))
  have hsq : ∀ r : ↥R, r ^ 2 = 1 := fun r => Subtype.ext (by simpa using hR.2 r r.2)
  have hpow : ∀ r : ↥R, r ^ (Fintype.card (↥N ⧸ U')) = r := by
    intro r
    obtain ⟨j, hj⟩ := hm
    rw [hj, pow_succ, pow_mul, hsq r, one_pow, one_mul]
  refine ⟨(s : M), s.2, fun x hx => ?_⟩
  have h := hprod ⟨x, hx⟩
  rw [hpow] at h
  have h' : (s : M) = α x * x⁻¹ * (x * (s : M) * x⁻¹) := congrArg Subtype.val h
  have hk : (s : M) * (x * (s : M) * x⁻¹)⁻¹ = α x * x⁻¹ := mul_inv_eq_iff_eq_mul.mpr h'
  calc α x = (α x * x⁻¹) * x := by group
    _ = (s : M) * (x * (s : M) * x⁻¹)⁻¹ * x := by rw [hk]
    _ = s * x * (s : M)⁻¹ := by group


theorem mul_inv_mem_of_fix {M : Type} [Group M] (α : MulAut M) {R : Subgroup M}
    (hfix : ∀ r ∈ R, α r = r) (hC : ∀ g : M, (∀ r ∈ R, g * r = r * g) → g ∈ R) {x : M}
    (hx : x ∈ Subgroup.normalizer (R : Set M)) : α x * x⁻¹ ∈ R := by
  apply hC
  intro r hr
  have hr' : x⁻¹ * r * x ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) r).mp hr
    simpa using this
  have h1 : α (x * (x⁻¹ * r * x) * x⁻¹) = x * (x⁻¹ * r * x) * x⁻¹ := by
    have : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    rw [this]
    exact hfix r hr
  rw [map_mul, map_mul, map_inv, hfix _ hr'] at h1
  have h2 : α x * (x⁻¹ * r * x) * (α x)⁻¹ = r := by
    have : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    rw [this] at h1
    exact h1
  calc α x * x⁻¹ * r = (α x * (x⁻¹ * r * x) * (α x)⁻¹) * (α x * x⁻¹) := by group
    _ = r * (α x * x⁻¹) := by rw [h2]

theorem aut_eq_conj_of_fix {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    (hM : ModelData M U R₁ R₂)
    (hsup : Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) = ⊤)
    (hfix : ∀ w ∈ R₁ ⊓ R₂, (∀ b ∈ Subgroup.normalizer (U : Set M), b * w = w * b) → w = 1)
    (α : MulAut M) (hα : ∀ u ∈ U, α u = u) :
    ∃ w ∈ R₁ ⊓ R₂, ∀ x : M, α x = w * x * w⁻¹ := by
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set M) :=
    (Subgroup.le_normalizer (H := U)).trans hM.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set M) :=
    (Subgroup.le_normalizer (H := U)).trans hM.lt₂.le
  have hBN₁ : Subgroup.normalizer (U : Set M) ≤ Subgroup.normalizer (R₁ : Set M) := hM.lt₁.le
  have hBN₂ : Subgroup.normalizer (U : Set M) ≤ Subgroup.normalizer (R₂ : Set M) := hM.lt₂.le
  have hcoc : ∀ (R : Subgroup M), IsElemAbelian 2 R → R ≤ U →
      (∀ g : M, (∀ r ∈ R, g * r = r * g) → g ∈ R) → U ≤ Subgroup.normalizer (R : Set M) →
      ∃ r ∈ R, ∀ x ∈ Subgroup.normalizer (R : Set M), α x = r * x * r⁻¹ := by
    intro R hRe hRU hCR hUN
    refine inner_of_cocycle α (isSylowTwoOf_of_le hM.sylow hUN).2.2 hRe
      (fun x hx r hr => (Subgroup.mem_normalizer_iff.mp hx r).mp hr) hα
      (fun x hx => mul_inv_mem_of_fix α (fun r hr => hα r (hRU hr)) hCR hx)
  obtain ⟨r₁, hr₁, hα₁⟩ := hcoc R₁ hM.elem₁ hM.le₁ hM.cent₁ hUN₁
  obtain ⟨r₂, hr₂, hα₂⟩ := hcoc R₂ hM.elem₂ hM.le₂ hM.cent₂ hUN₂
  have hr₁₂ : r₁ ∈ R₂ := by
    apply hM.cent₂
    intro u hu
    have h1 := hα₁ u (hUN₁ (hM.le₂ hu))
    rw [hα u (hM.le₂ hu)] at h1
    calc r₁ * u = (r₁ * u * r₁⁻¹) * r₁ := by group
      _ = u * r₁ := by rw [← h1]
  have hr₂₁ : r₂ ∈ R₁ := by
    apply hM.cent₁
    intro u hu
    have h1 := hα₂ u (hUN₂ (hM.le₁ hu))
    rw [hα u (hM.le₁ hu)] at h1
    calc r₂ * u = (r₂ * u * r₂⁻¹) * r₂ := by group
      _ = u * r₂ := by rw [← h1]
  have hw : r₂⁻¹ * r₁ ∈ R₁ ⊓ R₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hr₂₁) hr₁, mul_mem (inv_mem hr₂) hr₁₂⟩
  have hw1 : r₂⁻¹ * r₁ = 1 := by
    apply hfix _ hw
    intro b hb
    have h1 := hα₁ b (hBN₁ hb)
    have h2 := hα₂ b (hBN₂ hb)
    have h3 : r₁ * b * r₁⁻¹ = r₂ * b * r₂⁻¹ := h1.symm.trans h2
    calc b * (r₂⁻¹ * r₁) = (r₂⁻¹ * (r₁ * b * r₁⁻¹) * r₂) * (r₂⁻¹ * r₁) := by
          rw [h3]; group
      _ = r₂⁻¹ * r₁ * b := by group
  have hr12 : r₁ = r₂ := (inv_mul_eq_one.mp hw1).symm
  refine ⟨r₁, Subgroup.mem_inf.mpr ⟨hr₁, hr₁₂⟩, fun x => ?_⟩
  let S : Subgroup M := MonoidHom.eqLocus α.toMonoidHom (MulAut.conj r₁).toMonoidHom
  have hS₁ : Subgroup.normalizer (R₁ : Set M) ≤ S := fun y hy => hα₁ y hy
  have hS₂ : Subgroup.normalizer (R₂ : Set M) ≤ S := fun y hy => by
    have := hα₂ y hy
    rw [← hr12] at this
    exact this
  have : (⊤ : Subgroup M) ≤ S := hsup ▸ sup_le hS₁ hS₂
  exact this (Subgroup.mem_top x)

end CFSG.QuasithinUnique.Fin257
