module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveSteps

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem eq_of_conj_eq {X : Type} [Group X] {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    {k k' : X} (hk : k ∈ K) (hk' : k' ∈ K) (h : ∀ c ∈ K, k * c * k⁻¹ = k' * c * k'⁻¹) :
    k = k' := by
  have hmem : (⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk'⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (c : X) * (k⁻¹ * k') = k⁻¹ * (k * c * k⁻¹) * k' := by group
      _ = k⁻¹ * (k' * c * k'⁻¹) * k' := by rw [h c c.2]
      _ = k⁻¹ * k' * c := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp (congrArg Subtype.val hmem)

theorem mem_normalizer_sup {G : Type*} [Group G] {H L : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hL ⊢
  rw [Subgroup.map_sup, hH, hL]

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem exists_inner_of_mem_E (h : ThreeNineHyp K E D X₁ p d)
    (hout : ¬ p ∣ Nat.card (Outer ↥K)) {x : X} (hxE : x ∈ E) :
    ∃ k ∈ K, ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹ := by
  have : K.Normal := h.normal
  set α : MulAut ↥K := MulAut.conjNormal x
  have hα : α ^ p = 1 := by rw [← map_pow, h.elem.2 x hxE, map_one]
  set o : Outer ↥K := QuotientGroup.mk α
  have ho : o ^ p = 1 := by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have ho1 : o = 1 := by
    rcases (Nat.dvd_prime h.prime).1 (orderOf_dvd_of_pow_eq_one ho) with h1 | hp
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (hp ▸ orderOf_dvd_natCard o) hout
  obtain ⟨b, hbk⟩ := (QuotientGroup.eq_one_iff α).mp ho1
  refine ⟨b, b.2, fun c hc => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hc⟩ : ↥K) : X)) hbk
  simp only [MulAut.conj_apply, α, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1.symm

theorem exists_barE (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ¬ p ∣ Nat.card (Outer ↥K)) :
    ∃ Ebar : Subgroup ↥K, IsElemAbelian p Ebar ∧ Nat.card Ebar = p ^ 2 ∧
      (∀ e ∈ Ebar, e ≠ 1 → Subgroup.centralizer {e} ≤ X₁.subgroupOf K) ∧
      ∀ R : Subgroup ↥K, IsPGroup p R → Ebar ≤ R →
        Subgroup.normalizer (R : Set ↥K) ≤ X₁.subgroupOf K := by
  have : K.Normal := h.normal
  choose k hkK hk using fun x : ↥E => h.exists_inner_of_mem_E hout x.2
  have hmul : ∀ x y : ↥E, k (x * y) = k x * k y := by
    intro x y
    refine eq_of_conj_eq hZ (hkK (x * y)) (K.mul_mem (hkK x) (hkK y)) fun c hc => ?_
    have hyc : (y : X) * c * (y : X)⁻¹ ∈ K := by
      rw [hk y c hc]
      exact K.mul_mem (K.mul_mem (hkK y) hc) (K.inv_mem (hkK y))
    calc k (x * y) * c * (k (x * y))⁻¹
        = (x : X) * ((y : X) * c * (y : X)⁻¹) * (x : X)⁻¹ := by
          rw [← hk (x * y) c hc]; simp only [Subgroup.coe_mul]; group
      _ = k x * (k y * c * (k y)⁻¹) * (k x)⁻¹ := by rw [hk x _ hyc, hk y c hc]
      _ = k x * k y * c * (k x * k y)⁻¹ := by group
  have hk1 : k 1 = 1 :=
    eq_of_conj_eq hZ (hkK 1) K.one_mem fun c hc => by rw [← hk 1 c hc]; simp
  let φ : ↥E →* ↥K :=
    { toFun := fun x => ⟨k x, hkK x⟩
      map_one' := Subtype.ext hk1
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  have hcent : ∀ x : ↥E, ∀ c ∈ K, (k x)⁻¹ * x * c = c * ((k x)⁻¹ * x) := by
    intro x c hc
    calc (k x)⁻¹ * x * c = (k x)⁻¹ * ((x : X) * c * (x : X)⁻¹) * x := by group
      _ = (k x)⁻¹ * (k x * c * (k x)⁻¹) * x := by rw [hk x c hc]
      _ = c * ((k x)⁻¹ * x) := by group
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hkx : k x = 1 := congrArg Subtype.val hx
    apply Subtype.ext
    refine h.E_faithful x.2 fun c hc => ?_
    simpa [hkx] using hcent x c hc
  have hcomm : IsMulCommutative φ.range := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul]
    rw [h.elem.1.is_comm.comm x y]
  refine ⟨φ.range, ⟨hcomm, ?_⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (h.elem.2 x x.2), map_one]
  · rw [← h.card_E]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · rintro _ ⟨x, rfl⟩ hx1 c hc
    have hx1' : (x : X) ≠ 1 := fun h1 => hx1 (by
      rw [show x = 1 from Subtype.ext h1, map_one])
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_subgroupOf]
    refine h.mem_of_commute_E x.2 hx1' ((le_sup_left : K ≤ K ⊔ D) c.2) ?_
    have hc' : (c : X) * k x = k x * c := congrArg Subtype.val hc
    calc (x : X) * c = k x * ((k x)⁻¹ * x * c) := by group
      _ = k x * (c * ((k x)⁻¹ * x)) := by rw [hcent x c c.2]
      _ = k x * c * (k x)⁻¹ * x := by group
      _ = c * x := by rw [← hc']; group
  · intro P hPp hEP n hn
    rw [Subgroup.mem_subgroupOf]
    let ψ : ↥E →* X :=
      { toFun := fun x => (k x)⁻¹ * x
        map_one' := by simp [hk1]
        map_mul' := fun x y => by
          simp only [Subgroup.coe_mul, hmul x y, mul_inv_rev]
          have hc := hcent x (k y)⁻¹ (K.inv_mem (hkK y))
          calc (k y)⁻¹ * (k x)⁻¹ * ((x : X) * y) = (k y)⁻¹ * ((k x)⁻¹ * x) * y := by group
            _ = (k x)⁻¹ * x * (k y)⁻¹ * y := by rw [← hc]
            _ = (k x)⁻¹ * x * ((k y)⁻¹ * y) := by group }
    set A : Subgroup X := P.map K.subtype
    set B : Subgroup X := ψ.range
    have hBc : ∀ b ∈ B, ∀ c ∈ K, c * b = b * c := by
      rintro _ ⟨x, rfl⟩ c hc
      exact (hcent x c hc).symm
    have hEp : IsPGroup p ↥E := IsPGroup.of_card h.card_E
    have hA : IsPGroup p A := hPp.map K.subtype
    have hB : IsPGroup p B := hEp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hAB : A ≤ Subgroup.normalizer (B : Set X) := by
      rintro a ⟨q, -, rfl⟩
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro b hb
      exact (hBc b hb q q.2).symm
    have hQ : IsPGroup p (A ⊔ B : Subgroup X) := IsPGroup.to_sup_of_normal_right' hA hB hAB
    have hEQ : E ≤ A ⊔ B := by
      intro x hx
      have hkA : k ⟨x, hx⟩ ∈ A := Subgroup.mem_map.mpr ⟨φ ⟨x, hx⟩, hEP ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      have hψ : (k ⟨x, hx⟩)⁻¹ * x ∈ B := ⟨⟨x, hx⟩, rfl⟩
      have := (A ⊔ B).mul_mem (Subgroup.mem_sup_left hkA) (Subgroup.mem_sup_right hψ)
      simpa using this
    have hnA : (n : X) ∈ Subgroup.normalizer (A : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨n * q * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn q).mp hq, by simp⟩
      · rintro ⟨q, hq, hqy⟩
        have hqy' : (q : X) = n * y * (n : X)⁻¹ := hqy
        have hyK : y ∈ K := by
          have : y = (n : X)⁻¹ * q * n := by rw [hqy']; group
          rw [this]
          exact K.mul_mem (K.mul_mem (K.inv_mem n.2) q.2) n.2
        have heq : n * ⟨y, hyK⟩ * n⁻¹ = q :=
          Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hqy'.symm)
        refine ⟨⟨y, hyK⟩, (Subgroup.mem_normalizer_iff.mp hn ⟨y, hyK⟩).mpr ?_, rfl⟩
        rw [heq]
        exact hq
    have hnB : (n : X) ∈ Subgroup.normalizer (B : Set X) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro b hb
      exact (hBc b hb n n.2).symm
    exact h.normQ (A ⊔ B) hQ hEQ ⟨mem_normalizer_sup hnA hnB, (le_sup_left : K ≤ K ⊔ D) n.2⟩

end ThreeNineHyp

end CFSG.LocalAnalysis.AGL81I.Section3
