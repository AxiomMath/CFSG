module

import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThree.PartOne.Planes CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83NormalElementaryRankFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G), IsPGroup 3 P → 4 ≤ Open.pRank 3 P →
    ∃ E : Subgroup G, E ≤ P ∧ P ≤ normalizer (E : Set G) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4

theorem nine_le_card_eqLocus {E : Type*} [CommGroup E] [Finite E] (hE : Nat.card E = 3 ^ 4)
    (h3 : ∀ y : E, y ^ 3 = 1) (α : E →* E) (hα : ∀ e, α (α (α e)) = e) :
    9 ≤ Nat.card (MonoidHom.eqLocus α (MonoidHom.id E)) := by
  classical
  let φ : E →* E := MonoidHom.mk' (fun e => α e * e⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv_rev]
    ac_rfl)
  have hφ : ∀ e, φ e = α e * e⁻¹ := fun e => rfl
  have hcube : ∀ y : E, y⁻¹ * y⁻¹ = y := by
    intro y
    have h := h3 y
    calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * (y * y * y) := by
          rw [show y * y * y = 1 by simpa [pow_succ] using h, mul_one]
      _ = y := by group
  have hφ2 : ∀ e, φ (φ e) = e * α e * α (α e) := by
    intro e
    rw [hφ, hφ, map_mul, map_inv]
    have := hcube (α e)
    calc α (α e) * (α e)⁻¹ * (α e * e⁻¹)⁻¹ = α (α e) * ((α e)⁻¹ * (α e)⁻¹) * e := by
          simp only [mul_inv_rev, inv_inv]; ac_rfl
      _ = e * α e * α (α e) := by rw [this]; ac_rfl
  have hφ3 : ∀ e, φ (φ (φ e)) = 1 := by
    intro e
    rw [hφ2 e, hφ, map_mul, map_mul, hα e]
    exact mul_inv_eq_one.2 (by ac_rfl)
  have hker : φ.ker = MonoidHom.eqLocus α (MonoidHom.id E) := by
    ext e
    simp only [MonoidHom.mem_ker, hφ, mul_inv_eq_one]
    rfl
  have h1 := Subgroup.card_ker_mul_card_range φ
  let R : Subgroup E := φ.range
  let ψ : R →* E := φ.comp R.subtype
  have h2 := Subgroup.card_ker_mul_card_range ψ
  have hψker : Nat.card ψ.ker ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective
      (fun r => (⟨(r.1 : R).1, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 r.2)⟩ : φ.ker)) ?_
    intro a b hab
    have := congrArg (fun z : φ.ker => (z : E)) hab
    exact Subtype.ext (Subtype.ext this)
  have hψrange : Nat.card ψ.range ≤ Nat.card φ.ker := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨r, rfl⟩
    obtain ⟨e, he⟩ := r.2
    rw [MonoidHom.mem_ker]
    change φ (φ r) = 1
    rw [← he]
    exact hφ3 e
  set k := Nat.card φ.ker with hk
  have hk81 : k * Nat.card R = 3 ^ 4 := h1.trans hE
  have hRk : Nat.card R ≤ k * k := by
    rw [← h2]
    exact Nat.mul_le_mul hψker hψrange
  have hkdvd : k ∣ 3 ^ 4 := Dvd.intro _ hk81
  have hk3 : 3 ^ 4 ≤ k * (k * k) := by
    calc 3 ^ 4 = k * Nat.card R := hk81.symm
      _ ≤ k * (k * k) := Nat.mul_le_mul_left _ hRk
  rw [← hker]
  show 9 ≤ k
  by_contra hlt
  have hkd : k ∣ 81 := by simpa using hkdvd
  have hlt' : k < 9 := by omega
  interval_cases k <;> omega

theorem le_pRank_of_isElemAbelian {p : ℕ} (hp : p.Prime) {Y A : Subgroup G} (hYA : Y ≤ A)
    (hY : IsElemAbelian p Y) {k : ℕ} (hk : p ^ k ≤ Nat.card Y) : k ≤ Open.pRank p A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p Y hY).exists_card_eq
  have hkj : k ≤ j := by
    rw [hj] at hk
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hk
  refine hkj.trans ?_
  unfold Open.pRank
  exact le_csSup (pRank_set_bddAbove p hp.one_lt _) ⟨Y, hYA, hY, hj⟩

theorem three_le_pRank_inf_centralizer_of_normal {P E : Subgroup G} (hEP : E ≤ P)
    (hEn : P ≤ normalizer (E : Set G)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 4)
    {x : G} (hxP : x ∈ P) (hx3 : x ^ 3 = 1) :
    3 ≤ Open.pRank 3 (P ⊓ centralizer ({x} : Set G)) := by
  classical
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hxn : x ∈ normalizer (E : Set G) := hEn hxP
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  by_cases hxE : x ∈ E
  ·
    have hEC : E ≤ P ⊓ centralizer ({x} : Set G) := by
      intro e he
      refine ⟨hEP he, mem_centralizer_singleton_iff.2 ?_⟩
      exact congrArg Subtype.val (hcomm ⟨e, he⟩ ⟨x, hxE⟩)
    have := le_pRank_of_isElemAbelian hp3 hEC hE (k := 4) (by rw [hEc])
    omega
  · let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
    let α : E →* E := MonoidHom.mk' (fun e => ⟨x * e * x⁻¹, (mem_normalizer_iff.1 hxn e).1 e.2⟩)
      (by
        intro a b
        apply Subtype.ext
        simp [mul_assoc])
    have hx111 : x * x * x = 1 := by simpa [pow_succ] using hx3
    have hα : ∀ e, α (α (α e)) = e := by
      intro e
      apply Subtype.ext
      change x * (x * (x * (e : G) * x⁻¹) * x⁻¹) * x⁻¹ = e
      have : x * (x * (x * (e : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * e * (x * x * x)⁻¹ := by
        group
      rw [this, hx111]
      simp
    have h3 : ∀ y : E, y ^ 3 = 1 := fun y =>
      Subtype.ext (by simpa using hE.2 y y.2)
    have h9 := nine_le_card_eqLocus (E := E) hEc h3 α hα
    set C : Subgroup G := E ⊓ centralizer ({x} : Set G) with hC
    have hC9 : 9 ≤ Nat.card C := by
      refine h9.trans ?_
      calc Nat.card (MonoidHom.eqLocus α (MonoidHom.id E))
          = Nat.card ((MonoidHom.eqLocus α (MonoidHom.id E)).map E.subtype) :=
            (card_map_of_injective E.subtype_injective).symm
        _ ≤ Nat.card C := by
          refine Subgroup.card_le_of_le ?_
          rintro _ ⟨f, hf, rfl⟩
          refine ⟨f.2, mem_centralizer_singleton_iff.2 ?_⟩
          have hf' : α f = f := hf
          have := congrArg Subtype.val hf'
          change x * (f : G) * x⁻¹ = f at this
          calc (f : G) * x = (x * (f : G) * x⁻¹) * x := by rw [this]
            _ = x * (f : G) := by group
    have hxC : x ∉ C := fun h => hxE h.1
    have hCx : ∀ c ∈ C, c * x = x * c := fun c hc => mem_centralizer_singleton_iff.1 hc.2
    have hcard : Nat.card ↥(C ⊔ zpowers x) = Nat.card C * 3 :=
      card_sup_zpowers hp3 C hx3 hxC hCx
    have hCe : IsElementaryAbelian 3 C :=
      isElementaryAbelian_of_le inf_le_left
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE)
    have hxe : IsElementaryAbelian 3 (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
    have hle : zpowers x ≤ centralizer (C : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun c hc => hCx c hc
    have hY : IsElementaryAbelian 3 ↥(C ⊔ zpowers x) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
    have hYle : C ⊔ zpowers x ≤ P ⊓ centralizer ({x} : Set G) := by
      refine sup_le (le_inf (inf_le_left.trans hEP) inf_le_right) (le_inf ?_ ?_)
      · exact zpowers_le.2 hxP
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    have := le_pRank_of_isElemAbelian hp3 hYle
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hY) (k := 3)
      (by rw [hcard]; omega)
    omega

theorem three_le_pRank_inf_centralizer (h313 : GL83NormalElementaryRankFour) {P : Subgroup G}
    (hP : IsPGroup 3 P) (hP4 : 4 ≤ Open.pRank 3 P) {x : G} (hxP : x ∈ P) (hx3 : x ^ 3 = 1) :
    3 ≤ Open.pRank 3 (P ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨E, hEP, hEn, hE, hEc⟩ := h313 G P hP hP4
  exact three_le_pRank_inf_centralizer_of_normal hEP hEn hE hEc hxP hx3

end CFSG.LocalAnalysis.RankFourTheoremC
