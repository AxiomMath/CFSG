module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627Act

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.IVK

variable {G : Type} [Group G] [Finite G]

theorem e4_false {t u : G} {J T : Subgroup G} {a : G}
    (hT2 : IsPGroup 2 ↥T) (hcen : CenterlessBar J)
    (hTC : T ≤ centralizer ({t} : Set G))
    (hnormT : ∀ m ∈ T, ∀ l ∈ J, m * l * m⁻¹ ∈ J)
    (hD8 : IsD8 (Back.actHom hnormT).range)
    (hT32 : Nat.card ↥T = 32) (hQ4 : Nat.card ↥(T ⊓ CxK t J) = 4)
    (hPJ : 4 ≤ Nat.card ↥(T ⊓ J))
    (huT : u ∈ T) (hQab : ∀ q ∈ T ⊓ CxK t J, ∀ q' ∈ T ⊓ CxK t J, q * q' = q' * q)
    (hQu : ∀ q ∈ T ⊓ CxK t J, q * u = u * q)
    (hout : Back.actHom hnormT ⟨u, huT⟩ ∉ innAut (kBar J))
    (haN : a ∈ normalizer (T : Set G))
    (hdisj : (T ⊓ CxK t J) ⊓ conjugate (T ⊓ CxK t J) a = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := Back.actHom hnormT with hψ
  set P := T ⊓ J with hP
  set Q := T ⊓ CxK t J with hQ
  have hcd : Th2.CommDisj P Q := commDisj_inf hT2 hcen
  have hcardPQ : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q :=
    card_sup_of_commute_of_disjoint hcd.comm hcd.inf
  have huPQ : u ∉ P ⊔ Q := by
    intro hu
    obtain ⟨p, hp, q, hq, hupq⟩ := mem_sup_of_commute hcd.comm hu
    have hψq : ψ ⟨q, hq.1⟩ = 1 := (actHom_eq_one_iff_mem hTC hnormT hq.1).2 hq.2
    have hψu : ψ ⟨u, huT⟩ = ψ ⟨p, hp.1⟩ * ψ ⟨q, hq.1⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hupq
    have hψp : ψ ⟨p, hp.1⟩ = MulAut.conj (QuotientGroup.mk (⟨p, hp.2⟩ : ↥J) : kBar J) :=
      Back.actHom_of_mem hnormT hp.2 hp.1
    apply hout
    rw [hψu, hψq, mul_one, hψp]
    exact ⟨_, rfl⟩
  have hsub : (P ⊔ Q) ⊔ zpowers u ≤ T := sup_le (sup_le inf_le_left inf_le_left) (zpowers_le.2 huT)
  have hne : P ⊔ Q ≠ (P ⊔ Q) ⊔ zpowers u := fun h => by
    have hu : u ∈ (P ⊔ Q) ⊔ zpowers u := Subgroup.mem_sup_right (mem_zpowers u)
    rw [← h] at hu
    exact huPQ hu
  have hTbig : IsPGroup 2 ↥((P ⊔ Q) ⊔ zpowers u) := hT2.to_le hsub
  have h2 : 2 * Nat.card ↥(P ⊔ Q) ≤ Nat.card ↥((P ⊔ Q) ⊔ zpowers u) :=
    two_mul_card_le hTbig le_sup_left hne
  have h16 : 16 ≤ Nat.card ↥(P ⊔ Q) := by rw [hcardPQ, hQ4]; omega
  have hTeq : (P ⊔ Q) ⊔ zpowers u = T :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hT32]; omega)
  have hQc : ∀ q ∈ Q, ∀ τ ∈ T, q * τ = τ * q := by
    intro q hq τ hτ
    have hle : T ≤ centralizer ({q} : Set G) := by
      rw [← hTeq]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro p hp
        exact mem_centralizer_singleton_iff.2 (hcd.comm p hp q hq)
      · intro q' hq'
        exact mem_centralizer_singleton_iff.2 (hQab q' hq' q hq)
      · refine zpowers_le.2 ?_
        exact mem_centralizer_singleton_iff.2 (hQu q hq).symm
    exact (mem_centralizer_singleton_iff.1 (hle hτ)).symm
  have haT : ∀ τ ∈ T, a * τ * a⁻¹ ∈ T := fun τ hτ => (Subgroup.mem_normalizer_iff.1 haN τ).1 hτ
  have haT' : ∀ τ ∈ T, a⁻¹ * τ * a ∈ T := fun τ hτ => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem haN) τ).1 hτ
    simpa using this
  have hQaT : conjugate Q a ≤ T := by
    intro g hg
    have h1 : a * g * a⁻¹ ∈ T := (mem_conjugate_iff'.1 hg).1
    have := haT' _ h1
    have e : a⁻¹ * (a * g * a⁻¹) * a = g := by group
    rwa [e] at this
  have hQac : ∀ g ∈ conjugate Q a, ∀ τ ∈ T, g * τ = τ * g := by
    intro g hg τ hτ
    have hg' : a * g * a⁻¹ ∈ Q := mem_conjugate_iff'.1 hg
    have := hQc _ hg' _ (haT τ hτ)
    have e1 : a * g * a⁻¹ * (a * τ * a⁻¹) = a * (g * τ) * a⁻¹ := by group
    have e2 : a * τ * a⁻¹ * (a * g * a⁻¹) = a * (τ * g) * a⁻¹ := by group
    rw [e1, e2] at this
    exact mul_left_cancel (mul_right_cancel this)
  obtain ⟨z, hzR, hz1, -, hzc, hzu⟩ := hD8.exists_z
  let ψ' : ↥(conjugate Q a) → MulAut (kBar J) := fun g => ψ ⟨(g : G), hQaT g.2⟩
  have hψ'inj : Function.Injective ψ' := by
    intro g₁ g₂ h
    have hmem : ((g₁ : G) * (g₂ : G)⁻¹) ∈ conjugate Q a :=
      mul_mem g₁.2 (Subgroup.inv_mem _ g₂.2)
    have hker : ψ ⟨(g₁ : G) * (g₂ : G)⁻¹, hQaT hmem⟩ = 1 := by
      have : (⟨(g₁ : G) * (g₂ : G)⁻¹, hQaT hmem⟩ : ↥T) =
          ⟨(g₁ : G), hQaT g₁.2⟩ * ⟨(g₂ : G), hQaT g₂.2⟩⁻¹ := rfl
      rw [this, map_mul, map_inv]
      exact mul_inv_eq_one.2 h
    have hCx : (g₁ : G) * (g₂ : G)⁻¹ ∈ CxK t J :=
      (actHom_eq_one_iff_mem hTC hnormT (hQaT hmem)).1 hker
    have h1 : (g₁ : G) * (g₂ : G)⁻¹ ∈ Q ⊓ conjugate Q a := ⟨⟨hQaT hmem, hCx⟩, hmem⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    exact Subtype.ext (mul_inv_eq_one.1 h1)
  have hcard4 : Nat.card ↥(conjugate Q a) = 4 := by rw [card_conjugate', hQ4]
  have hcent : ∀ g : ↥(conjugate Q a), ψ' g = 1 ∨ ψ' g = z := by
    intro g
    refine hzu _ ⟨⟨g, hQaT g.2⟩, rfl⟩ (fun p hp => ?_)
    obtain ⟨τ, rfl⟩ := hp
    show ψ τ * ψ ⟨(g : G), hQaT g.2⟩ = ψ ⟨(g : G), hQaT g.2⟩ * ψ τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQac g g.2 τ τ.2).symm
  have : Fintype ↥(conjugate Q a) := Fintype.ofFinite _
  have hlt : Fintype.card Bool < Fintype.card ↥(conjugate Q a) := by
    rw [Fintype.card_bool, ← Nat.card_eq_fintype_card, hcard4]
    norm_num
  obtain ⟨x, y, hxy, hfxy⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun g : ↥(conjugate Q a) => decide (ψ' g = 1)) hlt
  apply hxy
  apply hψ'inj
  by_cases hx : ψ' x = 1
  · have hy : ψ' y = 1 := by simpa [hx] using hfxy.symm
    rw [hx, hy]
  · have hy : ¬ ψ' y = 1 := by
      intro hy
      simp [hx, hy] at hfxy
    rw [(hcent x).resolve_left hx, (hcent y).resolve_left hy]

end CFSG.GH74.GLS.Th2.L627
