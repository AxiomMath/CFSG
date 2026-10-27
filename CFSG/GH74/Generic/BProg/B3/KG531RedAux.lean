module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.BProg.B3.KG531Red

open Subgroup CFSG
open scoped MatrixGroups

theorem not_le_center_of_isQuasisimple {X : Type*} [Group X] {J : Subgroup X}
    (hJ : IsQuasisimple J) : ¬ J ≤ center X := by
  intro hJZ
  obtain ⟨-, -, a, b, hab⟩ := hJ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h : a * b = b * a := Subtype.ext (mem_center_iff.mp (hJZ a.2) b).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem conj_mem_centralizer {Q : Type*} [Group Q] {u q c : Q}
    (hq : QuotientGroup.mk' (center Q) q ∈ centralizer ({QuotientGroup.mk' (center Q) u} : Set _))
    (hc : c ∈ centralizer ({u} : Set Q)) : q * c * q⁻¹ ∈ centralizer ({u} : Set Q) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hq hc ⊢
  have hq' : (u⁻¹ * q⁻¹ * u * q) ∈ center Q := by
    have := hq
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at this
    simpa [mul_assoc] using this
  have hw : ∀ g : Q, g * (u⁻¹ * q⁻¹ * u * q) = (u⁻¹ * q⁻¹ * u * q) * g :=
    Subgroup.mem_center_iff.mp hq'
  have h1 : c * (q⁻¹ * u * q) = (q⁻¹ * u * q) * c := by
    have e1 : q⁻¹ * u * q = u * (u⁻¹ * q⁻¹ * u * q) := by group
    rw [e1]
    calc c * (u * (u⁻¹ * q⁻¹ * u * q)) = (c * u) * (u⁻¹ * q⁻¹ * u * q) := by group
      _ = (u * c) * (u⁻¹ * q⁻¹ * u * q) := by rw [hc]
      _ = u * (c * (u⁻¹ * q⁻¹ * u * q)) := by group
      _ = u * ((u⁻¹ * q⁻¹ * u * q) * c) := by rw [hw c]
      _ = u * (u⁻¹ * q⁻¹ * u * q) * c := by group
  calc q * c * q⁻¹ * u = q * (c * (q⁻¹ * u * q)) * q⁻¹ := by group
    _ = q * ((q⁻¹ * u * q) * c) * q⁻¹ := by rw [h1]
    _ = u * (q * c * q⁻¹) := by group

theorem range_le_centralizer {K Q : Type*} [Group K] [Group Q] (κ : K →* Q) {u : Q}
    (hrange : κ.range = centralizer ({u} : Set Q)) :
    ((QuotientGroup.mk' (center Q)).comp κ).range ≤
      centralizer ({QuotientGroup.mk' (center Q) u} : Set (Q ⧸ center Q)) := by
  rintro _ ⟨k, rfl⟩
  have : κ k ∈ centralizer ({u} : Set Q) := hrange ▸ ⟨k, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, this]

theorem isComponent_central_quotient {K Q : Type*} [Group K] [Group Q] (κ : K →* Q)
    (hκ : Function.Injective κ) {u : Q} (hrange : κ.range = centralizer ({u} : Set Q))
    {J : Subgroup K} (hJ : IsComponent J) :
    IsComponent ((J.map ((QuotientGroup.mk' (center Q)).comp κ)).subgroupOf
      (centralizer ({QuotientGroup.mk' (center Q) u} : Set (Q ⧸ center Q)))) := by
  set π := QuotientGroup.mk' (center Q) with hπ
  set ρ := π.comp κ with hρ
  set Cb := centralizer ({π u} : Set (Q ⧸ center Q)) with hCb
  have hmemC : ∀ k : K, κ k ∈ centralizer ({u} : Set Q) := fun k => hrange ▸ ⟨k, rfl⟩
  have hle : ρ.range ≤ Cb := range_le_centralizer κ hrange
  have hker : ρ.ker ≤ center K := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply hκ
    simpa using (Subgroup.mem_center_iff.mp hk (κ g))
  let ρ' : K →* ↥Cb := ρ.codRestrict Cb (fun k => hle ⟨k, rfl⟩)
  have hrange' : ρ'.range = ρ.range.subgroupOf Cb := by
    ext x
    simp [MonoidHom.mem_range, Subgroup.mem_subgroupOf, ρ', Subtype.ext_iff]
  have hnorm : (ρ.range.subgroupOf Cb).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := hn
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (center Q) (g : Q ⧸ center Q)
    have hgC : π q ∈ centralizer ({π u} : Set _) := by rw [hπ, hq]; exact g.2
    have h2 := conj_mem_centralizer hgC (hmemC k)
    rw [← hrange] at h2
    obtain ⟨k', hk'⟩ := h2
    refine ⟨k', ?_⟩
    simp only [hρ, MonoidHom.comp_apply, hk', map_mul, map_inv] at hk ⊢
    rw [hq, hk]
    rfl
  have himg : (J.map ρ).subgroupOf Cb = J.map ρ' := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, ρ', Subtype.ext_iff]
  rw [himg]
  have hkerρ' : ρ'.ker ≤ center K := by
    intro k hk
    apply hker
    rw [MonoidHom.mem_ker] at hk ⊢
    exact congrArg Subtype.val hk
  refine ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 ρ'
    (fun h => not_le_center_of_isQuasisimple hJ.1 (h.trans hkerρ')), ?_⟩
  have h1 : (J.map ρ'.rangeRestrict).IsSubnormal := hJ.2.map ρ'.rangeRestrict_surjective
  have hn' : ρ'.range.Normal := hrange' ▸ hnorm
  have h2 := h1.trans' hn'.isSubnormal
  have h3 : ρ'.range.subtype.comp ρ'.rangeRestrict = ρ' := MonoidHom.ext fun _ => rfl
  rwa [Subgroup.map_map, h3] at h2

theorem false_of_components_top {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {B₁ B₂ : Subgroup S}
    (hc₁ : IsComponent (B₁.subgroupOf (⊤ : Subgroup S)))
    (hc₂ : IsComponent (B₂.subgroupOf (⊤ : Subgroup S)))
    (hcomm : ∀ b ∈ B₁, ∀ c ∈ B₂, b * c = c * b) : False := by
  have key : ∀ B : Subgroup S, IsComponent (B.subgroupOf (⊤ : Subgroup S)) → B = ⊤ := by
    intro B hB
    have hsub : B.IsSubnormal := by
      have := hB.2.trans' (Subgroup.IsSubnormal.top : (⊤ : Subgroup S).IsSubnormal)
      rwa [Subgroup.map_subgroupOf_eq_of_le le_top] at this
    rcases hsub.eq_bot_or_top_of_isSimpleGroup hS with h | h
    · exfalso
      have hnt : Nontrivial ↥(B.subgroupOf (⊤ : Subgroup S)) :=
        CFSG.LocalCores.isQuasisimple_nontrivial hB.1
      rw [h, Subgroup.bot_subgroupOf] at hnt
      exact (not_nontrivial _) hnt
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  refine hab (hcomm a ?_ b ?_)
  · rw [key B₁ hc₁]; exact Subgroup.mem_top a
  · rw [key B₂ hc₂]; exact Subgroup.mem_top b

theorem center_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (h : a ∈ center A) : e a ∈ center B := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp h g']

theorem sl2_center_cases {F : Type*} [Field F] {z w : SL(2, F)} (hz : z ∈ center SL(2, F))
    (hw : w ∈ center SL(2, F)) (hw1 : w ≠ 1) : z = 1 ∨ z = w := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  obtain ⟨s, hs, hsw⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw
  simp only [Fintype.card_fin] at hr hs
  have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.mp (by simpa [sq] using hr)
  have hs' : s = 1 ∨ s = -1 := mul_self_eq_one_iff.mp (by simpa [sq] using hs)
  rcases hs' with rfl | rfl
  · exact absurd (Subtype.ext (by rw [← hsw]; simp)) hw1
  · rcases hr' with rfl | rfl
    · left
      exact Subtype.ext (by rw [← hrz]; simp)
    · right
      exact Subtype.ext (by rw [← hrz, ← hsw])

theorem exists_prime_pow_card {F : Type*} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    (hF : 5 ≤ Fintype.card F) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Nat.card F = p ^ f ∧ 5 ≤ p ^ f := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  refine ⟨ringChar F, n, hp, ?_, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn, hn ▸ hF⟩
  intro h
  rw [h] at hn
  rw [hn] at hodd
  have := (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr hodd) (by simpa using this)

end CFSG.GH74.Generic.BProg.B3.KG531Red
