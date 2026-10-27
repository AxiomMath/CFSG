module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.CosetNormalizer
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isConj_mul_of_mem_root {H U : Subgroup G} {z u : G}
    (hUset : (U : Set G) = {1} ∪ distinguishedRoots H z u)
    (hΔ : ∀ b ∈ U, IsConj u (u * b))
    (hconj : ∀ c : G, c * u * c⁻¹ ∈ H → ∃ m ∈ Subgroup.centralizer ({u} : Set G), c * m ∈ H)
    {x : G} (hxH : x ∈ H) (hxU : x ∈ Subgroup.centralizer (U : Set G)) (hx : IsConj u x)
    {b : G} (hb : b ∈ U) : IsConj u (x * b) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  obtain ⟨m, hm, hcm⟩ := hconj c hxH
  set h := c * m with hh
  have hmu : m * u = u * m := Subgroup.mem_centralizer_singleton_iff.mp hm
  have hhu : h * u * h⁻¹ = c * u * c⁻¹ := by
    rw [hh]
    calc c * m * u * (c * m)⁻¹ = c * (m * u) * m⁻¹ * c⁻¹ := by group
      _ = c * u * c⁻¹ := by rw [hmu]; group
  have hb' : h⁻¹ * b * h ∈ U := by
    have hbU := hb
    rw [← SetLike.mem_coe, hUset] at hb ⊢
    rcases hb with hb | ⟨⟨hbz, hbH⟩, -⟩
    · left
      rw [Set.mem_singleton_iff.mp hb]
      simp
    · right
      refine ⟨⟨?_, H.mul_mem (H.mul_mem (H.inv_mem hcm) hbH) hcm⟩, ?_⟩
      · rw [mem_involutionPointClass_iff] at hbz ⊢
        exact hbz.trans (isConj_iff.mpr ⟨h⁻¹, by rw [inv_inv]⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hbxc : b * (c * u * c⁻¹) = (c * u * c⁻¹) * b :=
          Subgroup.mem_centralizer_iff.mp hxU b hbU
        rw [← hhu] at hbxc
        calc h⁻¹ * b * h * u = h⁻¹ * (b * (h * u * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * u * h⁻¹) * b) * h := by rw [hbxc]
          _ = u * (h⁻¹ * b * h) := by group
  have hxb : c * u * c⁻¹ * b = h * (u * (h⁻¹ * b * h)) * h⁻¹ := by
    rw [← hhu]; group
  rw [hxb]
  exact (hΔ _ hb').trans (isConj_iff.mpr ⟨h, rfl⟩)

theorem inf_le_normalizer_root {H U : Subgroup G} {z u : G}
    (hUset : (U : Set G) = {1} ∪ distinguishedRoots H z u) :
    H ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  have key : ∀ g ∈ H ⊓ Subgroup.centralizer ({u} : Set G), ∀ b ∈ U, g * b * g⁻¹ ∈ U := by
    rintro g ⟨hgH, hgu⟩ b hb
    rw [← SetLike.mem_coe, hUset] at hb ⊢
    rcases hb with hb | ⟨⟨hbz, hbH⟩, hbu⟩
    · left
      rw [Set.mem_singleton_iff.mp hb]
      simp
    · right
      refine ⟨⟨?_, H.mul_mem (H.mul_mem hgH hbH) (H.inv_mem hgH)⟩, ?_⟩
      · rw [mem_involutionPointClass_iff] at hbz ⊢
        exact hbz.trans (isConj_iff.mpr ⟨g, rfl⟩)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgu hbu) (Subgroup.inv_mem _ hgu)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key g hg b, fun hb => ?_⟩
  have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hb
  have h2 : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
  rwa [h2] at h

theorem exists_conj_mem_sylow_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {P : Subgroup G} (hP : IsPGroup p P) : ∃ g : G, ∀ x ∈ P, g⁻¹ * x * g ∈ (S : Subgroup G) := by
  obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  refine ⟨g⁻¹, fun x hx => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, inv_inv]
  exact Set.mem_smul_set.mpr ⟨x, hPS' hx, rfl⟩

theorem isConj_mul_of_commute_of_sylow [Finite G] {u z : G} (hu : orderOf u = 2)
    (S : Sylow 2 (Subgroup.centralizer ({u} : Set G))) (U : Subgroup G)
    (hclass : ∀ x ∈ (S : Subgroup _).map (Subgroup.centralizer ({u} : Set G)).subtype,
      IsConj u x → ∃ w ∈ U, x = u * w)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    {a b : G} (ha : IsConj u a) (hb : IsConj u b) (hab : a ≠ b) (hcomm : Commute a b) :
    IsConj z (a * b) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  set b' := g⁻¹ * b * g with hb'
  have hb'u : b' ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm.eq
    calc b' * u = g⁻¹ * (b * (g * u * g⁻¹)) * g := by rw [hb']; group
      _ = g⁻¹ * ((g * u * g⁻¹) * b) * g := by rw [← h]
      _ = u * b' := by rw [hb']; group
  have hb'conj : IsConj u b' := hb.trans (isConj_iff.mpr ⟨g⁻¹, by rw [hb', inv_inv]⟩)
  have hb'order : orderOf b' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hb'conj
    rw [← hc, ← hu]
    simpa only [MulAut.conj_apply] using (MulAut.conj c).orderOf_eq u
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨b', hb'u⟩ : Subgroup.centralizer ({u} : Set G))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hb'order
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow_of_isPGroup S hp
  have hcS := hc _ (Subgroup.mem_zpowers _)
  have hcb'S : (c : G)⁻¹ * b' * c ∈
      (S : Subgroup _).map (Subgroup.centralizer ({u} : Set G)).subtype :=
    ⟨_, hcS, rfl⟩
  obtain ⟨w, hwU, hw⟩ := hclass _ hcb'S
    (hb'conj.trans (isConj_iff.mpr ⟨(c : G)⁻¹, by rw [inv_inv]⟩))
  have hcu : (c : G)⁻¹ * u * c = u := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc (c : G)⁻¹ * u * c = (c : G)⁻¹ * (c * u) := by rw [mul_assoc, h]
      _ = u := by group
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hab
    have h1 : (c : G)⁻¹ * b' * c = (c : G)⁻¹ * u * c := by rw [hw, mul_one, hcu]
    have h2 : b' = u := by simpa using h1
    rw [hb'] at h2
    calc g * u * g⁻¹ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h2]
      _ = b := by group
  have hprod : (g * c)⁻¹ * (g * u * g⁻¹ * b) * (g * c) = w := by
    have h : (g * c)⁻¹ * (g * u * g⁻¹ * b) * (g * c) =
        ((c : G)⁻¹ * u * c) * ((c : G)⁻¹ * b' * c) := by rw [hb']; group
    rw [h, hcu, hw, ← mul_assoc, huu, one_mul]
  have hconj : IsConj (g * u * g⁻¹ * b) w := hprod ▸ isConj_iff.mpr ⟨(g * c)⁻¹, by rw [inv_inv]⟩
  exact (hUz w hwU hw1).trans hconj.symm

end CFSG.ProperTwoGeneratedCore.HighRankPair
