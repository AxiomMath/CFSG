module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped commutatorElement

section ComponentCentralizer

theorem not_isPGroup_two_quotient_center {Q : Type*} [Group Q] [Finite Q]
    (hQ : Open.IsQuasisimple Q) : ¬ IsPGroup 2 (Q ⧸ Subgroup.center Q) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have : Group.IsNilpotent (Q ⧸ Subgroup.center Q) := h2.isNilpotent
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ
  exact hab ((IsCyclic.isMulCommutative (α := Q ⧸ Subgroup.center Q)).is_comm.comm a b)

theorem le_center_of_normal_of_isPGroup_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : Open.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N ≤ Subgroup.center Q := by
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center Q))) with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    apply not_isPGroup_two_quotient_center hQ
    have hmap : IsPGroup 2 (N.map (QuotientGroup.mk' (Subgroup.center Q))) := h2.map _
    rw [htop] at hmap
    exact hmap.of_equiv Subgroup.topEquiv

theorem le_centralizer_of_forall_commutator_mem {Y : Type*} [Group Y] [Finite Y]
    {A N₀ S₀ L : Subgroup Y} (hL : IsComponentOf L ⊤) (hLN : L ≤ N₀) (hS : IsPGroup 2 S₀)
    (hNS : N₀ ≤ Subgroup.normalizer (S₀ : Set Y))
    (hAN : ∀ a ∈ A, ∀ x ∈ N₀, a * x * a⁻¹ * x⁻¹ ∈ S₀) :
    A ≤ Subgroup.centralizer (L : Set Y) := by
  have hQ : Open.IsQuasisimple L := hL.2.2
  have hSL : ∀ v ∈ S₀, v ∈ L → ∀ l ∈ L, v * l = l * v := by
    intro v hvS hvL l hl
    have hNn : (S₀.subgroupOf L).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hg := hNS (hLN g.2)
      simpa using (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h2 : IsPGroup 2 (S₀.subgroupOf L) := hS.comap_subtype
    have hcen := le_center_of_normal_of_isPGroup_two hQ hNn h2
      (Subgroup.mem_subgroupOf.mpr hvS : (⟨v, hvL⟩ : L) ∈ S₀.subgroupOf L)
    have := Subgroup.mem_center_iff.mp hcen ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have hLL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hQ.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  intro a ha
  by_cases haN : a ∈ Subgroup.normalizer (L : Set Y)
  · have hzp : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr ha
    have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set Y) :=
      (Subgroup.zpowers_le).mpr haN
    have hcomm : ⁅Subgroup.zpowers a, L⁆ ≤ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.commutator_le]
      intro g hg l hl
      have hgS : ⁅g, l⁆ ∈ S₀ := by
        rw [commutatorElement_def]
        exact hAN g (hzp hg) l (hLN hl)
      have hgL : ⁅g, l⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hzN hg) l).mp hl) (L.inv_mem hl)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (hSL _ hgS hgL m hm).symm
    have h1 : ⁅⁅L, Subgroup.zpowers a⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcomm
    have h2 : ⁅⁅Subgroup.zpowers a, L⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcomm
    have h3 : ⁅⁅L, L⁆, Subgroup.zpowers a⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hLL, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (h3 hl) a (Subgroup.mem_zpowers a)).symm
  · exfalso
    set L' := L.map (MulAut.conj a).toMonoidHom with hL'
    have hL'c : IsComponentOf L' ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj a) L).mpr hL
    have hne : L ≠ L' := by
      intro he
      apply haN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact he.symm
    have hLL' : L ≤ Subgroup.centralizer (L' : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL'c hne)
    apply not_isPGroup_two_quotient_center hQ
    intro z
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hxL' : a * l * a⁻¹ ∈ L' := ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have hc : Commute (a * l * a⁻¹) l⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (hLL' (L.inv_mem hl)) _ hxL')
    obtain ⟨e, he⟩ := hS ⟨a * l * a⁻¹ * l⁻¹, hAN a ha l (hLN hl)⟩
    have he' : (a * l * a⁻¹ * l⁻¹) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    rw [hc.mul_pow, inv_pow, mul_inv_eq_one] at he'
    have hlL' : l ^ 2 ^ e ∈ L' := he' ▸ L'.pow_mem hxL' _
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact (Subgroup.mem_centralizer_iff.mp (hLL' g.2) _ hlL').symm

theorem le_centralizer_pCore_of_forall_commutator_mem {Y : Type*} [Group Y] [Finite Y]
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) {A N₀ S₀ : Subgroup Y} (hS : IsPGroup 2 S₀)
    (hlN : CFSG.pCore l Y ≤ N₀) (hAN : ∀ a ∈ A, ∀ x ∈ N₀, a * x * a⁻¹ * x⁻¹ ∈ S₀) :
    A ≤ Subgroup.centralizer (CFSG.pCore l Y : Set Y) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hc := hAN a ha x (hlN hx)
  have hcl : a * x * a⁻¹ * x⁻¹ ∈ CFSG.pCore l Y := by
    have hn : (CFSG.pCore l Y).Normal := inferInstance
    exact (CFSG.pCore l Y).mul_mem (hn.conj_mem x hx a) ((CFSG.pCore l Y).inv_mem hx)
  have : Fact l.Prime := ⟨hl⟩
  have hdisj := IsPGroup.disjoint_of_ne l 2 hl2 (CFSG.pCore l Y) S₀ CFSG.pCore_isPGroup hS
  have h1 : a * x * a⁻¹ * x⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj hcl hc
  have h2 := mul_inv_eq_one.mp h1
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

end ComponentCentralizer

section InvariantSubgroups

variable {G : Type*} [Group G]

theorem eq_or_le_of_mem_normalizer {U X V : Subgroup G} {t : G} (hX : ⁅U, U⁆ = X)
    (hXc : X ≤ Subgroup.centralizer (U : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ W : Subgroup G, X ≤ W → W ≤ U → t ∈ Subgroup.normalizer (W : Set G) →
      W = X ∨ W = U)
    (hVU : V ≤ U) (htV : t ∈ Subgroup.normalizer (V : Set G)) : V = U ∨ V ≤ X := by
  have hXU : X ≤ U := hX ▸ Subgroup.commutator_le_self U
  have hcen : ∀ x ∈ X, ∀ u ∈ U, x * u = u * x := fun x hx u hu =>
    (Subgroup.mem_centralizer_iff.mp (hXc hx) u hu).symm
  have hXV : X ≤ Subgroup.normalizer (V : Set G) :=
    hXc.trans ((Subgroup.centralizer_le hVU).trans (Subgroup.centralizer_le_normalizer _))
  have htVX : t ∈ Subgroup.normalizer ((V ⊔ X : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htV htX ⊢
    rw [Subgroup.map_sup, htV, htX]
  rcases hirr (V ⊔ X) le_sup_right (sup_le hVU hXU) htVX with h | h
  · exact Or.inr (le_sup_left.trans h.le)
  · left
    have hXV' : X ≤ V := by
      rw [← hX, ← h, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left V X hXV
      have hg₁' : g₁ ∈ ((V ⊔ X : Subgroup G) : Set G) := hg₁
      have hg₂' : g₂ ∈ ((V ⊔ X : Subgroup G) : Set G) := hg₂
      rw [hset] at hg₁' hg₂'
      obtain ⟨v₁, hv₁, x₁, hx₁, rfl⟩ := hg₁'
      obtain ⟨v₂, hv₂, x₂, hx₂, rfl⟩ := hg₂'
      have c1 : x₁ * (v₂ * x₂) = (v₂ * x₂) * x₁ :=
        hcen x₁ hx₁ _ (U.mul_mem (hVU hv₂) (hXU hx₂))
      have c2 : Commute x₂ v₁ := hcen x₂ hx₂ v₁ (hVU hv₁)
      have c3 : x₂ * v₁⁻¹ = v₁⁻¹ * x₂ := c2.inv_right
      have e : ⁅v₁ * x₁, v₂ * x₂⁆ = ⁅v₁, v₂⁆ := by
        simp only [commutatorElement_def]
        calc v₁ * x₁ * (v₂ * x₂) * (v₁ * x₁)⁻¹ * (v₂ * x₂)⁻¹
            = v₁ * (x₁ * (v₂ * x₂)) * x₁⁻¹ * v₁⁻¹ * (v₂ * x₂)⁻¹ := by group
          _ = v₁ * (v₂ * x₂) * v₁⁻¹ * (v₂ * x₂)⁻¹ := by rw [c1]; group
          _ = v₁ * v₂ * (x₂ * v₁⁻¹) * x₂⁻¹ * v₂⁻¹ := by group
          _ = v₁ * v₂ * v₁⁻¹ * v₂⁻¹ := by rw [c3]; group
      rw [e, commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hv₁ hv₂) (V.inv_mem hv₁)) (V.inv_mem hv₂)
    exact le_antisymm hVU (by rw [← h]; exact sup_le le_rfl hXV')

end InvariantSubgroups

end CFSG.AGLEmbedding
