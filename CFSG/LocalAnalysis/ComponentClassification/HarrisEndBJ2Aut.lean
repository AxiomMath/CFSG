module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBJ2Cert
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42C
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsTransfer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms CFSG.ABGLocalTools

theorem map_conj_centralizerIn {M : Type*} [Group M] (H : Subgroup M) {g : M} (hg : g ∈ H)
    (x : M) :
    (centralizerIn H x).map (MulAut.conj g).toMonoidHom = centralizerIn H (g * x * g⁻¹) := by
  rw [centralizerIn, centralizerIn, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
    map_conj_centralizer]
  congr 1
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro y hy
    refine ⟨g⁻¹ * y * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hy) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem orderOf_conj' {M : Type*} [Group M] (c x : M) : orderOf (c * x * c⁻¹) = orderOf x :=
  MulEquiv.orderOf_eq (MulAut.conj c) x

theorem card_centralizerIn_conj {M : Type*} [Group M] (H : Subgroup M) {g : M} (hg : g ∈ H)
    (x : M) : Nat.card (centralizerIn H (g * x * g⁻¹)) = Nat.card (centralizerIn H x) := by
  rw [← map_conj_centralizerIn H hg x, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_centralizer_R (r : R) :
    Nat.card (centralizer ({r} : Set R)) =
      Nat.card (centralizerIn R (r : Equiv.Perm (Fin 315))) := by
  have h : (centralizer ({r} : Set R)).map R.subtype =
      centralizerIn R (r : Equiv.Perm (Fin 315)) := by
    ext g
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg')⟩
    · rintro ⟨hgR, hg⟩
      exact ⟨⟨g, hgR⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext hg), rfl⟩
  rw [← h, Subgroup.card_map_of_injective R.subtype_injective]

theorem index_innAut_P :
    (innAut P).index = 2 :=
  index_inner_P

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (centralizer ({e a} : Set B)) = Nat.card (centralizer ({a} : Set A)) := by
  have h : (centralizer ({a} : Set A)).map e.toMonoidHom = centralizer ({e a} : Set B) := by
    ext b
    constructor
    · rintro ⟨a', ha', rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at ha'
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, ha']
    · intro hb
      refine ⟨e.symm b, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff] at hb
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb]
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem rAutEquiv_of_mem (p : P) :
    rAutEquiv ⟨p, P_le_R p.2⟩ = MulAut.conj p := by
  ext q
  rw [rAutEquiv_apply, rConj_apply, MulAut.conj_apply]
  rfl

theorem card_centralizer_outer
    {α : MulAut P} (h2 : orderOf α = 2) (hα : α ∉ innAut P) :
    Nat.card (centralizer ({α} : Set (MulAut P))) = 672 := by
  set r := rAutEquiv.symm α with hr
  have hrα : rAutEquiv r = α := MulEquiv.apply_symm_apply _ _
  have hr2 : orderOf (r : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, hr, MulEquiv.orderOf_eq, h2]
  have hrP : (r : Equiv.Perm (Fin 315)) ∉ P := by
    intro h
    apply hα
    have hr_eq : r = ⟨((⟨(r : Equiv.Perm (Fin 315)), h⟩ : P) : Equiv.Perm (Fin 315)),
        P_le_R h⟩ := rfl
    rw [← hrα, hr_eq, rAutEquiv_of_mem]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc, hrc⟩ := outer_classes.1 r ((mem_P_or_coset r.2).resolve_left hrP) hr2
  rw [← hrα, card_centralizer_mulEquiv, card_centralizer_R, hrc,
    card_centralizerIn_conj R (P_le_R hc), centralizerIn_R_permU.2.1]

theorem not_seven_dvd_centralizer_conj
    {x : P} (h2 : orderOf x = 2) :
    ¬ 7 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut P))) := by
  rw [← rAutEquiv_of_mem, card_centralizer_mulEquiv, card_centralizer_R]
  have h2' : orderOf (x : Equiv.Perm (Fin 315)) = 2 := by rw [Subgroup.orderOf_coe, h2]
  obtain ⟨r, hr, c, hc, hxc⟩ := inner_classes.1 x x.2 h2'
  change ¬ 7 ∣ Nat.card (centralizerIn R (x : Equiv.Perm (Fin 315)))
  rw [hxc, card_centralizerIn_conj R (P_le_R hc)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [centralizerIn_R_permA.2.1]
    norm_num
  · rw [centralizerIn_R_permTwoA.2.1]
    norm_num

theorem map_conj_closure_pair {M : Type*} [Group M] (c x y : M) :
    (closure {x, y}).map (MulAut.conj c).toMonoidHom = closure {c * x * c⁻¹, c * y * c⁻¹} := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem exists_perfect_conj
    {c : Equiv.Perm (Fin 315)} (hc : c ∈ P) :
    ∃ G : Subgroup (Equiv.Perm (Fin 315)), G ≤ centralizerIn P (c * permA * c⁻¹) ∧
      Nat.card G = 60 ∧ ⁅G, G⁆ = G := by
  obtain ⟨G, hG, hG60, hGp⟩ := exists_perfect_sixty
  refine ⟨G.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← map_conj_centralizerIn P hc]
    exact map_mono hG
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hG60]
  · rw [← Subgroup.map_commutator, hGp]

theorem inv_cases {x : Equiv.Perm (Fin 315)} (hx : x ∈ P)
    (h2 : orderOf x = 2) :
    (∃ c ∈ P, x = c * permA * c⁻¹ ∧ Models.fixCount x = 15) ∨
      ∃ c ∈ P, x = c * permTwoA * c⁻¹ ∧ Models.fixCount x = 11 := by
  obtain ⟨r, hr, c, hc, hxc⟩ := inner_classes.1 x hx h2
  obtain ⟨hf1, hf2, -⟩ := fixed_points_reps
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine Or.inl ⟨c, hc, hxc, ?_⟩
    rw [hxc, Models.fixCount_conj, Models.fixCount, ← Nat.card_eq_fintype_card, hf1]
  · refine Or.inr ⟨c, hc, hxc, ?_⟩
    rw [hxc, Models.fixCount_conj, Models.fixCount, ← Nat.card_eq_fintype_card, hf2]

theorem sylow_centralizer_facts
    {S' : Subgroup (Equiv.Perm (Fin 315))} (hS'P : S' ≤ P)
    (hS' : Nat.card S' = 128) :
    ∃ ζ ∈ S', ζ ≠ 1 ∧ (∀ s ∈ S', ζ * s = s * ζ) ∧
      (∀ r ∈ R, (∀ s ∈ S', r * s = s * r) → r = 1 ∨ r = ζ) ∧
      ∃ o₁ o₂ : Equiv.Perm (Fin 315), o₁ ∈ centralizerIn P ζ ∧ o₂ ∈ centralizerIn P ζ ∧
        Odd (orderOf o₁) ∧ Odd (orderOf o₂) ∧ closure {o₁, o₂} = centralizerIn P ζ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀c, hz₀, hcard⟩ := exists_s0
  have hfact : (Nat.card P).factorization 2 = 7 := by
    rw [card_P, show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hsyl₀ : IsSylowOf 2 S₀ P := isSylowOf_of_card
    (hS₀.trans inf_le_left) (by rw [hS₀c, hfact]; norm_num)
  have hsyl' : IsSylowOf 2 S' P := isSylowOf_of_card hS'P (by rw [hS', hfact]; norm_num)
  obtain ⟨c, hc, hcS⟩ := hsyl₀.exists_mem_conj hsyl'
  have hS'eq : S' = S₀.map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [hcS x]
    constructor
    · intro h
      exact ⟨c⁻¹ * x * c, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
  have hz1 : permTwoA ≠ 1 := by
    intro h
    have := orderOf_permTwoA
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  refine ⟨c * permTwoA * c⁻¹, ?_, ?_, ?_, fun r hr hrc => ?_, ?_⟩
  · rw [hS'eq]
    exact ⟨permTwoA, hz₀, rfl⟩
  · intro h
    apply hz1
    calc permTwoA = c⁻¹ * (c * permTwoA * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · intro s hs
    rw [hS'eq] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := (mem_centralizerIn.mp (hS₀ hs₀)).2
    calc c * permTwoA * c⁻¹ * (c * s₀ * c⁻¹) = c * (permTwoA * s₀) * c⁻¹ := by group
      _ = c * (s₀ * permTwoA) * c⁻¹ := by rw [← h]
      _ = c * s₀ * c⁻¹ * (c * permTwoA * c⁻¹) := by group
  ·
    set r' := c⁻¹ * r * c with hr'
    have hr'R : r' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem (P_le_R hc)) hr) (P_le_R hc)
    have hr'c : ∀ s ∈ S₀, r' * s = s * r' := by
      intro s hs
      have h1 := hrc (c * s * c⁻¹) (by rw [hS'eq]; exact ⟨s, hs, rfl⟩)
      calc r' * s = c⁻¹ * (r * (c * s * c⁻¹)) * c := by rw [hr']; group
        _ = c⁻¹ * ((c * s * c⁻¹) * r) * c := by rw [h1]
        _ = s * r' := by rw [hr']; group
    have hmem : ∀ g ∈ R, (∀ s ∈ S₀, g * s = s * g) →
        g ∈ centralizerIn R permTwoA ⊓ centralizer (S₀ : Set (Equiv.Perm (Fin 315))) := by
      intro g hg hgc
      exact mem_inf.mpr ⟨mem_centralizerIn.mpr ⟨hg, hgc _ hz₀⟩,
        mem_centralizer_iff.mpr fun s hs => (hgc s hs).symm⟩
    have hz₀c : ∀ s ∈ S₀, permTwoA * s = s * permTwoA := fun s hs =>
      ((mem_centralizerIn.mp (hS₀ hs)).2).symm
    by_cases h1 : r' = 1
    · left
      calc r = c * r' * c⁻¹ := by rw [hr']; group
        _ = 1 := by rw [h1]; group
    · right
      have heq := eq_of_card_eq_two hcard (hmem r' hr'R hr'c)
        (hmem permTwoA (P_le_R permTwoA_mem) hz₀c) h1 hz1
      calc r = c * r' * c⁻¹ := by rw [hr']; group
        _ = c * permTwoA * c⁻¹ := by rw [heq]
  · obtain ⟨o₁, o₂, h1, h2, o1, o2, hcl⟩ := exists_odd_gens_c2A
    have hmap := map_conj_centralizerIn P hc permTwoA
    refine ⟨c * o₁ * c⁻¹, c * o₂ * c⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hmap]
      exact ⟨o₁, h1, rfl⟩
    · rw [← hmap]
      exact ⟨o₂, h2, rfl⟩
    · rw [orderOf_conj', o1]
      decide
    · rw [orderOf_conj', o2]
      decide
    · rw [← map_conj_closure_pair, hcl, hmap]

end CFSG.ComponentClassification.HarrisLit.EndB
