module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HeisLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveSound

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding.MaxD2
open scoped commutatorElement

@[expose] def HeisLocalEq (p : ℕ) {X : Type*} [Group X] (R : Subgroup X) : Prop :=
  Nat.card R = p ^ 3 ∧
  Subgroup.centralizer (R : Set X) ≤ R ∧
  Nat.card (R ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) = p ∧
  ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set X) ∧
  (∀ r ∈ R, r ^ p = 1) ∧
  Group.IsSolvable (Subgroup.normalizer (R : Set X)) ∧
  ∃ t, t ∈ Subgroup.normalizer (R : Set X) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set X),
      t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set X),
      t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup X,
      R ⊓ Subgroup.centralizer (R : Set X) ≤ F → F ≤ R → F.relIndex R = p →
        t ^ k ∉ Subgroup.normalizer (F : Set X)

section Transport

variable {X Y : Type*} [Group X] [Group Y] {p : ℕ}

theorem HeisLocalEq.map [Finite X] {R : Subgroup X} (e : X ≃* Y) (h : HeisLocalEq p R) :
    HeisLocalEq p (R.map e.toMonoidHom) := by
  obtain ⟨hcard, hcent, hZ, hcomm, hexp, hsolv, t, htN, m, lam, k, hm, hlam, hk, hpow, hinv,
    hline⟩ := h
  have hnorm : Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (R : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R e).symm
  have hZmap : (R.map e.toMonoidHom ⊓ Subgroup.centralizer ((R.map e.toMonoidHom : Subgroup Y) :
      Set Y)) = (R ⊓ Subgroup.centralizer (R : Set X)).map e.toMonoidHom := by
    rw [map_centralizer_equiv, Subgroup.map_inf _ _ _ e.injective]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, e t, ?_, m, lam, k, hm, hlam, hk, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · intro g hg
    rw [map_centralizer_equiv] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨x, hcent hx, rfl⟩
  · rw [hZmap, Subgroup.card_map_of_injective e.injective, hZ]
  · rw [hZmap, ← Subgroup.map_commutator, hcomm]
  · rintro _ ⟨r, hr, rfl⟩
    simpa using congrArg e (hexp r hr)
  · rw [hnorm]
    have := hsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ e.toMonoidHom
      e.injective).toMonoidHom) (Subgroup.equivMapOfInjective _ e.toMonoidHom
      e.injective).surjective
  · rw [hnorm]
    exact ⟨t, htN, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨z, hz, hzr⟩ := hpow r hr
    refine ⟨e z, ?_, by simpa using congrArg e hzr⟩
    rw [hZmap]
    exact ⟨z, hz, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨z, hz, hzr⟩ := hinv r hr
    refine ⟨e z, ?_, by simpa using congrArg e hzr⟩
    rw [hZmap]
    exact ⟨z, hz, rfl⟩
  · intro j hj0 hjm F hZF hFR hidx hn
    rw [hZmap] at hZF
    have hZle : R ⊓ Subgroup.centralizer (R : Set X) ≤ F.comap e.toMonoidHom := by
      intro x hx
      exact hZF ⟨x, hx, rfl⟩
    have hle : F.comap e.toMonoidHom ≤ R := by
      intro x hx
      obtain ⟨r, hr, hrx⟩ := hFR hx
      have : r = x := e.injective hrx
      exact this ▸ hr
    have hidx' : (F.comap e.toMonoidHom).relIndex R = p := by
      rw [Subgroup.relIndex_comap]
      exact hidx
    refine hline j hj0 hjm _ hZle hle hidx' ?_
    refine Subgroup.mem_normalizer_fintype fun n hn' => ?_
    have hen : e n ∈ F := hn'
    show e (t ^ j * n * (t ^ j)⁻¹) ∈ F
    rw [map_mul, map_mul, map_inv, map_pow]
    exact (Subgroup.mem_normalizer_iff.1 hn (e n)).1 hen

end Transport

section SubgroupOf

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ}

theorem heisLocalEq_of_heisDataEq {G R : Subgroup Q} {m lam e : ℕ}
    (h : HeisDataEq p m lam e G R) (hm : 2 ≤ m) (hlam : orderOf (lam : ZMod p) = p - 1)
    (he : 6 ∣ e) : HeisLocalEq p (R.subgroupOf G) := by
  obtain ⟨hRG, hcard, hcent, hZ, hcomm, hexp, hsolv, t, htN, hpow, hinv, hline⟩ := h
  have hnorm : Subgroup.normalizer ((R.subgroupOf G : Subgroup G) : Set G) =
      (Subgroup.normalizer (R : Set Q)).subgroupOf G :=
    (Subgroup.subgroupOf_normalizer_eq hRG).symm
  have hcen := subgroupOf_centralizer_eq hRG
  have hZG : R ⊓ Subgroup.centralizer (R : Set Q) ≤ G := inf_le_left.trans hRG
  have hZsub : R.subgroupOf G ⊓ Subgroup.centralizer ((R.subgroupOf G : Subgroup G) : Set G) =
      (R ⊓ Subgroup.centralizer (R : Set Q)).subgroupOf G := by
    rw [hcen]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨t, htN.2⟩, ?_, m, lam, e, hm, hlam, he, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hcard]
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    refine hcent g g.2 fun r hr => ?_
    have := Subgroup.mem_centralizer_iff.1 hg ⟨r, hRG hr⟩ (Subgroup.mem_subgroupOf.2 hr)
    exact (congrArg Subtype.val this).symm
  · rw [hZsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZG).toEquiv, hZ]
  · rw [hZsub]
    refine Subgroup.map_injective G.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRG, hcomm,
      Subgroup.map_subgroupOf_eq_of_le hZG]
  · intro x hx
    have hx' : (x : Q) ∈ R := Subgroup.mem_subgroupOf.1 hx
    exact Subtype.ext (by simpa using hexp x hx')
  · rw [hnorm, ← Subgroup.inf_subgroupOf_right]
    have := hsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.normalizer (R : Set Q) ⊓ G ≤ G)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.normalizer (R : Set Q) ⊓ G ≤ G)).symm.surjective
  · rw [hnorm]
    exact Subgroup.mem_subgroupOf.2 htN.1
  · intro x hx
    have hx' : (x : Q) ∈ R := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨z, hz, hzx⟩ := hpow x hx'
    refine ⟨⟨z, hZG hz⟩, ?_, Subtype.ext (by simpa using hzx)⟩
    rw [hZsub]
    exact Subgroup.mem_subgroupOf.2 hz
  · intro x hx
    have hx' : (x : Q) ∈ R := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨z, hz, hzx⟩ := hinv x hx'
    refine ⟨⟨z, hZG hz⟩, ?_, Subtype.ext (by simpa using hzx)⟩
    rw [hZsub]
    exact Subgroup.mem_subgroupOf.2 hz
  · intro j hj0 hjm F hZF hFR hidx hn
    rw [hZsub] at hZF
    have hZle : R ⊓ Subgroup.centralizer (R : Set Q) ≤ F.map G.subtype := by
      intro x hx
      exact ⟨⟨x, hZG hx⟩, hZF (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hle : F.map G.subtype ≤ R := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hFR hy)
    have hidx' : (F.map G.subtype).relIndex R = p := by
      rw [← hidx, ← Subgroup.relIndex_map_map_of_injective F (R.subgroupOf G)
        G.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRG]
    refine hline j hj0 hjm _ hZle hle hidx' ?_
    refine Subgroup.mem_normalizer_fintype fun n hn' => ?_
    obtain ⟨y, hy, rfl⟩ := hn'
    refine ⟨_, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, ?_⟩
    simp

end SubgroupOf

section Sylow

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}

theorem heisLocalEq_sylow [Fact p.Prime] (e : X ≃* Y) {R₀ : Subgroup Y} (h : HeisLocalEq p R₀)
    (hsyl : Nat.card R₀ = p ^ (Nat.card Y).factorization p) (R : Sylow p X) :
    HeisLocalEq p (R : Subgroup X) := by
  have h1 := HeisLocalEq.map e.symm h
  have hcard : Nat.card (R₀.map e.symm.toMonoidHom) = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hsyl, Nat.card_congr e.toEquiv]
  let R₁ : Sylow p X := Sylow.ofCard (R₀.map e.symm.toMonoidHom) hcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R₁ R
  have hRc : (R : Subgroup X) = (R₀.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  rw [hRc]
  exact HeisLocalEq.map (MulAut.conj c) h1

end Sylow

end CFSG.AGLEmbeddingD2
