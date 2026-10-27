module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightBlockOfTheta
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ConjAutPerm
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SylowEqS
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Reduction
public import CFSG.HardMathSupport.Cooperstein.Proving.TwoPrimeSup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.Proving
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

@[expose] def SymAutInner : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], 7 ≤ Fintype.card α →
    ∀ φ : Perm α ≃* Perm α, ∃ g : Perm α, ∀ x, φ x = g * x * g⁻¹

@[expose] def EightBlockDataX (S L : Subgroup G) (r s : ℕ) : Prop :=
  ∀ X : Subgroup G, Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    SymAutInner → EightBlockData X S L r s

theorem mem_normalizer_sup {x : G} (hL : x ∈ Subgroup.normalizer (L : Set G))
    (hS : x ∈ Subgroup.normalizer (S : Set G)) :
    x ∈ Subgroup.normalizer ((L ⊔ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hL hS ⊢
  rw [Subgroup.map_sup, hL, hS]


@[expose] def conjAutOfNormalizer {M : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (M : Set G)) :
    ↥M ≃* ↥M where
  toFun m := ⟨x * m * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx m).1 m.2⟩
  invFun m := ⟨x⁻¹ * m * x, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) (m : G)).1 m.2
    simpa using this⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAutOfNormalizer_apply {M : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (M : Set G))
    (m : ↥M) : ((conjAutOfNormalizer hx m : ↥M) : G) = x * m * x⁻¹ := rfl

theorem map_barM_normalizer_eq_eightN (hA : Asc81bHyp (L ⊔ S) S)
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) {r s : ℕ} (θ : ↥(L ⊔ S) →* Perm (OmegaE r s))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ = Wr r s)
    (φ : ↥(barM (L ⊔ S) L) ≃* AltE r s)
    (hφ : ∀ l : ↥L, ((φ (barMHomSub (le_sup_left : L ≤ L ⊔ S) l) : AltE r s) : Perm (OmegaE r s)) =
      θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩) :
    ((barM (L ⊔ S) (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM (L ⊔ S) L)).map
      φ.toMonoidHom = eightN r s := by
  classical
  have hLM' : L ≤ L ⊔ S := le_sup_left
  have hKS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S := fun m h => hpS ((hker m).1 h)
  have hnormθ : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.normalizer (S : Set G) →
      θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := fun m hm => by
    rw [← hW]; exact theta_mem_normalizer_W θ m hm
  have hnormS : ∀ m : ↥(L ⊔ S), θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) →
      (m : G) ∈ Subgroup.normalizer (S : Set G) := fun m hm =>
    mem_normalizer_of_theta_normalizes hA le_rfl le_sup_right θ hKS m (by rw [hW]; exact hm)
  rw [subgroupOf_barM_eq_map hLM' inf_le_right, Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlS : (l : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_subgroupOf.1 hl).1
    show ((φ (barMHomSub hLM' l) : AltE r s) : Perm (OmegaE r s)) ∈ pTildeEmb r s
    rw [hφ]
    exact mem_pTildeEmb_iff.2 ⟨hnormθ _ hlS, mem_alternatingGroup.2 (by
      have := (φ (barMHomSub hLM' l)).2
      rw [hφ] at this
      exact mem_alternatingGroup.1 this)⟩
  · intro hx
    have hx' : (x : Perm (OmegaE r s)) ∈ pTildeEmb r s := hx
    obtain ⟨hxN, -⟩ := mem_pTildeEmb_iff.1 hx'
    obtain ⟨l0, hl0⟩ := barMHomSub_surjective hLM' (φ.symm x)
    have hxeq : φ (barMHomSub hLM' l0) = x := by rw [hl0]; simp
    have hθl : θ ⟨l0, hLM' l0.2⟩ = x := by
      have := hφ l0
      rw [hxeq] at this
      exact this.symm
    refine ⟨l0, Subgroup.mem_subgroupOf.2 ⟨hnormS _ (by rw [hθl]; exact hxN), l0.2⟩, ?_⟩
    exact hxeq


theorem eightBlockData_of_theta_X {r s : ℕ}
    (hAut : ∀ φ : Perm (OmegaE r s) ≃* Perm (OmegaE r s), ∃ g : Perm (OmegaE r s),
      ∀ x, φ x = g * x * g⁻¹)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) (hr1 : 1 ≤ r)
    (θ : ↥(L ⊔ S) →* Perm (OmegaE r s))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup (OmegaE r s),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ = Wr r s) :
    EightBlockData X S L r s := by
  classical
  have hLM' : L ≤ L ⊔ S := le_sup_left
  have hLX : L ≤ X := hL.le
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hcore : L ⊓ pCoreOf 2 X = L ⊓ pCoreOf 2 (L ⊔ S) :=
    Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  obtain ⟨φ, hφ⟩ := exists_barMEquiv_alt hLs θ hker hAltL
  let E := barMEquiv hLX hLM' hcore
  have hE : ∀ l : ↥L, E (barMHomSub hLX l) = barMHomSub hLM' l := barMEquiv_apply hLX hLM' hcore
  have hKS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S := fun m h => hpS ((hker m).1 h)
  have hWR : Wr r s ≤ θ.range := by
    rw [← hW]
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hAltR : alternatingGroup (OmegaE r s) ≤ θ.range := fun x hx => by
    obtain ⟨l, hl⟩ := hAltL x hx
    exact ⟨⟨l, hLM' l.2⟩, hl⟩
  let i₀ : Fin r := ⟨0, hr1⟩
  have htW : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ Wr r s := by
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  have hθs : Function.Surjective θ := by
    have := eq_top_of_alt_odd hAltR (hWR htW) (sign_swap (by simp))
    intro p
    have hp : p ∈ θ.range := by rw [this]; trivial
    exact hp
  refine ⟨E.trans φ, ?_, ?_⟩
  · have h1 := barMEquiv_map_subgroupOf hLX hLM' hcore
      (K := Subgroup.normalizer (S : Set G) ⊓ L) inf_le_right
    have h2 := map_barM_normalizer_eq_eightN hA' hpS θ hker hW φ hφ
    show Subgroup.map (φ.toMonoidHom.comp E.toMonoidHom) _ = _
    rw [← Subgroup.map_map, h1]
    exact h2
  · intro y hy
    obtain ⟨x, hxN, rfl⟩ := (mem_barM _).1 hy
    have hxS : (x : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.1 hxN).1
    have hxL : (x : G) ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_inf.1 hxN).2
    have hxM : (x : G) ∈ Subgroup.normalizer ((L ⊔ S : Subgroup G) : Set G) :=
      mem_normalizer_sup hxL hxS
    let α := conjAutOfNormalizer hxM
    have hα : ∀ m, θ m = 1 → θ (α m) = 1 := by
      intro m hm
      rw [hker] at hm ⊢
      rw [conjAutOfNormalizer_apply]
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ S) hxM) (m : G)).1 hm
    obtain ⟨g, hg⟩ := exists_conj_of_autM hAut θ hθs α hα
    have hgW : ∀ w ∈ Wr r s, g * w * g⁻¹ ∈ Wr r s := by
      intro w hw
      rw [← hW] at hw ⊢
      obtain ⟨j, hj, rfl⟩ := hw
      refine ⟨α j, ?_, hg j⟩
      show α j ∈ (thompsonJ S).subgroupOf (L ⊔ S)
      rw [Subgroup.mem_subgroupOf, conjAutOfNormalizer_apply]
      have hJ := normalizer_le_normalizer_thompsonJ S hxS
      exact (Subgroup.mem_normalizer_iff.1 hJ (j : G)).1 (Subgroup.mem_subgroupOf.1 hj)
    have hmapeq : (Wr r s).map (MulAut.conj g).toMonoidHom = Wr r s := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact hgW w hw
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hgN : g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hmapeq
    obtain ⟨σ₁, h₁, σ₂, hσ⟩ := exists_sumCongr_of_mem_normalizer hgN
    refine ⟨σ₁, h₁, σ₂, ?_⟩
    intro l l' hll'
    obtain ⟨l0, rfl⟩ := barMHomSub_surjective hLX l
    obtain ⟨l0', rfl⟩ := barMHomSub_surjective hLX l'
    show ((φ (E (barMHomSub hLX l0')) : AltE r s) : Perm (OmegaE r s)) =
      Perm.sumCongr σ₁ σ₂ * ((φ (E (barMHomSub hLX l0)) : AltE r s) : Perm (OmegaE r s)) *
        (Perm.sumCongr σ₁ σ₂)⁻¹
    rw [hE, hE, hφ, hφ, ← hσ]
    have hα0 : θ ⟨l0', hLM' l0'.2⟩ = θ (α ⟨l0, hLM' l0.2⟩) := by
      have h1 : (QuotientGroup.mk (Subgroup.inclusion hLX l0') :
          ↥X ⧸ CFSG.pCore 2 ↥X) =
          QuotientGroup.mk (x * Subgroup.inclusion hLX l0 * x⁻¹) := by
        have := hll'
        rw [coe_barMHomSub, coe_barMHomSub] at this
        rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h2 : (Subgroup.inclusion hLX l0')⁻¹ * (x * Subgroup.inclusion hLX l0 * x⁻¹) ∈
          CFSG.pCore 2 ↥X := QuotientGroup.eq.1 h1
      have h3 : (((Subgroup.inclusion hLX l0')⁻¹ * (x * Subgroup.inclusion hLX l0 * x⁻¹) : ↥X) : G)
          ∈ pCoreOf 2 X := by
        refine ⟨(Subgroup.inclusion hLX l0')⁻¹ * (x * Subgroup.inclusion hLX l0 * x⁻¹), ?_, rfl⟩
        exact h2
      have hmemL : (((Subgroup.inclusion hLX l0')⁻¹ *
          (x * Subgroup.inclusion hLX l0 * x⁻¹) : ↥X) : G) ∈ L := by
        have h5 : (x : G) * (l0 : G) * (x : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.1 hxL (l0 : G)).1 l0.2
        simpa using L.mul_mem (L.inv_mem l0'.2) h5
      have h4 := hcore ▸ (Subgroup.mem_inf.2 ⟨hmemL, h3⟩ : _ ∈ L ⊓ pCoreOf 2 X)
      have h6 := (Subgroup.mem_inf.1 h4).2
      have h7 := (hker ((⟨l0', hLM' l0'.2⟩ : ↥(L ⊔ S))⁻¹ * α ⟨l0, hLM' l0.2⟩)).2 (by
        have e : ((((⟨l0', hLM' l0'.2⟩ : ↥(L ⊔ S))⁻¹ * α ⟨l0, hLM' l0.2⟩ : ↥(L ⊔ S))) : G) =
            ((Subgroup.inclusion hLX l0')⁻¹ * (x * Subgroup.inclusion hLX l0 * x⁻¹) : ↥X) := rfl
        rw [e]; exact h6)
      rw [map_mul, map_inv, inv_mul_eq_one] at h7
      exact h7
    rw [hα0, hg]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
