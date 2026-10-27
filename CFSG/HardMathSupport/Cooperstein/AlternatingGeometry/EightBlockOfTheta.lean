module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ModelTwoAF
public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.Proving
open scoped commutatorElement

variable {G : Type} [Group G] {S L : Subgroup G}

theorem mem_pTildeEmb_iff {r s : ℕ} {x : Perm (OmegaE r s)} :
    x ∈ pTildeEmb r s ↔
      x ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) ∧ x ∈ alternatingGroup (OmegaE r s) := by
  rw [mem_normalizer_Wr_iff, mem_alternatingGroup]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p.1, hp.1, p.2, rfl⟩, ?_⟩
    rw [Perm.sumCongrHom_apply, sign_sumCongr]
    exact hp.2
  · rintro ⟨⟨σ₁, h₁, σ₂, rfl⟩, h⟩
    rw [sign_sumCongr] at h
    exact ⟨(σ₁, σ₂), ⟨h₁, h⟩, rfl⟩

theorem exists_barMEquiv_alt (hLM : IsTwoPrimeComponent (L ⊔ S) L) {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup Ω,
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x) :
    ∃ φ : ↥(barM (L ⊔ S) L) ≃* ↥(alternatingGroup Ω),
      ∀ l : ↥L, ((φ (barMHomSub (le_sup_left : L ≤ L ⊔ S) l) : ↥(alternatingGroup Ω)) : Perm Ω) =
        θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ := by
  classical
  have hLM' : L ≤ L ⊔ S := le_sup_left
  let χ : ↥L →* ℤˣ := (sign : Perm Ω →* ℤˣ).comp (θ.comp (Subgroup.inclusion hLM'))
  have hsign : ∀ l : ↥L, χ l = 1 := by
    have hcomm : ⁅L, L⁆ ≤ χ.ker.map L.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆, MonoidHom.mem_ker.2 ?_, rfl⟩
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
    intro l
    have hl : (l : G) ∈ χ.ker.map L.subtype := hcomm (by rw [hLM.perfect]; exact l.2)
    obtain ⟨k, hk, hkl⟩ := hl
    have : k = l := Subtype.ext hkl
    subst this
    exact hk
  let ψ : ↥L →* ↥(alternatingGroup Ω) :=
    (θ.comp (Subgroup.inclusion hLM')).codRestrict (alternatingGroup Ω)
      fun l => mem_alternatingGroup.2 (hsign l)
  have hψval : ∀ l : ↥L, ((ψ l : ↥(alternatingGroup Ω)) : Perm Ω) = θ ⟨l, hLM' l.2⟩ :=
    fun l => rfl
  have hψs : Function.Surjective ψ := by
    intro x
    obtain ⟨l, hl⟩ := hAltL x.1 x.2
    exact ⟨l, Subtype.ext (by rw [hψval]; exact hl)⟩
  have hψk : ψ.ker = (barMHomSub hLM').ker := by
    rw [ker_barMHomSub]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (ψ l = 1) ↔ (l : G) ∈ pCoreOf 2 (L ⊔ S)
    rw [← hker ⟨l, hLM' l.2⟩]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rwa [hψval] at this
    · intro h
      exact Subtype.ext (by rw [hψval]; exact h)
  let e1 : (↥L ⧸ (barMHomSub hLM').ker) ≃* ↥(barM (L ⊔ S) L) :=
    QuotientGroup.quotientKerEquivOfSurjective (barMHomSub hLM') (barMHomSub_surjective hLM')
  let e2 : (↥L ⧸ ψ.ker) ≃* ↥(alternatingGroup Ω) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  let φ : ↥(barM (L ⊔ S) L) ≃* ↥(alternatingGroup Ω) :=
    e1.symm.trans ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans e2)
  refine ⟨φ, fun l => ?_⟩
  have h1 : e1.symm (barMHomSub hLM' l) = QuotientGroup.mk l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have : φ (barMHomSub hLM' l) = ψ l := by
    show e2 (QuotientGroup.quotientMulEquivOfEq hψk.symm (e1.symm (barMHomSub hLM' l))) = ψ l
    rw [h1]
    rfl
  rw [this, hψval]

theorem theta_eq_of_mk_eq {Ω : Type*} (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S)) (a b : ↥(L ⊔ S))
    (hab : (QuotientGroup.mk a : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) = QuotientGroup.mk b) :
    θ a = θ b := by
  have h1 : a⁻¹ * b ∈ CFSG.pCore 2 ↥(L ⊔ S) := QuotientGroup.eq.1 hab
  have h2 : ((a⁻¹ * b : ↥(L ⊔ S)) : G) ∈ pCoreOf 2 (L ⊔ S) := by
    refine ⟨a⁻¹ * b, ?_, rfl⟩
    exact h1
  have h3 := (hker _).2 h2
  rw [map_mul, map_inv, inv_mul_eq_one] at h3
  exact h3

variable [Finite G]

theorem eightBlockData_of_theta (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hpS : pCoreOf 2 (L ⊔ S) ≤ S) (r s : ℕ)
    (θ : ↥(L ⊔ S) →* Perm (OmegaE r s))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup (OmegaE r s),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ = Wr r s) :
    EightBlockData (L ⊔ S) S L r s := by
  classical
  have hLM' : L ≤ L ⊔ S := le_sup_left
  obtain ⟨φ, hφ⟩ := exists_barMEquiv_alt hLM θ hker hAltL
  have hKS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S := fun m h => hpS ((hker m).1 h)
  have hnormθ : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.normalizer (S : Set G) →
      θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := fun m hm => by
    rw [← hW]; exact theta_mem_normalizer_W θ m hm
  have hnormS : ∀ m : ↥(L ⊔ S), θ m ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) →
      (m : G) ∈ Subgroup.normalizer (S : Set G) := fun m hm =>
    mem_normalizer_of_theta_normalizes hA le_rfl le_sup_right θ hKS m (by rw [hW]; exact hm)
  have hmk : ∀ l : ↥L, (barMHomSub hLM' l : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) =
      QuotientGroup.mk ⟨l, hLM' l.2⟩ := fun l => coe_barMHomSub hLM' l
  refine ⟨φ, ?_, ?_⟩
  · rw [subgroupOf_barM_eq_map hLM' inf_le_right, Subgroup.map_map]
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
  · intro y hy
    obtain ⟨s', hsN, rfl⟩ := (mem_barM _).1 hy
    obtain ⟨σ₁, h₁, σ₂, hσ⟩ := exists_sumCongr_of_mem_normalizer (hnormθ s' hsN.1)
    refine ⟨σ₁, h₁, σ₂, ?_⟩
    intro l l' hll'
    obtain ⟨l0, rfl⟩ := barMHomSub_surjective hLM' l
    obtain ⟨l0', rfl⟩ := barMHomSub_surjective hLM' l'
    rw [hφ, hφ]
    have h1 : (QuotientGroup.mk (⟨l0', hLM' l0'.2⟩ : ↥(L ⊔ S)) :
        ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) =
        QuotientGroup.mk (s' * ⟨l0, hLM' l0.2⟩ * s'⁻¹) := by
      rw [← hmk, hll', hmk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 := theta_eq_of_mk_eq θ hker _ _ h1
    rw [h2, map_mul, map_mul, map_inv, hσ]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
