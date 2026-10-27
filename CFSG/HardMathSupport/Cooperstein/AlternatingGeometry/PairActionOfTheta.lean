module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNode

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open
open CFSG.HardMathSupport.Cooperstein.Proving
open scoped commutatorElement

variable {G : Type} [Group G] {S L : Subgroup G}

theorem pairActionData_of_theta (hLM : IsTwoPrimeComponent (L ⊔ S) L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hpS : pCoreOf 2 (L ⊔ S) ≤ S) (n : ℕ)
    (θ : ↥(L ⊔ S) →* Perm (Fin n × Bool))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup (Fin n × Bool),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hSθ : ∀ x : Perm (Fin n × Bool), (∃ s : ↥(L ⊔ S), (s : G) ∈ S ∧ θ s = x) ↔
      x ∈ blockFix (Fin n) ∧ x ∈ θ.range) :
    PairActionData (L ⊔ S) S L n := by
  classical
  have hLM' : L ≤ L ⊔ S := le_sup_left
  let χ : ↥L →* ℤˣ := (sign : Perm (Fin n × Bool) →* ℤˣ).comp (θ.comp (Subgroup.inclusion hLM'))
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
  let ψ : ↥L →* AltB (Fin n) :=
    (θ.comp (Subgroup.inclusion hLM')).codRestrict (alternatingGroup (Fin n × Bool))
      fun l => mem_alternatingGroup.2 (hsign l)
  have hψval : ∀ l : ↥L, ((ψ l : AltB (Fin n)) : Perm (Fin n × Bool)) = θ ⟨l, hLM' l.2⟩ :=
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
  let e2 : (↥L ⧸ ψ.ker) ≃* AltB (Fin n) := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  let φ : ↥(barM (L ⊔ S) L) ≃* AltB (Fin n) :=
    e1.symm.trans ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans e2)
  have hφ : ∀ l : ↥L, φ (barMHomSub hLM' l) = ψ l := by
    intro l
    have h1 : e1.symm (barMHomSub hLM' l) = QuotientGroup.mk l := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show e2 (QuotientGroup.quotientMulEquivOfEq hψk.symm (e1.symm (barMHomSub hLM' l))) = ψ l
    rw [h1]
    rfl
  have hKS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S := fun m h => hpS ((hker m).1 h)
  have hKθ : ∀ a b : ↥(L ⊔ S),
      (QuotientGroup.mk a : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) = QuotientGroup.mk b → θ a = θ b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ CFSG.pCore 2 ↥(L ⊔ S) := QuotientGroup.eq.1 hab
    have h2 : ((a⁻¹ * b : ↥(L ⊔ S)) : G) ∈ pCoreOf 2 (L ⊔ S) := by
      refine ⟨a⁻¹ * b, ?_, rfl⟩
      exact h1
    have h3 := (hker _).2 h2
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3
  have hmk : ∀ l : ↥L, (barMHomSub hLM' l : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) =
      QuotientGroup.mk ⟨l, hLM' l.2⟩ := fun l => coe_barMHomSub hLM' l
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [subgroupOf_barM_eq_map hLM' inf_le_right, Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp (barMHomSub hLM') = ψ := by
      exact MonoidHom.ext fun l => hφ l
    rw [hcomp]
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlS : (l : G) ∈ S := (Subgroup.mem_subgroupOf.1 hl).1
      have := ((hSθ _).1 ⟨⟨l, hLM' l.2⟩, hlS, rfl⟩).1
      exact mem_EA.2 (by rw [hψval]; exact this)
    · intro hx
      have hxF : (x : Perm (Fin n × Bool)) ∈ blockFix (Fin n) := mem_EA.1 hx
      obtain ⟨l, hl⟩ := hAltL x.1 x.2
      have hrange : (x : Perm (Fin n × Bool)) ∈ θ.range := ⟨⟨l, hLM' l.2⟩, hl⟩
      obtain ⟨s, hsS, hs⟩ := (hSθ _).2 ⟨hxF, hrange⟩
      have h1 : θ (s⁻¹ * ⟨l, hLM' l.2⟩) = 1 := by rw [map_mul, map_inv, hs, hl, inv_mul_cancel]
      have h2 := hKS _ h1
      have hlS : (l : G) ∈ S := by
        have : (l : G) = (s : G) * ((s⁻¹ * ⟨l, hLM' l.2⟩ : ↥(L ⊔ S)) : G) := by
          simp
        rw [this]
        exact S.mul_mem hsS h2
      exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨hlS, l.2⟩, Subtype.ext (by rw [hψval]; exact hl)⟩
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    obtain ⟨s, hsS, rfl⟩ := (mem_barM _).1 hy
    have hsN : ∀ m : G, m ∈ L ↔ (s : G) * m * (s : G)⁻¹ ∈ L := fun m =>
      Subgroup.mem_normalizer_iff.1 (hSL hsS) m
    intro z
    constructor
    · intro hz
      obtain ⟨m, hmL, rfl⟩ := (mem_barM _).1 hz
      refine (mem_barM _).2 ⟨s * m * s⁻¹, (hsN _).1 hmL, ?_⟩
      rfl
    · intro hz
      obtain ⟨m, hmL, hm⟩ := (mem_barM _).1 hz
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
      refine (mem_barM _).2 ⟨s⁻¹ * m * s, (hsN _).2 ?_, ?_⟩
      · simpa [mul_assoc] using hmL
      · show QuotientGroup.mk (s⁻¹ * m * s) = (QuotientGroup.mk t : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S))
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm]
        group
  · intro y hy
    obtain ⟨s, hsS, rfl⟩ := (mem_barM _).1 hy
    refine ⟨θ s, ((hSθ _).1 ⟨s, hsS, rfl⟩).1, ?_⟩
    intro l l' hll'
    obtain ⟨l0, rfl⟩ := barMHomSub_surjective hLM' l
    obtain ⟨l0', rfl⟩ := barMHomSub_surjective hLM' l'
    rw [hφ, hφ]
    have h1 : (QuotientGroup.mk (⟨l0', hLM' l0'.2⟩ : ↥(L ⊔ S)) : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) =
        QuotientGroup.mk (s * ⟨l0, hLM' l0.2⟩ * s⁻¹) := by
      rw [← hmk, hll', hmk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 := hKθ _ _ h1
    show ((ψ l0' : AltB (Fin n)) : Perm (Fin n × Bool)) =
      θ s * ((ψ l0 : AltB (Fin n)) : Perm (Fin n × Bool)) * (θ s)⁻¹
    rw [hψval, hψval, h2, map_mul, map_mul, map_inv]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
