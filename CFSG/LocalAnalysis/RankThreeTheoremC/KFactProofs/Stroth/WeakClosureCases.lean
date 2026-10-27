module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureReduction
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

@[expose] def WCOn (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ P : Sylow p K, IsMulCommutative (P : Subgroup K) → 2 ≤ CFSG.Open.pRank p (P : Subgroup K) →
    ∀ A : Subgroup K, A ≤ (P : Subgroup K) → Nat.card A = p →
      ∃ g : K, A.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup K) ∧
        A.map (MulAut.conj g).toMonoidHom ≠ A

@[expose] def WCAlt : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 → WCOn p (alternatingGroup (Fin n))

@[expose] def WCLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n ℓ f → CFSG.Blueprint.LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → p ≠ 2 → WCOn p K

@[expose] def WCSporadic : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Blueprint.NativeSporadic.SporadicRep K → ∀ p : ℕ, p.Prime → p ≠ 2 → WCOn p K

variable {K L : Type} [Group K] [Finite K] [Group L] [Finite L]

theorem WCOn.of_mulEquiv {p : ℕ} [Fact p.Prime] (e : K ≃* L) (h : WCOn p L) : WCOn p K := by
  intro P hPab hrank A hAP hA
  have hcardP : Nat.card (P.map e.toMonoidHom) = p ^ (Nat.card L).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, P.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  let P' : Sylow p L := Sylow.ofCard (P.map e.toMonoidHom) hcardP
  have hP' : (P' : Subgroup L) = (P : Subgroup K).map e.toMonoidHom := Sylow.coe_ofCard _ _
  have hP'ab : IsMulCommutative (P' : Subgroup L) := by
    rw [hP']
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    have hxy := congrArg Subtype.val (hPab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at hxy ⊢
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  have hrank' : 2 ≤ CFSG.Open.pRank p (P' : Subgroup L) := by
    rw [hP']
    exact hrank.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p
      Fact.out e.toMonoidHom e.injective _)
  have hA'P : A.map e.toMonoidHom ≤ (P' : Subgroup L) := by
    rw [hP']
    exact Subgroup.map_mono hAP
  have hA' : Nat.card (A.map e.toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  obtain ⟨g', hg'P, hg'A⟩ := h P' hP'ab hrank' _ hA'P hA'
  refine ⟨e.symm g', ?_, fun heq => hg'A ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : g' * e a * g'⁻¹ ∈ (P' : Subgroup L) :=
      hg'P ⟨e a, ⟨a, ha, rfl⟩, rfl⟩
    rw [hP'] at h1
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 h1
    have : (MulAut.conj (e.symm g')).toMonoidHom a = x := by
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply] at hxe ⊢
      exact hxe.symm
    rw [this]
    exact hx
  ·
    have key : ∀ a : K, e ((MulAut.conj (e.symm g')).toMonoidHom a) =
        (MulAut.conj g').toMonoidHom (e a) := by
      intro a
      simp [MulAut.conj_apply]
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have : (MulAut.conj (e.symm g')).toMonoidHom a ∈ A := heq ▸ ⟨a, ha, rfl⟩
      exact ⟨_, this, key a⟩
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ A.map (MulAut.conj (e.symm g')).toMonoidHom := heq.symm ▸ ha
      obtain ⟨b, hb, rfl⟩ := ha'
      exact ⟨e b, ⟨b, hb, rfl⟩, (key b).symm⟩

section Dispatch

theorem kFactWeakClosureInner_of_cases (hAlt : WCAlt) (hLie : WCLie) (hSpor : WCSporadic) :
    KFactWeakClosureInner := by
  intro p hp hp2 K _ _ hs hnab hcat
  have : Fact p.Prime := ⟨hp⟩
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact WCOn.of_mulEquiv e (hAlt n hn5 p hp hp2)
  · exact hLie K hs hnab t n ℓ f hadm hmodel p hp hp2
  · exact hSpor K hs hnab hspor p hp hp2

end Dispatch

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
