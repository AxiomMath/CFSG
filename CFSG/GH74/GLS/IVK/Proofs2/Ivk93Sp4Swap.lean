module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open scoped MatrixGroups

theorem psp4_two_comp_bound {J : Type} [Group J] [Finite J] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (φ : J ≃* StatedProj (StatedSp 2 F)) {x : J} (hx : orderOf x = 2) :
    ∃ e₁ e₂ : Subgroup J, ∀ X : Subgroup J, IsPCompIn 2 (centralizer ({x} : Set J)) X →
      X = e₁ ∨ X = e₂ := by
  classical
  have hy : orderOf (φ x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd hy
  set ψ : J ≃* StatedProj (StatedSp 2 F) := φ.trans (MulAut.conj g⁻¹) with hψ
  have hψx : ψ x = g⁻¹ * φ x * g := by simp [hψ]
  have hC : (centralizer ({x} : Set J)).map ψ.toMonoidHom = centralizer ({ψ x} : Set _) :=
    map_centralizer_singleton_equiv' ψ x
  have key : ∀ X : Subgroup J, IsPCompIn 2 (centralizer ({x} : Set J)) X →
      X.map ψ.toMonoidHom ≤ centralizer ({ψ x} : Set _) ∧
      IsPComponent 2 ((X.map ψ.toMonoidHom).subgroupOf (centralizer ({ψ x} : Set _))) := by
    intro X hX
    rw [← hC]
    exact ⟨Subgroup.map_mono hX.1, (isPComponent_subgroupOf_map_iff' ψ hX.1).mp hX.2⟩
  rcases hg with hg | hg
  · have hψx' : ψ x = CatFactsSp4.u1 F := hψx.trans hg
    refine ⟨(CatFactsSp4.E1 F).comap ψ.toMonoidHom, (CatFactsSp4.E2 F).comap ψ.toMonoidHom, ?_⟩
    intro X hX
    obtain ⟨hle, hcomp⟩ := key X hX
    rw [hψx'] at hle hcomp
    obtain ⟨hcases, -⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd hle hcomp
    rcases hcases with h' | h'
    · left
      rw [← h', Subgroup.comap_map_eq_self_of_injective ψ.injective]
    · right
      rw [← h', Subgroup.comap_map_eq_self_of_injective ψ.injective]
  · have hψx' : ψ x = CatFactsSp4.u2 F := hψx.trans hg
    refine ⟨(CatFactsSp4.Lsub F).comap ψ.toMonoidHom, (CatFactsSp4.Lsub F).comap ψ.toMonoidHom, ?_⟩
    intro X hX
    obtain ⟨hle, hcomp⟩ := key X hX
    rw [hψx'] at hle hcomp
    obtain ⟨h', -⟩ := CatFactsSp4.pComponent_centralizer_u2 hodd hle hcomp
    left
    rw [← h', Subgroup.comap_map_eq_self_of_injective ψ.injective]

theorem isPCompIn_two_of_le_Ez {J : Type} [Group J] [Finite J] {x : J} {E : Subgroup J}
    (hE : E ≤ IVK.Ez x) (hn : IVK.Ez x ≤ normalizer (E : Set J)) (hq : IsQuasisimple ↥E) :
    IsPCompIn 2 (centralizer ({x} : Set J)) E := by
  have hEC : E ≤ centralizer ({x} : Set J) := hE.trans (Ivk93Adapt.jm_Ez_le_centralizer x)
  refine ⟨hEC, LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent ⟨?_, ?_⟩⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEC).symm hq
  · have hN1 : ((IVK.Ez x).subgroupOf (centralizer ({x} : Set J))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Ivk93Adapt.jm_Ez_le_centralizer x)).mpr
        (Ivk93Adapt.jm_centralizer_le_normalizer_Ez x)
    have hle : E.subgroupOf (centralizer ({x} : Set J)) ≤
        (IVK.Ez x).subgroupOf (centralizer ({x} : Set J)) := fun g hg => hE hg
    refine Subgroup.IsSubnormal.step _ _ hle hN1.isSubnormal ?_
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hg' : (g : J) ∈ normalizer (E : Set J) := hn hg
    rw [Subgroup.mem_normalizer_iff] at hg'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hg' k

theorem psp4_swap {J : Type} [Group J] [Finite J] {q q₁ q₂ : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : IVK.IsPSp4 J q) {x : J} {L₁ L₂ : Subgroup J} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂)
    (P : Sylow 2 J) (hxP : x ∈ (P : Subgroup J)) (hxc : ∀ s ∈ (P : Subgroup J), s * x = x * s) :
    ∃ s ∈ (P : Subgroup J), L₁.map (MulAut.conj s).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj s).toMonoidHom = L₁ := by
  obtain ⟨t, w, E₁, E₂, htP, -, ht2, -, -, -, -, -, hEz, hE₂, hsl, hE₁E₂, hcom, -⟩ :=
    CFSG.GH74.GLS.Stage2.Final.ivk_4_10 J q hq h5 (Or.inl hK) P x hxP h.ord hxc
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  obtain ⟨F', hF', hFin', hF'q, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model hsl
  have hq₁ : IsQuasisimple ↥E₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (GHInv.isQuasisimple_sl2 (by omega))
  have hq₂ : IsQuasisimple ↥E₂ := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_ hq₁
    exact (E₁.equivMapOfInjective _ (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hE₂.symm)
  have hE₂C : E₂ ≤ centralizer (E₁ : Set J) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun k hk => hcom k hk g hg
  have hE₁C : E₁ ≤ centralizer (E₂ : Set J) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (hcom g hg k hk).symm
  have hn₁ : IVK.Ez x ≤ normalizer (E₁ : Set J) := by
    rw [hEz]
    exact sup_le Subgroup.le_normalizer (hE₂C.trans (Subgroup.centralizer_le_normalizer _))
  have hn₂ : IVK.Ez x ≤ normalizer (E₂ : Set J) := by
    rw [hEz]
    exact sup_le (hE₁C.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have c₁ : IsPCompIn 2 (centralizer ({x} : Set J)) E₁ :=
    isPCompIn_two_of_le_Ez (hEz ▸ le_sup_left) hn₁ hq₁
  have c₂ : IsPCompIn 2 (centralizer ({x} : Set J)) E₂ :=
    isPCompIn_two_of_le_Ez (hEz ▸ le_sup_right) hn₂ hq₂
  have hne : E₁ ≠ E₂ := by
    intro heq
    have h1 : Nat.card ↥(E₁ ⊓ E₂) = Nat.card ↥E₁ := by rw [← heq, inf_idem]
    rw [hE₁E₂, Nat.card_zpowers, h.ord, card_of_hasSL2Model hsl] at h1
    have := sl2_card_mono h5
    norm_num at this
    omega
  obtain ⟨F, hF, hFin, hFq, ⟨φ⟩⟩ := hK
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  obtain ⟨e₁, e₂, he⟩ := psp4_two_comp_bound hodd φ h.ord
  have hmatch : (L₁ = E₁ ∧ L₂ = E₂) ∨ (L₁ = E₂ ∧ L₂ = E₁) := by
    rcases he L₁ h.comp₁ with h1 | h1 <;> rcases he L₂ h.comp₂ with h2 | h2 <;>
      rcases he E₁ c₁ with h3 | h3 <;> rcases he E₂ c₂ with h4 | h4
    all_goals first
      | exact absurd (h1.trans h2.symm) h.ne
      | exact absurd (h3.trans h4.symm) hne
      | exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
      | exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
  have hcc : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id J := by
    ext a
    have h1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
    show t * (t * a * t⁻¹) * t⁻¹ = a
    rw [h1]
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by simp only [mul_assoc]
      _ = a := by rw [ht1]; simp
  have hc2 : E₂.map (MulAut.conj t).toMonoidHom = E₁ := by
    rw [hE₂, Subgroup.map_map, hcc, Subgroup.map_id]
  refine ⟨t, htP, ?_⟩
  rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1, h2, ← hE₂], by rw [h2, hc2, h1]⟩
  · exact ⟨by rw [h1, h2, hc2], by rw [h1, h2, ← hE₂]⟩

end CFSG.GH74.GLS.IVK.Proofs2
