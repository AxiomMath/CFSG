module

public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG

theorem map_oddCore_le_oddCore {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    (oddCore A).map e.toMonoidHom ≤ oddCore B := by
  have hn : ((oddCore A).map e.toMonoidHom).Normal :=
    (inferInstance : (oddCore A).Normal).map _ e.surjective
  have hodd : Odd (Nat.card ((oddCore A).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact odd_natCard_oddCore A
  exact le_sSup ⟨hn, hodd⟩

theorem oddCore_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (oddCore A).map e.toMonoidHom = oddCore B := by
  apply le_antisymm (map_oddCore_le_oddCore e)
  intro y hy
  have hx : e.symm y ∈ oddCore A := map_oddCore_le_oddCore e.symm ⟨y, hy, rfl⟩
  exact ⟨e.symm y, hx, by simp⟩

theorem oddCore_eq_subgroupOf {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hK : oddCore X ≤ K) : oddCore K = (oddCore X).subgroupOf K := by
  apply le_antisymm
  · have hchar : (oddCore K).Characteristic := by
      rw [oddCore_eq_pPrimeCore_two]
      infer_instance
    have hW : ((oddCore K).map K.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hodd : Odd (Nat.card ((oddCore K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact odd_natCard_oddCore K
    have hle : (oddCore K).map K.subtype ≤ oddCore X := le_sSup ⟨hW, hodd⟩
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  · have hn : ((oddCore X).subgroupOf K).Normal := Subgroup.normal_subgroupOf
    have hodd : Odd (Nat.card ((oddCore X).subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
      exact odd_natCard_oddCore X
    exact le_sSup ⟨hn, hodd⟩

theorem injective_domRestrict_of_odd_ker {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hker : Odd (Nat.card f.ker)) (P : Subgroup A) (hP : IsPGroup 2 P) :
    Function.Injective (f.domRestrict P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hcop : (Nat.card P).Coprime (Nat.card f.ker) := by
    rw [hm]
    exact (Nat.coprime_two_left.mpr hker).pow_left m
  have hdisj : Disjoint P f.ker := Subgroup.disjoint_of_coprime_natCard hcop
  have hxP : (x : A) ∈ P := x.2
  have hxN : (x : A) ∈ f.ker := hx
  have : (x : A) ∈ P ⊓ f.ker := ⟨hxP, hxN⟩
  rw [(disjoint_iff.mp hdisj)] at this
  exact Subtype.ext this

theorem nonempty_sylow_equiv_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) (T : Sylow 2 A)
    (U : Sylow 2 B) : Nonempty ((T : Subgroup A) ≃* (U : Subgroup B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(mulEquivMapOfInjective f T (injective_domRestrict_of_odd_ker f hker T T.isPGroup')).trans
    (Sylow.equiv (T.mapSurjective hf) U)⟩

theorem nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient {X : Type*} [Group X] [Finite X]
    (h : IsPGroup 2 (X ⧸ oddCore X)) (S : Sylow 2 X) :
    Nonempty ((X ⧸ oddCore X) ≃* (S : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (X ⧸ oddCore X)) := inferInstance
  have hTop : IsPGroup 2 (⊤ : Subgroup (X ⧸ oddCore X)) := h.of_equiv Subgroup.topEquiv.symm
  have hP : (⊤ : Subgroup (X ⧸ oddCore X)) = (P : Subgroup (X ⧸ oddCore X)) :=
    P.is_maximal' hTop le_top
  obtain ⟨f⟩ := sylow_oddCore_quotient_equiv S P
  exact ⟨((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hP)).trans f)⟩

end CFSG.ClassicalInvolution.QuaternionStructure
