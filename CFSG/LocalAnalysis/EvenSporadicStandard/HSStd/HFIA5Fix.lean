module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvCent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HOv
  CFSG.EvenSporadicStandard.HSStd.HL34

theorem card_eq_mul_card_map' {Γ Q : Type*} [Group Γ] [Group Q] [Finite Γ] (π : Γ →* Q)
    (A : Subgroup Γ) : Nat.card A = Nat.card ↥(A ⊓ π.ker) * Nat.card ↥(A.map π) := by
  let f : ↥A →* Q := π.comp A.subtype
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ π.ker) :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card f.range = Nat.card ↥(A.map π) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_centralizer_le_two_mul (σ : Perm (Fin 5)) :
    Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5)))) ≤
      2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) := by
  have h := card_eq_mul_card_map' (Perm.sign : Perm (Fin 5) →* ℤˣ)
    (centralizer ({σ} : Set (Perm (Fin 5))))
  have hle : Nat.card ↥((centralizer ({σ} : Set (Perm (Fin 5)))).map Perm.sign) ≤ 2 := by
    refine (Subgroup.card_le_card_group _).trans ?_
    rw [Nat.card_eq_fintype_card]
    exact le_of_eq (by decide)
  calc Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))))
      = Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) *
        Nat.card ↥((centralizer ({σ} : Set (Perm (Fin 5)))).map Perm.sign) := h
    _ ≤ Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) * 2 :=
      Nat.mul_le_mul_left _ hle
    _ = 2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) :=
      mul_comm _ _

theorem fixed_card_of_involution (α : MulAut (alternatingGroup (Fin 5))) (h2 : α * α = 1) :
    (α = 1 ∧ Nat.card {a : alternatingGroup (Fin 5) // α a = a} = 60) ∨
      (4 ≤ Nat.card {a : alternatingGroup (Fin 5) // α a = a} ∧
        Nat.card {a : alternatingGroup (Fin 5) // α a = a} ∣ 24) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 α
  subst hσ
  have hσ2 : σ * σ = 1 := hbij.1 (by rw [map_mul, h2, map_one])
  by_cases hσ1 : σ = 1
  · left
    subst hσ1
    have hα : (MulAut.conjNormal (1 : Perm (Fin 5)) : MulAut (alternatingGroup (Fin 5))) = 1 :=
      map_one _
    refine ⟨hα, ?_⟩
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun a => by rw [hα]; rfl)]
    exact card_alternatingGroup_five
  · right
    obtain ⟨m, hm1, hm2, hcard, -⟩ := exists_card_centralizer_involution hσ2 hσ1
    have hFC : Nat.card {a : alternatingGroup (Fin 5) // MulAut.conjNormal σ a = a} =
        Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) := by
      refine Nat.card_congr
        { toFun := fun a => ⟨(a.1 : Perm (Fin 5)), ?_, a.1.2⟩
          invFun := fun c => ⟨⟨(c : Perm (Fin 5)), c.2.2⟩, ?_⟩
          left_inv := fun a => rfl
          right_inv := fun c => rfl }
      · have h1 : ((MulAut.conjNormal σ a.1 : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
            (a.1 : Perm (Fin 5)) := congrArg Subtype.val a.2
        rw [MulAut.conjNormal_apply] at h1
        show (a.1 : Perm (Fin 5)) ∈ centralizer ({σ} : Set (Perm (Fin 5)))
        rw [mem_centralizer_singleton_iff]
        calc (a.1 : Perm (Fin 5)) * σ = σ * (a.1 : Perm (Fin 5)) * σ⁻¹ * σ := by rw [h1]
          _ = σ * (a.1 : Perm (Fin 5)) := by group
      · have h1 : (c : Perm (Fin 5)) * σ = σ * c := mem_centralizer_singleton_iff.1 c.2.1
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        show σ * (c : Perm (Fin 5)) * σ⁻¹ = c
        rw [← h1]
        group
    have hdvd : Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) ∣
        Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5)))) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hle := card_centralizer_le_two_mul σ
    rw [hFC]
    generalize Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 5))) ⊓ alternatingGroup (Fin 5)) = n
      at hdvd hle ⊢
    rw [hcard] at hdvd hle
    have hm3 : m ≤ 2 := by omega
    interval_cases m
    · norm_num [Nat.factorial] at hdvd hle
      exact ⟨by omega, hdvd.trans (by norm_num)⟩
    · norm_num [Nat.factorial] at hdvd hle
      exact ⟨by omega, hdvd.trans (by norm_num)⟩

theorem fixed_card_cases (α : MulAut (alternatingGroup (Fin 5))) (h2 : α * α = 1) :
    4 ≤ Nat.card {a : alternatingGroup (Fin 5) // α a = a} ∧
      (Nat.card {a : alternatingGroup (Fin 5) // α a = a} = 60 ∨
        Nat.card {a : alternatingGroup (Fin 5) // α a = a} ∣ 24) := by
  rcases fixed_card_of_involution α h2 with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact ⟨by omega, Or.inl h⟩
  · exact ⟨h1, Or.inr h2⟩

theorem prod_eq_of_dvd (f₁ f₂ : ℕ) (h₁ : 4 ≤ f₁) (h₂ : 4 ≤ f₂) (h₁' : f₁ = 60 ∨ f₁ ∣ 24)
    (h₂' : f₂ = 60 ∨ f₂ ∣ 24) (h60 : 60 ≤ f₁ * f₂) (hd : f₁ * f₂ ∣ 240) : f₁ * f₂ = 240 := by
  rcases h₁' with rfl | h₁'
  · rcases h₂' with rfl | h₂'
    · norm_num at hd
    · have : f₂ ≤ 24 := Nat.le_of_dvd (by norm_num) h₂'
      interval_cases f₂ <;> omega
  · have : f₁ ≤ 24 := Nat.le_of_dvd (by norm_num) h₁'
    rcases h₂' with rfl | h₂'
    · interval_cases f₁ <;> omega
    · have : f₂ ≤ 24 := Nat.le_of_dvd (by norm_num) h₂'
      interval_cases f₁ <;> interval_cases f₂ <;> omega

theorem not_injective_perm_five_to_A5A5
    (ι : Perm (Fin 5) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    ¬ Function.Injective ι := by
  intro hι
  have key : ∀ f : Perm (Fin 5) →* alternatingGroup (Fin 5),
      alternatingGroup (Fin 5) ≤ f.ker := by
    intro f
    by_cases hker : f.ker = ⊥
    · exfalso
      have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
      have := Nat.card_le_card_of_injective f hinj
      rw [card_perm_five, card_alternatingGroup_five] at this
      omega
    · have hnt : Nontrivial f.ker := by
        rw [Subgroup.nontrivial_iff_ne_bot]
        exact hker
      exact Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  have h1 := key ((MonoidHom.fst _ _).comp ι)
  have h2 := key ((MonoidHom.snd _ _).comp ι)
  have hA : alternatingGroup (Fin 5) ≠ ⊥ := by
    intro h
    have := card_alternatingGroup_five
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  apply hg1
  have e1 : ((MonoidHom.fst _ _).comp ι) g = 1 := h1 hg
  have e2 : ((MonoidHom.snd _ _).comp ι) g = 1 := h2 hg
  have : ι g = ι 1 := by
    rw [map_one]
    exact Prod.ext e1 e2
  exact Subtype.ext (hι this)

end CFSG.EvenSporadicStandard.HSStd.HFI
