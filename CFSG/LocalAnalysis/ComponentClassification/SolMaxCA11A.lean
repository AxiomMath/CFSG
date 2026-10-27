module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11L
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem exists_fixed_layer_seven {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    ∃ (L₀ F : Subgroup X) (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
      (DY : Finset (Fin 7)), L₀ ≤ J ∧
      L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X))) ∧
      F ≤ L₀ ∧ F ≤ J ∧ Nat.card F = 4 ∧ (∀ x ∈ F, x * x = 1) ∧
      (∃ DF : Finset (Fin 11), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) : Perm (Fin 11)) ω = ω) ∧
      DY.card = 4 ∧
      ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
        ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀J : e₀ ∈ J := S.le he₀E
  have h4 := S.card_support_coreImage_E he₀E he₀1
  obtain ⟨L₀, hL₀J, hL₀pc, hinv, -, χ₀, hχ₀⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 e (le_normalizer he₀J) he₀2
      he₀J (by rw [mul_inv_cancel]; exact one_mem _) (by rw [h4]; norm_num)
  have hL₀J' : L₀ ≤ J := hL₀J.trans inf_le_left
  have hL₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X) :=
    le_inf (hL₀J'.trans S.pair.1.2.1) (hL₀J.trans inf_le_right)
  obtain ⟨F, DF, hFJ, hF4, hFsq, hDF, hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hsuppD : (coreImage e he₀J).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨e₀, he₀J⟩ he₀E ω hωD)
  have hDFc : DF ⊆ (coreImage e he₀J).supportᶜ := by
    intro ω hω
    rw [Finset.mem_compl]
    intro h
    exact Finset.disjoint_left.mp hdisj (hsuppD h) hω
  have hFL₀ : F ≤ L₀ := by
    intro x hx
    have hxJ : x ∈ J := hFJ hx
    refine hinv x hxJ ?_ ⟨1, by rw [pow_one, sq]; exact hFsq x hx⟩ ?_
    · exact (mem_centralizer_iff.mp (hFE hx) e₀ he₀E).symm
    · intro ω hω
      refine hDFc ?_
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hFs ⟨x, hxJ⟩ hx ω hωF)
  have hβ : Fintype.card ↥((coreImage e he₀J).supportᶜ : Finset (Fin 11)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
  set π := Fintype.equivFinOfCardEq hβ with hπdef
  set χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7) := χ₀.trans π.altCongrHom
    with hχdef
  obtain ⟨κ, hκdef⟩ : ∃ κ : Fin 7 → Fin 11, ∀ i, κ i =
      ((π.symm i : ↥((coreImage e he₀J).supportᶜ : Finset (Fin 11))) : Fin 11) :=
    ⟨_, fun _ => rfl⟩
  have hκ : Function.Injective κ := by
    intro i j hij
    rw [hκdef, hκdef] at hij
    exact π.symm.injective (Subtype.ext hij)
  set DY₀ := Finset.univ.filter (fun i : Fin 7 => κ i ∈ DF) with hDY₀def
  have hDY₀ : DY₀.card ≤ 4 := by
    have h1 : DY₀.card ≤ DF.card := Finset.card_le_card_of_injOn κ
      (fun i hi => (Finset.mem_filter.mp hi).2) hκ.injOn
    rwa [hDF] at h1
  obtain ⟨DY, hDY₀Y, -, hDY4⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ DY₀) hDY₀
    (by rw [Finset.card_univ, Fintype.card_fin]; norm_num)
  refine ⟨L₀, F, χ, DY, hL₀J', hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, hFs⟩, hDY4, ?_⟩
  intro x hxF y hy
  have h1 : ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      π.permCongr ((χ₀ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup _) : Perm _) := rfl
  rw [h1]
  have hxJ : (x : X) ∈ J := hL₀J' x.2
  refine permCongr_apply_eq_of_ofSubtype π _ (hχ₀ x hxJ) ?_
  refine hFs ⟨x, hxJ⟩ hxF _ fun hω => hy (hDY₀Y ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hκdef]; exact hω⟩

theorem false_of_pump_held_seven
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (h13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hMult : TBLit.HeldTrivialMultiplier)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {L₀ N : Subgroup X} (hL₀J : L₀ ≤ J)
    (hL₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hL₀pc : IsPComponent 2
      (L₀.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 7))
    (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hfix : N.map (MulAut.conj t).toMonoidHom = N) (hL₀N : L₀ ≤ N)
    (hL₀Npc : IsPComponent 2 (L₀.subgroupOf (N ⊓ centralizer ({t} : Set X))))
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) : False := by
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have htc : t * e₀ = e₀ * t := (mem_centralizer_singleton_iff.mp (S.pair.1.2.1 he₀J)).symm
  exact He11.false_of_held_pump hPump hN1 h13 hML hSch hMult S.nonab S.kProper S.unbal S.notU
    S.pair e he₀J he₀o htc (le_normalizer he₀J) (by rw [mul_inv_cancel]; exact one_mem _)
    (S.card_support_coreImage_E he₀E he₀1) (le_inf hL₀J (hL₀C.trans inf_le_right)) hL₀pc
    ⟨χ⟩ hNC hNpc hfix hL₀N hL₀Npc ψ

end Sig36

end CFSG.ComponentClassification.SolMax
