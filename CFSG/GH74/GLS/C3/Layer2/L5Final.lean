module

public import CFSG.GH74.GLS.C3.Layer2.Final
public import CFSG.GH74.GLS.C3.Layer2.L5Local
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.G5Iota
public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.GH74.GLS

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5

@[expose] def S_Prop46 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K T Q S : Subgroup G) (a : G),
    IsAConfig 5 x K T Q S a → SameInvolutionFusionPattern G (alternatingGroup (Fin 9))

theorem sameCentralizer_of_hom {G Gs : Type} [Group G] [Group Gs] [Finite G] [Finite Gs]
    {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (φ : ↥S →* Gs) (hinj : Function.Injective φ)
    (hsyl : IsSylowOf 2 φ.range ⊤) (x v : G) (x' v' : Gs)
    (hcl : ∀ u : ↥S, orderOf u = 2 → IsConj (u : G) x ∨ IsConj (u : G) v)
    (hcl' : ∀ u : ↥φ.range, orderOf u = 2 → IsConj (u : Gs) x' ∨ IsConj (u : Gs) v')
    (hφ : ∀ u : ↥S, orderOf u = 2 → (IsConj (u : G) x ↔ IsConj (φ u) x'))
    (Cx : Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({x'} : Set Gs))))
    (Cv : Nonempty (↥(centralizer ({v} : Set G)) ≃* ↥(centralizer ({v'} : Set Gs)))) :
    SameCentralizerOfInvolutionPattern G Gs := by
  obtain ⟨Q, hQ⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hS
  obtain ⟨Q', hQ'⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hsyl
  let e : ↥(Q : Subgroup G) ≃* ↥(Q' : Subgroup Gs) :=
    (MulEquiv.subgroupCongr hQ).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hQ'.symm))
  refine sameCentralizerOfInvolutionPattern_of_classes Q Q' e x v x' v' ?_ ?_ ?_ Cx Cv
  · intro u hu
    exact hcl (MulEquiv.subgroupCongr hQ u) (by rw [MulEquiv.orderOf_eq]; exact hu)
  · intro u hu
    exact hcl' (MulEquiv.subgroupCongr hQ' u) (by rw [MulEquiv.orderOf_eq]; exact hu)
  · intro u hu
    exact hφ (MulEquiv.subgroupCongr hQ u) (by rw [MulEquiv.orderOf_eq]; exact hu)

theorem fgrp5_equiv_centralizer :
    Nonempty (↥(Fgrp 5) ≃* ↥(Subgroup.centralizer ({xstarA 5} :
      Set (alternatingGroup (Fin (5 + 4)))))) :=
  ⟨(MonoidHom.ofInjective (embA_injective 5)).trans
    (MulEquiv.subgroupCongr (range_embA_eq 5 (by norm_num)))⟩

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem approxTo_of_config_five
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig 5 x K T Q S a)
    (hfus : SameInvolutionFusionPattern G (alternatingGroup (Fin 9))) :
    IsApproxTo G (alternatingGroup (Fin 9)) := by
  have hn : (5 : ℕ) = 5 ∨ (5 : ℕ) = 6 ∨ (5 : ℕ) = 7 := Or.inl rfl
  obtain ⟨ι₀, hι₀1, hι₀Q⟩ := exists_coord hn hG4 h
  obtain ⟨ι, hι1, hιQ, hιT⟩ := exists_equiv_T5 h ι₀ hι₀1 hι₀Q
  have hC480 : Nat.card ↥(centralizer ({x} : Set G)) = 480 := by
    rw [Coord.card_cent_x ι]
    decide
  have hT32 : Nat.card T = 32 := by
    have := h.sylowT.card_eq
    rw [hC480, Nat.factorization_def _ Nat.prime_two] at this
    rw [this]
    decide +kernel
  obtain ⟨ψ, hψ⟩ := exists_psi5 h hT32 hfus
  have hQX := hQX_five hG4 h hψ
  obtain ⟨b, hb, hbψ⟩ := exists_adm h hQX ι hι1 hιQ hιT hψ
  let L : Loc5 h := ⟨_, _, hT32, ι, hι1, hιQ, hιT, ψ, hψ, b, hb, hbψ⟩
  obtain ⟨v', hv'o, hv'n, Cv⟩ := L.exists_equiv_centralizer_v5 hZD
  let Ψ : ↥S →* alternatingGroup (Fin 9) :=
    ψ.codRestrict (alternatingGroup (Fin 9)) (fun s => S0_le_alt (hψ.mem s))
  have hΨinj : Function.Injective Ψ := fun u w huw => hψ.inj (congrArg Subtype.val huw)
  have hΨrange : Ψ.range = S0A := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact hψ.mem s
    · intro hz
      obtain ⟨s, hs⟩ := hψ.surj (z : Perm (Fin 9)) (mem_S0A.1 hz)
      exact ⟨s, Subtype.ext hs⟩
  have hΨsyl : IsSylowOf 2 Ψ.range ⊤ := by
    rw [hΨrange]
    exact isSylowOf_S0A
  let x' : alternatingGroup (Fin 9) := xstarA 5
  have hx'o : orderOf x' = 2 := orderOf_xstarA 5
  have hx'n : numMoved (x' : Perm (Fin 9)) = 4 := numMoved_xstarA 5
  have hxS : x ∈ S := L.hxS
  have hnx : numMoved (ψ ⟨x, hxS⟩) = 4 := by
    rw [hψ.x_eq]
    exact nmE_f1
  have hnv : numMoved (ψ ⟨x * (a * x * a⁻¹), L.hvS⟩) = 8 := by
    rw [hψ.v_eq]
    exact numMoved_yS
  have hxord : orderOf (⟨x, hxS⟩ : ↥S) = 2 :=
    L4.orderOf_eq_two_of_mul_self _ (L4.x_mul_self h) h.x_ne_one
  have hvord : orderOf (⟨x * (a * x * a⁻¹), L.hvS⟩ : ↥S) = 2 :=
    L4.orderOf_eq_two_of_mul_self _ (L4.v_mul_self h) (L4.v_ne_one h)
  have hcl : ∀ u : ↥S, orderOf u = 2 → IsConj (u : G) x ∨ IsConj (u : G) (x * (a * x * a⁻¹)) := by
    intro u hu
    rcases hψ.nm_four_or_eight hu with h4 | h8
    · exact Or.inl ((hψ.conj u ⟨x, hxS⟩ hu hxord).2 (h4.trans hnx.symm))
    · exact Or.inr ((hψ.conj u ⟨x * (a * x * a⁻¹), L.hvS⟩ hu hvord).2 (h8.trans hnv.symm))
  have hΨord : ∀ u : ↥S, orderOf u = 2 → orderOf (Ψ u) = 2 := fun u hu => by
    rw [orderOf_injective Ψ hΨinj u]
    exact hu
  have hφ : ∀ u : ↥S, orderOf u = 2 → (IsConj (u : G) x ↔ IsConj (Ψ u) x') := by
    intro u hu
    constructor
    · intro hc
      have h4 : numMoved (ψ u) = 4 := ((hψ.conj u ⟨x, hxS⟩ hu hxord).1 hc).trans hnx
      exact isConj_alternating_of_numMoved_eq 9 _ _ (hΨord u hu) hx'o (by
        show numMoved (ψ u) = numMoved (x' : Perm (Fin 9))
        rw [h4, hx'n])
    · intro hc
      have h4 : numMoved (ψ u) = 4 := by
        have := numMoved_eq_of_isConj_alternating 9 hc
        rw [hx'n] at this
        exact this
      exact (hψ.conj u ⟨x, hxS⟩ hu hxord).2 (h4.trans hnx.symm)
  have hcl' : ∀ u : ↥Ψ.range, orderOf u = 2 →
      IsConj (u : alternatingGroup (Fin 9)) x' ∨ IsConj (u : alternatingGroup (Fin 9)) v' := by
    intro u hu
    have hu2 : orderOf (u : alternatingGroup (Fin 9)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hu
    rcases numMoved_eq_of_involution_alternating 9 (by norm_num) _ hu2 with h4 | h8
    · exact Or.inl (isConj_alternating_of_numMoved_eq 9 _ _ hu2 hx'o (by rw [h4, hx'n]))
    · exact Or.inr (isConj_alternating_of_numMoved_eq 9 _ _ hu2 hv'o (by rw [h8, hv'n]))
  obtain ⟨e⟩ := fgrp5_equiv_centralizer
  have Cx : Nonempty (↥(centralizer ({x} : Set G)) ≃*
      ↥(centralizer ({x'} : Set (alternatingGroup (Fin 9))))) := ⟨ι.trans e⟩
  refine ⟨sameCentralizer_of_hom h.sylowS Ψ hΨinj hΨsyl x (x * (a * x * a⁻¹)) x' v' hcl hcl' hφ
    Cx Cv, ?_⟩
  rintro (h7 | h11)
  · exfalso
    obtain ⟨e₁⟩ := h7
    have h1 := Nat.card_congr e₁.toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h1
    revert h1
    decide
  · exfalso
    obtain ⟨e₁⟩ := h11
    have h1 := Nat.card_congr e₁.toEquiv
    have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
      CFSG.Semidihedral.GL2Recognition.card_nativeM11
    rw [hc, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    revert h1
    decide

theorem b_L2_five_of
    (h46 : S_Prop46) : B_L2_five := by
  intro G _ _ hG hconf
  obtain ⟨x, K, T, Q, S, a, h⟩ := hconf
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four ▸ le_rfl
  exact approxTo_of_config_five CFSG.GH74.Uniqueness.S_ZD_unconditional hG4 h
    (h46 G hG x K T Q S a h)

end CFSG.GH74.GLS
