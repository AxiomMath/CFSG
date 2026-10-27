module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Cited

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L246C127

theorem exists_conj_of_isSylowTwoOf' {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem isSylowTwoOf_top_map_subgroupOf {N X : Type} [Group N] [Group X] {Lb Q : Subgroup N}
    (e : Lb ≃* X) (hQ : IsSylowTwoOf Q Lb) :
    IsSylowTwoOf ((Q.subgroupOf Lb).map e.toMonoidHom) ⊤ := by
  have hQ2 : IsPGroup 2 (Q.subgroupOf Lb) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  refine ⟨le_top, hQ2.map e.toMonoidHom, ?_⟩
  have h1 : ((Q.subgroupOf Lb).map e.toMonoidHom).relIndex ⊤ =
      ((Q.subgroupOf Lb).map e.toMonoidHom).index := Subgroup.relIndex_top_right _
  have h2 : ((Q.subgroupOf Lb).map e.toMonoidHom).index = (Q.subgroupOf Lb).index :=
    Subgroup.index_map_equiv _ e
  change ¬ 2 ∣ ((Q.subgroupOf Lb).map e.toMonoidHom).relIndex ⊤
  rw [h1, h2]
  exact hQ.2.2

theorem core_abstract {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {D : Subgroup X}
    (hD : IsSylowTwoOf D ⊤) (hover : ∀ Y : Subgroup X, D ≤ Y → Y = ⊤ ∨ CharTwo Y)
    {T K : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hK : Good2 ↥K) (hKtop : K ≠ ⊤)
    (hsub : IsSubnormal K (K ⊔ T)) : False := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT hD
  set e : X →* X := (MulAut.conj g).toMonoidHom with he
  have hinj : Function.Injective e := (MulAut.conj g).injective
  set K' := K.map e with hK'
  have hsub' : IsSubnormal K' (K' ⊔ D) := by
    have := A3.subnormal_map e hsub
    rwa [Subgroup.map_sup, hg] at this
  have hgood : Good2 ↥K' := hK.of_mulEquiv (Subgroup.equivMapOfInjective K e hinj)
  have hK'nt : K' ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K').1 hgood.nontrivial
  have hK'top : K' ≠ ⊤ := by
    intro h
    apply hKtop
    refine Subgroup.eq_top_of_card_eq K ?_
    have h1 : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective hinj
    rw [← h1, h, Subgroup.card_top]
  rcases hover (K' ⊔ D) le_sup_right with hH | hH
  · rw [hH] at hsub'
    have hs : IsSimpleGroup ↥(⊤ : Subgroup X) :=
      (MulEquiv.isSimpleGroup_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)).2 hX
    rcases eq_bot_or_eq_of_isSubnormal hs hsub' with h | h
    · exact hK'nt h
    · exact hK'top h
  · exact hK'nt (eq_bot_of_isSubnormal_of_charTwo hH hsub' hgood.noTwoNormal hgood.noTwoQuot)

theorem altEven_of_data {m n : ℕ} (hm5 : 5 ≤ m) (hn : n = 3 ∨ n = 5)
    (hcard : Nat.card (alternatingGroup (Fin n)) ≠ Nat.card (alternatingGroup (Fin m)))
    {D : Subgroup ↥(alternatingGroup (Fin m))} (hD : IsSylowTwoOf D ⊤)
    (hover : ∀ Y : Subgroup ↥(alternatingGroup (Fin m)), D ≤ Y → Y = ⊤ ∨ CharTwo Y)
    {Γ : Type} [Group Γ] [Finite Γ] {L K T : Subgroup Γ} (ψ : ↥L ≃* alternatingGroup (Fin m))
    (hKL : K ≤ L) (φ : ↥K ≃* alternatingGroup (Fin n)) (hT : IsSylowTwoOf T L)
    (hsub : IsSubnormal K (K ⊔ T)) : False := by
  have hTL : T ≤ L := hT.1
  have hsub1 : IsSubnormal (K.subgroupOf L) (K.subgroupOf L ⊔ T.subgroupOf L) := by
    have h1 := A3.subnormal_comap L.subtype hsub
    have e : (K ⊔ T).comap L.subtype = K.subgroupOf L ⊔ T.subgroupOf L :=
      (Subgroup.comap_sup_eq_of_le_range L.subtype (by rw [Subgroup.range_subtype]; exact hKL)
        (by rw [Subgroup.range_subtype]; exact hTL)).symm
    rw [e] at h1
    exact h1
  have hsub2 : IsSubnormal ((K.subgroupOf L).map ψ.toMonoidHom)
      ((K.subgroupOf L).map ψ.toMonoidHom ⊔ (T.subgroupOf L).map ψ.toMonoidHom) := by
    have := A3.subnormal_map ψ.toMonoidHom hsub1
    rwa [Subgroup.map_sup] at this
  have hT2 := isSylowTwoOf_top_map_subgroupOf ψ hT
  have eK : ↥((K.subgroupOf L).map ψ.toMonoidHom) ≃* alternatingGroup (Fin n) :=
    ((Subgroup.equivMapOfInjective (K.subgroupOf L) ψ.toMonoidHom ψ.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKL)).trans φ
  have hgood : Good2 ↥((K.subgroupOf L).map ψ.toMonoidHom) := (good2_alt hn).of_mulEquiv eK.symm
  have hKtop : (K.subgroupOf L).map ψ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hcard
    rw [← Nat.card_congr eK.toEquiv, h, Subgroup.card_top]
  exact core_abstract (Bridge.alt_isSimple hm5) hD hover hT2 hgood hKtop hsub2

theorem card_alt_ne {n m : ℕ} (hn : n = 3 ∨ n = 5) (hm : m = 6 ∨ m = 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ Nat.card (alternatingGroup (Fin m)) := by
  rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;>
    (rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
      card_alternatingGroup, Fintype.card_fin, Fintype.card_fin]
     decide)

theorem altEvenExcluded :
    AltEvenExcluded := by
  intro Γ _ _ L K T m n hm hn ⟨ψ⟩ hKL ⟨φ⟩ hT hsub
  have hc := card_alt_ne hn hm
  rcases hm with rfl | rfl
  · exact altEven_of_data (by norm_num) hn hc Even6.isSylow_D Even6.overgroups ψ hKL φ hT hsub
  · exact altEven_of_data (by norm_num) hn hc Even8.isSylow_D Even8.overgroups ψ hKL φ hT hsub

end L246C127

end CFSG.QuasithinUnique
