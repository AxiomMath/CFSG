module

public import CFSG.LieType.Ree.ReeTorus
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] noncomputable def reeDerived : Subgroup (adjointGroup t.tag K) :=
  (commutator (reeFixed t K a)).map (reeFixed t K a).subtype

noncomputable abbrev reeTorusPart : Subgroup (reeFixed t K a) :=
  (nativeData t.tag K).H.comap (reeFixed t K a).subtype

noncomputable abbrev reeUnipPart : Subgroup (reeFixed t K a) :=
  (nativeData t.tag K).U.comap (reeFixed t K a).subtype

variable {t K a}

theorem commutator_mem_reeDerived {g h : adjointGroup t.tag K} (hg : g ∈ reeFixed t K a)
    (hh : h ∈ reeFixed t K a) : g * h * g⁻¹ * h⁻¹ ∈ reeDerived t K a := by
  have hc := Subgroup.commutator_mem_commutator (g₁ := (⟨g, hg⟩ : reeFixed t K a))
    (g₂ := ⟨h, hh⟩) (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [← commutator_def, commutatorElement_def] at hc
  refine ⟨_, hc, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

variable (t K a)

@[expose, instance_reducible] noncomputable def reeConjAction :
    MulDistribMulAction (reeTorusPart t K a) (reeUnipPart t K a) where
  smul h s := ⟨(h : reeFixed t K a) * s * (h : reeFixed t K a)⁻¹, by
    change ((h : adjointGroup t.tag K) * s * (h : adjointGroup t.tag K)⁻¹) ∈
      (nativeData t.tag K).U
    exact (Subgroup.mem_normalizer_iff.mp
      (RootGroupData.H_le_normalizer_U (D := nativeData t.tag K) h.2) _).mp s.2⟩
  one_smul s := Subtype.ext (by
    change (1 : reeFixed t K a) * s * (1 : reeFixed t K a)⁻¹ = s
    group)
  mul_smul h h' s := Subtype.ext (by
    change ((h : reeFixed t K a) * h') * s * ((h : reeFixed t K a) * h')⁻¹ =
      (h : reeFixed t K a) * ((h' : reeFixed t K a) * s * (h' : reeFixed t K a)⁻¹) *
        (h : reeFixed t K a)⁻¹
    group)
  smul_mul h s s' := Subtype.ext (by
    change (h : reeFixed t K a) * (s * s') * (h : reeFixed t K a)⁻¹ =
      ((h : reeFixed t K a) * s * (h : reeFixed t K a)⁻¹) *
        ((h : reeFixed t K a) * s' * (h : reeFixed t K a)⁻¹)
    group)
  smul_one h := Subtype.ext (by
    change (h : reeFixed t K a) * 1 * (h : reeFixed t K a)⁻¹ = 1
    group)

theorem reeFixed_U_le_derived (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ∀ x ∈ (nativeData t.tag K).U, x ∈ reeFixed t K a → x ∈ reeDerived t K a := by
  let _ := reeConjAction t K a
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  obtain ⟨u₀, hu₀⟩ := exists_orderOf_eq_card_sub_one (K := K)
  have hfix : CFSG.fixedPointSubgroup (reeTorusPart t K a) (reeUnipPart t K a) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have h1 : ((s : reeFixed t K a) : adjointGroup t.tag K) = 1 :=
      t.eq_one_of_mem_U_of_forall_reeTorus a ha hK hu₀ s.2 fun j hj => by
        have hT := t.reeTorus_mem_reeFixed a hK hj u₀
        have h2 := congrArg (fun z : reeUnipPart t K a =>
          ((z : reeFixed t K a) : adjointGroup t.tag K))
          (hs ⟨⟨_, hT⟩, t.reeTorus_mem_H a j u₀⟩)
        exact h2
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h1))
  have hSp : IsPGroup t.prime (reeUnipPart t K a) :=
    ((nativeRootSubgroups t.tag K).isPGroup_U t.prime).comap_of_injective _
      Subtype.val_injective
  have hsolv : Group.IsSolvable (reeUnipPart t K a) := by
    have := hSp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (reeTorusPart t K a)) (Nat.card (reeUnipPart t K a)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hSp
    rw [hn]
    refine Nat.Coprime.pow_right n ?_
    have hH := (nativeRootSubgroups t.tag K).coprime_card_H t.prime
    have hdvd : Nat.card (reeTorusPart t K a) ∣ Nat.card (nativeData t.tag K).H := by
      rw [← Subgroup.card_map_of_injective (f := (reeFixed t K a).subtype)
        Subtype.val_injective]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    exact Nat.Coprime.coprime_dvd_left hdvd hH
  have htop := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolv hcop
  rw [hfix, bot_sup_eq] at htop
  intro x hxU hxΓ
  set ι : reeUnipPart t K a →* adjointGroup t.tag K :=
    (reeFixed t K a).subtype.comp (reeUnipPart t K a).subtype
  have hle : CFSG.commutatorAction (A := reeTorusPart t K a) (G := reeUnipPart t K a) ≤
      (reeDerived t K a).comap ι := by
    rw [CFSG.commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨h, g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    convert commutator_mem_reeDerived (inv_mem (g : reeFixed t K a).2) (h : reeFixed t K a).2
      using 1
    rw [map_mul, map_inv, inv_inv]
    change (ι g)⁻¹ * (((h : reeFixed t K a) : adjointGroup t.tag K) *
      ((g : reeFixed t K a) : adjointGroup t.tag K) *
        ((h : reeFixed t K a) : adjointGroup t.tag K)⁻¹) = _
    simp only [mul_assoc]
    rfl
  exact hle (htop ▸ Subgroup.mem_top (⟨⟨x, hxΓ⟩, hxU⟩ : reeUnipPart t K a))

end CFSG.LieType.Ree
