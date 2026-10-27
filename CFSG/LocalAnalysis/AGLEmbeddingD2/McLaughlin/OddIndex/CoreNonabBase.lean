module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreNonabKills
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreAction
public import CFSG.LocalAnalysis.LargeEvenClassification.MinimalNormalFactors

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open SemidirectProduct CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.LargeEvenClassification.Helpers

section Gen

variable {Y I : Type} [Group Y] [Group I] {ρ : Y →* MulAut I}

theorem mem_of_comm_conj {a₀ : Y} {J : Subgroup I} (hJ : ActInv ρ J)
    (hC : ∀ x : I, ρ a₀ x = x → x ∈ J) {x₀ : I} {c : I ⋊[ρ] Y}
    (hc : c ∈ conjClass (inr : Y →* I ⋊[ρ] Y).range (inr a₀))
    (hxc : (inl x₀ : I ⋊[ρ] Y) * c = c * inl x₀) : x₀ ∈ J := by
  obtain ⟨_, ⟨y, rfl⟩, hcy⟩ := hc
  have key : ∀ (ε : Y) (hε : ε = a₀ ∨ ε = a₀⁻¹), c = inr (y * ε * y⁻¹) →
      x₀ ∈ J := by
    intro ε hε hcz
    rw [hcz] at hxc
    have h1 : (inl (ρ (y * ε * y⁻¹) x₀) : I ⋊[ρ] Y) = inl x₀ := by
      rw [inl_aut]
      calc inr (y * ε * y⁻¹) * inl x₀ * inr (y * ε * y⁻¹)⁻¹
          = (inl x₀ * inr (y * ε * y⁻¹)) * inr (y * ε * y⁻¹)⁻¹ := by rw [← hxc]
        _ = inl x₀ := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have h2 : ρ (y * ε * y⁻¹) x₀ = x₀ := inl_injective h1
    have hw : ρ ε (ρ y⁻¹ x₀) = ρ y⁻¹ x₀ := by
      have e : ρ ε (ρ y⁻¹ x₀) = ρ y⁻¹ (ρ (y * ε * y⁻¹) x₀) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      rw [e, h2]
    have hw' : ρ a₀ (ρ y⁻¹ x₀) = ρ y⁻¹ x₀ := by
      rcases hε with rfl | rfl
      · exact hw
      · have : ρ a₀⁻¹ (ρ y⁻¹ x₀) = ρ y⁻¹ x₀ := hw
        calc ρ a₀ (ρ y⁻¹ x₀) = ρ a₀ (ρ a₀⁻¹ (ρ y⁻¹ x₀)) := by rw [this]
          _ = ρ y⁻¹ x₀ := ρ_apply_inv ρ a₀ _
    have hmem : ρ y⁻¹ x₀ ∈ J := hC _ hw'
    have := hJ y _ hmem
    rwa [ρ_apply_inv] at this
  rcases hcy with h | h
  · exact key a₀ (Or.inl rfl) (by rw [h]; simp [map_mul, map_inv])
  · exact key a₀⁻¹ (Or.inr rfl) (by rw [h]; simp [map_mul, map_inv])

end Gen

section Socle

variable {Y I : Type} [Group Y] [Group I] [Finite I] {ρ : Y →* MulAut I}

theorem center_eq_bot_of_min (hnonab : ∃ x y : I, x * y ≠ y * x)
    (hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤) :
    Subgroup.center I = ⊥ := by
  have hinv : ActInv ρ (Subgroup.center I) := by
    intro y x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have h := hx (ρ y⁻¹ g)
    have := congrArg (ρ y) h
    rw [map_mul, map_mul, ρ_apply_inv] at this
    exact this
  rcases hmin _ inferInstance hinv with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnonab
    have : x ∈ Subgroup.center I := by rw [h]; trivial
    exact hxy (Subgroup.mem_center_iff.1 this y).symm

theorem socle_eq_top_of_min (hnonab : ∃ x y : I, x * y ≠ y * x)
    (hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤) :
    finiteSocle I = ⊤ := by
  have hinv : ActInv ρ (finiteSocle I) := by
    intro y x hx
    have := (Subgroup.characteristic_iff_map_le.1
      (inferInstance : (finiteSocle I).Characteristic)) (ρ y)
    exact this ⟨x, hx, rfl⟩
  rcases hmin _ inferInstance hinv with h | h
  · exfalso
    have hnt : (⊤ : Subgroup I) ≠ ⊥ := by
      obtain ⟨x, y, hxy⟩ := hnonab
      intro h
      apply hxy
      have hx : x = 1 := Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top x)
      rw [hx]; simp
    obtain ⟨M, -, hM⟩ := finite_minimal_normal_inside (⊤ : Subgroup I) inferInstance hnt
    have := minimal_normal_le_socle M hM
    rw [h] at this
    exact hM.prop.2 (le_bot_iff.1 this)
  · exact h

end Socle

section Cat

theorem isCatalogGroup_of_simple_subgroup {I : Type} [Group I] (hK : CFSG.Open.IsKGroup I)
    (S : Subgroup I) [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Open.IsCatalogGroup S := by
  have hbot : (⊥ : Subgroup I).subgroupOf S = ⊥ := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  let e : (↥S ⧸ (⊥ : Subgroup I).subgroupOf S) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hN : ((⊥ : Subgroup I).subgroupOf S).Normal := by rw [hbot]; infer_instance
  have hs : IsSimpleGroup (↥S ⧸ (⊥ : Subgroup I).subgroupOf S) := e.isSimpleGroup
  have hn : ∃ a b : ↥S ⧸ (⊥ : Subgroup I).subgroupOf S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨f⟩⟩ := @hK S ⊥ bot_le hN hs hn
  exact ⟨i, ⟨e.symm.trans f⟩⟩

end Cat

section Base

variable {Y I : Type} [Group Y] [Finite Y] [Group I] [Finite I]

theorem nonab_base (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable)
    (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) {a₀ : Y}
    (ha : orderOf a₀ = 3) (hK : CFSG.Open.IsKGroup I) (h3 : ¬ 3 ∣ Nat.card I)
    (ρ : Y →* MulAut I) (hnonab : ∃ x y : I, x * y ≠ y * x)
    (hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤)
    (J : Subgroup I) (hJ : ActInv ρ J) (hC : ∀ x : I, ρ a₀ x = x → x ∈ J) : J = ⊤ := by
  have hcenter := center_eq_bot_of_min hnonab hmin
  have hsocle := socle_eq_top_of_min hnonab hmin
  haveI : Finite (I ⋊[ρ] Y) := Finite.of_equiv (I × Y) equivProd.symm
  have hsimple : ∀ S : Subgroup I, minimalNormalEligible S → IsSimpleGroup ↥S := fun S hS =>
    socle_top_minimal_normal_simple hsocle S hS
  have hnonabS : ∀ S : Subgroup I, minimalNormalEligible S → ∃ x y : ↥S, x * y ≠ y * x :=
    fun S hS => socle_top_centerless_minimal_nonabelian hsocle hcenter S hS
  have hcomm : ∀ S : Subgroup I, minimalNormalEligible S → ∀ S' : Subgroup I,
      minimalNormalEligible S' → S ≠ S' → ∀ x ∈ S, ∀ y ∈ S', x * y = y * x := by
    intro S hS S' hS' hne x hx y hy
    have : S.Normal := hS.prop.1
    have : S'.Normal := hS'.prop.1
    exact (Subgroup.commute_of_normal_of_disjoint S S' hS.prop.1 hS'.prop.1
      (distinct_minimal_normals_disjoint S S' hS hS' hne) x y hx hy).eq
  have hauto : ∀ S : Subgroup I, minimalNormalEligible S → ∀ y : Y,
      minimalNormalEligible (S.map (ρ y).toMonoidHom) := fun S hS y =>
    minimal_normal_map_mulAut S hS (ρ y)
  have htrans : ∀ S : Subgroup I, minimalNormalEligible S → ∀ S' : Subgroup I,
      minimalNormalEligible S' → ∃ y : Y, S.map (ρ y).toMonoidHom = S' := by
    intro S hS S' hS'
    by_contra hno
    push Not at hno
    set T : Subgroup I := ⨆ y : Y, S.map (ρ y).toMonoidHom with hT
    haveI : ∀ y : Y, (S.map (ρ y).toMonoidHom).Normal := fun y => (hauto S hS y).prop.1
    have hTn : T.Normal := Subgroup.iSup_normal _
    have hTinv : ActInv ρ T := by
      intro z x hx
      have : T.map (ρ z).toMonoidHom ≤ T := by
        rw [hT, Subgroup.map_iSup]
        refine iSup_le fun y => ?_
        rw [Subgroup.map_map]
        refine le_trans (le_of_eq ?_) (le_iSup _ (z * y))
        congr 1
        ext n
        simp [map_mul, MulAut.mul_apply]
      exact this ⟨x, hx, rfl⟩
    have hTne : T ≠ ⊥ := by
      intro h
      have h1 : S ≤ T := by
        refine le_trans (le_of_eq ?_) (le_iSup _ (1 : Y))
        ext n
        simp
      exact hS.prop.2 (le_bot_iff.1 (h ▸ h1))
    have hTtop : T = ⊤ := (hmin T hTn hTinv).resolve_left hTne
    have hcent : T ≤ Subgroup.centralizer (S' : Set I) := by
      refine iSup_le fun y => ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hcomm S' hS' _ (hauto S hS y) (fun e => hno y e.symm) g hg _ ⟨x, hx, rfl⟩
    rw [hTtop] at hcent
    have : S' ≤ Subgroup.center I := by
      intro g hg
      rw [Subgroup.mem_center_iff]
      intro h
      have := Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_top h)) g hg
      exact this.symm
    rw [hcenter] at this
    exact hS'.prop.2 (le_bot_iff.1 this)
  have ha3 : a₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one a₀
    rwa [ha] at this
  have hcjemb : ∀ (y : Y) (S : Subgroup I), cj (inr y : I ⋊[ρ] Y) (S.map (inl : I →* I ⋊[ρ] Y)) =
      (S.map (ρ y).toMonoidHom).map (inl : I →* I ⋊[ρ] Y) := by
    intro y S
    show (S.map inl).map (MulAut.conj (inr y)).toMonoidHom = (S.map (ρ y).toMonoidHom).map inl
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun n => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inl_aut, map_inv]
  have hequiv : ∀ S : Subgroup I, ↥(S.map (inl : I →* I ⋊[ρ] Y)) ≃* ↥S := fun S =>
    (S.equivMapOfInjective inl inl_injective).symm
  let C : NonabCfg (I ⋊[ρ] Y) :=
    { Y := (inr : Y →* I ⋊[ρ] Y).range
      M := (inl : I →* I ⋊[ρ] Y).range
      a := inr a₀
      𝒮 := (fun S : Subgroup I => S.map (inl : I →* I ⋊[ρ] Y)) '' {S | minimalNormalEligible S}
      a_mem := ⟨a₀, rfl⟩
      a_pow := by rw [← map_pow, ha3, map_one]
      simple := by
        rintro _ ⟨S, hS, rfl⟩
        have := hsimple S hS
        exact (hequiv S).isSimpleGroup
      nonab := by
        rintro _ ⟨S, hS, rfl⟩
        obtain ⟨x, y, hxy⟩ := hnonabS S hS
        refine ⟨inl x, ⟨x, x.2, rfl⟩, inl y, ⟨y, y.2, rfl⟩, fun h => hxy (Subtype.ext ?_)⟩
        rw [← map_mul, ← map_mul] at h
        exact inl_injective h
      le_M := by
        rintro _ ⟨S, hS, rfl⟩
        exact Subgroup.map_le_range _ _
      comm := by
        rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        have hne' : S ≠ S' := fun e => hne (by rw [e])
        rw [← map_mul, ← map_mul, hcomm S hS S' hS' hne' x hx y hy]
      cj_mem := by
        rintro _ ⟨y₀, rfl⟩ _ ⟨S, hS, rfl⟩
        exact ⟨S.map (ρ y₀).toMonoidHom, hauto S hS y₀, (hcjemb y₀ S).symm⟩
      trans := by
        rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩
        obtain ⟨y, hy⟩ := htrans S hS S' hS'
        exact ⟨inr y, ⟨y, rfl⟩, by rw [hcjemb, hy]⟩
      normM := by
        rintro _ ⟨y, rfl⟩ _ ⟨x, rfl⟩
        exact ⟨ρ y x, by rw [inl_aut, map_inv]⟩
      three := by
        rintro _ ⟨S, hS, rfl⟩ hd
        have : Nat.card ↥(S.map (inl : I →* I ⋊[ρ] Y)) = Nat.card ↥S :=
          Nat.card_congr (hequiv S).toEquiv
        rw [this] at hd
        exact h3 (hd.trans (Subgroup.card_subgroup_dvd_card S))
      outer := by
        rintro _ ⟨S, hS, rfl⟩
        have := hsimple S hS
        have hcat : CFSG.Open.IsCatalogGroup ↥S :=
          isCatalogGroup_of_simple_subgroup hK S (hnonabS S hS)
        have hsolv := hCat ↥S (hnonabS S hS) hcat
        exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv (hequiv S).symm
      kills := kills_of_isLThreeTwo hY ha ρ }
  have hU : C.U ≤ J.map (inl : I →* I ⋊[ρ] Y) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨x₀, rfl⟩, c, hc, hxc⟩
    exact ⟨x₀, mem_of_comm_conj hJ hC hc hxc, rfl⟩
  have hall := C.all_le_U
  have hle : ∀ S : Subgroup I, minimalNormalEligible S → S ≤ J := by
    intro S hS
    have := (hall _ ⟨S, hS, rfl⟩).trans hU
    exact (Subgroup.map_le_map_iff_of_injective inl_injective).1 this
  refine top_unique ?_
  rw [← hsocle]
  exact iSup_le fun S => hle S.1 S.2

end Base

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
