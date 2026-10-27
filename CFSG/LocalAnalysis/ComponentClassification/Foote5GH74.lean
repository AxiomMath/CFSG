module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Basic
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.GH74.Conclusion
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocOdd

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

theorem oddLieType_of_lieModel_ne_two {X : Type} [Group X]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hm : Blueprint.LieModel X t n p f)
    (hp : p.Prime) (hp2 : p ≠ 2) : Blueprint.OddLieType X :=
  CFSG.ComponentClassification.GSThmB.Soc.oddLieType_of_lieModel hm hp hp2

theorem ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

@[expose] def MacWilliamsStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    (∀ E : Subgroup S, E.Normal → Open.IsElemAbelian 2 E → Nat.card E ≠ 8) →
    ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U

variable {G : Type} [Group G] [Finite G]

theorem gen4_of_isSylowOf {T : Subgroup G} (hT : IsSylowOf 2 T ⊤)
    (hgen : ∀ U ≤ T, ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = U) : GH74.Gen4 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hT (le_top : P ≤ ⊤) hP
  set U := P.map (MulAut.conj k⁻¹).toMonoidHom with hUdef
  have hU : U ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hk e he
  obtain ⟨s, hs, hsU⟩ := hgen U hU
  refine ⟨s.image (MulAut.conj k), Finset.card_image_le.trans hs, ?_⟩
  have h1 : closure ((s.image (MulAut.conj k) : Finset G) : Set G) =
      (closure (s : Set G)).map (MulAut.conj k).toMonoidHom := by
    rw [MonoidHom.map_closure, Finset.coe_image]
    rfl
  rw [h1, hsU, hUdef, Subgroup.map_map]
  convert Subgroup.map_id P using 2
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
  group

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem nonabelian : ∃ a b : G, a * b ≠ b * a := by
  have hq := isQuasisimple_quotient_of_isPComponent h.zL.2.1 h.zL.2.2
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isQuasisimple hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun hab' => hab ?_⟩
  have h1 : a * b = b * a := Subtype.ext (by rw [coe_mul, coe_mul]; exact hab')
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]

theorem three_le_twoRank : 3 ≤ Open.twoRank G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrQ : CFSG.Open.pRank 2 Q = 2 := by
    have h1 := h.pRank_Q
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  obtain ⟨E, hEQ, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two Q
  rw [hrQ] at hEcard
  have ht2 : t ^ 2 = 1 := by rw [← h.t2]; exact pow_orderOf_eq_one t
  have htE : t ∉ E := fun htE => by
    have h1 : t ∈ Q ⊓ L := mem_inf.mpr ⟨hEQ htE, h.tL⟩
    rw [h.Q_inf_L, mem_bot] at h1
    have h2 := h.t2
    rw [h1, orderOf_one] at h2
    omega
  exact succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
    (fun e he => h.commute_Q_R (hEQ he) h.tR) ht2 htE (le_top : E ≤ ⊤) (mem_top t)

theorem false_of_gh74Conclusion (hKG : Foote5KnownGroups) (hGH : GH74.GH74Conclusion G) :
    False := by
  have : IsSimpleGroup G := h.sec4.simple
  obtain ⟨t₀, ⟨-, -, ht₀, hmax₀, htype₀, -⟩, hncon⟩ := h.sec4.ce
  have hL₀F : L₀ ∈ footeFamilyOf L₀ := ⟨⟨t₀, hmax₀⟩, ⟨MulEquiv.refl _⟩⟩
  have hL₀ : IsFooteComponent L₀ := ⟨⟨t₀, ht₀⟩, htype₀, h.sec4.hrank2 L₀ hL₀F⟩
  have hL : IsFooteComponent L := by
    obtain ⟨-, ⟨eML⟩⟩ := id h.memF
    exact ⟨⟨z, h.zL⟩, footeFamilyType_of_equiv eML htype₀, h.sec4.hrank2 L h.memF⟩
  have hK := hKG G h.sec4.simple L hL
  have hK₀ := hKG G h.sec4.simple L₀ hL₀
  have hrk : ¬ CFSG.pRank 2 ↥(coreActionKernel L) ≤ 1 := by rw [h.rankCL]; omega
  have hsmall := fun hX => hrk (hK.2.2.2.2 hX)
  have hL₀ne : L₀ ≠ ⊥ := by
    intro hbot
    have h1 := h.sec4.hrank2 L₀ hL₀F
    rw [hbot] at h1
    have h2 : CFSG.pRank 2 ↥(⊥ : Subgroup G) ≤ 1 :=
      pRank_le_one_of_card_le_two (by rw [card_bot]; norm_num)
    omega
  have hA : conjClosure L₀ (pLayer G 2) = ⊤ := by
    rw [pLayer_two_eq_top_of_isSimpleGroup h.nonabelian h.t2, conjClosure_top_eq_top hL₀ne]
  obtain ⟨eX⟩ := nonempty_quotient_top_equiv h.t2
  apply hncon
  rw [hA]
  have h5 : Blueprint.OddLieType G → FooteConclusion t₀ L₀ ⊤ := fun hodd =>
    Or.inr (Or.inr (Or.inr (Or.inr
      ⟨eX.isSimpleGroup, (ClassicalInvolution.oddLieType_congr eX).2 hodd⟩)))
  rcases hGH with ⟨p, f, hp, hp2, hf, h1 | h1⟩ | ⟨p, f, hp, hp2, hf, h1⟩ | ⟨f, h1⟩ |
      ⟨p, f, hp, hp2, hf, -, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ | ⟨p, f, hp, hf, hm, h1⟩ |
      ⟨p, f, hp, hf, hm, h1⟩ | (h1 | h1 | h1 | h1) | ⟨n, hn, hn', ⟨e⟩⟩ |
      (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp hp2)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp hp2)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp hp2)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 Nat.prime_three (by norm_num))
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp hp2)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp hp2)
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp (ne_two_of_pow_mod_four hf (Or.inl hm)))
  · exact h5 (oddLieType_of_lieModel_ne_two h1 hp (ne_two_of_pow_mod_four hf (Or.inr hm)))
  · exact (hsmall (Or.inl h1)).elim
  · exact (hsmall (Or.inr (Or.inl h1))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inl h1)))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inl h1))))).elim
  · interval_cases n
    · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))).elim
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨⟨eX.trans e⟩, hK₀.1 ⟨e⟩⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨⟨eX.trans e⟩, hK₀.2.1 ⟨e⟩⟩))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨eX.trans e⟩, hK₀.2.2.1 ⟨e⟩⟩)))))
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h1))))))))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h1)))))))))).elim
  · obtain ⟨e⟩ := id h1
    exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr
      ⟨⟨eX.trans (e : G ≃* Blueprint.NativeSporadic.J2)⟩, hK₀.2.2.2.1 h1⟩)))))
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h1))))))))))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h1)))))))))))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h1)))))))))))).elim

theorem false_of_gen4 (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) (h4 : GH74.Gen4 G) :
    False :=
  h.false_of_gh74Conclusion hKG (hGH G h.sec4.simple h.nonabelian h.three_le_twoRank h4)

theorem exists_normal_e8 (hMW : MacWilliamsStatement) (hGH : GH74.GH74Statement)
    (hKG : Foote5KnownGroups) {T' : Subgroup G} (hT' : IsSylowOf 2 T' ⊤) :
    ∃ E : Subgroup G, E ≤ T' ∧ T' ≤ normalizer (E : Set G) ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 8 := by
  classical
  by_contra hno
  apply h.false_of_gen4 hGH hKG
  refine gen4_of_isSylowOf hT' fun U hU => ?_
  have hnoE : ∀ E : Subgroup T', E.Normal → Open.IsElemAbelian 2 E → Nat.card E ≠ 8 := by
    intro E hEn hE h8
    refine hno ⟨E.map T'.subtype, map_subtype_le E, fun x hx => ?_, ?_, ?_⟩
    · refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨e, he, rfl⟩ := mem_map.mp hy
        exact mem_map.mpr ⟨⟨x, hx⟩ * e * ⟨x, hx⟩⁻¹, hEn.conj_mem e he _, rfl⟩
      · obtain ⟨e, he, hey⟩ := mem_map.mp hy
        refine mem_map.mpr ⟨⟨x, hx⟩⁻¹ * e * ⟨x, hx⟩, ?_, ?_⟩
        · have h1 := hEn.conj_mem e he ⟨x, hx⟩⁻¹
          rwa [inv_inv] at h1
        · rw [subtype_apply] at hey ⊢
          simp only [coe_mul, coe_inv]
          rw [hey]
          group
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
        obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
        have h1 : (⟨a', ha'⟩ : E) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := hE.1.is_comm.comm _ _
        apply Subtype.ext
        simp only [coe_mul, subtype_apply]
        exact congrArg (fun y : E => ((y : T') : G)) h1
      · obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
        rw [subtype_apply, ← coe_pow, hE.2 x' hx', coe_one]
    · rw [card_map_of_injective T'.subtype_injective, h8]
  obtain ⟨X, hX, hXU⟩ := hMW T' hT'.isPGroup hnoE (U.subgroupOf T')
  refine ⟨X.image T'.subtype, Finset.card_image_le.trans hX, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXU, subgroupOf_map_subtype, inf_of_le_left hU]

end Sec5

end CFSG.ComponentClassification.Foote5
