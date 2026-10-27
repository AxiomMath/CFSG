module

public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Steps.GoldType
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.G37CoreSetup
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Goldschmidt

namespace RuGold

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L) : goldschmidtSimpleType L' := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hpo, hf, h5, h8, ⟨e'⟩⟩ | ⟨m, hm, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hpo, hf, h5, h8, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, (Nat.card_congr e.toEquiv).symm.trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))))

noncomputable def quotCenterCongr {K L : Type*} [Group K] [Group L] (e : K ≃* L) :
    K ⧸ center K ≃* L ⧸ center L :=
  QuotientGroup.congr (center K) (center L) e (Subgroup.map_center_eq e)

variable {Y Z : Type*} [Group Y] [Group Z]

theorem inducesOmega1_of_map (φ : Y →* Z) (hφ : Function.Injective φ) {A K T : Subgroup Y}
    (h : InducesOmega1 (A.map φ) (K.map φ) (T.map φ)) : InducesOmega1 A K T := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a ha => ?_, fun t ht ht2 => ?_⟩
  · obtain ⟨_, ⟨⟨t, htT, rfl⟩, ⟨t₂, htK, ht₂⟩⟩, ht2, hconj⟩ := h1 (φ a) ⟨a, ha, rfl⟩
    have htt : t₂ = t := hφ ht₂
    subst htt
    refine ⟨t₂, ⟨htT, htK⟩, mem_centralizer_iff.mpr fun k hk => hφ ?_, fun x hx => hφ ?_⟩
    · have := mem_centralizer_iff.mp ht2 (φ k) ⟨k, hk, rfl⟩
      simpa [map_mul, map_pow] using this
    · have := hconj (φ x) ⟨x, hx, rfl⟩
      simpa [map_mul, map_inv] using this
  · have hφt : φ t ∈ T.map φ ⊓ K.map φ := ⟨⟨t, ht.1, rfl⟩, ⟨t, ht.2, rfl⟩⟩
    have hφt2 : φ t ^ 2 ∈ centralizer ((K.map φ : Subgroup Z) : Set Z) := by
      refine mem_centralizer_iff.mpr ?_
      rintro _ ⟨k, hk, rfl⟩
      have := mem_centralizer_iff.mp ht2 k hk
      rw [← map_pow, ← map_mul, ← map_mul, this]
    obtain ⟨_, ⟨a, ha, rfl⟩, hconj⟩ := h2 (φ t) hφt hφt2
    exact ⟨a, ha, fun x hx => hφ (by simpa [map_mul, map_inv] using hconj (φ x) ⟨x, hx, rfl⟩)⟩

theorem inducesOmega1_map (φ : Y →* Z) (hφ : Function.Injective φ) {A K T : Subgroup Y}
    (h : InducesOmega1 A K T) : InducesOmega1 (A.map φ) (K.map φ) (T.map φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ⟨htT, htK⟩, ht2, hconj⟩ := h1 a ha
    refine ⟨φ t, ⟨⟨t, htT, rfl⟩, ⟨t, htK, rfl⟩⟩, ?_, ?_⟩
    · refine mem_centralizer_iff.mpr ?_
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_pow, ← map_mul, ← map_mul, mem_centralizer_iff.mp ht2 k hk]
    · rintro _ ⟨x, hx, rfl⟩
      simp only [← map_inv, ← map_mul, hconj x hx]
  · rintro _ ⟨⟨t, htT, rfl⟩, ⟨t₂, htK, ht₂⟩⟩ ht2
    have htt : t₂ = t := hφ ht₂
    subst htt
    have ht2' : t₂ ^ 2 ∈ centralizer (K : Set Y) := by
      refine mem_centralizer_iff.mpr fun k hk => hφ ?_
      have := mem_centralizer_iff.mp ht2 (φ k) ⟨k, hk, rfl⟩
      simpa [map_mul, map_pow] using this
    obtain ⟨a, ha, hconj⟩ := h2 t₂ ⟨htT, htK⟩ ht2'
    refine ⟨φ a, ⟨a, ha, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simp only [← map_inv, ← map_mul, hconj x hx]

theorem inducesOmega1_of_inf_eq {A K T T' : Subgroup Y} (hT : T ⊓ K = T' ⊓ K)
    (h : InducesOmega1 A K T) : InducesOmega1 A K T' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a ha => ?_, fun t ht ht2 => ?_⟩
  · obtain ⟨t, htK, rest⟩ := h1 a ha
    exact ⟨t, hT ▸ htK, rest⟩
  · exact h2 t (hT ▸ ht) ht2

end RuGold

open RuGold

section Main

variable {H : Type} [Group H] [Finite H]

theorem component_le_normalClosure_or_le_centralizer {K : Subgroup H} (hK : IsComponent K)
    (A : Subgroup H) :
    K ≤ normalClosure (A : Set H) ∨ A ≤ centralizer (K : Set H) := by
  rcases GorensteinWalter.component_le_or_commutator_eq_bot_of_normal
      ((CFSG.Walter.isComponent_iff_isComponentOf_top K).mp hK)
      (normalClosure_normal (s := (A : Set H))) with h | h
  · exact Or.inl h
  · refine Or.inr fun a ha => mem_centralizer_iff.mpr fun k hk => ?_
    have h1 := commutator_eq_bot_iff_le_centralizer.mp h hk
    exact (mem_centralizer_iff.mp h1 a (subset_normalClosure ha)).symm

theorem stronglyClosed_components_or_normal
    (hO : goldschmidtOddCore H = ⊥) (S : Sylow 2 H)
    {A : Subgroup H} (hAS : A ≤ (S : Subgroup H)) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set H) (S : Subgroup H)) :
    (∀ K : Subgroup H, IsComponent K → K ≤ normalClosure (A : Set H) →
        goldschmidtSimpleType (K ⧸ center K) ∧ InducesOmega1 A K (S : Subgroup H) ∧
        ∀ a ∈ A, ∃ x ∈ A ⊓ K, ∀ y ∈ K, a⁻¹ * y * a = x⁻¹ * y * x) ∧
      ((∀ K : Subgroup H, IsComponent K → ¬ K ≤ normalClosure (A : Set H)) → A.Normal) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIH : IH (Nat.card H + 1) := fun Z _ _ _ => coreStatement_iff.mp coreStatement Z
  have hTsyl : fusionIsSylowIn 2 (S : Subgroup H) ⊤ :=
    ⟨le_top, S.isPGroup', fun P _ hP hTP => S.is_maximal' hP hTP⟩
  obtain ⟨hConc, -, -, hC3, hlast⟩ := N16_of N1 _ hIH H S A ⊤ S hAS hAab hcl hAS hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup H := normalClosureIn ⊤ A with hMdef
  have hMeq : M = normalClosure (A : Set H) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hAM : A ≤ M := by
    rw [hMeq]
    exact subset_normalClosure
  have hOM : goldschmidtOddCore M = ⊥ :=
    G37.goldschmidtOddCore_eq_bot_of_isSubnormal hO hMn.isSubnormal
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  set e : M ≃* M ⧸ goldschmidtOddCore M :=
    MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩ with he
  have heπ : e.toMonoidHom = π := MonoidHom.ext fun _ => rfl
  have hbar : ∀ B : Subgroup H, barOf M B = (B.subgroupOf M).map e.toMonoidHom := fun B => by
    rw [heπ]
    rfl
  refine ⟨fun K hK hKM => ?_, fun hno => ?_⟩
  · rw [← hMeq] at hKM
    have hK' : IsComponent (K.subgroupOf M) := CFSG.LocalCores.component_overgroup hK hKM
    set L := (K.subgroupOf M).map e.toMonoidHom with hL
    have hLo : IsComponentOf L ⊤ :=
      (CFSG.isComponent_iff_open L).mp (CFSG.LocalCores.isComponent_map_mulEquiv e hK')
    have eKL : K ≃* L := (subgroupOfEquivOfLe hKM).symm.trans
      ((K.subgroupOf M).equivMapOfInjective e.toMonoidHom e.injective)
    have htype : goldschmidtSimpleType (K ⧸ center K) :=
      goldschmidtSimpleType_of_mulEquiv (quotCenterCongr eKL).symm (hConc.2.2 L hLo)
    have hind0 := hC3 L hLo
    rw [hbar, hbar] at hind0
    have hind1 := inducesOmega1_map M.subtype M.subtype_injective
      (inducesOmega1_of_map e.toMonoidHom e.injective hind0)
    rw [subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hAM, inf_eq_left.mpr hKM] at hind1
    have hind : InducesOmega1 A K (S : Subgroup H) := by
      refine inducesOmega1_of_inf_eq ?_ hind1
      rw [inf_assoc, inf_eq_right.mpr hKM]
    exact ⟨htype, hind, N17_of N11b H S A K hAS hAab hcl hO
      ((CFSG.isComponent_iff_open K).mp hK) htype hind⟩
  · have hlayer : goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥ := by
      rw [goldschmidtLayer, sSup_eq_bot]
      intro L hL
      exfalso
      have hK'c : IsComponent (L.map e.symm.toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv e.symm ((CFSG.isComponent_iff_open L).mpr hL)
      set K' := L.map e.symm.toMonoidHom with hK'
      have hKc : IsComponent (K'.map M.subtype) :=
        ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (K'.equivMapOfInjective M.subtype M.subtype_injective) hK'c.1,
          hK'c.2.trans' hMn.isSubnormal⟩
      exact hno _ hKc (hMeq ▸ map_subtype_le K')
    obtain ⟨-, hnorm⟩ := hlast hlayer
    have hOM' : oddCoreOf M = ⊥ := by rw [oddCoreOf, hOM, Subgroup.map_bot]
    have h1 := hnorm (by rw [hOM']; exact commutator_bot_left A)
    exact normalizer_eq_top_iff.mp (top_le_iff.mp h1)

end Main

end CFSG.ComponentClassification.GMS78
