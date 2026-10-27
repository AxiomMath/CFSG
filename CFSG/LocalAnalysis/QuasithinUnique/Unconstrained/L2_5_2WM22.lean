module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2WLift
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin

namespace QLift

theorem map_conj_self_of_mem {X : Type*} [Group X] {S : Subgroup X} {s : X} (hs : s ∈ S) :
    S.map (MulAut.conj s).toMonoidHom = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)
  · intro hy
    refine ⟨s⁻¹ * y * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs, ?_⟩
    show s * (s⁻¹ * y * s) * s⁻¹ = y
    group

theorem mem_normalizer_of_map_conj_eq' {X : Type*} [Group X] {K : Subgroup X} {s : X}
    (h : K.map (MulAut.conj s).toMonoidHom = K) : s ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : s * x * s⁻¹ ∈ K.map (MulAut.conj s).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h2 : s * y * s⁻¹ = s * x * s⁻¹ := hyx
    have : y = x := mul_left_cancel (mul_right_cancel h2)
    rwa [← this]

open CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239 M2x

theorem m22_two_parabolics
    :
    ∃ S K₀ V₀ K₁ V₁ : Subgroup ↥NativeSporadic.M22, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧
      Canon K₀ V₀ ∧ Canon K₁ V₁ ∧
      (∀ α : MulAut ↥NativeSporadic.M22, S.map α.toMonoidHom = S → K₀.map α.toMonoidHom = K₀) ∧
      (∀ α : MulAut ↥NativeSporadic.M22, S.map α.toMonoidHom = S → K₁.map α.toMonoidHom = K₁) ∧
      K₀ ⊔ K₁ = ⊤ := by
  classical
  obtain ⟨K₀, E₀, S, hstruct, hmax, hS2, hSi, hinv⟩ :=
    BlockData.exists_struct M22Insp.data M22Insp.valid M22Insp.hgens M22Insp.hcard M22Insp.hAut
  have h6s : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn6 : ¬ IsPGroup 2 (alternatingGroup (Fin 6)) := M22Insp.alt6_not_pgroup
  obtain ⟨hXfin, -, hXs⟩ := fam_m22_simplicity
  have hE₀card : Nat.card E₀ = 16 := by
    rw [hstruct.card]
    norm_num
  have hK₀N : K₀ ≤ Subgroup.normalizer (E₀ : Set ↥NativeSporadic.M22) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstruct.le).mp hstruct.normal
  have hE₀bot : E₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE₀card
    omega
  have hE₀top : E₀ ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, card_M22] at hE₀card
    omega
  have hK₀bot : K₀ ≠ ⊥ := fun h => hE₀bot (le_bot_iff.mp (h ▸ hstruct.le))
  have hK₀top : K₀ ≠ ⊤ := by
    intro htop
    rw [htop] at hK₀N
    have hnt : Subgroup.normalizer (E₀ : Set ↥NativeSporadic.M22) = ⊤ := top_le_iff.mp hK₀N
    have hEn : E₀.Normal := Subgroup.normalizer_eq_top_iff.mp hnt
    rcases hXs.eq_bot_or_eq_top_of_normal E₀ with h | h
    · exact hE₀bot h
    · exact hE₀top h
  have hNK : Subgroup.normalizer (K₀ : Set ↥NativeSporadic.M22) = K₀ := by
    rcases hmax _ Subgroup.le_normalizer with h | h
    · exact h
    · exfalso
      have hKn : K₀.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases hXs.eq_bot_or_eq_top_of_normal K₀ with h1 | h1
      · exact hK₀bot h1
      · exact hK₀top h1
  have hSK : S ≤ K₀ := by
    intro s hs
    have hK := hinv (MulAut.conj s) (map_conj_self_of_mem hs)
    rw [← hNK]
    exact mem_normalizer_of_map_conj_eq' hK
  have hodd : ¬ 2 ∣ (S.subgroupOf K₀).index := by
    intro h
    apply hSi
    have := Subgroup.relIndex_mul_index hSK
    exact h.trans ⟨K₀.index, this.symm⟩
  have hE₀S : E₀ ≤ S :=
    le_of_normal_pGroup_of_sylow hS2 hodd hstruct.le hstruct.normal hstruct.isPGroup
  have hEinv : ∀ α : MulAut ↥NativeSporadic.M22, S.map α.toMonoidHom = S →
      E₀.map α.toMonoidHom = E₀ := by
    intro α hα
    have hK := hinv α hα
    have hle1 : E₀.map α.toMonoidHom ≤ K₀ := by
      rw [← hK]
      exact Subgroup.map_mono hstruct.le
    have hn : K₀ ≤ Subgroup.normalizer ((E₀.map α.toMonoidHom : Subgroup _) : Set _) := by
      rw [← Subgroup.map_equiv_normalizer_eq E₀ α]
      calc K₀ = K₀.map α.toMonoidHom := hK.symm
        _ ≤ (Subgroup.normalizer (E₀ : Set ↥NativeSporadic.M22)).map α.toMonoidHom :=
          Subgroup.map_mono hK₀N
    have hnormal : ((E₀.map α.toMonoidHom).subgroupOf K₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle1).mpr hn
    have hle : E₀.map α.toMonoidHom ≤ pCoreOf 2 K₀ :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ K₀ hle1 hnormal
        (hstruct.isPGroup.map _)
    rw [hstruct.pCoreOf_eq h6s hn6] at hle
    exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge
  have hE₀ab : ElemAb E₀ := by
    have hEab := hstruct.elem
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · have := isMulCommutative_iff.mp hEab.1 ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    · have := hEab.2 x hx
      simpa [pow_two] using this
  obtain ⟨Ea, Eb, ga, gb, hEaP, hEbP, hne, hEa, hEb, hca, hcb, hcl, hcena, hcenb,
    ⟨hga1, hga2⟩, ⟨hgb1, hgb2⟩⟩ := twoE_M22.exists_at hS2 hSi
  let Φ : MulAut ↥NativeSporadic.M22 → Prop := fun α => S.map α.toMonoidHom = S
  have hΦP : ∀ α, Φ α → S.map α.toMonoidHom = S := fun α h => h
  have hΦE : ∀ α, Φ α → E₀.map α.toMonoidHom = E₀ := hEinv
  obtain ⟨K, V, hVK, hKn, hV2, hVc, hKinv, hKnot⟩ : ∃ K V : Subgroup ↥NativeSporadic.M22,
      V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set ↥NativeSporadic.M22) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ (∀ β, Φ β → K.map β.toMonoidHom = K) ∧
      ¬ K ≤ Subgroup.normalizer (E₀ : Set ↥NativeSporadic.M22) := by
    rcases hcl E₀ hE₀S hE₀ab hE₀card with h | h
    · rw [h] at hΦE ⊢
      exact pair_step hne hEbP hEb hcb hcl hcenb hga1 hga2 Φ hΦP hΦE
    · rw [h] at hΦE ⊢
      exact pair_step hne.symm hEaP hEa hca (fun E hE hab hc => (hcl E hE hab hc).symm) hcena
        hgb1 hgb2 Φ hΦP hΦE
  refine ⟨S, K₀, E₀, K, V, hS2, hSi,
    ⟨hstruct.le, hK₀N, hstruct.isPGroup, fun x hx hc => ?_⟩, ⟨hVK, hKn, hV2, hVc⟩, hinv, hKinv, ?_⟩
  · exact hstruct.centralizer_le h6s ⟨hx, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc v hv).symm⟩
  · rcases hmax (K₀ ⊔ K) le_sup_left with h | h
    · exfalso
      exact hKnot (fun k hk => hK₀N (h ▸ (le_sup_right : K ≤ K₀ ⊔ K) hk))
    · exact h

end QLift

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def M22CoverExcluded252 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ ML : Subgroup G),
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
    ML ≤ L → ML ≠ L → S₀ ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S₀ ⊓ L) L →
    (∀ K : Subgroup G, K ≤ L → S₀ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ ML) →
    False

theorem m22CoverExcluded252
    : M22CoverExcluded252 := by
  intro G _ _ L S₀ ML hQ hMLL hMLne hS₀N hsyl hall
  obtain ⟨ε⟩ := hQ
  obtain ⟨S, K₀, V₀, K₁, V₁, hS2, hSi, h₀, h₁, hinv₀, hinv₁, hgen⟩ :=
    Unc25G2.QLift.m22_two_parabolics
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := ε
  let f : ↥L →* ↥CFSG.Blueprint.NativeSporadic.M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = CFSG.pCore 2 ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk z) = 1 ↔ z ∈ CFSG.pCore 2 ↥L
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff z
  have : Finite ↥CFSG.Blueprint.NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  obtain ⟨A, B, hAL, hBL, hAB, hNA, hNB, hcA, hcB⟩ :=
    Unc25G2.QLift.exists_two_lifts hS₀N hsyl f hf hker hS2 hSi h₀ h₁ hinv₀ hinv₁ hgen
  have hA := hall A hAL hNA hcA
  have hB := hall B hBL hNB hcB
  apply hMLne
  apply le_antisymm hMLL
  rw [← hAB]
  exact sup_le hA hB

end CFSG.QuasithinUnique
