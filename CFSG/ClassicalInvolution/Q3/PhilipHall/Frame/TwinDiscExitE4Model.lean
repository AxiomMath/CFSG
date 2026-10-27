module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Conn
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TL4

namespace TwinDisc

namespace ExitE4

section Graph

variable {M G : Type} [Group M] [Group G] [Finite M] [Finite G]

theorem dstar_at (φ : M →* G) (hφ : Function.Injective φ) (Kc : Subgroup G) {K : Subgroup M}
    (hq : Nonempty (↥K ≃* QuaternionGroup 2)) (hKc : K.map φ = Kc)
    (hD : ∀ m : M, Relation.ReflTransGen (Vtx.StarRel φ.range Kc) Kc (conjSub (φ m) Kc)) :
    T3.DStarConnected (CoreAssembly.conjClass K) := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : M, conjSub (φ m₀) (K.map φ) = Kc :=
    ⟨1, by rw [map_one, conjSub_one, hKc]⟩
  obtain ⟨eK⟩ := hq
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  set K' := conjSub m₀ K with hK'
  have hK'map : K'.map φ = Kc := by rw [hK', ← conjSub_map, hm₀]
  have hmapc : ∀ m : M, (conjSub m K').map φ = conjSub (φ m) Kc := by
    intro m
    rw [← conjSub_map, hK'map]
  have hcl : ∀ J, J ∈ CoreAssembly.conjClass K ↔ ∃ m, J = conjSub m K' := by
    intro J
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g * m₀⁻¹, ?_⟩
      show conjSub g K = conjSub (g * m₀⁻¹) K'
      rw [hK', ← conjSub_mul, inv_mul_cancel_right]
    · rintro ⟨m, rfl⟩
      refine ⟨m * m₀, ?_⟩
      show conjSub (m * m₀) K = conjSub m K'
      rw [hK', conjSub_mul]
  have hmem : ∀ m, conjSub m K' ∈ CoreAssembly.conjClass K := fun m => (hcl _).mpr ⟨m, rfl⟩
  have hK'mem : K' ∈ CoreAssembly.conjClass K := (hcl _).mpr ⟨1, (conjSub_one K').symm⟩
  have hne_of : ∀ m₁ m₂ : M, conjSub (φ m₁) Kc ≠ conjSub (φ m₂) Kc →
      conjSub m₁ K' ≠ conjSub m₂ K' := fun m₁ m₂ h e => h (by rw [← hmapc, ← hmapc, e])
  have hu_of : ∀ m₁ m₂ : M, (∃ u ∈ conjSub (φ m₁) Kc, orderOf u = 4 ∧
      u ∈ Subgroup.normalizer ((conjSub (φ m₂) Kc : Subgroup G) : Set G)) →
      ∃ v ∈ conjSub m₁ K', orderOf v = 4 ∧
        v ∈ Subgroup.normalizer ((conjSub m₂ K' : Subgroup M) : Set M) := by
    rintro m₁ m₂ ⟨u, hu, hu4, huN⟩
    rw [← hmapc] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [← hmapc, Vtx.mem_normalizer_map_iff φ hφ] at huN
    exact ⟨v, hv, by rwa [orderOf_injective φ hφ] at hu4, huN⟩
  have hpath : ∀ m : M, Relation.ReflTransGen
      (dstarAdj (CoreAssembly.conjClass K)) K' (conjSub m K') := by
    have key : ∀ B, Relation.ReflTransGen (Vtx.StarRel φ.range Kc) Kc B → ∀ m : M,
        B = conjSub (φ m) Kc →
          Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) K' (conjSub m K') := by
      intro B hB
      induction hB with
      | refl =>
        intro m hm
        have he : conjSub m K' = K' :=
          Subgroup.map_injective hφ (by rw [hmapc, hK'map, ← hm])
        rw [he]
      | tail _ hstep ih =>
        intro m hm
        obtain ⟨⟨_, ⟨m', rfl⟩, hA⟩, -, hne, hu⟩ := hstep
        refine (ih m' hA).tail ⟨hmem m, ?_⟩
        rw [hA, hm] at hne
        rw [hA, hm] at hu
        rcases hu with hu | hu
        · exact Or.inl ((Vtx.mem_omegaStarNbr_conjClass_iff h2 h8).mpr
            ⟨hmem m, fun e => hne_of m' m hne e.symm, hu_of m m' hu⟩)
        · exact Or.inr ((Vtx.mem_omegaStarNbr_conjClass_iff h2 h8).mpr
            ⟨hmem m', hne_of m' m hne, hu_of m' m hu⟩)
    exact fun m => key _ (hD m) m rfl
  have hrev : ∀ X, Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) K' X →
      X ∈ CoreAssembly.conjClass K ∧
        Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass K)) X K' := by
    intro X hX
    induction hX with
    | refl => exact ⟨hK'mem, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
      exact ⟨hstep.1, Relation.ReflTransGen.head ⟨ih.1, hstep.2.symm⟩ ih.2⟩
  intro A hA B hB
  obtain ⟨m₁, rfl⟩ := (hcl A).mp hA
  obtain ⟨m₂, rfl⟩ := (hcl B).mp hB
  exact ((hrev _ (hpath m₁)).2).trans (hpath m₂)

theorem dstar_of_emb (H Kc : Subgroup G)
    (hD : ∀ h ∈ H, Relation.ReflTransGen (Vtx.StarRel H Kc) Kc (conjSub h Kc))
    {K : Subgroup M} (hq : Nonempty (↥K ≃* QuaternionGroup 2)) (φ : M →* G)
    (hφ : Function.Injective φ) (hrange : φ.range = H) (hKc : K.map φ = Kc) :
    T3.DStarConnected (CoreAssembly.conjClass K) :=
  dstar_at φ hφ Kc hq hKc fun m => by
    rw [hrange]
    exact hD _ (hrange ▸ ⟨m, rfl⟩)

end Graph

section Models


theorem e4DStarW_PSp {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4DStarW M := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
  intro K s hq hinv htw
  have hinj := E4Sp6.emb_injective e
  obtain ⟨eK⟩ := hq
  have hd : Vtx.AmbientQuatDatum CFSG.Sporadic.Schreier.Co3.co3X36 (K.map (E4Sp6.emb e))
      (E4Sp6.emb e s) := by
    rw [← E4Sp6.range_emb e]
    refine ⟨Subgroup.map_le_range _ K, ⟨(K.equivMapOfInjective _ hinj).symm.trans eK⟩,
      Vtx.isUniqueInvolution_map _ hinj hinv, ?_⟩
    rintro _ ⟨m, rfl⟩ hms
    have hm : m ∈ Subgroup.centralizer ({s} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hms])
    rw [conjSub_map]
    rcases htw m hm with h | h
    · left
      rw [h]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  obtain ⟨g, hg, hgK⟩ := E4Sp6.ident_ambient hd
  rw [← E4Sp6.range_emb e] at hg
  obtain ⟨m, rfl⟩ := hg
  have hmem : ∀ m' : M, E4Sp6.emb e m' ∈ CFSG.Sporadic.Schreier.Co3.co3X36 :=
    fun m' => (e m').2
  refine dstar_of_emb CFSG.Sporadic.Schreier.Co3.co3X36 E4Sp6.K0
    (fun h hh => E4Sp6.reflTransGen_starRel hh) ⟨eK⟩
    ((MulAut.conj (E4Sp6.emb e m)).toMonoidHom.comp (E4Sp6.emb e))
    ((MulAut.conj (E4Sp6.emb e m)).injective.comp hinj) ?_ ?_
  · rw [MonoidHom.range_comp, E4Sp6.range_emb]
    exact conjSub_eq_self_of_mem (hmem m)
  · rw [← Subgroup.map_map]
    exact hgK

theorem e4DStarW_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4DStarW M := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hM
  intro K s hq hinv htw
  have hinj := E4O8.emb_injective e
  obtain ⟨eK⟩ := hq
  have hd : Vtx.AmbientQuatDatum CFSG.EvenSmallLie.OmegaEight.omegaT (K.map (E4O8.emb e))
      (E4O8.emb e s) := by
    rw [← E4O8.range_emb e]
    refine ⟨Subgroup.map_le_range _ K, ⟨(K.equivMapOfInjective _ hinj).symm.trans eK⟩,
      Vtx.isUniqueInvolution_map _ hinj hinv, ?_⟩
    rintro _ ⟨m, rfl⟩ hms
    have hm : m ∈ Subgroup.centralizer ({s} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hms])
    rw [conjSub_map]
    rcases htw m hm with h | h
    · left
      rw [h]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  obtain ⟨g, hg, hgK⟩ := E4O8.ident_omega hd
  rw [← E4O8.range_emb e] at hg
  obtain ⟨m, rfl⟩ := hg
  have hmem : ∀ m' : M, E4O8.emb e m' ∈ CFSG.EvenSmallLie.OmegaEight.omegaT :=
    fun m' => (e m').2
  refine dstar_of_emb CFSG.EvenSmallLie.OmegaEight.omegaT E4O8.K0
    (fun h hh => E4O8.reflTransGen_starRel hh) ⟨eK⟩
    ((MulAut.conj (E4O8.emb e m)).toMonoidHom.comp (E4O8.emb e))
    ((MulAut.conj (E4O8.emb e m)).injective.comp hinj) ?_ ?_
  · rw [MonoidHom.range_comp, E4O8.range_emb]
    exact conjSub_eq_self_of_mem (hmem m)
  · rw [← Subgroup.map_map]
    exact hgK

theorem e4ModelDStar_of_certs : E4ModelDStar := by
  intro M _ _ hM
  exact hM.elim e4DStarW_PSp e4DStarW_POmegaPlus

end Models

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
