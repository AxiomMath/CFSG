module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique CFSG.ABGLocalTools

section Generic

variable {G : Type*} [Group G]

theorem map_conj_eq_self_of_mem {D : Subgroup G} {k : G} (hk : k ∈ D) :
    D.map (MulAut.conj k).toMonoidHom = D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact D.mul_mem (D.mul_mem hk hx) (D.inv_mem hk)
  · intro x hx
    refine ⟨k⁻¹ * x * k, D.mul_mem (D.mul_mem (D.inv_mem hk) hx) hk, ?_⟩
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group

theorem exists_conj_le_of_odd_index [Finite G] {D K R : Subgroup G} (hKD : K ≤ D)
    (hodd : ¬ 2 ∣ K.relIndex D) (hR : IsSylowTwoOf R D) :
    ∃ k ∈ D, ∀ x ∈ R, k⁻¹ * x * k ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 K
  obtain ⟨hTK, hT2, hTodd⟩ := isSylowOf_iff.mp hT
  have hTD : IsSylowOf 2 T D := by
    refine isSylowOf_iff.mpr ⟨hTK.trans hKD, hT2, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex T K D hTK hKD]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
    · exact hTodd h
    · exact hodd h
  have hRD : IsSylowOf 2 R D := isSylowOf_iff.mpr ⟨hR.1, hR.2.1, hR.2.2⟩
  obtain ⟨k, hk, hconj⟩ := hTD.exists_mem_conj hRD
  exact ⟨k, hk, fun x hx => hTK ((hconj x).mp hx)⟩

theorem hasTwoGen_of_odd_index [Finite G] {D X Y R : Subgroup G} (hXD : X < D) (hYD : Y < D)
    (hgen : X ⊔ Y = D) (hodd : ¬ 2 ∣ (X ⊓ Y).relIndex D) (hR : IsSylowTwoOf R D) :
    ∃ X' Y' : Subgroup G, R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧ X' ⊔ Y' = D := by
  have hXYD : X ⊓ Y ≤ D := inf_le_left.trans hXD.le
  obtain ⟨k, hk, hRk⟩ := exists_conj_le_of_odd_index hXYD hodd hR
  have hD := map_conj_eq_self_of_mem hk
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  have hmem : ∀ Z : Subgroup G, (∀ x ∈ R, k⁻¹ * x * k ∈ Z) → R ≤ Z.map (MulAut.conj k).toMonoidHom := by
    intro Z hZ x hx
    refine ⟨k⁻¹ * x * k, hZ x hx, ?_⟩
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  refine ⟨X.map (MulAut.conj k).toMonoidHom, Y.map (MulAut.conj k).toMonoidHom,
    hmem X fun x hx => (hRk x hx).1, hmem Y fun x hx => (hRk x hx).2, ?_, ?_, ?_⟩
  · rw [← hD]
    exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hXD
  · rw [← hD]
    exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hYD
  · rw [← Subgroup.map_sup, hgen, hD]

theorem exists_two_maximal [Finite G] {D X Y R : Subgroup G} (hRX : R ≤ X) (hRY : R ≤ Y)
    (hXD : X < D) (hYD : Y < D) (hgen : X ⊔ Y = D) :
    ∃ M₁ M₂ : Subgroup G, R ≤ M₁ ∧ R ≤ M₂ ∧ M₁ < D ∧ M₂ < D ∧ M₁ ≠ M₂ ∧
      (∀ Z : Subgroup G, M₁ ≤ Z → Z < D → Z = M₁) ∧ (∀ Z : Subgroup G, M₂ ≤ Z → Z < D → Z = M₂) := by
  classical
  have hmax : ∀ W : Subgroup G, W < D → ∃ M : Subgroup G, W ≤ M ∧ M < D ∧
      ∀ Z : Subgroup G, M ≤ Z → Z < D → Z = M := by
    intro W hW
    have hfin : {Z : Subgroup G | W ≤ Z ∧ Z < D}.Finite := Set.toFinite _
    obtain ⟨M, ⟨hWM, hMD⟩, hMmax⟩ := Set.Finite.exists_maximalFor id _ hfin ⟨W, le_rfl, hW⟩
    exact ⟨M, hWM, hMD, fun Z hMZ hZD => le_antisymm (hMmax ⟨hWM.trans hMZ, hZD⟩ hMZ) hMZ⟩
  obtain ⟨M₁, hXM₁, hM₁D, hM₁⟩ := hmax X hXD
  obtain ⟨M₂, hYM₂, hM₂D, hM₂⟩ := hmax Y hYD
  refine ⟨M₁, M₂, hRX.trans hXM₁, hRY.trans hYM₂, hM₁D, hM₂D, ?_, hM₁, hM₂⟩
  intro heq
  have : D ≤ M₁ := by
    rw [← hgen]
    exact sup_le hXM₁ (heq ▸ hYM₂)
  exact absurd hM₁D (not_lt_of_ge this)

end Generic

section Alt

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem alt_le_sup_of_common_odd {X Y : Subgroup (Perm α)} {s f : Perm α}
    (hsX : s ∈ X) (hsY : s ∈ Y) (hs : Perm.sign s = -1) (hgen : X ⊔ Y = ⊤)
    (hα : 5 ≤ Nat.card α) (hf : f.IsThreeCycle) (hfX : f ∈ X) :
    alternatingGroup α ≤ (X ⊓ alternatingGroup α) ⊔ (Y ⊓ alternatingGroup α) := by
  set A := X ⊓ alternatingGroup α with hA
  set B := Y ⊓ alternatingGroup α with hB
  set G := A ⊔ B with hG
  have hAG : A ≤ G := le_sup_left
  have hBG : B ≤ G := le_sup_right
  have hconj : ∀ c ∈ X ⊓ Y, ∀ g ∈ G, c * g * c⁻¹ ∈ G := by
    intro c hc g hg
    have key : G ≤ G.comap (MulAut.conj c).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro a ha
        exact hAG ⟨X.mul_mem (X.mul_mem hc.1 ha.1) (X.inv_mem hc.1),
          (alternatingGroup.normal (α := α)).conj_mem a ha.2 c⟩
      · intro a ha
        exact hBG ⟨Y.mul_mem (Y.mul_mem hc.2 ha.1) (Y.inv_mem hc.2),
          (alternatingGroup.normal (α := α)).conj_mem a ha.2 c⟩
    exact key hg
  have hnorm : ∀ c ∈ X ⊓ Y, c ∈ Subgroup.normalizer (G : Set (Perm α)) := by
    intro c hc
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hconj c hc h hh, fun hh => ?_⟩
    have := hconj c⁻¹ ((X ⊓ Y).inv_mem hc) _ hh
    simpa [mul_assoc] using this
  have hsXY : s ∈ X ⊓ Y := ⟨hsX, hsY⟩
  have hZ : ∀ Z : Subgroup (Perm α), s ∈ Z → Z ⊓ alternatingGroup α ≤ G →
      ∀ x ∈ Z, x ∈ Subgroup.normalizer (G : Set (Perm α)) := by
    intro Z hsZ hZG x hxZ
    rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
    · exact Subgroup.le_normalizer (hZG ⟨hxZ, Perm.mem_alternatingGroup.mpr h1⟩)
    · have h2 : x * s ∈ alternatingGroup α := by
        rw [Perm.mem_alternatingGroup, map_mul, h1, hs]; rfl
      have h3 : x * s ∈ Subgroup.normalizer (G : Set (Perm α)) :=
        Subgroup.le_normalizer (hZG ⟨Z.mul_mem hxZ hsZ, h2⟩)
      have := (Subgroup.normalizer (G : Set (Perm α))).mul_mem h3
        ((Subgroup.normalizer (G : Set (Perm α))).inv_mem (hnorm s hsXY))
      simpa using this
  have htop : (⊤ : Subgroup (Perm α)) ≤ Subgroup.normalizer (G : Set (Perm α)) := by
    rw [← hgen]
    exact sup_le (hZ X hsX hAG) (hZ Y hsY hBG)
  have hGn : G.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
  have : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup hα
  have hfalt : f ∈ alternatingGroup α := hf.mem_alternatingGroup
  have hfG : f ∈ G := hAG ⟨hfX, hfalt⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G.subgroupOf (alternatingGroup α)) with h0 | h0
  · exfalso
    have : (⟨f, hfalt⟩ : alternatingGroup α) ∈ G.subgroupOf (alternatingGroup α) := hfG
    rw [h0, Subgroup.mem_bot] at this
    exact hf.ne_one (congrArg Subtype.val this)
  · exact Subgroup.subgroupOf_eq_top.mp h0

end Alt

end CFSG.QuasithinUnique.Setup.X3
