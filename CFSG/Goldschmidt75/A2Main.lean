module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Goldschmidt.Steps.Red1
public import CFSG.Goldschmidt75.Quotient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def A2For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (S₁ S₂ : Subgroup G), S₁ ≤ T → S₂ ≤ T →
    fusionStronglyClosed (S₁ : Set G) T → fusionStronglyClosed (S₂ : Set G) T → ⁅S₁, S₂⁆ = ⊥ →
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔ goldschmidtOddCore G

theorem pCore_map_le
    {M A : Subgroup G} {TM : Sylow 2 M} (hcore : CoreHyp M TM (A.subgroupOf M)) :
    (CFSG.Open.pCore 2 M).map M.subtype ≤ A := by
  obtain ⟨-, h2, -⟩ :=
    coreStatement M TM _ hcore.le hcore.comm hcore.closed hcore.gen hcore.oddCore
  rintro _ ⟨z, hz, rfl⟩
  have : z ∈ A.subgroupOf M := by rw [h2]; exact mem_sup_left hz
  exact mem_subgroupOf.mp this

theorem le_centralizer_pCore_map
    {M A : Subgroup G} {TM : Sylow 2 M}
    (hcore : CoreHyp M TM (A.subgroupOf M)) :
    M ≤ centralizer (((CFSG.Open.pCore 2 M).map M.subtype : Subgroup G) : Set G) := by
  obtain ⟨-, h2, -⟩ :=
    coreStatement M TM _ hcore.le hcore.comm hcore.closed hcore.gen hcore.oddCore
  have h18 := (N18 M TM _ hcore.le hcore.comm hcore.closed hcore.gen).1
  have hle : CFSG.Open.pCore 2 M ≤ A.subgroupOf M := by rw [h2]; exact le_sup_left
  intro m hm
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzc := h18 (mem_inf.mpr ⟨hle hz, hz⟩)
  exact (congrArg Subtype.val (mem_center_iff.mp hzc ⟨m, hm⟩)).symm

omit [Finite G] in
theorem normal_pCore_map {M : Subgroup G} [M.Normal] :
    ((CFSG.Open.pCore 2 M).map M.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hx
  have h := SStarTransport.pCore_map_mulEquiv 2 (MulAut.conjNormal g : MulAut M)
  have hz' : (MulAut.conjNormal g : MulAut M) z ∈ CFSG.Open.pCore 2 M := by
    rw [← h]
    exact ⟨z, hz, rfl⟩
  exact ⟨_, hz', by simp [MulAut.conjNormal_apply]⟩

theorem commutator_le_of_quotient {N : Subgroup G} [N.Normal] (hIH : A2For (G ⧸ N))
    (T : Sylow 2 G) {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T)
    (hS₁ : fusionStronglyClosed (S₁ : Set G) T) (hS₂ : fusionStronglyClosed (S₂ : Set G) T)
    (hcomm : ⁅S₁, S₂⁆ = ⊥)
    (hdisj : S₁.map (QuotientGroup.mk' N) ⊓ S₂.map (QuotientGroup.mk' N) ≤
      (S₁ ⊓ S₂).map (QuotientGroup.mk' N)) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G) ⊔
        (goldschmidtOddCore (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  set q := QuotientGroup.mk' N with hq
  have hsurj := QuotientGroup.mk'_surjective N
  have h := hIH (sylowMap N T) (S₁.map q) (S₂.map q) (by rw [coe_sylowMap]; exact map_mono h₁)
    (by rw [coe_sylowMap]; exact map_mono h₂) (stronglyClosed_map N T h₁ hS₁)
    (stronglyClosed_map N T h₂ hS₂) (by rw [← map_commutator, hcomm, Subgroup.map_bot])
  have hle : normalClosure ((S₁.map q ⊓ S₂.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ≤
      (normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)).map q := by
    rw [map_normalClosure _ _ hsurj, ← coe_map]
    exact normalClosure_mono hdisj
  intro x hx
  have hqx : q x ∈ ⁅normalClosure ((S₁.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)),
      normalClosure ((S₂.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N))⁆ := by
    have : q x ∈ (⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆).map q :=
      ⟨x, hx, rfl⟩
    rwa [map_commutator, map_normalClosure _ _ hsurj, map_normalClosure _ _ hsurj, ← coe_map,
      ← coe_map] at this
  have h3 : q x ∈ ((normalClosure ((S₁ ⊓ S₂ : Subgroup G) : Set G)).map q ⊔
      goldschmidtOddCore (G ⧸ N) : Subgroup (G ⧸ N)) := (sup_le_sup_right hle _) (h hqx)
  rw [← SetLike.mem_coe, mul_normal] at h3
  obtain ⟨_, ⟨m, hm, rfl⟩, o, ho, hmo⟩ := h3
  have hy : m⁻¹ * x ∈ (goldschmidtOddCore (G ⧸ N)).comap q := by
    rw [mem_comap, map_mul, map_inv, ← hmo]
    simpa using ho
  have e : x = m * (m⁻¹ * x) := by group
  rw [e]
  exact mul_mem_sup hm hy

end CFSG.Goldschmidt75
