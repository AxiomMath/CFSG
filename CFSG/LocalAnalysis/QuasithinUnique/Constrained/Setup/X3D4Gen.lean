module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.X5
open scoped commutatorElement

section Gen

variable {H : Type*} [Group H] (L : Subgroup H) [L.Normal] {S : Type*} [Group S]

theorem mem_normalizer_of_normal (h : H) : h ∈ Subgroup.normalizer (L : Set H) := by
  rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top h

@[expose] noncomputable def outAct (eQ : (L ⧸ Subgroup.center L) ≃* S) : H →* MulAut S :=
  (MulAut.congr eQ).toMonoidHom.comp
    ((normalizerAct L).comp
      (MonoidHom.codRestrict (MonoidHom.id H) (Subgroup.normalizer (L : Set H))
        (fun h => mem_normalizer_of_normal L h)))

theorem outAct_apply_mk (eQ : (L ⧸ Subgroup.center L) ≃* S) (h : H) (l : L) :
    outAct L eQ h (eQ (QuotientGroup.mk l)) =
      eQ (QuotientGroup.mk (⟨h * l * h⁻¹, (Subgroup.mem_normalizer_iff.1
        (mem_normalizer_of_normal L h) l).1 l.2⟩ : L)) := by
  show eQ ((normalizerAct L ⟨h, _⟩) (eQ.symm (eQ (QuotientGroup.mk l)))) = _
  rw [MulEquiv.symm_apply_apply, normalizerAct_apply_mk]
  rfl

theorem outAct_of_mem (eQ : (L ⧸ Subgroup.center L) ≃* S) (l : L) :
    outAct L eQ l = MulAut.conj (eQ (QuotientGroup.mk l)) := by
  ext x
  obtain ⟨y, rfl⟩ := eQ.surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [outAct_apply_mk]
  show eQ (QuotientGroup.mk _) = eQ (QuotientGroup.mk l) * eQ (QuotientGroup.mk y) *
    (eQ (QuotientGroup.mk l))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem mem_centralizer_of_outAct_eq_one [Group.IsPerfect ↥L] (eQ : (L ⧸ Subgroup.center L) ≃* S)
    {h : H} (hh : outAct L eQ h = 1) : h ∈ Subgroup.centralizer (L : Set H) := by
  have : normalizerAct L ⟨h, mem_normalizer_of_normal L h⟩ = 1 := by
    have h1 : (MulAut.congr eQ) (normalizerAct L ⟨h, mem_normalizer_of_normal L h⟩) = 1 := hh
    exact (MulAut.congr eQ).injective (by rw [h1, map_one])
  exact mem_centralizer_of_normalizerAct_eq_one L this

theorem commutator_mul_commute_left {G : Type*} [Group G] (x y z : G) (hz : z * y = y * z) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : z * y * z⁻¹ = y := by rw [hz]; group
  simp only [commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem commutator_mul_commute_right {G : Type*} [Group G] (x y z : G) (hz : z * x = x * z) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hz]
      _ = x⁻¹ * z := by group
  simp only [commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem L_le_closure_of_inner_generation [Group.IsPerfect ↥L]
    (eQ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))
    (hker : ∀ h : H, outAct L eQ h = 1 → h ∈ (Subgroup.center L).map L.subtype)
    (A : Subgroup H) {m : ℕ} (s : Fin m → alternatingGroup (Fin 6))
    (hgen : (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤
      Subgroup.closure (⋃ i, ((A.map (outAct L eQ)).map
        (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
          Subgroup (MulAut (alternatingGroup (Fin 6)))) : Set (MulAut (alternatingGroup (Fin 6))))) :
    ∃ l : Fin m → L, L ≤ Subgroup.closure (⋃ i,
      ((A.map (MulAut.conj (l i : H)).toMonoidHom : Subgroup H) : Set H)) := by
  classical
  choose l hl using fun i => QuotientGroup.mk_surjective (eQ.symm (s i))
  refine ⟨l, ?_⟩
  have hs : ∀ i, eQ (QuotientGroup.mk (l i)) = s i := fun i => by rw [hl i]; simp
  set J : Subgroup H := Subgroup.closure (⋃ i,
      ((A.map (MulAut.conj (l i : H)).toMonoidHom : Subgroup H) : Set H)) with hJ
  have hconj : ∀ i, ∀ a : H, outAct L eQ ((l i : H) * a * (l i : H)⁻¹) =
      MulAut.conj (MulAut.conj (s i)) (outAct L eQ a) := by
    intro i a
    rw [map_mul, map_mul, map_inv, outAct_of_mem, hs i]
    rfl
  have hmapJ : J.map (outAct L eQ) = Subgroup.closure (⋃ i, ((A.map (outAct L eQ)).map
      (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
        Subgroup (MulAut (alternatingGroup (Fin 6)))) : Set (MulAut (alternatingGroup (Fin 6)))) := by
    rw [hJ, MonoidHom.map_closure, Set.image_iUnion]
    congr 1
    refine Set.iUnion_congr fun i => ?_
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨outAct L eQ a, ⟨a, ha, rfl⟩, ?_⟩
      exact (hconj i a).symm
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
      exact hconj i a
  have hdec : ∀ x ∈ L, ∃ j ∈ J, ∃ z : L, z ∈ Subgroup.center L ∧ x = j * (z : H) := by
    intro x hx
    have hinner : outAct L eQ x ∈
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range :=
      ⟨eQ (QuotientGroup.mk ⟨x, hx⟩), (outAct_of_mem L eQ ⟨x, hx⟩).symm⟩
    have hin : outAct L eQ x ∈ J.map (outAct L eQ) := by rw [hmapJ]; exact hgen hinner
    obtain ⟨j, hjJ, hjx⟩ := hin
    have hmem : j⁻¹ * x ∈ (Subgroup.center L).map L.subtype :=
      hker _ (by rw [map_mul, map_inv, hjx, inv_mul_cancel])
    obtain ⟨z, hz, hzx⟩ := hmem
    refine ⟨j, hjJ, z, hz, ?_⟩
    have : (z : H) = j⁻¹ * x := hzx
    rw [this]; group
  have hperf : ⁅L, L⁆ = L := by
    have h1 : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) = ⊤ := by
      have := Group.isPerfect_def.1 ‹Group.IsPerfect ↥L›
      rwa [_root_.commutator_def] at this
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ L.subtype
    rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  calc L = ⁅L, L⁆ := hperf.symm
    _ ≤ J := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := hdec x hx
      obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := hdec y hy
      have hz₁c : ∀ g ∈ L, (z₁ : H) * g = g * (z₁ : H) := fun g hg => by
        have := (Subgroup.mem_center_iff.1 hz₁) ⟨g, hg⟩
        exact congrArg Subtype.val this.symm
      have hz₂c : ∀ g ∈ L, (z₂ : H) * g = g * (z₂ : H) := fun g hg => by
        have := (Subgroup.mem_center_iff.1 hz₂) ⟨g, hg⟩
        exact congrArg Subtype.val this.symm
      have hj₁L : j₁ ∈ L := by
        have : j₁ = (j₁ * z₁) * (z₁ : H)⁻¹ := by group
        rw [this]; exact L.mul_mem hx (L.inv_mem z₁.2)
      have hj₂L : j₂ ∈ L := by
        have : j₂ = (j₂ * z₂) * (z₂ : H)⁻¹ := by group
        rw [this]; exact L.mul_mem hy (L.inv_mem z₂.2)
      have h1 : ⁅j₁ * (z₁ : H), j₂ * (z₂ : H)⁆ = ⁅j₁, j₂⁆ := by
        rw [commutator_mul_commute_left _ _ _ (hz₁c _ (L.mul_mem hj₂L z₂.2)),
          commutator_mul_commute_right _ _ _ (hz₂c _ hj₁L)]
      rw [h1]
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)

end Gen

end CFSG.QuasithinUnique.Setup.X3
