module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Class
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnH90
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnPerX
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg2
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false

section Commute

variable {L : Type} [Field L]

theorem ell_diagramMap_commute_xUnit_two (c : L) :
    diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 2 c =
      xUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L := by
  have h := twistHom_xUnit TwistTag.D4 L (RingHom.id L) 2 c
  rw [twistHom_id_eq, RingHom.id_apply] at h
  rw [← mul_inv_eq_iff_eq_mul, h]
  rfl

theorem ell_diagramMap_commute_yUnit_two (c : L) :
    diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 2 c =
      yUnit TwistTag.D4.tag L 2 c * diagramMap TwistTag.D4 L := by
  have h := twistHom_yUnit TwistTag.D4 L (RingHom.id L) 2 c
  rw [twistHom_id_eq, RingHom.id_apply] at h
  rw [← mul_inv_eq_iff_eq_mul, h]
  rfl

theorem rootSubgroup_two_le_centralizer {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : β = Pi.single 2 1 ∨ β = -Pi.single 2 1) :
    rootSubgroup TwistTag.D4.tag L β ≤ Subgroup.centralizer {diagramMap TwistTag.D4 L} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hβ with rfl | rfl
  · rw [pinnedX_single]
    exact (ell_diagramMap_commute_xUnit_two c).symm
  · rw [pinnedX_neg_single]
    exact (ell_diagramMap_commute_yUnit_two c).symm

theorem d4LongA2_eq_smul {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : γ ∈ d4LongA2) :
    ∃ v ∈ relWeylTwist TwistTag.D4, ∃ β : Fin TwistTag.D4.tag.rank → ℤ,
      (β = Pi.single 2 1 ∨ β = -Pi.single 2 1) ∧ γ = v • β := by
  have h0 := TwistTag.D4.orbitReflection_mem (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
  have h1 := TwistTag.D4.orbitReflection_mem (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
  have e0 : ∀ x, TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) • x =
      d4MatShort *ᵥ x := d4_orbitReflection_zero_smul
  have e1 : ∀ x, TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) • x =
      d4MatLong *ᵥ x := d4_orbitReflection_one_smul
  rw [d4LongA2_eq] at hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, Pi.single 2 1, Or.inl rfl, by rw [one_smul]; funext i; fin_cases i <;> rfl⟩
  · refine ⟨_, h0, Pi.single 2 1, Or.inl rfl, ?_⟩
    rw [e0]
    decide +kernel
  · refine ⟨_, mul_mem h1 h0, Pi.single 2 1, Or.inl rfl, ?_⟩
    rw [mul_smul, e0, e1]
    decide +kernel
  · exact ⟨1, one_mem _, -Pi.single 2 1, Or.inr rfl, by rw [one_smul]; funext i; fin_cases i <;> rfl⟩
  · refine ⟨_, h0, -Pi.single 2 1, Or.inr rfl, ?_⟩
    rw [e0]
    decide +kernel
  · refine ⟨_, mul_mem h1 h0, -Pi.single 2 1, Or.inr rfl, ?_⟩
    rw [mul_smul, e0, e1]
    decide +kernel

theorem rootSpan_d4LongA2_le_centralizer_P :
    rootSpan TwistTag.D4.tag L d4LongA2 ≤ Subgroup.centralizer {diagramMap TwistTag.D4 L} := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨v, hv, β, hβ, rfl⟩ := d4LongA2_eq_smul hγ
  have hroot : IsRoot TwistTag.D4.tag β := by
    rcases hβ with rfl | rfl
    · exact isRoot_single _ _
    · exact IsRoot.neg (isRoot_single _ _)
  rw [← map_conj_rootSubgroup (L := L) v hroot]
  rintro _ ⟨y, hy, rfl⟩
  have hy' := rootSubgroup_two_le_centralizer (L := L) hβ hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy'
  have hn : Commute (diagramMap TwistTag.D4 L)
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L v) := diagramMap_comm_canonicalRep hv
  have hy'' : Commute y (diagramMap TwistTag.D4 L) := hy'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hn.symm.mul_left hy'').mul_left hn.symm.inv_left

theorem diagramMap_commute_of_mem_rootSpan {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    diagramMap TwistTag.D4 L * g = g * diagramMap TwistTag.D4 L :=
  (Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_d4LongA2_le_centralizer_P hg)).symm

end Commute

section Levi

variable {L : Type} [Field L]

theorem torus_conj_mem_rootSpan {t q : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L) (hq : q ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    t * q * t⁻¹ ∈ rootSpan TwistTag.D4.tag L d4LongA2 := by
  have h := map_conj_rootSpan_of_mem_monomialSubgroup (torusGroup_le_monomialSubgroup ht)
    (S := d4LongA2) (fun _ h => d4LongA2_isRoot h)
  have hmem : t * q * t⁻¹ ∈ (rootSpan TwistTag.D4.tag L d4LongA2).map
      (MulAut.conj t).toMonoidHom := ⟨q, hq, by simp [MulAut.conj_apply]⟩
  rw [h, mp_image_torus ht] at hmem
  simpa using hmem

variable (L) in
def leviGroup : Subgroup (ModGL TwistTag.D4.tag L) where
  carrier := {g | ∃ t ∈ torusGroup TwistTag.D4.tag L, ∃ q ∈ rootSpan TwistTag.D4.tag L d4LongA2,
    g = t * q}
  mul_mem' := by
    rintro _ _ ⟨t₁, ht₁, q₁, hq₁, rfl⟩ ⟨t₂, ht₂, q₂, hq₂, rfl⟩
    refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, (t₂⁻¹ * q₁ * t₂) * q₂,
      mul_mem ?_ hq₂, by group⟩
    simpa using torus_conj_mem_rootSpan (inv_mem ht₂) hq₁
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro _ ⟨t, ht, q, hq, rfl⟩
    refine ⟨t⁻¹, inv_mem ht, t * q⁻¹ * t⁻¹, torus_conj_mem_rootSpan ht (inv_mem hq), by group⟩

theorem mem_leviGroup {g : ModGL TwistTag.D4.tag L} :
    g ∈ leviGroup L ↔ ∃ t ∈ torusGroup TwistTag.D4.tag L,
      ∃ q ∈ rootSpan TwistTag.D4.tag L d4LongA2, g = t * q := Iff.rfl

theorem torus_le_leviGroup {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    t ∈ leviGroup L := ⟨t, ht, 1, one_mem _, (mul_one t).symm⟩

theorem rootSpan_le_leviGroup {q : ModGL TwistTag.D4.tag L}
    (hq : q ∈ rootSpan TwistTag.D4.tag L d4LongA2) : q ∈ leviGroup L :=
  ⟨1, one_mem _, q, hq, (one_mul q).symm⟩

end Levi

section Torus

variable {L : Type} [Field L] [IsAlgClosed L]

theorem permLattice_d4_eq (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm x = d4PermMat *ᵥ x := by
  have h1 := permLattice_symm_permLattice TwistTag.D4.perm x
  rw [permLattice_symm_d4_eq] at h1
  calc permLattice TwistTag.D4.perm x =
      (d4PermMat * d4PermInvMat) *ᵥ permLattice TwistTag.D4.perm x := by
        rw [d4PermMat_mul, Matrix.one_mulVec]
    _ = d4PermMat *ᵥ x := by rw [← Matrix.mulVec_mulVec, h1]

theorem conj_rootDiagUnit_of_weyl {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) {v : WeylGroup TwistTag.D4.tag}
    (hv : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = v)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    n * rootDiagUnit TwistTag.D4.tag a * n⁻¹ = rootDiagUnit TwistTag.D4.tag (weylTuple v a) := by
  set c := canonicalRep (coxeterSystem TwistTag.D4.tag) L v with hc
  have hh : c * n⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    canonicalRep_mul_inv_mem_torusGroup hn v hv
  have hh' : n * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    simpa using inv_mem hh
  have hcy : c * rootDiagUnit TwistTag.D4.tag a * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    rw [hc, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm := torusGroup_comm hh' hcy
  calc n * rootDiagUnit TwistTag.D4.tag a * n⁻¹ =
        (n * c⁻¹) * (c * rootDiagUnit TwistTag.D4.tag a * c⁻¹) * (n * c⁻¹)⁻¹ := by group
    _ = c * rootDiagUnit TwistTag.D4.tag a * c⁻¹ := by rw [hcomm, mul_inv_cancel_right]
    _ = _ := canonicalRep_conj_rootDiagUnit v a

theorem torus_normalize {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) {Mi : D4Mat}
    (hMi : ∀ x, (weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩)⁻¹ • x = Mi *ᵥ x)
    (hdet : (d4PermMat * Mi - 1 : D4Mat).det ≠ 0) {k : ModGL TwistTag.D4.tag L}
    (hk : k ∈ torusGroup TwistTag.D4.tag L) :
    ∃ u ∈ torusGroup TwistTag.D4.tag L,
      u * (k * n * (diagramMap TwistTag.D4 L)⁻¹) * u⁻¹ = n * (diagramMap TwistTag.D4 L)⁻¹ := by
  obtain ⟨κ, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  obtain ⟨a, ha⟩ := exists_tuple_of_char_eq (d4PermMat * Mi - 1) 1 hdet κ
  refine ⟨rootDiagUnit TwistTag.D4.tag a, rootDiagUnit_mem_torusGroup a, ?_⟩
  have hchar : ∀ u, rootChar (weylTuple (weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩)
      (fun i => a (TwistTag.D4.perm i))) u = rootChar (a * κ) u := fun u => by
    rw [rootChar_weylTuple, hMi, ← rootChar_permLattice a TwistTag.D4.perm, permLattice_d4_eq,
      CTTorus.rootChar_mul]
    have h := ha u
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, rootChar_sub,
      mul_inv_eq_iff_eq_mul] at h
    rw [h, mul_comm]
  have htup : weylTuple (weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩)
      (fun i => a (TwistTag.D4.perm i)) = a * κ := by
    funext i
    have := hchar (Pi.single i 1)
    rwa [CTTorus.rootChar_single, CTTorus.rootChar_single] at this
  have key : rootDiagUnit TwistTag.D4.tag a * rootDiagUnit TwistTag.D4.tag κ =
      n * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag a *
        diagramMap TwistTag.D4 L) * n⁻¹ := by
    rw [d4Minus_h90_conj, conj_rootDiagUnit_of_weyl hn rfl, htup, rootDiagUnit_mul]
  calc rootDiagUnit TwistTag.D4.tag a * (rootDiagUnit TwistTag.D4.tag κ * n *
        (diagramMap TwistTag.D4 L)⁻¹) * (rootDiagUnit TwistTag.D4.tag a)⁻¹
      = (rootDiagUnit TwistTag.D4.tag a * rootDiagUnit TwistTag.D4.tag κ) * n *
        (diagramMap TwistTag.D4 L)⁻¹ * (rootDiagUnit TwistTag.D4.tag a)⁻¹ := by group
    _ = (n * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag a *
        diagramMap TwistTag.D4 L) * n⁻¹) * n * (diagramMap TwistTag.D4 L)⁻¹ *
        (rootDiagUnit TwistTag.D4.tag a)⁻¹ := by rw [key]
    _ = n * (diagramMap TwistTag.D4 L)⁻¹ := by group

end Torus

end CFSG.HardMathSupport.Lang.E6Descent
