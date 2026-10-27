module

public import CFSG.GF2Type.SmithTypeE.LMod.Aut
public import Certificates.Certificate38606

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6

attribute [local irreducible] tvIdxTab tvTab tvImg tvList elemGens

theorem ptTrans_reach :
    CFSG.SmithL6.K.Reach 1953 1953 (· == 0) (fun g u v => tvImg g u == v) :=
  Certificates.certificate38606.1

theorem ptFixCheck_holds : chkPtFix = true :=
  Certificates.certificate38606.2

section Norm

theorem exists_mem_T6_apply_zero {v : Fin 1953} : ∃ g ∈ T6, g 0 = v := by
  have key := ptTrans_reach (fun j => ∃ hj : j < 1953, ∃ g ∈ T6, g 0 = ⟨j, hj⟩) ?_ ?_
    v.val v.2
  · obtain ⟨hj, g, hg, e⟩ := key
    exact ⟨g, hg, by rw [e]⟩
  · intro v _ hv
    have : v = 0 := by simpa using hv
    subst this
    exact ⟨by norm_num, 1, T6.one_mem, rfl⟩
  · intro g hg u _ v hv he ⟨hu', g', hg', hg'e⟩
    refine ⟨hv, tvP ⟨g, hg⟩ * g', T6.mul_mem (tvP_mem _) hg', ?_⟩
    rw [Equiv.Perm.mul_apply, hg'e]
    apply Fin.ext
    rw [tvP_apply]
    exact beq_iff_eq.mp he

theorem exists_mem_T6_apply_eq (a b : Fin 1953) : ∃ g ∈ T6, g a = b := by
  obtain ⟨g, hg, hga⟩ := exists_mem_T6_apply_zero (v := a)
  obtain ⟨h, hh, hhb⟩ := exists_mem_T6_apply_zero (v := b)
  refine ⟨h * g⁻¹, T6.mul_mem hh (T6.inv_mem hg), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hga]
  simpa using hhb

theorem exists_tvP_move {b : Fin 1953} (hb : b ≠ 0) :
    ∃ q : Fin 1953, tvP q 0 = 0 ∧ tvP q b ≠ b := by
  have h := ptFixCheck_holds
  simp only [chkPtFix, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h b.val b.2 with h0 | ⟨q, hq, h1, h2⟩
  · exact absurd (Fin.ext h0) hb
  · refine ⟨⟨q, hq⟩, Fin.ext ?_, fun hh => h2 ?_⟩
    · rw [tvP_apply, ← tvTab_get hq (by norm_num)]
      exact h1
    · rw [tvTab_get hq b.2, ← tvP_apply ⟨q, hq⟩ b]
      exact congrArg Fin.val hh

theorem eq_one_of_commute_T6 {z : Equiv.Perm (Fin 1953)} (hz : ∀ h ∈ T6, z * h = h * z) :
    z = 1 := by
  have hz0 : z 0 = 0 := by
    by_contra hne
    obtain ⟨q, hq0, hqz⟩ := exists_tvP_move hne
    apply hqz
    have h1 := congrArg (fun σ : Equiv.Perm (Fin 1953) => σ 0) (hz _ (tvP_mem q))
    simp only [Equiv.Perm.mul_apply, hq0] at h1
    exact h1.symm
  refine Equiv.ext fun a => ?_
  obtain ⟨h, hh, hha⟩ := exists_mem_T6_apply_eq 0 a
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 1953) => σ 0) (hz h hh)
  simp only [Equiv.Perm.mul_apply, hz0, hha] at h1
  rw [Equiv.Perm.one_apply]
  exact h1

theorem isTvAut_of_mem_normalizer {π : Equiv.Perm (Fin 1953)}
    (hπ : π ∈ Subgroup.normalizer (T6 : Set (Equiv.Perm (Fin 1953)))) : IsTvAut π := by
  have hN := Subgroup.mem_normalizer_iff.1 hπ
  have hN' := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hπ)
  let α : MulAut T6 :=
    { toFun := fun x => ⟨π * x * π⁻¹, (hN x.1).1 x.2⟩
      invFun := fun x => ⟨π⁻¹ * x * π⁻¹⁻¹, (hN' x.1).1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ k : Fin 1953, π * tvP k * π⁻¹ = tvP (autPerm α k) := fun k =>
    congrArg Subtype.val (autPerm_tvP α k)
  have hg' := isTvAut_autPerm α
  have hzgen : ∀ k : Fin 1953, (autPerm α)⁻¹ * π * tvP k = tvP k * ((autPerm α)⁻¹ * π) := by
    intro k
    have h1 : π * tvP k * π⁻¹ = autPerm α * tvP k * (autPerm α)⁻¹ := by
      rw [hα k, hg' k]
    calc (autPerm α)⁻¹ * π * tvP k = (autPerm α)⁻¹ * (π * tvP k * π⁻¹) * π := by group
      _ = (autPerm α)⁻¹ * (autPerm α * tvP k * (autPerm α)⁻¹) * π := by rw [h1]
      _ = tvP k * ((autPerm α)⁻¹ * π) := by group
  have hz : ∀ h ∈ T6, ((autPerm α)⁻¹ * π) * h = h * ((autPerm α)⁻¹ * π) := by
    intro h hh
    change h ∈ Subgroup.closure (Set.range tvP) at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hzgen k
    | one => simp
    | mul x y _ _ hx hy =>
      calc (autPerm α)⁻¹ * π * (x * y) = ((autPerm α)⁻¹ * π * x) * y := by group
        _ = x * ((autPerm α)⁻¹ * π) * y := by rw [hx]
        _ = x * ((autPerm α)⁻¹ * π * y) := by group
        _ = x * (y * ((autPerm α)⁻¹ * π)) := by rw [hy]
        _ = x * y * ((autPerm α)⁻¹ * π) := by group
    | inv x _ hx =>
      calc (autPerm α)⁻¹ * π * x⁻¹ = x⁻¹ * (x * ((autPerm α)⁻¹ * π)) * x⁻¹ := by group
        _ = x⁻¹ * (((autPerm α)⁻¹ * π) * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * ((autPerm α)⁻¹ * π) := by group
  have hz1 := eq_one_of_commute_T6 hz
  have : π = autPerm α := by
    calc π = autPerm α * ((autPerm α)⁻¹ * π) := by group
      _ = autPerm α := by rw [hz1, mul_one]
  rw [this]
  exact hg'

end Norm

end CFSG.GF2Type.SmithTypeE.LMod
