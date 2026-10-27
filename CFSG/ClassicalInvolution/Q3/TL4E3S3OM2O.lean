module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2P
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2C
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C
open CFSG.ClassicalInvolution.Q3.TL4.E4O8

namespace E3S3O

theorem sig_mem_autT {s : Equiv.Perm (Fin 360)} (hs : s ∈ sig) : s ∈ autT := by
  have h8 := gen_mem_autT (i := 8) (by norm_num)
  have h9 := gen_mem_autT (i := 9) (by norm_num)
  simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact autT.one_mem
  · exact h8
  · exact autT.mul_mem h8 h8
  · exact h9
  · exact autT.mul_mem h9 h8
  · exact autT.mul_mem h9 (autT.mul_mem h8 h8)


theorem sig_comm {s : Equiv.Perm (Fin 360)} (hs : s ∈ sig) : s * mainPerm 0 = mainPerm 0 * s := by
  obtain ⟨c8, c9⟩ := gen_comm_x0
  have hmul : ∀ a b : Equiv.Perm (Fin 360), a * mainPerm 0 = mainPerm 0 * a →
      b * mainPerm 0 = mainPerm 0 * b → a * b * mainPerm 0 = mainPerm 0 * (a * b) :=
    fun a b ha hb => by rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  simp only [sig, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact c8
  · exact hmul _ _ c8 c8
  · exact c9
  · exact hmul _ _ c9 c8
  · exact hmul _ _ c9 (hmul _ _ c8 c8)


theorem e4SigmaFix_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4SigmaFix M := by
  intro A B r x hd hB hBA hx2 hfixA hact
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  obtain ⟨φ, hφ, hrange, hAφ⟩ := E4O8.exists_emb e hd
  have hmem : ∀ m, φ m ∈ omegaT := fun m => hrange ▸ ⟨m, rfl⟩
  let e' : M ≃* ↥omegaT := MulEquiv.ofBijective (φ.codRestrict omegaT hmem)
    ⟨fun a b hab => hφ (congrArg Subtype.val hab), fun z => by
      obtain ⟨m, hm⟩ : (z : Equiv.Perm (Fin 360)) ∈ φ.range := by rw [hrange]; exact z.2
      exact ⟨m, Subtype.ext hm⟩⟩
  set a : ↥autT := autEquiv.symm ((MulAut.congr e') x) with hadef
  set y : Equiv.Perm (Fin 360) := (a : Equiv.Perm (Fin 360)) with hydef
  have hyA : y ∈ autT := a.2
  have ha : autEquiv a = MulAut.congr e' x := MulEquiv.apply_symm_apply _ _
  have hy : ∀ m, y * φ m * y⁻¹ = φ (x m) := by
    intro m
    have h1 := autEquiv_apply a (e' m)
    have h2 : (MulAut.congr e' x) (e' m) = e' (x m) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [ha, h2] at h1
    exact h1.symm
  have hy2 : y * y = 1 := by
    have h1 : a * a = 1 := by
      rw [hadef, ← map_mul, ← map_mul, hx2, map_one, map_one]
    exact congrArg Subtype.val h1
  have hyK : ∀ z ∈ K0, y * z = z * y := by
    intro z hz
    rw [← hAφ] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have h1 := hy a
    rw [hfixA a ha] at h1
    calc y * φ a = y * φ a * y⁻¹ * y := by group
      _ = φ a * y := by rw [h1]
  have hr : φ r = mainPerm 0 :=
    eq_x0_of_isUniqueInvolution (hAφ ▸ Vtx.isUniqueInvolution_map φ hφ hd.inv)
  have hu0 : u0 ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hv0 : v0 ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hyx : y * mainPerm 0 = mainPerm 0 * y :=
    hyK _ (by rw [← hr, ← hAφ]; exact Subgroup.mem_map_of_mem φ hd.inv.mem)
  obtain ⟨ω, hω, s, hs, hys⟩ := exists_sig hyA
  have hsx := sig_comm hs
  have hcx : s⁻¹ * y ∈ centralizerIn omegaT (mainPerm 0) := by
    refine mem_centralizerIn.2 ⟨?_, ?_⟩
    · have h1 := (conj_mem_omegaT (autT.inv_mem (sig_mem_autT hs))).1 hω
      rwa [inv_inv, show s⁻¹ * ω * s = s⁻¹ * (ω * s) by group, ← hys] at h1
    · have hsx' : s⁻¹ * mainPerm 0 = mainPerm 0 * s⁻¹ := by
        calc s⁻¹ * mainPerm 0 = s⁻¹ * (mainPerm 0 * s) * s⁻¹ := by group
          _ = s⁻¹ * (s * mainPerm 0) * s⁻¹ := by rw [hsx]
          _ = mainPerm 0 * s⁻¹ := by group
      calc s⁻¹ * y * mainPerm 0 = s⁻¹ * (y * mainPerm 0) := by group
        _ = s⁻¹ * (mainPerm 0 * y) := by rw [hyx]
        _ = s⁻¹ * mainPerm 0 * y := by group
        _ = mainPerm 0 * s⁻¹ * y := by rw [hsx']
        _ = mainPerm 0 * (s⁻¹ * y) := by group
  obtain ⟨q, hq, rfl⟩ := hB
  have hBφ : (conjSub q A).map φ = conjSub (φ q) K0 := by rw [AscQuot.map_conjSub, hAφ]
  have hqx : φ q * mainPerm 0 = mainPerm 0 * φ q := by
    rw [← hr, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hq]
  have hne : conjSub (φ q) K0 ≠ K0 := fun h1 => hBA (by
    apply Subgroup.map_injective hφ
    rw [hBφ, h1, hAφ])
  obtain ⟨w, hwB, -, hwact⟩ := hact
  have hact' : ∀ b ∈ conjSub (φ q) K0, y * b * y⁻¹ = φ w * b * (φ w)⁻¹ := by
    intro b hb
    rw [← hBφ] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    rw [hy b₀, hwact b₀ hb₀, map_mul, map_mul, map_inv]
  obtain ⟨d, hdO, hdx, hdne, hdy⟩ := sg_model hs (mem_centralizerIn.1 hcx).1 (hyK _ hu0)
    (hyK _ hv0) hy2 (hmem q) hqx hne (by rw [← hBφ]; exact Subgroup.mem_map_of_mem φ hwB) hact'
  obtain ⟨q', hq'⟩ : d ∈ φ.range := hrange ▸ hdO
  have hCφ : (conjSub q' A).map φ = conjSub d K0 := by rw [AscQuot.map_conjSub, hAφ, hq']
  refine ⟨conjSub q' A, ⟨q', ?_, rfl⟩, fun h1 => ?_, fun z hz => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ
    rw [map_mul, map_mul, hq', hr, hdx]
  · apply hdne
    rw [← hCφ, h1, hAφ]
  · apply hφ
    have h1 := hy z
    rw [← h1, hdy (φ z) (hCφ ▸ Subgroup.mem_map_of_mem φ hz), mul_inv_cancel_right]

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
