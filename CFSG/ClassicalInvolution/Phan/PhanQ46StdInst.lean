module

public import CFSG.ClassicalInvolution.Phan.PhanQ45StdSolid

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

section Gen

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))}
  {e' : Fin 3 → Fin 4} {ψ : Su K p f 4 →* spinGroup (quadPlus 4 F)}

theorem ChainCtx.psi_comm (C : ChainCtx S e' ψ) (JF : V8 F → V8 F)
    (hblk : ∀ (j : Fin 3) (A : Su K p f 2) (v : V8 F),
      JF (spinAction (quadPlus 4 F) (ψ (blockEmb2 K p f 3 j A)) v) =
        spinAction (quadPlus 4 F) (ψ (blockEmb2 K p f 3 j A)) (JF v))
    (h : Su K p f 4) (v : V8 F) :
    JF (spinAction (quadPlus 4 F) (ψ h) v) = spinAction (quadPlus 4 F) (ψ h) (JF v) := by
  let H : Subgroup (Su K p f 4) :=
    { carrier := {h | ∀ v, JF (spinAction (quadPlus 4 F) (ψ h) v) =
        spinAction (quadPlus 4 F) (ψ h) (JF v)}
      mul_mem' := fun {a b} ha hb v => by
        simp only [map_mul, LinearEquiv.mul_apply]
        rw [ha, hb]
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        have h1 := ha (spinAction (quadPlus 4 F) (ψ a⁻¹) v)
        have e1 : spinAction (quadPlus 4 F) (ψ a) (spinAction (quadPlus 4 F) (ψ a⁻¹) v) = v := by
          rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel]
          simp
        rw [e1] at h1
        have h2 := congrArg (spinAction (quadPlus 4 F) (ψ a⁻¹)) h1
        rw [← LinearEquiv.mul_apply (spinAction (quadPlus 4 F) (ψ a⁻¹))
          (spinAction (quadPlus 4 F) (ψ a)), ← map_mul, ← map_mul, inv_mul_cancel] at h2
        simpa using h2.symm }
  have hblocks : ∀ j : Fin 3, (blockEmb2 K p f 3 j).range ≤ H := by
    rintro j _ ⟨A, rfl⟩
    exact hblk j A
  have htorus : torus (unitaryInvolution K p f) 4 ≤ H := by
    intro t ht
    obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 3).surjective ⟨t, ht⟩
    have hts : t = ((torusEquiv (unitaryInvolution K p f) 3 s : torus (unitaryInvolution K p f) 4) :
        Su K p f 4) := by rw [hs]
    have hs3 : s = Pi.mulSingle 0 (s 0) * Pi.mulSingle 1 (s 1) * Pi.mulSingle 2 (s 2) := by
      ext i
      fin_cases i <;> simp
    rw [hts, hs3]
    simp only [map_mul, Subgroup.coe_mul, coe_torusEquiv_mulSingle]
    exact H.mul_mem (H.mul_mem (hblocks 0 ⟨_, rfl⟩) (hblocks 1 ⟨_, rfl⟩)) (hblocks 2 ⟨_, rfl⟩)
  have hpar : parabolic K p f 3 Set.univ ≤ H := by
    refine sup_le htorus (iSup₂_le fun j _ => hblocks j)
  have hmem : h ∈ parabolic K p f 3 Set.univ := by
    rw [mem_parabolic_iff C.hK]
    obtain ⟨γ, hγ, hend⟩ := frameSystem_connected C.hσ C.hK (by have := C.hq; omega)
      (stdFrame (unitaryInvolution K p f) 4) (h • stdFrame (unitaryInvolution K p f) 4)
    exact ⟨γ, hγ, fun _ _ => trivial, hend⟩
  exact hpar hmem v

end Gen

section Nodes

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} (hS : ModelSpec S ε hε h4)

include hS in
theorem jG_comm_range {k : Fin 4} (hk : k = 0 ∨ k = 1 ∨ k = 2)
    {r : spinGroup (quadPlus 4 F)} (hr : r ∈ (S.ι k).range) (v : V8 F) :
    jG ε (spinAction (quadPlus 4 F) r v) = spinAction (quadPlus 4 F) r (jG ε v) := by
  have hmem : spinAction (quadPlus 4 F) r ∈ (stdFrames ε hε h4 k).La.range := by
    rw [← hS.map_range k]
    exact ⟨r, hr, rfl⟩
  obtain ⟨M, hM⟩ := hmem
  rw [← hM]
  rcases hk with rfl | rfl | rfl
  · exact jG_La_comm_of_incl hε (frame0 (F := F)) (jG_incl_frame0 ε) M v
  · exact jG_La_comm_of_incl hε (frame1 ε hε h4) (jG_incl_frame1 ε hε h4) M v
  · exact jG_La_comm_of_incl hε (frame2 (F := F)) (jG_incl_frame2 ε) M v

include hS in
theorem jH_comm_range {k : Fin 4} (hk : k = 0 ∨ k = 1 ∨ k = 3)
    {r : spinGroup (quadPlus 4 F)} (hr : r ∈ (S.ι k).range) (v : V8 F) :
    jH ε (spinAction (quadPlus 4 F) r v) = spinAction (quadPlus 4 F) r (jH ε v) := by
  have hmem : spinAction (quadPlus 4 F) r ∈ (stdFrames ε hε h4 k).La.range := by
    rw [← hS.map_range k]
    exact ⟨r, hr, rfl⟩
  obtain ⟨M, hM⟩ := hmem
  rw [← hM]
  rcases hk with rfl | rfl | rfl
  · exact jH_La_comm_of_incl hε (frame0 (F := F)) (jH_incl_frame0 ε) M v
  · exact jH_La_comm_of_incl hε (frame1 ε hε h4) (jH_incl_frame1 ε hε h4) M v
  · exact jH_La_comm_of_incl_Pm hε (frame2 (F := F)).swap (jH_incl_frame3 ε) M v

end Nodes

section Inst

variable {p e : ℕ} [Fact p.Prime] (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  (D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε)

include hp2 hq in
theorem exists_stdSolid_G :
    ∃ ψ : Su (GaloisField p (2 * e)) p e 4 →* spinGroup (quadPlus 4 (GaloisField p e)),
      StdSolid M D ![0, 1, 2] ψ 3 (jGK (GaloisField p (2 * e)) M.ε) (jG M.ε) := by
  have hK := StdModel.card_K hq
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨ψ, hch⟩ := exists_chain_012 hK hq (S := M.S) M.good
  have C : ChainCtx M.S ![0, 1, 2] ψ := ⟨hK, hq, M.good, h2K, rfl, hch⟩
  refine ⟨ψ, C, by decide, fun A B => M.S.comm 3 0 (by decide) (by decide) (by decide) A B,
    fun A B => M.S.comm 3 2 (by decide) (by decide) (by decide) A B, ?_,
    commuteTypes_phan hK (by decide) (by decide) (by decide), ?_, phanJK_jGK D, jGK_extV _ _,
    fun x => jG_jG _ x, ?_, ?_⟩
  · ext x
    simp [or_comm]
  · left
    ext x
    simp
    tauto
  · intro h v
    refine C.psi_comm (jG M.ε) (fun j A v => ?_) h v
    obtain ⟨B, hB⟩ := hch.le_range j A
    refine jG_comm_range M.spec ?_ ⟨B, hB⟩ v
    fin_cases j <;> simp
  · rw [z0_x_eq, z0_y_eq, jG_incl_frame0, one_mul]

include hp2 hq in
theorem exists_stdSolid_H :
    ∃ ψ : Su (GaloisField p (2 * e)) p e 4 →* spinGroup (quadPlus 4 (GaloisField p e)),
      StdSolid M D ![0, 1, 3] ψ 2 (jHK (GaloisField p (2 * e)) M.ε) (jH M.ε) := by
  have hK := StdModel.card_K hq
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨ψ, hch⟩ := exists_chain_013 hK hq (S := M.S) M.good
  have C : ChainCtx M.S ![0, 1, 3] ψ := ⟨hK, hq, M.good, h2K, rfl, hch⟩
  refine ⟨ψ, C, by decide, fun A B => M.S.comm 2 0 (by decide) (by decide) (by decide) A B,
    fun A B => M.S.comm 2 3 (by decide) (by decide) (by decide) A B, ?_,
    commuteTypes_phan hK (by decide) (by decide) (by decide), ?_, phanJK_jHK D, jHK_extV _ _,
    fun x => jH_jH _ x, ?_, ?_⟩
  · ext x
    simp
  · right
    ext x
    simp
    tauto
  · intro h v
    refine C.psi_comm (jH M.ε) (fun j A v => ?_) h v
    obtain ⟨B, hB⟩ := hch.le_range j A
    refine jH_comm_range M.spec ?_ ⟨B, hB⟩ v
    fin_cases j <;> simp
  · rw [z0_x_eq, z0_y_eq, jH_incl_frame0, one_mul]

end Inst

end CFSG.ClassicalInvolution.PhanQ
