module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Z
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Mem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Beta
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Frat

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThinPf13

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem sum_indicator_emb4 {n : ℕ} (α β : Finset (Fin n)) (h : α.card = 4) :
    ∑ i, (if emb α h i ∈ β then (1 : ZMod 2) else 0) = ((α ∩ β).card : ZMod 2) := by
  classical
  have h1 : ∑ i, (if emb α h i ∈ β then (1 : ZMod 2) else 0) =
      ∑ x ∈ α, (if x ∈ β then (1 : ZMod 2) else 0) := by
    have himg : (Finset.univ.image (emb α h)) = α := by
      have := Finset.image_orderEmbOfFin_univ α h
      exact this
    have h2 := Finset.sum_image (f := fun x => if x ∈ β then (1 : ZMod 2) else 0)
      (s := (Finset.univ : Finset (Fin 4))) (g := emb α h)
      (fun a _ b _ hab => (emb α h).injective hab)
    rw [himg] at h2
    exact h2.symm
  rw [h1, Finset.sum_boole, Finset.filter_mem_eq_inter]

end TwinThinPf13

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem hz' : IsUniqueInvolution K' z := by
  obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
  have : z' = z := (S.hz.eq hz'K).symm
  rw [this] at hz'K'
  exact hz'K'

theorem zfam_comm_z {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {L : Subgroup G}
    (hL : L ∈ fam K (conjSub g (piGen π))) {u : G} (hu : IsUniqueInvolution L u) :
    u * z = z * u := by
  classical
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  obtain ⟨β, hβ, c, hlabL⟩ := J.label L hL
  have hux : u ∈ pSpan (fam K (conjSub g (piGen π))) := le_pSpan hL hu.mem
  have hX' : u ∈ conjSub g (piGen π) := by rw [← S.fam_gen]; exact hux
  have e1 := J.map_eq_zBar hm hL (S.card8 L (S.fam_mem hL)) hlabL hu
  have hKu : conjSub u K ∈ fam K (conjSub g (piGen π)) := fam_inv K S.mem_fam_self u hX'
  have hmap := S.map_conj_member J ⟨u, hux⟩ K
  rw [hlab, e1] at hmap
  have hzb : AE.zBar β hβ = AE.mkQ m (ofVec (fun i => if i ∈ β then (1 : ZMod 2) else 0)) := by
    show AE.mkQ m (zOf (emb β hβ)) = _
    rw [TL4.Mdl117.zOf_emb_eq β hβ]; rfl
  rw [hzb] at hmap
  have hsum := TwinThinPf13.sum_indicator_emb4 α β h
  have hKu_lab : ((conjSub u K).subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      AE.memBar α h b ∨ ((conjSub u K).subgroupOf
        (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b) := by
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) ((α ∩ β).card : ZMod 2) with h0 | h1
    · left
      rw [hmap]
      exact TwinThinPf10.conj_memBar_vec_even hm α h b (fun i => if i ∈ β then (1 : ZMod 2) else 0)
        (by show ∑ i, (if emb α h i ∈ β then (1 : ZMod 2) else 0) = 0; rw [hsum, h0])
    · right
      rw [hmap]
      exact TwinThinPf10.conj_memBar_vec_odd hm α h b (fun i => if i ∈ β then (1 : ZMod 2) else 0)
        (by show ∑ i, (if emb α h i ∈ β then (1 : ZMod 2) else 0) = 1; rw [hsum, h1])
  have hlab' := S.map_twin_eq hm hm8 J hlab
  have hcases : conjSub u K = K ∨ conjSub u K = K' := by
    rcases hKu_lab with h0 | h1
    · left
      exact S.eq_of_map_le hm J hKu S.mem_fam_self (le_of_eq (h0.trans hlab.symm))
    · right
      exact S.eq_of_map_le hm J hKu S.twin_mem_fam (le_of_eq (h1.trans hlab'.symm))
  have hcz : u * z * u⁻¹ = z := by
    have hconj := S.hz.conj u
    rcases hcases with h0 | h1
    · rw [h0] at hconj
      exact (S.hz.eq hconj).symm
    · rw [h1] at hconj
      exact (S.hz'.eq hconj).symm
  calc u * z = (u * z * u⁻¹) * u := by group
    _ = z * u := by rw [hcz]

theorem zfam_comm {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ fam K (conjSub g (piGen π))) (h₂ : L₂ ∈ fam K (conjSub g (piGen π)))
    {u₁ u₂ : G} (hu₁ : IsUniqueInvolution L₁ u₁) (hu₂ : IsUniqueInvolution L₂ u₂) :
    u₁ * u₂ = u₂ * u₁ := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := h₁
  obtain ⟨⟨b, hb⟩, rfl⟩ := h₂
  have e1 : a * z * a⁻¹ = u₁ := (S.hz.conj a).eq hu₁
  have e2 : b * z * b⁻¹ = u₂ := (S.hz.conj b).eq hu₂
  have hab : a⁻¹ * b ∈ conjSub g (piGen π) :=
    (conjSub g (piGen π)).mul_mem ((conjSub g (piGen π)).inv_mem ha) hb
  have hL : conjSub (a⁻¹ * b) K ∈ fam K (conjSub g (piGen π)) := mem_fam hab
  have hcomm := S.zfam_comm_z hm hm8 J hL ((S.hz.conj (a⁻¹ * b)))
  rw [← e1, ← e2]
  have : (a⁻¹ * b) * z * (a⁻¹ * b)⁻¹ * z = z * ((a⁻¹ * b) * z * (a⁻¹ * b)⁻¹) := hcomm
  calc a * z * a⁻¹ * (b * z * b⁻¹)
      = a * (z * ((a⁻¹ * b) * z * (a⁻¹ * b)⁻¹)) * a⁻¹ := by group
    _ = a * (((a⁻¹ * b) * z * (a⁻¹ * b)⁻¹) * z) * a⁻¹ := by rw [this]
    _ = b * z * b⁻¹ * (a * z * a⁻¹) := by group

theorem Zgrp_fam_comm {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ∀ a ∈ Zgrp (fam K (conjSub g (piGen π))), ∀ b ∈ Zgrp (fam K (conjSub g (piGen π))),
      a * b = b * a := by
  refine closure_comm_of_comm _ ?_
  rintro s ⟨L₁, h₁, hs⟩ t ⟨L₂, h₂, ht⟩
  exact S.zfam_comm hm hm8 J h₁ h₂ hs ht

theorem Zgrp_pi_comm {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ∀ a ∈ Zgrp π, ∀ b ∈ Zgrp π, a * b = b * a := by
  refine closure_comm_of_comm _ ?_
  rintro s ⟨L₁, h₁, hs⟩ t ⟨L₂, h₂, ht⟩
  have hf : ∀ L ∈ π, conjSub g L ∈ fam K (conjSub g (piGen π)) := by
    intro L hL
    have : L ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by rw [S.Q_eq_pi]; exact hL
    obtain ⟨M, hM, rfl⟩ := this
    rwa [conjSub_conjSub_inv]
  have := S.zfam_comm hm hm8 J (hf L₁ h₁) (hf L₂ h₂) (hs.conj g) (ht.conj g)
  calc s * t = g⁻¹ * ((g * s * g⁻¹) * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * t * g⁻¹) * (g * s * g⁻¹)) * g := by rw [this]
    _ = t * s := by group

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
