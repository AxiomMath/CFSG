module

public import CFSG.Quasithin.Background.B6Defs
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
import CFSG.Quasithin.Background.E1Amb
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] [Finite G]

theorem twoResidual_inf_centralizer_le_inf {N : Subgroup G} [N.Normal]
    (hGN : IsPGroup 2 (G ⧸ N)) (X : Subgroup G) :
    twoResidual (X ⊓ centralizer (pCoreOf 2 X : Set G)) ≤
      twoResidual (X ⊓ N ⊓ centralizer (pCoreOf 2 (X ⊓ N) : Set G)) := by
  set C := X ⊓ centralizer (pCoreOf 2 X : Set G)
  have hCN : twoResidual C ≤ C ⊓ N := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left (fun c hc => ?_) fun y hy => ?_
    · exact inf_normalizer_le_normalizer_inf
        ⟨le_normalizer hc, by rw [normalizer_eq_top]; exact mem_top c⟩
    · obtain ⟨k, hk⟩ := hGN (y : G ⧸ N)
      exact ⟨k, pow_mem hy _,
        (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hk)⟩
  have hO : pCoreOf 2 (X ⊓ N) ≤ pCoreOf 2 X :=
    pCoreOf_le_pCoreOf_of_le_normalizer 2 inf_le_left fun x hx => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hx, by rw [normalizer_eq_top]; exact mem_top x⟩
  calc twoResidual C = twoResidual (twoResidual C) := (twoResidual_twoResidual C).symm
    _ ≤ _ := E1.twoResidual_mono (hCN.trans (le_inf (inf_le_inf_right N inf_le_left)
      (inf_le_left.trans (inf_le_right.trans (centralizer_le hO)))))

private theorem coord_mem_inf_centralizer {S : Set (Subgroup G)} {N M : Subgroup G}
    (hN : IsDirectProduct S N) (hM : M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B}) {y : G}
    (hy : y ∈ M ⊓ N ⊓ centralizer (pCoreOf 2 (M ⊓ N) : Set G)) {B : Subgroup G} (hB : B ∈ S) :
    ((hN.coord hB ⟨y, hy.1.2⟩ : B) : G) ∈ M ⊓ B ⊓ centralizer (pCoreOf 2 (M ⊓ B) : Set G) := by
  obtain ⟨_, h⟩ := (Near.Thm210.mem_sSup_image_iff hN (T := (M ⊓ ·)) fun _ _ => inf_le_right).mp
    (hM.le hy.1)
  refine ⟨h B hB, mem_centralizer_iff.mpr fun o ho => ?_⟩
  have hoB : o ∈ B := (ASVolI.ChH.pCoreOf_le_self 2 _ ho).2
  have hoN : o ∈ pCoreOf 2 (M ⊓ N) := pCoreOf_le_pCoreOf_of_le_normalizer 2
    (inf_le_inf_left M (hN.le hB)) (fun x hx => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hx.1, hN.le_normalizer hB hx.2⟩) ho
  have h1 := hN.coord_of_mem hB hoB
  have h3 : (⟨o, hN.le hB hoB⟩ : N) = ⟨y, hy.1.2⟩ * ⟨o, hN.le hB hoB⟩ * (⟨y, hy.1.2⟩ : N)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq (mem_centralizer_iff.mp hy.2 o hoN))
  rw [h3, map_mul, map_mul, map_inv] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hN.coord_of_mem hB hoB] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem twoResidual_inf_centralizer_le_sSup {S : Set (Subgroup G)} {N M : Subgroup G}
    (hN : IsDirectProduct S N) (hM : M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B})
    {T : Subgroup G → Subgroup G}
    (hT : ∀ B ∈ S, twoResidual (M ⊓ B ⊓ centralizer (pCoreOf 2 (M ⊓ B) : Set G)) ≤ T B) :
    twoResidual (M ⊓ N ⊓ centralizer (pCoreOf 2 (M ⊓ N) : Set G)) ≤
      sSup {Y | ∃ B ∈ S, Y = T B} := by
  set C := M ⊓ N ⊓ centralizer (pCoreOf 2 (M ⊓ N) : Set G)
  set W := sSup {Y | ∃ B ∈ S, Y = twoResidual (M ⊓ B ⊓ centralizer (pCoreOf 2 (M ⊓ B) : Set G))}
  have hTB : ∀ B ∈ S, twoResidual (M ⊓ B ⊓ centralizer (pCoreOf 2 (M ⊓ B) : Set G)) ≤ B :=
    fun _ _ => (twoResidual_le _).trans (inf_le_left.trans inf_le_right)
  have hconj : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    obtain ⟨hwN, h⟩ := (Near.Thm210.mem_sSup_image_iff hN hTB).mp hw
    have hcN : c ∈ N := hc.1.2
    have hm : c * w * c⁻¹ ∈ N := mul_mem (mul_mem hcN hwN) (inv_mem hcN)
    refine (Near.Thm210.mem_sSup_image_iff hN hTB).mpr ⟨hm, fun B hB => ?_⟩
    have e : (⟨c * w * c⁻¹, hm⟩ : N) = ⟨c, hcN⟩ * ⟨w, hwN⟩ * (⟨c, hcN⟩ : N)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (le_normalizer_twoResidual _
      (coord_mem_inf_centralizer hN hM hc hB)) _).mp (h B hB)
  obtain ⟨k, hk⟩ := B6.exists_uniform_two_pow W
    {x | ∃ B ∈ S, x ∈ M ⊓ B ⊓ centralizer (pCoreOf 2 (M ⊓ B) : Set G)} fun x hx => by
      obtain ⟨B, hB, hx⟩ := hx
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient _ x hx
      exact ⟨k, (le_sSup ⟨B, hB, rfl⟩ : _ ≤ W) hk⟩
  have hCW : twoResidual C ≤ W := by
    refine (twoResidual_le_of_isTwoQuotient (N := C ⊓ W) inf_le_left (fun c hc =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer hc, B6.mem_normalizer_of_forall_mem
        (hconj c hc) fun w hw => by simpa using hconj c⁻¹ (inv_mem hc) w hw⟩)
      fun y hy => ⟨k, pow_mem hy _, ?_⟩).trans inf_le_right
    refine hN.mem_of_coord_mem (pow_mem hy.1.2 _) fun B hB => ?_
    have e : (⟨y ^ 2 ^ k, pow_mem hy.1.2 _⟩ : N) = ⟨y, hy.1.2⟩ ^ 2 ^ k := rfl
    rw [e, map_pow, Subgroup.coe_pow]
    exact hk _ ⟨B, hB, coord_mem_inf_centralizer hN hM hy hB⟩
  refine hCW.trans (sSup_le ?_)
  rintro _ ⟨B, hB, rfl⟩
  exact (hT B hB).trans (le_sSup ⟨B, hB, rfl⟩)

theorem twoResidual_inf_centralizer_map {G' : Type*} [Group G'] [Finite G']
    {f : G →* G'} (hf : Function.Injective f) (X : Subgroup G) :
    twoResidual (X.map f ⊓ centralizer (pCoreOf 2 (X.map f) : Set G')) =
      (twoResidual (X ⊓ centralizer (pCoreOf 2 X : Set G))).map f := by
  rw [E1.map_twoResidual, ASVolI.ChH.pCoreOf_map_of_injective 2 f hf X]
  congr 1
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, mem_centralizer_iff.mpr fun o ho => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hc (f o) (mem_map_of_mem f ho)
  · rintro _ ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem f hx, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨o, ho, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc o ho]

theorem charTwo_iff_twoResidual_eq_bot (X : Subgroup G) :
    CharTwo X ↔ twoResidual (X ⊓ centralizer (pCoreOf 2 X : Set G)) = ⊥ := by
  refine ⟨fun h => eq_bot_iff.mpr (twoResidual_le_of_isTwoQuotient bot_le
    (fun c _ => by rw [normalizer_eq_top]; exact mem_top c) fun y hy => ?_), fun h => ?_⟩
  · obtain ⟨k, hk⟩ := ASVolI.ChH.isPGroup_pCoreOf 2 X ⟨y, h hy⟩
    exact ⟨k, (mem_bot).mpr (by simpa using congrArg Subtype.val hk)⟩
  · refine ASVolI.ChH.le_pCoreOf_of_isPGroup_normal inf_le_left (fun s hs k hk => ?_) fun y => ?_
    · have hkX : k ∈ X := hk.1
      refine mem_inf.mpr ⟨mul_mem (mul_mem hs hkX) (inv_mem hs),
        mem_centralizer_iff.mpr fun o ho => ?_⟩
      have ho' : s⁻¹ * o * s ∈ pCoreOf 2 X := by
        simpa using ASVolI.ChH.pCoreOf_conj_mem (inv_mem hs) ho
      have hc := mem_centralizer_iff.mp hk.2 _ ho'
      calc o * (s * k * s⁻¹) = s * ((s⁻¹ * o * s) * k) * s⁻¹ := by group
        _ = s * (k * (s⁻¹ * o * s)) * s⁻¹ := by rw [hc]
        _ = s * k * s⁻¹ * o := by group
    · obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient _ (y : G) y.2
      rw [h, mem_bot] at hk
      exact ⟨k, Subtype.ext (by simpa using hk)⟩

end CFSG.GroupTheory

end
