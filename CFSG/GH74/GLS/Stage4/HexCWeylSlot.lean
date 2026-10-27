module

public import CFSG.GH74.GLS.Stage4.HexCWeylId
public import CFSG.GH74.GLS.Stage4.HexCAct
public import CFSG.GH74.GLS.Stage4.HexCWeyl

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

section Slot

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)
  {a2 a4 : F → F → F} {L : F → F → G} (hcd : CommData D a2 a4 L)
  {A2 A4 : F → F → F} {g3 : F → F → G} (had : ActData D A2 A4 g3)
  {n : G} (hnφ : n = D.φ (sl2W F)) (hnact : ActsPos 6 root n (fun q => 4 - q))
  {f₁ f₅ f₂ f₄ : F → F} (hf1 : ∀ d, n * D.p1 d * n⁻¹ = D.p5 (f₁ d))
  (hf5 : ∀ d, n * D.p5 d * n⁻¹ = D.p1 (f₅ d)) (hf2 : ∀ d, n * D.p2 d * n⁻¹ = D.p4 (f₂ d))
  (hf4 : ∀ d, n * D.p4 d * n⁻¹ = D.p2 (f₄ d))

include R hC hcd had hnφ hnact hf1 hf5 hf2 hf4 in
theorem weyl_slot (s : F) : f₂ (A2 1 s) + a4 (-s) s = A4 (-1) (-s) := by
  have hu : (D.p6 1)⁻¹ = D.p6 (-1) := by
    have h0 : D.p6 0 = 1 := map_zero_of_add' D.p6_add
    have := D.p6_add 1 (-1)
    rw [add_neg_cancel, h0] at this
    exact inv_eq_of_mul_eq_one_right this.symm
  have hz : n * D.p5 (f₁ s) * n⁻¹ = D.p1 (-s) := by
    rw [← hf1 s]
    have e : n * (n * D.p1 s * n⁻¹) * n⁻¹ = (n * n) * D.p1 s * (n * n)⁻¹ := by group
    rw [e, weyl_sq D hnφ, D.w1 (-1) s]
    simp
  have hy : D.p6 1 * D.p5 (f₁ s) = D.p5 (f₁ s) * D.p6 1 :=
    (hC.c56 _ (D.p5_mem _) _ (D.p6_mem 1)).symm
  have hid := weyl_aux (weyl_BR D hnφ) (hf1 s) hy hz
  have hv : n * g3 1 s * n⁻¹ ∈ root 3 := by
    simpa using weyl_mem hnact (i := 3) (by norm_num) (by norm_num) (had.g3_mem 1 s)
  have hL1 : D.p6 1 * D.p1 s * (D.p6 1)⁻¹ =
      Nel D (A2 1 s) (g3 1 s) (A4 1 s) * D.p5 (1 * s) * D.p1 s := by
    rw [← had.eq 1 s]; simp only [commutatorElement_def]; group
  have hL2 : n * (D.p6 1 * D.p1 s * (D.p6 1)⁻¹) * n⁻¹ =
      Nel D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) * D.p1 (f₅ (1 * s)) * D.p5 (f₁ s) := by
    rw [hL1]
    calc n * (Nel D (A2 1 s) (g3 1 s) (A4 1 s) * D.p5 (1 * s) * D.p1 s) * n⁻¹
        = (n * Nel D (A2 1 s) (g3 1 s) (A4 1 s) * n⁻¹) * (n * D.p5 (1 * s) * n⁻¹) *
          (n * D.p1 s * n⁻¹) := by group
      _ = _ := by rw [weyl_conj_Nel hC D hf2 hf4 _ _ hv, hf5, hf1]
  have hR1 : (D.p6 1)⁻¹ * D.p1 (-s) * D.p6 1 =
      Nel D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) * D.p5 (-1 * -s) * D.p1 (-s) := by
    rw [← had.eq (-1) (-s), ← hu]
    simp only [commutatorElement_def]; group
  have hE := hL2.symm.trans (hid.trans hR1)
  have hVL := Nel_mem D (e := f₄ (A4 1 s)) (f := f₂ (A2 1 s)) hv
  have hVR := Nel_mem D (e := A2 (-1) (-s)) (f := A4 (-1) (-s)) (had.g3_mem (-1) (-s))
  have hK : ⁅D.p1 (-s), D.p5 (-1 * -s)⁆ ∈ Vsub root 2 4 := by
    rw [hcd.eq]; exact Nel_mem D (hcd.L_mem _ _)
  obtain ⟨ha, hb⟩ := weyl_cmp R D hVL hVR hK hE
  rw [ha, hb] at hE
  have hcm : Nel D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) *
      ⁅D.p1 (-s), D.p5 (-1 * -s)⁆ =
      Nel D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) := by
    calc _ = (Nel D (f₄ (A4 1 s)) (n * g3 1 s * n⁻¹) (f₂ (A2 1 s)) * D.p1 (-s) *
          D.p5 (-1 * -s)) * (D.p1 (-s))⁻¹ * (D.p5 (-1 * -s))⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (Nel D (A2 (-1) (-s)) (g3 (-1) (-s)) (A4 (-1) (-s)) * D.p5 (-1 * -s) * D.p1 (-s)) *
          (D.p1 (-s))⁻¹ * (D.p5 (-1 * -s))⁻¹ := by rw [hE]
      _ = _ := by group
  have eqc : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  rw [eqc, Nel_mul hC D hv (hcd.L_mem _ _)] at hcm
  have key := Nel_inj R D ((root 3).mul_mem hv (hcd.L_mem _ _)) (had.g3_mem _ _) hcm
  have h4 := key.2.2
  have hb' : (-1 : F) * -s = s := by ring
  rw [hb'] at h4
  exact h4

end Slot

end CFSG.GH74.GLS.Stage4.Hex
