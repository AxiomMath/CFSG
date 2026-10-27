module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Stab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l77_orderOf_s {t : G} (ht : orderOf t = 2) (g : G) : orderOf (g⁻¹ * t * g) = 2 := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
  simpa [MulAut.conj_apply, ht] using h

theorem sec7l77_exists_b [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∃ b ∈ B, b ≠ 1 ∧ ∀ l ∈ L ⊓ normalizer (B : Set G),
      l * (g⁻¹ * t * g) = (g⁻¹ * t * g) * l → l * b = b * l := by
  have hctx := hc.ctx
  have hL := hctx.isOm6P
  have hPsyl := hctx.isSylow2Of_inf h36
  have hBL : B ≤ L := sec7l77_B_le_L hc
  rcases hc.choice with hA | ⟨-, hscent, ⟨α, hα⟩, n, hnN, hn⟩
  ·
    have hzB : z ∈ B := hP.center_le G L hL (S ⊓ L) hPsyl B hc.normalE16 hctx.z_mem_centerIn
    have hz1 : z ≠ 1 := by
      intro hz1
      apply hc.s_ne
      rw [hA, hz1, mul_one]
    refine ⟨z, hzB, hz1, fun l hl hls => ?_⟩
    have hlt : l * t = t * l :=
      Subgroup.mem_centralizer_singleton_iff.mp (hctx.le_centralizer hl.1)
    rw [hA] at hls
    have key : t * (l * z) = t * (z * l) :=
      calc t * (l * z) = (t * l) * z := by group
        _ = (l * t) * z := by rw [hlt]
        _ = l * (t * z) := by group
        _ = (t * z) * l := hls
        _ = t * (z * l) := by group
    exact mul_left_cancel key
  ·
    set s := g⁻¹ * t * g with hs
    have hsCt : s ∈ centralizer ({t} : Set G) := hctx.sylow.1 hc.s_mem
    have hsN : s ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 s hsCt
    have hsB : ∀ b ∈ B, s * b = b * s := fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hscent b (hc.normalE16.1 hb)).symm
    have hs2 : orderOf s = 2 := sec7l77_orderOf_s hctx.involution g
    rcases hP.cent_B G L hL (S ⊓ L) hPsyl B hc.normalE16 s hsN hsB with
      ⟨b, hb, hbc⟩ | ⟨b, hb, -, hcent⟩
    · exfalso
      have hbs : b * (s * b⁻¹) = s := by
        rw [Subgroup.mem_centralizer_iff.mp hbc b (hBL hb)]
        group
      have hinner : InnerOn L s := by
        change s ∈ L ⊔ centralizer (L : Set G)
        rw [← hbs]
        exact Subgroup.mul_mem_sup (hBL hb) hbc
      exact sec79_not_inner_of_i1 hP hL hs2 hsN ⟨α, hα⟩ hinner
    · have hb1 : b ≠ 1 := by
        rintro rfl
        apply hn
        simpa using hcent n hnN
      refine ⟨b, hb, hb1, fun l hl hls => ?_⟩
      have h1 := hcent l hl
      have key : (s * b⁻¹) * (l * b) = (s * b⁻¹) * (b * l) :=
        calc (s * b⁻¹) * (l * b) = ((s * b⁻¹) * l) * b := by group
          _ = (l * (s * b⁻¹)) * b := by rw [h1]
          _ = l * s := by group
          _ = s * l := hls
          _ = (s * b⁻¹) * (b * l) := by group
      exact mul_left_cancel key

theorem sec7l77_cent_s_solvable [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    Group.IsSolvable ↥(L ⊓ normalizer (B : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
  have hctx := hc.ctx
  obtain ⟨b, hb, hb1, hbc⟩ := sec7l77_exists_b h36 hP hc
  obtain ⟨hQ, hCB, hφ⟩ :=
    hP.aut_B G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36) B hc.normalE16
  have hBN : B ≤ L ⊓ normalizer (B : Set G) :=
    le_inf (sec7l77_B_le_L hc) (Subgroup.le_normalizer)
  have hsol := sec7l77_cent_solvable hQ hc.normalE16.2.1 hBN
    (fun x hx => hCB ▸ ⟨hx.1.1, hx.2⟩) hφ hb hb1
  have hle : L ⊓ normalizer (B : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ≤
      L ⊓ normalizer (B : Set G) ⊓ centralizer ({b} : Set G) := by
    rintro l ⟨hl, hls⟩
    refine ⟨hl, ?_⟩
    have h1 : l * (g⁻¹ * t * g) = (g⁻¹ * t * g) * l :=
      Subgroup.mem_centralizer_singleton_iff.mp hls
    have h2 := hbc l hl h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr h2
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

end CFSG.OddStandard.SmallF3.Omega
