module

public import CFSG.GH74.GLS.Stage4.HexCSub

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem phi6_U_mem (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (c : E.F) :
    phi6 r₁ r₂ E.φ (sl2U c) ∈ root 6 := by
  rw [phi6_apply]; exact (mem_iff_r12 R _).1 (sl2Pos_U_mem E c)

theorem phi6_L_mem (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (c : E.F) :
    phi6 r₁ r₂ E.φ (sl2L c) ∈ root (-6) := by
  rw [phi6_apply]; exact (mem_iff_r12_neg R _).1 (sl2Pos_L_mem E c)

theorem actsPos_weylSix (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    ActsPos 6 root (phi6 r₁ r₂ E.φ (sl2W E.F)) (fun q => 4 - q) := by
  rw [phi6_apply]; exact actsPos_conj_r12 R (actsPos_weylFour R E hO)

theorem r2_neg6_mem (R : RGD2 6 H r₁ r₂ U root) {z : G} (hz : z ∈ root (-6)) :
    r₂ * z * r₂⁻¹ ∈ root 6 := by
  have h62 : conjBy r₂⁻¹ (root (-6)) = root 6 := by simpa using R.act₂.2.1
  exact (mem_iff_conj_of_conjBy h62 z).1 hz

theorem r2_one_mem (R : RGD2 6 H r₁ r₂ U root) {x : G} (hx : x ∈ root 1) :
    r₂ * x * r₂⁻¹ ∈ root 5 := by
  have := (RGD2.mem_iff_r₂ R (i := 1) (by norm_num) (by norm_num) x).1 hx
  norm_num at this; exact this

theorem r2_five_mem (R : RGD2 6 H r₁ r₂ U root) {x : G} (hx : x ∈ root 5) :
    r₂ * x * r₂⁻¹ ∈ root 1 := by
  have := (RGD2.mem_iff_r₂ R (i := 5) (by norm_num) (by norm_num) x).1 hx
  norm_num at this; exact this

theorem exists_mul_of_mem_V25 (R : RGD2 6 H r₁ r₂ U root) {z : G} (hz : z ∈ Vsub root 2 5) :
    ∃ n ∈ Vsub root 2 4, ∃ a ∈ root 5, z = n * a := by
  have hc : z ∈ chainProd root (intList 2 5) := by
    have : z ∈ ((Vsub root 2 5 : Subgroup G) : Set G) := hz
    rwa [Vsub_carrier R (by norm_num) (by norm_num)] at this
  have hl : intList 2 5 = intList 2 4 ++ [5] := by
    have := intList_snoc (i := 2) (j := 5) (by norm_num)
    simpa using this
  rw [hl, chainProd_append, chainProd_singleton] at hc
  obtain ⟨n, hn, a, ha, rfl⟩ := Set.mem_mul.1 hc
  refine ⟨n, ?_, a, ha, rfl⟩
  have : n ∈ ((Vsub root 2 4 : Subgroup G) : Set G) := by
    rw [Vsub_carrier R (by norm_num) (by norm_num)]; exact hn
  exact this

theorem exists_mul_of_mem_V14 (R : RGD2 6 H r₁ r₂ U root) {z : G} (hz : z ∈ Vsub root 1 4) :
    ∃ b ∈ root 1, ∃ n ∈ Vsub root 2 4, z = b * n := by
  have hc : z ∈ chainProd root (intList 1 4) := by
    have : z ∈ ((Vsub root 1 4 : Subgroup G) : Set G) := hz
    rwa [Vsub_carrier R (by norm_num) (by norm_num)] at this
  have hl : intList 1 4 = [1] ++ intList 2 4 := by
    have := intList_cons (i := 1) (j := 4) (by norm_num)
    simpa using this
  rw [hl, chainProd_append, chainProd_singleton] at hc
  obtain ⟨b, hb, n, hn, rfl⟩ := Set.mem_mul.1 hc
  refine ⟨b, hb, n, ?_, rfl⟩
  have : n ∈ ((Vsub root 2 4 : Subgroup G) : Set G) := by
    rw [Vsub_carrier R (by norm_num) (by norm_num)]; exact hn
  exact this

end CFSG.GH74.GLS.Stage4.Hex
