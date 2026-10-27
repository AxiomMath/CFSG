module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Facts

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} {t x : G} {K D : Subgroup P}
  {t₀ x₀ : P} {ι : ↥(centralizer ({t} : Set G)) →* P}

theorem IsEmb.L_le (hE : IsEmb L t x K D t₀ x₀ ι) : L ≤ centralizer ({t} : Set G) := by
  intro l hl
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hE.t_mem) l hl

theorem IsEmb.x_mem_C (hE : IsEmb L t x K D t₀ x₀ ι) : x ∈ centralizer ({t} : Set G) :=
  hE.L_le hE.x_mem

private theorem push_inf_centralizer (hE : IsEmb L t x K D t₀ x₀ ι) :
    push ι (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) =
      K ⊓ centralizer ({x₀} : Set P) := by
  rw [push_inf hE.inj (centralizer ({x} : Set G)) (centralizer ({t} : Set G)),
    push_centralizer_singleton hE.inj hE.x_mem_C, push_self ι, hE.range_eq,
    hE.map_x ⟨x, hE.x_mem_C⟩ rfl]
  rw [inf_assoc, inf_idem, inf_comm]

theorem IsEmb.push_jOf (hE : IsEmb L t x K D t₀ x₀ ι) (hDK : D ≤ K) :
    push ι (jOf L x) = jOf D x₀ := by
  have hA : L ⊓ centralizer ({x} : Set G) ≤ centralizer ({t} : Set G) :=
    le_trans inf_le_left hE.L_le
  have hpush : push ι (L ⊓ centralizer ({x} : Set G)) =
      D ⊓ centralizer ({x₀} : Set P) := by
    rw [push_inf hE.inj L (centralizer ({x} : Set G)), hE.push_L,
      push_centralizer_singleton hE.inj hE.x_mem_C, hE.range_eq,
      hE.map_x ⟨x, hE.x_mem_C⟩ rfl]
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hDK)]
  change push ι ⁅L ⊓ centralizer ({x} : Set G),
    L ⊓ centralizer ({x} : Set G)⁆ = jOf D x₀
  rw [push_commutator ι (H := L ⊓ centralizer ({x} : Set G))
    (H' := L ⊓ centralizer ({x} : Set G)) hA hA, hpush]

theorem IsEmb.card_J (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    Nat.card ↥(jOf L x) = 60 := by
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) :=
    (Subgroup.commutator_le_self _).trans (le_trans inf_le_left hE.L_le)
  rw [← card_push hE.inj hJ_C, hE.push_jOf M.D_le]
  exact M.card_J

theorem IsEmb.card_Cx (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) = 960 := by
  have hH_C : centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) := inf_le_right
  rw [← card_push hE.inj hH_C, push_inf_centralizer hE]
  exact M.card_Kx

theorem IsEmb.J_le (hE : IsEmb L t x K D t₀ x₀ ι) :
    jOf L x ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) := by
  intro j hj
  have hJA : j ∈ L ⊓ centralizer ({x} : Set G) :=
    Subgroup.commutator_le_self _ hj
  exact ⟨hJA.2, hE.L_le hJA.1⟩

theorem IsEmb.J_normal (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ((jOf L x).subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))).Normal := by
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) :=
    (Subgroup.commutator_le_self _).trans (le_trans inf_le_left hE.L_le)
  have hKx_C : centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) := inf_le_right
  have hpushJ : push ι (jOf L x) = jOf D x₀ := hE.push_jOf M.D_le
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hg' : ι (inclusion hKx_C g) ∈ K ⊓ centralizer ({x₀} : Set P) := by
    rw [← push_inf_centralizer hE]
    exact (mem_push ι).mpr ⟨inclusion hKx_C g, g.2, rfl⟩
  have hn' : ι (inclusion hKx_C n) ∈ K ⊓ centralizer ({x₀} : Set P) := by
    rw [← push_inf_centralizer hE]
    exact (mem_push ι).mpr ⟨inclusion hKx_C n, n.2, rfl⟩
  have hn'' : (⟨ι (inclusion hKx_C n), hn'⟩ : ↥(K ⊓ centralizer ({x₀} : Set P))) ∈
      (jOf D x₀).subgroupOf (K ⊓ centralizer ({x₀} : Set P)) := by
    rw [mem_subgroupOf, ← hpushJ]
    exact (mem_push ι).mpr ⟨inclusion hKx_C n, hn, rfl⟩
  have hconj := M.J_normal.conj_mem (⟨ι (inclusion hKx_C n), hn'⟩) hn''
    (⟨ι (inclusion hKx_C g), hg'⟩)
  rw [mem_subgroupOf] at hconj
  have hιconj : ι (inclusion hKx_C (g * n * g⁻¹)) ∈ jOf D x₀ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hconj
  rw [← hpushJ] at hιconj
  obtain ⟨c, hcJ, hc_eq⟩ := (mem_push ι).mp hιconj
  have hc : c = inclusion hKx_C (g * n * g⁻¹) := hE.inj hc_eq
  rw [← coe_inclusion hKx_C (g * n * g⁻¹), ← hc]
  exact hcJ

theorem IsEmb.J_center (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ∀ j ∈ jOf L x, (∀ j' ∈ jOf L x, j * j' = j' * j) → j = 1 := by
  intro j hj hcomm
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) :=
    (Subgroup.commutator_le_self _).trans (le_trans inf_le_left hE.L_le)
  have hpushJ : push ι (jOf L x) = jOf D x₀ := hE.push_jOf M.D_le
  let jC : ↥(centralizer ({t} : Set G)) := ⟨j, hJ_C hj⟩
  have hjC_mem : ι jC ∈ jOf D x₀ := by
    rw [← hpushJ]
    exact (mem_push ι).mpr ⟨jC, hj, rfl⟩
  have hcommP : ∀ j' ∈ jOf D x₀, ι jC * j' = j' * ι jC := by
    intro j' hj'
    rw [← hpushJ] at hj'
    obtain ⟨c, hcJ, rfl⟩ := (mem_push ι).mp hj'
    have hjc : jC * c = c * jC := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hcomm c hcJ
    rw [← map_mul, ← map_mul, hjc]
  have h1 : ι jC = 1 := M.J_center (ι jC) hjC_mem hcommP
  have hJ1 : jC = 1 := hE.inj (by rw [h1, map_one])
  have hval : (j : G) = 1 :=
    congrArg (fun x : ↥(centralizer ({t} : Set G)) => (x : G)) hJ1
  simpa using hval

theorem IsEmb.card_Y (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    Nat.card ↥(centralizer (jOf L x : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) = 8 := by
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) :=
    (Subgroup.commutator_le_self _).trans (le_trans inf_le_left hE.L_le)
  have hKx_C : centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) := inf_le_right
  have hY_C : centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) ≤
      centralizer ({t} : Set G) := le_trans inf_le_right hKx_C
  rw [← card_push hE.inj hY_C,
    push_inf hE.inj (centralizer (jOf L x : Set G))
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
    push_centralizer hE.inj hJ_C, hE.push_jOf M.D_le, push_inf_centralizer hE,
    hE.range_eq]
  rw [inf_assoc, inf_left_idem]
  exact M.card_Y

end CFSG.EvenSporadicStandard.M12Std.PropA
