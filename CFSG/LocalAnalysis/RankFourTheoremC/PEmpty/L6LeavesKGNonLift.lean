module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNon

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

@[expose] def act {K : Subgroup A} (H : Subgroup A) (hH : H ≤ normalizer (K : Set A)) :
    ↥H →* MulAut ↥K :=
  (K.normalizerMonoidHom).comp (Subgroup.inclusion hH)

theorem act_apply {K H : Subgroup A} (hH : H ≤ normalizer (K : Set A)) (h : ↥H) (k : ↥K) :
    ((act H hH h k : ↥K) : A) = (h : A) * k * (h : A)⁻¹ := rfl

theorem act_injective (c : KQCfg A p Kb Sb Bb Mb z) : Function.Injective (act Sb c.S_le_K) := by
  refine (injective_iff_map_eq_one _).mpr fun s hs => ?_
  have h1 : (s : A) = 1 := by
    refine eq_one_of_centralizes c (Subgroup.mem_sup_right s.2) fun k hk => ?_
    have := congrArg (fun f : MulAut ↥Kb => ((f ⟨k, hk⟩ : ↥Kb) : A)) hs
    simp only [act_apply, MulAut.one_apply] at this
    rwa [mul_inv_eq_iff_eq_mul] at this
  exact Subtype.ext h1

theorem inf_inner_eq_bot (c : KQCfg A p Kb Sb Bb Mb z) (hbot : Sb ⊓ Kb = ⊥) :
    (act Sb c.S_le_K).range ⊓ (MulAut.conj : ↥Kb →* MulAut ↥Kb).range = ⊥ := by
  rw [eq_bot_iff]
  rintro σ ⟨⟨s, rfl⟩, ⟨k, hk⟩⟩
  have hsK : ∀ l ∈ Kb, (k : A) * l * (k : A)⁻¹ = (s : A) * l * (s : A)⁻¹ := fun l hl => by
    have := congrArg (fun f : MulAut ↥Kb => ((f ⟨l, hl⟩ : ↥Kb) : A)) hk
    simpa only [MulAut.conj_apply, act_apply, Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hx : (k : A)⁻¹ * (s : A) = 1 := by
    refine eq_one_of_centralizes c
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Kb.inv_mem k.2))
        (Subgroup.mem_sup_right s.2)) fun l hl => ?_
    have h1 := hsK l hl
    calc (k : A)⁻¹ * (s : A) * l = (k : A)⁻¹ * ((s : A) * l * (s : A)⁻¹) * (s : A) := by group
      _ = (k : A)⁻¹ * ((k : A) * l * (k : A)⁻¹) * (s : A) := by rw [h1]
      _ = l * ((k : A)⁻¹ * (s : A)) := by group
  have hsk : (s : A) = k := by
    rw [inv_mul_eq_one] at hx
    exact hx.symm
  have hs1 : (s : A) = 1 := by
    have hmem : (s : A) ∈ Sb ⊓ Kb := ⟨s.2, by rw [hsk]; exact k.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have : s = 1 := Subtype.ext hs1
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem mul_comm_of_act_mul_comm (c : KQCfg A p Kb Sb Bb Mb z) {s t : ↥Sb}
    (h : act Sb c.S_le_K t * act Sb c.S_le_K s = act Sb c.S_le_K s * act Sb c.S_le_K t) :
    (t : A) * s = s * t := by
  have h1 : t * s = s * t := act_injective c (by rw [map_mul, map_mul]; exact h)
  exact congrArg Subtype.val h1

theorem act_conj (c : KQCfg A p Kb Sb Bb Mb z) (b : ↥Bb) (s : ↥Sb) :
    act Sb c.S_le_K ⟨(b : A) * s * (b : A)⁻¹,
      (mem_normalizer_iff.mp (c.B_le_S b.2) s).mp s.2⟩ * act Bb c.B_le_K b =
      act Bb c.B_le_K b * act Sb c.S_le_K s := by
  ext k
  simp only [MulAut.mul_apply, act_apply]
  group

theorem comm_of_act_comm (c : KQCfg A p Kb Sb Bb Mb z) {b : ↥Bb} {s : ↥Sb}
    (h : act Bb c.B_le_K b * act Sb c.S_le_K s = act Sb c.S_le_K s * act Bb c.B_le_K b) :
    (b : A) * s = s * b := by
  have hbs : (b : A) * s * (b : A)⁻¹ ∈ Sb := (mem_normalizer_iff.mp (c.B_le_S b.2) s).mp s.2
  have h1 : act Sb c.S_le_K ⟨(b : A) * s * (b : A)⁻¹, hbs⟩ = act Sb c.S_le_K s := by
    have h2 := act_conj c b s
    rw [h] at h2
    exact mul_right_cancel h2
  have h3 : (⟨(b : A) * s * (b : A)⁻¹, hbs⟩ : ↥Sb) = s := act_injective c h1
  have h4 : (b : A) * s * (b : A)⁻¹ = s := congrArg Subtype.val h3
  rwa [mul_inv_eq_iff_eq_mul] at h4

theorem act_apply_eq_iff {s : ↥Sb} (hS : Sb ≤ normalizer (Kb : Set A)) {k : ↥Kb} :
    act Sb hS s k = k ↔ (s : A) * k = k * s := by
  rw [Subtype.ext_iff, act_apply, mul_inv_eq_iff_eq_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNon
