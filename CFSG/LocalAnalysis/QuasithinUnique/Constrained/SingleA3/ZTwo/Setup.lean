module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Dihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwoConfig

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c)

include h

theorem isPGroup_T : IsPGroup 2 T := h.sylowT.2.1

theorem conj_mem {s : G} (hs : s ∈ S) : x * s * x⁻¹ ∈ S :=
  (mem_normalizer_iff.mp h.x_normalizes s).mp hs

theorem conj_inv_mem {s : G} (hs : s ∈ S) : x⁻¹ * s * x ∈ S := by
  have := (mem_normalizer_iff.mp (inv_mem h.x_normalizes) s).mp hs
  simpa using this

theorem U'_le : conjSubgroup U x ≤ S :=
  A3Dich.conjSubgroup_le_of_le h.U_le h.x_normalizes

theorem S_norm_U' : S ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) :=
  A3Dich.le_normalizer_conjSubgroup h.S_normalizes_U h.x_normalizes

theorem card_U' : Nat.card (conjSubgroup U x) = 4 := by
  rw [A3Dich.card_conjSubgroup, h.card_U]

theorem U'_conj : conjSubgroup (conjSubgroup U x) x = U :=
  A3Dich.conjSubgroup_conjSubgroup_self (h.S_normalizes_U h.x_sq_mem)

theorem U'_exp : ∀ v ∈ conjSubgroup U x, v ^ 2 = 1 := by
  intro v hv
  rw [mem_conjSubgroup_iff] at hv
  have h1 := h.U_exp _ hv
  rw [pow_two] at h1 ⊢
  have h2 : x * (v * v) * x⁻¹ = 1 := by rw [← h1]; group
  have h3 : v * v = x⁻¹ * (x * (v * v) * x⁻¹) * x := by group
  rw [h3, h2]
  group

theorem U_le_R : U ≤ R := h.R_eq ▸ le_sup_left

theorem U'_le_R : conjSubgroup U x ≤ R := h.R_eq ▸ le_sup_right

theorem S_norm_R : S ≤ normalizer (R : Set G) := by
  rw [h.R_eq]
  exact fun s hs => A3Gen.mem_normalizer_sup (h.S_normalizes_U hs) (h.S_norm_U' hs)

theorem R_conj : conjSubgroup R x = R := by
  rw [h.R_eq, A3Dich.conjSubgroup_sup, h.U'_conj, sup_comm]

theorem x_norm_R : x ∈ normalizer (R : Set G) :=
  conjSubgroup_eq_iff_mem_normalizer.mp h.R_conj

theorem card_inf : Nat.card ↥(U ⊓ conjSubgroup U x) = 2 := by
  have hh := A3Gen.card_sup_mul_card_inf_of_le_normalizer' (A := U) (B := conjSubgroup U x)
    (h.U_le.trans h.S_norm_U')
  rw [h.card_U, h.card_U', ← h.R_eq, h.card_R] at hh
  omega

theorem exists_d8 : ∃ z : G, D8Data R U (conjSubgroup U x) z := by
  have hcard := h.card_inf
  have hne : U ⊓ conjSubgroup U x ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hz2 : z ^ 2 = 1 := h.U_exp z hz.1
  have hzp : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1'
  have heq : zpowers z = U ⊓ conjSubgroup U x :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz) (by rw [hcard, hzp])
  exact ⟨z,
    { R_eq := h.R_eq
      card_U := h.card_U
      card_V := h.card_U'
      U_exp := h.U_exp
      V_exp := h.U'_exp
      U_norm_V := fun u hu => h.S_norm_U' (h.U_le hu)
      V_norm_U := fun v hv => h.S_normalizes_U (h.U'_le hv)
      R_nonab := h.R_nonabelian
      z_mem_U := hz.1
      z_mem_V := hz.2
      z_ne_one := hz1'
      inter := fun g hgU hgV => heq ▸ (⟨hgU, hgV⟩ : g ∈ U ⊓ conjSubgroup U x) }, ⟩

end ZTwoConfig

end CFSG.QuasithinUnique
