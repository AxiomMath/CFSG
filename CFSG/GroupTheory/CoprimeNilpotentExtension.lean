module

public import CFSG.GroupTheory.CoprimeNilpotentTorsor

public section

namespace CFSG.GroupTheory

universe u

variable {G : Type*} [Group G]

theorem exists_norm_mul_eq_one_of_pow_three_eq_conj_of_nilpotencyClass_le (n : ℕ) :
    ∀ (G : Type u) [Group G] [Group.IsNilpotent G],
      Group.nilpotencyClass G ≤ n →
      ∀ (α : MulAut G) (c : G),
        Function.Bijective (fun g : G => g ^ 3) →
        (∀ g : G, α (α (α g)) = c * g * c⁻¹) →
        α c = c →
        ∃ u : G, u * α u * α (α u) * c = 1 := by
  induction n with
  | zero =>
      intro G _ _ hclass α c hcube hα3 hc
      have hzero : Group.nilpotencyClass G = 0 := Nat.le_zero.mp hclass
      let : Subsingleton G := (Group.nilpotencyClass_zero_iff_subsingleton).mp hzero
      exact ⟨1, Subsingleton.elim (1 * α 1 * α (α 1) * c) 1⟩
  | succ n ih =>
      intro G _ _ hclass α c hcube hα3 hc
      let Z : Subgroup G := Subgroup.center G
      let Q := G ⧸ Z
      have : Group.IsNilpotent Q := Group.nilpotent_quotient_of_nilpotent Z
      have hclQ : Group.nilpotencyClass Q = Group.nilpotencyClass G - 1 := by
        dsimp [Q, Z]
        exact Group.nilpotencyClass_quotient_center
      have hclassQ : Group.nilpotencyClass Q ≤ n := by
        rw [hclQ]
        exact (Nat.sub_le_iff_le_add).mpr hclass
      let αQ : MulAut Q := CFSG.quotientAut α
      let cQ : Q := QuotientGroup.mk' Z c
      have hcubeQ : Function.Bijective (fun q : Q => q ^ 3) := by
        dsimp [Q, Z]
        exact bijective_pow_three_quotient_center hcube
      have hα3Q : ∀ q : Q, αQ (αQ (αQ q)) = cQ * q * cQ⁻¹ := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H x =>
          change (CFSG.quotientAut α) ((CFSG.quotientAut α) ((CFSG.quotientAut α)
            (QuotientGroup.mk' (Subgroup.center G) x))) =
            QuotientGroup.mk' (Subgroup.center G) c *
              QuotientGroup.mk' (Subgroup.center G) x *
              (QuotientGroup.mk' (Subgroup.center G) c)⁻¹
          simp only [CFSG.quotientAut_mk, hα3 x]
          simp [map_mul, map_inv]
      have hcQ : αQ cQ = cQ := by
        change (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) c) =
          QuotientGroup.mk' (Subgroup.center G) c
        rw [CFSG.quotientAut_mk, hc]
      obtain ⟨uQ, huQ⟩ := ih Q hclassQ αQ cQ hcubeQ hα3Q hcQ
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective Z uQ
      rw [← hu] at huQ
      have h1 : αQ (QuotientGroup.mk' Z u) = QuotientGroup.mk' Z (α u) := by
        change (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) u) =
          QuotientGroup.mk' (Subgroup.center G) (α u)
        rw [CFSG.quotientAut_mk]
      have h3 : αQ (QuotientGroup.mk' Z (α u)) =
          QuotientGroup.mk' Z (α (α u)) := by
        change (CFSG.quotientAut α) (QuotientGroup.mk' (Subgroup.center G) (α u)) =
          QuotientGroup.mk' (Subgroup.center G) (α (α u))
        rw [CFSG.quotientAut_mk]
      let w : G := u * α u * α (α u) * c
      have hw_mk : QuotientGroup.mk' Z w = 1 := by
        have h := huQ
        rw [h1, h3] at h
        dsimp only [w]
        rw [show QuotientGroup.mk' Z (u * α u * α (α u) * c) =
            QuotientGroup.mk' Z u * QuotientGroup.mk' Z (α u) *
              QuotientGroup.mk' Z (α (α u)) * QuotientGroup.mk' Z c by
          simp [map_mul]]
        exact h
      have hw_mem : w ∈ Z := (QuotientGroup.eq_one_iff w).mp hw_mk
      have hαw : α w = u⁻¹ * w * u := by
        dsimp only [w]
        simp only [map_mul, hc, hα3 u]
        group
      have hαw_eq : α w = w := by
        rw [hαw]
        have hcomm : u * w = w * u := Subgroup.mem_center_iff.mp hw_mem u
        calc
          u⁻¹ * w * u = u⁻¹ * (w * u) := by group
          _ = u⁻¹ * (u * w) := by rw [hcomm.symm]
          _ = w := by group
      obtain ⟨d, hd3⟩ := hcube.2 (w⁻¹)
      have hd3' : d ^ 3 = w⁻¹ := hd3
      have hd_mem : d ∈ Z :=
        mem_center_of_pow_three_mem_center hcube (by rw [hd3']; exact Z.inv_mem hw_mem)
      have hαd : α d = d := by
        apply hcube.1
        have h := congrArg α hd3'
        rw [map_pow, map_inv, hαw_eq] at h
        rw [← hd3'] at h
        exact h
      refine ⟨d * u, ?_⟩
      have hdu : d * u = u * d := (Subgroup.mem_center_iff.mp hd_mem u).symm
      have hd3Z : d ^ 3 ∈ Z := Z.pow_mem hd_mem 3
      have hd3_comm : d ^ 3 * c = c * d ^ 3 :=
        (Subgroup.mem_center_iff.mp hd3Z c).symm
      calc
        (d * u) * α (d * u) * α (α (d * u)) * c
            = (u * d) * α (u * d) * α (α (u * d)) * c := by rw [hdu]
        _ = ((u * α u * α (α u)) * (d * α d * α (α d))) * c := by
              rw [norm_mul_of_mem_center α hd_mem u]
        _ = ((u * α u * α (α u)) * d ^ 3) * c := by
              simp only [hαd]
              rw [show d ^ 3 = d * d * d by rw [pow_succ, pow_succ, pow_one]]
        _ = ((u * α u * α (α u)) * c) * d ^ 3 := by
              rw [mul_assoc (u * α u * α (α u)) (d ^ 3) c, hd3_comm]
              group
        _ = 1 := by
              change w * d ^ 3 = 1
              rw [hd3']
              group

theorem exists_norm_mul_eq_one_of_pow_three_eq_conj
    {G : Type u} [Group G] [Group.IsNilpotent G]
    (α : MulAut G) (c : G)
    (hcube : Function.Bijective (fun g : G => g ^ 3))
    (hα3 : ∀ g : G, α (α (α g)) = c * g * c⁻¹)
    (hc : α c = c) :
    ∃ u : G, u * α u * α (α u) * c = 1 :=
  exists_norm_mul_eq_one_of_pow_three_eq_conj_of_nilpotencyClass_le
    (Group.nilpotencyClass G) G (le_refl (Group.nilpotencyClass G)) α c hcube hα3 hc

end CFSG.GroupTheory
