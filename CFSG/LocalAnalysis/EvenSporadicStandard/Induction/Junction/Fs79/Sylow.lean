module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

theorem not_isCyclic_sylow_two {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) (S : Sylow 2 Y) : ¬ IsCyclic ↥S := by
  intro hS
  obtain ⟨N, hN, hcompl⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hS
  obtain ⟨a, b, hab⟩ := hnonab
  have hcard := hcompl.card_mul_card
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.card_bot, one_mul] at hcard
    have htop : (S : Subgroup Y) = ⊤ := (Subgroup.card_eq_iff_eq_top (S : Subgroup Y)).1 hcard
    have hY : IsCyclic Y :=
      (MulEquiv.isCyclic (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))).2 hS
    exact hab ((IsCyclic.commGroup (α := Y)).mul_comm a b)
  · rw [h, Subgroup.card_top] at hcard
    have h1 : Nat.card S = 1 :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (mul_one _).symm)
    have hodd : Odd (Nat.card Y) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have := S.dvd_card_of_dvd_card (even_iff_two_dvd.1 hev)
      rw [h1] at this
      omega
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr
      (CFSG.Milestones.odd_order_solvable hodd)) a b)

theorem r_mem_zpowers_r_one {n : ℕ} [NeZero n] (i : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) ∈ Subgroup.zpowers (DihedralGroup.r 1) :=
  Subgroup.mem_zpowers_iff.2 ⟨i.val, by
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩

theorem isCyclic_or_dihedral_of_gen {A B : Type} [Group A] [Group B] [Finite B]
    (hB : IsPGroup 2 B) (g : A →* B) {ρ σ : A}
    (hgen : (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).map g = ⊤) (hσ2 : σ ^ 2 ∈ g.ker)
    (hrel : σ * ρ * σ⁻¹ * ρ ∈ g.ker) :
    IsCyclic B ∨ ∃ j : ℕ, 1 ≤ j ∧ Nonempty (B ≃* DihedralGroup (2 ^ j)) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hgen
  have hσ2' : g σ ^ 2 = 1 := by
    rw [← map_pow]
    exact hσ2
  have hrel' : g σ * g ρ * (g σ)⁻¹ = (g ρ)⁻¹ := by
    have := hrel
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv] at this
    exact mul_eq_one_iff_eq_inv.1 this
  rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators (g ρ) (g σ) hgen.symm hσ2'
    hrel' with h | he
  · exact Or.inl h
  · obtain ⟨e⟩ := he
    obtain ⟨a, ha⟩ := hB.exists_card_eq
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (ha ▸ orderOf_dvd_natCard (g ρ))
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left
      have hρ : g ρ = 1 := orderOf_eq_one_iff.1 (by simpa using hj)
      refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨g σ, ?_⟩
      rw [hρ, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hgen
      exact hgen
    · right
      exact ⟨j, hj0, ⟨by rw [hj] at e; exact e⟩⟩

theorem map_eq_top_of_ker_le {A B C : Type} [Group A] [Group B] [Group C] (g : A →* B)
    (hg : Function.Surjective g) (h : A →* C) {M : Subgroup A} (hM : M.map h = ⊤)
    (hker : h.ker ≤ g.ker) : M.map g = ⊤ := by
  rw [eq_top_iff]
  intro b _
  obtain ⟨a, rfl⟩ := hg b
  have hha : h a ∈ M.map h := hM ▸ Subgroup.mem_top _
  obtain ⟨m, hm, hma⟩ := hha
  refine ⟨m, hm, ?_⟩
  have h1 : m⁻¹ * a ∈ h.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hma, inv_mul_cancel]
  have h2 := hker h1
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

theorem isCyclic_or_dihedral_of_dihedral_hom {A B : Type} [Group A] [Group B] [Finite B]
    (hB : IsPGroup 2 B) {k : ℕ} (g : A →* B) (hg : Function.Surjective g)
    (h : A →* DihedralGroup (2 ^ k)) (hh : Function.Surjective h) (hker : h.ker ≤ g.ker) :
    IsCyclic B ∨ ∃ j : ℕ, 1 ≤ j ∧ Nonempty (B ≃* DihedralGroup (2 ^ j)) := by
  obtain ⟨ρA, hρA⟩ := hh (DihedralGroup.r 1)
  obtain ⟨σA, hσA⟩ := hh (DihedralGroup.sr 0)
  have hD : Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ k)) ⊔
      Subgroup.zpowers (DihedralGroup.sr 0) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    cases x with
    | r i => exact Subgroup.mem_sup_left (r_mem_zpowers_r_one i)
    | sr i =>
      have : (DihedralGroup.sr i : DihedralGroup (2 ^ k)) =
          DihedralGroup.sr 0 * DihedralGroup.r i := by
        rw [DihedralGroup.sr_mul_r, zero_add]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left (r_mem_zpowers_r_one i))
  have hM : (Subgroup.zpowers ρA ⊔ Subgroup.zpowers σA).map h = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hρA, hσA, hD]
  refine isCyclic_or_dihedral_of_gen hB g (map_eq_top_of_ker_le g hg h hM hker) ?_ ?_
  · refine hker ?_
    rw [MonoidHom.mem_ker, map_pow, hσA, pow_two, DihedralGroup.sr_mul_self]
  · refine hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hρA, hσA, DihedralGroup.inv_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
    simp

end CFSG.EvenSporadicStandard.Induction.Junction
