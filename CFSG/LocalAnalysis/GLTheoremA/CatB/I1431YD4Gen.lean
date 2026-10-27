module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

open scoped commutatorElement

theorem exists_perfect_cover {X Y : Type} [Group X] [Finite X] [Group Y] [Group.IsPerfect Y]
    (π : X →* Y) (hπ : Function.Surjective π) :
    ∃ P : Subgroup X, Group.IsPerfect P ∧ P.map π = ⊤ := by
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image {P : Subgroup X | P.map π = ⊤}
    (fun P => Nat.card P) (Set.toFinite _)
    ⟨⊤, show (⊤ : Subgroup X).map π = ⊤ by
      rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.2 hπ⟩
  have hP' : P.map π = ⊤ := hP
  have hc : (⁅P, P⁆ : Subgroup X).map π = ⊤ := by
    rw [Subgroup.map_commutator, hP', Subgroup.commutator_eq_self (H := (⊤ : Subgroup Y))]
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  have heq : ⁅P, P⁆ = P := Subgroup.eq_of_le_of_card_ge hle (hmin _ hc)
  exact ⟨P, Subgroup.isPerfect_iff.mpr heq, hP'⟩

theorem exists_descend {X Y T : Type} [Group X] [Group Y] [Group T] (ρ : X →* Y) (f : X →* T)
    (hker : ρ.ker ≤ f.ker) :
    ∃ φ : ρ.range →* T, ∀ x, φ (ρ.rangeRestrict x) = f x := by
  have hs := ρ.rangeRestrict_surjective
  refine ⟨ρ.rangeRestrict.liftOfRightInverse (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨f, by rw [MonoidHom.ker_rangeRestrict]; exact hker⟩, ?_⟩
  intro x
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem perfect_hom_perm_trivial {L α : Type} [Group L] [Group.IsPerfect L] [Finite α]
    (hα : Nat.card α ≤ 4) (ψ : L →* Equiv.Perm α) : ψ = 1 := by
  haveI : Group.IsSolvable (Equiv.Perm α) := Equiv.Perm.isSolvable hα
  haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  haveI : Group.IsSolvable ψ.range := inferInstance
  have : Subsingleton ψ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable ψ.range ‹_›
  refine MonoidHom.ext fun x => ?_
  have := Subsingleton.elim (ψ.rangeRestrict x) 1
  have h2 := congrArg Subtype.val this
  simpa using h2

theorem dvd_card_sup_zpowers {Om : Type} [Group Om] [Finite Om] {L : Subgroup Om} {g : Om}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hLg : ∀ l ∈ L, l * g = g * l)
    {S : Type} [Group S] [IsSimpleGroup S] (hS : Nat.card S = 360)
    (f : L →* S) (hf : Function.Surjective f) :
    27 ∣ Nat.card ↥(L ⊔ Subgroup.zpowers g) := by
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hncS : ¬ ∀ a b : S, a * b = b * a :=
    U4Sp8.not_comm_of_simple_of_card (by rw [hS]; norm_num)
  have hZS : Subgroup.center S = ⊥ := center_eq_bot_of_simple_of_not_comm hncS
  have hmul : Nat.card f.ker * Nat.card S = Nat.card L := by
    have := Subgroup.card_ker_mul_card_of_surjective hf
    simpa [mul_comm] using this
  by_cases hgL : g ∈ L
  · have hsup : L ⊔ Subgroup.zpowers g = L := sup_eq_left.2 ((Subgroup.zpowers_le).2 hgL)
    rw [hsup]
    have hmem : (⟨g, hgL⟩ : L) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have : f ⟨g, hgL⟩ ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨l, rfl⟩ := hf s
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hLg l l.2)
      rw [hZS, Subgroup.mem_bot] at this
      exact this
    have h3 : 3 ∣ Nat.card f.ker := by
      have : orderOf (⟨⟨g, hgL⟩, hmem⟩ : f.ker) = 3 := by
        rw [← hord, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      rw [← this]
      exact orderOf_dvd_natCard _
    rw [← hmul, hS]
    obtain ⟨c, hc⟩ := h3
    rw [hc]
    exact ⟨c * 40, by ring⟩
  ·
    let ν : L × Subgroup.zpowers g →* Om :=
      MonoidHom.noncommCoprod L.subtype (Subgroup.zpowers g).subtype (fun l z => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
        show Commute (l : Om) (z : Om)
        rw [← hk]
        exact Commute.zpow_right (hLg l l.2) k)
    have hrange : ν.range = L ⊔ Subgroup.zpowers g := by
      rw [MonoidHom.noncommCoprod_range]
      simp
    have hker : ν.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨l, z⟩ hlz
      rw [MonoidHom.mem_ker] at hlz
      have h1 : (l : Om) * z = 1 := hlz
      have hzL : (z : Om) ∈ L := by
        have : (z : Om) = (l : Om)⁻¹ := eq_inv_of_mul_eq_one_right h1 |>.symm ▸ rfl
        rw [this]
        exact L.inv_mem l.2
      have hz1 : (z : Om) = 1 := by
        by_contra hz1
        apply hgL
        have hzo : orderOf (z : Om) = 3 := by
          have h3' : (z : Om) ^ 3 = 1 := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
            rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
          exact orderOf_eq_prime h3' hz1
        have hle : Subgroup.zpowers (z : Om) ≤ Subgroup.zpowers g :=
          (Subgroup.zpowers_le).2 z.2
        have hcard1 : Nat.card (Subgroup.zpowers (z : Om)) = 3 := by rw [Nat.card_zpowers, hzo]
        have hcard2 : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hord]
        have heq : Subgroup.zpowers (z : Om) = Subgroup.zpowers g :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
        have : g ∈ Subgroup.zpowers (z : Om) := by rw [heq]; exact Subgroup.mem_zpowers g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
        rw [← hk]
        exact L.zpow_mem hzL k
      have hl1 : (l : Om) = 1 := by rw [hz1, mul_one] at h1; exact h1
      rw [Subgroup.mem_bot]
      exact Prod.ext (Subtype.ext hl1) (Subtype.ext hz1)
    have hcard := Subgroup.card_ker_mul_card_range ν
    rw [hker, hrange, Subgroup.card_bot, one_mul, Nat.card_prod, Nat.card_zpowers, hord] at hcard
    rw [hcard]
    have h9 : 9 ∣ Nat.card L := by
      rw [← hmul, hS]
      exact Dvd.dvd.mul_left (by norm_num) _
    obtain ⟨c, hc⟩ := h9
    rw [hc]
    exact ⟨c, by ring⟩

theorem isPerfect_of_simple {S : Type} [Group S] [IsSimpleGroup S] (h : ¬ (Nat.card S).Prime) :
    Group.IsPerfect S := by
  have hnc : ¬ ∀ a b : S, a * b = b * a := U4Sp8.not_comm_of_simple_of_card h
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h0 | h1
  · exfalso
    apply hnc
    intro a b
    have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h1

theorem exists_perfect_sub {G S : Type} [Group G] [Finite G] [Group S] [Group.IsPerfect S]
    {A₀ : Subgroup G} (f : ↥A₀ →* S) (hf : Function.Surjective f) :
    ∃ L : Subgroup G, L ≤ A₀ ∧ Group.IsPerfect ↥L ∧ ∃ φ : ↥L →* S, Function.Surjective φ := by
  obtain ⟨P, hP, hPmap⟩ := exists_perfect_cover f hf
  refine ⟨P.map A₀.subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · haveI := hP
    exact Group.IsPerfect.map A₀.subtype
  · let e : ↥P ≃* ↥(P.map A₀.subtype) :=
      Subgroup.equivMapOfInjective P A₀.subtype A₀.subtype_injective
    refine ⟨(f.comp P.subtype).comp e.symm.toMonoidHom, ?_⟩
    have h1 : Function.Surjective (f.comp P.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      exact hPmap
    exact h1.comp e.symm.surjective

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

end
