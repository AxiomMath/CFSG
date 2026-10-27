module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ExistsZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

theorem m24Out_E_comm (hm : M24Out G E t) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
  fun _ ha _ hb => ExistsZ.comm_of_sq hm.E_sq ha hb

theorem m24Out_E_sq (hm : M24Out G E t) : ∀ w : ↥E, w ^ 2 = 1 :=
  fun w => Subtype.ext (hm.E_sq w w.2)

theorem m24Out_E_mul_self (hm : M24Out G E t) : ∀ w : ↥E, w * w = 1 :=
  fun w => by rw [← pow_two]; exact m24Out_E_sq hm w

theorem finite_E_of_m24Out (hm : M24Out G E t) : Finite ↥E :=
  Nat.finite_of_card_ne_zero (by rw [hm.card_E]; norm_num)

@[expose, instance_reducible] def commGroupOfM24Out (hm : M24Out G E t) : CommGroup ↥E :=
  S44.commE (m24Out_E_comm hm)

theorem xe_equiv_m24 (hm : M24Out G E t) : Nonempty (↥(S44.XE E) ≃* Carrier .M24) := by
  obtain ⟨e⟩ := hm.quotient
  have hker := S44.ker_actN_eq hm.centralizer_eq
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange (S44.actN E))).symm.trans e⟩

theorem normClass_eq_image_orbit (x : ↥E) :
    normClass E (x : G) = Subtype.val '' orbit (S44.XE E) x := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨S44.actN E ⟨n, hn⟩ x, ⟨⟨S44.actN E ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨m, ⟨n, rfl⟩⟩, rfl⟩, rfl⟩
    exact ⟨n, n.2, rfl⟩

theorem mem_normClass_iff_mem_orbit (x y : ↥E) :
    (y : G) ∈ normClass E (x : G) ↔ y ∈ orbit (S44.XE E) x := by
  rw [normClass_eq_image_orbit]
  exact Subtype.val_injective.mem_set_image

theorem ncard_normClass_eq (x : ↥E) :
    (normClass E (x : G)).ncard = Nat.card ↥(orbit (S44.XE E) x) := by
  rw [normClass_eq_image_orbit, Set.ncard_image_of_injective _ Subtype.val_injective,
    Nat.card_coe_set_eq]

theorem mem_orbit_one_iff {x : ↥E} : x ∈ orbit (S44.XE E) (1 : ↥E) ↔ x = 1 := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact map_one g
  · rintro rfl
    exact mem_orbit_self _

theorem one_notMem_orbit {x : ↥E} (hx : x ≠ 1) : (1 : ↥E) ∉ orbit (S44.XE E) x := by
  intro h
  apply hx
  have h1 : orbit (S44.XE E) (1 : ↥E) = orbit (S44.XE E) x := MulAction.orbit_eq_iff.2 h
  have h2 : x ∈ orbit (S44.XE E) (1 : ↥E) := by
    rw [h1]
    exact mem_orbit_self x
  exact mem_orbit_one_iff.1 h2

theorem exists_two_orbits (hm : M24Out G E t) :
    ∃ y : ↥E, y ≠ 1 ∧ y ∉ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) ∧
      Nat.card ↥(orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E)) = 276 ∧
      Nat.card ↥(orbit (S44.XE E) y) = 1771 ∧
      ∀ x : ↥E, x ≠ 1 →
        x ∈ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) ∨ x ∈ orbit (S44.XE E) y := by
  obtain ⟨y, hyE, hy1, hyt, hyc, hall⟩ := hm.rest
  refine ⟨⟨y, hyE⟩, fun h => hy1 (congrArg Subtype.val h), ?_, ?_, ?_, ?_⟩
  · rw [← mem_normClass_iff_mem_orbit]
    exact hyt
  · rw [← ncard_normClass_eq]
    exact hm.ncard_t
  · rw [← ncard_normClass_eq]
    exact hyc
  · intro x hx
    by_cases h : x ∈ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← mem_normClass_iff_mem_orbit]
      refine hall x.1 x.2 (fun h1 => hx (Subtype.ext h1)) fun h2 => h ?_
      exact (mem_normClass_iff_mem_orbit (⟨t, hm.t_mem⟩ : ↥E) x).1 h2

theorem card_orbit_cases (hm : M24Out G E t) {x : ↥E} (hx : x ≠ 1) :
    (x ∈ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) ∧ Nat.card ↥(orbit (S44.XE E) x) = 276) ∨
    (x ∉ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E) ∧ Nat.card ↥(orbit (S44.XE E) x) = 1771) := by
  obtain ⟨y, -, -, hc1, hc2, hcover⟩ := exists_two_orbits hm
  by_cases h : x ∈ orbit (S44.XE E) (⟨t, hm.t_mem⟩ : ↥E)
  · left
    exact ⟨h, by rw [MulAction.orbit_eq_iff.2 h]; exact hc1⟩
  · right
    refine ⟨h, ?_⟩
    rcases hcover x hx with h1 | h1
    · exact absurd h1 h
    · rw [MulAction.orbit_eq_iff.2 h1]
      exact hc2

theorem centSub_zpowers_eq_stabilizer (hm : M24Out G E t) (x : ↥E) :
    @Quasithin.centSub ↥E (commGroupOfM24Out hm) (Subgroup.zpowers x) =
      stabilizer (MulAut ↥E) x := by
  letI := commGroupOfM24Out hm
  ext g
  rw [Quasithin.mem_centSub, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hx : g x = x := h
    rw [map_zpow, hx]

theorem XE_invariant_eq_bot_or_top (hm : M24Out G E t) (U : Subgroup ↥E)
    (hU : ∀ g ∈ S44.XE E, ∀ u ∈ U, g u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  haveI : Finite ↥E := finite_E_of_m24Out hm
  obtain ⟨y, hy1, hyt, hc1, hc2, hcover⟩ := exists_two_orbits hm
  set t' : ↥E := ⟨t, hm.t_mem⟩ with ht'
  have ht1 : t' ≠ 1 := fun h => hm.t_ne_one (congrArg Subtype.val h)
  have horb : ∀ x ∈ U, orbit (S44.XE E) x ⊆ U := by
    rintro x hx _ ⟨⟨g, hg⟩, rfl⟩
    exact hU g hg x hx
  have hback : ∀ x w : ↥E, w ∈ U → w ∈ orbit (S44.XE E) x → x ∈ U := by
    intro x w hw hwx
    have h1 : orbit (S44.XE E) w = orbit (S44.XE E) x := MulAction.orbit_eq_iff.2 hwx
    exact horb w hw (h1 ▸ mem_orbit_self x)
  have hdvd := Subgroup.card_subgroup_dvd_card U
  rw [hm.card_E] at hdvd
  by_cases ht : t' ∈ U <;> by_cases hy : y ∈ U
  · right
    rw [eq_top_iff]
    intro x _
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem U
    · rcases hcover x hx1 with h | h
      · exact horb t' ht h
      · exact horb y hy h
  · exfalso
    have hset : (U : Set ↥E) = insert 1 (orbit (S44.XE E) t') := by
      ext x
      constructor
      · intro hx
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · refine Or.inr ?_
          rcases hcover x hx1 with h | h
          · exact h
          · exact absurd (hback y x hx h) hy
      · rintro (rfl | hx)
        · exact one_mem U
        · exact horb t' ht hx
    have hcard : Nat.card ↥U = 277 := by
      have h2 : Nat.card ↥U = (U : Set ↥E).ncard := Nat.card_coe_set_eq (U : Set ↥E)
      rw [h2, hset, Set.ncard_insert_of_notMem (one_notMem_orbit ht1) (Set.toFinite _),
        ← Nat.card_coe_set_eq, hc1]
    rw [hcard] at hdvd
    exact absurd hdvd (by norm_num)
  · exfalso
    have hset : (U : Set ↥E) = insert 1 (orbit (S44.XE E) y) := by
      ext x
      constructor
      · intro hx
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · refine Or.inr ?_
          rcases hcover x hx1 with h | h
          · exact absurd (hback t' x hx h) ht
          · exact h
      · rintro (rfl | hx)
        · exact one_mem U
        · exact horb y hy hx
    have hcard : Nat.card ↥U = 1772 := by
      have h2 : Nat.card ↥U = (U : Set ↥E).ncard := Nat.card_coe_set_eq (U : Set ↥E)
      rw [h2, hset, Set.ncard_insert_of_notMem (one_notMem_orbit hy1) (Set.toFinite _),
        ← Nat.card_coe_set_eq, hc2]
    rw [hcard] at hdvd
    exact absurd hdvd (by norm_num)
  · left
    rw [eq_bot_iff]
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · exfalso
      rcases hcover u hu1 with h | h
      · exact ht (hback t' u hu h)
      · exact hy (hback y u hu h)

theorem isIrrOn_XE (hm : M24Out G E t) :
    @QuasithinUnique.Setup.X1.IsIrrOn ↥E (commGroupOfM24Out hm) (S44.XE E) := by
  letI := commGroupOfM24Out hm
  refine ⟨⟨⟨1, ⟨t, hm.t_mem⟩, fun h => hm.t_ne_one (congrArg Subtype.val h).symm⟩⟩, ?_⟩
  intro U hU
  exact XE_invariant_eq_bot_or_top hm U hU

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
