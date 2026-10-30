module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.Adapters.LieModelOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem ff_card_model_psp {X : Type} [Group X] (h : LieModel X .PSp 2 3 1) :
    Nat.card X = 25920 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

theorem ff_card_model_psl2 {X : Type} [Group X] (h : LieModel X .PSL 2 3 2) :
    Nat.card X = 360 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

theorem ff_card_model_psl3 {X : Type} [Group X] (h : LieModel X .PSL 3 3 1) :
    Nat.card X = 5616 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

theorem ff_card_model_psl4 {X : Type} [Group X] (h : LieModel X .PSL 4 3 1) :
    Nat.card X = 6065280 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

theorem ff_fin_simple_psp {X : Type} [Group X] (h : LieModel X .PSp 2 3 1) :
    Finite X ∧ IsSimpleGroup X := by
  have := CFSG.LieType.Simplicity.fam_classical_converse X
    ⟨.PSp, 2, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩
  exact ⟨this.1, this.2.2⟩

theorem ff_fin_simple_psl2 {X : Type} [Group X] (h : LieModel X .PSL 2 3 2) :
    Finite X ∧ IsSimpleGroup X := by
  have := CFSG.LieType.Simplicity.fam_classical_converse X
    ⟨.PSL, 2, 3, 2, h.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩
  exact ⟨this.1, this.2.2⟩

theorem ff_fin_simple_psl3 {X : Type} [Group X] (h : LieModel X .PSL 3 3 1) :
    Finite X ∧ IsSimpleGroup X := by
  have := CFSG.LieType.Simplicity.fam_classical_converse X
    ⟨.PSL, 3, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)⟩
  exact ⟨this.1, this.2.2⟩

theorem ff_noncomm_of_simple_card {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hne
  push Not at hne
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := fun a b => hne a b }
  exact hp (IsSimpleGroup.prime_card (α := X))

theorem ff_oddCore_eq_bot_of_simple_even {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hev : 2 ∣ Nat.card X) : oddCore X = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore X) with h | h
  · exact h
  · exfalso
    have hodd := ff_odd_card_oddCore X
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hev)

theorem ff_lieModel_quot_oddCore {X : Type} [Group X] [Finite X] {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (h : LieModel X t n p f) (hs : IsSimpleGroup X) (hev : 2 ∣ Nat.card X) :
    LieModel (X ⧸ oddCore X) t n p f := by
  have h0 := ff_oddCore_eq_bot_of_simple_even hs hev
  exact LieModel.of_mulEquiv ((QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h0.symm)) h

theorem ff_card_quot_bot {X : Subgroup G} (h : X = ⊥) : Nat.card (↥X ⧸ oddCore ↥X) = 1 := by
  haveI : Subsingleton ↥X := by subst h; infer_instance
  haveI : Subsingleton (↥X ⧸ oddCore ↥X) := QuotientGroup.mk_surjective.subsingleton
  exact Nat.card_unique

theorem ff_orderOf_conj {E : Type} [Group E] (k g : E) : orderOf (k * g * k⁻¹) = orderOf g :=
  orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective g

theorem ff_exists_odd_ne_one {E : Type} [Group E] [Finite E] (hs : IsSimpleGroup E)
    (hnc : ∃ a b : E, a * b ≠ b * a) : ∃ g : E, Odd (orderOf g) ∧ g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card E) Nat.card_pos.ne'
  by_cases hm1 : m = 1
  · have hp : IsPGroup 2 E := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact IsPGroup.of_card (by rw [hcard, hm1, mul_one])
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent E := hp.isNilpotent
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := E)).mpr inferInstance a b)
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
    have hdvd : p ∣ Nat.card E := by rw [hcard]; exact dvd_mul_of_dvd_right hpm _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 := hcon g (by rw [hg]; exact hp.odd_of_ne_two hp2)
    rw [h1, orderOf_one] at hg
    exact hp.one_lt.ne hg

theorem ff_closure_eq_top_of_simple {E : Type} [Group E] (hs : IsSimpleGroup E) (P : E → Prop)
    (hP : ∀ g k : E, P g → P (k * g * k⁻¹)) (hne : ∃ g, P g ∧ g ≠ 1) :
    Subgroup.closure {g : E | P g} = ⊤ := by
  haveI := hs
  have hnorm : (Subgroup.closure {g : E | P g}).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hmap : (Subgroup.closure {g : E | P g}).map (MulAut.conj k).toMonoidHom ≤
        Subgroup.closure {g : E | P g} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨g, hg, rfl⟩
      exact hP g k hg
    exact hmap (Subgroup.mem_map.mpr ⟨n, hn, by simp⟩)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {g : E | P g}) with h | h
  · exfalso
    obtain ⟨g, hg, hg1⟩ := hne
    have : g ∈ Subgroup.closure {g : E | P g} := Subgroup.subset_closure hg
    rw [h] at this
    exact hg1 (Subgroup.mem_bot.mp this)
  · exact h

theorem ff_closure_filter_eq {B : Type} [Group B] (E : Subgroup B) (hs : IsSimpleGroup ↥E)
    (P : B → Prop) (hP : ∀ g k : ↥E, P (g : B) → P ((k * g * k⁻¹ : ↥E) : B))
    (hne : ∃ g : ↥E, P (g : B) ∧ g ≠ 1) :
    Subgroup.closure {g : B | g ∈ E ∧ P g} = E := by
  apply le_antisymm
  · exact (Subgroup.closure_le E).mpr (fun g hg => hg.1)
  · intro x hx
    have htop := ff_closure_eq_top_of_simple hs (fun g : ↥E => P (g : B)) hP hne
    have hxK : (⟨x, hx⟩ : ↥E) ∈ Subgroup.closure {g : ↥E | P (g : B)} := by
      rw [htop]; trivial
    have := Subgroup.mem_map_of_mem E.subtype hxK
    rw [MonoidHom.map_closure] at this
    refine Subgroup.closure_mono ?_ this
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩

theorem ff_isQuasisimple_of_simple {E : Type} [Group E] (hs : IsSimpleGroup E)
    (hnc : ∃ a b : E, a * b ≠ b * a) : CFSG.IsQuasisimple E := by
  haveI := hs
  have hc : center E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd ((mem_center_iff.mp (h ▸ mem_top b)) a) hab
  have e : E ⧸ center E ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hperf : Group.IsPerfect E := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator E) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact h
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem ff_perfect_le_of_quot_two {B : Type} [Group B] [Finite B] (E : Subgroup B) [E.Normal]
    (h2 : IsPGroup 2 (B ⧸ E)) (K : Subgroup B) (hK : Group.IsPerfect ↥K) : K ≤ E := by
  haveI := hK
  let f : ↥K →* B ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  haveI : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥f.range := (h2.to_subgroup f.range).isNilpotent
  haveI : Subsingleton ↥f.range := by
    by_contra hns
    haveI : Nontrivial ↥f.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance
  intro k hk
  have h1 : (⟨f ⟨k, hk⟩, MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩⟩ : ↥f.range) = 1 :=
    Subsingleton.elim _ _
  have h3 : f ⟨k, hk⟩ = 1 := congrArg Subtype.val h1
  exact (QuotientGroup.eq_one_iff k).mp h3

end CFSG.OddStandard.SmallF3.Omega
