module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Cfg

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

theorem card_centralizer_one_eq {A : Type*} [Group A] :
    Nat.card (centralizer ({1} : Set A)) = Nat.card A := by
  have : centralizer ({1} : Set A) = ⊤ :=
    eq_top_iff.2 fun g _ => mem_centralizer_singleton_iff.2 (by simp)
  rw [this, Subgroup.card_top]

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

include c

theorem ker_rho_card : Nat.card c.pair.rho.ker = 4 := by
  rw [c.pair.ker_rho, ← c.card_F,
    ← Subgroup.card_map_of_injective (centralizer ({c.u} : Set G)).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  congr 2
  ext g
  simp only [mem_inf]
  tauto

theorem exists_pair_rho_eq (α β : MulAut ↥c.L₁) : ∃ p : ↥c.P, c.pair.rho p = base α β := by
  have : base α β ∈ c.pair.rho.range := by
    rw [c.rho_range]
    exact mem_top _
  obtain ⟨p, hp⟩ := this
  exact ⟨p, hp⟩

omit c [Finite G] in
theorem orderOf_mk_subgroup {L : Subgroup G} {a : G} (ha : a ∈ L) :
    orderOf (⟨a, ha⟩ : ↥L) = orderOf a := Subgroup.orderOf_mk a ha

theorem exists_transport (hA : AutFacts ↥c.L₁) {a b : G} (ha : a ∈ c.L₁) (ha3 : orderOf a = 3)
    (hb : b ∈ c.L₁) (hb3 : orderOf b = 3) :
    ∃ p : G, p * c.x * p⁻¹ = a ∧ (t * p * t) * c.x * (t * p * t)⁻¹ = b := by
  have hex : ∀ {a : G} (ha : a ∈ c.L₁), orderOf a = 3 →
      ∃ α : MulAut ↥c.L₁, α ⟨c.x, c.x_mem⟩ = ⟨a, ha⟩ := by
    intro a ha h
    exact hA.1 _ _ (by rw [orderOf_mk_subgroup c.x_mem]; exact c.x_ord)
      (by rw [orderOf_mk_subgroup ha]; exact h)
  obtain ⟨α, hα⟩ := hex ha ha3
  obtain ⟨β, hβ⟩ := hex hb hb3
  obtain ⟨p, hp⟩ := c.exists_pair_rho_eq α β
  have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := by
    rw [mem_normalizer_iff_map_eq, ← c.pair.rho_mem_baseSubgroup_iff p, hp,
      mem_baseSubgroup_iff, swapChar_base]
  have hr := c.pair.rho_of_normalizes p hn
  rw [hp, base_injective] at hr
  refine ⟨p, ?_, ?_⟩
  · have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.1
    simp only [hα, conjAutOf_apply] at this
    exact this.symm
  · have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.2
    simp only [hβ, conjAutOf_apply] at this
    exact this.symm

theorem exists_conj_pair (hA : AutFacts ↥c.L₁) {a b : G} (ha : a ∈ c.X) (ha1 : a ≠ 1)
    (hb : b ∈ c.Xt) (hb1 : b ≠ 1) :
    ∃ p : G, p * c.x * p⁻¹ = a ∧ p * c.xt * p⁻¹ = b := by
  obtain ⟨b', hb', rfl⟩ := c.exists_conj_of_mem_Xt hb
  have hb'1 : b' ≠ 1 := by
    rintro rfl
    apply hb1
    simp
  obtain ⟨p, h1, h2⟩ := c.exists_transport hA (c.X_le_L₁ ha) (c.orderOf_eq_three_of_mem_X ha ha1)
    (c.X_le_L₁ hb') (c.orderOf_eq_three_of_mem_X hb' hb'1)
  refine ⟨p, h1, ?_⟩
  have htg : t * (t * p * t) = p * t := by
    calc t * (t * p * t) = (t * t) * p * t := by group
      _ = p * t := by rw [c.t_sq, one_mul]
  calc p * (t * c.x * t⁻¹) * p⁻¹ = (p * t) * c.x * (p * t)⁻¹ := by group
    _ = (t * (t * p * t)) * c.x * (t * (t * p * t))⁻¹ := by rw [htg]
    _ = t * ((t * p * t) * c.x * (t * p * t)⁻¹) * t⁻¹ := by group
    _ = t * b' * t⁻¹ := by rw [h2]

theorem isConj_y_mul (hA : AutFacts ↥c.L₁) {a b : G} (ha : a ∈ c.X) (ha1 : a ≠ 1)
    (hb : b ∈ c.Xt) (hb1 : b ≠ 1) : IsConj c.y (a * b) := by
  obtain ⟨p, h1, h2⟩ := c.exists_conj_pair hA ha ha1 hb hb1
  rw [isConj_iff]
  refine ⟨p, ?_⟩
  rw [← h1, ← h2]
  group

theorem isConj_x_of_mem (hA : AutFacts ↥c.L₁) {d : G} (hd : d ∈ c.X ∨ d ∈ c.Xt) (hd1 : d ≠ 1) :
    IsConj c.x d := by
  rcases hd with hd | hd
  · obtain ⟨p, h1, -⟩ := c.exists_conj_pair hA hd hd1 c.xt_mem_Xt c.xt_ne_one
    exact isConj_iff.2 ⟨p, h1⟩
  · obtain ⟨p, -, h2⟩ := c.exists_conj_pair hA c.x_mem_X c.x_ne_one hd hd1
    have h3 : IsConj c.x c.xt := isConj_iff.2 ⟨t, rfl⟩
    exact h3.trans (isConj_iff.2 ⟨p, h2⟩)

theorem card_P_inf_centralizer_x (hA : AutFacts ↥c.L₁) :
    Nat.card ↥(c.P ⊓ centralizer ({c.x} : Set G)) = 103680 := by
  let x' : ↥c.P := ⟨c.x, c.x_mem_P⟩
  let xh : ↥c.L₁ := ⟨c.x, c.x_mem⟩
  have hxho : orderOf xh = 3 := by rw [orderOf_mk_subgroup c.x_mem]; exact c.x_ord
  have hρx : c.pair.rho x' = base (MulAut.conj xh) 1 := c.pair.rho_of_mem c.x c.x_mem
  have ha1 : MulAut.conj xh ≠ 1 := by
    intro h
    apply c.x_ne_one
    refine c.eq_one_of_central_cube c.x_mem (fun b hb => ?_) c.x_cube
    have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨b, hb⟩ : ↥c.L₁) : G)) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hcomap : (c.P ⊓ centralizer ({c.x} : Set G)).subgroupOf c.P =
      (centralizer ({c.pair.rho x'} : Set _)).comap c.pair.rho := by
    ext p
    simp only [mem_subgroupOf, mem_comap, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
    · intro h
      refine ⟨mem_centralizer_singleton_iff.1 p.2, ?_⟩
      have hw : c.pair.rho p ∈ centralizer ({base (MulAut.conj xh) 1} :
          Set (Wr2 (MulAut ↥c.L₁))) := by
        rw [mem_centralizer_singleton_iff, ← hρx]
        exact h
      obtain ⟨c', d', hcd⟩ := exists_base_of_mem_centralizer ha1 hw
      have hbase : c.pair.rho p ∈ (baseSubgroup : Subgroup (Wr2 (MulAut ↥c.L₁))) := by
        rw [hcd]
        exact (mem_baseSubgroup_iff _).2 (swapChar_base c' d')
      have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := by
        rw [mem_normalizer_iff_map_eq]
        exact (c.pair.rho_mem_baseSubgroup_iff p).1 hbase
      have hk : (p : G) * c.x * (p : G)⁻¹ ∈ c.L₁ := (mem_normalizer_iff.1 hn c.x).1 c.x_mem
      have hkP : (p : G) * c.x * (p : G)⁻¹ ∈ c.P := c.pair.K_le hk
      have hρk : c.pair.rho ⟨(p : G) * c.x * (p : G)⁻¹, hkP⟩ = c.pair.rho x' := by
        have : (⟨(p : G) * c.x * (p : G)⁻¹, hkP⟩ : ↥c.P) = p * x' * p⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
      rw [c.pair.rho_of_mem _ hk, hρx] at hρk
      have h5 := (base_injective.1 hρk).1
      have hko : orderOf (⟨(p : G) * c.x * (p : G)⁻¹, hk⟩ : ↥c.L₁) = 3 := by
        rw [orderOf_mk_subgroup hk]
        have := MulEquiv.orderOf_eq (MulAut.conj (p : G)) c.x
        simp only [MulAut.conj_apply] at this
        rw [this]
        exact c.x_ord
      have h6 := hA.2.2.2 _ _ hko hxho h5
      have hkx : (p : G) * c.x * (p : G)⁻¹ = c.x := congrArg Subtype.val h6
      exact mul_inv_eq_iff_eq_mul.1 hkx
  have hsurj' : Function.Surjective c.pair.rho := MonoidHom.range_eq_top.1 c.rho_range
  rw [← Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_left : c.P ⊓ centralizer ({c.x} : Set G) ≤ c.P)).toEquiv,
    hcomap, card_comap_of_surj c.pair.rho hsurj', c.ker_rho_card, hρx,
    card_centralizer_base_of_not_isConj (a := MulAut.conj xh) (b := 1)
      (fun h => ha1 (isConj_one_left.1 h)),
    hA.2.1 _ hxho, card_centralizer_one_eq, hA.2.2.1]

theorem not_isConj_x_y (hA : AutFacts ↥c.L₁) : ¬ IsConj c.x c.y := by
  intro h
  have h1 := card_centralizer_eq_of_isConj h
  rw [c.card_Cy] at h1
  have h2 := Subgroup.card_dvd_of_le
    (inf_le_right : c.P ⊓ centralizer ({c.x} : Set G) ≤ centralizer ({c.x} : Set G))
  rw [c.card_P_inf_centralizer_x hA, h1] at h2
  omega

theorem conj_xt_eq_of_mem (hA : AutFacts ↥c.L₁) {g : G}
    (hz : ∃ z ∈ c.Zc, g * c.xt * g⁻¹ = c.xt * z) : g * c.xt * g⁻¹ = c.xt := by
  obtain ⟨z, hzZ, hgz⟩ := hz
  have hcom : c.xt * z = z * c.xt := (c.cm_Z_xt.comm hzZ (mem_zpowers _)).symm
  have h1 : (g * c.xt * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, c.xt_cube]
    simp
  rw [hgz, (show Commute c.xt z from hcom).mul_pow, c.xt_cube, one_mul] at h1
  have hzX : z ∈ c.X := c.mem_X_of_cube hzZ h1
  by_cases hz1 : z = 1
  · rw [hgz, hz1, mul_one]
  · exfalso
    have hxt : IsConj c.x c.xt := c.isConj_x_of_mem hA (Or.inr c.xt_mem_Xt) c.xt_ne_one
    have hy : IsConj c.y (z * c.xt) := c.isConj_y_mul hA hzX hz1 c.xt_mem_Xt c.xt_ne_one
    have hg : IsConj c.xt (g * c.xt * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    rw [hgz, hcom] at hg
    exact c.not_isConj_x_y hA ((hxt.trans hg).trans hy.symm)

end S14Cfg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
