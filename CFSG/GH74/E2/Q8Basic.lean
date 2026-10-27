module

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.Cl2BPair
public import CFSG.GH74.E2.Cl2Weights

public section

namespace CFSG.GH74.E2

open Subgroup

namespace Q8

structure Good (X : Type*) [Group X] [Finite X] (c : MulAut X) : Prop where
  pgroup : IsPGroup 2 X
  rank_eq : Group.rank X = 2
  sub_rank : ∀ P : Subgroup X, Group.rank ↥P ≤ 2
  cube : c ^ 3 = 1
  fpf : ∀ x : X, c x * x⁻¹ ∈ frattini X → x ∈ frattini X

variable {X : Type*} [Group X] [Finite X] {c : MulAut X}

theorem Good.card_V (hg : Good X c) : Nat.card (X ⧸ frattini X) = 4 := by
  rw [card_frattini_quotient_eq_two_pow_rank hg.pgroup, hg.rank_eq]
  norm_num

theorem V_sq (hX : IsPGroup 2 X) (v : X ⧸ frattini X) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact mul_self_mem_frattini hX g

theorem V_comm (hX : IsPGroup 2 X) (v w : X ⧸ frattini X) : v * w = w * v := by
  have hi : ∀ z : X ⧸ frattini X, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (V_sq hX z)
  calc v * w = (v * w)⁻¹ := (hi (v * w)).symm
    _ = w⁻¹ * v⁻¹ := mul_inv_rev v w
    _ = w * v := by rw [hi v, hi w]

@[expose] noncomputable def cV (hg : Good X c) : MulAut (X ⧸ frattini X) := aV c hg.cube

theorem cV_mk (hg : Good X c) (x : X) :
    cV hg (x : X ⧸ frattini X) = ((c x : X) : X ⧸ frattini X) := by
  simp [cV, aV, quotAut_mk]

theorem cV_pow3 (hg : Good X c) : cV hg ^ 3 = 1 :=
  quotAut_pow_three c (frattini X) (frattini_inv_iff hg.cube) hg.cube

theorem cV_cube (hg : Good X c) (v : X ⧸ frattini X) : cV hg (cV hg (cV hg v)) = v :=
  Cl2Wt.cube_apply (cV_pow3 hg) v

theorem cV_fpf (hg : Good X c) {v : X ⧸ frattini X} (hv : cV hg v = v) : v = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rw [cV_mk] at hv
  have h1 : c x * x⁻¹ ∈ frattini X := by
    have := QuotientGroup.eq_iff_div_mem.1 hv
    simpa [div_eq_mul_inv] using this
  exact (QuotientGroup.eq_one_iff x).2 (hg.fpf x h1)

theorem V_norm (hg : Good X c) (v : X ⧸ frattini X) : v * cV hg v * cV hg (cV hg v) = 1 := by
  apply cV_fpf hg
  rw [map_mul, map_mul, cV_cube hg]
  have := V_comm hg.pgroup (v * cV hg v) (cV hg (cV hg v))
  calc cV hg v * cV hg (cV hg v) * v = v * (cV hg v * cV hg (cV hg v)) :=
        V_comm hg.pgroup _ _
    _ = v * cV hg v * cV hg (cV hg v) := by rw [mul_assoc]

theorem X_norm (hg : Good X c) (g : X) : g * c g * c (c g) ∈ frattini X := by
  have h := V_norm hg (g : X ⧸ frattini X)
  rw [cV_mk, cV_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_one_iff] at h
  exact h

theorem fixed_mem_frattini (hg : Good X c) {x : X} (hx : c x = x) : x ∈ frattini X :=
  hg.fpf x (by rw [hx, mul_inv_cancel]; exact Subgroup.one_mem _)

theorem exists_not_mem_frattini (hg : Good X c) : ∃ x : X, x ∉ frattini X := by
  by_contra h
  push Not at h
  have h4 := hg.card_V
  have h1 : Nat.card (X ⧸ frattini X) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [(QuotientGroup.eq_one_iff x).2 (h x), (QuotientGroup.eq_one_iff y).2 (h y)]
  omega

theorem V_inv_subgroup (hg : Good X c) (H : Subgroup (X ⧸ frattini X))
    (hH : ∀ x ∈ H, cV hg x ∈ H) : H = ⊥ ∨ H = ⊤ := by
  have h4 := hg.card_V
  have hdvd : Nat.card H ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = Nat.card (X ⧸ frattini X) by rw [h4]; norm_num]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨i, hi, hiH⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases i
  · left
    exact Subgroup.card_eq_one.1 (by simpa using hiH)
  · exfalso
    have h2 : Nat.card H = 2 := by simpa using hiH
    obtain ⟨u, hu1, hu2⟩ := (Nat.card_eq_two_iff' (1 : H)).1 h2
    have hcu : cV hg (u : X ⧸ frattini X) ∈ H := hH u u.2
    have hne : (⟨cV hg u, hcu⟩ : H) ≠ 1 := fun e => hu1 (by
      have h1 : cV hg (u : X ⧸ frattini X) = 1 := congrArg Subtype.val e
      exact Subtype.ext ((cV hg).map_eq_one_iff.1 h1))
    have := hu2 _ hne
    have hfix : cV hg (u : X ⧸ frattini X) = u := congrArg Subtype.val this
    exact hu1 (Subtype.ext (cV_fpf hg hfix))
  · right
    exact Subgroup.eq_top_of_card_eq H (by rw [h4]; simpa using hiH)

theorem inv_between (hg : Good X c) {H : Subgroup X} (hΦ : frattini X ≤ H)
    (hH : ∀ x ∈ H, c x ∈ H) : H = frattini X ∨ H = ⊤ := by
  have hmap : ∀ v ∈ H.map (QuotientGroup.mk' (frattini X)),
      cV hg v ∈ H.map (QuotientGroup.mk' (frattini X)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨c x, hH x hx, ?_⟩
    exact (cV_mk hg x).symm
  have hcm : (H.map (QuotientGroup.mk' (frattini X))).comap (QuotientGroup.mk' (frattini X)) =
      H := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hΦ]
  rcases V_inv_subgroup hg _ hmap with h0 | h1
  · left
    rw [← hcm, h0, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · right
    rw [← hcm, h1, Subgroup.comap_top]

theorem closure_pair (hg : Good X c) {x : X} (hx : x ∉ frattini X) :
    Subgroup.closure ({x, c x} : Set X) = ⊤ := by
  have hxH : x ∈ Subgroup.closure ({x, c x} : Set X) := Subgroup.subset_closure (by simp)
  have hcxH : c x ∈ Subgroup.closure ({x, c x} : Set X) := Subgroup.subset_closure (by simp)
  have hcc : c (c x) ∈ Subgroup.closure ({x, c x} : Set X) ⊔ frattini X := by
    have h1 : c (c x) = (x * c x)⁻¹ * (x * c x * c (c x)) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left
      (Subgroup.mul_mem _ hxH hcxH))) (Subgroup.mem_sup_right (X_norm hg x))
  have hK : Subgroup.closure ({x, c x} : Set X) ⊔ frattini X ≤
      (Subgroup.closure ({x, c x} : Set X) ⊔ frattini X).comap c.toMonoidHom := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
    · intro y hy
      rcases Set.mem_insert_iff.1 hy with rfl | hy'
      · exact Subgroup.mem_sup_left hcxH
      · rw [Set.mem_singleton_iff.1 hy']
        exact hcc
    · intro y hy
      exact Subgroup.mem_sup_right (frattini_inv c hy)
  have hsup : Subgroup.closure ({x, c x} : Set X) ⊔ frattini X = ⊤ := by
    rcases inv_between hg le_sup_right (fun y hy => hK hy) with h1 | h1
    · exact absurd (h1 ▸ Subgroup.mem_sup_left hxH) hx
    · exact h1
  exact frattini_nongenerating hsup

theorem exists_inv_mul (hg : Good X c) (x : X) : ∃ g : X, x⁻¹ * (g⁻¹ * c g) ∈ frattini X := by
  let f : (X ⧸ frattini X) → (X ⧸ frattini X) := fun v => v⁻¹ * cV hg v
  have hinj : Function.Injective f := by
    intro v w h
    have h1 : cV hg v = v * (w⁻¹ * cV hg w) := by
      calc cV hg v = v * (v⁻¹ * cV hg v) := by group
        _ = v * (w⁻¹ * cV hg w) := by rw [show v⁻¹ * cV hg v = w⁻¹ * cV hg w from h]
    have h2 : cV hg (v * w⁻¹) = v * w⁻¹ := by
      rw [map_mul, map_inv, h1]
      group
    have h3 := cV_fpf hg h2
    exact mul_inv_eq_one.1 h3
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) (x : X ⧸ frattini X)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨g, ?_⟩
  have : ((g⁻¹ * c g : X) : X ⧸ frattini X) = (x : X ⧸ frattini X) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have := hw
    simp only [f, cV_mk] at this
    exact this
  exact QuotientGroup.eq.1 this.symm

end Q8

end CFSG.GH74.E2
