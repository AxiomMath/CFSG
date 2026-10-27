module

public import CFSG.Fischer.Classification.Skeleton
import CFSG.Fischer.Classification.Basic.Center
import CFSG.Fischer.Classification.Symplectic.Basic
import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Fischer.Classification.Symplectic

namespace TransvectionSymplectic

section Deriv

variable {G K : Type} {V : Type*} [Group G] [Group K] [Group V]

lemma rho_mem_map_pi_ker (ρ : G →* MulAut V) (π : G →* K) {x : G}
    (hx : x ∈ ρ.ker ⊔ π.ker) : ρ x ∈ (π.ker).map ρ := by
  rw [Subgroup.mem_sup_of_normal_left (s := ρ.ker) (t := π.ker)] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  rw [← hab]
  rw [map_mul, (MonoidHom.mem_ker).1 ha, one_mul]
  exact Subgroup.mem_map_of_mem ρ hb

lemma commutator_le_sup_ker (ρ : G →* MulAut V) (π : G →* K)
    (hπ : Function.Surjective π) (hN : commutator K ≤ (ρ.ker).map π) :
    commutator G ≤ ρ.ker ⊔ π.ker := by
  intro x hx
  have hπx : π x ∈ commutator K := by
    have hmap : (commutator G).map π = commutator K := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπ]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem π hx
  have hxN : π x ∈ (ρ.ker).map π := hN hπx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hxN
  have hyx : x * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have hx_eq : x = (x * y⁻¹) * y := by group
  rw [hx_eq, sup_comm]
  exact Subgroup.mul_mem_sup hyx hy

lemma derivedSeries_two_le_ker (ρ : G →* MulAut V) (π : G →* K)
    (hker : π.ker ≤ Subgroup.center G) (hG' : commutator G ≤ ρ.ker ⊔ π.ker) :
    derivedSeries G 2 ≤ ρ.ker := by
  rw [show derivedSeries G 2 = ⁅commutator G, commutator G⁆ by
    simp [derivedSeries_succ, commutator_def]]
  refine Subgroup.commutator_le.mpr ?_
  intro x hx y hy
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have hxρ : ρ x ∈ (π.ker).map ρ := rho_mem_map_pi_ker ρ π (hG' hx)
  have hyρ : ρ y ∈ (π.ker).map ρ := rho_mem_map_pi_ker ρ π (hG' hy)
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 hxρ
  obtain ⟨b, hb, hyb⟩ := Subgroup.mem_map.1 hyρ
  rw [← hxa, ← hyb]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (by
    rw [← map_mul, ← map_mul]
    congr 1
    exact ((Subgroup.mem_center_iff.1 (hker ha)) b).symm)

end Deriv

section PiNe

variable {G K : Type} {V : Type*} [Group G] [Group K] [Group V]
variable {ρ : G →* MulAut V} {π : G →* K} {D : Set G}

lemma pi_ne_of_rho_eq {d e : G} (hd : d ∈ D) (he : e ∈ D) (hne : d ≠ e)
    (hself : ∀ x ∈ D, x * x = 1)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card π.ker)) :
    π d ≠ π e := by
  intro hπeq
  have hmem : d * e ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hπeq, ← map_mul, hself e he, map_one]
  have hcent : d * e ∈ Subgroup.center G := hker hmem
  have hc := (Subgroup.mem_center_iff.1 hcent) d
  have hcomm : d * e = e * d := by
    calc d * e = (d * e) * (d * d⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = ((d * e) * d) * d⁻¹ := by group
      _ = (d * (d * e)) * d⁻¹ := by rw [hc]
      _ = (d * d) * e * d⁻¹ := by group
      _ = e * d := by
            rw [hself d hd, one_mul, inv_eq_of_mul_eq_one_right (hself d hd)]
  have hsq : (d * e) ^ 2 = 1 := by
    rw [Commute.mul_pow hcomm, pow_two d, pow_two e, hself d hd, hself e he, mul_one]
  have hdvd2 : orderOf (d * e) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hdvdker : orderOf (d * e) ∣ Nat.card π.ker :=
    Subgroup.orderOf_dvd_natCard π.ker hmem
  have hodd_o : Odd (orderOf (d * e)) := Odd.of_dvd_nat hodd hdvdker
  obtain ⟨k, hk⟩ := hodd_o
  have hle : orderOf (d * e) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have hone : orderOf (d * e) = 1 := by omega
  have hde1 : d * e = 1 := (orderOf_eq_one_iff).1 hone
  have hdeq : d = e := by
    rw [eq_inv_of_mul_eq_one_left hde1, inv_eq_of_mul_eq_one_right (hself e he)]
  exact hne hdeq

end PiNe

section Generic

variable {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]

noncomputable def tvPhi (t : A →+ A) (u : A) : ZMod 2 := by
  classical
  exact if t u = u then 0 else 1

omit [Module (ZMod 2) A] in
lemma tvPhi_eq_zero_iff (t : A →+ A) (u : A) : tvPhi t u = 0 ↔ t u = u := by
  classical
  unfold tvPhi
  by_cases h : t u = u <;> simp [h]

omit [Module (ZMod 2) A] in
lemma tvPhi_eq_one_iff (t : A →+ A) (u : A) : tvPhi t u = 1 ↔ t u ≠ u := by
  classical
  unfold tvPhi
  by_cases h : t u = u <;> simp [h]

lemma tvPhi_apply (t : A →+ A) {c : A} (hc : ∀ u, t u = u ∨ t u = u + c) (hc0 : c ≠ 0)
    (u : A) : t u = u + (tvPhi t u) • c := by
  classical
  rcases hc u with h | h
  · rw [h, show tvPhi t u = 0 from by simp [tvPhi, h], zero_smul, add_zero]
  · have hne : t u ≠ u := by
      rw [h]
      intro hh
      have hh' : c = 0 := by
        have := congrArg (fun x => x - u) hh
        simpa using this
      exact hc0 hh'
    rw [h, show tvPhi t u = 1 from by simp [tvPhi, hne], one_smul]

lemma tvPhi_fixes (t : A →+ A) {c : A} (hc : ∀ u, t u = u ∨ t u = u + c) (hc0 : c ≠ 0)
    (ht : ∀ u, t (t u) = u) : tvPhi t c = 0 := by
  rw [tvPhi_eq_zero_iff]
  by_contra h
  have h1 : t c = c + c := by
    rcases hc c with hh | hh
    · exact absurd hh h
    · exact hh
  have h2 : c = t (t c) := (ht c).symm
  rw [h1, map_add, h1] at h2
  have h3 : c = 0 := by simpa [zmod_two_add_self] using h2
  exact hc0 h3

lemma tvPhi_eq_of_apply (t : A →+ A) {c : A} (hc0 : c ≠ 0) {u : A} {a : ZMod 2}
    (h : t u = u + a • c) : tvPhi t u = a := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [zero_smul, add_zero] at h
    exact (tvPhi_eq_zero_iff t u).2 h
  · have hne : t u ≠ u := by
      rw [h, one_smul]
      intro hh
      have hh' : c = 0 := by
        have := congrArg (fun x => x - u) hh
        simpa using this
      exact hc0 hh'
    exact (tvPhi_eq_one_iff t u).2 hne

lemma tvPhi_add (t : A →+ A) {c : A} (hc : ∀ u, t u = u ∨ t u = u + c) (hc0 : c ≠ 0)
    (u v : A) : tvPhi t (u + v) = tvPhi t u + tvPhi t v := by
  refine tvPhi_eq_of_apply t hc0 ?_
  rw [map_add, tvPhi_apply t hc hc0 u, tvPhi_apply t hc hc0 v, add_smul]
  abel

end Generic

section Action

variable {G V : Type*} [Group G] [CommGroup V] [Module (ZMod 2) (Additive V)]

noncomputable def rhoAddHom (ρ : G →* MulAut V) (g : G) : Additive V →+ Additive V :=
  (MulEquiv.toAdditive (ρ g)).toAddMonoidHom

variable {ρ : G →* MulAut V} {D : Set G} {C : G → Additive V}

omit [Module (ZMod 2) (Additive V)] in
lemma rhoAddHom_mul (d e : G) (u : Additive V) :
    rhoAddHom ρ (d * e) u = rhoAddHom ρ d (rhoAddHom ρ e u) := by
  change Additive.ofMul ((ρ (d * e)) (Additive.toMul u)) =
    Additive.ofMul ((ρ d) ((ρ e) (Additive.toMul u)))
  rw [map_mul]
  rfl

omit [Module (ZMod 2) (Additive V)] in
lemma rhoAddHom_self (d : G) (hd : d * d = 1) (u : Additive V) :
    rhoAddHom ρ d (rhoAddHom ρ d u) = u := by
  change Additive.ofMul ((ρ d * ρ d) (Additive.toMul u)) = u
  rw [show ρ d * ρ d = 1 from by rw [← map_mul, hd, map_one]]
  rfl

omit [Module (ZMod 2) (Additive V)] in
lemma orderOf_mul_eq_three_of_not_commute {d e : G} (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) (hde : d * e ≠ e * d) :
    orderOf (d * e) = 3 := by
  rcases h3de with h | h | h
  · have h1 : d * e = 1 := (orderOf_eq_one_iff).1 h
    have hed : e * d = (d * e)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd2, inv_eq_of_mul_eq_one_right he2]
    exact absurd (by rw [hed, h1, inv_one]) hde
  · have h2 : (d * e) ^ 2 = 1 := by rw [← h, pow_orderOf_eq_one]
    rw [pow_two] at h2
    have hinv : (d * e)⁻¹ = d * e := inv_eq_of_mul_eq_one_right h2
    have hcomm : d * e = e * d := by
      rw [← hinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hd2,
        inv_eq_of_mul_eq_one_right he2]
    exact absurd hcomm hde
  · exact h

omit [Module (ZMod 2) (Additive V)] in
lemma mulAut_commute_of_addCommute {a b : G}
    (h : ∀ u : Additive V, rhoAddHom ρ a (rhoAddHom ρ b u) = rhoAddHom ρ b (rhoAddHom ρ a u)) :
    ρ a * ρ b = ρ b * ρ a := by
  ext v
  have hv := h (Additive.ofMul v)
  change Additive.ofMul ((ρ a) ((ρ b) v)) = Additive.ofMul ((ρ b) ((ρ a) v)) at hv
  exact Additive.ofMul.injective hv

omit [Module (ZMod 2) (Additive V)] in
lemma commute_of_rho_commute {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hinj : Set.InjOn ρ D)
    (hρ : ρ d * ρ e = ρ e * ρ d) : d * e = e * d := by
  by_contra hde
  have h3 : orderOf (d * e) = 3 := orderOf_mul_eq_three_of_not_commute hd2 he2 h3de hde
  have hcomm : Commute (ρ d) (ρ e) := hρ
  have h2d : (ρ d) ^ 2 = 1 := by rw [pow_two, ← map_mul, hd2, map_one]
  have h2e : (ρ e) ^ 2 = 1 := by rw [pow_two, ← map_mul, he2, map_one]
  have hprod2 : (ρ d * ρ e) ^ 2 = 1 := by
    rw [hcomm.mul_pow, h2d, h2e, mul_one]
  have hprod3 : (ρ d * ρ e) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow,
      show (d * e) ^ 3 = 1 from by rw [← h3, pow_orderOf_eq_one], map_one]
  have hprod1 : ρ d * ρ e = 1 := by
    have h := hprod3
    rw [show (ρ d * ρ e) ^ 3 = (ρ d * ρ e) ^ 2 * (ρ d * ρ e) by
      rw [pow_succ, pow_two]] at h
    rwa [hprod2, one_mul] at h
  have hρeq : ρ d = ρ e := by
    rw [← inv_eq_of_mul_eq_one_right h2d, inv_eq_of_mul_eq_one_right hprod1]
  exact hde (by rw [hinj hd he hρeq])

omit [Module (ZMod 2) (Additive V)] in
lemma rhoAddHom_id_iff (g : G) :
    (∀ u : Additive V, rhoAddHom ρ g u = u) ↔ ρ g = 1 := by
  constructor
  · intro h
    ext u
    have hu := h (Additive.ofMul u)
    change Additive.ofMul ((ρ g) u) = Additive.ofMul u at hu
    exact Additive.ofMul.injective hu
  · intro h u
    change Additive.ofMul ((ρ g) (Additive.toMul u)) = u
    rw [h]
    rfl

omit [Module (ZMod 2) (Additive V)] in
lemma C_ne_zero {d : G} (hC : ∀ d, d ∈ D → ∀ u : Additive V,
    rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d) (hd : d ∈ D) (hne : ρ d ≠ 1) :
    C d ≠ 0 := by
  intro h0
  apply hne
  rw [← rhoAddHom_id_iff]
  intro u
  rcases hC d hd u with h | h
  · exact h
  · rwa [h0, add_zero] at h

lemma commute_of_phi_zero {d e : G} {cd ce : Additive V}
    (hcd : ∀ u, rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + cd)
    (hce : ∀ u, rhoAddHom ρ e u = u ∨ rhoAddHom ρ e u = u + ce)
    (hcd0 : cd ≠ 0) (hce0 : ce ≠ 0)
    (hbde : tvPhi (rhoAddHom ρ d) ce = 0) (hbed : tvPhi (rhoAddHom ρ e) cd = 0)
    (u : Additive V) :
    rhoAddHom ρ d (rhoAddHom ρ e u) = rhoAddHom ρ e (rhoAddHom ρ d u) := by
  rw [tvPhi_apply (rhoAddHom ρ e) hce hce0 u,
    tvPhi_apply (rhoAddHom ρ d) hcd hcd0 u]
  rw [map_add, map_add, ZMod.map_smul (rhoAddHom ρ d), ZMod.map_smul (rhoAddHom ρ e)]
  rw [tvPhi_apply (rhoAddHom ρ d) hcd hcd0 u,
    tvPhi_apply (rhoAddHom ρ e) hce hce0 u]
  rw [show rhoAddHom ρ d ce = ce from (tvPhi_eq_zero_iff _ _).1 hbde,
    show rhoAddHom ρ e cd = cd from (tvPhi_eq_zero_iff _ _).1 hbed]
  abel

lemma square_of_phi {d e : G} {cd ce : Additive V}
    (hcd : ∀ u, rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + cd)
    (hce : ∀ u, rhoAddHom ρ e u = u ∨ rhoAddHom ρ e u = u + ce)
    (hcd0 : cd ≠ 0) (hce0 : ce ≠ 0)
    (hbde : tvPhi (rhoAddHom ρ d) ce = 1)
    (hbed : tvPhi (rhoAddHom ρ e) cd = 0)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (u : Additive V) :
    rhoAddHom ρ d (rhoAddHom ρ e (rhoAddHom ρ d (rhoAddHom ρ e u))) =
      u + (tvPhi (rhoAddHom ρ e) u) • cd := by
  let t := rhoAddHom ρ d
  let s := rhoAddHom ρ e
  have ht2 : ∀ v, t (t v) = v := fun v => rhoAddHom_self d hd2 v
  have hs2 : ∀ v, s (s v) = v := fun v => rhoAddHom_self e he2 v
  have hta : t cd = cd :=
    (tvPhi_eq_zero_iff t cd).1 (tvPhi_fixes t hcd hcd0 ht2)
  have hsb : s ce = ce :=
    (tvPhi_eq_zero_iff s ce).1 (tvPhi_fixes s hce hce0 hs2)
  have htb : t ce = ce + cd := by
    rcases hcd ce with h | h
    · exact absurd h ((tvPhi_eq_one_iff t ce).1 hbde)
    · exact h
  have hsa : s cd = cd := (tvPhi_eq_zero_iff s cd).1 hbed
  have hA : s u = u + (tvPhi s u) • ce := tvPhi_apply s hce hce0 u
  have hB : t (s u) = t u + (tvPhi s u) • (ce + cd) := by
    rw [hA, map_add, ZMod.map_smul t, htb]
  have hC : s (t (s u)) = s u + (tvPhi t u) • cd + (tvPhi s u) • (ce + cd) := by
    rw [hB, map_add, ZMod.map_smul s, map_add, hsb, hsa]
    rw [tvPhi_apply t hcd hcd0 u, map_add, ZMod.map_smul s, hsa]
  have hD : t (s (t (s u))) = t u + (tvPhi s u) • (ce + cd) +
      (tvPhi t u) • cd + (tvPhi s u) • ((ce + cd) + cd) := by
    rw [hC]
    simp only [map_add, ZMod.map_smul t, htb, hta, hB]
  rw [hD, tvPhi_apply t hcd hcd0 u]
  have h1 : tvPhi t u • cd + tvPhi t u • cd = 0 := zmod_two_add_self _
  have h2 : (ce + cd) + ((ce + cd) + cd) = cd := by
    rw [show (ce + cd) + ((ce + cd) + cd) = (ce + ce) + (cd + cd) + cd by abel,
      zmod_two_add_self ce, zmod_two_add_self cd, zero_add, zero_add]
  calc
    u + tvPhi t u • cd + tvPhi s u • (ce + cd) + tvPhi t u • cd +
        tvPhi s u • ((ce + cd) + cd)
        = u + (tvPhi t u • cd + tvPhi t u • cd) +
          (tvPhi s u • (ce + cd) + tvPhi s u • ((ce + cd) + cd)) := by abel
    _ = u + 0 + tvPhi s u • ((ce + cd) + ((ce + cd) + cd)) := by
          rw [h1, ← smul_add]
    _ = u + tvPhi s u • cd := by rw [h2]; simp

lemma square_eq {d e : G} {cd ce : Additive V}
    (hcd : ∀ u, rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + cd)
    (hce : ∀ u, rhoAddHom ρ e u = u ∨ rhoAddHom ρ e u = u + ce)
    (hcd0 : cd ≠ 0) (hce0 : ce ≠ 0)
    (hbde : tvPhi (rhoAddHom ρ d) ce = 1)
    (hbed : tvPhi (rhoAddHom ρ e) cd = 0)
    (hd2 : d * d = 1) (he2 : e * e = 1) (u : Additive V) :
    rhoAddHom ρ ((d * e) ^ 2) u = u + (tvPhi (rhoAddHom ρ e) u) • cd := by
  rw [pow_two, rhoAddHom_mul, rhoAddHom_mul, rhoAddHom_mul]
  exact square_of_phi hcd hce hcd0 hce0 hbde hbed hd2 he2 u

lemma square_eq_sq {d e : G} {cd ce : Additive V}
    (hcd : ∀ u, rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + cd)
    (hce : ∀ u, rhoAddHom ρ e u = u ∨ rhoAddHom ρ e u = u + ce)
    (hcd0 : cd ≠ 0) (hce0 : ce ≠ 0)
    (hbde : tvPhi (rhoAddHom ρ d) ce = 1)
    (hbed : tvPhi (rhoAddHom ρ e) cd = 0)
    (hd2 : d * d = 1) (he2 : e * e = 1) (u : Additive V) :
    rhoAddHom ρ ((d * e) ^ 2) (rhoAddHom ρ ((d * e) ^ 2) u) = u := by
  rw [square_eq hcd hce hcd0 hce0 hbde hbed hd2 he2,
    square_eq hcd hce hcd0 hce0 hbde hbed hd2 he2]
  have hφ : tvPhi (rhoAddHom ρ e) (u + tvPhi (rhoAddHom ρ e) u • cd) =
      tvPhi (rhoAddHom ρ e) u := by
    rw [tvPhi_add (rhoAddHom ρ e) hce hce0]
    have hzero : tvPhi (rhoAddHom ρ e) (tvPhi (rhoAddHom ρ e) u • cd) = 0 := by
      rw [tvPhi_eq_zero_iff, ZMod.map_smul (rhoAddHom ρ e),
        (tvPhi_eq_zero_iff (rhoAddHom ρ e) cd).1 hbed]
    rw [hzero, add_zero]
  rw [hφ]
  calc
    u + tvPhi (rhoAddHom ρ e) u • cd + tvPhi (rhoAddHom ρ e) u • cd
        = u + (tvPhi (rhoAddHom ρ e) u • cd + tvPhi (rhoAddHom ρ e) u • cd) := by
          abel
    _ = u + 0 := by rw [zmod_two_add_self]
    _ = u := by rw [add_zero]

lemma phi_contra {d e : G}
    (hC : ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d)
    (hd : d ∈ D) (he : e ∈ D) (hne_d : ρ d ≠ 1) (hne_e : ρ e ≠ 1)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hbde : tvPhi (rhoAddHom ρ d) (C e) = 1)
    (hbed : tvPhi (rhoAddHom ρ e) (C d) = 0) : False := by
  have hcd := hC d hd
  have hce := hC e he
  have hcd0 := C_ne_zero hC hd hne_d
  have hce0 := C_ne_zero hC he hne_e
  have hsq := square_eq hcd hce hcd0 hce0 hbde hbed hd2 he2
  obtain ⟨u, hu⟩ : ∃ u : Additive V, tvPhi (rhoAddHom ρ e) u = 1 := by
    by_contra h
    have h0 : ∀ u : Additive V, tvPhi (rhoAddHom ρ e) u = 0 := fun u =>
      (zmod_two_cases _).resolve_right (fun h1 => h ⟨u, h1⟩)
    have hall : ∀ u : Additive V, rhoAddHom ρ e u = u := fun u =>
      (tvPhi_eq_zero_iff _ _).1 (h0 u)
    exact hne_e ((rhoAddHom_id_iff (ρ := ρ) e).1 hall)
  have hne_rho : ρ ((d * e) ^ 2) ≠ 1 := by
    intro h
    have h1 : rhoAddHom ρ ((d * e) ^ 2) u = u := by
      change Additive.ofMul ((ρ ((d * e) ^ 2)) (Additive.toMul u)) = u
      rw [h]
      rfl
    rw [hsq u, hu, one_smul] at h1
    have hc0 : C d = 0 := by
      have := congrArg (fun x => x - u) h1
      simpa using this
    exact hcd0 hc0
  have hsq2 : ∀ u : Additive V,
      rhoAddHom ρ ((d * e) ^ 2) (rhoAddHom ρ ((d * e) ^ 2) u) = u :=
    square_eq_sq hcd hce hcd0 hce0 hbde hbed hd2 he2
  have hρx2 : (ρ ((d * e) ^ 2)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, ← rhoAddHom_id_iff]
    intro u
    rw [rhoAddHom_mul]
    exact hsq2 u
  have hx3 : ((d * e) ^ 2) ^ 3 = 1 := by
    have h6 : (d * e) ^ 6 = 1 := by
      have hdvd : orderOf (d * e) ∣ 6 := by
        rcases h3de with h | h | h <;> rw [h] <;> norm_num
      exact (orderOf_dvd_iff_pow_eq_one).1 hdvd
    rwa [← pow_mul, show 2 * 3 = 6 by norm_num]
  have hρx3 : (ρ ((d * e) ^ 2)) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hρx1 : ρ ((d * e) ^ 2) = 1 := by
    have h := hρx3
    rw [show (ρ ((d * e) ^ 2)) ^ 3 = (ρ ((d * e) ^ 2)) ^ 2 * ρ ((d * e) ^ 2) by
      rw [pow_succ, pow_two]] at h
    rwa [hρx2, one_mul] at h
  exact hne_rho hρx1

lemma phi_symm {d e : G}
    (hC : ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d)
    (hd : d ∈ D) (he : e ∈ D) (hne_d : ρ d ≠ 1) (hne_e : ρ e ≠ 1)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    tvPhi (rhoAddHom ρ d) (C e) = tvPhi (rhoAddHom ρ e) (C d) := by
  rcases zmod_two_cases (tvPhi (rhoAddHom ρ d) (C e)) with hde | hde <;>
    rcases zmod_two_cases (tvPhi (rhoAddHom ρ e) (C d)) with hed | hed
  · rw [hde, hed]
  · exfalso
    have h3ed : orderOf (e * d) ∈ ({1, 2, 3} : Set ℕ) := by
      have hinv : e * d = (d * e)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hd2, inv_eq_of_mul_eq_one_right he2]
      rw [hinv, orderOf_inv]
      exact h3de
    exact phi_contra hC he hd hne_e hne_d he2 hd2 h3ed hed hde
  · exfalso
    exact phi_contra hC hd he hne_d hne_e hd2 he2 h3de hde hed
  · rw [hde, hed]

lemma conj_both {d e : G} {cd ce : Additive V}
    (hcd : ∀ u, rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + cd)
    (hce : ∀ u, rhoAddHom ρ e u = u ∨ rhoAddHom ρ e u = u + ce)
    (hcd0 : cd ≠ 0) (hce0 : ce ≠ 0)
    (hbde : tvPhi (rhoAddHom ρ d) ce = 1)
    (hbed : tvPhi (rhoAddHom ρ e) cd = 1)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (u : Additive V) :
    rhoAddHom ρ d (rhoAddHom ρ e (rhoAddHom ρ d u)) =
      u + (tvPhi (rhoAddHom ρ e) u + tvPhi (rhoAddHom ρ d) u) • (ce + cd) := by
  let t := rhoAddHom ρ d
  let s := rhoAddHom ρ e
  have ht2 : ∀ v, t (t v) = v := fun v => rhoAddHom_self d hd2 v
  have hs2 : ∀ v, s (s v) = v := fun v => rhoAddHom_self e he2 v
  have hta : t cd = cd :=
    (tvPhi_eq_zero_iff t cd).1 (tvPhi_fixes t hcd hcd0 ht2)
  have hsb : s ce = ce :=
    (tvPhi_eq_zero_iff s ce).1 (tvPhi_fixes s hce hce0 hs2)
  have htb : t ce = ce + cd := by
    rcases hcd ce with h | h
    · exact absurd h ((tvPhi_eq_one_iff t ce).1 hbde)
    · exact h
  have hsa : s cd = cd + ce := by
    rcases hce cd with h | h
    · exact absurd h ((tvPhi_eq_one_iff s cd).1 hbed)
    · exact h
  have hA : t u = u + (tvPhi t u) • cd := tvPhi_apply t hcd hcd0 u
  have hBt : t (s u) = t u + (tvPhi s u) • (ce + cd) := by
    rw [tvPhi_apply s hce hce0 u, map_add, ZMod.map_smul t, htb]
  have hBs : s (t u) = s u + (tvPhi t u) • (cd + ce) := by
    rw [hA, map_add, ZMod.map_smul s, hsa]
  have hC : t (s (t u)) = t u + (tvPhi s u) • (ce + cd) +
      (tvPhi t u) • ce := by
    rw [hBs, map_add, ZMod.map_smul t, hBt, map_add, htb, hta]
    rw [show cd + (ce + cd) = ce by
      rw [show cd + (ce + cd) = (cd + cd) + ce by abel, zmod_two_add_self cd, zero_add]]
  rw [hC, hA, add_smul, smul_add, smul_add]
  abel

lemma phi_ded {d e z : G}
    (hC : ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d)
    (hd : d ∈ D) (he : e ∈ D) (_hz : z ∈ D)
    (hne_d : ρ d ≠ 1) (hne_e : ρ e ≠ 1)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hde1 : tvPhi (rhoAddHom ρ d) (C e) = 1) :
    tvPhi (rhoAddHom ρ (d * e * d)) (C z) =
      tvPhi (rhoAddHom ρ d) (C z) + tvPhi (rhoAddHom ρ e) (C z) := by
  have hcd := hC d hd
  have hce := hC e he
  have hcd0 := C_ne_zero hC hd hne_d
  have hce0 := C_ne_zero hC he hne_e
  have hbed : tvPhi (rhoAddHom ρ e) (C d) = 1 := by
    rw [← phi_symm hC hd he hne_d hne_e hd2 he2 h3de]
    exact hde1
  have htb : rhoAddHom ρ d (C e) = C e + C d := by
    rcases hcd (C e) with h | h
    · exact absurd h ((tvPhi_eq_one_iff _ _).1 hde1)
    · exact h
  have hsum0 : C e + C d ≠ 0 := by
    intro h0
    have hceq : C e = C d := by
      have := congrArg (fun x => x + C d) h0
      simpa [add_assoc, zmod_two_add_self] using this
    have hfix : rhoAddHom ρ d (C d) = C d := (tvPhi_eq_zero_iff _ _).1
      (tvPhi_fixes _ hcd hcd0 (fun v => rhoAddHom_self d hd2 v))
    rw [hceq, hfix, zmod_two_add_self] at htb
    exact hcd0 htb
  have hconj := conj_both hcd hce hcd0 hce0 hde1 hbed hd2 he2 (C z)
  have hL : rhoAddHom ρ (d * e * d) (C z) =
      C z + (tvPhi (rhoAddHom ρ e) (C z) + tvPhi (rhoAddHom ρ d) (C z)) •
        (C e + C d) := by
    rw [rhoAddHom_mul, rhoAddHom_mul]
    exact hconj
  have hT : tvPhi (rhoAddHom ρ (d * e * d)) (C z) =
      tvPhi (rhoAddHom ρ e) (C z) + tvPhi (rhoAddHom ρ d) (C z) :=
    tvPhi_eq_of_apply _ hsum0 hL
  rw [hT, add_comm]

lemma central_of_rho_eq_one {G V : Type*} [Group G] [Group V] {ρ : G →* MulAut V} {D : Set G}
    (hconj : ∀ d ∈ D, ∀ g : G, g * d * g⁻¹ ∈ D) (hinj : Set.InjOn ρ D)
    {x : G} (hx : x ∈ D) (hx1 : ρ x = 1) : ∀ g : G, g * x = x * g := by
  intro g
  have hgx : g * x * g⁻¹ ∈ D := hconj x hx g
  have hr : ρ (g * x * g⁻¹) = 1 := by
    rw [map_mul, map_mul, hx1]
    simp
  have hxeq : g * x * g⁻¹ = x := hinj hgx hx (by rw [hr, hx1])
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [hxeq]

lemma phi_one_of_not_commute {d e : G}
    (hC : ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d)
    (hd : d ∈ D) (he : e ∈ D) (hdn : ρ d ≠ 1) (hen : ρ e ≠ 1)
    (hd2 : d * d = 1) (he2 : e * e = 1)
    (h3de : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) (hinj : Set.InjOn ρ D)
    (hde : d * e ≠ e * d) :
    tvPhi (rhoAddHom ρ d) (C e) = 1 := by
  rcases zmod_two_cases (tvPhi (rhoAddHom ρ d) (C e)) with h | h
  · have hbed : tvPhi (rhoAddHom ρ e) (C d) = 0 := by
      rw [← phi_symm hC hd he hdn hen hd2 he2 h3de]
      exact h
    have hcommAdd := commute_of_phi_zero (hC d hd) (hC e he)
      (C_ne_zero hC hd hdn) (C_ne_zero hC he hen) h hbed
    have hcommρ := mulAut_commute_of_addCommute hcommAdd
    exact absurd (commute_of_rho_commute hd he hd2 he2 h3de hinj hcommρ) hde
  · exact h


omit [Module (ZMod 2) (Additive V)] in
lemma rho_ded_ne_one {d e : G} (hd2 : d * d = 1) (hen : ρ e ≠ 1) :
    ρ (d * e * d) ≠ 1 := by
  intro h
  apply hen
  have h' : ρ d * ρ e * ρ d = 1 := by rwa [map_mul, map_mul] at h
  have h2d : ρ d * ρ d = 1 := by rw [← map_mul, hd2, map_one]
  have h2 : ρ e = 1 := by
    have h3' : ρ e = (ρ d)⁻¹ * (ρ d)⁻¹ := by
      have := congrArg (fun f => (ρ d)⁻¹ * f * (ρ d)⁻¹) h'
      simpa [mul_assoc] using this
    rw [inv_eq_of_mul_eq_one_right h2d, h2d] at h3'
    exact h3'
  exact h2

lemma commute_ded_of_not_commute {d e z : G} {C : G → Additive V}
    (hC : ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d)
    (hd : d ∈ D) (he : e ∈ D) (hz : z ∈ D)
    (hdn : ρ d ≠ 1) (hen : ρ e ≠ 1) (hzn : ρ z ≠ 1)
    (hconj : ∀ d ∈ D, ∀ g : G, g * d * g⁻¹ ∈ D)
    (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hinj : Set.InjOn ρ D)
    (hde : d * e ≠ e * d) (hzd : z * d ≠ d * z) (hze : z * e ≠ e * z) :
    z * (d * e * d) = (d * e * d) * z := by
  have hd2 : d * d = 1 := hself d hd
  have he2 : e * e = 1 := hself e he
  have hz2 : z * z = 1 := hself z hz
  have hded : d * e * d ∈ D := by
    have := hconj e he d
    rwa [show d⁻¹ = d from inv_eq_of_mul_eq_one_right hd2] at this
  have hded2 : (d * e * d) * (d * e * d) = 1 := hself (d * e * d) hded
  have hne_ded : ρ (d * e * d) ≠ 1 := rho_ded_ne_one hd2 hen
  have hde1 : tvPhi (rhoAddHom ρ d) (C e) = 1 :=
    phi_one_of_not_commute hC hd he hdn hen hd2 he2 (h3 d hd e he) hinj hde
  have hdz1 : tvPhi (rhoAddHom ρ d) (C z) = 1 :=
    phi_one_of_not_commute hC hd hz hdn hzn hd2 hz2 (h3 d hd z hz) hinj (Ne.symm hzd)
  have hez1 : tvPhi (rhoAddHom ρ e) (C z) = 1 :=
    phi_one_of_not_commute hC he hz hen hzn he2 hz2 (h3 e he z hz) hinj (Ne.symm hze)
  have hphided := phi_ded hC hd he hz hdn hen hd2 he2 (h3 d hd e he) hde1
  rw [hdz1, hez1, zmod_two_one_add_one] at hphided
  have hphized : tvPhi (rhoAddHom ρ z) (C (d * e * d)) = 0 := by
    rw [← phi_symm hC hded hz hne_ded hzn hded2 hz2 (h3 (d * e * d) hded z hz)]
    exact hphided
  have hcommAdd := commute_of_phi_zero (hC (d * e * d) hded) (hC z hz)
    (C_ne_zero hC hded hne_ded) (C_ne_zero hC hz hzn) hphided hphized
  have hcommρ := mulAut_commute_of_addCommute hcommAdd
  exact (commute_of_rho_commute hded hz hded2 hz2
    (h3 (d * e * d) hded z hz) hinj hcommρ).symm

omit [Module (ZMod 2) (Additive V)] in
lemma exists_transvection_data
    (htv : ∀ d ∈ D, ∃ c : V, ∀ u : V, ρ d u = u ∨ ρ d u = u * c) :
    ∃ C : G → Additive V, ∀ d, d ∈ D → ∀ u : Additive V,
      rhoAddHom ρ d u = u ∨ rhoAddHom ρ d u = u + C d := by
  classical
  choose c hc using htv
  refine ⟨fun d => if hd : d ∈ D then Additive.ofMul (c d hd) else 0, ?_⟩
  intro d hd u
  have h := hc d hd (Additive.toMul u)
  have hu : Additive.ofMul (Additive.toMul u) = u := Additive.ofMul.apply_symm_apply u
  have hCd : (fun d => if hd : d ∈ D then Additive.ofMul (c d hd) else 0) d =
      Additive.ofMul (c d hd) := by simp only [dif_pos hd]
  rw [hCd]
  change Additive.ofMul ((ρ d) (Additive.toMul u)) = u ∨
    Additive.ofMul ((ρ d) (Additive.toMul u)) = u + Additive.ofMul (c d hd)
  rcases h with h | h
  · left
    rw [h, hu]
  · right
    rw [h, ofMul_mul, hu]

end Action

end TransvectionSymplectic

open TransvectionSymplectic

theorem isSymplecticType_of_transvections {G : Type} {V : Type*} [Group G] [Group V]
    (h2V : ∀ u : V, u * u = 1) (ρ : G →* MulAut V) {D : Set G}
    (hconj : ∀ d ∈ D, ∀ g : G, g * d * g⁻¹ ∈ D) (hinv : ∀ d ∈ D, orderOf d = 2)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (htv : ∀ d ∈ D, ∃ c : V, ∀ u : V, ρ d u = u ∨ ρ d u = u * c)
    (hinj : Set.InjOn ρ D) :
    CFSG.Fischer.Classification.IsSymplecticType D := by
  classical
  let : CommGroup V := CommGroup.mk fun a b => by
    rw [← inv_eq_of_mul_eq_one_right (h2V (a * b)), mul_inv_rev,
      inv_eq_of_mul_eq_one_right (h2V b), inv_eq_of_mul_eq_one_right (h2V a)]
  let : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule (by intro x; rw [two_nsmul]; exact h2V (Additive.toMul x))
  obtain ⟨C, hC⟩ := exists_transvection_data (ρ := ρ) htv
  have hself : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    have h : d ^ 2 = 1 := by rw [← hinv d hd, pow_orderOf_eq_one]
    simpa [pow_two] using h
  have hcentral : ∀ x ∈ D, ρ x = 1 → ∀ g : G, g * x = x * g :=
    fun x hx hx1 => central_of_rho_eq_one hconj hinj hx hx1
  intro d hd e he z hz hde
  by_cases hdn : ρ d = 1
  · exfalso
    exact hde (hcentral d hd hdn e).symm
  by_cases hen : ρ e = 1
  · exfalso
    exact hde (hcentral e he hen d)
  by_cases hzn : ρ z = 1
  · exact Or.inl (hcentral z hz hzn d).symm
  by_cases hzd : z * d = d * z
  · exact Or.inl hzd
  by_cases hze : z * e = e * z
  · exact Or.inr (Or.inl hze)
  exact Or.inr (Or.inr (commute_ded_of_not_commute hC hd he hz hdn hen hzn
    hconj hself h3 hinj hde hzd hze))

section MainA

variable {G K : Type} {V : Type*} [Group G] [Group K] [Group V]

theorem isSymplecticType_or_derivedSeries_le_ker
    (h2V : ∀ u : V, u * u = 1) (ρ : G →* MulAut V)
    (π : G →* K) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card π.ker)) {D : Set G}
    (hconj : ∀ d ∈ D, ∀ g : G, g * d * g⁻¹ ∈ D) (hinv : ∀ d ∈ D, orderOf d = 2)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (htv : ∀ d ∈ D, ∃ c : V, ∀ u : V, ρ d u = u ∨ ρ d u = u * c)
    (hK : CFSG.Fischer.Classification.Hyp K (π '' D)) :
    CFSG.Fischer.Classification.IsSymplecticType D ∨ derivedSeries G 2 ≤ ρ.ker := by
  classical
  by_cases hinj : Set.InjOn ρ D
  · exact Or.inl (isSymplecticType_of_transvections h2V ρ hconj hinv h3 htv hinj)
  · right
    rw [Set.InjOn] at hinj
    simp only [not_forall] at hinj
    obtain ⟨d, hd, e, he, hρeq, hne⟩ := hinj
    have hself : ∀ x ∈ D, x * x = 1 := fun x hx => by
      have h : x ^ 2 = 1 := by rw [← hinv x hx, pow_orderOf_eq_one]
      simpa [pow_two] using h
    have hπne : π d ≠ π e := pi_ne_of_rho_eq hd he hne hself hker hodd
    have h2e : ρ e * ρ e = 1 := by rw [← map_mul, hself e he, map_one]
    have hmem : d * e ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hρeq, h2e]
    have hπde_ne : π (d * e) ≠ 1 := by
      rw [map_mul]
      intro h
      apply hπne
      have h2e' : π e * π e = 1 := by rw [← map_mul, hself e he, map_one]
      rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right h2e']
    have hNnormal : ((ρ.ker).map π).Normal :=
      Subgroup.Normal.map (MonoidHom.normal_ker ρ) π hπ
    have hNne : (ρ.ker).map π ≠ ⊥ := by
      intro hbot
      have hmem' : π (d * e) ∈ (⊥ : Subgroup K) := by
        rw [← hbot]
        exact Subgroup.mem_map_of_mem π hmem
      exact hπde_ne (by simpa using hmem')
    have hNK' : commutator K ≤ (ρ.ker).map π :=
      CFSG.Fischer.Classification.commutator_le_of_normal hK.center hK.simple hNne
    have hG' : commutator G ≤ ρ.ker ⊔ π.ker := commutator_le_sup_ker ρ π hπ hNK'
    exact derivedSeries_two_le_ker ρ π hker hG'

end MainA

end CFSG.GroupTheory.ThreeTranspositions

