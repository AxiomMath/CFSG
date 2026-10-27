module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888CN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Uni
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem l16a_eq_one_of_pow {x : G} {m : ℕ} (hm : Odd m) (h4 : x ^ 4 = 1) (hxm : x ^ m = 1) :
    x = 1 := by
  have hd4 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hdm : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  have hcop : Nat.Coprime 4 m := by
    have := (hm.coprime_two_left).pow_left 2
    simpa using this
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd4 hdm)

theorem l16a_odd_normal_centralizes {Q U : Subgroup G} {t z : G}
    (hQ4 : ∀ q ∈ Q, q ^ 4 = 1) (htQ : t ∈ Q)
    (hcomm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ ∈ zpowers z)
    (hUN : U ≤ normalizer (Q : Set G)) (hUz : U ≤ centralizer ({z} : Set G))
    (hUt : U ≤ centralizer ({t} : Set G)) (hUodd : ∀ u ∈ U, Odd (orderOf u))
    (hUnorm : ∀ e ∈ Q ⊓ centralizer ({t} : Set G), ∀ u ∈ U, e * u * e⁻¹ ∈ U) :
    U ≤ centralizer (Q : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have step1 : ∀ e ∈ Q ⊓ centralizer ({t} : Set G), u * e * u⁻¹ = e := by
    intro e he
    have h1 : e * u * e⁻¹ ∈ U := hUnorm e he u hu
    have h2 : e * u * e⁻¹ * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have h3 : u * e⁻¹ * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hUN hu) e⁻¹).mp (Q.inv_mem he.1)
    have h4 : e * u * e⁻¹ * u⁻¹ ∈ Q := by
      have := Q.mul_mem he.1 h3
      simpa [mul_assoc] using this
    have h5 : e * u * e⁻¹ * u⁻¹ = 1 :=
      l16a_eq_one_of_pow (hUodd _ h2) (hQ4 _ h4) (pow_orderOf_eq_one _)
    have h6 : e * u = u * e := commutatorElement_eq_one_iff_mul_comm.mp h5
    calc u * e * u⁻¹ = (e * u) * u⁻¹ := by rw [h6]
      _ = e := by group
  have hut : u * t * u⁻¹ = t := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hUt hu)
    calc u * t * u⁻¹ = (t * u) * u⁻¹ := by rw [h]
      _ = t := by group
  have huζ : ∀ ζ ∈ zpowers z, u * ζ * u⁻¹ = ζ := by
    intro ζ hζ
    obtain ⟨k, rfl⟩ := hζ
    have hcz : Commute u z := Subgroup.mem_centralizer_singleton_iff.mp (hUz hu)
    exact (hcz.zpow_right k).mul_inv_cancel
  have hq' : u * q * u⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hUN hu) q).mp hq
  obtain ⟨d, hd⟩ : ∃ d : G, d = q⁻¹ * (u * q * u⁻¹) := ⟨_, rfl⟩
  have hdQ : d ∈ Q := by rw [hd]; exact Q.mul_mem (Q.inv_mem hq) hq'
  have hqd : u * q * u⁻¹ = q * d := by rw [hd]; group
  have hζ : (u * q * u⁻¹) * t * (u * q * u⁻¹)⁻¹ * t⁻¹ = q * t * q⁻¹ * t⁻¹ := by
    have key : (u * q * u⁻¹) * t * (u * q * u⁻¹)⁻¹ * t⁻¹ =
        u * (q * t * q⁻¹ * t⁻¹) * u⁻¹ := by
      calc (u * q * u⁻¹) * t * (u * q * u⁻¹)⁻¹ * t⁻¹
          = (u * q * u⁻¹) * (u * t * u⁻¹) * (u * q * u⁻¹)⁻¹ * (u * t * u⁻¹)⁻¹ := by rw [hut]
        _ = u * (q * t * q⁻¹ * t⁻¹) * u⁻¹ := by group
    rw [key]
    exact huζ _ (hcomm q hq t htQ)
  have hdt' : d * t * d⁻¹ = t := by
    have h1 : (u * q * u⁻¹) * t * (u * q * u⁻¹)⁻¹ = q * t * q⁻¹ := mul_right_cancel hζ
    calc d * t * d⁻¹ = q⁻¹ * ((u * q * u⁻¹) * t * (u * q * u⁻¹)⁻¹) * q := by rw [hd]; group
      _ = q⁻¹ * (q * t * q⁻¹) * q := by rw [h1]
      _ = t := by group
  have hdt : d ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * t = (d * t * d⁻¹) * d := by group
      _ = t * d := by rw [hdt']
  have hud : u * d * u⁻¹ = d := step1 d ⟨hdQ, hdt⟩
  have hiter : ∀ n : ℕ, u ^ n * q * (u ^ n)⁻¹ = q * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e0 : u ^ (n + 1) * q * (u ^ (n + 1))⁻¹ = u * (u ^ n * q * (u ^ n)⁻¹) * u⁻¹ := by
        group
      have e1 : u * (q * d ^ n) * u⁻¹ = (u * q * u⁻¹) * (u * d ^ n * u⁻¹) := by group
      have e3 : u * d ^ n * u⁻¹ = d ^ n := by rw [← conj_pow, hud]
      rw [e0, ih, e1, hqd, e3, pow_succ', mul_assoc]
  have hm : Odd (orderOf u) := hUodd u hu
  have hdm : d ^ orderOf u = 1 := by
    have h := hiter (orderOf u)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    exact mul_left_cancel (a := q) (by rw [mul_one]; exact h.symm)
  have hd1 : d = 1 := l16a_eq_one_of_pow hm (hQ4 d hdQ) hdm
  have hfix : u * q * u⁻¹ = q := by rw [hqd, hd1, mul_one]
  calc q * u = (u * q * u⁻¹) * u := by rw [hfix]
    _ = u * q := by group

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

private lemma l16a_kfam_two : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]

private lemma l16a_kfam_three : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]

theorem l16a_Qsub_eq (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Qsub K₁ K₂ h = Sec5B517Q8 (sec5b517_quad h514 c) := by
  rw [sec5b517_Qsub_eq, (sec5b517_quad h514 c).core_eq]

theorem l16a_t_mem_Qsub (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    t ∈ Qsub K₁ K₂ h := by
  have hq := sec5b517_quad h514 c
  have htR : t ∈ Sec5B517Q8.pair hq 2 3 := by
    refine Sec5B517Q8.mem_pair_of_sq (i := 2) (j := 3) hq ?_ c.t_mul_self
    rw [l16a_kfam_two, l16a_kfam_three]
    exact c.t_mem_sup₃₄
  rw [l16a_Qsub_eq h514 c]
  exact htR.1

theorem l16a_t_mem_Delta (h514 : Asc82Lemma514) (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
  sec5_mem_delta_of_pair h514 c (i := 2) (j := 3) (by decide) c.involution (c.t_ne_z h37)
    (by rw [l16a_kfam_two, l16a_kfam_three]; exact c.t_mem_sup₃₄)

theorem l16a_sup_le_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : K₁ ⊔ K₂ ≤ L :=
  sup_le (fun _ hx => (c.pocket₁.2.1 hx).1) (fun _ hx => (c.pocket₂.2.1 hx).1)

theorem l16a_oddCore_le_centralizer_Q (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h514 : Asc82Lemma514) (h73 : Asc82CHdLeN) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (Qsub K₁ K₂ h : Set G) := by
  have hq := sec5b517_quad h514 c
  have hN : centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (Qsub K₁ K₂ h : Set G) :=
    h73 G t L S z r B A K₁ K₂ h c t (l16a_t_mem_Delta h514 h37 c)
  have hUt : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer ({t} : Set G) :=
    (oddCoreIn_normal _).1
  have hLU : L ≤ centralizer (oddCoreIn (centralizer ({t} : Set G)) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (sec5_oddCore_comm_L h36 c.toSec5Setting).1
  have hzL : z ∈ L := (c.pocket₁.2.1 c.pocket₁.1).1
  have hUz : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer ({z} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hLU hzL) u hu)
  refine l16a_odd_normal_centralizes (t := t) (z := z) ?_ (l16a_t_mem_Qsub h514 c) ?_
    (fun u hu => hN ⟨hUt hu, hUz hu⟩) hUz hUt
    (fun u hu => odd_orderOf_of_mem_oddCoreIn hu) ?_
  · intro q hqQ
    rw [l16a_Qsub_eq h514 c] at hqQ
    exact Sec5B517Q8.pow_four hq hqQ
  · intro q hqQ q' hq'Q
    exact (qsub_le_centralizerMod h514 c hqQ).2.2.2 q' hq'Q
  · intro e he u hu
    exact conj_mem_oddCoreIn (Subgroup.le_normalizer he.2) hu

end Ctx

end CFSG.OddStandard.SmallF3.Omega
