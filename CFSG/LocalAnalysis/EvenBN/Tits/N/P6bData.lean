module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Z0Inv
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bMod
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open
open commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem z_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) : d.z ∈ d.s56V :=
  hd.s56_E_le_V h49 hd.s56_z_mem_E

theorem Z_le_V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) : Zz d z₀ ≤ d.s56V :=
  sup_le (zpowers_le.2 (z_mem_V h49 hd)) (zpowers_le.2 hz.mem_V)


theorem z_sq (hd : d.Hyp) : d.z * d.z = 1 := by
  have := hd.s56_orderOf_z
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [this])

theorem z_ne_one (hd : d.Hyp) : d.z ≠ 1 := by
  intro h
  have := hd.s56_orderOf_z
  rw [h, orderOf_one] at this
  omega

theorem eps_z (hd : d.Hyp) : d.s56Eps d.z = 1 := by
  have hc : d.z * d.t = d.t * d.z := hd.L_comm_t (d.lift_mem _)
  unfold Data.s56Eps
  rw [hc]
  simp [hd.t_mul_self]

theorem z0_ne_one (hd : d.Hyp) (hz : d.S56Z0 z₀) : z₀ ≠ 1 := by
  intro h
  have h1 := hz.eps
  rw [h, hd.s56_eps_one] at h1
  exact z_ne_one hd h1.symm

theorem z0_ne_z (hd : d.Hyp) (hz : d.S56Z0 z₀) : z₀ ≠ d.z := by
  intro h
  have h1 := hz.eps
  rw [h, eps_z hd] at h1
  exact z_ne_one hd h1.symm


theorem z_comm_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    d.z * z₀ = z₀ * d.z := hz.comm_V (z_mem_V h49 hd)

theorem mem_Z_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    {g : G} : g ∈ Zz d z₀ ↔ g = 1 ∨ g = d.z ∨ g = z₀ ∨ g = d.z * z₀ := by
  have hz0 : z₀ * z₀ = 1 := hinv z₀ hz
  have hz2 : orderOf d.z = 2 := hd.s56_orderOf_z
  have hz02 : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz0) (z0_ne_one hd hz)
  have hc := z_comm_z0 h49 hd hz
  constructor
  · intro hg
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute (zpowers d.z) (zpowers z₀)
      (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := ha
        obtain ⟨n, rfl⟩ := hb
        exact ((Commute.zpow_zpow (show Commute d.z z₀ from hc) m n)).eq) hg
    rcases (Model.mem_zpowers_of_orderOf_two hz2).1 ha with rfl | rfl <;>
      rcases (Model.mem_zpowers_of_orderOf_two hz02).1 hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))


theorem card_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv) :
    Nat.card (Zz d z₀) = 4 := by
  have hset : (Zz d z₀ : Set G) = {1, d.z, z₀, d.z * z₀} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact mem_Z_iff h49 hd hz hinv
  have h1 : (1 : G) ≠ d.z := (z_ne_one hd).symm
  have h2 : (1 : G) ≠ z₀ := (z0_ne_one hd hz).symm
  have h3 : (1 : G) ≠ d.z * z₀ := fun h => z0_ne_z hd hz (by
    have h' : z₀ = d.z⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    exact h'.trans (inv_eq_of_mul_eq_one_right (z_sq hd)))
  have h4 : d.z ≠ z₀ := (z0_ne_z hd hz).symm
  have h5 : d.z ≠ d.z * z₀ := fun h => z0_ne_one hd hz (mul_left_cancel (a := d.z) (by
    rw [mul_one]; exact h.symm))
  have h6 : z₀ ≠ d.z * z₀ := fun h => z_ne_one hd (mul_right_cancel (b := z₀) (by
    rw [one_mul]; exact h.symm))
  have h0 : Nat.card (Zz d z₀) = (Zz d z₀ : Set G).ncard := Nat.card_coe_set_eq (Zz d z₀ : Set G)
  rw [h0, hset]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h6]
  · simp [h4, h5]
  · simp [h1, h2, h3]


theorem t_mem_H (h49 : d.Thm49Statement) (hd : d.Hyp) : d.t ∈ Hg d :=
  hd.s56_M_le_normalizer_V h49 d.s56_t_mem_M

theorem x5_mem_H (h49 : d.Thm49Statement) (hd : d.Hyp) : d.x₅ ∈ Hg d :=
  hd.s56_M_le_normalizer_V h49 hd.s56_x5_mem_M

theorem t_conj_z0 (hd : d.Hyp) (hz : d.S56Z0 z₀) : d.t * z₀ * d.t⁻¹ = d.z * z₀ := by
  have h1 := hd.s56_conj_t z₀
  rw [hz.eps] at h1
  have ht2 : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_self
  have h2 : z₀ * d.t = d.t * d.z * z₀ := by
    calc z₀ * d.t = (z₀ * d.t * z₀⁻¹) * z₀ := by group
      _ = d.t * d.z * z₀ := by rw [h1]
  rw [ht2]
  calc d.t * z₀ * d.t = d.t * (z₀ * d.t) := by group
    _ = d.t * (d.t * d.z * z₀) := by rw [h2]
    _ = (d.t * d.t) * d.z * z₀ := by group
    _ = d.z * z₀ := by rw [hd.t_mul_self, one_mul]

theorem t_comm_z (hd : d.Hyp) : d.t * d.z = d.z * d.t := (hd.L_comm_t (d.lift_mem _)).symm

theorem inv_subgroups_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hinv : d.S56Z0Inv) (U : Subgroup G) (hU : U ≤ Zz d z₀)
    (hUH : ∀ h ∈ Hg d, ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    U = ⊥ ∨ U = zpowers d.z ∨ U = Zz d z₀ := by
  by_cases hbig : z₀ ∈ U ∨ d.z * z₀ ∈ U
  ·
    right; right
    have hboth : z₀ ∈ U ∧ d.z * z₀ ∈ U := by
      have htz : d.t * z₀ * d.t⁻¹ = d.z * z₀ := t_conj_z0 hd hz
      have htzz : d.t * (d.z * z₀) * d.t⁻¹ = z₀ := by
        calc d.t * (d.z * z₀) * d.t⁻¹ = (d.t * d.z * d.t⁻¹) * (d.t * z₀ * d.t⁻¹) := by group
          _ = d.z * (d.z * z₀) := by
            rw [htz, show d.t * d.z * d.t⁻¹ = d.z by rw [t_comm_z hd]; group]
          _ = z₀ := by
            rw [← mul_assoc, z_sq hd, one_mul]
      rcases hbig with h | h
      · exact ⟨h, htz ▸ hUH _ (t_mem_H h49 hd) _ h⟩
      · exact ⟨htzz ▸ hUH _ (t_mem_H h49 hd) _ h, h⟩
    refine le_antisymm hU (sup_le ?_ (zpowers_le.2 hboth.1))
    refine zpowers_le.2 ?_
    have : d.z = (d.z * z₀) * z₀⁻¹ := by group
    rw [this]
    exact mul_mem hboth.2 (inv_mem hboth.1)
  · push Not at hbig
    have hsub : U ≤ zpowers d.z := by
      intro u hu
      have := (mem_Z_iff h49 hd hz hinv).1 (hU hu)
      rcases this with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
      · exact absurd hu hbig.1
      · exact absurd hu hbig.2
    have hz2 : orderOf d.z = 2 := hd.s56_orderOf_z
    by_cases hzU : d.z ∈ U
    · right; left
      exact le_antisymm hsub (zpowers_le.2 hzU)
    · left
      refine le_antisymm (fun u hu => ?_) bot_le
      rcases (Model.mem_zpowers_of_orderOf_two hz2).1 (hsub hu) with rfl | rfl
      · exact one_mem _
      · exact absurd hu hzU


theorem x5_comm_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    {g : G} (hg : g ∈ Zz d z₀) : d.x₅ * g = g * d.x₅ := by
  have hxz := hd.s56_x5_comm_z
  have hxz0 := hz.comm_x
  rcases (mem_Z_iff h49 hd hz hinv).1 hg with rfl | rfl | rfl | rfl
  · simp
  · exact hxz
  · exact hxz0
  · calc d.x₅ * (d.z * z₀) = (d.x₅ * d.z) * z₀ := by group
      _ = (d.z * d.x₅) * z₀ := by rw [hxz]
      _ = d.z * (d.x₅ * z₀) := by group
      _ = d.z * (z₀ * d.x₅) := by rw [hxz0]
      _ = d.z * z₀ * d.x₅ := by group

theorem CV_x5_le_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {v : G}
    (hv : v ∈ d.s56V) (hc : d.x₅ * v = v * d.x₅) : v ∈ Zz d z₀ := by
  have hQ : v ∈ d.s56Q := d.s56_V_le_Q hv
  have hcen : v ∈ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute d.x₅ v from hc) k)).eq
  have := hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich
  show v ∈ zpowers d.z ⊔ zpowers z₀
  rw [← this]
  exact mem_inf.2 ⟨hQ, hcen⟩

end Data

section V2

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem pv2_facts (hd : d.Hyp) :
    d.pv 2 ∈ d.M ∧ d.pv 2 * d.x₅ * (d.pv 2)⁻¹ = d.x₅⁻¹ := by
  obtain ⟨-, -, hconj, -, hH, -⟩ := Model.parrottV_two_facts
  have hVD : Model.parrottV 2 ∈ titsD := titsH_le_titsD hH
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD Model.hatX_facts.1
  refine ⟨?_, ?_⟩
  · have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
    have hC : d.pv 2 ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem _)
    have hVN : Model.parrottV 2 ∈
        titsD ⊓ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
      rw [Model.titsD_inf_normalizer_hatE]
      exact hH
    show d.pv 2 ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
    rw [hd.mem_normalizer_tSup_iff hED hC]
    have hρ : (d.ρ ⟨d.pv 2, hC⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 2 := hd.ρ_lift hVD
    rw [hρ]
    exact hVN.2
  · have h1 := d.lift_conj hVD hXD
    rw [hconj, d.lift_inv hXD] at h1
    exact h1.symm


theorem pv2_mem_H (h49 : d.Thm49Statement) (hd : d.Hyp) : d.pv 2 ∈ Hg d :=
  hd.s56_M_le_normalizer_V h49 (pv2_facts hd).1

end V2

section Star

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def starB (d : Data G) (g : G) (hg : g ∈ Hg d) : ↥(Hs d) :=
  ⟨star d g, actFun_mem_imgIn hg hg⟩

theorem star_apply_val {g : G} (hg : g ∈ Hg d) (v : ↥d.s56V) :
    ((star d g v : ↥d.s56V) : G) = g * v * g⁻¹ := actFun_apply_coe d.s56V hg v

@[expose] noncomputable def Zv (d : Data G) (z₀ : G) : Subgroup ↥d.s56V :=
  (Zz d z₀).subgroupOf d.s56V

theorem star_mem_Zv (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀) {g : G}
    (hg : g ∈ Hg d) {y : ↥d.s56V} (hy : y ∈ Zv d z₀) : star d g y ∈ Zv d z₀ := by
  show ((star d g y : ↥d.s56V) : G) ∈ Zz d z₀
  rw [star_apply_val hg]
  exact hZH g hg y hy

theorem map_Zv_eq (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀) :
    ∀ σ ∈ Hs d, (Zv d z₀).map (σ : ↥d.s56V →* ↥d.s56V) = Zv d z₀ := by
  intro σ hσ
  obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hσ
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact star_mem_Zv hZH hg hy
  · intro y hy
    refine ⟨star d g⁻¹ y, star_mem_Zv hZH (inv_mem hg) hy, ?_⟩
    show star d g (star d g⁻¹ y) = y
    rw [← MulAut.mul_apply]
    change (actFun d.s56V g * actFun d.s56V g⁻¹) y = y
    rw [← actFun_mul d.s56V hg (inv_mem hg), mul_inv_cancel, actFun_one]
    rfl


instance commGroupOfFact {S : Subgroup G} [h : Fact (∀ a b : ↥S, a * b = b * a)] : CommGroup ↥S :=
  { (inferInstance : Group ↥S) with mul_comm := h.out }

end Star

section Gen

theorem xfix_of_fixed_le {V : Type*} [CommGroup V] (hV2 : ∀ a : V, a * a = 1) (Z : Subgroup V)
    (σ : MulAut V) (hσ5 : σ ^ 5 = 1) (hZ : ∀ z ∈ Z, σ z = z)
    (hfix : ∀ v : V, σ v = v → v ∈ Z) : ∀ v : V, σ v * v⁻¹ ∈ Z → v ∈ Z := by
  intro v hv
  set z' := σ v * v⁻¹ with hz'
  have hσv : σ v = z' * v := by rw [hz']; group
  have hσz : σ z' = z' := hZ z' hv
  have hn : ∀ n : ℕ, (σ ^ n) v = v * z' ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hσz, hσv, pow_succ']
      rw [mul_comm z' v, mul_assoc]
  have h5 := hn 5
  rw [hσ5, MulAut.one_apply] at h5
  have h6 : z' ^ 5 = 1 := by
    have : v * z' ^ 5 = v * 1 := by rw [mul_one]; exact h5.symm
    exact mul_left_cancel this
  have hz2 : z' * z' = 1 := hV2 z'
  have h7 : z' = 1 := by
    have : z' ^ 5 = z' := by
      rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, pow_two z', hz2, one_pow, one_mul]
    rw [← this]; exact h6
  apply hfix
  rw [hσv, h7, one_mul]

end Gen

section Wsec

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Wg_eq_pre (hz : d.S56Z0 z₀) (hWimg : img d (Wg d z₀) = Ws d) :
    Wg d z₀ = pre d (Ws d) := by
  have hCvW : centralizer (d.s56V : Set G) ≤ Wg d z₀ := by
    intro c hc
    refine mem_inf.2 ⟨centralizer_le_preIn d.s56V _ hc, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hc z₀ hz.mem_V).symm
  apply le_antisymm
  · intro w hw
    have hwH : w ∈ normalizer (d.s56V : Set G) := ((mem_preIn_iff d.s56V _).1 hw.1).1
    refine (mem_preIn_iff d.s56V _).2 ⟨hwH, ?_⟩
    rw [← hWimg]
    exact actFun_mem_imgIn hw hwH
  · intro g hg
    obtain ⟨hgN, hgs⟩ := (mem_preIn_iff d.s56V _).1 hg
    rw [← hWimg] at hgs
    obtain ⟨w, hwW, hwN, hwg⟩ := (mem_imgIn_iff d.s56V _).1 hgs
    have hwg' : w⁻¹ * g ∈ centralizer (d.s56V : Set G) := by
      rw [← actFun_eq_one_iff d.s56V (mul_mem (inv_mem hwN) hgN),
        actFun_mul d.s56V (inv_mem hwN) hgN, actFun_inv d.s56V hwN, hwg, inv_mul_cancel]
    have : g = w * (w⁻¹ * g) := by group
    rw [this]
    exact mul_mem hwW (hCvW hwg')


theorem Wg_conj_mem (hz : d.S56Z0 z₀) (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) {h : G} (hh : h ∈ Hg d) {w : G}
    (hw : w ∈ Wg d z₀) : h * w * h⁻¹ ∈ Wg d z₀ := by
  rw [Wg_eq_pre hz hWimg] at hw ⊢
  obtain ⟨hwN, hws⟩ := (mem_preIn_iff d.s56V _).1 hw
  refine (mem_preIn_iff d.s56V _).2 ⟨mul_mem (mul_mem hh hwN) (inv_mem hh), ?_⟩
  rw [actFun_conj d.s56V hh hwN]
  exact hWnorm _ (actFun_mem_imgIn hh hh) _ hws


end Wsec

section MD

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem mdata_d [Fact (∀ a b : ↥d.s56V, a * b = b * a)] [Fact (∀ a : ↥d.s56V, a * a = 1)]
    (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hinv : d.S56Z0Inv)
    (hcard : Nat.card d.s56V = 2 ^ 10) {h₀ : G} (hh₀ : h₀ ∈ Hg d)
    (hh : star d (h₀ * d.t * h₀⁻¹) = star d (d.t * d.pv 2)) :
    MData (Zv d z₀) (Hs d) (starB d d.x₅ (x5_mem_H h49 hd)) (starB d d.t (t_mem_H h49 hd))
      (starB d (d.pv 2) (pv2_mem_H h49 hd)) (starB d h₀ hh₀) := by
  have hxH := x5_mem_H h49 hd
  have htH := t_mem_H h49 hd
  have hvH := pv2_mem_H h49 hd
  have hZv : Nat.card (Zv d z₀) = 4 := by
    unfold Zv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_V h49 hd hz)).toEquiv]
    exact card_Z h49 hd hz hinv
  have hx5 : (star d d.x₅) ^ 5 = 1 := by
    rw [star, ← actFun_pow d.s56V hxH, show d.x₅ ^ 5 = 1 by
      rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _, actFun_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := card_quot_mul_card (Zv d z₀)
    rw [hZv, hcard] at h1
    omega
  · exact Subtype.ext (by simpa [starB] using hx5)
  · refine xfix_of_fixed_le Fact.out (Zv d z₀) (star d d.x₅) hx5 ?_ ?_
    · intro y hy
      refine Subtype.ext ?_
      rw [star_apply_val hxH]
      have hc := x5_comm_Z h49 hd hz hinv ((Subgroup.mem_subgroupOf).1 hy)
      calc d.x₅ * (y : G) * d.x₅⁻¹ = (y : G) * d.x₅ * d.x₅⁻¹ := by rw [hc]
        _ = y := by group
    · intro v hv
      have h1 := congrArg (fun w : ↥d.s56V => (w : G)) hv
      simp only [star_apply_val hxH] at h1
      have hc : d.x₅ * (v : G) = (v : G) * d.x₅ := by
        calc d.x₅ * (v : G) = d.x₅ * v * d.x₅⁻¹ * d.x₅ := by group
          _ = (v : G) * d.x₅ := by rw [h1]
      exact (Subgroup.mem_subgroupOf).2 (CV_x5_le_Z h49 hd hz v.2 hc)
  · refine Subtype.ext ?_
    show star d d.t * star d d.t = 1
    rw [star, ← actFun_mul d.s56V htH htH, hd.t_mul_self, actFun_one]
  · refine Subtype.ext ?_
    show star d d.t * star d d.x₅ = star d d.x₅ * star d d.t
    exact actFun_comm_of_comm d.s56V hd.s56_x5_comm_t.symm
  · refine Subtype.ext ?_
    show actFun d.s56V (d.pv 2) * actFun d.s56V d.x₅ * (actFun d.s56V (d.pv 2))⁻¹ =
      (actFun d.s56V d.x₅)⁻¹
    rw [← actFun_conj d.s56V hvH hxH, (pv2_facts hd).2, actFun_inv d.s56V hxH]
  · refine Subtype.ext ?_
    show star d h₀ * star d d.t * (star d h₀)⁻¹ = star d d.t * star d (d.pv 2)
    have h1 : star d (h₀ * d.t * h₀⁻¹) = star d h₀ * star d d.t * (star d h₀)⁻¹ :=
      actFun_conj d.s56V hh₀ htH
    have h2 : star d (d.t * d.pv 2) = star d d.t * star d (d.pv 2) :=
      actFun_mul d.s56V htH hvH
    rw [← h1, hh, h2]


theorem comm_VW_mem_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hinv : d.S56Z0Inv) (hVel : IsElemAbelian 2 d.s56V) (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    (hconj : StarConj d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d)) :
    ∀ w ∈ Wg d z₀, ∀ v ∈ d.s56V, w * v * w⁻¹ * v⁻¹ ∈ Zz d z₀ := by
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => hVel.1.is_comm.comm a b
  have hs : ∀ a : ↥d.s56V, a * a = 1 := fun a => by
    have := hVel.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  haveI : Fact (∀ a b : ↥d.s56V, a * b = b * a) := ⟨hc⟩
  haveI : Fact (∀ a : ↥d.s56V, a * a = 1) := ⟨hs⟩
  obtain ⟨h₀, hh₀, hh⟩ := hconj
  have M := mdata_d h49 hd hz hinv hcard hh₀ hh
  let Wb : Subgroup ↥(Hs d) := (Ws d).subgroupOf (Hs d)
  haveI : Wb.Normal := ⟨fun n hn g => by
    exact Subgroup.mem_subgroupOf.2 (by
      simpa using hWnorm (g : MulAut ↥d.s56V) g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  have hW2 : ∀ w ∈ Wb, w * w = 1 := by
    intro w hw
    have := hWel.2 (w : MulAut ↥d.s56V) (Subgroup.mem_subgroupOf.1 hw)
    exact Subtype.ext (by simpa [pow_two] using this)
  have key := M.normal_trivial (map_Zv_eq hZH) Wb hW2
  intro w hw v hv
  have hwH : w ∈ Hg d := ((mem_preIn_iff d.s56V _).1 hw.1).1
  have hstar : star d w ∈ Ws d := by
    rw [← hWimg]
    exact actFun_mem_imgIn hw hwH
  have h1 := key ⟨star d w, actFun_mem_imgIn hwH hwH⟩ (Subgroup.mem_subgroupOf.2 hstar) ⟨v, hv⟩
  have h2 : v⁻¹ * (w * v * w⁻¹) ∈ Zz d z₀ := by
    have := (Subgroup.mem_subgroupOf).1 h1
    have e : ((⟨v, hv⟩⁻¹ * (star d w) ⟨v, hv⟩ : ↥d.s56V) : G) = v⁻¹ * (w * v * w⁻¹) := by
      show (v⁻¹ : G) * ((star d w ⟨v, hv⟩ : ↥d.s56V) : G) = _
      rw [star_apply_val hwH]
    rw [← e]
    exact this
  have hwv : w * v * w⁻¹ ∈ d.s56V := by
    have := (star d w ⟨v, hv⟩).2
    rwa [star_apply_val hwH] at this
  have hcomm : v⁻¹ * (w * v * w⁻¹) = (w * v * w⁻¹) * v⁻¹ :=
    congrArg (fun a : ↥d.s56V => (a : G)) (hc ⟨v, hv⟩⁻¹ ⟨w * v * w⁻¹, hwv⟩)
  rw [← hcomm]
  exact h2


theorem commutator_eq_Z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hinv : d.S56Z0Inv) (hVel : IsElemAbelian 2 d.s56V) (hcard : Nat.card d.s56V = 2 ^ 10)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    (hconj : StarConj d (d.t * d.pv 2))
    (hWimg : img d (Wg d z₀) = Ws d)
    (hWnorm : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hWel : IsElemAbelian 2 (Ws d))
    (hZW : Zz d z₀ = d.s56V ⊓ centralizer (Wg d z₀ : Set G))
    (hCU : d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) = Zz d z₀)
    (hUW : IsElemAbQuot (Ws d) (Us d) 4) (hWcard : Nat.card (Ws d) = 2 ^ 8) :
    ⁅d.s56V, Wg d z₀⁆ = Zz d z₀ := by
  have hcomm := comm_VW_mem_Z h49 hd hz hinv hVel hcard hZH hconj hWimg hWnorm hWel
  have hc : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => hVel.1.is_comm.comm a b
  have hs : ∀ a : ↥d.s56V, a * a = 1 := fun a => by
    have := hVel.2 a a.2
    exact Subtype.ext (by simpa [pow_two] using this)
  have hVH : ∀ h ∈ Hg d, ∀ v ∈ d.s56V, h * v * h⁻¹ ∈ d.s56V := fun h hh v hv =>
    (mem_normalizer_iff.1 hh v).1 hv
  set R := ⁅d.s56V, Wg d z₀⁆ with hR
  have hRZ : R ≤ Zz d z₀ := by
    rw [hR, Subgroup.commutator_le]
    intro v hv w hw
    have h1 := hcomm w hw v hv
    have e : ⁅v, w⁆ = (w * v * w⁻¹ * v⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact inv_mem h1
  have hRinv : ∀ h ∈ Hg d, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh
    have : R ≤ R.comap (MulAut.conj h).toMonoidHom := by
      rw [hR, Subgroup.commutator_le]
      intro v hv w hw
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj h).toMonoidHom ⁅v, w⁆ = ⁅h * v * h⁻¹, h * w * h⁻¹⁆ := by
        simp only [commutatorElement_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hVH h hh v hv) (Wg_conj_mem hz hWimg hWnorm hh hw)
    intro r hr
    exact this hr
  rcases inv_subgroups_Z h49 hd hz hinv R hRZ hRinv with h0 | h1 | h2
  · exfalso
    have hVZ : d.s56V ≤ Zz d z₀ := by
      intro v hv
      rw [hZW]
      refine mem_inf.2 ⟨hv, ?_⟩
      rw [mem_centralizer_iff]
      intro w hw
      have h4 : ⁅v, w⁆ ∈ R := Subgroup.commutator_mem_commutator hv hw
      rw [h0] at h4
      have h3 : v * w * v⁻¹ * w⁻¹ = 1 := h4
      exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)).symm
    have := Subgroup.card_le_of_le hVZ
    rw [hcard, card_Z h49 hd hz hinv] at this
    norm_num at this
  · exfalso
    have hUle : Us d ≤ Ws d := hUW.1
    have hUcard : Nat.card (Us d) = 2 ^ 4 := by
      have h1 := Subgroup.relIndex_mul_card (H := Us d) (K := Ws d)
      rw [inf_eq_left.2 hUle, hUW.2.2.2.2, hWcard] at h1
      omega
    have hU2 : ∀ u ∈ Us d, u * u = 1 := fun u hu => by
      have := hWel.2 u (hUle hu)
      simpa [pow_two] using this
    have hUc : ∀ u₁ ∈ Us d, ∀ u₂ ∈ Us d, u₁ * u₂ = u₂ * u₁ := fun u₁ hu₁ u₂ hu₂ =>
      congrArg Subtype.val (hWel.1.is_comm.comm (⟨u₁, hUle hu₁⟩ : ↥(Ws d)) ⟨u₂, hUle hu₂⟩)
    let L : Subgroup ↥d.s56V := (zpowers d.z).subgroupOf d.s56V
    have hzV : zpowers d.z ≤ d.s56V := zpowers_le.2 (z_mem_V h49 hd)
    have hL : Nat.card L ≤ 2 := by
      have : Nat.card L = Nat.card (zpowers d.z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzV).toEquiv
      rw [this, Nat.card_zpowers, hd.s56_orderOf_z]
    have hUL : ∀ u ∈ Us d, ∀ v : ↥d.s56V, v⁻¹ * u v ∈ L := by
      intro u hu v
      have hu' : u ∈ img d (Wg d z₀) := by rw [hWimg]; exact hUle hu
      obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hu'
      have h5 : ⁅(v : G)⁻¹, w⁆ ∈ R := Subgroup.commutator_mem_commutator (inv_mem v.2) hw
      rw [h1] at h5
      show ((v⁻¹ * actFun d.s56V w v : ↥d.s56V) : G) ∈ zpowers d.z
      have e : ((v⁻¹ * actFun d.s56V w v : ↥d.s56V) : G) = ⁅(v : G)⁻¹, w⁆ := by
        show (v : G)⁻¹ * ((actFun d.s56V w v : ↥d.s56V) : G) = _
        rw [actFun_apply_coe d.s56V hwN]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h5
    have hcount := card_le_mul_card_fixedSub hc hs (Us d) hU2 hUc hUcard L hL hUL
    have hfix : fixedSub ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ≤ Zv d z₀ := by
      intro v hv
      have hcent : (v : G) ∈ centralizer ((Ug d : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨hgN, hgs⟩ := (mem_preIn_iff d.s56V _).1 hg
        have h6 := hv (actFun d.s56V g) hgs
        have h7 := congrArg (fun a : ↥d.s56V => (a : G)) h6
        simp only [actFun_apply_coe d.s56V hgN] at h7
        calc g * (v : G) = g * v * g⁻¹ * g := by group
          _ = (v : G) * g := by rw [h7]
      have : (v : G) ∈ Zz d z₀ := by rw [← hCU]; exact mem_inf.2 ⟨v.2, hcent⟩
      exact Subgroup.mem_subgroupOf.2 this
    have hZv : Nat.card (Zv d z₀) = 4 := by
      unfold Zv
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_V h49 hd hz)).toEquiv]
      exact card_Z h49 hd hz hinv
    have h8 := Subgroup.card_le_of_le hfix
    rw [hZv] at h8
    rw [hcard] at hcount
    norm_num at hcount
    omega
  · exact h2

end MD

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
