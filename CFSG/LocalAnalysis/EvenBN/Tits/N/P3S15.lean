module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThAbs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThF5
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section S15

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def vCommGroup (h10 : Node10 d z₀) : CommGroup ↥d.s56V :=
  { (inferInstance : Group ↥d.s56V) with
    mul_comm := fun a b => Subtype.ext (h10.comm_V a.2 b.2) }

theorem mem_sup_zpowers_iff {Γ : Type*} [Group Γ] {a b : Γ} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (v : Γ) :
    v ∈ zpowers a ⊔ zpowers b ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have hnorm : zpowers a ≤ normalizer (zpowers b : Set Γ) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨m, rfl⟩ := hu
    obtain ⟨n, rfl⟩ := hw
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq.symm
  have hset : ((zpowers a ⊔ zpowers b : Subgroup Γ) : Set Γ) = (zpowers a : Set Γ) * (zpowers b : Set Γ) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (zpowers a) (zpowers b) hnorm
  have hmem : v ∈ zpowers a ⊔ zpowers b ↔ ∃ u ∈ zpowers a, ∃ w ∈ zpowers b, u * w = v := by
    rw [← SetLike.mem_coe, hset]
    exact Set.mem_mul
  rw [hmem]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    rcases eq_one_or_of_mem_zpowers ha hu with rfl | rfl <;>
      rcases eq_one_or_of_mem_zpowers hb hw with rfl | rfl
    · left; simp
    · right; right; left; simp
    · right; left; simp
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
    · exact ⟨v, mem_zpowers _, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, v, mem_zpowers _, by simp⟩
    · exact ⟨a, mem_zpowers _, b, mem_zpowers _, rfl⟩

@[expose] noncomputable def zV (h49 : d.Thm49Statement) (hd : d.Hyp) : ↥d.s56V :=
  ⟨d.z, hd.s56_E_le_V h49 hd.s56_z_mem_E⟩

@[expose] noncomputable def z0V (hz : d.S56Z0 z₀) : ↥d.s56V := ⟨z₀, hz.mem_V⟩

theorem star_x5_fix_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (v : ↥d.s56V) : star d d.x₅ v = v ↔
      (v = 1 ∨ v = zV h49 hd ∨ v = z0V hz ∨ v = zV h49 hd * z0V hz) := by
  have hCQX := hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich
  have hfix := actFun_fixes_iff d.s56V (x5_mem_Hg h49 hd) v
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzz₀ : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  show actFun d.s56V d.x₅ v = v ↔ _
  rw [hfix]
  constructor
  · intro hc
    have hmem : (v : G) ∈ d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
      refine ⟨V_le_Q v.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro g ⟨n, rfl⟩
      exact (Commute.zpow_left (show Commute d.x₅ (v : G) from hc) n).eq
    rw [hCQX, mem_sup_zpowers_iff hzz hz₀z₀ hzz₀] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · left; exact Subtype.ext h1
    · right; left; exact Subtype.ext h1
    · right; right; left; exact Subtype.ext h1
    · right; right; right; exact Subtype.ext h1
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · exact hd.s56_x5_comm_z
    · exact hz.comm_x
    · show d.x₅ * (d.z * z₀) = d.z * z₀ * d.x₅
      rw [← mul_assoc, hd.s56_x5_comm_z, mul_assoc, hz.comm_x, mul_assoc]

theorem star_t_fix_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (v : ↥d.s56V) :
    star d d.t v = v ↔ (v : G) ∈ d.E := by
  rw [star_eq, actFun_fixes_iff d.s56V (t_mem_Hg h49 hd), ← hd.s56_V_eps_eq_one_iff h49 v.2]
  constructor
  · intro h
    exact hd.s56_eps_of_comm h.symm
  · intro h
    have h1 := hd.s56_conj_t (v : G)
    rw [h, mul_one] at h1
    calc d.t * (v : G) = ((v : G) * d.t * (v : G)⁻¹) * (v : G) := by rw [h1]
      _ = (v : G) * d.t := by group

theorem star_t_apply_mul_inv_mem (h49 : d.Thm49Statement) (hd : d.Hyp) (v : ↥d.s56V) :
    ((star d d.t v : ↥d.s56V) : G) * (v : G)⁻¹ ∈ d.E := by
  rw [star_eq, actFun_apply_coe d.s56V (t_mem_Hg h49 hd)]
  have h1 : d.s56Eps (v : G) = d.t * ((v : G) * d.t * (v : G)⁻¹) := rfl
  have h2 : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_self
  have h3 : d.t * (v : G) * d.t⁻¹ * (v : G)⁻¹ = d.s56Eps (v : G) := by
    rw [h1, h2]; group
  rw [h3]
  exact hd.s56_V_eps_mem_E v.2

theorem card_E_subgroupOf (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card (d.E.subgroupOf d.s56V) = 2 ^ 5 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hd.s56_E_le_V h49)).toEquiv]
  exact hd.A_facts.1

theorem z0V_not_mem (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    z0V hz ∉ d.E.subgroupOf d.s56V := by
  intro h
  have h1 : z₀ ∈ d.E := Subgroup.mem_subgroupOf.1 h
  have h2 := (hd.s56_V_eps_eq_one_iff h49 hz.mem_V).2 h1
  rw [hz.eps] at h2
  exact hd.s56_z_ne_one h2

theorem star_t_z0V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    star d d.t (z0V hz) = z0V hz * zV h49 hd := by
  apply Subtype.ext
  rw [star_eq, actFun_apply_coe d.s56V (t_mem_Hg h49 hd)]
  have h1 : d.s56Eps z₀ = d.t * (z₀ * d.t * z₀⁻¹) := rfl
  rw [hz.eps] at h1
  have h2 : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_self
  have h3 : d.t * z₀ * d.t⁻¹ = d.z * z₀ := by
    rw [h2]
    calc d.t * z₀ * d.t = d.t * (z₀ * d.t * z₀⁻¹) * z₀ := by group
      _ = d.z * z₀ := by rw [← h1]
  show d.t * z₀ * d.t⁻¹ = z₀ * d.z
  rw [h3]
  exact (hz.cen hd.s56_z_mem_E).symm

theorem star_mem_E_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {g : G} (hg : g ∈ d.M)
    (e : ↥d.s56V) (he : e ∈ d.E.subgroupOf d.s56V) :
    star d g e ∈ d.E.subgroupOf d.s56V := by
  rw [Subgroup.mem_subgroupOf] at he ⊢
  rw [star_eq, actFun_apply_coe d.s56V (M_le_Hg h49 hd hg)]
  exact (mem_normalizer_iff.1 (hd.s56_ME hg) (e : G)).1 he

theorem exists_thData (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    ∃ D : @ThData ↥d.s56V (vCommGroup h10) inferInstance,
      @ThData.E _ (vCommGroup h10) _ D = d.E.subgroupOf d.s56V ∧
        @ThData.z _ (vCommGroup h10) _ D = zV h49 hd ∧
        @ThData.z₀ _ (vCommGroup h10) _ D = z0V hz ∧
        @ThData.τ _ (vCommGroup h10) _ D = star d d.t ∧
        @ThData.x _ (vCommGroup h10) _ D = star d d.x₅ ∧
        @ThData.y _ (vCommGroup h10) _ D = star d y₁ :=
  ⟨@ThData.mk ↥d.s56V (vCommGroup h10) inferInstance
    (fun a => Subtype.ext (h10.sq_V a.2))
    h10.card_V
    (d.E.subgroupOf d.s56V)
    (card_E_subgroupOf h49 hd)
    (zV h49 hd)
    (z0V hz)
    (Subgroup.mem_subgroupOf.2 hd.s56_z_mem_E)
    (fun h => hd.s56_z_ne_one (congrArg Subtype.val h))
    (z0V_not_mem h49 hd hz)
    (star d d.t)
    (star d d.x₅)
    (star d y₁)
    (star_t_mul_self h49 hd)
    (fun v => (star_t_fix_iff h49 hd v).trans Subgroup.mem_subgroupOf.symm)
    (fun v => Subgroup.mem_subgroupOf.2 (star_t_apply_mul_inv_mem h49 hd v))
    (star_t_z0V h49 hd hz h10)
    (star_x5_pow_five h49 hd)
    (star_x5_fix_iff h49 hd hz h10)
    (fun e he => star_mem_E_iff h49 hd hd.s56_x5_mem_M e he)
    (actFun_comm_of_comm d.s56V hd.s56_x5_comm_t)
    (hy.isFrob h49 hd hz h10).yx
    (hy.isFrob h49 hd hz h10).y4
    (actFun_comm_of_comm d.s56V (mem_centralizer_singleton_iff.1 hy.mem_C))
    ((actFun_fixes_iff d.s56V (y1_mem_Hg h49 hd hy) _).2 (hd.s56_M_comm_z (hy.mem_M hd)))
    ((actFun_fixes_iff d.s56V (y1_mem_Hg h49 hd hy) _).2 hy.2.1)
    (fun e he => star_mem_E_iff h49 hd (hy.mem_M hd) e he),
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mem_sup_zpowers_of_comm {Γ : Type*} [Group Γ] (H : Subgroup Γ) (a : Γ) (ha : a * a = 1)
    (hc : ∀ h ∈ H, h * a = a * h) (v : Γ) :
    v ∈ H ⊔ zpowers a ↔ v ∈ H ∨ ∃ e ∈ H, v = e * a := by
  have hnorm : H ≤ normalizer (zpowers a : Set Γ) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := hw
    exact (Commute.zpow_left (show Commute a u from (hc u hu).symm) n).eq
  have hset : ((H ⊔ zpowers a : Subgroup Γ) : Set Γ) = (H : Set Γ) * (zpowers a : Set Γ) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H (zpowers a) hnorm
  have hmem : v ∈ H ⊔ zpowers a ↔ ∃ u ∈ H, ∃ w ∈ zpowers a, u * w = v := by
    rw [← SetLike.mem_coe, hset]
    exact Set.mem_mul
  rw [hmem]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    rcases eq_one_or_of_mem_zpowers ha hw with rfl | rfl
    · left; simpa using hu
    · right; exact ⟨u, hu, rfl⟩
  · rintro (hv | ⟨e, he, rfl⟩)
    · exact ⟨v, hv, 1, one_mem _, mul_one v⟩
    · exact ⟨e, he, a, mem_zpowers a, rfl⟩

theorem f5Stmt : ThData.F5Stmt := fun hsq W hW x y hx5 hxW hyW hxfpf hyx w₀ hw₀W hw₀1 hw₀y =>
  fixed_vectors_of_frobenius20 hsq W hW x y hx5 hxW hyW hxfpf hyx w₀ hw₀W hw₀1 hw₀y

theorem coe_star_mul_inv (g : G) (hg : g ∈ Hg d) (a : ↥d.s56V) :
    ((star d g a * a⁻¹ : ↥d.s56V) : G) = g * (a : G) * g⁻¹ * (a : G)⁻¹ := by
  show ((star d g a : ↥d.s56V) : G) * ((a⁻¹ : ↥d.s56V) : G) = _
  rw [star_eq, actFun_apply_coe d.s56V hg]
  rfl

theorem commutator_V_X_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀)
    (D : @ThData ↥d.s56V (vCommGroup h10) inferInstance)
    (hx : @ThData.x _ (vCommGroup h10) _ D = star d d.x₅) :
    ⁅d.s56V, Xg d⁆ = (@ThData.V₁ _ (vCommGroup h10) _ D).map d.s56V.subtype := by
  letI : CommGroup ↥d.s56V := vCommGroup h10
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha g hg
    have hnat : ∀ m : ℕ, a * d.x₅ ^ m * a⁻¹ * (d.x₅ ^ m)⁻¹ ∈
        (D.V₁).map d.s56V.subtype := by
      intro m
      have hgm : d.x₅ ^ m ∈ Hg d := pow_mem (x5_mem_Hg h49 hd) m
      refine ⟨((D.x ^ m) ⟨a, ha⟩ * (⟨a, ha⟩ : ↥d.s56V)⁻¹)⁻¹,
        D.V₁.inv_mem (D.xpow_mul_inv_mem_V₁ m _), ?_⟩
      have hD : D.x ^ m = star d (d.x₅ ^ m) := by
        rw [hx, star_eq, star_eq, actFun_pow d.s56V (x5_mem_Hg h49 hd)]
        rfl
      have h1 := coe_star_mul_inv (d := d) (d.x₅ ^ m) hgm ⟨a, ha⟩
      rw [hD]
      show (((star d (d.x₅ ^ m) ⟨a, ha⟩ * (⟨a, ha⟩ : ↥d.s56V)⁻¹ : ↥d.s56V))⁻¹ : G) = _
      rw [h1]
      group
    obtain ⟨n, rfl⟩ := hg
    have hord : orderOf d.x₅ = 5 := hd.s56_orderOf_x5
    have hn : d.x₅ ^ n = d.x₅ ^ (n % 5).toNat := by
      have h1 := zpow_mod_orderOf d.x₅ n
      rw [hord] at h1
      have h2 : ((n % 5).toNat : ℤ) = n % 5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [← zpow_natCast, h2]
      exact h1.symm
    show a * (d.x₅ ^ n) * a⁻¹ * (d.x₅ ^ n)⁻¹ ∈ _
    rw [hn]
    exact hnat _
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := hw
    have h1 : ((D.xm1 a : ↥d.s56V) : G) = d.x₅ * (a : G) * d.x₅⁻¹ * (a : G)⁻¹ := by
      rw [ThData.xm1_apply, hx]
      exact coe_star_mul_inv d.x₅ (x5_mem_Hg h49 hd) a
    show ((D.xm1 a : ↥d.s56V) : G) ∈ ⁅d.s56V, Xg d⁆
    rw [h1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (mem_zpowers d.x₅) a.2

theorem mem_axis_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀)
    (D : @ThData ↥d.s56V (vCommGroup h10) inferInstance)
    (hx : @ThData.x _ (vCommGroup h10) _ D = star d d.x₅)
    (hzD : @ThData.z _ (vCommGroup h10) _ D = zV h49 hd) (y : ↥d.s56V) :
    (y : G) ∈ ⁅d.s56V, Xg d⁆ ⊔ zpowers d.z ↔
      ∃ a : ↥d.s56V, y = (@ThData.x _ (vCommGroup h10) _ D) a * a⁻¹ ∨
        y = (@ThData.x _ (vCommGroup h10) _ D) a * a⁻¹ * (@ThData.z _ (vCommGroup h10) _ D) := by
  letI : CommGroup ↥d.s56V := vCommGroup h10
  rw [commutator_V_X_eq h49 hd h10 D hx]
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hc : ∀ h ∈ D.V₁.map d.s56V.subtype, h * d.z = d.z * h := by
    rintro _ ⟨w, hw, rfl⟩
    exact h10.comm_V w.2 (hd.s56_E_le_V h49 hd.s56_z_mem_E)
  rw [mem_sup_zpowers_of_comm _ d.z hzz hc]
  have hzcoe : ((D.z : ↥d.s56V) : G) = d.z := by rw [hzD]; rfl
  constructor
  · rintro (⟨w, hw, hwy⟩ | ⟨e, ⟨w, hw, rfl⟩, hey⟩)
    · obtain ⟨a, rfl⟩ := hw
      exact ⟨a, Or.inl (Subtype.ext hwy).symm⟩
    · obtain ⟨a, rfl⟩ := hw
      refine ⟨a, Or.inr (Subtype.ext ?_)⟩
      rw [hey]
      show _ = ((D.x a * a⁻¹ : ↥d.s56V) : G) * ((D.z : ↥d.s56V) : G)
      rw [hzcoe]
      rfl
  · rintro ⟨a, rfl | rfl⟩
    · left
      exact ⟨D.x a * a⁻¹, D.xm1_mem_V₁ a, rfl⟩
    · right
      refine ⟨((D.x a * a⁻¹ : ↥d.s56V) : G), ⟨D.x a * a⁻¹, D.xm1_mem_V₁ a, rfl⟩, ?_⟩
      show ((D.x a * a⁻¹ * D.z : ↥d.s56V) : G) = ((D.x a * a⁻¹ : ↥d.s56V) : G) * d.z
      rw [← hzcoe]
      rfl

theorem node15 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Node15 d z₀ := by
  intro y₁ hy S' hS' ht
  obtain ⟨D, hE, hz', hz₀', hτ, hx, hy'⟩ := exists_thData h49 hd hz h10 hy
  letI : CommGroup ↥d.s56V := vCommGroup h10
  have hSOK : D.SOK S' := by
    refine ⟨hS'.2.1, ?_, ?_, ?_⟩
    · intro s hs
      have hmem : D.x ∈ ((img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) :
          Set (MulAut ↥d.s56V)) := by
        rw [hx]
        refine mem_sup_left ?_
        rw [img_eq, show Xg d = zpowers d.x₅ from rfl, imgIn_zpowers d.s56V (x5_mem_Hg h49 hd)]
        exact mem_zpowers _
      exact (mem_centralizer_iff.1 (hS'.1 hs).1 _ hmem).symm
    · intro s hs
      have hmem : D.y ∈ ((img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) :
          Set (MulAut ↥d.s56V)) := by
        rw [hy']
        exact mem_sup_right (mem_zpowers _)
      exact (mem_centralizer_iff.1 (hS'.1 hs).1 _ hmem).symm
    · rw [hτ]
      exact ht
  have hmain := ThData.thompson68_of_F5 f5Stmt D hSOK
  rcases hmain with hS | ⟨β, hβS, hSβ, hP1, hP2, hP3, hP4⟩
  · left
    rw [hτ] at hS
    exact hS
  · right
    obtain ⟨b, hbH, hbN, hb⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 ((hS'.1 hβS).2)
    have hbstar : β = star d b := hb.symm
    refine ⟨b, hbH, ?_, ?_, ?_⟩
    · rw [hτ, hbstar] at hSβ
      exact hSβ
    · have hzcoe : ((D.z : ↥d.s56V) : G) = d.z := by rw [hz']; rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine sup_le ?_ (zpowers_le.2 (hd.s56_E_le_V h49 hd.s56_z_mem_E))
        rw [Subgroup.commutator_le]
        intro a ha g hg
        have hgN : g ∈ normalizer (d.s56V : Set G) := Xg_le_Hg h49 hd hg
        have h1 : g * a⁻¹ * g⁻¹ ∈ d.s56V := (mem_normalizer_iff.1 hgN a⁻¹).1 (inv_mem ha)
        have e : a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) := by group
        rw [commutatorElement_def, e]
        exact mul_mem ha h1
      · exact mem_sup_right (mem_zpowers _)
      · obtain ⟨v, hv⟩ := hP3
        exact ⟨(v : G), v.2, fun hmem => hv ((mem_axis_iff h49 hd h10 D hx hz' v).1 hmem)⟩
      · intro y hy
        have key : ((β ⟨y, hy⟩ : ↥d.s56V) : G) = b * y * b⁻¹ := by
          rw [← hb]
          exact actFun_apply_coe d.s56V hbN ⟨y, hy⟩
        refine ⟨?_, ?_⟩
        · rcases hP1 ⟨y, hy⟩ with h1 | h1
          · left
            rw [← key, h1]
          · right
            rw [← key, h1]
            show y * ((D.z : ↥d.s56V) : G) = y * d.z
            rw [hzcoe]
        · rw [← key]
          constructor
          · intro hfix
            exact (mem_axis_iff h49 hd h10 D hx hz' ⟨y, hy⟩).2 ((hP2 ⟨y, hy⟩).1 (Subtype.ext hfix))
          · intro hmem
            exact congrArg Subtype.val
              ((hP2 ⟨y, hy⟩).2 ((mem_axis_iff h49 hd h10 D hx hz' ⟨y, hy⟩).1 hmem))
    · have hz₀₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
      have hcE : ∀ h ∈ d.E, h * z₀ = z₀ * h := fun h hh => (hz.cen hh).symm
      have hGsup := mem_sup_zpowers_of_comm d.E z₀ hz₀₀ hcE
      have hz₀coe : ((D.z₀ : ↥d.s56V) : G) = z₀ := by rw [hz₀']; rfl
      have hiffE : ∀ y : ↥d.s56V, ((y : G) ∈ d.E ⊔ zpowers z₀ ↔ y ∈ D.E ⊔ zpowers D.z₀) := by
        intro y
        rw [hGsup, ThData.mem_E_sup_iff]
        have hEm : ∀ w : ↥d.s56V, w ∈ D.E ↔ (w : G) ∈ d.E := fun w => by
          rw [hE]; exact Subgroup.mem_subgroupOf
        constructor
        · rintro (h1 | ⟨e, he, hey⟩)
          · left; exact (hEm y).2 h1
          · right
            refine ⟨⟨e, hd.s56_E_le_V h49 he⟩, (hEm _).2 he, Subtype.ext ?_⟩
            show (y : G) = ((D.z₀ : ↥d.s56V) : G) * e
            rw [hz₀coe, hey, hcE e he]
        · rintro (h1 | ⟨e, he, hey⟩)
          · left; exact (hEm y).1 h1
          · right
            refine ⟨(e : G), (hEm e).1 he, ?_⟩
            have := congrArg Subtype.val hey
            show (y : G) = (e : G) * z₀
            rw [← hz₀coe]
            have h2 : (y : G) = ((D.z₀ : ↥d.s56V) : G) * (e : G) := this
            rw [h2, hz₀coe, hcE e ((hEm e).1 he)]
      have htb : d.t * b ∈ normalizer (d.s56V : Set G) := mul_mem (t_mem_Hg h49 hd) hbH
      have hτb : D.τ * β = star d (d.t * b) := by
        rw [hτ, hbstar, star_eq, star_eq, star_eq, actFun_mul d.s56V (t_mem_Hg h49 hd) hbN]
        rfl
      have hcent : ∀ y : ↥d.s56V, ((y : G) ∈ centralizer ({d.t * b} : Set G) ↔ (D.τ * β) y = y) := by
        intro y
        have h1 := actFun_fixes_iff d.s56V htb y
        rw [mem_centralizer_singleton_iff, hτb]
        exact (h1.trans eq_comm).symm
      ext y
      constructor
      · rintro ⟨hyV, hyC⟩
        exact (hiffE ⟨y, hyV⟩).2 ((hP4 ⟨y, hyV⟩).1 ((hcent ⟨y, hyV⟩).1 hyC))
      · intro hy
        have hyV : y ∈ d.s56V := (sup_le (hd.s56_E_le_V h49) (zpowers_le.2 hz.mem_V)) hy
        exact ⟨hyV, (hcent ⟨y, hyV⟩).2 ((hP4 ⟨y, hyV⟩).2 ((hiffE ⟨y, hyV⟩).1 hy))⟩

theorem step15_holds : Step15 := by
  intro G _ _ d z₀ h49 hd hz h10
  exact node15 h49 hd hz h10

end S15



end CFSG.LocalAnalysis.EvenBN.Tits.N
