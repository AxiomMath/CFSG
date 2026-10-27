module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42C

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem sq_eq_one_of_mem_closure_three {G : Type} [Group G] {a b c x : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hc : orderOf c = 2) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (hx : x ∈ closure {a, b, c}) : x ^ 2 = 1 := by
  obtain ⟨a', b', c', ha', hb', hc', rfl⟩ := mem_closure_three ha hb hc hab hac hbc hx
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hb2 : b ^ 2 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hc2 : c ^ 2 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have h1 : a' ^ 2 = 1 := by rcases ha' with rfl | rfl <;> simp [ha2]
  have h2 : b' ^ 2 = 1 := by rcases hb' with rfl | rfl <;> simp [hb2]
  have h3 : c' ^ 2 = 1 := by rcases hc' with rfl | rfl <;> simp [hc2]
  have h12 : Commute a' b' := by
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    exacts [Commute.one_left _, Commute.one_left _, Commute.one_right _, hab]
  have h13 : Commute a' c' := by
    rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl
    exacts [Commute.one_left _, Commute.one_left _, Commute.one_right _, hac]
  have h23 : Commute b' c' := by
    rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl
    exacts [Commute.one_left _, Commute.one_left _, Commute.one_right _, hbc]
  rw [(h13.mul_left h23).mul_pow, h12.mul_pow, h1, h2, h3, one_mul, one_mul]

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem sq_eq_one_of_mem_X [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hx : x ∈ closure {t, w ^ (orderOf w / 2), z}) : x ^ 2 = 1 :=
  sq_eq_one_of_mem_closure_three h.config.orderOf_eq hσ.orderOf_u hσ.z_order
    (mem_centralizer_singleton_iff.mp (hS.le hσ.u_mem)).symm
    (mem_centralizer_singleton_iff.mp (hS.le hσ.z_mem.1)).symm
    (hσ.lift.comm_D z hσ.z_mem).symm hx

theorem X_le_T [Finite X] (hσ : Setup42 h hS w z) :
    closure {t, w ^ (orderOf w / 2), z} ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
  hσ.X_le_center_T.trans inf_le_left

theorem conj_mem_X [Finite X] (hσ : Setup42 h hS w z) {s x : X} (hs : s ∈ S)
    (hx : x ∈ closure {t, w ^ (orderOf w / 2), z}) :
    s * x * s⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
  rw [← hσ.centralizer_D] at hx ⊢
  refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs hx.1) (S.inv_mem hs),
    mem_centralizer_iff.mpr fun d hd => ?_⟩
  have hd' : s⁻¹ * d * s ∈ S ⊓ L := by
    simpa using hσ.conj_mem_D (S.inv_mem hs) hd
  have hc := mem_centralizer_iff.mp hx.2 _ hd'
  calc d * (s * x * s⁻¹) = s * ((s⁻¹ * d * s) * x) * s⁻¹ := by group
    _ = s * (x * (s⁻¹ * d * s)) * s⁻¹ := by rw [hc]
    _ = s * x * s⁻¹ * d := by group

theorem mem_T1 [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hx : x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) :
    ∃ i : ℤ, ∃ d ∈ S ⊓ L, ∃ j : ℤ, x = t ^ i * d * (w ^ (orderOf w / 2)) ^ j := by
  have htC : t ∈ centralizer (zpowers (w ^ (orderOf w / 2)) : Set X) :=
    mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp (hS.le hσ.u_mem)) j).eq
  have hDC : S ⊓ L ≤ centralizer (zpowers (w ^ (orderOf w / 2)) : Set X) := fun d hd =>
    mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute (w ^ (orderOf w / 2)) d from
        (hσ.lift.comm_D d hd).symm) j).eq
  have huN : zpowers (w ^ (orderOf w / 2)) ≤
      normalizer ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) :=
    (le_centralizer_iff.mp (sup_le (zpowers_le.mpr htC) hDC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have htN : zpowers t ≤ normalizer ((S ⊓ L : Subgroup X) : Set X) := fun y hy => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun d hd => ?_)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hS.le hd.1)) i).eq
  have hx' : x ∈ ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) *
      (zpowers (w ^ (orderOf w / 2)) : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ huN]
    exact hx
  obtain ⟨y, hy, _, ⟨j, rfl⟩, rfl⟩ := hx'
  have hy' : y ∈ (zpowers t : Set X) * ((S ⊓ L : Subgroup X) : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ htN]
    exact hy
  obtain ⟨_, ⟨i, rfl⟩, d, hd, rfl⟩ := hy'
  exact ⟨i, d, hd, j, rfl⟩

theorem le_X_of_normal_T [Finite X] (hσ : Setup42 h hS w z) {F : Subgroup X}
    (hFT : F ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (hFn : ∀ g ∈ S ⊓ L, ∀ x ∈ F, g * x * g⁻¹ ∈ F)
    (hF2 : ∀ x ∈ F, x ^ 2 = 1) : F ≤ closure {t, w ^ (orderOf w / 2), z} := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  have hFD : F ⊓ (S ⊓ L) ≤ zpowers z :=
    normal_le_zpowers e hm hσ.center_D inf_le_right
      (fun d hd x hx => Subgroup.mem_inf.mpr ⟨hFn d hd x hx.1, hσ.conj_mem_D hd.1 hx.2⟩)
      (fun x hx => hF2 x hx.1)
  intro x hx
  have hxT := hFT hx
  obtain ⟨i, d, hd, j, hxe⟩ := hσ.mem_T1 (hσ.involution_mem hxT (hF2 x hx))
  have hti : ∀ y ∈ S, t ^ i * y = y * t ^ i := fun y hy =>
    (Commute.zpow_left (mem_centralizer_singleton_iff.mp (hS.le hy)).symm i).eq
  have huj : ∀ y ∈ S ⊓ L, (w ^ (orderOf w / 2)) ^ j * y = y * (w ^ (orderOf w / 2)) ^ j :=
    fun y hy => (Commute.zpow_left (show Commute (w ^ (orderOf w / 2)) y from
      (hσ.lift.comm_D y hy).symm) j).eq
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hti2 : (t ^ i) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have huj2 : ((w ^ (orderOf w / 2)) ^ j) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ.lift.sq_u, one_zpow]
  have hc1 : Commute (t ^ i) d := hti d hd.1
  have hc2 : Commute (t ^ i) ((w ^ (orderOf w / 2)) ^ j) :=
    hti _ (zpow_mem hσ.u_mem j)
  have hc3 : Commute d ((w ^ (orderOf w / 2)) ^ j) := (huj d hd).symm
  have hd2 : d ^ 2 = 1 := by
    have := hF2 x hx
    rw [hxe, (hc2.mul_left hc3).mul_pow, hc1.mul_pow, hti2, huj2, one_mul, mul_one] at this
    exact this
  have hcomm : ∀ d' ∈ S ⊓ L, d⁻¹ * d'⁻¹ * d * d' ∈ zpowers z := by
    intro d' hd'
    have hxS : x ∈ S := hσ.T_le hxT
    have hmemF : x⁻¹ * d'⁻¹ * x * d' ∈ F := by
      have h1 := hFn d'⁻¹ (inv_mem hd') x hx
      rw [inv_inv] at h1
      rw [show x⁻¹ * d'⁻¹ * x * d' = x⁻¹ * (d'⁻¹ * x * d') by group]
      exact F.mul_mem (F.inv_mem hx) h1
    have hmemD : x⁻¹ * d'⁻¹ * x * d' ∈ S ⊓ L := by
      have h1 := hσ.conj_mem_D (S.inv_mem hxS) (inv_mem hd')
      rw [inv_inv] at h1
      exact mul_mem h1 hd'
    have heq : x⁻¹ * d'⁻¹ * x * d' = d⁻¹ * d'⁻¹ * d * d' := by
      have e1 : (t ^ i)⁻¹ * d'⁻¹ * t ^ i = d'⁻¹ := by
        rw [mul_assoc, ← hti _ (S.inv_mem hd'.1), ← mul_assoc, inv_mul_cancel, one_mul]
      have hdd : d⁻¹ * d'⁻¹ * d ∈ S ⊓ L := mul_mem (mul_mem (inv_mem hd) (inv_mem hd')) hd
      have e2 : ((w ^ (orderOf w / 2)) ^ j)⁻¹ * (d⁻¹ * d'⁻¹ * d) * (w ^ (orderOf w / 2)) ^ j =
          d⁻¹ * d'⁻¹ * d := by
        rw [mul_assoc, ← huj _ hdd, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hxe]
      calc (t ^ i * d * (w ^ (orderOf w / 2)) ^ j)⁻¹ * d'⁻¹ *
            (t ^ i * d * (w ^ (orderOf w / 2)) ^ j) * d' =
          ((w ^ (orderOf w / 2)) ^ j)⁻¹ * (d⁻¹ * ((t ^ i)⁻¹ * d'⁻¹ * t ^ i) * d) *
            (w ^ (orderOf w / 2)) ^ j * d' := by group
        _ = ((w ^ (orderOf w / 2)) ^ j)⁻¹ * (d⁻¹ * d'⁻¹ * d) *
            (w ^ (orderOf w / 2)) ^ j * d' := by rw [e1]
        _ = d⁻¹ * d'⁻¹ * d * d' := by rw [e2]
    rw [← heq]
    exact hFD (Subgroup.mem_inf.mpr ⟨hmemF, hmemD⟩)
  have hdz := mem_zpowers_of_comm_le e hm hσ.center_D hd hd2 hcomm
  rw [hxe]
  refine mul_mem (mul_mem (zpow_mem (subset_closure (by simp)) i) ?_)
    (zpow_mem (subset_closure (by simp)) j)
  exact (zpowers_le.mpr (subset_closure (by simp))) hdz

theorem le_T_of_normal_S [Finite X] (hσ : Setup42 h hS w z) {F : Subgroup X} (hFS : F ≤ S)
    (hFn : ∀ g ∈ S ⊓ L, ∀ x ∈ F, g * x * g⁻¹ ∈ F) (hF2 : ∀ x ∈ F, x ^ 2 = 1) :
    F ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  have hdata := hσ.lift.data
  have hR := h.map_rho_inf_innAut hS
  have hFD : F ⊓ (S ⊓ L) ≤ zpowers z :=
    normal_le_zpowers e hm hσ.center_D inf_le_right
      (fun d hd x hx => Subgroup.mem_inf.mpr ⟨hFn d hd x hx.1, hσ.conj_mem_D hd.1 hx.2⟩)
      (fun x hx => hF2 x hx.1)
  intro f hf
  by_contra hfT
  have hfS := hFS hf
  set y : ↥(S ⊓ L) := e.symm (DihedralGroup.sr 0) with hy
  set c : ↥(S ⊓ L) := e.symm (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) with hc
  have hz := hσ.coe_symm_r_half hm e
  have hyc : (c : X)⁻¹ * y * c = z * y := by
    rw [← hz]
    have : c⁻¹ * y * c = e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * y := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hy, hc]
      rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.r_mul_sr]
      congr 1
      have h0 : (2 : ZMod (2 ^ m)) ^ (m - 2) * 4 = 0 := by
        rw [show (4 : ZMod (2 ^ m)) = 2 ^ 2 by norm_num, ← pow_add,
          Nat.sub_add_cancel (by omega : 2 ≤ m)]
        exact_mod_cast ZMod.natCast_self (2 ^ m)
      push_cast
      rw [show m - 1 = m - 2 + 1 by omega, pow_succ]
      linear_combination h0
    exact congrArg Subtype.val this
  have hyS : (y : X) ∈ S := y.2.1
  have hmem : f⁻¹ * y * f * (y : X)⁻¹ ∈ F ⊓ (S ⊓ L) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [show f⁻¹ * y * f * (y : X)⁻¹ = f⁻¹ * (y * f * (y : X)⁻¹) by group]
      exact F.mul_mem (F.inv_mem hf) (hFn _ y.2 f hf)
    · have h1 := hσ.conj_mem_D (S.inv_mem hfS) y.2
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem y.2)
  have hfH := hS.le hfS
  have hα : h.rho ⟨f, hfH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho :=
    ⟨⟨f, hfH⟩, hfS, rfl⟩
  have hα' : h.rho ⟨f, hfH⟩ ∉ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := fun h' =>
    hfT (hσ.mem_T_of_rho_mem hfS h')
  have hne : (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ≠
      ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
        zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := fun heq => hα' (heq ▸ hα)
  have hyH := hS.le hyS
  have hyR : h.rho ⟨y, hyH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L) := by
    rw [hR]
    exact ⟨⟨y, hyH⟩, y.2, rfl⟩
  have hy2 : h.rho ⟨y, hyH⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 := by
      apply Subtype.ext
      change (y : X) ^ 2 = 1
      have : y ^ 2 = 1 := by
        apply e.injective
        rw [sq, map_mul, hy, MulEquiv.apply_symm_apply, DihedralGroup.sr_mul_sr, sub_self,
          DihedralGroup.r_zero, map_one]
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    rw [this, map_one]
  have hyC : h.rho ⟨y, hyH⟩ ∉ centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
    intro hyC
    have hyZ : (y : X) ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
      refine Subgroup.mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hdR : h.rho ⟨d, hS.le hd.1⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
          innAut (Bar L) := by
        rw [hR]
        exact ⟨⟨d, hS.le hd.1⟩, hd, rfl⟩
      have := mem_centralizer_iff.mp hyC _ hdR
      exact (h.commute_of_rho_commute hS hyS hd.1 y.2.2 this.symm).symm
    rw [hσ.center_D] at hyZ
    rcases eq_one_or_eq_of_mem_zpowers hσ.z_order hyZ with h1 | h1
    · have : y = 1 := Subtype.ext h1
      rw [hy, MulEquiv.map_eq_one_iff] at this
      exact absurd (this.trans DihedralGroup.one_def) fun h' => by cases h'
    · rw [← hz] at h1
      have : y = e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := Subtype.ext h1
      rw [hy] at this
      exact absurd (e.symm.injective this) fun h' => by cases h'
  have hswap := hdata.swap_of_ne hne _ hα hα' _ hyR hy2 hyC
  have hfy : h.rho ⟨f⁻¹ * y * f, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hfS) hyS) hfS)⟩ =
      (h.rho ⟨f, hfH⟩)⁻¹ * h.rho ⟨y, hyH⟩ * h.rho ⟨f, hfH⟩ := by
    have : (⟨f⁻¹ * y * f, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hfS) hyS) hfS)⟩ :
        ↥(centralizer ({t} : Set X))) = (⟨f, hfH⟩)⁻¹ * ⟨y, hyH⟩ * ⟨f, hfH⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
  rcases eq_one_or_eq_of_mem_zpowers hσ.z_order (hFD hmem) with h1 | h1
  ·
    have h2 : f⁻¹ * y * f = y := by
      rw [mul_inv_eq_one] at h1
      exact h1
    apply hswap 1 (one_mem _)
    rw [← hfy]
    simp only [h2, inv_one, one_mul, mul_one]
  ·
    have h2 : f⁻¹ * y * f = (c : X)⁻¹ * y * c := by
      rw [hyc, ← h1]
      group
    have hcH := hS.le c.2.1
    have hcR : h.rho ⟨c, hcH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        innAut (Bar L) := by
      rw [hR]
      exact ⟨⟨c, hcH⟩, c.2, rfl⟩
    apply hswap _ hcR
    rw [← hfy]
    have : (⟨f⁻¹ * y * f, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hfS) hyS) hfS)⟩ :
        ↥(centralizer ({t} : Set X))) = (⟨c, hcH⟩)⁻¹ * ⟨y, hyH⟩ * ⟨c, hcH⟩ := Subtype.ext h2
    rw [this, map_mul, map_mul, map_inv]

theorem le_X_of_normal_S [Finite X] (hσ : Setup42 h hS w z) {F : Subgroup X} (hFS : F ≤ S)
    (hFn : ∀ g ∈ S ⊓ L, ∀ x ∈ F, g * x * g⁻¹ ∈ F) (hF2 : ∀ x ∈ F, x ^ 2 = 1) :
    F ≤ closure {t, w ^ (orderOf w / 2), z} :=
  hσ.le_X_of_normal_T (hσ.le_T_of_normal_S hFS hFn hF2) hFn hF2

theorem normalizer_S_le_normalizer_X [Finite X] (hσ : Setup42 h hS w z) :
    normalizer (S : Set X) ≤
      normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  intro n hn
  have hXS : closure {t, w ^ (orderOf w / 2), z} ≤ S := hσ.X_le_T.trans hσ.T_le
  have hFS : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj n).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hn x).mp (hXS hx)
  have hFn : ∀ g ∈ S, ∀ x ∈ (closure {t, w ^ (orderOf w / 2), z}).map
      (MulAut.conj n).toMonoidHom, g * x * g⁻¹ ∈ (closure {t, w ^ (orderOf w / 2), z}).map
        (MulAut.conj n).toMonoidHom := by
    rintro g hg _ ⟨x, hx, rfl⟩
    have hg' : n⁻¹ * g * n ∈ S := by
      simpa using (mem_normalizer_iff.mp (inv_mem hn) g).mp hg
    refine ⟨(n⁻¹ * g * n) * x * (n⁻¹ * g * n)⁻¹, hσ.conj_mem_X hg' hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hF2 : ∀ x ∈ (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj n).toMonoidHom,
      x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (n * x * n⁻¹) ^ 2 = n * x ^ 2 * n⁻¹ by rw [sq, sq]; group,
      hσ.sq_eq_one_of_mem_X hx, mul_one, mul_inv_cancel]
  have hFX := hσ.le_X_of_normal_S hFS (fun g hg => hFn g hg.1) hF2
  have hFeq : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj n).toMonoidHom =
      closure {t, w ^ (orderOf w / 2), z} :=
    Subgroup.eq_of_le_of_card_ge hFX
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hFeq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hFeq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj n).injective (by simpa [MulAut.conj_apply] using hyx)
    rwa [← this]

theorem normalizer_S_le_normalizer_T [Finite X] (hσ : Setup42 h hS w z) :
    normalizer (S : Set X) ≤
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := by
  have key : ∀ n ∈ normalizer (S : Set X), ∀ y ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
      n * y * n⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro n hn y hy
    have hnX' := hσ.normalizer_S_le_normalizer_X (inv_mem hn)
    rw [← hσ.centralizer_X] at hy ⊢
    refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hn y).mp hy.1,
      mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : n⁻¹ * x * n ∈ closure {t, w ^ (orderOf w / 2), z} := by
      simpa using (mem_normalizer_iff.mp hnX' x).mp hx
    have hc := mem_centralizer_iff.mp hy.2 _ hx'
    calc x * (n * y * n⁻¹) = n * ((n⁻¹ * x * n) * y) * n⁻¹ := by group
      _ = n * (y * (n⁻¹ * x * n)) * n⁻¹ := by rw [hc]
      _ = n * y * n⁻¹ * x := by group
  intro n hn
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun hy => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hy
  simpa [mul_assoc] using this

theorem normalizer_T_le_normalizer_X [Finite X] (hσ : Setup42 h hS w z) :
    normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) ≤
      normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  have key : ∀ n ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
        n * x * n⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
    intro n hn x hx
    rw [← hσ.center_T] at hx ⊢
    refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hn x).mp hx.1,
      mem_centralizer_iff.mpr fun g hg => ?_⟩
    have hg' : n⁻¹ * g * n ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      simpa using (mem_normalizer_iff.mp (inv_mem hn) g).mp hg
    have hc := mem_centralizer_iff.mp hx.2 _ hg'
    calc g * (n * x * n⁻¹) = n * ((n⁻¹ * g * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * g * n)) * n⁻¹ := by rw [hc]
      _ = n * x * n⁻¹ * g := by group
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using this

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
