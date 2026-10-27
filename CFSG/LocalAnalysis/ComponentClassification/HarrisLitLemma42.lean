module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralD

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

structure Setup42 (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (w z : X) : Prop where
  lift : Lift h hS w
  gen3 : ∀ Q : Subgroup (MulAut (Bar L)),
    Q ≤ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho →
      ∃ s : Finset (MulAut (Bar L)), s.card ≤ 3 ∧ Subgroup.closure (s : Set (MulAut (Bar L))) = Q
  dihedral : ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ m))
  z_mem : z ∈ S ⊓ L
  z_order : orderOf z = 2
  center_D : (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) = zpowers z

theorem exists_setup42 [Finite X] (hKG : AutPSL2SylowInput) (h : Standing t L p f)
    {S : Subgroup X} (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    ∃ w z : X, Setup42 h hS w z := by
  obtain ⟨⟨w, hL⟩, hgen⟩ := h.exists_lift hKG hS
  obtain ⟨m, hm, ⟨e⟩⟩ := h.exists_dihedral hL
  obtain ⟨z, hzD, hz2, hzc⟩ := exists_center_eq_zpowers e hm
  exact ⟨w, z, hL, hgen, ⟨m, hm, ⟨e⟩⟩, hzD, hz2, hzc⟩

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem conj_mem_D (_hσ : Setup42 h hS w z) {s d : X} (hs : s ∈ S) (hd : d ∈ S ⊓ L) :
    s * d * s⁻¹ ∈ S ⊓ L :=
  ⟨S.mul_mem (S.mul_mem hs hd.1) (S.inv_mem hs),
    (mem_normalizer_iff.mp (h.centralizer_le_normalizer (hS.le hs)) d).mp hd.2⟩

theorem z_comm_D (hσ : Setup42 h hS w z) {d : X} (hd : d ∈ S ⊓ L) : d * z = z * d := by
  have hzc : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    rw [hσ.center_D]
    exact mem_zpowers z
  exact mem_centralizer_iff.mp hzc.2 d hd

theorem z_comm (hσ : Setup42 h hS w z) {s : X} (hs : s ∈ S) : s * z = z * s := by
  have h1 : s * z * s⁻¹ ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    refine ⟨hσ.conj_mem_D hs hσ.z_mem, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hd' : s⁻¹ * d * s ∈ S ⊓ L := by
      have := hσ.conj_mem_D (S.inv_mem hs) hd
      rwa [inv_inv] at this
    have h2 := hσ.z_comm_D hd'
    calc d * (s * z * s⁻¹) = s * ((s⁻¹ * d * s) * z) * s⁻¹ := by group
      _ = s * (z * (s⁻¹ * d * s)) * s⁻¹ := by rw [h2]
      _ = s * z * s⁻¹ * d := by group
  rw [hσ.center_D] at h1
  rcases eq_one_or_eq_of_mem_zpowers hσ.z_order h1 with h2 | h2
  · exfalso
    have hz1 : z = 1 := by
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [h2]; group
    have := hσ.z_order
    rw [hz1, orderOf_one] at this
    exact absurd this (by norm_num)
  · calc s * z = (s * z * s⁻¹) * s := by group
      _ = z * s := by rw [h2]


theorem w_mem (hσ : Setup42 h hS w z) : w ∈ S := hσ.lift.mem

theorem u_mem (hσ : Setup42 h hS w z) : w ^ (orderOf w / 2) ∈ S := S.pow_mem hσ.w_mem _

theorem centralizer_u [Finite X] (hσ : Setup42 h hS w z) :
    S ⊓ centralizer {w ^ (orderOf w / 2)} = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
  (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.2.2.1

theorem T_le [Finite X] (hσ : Setup42 h hS w z) : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ S := by
  rw [← hσ.centralizer_u]
  exact inf_le_left

theorem rho_u [Finite X] (hσ : Setup42 h hS w z) :
    h.rho ⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ =
      h.rho ⟨w, hS.le hσ.w_mem⟩ ^ (orderOf (h.rho ⟨w, hS.le hσ.w_mem⟩) / 2) := by
  rw [← hσ.lift.orderOf_eq, ← map_pow]
  rfl

theorem X_le_center_T [Finite X] (hσ : Setup42 h hS w z) :
    closure {t, w ^ (orderOf w / 2), z} ≤
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓
        centralizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := by
  have hTu : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer {w ^ (orderOf w / 2)} := by
    rw [← hσ.centralizer_u]
    exact inf_le_right
  rw [closure_le]
  rintro x (rfl | rfl | rfl)
  · refine ⟨mem_sup_left (mem_sup_left (mem_zpowers x)), mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact mem_centralizer_singleton_iff.mp (hS.le (hσ.T_le hg))
  · refine ⟨mem_sup_right (pow_mem (mem_zpowers w) _), mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact mem_centralizer_singleton_iff.mp (hTu hg)
  · refine ⟨mem_sup_left (mem_sup_right hσ.z_mem), mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact hσ.z_comm (hσ.T_le hg)

theorem centralizer_D_le [Finite X] (hσ : Setup42 h hS w z) :
    S ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
  classical
  have hR := h.map_rho_inf_innAut hS
  have hdata := hσ.lift.data
  set v := h.rho ⟨w, hS.le hσ.w_mem⟩ with hv
  rintro x ⟨hxS, hxc⟩
  have hxH := hS.le hxS
  have hρx : h.rho ⟨x, hxH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) :
        Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
    refine ⟨⟨⟨x, hxH⟩, hxS, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ hφ
    rw [hR] at hφ
    obtain ⟨⟨d, hdH⟩, hdD, rfl⟩ := hφ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hxc d hdD)
  rw [hdata.centralizer_R] at hρx
  have hv0n : ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊓
      centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) :
        Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) ≤
      normalizer ((zpowers (v ^ (orderOf v / 2)) : Subgroup (MulAut (Bar L))) :
        Set (MulAut (Bar L))) := by
    rintro a ⟨haR, -⟩
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((Commute.zpow_left (hdata.comm_v₀ a haR).symm j) : _).eq
  have hρx' : h.rho ⟨x, hxH⟩ ∈ ((((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊓ centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        innAut (Bar L) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) ⊔
          zpowers (v ^ (orderOf v / 2)) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) :=
    hρx
  rw [coe_mul_of_left_le_normalizer_right _ _ hv0n] at hρx'
  obtain ⟨a, ⟨haR, hac⟩, b, hb, hab⟩ := hρx'
  beta_reduce at hab
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  have haD := haR
  rw [hR] at haD
  obtain ⟨⟨d, hdH⟩, hdD, rfl⟩ := haD
  change d ∈ S ⊓ L at hdD
  have hdz : d ∈ zpowers z := by
    rw [← hσ.center_D]
    refine ⟨hdD, mem_centralizer_iff.mpr fun d' hd' => ?_⟩
    have hc := mem_centralizer_iff.mp hac (h.rho ⟨d', hS.le hd'.1⟩)
      (by rw [hR]; exact ⟨_, hd', rfl⟩)
    exact h.commute_of_rho_commute hS hd'.1 hdD.1 hd'.2 hc
  have hu := hσ.u_mem
  have hxj : h.rho ⟨(d * (w ^ (orderOf w / 2)) ^ j)⁻¹ * x,
      hS.le (S.mul_mem (S.inv_mem (S.mul_mem hdD.1 (zpow_mem hu j))) hxS)⟩ = 1 := by
    have : (⟨(d * (w ^ (orderOf w / 2)) ^ j)⁻¹ * x,
        hS.le (S.mul_mem (S.inv_mem (S.mul_mem hdD.1 (zpow_mem hu j))) hxS)⟩ :
          ↥(centralizer ({t} : Set X))) =
        ((⟨d, hdH⟩ : ↥(centralizer ({t} : Set X))) *
          (⟨w ^ (orderOf w / 2), hS.le hu⟩) ^ j)⁻¹ * ⟨x, hxH⟩ := rfl
    rw [this, map_mul, map_inv, map_mul, map_zpow, hσ.rho_u, ← hv, hab, inv_mul_cancel]
  have hk := h.mem_zpowers_of_rho_eq_one hS
    (S.mul_mem (S.inv_mem (S.mul_mem hdD.1 (zpow_mem hu j))) hxS) hxj
  rw [show x = d * (w ^ (orderOf w / 2)) ^ j * ((d * (w ^ (orderOf w / 2)) ^ j)⁻¹ * x) by
    group]
  refine mul_mem (mul_mem ?_ (zpow_mem (subset_closure (by simp)) j)) ?_
  · exact (zpowers_le.mpr (subset_closure (by simp))) hdz
  · exact (zpowers_le.mpr (subset_closure (by simp))) hk

theorem center_T [Finite X] (hσ : Setup42 h hS w z) :
    (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓
        centralizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) =
      closure {t, w ^ (orderOf w / 2), z} := by
  refine le_antisymm (le_trans ?_ hσ.centralizer_D_le) hσ.X_le_center_T
  rintro x ⟨hxT, hxc⟩
  refine ⟨hσ.T_le hxT, mem_centralizer_iff.mpr fun d hd => ?_⟩
  exact mem_centralizer_iff.mp hxc d (mem_sup_left (mem_sup_right hd))

theorem centralizer_D [Finite X] (hσ : Setup42 h hS w z) :
    S ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) = closure {t, w ^ (orderOf w / 2), z} := by
  refine le_antisymm hσ.centralizer_D_le ?_
  intro x hx
  have hx' := hσ.X_le_center_T hx
  refine ⟨hσ.T_le hx'.1, mem_centralizer_iff.mpr fun d hd => ?_⟩
  exact mem_centralizer_iff.mp hx'.2 d (mem_sup_left (mem_sup_right hd))

theorem centralizer_X [Finite X] (hσ : Setup42 h hS w z) :
    S ⊓ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  apply le_antisymm
  · rw [← hσ.centralizer_u]
    refine inf_le_inf_left _ (centralizer_le ?_)
    rw [Set.singleton_subset_iff]
    exact subset_closure (by simp)
  · refine le_inf hσ.T_le (fun g hg => mem_centralizer_iff.mpr fun x hx => ?_)
    exact (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 g hg).symm


theorem w_ne_one [Finite X] (hσ : Setup42 h hS w z) : w ≠ 1 :=
  (h.lemma41_of_lift hS hσ.lift hσ.gen3).1

theorem disj [Finite X] (hσ : Setup42 h hS w z) : (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w = ⊥ :=
  (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.1

theorem orderOf_w_eq [Finite X] (hσ : Setup42 h hS w z) : orderOf w = 2 * (orderOf w / 2) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS.isPGroup ⟨w, hσ.w_mem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hσ.w_ne_one
    · exact hk0
  rw [hk, ← pow_sub_mul_pow 2 hk1, pow_one, Nat.mul_div_cancel _ two_pos, mul_comm]

theorem zpowers_w_le_normalizer [Finite X] (hσ : Setup42 h hS w z) :
    zpowers w ≤ normalizer ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) := by
  have hSN : S ≤ normalizer ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    have key : ∀ g ∈ S, ∀ y ∈ zpowers t ⊔ (S ⊓ L), g * y * g⁻¹ ∈ zpowers t ⊔ (S ⊓ L) := by
      intro g hg y hy
      have hc : (zpowers t ⊔ (S ⊓ L)).map (MulAut.conj g).toMonoidHom ≤
          zpowers t ⊔ (S ⊓ L) := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rw [MonoidHom.map_zpowers, zpowers_le]
          have htc : g * t = t * g := mem_centralizer_singleton_iff.mp (hS.le hg)
          have : (MulAut.conj g).toMonoidHom t = t := by
            simp [MulAut.conj_apply, htc]
          rw [this]
          exact mem_zpowers t
        · rintro _ ⟨d, hd, rfl⟩
          exact hσ.conj_mem_D hg hd
      exact hc ⟨y, hy, rfl⟩
    constructor
    · exact key s hs y
    · intro hy
      have := key s⁻¹ (S.inv_mem hs) _ hy
      rwa [inv_inv, show s⁻¹ * (s * y * s⁻¹) * s = y by group] at this
  exact zpowers_le.mpr (hSN hσ.w_mem)

theorem involution_mem [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hxT : x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hx2 : x ^ 2 = 1) :
    x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) := by
  have hx' : x ∈ ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) * (zpowers w : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hσ.zpowers_w_le_normalizer]
    exact hxT
  obtain ⟨y, hy, _, ⟨j, rfl⟩, rfl⟩ := hx'
  beta_reduce at hx2 ⊢
  have hyN : w ^ j * y * (w ^ j)⁻¹ ∈ zpowers t ⊔ (S ⊓ L) :=
    (mem_normalizer_iff.mp (hσ.zpowers_w_le_normalizer (zpow_mem (mem_zpowers w) j)) y).mp hy
  have hw2' : w ^ (2 * j) ∈ zpowers t ⊔ (S ⊓ L) := by
    have : w ^ (2 * j) = (w ^ j * y * (w ^ j)⁻¹)⁻¹ * y⁻¹ * (y * w ^ j) ^ 2 := by
      rw [two_mul, zpow_add, sq]
      group
    rw [this, hx2, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) (Subgroup.inv_mem _ hy)
  have hw2 : w ^ (2 * j) ∈ (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w :=
    Subgroup.mem_inf.mpr ⟨hw2', zpow_mem (mem_zpowers w) _⟩
  rw [hσ.disj, mem_bot] at hw2
  have hdvd : (orderOf w : ℤ) ∣ 2 * j := orderOf_dvd_iff_zpow_eq_one.mpr hw2
  rw [hσ.orderOf_w_eq, Nat.cast_mul] at hdvd
  obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hdvd
  have hwj : w ^ j = (w ^ (orderOf w / 2)) ^ c := by
    rw [hc, zpow_mul, zpow_natCast]
  rw [hwj]
  exact mul_mem (mem_sup_left hy) (mem_sup_right (zpow_mem (mem_zpowers _) c))

theorem le_X_of_normal [Finite X] (hσ : Setup42 h hS w z) {E : Subgroup X}
    (hET : E ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (hEn : ∀ g ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hzE : z ∉ E) :
    E ≤ closure {t, w ^ (orderOf w / 2), z} ∧ E ≠ closure {t, w ^ (orderOf w / 2), z} := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  have hcE : ⁅E, S ⊓ L⁆ ≤ E := by
    rw [commutator_le]
    intro a ha d hd
    rw [commutatorElement_def, show a * d * a⁻¹ * d⁻¹ = a * (d * a⁻¹ * d⁻¹) by group]
    exact mul_mem ha (hEn d (hDT hd) a⁻¹ (inv_mem ha))
  have hcD : ⁅E, S ⊓ L⁆ ≤ S ⊓ L := by
    rw [commutator_le]
    intro a ha d hd
    rw [commutatorElement_def]
    exact mul_mem (hσ.conj_mem_D (hσ.T_le (hET ha)) hd) (inv_mem hd)
  have hbot : ⁅E, S ⊓ L⁆ = ⊥ := by
    by_contra hne
    refine hzE (hcE (mem_of_normal_ne_bot e hσ.z_order hσ.center_D hcD ?_ hne))
    intro g hg x hx
    have hmap : (⁅E, S ⊓ L⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅E, S ⊓ L⁆ := by
      rw [Subgroup.map_commutator]
      refine commutator_mono ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hEn g (hDT hg) y hy
      · rintro _ ⟨y, hy, rfl⟩
        exact hσ.conj_mem_D hg.1 hy
    exact hmap ⟨x, hx, rfl⟩
  have hEC : E ≤ S ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    intro x hx
    refine ⟨hσ.T_le (hET hx), mem_centralizer_iff.mpr fun d hd => ?_⟩
    have := (commutator_eq_bot_iff_le_centralizer.mp hbot) hx
    exact (mem_centralizer_iff.mp this d hd)
  rw [hσ.centralizer_D] at hEC
  refine ⟨hEC, fun heq => hzE ?_⟩
  rw [heq]
  exact subset_closure (by simp)

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
