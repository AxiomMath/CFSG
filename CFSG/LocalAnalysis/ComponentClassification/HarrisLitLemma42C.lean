module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42E
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

theorem mem_closure_three {G : Type} [Group G] {a b c x : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hc : orderOf c = 2) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (hx : x ∈ closure {a, b, c}) :
    ∃ a' b' c' : G, (a' = 1 ∨ a' = a) ∧ (b' = 1 ∨ b' = b) ∧ (c' = 1 ∨ c' = c) ∧
      x = a' * b' * c' := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have hcl : closure ({a, b, c} : Set G) = zpowers a ⊔ (zpowers b ⊔ zpowers c) := by
    rw [show ({a, b, c} : Set G) = {a} ∪ ({b} ∪ {c}) by rw [Set.insert_eq, Set.insert_eq],
      Subgroup.closure_union, Subgroup.closure_union, ← zpowers_eq_closure,
      ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hbcN : zpowers b ≤ normalizer (zpowers c : Set G) := fun y hy => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_zpow hbc' i j).symm.eq
  have hbC : b ∈ centralizer (zpowers a : Set G) := mem_centralizer_iff.mpr fun x hx => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    exact (hab'.zpow_left i).eq
  have hcC : c ∈ centralizer (zpowers a : Set G) := mem_centralizer_iff.mpr fun x hx => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    exact (hac'.zpow_left i).eq
  have haN : zpowers a ≤ normalizer ((zpowers b ⊔ zpowers c : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp (sup_le (zpowers_le.mpr hbC) (zpowers_le.mpr hcC))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [hcl] at hx
  have hx' : x ∈ (zpowers a : Set G) * ((zpowers b ⊔ zpowers c : Subgroup G) : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ haN]
    exact hx
  obtain ⟨a', ha', y, hy, rfl⟩ := hx'
  have hy' : y ∈ (zpowers b : Set G) * (zpowers c : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hbcN]
    exact hy
  obtain ⟨b', hb', c', hc', rfl⟩ := hy'
  exact ⟨a', b', c', eq_one_or_eq_of_mem_zpowers ha ha', eq_one_or_eq_of_mem_zpowers hb hb',
    eq_one_or_eq_of_mem_zpowers hc hc', (mul_assoc _ _ _).symm⟩

theorem commutator_self_le {G : Type*} [Group G] (R : Subgroup G) : ⁅R, R⁆ ≤ R := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem mul_mul_inv_mem_innAut {Y : Type} [Group Y] (φ : MulAut Y) {ψ : MulAut Y}
    (hψ : ψ ∈ innAut Y) : φ * ψ * φ⁻¹ ∈ innAut Y := by
  obtain ⟨y, rfl⟩ := hψ
  refine ⟨φ y, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem map_conj_centralizer {G : Type*} [Group G] (g x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer {g * x * g⁻¹} := by
  ext y
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hy]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group

theorem dihedral_sq_mem_center {m : ℕ} (g : DihedralGroup (2 ^ m)) (hg : (g ^ 2) ^ 2 = 1) :
    g ^ 2 ∈ center (DihedralGroup (2 ^ m)) := by
  rcases g with i | j
  · simp only [sq, DihedralGroup.r_mul_r] at hg ⊢
    rw [← DihedralGroup.r_zero] at hg
    exact r_mem_center_of_two_mul (i + i) (by rw [two_mul]; exact DihedralGroup.r.inj hg)
  · simp only [sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]
    exact one_mem _

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem rho_mem_innAut (h : Standing t L p f) {x : X} (hx : x ∈ zpowers t ⊔ L)
    (hxH : x ∈ centralizer ({t} : Set X)) : h.rho ⟨x, hxH⟩ ∈ innAut (Bar L) := by
  have hle : zpowers t ⊔ L ≤
      ((innAut (Bar L)).comap h.rho).map (centralizer ({t} : Set X)).subtype := by
    refine sup_le (zpowers_le.mpr ⟨⟨t, mem_centralizer_singleton_iff.mpr rfl⟩, ?_, rfl⟩)
      fun l hl => ⟨⟨l, h.config.le_centralizer hl⟩, ?_, rfl⟩
    · change h.rho _ ∈ innAut (Bar L)
      rw [h.rho_t]
      exact one_mem _
    · exact ⟨QuotientGroup.mk ⟨l, hl⟩, (h.rho_of_mem ⟨l, hl⟩).symm⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxH⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem orderOf_u [Finite X] (hσ : Setup42 h hS w z) : orderOf (w ^ (orderOf w / 2)) = 2 :=
  (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.1

theorem mem_X [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hx : x ∈ closure {t, w ^ (orderOf w / 2), z}) :
    ∃ a b c : X, (a = 1 ∨ a = t) ∧ (b = 1 ∨ b = w ^ (orderOf w / 2)) ∧ (c = 1 ∨ c = z) ∧
      x = a * b * c :=
  mem_closure_three h.config.orderOf_eq hσ.orderOf_u hσ.z_order
    (mem_centralizer_singleton_iff.mp (hS.le hσ.u_mem)).symm
    (mem_centralizer_singleton_iff.mp (hS.le hσ.z_mem.1)).symm
    (hσ.lift.comm_D z hσ.z_mem).symm hx

theorem rho_u_not_mem_inn [Finite X] (hσ : Setup42 h hS w z) :
    h.rho ⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ ∉ innAut (Bar L) := by
  intro hinn
  have hmem : h.rho ⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ ∈
      zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) ⊓
        ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mpr
      ⟨⟨⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩, hσ.u_mem, rfl⟩, hinn⟩⟩
    rw [hσ.rho_u]
    exact pow_mem (mem_zpowers _) _
  rw [hσ.lift.data.disj, mem_bot] at hmem
  have hu := h.mem_zpowers_of_rho_eq_one hS hσ.u_mem hmem
  have hu' : w ^ (orderOf w / 2) ∈ (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w :=
    Subgroup.mem_inf.mpr ⟨mem_sup_left hu, pow_mem (mem_zpowers w) _⟩
  rw [hσ.disj, mem_bot] at hu'
  have := hσ.orderOf_u
  rw [hu', orderOf_one] at this
  exact absurd this (by norm_num)

theorem mem_T_of_rho_mem [Finite X] (hσ : Setup42 h hS w z) {s : X} (hs : s ∈ S)
    (hρ : h.rho ⟨s, hS.le hs⟩ ∈ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩)) :
    s ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  rw [← hσ.map_rho_T] at hρ
  obtain ⟨y, hyT, hys⟩ := hρ
  have hyS : (y : X) ∈ S := hσ.T_le hyT
  have hk : (y : X)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hyS) hs
  have h1 : h.rho ⟨(y : X)⁻¹ * s, hS.le hk⟩ = 1 := by
    have : (⟨(y : X)⁻¹ * s, hS.le hk⟩ : ↥(centralizer ({t} : Set X))) =
        y⁻¹ * ⟨s, hS.le hs⟩ := rfl
    rw [this, map_mul, map_inv, hys, inv_mul_cancel]
  have ht := h.mem_zpowers_of_rho_eq_one hS hk h1
  rw [show s = (y : X) * ((y : X)⁻¹ * s) by group]
  exact mul_mem hyT (mem_sup_left (mem_sup_left ht))

theorem coe_symm_r_half [Finite X] (hσ : Setup42 h hS w z) {m : ℕ} (hm : 3 ≤ m)
    (e : ↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) :
    ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥(S ⊓ L)) : X) = z := by
  have hcen : e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) ∈ center ↥(S ⊓ L) := by
    rw [← Subgroup.map_center_eq e.symm]
    refine ⟨_, r_mem_center_of_two_mul _ ?_, rfl⟩
    have : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
        ((2 ^ (m - 1 + 1) : ℕ) : ZMod (2 ^ m)) := by
      push_cast
      ring
    rw [this, Nat.sub_add_cancel (by omega : 1 ≤ m), ZMod.natCast_self]
  have hz' : ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥(S ⊓ L)) : X) ∈
      zpowers z := by
    rw [← hσ.center_D, ← map_subtype_center]
    exact ⟨_, hcen, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hσ.z_order hz' with h1 | h1
  · exfalso
    have h2 : e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff, ← DihedralGroup.r_zero] at h2
    have h3 := DihedralGroup.r.inj h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact h1

theorem conj_u_of_not_mem [Finite X] (hσ : Setup42 h hS w z) {s : X} (hs : s ∈ S)
    (hsT : s ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) :
    s⁻¹ * w ^ (orderOf w / 2) * s = w ^ (orderOf w / 2) * z ∨
      s⁻¹ * w ^ (orderOf w / 2) * s = t * w ^ (orderOf w / 2) * z := by
  have huS := hσ.u_mem
  have hxS : s⁻¹ * w ^ (orderOf w / 2) * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) huS) hs
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have hxC : s⁻¹ * w ^ (orderOf w / 2) * s ∈
      S ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨hxS, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hc := hσ.lift.comm_D _ (hσ.conj_mem_D hs hd)
    calc d * (s⁻¹ * w ^ (orderOf w / 2) * s) =
          s⁻¹ * ((s * d * s⁻¹) * w ^ (orderOf w / 2)) * s := by group
      _ = s⁻¹ * (w ^ (orderOf w / 2) * (s * d * s⁻¹)) * s := by rw [hc]
      _ = s⁻¹ * w ^ (orderOf w / 2) * s * d := by group
  rw [hσ.centralizer_D] at hxC
  obtain ⟨a, b, c, ha, hb, hc, hx⟩ := hσ.mem_X hxC
  have hρx : h.rho ⟨s⁻¹ * w ^ (orderOf w / 2) * s, hS.le hxS⟩ =
      (h.rho ⟨s, hS.le hs⟩)⁻¹ * h.rho ⟨w ^ (orderOf w / 2), hS.le huS⟩ *
        h.rho ⟨s, hS.le hs⟩ := by
    have : (⟨s⁻¹ * w ^ (orderOf w / 2) * s, hS.le hxS⟩ : ↥(centralizer ({t} : Set X))) =
        (⟨s, hS.le hs⟩)⁻¹ * ⟨w ^ (orderOf w / 2), hS.le huS⟩ * ⟨s, hS.le hs⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hnotL : s⁻¹ * w ^ (orderOf w / 2) * s ∉ zpowers t ⊔ L := by
    intro hxL
    apply hσ.rho_u_not_mem_inn
    have := mul_mul_inv_mem_innAut (h.rho ⟨s, hS.le hs⟩) (h.rho_mem_innAut hxL (hS.le hxS))
    rw [hρx] at this
    simpa [mul_assoc] using this
  have htL : t ∈ zpowers t ⊔ L := mem_sup_left (mem_zpowers t)
  have hzL : z ∈ zpowers t ⊔ L := mem_sup_right hσ.z_mem.2
  rcases hb with hb | hb <;> rcases ha with ha | ha <;> rcases hc with hc | hc <;>
    rw [ha, hb, hc] at hx
  · exact (hnotL (by rw [hx, mul_one, mul_one]; exact one_mem _)).elim
  · exact (hnotL (by rw [hx, one_mul, one_mul]; exact hzL)).elim
  · exact (hnotL (by rw [hx, mul_one, mul_one]; exact htL)).elim
  · exact (hnotL (by rw [hx, mul_one]; exact mul_mem htL hzL)).elim
  ·
    exfalso
    apply hsT
    rw [← hσ.centralizer_u]
    refine Subgroup.mem_inf.mpr ⟨hs, mem_centralizer_singleton_iff.mpr ?_⟩
    simp only [one_mul, mul_one] at hx
    calc s * w ^ (orderOf w / 2) = s * (s⁻¹ * w ^ (orderOf w / 2) * s) := by rw [hx]
      _ = w ^ (orderOf w / 2) * s := by group
  · left
    simpa using hx
  ·
    exfalso
    have hρ1 : h.rho ⟨s⁻¹ * w ^ (orderOf w / 2) * s, hS.le hxS⟩ =
        h.rho ⟨w ^ (orderOf w / 2), hS.le huS⟩ := by
      have : (⟨s⁻¹ * w ^ (orderOf w / 2) * s, hS.le hxS⟩ : ↥(centralizer ({t} : Set X))) =
          ⟨t, htH⟩ * ⟨w ^ (orderOf w / 2), hS.le huS⟩ * 1 := Subtype.ext hx
      rw [this, mul_one, map_mul, h.rho_t, one_mul]
    have h2 := hρx.symm.trans hρ1
    have hcomm : h.rho ⟨s, hS.le hs⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        centralizer {h.rho ⟨w, hS.le hσ.lift.mem⟩ ^
          (orderOf (h.rho ⟨w, hS.le hσ.lift.mem⟩) / 2)} := by
      refine Subgroup.mem_inf.mpr ⟨⟨⟨s, hS.le hs⟩, hs, rfl⟩,
        mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hσ.rho_u]
      calc h.rho ⟨s, hS.le hs⟩ * h.rho ⟨w ^ (orderOf w / 2), hS.le huS⟩ =
            h.rho ⟨s, hS.le hs⟩ * ((h.rho ⟨s, hS.le hs⟩)⁻¹ *
              h.rho ⟨w ^ (orderOf w / 2), hS.le huS⟩ * h.rho ⟨s, hS.le hs⟩) := by rw [h2]
        _ = h.rho ⟨w ^ (orderOf w / 2), hS.le huS⟩ * h.rho ⟨s, hS.le hs⟩ := by group
    rw [hσ.lift.data.centralizer_v₀] at hcomm
    exact hsT (hσ.mem_T_of_rho_mem hs hcomm)
  · right
    exact hx

theorem exists_of_mem_commutator [Finite X] (hσ : Setup42 h hS w z) {y : X}
    (hy : y ∈ ⁅S, S⁆) : ∃ d ∈ S ⊓ L, ∃ k : ℤ, y = d * t ^ k := by
  have hdata := hσ.lift.data
  have hR := h.map_rho_inf_innAut hS
  have hcR : (⁅(S.subgroupOf (centralizer ({t} : Set X))).map h.rho,
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho⁆ : Subgroup (MulAut (Bar L))) ≤
        (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
    by_cases heq : (S.subgroupOf (centralizer ({t} : Set X))).map h.rho =
        ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
          zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩)
    · have hd := hdata.derived
      rw [← heq] at hd
      rw [hd]
      exact commutator_self_le _
    · exact (hdata.derived_cyclic_of_ne heq).2.1
  have hle : ⁅S, S⁆ ≤ (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)).comap h.rho).map (centralizer ({t} : Set X)).subtype := by
    rw [commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ S := commutator_self_le S (commutator_mem_commutator ha hb)
    refine ⟨⟨⁅a, b⁆, hS.le hab⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have : (⟨⁅a, b⁆, hS.le hab⟩ : ↥(centralizer ({t} : Set X))) =
        ⁅(⟨a, hS.le ha⟩ : ↥(centralizer ({t} : Set X))), ⟨b, hS.le hb⟩⁆ := rfl
    rw [this, map_commutatorElement]
    exact hcR (commutator_mem_commutator ⟨⟨a, hS.le ha⟩, ha, rfl⟩ ⟨⟨b, hS.le hb⟩, hb, rfl⟩)
  have hyS : y ∈ S := commutator_self_le S hy
  obtain ⟨y', hy', rfl⟩ := hle hy
  have hy'' : h.rho y' ∈ ((S ⊓ L).subgroupOf (centralizer ({t} : Set X))).map h.rho := by
    rw [← hR]
    exact hy'
  obtain ⟨d, hd, hdy⟩ := hy''
  have hdD : (d : X) ∈ S ⊓ L := hd
  have hk : (d : X)⁻¹ * y' ∈ S := S.mul_mem (S.inv_mem hdD.1) hyS
  have h1 : h.rho ⟨(d : X)⁻¹ * y', hS.le hk⟩ = 1 := by
    have : (⟨(d : X)⁻¹ * y', hS.le hk⟩ : ↥(centralizer ({t} : Set X))) = d⁻¹ * y' := rfl
    rw [this, map_mul, map_inv, hdy, inv_mul_cancel]
  obtain ⟨k, hk'⟩ := mem_zpowers_iff.mp (h.mem_zpowers_of_rho_eq_one hS hk h1)
  refine ⟨d, hdD, k, ?_⟩
  change (y' : X) = d * t ^ k
  rw [hk']
  group

theorem sq_mem_zpowers [Finite X] (hσ : Setup42 h hS w z) {d : X} (hd : d ∈ S ⊓ L)
    (h4 : (d ^ 2) ^ 2 = 1) : d ^ 2 ∈ zpowers z := by
  obtain ⟨m, -, ⟨e⟩⟩ := hσ.dihedral
  have h4' : ((⟨d, hd⟩ : ↥(S ⊓ L)) ^ 2) ^ 2 = 1 := Subtype.ext (by simp [h4])
  have h1 : (e ⟨d, hd⟩) ^ 2 ∈ center (DihedralGroup (2 ^ m)) :=
    dihedral_sq_mem_center _ (by rw [← map_pow, ← map_pow, h4', map_one])
  have h2 : (⟨d, hd⟩ : ↥(S ⊓ L)) ^ 2 ∈ center ↥(S ⊓ L) := by
    rw [← Subgroup.map_center_eq e.symm]
    exact ⟨_, h1, by simp⟩
  rw [← hσ.center_D, ← map_subtype_center]
  exact ⟨_, h2, rfl⟩

theorem exists_commutator_sq_eq_z [Finite X] (hσ : Setup42 h hS w z) :
    ∃ c ∈ ⁅S ⊓ L, S ⊓ L⁆, c ^ 2 = z := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  set a : ↥(S ⊓ L) := e.symm (DihedralGroup.r ((2 ^ (m - 3) : ℕ) : ZMod (2 ^ m))) with ha
  set b : ↥(S ⊓ L) := e.symm (DihedralGroup.sr 0) with hb
  refine ⟨⁅(a : X), (b : X)⁆, commutator_mem_commutator a.2 b.2, ?_⟩
  have hcomm : (⁅DihedralGroup.r ((2 ^ (m - 3) : ℕ) : ZMod (2 ^ m)), DihedralGroup.sr 0⁆ :
      DihedralGroup (2 ^ m)) = DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) := by
    rw [commutatorElement_def, DihedralGroup.r_mul_sr, DihedralGroup.inv_r,
      DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
    congr 1
    push_cast
    rw [show m - 2 = m - 3 + 1 by omega, pow_succ]
    ring
  have hsq : (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) ^ 2 =
      DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [sq, DihedralGroup.r_mul_r]
    congr 1
    push_cast
    rw [show m - 1 = m - 2 + 1 by omega, pow_succ]
    ring
  have hc : (⁅(a : X), (b : X)⁆ : X) ^ 2 =
      ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : ↥(S ⊓ L)) : X) := by
    rw [← hsq, ← hcomm, map_pow, map_commutatorElement]
    rfl
  rw [hc]
  exact hσ.coe_symm_r_half hm e

theorem conj_z_eq [Finite X] (hσ : Setup42 h hS w z) {P : Subgroup X} (hDP : S ⊓ L ≤ P)
    (hPS : P ≤ S) {n : X} (hn : n ∈ normalizer (P : Set X)) : n * z * n⁻¹ = z := by
  obtain ⟨c, hc, hcz⟩ := hσ.exists_commutator_sq_eq_z
  have hcP : c ∈ ⁅P, P⁆ := commutator_mono hDP hDP hc
  have hmap : (⁅P, P⁆).map (MulAut.conj n).toMonoidHom ≤ ⁅P, P⁆ := by
    rw [Subgroup.map_commutator]
    refine commutator_mono ?_ ?_ <;>
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hn y).mp hy
  have hnc : n * c * n⁻¹ ∈ ⁅S, S⁆ := commutator_mono hPS hPS (hmap ⟨c, hcP, rfl⟩)
  obtain ⟨d, hd, k, hdk⟩ := hσ.exists_of_mem_commutator hnc
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hz2 : z ^ 2 = 1 := by rw [← hσ.z_order, pow_orderOf_eq_one]
  have htd : Commute d (t ^ k) :=
    (show Commute d t from mem_centralizer_singleton_iff.mp (hS.le hd.1)).zpow_right k
  have htk2 : (t ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hsq : (n * c * n⁻¹) ^ 2 = d ^ 2 := by rw [hdk, htd.mul_pow, htk2, mul_one]
  have hnz : (n * c * n⁻¹) ^ 2 = n * z * n⁻¹ := by
    rw [← hcz, sq, sq]
    group
  have hnz2 : (n * z * n⁻¹) ^ 2 = 1 := by
    calc (n * z * n⁻¹) ^ 2 = n * z ^ 2 * n⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hz2]; group
  have h4 : (d ^ 2) ^ 2 = 1 := by rw [← hsq, hnz, hnz2]
  rcases eq_one_or_eq_of_mem_zpowers hσ.z_order (hσ.sq_mem_zpowers hd h4) with h1 | h1
  · exfalso
    rw [← hsq, hnz] at h1
    have hz1 : z = 1 := by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have := hσ.z_order
    rw [hz1, orderOf_one] at this
    exact absurd this (by norm_num)
  · rwa [← hsq, hnz] at h1

theorem conj_t_ne_z [Finite X] (hσ : Setup42 h hS w z) (g : X) : g * t * g⁻¹ ≠ z := by
  intro hg
  have hSz : S ≤ centralizer ({z} : Set X) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hσ.z_comm hs)
  have hcz : (centralizer ({t} : Set X)).map (MulAut.conj g).toMonoidHom =
      centralizer ({z} : Set X) := by
    rw [map_conj_centralizer, hg]
  have hS' : IsSylowOf 2 (S.map (MulAut.conj g).toMonoidHom) (centralizer ({z} : Set X)) := by
    rw [← hcz]
    exact isSylowOf_map _ hS
  have hS'' : IsSylowOf 2 S (centralizer ({z} : Set X)) := by
    refine isSylowOf_of_card hSz ?_
    rw [hS.card_eq, ← hcz, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨c, hcC, hc⟩ := hS''.exists_mem_conj hS'
  have hn : c⁻¹ * g ∈ normalizer (S : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    have key : y ∈ S ↔ g * y * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := by
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y', hy', hyy⟩
        have : y' = y :=
          (MulAut.conj g).injective (by simpa [MulAut.conj_apply] using hyy)
        rwa [← this]
    rw [key, hc, show c⁻¹ * g * y * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * y * g⁻¹) * c by group]
  have hcz' : c * z = z * c := mem_centralizer_singleton_iff.mp hcC
  have hnt : c⁻¹ * g * t * (c⁻¹ * g)⁻¹ = z := by
    calc c⁻¹ * g * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by group
      _ = c⁻¹ * (z * c) := by rw [hg, mul_assoc]
      _ = z := by rw [← hcz', ← mul_assoc, inv_mul_cancel, one_mul]
  have hnz := hσ.conj_z_eq inf_le_left le_rfl hn
  have htz : t = z := by
    have h2 : c⁻¹ * g * t * (c⁻¹ * g)⁻¹ = c⁻¹ * g * z * (c⁻¹ * g)⁻¹ := hnt.trans hnz.symm
    simpa using h2
  exact h.config.not_mem (htz ▸ hσ.z_mem.2)

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
