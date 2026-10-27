module

public import CFSG.GH74.GLS.SP.Local.SPLL34a
public import CFSG.GH74.GLS.SP.Local.SPLCoprime

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section L34b

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem z_ne_t (hs : SPLSetup D.toSPLNot0) : D.z ≠ D.t := by
  intro h
  exact hs.syl.t_nconj (by rw [← h])

omit [Finite G] in
theorem t_ne_one (hs : SPLSetup D.toSPLNot0) : D.t ≠ 1 := by
  intro h
  have := hs.syl.t_ord
  rw [h, orderOf_one] at this
  omega

theorem comm_zt_eq (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {x : G} (hx : x ∈ D.X) :
    x * (D.z * D.t) * x⁻¹ * (D.z * D.t)⁻¹ = x * D.t * x⁻¹ * D.t⁻¹ := by
  have hxt : x * D.t * x⁻¹ * D.t⁻¹ ∈ D.Y₁ := by
    have := Subgroup.commutator_mem_commutator hx (mem_zpowers D.t)
    rw [← h3.Y₁_eq] at this
    simpa [commutatorElement_def] using this
  have hxz : x * D.z = D.z * x := (z_cen_K D hs x (X_le_K' D hs h3 hx)).symm
  have hzy : D.z * (x * D.t * x⁻¹ * D.t⁻¹) * D.z⁻¹ = x * D.t * x⁻¹ * D.t⁻¹ := by
    have := z_cen_K D hs _ (X_le_K' D hs h3 (h3.Y₁_le hxt))
    rw [this]; group
  calc x * (D.z * D.t) * x⁻¹ * (D.z * D.t)⁻¹ = x * D.z * D.t * x⁻¹ * D.t⁻¹ * D.z⁻¹ := by group
    _ = D.z * x * D.t * x⁻¹ * D.t⁻¹ * D.z⁻¹ := by rw [hxz]
    _ = D.z * (x * D.t * x⁻¹ * D.t⁻¹) * D.z⁻¹ := by group
    _ = x * D.t * x⁻¹ * D.t⁻¹ := hzy

theorem comm_zt_mem_Y₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {x : G} (hx : x ∈ D.X) :
    x * (D.z * D.t) * x⁻¹ * (D.z * D.t)⁻¹ ∈ D.Y₁ := by
  rw [comm_zt_eq D hs h3 hx]
  have := Subgroup.commutator_mem_commutator hx (mem_zpowers D.t)
  rw [← h3.Y₁_eq] at this
  simpa [commutatorElement_def] using this

theorem comm_eq_Y₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2)
    (h3 : SPL3X D) (V : Subgroup G) (hVC : V ≤ D.C₁)
    (hVn : ∀ g ∈ D.C₁, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hVodd : Odd (Nat.card ↥V))
    (hVall : ∀ g ∈ D.C₁, Odd (orderOf g) → g ∈ V) :
    ⁅V, zpowers (D.z * D.t)⁆ = D.Y₁ := by
  classical
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  have hzt : D.z * D.t = D.t * D.z := z_comm_t D hs
  have hzi : D.z⁻¹ = D.z := inv_eq_of_mul_eq_one_right hzz
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  have hVel : ∀ v ∈ V, Odd (orderOf v) := fun v hv =>
    hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard V hv)
  have hzV : ∀ v ∈ V, D.z * v * D.z⁻¹ ∈ V := fun v hv => hVn D.z (z_mem_C₁ D hs h3) v hv
  have htV : ∀ v ∈ V, D.t * v * D.t⁻¹ ∈ V := fun v hv =>
    hVall _ (t_conj_C₁ D hs h3 (hVC hv)) (by rw [orderOf_conj']; exact hVel v hv)
  have hXodd : ∀ x ∈ D.X, Odd (orderOf x) := fun x hx =>
    hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one (X_exp D hs h3 x hx))
  have hXV : D.X ≤ V := fun x hx => hVall x (X_le_C₁ D hs h3 hx) (hXodd x hx)
  have hCz : ∀ v ∈ V, v * D.z = D.z * v → v ∈ D.X := fun v hv hcomm =>
    cen_z_odd_Y₁ D hs h1 h3 (hVC hv) hcomm (hVel v hv)
  have hCt : ∀ v ∈ V, v * D.t = D.t * v → v ∈ D.X := by
    intro v hv hvt
    obtain ⟨w, hw⟩ : ∃ w : G, w = v * (D.z * v⁻¹ * D.z⁻¹) := ⟨_, rfl⟩
    have hwV : w ∈ V := by rw [hw]; exact V.mul_mem hv (hzV v⁻¹ (V.inv_mem hv))
    have hwt : w * D.t = D.t * w := by
      have cv : Commute v D.t := hvt
      have cz : Commute D.z D.t := hzt
      have : Commute (v * (D.z * v⁻¹ * D.z⁻¹)) D.t :=
        cv.mul_left ((cz.mul_left cv.inv_left).mul_left cz.inv_left)
      rw [hw]; exact this
    have hwCt : w ∈ D.Ct := mem_centralizer_singleton_iff.mpr hwt
    have hzw : D.z * w * D.z⁻¹ = w⁻¹ := by
      rw [hw]
      calc D.z * (v * (D.z * v⁻¹ * D.z⁻¹)) * D.z⁻¹
          = D.z * v * D.z * v⁻¹ * (D.z⁻¹ * D.z⁻¹) := by group
        _ = D.z * v * D.z * v⁻¹ := by rw [hzi, hzz]; group
        _ = D.z * v * D.z⁻¹ * v⁻¹ := by rw [hzi]
        _ = (v * (D.z * v⁻¹ * D.z⁻¹))⁻¹ := by group
    have e2 : D.z * w⁻¹ * D.z⁻¹ = w := by rw [← conj_inv, hzw, inv_inv]
    have hwI : ∀ i ∈ D.I, w * i = i * w := by
      intro i hi
      have hj : w * i * w⁻¹ ∈ D.I := I_normalized D hc w hwCt i hi
      have hzi' : D.z * i = i * D.z := z_cen_I D hs hc i hi
      have hzj : D.z * (w * i * w⁻¹) = (w * i * w⁻¹) * D.z := z_cen_I D hs hc _ hj
      have hzi'' : D.z⁻¹ * i * D.z = i := by
        calc D.z⁻¹ * i * D.z = D.z⁻¹ * (i * D.z) := by group
          _ = D.z⁻¹ * (D.z * i) := by rw [hzi']
          _ = i := by group
      have hzj' : D.z * (w * i * w⁻¹) * D.z⁻¹ = w * i * w⁻¹ := by
        calc D.z * (w * i * w⁻¹) * D.z⁻¹ = ((w * i * w⁻¹) * D.z) * D.z⁻¹ := by rw [hzj]
          _ = w * i * w⁻¹ := by group
      have hkey : w⁻¹ * i * w = w * i * w⁻¹ := by
        calc w⁻¹ * i * w = (D.z * w * D.z⁻¹) * i * (D.z * w⁻¹ * D.z⁻¹) := by rw [hzw, e2]
          _ = D.z * (w * (D.z⁻¹ * i * D.z) * w⁻¹) * D.z⁻¹ := by group
          _ = D.z * (w * i * w⁻¹) * D.z⁻¹ := by rw [hzi'']
          _ = w * i * w⁻¹ := hzj'
      have hw2 : w * w * i = i * (w * w) := by
        calc w * w * i = w * (w * i * w⁻¹) * w := by group
          _ = w * (w⁻¹ * i * w) * w := by rw [hkey]
          _ = i * (w * w) := by group
      obtain ⟨m, hm⟩ := hVel w hwV
      have hwm : w ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
      have hwp : (w * w) ^ (m + 1) = w := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hwm, one_mul]
      have hc2 : Commute (w * w) i := hw2
      have := (hc2.pow_left (m + 1)).eq
      rw [hwp] at this
      exact this
    have hwM : w ∈ centralizer (D.I : Set G) ⊓ D.Ct :=
      ⟨mem_centralizer_iff.mpr (fun i hi => (hwI i hi).symm), hwCt⟩
    rw [hc.cen_I] at hwM
    have hwA : w ∈ D.A := odd_mem_A D hs hc hwM (hVel w hwV)
    have hw1 : w = 1 := C_A_Y₁ D hs hc h3 hwA
      (fun y hy => ((mem_C₁ D).mp (hVC hwV) y hy).symm)
    have hvz : v * D.z = D.z * v := by
      have h' : v * (D.z * v⁻¹ * D.z⁻¹) = 1 := by rw [← hw]; exact hw1
      calc v * D.z = (v * (D.z * v⁻¹ * D.z⁻¹)) * (D.z * v) := by group
        _ = D.z * v := by rw [h', one_mul]
    exact hCz v hv hvz
  let W : Subgroup G :=
    { carrier := {v | v ∈ V ∧ v * (D.z * D.t) * v⁻¹ * (D.z * D.t)⁻¹ ∈ D.Y₁}
      mul_mem' := by
        rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
        refine ⟨V.mul_mem haV hbV, ?_⟩
        have e : (a * b) * (D.z * D.t) * (a * b)⁻¹ * (D.z * D.t)⁻¹ =
            a * (b * (D.z * D.t) * b⁻¹ * (D.z * D.t)⁻¹) * a⁻¹ *
              (a * (D.z * D.t) * a⁻¹ * (D.z * D.t)⁻¹) := by group
        rw [e]
        have hac : a * (b * (D.z * D.t) * b⁻¹ * (D.z * D.t)⁻¹) * a⁻¹ =
            b * (D.z * D.t) * b⁻¹ * (D.z * D.t)⁻¹ := by
          have := (mem_C₁ D).mp (hVC haV) _ hb
          rw [← this]; group
        rw [hac]
        exact D.Y₁.mul_mem hb ha
      one_mem' := by
        refine ⟨V.one_mem, ?_⟩
        simp
      inv_mem' := by
        rintro a ⟨haV, ha⟩
        refine ⟨V.inv_mem haV, ?_⟩
        have hci : (a * (D.z * D.t) * a⁻¹ * (D.z * D.t)⁻¹)⁻¹ ∈ D.Y₁ := D.Y₁.inv_mem ha
        have hcomm := (mem_C₁ D).mp (hVC haV) _ hci
        have e : a⁻¹ * (D.z * D.t) * a⁻¹⁻¹ * (D.z * D.t)⁻¹ =
            a⁻¹ * ((a * (D.z * D.t) * a⁻¹ * (D.z * D.t)⁻¹)⁻¹ * a) := by group
        have e2 : a⁻¹ * ((a * (D.z * D.t) * a⁻¹ * (D.z * D.t)⁻¹)⁻¹ * a) =
            (a * (D.z * D.t) * a⁻¹ * (D.z * D.t)⁻¹)⁻¹ := by
          rw [hcomm]; group
        rw [e, e2]; exact hci }
  have hVcl := klein_generation V hVodd D.z D.t hzz htt hzt (z_ne_one D hs) (t_ne_one D hs)
    (z_ne_t D hs) hzV htV
  have hSW : ((V ⊓ centralizer ({D.z} : Set G) : Subgroup G) ∪
      (V ⊓ centralizer ({D.t} : Set G) : Subgroup G) ∪
      (V ⊓ centralizer ({D.z * D.t} : Set G) : Subgroup G) : Set G) ⊆ (W : Set G) := by
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · intro v hv
      have hv' : v ∈ (V ⊓ centralizer ({D.z} : Set G) : Subgroup G) := hv
      have hvz : v * D.z = D.z * v := mem_centralizer_singleton_iff.mp hv'.2
      exact ⟨hv'.1, comm_zt_mem_Y₁ D hs h3 (hCz v hv'.1 hvz)⟩
    · intro v hv
      have hv' : v ∈ (V ⊓ centralizer ({D.t} : Set G) : Subgroup G) := hv
      have hvt : v * D.t = D.t * v := mem_centralizer_singleton_iff.mp hv'.2
      exact ⟨hv'.1, comm_zt_mem_Y₁ D hs h3 (hCt v hv'.1 hvt)⟩
    · intro v hv
      have hv' : v ∈ (V ⊓ centralizer ({D.z * D.t} : Set G) : Subgroup G) := hv
      have hvzt : v * (D.z * D.t) = (D.z * D.t) * v := mem_centralizer_singleton_iff.mp hv'.2
      refine ⟨hv'.1, ?_⟩
      have e : v * (D.z * D.t) * v⁻¹ * (D.z * D.t)⁻¹ = 1 := by rw [hvzt]; group
      rw [e]; exact D.Y₁.one_mem
  have hVW : V ≤ W := hVcl.trans ((Subgroup.closure_le W).mpr hSW)
  have hztsq : (D.z * D.t) * (D.z * D.t) = 1 := by
    calc (D.z * D.t) * (D.z * D.t) = D.z * (D.t * D.z) * D.t := by group
      _ = D.z * (D.z * D.t) * D.t := by rw [← hzt]
      _ = (D.z * D.z) * (D.t * D.t) := by group
      _ = 1 := by rw [hzz, htt]; group
  have hpowe : ∀ (g : G), g * g = 1 → ∀ k : ℤ, g ^ (2 * k) = 1 := by
    intro g hg2 k
    rw [zpow_mul, zpow_two, hg2, one_zpow]
  have hpowo : ∀ (g : G), g * g = 1 → ∀ k : ℤ, g ^ (2 * k + 1) = g := by
    intro g hg2 k
    rw [zpow_add_one, hpowe g hg2 k, one_mul]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    have hP := (hVW hv).2
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · rw [hpowe _ hztsq k]
      simp [commutatorElement_def]
    · rw [hpowo _ hztsq k]
      simpa [commutatorElement_def] using hP
  · rw [h3.Y₁_eq]
    refine Subgroup.commutator_le.mpr (fun x hx g hg => ?_)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · rw [hpowe _ htt k]
      simp [commutatorElement_def]
    · rw [hpowo _ htt k]
      have hx' : ⁅x, D.t⁆ = ⁅x, D.z * D.t⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        exact (comm_zt_eq D hs h3 hx).symm
      rw [hx']
      exact Subgroup.commutator_mem_commutator (hXV hx) (mem_zpowers _)

end L34b

end CFSG.GH74.GLS.SP.Local
