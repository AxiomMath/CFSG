module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L62Irred

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

open Matrix

theorem rho_cube {d : Gx} (hd : d ^ 3 = 1) : rho d * (rho d * rho d) = 1 := by
  rw [← pow_three, ← map_pow, hd, map_one]

@[expose] def IsHW (d : Gx) (h : Ex) : Prop :=
  (∀ v, h v ∈ LinearMap.range (epsE d)) ∧ ∀ w ∈ LinearMap.range (epsE d), h w = 0

@[expose] def IsHU (d : Gx) (h : Ex) : Prop :=
  (∀ v, h v ∈ LinearMap.ker (epsE d)) ∧ ∀ u ∈ LinearMap.ker (epsE d), h u = 0

theorem zero_of_kill {d : Gx} (hd : d ^ 3 = 1) {h : Ex}
    (hW : ∀ w ∈ LinearMap.range (epsE d), h w = 0) (hU : ∀ u ∈ LinearMap.ker (epsE d), h u = 0) :
    h = 0 := by
  apply LinearMap.ext
  intro v
  have h1 : epsE d v ∈ LinearMap.range (epsE d) := ⟨v, rfl⟩
  have h2 : v - epsE d v ∈ LinearMap.ker (epsE d) :=
    LinearMap.mem_ker.2 (by rw [map_sub, epsE_eps hd, sub_self])
  calc h v = h (epsE d v) + h (v - epsE d v) := by rw [← map_add]; congr 1; abel
    _ = 0 := by rw [hW _ h1, hU _ h2, add_zero]

theorem zero_of_kill_U {d : Gx} (hd : d ^ 3 = 1)
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2) {u : Vx}
    (hu : u ∈ LinearMap.ker (epsE d)) (hu0 : u ≠ 0) {h : Ex}
    (hW : ∀ w ∈ LinearMap.range (epsE d), h w = 0) (hu1 : h u = 0) (hdu : h (rho d u) = 0) : h = 0 := by
  apply zero_of_kill hd hW
  intro x hx
  obtain ⟨a, b, rfl⟩ := U_span hd hU2 hu hu0 x hx
  rw [map_add, map_smul, map_smul, hu1, hdu, smul_zero, smul_zero, add_zero]

theorem sum_conj_zero {d : Gx} (hd : d ^ 3 = 1) {h : Ex} (hh : IsHW d h) :
    rho d * h * (rho d * rho d) + rho d * rho d * h * rho d + h = 0 := by
  apply LinearMap.ext
  intro v
  have hw : ∀ w ∈ LinearMap.range (epsE d), rho d w = w := fun w hw => (range_eps_iff hd w).1 hw
  have ha : rho d (h (rho d (rho d v))) = h (rho d (rho d v)) := hw _ (hh.1 _)
  have hb : rho d (rho d (h (rho d v))) = h (rho d v) := by
    rw [hw _ (hh.1 _), hw _ (hh.1 _)]
  have hε : h v + h (rho d v) + h (rho d (rho d v)) = 0 := by
    have := hh.2 (epsE d v) ⟨v, rfl⟩
    rw [epsE_apply, map_add, map_add] at this
    exact this
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [ha, hb]
  calc h (rho d (rho d v)) + h (rho d v) + h v = h v + h (rho d v) + h (rho d (rho d v)) := by abel
    _ = 0 := hε

theorem lemmaA (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    (T : Submodule (ZMod 2) Ex) (hT0 : ∀ h ∈ T, IsHW d h)
    (hTI : ∀ i ∈ I, ∀ h ∈ T, rho i * h * rho i⁻¹ ∈ T)
    (hTd1 : ∀ h ∈ T, rho d * h * (rho d * rho d) ∈ T)
    (hTd2 : ∀ h ∈ T, rho d * rho d * h * rho d ∈ T) :
    (∀ h ∈ T, h = 0) ∨ (∀ h : Ex, IsHW d h → h ∈ T) := by
  by_cases hT : ∀ h ∈ T, h = 0
  · exact Or.inl hT
  right
  push Not at hT
  obtain ⟨h0, hh0T, hh0⟩ := hT
  obtain ⟨u1, hu1U, hu1⟩ : ∃ u ∈ LinearMap.ker (epsE d), u ≠ 0 := by
    obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).1 (by rw [hU2]; norm_num)
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  have hdu1 : rho d u1 ∈ LinearMap.ker (epsE d) := by
    rw [LinearMap.mem_ker] at hu1U ⊢; rw [epsE_rho hd, hu1U]
  have triv' : ∀ i ∈ I, rho i u1 = u1 := fun i hi => act_triv_U I eI hc hU2 ⟨i, hi⟩ u1 hu1U
  have hcEx : ∀ i ∈ I, rho i * rho d = rho d * rho i := fun i hi => LinearMap.ext (hc i hi)
  have hwfix : ∀ w ∈ LinearMap.range (epsE d), rho d w = w := fun w hw => (range_eps_iff hd w).1 hw
  have hfinW : Module.finrank (ZMod 2) (LinearMap.range (epsE d)) = 4 := by
    have := finrank_range_add_ker (d := d); omega
  let evT : T →ₗ[ZMod 2] Vx := (LinearMap.applyₗ u1).comp T.subtype
  let Yw : Submodule (ZMod 2) Vx := LinearMap.range evT
  have hYw_mem : ∀ y, y ∈ Yw ↔ ∃ h ∈ T, h u1 = y := by
    intro y; constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩; exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩; exact ⟨⟨h, hh⟩, rfl⟩
  have hYW : Yw ≤ LinearMap.range (epsE d) := by
    rintro _ ⟨⟨h, hh⟩, rfl⟩; exact (hT0 h hh).1 u1
  have hYI : ∀ i ∈ I, ∀ y ∈ Yw, rho i y ∈ Yw := by
    intro i hi y hy
    obtain ⟨h, hh, rfl⟩ := (hYw_mem _).1 hy
    rw [hYw_mem]
    refine ⟨rho i * h * rho i⁻¹, hTI i hi h hh, ?_⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, triv' i⁻¹ (I.inv_mem hi)]
  have hYbot : Yw ≠ ⊥ := by
    intro hbot
    have h1 : h0 u1 ∈ Yw := (hYw_mem _).2 ⟨h0, hh0T, rfl⟩
    rw [hbot, Submodule.mem_bot] at h1
    have h2 : (rho d * rho d * h0 * rho d) u1 ∈ Yw := (hYw_mem _).2 ⟨_, hTd2 h0 hh0T, rfl⟩
    rw [hbot, Submodule.mem_bot] at h2
    simp only [Module.End.mul_apply] at h2
    have hw := (hT0 h0 hh0T).1 (rho d u1)
    have hdu : h0 (rho d u1) = 0 := by
      have e : rho d (rho d (h0 (rho d u1))) = h0 (rho d u1) := by
        rw [hwfix _ hw, hwfix _ hw]
      rw [← e, h2]
    exact hh0 (zero_of_kill_U hd hU2 hu1U hu1 (hT0 h0 hh0T).2 h1 hdu)
  have hYeq : Yw = LinearMap.range (epsE d) := by
    rcases irr_W I eI hd hc hU2 Yw hYW hYI with h | h
    · exact absurd h hYbot
    · exact h
  let Kx : Submodule (ZMod 2) Ex := T ⊓ LinearMap.ker (LinearMap.applyₗ u1)
  let ψ : Ex →ₗ[ZMod 2] Vx := LinearMap.applyₗ (rho d u1)
  let Zx : Submodule (ZMod 2) Vx := LinearMap.range (ψ.comp Kx.subtype)
  have hZW : Zx ≤ LinearMap.range (epsE d) := by
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    exact (hT0 k hk.1).1 _
  have hZI : ∀ i ∈ I, ∀ z ∈ Zx, rho i z ∈ Zx := by
    rintro i hi _ ⟨⟨k, hk⟩, rfl⟩
    have hk1 : k u1 = 0 := LinearMap.mem_ker.1 hk.2
    have hinvd : rho i⁻¹ (rho d u1) = rho d u1 := by
      rw [hc i⁻¹ (I.inv_mem hi), triv' i⁻¹ (I.inv_mem hi)]
    refine ⟨⟨rho i * k * rho i⁻¹, ⟨hTI i hi k hk.1, ?_⟩⟩, ?_⟩
    · show (rho i * k * rho i⁻¹) u1 = 0
      rw [Module.End.mul_apply, Module.End.mul_apply, triv' i⁻¹ (I.inv_mem hi), hk1, map_zero]
    · show (rho i * k * rho i⁻¹) (rho d u1) = rho i (k (rho d u1))
      rw [Module.End.mul_apply, Module.End.mul_apply, hinvd]
  rcases irr_W I eI hd hc hU2 Zx hZW hZI with hZ | hZ
  ·
    exfalso
    have hK0 : ∀ k ∈ Kx, k = 0 := by
      intro k hk
      have hk1 : k u1 = 0 := LinearMap.mem_ker.1 hk.2
      apply zero_of_kill_U hd hU2 hu1U hu1 (hT0 k hk.1).2 hk1
      have hmem : k (rho d u1) ∈ Zx := ⟨⟨k, hk⟩, rfl⟩
      rw [hZ, Submodule.mem_bot] at hmem
      exact hmem
    have hinj : Function.Injective evT := by
      intro a b hab
      have hk : (a : Ex) - b ∈ Kx := by
        refine ⟨T.sub_mem a.2 b.2, LinearMap.mem_ker.2 ?_⟩
        show ((a : Ex) - b) u1 = 0
        rw [LinearMap.sub_apply]; exact sub_eq_zero.2 hab
      exact Subtype.ext (sub_eq_zero.1 (hK0 _ hk))
    have hfinT : Module.finrank (ZMod 2) T = 4 := by
      rw [← LinearMap.finrank_range_of_inj hinj]
      show Module.finrank (ZMod 2) Yw = 4
      rw [hYeq, hfinW]
    haveI : Finite Ex := finite_end Vx
    have hδ3 := rho_cube hd
    let RT : Module.End (ZMod 2) T :=
      { toFun := fun h => ⟨rho d * h * (rho d * rho d), hTd1 h h.2⟩
        map_add' := fun a b => Subtype.ext (by simp [mul_add, add_mul])
        map_smul' := fun c a => Subtype.ext (by simp [mul_smul_comm, smul_mul_assoc]) }
    let conjT : I →* Module.End (ZMod 2) T :=
      { toFun := fun i =>
          { toFun := fun h => ⟨rho (i : Gx) * h * rho (i : Gx)⁻¹, hTI (i : Gx) i.2 h h.2⟩
            map_add' := fun a b => Subtype.ext (by simp [mul_add, add_mul])
            map_smul' := fun c a => Subtype.ext (by simp [mul_smul_comm, smul_mul_assoc]) }
        map_one' := LinearMap.ext fun h => Subtype.ext (by simp)
        map_mul' := fun i j => LinearMap.ext fun h => Subtype.ext (by
          simp [mul_assoc, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]) }
    have hcomm : ∀ (i : I) (x : T), conjT i (RT x) = RT (conjT i x) := by
      intro i x
      apply Subtype.ext
      show rho (i : Gx) * (rho d * x * (rho d * rho d)) * rho (i : Gx)⁻¹ =
        rho d * (rho (i : Gx) * x * rho (i : Gx)⁻¹) * (rho d * rho d)
      have hA : rho (i : Gx) * rho d = rho d * rho (i : Gx) := hcEx i i.2
      have hB : rho (i : Gx)⁻¹ * rho d = rho d * rho (i : Gx)⁻¹ := hcEx _ (I.inv_mem i.2)
      have hδδb : rho d * rho d * rho (i : Gx)⁻¹ = rho (i : Gx)⁻¹ * (rho d * rho d) := by
        rw [mul_assoc, ← hB, ← mul_assoc, ← hB, mul_assoc]
      calc rho (i : Gx) * (rho d * x * (rho d * rho d)) * rho (i : Gx)⁻¹
          = (rho (i : Gx) * rho d) * x * ((rho d * rho d) * rho (i : Gx)⁻¹) := by simp only [mul_assoc]
        _ = (rho d * rho (i : Gx)) * x * (rho (i : Gx)⁻¹ * (rho d * rho d)) := by rw [hA, hδδb]
        _ = rho d * (rho (i : Gx) * x * rho (i : Gx)⁻¹) * (rho d * rho d) := by simp only [mul_assoc]
    have hR : ∀ x : T, RT (RT x) + RT x + x = 0 := by
      intro x
      apply Subtype.ext
      have hsum := sum_conj_zero hd (hT0 x.1 x.2)
      have hRR : rho d * (rho d * x.1 * (rho d * rho d)) * (rho d * rho d) =
          rho d * rho d * x.1 * rho d := by
        calc rho d * (rho d * x.1 * (rho d * rho d)) * (rho d * rho d)
            = rho d * rho d * x.1 * (rho d * rho d * rho d * rho d) := by simp only [mul_assoc]
          _ = rho d * rho d * x.1 * rho d := by
            rw [show rho d * rho d * rho d * rho d = rho d * (rho d * (rho d * rho d)) by
              simp only [mul_assoc], hδ3, mul_one]
      show rho d * (rho d * x.1 * (rho d * rho d)) * (rho d * rho d) +
        rho d * x.1 * (rho d * rho d) + x.1 = 0
      rw [hRR]
      calc rho d * rho d * x.1 * rho d + rho d * x.1 * (rho d * rho d) + x.1
          = rho d * x.1 * (rho d * rho d) + rho d * rho d * x.1 * rho d + x.1 := by abel
        _ = 0 := hsum
    have htriv : ∀ i : I, conjT i = 1 := fun i => hom_trivial_comm (Q := ↥T) I eI hfinT conjT RT hR hcomm i
    have hinvmul : ∀ g : Gx, rho g⁻¹ * rho g = 1 := fun g => by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hcom0 : ∀ i ∈ I, rho i * h0 = h0 * rho i := by
      intro i hi
      have h1 : rho i * h0 * rho i⁻¹ = h0 :=
        congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) T => f ⟨h0, hh0T⟩) (htriv ⟨i, hi⟩))
      have h2 : rho i * h0 * rho i⁻¹ * rho i = h0 * rho i := by rw [h1]
      rwa [mul_assoc, hinvmul, mul_one] at h2
    have hMW' : LinearMap.range h0 ≤ LinearMap.range (epsE d) := by
      rintro _ ⟨v, rfl⟩
      exact (hT0 h0 hh0T).1 v
    have hM' : ∀ i ∈ I, ∀ m ∈ LinearMap.range h0, rho i m ∈ LinearMap.range h0 := by
      intro i hi _ hm
      obtain ⟨v, rfl⟩ := hm
      refine ⟨rho i v, ?_⟩
      have := congrArg (fun f : Ex => f v) (hcom0 i hi)
      simpa [Module.End.mul_apply] using this.symm
    have hRan : LinearMap.range h0 = LinearMap.range (epsE d) := by
      rcases irr_W I eI hd hc hU2 (LinearMap.range h0) hMW' hM' with h | h
      · exfalso; exact hh0 (LinearMap.range_eq_bot.1 h)
      · exact h
    have hWsub : LinearMap.range (epsE d) ≤
        LinearMap.range (h0.comp (LinearMap.ker (epsE d)).subtype) := by
      rintro _ ⟨v, rfl⟩
      have hv : epsE d v ∈ LinearMap.range h0 := by rw [hRan]; exact ⟨v, rfl⟩
      obtain ⟨x, hx⟩ := hv
      refine ⟨⟨x - epsE d x, LinearMap.mem_ker.2 (by rw [map_sub, epsE_eps hd, sub_self])⟩, ?_⟩
      show h0 (x - epsE d x) = epsE d v
      rw [map_sub, (hT0 h0 hh0T).2 (epsE d x) ⟨x, rfl⟩, sub_zero, hx]
    have h1 := Submodule.finrank_mono hWsub
    have h2 := LinearMap.finrank_range_le (h0.comp (LinearMap.ker (epsE d)).subtype)
    omega
  ·
    intro k hk
    have hku : k u1 ∈ Yw := by rw [hYeq]; exact hk.1 u1
    obtain ⟨t, htT, htu⟩ := (hYw_mem _).1 hku
    have hkt : (k - t) (rho d u1) ∈ Zx := by
      rw [hZ]
      refine Submodule.sub_mem _ (hk.1 _) ?_
      exact (hT0 t htT).1 _
    obtain ⟨⟨s, hsK⟩, hs⟩ := LinearMap.mem_range.1 hkt
    have hsu : s u1 = 0 := LinearMap.mem_ker.1 hsK.2
    have hr : k - t - s = 0 := by
      apply zero_of_kill_U hd hU2 hu1U hu1
      · intro w hw
        rw [LinearMap.sub_apply, LinearMap.sub_apply, hk.2 w hw, (hT0 t htT).2 w hw, (hT0 s hsK.1).2 w hw]
        simp
      · rw [LinearMap.sub_apply, LinearMap.sub_apply, htu, hsu, sub_self, sub_zero]
      · have hs' : s (rho d u1) = (k - t) (rho d u1) := hs
        rw [LinearMap.sub_apply, hs', sub_self]
    have hkts : k = t + s := by
      rw [← sub_eq_zero]
      rw [← hr]; abel
    rw [hkts]
    exact T.add_mem htT hsK.1

theorem IsHW_zero (d : Gx) : IsHW d 0 := ⟨fun v => by simp, fun w _ => by simp⟩
theorem IsHW_add {d : Gx} {h k : Ex} (hh : IsHW d h) (hk : IsHW d k) : IsHW d (h + k) :=
  ⟨fun v => Submodule.add_mem _ (hh.1 v) (hk.1 v), fun w hw => by
    rw [LinearMap.add_apply, hh.2 w hw, hk.2 w hw, add_zero]⟩
theorem IsHW_smul {d : Gx} (c : ZMod 2) {h : Ex} (hh : IsHW d h) : IsHW d (c • h) :=
  ⟨fun v => Submodule.smul_mem _ c (hh.1 v), fun w hw => by
    rw [LinearMap.smul_apply, hh.2 w hw, smul_zero]⟩
theorem IsHU_zero (d : Gx) : IsHU d 0 := ⟨fun v => by simp, fun w _ => by simp⟩
theorem IsHU_add {d : Gx} {h k : Ex} (hh : IsHU d h) (hk : IsHU d k) : IsHU d (h + k) :=
  ⟨fun v => Submodule.add_mem _ (hh.1 v) (hk.1 v), fun w hw => by
    rw [LinearMap.add_apply, hh.2 w hw, hk.2 w hw, add_zero]⟩
theorem IsHU_smul {d : Gx} (c : ZMod 2) {h : Ex} (hh : IsHU d h) : IsHU d (c • h) :=
  ⟨fun v => Submodule.smul_mem _ c (hh.1 v), fun w hw => by
    rw [LinearMap.smul_apply, hh.2 w hw, smul_zero]⟩

def HWs (d : Gx) : Submodule (ZMod 2) Ex where
  carrier := {h | IsHW d h}
  add_mem' := fun hh hk => IsHW_add hh hk
  zero_mem' := IsHW_zero d
  smul_mem' := fun c _ hh => IsHW_smul c hh
def HUs (d : Gx) : Submodule (ZMod 2) Ex where
  carrier := {h | IsHU d h}
  add_mem' := fun hh hk => IsHU_add hh hk
  zero_mem' := IsHU_zero d
  smul_mem' := fun c _ hh => IsHU_smul c hh

noncomputable def pairB (d : Gx) : HWs d →ₗ[ZMod 2] HUs d →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun k h => LinearMap.trace (ZMod 2) Vx ((k : Ex) * (h : Ex)))
    (fun a b h => by simp [add_mul, map_add]) (fun c a h => by simp [smul_mul_assoc, map_smul])
    (fun k h1 h2 => by simp [mul_add, map_add]) (fun c k h => by simp [mul_smul_comm, map_smul])

theorem pair_U_nondeg {d : Gx} (hd : d ^ 3 = 1) {k : Ex} (hk : IsHW d k) (hk0 : k ≠ 0) :
    ∃ h : Ex, IsHU d h ∧ LinearMap.trace (ZMod 2) Vx (k * h) ≠ 0 := by
  obtain ⟨u, hu, hku⟩ : ∃ u ∈ LinearMap.ker (epsE d), k u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk0 (zero_of_kill hd hk.2 hcon)
  have hy : k u ∈ LinearMap.range (epsE d) := hk.1 u
  obtain ⟨μ, hμy, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (R := ZMod 2) (p := ⊥) (x := k u)
    (by rw [Submodule.mem_bot]; exact hku) inferInstance
  have hεy : epsE d (k u) = k u := by
    obtain ⟨x, hx⟩ := hy
    rw [← hx, epsE_eps hd]
  have hkh : k * (μ.comp (epsE d)).smulRight u = (μ.comp (epsE d)).smulRight (k u) := by
    apply LinearMap.ext; intro v
    show k ((μ.comp (epsE d)) v • u) = (μ.comp (epsE d)) v • k u
    rw [map_smul]
  refine ⟨(μ.comp (epsE d)).smulRight u, ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩
  · show (μ.comp (epsE d)) v • u ∈ LinearMap.ker (epsE d)
    exact Submodule.smul_mem _ _ hu
  · show (μ.comp (epsE d)) w • u = 0
    rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hw, map_zero, zero_smul]
  · rw [hkh, LinearMap.trace_smulRight]
    show μ (epsE d (k u)) ≠ 0
    rw [hεy]; exact hμy

theorem pair_W_nondeg {d : Gx} (hd : d ^ 3 = 1) {h : Ex} (hh : IsHU d h) (hh0 : h ≠ 0) :
    ∃ k : Ex, IsHW d k ∧ LinearMap.trace (ZMod 2) Vx (k * h) ≠ 0 := by
  obtain ⟨w, hw, hhw⟩ : ∃ w ∈ LinearMap.range (epsE d), h w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hh0 (zero_of_kill hd hcon hh.2)
  obtain ⟨μ, hμx, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (R := ZMod 2) (p := ⊥) (x := h w)
    (by rw [Submodule.mem_bot]; exact hhw) inferInstance
  set lam : Vx →ₗ[ZMod 2] ZMod 2 := μ.comp ((LinearMap.id : Vx →ₗ[ZMod 2] Vx) - epsE d) with hlam
  have hlamW : ∀ w' ∈ LinearMap.range (epsE d), lam w' = 0 := by
    intro w' hw'
    obtain ⟨x, rfl⟩ := hw'
    rw [hlam, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, epsE_eps hd, sub_self, map_zero]
  have hlamU : ∀ x ∈ LinearMap.ker (epsE d), lam x = μ x := by
    intro x hx
    rw [hlam, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.mem_ker.1 hx,
      sub_zero]
  have hhwU : epsE d (h w) = 0 := LinearMap.mem_ker.1 (hh.1 w)
  have hkh : lam.smulRight w * h = (lam.comp h).smulRight w := by
    apply LinearMap.ext; intro v
    show (lam.smulRight w) (h v) = (lam.comp h) v • w
    rfl
  refine ⟨lam.smulRight w, ⟨fun v => Submodule.smul_mem _ _ hw, fun w' hw' => ?_⟩, ?_⟩
  · show lam w' • w = 0
    rw [hlamW w' hw', zero_smul]
  · rw [hkh, LinearMap.trace_smulRight]
    show lam (h w) ≠ 0
    rw [hlamU _ (hh.1 w)]
    exact hμx

theorem finrank_dual_F2 (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M] :
    Module.finrank (ZMod 2) (M →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) M := by
  rw [Module.finrank_linearMap, Module.finrank_self, mul_one]

theorem pairing_surj {d : Gx} (hd : d ^ 3 = 1) (f : HUs d →ₗ[ZMod 2] ZMod 2) :
    ∃ k : HWs d, pairB d k = f := by
  have hinj1 : Function.Injective (pairB d) := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hk0
    obtain ⟨h, hh, hne⟩ := pair_U_nondeg hd k.2 (fun h => hk0 (Subtype.ext h))
    apply hne
    have := congrArg (fun g => g ⟨h, hh⟩) hk
    simpa [pairB] using this
  have hinj2 : Function.Injective (LinearMap.flip (pairB d)) := by
    rw [injective_iff_map_eq_zero]
    intro h hh0
    by_contra hh
    obtain ⟨k, hk, hne⟩ := pair_W_nondeg hd h.2 (fun h => hh (Subtype.ext h))
    apply hne
    have := congrArg (fun g => g ⟨k, hk⟩) hh0
    simpa [pairB] using this
  have hle1 : Module.finrank (ZMod 2) (HWs d) ≤ Module.finrank (ZMod 2) (HUs d →ₗ[ZMod 2] ZMod 2) :=
    LinearMap.finrank_le_finrank_of_injective hinj1
  have hle2 : Module.finrank (ZMod 2) (HUs d) ≤ Module.finrank (ZMod 2) (HWs d →ₗ[ZMod 2] ZMod 2) :=
    LinearMap.finrank_le_finrank_of_injective hinj2
  have hdual1 := finrank_dual_F2 (HUs d)
  have hdual2 := finrank_dual_F2 (HWs d)
  have heq : Module.finrank (ZMod 2) (HWs d) = Module.finrank (ZMod 2) (HUs d →ₗ[ZMod 2] ZMod 2) := by
    omega
  have hrk : Module.finrank (ZMod 2) (LinearMap.range (pairB d)) = Module.finrank (ZMod 2) (HWs d) :=
    LinearMap.finrank_range_of_inj hinj1
  have hrange : LinearMap.range (pairB d) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrk]
    omega
  have hsurj : Function.Surjective (pairB d) := by
    intro f
    have hf : f ∈ LinearMap.range (pairB d) := by rw [hrange]; exact Submodule.mem_top
    exact LinearMap.mem_range.1 hf
  exact hsurj f

theorem lemmaB (I : Subgroup Gx) (eI : I ≃* alternatingGroup (Fin 7)) {d : Gx} (hd : d ^ 3 = 1)
    (hc : ∀ i ∈ I, ∀ v, rho i (rho d v) = rho d (rho i v))
    (hU2 : Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 2)
    (T : Submodule (ZMod 2) Ex) (hT0 : ∀ h ∈ T, IsHU d h)
    (hTI : ∀ i ∈ I, ∀ h ∈ T, rho i * h * rho i⁻¹ ∈ T)
    (hTd1 : ∀ h ∈ T, rho d * h * (rho d * rho d) ∈ T)
    (hTd2 : ∀ h ∈ T, rho d * rho d * h * rho d ∈ T) :
    (∀ h ∈ T, h = 0) ∨ (∀ h : Ex, IsHU d h → h ∈ T) := by
  have hwfix : ∀ w ∈ LinearMap.range (epsE d), rho d w = w := fun w hw => (range_eps_iff hd w).1 hw
  have hWd : ∀ x ∈ LinearMap.range (epsE d), rho d x ∈ LinearMap.range (epsE d) := fun x hx => by
    rw [hwfix x hx]; exact hx
  have hWI : ∀ i ∈ I, ∀ w ∈ LinearMap.range (epsE d), rho i w ∈ LinearMap.range (epsE d) := by
    intro i hi w hw
    rw [range_eps_iff hd] at hw ⊢
    rw [← hc i hi w, hw]
  let Tp : Submodule (ZMod 2) Ex :=
    { carrier := {k | IsHW d k ∧ ∀ h ∈ T, LinearMap.trace (ZMod 2) Vx (k * h) = 0}
      add_mem' := fun {a b} ha hb => ⟨IsHW_add ha.1 hb.1, fun h hh => by
        rw [add_mul, map_add, ha.2 h hh, hb.2 h hh, add_zero]⟩
      zero_mem' := ⟨IsHW_zero d, fun h _ => by simp⟩
      smul_mem' := fun c a ha => ⟨IsHW_smul c ha.1, fun h hh => by
        rw [smul_mul_assoc, map_smul, ha.2 h hh, smul_zero]⟩ }
  have hTpI : ∀ i ∈ I, ∀ k ∈ Tp, rho i * k * rho i⁻¹ ∈ Tp := by
    intro i hi k hk
    refine ⟨⟨fun v => ?_, fun w hw => ?_⟩, fun h hh => ?_⟩
    · show rho i (k (rho i⁻¹ v)) ∈ LinearMap.range (epsE d)
      exact hWI i hi _ (hk.1.1 _)
    · show rho i (k (rho i⁻¹ w)) = 0
      rw [hk.1.2 _ (hWI i⁻¹ (I.inv_mem hi) w hw), map_zero]
    · have hmem := hk.2 (rho i⁻¹ * h * rho i⁻¹⁻¹) (hTI i⁻¹ (I.inv_mem hi) h hh)
      rw [inv_inv] at hmem
      calc LinearMap.trace (ZMod 2) Vx (rho i * k * rho i⁻¹ * h)
          = LinearMap.trace (ZMod 2) Vx (rho i * (k * rho i⁻¹ * h)) := by simp only [mul_assoc]
        _ = LinearMap.trace (ZMod 2) Vx ((k * rho i⁻¹ * h) * rho i) := LinearMap.trace_mul_comm (ZMod 2) _ _
        _ = LinearMap.trace (ZMod 2) Vx (k * (rho i⁻¹ * h * rho i)) := by simp only [mul_assoc]
        _ = 0 := hmem
  have hTpd1 : ∀ k ∈ Tp, rho d * k * (rho d * rho d) ∈ Tp := by
    intro k hk
    refine ⟨⟨fun v => ?_, fun w hw => ?_⟩, fun h hh => ?_⟩
    · show rho d (k (rho d (rho d v))) ∈ LinearMap.range (epsE d)
      exact hWd _ (hk.1.1 _)
    · have h2 : rho d (rho d w) = w := by rw [hwfix w hw, hwfix w hw]
      show rho d (k (rho d (rho d w))) = 0
      rw [h2, hk.1.2 w hw, map_zero]
    · have hmem := hk.2 (rho d * rho d * h * rho d) (hTd2 h hh)
      calc LinearMap.trace (ZMod 2) Vx (rho d * k * (rho d * rho d) * h)
          = LinearMap.trace (ZMod 2) Vx (rho d * (k * (rho d * rho d) * h)) := by simp only [mul_assoc]
        _ = LinearMap.trace (ZMod 2) Vx ((k * (rho d * rho d) * h) * rho d) :=
            LinearMap.trace_mul_comm (ZMod 2) _ _
        _ = LinearMap.trace (ZMod 2) Vx (k * (rho d * rho d * h * rho d)) := by simp only [mul_assoc]
        _ = 0 := hmem
  have hTpd2 : ∀ k ∈ Tp, rho d * rho d * k * rho d ∈ Tp := by
    intro k hk
    refine ⟨⟨fun v => ?_, fun w hw => ?_⟩, fun h hh => ?_⟩
    · show rho d (rho d (k (rho d v))) ∈ LinearMap.range (epsE d)
      exact hWd _ (hWd _ (hk.1.1 _))
    · show rho d (rho d (k (rho d w))) = 0
      rw [hwfix w hw, hk.1.2 w hw, map_zero, map_zero]
    · have hmem := hk.2 (rho d * h * (rho d * rho d)) (hTd1 h hh)
      calc LinearMap.trace (ZMod 2) Vx (rho d * rho d * k * rho d * h)
          = LinearMap.trace (ZMod 2) Vx ((rho d * rho d) * (k * rho d * h)) := by simp only [mul_assoc]
        _ = LinearMap.trace (ZMod 2) Vx ((k * rho d * h) * (rho d * rho d)) :=
            LinearMap.trace_mul_comm (ZMod 2) _ _
        _ = LinearMap.trace (ZMod 2) Vx (k * (rho d * h * (rho d * rho d))) := by simp only [mul_assoc]
        _ = 0 := hmem
  have hTp := lemmaA I eI hd hc hU2 Tp (fun k hk => hk.1) hTpI hTpd1 hTpd2
  by_cases hall : ∀ k : Ex, IsHW d k → k ∈ Tp
  · left
    intro h hh
    by_contra hne
    obtain ⟨k, hk, hkh⟩ := pair_W_nondeg hd (hT0 h hh) hne
    exact hkh ((hall k hk).2 h hh)
  · right
    have hTp0 : ∀ k ∈ Tp, k = 0 := hTp.resolve_right hall
    intro h0 hh0
    by_contra hnot
    let HUT : Submodule (ZMod 2) (HUs d) := T.comap (HUs d).subtype
    have hnot' : (⟨h0, hh0⟩ : HUs d) ∉ HUT := hnot
    obtain ⟨f, hf0, hfT⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (R := ZMod 2) (p := HUT)
      (x := (⟨h0, hh0⟩ : HUs d)) hnot' inferInstance
    obtain ⟨k, hk⟩ := pairing_surj hd f
    have hkTp : (k : Ex) ∈ Tp := by
      refine ⟨k.2, fun h hh => ?_⟩
      have hmem : (⟨h, hT0 h hh⟩ : HUs d) ∈ HUT := hh
      have hfz : f ⟨h, hT0 h hh⟩ = 0 := by
        have := Submodule.mem_map_of_mem (f := f) hmem
        rw [hfT, Submodule.mem_bot] at this
        exact this
      have := congrArg (fun g => g ⟨h, hT0 h hh⟩) hk
      simp only [pairB, LinearMap.mk₂_apply] at this
      rw [this, hfz]
    have hk0 : (k : Ex) = 0 := hTp0 _ hkTp
    have hf : f = 0 := by
      rw [← hk]
      have : k = 0 := Subtype.ext hk0
      rw [this, map_zero]
    apply hf0
    rw [hf]; rfl

end CFSG.LocalAnalysis.GLTheoremA.CatB.L62F
