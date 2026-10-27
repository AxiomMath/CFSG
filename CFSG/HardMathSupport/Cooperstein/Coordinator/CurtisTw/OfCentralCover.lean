module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverLift
public import CFSG.Quasithin.Background.SmithCurtisDatum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Quasithin.SmithCurtis CoxeterSystem

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ}

structure CentralCoverData (D : CurtisDatum G cs p) (π : Ĝ →* G) (p : ℕ) where
  cover : IsCentralCover π p
  nhatW : W → Ĝ
  map_nhatW : ∀ w, π (nhatW w) = D.nW w
  nhatW_one : nhatW 1 = 1
  nhatW_simple_mul : ∀ (w : W) (s : B), cs.length (cs.simple s * w) = cs.length w + 1 →
    nhatW (cs.simple s * w) = nhatW (cs.simple s) * nhatW w
  hcomm : ∀ a ∈ D.H.comap π, ∀ b ∈ D.H.comap π, a * b = b * a

namespace CentralCoverData

variable [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p} {π : Ĝ →* G}
  (C : CentralCoverData D π p)

@[expose] def nhat (s : B) : Ĝ := C.nhatW (cs.simple s)

theorem nW_simple (D : CurtisDatum G cs p) (s : B) : D.nW (cs.simple s) = D.n s := by
  have h : cs.length (cs.simple s * 1) = cs.length 1 + 1 := by
    rw [mul_one, cs.length_simple, cs.length_one]
  rw [← mul_one (cs.simple s), D.nW_simple_mul 1 s h, D.nW_one, mul_one]

theorem hn (s : B) : π (C.nhat s) = D.n s := by
  rw [nhat, C.map_nhatW, nW_simple]

@[expose] def lU : Subgroup Ĝ := pLift C.cover D.U D.isPGroup_U

@[expose] def lL : Subgroup Ĝ := pLift C.cover D.L D.isPGroup_L

@[expose] def lX (s : B) : Subgroup Ĝ := pLift C.cover (D.X s) (D.isPGroup_U.to_le (D.X_le s))

@[expose] def lY (s : B) : Subgroup Ĝ := pLift C.cover (D.Y s) (D.isPGroup_L.to_le (D.Y_le s))

@[expose] def lUs (s : B) : Subgroup Ĝ := pLift C.cover (D.Us s) (D.isPGroup_U.to_le (D.Us_le s))

@[expose] def lQ (s : B) : Subgroup Ĝ := pLift C.cover (D.Q s) (D.isPGroup_L.to_le (D.Q_le s))

theorem mem_lU {x : Ĝ} : x ∈ C.lU ↔ π x ∈ D.U ∧ IsPElt p x := Iff.rfl
theorem mem_lL {x : Ĝ} : x ∈ C.lL ↔ π x ∈ D.L ∧ IsPElt p x := Iff.rfl
theorem mem_lX {s : B} {x : Ĝ} : x ∈ C.lX s ↔ π x ∈ D.X s ∧ IsPElt p x := Iff.rfl
theorem pElt_ne_one {P : Subgroup G} {hP : IsPGroup p P} {x : Ĝ} (hx : x ∈ pLift C.cover P hP)
    (hx1 : x ≠ 1) : π x ≠ 1 := fun h =>
  hx1 (C.cover.eq_one_of_isPElt (MonoidHom.mem_ker.2 h) hx.2)

theorem exists_lift {P : Subgroup G} {hP : IsPGroup p P} {g : G} (hg : g ∈ P) :
    ∃ x ∈ pLift C.cover P hP, π x = g := exists_pLift hg

include C in
theorem exists_lift_H {g : G} (hg : g ∈ D.H) : ∃ x : Ĝ, x ∈ D.H.comap π ∧ π x = g := by
  obtain ⟨x, rfl⟩ := C.cover.surj g
  exact ⟨x, hg, rfl⟩

theorem exists_phiHat (s : B) {x : Ĝ} (hx : x ∈ C.lX s) (hx1 : x ≠ 1) :
    ∃ ĥ ∈ D.H.comap π, π ĥ = D.phi s (π x) ∧ ∃ l ∈ C.lL, ∃ u ∈ C.lU,
      x * C.nhat s = l * ĥ * u := by
  obtain ⟨l', hl', u', hu', e⟩ := D.phi_spec s (π x) hx.1 (C.pElt_ne_one hx hx1)
  obtain ⟨l, hl, rfl⟩ := C.exists_lift (hP := D.isPGroup_L) hl'
  obtain ⟨u, hu, rfl⟩ := C.exists_lift (hP := D.isPGroup_U) hu'
  have hπ : π (l⁻¹ * (x * C.nhat s) * u⁻¹) = D.phi s (π x) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, C.hn, e]
    group
  refine ⟨l⁻¹ * (x * C.nhat s) * u⁻¹, ?_, hπ, l, hl, u, hu, by group⟩
  show π (l⁻¹ * (x * C.nhat s) * u⁻¹) ∈ D.H
  rw [hπ]
  exact D.phi_mem s _ hx.1 (C.pElt_ne_one hx hx1)

theorem exists_psiHat (s : B) {x : Ĝ} (hx : x ∈ C.lX s) (hx1 : x ≠ 1) :
    ∃ ĥ ∈ D.H.comap π, π ĥ = D.psi s (π x) ∧ ∃ a ∈ C.lX s, ∃ u ∈ C.lU,
      C.nhat s * x * C.nhat s = a * C.nhat s * ĥ * u := by
  obtain ⟨a', ha', u', hu', e⟩ := D.psi_spec s (π x) hx.1 (C.pElt_ne_one hx hx1)
  obtain ⟨a, ha, rfl⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.X_le s)) ha'
  obtain ⟨u, hu, rfl⟩ := C.exists_lift (hP := D.isPGroup_U) hu'
  have hπ : π ((a * C.nhat s)⁻¹ * (C.nhat s * x * C.nhat s) * u⁻¹) = D.psi s (π x) := by
    have h1 : π ((a * C.nhat s)⁻¹ * (C.nhat s * x * C.nhat s) * u⁻¹) =
        (π a * D.n s)⁻¹ * (D.n s * π x * D.n s) * (π u)⁻¹ := by
      simp only [map_mul, map_inv, C.hn]
    rw [h1, e]
    group
  refine ⟨(a * C.nhat s)⁻¹ * (C.nhat s * x * C.nhat s) * u⁻¹, ?_, hπ, a, ha, u, hu, by group⟩
  show π ((a * C.nhat s)⁻¹ * (C.nhat s * x * C.nhat s) * u⁻¹) ∈ D.H
  rw [hπ]
  exact D.psi_mem s _ hx.1 (C.pElt_ne_one hx hx1)

open Classical in
@[expose] noncomputable def phiHat (s : B) (x : Ĝ) : Ĝ :=
  if h : x ∈ C.lX s ∧ x ≠ 1 then (C.exists_phiHat s h.1 h.2).choose else 1

open Classical in
@[expose] noncomputable def psiHat (s : B) (x : Ĝ) : Ĝ :=
  if h : x ∈ C.lX s ∧ x ≠ 1 then (C.exists_psiHat s h.1 h.2).choose else 1

theorem natCard_eq_of_bij {S : Subgroup Ĝ} {S' : Subgroup G} (hS : ∀ x ∈ S, π x ∈ S')
    (hsurj : ∀ y ∈ S', ∃ x ∈ S, π x = y) (hinj : ∀ x ∈ S, ∀ y ∈ S, π x = π y → x = y) :
    Nat.card S = Nat.card S' := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : S => (⟨π x, hS x x.2⟩ : S')) ⟨?_, ?_⟩)
  · intro x y hxy
    exact Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))
  · intro y
    obtain ⟨x, hx, hxy⟩ := hsurj y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem natCard_lU : Nat.card C.lU = Nat.card D.U :=
  natCard_eq_of_bij (fun x hx => hx.1)
    (fun y hy => exists_pLift (h := C.cover) (hP := D.isPGroup_U) hy)
    (fun x hx y hy hxy => pLift_inj hx hy hxy)

theorem heckeDeg_lU (g : Ĝ) : heckeDeg C.lU g = heckeDeg D.U (π g) := by
  have : Finite G := Finite.of_surjective π C.cover.surj
  set A : Subgroup Ĝ := C.lU.map (MulAut.conj g).toMonoidHom
  set A' : Subgroup G := D.U.map (MulAut.conj (π g)).toMonoidHom
  have hcard : Nat.card ↥(A ⊓ C.lU) = Nat.card ↥(A' ⊓ D.U) := by
    refine natCard_eq_of_bij (π := π) ?_ ?_ ?_
    · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
      refine ⟨⟨π y, hy.1, ?_⟩, hx.1⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    · intro y ⟨⟨u, hu, hyu⟩, hyU⟩
      obtain ⟨x, hx, hxy⟩ := exists_pLift (h := C.cover) (hP := D.isPGroup_U) hyU
      refine ⟨x, ⟨⟨g⁻¹ * x * g, ⟨?_, hx.2.conj' g⟩, ?_⟩, hx⟩, hxy⟩
      · have : π (g⁻¹ * x * g) = u := by
          rw [map_mul, map_mul, map_inv, hxy, ← hyu]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [this]
        exact hu
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · intro x hx y hy hxy
      exact pLift_inj hx.2 hy.2 hxy
  have h1 := Subgroup.relIndex_mul_card A C.lU
  have h2 := Subgroup.relIndex_mul_card A' D.U
  rw [hcard, natCard_lU] at h1
  have hpos : 0 < Nat.card ↥(A' ⊓ D.U) := Nat.card_pos
  unfold heckeDeg
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

@[expose] noncomputable def datum : CurtisDatum Ĝ cs p where
  U := C.lU
  L := C.lL
  H := D.H.comap π
  X := C.lX
  Y := C.lY
  Us := C.lUs
  Q := C.lQ
  n := C.nhat
  nW := C.nhatW
  phi := C.phiHat
  psi := C.psiHat
  isPGroup_U := pLift_isPGroup _ _
  isPGroup_L := pLift_isPGroup _ _
  U_inf_L := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have h : π x ∈ D.U ⊓ D.L := Subgroup.mem_inf.2 ⟨h1.1, h2.1⟩
    rw [D.U_inf_L, Subgroup.mem_bot] at h
    exact C.cover.eq_one_of_isPElt (MonoidHom.mem_ker.2 h) h1.2
  H_comm := C.hcomm
  H_normU h hh u hu := ⟨by simpa only [map_mul, map_inv] using D.H_normU _ hh _ hu.1, hu.2.conj _⟩
  H_normU' h hh u hu :=
    ⟨by simpa only [map_mul, map_inv] using D.H_normU' _ hh _ hu.1, hu.2.conj' _⟩
  H_normL h hh l hl := ⟨by simpa only [map_mul, map_inv] using D.H_normL _ hh _ hl.1, hl.2.conj _⟩
  H_normX s h hh x hx :=
    ⟨by simpa only [map_mul, map_inv] using D.H_normX s _ hh _ hx.1, hx.2.conj _⟩
  H_normQ s h hh q hq :=
    ⟨by simpa only [map_mul, map_inv] using D.H_normQ s _ hh _ hq.1, hq.2.conj _⟩
  X_le s x hx := ⟨D.X_le s hx.1, hx.2⟩
  X_ne_bot s hbot := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (D.X_ne_bot s)
    obtain ⟨x, hx, hxy⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.X_le s)) hy
    have hx1 : x = 1 := by
      have : x ∈ C.lX s := hx
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have hy0 : y = 1 := by rw [← hxy, hx1, map_one]
    exact hy1 (Subtype.ext hy0)
  U_eq s u hu := by
    obtain ⟨x', hx', v', hv', e⟩ := D.U_eq s (π u) hu.1
    obtain ⟨x, hx, rfl⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.X_le s)) hx'
    obtain ⟨v, hv, rfl⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.Us_le s)) hv'
    refine ⟨x, hx, v, hv, ?_⟩
    have hxU : x ∈ C.lU := ⟨D.X_le s hx.1, hx.2⟩
    have hvU : v ∈ C.lU := ⟨D.Us_le s hv.1, hv.2⟩
    exact pLift_inj hu (mul_mem hxU hvU) (by rw [map_mul]; exact e)
  Us_le s v hv := ⟨D.Us_le s hv.1, hv.2⟩
  X_normUs s x hx v hv :=
    ⟨by simpa only [map_mul, map_inv] using D.X_normUs s _ hx.1 _ hv.1, hv.2.conj _⟩
  n_normUs s v hv :=
    ⟨by simpa only [map_mul, map_inv, C.hn] using D.n_normUs s _ hv.1, hv.2.conj _⟩
  n_normUs' s v hv :=
    ⟨by simpa only [map_mul, map_inv, C.hn] using D.n_normUs' s _ hv.1, hv.2.conj' _⟩
  Y_le s y hy := ⟨D.Y_le s hy.1, hy.2⟩
  Q_le s q hq := ⟨D.Q_le s hq.1, hq.2⟩
  L_le s l hl := by
    have hmapY : (C.lY s).map π = D.Y s := le_antisymm
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.1)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := C.exists_lift (hP := D.isPGroup_L.to_le (D.Y_le s)) hy
        exact ⟨x, hx, rfl⟩)
    have hmapQ : (C.lQ s).map π = D.Q s := le_antisymm
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.1)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := C.exists_lift (hP := D.isPGroup_L.to_le (D.Q_le s)) hy
        exact ⟨x, hx, rfl⟩)
    have h1 : π l ∈ (C.lY s ⊔ C.lQ s).map π := by
      rw [Subgroup.map_sup, hmapY, hmapQ]
      exact D.L_le s hl.1
    obtain ⟨w, hw, hwl⟩ := h1
    have hle : C.lY s ⊔ C.lQ s ≤ C.lL := sup_le
      (fun x (hx : x ∈ C.lY s) => (⟨D.Y_le s hx.1, hx.2⟩ : x ∈ C.lL))
      (fun x (hx : x ∈ C.lQ s) => (⟨D.Q_le s hx.1, hx.2⟩ : x ∈ C.lL))
    have hwL : w ∈ C.lL := hle hw
    have : l = w := pLift_inj hl hwL hwl.symm
    rw [this]
    exact hw
  X_normQ s x hx q hq :=
    ⟨by simpa only [map_mul, map_inv] using D.X_normQ s _ hx.1 _ hq.1, hq.2.conj _⟩
  Y_normQ s y hy q hq :=
    ⟨by simpa only [map_mul, map_inv] using D.Y_normQ s _ hy.1 _ hq.1, hq.2.conj _⟩
  n_normQ s q hq :=
    ⟨by simpa only [map_mul, map_inv, C.hn] using D.n_normQ s _ hq.1, hq.2.conj _⟩
  n_conjX s x hx :=
    ⟨by simpa only [map_mul, map_inv, C.hn] using D.n_conjX s _ hx.1, hx.2.conj _⟩
  n_conjY s y hy :=
    ⟨by simpa only [map_mul, map_inv, C.hn] using D.n_conjY s _ hy.1, hy.2.conj _⟩
  n_sq s := by
    show π (C.nhat s * C.nhat s) ∈ D.H
    rw [map_mul, C.hn]
    exact D.n_sq s
  n_normH s h hh := by
    show π (C.nhat s * h * (C.nhat s)⁻¹) ∈ D.H
    simpa only [map_mul, map_inv, C.hn] using D.n_normH s _ hh
  phi_mem s x hx hx1 := by
    unfold phiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    exact (C.exists_phiHat s hx hx1).choose_spec.1
  psi_mem s x hx hx1 := by
    unfold psiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    exact (C.exists_psiHat s hx hx1).choose_spec.1
  phi_spec s x hx hx1 := by
    unfold phiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    obtain ⟨l, hl, u, hu, e⟩ := (C.exists_phiHat s hx hx1).choose_spec.2.2
    exact ⟨l, hl, u, hu, e⟩
  psi_spec s x hx hx1 := by
    unfold psiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    obtain ⟨a, ha, u, hu, e⟩ := (C.exists_psiHat s hx hx1).choose_spec.2.2
    exact ⟨a, ha, u, hu, e⟩
  bruhatY s y hy hy1 := by
    obtain ⟨h, hh, a, ha, c, hc, e⟩ := D.bruhatY s (π y) hy.1 (C.pElt_ne_one hy hy1)
    obtain ⟨ah, hah, rfl⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.X_le s)) ha
    obtain ⟨ch, hch, rfl⟩ := C.exists_lift (hP := D.isPGroup_U.to_le (D.X_le s)) hc
    obtain ⟨h0, hh0, rfl⟩ := C.exists_lift_H hh
    set z := (ah * (h0 * C.nhat s) * ch)⁻¹ * y with hz_def
    have hz : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz_def]
      simp only [map_mul, map_inv, C.hn]
      rw [e]
      group
    have hzc := C.cover.ker_le hz
    have c1 : ch * z = z * ch := Subgroup.mem_center_iff.1 hzc ch
    have c2 : C.nhat s * z = z * C.nhat s := Subgroup.mem_center_iff.1 hzc _
    refine ⟨h0 * z, ?_, ah, hah, ch, hch, ?_⟩
    · show π (h0 * z) ∈ D.H
      rw [map_mul, MonoidHom.mem_ker.1 hz, mul_one]
      exact hh0
    · have hy' : y = ah * (h0 * C.nhat s) * ch * z := by rw [hz_def]; group
      rw [hy']
      calc ah * (h0 * C.nhat s) * ch * z = ah * h0 * C.nhat s * (ch * z) := by group
        _ = ah * h0 * C.nhat s * (z * ch) := by rw [c1]
        _ = ah * h0 * (C.nhat s * z) * ch := by group
        _ = ah * h0 * (z * C.nhat s) * ch := by rw [c2]
        _ = ah * (h0 * z * C.nhat s) * ch := by group
  nW_one := C.nhatW_one
  nW_simple_mul w s h := C.nhatW_simple_mul w s h
  nW_conj w s h x hx :=
    ⟨by simpa only [map_mul, map_inv, C.map_nhatW] using D.nW_conj w s h _ hx.1, hx.2.conj' _⟩
  heckeDeg_mul w s h := by
    show heckeDeg C.lU (C.nhat s) * heckeDeg C.lU (C.nhatW w) =
      heckeDeg C.lU (C.nhatW (cs.simple s * w))
    rw [C.heckeDeg_lU, C.heckeDeg_lU, C.heckeDeg_lU, C.hn, C.map_nhatW, C.map_nhatW]
    exact D.heckeDeg_mul w s h
  cover g := by
    obtain ⟨l, hl, w, h, hh, u, hu, e⟩ := D.cover (π g)
    obtain ⟨lh, hlh, rfl⟩ := C.exists_lift (hP := D.isPGroup_L) hl
    obtain ⟨uh, huh, rfl⟩ := C.exists_lift (hP := D.isPGroup_U) hu
    obtain ⟨h0, hh0, rfl⟩ := C.exists_lift_H hh
    set z := (lh * C.nhatW w * (h0 * uh))⁻¹ * g with hz_def
    have hz : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz_def]
      simp only [map_mul, map_inv, C.map_nhatW]
      rw [e]
      group
    have hzc := C.cover.ker_le hz
    have c1 : uh * z = z * uh := Subgroup.mem_center_iff.1 hzc uh
    refine ⟨lh, hlh, w, h0 * z, ?_, uh, huh, ?_⟩
    · show π (h0 * z) ∈ D.H
      rw [map_mul, MonoidHom.mem_ker.1 hz, mul_one]
      exact hh0
    · have hg' : g = lh * C.nhatW w * (h0 * uh) * z := by rw [hz_def]; group
      rw [hg']
      calc lh * C.nhatW w * (h0 * uh) * z = lh * C.nhatW w * h0 * (uh * z) := by group
        _ = lh * C.nhatW w * h0 * (z * uh) := by rw [c1]
        _ = lh * C.nhatW w * (h0 * z * uh) := by group

@[expose] noncomputable def lXEquiv (s : B) : ↥(C.lX s) ≃ ↥(D.X s) :=
  Equiv.ofBijective (fun x => ⟨π x, x.2.1⟩)
    ⟨fun x y h => Subtype.ext (pLift_inj x.2 y.2 (congrArg Subtype.val h)), fun y => by
      obtain ⟨x, hx, hxy⟩ := exists_pLift (h := C.cover) (hP := D.isPGroup_U.to_le (D.X_le s)) y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem exists_pow_mul_of_normalizes {g : Ĝ} (hg : g ∈ D.H.comap π) (n : ℕ) {w : Ĝ}
    (hw : w ∈ C.lU) : ∃ w' ∈ C.lU, (w * g) ^ n = w' * g ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨w', hw', e⟩ := ih
    have hgn : g ^ n ∈ D.H.comap π := pow_mem hg n
    have hconj : g ^ n * w * (g ^ n)⁻¹ ∈ C.lU :=
      ⟨by simpa only [map_mul, map_inv] using D.H_normU _ hgn _ hw.1, hw.2.conj _⟩
    refine ⟨w' * (g ^ n * w * (g ^ n)⁻¹), mul_mem hw' hconj, ?_⟩
    rw [pow_succ, e]
    group

theorem core_unique (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) {v h h' w : Ĝ}
    (hv : v ∈ C.lL) (hh : h ∈ D.H.comap π) (hh' : h' ∈ D.H.comap π) (hw : w ∈ C.lU)
    (e : v = h' * w * h⁻¹) : v = 1 ∧ h' = h ∧ w = 1 := by
  set g := h' * h⁻¹ with hg_def
  have hgH : g ∈ D.H.comap π := mul_mem hh' (inv_mem hh)
  have hw'' : h' * w * h'⁻¹ ∈ C.lU :=
    ⟨by simpa only [map_mul, map_inv] using D.H_normU _ hh' _ hw.1, hw.2.conj _⟩
  have hvg : v = (h' * w * h'⁻¹) * g := by rw [e, hg_def]; group
  obtain ⟨k, hk⟩ := hv.2
  obtain ⟨w₃, hw₃, e3⟩ := exists_pow_mul_of_normalizes C hgH (p ^ k) hw''
  have hgk : g ^ (p ^ k) = w₃⁻¹ := by
    rw [← hvg, hk] at e3
    exact eq_inv_of_mul_eq_one_right e3.symm
  have hg1 : g ^ (p ^ k) = 1 := by
    refine hodd _ (pow_mem hgH _) ?_
    rw [hgk]
    exact hw₃.2.inv
  have hg2 : g = 1 := hodd g hgH ⟨k, hg1⟩
  have hh'h : h' = h := by
    have : h' * h⁻¹ = 1 := hg2
    exact mul_inv_eq_one.1 this
  have hv' : v = h' * w * h'⁻¹ := by rw [hvg, hg2, mul_one]
  have hvLU : v ∈ C.lU := by rw [hv']; exact hw''
  have hv1 : v = 1 := by
    have : v ∈ C.lU ⊓ C.lL := Subgroup.mem_inf.2 ⟨hvLU, hv⟩
    have hbot : C.lU ⊓ C.lL = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
      have h : π x ∈ D.U ⊓ D.L := Subgroup.mem_inf.2 ⟨h1.1, h2.1⟩
      rw [D.U_inf_L, Subgroup.mem_bot] at h
      exact C.cover.eq_one_of_isPElt (MonoidHom.mem_ker.2 h) h1.2
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  refine ⟨hv1, hh'h, ?_⟩
  rw [hv1] at hv'
  have : h' * w * h'⁻¹ = 1 := hv'.symm
  have hw1 : w = 1 := by
    have := congrArg (fun z => h'⁻¹ * z * h') this
    simpa [mul_assoc] using this
  exact hw1

theorem eq_phiHat_of_spec (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) {x : Ĝ}
    (hx : x ∈ C.lX s) (hx1 : x ≠ 1) {l h u : Ĝ} (hl : l ∈ C.lL) (hh : h ∈ D.H.comap π)
    (hu : u ∈ C.lU) (e : x * C.nhat s = l * h * u) : C.phiHat s x = h := by
  have hspec : ∃ ĥ ∈ D.H.comap π, π ĥ = D.phi s (π x) ∧ ∃ l ∈ C.lL, ∃ u ∈ C.lU,
      x * C.nhat s = l * ĥ * u := C.exists_phiHat s hx hx1
  have hphi : C.phiHat s x ∈ D.H.comap π ∧ ∃ l ∈ C.lL, ∃ u ∈ C.lU,
      x * C.nhat s = l * C.phiHat s x * u := by
    unfold phiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    exact ⟨(C.exists_phiHat s hx hx1).choose_spec.1, (C.exists_phiHat s hx hx1).choose_spec.2.2⟩
  obtain ⟨hphiH, l', hl', u', hu', e'⟩ := hphi
  set ĥ := C.phiHat s x
  have e2 : l'⁻¹ * l = ĥ * (u' * u⁻¹) * h⁻¹ := by
    have : l * h * u = l' * ĥ * u' := e.symm.trans e'
    calc l'⁻¹ * l = l'⁻¹ * (l * h * u) * u⁻¹ * h⁻¹ := by group
      _ = l'⁻¹ * (l' * ĥ * u') * u⁻¹ * h⁻¹ := by rw [this]
      _ = ĥ * (u' * u⁻¹) * h⁻¹ := by group
  obtain ⟨-, h1, -⟩ := core_unique C hodd (mul_mem (inv_mem hl') hl) hh hphiH
    (mul_mem hu' (inv_mem hu)) e2
  exact h1

theorem eq_psiHat_of_spec (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) {x : Ĝ}
    (hx : x ∈ C.lX s) (hx1 : x ≠ 1) {a h u : Ĝ} (ha : a ∈ C.lX s) (hh : h ∈ D.H.comap π)
    (hu : u ∈ C.lU) (e : C.nhat s * x * C.nhat s = a * C.nhat s * h * u) :
    C.psiHat s x = h := by
  have hpsi : C.psiHat s x ∈ D.H.comap π ∧ ∃ a ∈ C.lX s, ∃ u ∈ C.lU,
      C.nhat s * x * C.nhat s = a * C.nhat s * C.psiHat s x * u := by
    unfold psiHat
    rw [dite_eq_left ⟨hx, hx1⟩]
    exact ⟨(C.exists_psiHat s hx hx1).choose_spec.1, (C.exists_psiHat s hx hx1).choose_spec.2.2⟩
  obtain ⟨hpsiH, a', ha', u', hu', e'⟩ := hpsi
  set ĥ := C.psiHat s x
  have hvL : (C.nhat s)⁻¹ * (a'⁻¹ * a) * C.nhat s ∈ C.lL := by
    have hax : a'⁻¹ * a ∈ C.lX s := mul_mem (inv_mem ha') ha
    refine ⟨?_, hax.2.conj' _⟩
    have h1 := D.n_inv_conjX s (x := π (a'⁻¹ * a)) hax.1
    simpa only [map_mul, map_inv, C.hn] using h1
  have e2 : (C.nhat s)⁻¹ * (a'⁻¹ * a) * C.nhat s = ĥ * (u' * u⁻¹) * h⁻¹ := by
    have : a * C.nhat s * h * u = a' * C.nhat s * ĥ * u' := e.symm.trans e'
    calc (C.nhat s)⁻¹ * (a'⁻¹ * a) * C.nhat s =
        (C.nhat s)⁻¹ * a'⁻¹ * (a * C.nhat s * h * u) * u⁻¹ * h⁻¹ := by group
      _ = (C.nhat s)⁻¹ * a'⁻¹ * (a' * C.nhat s * ĥ * u') * u⁻¹ * h⁻¹ := by rw [this]
      _ = ĥ * (u' * u⁻¹) * h⁻¹ := by group
  obtain ⟨-, h1, -⟩ := core_unique C hodd hvL hh hpsiH (mul_mem hu' (inv_mem hu)) e2
  exact h1

end CentralCoverData

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
