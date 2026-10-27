module

public import CFSG.ClassicalInvolution.Q3.Q3T6XQuot
public import CFSG.ClassicalInvolution.Q3.Q3T6XSwAbs
public import CFSG.ClassicalInvolution.Q3.Q3T6XTriv
public import CFSG.ClassicalInvolution.Q3.Q3T6BExact
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Grp
public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
  CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement MatrixGroups

section Kfacts

variable {F : Type} [Group F] [Finite F]

@[expose] def oddCent (r : F) (I : Subgroup F) : Set F := {g | g ∈ I ∧ g ∈ Cz r ∧ Odd (orderOf g)}

@[expose] def Kf (r : F) (I : Subgroup F) : Subgroup F := Subgroup.closure (oddCent r I)

theorem Kf_le (r : F) (I : Subgroup F) : Kf r I ≤ I ⊓ Cz r := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  exact ⟨hg.1, hg.2.1⟩

theorem Kf_normal (r : F) (I : Subgroup F) : ((Kf r I).subgroupOf (I ⊓ Cz r)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Kf_le r I)]
  intro h k hh hk
  have hmap : (Kf r I).map (MulAut.conj k).toMonoidHom ≤ Kf r I := by
    unfold Kf
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact I.mul_mem (I.mul_mem hk.1 hg.1) (I.inv_mem hk.1)
    · exact (Cz r).mul_mem ((Cz r).mul_mem hk.2 hg.2.1) ((Cz r).inv_mem hk.2)
    · show Odd (orderOf (k * g * k⁻¹))
      rw [orderOf_conj_eq]; exact hg.2.2
  exact hmap ⟨h, hh, rfl⟩

theorem isSubnormal_Kf {r u : F} {I : Subgroup F} (hI : Mem3 I u) :
    IsSubnormal (Kf r I) (Cz r ⊓ Cz u) := by
  have h1 : IsSubnormal (I ⊓ Cz r) (Cz u ⊓ Cz r) := isSubnormal_inf hI.subnormal (Cz r)
  rw [inf_comm (Cz u) (Cz r)] at h1
  exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf (Kf_le r I) (Kf_normal r I)) h1

theorem mem_oddCoreOf_coe_iff {H : Subgroup F} (x : ↥H) :
    (x : F) ∈ oddCoreOf H ↔ x ∈ classicalInvolutionOddCore ↥H := by
  rw [mem_oddCoreOf_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem u_mem_Kf {r u : F} {I : Subgroup F} (hI : Mem3 I u) (hr2 : r * r = 1)
    (hur : u * r = r * u) (htriv : ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) : u ∈ Kf r I := by
  classical
  have hrI : r ∈ Subgroup.normalizer (I : Set F) := mem_normalizer_of_trivial hr2 htriv
  set P : Subgroup F := oddCoreOf I with hP
  have hPodd : Odd (Nat.card P) := oddCoreOf_odd_natCard I
  have hrP : ∀ p ∈ P, r * p * r⁻¹ ∈ P := by
    intro p hp
    have h1 := Balance.Bootstrap.oddCoreIn_conjSub_eq r I
    rw [conjSub_eq_of_mem_normalizer hrI] at h1
    have hp' : p ∈ Balance.oddCoreIn I := hp
    have this := conj_mem_conjSub (n := r) hp'
    rw [← h1] at this
    exact this
  have hlift : ∀ g ∈ I, ∃ p ∈ P, g * p ∈ Cz r ∧ g * p ∈ I := by
    intro g hg
    have hx : g⁻¹ * (r * g * r⁻¹) ∈ P := by
      have h1 : ⁅r, g⁆ ∈ P := htriv g hg
      have h2 : g⁻¹ * ⁅r, g⁆ * g⁻¹⁻¹ ∈ P := Balance.conj_mem_oddCoreIn (I.inv_mem hg) h1
      have e : g⁻¹ * ⁅r, g⁆ * g⁻¹⁻¹ = g⁻¹ * (r * g * r⁻¹) := by
        rw [commutatorElement_def]; group
      rwa [e] at h2
    obtain ⟨p, hp, hfix⟩ := exists_fixed_mul_of_odd hr2 hPodd hrP hx
    exact ⟨p, hp, Subgroup.mem_centralizer_singleton_iff.mpr hfix,
      I.mul_mem hg (oddCoreOf_le_self I hp)⟩
  have hodd_of_pow : ∀ {g : F} {m : ℕ}, Odd m → g ^ m ∈ P → Odd (orderOf g) := by
    intro g m hm hgm
    have hdvd : orderOf (g ^ m) ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hgm
    have h1 : (g ^ m) ^ Nat.card P = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [← pow_mul] at h1
    exact (hm.mul hPodd).of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr h1)
  let e : OddQuot I ≃* SL(2, ZMod 3) := Mem3.equiv hI
  let φ : ↥I →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥I))
  have hφsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : ∀ x : ↥I, φ x = 1 ↔ (x : F) ∈ P := by
    intro x
    rw [hP, mem_oddCoreOf_coe_iff]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := Q3T7T2.sl2Three_gen (φ ⟨u, hI.mem⟩)
  have hlift3 : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 →
      ∃ (g : F) (hg : g ∈ I), g ∈ oddCent r I ∧ φ ⟨g, hg⟩ = s := by
    intro s hs
    obtain ⟨x, hx⟩ := hφsurj s
    obtain ⟨p, hp, hgC, hgI⟩ := hlift (x : F) x.2
    have hφp : φ ⟨(x : F) * p, hgI⟩ = s := by
      have : (⟨(x : F) * p, hgI⟩ : ↥I) = x * ⟨p, oddCoreOf_le_self I hp⟩ := rfl
      rw [this, map_mul, hx, (hφker ⟨p, oddCoreOf_le_self I hp⟩).mpr hp, mul_one]
    refine ⟨(x : F) * p, hgI, ⟨hgI, hgC, ?_⟩, hφp⟩
    have h3 : φ ((⟨(x : F) * p, hgI⟩ : ↥I) ^ 3) = 1 := by rw [map_pow, hφp, hs]
    have h3' := (hφker _).mp h3
    exact hodd_of_pow (m := 3) (by decide) (by simpa using h3')
  obtain ⟨g₁, hg₁I, hg₁, hφ₁⟩ := hlift3 a ha
  obtain ⟨g₂, hg₂I, hg₂, hφ₂⟩ := hlift3 b hb
  obtain ⟨g₃, hg₃I, hg₃, hφ₃⟩ := hlift3 c hc
  have hmem : ∀ g ∈ oddCent r I, g ∈ Kf r I := fun g hg => Subgroup.subset_closure hg
  set t : F := g₁ * g₂ * g₃ with ht
  have htK : t ∈ Kf r I := (Kf r I).mul_mem ((Kf r I).mul_mem (hmem _ hg₁) (hmem _ hg₂))
    (hmem _ hg₃)
  have htI : t ∈ I := I.mul_mem (I.mul_mem hg₁I hg₂I) hg₃I
  have hφt : φ ⟨t, htI⟩ = φ ⟨u, hI.mem⟩ := by
    have : (⟨t, htI⟩ : ↥I) = ⟨g₁, hg₁I⟩ * ⟨g₂, hg₂I⟩ * ⟨g₃, hg₃I⟩ := rfl
    rw [this, map_mul, map_mul, hφ₁, hφ₂, hφ₃, ← habc]
  have hoI : u⁻¹ * t ∈ I := I.mul_mem (I.inv_mem hI.mem) htI
  have hoP : u⁻¹ * t ∈ P := by
    rw [← hφker ⟨u⁻¹ * t, hoI⟩]
    have : (⟨u⁻¹ * t, hoI⟩ : ↥I) = ⟨u, hI.mem⟩⁻¹ * ⟨t, htI⟩ := rfl
    rw [this, map_mul, map_inv, hφt, inv_mul_cancel]
  have hoC : u⁻¹ * t ∈ Cz r := by
    have hu : u ∈ Cz r := Subgroup.mem_centralizer_singleton_iff.mpr hur
    exact (Cz r).mul_mem ((Cz r).inv_mem hu) (Kf_le r I htK).2
  have hoK : u⁻¹ * t ∈ Kf r I :=
    hmem _ ⟨hoI, hoC, hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hoP)⟩
  have : u = t * (u⁻¹ * t)⁻¹ := by group
  rw [this]
  exact (Kf r I).mul_mem htK ((Kf r I).inv_mem hoK)

end Kfacts

section Wgroup

variable {F : Type} [Group F] [Finite F]

@[expose] def R4 {X : Type} [Group X] (Z : Subgroup X) : Subgroup X :=
  Subgroup.closure {x | x ∈ Z ∧ x ^ 4 = 1}

@[expose] def memberSet (z : F) : Set (Subgroup (Qz z)) := {Z | ∃ Y, Mem3 Y z ∧ Z = imgz z Y}

theorem Mem3.of_memberSet {z : F} {Z : Subgroup (Qz z)} (h : Z ∈ memberSet z) :
    Mem3 Z (zb z) := by
  obtain ⟨Y, hY, rfl⟩ := h
  exact Mem3.imgz hY

theorem commute_of_memberSet {z : F} {Z Z' : Subgroup (Qz z)} (h : Z ∈ memberSet z)
    (h' : Z' ∈ memberSet z) (hne : Z ≠ Z') {a b : Qz z} (ha : a ∈ Z) (hb : b ∈ Z') :
    a * b = b * a :=
  Mem3.commute_of_twin_exact (Mem3.of_memberSet h) (Mem3.of_memberSet h') (exAt_zb z) hne ha hb

theorem pow_four_mul_of_exact {X : Type} [Group X] [Finite X] {Z : Subgroup X} {z : X}
    (hZ : Mem3 Z z) (hex : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥)
    {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) (hx4 : x ^ 4 = 1) (hy4 : y ^ 4 = 1) :
    (x * y) ^ 4 = 1 := by
  have hbot : classicalInvolutionOddCore ↥Z = ⊥ := (Mem3.exAt_iff hZ).mp hex
  obtain ⟨e⟩ := (hZ.member.toQ3 (by norm_num)).nonempty_equiv_sl2 hbot
  have h1 : (e ⟨x, hx⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥Z) ^ 4 = 1 := Subtype.ext hx4
    rw [this, map_one]
  have h2 : (e ⟨y, hy⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥Z) ^ 4 = 1 := Subtype.ext hy4
    rw [this, map_one]
  have h3 : (e ⟨x, hx⟩ * e ⟨y, hy⟩) ^ 4 = 1 :=
    mem_sl2ThreeQ8.mp (sl2ThreeQ8.mul_mem (mem_sl2ThreeQ8.mpr h1) (mem_sl2ThreeQ8.mpr h2))
  rw [← map_mul, ← map_pow] at h3
  have h4 : (⟨x, hx⟩ * ⟨y, hy⟩ : ↥Z) ^ 4 = 1 := e.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

theorem mem_R4 {X : Type} [Group X] [Finite X] {Z : Subgroup X} {z : X} (hZ : Mem3 Z z)
    (hex : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥) {x : X} :
    x ∈ R4 Z ↔ x ∈ Z ∧ x ^ 4 = 1 := by
  constructor
  · intro hx
    unfold R4 at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨Z.one_mem, one_pow 4⟩
    | mul x y _ _ hxx hyy =>
      exact ⟨Z.mul_mem hxx.1 hyy.1, pow_four_mul_of_exact hZ hex hxx.1 hyy.1 hxx.2 hyy.2⟩
    | inv x _ hxx =>
      refine ⟨Z.inv_mem hxx.1, ?_⟩
      rw [inv_pow, hxx.2, inv_one]
  · intro hx
    exact Subgroup.subset_closure hx

theorem isPGroup_R4 {X : Type} [Group X] [Finite X] {Z : Subgroup X} {z : X} (hZ : Mem3 Z z)
    (hex : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥) :
    IsPGroup 2 (R4 Z) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  exact ((mem_R4 hZ hex).mp g.2).2

end Wgroup

section Wr

variable {F : Type} [Group F] [Finite F]

@[expose] def Wr (z : F) : Subgroup (Qz z) := ⨆ Z : ↥(memberSet z), R4 (Z : Subgroup (Qz z))

theorem conj_mem_memberSet {z : F} {Z : Subgroup (Qz z)} (hZ : Z ∈ memberSet z) (k : Qz z) :
    conjSub k Z ∈ memberSet z := by
  obtain ⟨Y, hY, rfl⟩ := hZ
  obtain ⟨κ, rfl⟩ := piz_surjective z k
  exact ⟨conjSub (κ : F) Y,
    hY.conj_of_commute (Subgroup.mem_centralizer_singleton_iff.mp κ.2), imgz_conjSub z Y κ⟩

theorem isPGroup_Wr (z : F) : IsPGroup 2 (Wr z) :=
  isPGroup_iSup_of_commutes _ (fun Z => isPGroup_R4 (Mem3.of_memberSet Z.2) (exAt_zb z))
    (fun Z Z' hne _ ha _ hb => commute_of_memberSet Z.2 Z'.2 (fun h => hne (Subtype.ext h))
      ((mem_R4 (Mem3.of_memberSet Z.2) (exAt_zb z)).mp ha).1
      ((mem_R4 (Mem3.of_memberSet Z'.2) (exAt_zb z)).mp hb).1)

theorem R4_le_Wr {z : F} {Z : Subgroup (Qz z)} (hZ : Z ∈ memberSet z) : R4 Z ≤ Wr z :=
  le_iSup (fun Z : ↥(memberSet z) => R4 (Z : Subgroup (Qz z))) ⟨Z, hZ⟩

theorem Wr_le_normalizer {z : F} {Y : Subgroup (Qz z)} (hY : Y ∈ memberSet z) :
    Wr z ≤ Subgroup.normalizer (Y : Set (Qz z)) := by
  refine iSup_le fun Z => ?_
  intro x hx
  have hxZ : x ∈ (Z : Subgroup (Qz z)) :=
    ((mem_R4 (Mem3.of_memberSet Z.2) (exAt_zb z)).mp hx).1
  by_cases hZY : (Z : Subgroup (Qz z)) = Y
  · rw [← hZY]
    exact Subgroup.le_normalizer hxZ
  · refine Subgroup.centralizer_le_normalizer (Y : Set (Qz z)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_memberSet Z.2 hY hZY hxZ hy).symm

theorem Wr_normal {z : F} (k : Qz z) {w : Qz z} (hw : w ∈ Wr z) : k * w * k⁻¹ ∈ Wr z := by
  refine Subgroup.iSup_induction (fun Z : ↥(memberSet z) => R4 (Z : Subgroup (Qz z)))
    (C := fun w => k * w * k⁻¹ ∈ Wr z) hw ?_ ?_ ?_
  · intro Z w hw
    have hZ' := conj_mem_memberSet Z.2 k
    have hw' := (mem_R4 (Mem3.of_memberSet Z.2) (exAt_zb z)).mp hw
    refine R4_le_Wr hZ' ((mem_R4 (Mem3.of_memberSet hZ') (exAt_zb z)).mpr
      ⟨conj_mem_conjSub hw'.1, ?_⟩)
    rw [conj_pow, hw'.2]
    group
  · simp
  · intro x y hx hy
    have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rw [this]
    exact (Wr z).mul_mem hx hy

end Wr

section Main

variable {F : Type} [Group F] [Finite F]

theorem noTrivialSwap_false {Q I : Subgroup F} {r u : F} (hQ : Mem3 Q r) (hI : Mem3 I u)
    (hur : u * r = r * u) (hne : Q ≠ conjSub u Q)
    (htriv : ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) : False := by
  classical
  have hr2 : r * r = 1 := hQ.mul_self
  have hu2 : u * u = 1 := hI.mul_self
  have hu : u ∈ Cz r := Subgroup.mem_centralizer_singleton_iff.mpr hur
  have hu1 : orderOf u = 2 := hI.orderOf_eq_two
  have hQC : Q ≤ Cz r := hQ.le_centralizer
  have hQ' : Mem3 (conjSub u Q) r := hQ.conj_of_commute hur
  have hOQ : oddCoreOf (Cz r) ≤ Q := hQ.intrinsic solvableType_three
  have hOQ' : oddCoreOf (Cz r) ≤ conjSub u Q := hQ'.intrinsic solvableType_three
  set ub : Qz r := piz r ⟨u, hu⟩ with hubdef
  set Kb : Subgroup (Qz r) := imgz r (Kf r I) with hKbdef
  set Qb : Subgroup (Qz r) := imgz r Q with hQbdef
  have hQb : Mem3 Qb (zb r) := Mem3.imgz hQ
  have hexr : Balance.oddCoreIn (Subgroup.centralizer ({zb r} : Set (Qz r))) = ⊥ := exAt_zb r
  have hDb : imgz r (Cz r ⊓ Cz u) = Subgroup.centralizer ({ub} : Set (Qz r)) :=
    (centralizer_piz r hu hu1).symm
  have hKD : Kb ≤ imgz r (Cz r ⊓ Cz u) :=
    imgz_mono r (fun x hx => ⟨(Kf_le r I hx).2, hI.le_centralizer (Kf_le r I hx).1⟩)
  have hsub : IsSubnormal Kb (imgz r (Cz r ⊓ Cz u)) := isSubnormal_imgz r (isSubnormal_Kf hI)
  have hKgen : Kb ≤ Subgroup.closure {g : Qz r | g ∈ Kb ∧ Odd (orderOf g)} := by
    have key : ∀ (κ : F) (hκ : κ ∈ Kf r I), ∃ hC : κ ∈ Cz r,
        piz r ⟨κ, hC⟩ ∈ Subgroup.closure {g : Qz r | g ∈ Kb ∧ Odd (orderOf g)} := by
      intro κ hκ
      unfold Kf at hκ
      induction hκ using Subgroup.closure_induction with
      | mem x hx =>
        refine ⟨hx.2.1, Subgroup.subset_closure ⟨piz_mem_imgz hx.2.1 (Subgroup.subset_closure hx),
          ?_⟩⟩
        have h1 : orderOf (piz r ⟨x, hx.2.1⟩) ∣ orderOf (⟨x, hx.2.1⟩ : ↥(Cz r)) :=
          orderOf_map_dvd (piz r) _
        rw [Subgroup.orderOf_mk] at h1
        exact hx.2.2.of_dvd_nat h1
      | one =>
        refine ⟨(Cz r).one_mem, ?_⟩
        have : (⟨1, (Cz r).one_mem⟩ : ↥(Cz r)) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        obtain ⟨hCx, hx'⟩ := ihx
        obtain ⟨hCy, hy'⟩ := ihy
        refine ⟨(Cz r).mul_mem hCx hCy, ?_⟩
        have : piz r ⟨x * y, (Cz r).mul_mem hCx hCy⟩ =
            piz r ⟨x, hCx⟩ * piz r ⟨y, hCy⟩ := by
          rw [← map_mul]; rfl
        rw [this]
        exact Subgroup.mul_mem _ hx' hy'
      | inv x hx ih =>
        obtain ⟨hCx, hx'⟩ := ih
        refine ⟨(Cz r).inv_mem hCx, ?_⟩
        have : piz r ⟨x⁻¹, (Cz r).inv_mem hCx⟩ = (piz r ⟨x, hCx⟩)⁻¹ := by
          rw [← map_inv]; rfl
        rw [this]
        exact Subgroup.inv_mem _ hx'
    intro x hx
    obtain ⟨κ, hC, hκK, rfl⟩ := (mem_imgz_iff r).mp hx
    obtain ⟨_, h⟩ := key κ hκK
    exact h
  have hubK : ub ∈ Kb := piz_mem_imgz hu (u_mem_Kf hI hr2 hur htriv)
  have hub2 : ub * ub = 1 := by
    rw [hubdef, ← map_mul]
    have : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥(Cz r)) = 1 := Subtype.ext hu2
    rw [this, map_one]
  have hub1 : ub ≠ 1 := piz_ne_one_of_orderOf_eq_two r hu hu1
  have huniq : ∀ x ∈ Kb, x * x = 1 → x = 1 ∨ x = ub := by
    intro x hx hx2
    obtain ⟨w, hC, hwK, hw2, rfl⟩ := exists_lift_involution_of_mem r hx hx2
    rcases hI.isUniqueInvolution.unique w (Kf_le r I hwK).1 hw2 with h | h
    · left
      subst h
      have : (⟨1, hC⟩ : ↥(Cz r)) = 1 := rfl
      rw [this, map_one]
    · right
      subst h
      rfl
  have hQmem : Qb ∈ memberSet r := ⟨Q, hQ, rfl⟩
  have hperm : ∀ k ∈ Kb, conjSub k Qb ∈ memberSet r := fun k _ => conj_mem_memberSet hQmem k
  have hQbu : conjSub ub Qb ∈ memberSet r := conj_mem_memberSet hQmem ub
  have hQu : conjSub ub Qb ≠ Qb := by
    intro h
    have h1 : conjSub ub Qb = imgz r (conjSub u Q) := imgz_conjSub r Q ⟨u, hu⟩
    rw [h1] at h
    exact hne (eq_of_imgz_eq r (conjSub_le_Cz hQC ⟨u, hu⟩) hQC hOQ' hOQ h).symm
  have hubzb : ub * zb r = zb r * ub := by
    rw [hubdef]
    unfold zb
    rw [← map_mul, ← map_mul]
    exact congrArg (piz r) (Subtype.ext hur)
  have hswap : Swap Qb (zb r) ub := ⟨hQb, hub2, hubzb, hQu⟩
  obtain ⟨R, hR⟩ := hswap.exists_swapSylow
  obtain ⟨e, he, e₂, -, he2, -, -⟩ := hQb.exists_two_sq_elements hR.sylow
  have heQ : e ∈ Qb := (he).2
  have hzb2 : zb r * zb r = 1 := by
    unfold zb
    rw [← map_mul]
    have : (⟨r, self_mem_Cz r⟩ * ⟨r, self_mem_Cz r⟩ : ↥(Cz r)) = 1 := Subtype.ext hr2
    rw [this, map_one]
  have he4 : e ^ 4 = 1 := by
    calc e ^ 4 = (e * e) * (e * e) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [he2, hzb2]
  set e' : Qz r := ub * e * ub⁻¹ with he'def
  have he'Q : e' ∈ conjSub ub Qb := conj_mem_conjSub heQ
  have he'4 : e' ^ 4 = 1 := by rw [he'def, conj_pow, he4]; group
  have hcomm_ee' : e * e' = e' * e := hR.comm_conj he
  set δb : Qz r := diag ub e with hδdef
  have hδu : ub * δb = δb * ub := diag_comm_y hub2 hcomm_ee'
  have hδD : δb ∈ imgz r (Cz r ⊓ Cz u) := by
    rw [hDb]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hδu.symm
  have heW : e ∈ Wr r :=
    R4_le_Wr hQmem ((mem_R4 hQb hexr).mpr ⟨heQ, he4⟩)
  have he'W : e' ∈ Wr r :=
    R4_le_Wr hQbu ((mem_R4 (Mem3.of_memberSet hQbu) hexr).mpr ⟨he'Q, he'4⟩)
  have hδW : δb ∈ Wr r := (Wr r).mul_mem heW he'W
  have hΘ : ∀ Y ∈ memberSet r, (∃ y ∈ Y, δb * y ≠ y * δb) → Y = Qb ∨ Y = conjSub ub Qb := by
    intro Y hY ⟨y, hyY, hy⟩
    by_contra hcon
    push Not at hcon
    apply hy
    have h1 : y * e = e * y := commute_of_memberSet hY hQmem hcon.1 hyY heQ
    have h2 : y * e' = e' * y := commute_of_memberSet hY hQbu hcon.2 hyY he'Q
    show e * e' * y = y * (e * e')
    calc e * e' * y = e * (e' * y) := by group
      _ = e * (y * e') := by rw [h2]
      _ = (e * y) * e' := by group
      _ = (y * e) * e' := by rw [h1]
      _ = y * (e * e') := by group
  have hΘQ : ∃ y ∈ Qb, δb * y ≠ y * δb := by
    have hbot : oddCoreOf Qb = ⊥ := Mem3.oddCoreOf_eq_bot hQb hexr
    have hnc := Mem3.not_forall_comm_of_sq_eq hQb heQ he2
    push Not at hnc
    obtain ⟨y, hyQ, hy⟩ := hnc
    rw [hbot, Subgroup.mem_bot] at hy
    have hey : e * y ≠ y * e := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mpr h)
    refine ⟨y, hyQ, fun h => hey ?_⟩
    have h1 : y * e' = e' * y := commute_of_memberSet hQmem hQbu hQu.symm hyQ he'Q
    have h2 : e * e' * y = y * (e * e') := h
    have h3 : e * y * e' = y * e * e' := by
      calc e * y * e' = e * (y * e') := by group
        _ = e * (e' * y) := by rw [h1]
        _ = e * e' * y := by group
        _ = y * (e * e') := h2
        _ = y * e * e' := by group
    exact mul_right_cancel h3
  exact swap_contra hKD hsub hKgen hubK hub2 hub1 huniq hQmem hperm
    (fun k _ w hw => Wr_normal k hw)
    (fun w hw Y hY => mem_normalizer_iff_conjSub_eq.mp (Wr_le_normalizer hY hw))
    (isPGroup_Wr r) hQu hδW hδD hΘ hΘQ

theorem noTrivialSwapOn_all (F : Type) [Group F] [Finite F] (S : Set F) : NoTrivialSwapOn F S :=
  fun hQ _ _ _ hur hne _ hI htriv => noTrivialSwap_false hQ hI hur hne htriv

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6X
