module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinBridge
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinReduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem quat_center_eqK (hd : Q8TwinDatum R S t) {n : ℕ} [NeZero n]
    (e : ↥(S : Subgroup R) ≃* QuaternionGroup n) :
    (((e.symm (QuaternionGroup.a n) : ↥(S : Subgroup R)) : ↥R) : Y) = t := by
  set u : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a n) with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, TL4.quat_sq_center, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h
    exact TL4.quat_center_ne (by simpa using congrArg e h)
  have hord : orderOf (((u : ↥R) : Y)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) hu2
      simpa using this
    · intro h
      apply hu1
      exact Subtype.ext (Subtype.ext h)
  exact Q8Datum.eq_of_orderOf_eq_two hd (u : ↥R).2 hord

theorem exists_S₀_pairK (hd : Q8TwinDatum R S t) {k : ℕ} (hk : 3 ≤ k)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (k - 2)))) :
    ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype,
      r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t := by
  obtain ⟨e⟩ := hq
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hct := quat_center_eqK hd e
  have hm : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := TL4.quat_pair hm
  set u₁ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a (2 ^ (k - 3) : ℕ))
  set u₂ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.xa 0)
  refine ⟨((u₁ : ↥R) : Y), ⟨u₁, u₁.2, rfl⟩, ((u₂ : ↥R) : Y), ⟨u₂, u₂.2, rfl⟩,
    TL4.sq_eq_of_quat e hct h1, TL4.sq_eq_of_quat e hct h2, ?_⟩
  have h3' := TL4.sq_eq_of_quat e hct h3
  rw [map_mul] at h3'
  exact h3'

theorem exists_sq_of_conjSub_neK (hd : Q8TwinDatum R S t) {k : ℕ} (hk : 3 ≤ k)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (k - 2)))) {A : Subgroup Y} {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) (hsA : conjSub s A ≠ A) :
    ∃ s' ∈ (S : Subgroup R).map R.subtype, s' * s' = t ∧ conjSub s' A ≠ A := by
  obtain ⟨e⟩ := hq
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hct := quat_center_eqK hd e
  obtain ⟨x, hx, rfl⟩ := hs
  have hxe : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
  rcases TL4.quat_split (e ⟨x, hx⟩) with h | ⟨y, z, hy, hz, hyz⟩
  · refine ⟨R.subtype x, ⟨x, hx, rfl⟩, ?_, hsA⟩
    have := TL4.sq_eq_of_quat e hct h
    rwa [← hxe] at this
  · have hxyz : (R.subtype x : Y) = (((e.symm y : ↥(S : Subgroup R)) : ↥R) : Y) *
        (((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y) := by
      have h1 : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm y * e.symm z := by
        rw [hxe, hyz, map_mul]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) h1
      simpa using this
    by_cases hzA : conjSub (((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y) A = A
    · refine ⟨(((e.symm y : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm y).2, rfl⟩,
        TL4.sq_eq_of_quat e hct hy, fun hyA => hsA ?_⟩
      rw [hxyz, conjSub_mul, hzA, hyA]
    · exact ⟨(((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm z).2, rfl⟩,
        TL4.sq_eq_of_quat e hct hz, hzA⟩

theorem inv_in_S₀K (hd : Q8TwinDatum R S t) {k : ℕ} (hk : 3 ≤ k)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (k - 2)))) :
    ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype,
      s * r * s⁻¹ = r⁻¹ := by
  obtain ⟨e⟩ := hq
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hev : Even (2 ^ (k - 2)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨h, hh⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.quaternionGroup_exists_conj_eq_inv hev
    (e ⟨x, hx⟩)
  refine ⟨(((e.symm h : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm h).2, rfl⟩, ?_⟩
  have h1 : e.symm h * ⟨x, hx⟩ * (e.symm h)⁻¹ = (⟨x, hx⟩ : ↥(S : Subgroup R))⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hh
  have h2 := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) h1
  simpa using h2

theorem exists_noncommK (hd : Q8TwinDatum R S t) (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹) {r : Y}
    (hrS : r ∈ (S : Subgroup R).map R.subtype) (hrr : r * r = t) :
    ∃ s ∈ (S : Subgroup R).map R.subtype, s * r ≠ r * s := by
  obtain ⟨s, hs, hsr⟩ := hinv _ hrS
  refine ⟨s, hs, fun h => ?_⟩
  have h1 : s * r * s⁻¹ = r := by rw [h]; group
  rw [h1] at hsr
  have : r * r = 1 := by simpa using congrArg (· * r) hsr
  rw [hrr] at this
  have h' := hd.order
  rw [this, orderOf_one] at h'
  norm_num at h'

theorem no_twinK (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹)
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) {a : Y} (haA : a ∈ A)
    (hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹) (ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a))
    {w : Y} (hw : w ∈ A)
    (hc : ∀ y ∈ A, (w * a * w⁻¹ * a⁻¹) * y = y * (w * a * w⁻¹ * a⁻¹)) : w * a = a * w := by
  set c : Y := w * a * w⁻¹ * a⁻¹ with hcdef
  have hcA : c ∈ A := A.mul_mem (A.mul_mem (A.mul_mem hw haA) (A.inv_mem hw)) (A.inv_mem haA)
  have hca : c * a = a * c := hc a haA
  have hc2 : c * c = 1 := by
    have e1 : (c * a) * (c * a) = a * a := by
      have : c * a = w * a * w⁻¹ := by rw [hcdef]; group
      rw [this]
      calc w * a * w⁻¹ * (w * a * w⁻¹) = w * (a * a) * w⁻¹ := by group
        _ = (a * a) * w * w⁻¹ := by rw [ha2 w hw]
        _ = a * a := by group
    have e2 : (c * a) * (c * a) = (c * c) * (a * a) := by
      calc (c * a) * (c * a) = c * (a * c) * a := by group
        _ = c * (c * a) * a := by rw [hca]
        _ = (c * c) * (a * a) := by group
    rw [e2] at e1
    calc c * c = (c * c) * (a * a) * (a * a)⁻¹ := by group
      _ = 1 := by rw [e1]; group
  have hcZ : c ∈ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) :=
    TightA.mem_centerLayer_of_mem_center hA hcA fun y hy => (hc y hy).symm
  have htZ : t ∉ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) := fun h =>
    hE2 ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup hO, h⟩
  have hcomN : ∀ {s : Y}, s ∈ (S : Subgroup R).map R.subtype → s * c = c * s := fun {s} hs =>
    commute_of_normal_two hd hΩ TightA.centerLayer_normal (TightA.centerLayer_isPGroup hO) htZ
      hs hcZ
  have hrc : r * c = c * r := hcomN hrS
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hwB : r * w * r⁻¹ ∈ conjSub r A := conj_mem_conjSub hw
  have hwtA : t * w⁻¹ * t⁻¹ ∈ A := by
    rw [hta _ (A.inv_mem hw)]
    exact A.mul_mem (A.mul_mem haA (A.inv_mem hw)) (A.inv_mem haA)
  have hcomm := comm_of_ne hB hA hrA hwB hwtA
  set v : Y := w * (r * w * r⁻¹) with hvdef
  have hvr : v * r * v⁻¹ = c * r := by
    have e1 : v * r * v⁻¹ * r⁻¹ =
        w * ((r * w * r⁻¹) * (t * w⁻¹ * t⁻¹)) * (r * w⁻¹ * r⁻¹) := by
      rw [hvdef, ← hrr]; group
    rw [hcomm] at e1
    have e2 : w * ((t * w⁻¹ * t⁻¹) * (r * w * r⁻¹)) * (r * w⁻¹ * r⁻¹) = w * (t * w⁻¹ * t⁻¹) := by
      group
    rw [e2, hta _ (A.inv_mem hw)] at e1
    calc v * r * v⁻¹ = (v * r * v⁻¹ * r⁻¹) * r := by group
      _ = c * r := by rw [e1, hcdef]; group
  have hvt : v * t = t * v := by
    have e : v * t * v⁻¹ = t := by
      calc v * t * v⁻¹ = (v * r * v⁻¹) * (v * r * v⁻¹) := by rw [← hrr]; group
        _ = (c * r) * (c * r) := by rw [hvr]
        _ = c * (r * c) * r := by group
        _ = c * (c * r) * r := by rw [hrc]
        _ = (c * c) * (r * r) := by group
        _ = t := by rw [hc2, hrr, one_mul]
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [e]
  have hc1 : c = 1 := by
    by_contra hc1
    have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
      CoreAssembly.mem_conjClass_self _
    have hJ : conjSub v (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨v, rfl⟩
    have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
    have huJ : c * r ∈ conjSub v (tightCore R) := by
      rw [← hvr]
      exact conj_mem_conjSub hrK
    have hzK := isUniqueInvolution_core hd
    by_cases hJK : conjSub v (tightCore R) = tightCore R
    ·
      have hcK : c ∈ tightCore R := by
        have := (tightCore R).mul_mem (hJK ▸ huJ) ((tightCore R).inv_mem hrK)
        simpa using this
      have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
      exact htZ (eq_of_orderOf_eq_two hd (tightCore_le R hcK) hord ▸ hcZ)
    · have hzJ : IsUniqueInvolution (conjSub v (tightCore R)) t := by
        have := hzK.conj v
        have hvt' : v * t * v⁻¹ = t := by
          calc v * t * v⁻¹ = t * v * v⁻¹ := by rw [hvt]
            _ = t := by group
        rwa [hvt'] at this
      have hodd := (Disconnected.AschTight.Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ (Ne.symm hJK)
        hzK hzJ)
      obtain ⟨s, hsS, hsr⟩ := hinv _ hrS
      have hsK : s ∈ tightCore R := mem_core_of_mem_S₀ hd hsS
      have hcomm2 : ⁅s, c * r⁆ ∈ ⁅tightCore R, conjSub v (tightCore R)⁆ :=
        Subgroup.commutator_mem_commutator hsK huJ
      have hsc := hcomN hsS
      have htc : c * t = t * c := by rw [← hrr]; calc c * (r * r) = (c * r) * r := by group
        _ = (r * c) * r := by rw [hrc]
        _ = r * (c * r) := by group
        _ = r * (r * c) := by rw [hrc]
        _ = (r * r) * c := by group
      have hcomval : ⁅s, c * r⁆ = t := by
        rw [commutatorElement_def]
        have e1 : s * (c * r) * s⁻¹ = c * r⁻¹ := by
          calc s * (c * r) * s⁻¹ = (s * c) * (r * s⁻¹) := by group
            _ = (c * s) * (r * s⁻¹) := by rw [hsc]
            _ = c * (s * r * s⁻¹) := by group
            _ = c * r⁻¹ := by rw [hsr]
        have e2 : r⁻¹ * r⁻¹ = t⁻¹ := by rw [← hrr]; group
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (t_mul_t hd)
        calc s * (c * r) * s⁻¹ * (c * r)⁻¹ = (s * (c * r) * s⁻¹) * (r⁻¹ * c⁻¹) := by group
          _ = c * (r⁻¹ * r⁻¹) * c⁻¹ := by rw [e1]; group
          _ = c * t * c⁻¹ := by rw [e2, htinv]
          _ = t := by rw [htc]; group
      rw [hcomval] at hcomm2
      have ht1 : t ∈ oddCoreOf (tightCore R) := (hodd hcomm2).1
      have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
      have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (tightCore R)) ht1 ht2
      have h' := hd.order
      rw [this, orderOf_one] at h'
      norm_num at h'
  calc w * a = c * (a * w) := by rw [hcdef]; group
    _ = a * w := by rw [hc1, one_mul]

theorem mem_normalizer_core_of_commK (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) {a : Y} (haA : a ∈ A)
    (hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹) {g₁ : Y} (hg₁ : g₁ ∈ A)
    (hxt : (g₁ * a * g₁⁻¹ * a⁻¹) * t = t * (g₁ * a * g₁⁻¹ * a⁻¹)) :
    g₁ * a * g₁⁻¹ * a⁻¹ ∈ Subgroup.normalizer (tightCore R : Set Y) := by
  set x : Y := g₁ * a * g₁⁻¹ * a⁻¹ with hx
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  set g₂ : Y := r * g₁ * r⁻¹ with hg₂
  set h : Y := t * g₁⁻¹ * t⁻¹ with hh
  have hg₂B : g₂ ∈ conjSub r A := conj_mem_conjSub hg₁
  have hhA : h ∈ A := by
    rw [hh, hta _ (A.inv_mem hg₁)]
    exact A.mul_mem (A.mul_mem haA (A.inv_mem hg₁)) (A.inv_mem haA)
  have hcomm : g₂ * h = h * g₂ := comm_of_ne hB hA hrA hg₂B hhA
  set G : Y := g₁ * g₂ with hG
  have hconj : G * r * G⁻¹ = x * r := by
    have e1 : G * r * G⁻¹ = g₁ * (g₂ * h * g₂⁻¹) * r := by
      rw [hG, hg₂, hh, ← hrr]; group
    have e2 : g₂ * h * g₂⁻¹ = h := by rw [hcomm]; group
    rw [e1, e2, hh, hta _ (A.inv_mem hg₁), hx]; group
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub G (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨G, rfl⟩
  have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
  have huJ : x * r ∈ conjSub G (tightCore R) := by
    rw [← hconj]
    exact conj_mem_conjSub hrK
  by_cases hJK : conjSub G (tightCore R) = tightCore R
  · have h1 : x * r ∈ tightCore R := hJK ▸ huJ
    have hx' : x ∈ tightCore R := by
      simpa using (tightCore R).mul_mem h1 ((tightCore R).inv_mem hrK)
    exact Subgroup.le_normalizer hx'
  · have hxrN : x * r ∈ Subgroup.normalizer (tightCore R : Set Y) := by
      refine hΩ.omega5 _ hK _ hJ (Ne.symm hJK) t (isUniqueInvolution_core hd) (x * r) huJ ?_ ?_ ?_
      · intro hall
        obtain ⟨s, hsS, hsr⟩ := exists_noncommK hd hinv hrS hrr
        have hsK := mem_core_of_mem_S₀ hd hsS
        have hw : G * s * G⁻¹ ∈ conjSub G (tightCore R) := conj_mem_conjSub hsK
        have h2 := hall _ hw
        rw [← hconj] at h2
        apply hsr
        have e : G * (r * s) * G⁻¹ = G * (s * r) * G⁻¹ := by
          calc G * (r * s) * G⁻¹ = (G * r * G⁻¹) * (G * s * G⁻¹) := by group
            _ = (G * s * G⁻¹) * (G * r * G⁻¹) := h2
            _ = G * (s * r) * G⁻¹ := by group
        exact (mul_left_cancel (mul_right_cancel e)).symm
      · have hr2 : IsPGroup 2 ↥(Subgroup.zpowers r) :=
          (hd.sylow_core.2.1).to_le (Subgroup.zpowers_le.mpr hrS)
        rw [← hconj]
        have e : Subgroup.zpowers (G * r * G⁻¹) =
            (Subgroup.zpowers r).map (MulAut.conj G).toMonoidHom := by
          rw [MonoidHom.map_zpowers]
          rfl
        rw [e]
        exact hr2.map _
      · calc x * r * t = x * (r * t) := by group
          _ = x * (t * r) := by rw [mul_t_comm_of_sq hrr]
          _ = (x * t) * r := by group
          _ = (t * x) * r := by rw [hxt]
          _ = t * (x * r) := by group
    have := (Subgroup.normalizer (tightCore R : Set Y)).mul_mem hxrN
      ((Subgroup.normalizer (tightCore R : Set Y)).inv_mem (Subgroup.le_normalizer hrK))
    simpa using this

theorem false_of_innerK (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P)
    (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrr : r * r = t) (hrA : conjSub r A ≠ A) (hnc : ¬ ∀ x ∈ A, x * t = t * x) : False := by
  classical
  have ht2 : t * t = 1 := t_mul_t hd
  obtain ⟨a, haA, e, he, hae⟩ := exists_inner hd hΩ hA hrS hrA
  have hta : ∀ x ∈ A, t * x * t⁻¹ = a * x * a⁻¹ := by
    intro x hx
    rw [hae, mul_inv_rev]
    calc a * e * x * (e⁻¹ * a⁻¹) = a * (e * x) * e⁻¹ * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [← he x hx]; group
  have ha2 : ∀ y ∈ A, (a * a) * y = y * (a * a) := by
    intro y hy
    have h1 : t * (t * y * t⁻¹) * t⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by
      rw [hta y hy, hta _ (A.mul_mem (A.mul_mem haA hy) (A.inv_mem haA))]
    have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [ht2]; group
    rw [h2] at h1
    calc a * a * y = a * (a * y * a⁻¹) * a⁻¹ * (a * a) := by group
      _ = y * (a * a) := by rw [← h1]
  have hanc : ∃ y ∈ A, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro x hx
    have h1 : t * x * t⁻¹ = x := by rw [hta x hx, hcon x hx]; group
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  set a' : ↥A := ⟨a, haA⟩ with ha'
  have hi2 : MulAut.conj a' * MulAut.conj a' = 1 := by
    rw [← map_mul]
    exact conj_eq_one_of_central fun y hy => ha2 y hy
  have hi1 : MulAut.conj a' ≠ 1 := by
    intro h
    obtain ⟨y, hyA, hay⟩ := hanc
    exact hay (central_of_conj_eq_one h y hyA)
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_comm_conj hA.1 a' hi2 hi1
  set x' : ↥A := g * a' * g⁻¹ * a'⁻¹ with hx'
  set x : Y := (x' : Y) with hx
  have hxA : x ∈ A := x'.2
  have hxdef : x = (g : Y) * a * (g : Y)⁻¹ * a⁻¹ := rfl
  have hxa : x * a = a * x := by
    refine no_twinK hd hΩ hinv hO hE2 hA hrS hrr hrA haA hta ha2 hxA ?_
    exact fun y hy => central_of_conj_eq_one h1 y hy
  have hxt : x * t = t * x := by
    have h5 : t * x * t⁻¹ = x := by rw [hta x hxA, ← hxa]; group
    calc x * t = t * x * t⁻¹ * t := by rw [h5]
      _ = t * x := by group
  have hxN := mem_normalizer_core_of_commK hd hΩ hinv hA hrS hrr hrA haA hta g.2 (by
    rw [← hxdef]; exact hxt)
  rw [← hxdef] at hxN
  have hrK : r ∈ tightCore R := mem_core_of_mem_S₀ hd hrS
  have hrR : r ∈ R := tightCore_le R hrK
  have hB : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  set ξ : Y := x * r * x⁻¹ * r⁻¹ with hξ
  have hξR : ξ ∈ R := by
    have h1 : x * r * x⁻¹ ∈ tightCore R := (Subgroup.mem_normalizer_iff.mp hxN r).mp hrK
    exact R.mul_mem (tightCore_le R h1) (R.inv_mem hrR)
  have hacts : ∀ y ∈ A, ξ * y * ξ⁻¹ = x * y * x⁻¹ := by
    intro y hy
    have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hxA)
    have hc := comm_of_ne hB hA hrA hu hy
    calc ξ * y * ξ⁻¹
        = x * ((r * x⁻¹ * r⁻¹) * y) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by rw [hξ]; group
      _ = x * y * x⁻¹ := by rw [hc]; group
  have hc0 : r * (x * x) = (x * x) * r :=
    commute_center_component hd hΩ hO hE2 hA hrS (A.mul_mem hxA hxA)
      fun y hy => (central_of_conj_eq_one h2 y hy).symm
  have hy'x : (r * x⁻¹ * r⁻¹) * x = x * (r * x⁻¹ * r⁻¹) :=
    comm_of_ne hB hA hrA (conj_mem_conjSub (A.inv_mem hxA)) hxA
  have hξξ : ξ * ξ = 1 := by
    have e1 : ξ * ξ = x * ((r * x⁻¹ * r⁻¹) * x) * (r * x⁻¹ * r⁻¹) := by rw [hξ]; group
    have e2 : r * (x * x)⁻¹ * r⁻¹ = (x * x)⁻¹ := by
      have : r * (x * x)⁻¹ = (x * x)⁻¹ * r := (show Commute r (x * x) from hc0).inv_right
      rw [this]; group
    rw [e1, hy'x]
    calc x * (x * (r * x⁻¹ * r⁻¹)) * (r * x⁻¹ * r⁻¹) = (x * x) * (r * (x * x)⁻¹ * r⁻¹) := by group
      _ = 1 := by rw [e2]; group
  by_cases hξ1 : ξ = 1
  · apply h3
    refine conj_eq_one_of_central (c := x') fun y hy => ?_
    have := hacts y hy
    rw [hξ1, inv_one, one_mul, mul_one] at this
    show x * y = y * x
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [← this]
  · have hord : orderOf ξ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hξξ) hξ1
    have hξt : ξ = t := eq_of_orderOf_eq_two hd hξR hord
    apply h4
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have := hacts y y.2
    rw [hξt, hta _ y.2] at this
    simp only [MulAut.conj_apply]
    exact this.symm

theorem conjSub_t_eqK (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hpair : ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype, r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) : conjSub t A = A := by
  by_contra htA
  have ht1 := Q8Datum.t_mul_t hd
  have htinv := Q8Datum.t_inv hd
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := hpair
  have key : ∀ r : Y, r * r = t → conjSub r A ≠ A := by
    intro r hrr heq
    apply htA
    rw [← hrr, conjSub_mul, heq, heq]
  have hex : ∃ r ∈ (S : Subgroup R).map R.subtype,
      conjSub r A ≠ A ∧ conjSub r A ≠ conjSub t A := by
    by_contra hno
    push Not at hno
    have e1 : conjSub r₁ A = conjSub t A := hno r₁ hr₁ (key r₁ h1)
    have e2 : conjSub r₂ A = conjSub t A := hno r₂ hr₂ (key r₂ h2)
    have hr12 : r₁ * r₂ ∈ (S : Subgroup R).map R.subtype := Subgroup.mul_mem _ hr₁ hr₂
    have e12 : conjSub (r₁ * r₂) A = conjSub t A := hno _ hr12 (key _ h12)
    apply htA
    have hr1t : r₁ * t = t * r₁ := mul_t_comm_of_sq h1
    symm
    calc A = conjSub (t * t) A := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub r₁ A) := by rw [conjSub_mul, e1]
      _ = conjSub (r₁ * t) A := by rw [← conjSub_mul, hr1t]
      _ = conjSub (r₁ * r₂) A := by rw [conjSub_mul, conjSub_mul, e2]
      _ = conjSub t A := e12
  obtain ⟨r, hrS, hrA, hrtA⟩ := hex
  have hrR : r ∈ R := Q8Datum.S₀_le hd hrS
  have hrsq : r * t = t * r :=
    Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (Q8Datum.S₀_le hd hrS))
  have hAt : CFSG.IsComponent (conjSub t A) := AscThmA.isComponent_conjSub hA t
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hArt : CFSG.IsComponent (conjSub (r * t) A) := AscThmA.isComponent_conjSub hA (r * t)
  have hrtne : conjSub (r * t) A ≠ A := by
    intro heq
    apply hrtA
    have h' : conjSub t (conjSub r A) = A := by rw [← conjSub_mul, ← hrsq, heq]
    calc conjSub r A = conjSub (t * t) (conjSub r A) := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub t (conjSub r A)) := conjSub_mul _ _ _
      _ = conjSub t A := by rw [h']
  refine TightA.false_of_solvable_covers (W := twinGroup R) hA.1
    (twinGroup_isSolvable hd hΩ) fun x hx => ?_
  set d : Y := x * (t * x * t⁻¹) with hd_def
  have hxt : t * x * t⁻¹ ∈ conjSub t A := conj_mem_conjSub hx
  have hdt : d * t = t * d := by
    have hc : (t * x * t⁻¹) * x = x * (t * x * t⁻¹) := (comm_of_ne hAt hA htA hxt hx)
    rw [hd_def]
    calc x * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [hc]
      _ = t * (x * (t * x * t⁻¹)) := by rw [htinv]; group
  refine ⟨d * r * d⁻¹ * r⁻¹,
    comm_mem_twinGroup hd hΩ hdt (hd.sylow_core.1 hrS), fun a ha => ?_⟩
  have hu1 : r * (t * x⁻¹ * t⁻¹) * r⁻¹ ∈ conjSub (r * t) A := by
    have := conj_mem_conjSub (n := r * t) (A.inv_mem hx)
    simpa [mul_assoc] using this
  have hu2 : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
  have hc1 := comm_of_ne hArt hA hrtne hu1 ha
  have hc2 := comm_of_ne hAr hA hrA hu2 ha
  have hc3 := comm_of_ne hAt hA htA hxt ha
  have e : d * r * d⁻¹ * r⁻¹ =
      x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) := by
    rw [hd_def]; group
  rw [e]
  calc x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) * a *
        (x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹))⁻¹
      = x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * ((r * x⁻¹ * r⁻¹) * a) *
          (r * x⁻¹ * r⁻¹)⁻¹ * (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        group
    _ = x * (t * x * t⁻¹) * ((r * (t * x⁻¹ * t⁻¹) * r⁻¹) * a) *
          (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc2]; group
    _ = x * ((t * x * t⁻¹) * a) * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc1]; group
    _ = x * a * x⁻¹ := by
        rw [hc3]; group

theorem conjSub_component_eq_of_casesK
    (hd : Q8TwinDatum R S t) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹) (hsq : ∀ (A : Subgroup Y) (s : Y), s ∈ (S : Subgroup R).map R.subtype → conjSub s A ≠ A → ∃ s' ∈ (S : Subgroup R).map R.subtype, s' * s' = t ∧ conjSub s' A ≠ A)
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) (htA : conjSub t A = A)
    (hcent : ∀ r ∈ (S : Subgroup R).map R.subtype, conjSub r A ≠ A →
      (∀ x ∈ A, x * t = t * x) → False)
    {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) : conjSub s A = A := by
  by_contra hsA
  obtain ⟨s', hs', h, hs'A⟩ := hsq A s hs hsA
  by_cases hc : ∀ x ∈ A, x * t = t * x
  · exact hcent s' hs' hs'A hc
  · exact false_of_innerK hd hΩ hO hE2 hinv hA hs' h hs'A hc

theorem thmA_twinK (hd : Q8TwinDatum R S t)
    (hpair : ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype, r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t) (hinv : ∀ r ∈ (S : Subgroup R).map R.subtype, ∃ s ∈ (S : Subgroup R).map R.subtype, s * r * s⁻¹ = r⁻¹) (hsq : ∀ (A : Subgroup Y) (s : Y), s ∈ (S : Subgroup R).map R.subtype → conjSub s A ≠ A → ∃ s' ∈ (S : Subgroup R).map R.subtype, s' * s' = t ∧ conjSub s' A ≠ A)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) :
    conjSub s A = A :=
  conjSub_component_eq_of_casesK hd hΩ hinv hsq hO hE2 hA
    (conjSub_t_eqK hd hΩ hpair hA)
    (fun _ hr hrA htA => Q8Datum.not_centralizes hd hΩ hA hr hrA htA) hs

theorem twinDichotomy_of_thmAK (hd : Q8TwinDatum R S t)
    (hpair : ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype, r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hThmA : (¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) →
      ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ s ∈ (S : Subgroup R).map R.subtype,
        conjSub s A = A) :
    TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t := by
  classical
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  right
  have hE2' : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P := hE2
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hd.sylow_core.2.1
  have hmem : ∀ X : Subgroup Y, S₀ ⊓ X ≠ ⊥ → t ∈ X := fun X hX =>
    (Subgroup.mem_inf.mp (Inner.mem_of_ne_bot hd (inf_le_left.trans (Subgroup.map_subtype_le _))
      (hS₀2.to_le inf_le_left) hX)).2
  have h613 : ∀ X : Subgroup Y, X.Normal → t ∉ X → S₀ ≤ Subgroup.centralizer (X : Set Y) := by
    intro X hXn htX
    have hSX : S₀ ⊓ X = ⊥ := by
      by_contra hne
      exact htX (hmem X hne)
    have h1 := comm613Gen_normal hΩ (Inner.S₀_mem_RSet hd) hXn hSX
    have h2 : oddCoreOf X = ⊥ := by
      have := hXn
      rw [AscThmA.oddCoreOf_eq_inf, hO', inf_bot_eq]
    rw [h2, le_bot_iff] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hcen : ∀ X : Subgroup Y, X.Normal → S₀ ≤ Subgroup.centralizer (X : Set Y) →
      X ≤ Subgroup.center Y := by
    intro X hXn hSC
    have htop : Subgroup.centralizer (X : Set Y) = ⊤ := eq_top_of_conj hd hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ X := by simpa using hXn.conj_mem p hp y⁻¹
      have := Subgroup.mem_centralizer_iff.mp (hSC hx) _ hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [this]
        _ = x * p := by group
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (X : Set Y) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm
  have hFZ : genFittingFitting Y ≤ Subgroup.center Y := by
    have hFn : (genFittingFitting Y).Normal := genFittingFitting_normal
    have hF2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO'
    exact hcen _ hFn (h613 _ hFn fun h => hE2' ⟨_, hFn, hF2, h⟩)
  have hThmA : ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ s ∈ S₀, conjSub s A = A :=
    hThmA hE2'
  have hnorm : ∀ A : Subgroup Y, CFSG.IsComponent A → A.Normal := by
    intro A hA
    have htop : Subgroup.normalizer (A : Set Y) = ⊤ := eq_top_of_conj hd hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      refine mem_normalizer_iff_conjSub_eq.mpr ?_
      have h1 := hThmA _ (AscThmA.isComponent_conjSub hA y⁻¹) _ hx
      calc conjSub x A = conjSub y (conjSub (y⁻¹ * x * y) (conjSub y⁻¹ A)) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = A := by rw [h1, conjSub_conjSub_inv]
    exact Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := hpair
  have hnab : r₁ * r₂ ≠ r₂ * r₁ := by
    intro hc
    have e : (r₁ * r₂) * (r₁ * r₂) = 1 := by
      calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
        _ = r₁ * (r₁ * r₂) * r₂ := by rw [hc]
        _ = (r₁ * r₁) * (r₂ * r₂) := by group
        _ = 1 := by rw [h1, h2, Inner.t_mul_t hd]
    have ht1 : t = 1 := h12.symm.trans e
    have := hd.order
    rw [ht1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hEn : (layer Y).Normal := AscThmA.normal_layer
  have htE : t ∈ layer Y := by
    by_contra htE
    have hSE := h613 (layer Y) hEn htE
    have hSF : S₀ ≤ Subgroup.centralizer (genFittingFStar Y : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      show genFittingFitting Y ⊔ genFittingLayer Y ≤ _
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro s _
        exact (Subgroup.mem_center_iff.mp (hFZ hx)) s
      · rw [genFittingLayer_eq_layer, ← Subgroup.le_centralizer_iff]
        exact hSE
    have hSFs : S₀ ≤ genFittingFStar Y :=
      hSF.trans (CFSG.Adapters.generalized_fitting_self_centralizing Y)
    exact hnab (Subgroup.mem_centralizer_iff.mp (hSF hr₂) r₁ (hSFs hr₁))
  have hL : ∃ L : Subgroup Y, CFSG.IsComponent L ∧ t ∈ L ∧ ∃ x ∈ L, x * t ≠ t * x := by
    by_contra hno
    push Not at hno
    have hcomp : ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ x ∈ A, x * t = t * x := by
      intro A hA
      by_cases htA : t ∈ A
      · exact hno A hA htA
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mp (h613 A (hnorm A hA) htA hd.mem) x hx
    have hEt : layer Y ≤ Subgroup.centralizer ({t} : Set Y) := by
      show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ _
      exact sSup_le fun A hA x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomp A hA x hx)
    have htC : t ∈ Subgroup.centralizer (layer Y : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEt hh)
    exact hE2' ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup hO', htE, htC⟩
  obtain ⟨L, hLc, htL, hLnc⟩ := hL
  have hLn := hnorm L hLc
  have huniq : ∀ A : Subgroup Y, CFSG.IsComponent A → A = L := by
    intro A hA
    by_contra hAL
    have htA : t ∉ A := by
      intro htA
      obtain ⟨x, hxL, hxt⟩ := hLnc
      exact hxt (comm_of_ne hLc hA (Ne.symm hAL) hxL htA)
    have hAn := hnorm A hA
    have hAZ := hcen A hAn (h613 A hAn htA)
    obtain ⟨a, b, hab⟩ := hA.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hAZ b'.2) (a' : Y))
  have hlayer : layer Y = L := by
    refine le_antisymm ?_ (CFSG.LocalCores.component_le_layer hLc)
    show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ L
    exact sSup_le fun A hA => (huniq A hA).le
  have hFstar : genFittingFStar Y = genFittingFitting Y ⊔ L := by
    show genFittingFitting Y ⊔ genFittingLayer Y = _
    rw [genFittingLayer_eq_layer, hlayer]
  by_cases hFL : genFittingFitting Y ≤ L
  · left
    have e : genFittingFStar Y = L := by rw [hFstar, sup_eq_right.mpr hFL]
    show CFSG.Open.IsQuasisimple ↥(genFittingFStar Y)
    rw [e]
    exact ((CFSG.isComponent_iff_open L).mp hLc).2.2
  · right
    exact ⟨L, hLc, hLn, hlayer, htL, hLnc, hFZ, hFL⟩

theorem twinDichotomy_ofK (hd : Q8TwinDatum R S t) {k : ℕ} (hk : 3 ≤ k)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (k - 2)))) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) :
    TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t :=
  twinDichotomy_of_thmAK hd (exists_S₀_pairK hd hk hq) hgen hO hΩ fun hE2 _ hA _ hs =>
    thmA_twinK hd (exists_S₀_pairK hd hk hq) (inv_in_S₀K hd hk hq)
      (fun _ _ hs hsA => exists_sq_of_conjSub_neK hd hk hq hs hsA) hΩ hO hE2 hA hs

section Step

@[expose] def Thm1RTwinCoreAtR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    IsSimpleGroup ↥(genFittingFStar Y) → (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) → TightSelfGen R →
      TightOddFree Y → HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R) →
      TwinE4 Y

theorem thm1RTwinBelowR_succ {r n : ℕ} (hr : 3 ≤ r) (hB : Thm1RTwinBelowR r n)
    (hcore : Thm1RTwinCoreAtR r n) : Thm1RTwinBelowR r (n + 1) := by
  intro Y _ _ hlt R S t hd hq8 hgen hO hΩ hA htw
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
  · exact hB Y hlt' R S t hd hq8 hgen hO hΩ hA htw
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  have hE2' : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P := hE2
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  right
  have hNn : (genFittingFitting Y).Normal := genFittingFitting_normal
  have hN2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO'
  have htN : t ∉ genFittingFitting Y := fun h => hE2' ⟨_, hNn, hN2, h⟩
  have hNc : genFittingFitting Y ≤ Subgroup.center Y :=
    TwinRed.le_center_of_normal_two hd hgen hΩ hNn hN2 htN
  by_cases hN1 : genFittingFitting Y = ⊥
  · rcases twinDichotomy_ofK hd hr hq8 hgen hO hΩ with h | h | ⟨L, -, -, -, -, -, -, hFL⟩
    · exact absurd h hE2
    · obtain ⟨hs, hnab⟩ := TwinRed.fstar_simple_of_fitting_eq_bot h hN1
      exact hcore Y heq hs hnab R S t hd hq8 hgen hO hΩ hA htw
    · exact absurd (hN1 ▸ bot_le) hFL
  · have : (genFittingFitting Y).Normal := hNn
    set N := genFittingFitting Y with hNdef
    have hRN : R ⊓ N = ⊥ := TwinRed.inf_eq_bot hd hN2 htN
    have h0 : tightCore R ⊓ N = ⊥ := TwinRed.core_inf_eq_bot hd hN2 htN
    have hlt2 : Nat.card (Y ⧸ N) < n := heq ▸ TwistQ.card_lt hN1
    rcases hB (Y ⧸ N) hlt2 (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
      (QuotientGroup.mk' N t) (TwinRed.q8TwinDatum_map hd hRN htN)
      ⟨(TwistQ.sylowMapEquiv hRN S).symm.trans hq8.some⟩
      (TwinRed.selfGen_map hRN hgen) (TwistQ.oddFree hNc hN2 hO')
      (TwinRed.hyp_map hΩ hNc hRN h0) (TwinRed.aEmpty_map hΩ hA hNc hRN h0)
      (TwinRed.twin_map hΩ hNc hRN h0 htw) with h | h
    · exact absurd (TwistQ.inO2_of hN2 h) hE2
    · exact TwinRed.twinE4_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2) h

structure TwinCoreHypR (r n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (S : Sylow 2 R) (t : Y) : Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  below : CIT3Below n
  tbelow : TightBelowR r n
  twinBelow : Thm1RTwinBelowR r n
  datum : Q8TwinDatum R S t
  quat : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  gen : TightSelfGen R
  oddFree : TightOddFree Y
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

@[expose] def TwinCoreConnR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypR r n Y R S t → Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      False

@[expose] def TwinCoreDiscPerpR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypR r n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) ≠
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) → False

@[expose] def TwinCorePerpR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypR r n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) → False

theorem thm1RTwinCoreAtR_of_cases {r n : ℕ} (hA : TwinCoreConnR r n) (hB : TwinCoreDiscPerpR r n)
    (hC : TwinCorePerpR r n) (hBelow : CIT3Below n) (hT : TightBelowR r n)
    (hL : Thm1RTwinBelowR r n) : Thm1RTwinCoreAtR r n := by
  intro Y _ _ hcard hF hnab R S t hd hq hg hO hΩ hAe htw
  have h : TwinCoreHypR r n Y R S t := ⟨hcard, hF, hnab, hBelow, hT, hL, hd, hq, hg, hO, hΩ, hAe, htw⟩
  exfalso
  by_cases hD : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  · exact hA Y R S t h hD
  · by_cases hP : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)
    · exact hC Y R S t h hD hP
    · exact hB Y R S t h hD hP

@[expose] def NoQuatE4 (r : ℕ) : Prop :=
  ∀ (Q : Type) [Group Q], (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) →
    ∀ f : QuaternionGroup (2 ^ (r - 2)) →* Q, ¬ Function.Injective f

theorem tightInO2_of_twinE4 {r : ℕ} (hno : NoQuatE4 r) (hd : Q8TwinDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (h : TwinE4 Y) :
    TightInO2 t := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  by_cases ht : t ∈ f.ker
  · exact ⟨f.ker, MonoidHom.normal_ker f, hf2, ht⟩
  · exfalso
    obtain ⟨e⟩ := hq
    let ι : ↥(S : Subgroup R) →* Y := R.subtype.comp (S : Subgroup R).subtype
    have hι : Function.Injective ι := R.subtype_injective.comp (Subgroup.subtype_injective _)
    have hinj : Function.Injective (f.comp ι) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      by_contra hx1
      have hxS : (ι x) ∈ (S : Subgroup R).map R.subtype := ⟨x, x.2, rfl⟩
      have hy1 : ι x ≠ 1 := fun h => hx1 (hι (h.trans (map_one ι).symm))
      have hPS : Subgroup.zpowers (ι x) ≤ (S : Subgroup R).map R.subtype :=
        Subgroup.zpowers_le.mpr hxS
      have hP2 : IsPGroup 2 ↥(Subgroup.zpowers (ι x)) := (hd.sylow_core.2.1).to_le hPS
      have hPR : Subgroup.zpowers (ι x) ≤ R := hPS.trans (Subgroup.map_subtype_le _)
      have hPb : Subgroup.zpowers (ι x) ≠ ⊥ := fun h => hy1 (Subgroup.zpowers_eq_bot.mp h)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Q8Datum.mem_of_ne_bot hd hPR hP2 hPb)
      apply ht
      rw [MonoidHom.mem_ker, ← hk, map_zpow]
      have h1 : f (ι x) = 1 := hx
      rw [h1, one_zpow]
    exact hno Q hQ ((f.comp ι).comp e.symm.toMonoidHom) (hinj.comp e.symm.injective)

@[expose] def NoQ16E4 : Prop :=
  ∀ (Q : Type) [Group Q], (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) → NoQ16 Q

theorem noQuatE4_of_noQ16E4 {r : ℕ} (hr : 4 ≤ r) (h : NoQ16E4) : NoQuatE4 r :=
  fun Q _ hQ f hf => by
    obtain ⟨x, y, hxy⟩ := exists_q16Pair_of_injective hr f hf
    exact h Q hQ x y hxy

theorem tightInO2_of_twinE4' {r : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4) (hd : Q8TwinDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (h : TwinE4 Y) :
    TightInO2 t :=
  tightInO2_of_twinE4 (noQuatE4_of_noQ16E4 hr h4) hd hq h

@[expose] def DatumOutcomeR {Y : Type} [Group Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) :
    Prop :=
  (HasTwin R → TightInO2 t ∨ TwinE4 Y) ∧ (¬ HasTwin R → TightEx Y R S t)

theorem datumOutcomeR_of_IH {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinBelowR r n)
    (hB : TightBelowR r n) (hlt : Nat.card Y < n)
    (hd : Q8TwinDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (htc : tightCore R = R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    DatumOutcomeR R S t := by
  refine ⟨fun htw => hT Y hlt R S t hd hq hgen hO hΩ hA htw, fun hno => ?_⟩
  have hzK : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
  have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R} := by
    ext K
    constructor
    · intro hK
      by_contra hne
      exact hno ⟨K, hK, hne⟩
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
  have hnormal := (twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
    (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
  rw [htc] at hnormal
  have hdt := hd.toTightDatum hnormal
  exact (hB Y hlt R S t hdt ⟨hq, hgen, hO⟩).resolve_right
    (not_goodThreeElement_of_four_le hr hdt hq)

theorem qTwinDatum_of_isPGroupK {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr : 3 ≤ r)
    {R : Subgroup Y} (hR : IsPGroup 2 R) (S : Sylow 2 R)
    {t : Y} (ht : IsUniqueInvolution R t)
    (hq8 : Nonempty (↥R ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Q8TwinDatum R S t ∧ Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hS := sylow_eq_top hR S
  let e : ↥(S : Subgroup R) ≃* ↥R :=
    (MulEquiv.subgroupCongr hS).trans Subgroup.topEquiv
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := ⟨e.trans hq8.some⟩
  refine ⟨⟨⟨r, hr, hq⟩, ?_, ?_, ?_, ?_⟩, hq⟩
  · have : (⟨t, ht.mem⟩ : R) ∈ (S : Subgroup R) := by rw [hS]; exact Subgroup.mem_top _
    exact ⟨⟨t, ht.mem⟩, this, rfl⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (ht.commute_of_mem hw).symm
  · exact hR.to_quotient _

end Step

end CFSG.CGT.PushingUpLit.SolKNA.R4
