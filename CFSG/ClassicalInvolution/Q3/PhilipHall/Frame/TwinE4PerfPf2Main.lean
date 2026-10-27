module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfQ8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

set_option linter.unusedSectionVars false
open scoped commutatorElement

@[expose] def Fin3ActsT (Q : Type) [Group Q] : Prop :=
  ∀ (R : Subgroup Q) (t : Q), Nonempty (↥R ≃* QuaternionGroup 2) → IsUniqueInvolution R t →
    (∀ c ∈ Subgroup.centralizer ({t} : Set Q), conjSub c R = R ∨
      ∀ x ∈ R, ∀ y ∈ conjSub c R, x * y = y * x) →
    ∃ x : Q, x * t = t * x ∧ x ^ 3 = 1 ∧ (∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      ∃ r ∈ R, x * r * x⁻¹ * r⁻¹ ≠ 1 ∧ x * r * x⁻¹ * r⁻¹ ≠ t

@[expose] def Fin3ActsModels : Prop :=
  (∀ (Q : Type) [Group Q] [Finite Q], CFSG.Blueprint.LieModel Q .PSp 3 2 1 → Fin3ActsT Q) ∧
  (∀ (Q : Type) [Group Q] [Finite Q], CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1 → Fin3ActsT Q)

section General

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {π : Set (Subgroup G)} {z g : G}

theorem commute_of_inv {J : Subgroup G} {u : G} (h : IsUniqueInvolution J u) {x : G} (hx : x ∈ J) :
    x * u = u * x := by
  have hmem : x * u * x⁻¹ ∈ J := J.mul_mem (J.mul_mem hx h.mem) (J.inv_mem hx)
  have hsq : x * u * x⁻¹ * (x * u * x⁻¹) = 1 := by
    calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  rcases h.unique _ hmem hsq with h1 | h1
  · exfalso
    apply h.ne_one
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [h1]

theorem le_normalizer_of_inv_commute (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) (hJz : ∀ v ∈ J, v * z = z * v)
    (hnab : ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a) : J ≤ Subgroup.normalizer (K : Set G) := by
  have hnc : ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) → v ∈ Subgroup.normalizer (K : Set G) :=
    fun v hv hnv => hΩ.omega5 K hK J hJ hKJ z hz v hv hnv
      ((h2 J hJ).to_le (Subgroup.zpowers_le.mpr hv)) (hJz v hv)
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hna : ∀ u ∈ J, (¬ ∀ w ∈ J, u * w = w * u) → u ∈ Subgroup.normalizer (K : Set G) := hnc
  intro v hv
  by_cases hvn : ∀ w ∈ J, v * w = w * v
  ·
    by_cases hac : ∀ w ∈ J, a * w = w * a
    · exact absurd (hac b hb) hab
    · have hva : ¬ ∀ w ∈ J, (v * a) * w = w * (v * a) := by
        intro hall
        apply hac
        intro w hw
        have h1 := hall w hw
        have h2 := hvn w hw
        have h3 : v * (a * w) = v * (w * a) := by
          calc v * (a * w) = (v * a) * w := by group
            _ = w * (v * a) := h1
            _ = (w * v) * a := by group
            _ = (v * w) * a := by rw [h2]
            _ = v * (w * a) := by group
        exact mul_left_cancel h3
      have h1 := hnc (v * a) (J.mul_mem hv ha) hva
      have h2 := hnc a ha hac
      have := (Subgroup.normalizer (K : Set G)).mul_mem h1 ((Subgroup.normalizer (K : Set G)).inv_mem h2)
      simpa using this
  · exact hnc v hv hvn

theorem twin_clause_of_cfg (h : Cfg' Ω K π z g) {w : G}
    (hR : IsUniqueInvolution (conjSub g K) w) (hnab : ∃ a ∈ conjSub g K, ∃ b ∈ conjSub g K, a * b ≠ b * a)
    {s : G} (hs : s ∈ piGen π) {q : G}
    (hq : w⁻¹ * (s * w * s⁻¹) = q) (hqc : ∀ y ∈ piGen π, y * q = q * y) :
    conjSub s (conjSub g K) = conjSub g K ∨ Commutes (conjSub g K) (conjSub s (conjSub g K)) := by
  by_cases he : conjSub s (conjSub g K) = conjSub g K
  · exact Or.inl he
  right
  have hRΩ := h.R_mem
  have hΩ' : conjSub s (conjSub g K) ∈ Ω := h.std.graph.conjMem _ hRΩ s
  have hne : conjSub g K ≠ conjSub s (conjSub g K) := fun e => he e.symm
  have hR' : IsUniqueInvolution (conjSub s (conjSub g K)) (s * w * s⁻¹) := hR.conj s
  have hw' : s * w * s⁻¹ = w * q := by rw [← hq]; group
  have hRX : conjSub g K ≤ piGen π := h.R_le
  have hR'X : conjSub s (conjSub g K) ≤ piGen π := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have := (piGen π).mul_mem ((piGen π).mul_mem hs (hRX hy)) ((piGen π).inv_mem hs)
    rwa [show s * (s⁻¹ * y * s) * s⁻¹ = y by group] at this
  have hJw : ∀ v ∈ conjSub s (conjSub g K), v * w = w * v := by
    intro v hv
    have h1 := commute_of_inv hR' hv
    rw [hw'] at h1
    have h2 := hqc v (hR'X hv)
    have h3 : v * w * q = w * v * q := by
      calc v * w * q = v * (w * q) := by group
        _ = (w * q) * v := h1
        _ = w * (q * v) := by group
        _ = w * (v * q) := by rw [← h2]
        _ = w * v * q := by group
    exact mul_right_cancel h3
  have hJw' : ∀ v ∈ conjSub g K, v * (s * w * s⁻¹) = (s * w * s⁻¹) * v := by
    intro v hv
    rw [hw']
    have h1 := commute_of_inv hR hv
    have h2 := hqc v (hRX hv)
    calc v * (w * q) = (v * w) * q := by group
      _ = (w * v) * q := by rw [h1]
      _ = w * (v * q) := by group
      _ = w * (q * v) := by rw [h2]
      _ = (w * q) * v := by group
  have hnab' : ∃ a ∈ conjSub s (conjSub g K), ∃ b ∈ conjSub s (conjSub g K), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    refine ⟨s * a * s⁻¹, conj_mem_conjSub ha, s * b * s⁻¹, conj_mem_conjSub hb, fun hh => hab ?_⟩
    have : s * (a * b) * s⁻¹ = s * (b * a) * s⁻¹ := by
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = (s * b * s⁻¹) * (s * a * s⁻¹) := hh
        _ = s * (b * a) * s⁻¹ := by group
    have h5 := congrArg (fun y => s⁻¹ * y * s) this
    simpa [mul_assoc] using h5
  have n1 := le_normalizer_of_inv_commute h.std.hyp h.std.two hRΩ hΩ' hne hR hJw hnab'
  have n2 := le_normalizer_of_inv_commute h.std.hyp h.std.two hΩ' hRΩ hne.symm hR' hJw' hnab
  exact commutes_of_mutual_normalizer h.std.hyp h.std.two hRΩ hΩ' hne n2 n1

theorem members_le_commutator_of_cfg2 (h : Cfg' Ω K π z g) (hF3 : Fin3ActsModels) {w : G}
    (hw : IsUniqueInvolution (conjSub g K) w) (hwX : w ∈ piGen π)
    {Q : Type} [Group Q] (F : ↥(piGen π) →* Q) (hFs : Function.Surjective F)
    (hker : IsPGroup 2 ↥F.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)
    (ht : F ⟨w, hwX⟩ ≠ 1) : ∀ J ∈ π, J ≤ ⁅piGen π, piGen π⁆ := by
  classical
  have hcen := kernel_le_center_of_cfg h hw hwX F hker ht
  have : Finite Q := Finite.of_surjective F hFs
  have hRΩ := h.R_mem
  have hRX : conjSub g K ≤ piGen π := h.R_le
  have hR2 : IsPGroup 2 ↥(conjSub g K) := h.std.two _ hRΩ
  let e : ↥(conjSub g K) ≃* QuaternionGroup 2 := (conjSubEquiv K g).symm.trans h.q8.some
  set R := conjSub g K with hRdef
  have hR : IsUniqueInvolution R w := hw
  let T0 : ↥(piGen π) := ⟨w, hwX⟩
  have Rinj : ∀ a b : ↥(piGen π), (a : G) ∈ R → (b : G) ∈ R → F a = F b → a = b := by
    intro a b ha hb hab
    by_contra hne
    have hc : a⁻¹ * b ∈ F.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hcR : ((a⁻¹ * b : ↥(piGen π)) : G) ∈ R := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact R.mul_mem (R.inv_mem ha) hb
    have hne1 : ((a⁻¹ * b : ↥(piGen π)) : G) ≠ 1 := by
      intro h1
      exact hne (inv_mul_eq_one.mp (Subtype.ext (by simpa using h1)))
    have hinf : R ⊓ F.ker.map (piGen π).subtype ≠ ⊥ := by
      intro hbot
      have : ((a⁻¹ * b : ↥(piGen π)) : G) ∈ R ⊓ F.ker.map (piGen π).subtype :=
        ⟨hcR, ⟨_, hc, rfl⟩⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hne1 this
    obtain ⟨p, hp, hpe⟩ := mem_of_inf_ne_bot hR2 hR hinf
    apply ht
    have : p = T0 := Subtype.ext hpe
    rw [this] at hp
    exact hp
  let φ : ↥R →* Q := F.comp (Subgroup.inclusion hRX)
  have hφ : Function.Injective φ := by
    intro a b hab
    have := Rinj (Subgroup.inclusion hRX a) (Subgroup.inclusion hRX b) a.2 b.2 hab
    exact Subgroup.inclusion_injective hRX this
  let Rb : Subgroup Q := φ.range
  let tb : Q := F T0
  have hRb_q8 : Nonempty (↥Rb ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hφ).symm.trans e⟩
  have hφt : φ ⟨w, hR.mem⟩ = tb := rfl
  have hRb_inv : IsUniqueInvolution Rb tb := by
    refine ⟨⟨⟨w, hR.mem⟩, hφt⟩, ht, ?_, ?_⟩
    · show F T0 * F T0 = 1
      rw [← map_mul]
      have : T0 * T0 = 1 := Subtype.ext hR.sq
      rw [this, map_one]
    · rintro y ⟨r, rfl⟩ hy
      have h1 : φ (r * r) = φ 1 := by rw [map_mul, hy, map_one]
      have h2 := hφ h1
      have h3 : ((r : ↥R) : G) * (r : G) = 1 := by
        have := congrArg Subtype.val h2
        simpa using this
      rcases hR.unique _ r.2 h3 with h4 | h4
      · left
        have : r = 1 := Subtype.ext h4
        rw [this, map_one]
      · right
        have : r = ⟨w, hR.mem⟩ := Subtype.ext h4
        rw [this]
        rfl
  have hnab : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
    refine ⟨(e.symm (QuaternionGroup.a 1) : G), (e.symm (QuaternionGroup.a 1)).2,
      (e.symm (QuaternionGroup.xa 0) : G), (e.symm (QuaternionGroup.xa 0)).2, fun hh => ?_⟩
    have h1 : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
        e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext hh
    have h2 := congrArg e h1
    rw [map_mul, map_mul] at h2
    simp only [MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide +kernel)
  have htwQ : ∀ c ∈ Subgroup.centralizer ({tb} : Set Q), conjSub c Rb = Rb ∨
      ∀ x ∈ Rb, ∀ y ∈ conjSub c Rb, x * y = y * x := by
    intro c hc
    have hc' : c * tb = tb * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    obtain ⟨c', rfl⟩ := hFs c
    have hq : T0⁻¹ * (c' * T0 * c'⁻¹) ∈ F.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
      show tb⁻¹ * (F c' * tb * (F c')⁻¹) = 1
      rw [hc', mul_inv_cancel_right, inv_mul_cancel]
    have hqc : ∀ y : ↥(piGen π), y * (T0⁻¹ * (c' * T0 * c'⁻¹)) = (T0⁻¹ * (c' * T0 * c'⁻¹)) * y :=
      fun y => Subgroup.mem_center_iff.mp (hcen hq) y
    have hclause := twin_clause_of_cfg h hR hnab (s := (c' : G)) c'.2 (q := ((T0⁻¹ * (c' * T0 * c'⁻¹) : ↥(piGen π)) : G))
      (by simp [T0]) (fun y hy => by simpa using congrArg Subtype.val (hqc ⟨y, hy⟩))
    rcases hclause with h1 | h1
    · left
      ext y
      rw [mem_conjSub_iff]
      constructor
      · rintro ⟨r, hr⟩
        have hy : y = F c' * φ r * (F c')⁻¹ := by rw [hr]; group
        have hm : (c' : G) * (r : G) * (c' : G)⁻¹ ∈ R := by
          have : (c' : G) * (r : G) * (c' : G)⁻¹ ∈ conjSub (c' : G) R := by
            rw [mem_conjSub_iff]
            have e1 : (c' : G)⁻¹ * ((c' : G) * (r : G) * (c' : G)⁻¹) * (c' : G) = (r : G) := by group
            rw [e1]; exact r.2
          rwa [h1] at this
        refine ⟨⟨_, hm⟩, ?_⟩
        rw [hy]
        show F (Subgroup.inclusion hRX ⟨_, hm⟩) = F c' * F (Subgroup.inclusion hRX r) * (F c')⁻¹
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
      · rintro ⟨r, rfl⟩
        have hm : (c' : G)⁻¹ * (r : G) * (c' : G) ∈ R := by
          have : (r : G) ∈ conjSub (c' : G) R := by rw [h1]; exact r.2
          rwa [mem_conjSub_iff] at this
        refine ⟨⟨_, hm⟩, ?_⟩
        show F (Subgroup.inclusion hRX ⟨_, hm⟩) = (F c')⁻¹ * F (Subgroup.inclusion hRX r) * F c'
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
    · right
      rintro _ ⟨r, rfl⟩ y hy
      rw [mem_conjSub_iff] at hy
      obtain ⟨r2, hr2⟩ := hy
      have hy' : y = F c' * φ r2 * (F c')⁻¹ := by rw [hr2]; group
      have hm : (c' : G) * (r2 : G) * (c' : G)⁻¹ ∈ conjSub (c' : G) R := by
        rw [mem_conjSub_iff]
        have e1 : (c' : G)⁻¹ * ((c' : G) * (r2 : G) * (c' : G)⁻¹) * (c' : G) = (r2 : G) := by group
        rw [e1]; exact r2.2
      have := h1 _ r.2 _ hm
      rw [hy']
      show F (Subgroup.inclusion hRX r) * (F c' * F (Subgroup.inclusion hRX r2) * (F c')⁻¹) =
        (F c' * F (Subgroup.inclusion hRX r2) * (F c')⁻¹) * F (Subgroup.inclusion hRX r)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext this
  have hF3Q : Fin3ActsT Q := hQ.elim (fun h' => hF3.1 Q h') (fun h' => hF3.2 Q h')
  obtain ⟨xb, hxt, hx3, hxR, rb, hrb, hn1, hn2⟩ := hF3Q Rb tb hRb_q8 hRb_inv htwQ
  obtain ⟨r₁, hr₁⟩ := hrb
  obtain ⟨x', hx'F, hx'3⟩ := exists_lift_pow F hker (m := 3) (by decide) hx3
    (MonoidHom.mem_range.mpr (hFs xb))
  have hx'T : x' * T0 * x'⁻¹ = T0 := by
    refine conj_eq_of_central F hker hcen (m := 3) (by decide) hx'3 ?_
    rw [map_mul, map_mul, map_inv, hx'F]
    show xb * tb * xb⁻¹ = tb
    rw [hxt, mul_inv_cancel_right]
  have hxX : (x' : G) ∈ piGen π := x'.2
  have hx3G : (x' : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hx'3
  have hxtG : (x' : G) * w * (x' : G)⁻¹ = w := by simpa using congrArg Subtype.val hx'T
  have hconjin : ∀ r : G, (x' : G)⁻¹ * ((x' : G) * r * (x' : G)⁻¹) * (x' : G) = r := by
    intro r; group
  have hconjR : conjSub (x' : G) R = R := by
    by_contra hne
    have hΩ : conjSub (x' : G) R ∈ Ω := h.std.graph.conjMem _ hRΩ _
    have hne' : R ≠ conjSub (x' : G) R := fun e => hne e.symm
    obtain ⟨h4a, h4b⟩ := h.std.hyp.omega4 R hRΩ _ hΩ hne'
    have hwR : w ∈ conjSub (x' : G) R := by
      rw [mem_conjSub_iff]
      have : (x' : G)⁻¹ * w * (x' : G) = w := by
        have h0 := hconjin w
        rwa [hxtG] at h0
      rw [this]; exact hR.mem
    have hv : padicValNat 2 (Nat.card ↥(R ⊓ conjSub (x' : G) R)) = 1 := by
      refine le_antisymm h4a ?_
      have hdvd : 2 ∣ Nat.card ↥(R ⊓ conjSub (x' : G) R) := by
        let τ : ↥(R ⊓ conjSub (x' : G) R) := ⟨w, hR.mem, hwR⟩
        have hτ : orderOf τ = 2 := by
          apply orderOf_eq_prime
          · apply Subtype.ext
            show w ^ 2 = 1
            rw [pow_two]; exact hR.sq
          · intro h1; exact hR.ne_one (congrArg Subtype.val h1)
        rw [← hτ]; exact orderOf_dvd_natCard τ
      exact one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
    have hcomm := h4b hv
    rw [oddCoreOf_eq_bot_of_isPGroup hR2, oddCoreOf_eq_bot_of_isPGroup (h.std.two _ hΩ),
      inf_bot_eq, le_bot_iff] at hcomm
    have hRc : R ≤ Subgroup.centralizer (conjSub (x' : G) R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    let a1 : ↥R := e.symm (QuaternionGroup.a 1)
    let b2 : ↥R := e.symm (QuaternionGroup.xa 0)
    have hnc : (a1 : G) * (b2 : G) ≠ (b2 : G) * (a1 : G) := by
      intro hh
      have h1 : a1 * b2 = b2 * a1 := Subtype.ext hh
      have h2 := congrArg e h1
      rw [map_mul, map_mul] at h2
      simp only [a1, b2, MulEquiv.apply_symm_apply] at h2
      exact absurd h2 (by decide +kernel)
    have hb2 : φ b2 ∈ Rb := ⟨b2, rfl⟩
    have hy1 := hxR _ hb2
    have hy2 := hxR _ hy1
    obtain ⟨r0, hr0⟩ := hy2
    let c : ↥(piGen π) := x' * Subgroup.inclusion hRX r0 * x'⁻¹
    have hFc : F c = F (Subgroup.inclusion hRX b2) := by
      show F (x' * Subgroup.inclusion hRX r0 * x'⁻¹) = φ b2
      rw [map_mul, map_mul, map_inv, hx'F]
      show xb * φ r0 * xb⁻¹ = φ b2
      rw [hr0]
      have h111 : xb * xb * xb = 1 := by rw [← pow_three']; exact hx3
      calc xb * (xb * (xb * φ b2 * xb⁻¹) * xb⁻¹) * xb⁻¹
          = (xb * xb * xb) * φ b2 * (xb * xb * xb)⁻¹ := by group
        _ = φ b2 := by rw [h111]; group
    obtain ⟨p, hpdef⟩ : ∃ p : ↥(piGen π), p = (Subgroup.inclusion hRX b2)⁻¹ * c := ⟨_, rfl⟩
    have hp : p ∈ F.ker := by
      rw [hpdef, MonoidHom.mem_ker, map_mul, map_inv, hFc, inv_mul_cancel]
    have hcb : c = Subgroup.inclusion hRX b2 * p := by rw [hpdef]; group
    have hpc := Subgroup.mem_center_iff.mp (hcen hp) (Subgroup.inclusion hRX a1)
    have hcR : (c : G) ∈ conjSub (x' : G) R := by
      rw [mem_conjSub_iff]
      have : (x' : G)⁻¹ * (c : G) * (x' : G) = (r0 : G) := by
        show (x' : G)⁻¹ * ((x' : G) * (r0 : G) * (x' : G)⁻¹) * (x' : G) = (r0 : G)
        group
      rw [this]; exact r0.2
    have hcomm' := Subgroup.mem_centralizer_iff.mp (hRc a1.2) _ hcR
    have e1 : c * Subgroup.inclusion hRX a1 = Subgroup.inclusion hRX a1 * c := Subtype.ext hcomm'
    rw [hcb] at e1
    have e2 : Subgroup.inclusion hRX b2 * Subgroup.inclusion hRX a1 =
        Subgroup.inclusion hRX a1 * Subgroup.inclusion hRX b2 := by
      apply mul_right_cancel (b := p)
      calc Subgroup.inclusion hRX b2 * Subgroup.inclusion hRX a1 * p
          = Subgroup.inclusion hRX b2 * (Subgroup.inclusion hRX a1 * p) := by rw [mul_assoc]
        _ = Subgroup.inclusion hRX b2 * (p * Subgroup.inclusion hRX a1) := by rw [hpc]
        _ = Subgroup.inclusion hRX b2 * p * Subgroup.inclusion hRX a1 := by rw [mul_assoc]
        _ = Subgroup.inclusion hRX a1 * (Subgroup.inclusion hRX b2 * p) := e1
        _ = Subgroup.inclusion hRX a1 * Subgroup.inclusion hRX b2 * p := by rw [mul_assoc]
    exact hnc (congrArg Subtype.val e2).symm
  have hxR' : ∀ r ∈ R, (x' : G) * r * (x' : G)⁻¹ ∈ R := by
    intro r hr
    have : (x' : G) * r * (x' : G)⁻¹ ∈ conjSub (x' : G) R := by
      rw [mem_conjSub_iff, hconjin]; exact hr
    rwa [hconjR] at this
  have hact : ∃ r ∈ R, (x' : G) * r * (x' : G)⁻¹ * r⁻¹ ≠ 1 ∧
      (x' : G) * r * (x' : G)⁻¹ * r⁻¹ ≠ w := by
    refine ⟨(r₁ : G), r₁.2, ?_, ?_⟩
    · intro h1
      apply hn1
      have h2 : x' * Subgroup.inclusion hRX r₁ * x'⁻¹ * (Subgroup.inclusion hRX r₁)⁻¹ = 1 :=
        Subtype.ext (by simpa using h1)
      have h3 := congrArg F h2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx'F, map_one] at h3
      rw [← hr₁]; exact h3
    · intro h1
      apply hn2
      have h2 : x' * Subgroup.inclusion hRX r₁ * x'⁻¹ * (Subgroup.inclusion hRX r₁)⁻¹ = T0 :=
        Subtype.ext (by simpa using h1)
      have h3 := congrArg F h2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx'F] at h3
      rw [← hr₁]; exact h3
  have het : ((e.symm zQ : ↥R) : G) = w := by
    have h1 : e ⟨w, hR.mem⟩ = zQ := by
      apply q8_inv_eq
      · rw [← map_mul]
        have : (⟨w, hR.mem⟩ : ↥R) * ⟨w, hR.mem⟩ = 1 := Subtype.ext hR.sq
        rw [this, map_one]
      · intro h1
        have := e.injective (h1.trans (map_one e).symm)
        exact hR.ne_one (congrArg Subtype.val this)
    rw [← h1]; simp
  have hRle : R ≤ ⁅piGen π, piGen π⁆ :=
    le_commutator_of_threeCycle hRX hxX e het hxR' hx3G hxtG hact
  have hconjX : ∀ a ∈ piGen π, ∀ c ∈ ⁅piGen π, piGen π⁆, a * c * a⁻¹ ∈ ⁅piGen π, piGen π⁆ := by
    intro a ha c hc
    have hcX : c ∈ piGen π := Subgroup.commutator_le_self _ hc
    have := Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator ha hcX) hc
    have e1 : ⁅a, c⁆ * c = a * c * a⁻¹ := by rw [commutatorElement_def]; group
    rwa [e1] at this
  intro J hJ
  have hxo := h.xOrbit_eq
  rw [← hxo] at hJ
  obtain ⟨a, ha, rfl⟩ := hJ
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h2 := hconjX a ha _ (hRle hy)
  have : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
  rwa [this] at h2


theorem members_le_commutator_of_cfg2' (h : Cfg' Ω K π z g) (hF3 : Fin3ActsModels) {X : Subgroup G}
    (hX : piGen π = X) {w : G} (hw : IsUniqueInvolution (conjSub g K) w) (hwX : w ∈ X)
    {Q : Type} [Group Q] (F : ↥X →* Q) (hFs : Function.Surjective F) (hker : IsPGroup 2 ↥F.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)
    (ht : F ⟨w, hwX⟩ ≠ 1) : ∀ J ∈ π, J ≤ ⁅X, X⁆ := by
  subst hX
  exact members_le_commutator_of_cfg2 h hF3 hw hwX F hFs hker hQ ht

end General

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf
