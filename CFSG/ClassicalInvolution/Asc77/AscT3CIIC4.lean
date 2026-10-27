module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIHexStmt
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hz, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hz, one_zpow, one_mul]

section Commute

variable [Finite G]

theorem commutes_of_mem_centModOddCore {S M : Subgroup G} (hS : IsPGroup 2 S) {x m : G}
    (hx : x ∈ centModOddCore M) (hxS : x ∈ S) (hm : m ∈ M) (hmS : m ∈ S) : x * m = m * x := by
  have h1 : ⁅x, m⁆ ∈ oddCoreOf M := hx m hm
  have h2 : ⁅x, m⁆ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hxS hmS) (S.inv_mem hxS)) (S.inv_mem hmS)
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅x, m⁆) := hS.to_le (Subgroup.zpowers_le.mpr h2)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) h1 h3)

theorem mem_centModOddCore_of_mem_centralizerModOdd {S M : Subgroup G} {a : G}
    (ha : a ∈ centralizerModOdd S M) : a ∈ centModOddCore M := ha.2.2.2

end Commute

section Data

variable [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G} {S : Sylow 2 G}
  {R R' W V : Subgroup G} {z t : G}

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem hK'Ω : K' ∈ CoreAssembly.conjClass K := by
  have : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact this.1

theorem hz' : IsUniqueInvolution K' z := by
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hzK, hzK'⟩ := hK'
  have e := d.viol.hzK.eq hzK
  subst e
  exact hzK'

theorem eight_le_R : 8 ≤ Nat.card R :=
  d.hyp.eight_le_of_mem_RSet d.branch.odd
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) d.hR)

theorem z_mem_R : z ∈ R :=
  mem_of_isPGroup d.viol.hzK d.hR.1 d.hR.2.1 (by have := d.eight_le_R; omega)

theorem z_mem_S : z ∈ (S : Subgroup G) := d.hRS d.z_mem_R

theorem t_mem_S : t ∈ (S : Subgroup G) := d.hVS d.htV

theorem t_ne_z : t ≠ z := d.viol.ne_involution d.hyp (CoreAssembly.mem_conjClass_self K)

theorem K_ne_K' : K ≠ K' := fun h => d.ne h.symm

theorem sup_le_centralizer_z : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.viol.hzK.commute_of_mem hw).symm)
    (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr (d.hz'.commute_of_mem hw).symm)

theorem z_mem_cent : z ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := by
  have hzM : z ∈ K ⊔ K' := Subgroup.mem_sup_left d.viol.hzK.mem
  refine ⟨d.z_mem_S, Subgroup.le_normalizer hzM,
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzM), fun l hl => ?_⟩
  have := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (d.sup_le_centralizer_z hl)).symm
  rw [this]
  exact (oddCoreOf _).one_mem

theorem cent_comm_t {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a * t = t * a :=
  commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd ha)
    ha.1 d.htKK d.t_mem_S

theorem cent_comm_WK {a w : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (hw : w ∈ W ⊓ K) : a * w = w * a :=
  commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd ha)
    ha.1 (Subgroup.mem_sup_left hw.2) (d.hWS hw.1)

theorem cent_le_normalizer {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  have haS : a ∈ (S : Subgroup G) := ha.1
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := d.hSz haS
  rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) haC with h | h
  · exact mem_normalizer_iff_conjSub_eq.mpr h
  · exfalso
    have hRle : R ≤ conjSub a R := fun r hr => by
      rw [mem_conjSub_iff]
      have hrM : r ∈ K ⊔ K' := Subgroup.mem_sup_left (d.hR.1 hr)
      have hcomm := commutes_of_mem_centModOddCore S.isPGroup'
        (mem_centModOddCore_of_mem_centralizerModOdd ha) haS hrM (d.hRS hr)
      have : a⁻¹ * r * a = r := by
        calc a⁻¹ * r * a = a⁻¹ * (r * a) := by group
          _ = a⁻¹ * (a * r) := by rw [hcomm]
          _ = r := by group
      rw [this]
      exact hr
    have hRK' : R ≤ K' := by
      rw [← h]
      exact hRle.trans (conjSub_mono d.hR.1)
    have := d.hyp.card_le_two_of_le_inf (CoreAssembly.mem_conjClass_self K) d.hK'Ω d.K_ne_K'
      d.hR.2.1 d.hR.1 hRK'
    have := d.eight_le_R
    omega

end Std20

end Data

section Main

variable [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G} {S : Sylow 2 G}
  {R R' W V : Subgroup G} {z t : G}

omit [Finite G] in
theorem le_normalizer_of_commutes {X B : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ B, x * y = y * x) :
    X ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hx' : ∀ y ∈ B, x⁻¹ * y * x = y := fun y hy => by
    calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x * y) := by rw [h x hx y hy]
      _ = y := by group
  have hx'' : ∀ y ∈ B, x * y * x⁻¹ = y := fun y hy => by
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h x hx y hy]
      _ = y := by group
  constructor
  · intro hy
    rw [hx'' y hy]
    exact hy
  · intro hy
    have := hx' _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at this
    rw [this]
    exact hy

theorem mul_self_eq_one_of_card_zpowers_le_two {x : G} (h : Nat.card (Subgroup.zpowers x) ≤ 2) :
    x * x = 1 := by
  rw [Nat.card_zpowers] at h
  have hpos : 0 < orderOf x := orderOf_pos x
  have h1 := pow_orderOf_eq_one x
  interval_cases hx : orderOf x
  · rw [pow_one] at h1
    rw [h1, one_mul]
  · rw [pow_two] at h1
    exact h1

theorem Std20.concl20_4_of_98 (d : Std20 p f K K' J S R R' W V z t)
    (hex : Hex20 (CoreAssembly.conjClass K) K J W)
    (h98 : (∀ x ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'), ∀ w ∈ W ⊓ K, x * w = w * x) →
      ∃ A' : Subgroup G,
        ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ centralizerModOdd (S : Subgroup G) (K ⊔ K') =
            ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A' ∧
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A' = ⊥ ∧
          (∀ a ∈ A', ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
          A' ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A' ≤ centralizerModOdd ⊤ J)
    (htor : ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
      r * t * r⁻¹ = z * t) :
    Concl20_4 S K K' J z := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJΩ : J ∈ CoreAssembly.conjClass K := d.viol.mem
  have hzK := d.viol.hzK
  have hzJ := d.viol.hzJ
  set A := centralizerModOdd (S : Subgroup G) (K ⊔ K') with hA
  have hY : (W ⊓ J) ⊔ (W ⊓ K) = W := by rw [sup_comm, ← hex.hW]
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, ⟨S₁, hS₁, hinv⟩, hWη⟩ := d.hW
    rw [hWη]
    exact ((l6_9_proved p f hp hq G _ d.hyp S₁).2 η hS₁ hinv).1
  obtain ⟨A', hWA, hWA', hcomm', hA'M, hA'J⟩ := h98 (fun x hx w hw => d.cent_comm_WK hx hw)
  rw [hY] at hWA hWA' hcomm'
  have hAS : A ≤ (S : Subgroup G) := fun x hx => hx.1
  have hA'S : A' ≤ (S : Subgroup G) :=
    (show A' ≤ W ⊔ A from hWA ▸ le_sup_right).trans (sup_le d.hWS hAS)
  have hA'W : A' ≤ Subgroup.normalizer (W : Set G) := le_normalizer_of_commutes hcomm'
  have hJWK : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => hWc x hx.1 y hy.1
  have hzA : z ∈ A := d.z_mem_cent
  have hzpA : Subgroup.zpowers z ≤ A := Subgroup.zpowers_le.mpr hzA
  have hle : A ≤ centralizerModOdd A J ⊔ Subgroup.zpowers z := by
    intro a ha
    have haWA' : a ∈ W ⊔ A' := hWA ▸ Subgroup.mem_sup_right ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W A' hA'W] at haWA'
    obtain ⟨w, hw, a', ha', rfl⟩ := haWA'
    have ha'M : a' ∈ centModOddCore (K ⊔ K') := (hA'M ha').2.2.2
    have hw_cent : w ∈ centModOddCore (K ⊔ K') := by
      have := (centModOddCore (K ⊔ K')).mul_mem
        (mem_centModOddCore_of_mem_centralizerModOdd ha)
        ((centModOddCore (K ⊔ K')).inv_mem ha'M)
      simpa using this
    have hwS : w ∈ (S : Subgroup G) := d.hWS hw
    have hwR : ∀ r ∈ R, w * r = r * w := fun r hr =>
      commutes_of_mem_centModOddCore S.isPGroup' hw_cent hwS
        (Subgroup.mem_sup_left (d.hR.1 hr)) (d.hRS hr)
    have hwR' : ∀ r ∈ R', w * r = r * w := fun r hr =>
      commutes_of_mem_centModOddCore S.isPGroup' hw_cent hwS
        (Subgroup.mem_sup_right (d.hR'.1 hr)) (d.hR'S hr)
    obtain ⟨r, hr, r', hr', hinv, hrt⟩ := htor
    have hsq : w * w = 1 := by
      have h1 : (r * r') * w * (r * r')⁻¹ = w := by
        have e1 : r' * w * r'⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hwR' r' hr').symm
        have e2 : r * w * r⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hwR r hr).symm
        calc (r * r') * w * (r * r')⁻¹ = r * (r' * w * r'⁻¹) * r⁻¹ := by group
          _ = w := by rw [e1, e2]
      have h2 := hinv w hw
      rw [h1] at h2
      calc w * w = w * w⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel w
    have hw' : w ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
      at hw'
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hw'
    have hab : b₁ * a₁ = a₁ * b₁ := hWc b₁ hb₁.1 a₁ ha₁.1
    have hsq' : (a₁ * a₁) * (b₁ * b₁) = 1 := by
      calc (a₁ * a₁) * (b₁ * b₁) = a₁ * (a₁ * b₁) * b₁ := by group
        _ = a₁ * (b₁ * a₁) * b₁ := by rw [hab]
        _ = (a₁ * b₁) * (a₁ * b₁) := by group
        _ = 1 := hsq
    have hx1 : a₁ * a₁ = (b₁ * b₁)⁻¹ := eq_inv_of_mul_eq_one_left hsq'
    have hxK : a₁ * a₁ ∈ K := K.mul_mem ha₁.2 ha₁.2
    have hxJ : a₁ * a₁ ∈ J := by rw [hx1]; exact J.inv_mem (J.mul_mem hb₁.2 hb₁.2)
    have hxS : a₁ * a₁ ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem (d.hWS ha₁.1) (d.hWS ha₁.1)
    have hKJ : K ≠ J := fun h => d.viol.ne h.symm
    have hxsq : (a₁ * a₁) * (a₁ * a₁) = 1 := by
      refine mul_self_eq_one_of_card_zpowers_le_two ?_
      exact d.hyp.card_le_two_of_le_inf hKΩ hJΩ hKJ (S.isPGroup'.to_le
        (Subgroup.zpowers_le.mpr hxS)) (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxJ)
    have hxone : a₁ * a₁ = 1 := by
      rcases hzK.unique _ hxK hxsq with h1 | h1
      · exact h1
      · rcases hzJ.unique _ hxJ hxsq with h2 | h2
        · exact h2
        · exact absurd (h2.symm.trans h1) d.t_ne_z
    have hbone : b₁ * b₁ = 1 := by
      have := hx1
      rw [hxone] at this
      exact inv_eq_one.mp this.symm
    have ha₁z : a₁ = 1 ∨ a₁ = z := hzK.unique a₁ ha₁.2 hxone
    have hb₁t : b₁ = 1 ∨ b₁ = t := hzJ.unique b₁ hb₁.2 hbone
    have hb₁1 : b₁ = 1 := by
      rcases hb₁t with h | h
      · exact h
      · exfalso
        subst h
        have hrw : r * (a₁ * b₁) * r⁻¹ = a₁ * b₁ := mul_inv_eq_iff_eq_mul.mpr (hwR r hr).symm
        have hra : r * a₁ * r⁻¹ = a₁ := by
          rcases ha₁z with h1 | h1
          · rw [h1]; group
          · rw [h1]
            exact mul_inv_eq_iff_eq_mul.mpr (hzK.commute_of_mem (d.hR.1 hr)).symm
        have h5 : r * (a₁ * b₁) * r⁻¹ = a₁ * (z * b₁) := by
          calc r * (a₁ * b₁) * r⁻¹ = (r * a₁ * r⁻¹) * (r * b₁ * r⁻¹) := by group
            _ = a₁ * (z * b₁) := by rw [hra, hrt]
        rw [h5] at hrw
        have h6 := mul_left_cancel hrw
        exact hzK.ne_one (mul_eq_right.mp h6)
    subst hb₁1
    have hwz : a₁ * 1 ∈ Subgroup.zpowers z := by
      rw [mul_one]
      rcases ha₁z with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    have hwA : a₁ * 1 ∈ A := hzpA hwz
    have ha'A : a' ∈ A := by
      have := A.mul_mem (A.inv_mem hwA) ha
      simpa using this
    have ha'J : a' ∈ centralizerModOdd A J := ⟨ha'A, (hA'J ha').2.1, (hA'J ha').2.2.1,
      (hA'J ha').2.2.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwz) (Subgroup.mem_sup_left ha'J)
  refine ⟨le_antisymm hle (sup_le (fun x hx => hx.1) hzpA), ?_⟩
  rw [Subgroup.disjoint_def]
  intro x hxJ hxz
  rcases eq_one_or_eq_of_mem_zpowers hzK.sq hxz with h | h
  · exact h
  · exfalso
    subst h
    have hzJ' : x ∈ centralizerModOdd A J := hxJ
    have htq : x ∈ Balance.Bootstrap.trivialOnQuot J := ⟨hzJ'.2.1, hzJ'.2.2.2⟩
    exact d.viol.not_nbr (mem_omegaNbr_of_trivialOnQuot hp hq d.hyp hKΩ hzK hJΩ d.viol.ne htq)

theorem c20_4 (hex : HexAll p f) : C20_4 p f := by
  intro G _ _ _ K K' J S R R' W V z t d _
  have hH := hex G K K' J S R R' W V z t d
  refine d.concl20_4_of_98 hH ?_ (d.late_tor hH.JW hH.hW)
  exact (d.late_98 hH.JW hH.hW (X := centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (S.isPGroup'.to_le (fun x hx => hx.1)) (fun x hx => hx.1) (fun x hx => d.cent_comm_t hx)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer hx))).2

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII
