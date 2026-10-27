module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksAux
import CFSG.GroupTheory.PCore.OpenTransport

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

open BlocksAux

namespace BlocksChief

section Chief
variable {X : Type} [Group X] {K V' U : Subgroup X}

theorem chief_comm_le (hch : IsChiefFactorOf K V' U) : ⁅U, K⁆ ≤ U :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 hch.2.2.1

theorem chief_sup_eq (hch : IsChiefFactorOf K V' U) (hnc : ¬ ⁅U, K⁆ ≤ V') : ⁅U, K⁆ ⊔ V' = U := by
  have hYU := chief_comm_le hch
  have hKY : K ≤ Subgroup.normalizer (⁅U, K⁆ : Subgroup X) :=
    le_normalizer_commutator hch.2.2.1 Subgroup.le_normalizer
  have hKYV : K ≤ Subgroup.normalizer ((⁅U, K⁆ ⊔ V' : Subgroup X) : Set X) :=
    le_trans (le_inf hKY hch.2.1) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rcases hch.2.2.2 (⁅U, K⁆ ⊔ V') le_sup_right (sup_le hYU hch.1.le) hKYV with h | h
  · exact absurd (le_sup_left.trans h.le) hnc
  · exact h

theorem chief_dec (hch : IsChiefFactorOf K V' U) (hUK : U ≤ K) (hnc : ¬ ⁅U, K⁆ ≤ V') :
    ∀ u ∈ U, ∃ y ∈ ⁅U, K⁆, ∃ v ∈ V', u = y * v := by
  intro u hu
  have hsup := chief_sup_eq hch hnc
  have hY : ⁅U, K⁆ ≤ Subgroup.normalizer (V' : Set X) :=
    ((chief_comm_le hch).trans hUK).trans hch.2.1
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right ⁅U, K⁆ V' hY
  have hu' : u ∈ (⁅U, K⁆ ⊔ V' : Subgroup X) := hsup.ge hu
  rw [← SetLike.mem_coe, hset] at hu'
  obtain ⟨y, hy, v, hv, rfl⟩ := Set.mem_mul.mp hu'
  exact ⟨y, hy, v, hv, rfl⟩

theorem comm_le_of_prod (hKV : K ≤ Subgroup.normalizer (V' : Set X)) (hUK : U ≤ K)
    {P : Subgroup X} (hPU : P ≤ U) (hP : ∀ p ∈ P, ∀ k ∈ K, ⁅p, k⁆ ∈ V')
    (hdec : ∀ u ∈ U, ∃ p ∈ P, ∃ v ∈ V', u = p * v) : ⁅U, K⁆ ≤ V' := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  obtain ⟨p, hp, v, hv, rfl⟩ := hdec u hu
  rw [commutatorElement_mul_left]
  have h1 : ⁅v, k⁆ ∈ V' := by
    have : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact V'.mul_mem hv (Subgroup.le_normalizer_iff.1 hKV k hk _ (V'.inv_mem hv))
  have h2 : p * ⁅v, k⁆ * p⁻¹ ∈ V' := Subgroup.le_normalizer_iff.1 hKV p (hUK (hPU hp)) _ h1
  exact V'.mul_mem h2 (hP p hp k hk)

theorem noncentral_comm_comm (hch : IsChiefFactorOf K V' U) (hUK : U ≤ K) (hnc : ¬ ⁅U, K⁆ ≤ V') :
    ¬ ⁅⁅U, K⁆, K⁆ ≤ V' := by
  intro h
  exact hnc (comm_le_of_prod hch.2.1 hUK (chief_comm_le hch)
    (fun p hp k hk => h (Subgroup.commutator_mem_commutator hp hk)) (chief_dec hch hUK hnc))

theorem comm_eq_one_of_fix {p k : X} (e : k * p * k⁻¹ = p) : ⁅p, k⁆ = 1 := by
  have : k * p = p * k := by
    calc k * p = (k * p * k⁻¹) * k := by group
      _ = p * k := by rw [e]
  simp only [commutatorElement_def]
  calc p * k * p⁻¹ * k⁻¹ = (k * p) * p⁻¹ * k⁻¹ := by rw [this]
    _ = 1 := by group

end Chief

section Series
variable {G : Type*} [Group G] {K R : Subgroup G} {n : ℕ} {T : Fin (n + 1) → Subgroup G}

theorem series_mono (hT : IsChiefSeriesIn K R T) : Monotone T :=
  Fin.monotone_iff_le_succ.2 fun i => (hT.2.2 i).1.le

theorem series_le (hT : IsChiefSeriesIn K R T) (j : Fin (n + 1)) : T j ≤ R := by
  have := series_mono hT (Fin.le_last j)
  rwa [hT.2.1] at this

end Series

section Setting
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem K_sup_S_le_normalizer (h : Setup28 W K S) : K ⊔ S ≤ Subgroup.normalizer (K : Set X) :=
  sup_le Subgroup.le_normalizer h.hN

theorem w1_le_sup (hR : Red28 W K S) : kerAct W K S ≤ K ⊔ S := hR.w1_S.trans le_sup_right

theorem sup_le_normalizer_w1 (hR : Red28 W K S) :
    K ⊔ S ≤ Subgroup.normalizer (kerAct W K S : Set X) :=
  Subgroup.le_normalizer_iff.2 hR.w1_nrm

theorem K_le_normalizer_V (hR : Red28 W K S) : K ≤ Subgroup.normalizer (vOf W K S : Set X) :=
  fun k hk => N_le_normalizer_V hR ((le_sup_left : K ≤ K ⊔ S) hk)

theorem pCoreOf_le_w1 (hR : Red28 W K S) : pCoreOf 2 K ≤ kerAct W K S := by
  rw [hR.o2K]
  exact inf_le_right.trans hR.w1_le

theorem comm_w1_le (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) : ⁅kerAct W K S, K⁆ ≤ U₁ := by
  have h1 : ⁅kerAct W K S, K⁆ ≤ vOf W K S := by
    rw [Subgroup.commutator_comm (kerAct W K S) K]
    exact Subgroup.commutator_le.2 hE
  have h2 : ⁅K, kerAct W K S⁆ ≤ ⁅⁅kerAct W K S, K⁆, K⁆ :=
    comm_le_comm_comm h.hK.2.1 le_sup_left (w1_le_sup hR) (K_sup_S_le_normalizer h)
      (sup_le_normalizer_w1 hR)
  have h3 : ⁅⁅kerAct W K S, K⁆, K⁆ ≤ ⁅vOf W K S, K⁆ := Subgroup.commutator_mono h1 le_rfl
  have h4 : ⁅vOf W K S, K⁆ ≤ U₁ :=
    Subgroup.commutator_le.2 (fun v hv k hk => sf.comm_le k hk v hv)
  rw [Subgroup.commutator_comm K (kerAct W K S)] at h2
  exact h2.trans (h3.trans h4)

theorem comm_V_le_pCore (h : Setup28 W K S) (hR : Red28 W K S) :
    ⁅vOf W K S, K⁆ ≤ pCoreOf 2 K := by
  have hVK : ⁅vOf W K S, K⁆ ≤ K := by
    have : vOf W K S ≤ Subgroup.normalizer (K : Set X) := (hR.v_le.trans hR.w1_S).trans h.hN
    exact Subgroup.le_normalizer_iff_commutator_le_right.1 this
  have hVV : ⁅vOf W K S, K⁆ ≤ vOf W K S :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (K_le_normalizer_V hR)
  have : ⁅vOf W K S, K⁆ ≤ K ⊓ kerAct W K S := le_inf hVK (hVV.trans hR.v_le)
  rwa [hR.k_w1, ← hR.o2K] at this

theorem toBar_surjective (W K : Subgroup X) [W.Normal] : Function.Surjective (toBar W K) := by
  rintro ⟨y, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem toBar_eq_one_iff {W K : Subgroup X} [W.Normal] (k : ↥K) :
    toBar W K k = 1 ↔ (k : X) ∈ W := by
  constructor
  · intro h
    have h' : ((k : X) : X ⧸ W) = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).1 h'
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 h

theorem zPre_of_center {k : ↥K} (hk : toBar W K k ∈ Subgroup.center ↥(bar W K)) :
    (k : X) ∈ zPre W K := by
  refine ⟨k.2, fun k' hk' => ?_⟩
  have h1 : toBar W K ⟨k', hk'⟩ * toBar W K k = toBar W K k * toBar W K ⟨k', hk'⟩ :=
    Subgroup.mem_center_iff.1 hk _
  have h2 : toBar W K ⁅k, ⟨k', hk'⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  have h3 := (toBar_eq_one_iff _).1 h2
  simpa [commutatorElement_def] using h3

theorem center_of_zPre {k : ↥K} (hk : (k : X) ∈ zPre W K) :
    toBar W K k ∈ Subgroup.center ↥(bar W K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k', rfl⟩ := toBar_surjective W K g
  have h2 : toBar W K ⁅k, k'⁆ = 1 :=
    (toBar_eq_one_iff _).2 (by simpa [commutatorElement_def] using hk.2 k' k'.2)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem zPre_iff_center_aux (k : ↥K) :
    (k : X) ∈ zPre W K ↔ toBar W K k ∈ Subgroup.center ↥(bar W K) :=
  ⟨center_of_zPre, zPre_of_center⟩

theorem piOf_props_aux {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    Function.Surjective (piOf e) ∧ ∀ k : ↥K, piOf e k = 1 ↔ (k : X) ∈ zPre W K := by
  refine ⟨e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (toBar_surjective W K)),
    fun k => ?_⟩
  show e (QuotientGroup.mk' _ (toBar W K k)) = 1 ↔ _
  rw [e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (zPre_iff_center_aux k).symm

theorem centre_odd_aux (h : Setup28 W K S) : Odd (Nat.card ↥(Subgroup.center ↥(bar W K))) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(bar W K)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcc : (z : ↥(bar W K)) ∈ Subgroup.center ↥(bar W K) := z.2
  have hord : orderOf (z : ↥(bar W K)) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hc2 : IsPGroup 2 ↥(Subgroup.zpowers (z : ↥(bar W K))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hnorm : (Subgroup.zpowers (z : ↥(bar W K))).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hcc)
  have hle : Subgroup.zpowers (z : ↥(bar W K)) ≤ CFSG.pCore 2 ↥(bar W K) := le_sSup ⟨hnorm, hc2⟩
  rw [h.hO] at hle
  have hc1 : (z : ↥(bar W K)) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  rw [hc1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem V_central {v : X} (hv : v ∈ vOf W K S) : ∀ w ∈ kerAct W K S, v * w = w * v := hv.2.1

theorem chief_core (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S) {V' U : Subgroup X}
    (hU : IsNoncentralChiefFactor K (pCoreOf 2 K) V' U) :
    ⁅U, K⁆ ≤ U ∧ ⁅U, K⁆ ≤ U₁ ∧ (∀ k ∈ K, ∀ y ∈ ⁅U, K⁆, k * y * k⁻¹ ∈ ⁅U, K⁆) ∧
      ⁅U, K⁆ ⊔ V' = U ∧ ⁅U, K⁆ ⊔ U₂ = U₁ ∧ ⁅U, K⁆ ⊓ V' = ⁅U, K⁆ ⊓ U₂ ∧
      (∀ y ∈ ⁅U, K⁆, ∀ v ∈ V', y * v = v * y) ∧ (∀ y ∈ ⁅U, K⁆, ∀ w ∈ U₂, y * w = w * y) := by
  obtain ⟨hch, hUR, hnc⟩ := hU
  have hUK : U ≤ K := hUR.trans (CFSG.openPCoreOf_le 2 K)
  have hUW1 : U ≤ kerAct W K S := hUR.trans (pCoreOf_le_w1 hR)
  have hV'U : V' ≤ U := hch.1.le
  have hYU : ⁅U, K⁆ ≤ U := chief_comm_le hch
  have hYU₁ : ⁅U, K⁆ ≤ U₁ :=
    (Subgroup.commutator_mono_left hUW1).trans (comm_w1_le h hR sf hE)
  have hKY : K ≤ Subgroup.normalizer (⁅U, K⁆ : Subgroup X) :=
    le_normalizer_commutator hch.2.2.1 Subgroup.le_normalizer
  have hKV' : K ≤ Subgroup.normalizer (V' : Set X) := hch.2.1
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set X) := Subgroup.le_normalizer_iff.2 sf.inv₂
  have hsupV : ⁅U, K⁆ ⊔ V' = U := chief_sup_eq hch hnc
  have hdecV : ∀ u ∈ U, ∃ y ∈ ⁅U, K⁆, ∃ v ∈ V', u = y * v := chief_dec hch hUK hnc
  have hYV : ⁅U, K⁆ ≤ vOf W K S := hYU₁.trans sf.le.2
  have hcV : ∀ y ∈ ⁅U, K⁆, ∀ v ∈ V', y * v = v * y := fun y hy v hv =>
    V_central (hYV hy) v (hUW1 (hV'U hv))
  have hcU₂ : ∀ y ∈ ⁅U, K⁆, ∀ w ∈ U₂, y * w = w * y := fun y hy w hw =>
    V_central (hYV hy) w (hR.v_le (sf.le.2 (sf.le.1 hw)))
  have hfix : ∀ p ∈ U₂, ∀ k ∈ K, ⁅p, k⁆ = 1 := fun p hp k hk =>
    comm_eq_one_of_fix (sf.triv₂ k hk p hp)
  have hD : ⁅U, K⁆ ⊓ U₂ ≤ V' := by
    have hKD : K ≤ Subgroup.normalizer ((⁅U, K⁆ ⊓ U₂ : Subgroup X) : Set X) :=
      le_trans (le_inf hKY hKU₂) Subgroup.inf_normalizer_le_normalizer_inf
    have hKDV : K ≤ Subgroup.normalizer (((⁅U, K⁆ ⊓ U₂) ⊔ V' : Subgroup X) : Set X) :=
      le_trans (le_inf hKD hKV') (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    rcases hch.2.2.2 ((⁅U, K⁆ ⊓ U₂) ⊔ V') le_sup_right
        (sup_le (inf_le_left.trans hYU) hV'U) hKDV with h1 | h1
    · exact le_sup_left.trans h1.le
    · exfalso
      apply hnc
      refine comm_le_of_prod hKV' hUK (inf_le_left.trans hYU : ⁅U, K⁆ ⊓ U₂ ≤ U)
        (fun p hp k hk => by rw [hfix p hp.2 k hk]; exact V'.one_mem) ?_
      intro u hu
      have hu' : u ∈ ((⁅U, K⁆ ⊓ U₂) ⊔ V' : Subgroup X) := h1.ge hu
      exact mem_sup_of_commute (H := ⁅U, K⁆ ⊓ U₂) (L := V')
        (fun d hd v hv => hcV d (Subgroup.mem_inf.1 hd).1 v hv) hu'
  have hsupU : ⁅U, K⁆ ⊔ U₂ = U₁ := by
    have hKYU : K ≤ Subgroup.normalizer ((⁅U, K⁆ ⊔ U₂ : Subgroup X) : Set X) :=
      le_trans (le_inf hKY hKU₂) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    rcases sf.irred (⁅U, K⁆ ⊔ U₂) le_sup_right (sup_le hYU₁ sf.le.1)
        (Subgroup.le_normalizer_iff.1 hKYU) with h1 | h1
    · exfalso
      have hYU₂ : ⁅U, K⁆ ≤ U₂ := le_sup_left.trans h1.le
      exact hnc (comm_le_of_prod hKV' hUK hYU
        (fun p hp k hk => by rw [hfix p (hYU₂ hp) k hk]; exact V'.one_mem) hdecV)
    · exact h1
  have hE' : ⁅U, K⁆ ⊓ V' ≤ U₂ := by
    have hKE : K ≤ Subgroup.normalizer ((⁅U, K⁆ ⊓ V' : Subgroup X) : Set X) :=
      le_trans (le_inf hKY hKV') Subgroup.inf_normalizer_le_normalizer_inf
    have hKEU : K ≤ Subgroup.normalizer (((⁅U, K⁆ ⊓ V') ⊔ U₂ : Subgroup X) : Set X) :=
      le_trans (le_inf hKE hKU₂) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    rcases sf.irred ((⁅U, K⁆ ⊓ V') ⊔ U₂) le_sup_right
        (sup_le (inf_le_left.trans hYU₁) sf.le.1) (Subgroup.le_normalizer_iff.1 hKEU) with h1 | h1
    · exact le_sup_left.trans h1.le
    · exfalso
      apply hnc
      have hYV' : ⁅U, K⁆ ≤ V' := by
        intro y hy
        have hy1 : y ∈ U₁ := hYU₁ hy
        rw [← h1] at hy1
        obtain ⟨e, he, w, hw, rfl⟩ :=
          mem_sup_of_commute (H := ⁅U, K⁆ ⊓ V') (L := U₂)
            (fun e he w hw => hcU₂ e (Subgroup.mem_inf.1 he).1 w hw) hy1
        have hwY : w ∈ ⁅U, K⁆ := by
          have : w = e⁻¹ * (e * w) := by group
          rw [this]
          exact (⁅U, K⁆).mul_mem ((⁅U, K⁆).inv_mem (Subgroup.mem_inf.1 he).1) hy
        exact V'.mul_mem (Subgroup.mem_inf.1 he).2 (hD ⟨hwY, hw⟩)
      exact hYV'
  have hinf : ⁅U, K⁆ ⊓ V' = ⁅U, K⁆ ⊓ U₂ :=
    le_antisymm (le_inf inf_le_left hE') (le_inf inf_le_left hD)
  exact ⟨hYU, hYU₁, Subgroup.le_normalizer_iff.1 hKY, hsupV, hsupU, hinf, hcV, hcU₂⟩

end Setting

end BlocksChief

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
