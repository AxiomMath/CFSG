module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Lifted.Alt51Idx
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.GH74.GLS.SP.Local

theorem le_fitting_of_normalized_abelian {G : Type*} [Group G] [Finite G] (W : Subgroup G)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hcomm : ∀ a b : G, ⁅a, b⁆ ∈ CFSG.fittingSubgroup G)
    (hnorm : ∀ x ∈ CFSG.fittingSubgroup G, ∀ w ∈ W, x * w * x⁻¹ ∈ W) :
    W ≤ CFSG.fittingSubgroup G := by
  set F := CFSG.fittingSubgroup G with hF
  set P : Subgroup G := W ⊔ F with hP
  have hWP : W ≤ P := le_sup_left
  have hFP : F ≤ P := le_sup_right
  have hPn : P.Normal := ⟨fun n hn g => by
    have h1 : ⁅g, n⁆ ∈ F := hcomm g n
    have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact P.mul_mem (hFP h1) hn⟩
  have hWnorm : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W := by
    intro p hp w hw
    obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hp
    have h1 : f * w * f⁻¹ ∈ W := hnorm f hf w hw
    have h2 : a * f * w * (a * f)⁻¹ = a * (f * w * f⁻¹) * a⁻¹ := by group
    rw [h2]
    exact W.mul_mem (W.mul_mem ha h1) (W.inv_mem ha)
  have hWPn : (W.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hWnorm (g : G) g.2 (n : G) hn⟩
  have hcomm' : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (hab a a.2 b b.2)
  have hWnil : Group.IsNilpotent (W.subgroupOf P) := by
    let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hcomm' }
    exact Group.nilpotent_of_mulEquiv (G := W) (Subgroup.subgroupOfEquivOfLe hWP).symm
  have hWle : W.subgroupOf P ≤ CFSG.fittingSubgroup ↥P := le_sSup ⟨hWPn, hWnil⟩
  set Q : Subgroup G := (CFSG.fittingSubgroup ↥P).map P.subtype with hQ
  have hWQ : W ≤ Q := by
    have hmap := Subgroup.map_mono (f := P.subtype) hWle
    rwa [Subgroup.map_subgroupOf_eq_of_le hWP] at hmap
  have hQn : Q.Normal := ⟨fun n hn g => by
    obtain ⟨q, hq, rfl⟩ := hn
    have hchar := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.fittingSubgroup ↥P).Characteristic) (MulAut.conjNormal (H := P) g)
    have hq' : (MulAut.conjNormal (H := P) g) q ∈ CFSG.fittingSubgroup ↥P := by
      rw [← hchar]
      exact ⟨q, hq, rfl⟩
    refine ⟨_, hq', ?_⟩
    simp [MulAut.conjNormal_apply]⟩
  have hQnil : Group.IsNilpotent Q :=
    Group.nilpotent_of_mulEquiv (G := CFSG.fittingSubgroup ↥P)
      (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective)
  exact hWQ.trans (le_sSup ⟨hQn, hQnil⟩)


theorem mem_of_odd_orderOf_of_two_power_index {A : Type*} [Group A] [Finite A] (C₀ Yu : Subgroup A)
    (hYuC : Yu ≤ C₀) (hYuN : ∀ c ∈ C₀, ∀ y ∈ Yu, c * y * c⁻¹ ∈ Yu) (k : ℕ)
    (hcard : Nat.card ↥Yu * 2 ^ k = Nat.card ↥C₀) {g : A} (hg : g ∈ C₀) (hodd : Odd (orderOf g)) :
    g ∈ Yu := by
  have hYn : (Yu.subgroupOf C₀).Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hYuN (c : A) c.2 (n : A) hn⟩
  have hQ : Nat.card (↥C₀ ⧸ Yu.subgroupOf C₀) = 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Yu.subgroupOf C₀)
    have h2 : Nat.card ↥(Yu.subgroupOf C₀) = Nat.card ↥Yu :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYuC).toEquiv
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥Yu := Nat.card_pos
    have : Nat.card ↥Yu * Nat.card (↥C₀ ⧸ Yu.subgroupOf C₀) = Nat.card ↥Yu * 2 ^ k := by
      rw [hcard, h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  set x : ↥C₀ := ⟨g, hg⟩ with hx
  set π : ↥C₀ →* ↥C₀ ⧸ Yu.subgroupOf C₀ := QuotientGroup.mk' (Yu.subgroupOf C₀) with hπ
  have hd1 : orderOf (π x) ∣ orderOf g := by
    have := orderOf_map_dvd π x
    rwa [hx, Subgroup.orderOf_mk] at this
  have hd2 : orderOf (π x) ∣ 2 ^ k := hQ ▸ orderOf_dvd_natCard (π x)
  have hdodd : Odd (orderOf (π x)) := Odd.of_dvd_nat hodd hd1
  have hcop : Nat.Coprime (orderOf (π x)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_left.mpr hdodd).symm
  have h1 : orderOf (π x) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd2
  have h2 : π x = 1 := orderOf_eq_one_iff.mp h1
  have h3 : x ∈ Yu.subgroupOf C₀ := (QuotientGroup.eq_one_iff x).mp h2
  exact (Subgroup.mem_subgroupOf).mp h3


open CFSG.GH74.GLS.IVK.Proofs2 in
theorem odd_abelian_le_xuInn {F : Type} [Field F] [Finite F] (hF : L2Field F)
    {K : Type} [Group K] [Finite K] (e : K ≃* L2 F) {ū : K} (hū : orderOf ū = 2)
    {M : Type} [Group M] [Finite M] (α : M →* MulAut K)
    (hα : ∀ m : M, α m ū = ū)
    (W : Subgroup M) (hWodd : Odd (Nat.card ↥W)) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hX : ∀ k ∈ xu (MulAut.conj ū), ∃ m : M, α m = MulAut.conj k ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, α w ∈ xuInn (MulAut.conj ū) := by
  set u : MulAut K := MulAut.conj ū with hu_def
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hu : u ∈ innDiagSub e := innAut_le_innDiagSub e ⟨ū, rfl⟩
  have hu2 : orderOf u = 2 := by
    rw [hu_def, orderOf_injective (MulAut.conj : K →* MulAut K) hinj ū]
    exact hū
  obtain ⟨Yu, hYuC, hYuN, hYuodd, ⟨k₂, hk₂⟩, hFit, ⟨hnormX, hcyc⟩, -⟩ := ivk_1_3d F hF K e u hu hu2
  set W' : Subgroup (MulAut K) := W.map α with hW'
  have hW'C : W' ≤ centralizer ({u} : Set (MulAut K)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mul_conj_mul_inv_eq_conj_apply (α w) ū
    rw [hα w] at h
    calc α w * u = (α w * u * (α w)⁻¹) * α w := by group
      _ = u * α w := by rw [hu_def, h]
  have hW'odd : Odd (Nat.card ↥W') := Odd.of_dvd_nat hWodd (Subgroup.card_map_dvd W α)
  have hW'ab : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := by
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
    rw [← map_mul, ← map_mul, hWab w₁ hw₁ w₂ hw₂]
  have hW'Yu : W' ≤ Yu := fun g hg =>
    mem_of_odd_orderOf_of_two_power_index _ Yu hYuC hYuN k₂ hk₂ (hW'C hg)
      (Odd.of_dvd_nat hW'odd (Subgroup.orderOf_dvd_natCard W' hg))
  have hXW' : ∀ x ∈ xuInn u, ∀ g ∈ W', x * g * x⁻¹ ∈ W' := by
    intro x hx g hg
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨m, hm, hmW⟩ := hX k hk
    obtain ⟨w, hw, rfl⟩ := hg
    rw [← hm, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨m * w * m⁻¹, hmW w hw, by simp⟩
  have hN : (xuInn u).subgroupOf Yu = CFSG.fittingSubgroup ↥Yu := by
    rw [← hFit]
    exact Subgroup.comap_map_eq_self_of_injective Yu.subtype_injective _
  have hcomm : ∀ a b : ↥Yu, ⁅a, b⁆ ∈ CFSG.fittingSubgroup ↥Yu := by
    intro a b
    rw [← hN]
    have h1 : QuotientGroup.mk' ((xuInn u).subgroupOf Yu) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (IsCyclic.commGroup (α := ↥Yu ⧸ (xuInn u).subgroupOf Yu)).mul_comm _ _
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hmain := le_fitting_of_normalized_abelian (W'.subgroupOf Yu)
    (fun a ha b hb => Subtype.ext (hW'ab _ ha _ hb)) hcomm (by
      intro x hx w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      have hxX : (x : MulAut K) ∈ xuInn u := by
        rw [← hFit]; exact ⟨x, hx, rfl⟩
      simpa using hXW' _ hxX _ hw)
  intro w hw
  have hmem : (⟨α w, hW'Yu ⟨w, hw, rfl⟩⟩ : ↥Yu) ∈ W'.subgroupOf Yu := ⟨w, hw, rfl⟩
  have := hmain hmem
  rw [← hFit]
  exact ⟨_, this, rfl⟩


section CentralQuot

variable {K : Type} [Group K]

theorem exists_odd_lift (hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1) {kb : K ⧸ Subgroup.center K}
    (hkb : Odd (orderOf kb)) : ∃ k : K, Odd (orderOf k) ∧ (k : K ⧸ Subgroup.center K) = kb := by
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
  set r := orderOf (k₀ : K ⧸ Subgroup.center K) with hr
  have hc : k₀ ^ r ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  refine ⟨k₀ ^ (r + 1), ?_, ?_⟩
  · have h1 : (k₀ ^ (r + 1)) ^ r = 1 := by
      obtain ⟨m, hm⟩ := hkb
      have h2 : r + 1 = 2 * (m + 1) := by omega
      rw [← pow_mul, mul_comm, pow_mul, h2, pow_mul, hZ _ hc, one_pow]
    exact Odd.of_dvd_nat hkb (orderOf_dvd_of_pow_eq_one h1)
  · rw [QuotientGroup.mk_pow, pow_succ, pow_orderOf_eq_one, one_mul]

theorem commute_of_odd_central (hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1) {k u : K}
    (hk : Odd (orderOf k)) (h : k * u * k⁻¹ * u⁻¹ ∈ Subgroup.center K) : k * u = u * k := by
  set c : K := k * u * k⁻¹ * u⁻¹ with hc
  have hcc : ∀ x : K, c * x = x * c := fun x => (Subgroup.mem_center_iff.mp h x).symm
  have hku : k * u * k⁻¹ = c * u := by rw [hc]; group
  have hpow : ∀ j : ℕ, k ^ j * u * (k ^ j)⁻¹ = c ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 1) * u * (k ^ (j + 1))⁻¹ = k * (k ^ j * u * (k ^ j)⁻¹) * k⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = k * (c ^ j * u) * k⁻¹ := by rw [ih]
        _ = c ^ j * (k * u * k⁻¹) := by
            have hck : k * c ^ j = c ^ j * k := by
              have : k * c = c * k := (hcc k).symm
              exact (Commute.pow_right (show Commute k c from this) j).eq
            calc k * (c ^ j * u) * k⁻¹ = (k * c ^ j) * u * k⁻¹ := by group
              _ = (c ^ j * k) * u * k⁻¹ := by rw [hck]
              _ = c ^ j * (k * u * k⁻¹) := by group
        _ = c ^ (j + 1) * u := by rw [hku, pow_succ]; group
  have h1 := hpow (orderOf k)
  rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
  have h2 : c ^ orderOf k = 1 := by
    have := h1.symm
    simpa using this
  obtain ⟨m, hm⟩ := hk
  have h3 : c ^ orderOf k = c := by
    rw [hm, pow_succ, pow_mul, hZ c h, one_pow, one_mul]
  have hc1 : c = 1 := by rw [← h3]; exact h2
  have : k * u * k⁻¹ = u := by rw [hku, hc1, one_mul]
  calc k * u = (k * u * k⁻¹) * k := by group
    _ = u * k := by rw [this]

end CentralQuot


section SL2Facts

variable {F : Type} [Field F] [Finite F]

theorem ringChar_ne_two (hF : L2Field F) : ringChar F ≠ 2 := by
  intro h
  have := Fintype.ofFinite F
  have h2 := (FiniteField.even_card_iff_char_two (F := F)).mp h
  have h3 := hF.1
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at h3
  omega

theorem center_sq_eq_one {K : Type} [Group K] (hF : L2Field F) (e : K ≃* SL2 F) {c : K}
    (hc : c ∈ Subgroup.center K) : c ^ 2 = 1 := by
  have h1 : e c ∈ Subgroup.center (SL2 F) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨c, hc, rfl⟩
  rw [← CFSG.Semidihedral.ProjectiveSL2Cover.statedScalarKernel_eq_center,
    CFSG.Semidihedral.ProjectiveSL2Cover.mem_statedScalarKernel_two_iff] at h1
  apply e.injective
  rw [map_pow, map_one]
  rcases h1 with h | h
  · rw [h, one_pow]
  · rw [h]
    have h2 := pow_orderOf_eq_one (CFSG.Semidihedral.ProjectiveSL2Cover.statedMinusIdentity F)
    rwa [CFSG.Semidihedral.ProjectiveSL2Cover.statedMinusIdentity_order F (ringChar_ne_two hF)] at h2

theorem perfect_of_SL2 {K : Type} [Group K] (hF : L2Field F) (e : K ≃* SL2 F) :
    commutator K = ⊤ := by
  have h4 : 4 ≤ Nat.card F := by have := hF.2; omega
  have hq := CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4
  have hq2 : CFSG.IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((specialLinearGroupEquivStatedSL 2 F).trans e.symm) hq
  have := hq2.1
  exact Group.IsPerfect.commutator_eq_top

noncomputable def quotCenterEquivL2 {K : Type} [Group K] (e : K ≃* SL2 F) :
    K ⧸ Subgroup.center K ≃* L2 F :=
  QuotientGroup.congr (Subgroup.center K)
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) e (by
      rw [Subgroup.map_center_eq e]
      exact (CFSG.Semidihedral.ProjectiveSL2Cover.statedScalarKernel_eq_center F 2).symm)

end SL2Facts


section LiftXu

variable {K : Type} [Group K]

theorem lift_xu (hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1) [Finite K] {u₁ : K}
    {kb : K ⧸ Subgroup.center K}
    (hkb : kb ∈ CFSG.GH74.GLS.IVK.xu (MulAut.conj (u₁ : K ⧸ Subgroup.center K))) :
    ∃ k : K, Odd (orderOf k) ∧ k * u₁ = u₁ * k ∧ (k : K ⧸ Subgroup.center K) = kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (orderOf kb) := by
    obtain ⟨c, hc, rfl⟩ := hkb
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(fixedSubgroup (K ⧸ Subgroup.center K)
        (MulAut.conj (u₁ : K ⧸ Subgroup.center K))))) := pPrimeCore_coprime_card
    have hd : orderOf c ∣ Nat.card (pPrimeCore 2 ↥(fixedSubgroup (K ⧸ Subgroup.center K)
        (MulAut.conj (u₁ : K ⧸ Subgroup.center K)))) := Subgroup.orderOf_dvd_natCard _ hc
    have hodd' : Odd (orderOf c) := Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hd hcop)
    rwa [show orderOf ((fixedSubgroup (K ⧸ Subgroup.center K)
        (MulAut.conj (u₁ : K ⧸ Subgroup.center K))).subtype c) = orderOf c from
          Subgroup.orderOf_coe _]
  have hfix : (u₁ : K ⧸ Subgroup.center K) * kb * (u₁ : K ⧸ Subgroup.center K)⁻¹ = kb := by
    have := CFSG.GH74.GLS.IVK.Proofs2.xu_le_fixedSubgroup
      (MulAut.conj (u₁ : K ⧸ Subgroup.center K)) hkb
    rw [CFSG.GH74.GLS.IVK.Proofs2.mem_fixedSubgroup_iff', MulAut.conj_apply] at this
    exact this
  obtain ⟨k, hk, hkk⟩ := exists_odd_lift hZ hodd
  refine ⟨k, hk, ?_, hkk⟩
  apply commute_of_odd_central hZ hk
  rw [← QuotientGroup.eq_one_iff]
  have : ((k * u₁ * k⁻¹ * u₁⁻¹ : K) : K ⧸ Subgroup.center K) =
      kb * (u₁ : K ⧸ Subgroup.center K) * kb⁻¹ * (u₁ : K ⧸ Subgroup.center K)⁻¹ := by
    simp [hkk]
  rw [this]
  have h2 : (u₁ : K ⧸ Subgroup.center K) * kb = kb * (u₁ : K ⧸ Subgroup.center K) := by
    have h3 := hfix
    rwa [mul_inv_eq_iff_eq_mul] at h3
  calc kb * (u₁ : K ⧸ Subgroup.center K) * kb⁻¹ * (u₁ : K ⧸ Subgroup.center K)⁻¹
      = ((u₁ : K ⧸ Subgroup.center K) * kb) * kb⁻¹ * (u₁ : K ⧸ Subgroup.center K)⁻¹ := by
        rw [h2]
    _ = 1 := by group

end LiftXu

theorem spl_fit_A1 : ∀ (F : Type) [Field F] [Finite F], L2Field F →
    ∀ (K : Type) [Group K] [Finite K], (K ≃* SL2 F) →
    ∀ u₁ : K, u₁ ^ 2 ∈ Subgroup.center K → u₁ ^ 2 ≠ 1 →
    ∀ (M : Type) [Group M] [Finite M] (α : M →* MulAut K),
      (∀ m : M, α m u₁ * u₁⁻¹ ∈ Subgroup.center K) →
    ∀ W : Subgroup M, Odd (Nat.card ↥W) → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) →
      (∀ k : K, Odd (orderOf k) → k * u₁ = u₁ * k →
        ∃ m : M, α m = MulAut.conj k ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) →
      ∀ w ∈ W, ∃ k : K, Odd (orderOf k) ∧ k * u₁ = u₁ * k ∧ α w = MulAut.conj k := by
  intro F _ _ hF K _ _ e u₁ hu₁c hu₁1 M _ _ α hα W hWodd hWab hX
  have hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1 := fun c hc => center_sq_eq_one hF e hc
  have hperf := perfect_of_SL2 hF e
  set ub : K ⧸ Subgroup.center K := (u₁ : K ⧸ Subgroup.center K) with hub
  have hub2 : orderOf ub = 2 := by
    have h1 : ub ^ 2 = 1 := by
      rw [hub, ← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hu₁c
    have h2 : ub ≠ 1 := by
      intro h
      exact hu₁1 (hZ u₁ ((QuotientGroup.eq_one_iff u₁).mp h))
    exact orderOf_eq_prime h1 h2
  let αb : M →* MulAut (K ⧸ Subgroup.center K) :=
    (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K).comp α
  have hαb_mk : ∀ (m : M) (x : K), αb m (x : K ⧸ Subgroup.center K) = ((α m x : K) : K ⧸ Subgroup.center K) :=
    fun m x => CFSG.GH74.GLS.IVK.Lifted.autQuotCenter_mk (α m) x
  have hαb : ∀ m : M, αb m ub = ub := by
    intro m
    rw [hub, hαb_mk, QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using hα m
  have hXb : ∀ kb ∈ CFSG.GH74.GLS.IVK.xu (MulAut.conj ub),
      ∃ m : M, αb m = MulAut.conj kb ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
    intro kb hkb
    obtain ⟨k, hk, hkc, hkk⟩ := lift_xu hZ hkb
    obtain ⟨m, hm, hmW⟩ := hX k hk hkc
    refine ⟨m, ?_, hmW⟩
    ext x
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [hαb_mk, hm, MulAut.conj_apply, MulAut.conj_apply, ← hkk]
    simp
  have hmain := odd_abelian_le_xuInn hF (quotCenterEquivL2 e) hub2 αb hαb W hWodd hWab hXb
  intro w hw
  obtain ⟨kb, hkb, hkbw⟩ := hmain w hw
  obtain ⟨k, hk, hkc, hkk⟩ := lift_xu hZ hkb
  refine ⟨k, hk, hkc, ?_⟩
  have hφ : α w * (MulAut.conj k)⁻¹ = 1 := by
    apply CFSG.GH74.GLS.IVK.Lifted.mulAut_eq_one_of_central_diff hperf
    intro x
    have h1 : (((α w * (MulAut.conj k)⁻¹) x : K) : K ⧸ Subgroup.center K) =
        (x : K ⧸ Subgroup.center K) := by
      rw [MulAut.mul_apply]
      have h2 : ((MulAut.conj k)⁻¹ x) = k⁻¹ * x * k := by
        simp
      rw [h2, ← hαb_mk, ← hkbw, MulAut.conj_apply, ← hkk]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    have h3 := QuotientGroup.eq_iff_div_mem.mp h1
    simpa [div_eq_mul_inv] using h3
  have := congrArg (· * MulAut.conj k) hφ
  simpa using this

end CFSG.GH74.GLS.SP.Local
