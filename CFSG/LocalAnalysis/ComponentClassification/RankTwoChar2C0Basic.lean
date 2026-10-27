module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.ComponentClassification.RankTwoChar2C0

open Subgroup CFSG
open CFSG.LocalAnalysis.ComponentInitial
  (parabolic_containing_subgroup_local_characteristic_transfer isCharacteristicP_of_mulEquiv)

theorem isCharacteristicP_of_le_normalizer {F : Type*} [Group F] {H Q : Subgroup F}
    (hQH : Q ≤ H) (hQp : IsPGroup 2 Q) (hnorm : H ≤ normalizer (Q : Set F))
    (hcen : ∀ c ∈ H, c ∈ centralizer (Q : Set F) → ∃ k : ℕ, c ^ 2 ^ k = 1) :
    IsCharacteristicP 2 H := by
  have hUn : (Q.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr hnorm
  have hUp : IsPGroup 2 (Q.subgroupOf H) := hQp.comap_of_injective H.subtype H.subtype_injective
  have hUO : Q.subgroupOf H ≤ pCore 2 H := le_sSup ⟨hUn, hUp⟩
  have hCp : IsPGroup 2 (centralizer ((Q.subgroupOf H : Subgroup H) : Set H)) := by
    intro c
    have hcQ : ((c : H) : F) ∈ centralizer (Q : Set F) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hq' : (⟨q, hQH hq⟩ : H) ∈ Q.subgroupOf H := mem_subgroupOf.mpr hq
      exact congrArg Subtype.val (mem_centralizer_iff.mp c.2 _ hq')
    obtain ⟨k, hk⟩ := hcen _ (c : H).2 hcQ
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hCn : (centralizer ((Q.subgroupOf H : Subgroup H) : Set H)).Normal := by
    have := hUn
    exact normal_centralizer
  change centralizer (pCore 2 H : Set H) ≤ pCore 2 H
  exact (centralizer_le hUO).trans (le_sSup ⟨hCn, hCp⟩)

theorem isCharacteristicP_centralizer_of_normal_pGroup_le {F : Type*} [Group F] {z : F}
    {Q : Subgroup F} (hQC : Q ≤ centralizer {z}) (hQp : IsPGroup 2 Q)
    (hnorm : ∀ c ∈ centralizer ({z} : Set F), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hcen : ∀ c ∈ centralizer ({z} : Set F), (∀ q ∈ Q, c * q = q * c) → c ∈ Q) :
    IsCharacteristicP 2 (centralizer ({z} : Set F)) := by
  refine isCharacteristicP_of_le_normalizer hQC hQp (fun c hc => ?_) (fun c hc hcQ => ?_)
  · rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hnorm c hc q hq, fun hq => ?_⟩
    have h1 := hnorm c⁻¹ (inv_mem hc) _ hq
    have h2 : c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q := by group
    rwa [h2] at h1
  · obtain ⟨k, hk⟩ := hQp ⟨c, hcen c hc fun q hq => (mem_centralizer_iff.mp hcQ q hq).symm⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isCharacteristicP_centralizer_of_two_radical {F M : Type*} [Group F] [Group M]
    (φ : F →* M) (hφ : Function.Injective φ) {z : F} (R : Subgroup M)
    (hRX : R ≤ φ.range ⊓ centralizer ({φ z} : Set M))
    (hnorm : ∀ x ∈ φ.range ⊓ centralizer ({φ z} : Set M), x ∈ normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ φ.range ⊓ centralizer ({φ z} : Set M),
      x ∈ centralizer (R : Set M) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsCharacteristicP 2 (centralizer ({z} : Set F)) := by
  have hφC : ∀ x : F, x ∈ centralizer ({z} : Set F) →
      φ x ∈ φ.range ⊓ centralizer ({φ z} : Set M) := by
    intro x hx
    refine mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hx ⊢
    rw [← map_mul, ← map_mul, hx]
  have hUC : R.comap φ ≤ centralizer ({z} : Set F) := by
    intro u hu
    have h := mem_centralizer_singleton_iff.mp (mem_inf.mp (hRX hu)).2
    rw [mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul]; exact h)
  have hUp : IsPGroup 2 (R.comap φ) := by
    intro u
    obtain ⟨k, hk⟩ := hR (φ u) u.2
    refine ⟨k, Subtype.ext (hφ ?_)⟩
    change φ ((u : F) ^ 2 ^ k) = φ 1
    rw [map_pow, hk, map_one]
  refine isCharacteristicP_of_le_normalizer hUC hUp (fun c hc => ?_) (fun c hc hcU => ?_)
  · rw [mem_normalizer_iff]
    intro q
    change φ q ∈ R ↔ φ (c * q * c⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.mp (hnorm _ (hφC c hc)) (φ q)
  · have hxc : φ c ∈ centralizer (R : Set M) := by
      rw [mem_centralizer_iff]
      intro r hr
      obtain ⟨u, hu⟩ := (mem_inf.mp (hRX hr)).1
      have hu' : u ∈ R.comap φ := by
        change φ u ∈ R
        rw [hu]
        exact hr
      have := mem_centralizer_iff.mp hcU u hu'
      rw [← hu, ← map_mul, ← map_mul, this]
    obtain ⟨k, hk⟩ := hcent _ (hφC c hc) hxc
    exact ⟨k, hφ (by rw [map_pow, hk, map_one])⟩

theorem map_centralizer_mulEquiv {T X : Type*} [Group T] [Group X] (e : T ≃* X) (u : T) :
    (centralizer ({u} : Set T)).map e.toMonoidHom = centralizer ({e u} : Set X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem isCharacteristicP_centralizer_of_mulEquiv {T X : Type*} [Group T] [Group X] {p : ℕ}
    (e : T ≃* X)
    (h : ∀ x : X, orderOf x = 2 → IsCharacteristicP p (centralizer ({x} : Set X))) :
    ∀ u : T, orderOf u = 2 → IsCharacteristicP p (centralizer ({u} : Set T)) := by
  intro u hu
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  exact isCharacteristicP_of_mulEquiv
    (((centralizer ({u} : Set T)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_mulEquiv e u))).symm (h (e u) hu')

theorem isCharacteristicP_centralizer_of_two_element {F : Type*} [Group F] [Finite F]
    (h : ∀ z : F, orderOf z = 2 → IsCharacteristicP 2 (centralizer ({z} : Set F)))
    {x : F} (hx1 : x ≠ 1) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    IsCharacteristicP 2 (centralizer ({x} : Set F)) ∧
      pPrimeCore 2 (centralizer ({x} : Set F)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : x ^ 2 ^ Nat.find hx2 = 1 := Nat.find_spec hx2
  have hk0 : Nat.find hx2 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk
    exact hx1 hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hnot : ¬ x ^ 2 ^ m = 1 := Nat.find_min hx2 (by omega)
  have hfin : x ^ 2 ^ (m + 1) = 1 := by rw [show m + 1 = Nat.find hx2 by omega]; exact hk
  have hord : orderOf x = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hz2 : orderOf (x ^ 2 ^ m) = 2 := by
    refine orderOf_eq_prime ?_ hnot
    rw [← pow_mul, ← pow_succ]
    exact hfin
  set z := x ^ 2 ^ m with hz
  set P := centralizer ({z} : Set F) with hP
  have hPc : IsCharacteristicP 2 P := h z hz2
  set U : Subgroup F := (pCore 2 P).map P.subtype with hU
  have hUP : U ≤ P := map_subtype_le _
  have hUn : (U.subgroupOf P).Normal := by
    rw [hU, Subgroup.subgroupOf, comap_map_eq_self_of_injective P.subtype_injective]
    exact pCore_normal
  have hUp : IsPGroup 2 U := pCore_isPGroup.map _
  have hCU : centralizer (U : Set F) ⊓ P ≤ U := by
    rintro g ⟨hgC, hgP⟩
    refine ⟨⟨g, hgP⟩, hPc ?_, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hgC _ ⟨y, hy, rfl⟩)
  have hQP : zpowers x ≤ P := by
    rw [zpowers_le, hP, mem_centralizer_singleton_iff]
    exact (Commute.self_pow x _).eq
  have hQp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := m + 1) (by
    rw [Nat.card_zpowers, hord])
  have hHP : centralizer ({x} : Set F) ≤ P := by
    intro c hc
    rw [hP, mem_centralizer_singleton_iff]
    exact (Commute.pow_right (mem_centralizer_singleton_iff.mp hc) _).eq
  obtain ⟨-, hH, -, hcore⟩ := parabolic_containing_subgroup_local_characteristic_transfer
    (p := 2) (H := centralizer ({x} : Set F)) hUP hUn hUp hCU hQP hQp
    (Or.inr (CFSG.ClassicalInvolution.centralizer_zpowers_eq x).symm) hHP
  exact ⟨hH, hcore⟩

theorem isCharacteristicP_of_normal {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (N : Subgroup K) [N.Normal] (hK : IsCharacteristicP p K) : IsCharacteristicP p ↥N := by
  have hKF := (isCharacteristicP_iff_generalizedFitting_eq_pCore K p).mp hK
  have hmono := CFSG.ComponentClassification.GeneralizedFitting.normal_monotone N
  rw [← generalizedFitting_eq_componentClassification,
    ← generalizedFitting_eq_componentClassification, hKF] at hmono
  have hFp : IsPGroup p ↥(generalizedFitting ↥N) := by
    have h := (pCore_isPGroup (p := p) (G := K)).to_le hmono
    exact h.of_injective ((generalizedFitting ↥N).equivMapOfInjective N.subtype
      N.subtype_injective).toMonoidHom (MulEquiv.injective _)
  have hFn : (generalizedFitting ↥N).Normal := by
    rw [generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hFO : generalizedFitting ↥N ≤ pCore p ↥N := le_sSup ⟨hFn, hFp⟩
  change centralizer (pCore p ↥N : Set ↥N) ≤ pCore p ↥N
  exact (centralizer_le hFO).trans ((centralizer_generalizedFitting_le ↥N).trans hFO)

theorem map_fittingSubgroup_le {C R : Type*} [Group C] [Group R] [Finite C] (ψ : C →* R)
    (hψ : Function.Surjective ψ) : (fittingSubgroup C).map ψ ≤ fittingSubgroup R :=
  CFSG.WholeGroup.fittingSubgroup_map_le_of_surjective ψ hψ

theorem map_generalizedFitting_le {C R : Type*} [Group C] [Group R] [Finite C] (ψ : C →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center C) :
    (generalizedFitting C).map ψ ≤ generalizedFitting R := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup]
  refine sup_le_sup (map_fittingSubgroup_le ψ hψ) ?_
  rw [layer_eq_componentClassification, layer_eq_componentClassification,
    CentralComponentQuotients.layer_map ψ hψ hker]

theorem exists_two_pow_mem_ker {C R : Type*} [Group C] [Group R] [Finite C] (ψ : C →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center C) (hR : IsCharacteristicP 2 R)
    {c : C} (hc : c ∈ generalizedFitting C) : ∃ k : ℕ, c ^ 2 ^ k ∈ ψ.ker := by
  have : Finite R := Finite.of_surjective ψ hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (isCharacteristicP_iff_generalizedFitting_eq_pCore R 2).mp hR
  have hmem : ψ c ∈ pCore 2 R := hF ▸ map_generalizedFitting_le ψ hψ hker ⟨c, hc, rfl⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := R)) ⟨ψ c, hmem⟩
  refine ⟨k, ?_⟩
  rw [MonoidHom.mem_ker, map_pow]
  simpa using congrArg Subtype.val hk

theorem le_ker_of_odd {C R : Type*} [Group C] [Group R] [Finite C] (ψ : C →* R)
    (hψ : Function.Surjective ψ) (hR : IsCharacteristicP 2 R) {W : Subgroup C}
    (hW : W.Normal) (hodd : Odd (Nat.card W)) : W ≤ ψ.ker := by
  have : Finite R := Finite.of_surjective ψ hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore := pPrimeCore_eq_bot_of_isCharacteristicP R 2 hR
  have hcop : Nat.Coprime 2 (Nat.card (W.map ψ)) :=
    (Nat.coprime_two_left.mpr hodd).of_dvd_right (W.card_map_dvd ψ)
  have hmap : W.map ψ ≤ pPrimeCore 2 R := le_sSup ⟨hW.map ψ hψ, hcop⟩
  rw [hcore, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
  exact hmap

variable {G : Type} [Group G]

theorem conj_mem_centralizer_of_mk_commute {A : Subgroup G} {a' g c : A}
    (hg : (QuotientGroup.mk g : A ⧸ center A) * QuotientGroup.mk a' =
      QuotientGroup.mk a' * QuotientGroup.mk g)
    (hc : c * a' = a' * c) : g * c * g⁻¹ * a' = a' * (g * c * g⁻¹) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hg
  set w := (g * a')⁻¹ * (a' * g) with hw
  have hga : a' * g = g * a' * w := by rw [hw]; group
  have hwc : w * c = c * w := (mem_center_iff.mp hg c).symm
  have hga' : g⁻¹ * a' = a' * w * g⁻¹ := by
    calc g⁻¹ * a' = g⁻¹ * (a' * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a' * w) * g⁻¹ := by rw [hga]
      _ = a' * w * g⁻¹ := by group
  calc g * c * g⁻¹ * a' = g * c * (g⁻¹ * a') := by group
    _ = g * (c * a') * w * g⁻¹ := by rw [hga']; group
    _ = g * a' * (c * w) * g⁻¹ := by rw [hc]; group
    _ = g * a' * w * c * g⁻¹ := by rw [← hwc]; group
    _ = a' * (g * c * g⁻¹) := by rw [← hga]; group

variable [Finite G]

theorem generalizedFitting_centralizer_of_isCharacteristicP {A : Subgroup G} {a : G}
    (haA : a ∈ A)
    (hchar : IsCharacteristicP 2 (centralizer
      ({(QuotientGroup.mk (⟨a, haA⟩ : A) : A ⧸ center A)} : Set (A ⧸ center A)))) :
    (∀ y ∈ inSubgroup generalizedFitting (A ⊓ centralizer ({a} : Set G)),
      ∃ k : ℕ, y ^ 2 ^ k ∈ (center A).map A.subtype) ∧
    ∀ W : Subgroup G, W ≤ A ⊓ centralizer ({a} : Set G) →
      A ⊓ centralizer ({a} : Set G) ≤ normalizer (W : Set G) → Odd (Nat.card W) →
        W ≤ (center A).map A.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := A ⊓ centralizer ({a} : Set G) with hCdef
  set a' : A := ⟨a, haA⟩ with ha'
  set D := centralizer ({(QuotientGroup.mk a' : A ⧸ center A)} : Set (A ⧸ center A)) with hD
  let ψ : C →* A ⧸ center A := (QuotientGroup.mk' (center A)).comp (inclusion inf_le_left)
  have hψ : ∀ c : C, ψ c = QuotientGroup.mk (inclusion inf_le_left c) := fun _ => rfl
  have hca : ∀ c : C, inclusion inf_le_left c * a' = a' * inclusion inf_le_left c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2)
  have hψD : ψ.range ≤ D := by
    rintro _ ⟨c, rfl⟩
    rw [hD, mem_centralizer_singleton_iff, hψ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      hca c]
  have hnormal : (ψ.range.subgroupOf D).Normal := by
    refine ⟨fun r hr x => ?_⟩
    rw [mem_subgroupOf] at hr ⊢
    obtain ⟨c, hc⟩ := hr
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : A ⧸ center A)
    have hxD := mem_centralizer_singleton_iff.mp x.2
    rw [← hg] at hxD
    have hcomm := conj_mem_centralizer_of_mk_commute hxD (hca c)
    have hmem : ((g * inclusion inf_le_left c * g⁻¹ : A) : G) ∈ C :=
      mem_inf.mpr ⟨(g * inclusion inf_le_left c * g⁻¹).2,
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    change QuotientGroup.mk (g * inclusion inf_le_left c * g⁻¹) = _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg, ← hψ, hc]
    simp
  have hR : IsCharacteristicP 2 ψ.range := by
    have h1 := isCharacteristicP_of_normal (ψ.range.subgroupOf D) hchar
    exact isCharacteristicP_of_mulEquiv (subgroupOfEquivOfLe hψD) h1
  have hkerZ : ∀ c : C, c ∈ ψ.ker → (c : G) ∈ (center A).map A.subtype := by
    intro c hc
    rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff] at hc
    exact ⟨_, hc, rfl⟩
  have hker : ψ.rangeRestrict.ker ≤ center C := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff] at hc
    rw [mem_center_iff]
    intro d
    apply Subtype.ext
    have := congrArg Subtype.val (mem_center_iff.mp hc (inclusion inf_le_left d))
    simpa using this
  refine ⟨?_, fun W hWC hCW hodd => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := exists_two_pow_mem_ker ψ.rangeRestrict ψ.rangeRestrict_surjective hker hR hc
    rw [MonoidHom.ker_rangeRestrict] at hk
    exact ⟨k, by simpa using hkerZ _ hk⟩
  · have hWn : (W.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hWC).mpr hCW
    have hWodd : Odd (Nat.card (W.subgroupOf C)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
      exact hodd
    have hle := le_ker_of_odd ψ.rangeRestrict ψ.rangeRestrict_surjective hR hWn hWodd
    rw [MonoidHom.ker_rangeRestrict] at hle
    intro w hw
    exact hkerZ ⟨w, hWC hw⟩ (hle (mem_subgroupOf.mpr hw))

end CFSG.ComponentClassification.RankTwoChar2C0
