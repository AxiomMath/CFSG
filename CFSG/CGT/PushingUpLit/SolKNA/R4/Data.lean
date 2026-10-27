module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Spine
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {r : ℕ} {G : Type} [Group G] [Finite G]

namespace StdR

variable {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G} (h : StdR r R S t T)
include h

theorem natCard_rSet {R' : Subgroup G} (hR' : R' ∈ RSet (CoreAssembly.conjClass (tightCore R))) :
    Nat.card R' = 2 ^ r := by
  obtain ⟨J, hJ, P, rfl⟩ := hR'
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := CoreAssembly.mem_conjClass_self _
  have hsyl := h.datum.sylow_core
  have h1 := Sec6Gen.natCard_isSylow2In_eq h.datum.hypOmegaGen hK hJ hsyl
    (isSylow2In_map_sylow J P)
  rw [← h1]
  obtain ⟨e⟩ := h.quat
  rw [Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by have := h.three_le; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_add]
  ring

theorem tightMemStd : TightMemStdR r (tightCore R) t where
  three_le := h.three_le
  isUniqueInvolution := h.datum.isUniqueInvolution_core
  le_centralizer := h.datum.le_centralizer_core
  hypGen := h.datum.hypOmegaGen
  normEq := h.datum.normalizer_core_eq
  edgeless := h.edgeless
  natCard_rSet := h.natCard_rSet

theorem exists_sylow_le : ∃ Q₀ : Sylow 2 (tightCore R),
    (Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype ≤ (T : Subgroup G) := by
  have hRK := h.datum.sylow_core
  have hRK2 : IsPGroup 2 (((S : Subgroup R).map R.subtype).subgroupOf (tightCore R)) :=
    hRK.2.1.comap_subtype
  obtain ⟨Q, hQ⟩ := hRK2.exists_le_sylow
  have heq : (Q : Subgroup (tightCore R)).map (tightCore R).subtype =
      (S : Subgroup R).map R.subtype :=
    hRK.2.2 _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _)
      (by rw [← Subgroup.map_subgroupOf_eq_of_le hRK.1]; exact Subgroup.map_mono hQ)
  exact ⟨Q, heq ▸ h.hST⟩

theorem sylowData (hmu : ¬ AllTypeTwo (tightCore R) t) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (hWT : W ≤ (T : Subgroup G)) :
    TightSylowDataR r (tightCore R) t T W where
  tight := h.tightMemStd
  mu := hmu
  sylow := h.exists_sylow_le
  hSz := h.hTt
  hW := hW
  hWS := hWT

end StdR

section Basic

variable {K : Subgroup G} {z : G}

namespace TightMemStdR

theorem eight_le_natCard_rSet (ht : TightMemStdR r K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) : 8 ≤ Nat.card R := by
  rw [ht.natCard_rSet hR]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) ht.three_le

theorem centralizer_le_normalizer (ht : TightMemStdR r K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  ht.normEq.ge

theorem centralizer_le_normalizer_member (ht : TightMemStdR r K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨a, rfl⟩ := hJ
  have hu' : a * z * a⁻¹ = u := (ht.isUniqueInvolution.conj a).eq hu
  intro v hv
  have hv' : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hv
  have hva : a⁻¹ * v * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
    calc a⁻¹ * v * a * z = a⁻¹ * (v * (a * z * a⁻¹)) * a := by group
      _ = a⁻¹ * (v * u) * a := by rw [hu']
      _ = a⁻¹ * (u * v) * a := by rw [hv']
      _ = a⁻¹ * ((a * z * a⁻¹) * v) * a := by rw [hu']
      _ = z * (a⁻¹ * v * a) := by group
  rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul, show v * a = a * (a⁻¹ * v * a) by group,
    conjSub_mul, conjSub_eq_of_mem_normalizer hva]

theorem not_le_centralizer_of_mem_rSet (ht : TightMemStdR r K z) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K) (hne : J₁ ≠ J₂)
    {u : G} (hu : IsUniqueInvolution J₂ u) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁J : R₁ ≤ J₁) :
    ¬ R₁ ≤ Subgroup.centralizer ({u} : Set G) := fun hC =>
  S1911.not_le_normalizer_of_mem_rSet ht.edgeless h₁ h₂ hne hR₁ hR₁J
    (hC.trans (ht.centralizer_le_normalizer_member h₂ hu))

end TightMemStdR

namespace TightSylowDataR

variable {S : Sylow 2 G} {W : Subgroup G} (hd : TightSylowDataR r K z S W)
include hd

theorem hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
  hd.hSz.trans hd.tight.centralizer_le_normalizer

theorem isSylow2In_inf : IsSylow2In ((S : Subgroup G) ⊓ K) K :=
  S1916.isSylow2In_inf S hd.hSz hd.tight.le_centralizer hd.tight.centralizer_le_normalizer

theorem inf_mem_rSet : (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hd.isSylow2In_inf

theorem mem_S : z ∈ (S : Subgroup G) := by
  have hzK := hd.tight.isUniqueInvolution
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hzK.sq hzK.ne_one
  have hSN' : (S : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    fun s hs => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left
          (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hs)).symm k).eq))
  have h2 : IsPGroup 2 ↥((S : Subgroup G) ⊔ Subgroup.zpowers z) :=
    S.isPGroup'.to_sup_of_normal_right' hz2 hSN'
  have h3 := S.is_maximal' h2 le_sup_left
  exact h3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem mem_inf : z ∈ (S : Subgroup G) ⊓ K := ⟨hd.mem_S, hd.tight.isUniqueInvolution.mem⟩

end TightSylowDataR

namespace TightSylowDataTR

variable {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}
  (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem member_ne : L ≠ K := by
  intro h
  apply hd.ne
  exact (h ▸ hd.invL).eq hd.tight.isUniqueInvolution

theorem htS : t ∈ (S : Subgroup G) := hd.hWS (hd.leW hd.memT)

theorem not_mem_centralizer_inf :
    t ∉ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro hC
  refine hd.tight.not_le_centralizer_of_mem_rSet (CoreAssembly.mem_conjClass_self K) hd.memL
    hd.member_ne.symm hd.invL hd.toTightSylowDataR.inf_mem_rSet inf_le_right ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hC r hr

theorem isCyclic_V : IsCyclic ↥V := by
  obtain ⟨R, -, -, hcyc, -⟩ := hd.memV
  exact hcyc

theorem isPGroup_V : IsPGroup 2 V := S.isPGroup'.to_le (hd.leW.trans hd.hWS)

theorem four_le_card_V : 4 ≤ Nat.card V := by
  obtain ⟨R, hR, hVR, -, hidx⟩ := hd.memV
  have h8 := hd.tight.eight_le_natCard_rSet hR
  have h1 := Subgroup.relIndex_mul_card (H := V) (K := R)
  rw [inf_eq_left.mpr hVR, hidx] at h1
  omega

theorem htN : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hN := hd.hSN hd.htS
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hN y]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hd.htS h1)
      ((S : Subgroup G).inv_mem hd.htS), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hd.htS) h1)
      hd.htS
    simpa [mul_assoc] using this

theorem inf_sec19Y_eq_bot : V ⊓ sec19Y K z = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    hd.isPGroup_V.to_le (Subgroup.zpowers_le.mpr hx.1)
  obtain ⟨m, hm⟩ := hx2.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hm
    exact hx1 hm
  have h2dvd : 2 ∣ Nat.card (Subgroup.zpowers x) := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨w, hwx⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hw2' : orderOf w = 2 := by rw [← Subgroup.orderOf_mk w hwx]; exact hw2
  have hwV : w ∈ V := (Subgroup.zpowers_le.mpr hx.1) hwx
  have hwsq : w * w = 1 := by rw [← sq, ← hw2', pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2'
    omega
  have hwt : w = t :=
    S1916.eq_of_mul_self_eq_one_of_isCyclic hd.isCyclic_V hwV hd.memT hwsq hd.invL.sq hw1
      hd.invL.ne_one
  have htY : t ∈ sec19Y K z := by
    have : w ∈ sec19Y K z := (Subgroup.zpowers_le.mpr hx.2) hwx
    rwa [hwt] at this
  apply hd.not_mem_centralizer_inf
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (S1916.commute_of_mem_centralizerModOdd htY inf_le_right
    (S.isPGroup'.to_le inf_le_left) hd.htN hy).symm

end TightSylowDataTR

namespace TightMemStdR

variable (ht : TightMemStdR r K z)
include ht

theorem conjSub_eq_conjSub {a b : G} (h : a * z * a⁻¹ = b * z * b⁻¹) :
    conjSub a K = conjSub b K := by
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h]
      _ = z * (b⁻¹ * a) := by group
  calc conjSub a K = conjSub b (conjSub (b⁻¹ * a) K) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b K := by rw [conjSub_eq_of_mem_normalizer hn]

theorem odd_card_inf {K₁ J : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    (hJ : J ∈ CoreAssembly.conjClass K) (hne : K₁ ≠ J) : Odd (Nat.card ↥(K₁ ⊓ J)) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K K₁ hK₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu'
    omega
  have huu : (u : G) * u = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
  have hI := ht.isUniqueInvolution
  have ha := ((hI.conj a).unique u (Subgroup.mem_inf.mp u.2).1 huu).resolve_left hu1
  have hb := ((hI.conj b).unique u (Subgroup.mem_inf.mp u.2).2 huu).resolve_left hu1
  exact hne (ht.conjSub_eq_conjSub (ha.symm.trans hb))

theorem exists_isUniqueInvolution_member {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) :
    ∃ u : G, IsUniqueInvolution J u := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  exact ⟨_, ht.isUniqueInvolution.conj g⟩

theorem eq_of_isUniqueInvolution_member {J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ CoreAssembly.conjClass K)
    (h₂ : J₂ ∈ CoreAssembly.conjClass K) {u : G} (hu₁ : IsUniqueInvolution J₁ u)
    (hu₂ : IsUniqueInvolution J₂ u) : J₁ = J₂ := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K J₁ h₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J₂ h₂
  have ha := (ht.isUniqueInvolution.conj a).eq hu₁
  have hb := (ht.isUniqueInvolution.conj b).eq hu₂
  exact ht.conjSub_eq_conjSub (ha.trans hb.symm)

end TightMemStdR

namespace TightSylowDataR

variable {S : Sylow 2 G} {W : Subgroup G} (hd : TightSylowDataR r K z S W)
include hd

theorem le_normalizer_inf :
    (S : Subgroup G) ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro s hs
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hd.hSN hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxK⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hxS) (Subgroup.inv_mem _ hs),
      (Subgroup.mem_normalizer_iff.mp hsK x).mp hxK⟩
  · rintro ⟨hxS, hxK⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hsK x).mpr hxK⟩
    have h1 : s⁻¹ * (s * x * s⁻¹) * s ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hxS) hs
    have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
    rwa [e] at h1

theorem natCard_inf : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 ^ r :=
  hd.tight.natCard_rSet hd.inf_mem_rSet

theorem eight_le_card_inf : 8 ≤ Nat.card ↥((S : Subgroup G) ⊓ K) :=
  hd.tight.eight_le_natCard_rSet hd.inf_mem_rSet

theorem exists_eta :
    ∃ η : Set (Subgroup G), ∃ S' : Sylow 2 G, η ∈ etaSet (CoreAssembly.conjClass K) S' ∧
      (∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧ W = ⨆ U ∈ η, U ∧
      ∀ U ∈ η, U ≤ (S : Subgroup G) := by
  obtain ⟨η, ⟨S', hηS', hinv⟩, hWη⟩ := hd.hW
  refine ⟨η, S', hηS', hinv, hWη, fun U hU => ?_⟩
  have hUW : U ≤ W := hWη ▸ le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) U hU
  exact hUW.trans hd.hWS

theorem comm_of_mem : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, S', hη, hinv, hWη, -⟩ := hd.exists_eta
  have hΩ := hd.tight.hypGen
  have h := (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1
  rw [hWη]
  exact h

theorem mem_eta_of_le {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K)) (hUW : U ≤ W) : U ∈ η := by
  have hΩ := hd.tight.hypGen
  have h := (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).2
  rw [← h]
  exact ⟨hU, hWη ▸ hUW⟩

theorem inf_mem_eta {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    (hηS : ∀ U ∈ η, U ≤ (S : Subgroup G)) : K ⊓ W ∈ η := by
  have h8 := hd.eight_le_card_inf
  rw [inf_comm] at h8
  have h := Sec6Gen.l6_11Gen G _ hd.tight.hypGen S η (S1911.mem_etaG hη hinv) hηS K
    (CoreAssembly.mem_conjClass_self K) (by omega)
  rwa [← hWη] at h

theorem conjSub_mem_eta {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) {S₁ : Sylow 2 G}
    (hηS₁ : ∀ U ∈ η, U ≤ (S₁ : Subgroup G)) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁S₁ : R₁ ≤ (S₁ : Subgroup G)) {x : G}
    (hx : x ∈ R₁) : ∀ U ∈ η, conjSub x U ∈ η :=
  (Sec6Gen.l6_10Gen G _ hd.tight.hypGen S₁ η (S1911.mem_etaG hη hinv) hηS₁).1 R₁ hR₁ hR₁S₁ x hx

end TightSylowDataR

end Basic

end CFSG.CGT.PushingUpLit.SolKNA.R4
