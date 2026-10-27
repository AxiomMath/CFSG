module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainSylow
public import CFSG.ClassicalInvolution.Q3.Q3T6FusConj
public import CFSG.ClassicalInvolution.AschTight.Sec7L713G
public import CFSG.ClassicalInvolution.AschTight.S19TSq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Facts



variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

structure FL3Facts (hd : Sec19DataT3 K z S W L t V) : Prop where
  UKW : K ⊓ W ∈ USet (CoreAssembly.conjClass K)
  invol_eq_or : ∀ {η : Set (Subgroup G)} {S' : Sylow 2 G},
    η ∈ etaSet (CoreAssembly.conjClass K) S' →
    (∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) → W = ⨆ U ∈ η, U →
    ∀ {A : Subgroup G}, A ∈ η → ∀ {J : Subgroup G}, J ∈ CoreAssembly.conjClass K → A ≤ J →
      ∀ {u : G}, IsUniqueInvolution J u → u = z ∨ u = t ∨ u = t * z
  invol_mem_W : ∀ {e : G}, e ∈ W → e * e = 1 → e ≠ 1 → e = z ∨ e = t ∨ e = t * z
  exists_mul : ∃ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ = t * z
  SW : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)
  CK : ∀ {y : G}, y ∈ (S : Subgroup G) →
    y ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) →
      y ∈ centralizerModOdd ⊤ K
  starSymm : ∀ {K₁ J : Subgroup G}, K₁ ∈ CoreAssembly.conjClass K → J ∈ CoreAssembly.conjClass K →
    J ∈ omegaStarNbr (CoreAssembly.conjClass K) K₁ → K₁ ∈ omegaStarNbr (CoreAssembly.conjClass K) J
  Bconj : ∀ {x d : G}, x ∈ S19B.sec19BPrime K S W L → d * z = z * d →
    d * x * d⁻¹ ∈ (S : Subgroup G) → d * x * d⁻¹ ∈ S19B.sec19BPrime K S W L

namespace FL3Facts

variable {hd : Sec19DataT3 K z S W L t V} (hF : FL3Facts hd)

include hF

theorem hypGen : HypOmegaGen (CoreAssembly.conjClass K) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hd.tight.hyp

theorem hzW : z ∈ W := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hF.hypGen hF.UKW
  exact (inf_le_right : K ⊓ W ≤ W)
    (S1911.mem_of_le_member hd.tight.isUniqueInvolution inf_le_left
      (Sec6Gen.isPGroup_of_mem_USet hF.hypGen hF.UKW) (by omega))

theorem comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := abelian_of_mem_WSet3 hF.hypGen hd.hW

theorem exists_eta : ∃ η : Set (Subgroup G), ∃ S' : Sylow 2 G,
    η ∈ etaSet (CoreAssembly.conjClass K) S' ∧
      (∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧ W = ⨆ U ∈ η, U ∧
      ∀ U ∈ η, U ≤ (S : Subgroup G) := by
  obtain ⟨η, ⟨S', hηS', hinv⟩, hWη⟩ := hd.hW
  refine ⟨η, S', hηS', hinv, hWη, fun U hU => ?_⟩
  have hUW : U ≤ W := hWη ▸ le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) U hU
  exact hUW.trans hd.hWS

theorem invol_eq_or_of_mem_USet3 {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUS : U ≤ (S : Subgroup G)) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hUJ : U ≤ J) {u : G} (hu : IsUniqueInvolution J u) : u = z ∨ u = t ∨ u = t * z := by
  have hΩ := hF.hypGen
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hF.exists_eta
  obtain ⟨V₀, ⟨hV₀η, hor⟩, -⟩ := Sec6Gen.six_eight hΩ S hU hUS (S1911.mem_etaG hη hinv) hηS
  rcases hor with h | h
  · exact hF.invol_eq_or hη hinv hWη hV₀η hJ (h ▸ hUJ) hu
  · obtain ⟨J₂, hJ₂, hRJ₂, -, -⟩ := mem_RSet_iff.mp h
    obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₂
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    have huU : u ∈ U := S1911.mem_of_le_member hu hUJ (S.isPGroup'.to_le hUS) (by omega)
    have hju : u = j := (hj.unique u (hRJ₂ (Subgroup.mem_sup_left huU)) hu.sq).resolve_left
      hu.ne_one
    exact hF.invol_eq_or hη hinv hWη hV₀η hJ₂ (le_sup_right.trans hRJ₂) (hju ▸ hj)

theorem exists_conj_eq_t3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t := by
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  obtain ⟨g, hgx, hgz⟩ := exists_conj_eq_t_of_centralizes3 hF.hypGen hd.tight.edgeless
    hd.tight.isUniqueInvolution hd.tight.centralizer_le_normalizer hd.hW hd.hWS hF.hzW
    hd.toSec19Data3.isSylow2In_inf hd.memL hd.invL (hd.leW hd.memT) hd.ne hxS hxR hxW hxL
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgx, hgz⟩

theorem exists_conj_eq_mul_z3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t * z := by
  obtain ⟨g, hg, hgz⟩ := hF.exists_conj_eq_t3 hx
  obtain ⟨r, hrR, hrt⟩ := hF.exists_mul
  have hrx : r ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1.1.2 r hrR)
  refine ⟨r * g, Subgroup.mul_mem _ hrx hg, ?_⟩
  rw [← hrt, ← hgz]
  group

theorem exists_conj_eq_of_comm3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {s : G} (hJs : IsUniqueInvolution J s)
    (hsx : s * x = x * s) (hsne : s ≠ z) {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4)
    (hwz : w * z = z * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hΩ := hF.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hK := CoreAssembly.mem_conjClass_self K
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := hd.hSz hxS
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) :=
    hd.tight.centralizer_le_normalizer_member hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hsx.symm)
  have hxH : x ∈ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyz⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxJ y).mp hyJ,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hxz hyz) (Subgroup.inv_mem _ hxz)⟩
    · rintro ⟨hyJ, hyz⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxJ y).mpr hyJ, ?_⟩
      have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxz) hyz) hxz
      simpa [mul_assoc] using h
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hNH : J ⊓ Subgroup.centralizer ({z} : Set G) ⊔ Subgroup.zpowers x ≤
      Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxH)
  obtain ⟨P, hP, hxP⟩ := IsSylow2In.exists_ge hx2
    (le_sup_right : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({z} : Set G) ⊔ _)
  have hV₀ : IsSylow2In (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)))
      (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    S1916.isSylow2In_inf_of_le_normalizer hP le_sup_left hNH
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) := S19T.isPGroup_zpowers_of_orderOf_four hw4
  obtain ⟨V₁, hV₁, hwV₁⟩ := IsSylow2In.exists_ge hw2
    (Subgroup.zpowers_le.mpr ⟨hwJ, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩ :
      Subgroup.zpowers w ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have h4 : 4 ≤ Nat.card ↥(P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) := by
    rw [IsSylow2In.natCard_eq hV₀ hV₁]
    calc 4 = Nat.card (Subgroup.zpowers w) := by rw [Nat.card_zpowers, hw4]
      _ ≤ Nat.card V₁ := Subgroup.card_le_of_le hwV₁
  have hsV₀ : s ∈ P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    S1911.mem_of_le_member hJs (hV₀.1.trans inf_le_left) hV₀.2.1 (by omega)
  have hJK : J ≠ K := by
    rintro rfl
    exact hsne ((hI.unique s hJs.mem hJs.sq).resolve_left hJs.ne_one)
  have hV3 : P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)) ∈
      USet (CoreAssembly.conjClass K) := by
    rcases Sec6Gen.Pair.six_two hΩ ⟨hK, hJ, hI, hJs, hsne.symm⟩ hV₀ hsV₀ with
      ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · exact hV3
    · exact absurd ((hV₀.1.trans inf_le_right).trans
        (hd.tight.centralizer_le_normalizer_member hK hI))
        (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ hK hJK hV4
          (hV₀.1.trans inf_le_left))
  have hPz : P ≤ Subgroup.centralizer ({z} : Set G) :=
    hP.1.trans (sup_le inf_le_right (Subgroup.zpowers_le.mpr hxz))
  obtain ⟨c, hcz, hcP⟩ := exists_conj_le_of_sylow_le S hd.hSz hPz hP.2.1
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hcxS : c * x * c⁻¹ ∈ (S : Subgroup G) :=
    hcP (conj_mem_conjSub (hxP (Subgroup.mem_zpowers x)))
  have hx' := hF.Bconj hx hcz' hcxS
  have hU' := S19B.conjSub_mem_USet hΩ.conjInvariant hV3 c
  have hU'S : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ (S : Subgroup G) :=
    (conjSub_mono inf_le_left).trans hcP
  have hU'J : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ conjSub c J :=
    conjSub_mono (inf_le_right.trans inf_le_left)
  rcases hF.invol_eq_or_of_mem_USet3 hU' hU'S (hΩ.conjInvariant c J hJ) hU'J (hJs.conj c) with
    h | h | h
  · exfalso
    apply hsne
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = z := by rw [h, mul_assoc, ← hcz', inv_mul_cancel_left]
  · obtain ⟨h', hh', he⟩ := hF.exists_conj_eq_t3 hx'
    exact S19T.exists_conj_of_conj hcz' hh' (he.trans h.symm)
  · obtain ⟨h', hh', he⟩ := hF.exists_conj_eq_mul_z3 hx'
    exact S19T.exists_conj_of_conj hcz' hh' (he.trans h.symm)

theorem exists_conj_eq_of_comm'3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G} (hJs : IsUniqueInvolution J s)
    (hsx : s * x = x * s) {h₀ m : G} (hh₀ : h₀ ∈ Subgroup.centralizer ({x} : Set G))
    (hm : h₀ * z * h₀⁻¹ = m) (hsne : s ≠ m) {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4)
    (hwm : w * m = m * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hΩ := hF.hypGen
  have hh₀x : h₀ * x = x * h₀ := Subgroup.mem_centralizer_singleton_iff.mp hh₀
  have hJs₁ : IsUniqueInvolution (conjSub h₀⁻¹ J) (h₀⁻¹ * s * h₀) := by
    have h := hJs.conj h₀⁻¹
    rwa [inv_inv] at h
  have e : x = h₀⁻¹ * x * h₀ := by rw [mul_assoc, ← hh₀x, inv_mul_cancel_left]
  have hsx₁ : h₀⁻¹ * s * h₀ * x = x * (h₀⁻¹ * s * h₀) := by
    calc h₀⁻¹ * s * h₀ * x = h₀⁻¹ * s * h₀ * (h₀⁻¹ * x * h₀) := by rw [← e]
      _ = h₀⁻¹ * (s * x) * h₀ := by group
      _ = h₀⁻¹ * (x * s) * h₀ := by rw [hsx]
      _ = (h₀⁻¹ * x * h₀) * (h₀⁻¹ * s * h₀) := by group
      _ = x * (h₀⁻¹ * s * h₀) := by rw [← e]
  have hmz : z = h₀⁻¹ * m * h₀ := by rw [← hm]; group
  have hsne₁ : h₀⁻¹ * s * h₀ ≠ z := by
    intro h
    apply hsne
    calc s = h₀ * (h₀⁻¹ * s * h₀) * h₀⁻¹ := by group
      _ = m := by rw [h, hm]
  have hwJ₁ : h₀⁻¹ * w * h₀ ∈ conjSub h₀⁻¹ J := by
    have h := conj_mem_conjSub (n := h₀⁻¹) hwJ
    rwa [inv_inv] at h
  have hw4₁ : orderOf (h₀⁻¹ * w * h₀) = 4 := by
    rw [← hw4]
    exact (SemiconjBy.orderOf_eq h₀⁻¹ (by unfold SemiconjBy; group)).symm
  have hwz₁ : h₀⁻¹ * w * h₀ * z = z * (h₀⁻¹ * w * h₀) := by
    rw [hmz]
    calc h₀⁻¹ * w * h₀ * (h₀⁻¹ * m * h₀) = h₀⁻¹ * (w * m) * h₀ := by group
      _ = h₀⁻¹ * (m * w) * h₀ := by rw [hwm]
      _ = h₀⁻¹ * m * h₀ * (h₀⁻¹ * w * h₀) := by group
  obtain ⟨h, hh, he⟩ := hF.exists_conj_eq_of_comm3 hx (hΩ.conjInvariant h₀⁻¹ J hJ) hJs₁ hsx₁
    hsne₁ hwJ₁ hw4₁ hwz₁
  refine ⟨h₀ * h, Subgroup.mul_mem _ hh₀ hh, ?_⟩
  calc h₀ * h * z * (h₀ * h)⁻¹ = h₀ * (h * z * h⁻¹) * h₀⁻¹ := by group
    _ = s := by rw [he]; group

theorem exists_comm_of_comm3 {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G}
    (hJs : IsUniqueInvolution J s) (hsne : s ≠ z) {u : G} (huK : u ∈ K) (hu4 : orderOf u = 4)
    (hus : u * s = s * u) : ∃ w ∈ J, orderOf w = 4 ∧ w * z = z * w := by
  have hΩ := hF.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hK := CoreAssembly.mem_conjClass_self K
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := S19T.isPGroup_zpowers_of_orderOf_four hu4
  obtain ⟨V₀, hV₀, huV₀⟩ := IsSylow2In.exists_ge hu2
    (Subgroup.zpowers_le.mpr ⟨huK, Subgroup.mem_centralizer_singleton_iff.mpr hus⟩ :
      Subgroup.zpowers u ≤ K ⊓ Subgroup.centralizer ({s} : Set G))
  have h4 : 4 ≤ Nat.card V₀ := by
    calc 4 = Nat.card (Subgroup.zpowers u) := by rw [Nat.card_zpowers, hu4]
      _ ≤ Nat.card V₀ := Subgroup.card_le_of_le huV₀
  have hzV₀ : z ∈ V₀ := S1911.mem_of_le_member hI (hV₀.1.trans inf_le_left) hV₀.2.1 (by omega)
  have hKJ : K ≠ J := by
    intro h
    apply hsne
    rw [← h] at hJs
    exact (hI.unique s hJs.mem hJs.sq).resolve_left hJs.ne_one
  rcases Sec6Gen.Pair.six_two hΩ ⟨hJ, hK, hJs, hI, hsne⟩ hV₀ hzV₀ with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, hVN, -⟩ | ⟨hV4, -⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one] at h4
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one] at h4
    omega
  · have hstar : K ∈ omegaStarNbr (CoreAssembly.conjClass K) J :=
      ⟨hK, hKJ, V₀, hV3, hV₀.1.trans inf_le_left, hVN⟩
    obtain ⟨-, -, U₁, hU₁, hU₁J, hU₁N⟩ := hF.starSymm hJ hK hstar
    have hU₁z : U₁ ≤ Subgroup.centralizer ({z} : Set G) :=
      hU₁N.trans (S1911.normalizer_le_centralizer_member hI)
    obtain ⟨R, -, J₂, -, hRJ₂, hU₁R, hcyc, -, h4'⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₁
    obtain ⟨w, hwU, hww⟩ :=
      exists_mul_self_eq_of_isCyclic hJs hU₁J hcyc (hRJ₂.2.1.to_le hU₁R) h4'
    refine ⟨w, hU₁J hwU, ?_, Subgroup.mem_centralizer_singleton_iff.mp (hU₁z hwU)⟩
    have h1 : ¬ w ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, hww]
      exact hJs.ne_one
    have h2 : w ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two w, hww, pow_two s, hJs.sq]
    rw [orderOf_eq_prime_pow h1 h2]
    norm_num
  · exact absurd ((hV₀.1.trans inf_le_right).trans
      (hd.tight.centralizer_le_normalizer_member hJ hJs))
      (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hK hJ hKJ hV4
        (hV₀.1.trans inf_le_left))

theorem exists_conj_eq_of_comm_u3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹)) (hsne : g * z * g⁻¹ ≠ z) {u : G} (huK : u ∈ K)
    (hu4 : orderOf u = 4) (hus : u * (g * z * g⁻¹) = g * z * g⁻¹ * u) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hΩ := hF.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  obtain ⟨w, hwJ, hw4, hwz⟩ := hF.exists_comm_of_comm3 hJ (hI.conj g) hsne huK hu4 hus
  exact hF.exists_conj_eq_of_comm3 hx hJ (hI.conj g) hsx hsne hwJ hw4 hwz

theorem inv_of_mul3 {r : G} (hr : r ∈ (S : Subgroup G) ⊓ K) (hrt : r * t * r⁻¹ = t * z) :
    ∀ u ∈ K ⊓ W, r * u * r⁻¹ = u⁻¹ := by
  have hI := hd.tight.isUniqueInvolution
  have hΩ := hF.hypGen
  have hcomm := hF.comm
  have htW : t ∈ W := hd.leW hd.memT
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hrW : r ∉ W := by
    intro hrW
    have h1 : r * t * r⁻¹ = t := by rw [hcomm r hrW t htW]; group
    rw [h1] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hrU : r ∉ K ⊓ W := fun h => hrW h.2
  obtain ⟨R', hR', J, -, hRJ, hUR', hUc, hcard', h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hF.UKW
  have hU4 : Nat.card ↥(K ⊓ W) = 4 := by
    have h8 := hd.tight.natCard_rSet hR'
    omega
  have hRset := hd.toSec19Data3.inf_mem_rSet
  have hRcard : Nat.card ↥((S : Subgroup G) ⊓ K) = 8 := hd.tight.natCard_rSet hRset
  have hidx : (K ⊓ W).relIndex ((S : Subgroup G) ⊓ K) = 2 := by
    have h := Subgroup.relIndex_mul_card (K ⊓ W) ((S : Subgroup G) ⊓ K)
    rw [inf_eq_left.mpr hUR, hU4, hRcard] at h
    omega
  obtain ⟨u₀, hu₀⟩ := S19B.exists_zpowers_eq_of_isCyclic hUc
  have hu₀U : u₀ ∈ K ⊓ W := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hord : orderOf u₀ = 4 := by rw [← Nat.card_zpowers, hu₀, hU4]
  have hrN : r * u₀ * r⁻¹ ∈ K ⊓ W :=
    ⟨K.mul_mem (K.mul_mem hr.2 hu₀U.1) (K.inv_mem hr.2),
      (Subgroup.mem_normalizer_iff.mp (hF.SW hr.1) u₀).mp hu₀U.2⟩
  have hu₀4 : u₀ ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one u₀
  have hu₀2 : u₀ ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have hu₀1 : u₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  have hdich : r * u₀ * r⁻¹ = u₀ ∨ r * u₀ * r⁻¹ = u₀⁻¹ := by
    rw [← hu₀] at hrN
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hrN
    have hmod : u₀ ^ (m % 4) = u₀ ^ m := by simpa [hord] using zpow_mod_orderOf u₀ m
    rw [hm] at hmod
    have hm4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm4 with h | h | h | h
    · exfalso
      rw [h, zpow_zero] at hmod
      apply hu₀1
      calc u₀ = r⁻¹ * (r * u₀ * r⁻¹) * r := by group
        _ = 1 := by rw [← hmod]; group
    · left
      rw [h, zpow_one] at hmod
      exact hmod.symm
    · exfalso
      rw [h] at hmod
      have h2 : (r * u₀ * r⁻¹) * (r * u₀ * r⁻¹) = 1 := by
        rw [← hmod]
        calc u₀ ^ (2 : ℤ) * u₀ ^ (2 : ℤ) = u₀ ^ 4 := by
              rw [← zpow_add]
              norm_num
          _ = 1 := hu₀4
      apply hu₀2
      calc u₀ ^ 2 = u₀ * u₀ := sq u₀
        _ = r⁻¹ * ((r * u₀ * r⁻¹) * (r * u₀ * r⁻¹)) * r := by group
        _ = 1 := by rw [h2]; group
    · right
      rw [h] at hmod
      rw [← hmod]
      have : u₀ ^ (3 : ℤ) * u₀ = 1 := by
        calc u₀ ^ (3 : ℤ) * u₀ = u₀ ^ 4 := by
              rw [← zpow_add_one]
              norm_num
          _ = 1 := hu₀4
      exact eq_inv_of_mul_eq_one_left this
  rcases hdich with hA | hB
  ·
    exfalso
    have hcl := Sec7.eq_closure_of_index_two hidx hUR hu₀ hr hrU
    have hur : u₀ * r = r * u₀ := by
      calc u₀ * r = (r * u₀ * r⁻¹) * r := by rw [hA]
        _ = r * u₀ := by group
    have hpair : ({u₀, r} : Set G).Pairwise Commute := by
      intro a ha b hb _
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Commute.refl _
      · exact hur
      · exact hur.symm
      · exact Commute.refl _
    obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset).exists_not_commute
    rw [hcl] at hx hy
    have := Subgroup.isMulCommutative_closure hpair
    exact hxy (congrArg Subtype.val
      ((IsMulCommutative.is_comm : Std.Commutative (α := ↥(Subgroup.closure ({u₀, r} : Set G)))
        (· * ·)).comm ⟨x, hx⟩ ⟨y, hy⟩))
  · intro u hu
    rw [← hu₀] at hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, hB, inv_zpow]

theorem mul_t_mem_centralizer3 {u : G} (huU : u ∈ K ⊓ W) (huu : u * u = z) :
    u * t ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hF.comm
  have htW : t ∈ W := hd.leW hd.memT
  have hzW := hF.hzW
  have hzt : z * t = t * z := hcomm z hzW t htW
  have hut : u * t = t * u := hcomm u huU.2 t htW
  obtain ⟨r₀, hr₀, hr₀t⟩ := hF.exists_mul
  have hr₀u := hF.inv_of_mul3 hr₀ hr₀t u huU
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hr.1)
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hF.SW hr.1
  have hrtW : r * t * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hrN t).mp htW
  have hrt2 : r * t * r⁻¹ * (r * t * r⁻¹) = 1 := by
    calc r * t * r⁻¹ * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
      _ = 1 := by rw [hd.invL.sq]; group
  have hrt1 : r * t * r⁻¹ ≠ 1 := by
    intro h
    apply hd.invL.ne_one
    calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
      _ = 1 := by rw [h]; group
  have key : r * u * r⁻¹ * (r * t * r⁻¹) = u * t := by
    rcases hF.invol_mem_W hrtW hrt2 hrt1 with h | h | h
    · exfalso
      apply hd.ne
      calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
        _ = z := by rw [h, mul_assoc, ← hrz, inv_mul_cancel_left]
    · have hrr₀ : r * r₀ * t * (r * r₀)⁻¹ = t * z := by
        calc r * r₀ * t * (r * r₀)⁻¹ = r * (r₀ * t * r₀⁻¹) * r⁻¹ := by group
          _ = r * t * r⁻¹ * (r * z * r⁻¹) := by rw [hr₀t]; group
          _ = t * z := by rw [h, hrz, mul_inv_cancel_right]
      have h1 := hF.inv_of_mul3 (Subgroup.mul_mem _ hr hr₀) hrr₀ u huU
      have h2 : r₀⁻¹ * u * r₀ = u⁻¹ := by
        calc r₀⁻¹ * u * r₀ = (r₀⁻¹ * u⁻¹ * r₀)⁻¹ := by group
          _ = (r₀⁻¹ * (r₀ * u * r₀⁻¹) * r₀)⁻¹ := by rw [hr₀u]
          _ = u⁻¹ := by group
      have h3 : r * u * r⁻¹ = u := by
        calc r * u * r⁻¹ = (r * r₀) * (r₀⁻¹ * u * r₀) * (r * r₀)⁻¹ := by group
          _ = ((r * r₀) * u * (r * r₀)⁻¹)⁻¹ := by rw [h2]; group
          _ = u := by rw [h1, inv_inv]
      rw [h3, h]
    · have h1 := hF.inv_of_mul3 hr h u huU
      rw [h1, h]
      calc u⁻¹ * (t * z) = u⁻¹ * (z * t) := by rw [hzt]
        _ = u⁻¹ * (u * u) * t := by rw [huu]; group
        _ = u * t := by group
  calc r * (u * t) = (r * u * r⁻¹ * (r * t * r⁻¹)) * r := by group
    _ = u * t * r := by rw [key]

end FL3Facts

end Facts

end CFSG.ClassicalInvolution.Q3.Q3T6
