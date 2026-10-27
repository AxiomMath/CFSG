module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Core
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAut
public import CFSG.ClassicalInvolution.AschTight.S19TSq

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_conj_eq_t_of_mem {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t := by
  obtain ⟨g, hgB, hgz⟩ := hd.exists_conj_eq_t_of_BPrime
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (hgB x hx), hgz⟩

theorem exists_conj_eq_mul_z_of_mem {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t * z := by
  obtain ⟨g, hg, hgz⟩ := hd.exists_conj_eq_t_of_mem hx
  obtain ⟨r, hrR, hrt⟩ := hd.exists_conj_eq_mul
  have hrx : r ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1.1.2 r hrR)
  refine ⟨r * g, Subgroup.mul_mem _ hrx hg, ?_⟩
  rw [← hrt, ← hgz]
  group

theorem invol_eq_or_of_mem_USet {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUS : U ≤ (S : Subgroup G)) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hUJ : U ≤ J) {u : G} (hu : IsUniqueInvolution J u) : u = z ∨ u = t ∨ u = t * z := by
  have hΩ := hd.tight.hypGen
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hd.toTightSylowDataR.exists_eta
  obtain ⟨V₀, ⟨hV₀η, hor⟩, -⟩ := Sec6Gen.six_eight hΩ S hU hUS (S1911.mem_etaG hη hinv) hηS
  rcases hor with h | h
  · exact hd.invol_eq_or hη hinv hWη hV₀η hJ (h ▸ hUJ) hu
  · obtain ⟨J₂, hJ₂, hRJ₂, -, -⟩ := mem_RSet_iff.mp h
    obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₂
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    have huU : u ∈ U := S1911.mem_of_le_member hu hUJ (S.isPGroup'.to_le hUS) (by omega)
    have hju : u = j := (hj.unique u (hRJ₂ (Subgroup.mem_sup_left huU)) hu.sq).resolve_left
      hu.ne_one
    exact hd.invol_eq_or hη hinv hWη hV₀η hJ₂ (le_sup_right.trans hRJ₂) (hju ▸ hj)

theorem exists_conj_eq_of_comm {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {s : G} (hJs : IsUniqueInvolution J s)
    (hsx : s * x = x * s) (hsne : s ≠ z) {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4)
    (hwz : w * z = z * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hΩ := hd.tight.hypGen
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
  have hx' := hd.conj_mem_sec19BPrime hx hcz' hcxS
  have hU' := S19B.conjSub_mem_USet hΩ.conjInvariant hV3 c
  have hU'S : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ (S : Subgroup G) :=
    (conjSub_mono inf_le_left).trans hcP
  have hU'J : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ conjSub c J :=
    conjSub_mono (inf_le_right.trans inf_le_left)
  rcases hd.invol_eq_or_of_mem_USet hU' hU'S (hΩ.conjInvariant c J hJ) hU'J (hJs.conj c) with
    h | h | h
  · exfalso
    apply hsne
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = z := by rw [h, mul_assoc, ← hcz', inv_mul_cancel_left]
  · obtain ⟨h', hh', he⟩ := hd.exists_conj_eq_t_of_mem hx'
    exact S19T.exists_conj_of_conj hcz' hh' (he.trans h.symm)
  · obtain ⟨h', hh', he⟩ := hd.exists_conj_eq_mul_z_of_mem hx'
    exact S19T.exists_conj_of_conj hcz' hh' (he.trans h.symm)

theorem exists_conj_eq_of_comm' {x : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G} (hJs : IsUniqueInvolution J s)
    (hsx : s * x = x * s) {h₀ m : G} (hh₀ : h₀ ∈ Subgroup.centralizer ({x} : Set G))
    (hm : h₀ * z * h₀⁻¹ = m) (hsne : s ≠ m) {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4)
    (hwm : w * m = m * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hΩ := hd.tight.hypGen
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
  obtain ⟨h, hh, he⟩ := hd.exists_conj_eq_of_comm hx (hΩ.conjInvariant h₀⁻¹ J hJ) hJs₁ hsx₁
    hsne₁ hwJ₁ hw4₁ hwz₁
  refine ⟨h₀ * h, Subgroup.mul_mem _ hh₀ hh, ?_⟩
  calc h₀ * h * z * (h₀ * h)⁻¹ = h₀ * (h * z * h⁻¹) * h₀⁻¹ := by group
    _ = s := by rw [he]; group

theorem exists_comm_of_comm {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G}
    (hJs : IsUniqueInvolution J s) (hsne : s ≠ z) {u : G} (huK : u ∈ K) (hu4 : orderOf u = 4)
    (hus : u * s = s * u) : ∃ w ∈ J, orderOf w = 4 ∧ w * z = z * w := by
  have hΩ := hd.tight.hypGen
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
    obtain ⟨-, -, U₁, hU₁, hU₁J, hU₁N⟩ := Q3T6.Mu.omegaStarNbr_symm hΩ hJ hK hstar
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

theorem exists_conj_eq_of_comm_u {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹)) (hsne : g * z * g⁻¹ ≠ z) {u : G} (huK : u ∈ K)
    (hu4 : orderOf u = 4) (hus : u * (g * z * g⁻¹) = g * z * g⁻¹ * u) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  obtain ⟨w, hwJ, hw4, hwz⟩ := hd.exists_comm_of_comm hJ (hI.conj g) hsne huK hu4 hus
  exact hd.exists_conj_eq_of_comm hx hJ (hI.conj g) hsx hsne hwJ hw4 hwz

theorem exists_quat_of_mem_RSet {Q : Subgroup G} (hQ : Q ∈ RSet (CoreAssembly.conjClass K)) :
    Nonempty (↥Q ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hd.tight.hypGen hQ
  have hr := hd.tight.natCard_rSet hQ
  have hc : Nat.card ↥Q = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hkr : k + 2 = r := by
    rw [hr] at hc
    exact (Nat.pow_right_injective (le_refl 2) hc).symm
  have hk2 : k = r - 2 := by omega
  rw [hk2] at e
  exact ⟨e⟩

theorem exists_conj_eq_of_comm_t (hr : 4 ≤ r) {x : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹))
    (hsz : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) (hst : g * z * g⁻¹ * t = t * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd.toTightSylowDataR.comm_of_mem
  have htW : t ∈ W := hd.leW hd.memT
  have hzW := hd.mem_W_z
  by_cases hsz' : g * z * g⁻¹ = z
  · exact ⟨1, Subgroup.one_mem _, by rw [hsz']; group⟩
  by_cases hst' : g * z * g⁻¹ = t
  · rw [hst']
    exact hd.exists_conj_eq_t_of_mem hx
  by_cases hstz : g * z * g⁻¹ = t * z
  · rw [hstz]
    exact hd.exists_conj_eq_mul_z_of_mem hx
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  have hJs := hI.conj g
  by_cases hw : ∃ w ∈ conjSub g K, orderOf w = 4 ∧ w * z = z * w
  · obtain ⟨w, hwJ, hw4, hwz⟩ := hw
    exact hd.exists_conj_eq_of_comm hx hJ hJs hsx hsz' hwJ hw4 hwz
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    hd.tight.centralizer_le_normalizer_member hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm)
  have htN : t ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    hd.tight.centralizer_le_normalizer_member hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hst.symm)
  have hzt : z * t = t * z := hcomm z hzW t htW
  set Z : Subgroup G := Subgroup.closure {z, t} with hZ
  have hZW : Z ≤ W := by
    rw [hZ, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hzW
    · exact htW
  have hZ2 : IsPGroup 2 Z := S.isPGroup'.to_le (hZW.trans hd.hWS)
  have hZN : Z ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
    rw [hZ, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hzN
    · exact htN
  obtain ⟨Q, hQ, hQZ⟩ := exists_sylow_normalized hZ2 hZN
  have hQR : Q ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_iff.mpr ⟨conjSub g K, hJ, hQ.1, hQ.2.1, hQ.2.2⟩
  obtain ⟨e⟩ := hd.exists_quat_of_mem_RSet hQR
  have hconjQ : ∀ c ∈ Z, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    have h := conj_mem_conjSub (n := c) hq
    rwa [hQZ c hc] at h
  have hzZ : z ∈ Z := Subgroup.subset_closure (Set.mem_insert z {t})
  have htZ : t ∈ Z := Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  have hna : ¬ ∃ w ∈ Q, orderOf w = 4 ∧ w * z = z * w := fun ⟨w, hwQ, hw4, hwz⟩ =>
    hw ⟨w, hQ.1 hwQ, hw4, hwz⟩
  rcases QSub.exists_comm_of_four e hr (hconjQ z hzZ) (hconjQ t htZ) hna with
    ⟨w, hwQ, hw4, hwt⟩ | ⟨w, hwQ, hw4, hwzt⟩
  · obtain ⟨h₀, hh₀, he⟩ := hd.exists_conj_eq_t_of_mem hx
    exact hd.exists_conj_eq_of_comm' hx hJ hJs hsx hh₀ he hst' (hQ.1 hwQ) hw4 hwt
  · obtain ⟨h₀, hh₀, he⟩ := hd.exists_conj_eq_mul_z_of_mem hx
    have hwm : w * (t * z) = t * z * w := by
      rw [← hzt]
      exact hwzt
    exact hd.exists_conj_eq_of_comm' hx hJ hJs hsx hh₀ he hstz (hQ.1 hwQ) hw4 hwm

theorem exists_sylow_conj {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {s : G}
    (hsx : s ∈ Subgroup.centralizer ({x} : Set G))
    (hsz : s ∈ Subgroup.centralizer ({z} : Set G)) (hs2 : IsPGroup 2 (Subgroup.zpowers s)) :
    ∃ S' : Sylow 2 G, TightSylowDataTR r K z S' W L t V ∧ x ∈ S19B.sec19BPrime K S' W L ∧
      ∃ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        c * s * c⁻¹ ∈ (S' : Subgroup G) := by
  have hd0 := hd.toTightSylowDataR
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  set H := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) with hH
  have hP₀H : (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H :=
    le_inf inf_le_right (inf_le_left.trans hd0.hSz)
  obtain ⟨T, hT, hP₀T⟩ := IsSylow2In.exists_ge (S.isPGroup'.to_le inf_le_left) hP₀H
  obtain ⟨c, hcH, hsc⟩ := Sec7.exists_conj_le_of_isSylow2In hT hs2
    (Subgroup.zpowers_le.mpr ⟨hsx, hsz⟩)
  have hcs : c⁻¹ * s * c ∈ T := by
    have h := mem_conjSub_iff.mp (hsc (Subgroup.mem_zpowers s))
    exact h
  obtain ⟨T', hT', hTT'⟩ := IsSylow2In.exists_ge hT.2.1 (hT.1.trans inf_le_right)
  have hcard : Nat.card T' = Nat.card (S : Subgroup G) :=
    IsSylow2In.natCard_eq hT' (S1916.isSylow2In_of_le S hd0.hSz)
  set S' : Sylow 2 G := Sylow.ofCard T' (by rw [hcard]; exact S.card_eq_multiplicity) with hS'
  have hS'T' : (S' : Subgroup G) = T' := Sylow.coe_ofCard _ _
  have hxS' : ∀ y ∈ (S : Subgroup G), y * x = x * y → y ∈ (S' : Subgroup G) := fun y hy hyx => by
    rw [hS'T']
    exact hTT' (hP₀T ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩)
  have hRS' : (S : Subgroup G) ⊓ K ≤ (S' : Subgroup G) := fun r hr =>
    hxS' r hr.1 (Subgroup.mem_centralizer_iff.mp hxR r hr)
  have hR : (S' : Subgroup G) ⊓ K = (S : Subgroup G) ⊓ K := by
    have hRK := hd0.isSylow2In_inf
    exact hRK.2.2 _ inf_le_right (S'.isPGroup'.to_le inf_le_left) (le_inf hRS' inf_le_right)
  have hWS' : W ≤ (S' : Subgroup G) := fun w hw =>
    hxS' w (hd.hWS hw) (Subgroup.mem_centralizer_iff.mp hxW w hw)
  have hS'z : (S' : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hS'T']
    exact hT'.1
  have hsyl : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S' : Subgroup G) := by
    obtain ⟨Q₀, hQ₀⟩ := hd0.sylow
    exact ⟨Q₀, (le_inf hQ₀ (Subgroup.map_subtype_le _)).trans hRS'⟩
  have hd' : TightSylowDataTR r K z S' W L t V :=
    ⟨⟨hd0.tight, hd0.mu, hsyl, hS'z, hd0.hW, hWS'⟩, hd.memL, hd.invL, hd.ne,
      hd.memV, hd.leW, hd.memT⟩
  refine ⟨S', hd', ⟨⟨⟨hxS' x hxS rfl, by rw [hR]; exact hxR⟩, hxW⟩, hxL⟩, c⁻¹,
    H.inv_mem hcH, ?_⟩
  rw [inv_inv, hS'T']
  exact hTT' hcs

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
