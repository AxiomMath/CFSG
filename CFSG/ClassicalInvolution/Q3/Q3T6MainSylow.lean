module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainData
public import CFSG.ClassicalInvolution.Q3.Q3T6LinMember
public import CFSG.ClassicalInvolution.AschTight.S1916CSR

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Basic


variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem le_sec19X_of_mem {A : Subgroup G}
    (hA : A ∈ USet (CoreAssembly.conjClass K) ∨ A ∈ RSet (CoreAssembly.conjClass K))
    (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) : A ≤ sec19X K z :=
  le_iSup₂ (f := fun B (_ : B ∈ {A : Subgroup G | (A ∈ USet (CoreAssembly.conjClass K) ∨
    A ∈ RSet (CoreAssembly.conjClass K)) ∧ A ≤ Subgroup.centralizer ({z} : Set G)}) => B) A
    ⟨hA, hAz⟩

namespace TightStd3

theorem isUniqueInvolution (ht : TightStd3 K z) : IsUniqueInvolution K z :=
  ht.member.isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem le_centralizer (ht : TightStd3 K z) : K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le ht.member.subnormal

theorem centralizer_le_normalizer (ht : TightStd3 K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  ht.normEq.ge

theorem centralizer_le_normalizer_member (ht : TightStd3 K z) {J : Subgroup G}
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

theorem not_le_centralizer_of_mem_rSet (ht : TightStd3 K z) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass K) (h₂ : J₂ ∈ CoreAssembly.conjClass K) (hne : J₁ ≠ J₂)
    {u : G} (hu : IsUniqueInvolution J₂ u) {R₁ : Subgroup G}
    (hR₁ : R₁ ∈ RSet (CoreAssembly.conjClass K)) (hR₁J : R₁ ≤ J₁) :
    ¬ R₁ ≤ Subgroup.centralizer ({u} : Set G) := fun hC =>
  S1911.not_le_normalizer_of_mem_rSet ht.edgeless h₁ h₂ hne hR₁ hR₁J
    (hC.trans (ht.centralizer_le_normalizer_member h₂ hu))

end TightStd3

namespace TightStd3

theorem natCard_rSet (ht : TightStd3 K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) : Nat.card R = 8 := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := hJ
  have hJm : Q3.IsClassicalMember3 (conjSub g K) (g * z * g⁻¹) :=
    (ht.member.conj g).toQ3 (by norm_num)
  obtain ⟨e⟩ := quaternion_sylow_of_isClassicalMember3 hJm P
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

end TightStd3

namespace Sec19Data3

variable {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W)
include hd

theorem hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
  hd.hSz.trans hd.tight.centralizer_le_normalizer

theorem isSylow2In_inf : IsSylow2In ((S : Subgroup G) ⊓ K) K :=
  S1916.isSylow2In_inf S hd.hSz hd.tight.le_centralizer hd.tight.centralizer_le_normalizer

theorem inf_mem_rSet : (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hd.isSylow2In_inf

theorem le_sec19X_inf : (S : Subgroup G) ⊓ K ≤ sec19X K z :=
  le_sec19X_of_mem (Or.inr hd.inf_mem_rSet) (inf_le_left.trans hd.hSz)

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

theorem mem_sec19X : z ∈ sec19X K z := hd.le_sec19X_inf hd.mem_inf

theorem mem_sec19Y : z ∈ sec19Y K z := by
  have hzK := hd.tight.isUniqueInvolution
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hzK.mem
  refine ⟨hd.mem_sec19X, hzN, mem_normalizer_oddCoreOf_of_mem_normalizer hzN, fun l hl => ?_⟩
  have hc : z * l = l * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hd.tight.le_centralizer hl)).symm
  rw [commutatorElement_def, hc, mul_inv_cancel_right, mul_inv_cancel]
  exact (oddCoreOf K).one_mem

theorem le_normalizer_sec19X :
    (S : Subgroup G) ≤ Subgroup.normalizer ((sec19X K z : Subgroup G) : Set G) :=
  hd.hSz.trans (Hall196.centralizer_le_normalizer_sec19X K z)

end Sec19Data3

namespace Sec19DataT3

variable {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}
  (hd : Sec19DataT3 K z S W L t V)
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
    hd.member_ne.symm hd.invL hd.toSec19Data3.inf_mem_rSet inf_le_right ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hC r hr

theorem le_sec19X_V : V ≤ sec19X K z :=
  le_sec19X_of_mem (Or.inl hd.memV) (hd.leW.trans (hd.hWS.trans hd.hSz))

theorem isCyclic_V : IsCyclic ↥V := by
  obtain ⟨R, -, -, hcyc, -⟩ := hd.memV
  exact hcyc

theorem isPGroup_V : IsPGroup 2 V := S.isPGroup'.to_le (hd.leW.trans hd.hWS)

theorem four_le_card_V : 4 ≤ Nat.card V := by
  obtain ⟨R, hR, hVR, -, hidx⟩ := hd.memV
  have h8 := hd.tight.natCard_rSet hR
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

end Sec19DataT3

end Basic

end CFSG.ClassicalInvolution.Q3.Q3T6
