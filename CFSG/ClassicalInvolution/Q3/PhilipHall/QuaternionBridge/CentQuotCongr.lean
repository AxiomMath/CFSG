module

public import CFSG.ClassicalInvolution.Q3.Q3T7K00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace CentQ

theorem isSubnormal_centralizer_gen (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  refine AscQuot.isSubnormal_centralizer (fun w hw => hz.commute_of_mem hw) ?_
  intro c hc hne
  have hcz : c * z * c⁻¹ = z := by
    rw [hc]
    group
  have hK' : conjSub c K ∈ Ω := hΩ.conjInvariant c K hK
  have hz' : IsUniqueInvolution (conjSub c K) z := by
    have := hz.conj c
    rwa [hcz] at this
  exact fun x hx => (Sec6Gen.comm_le_oddCore_of_twin hΩ hK hK' (Ne.symm hne) hz hz' hx).1

theorem comm_sylow_le_oddCoreOf_gen (hΩ : HypOmegaGen Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt' : z ≠ t)
    (hzt : t⁻¹ * z ∈ X) {V : Subgroup G} (hV : IsSylow2In V J) : ⁅V, K⁆ ≤ oddCoreOf K := by
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hKz', hJz'⟩
    exact hzt' ((hz.eq hKz').trans (ht.eq hJz').symm)
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hVR
  have htV : t ∈ V := AscQuot.mem_of_uniqueInvolution ht hV.1 hV.2.1 (by omega)
  have hzx : z = t * (t⁻¹ * z) := by group
  have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : r * (t⁻¹ * z) = (t⁻¹ * z) * r := Subgroup.mem_center_iff.mp (hXc hzt) r
    have h2 : t * r = r * t := ht.commute_of_mem (hV.1 hr)
    calc r * z = r * (t * (t⁻¹ * z)) := by rw [← hzx]
      _ = (r * t) * (t⁻¹ * z) := by rw [← mul_assoc]
      _ = (t * r) * (t⁻¹ * z) := by rw [← h2]
      _ = t * (r * (t⁻¹ * z)) := by rw [mul_assoc]
      _ = t * ((t⁻¹ * z) * r) := by rw [h1]
      _ = z * r := by group
  have hVsyl : IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hV.1 hVz, hV.2.1, fun V' hV'le hV'2 hle => hV.2.2 V' (hV'le.trans inf_le_left)
      hV'2 hle⟩
  have hnonab := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hVR).exists_not_commute
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases h62 K hK z hz J hJ hJt t ht V hVsyl htV with ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, -⟩ |
    ⟨-, hcomm⟩
  · exfalso
    have : Nat.card V = 2 := by rw [hVt, Nat.card_zpowers, ht2]
    omega
  · exfalso
    have : Nat.card V = 2 := by rw [hVt, Nat.card_zpowers, ht2]
    omega
  · exfalso
    obtain ⟨-, -, -, hcyc, -⟩ := hVU
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonab
    let _ : CommGroup ↥V := IsCyclic.commGroup
    have := mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩
    exact hxy (congrArg Subtype.val this)
  · exact hcomm

theorem conjSub_eq_of_mem_oddCore_gen (hΩ : HypOmegaGen Ω) {M : Subgroup G} {z : G} (hM : M ∈ Ω)
    (hz : IsUniqueInvolution M z) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) : conjSub n M = M := by
  by_contra hne
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hnC : n ∈ C := Balance.oddCoreIn_le C hn
  have hnz : n * z * n⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hnC
    rw [this]
    group
  have hM' : conjSub n M ∈ Ω := hΩ.conjInvariant n M hM
  have hz' : IsUniqueInvolution (conjSub n M) z := by
    have := hz.conj n
    rwa [hnz] at this
  have hcomm : ⁅M, conjSub n M⁆ ≤ oddCoreOf M ⊓ oddCoreOf (conjSub n M) :=
    Sec6Gen.comm_le_oddCore_of_twin hΩ hM hM' (Ne.symm hne) hz hz'
  have hO1 : oddCoreOf M ≤ oddCoreOf C :=
    Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_centralizer_gen hΩ hM hz)
  have hMC : M ≤ C := Q3T7M.CentQ.le_centralizer_of_uniq hz
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := M) IsPGroup.of_bot bot_le
  obtain ⟨x, hxQ, y, hyQ, hxy⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hQ)).exists_not_commute
  apply hxy
  have hxM : x ∈ M := hQ.1 hxQ
  have hyM : y ∈ M := hQ.1 hyQ
  have hy' : n * y * n⁻¹ ∈ conjSub n M := conj_mem_conjSub hyM
  have h1 : ⁅x, n * y * n⁻¹⁆ ∈ oddCoreOf C :=
    hO1 (hcomm (Subgroup.commutator_mem_commutator hxM hy')).1
  have ho : n * y * n⁻¹ * y⁻¹ ∈ oddCoreOf C := by
    have h2 : y * n⁻¹ * y⁻¹ ∈ oddCoreOf C :=
      Balance.conj_mem_oddCoreIn (hMC hyM) ((oddCoreOf C).inv_mem hn)
    have := (oddCoreOf C).mul_mem hn h2
    simpa [mul_assoc] using this
  have hx3 : x * (n * y * n⁻¹ * y⁻¹) * x⁻¹ ∈ oddCoreOf C :=
    Balance.conj_mem_oddCoreIn (hMC hxM) ho
  have hcommQ : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf C := by
    have e : x * y * x⁻¹ * y⁻¹ = (x * (n * y * n⁻¹ * y⁻¹) * x⁻¹)⁻¹ * ⁅x, n * y * n⁻¹⁆ *
        (n * y * n⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (oddCoreOf C).mul_mem ((oddCoreOf C).mul_mem ((oddCoreOf C).inv_mem hx3) h1) ho
  have hQmem : x * y * x⁻¹ * y⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ Q ⊓ oddCoreOf C := ⟨hQmem, hcommQ⟩
  rw [S1916.inf_oddCoreOf_eq_bot hQ.2.1 C, Subgroup.mem_bot] at h3
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem le_normalizer_of_congr_gen (hΩ : HypOmegaGen Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt' : z ≠ t)
    (hzt : t⁻¹ * z ∈ X) : J ≤ Subgroup.normalizer (K : Set G) := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hcen : t⁻¹ * z ∈ Subgroup.center G := hXc hzt
  have hCt : Subgroup.centralizer ({t} : Set G) = C := Q3T7M.CentQ.centralizer_eq_of_central hcen
  have hJC : J ≤ C := hCt ▸ Q3T7M.CentQ.le_centralizer_of_uniq ht
  have hKC : K ≤ C := Q3T7M.CentQ.le_centralizer_of_uniq hz
  have hJsub : IsSubnormal J C := hCt ▸ isSubnormal_centralizer_gen hΩ hJ ht
  have hOJ : oddCoreOf J ≤ oddCoreOf C := Balance.oddCoreIn_le_of_isSubnormal hJsub
  have hN₀C : oddCoreOf C ≤ C := Balance.oddCoreIn_le C
  have hN₀odd : Odd (Nat.card (oddCoreOf C)) := Balance.odd_card_oddCoreIn C
  have hCN : C ≤ Subgroup.normalizer ((oddCoreOf C : Subgroup G) : Set G) :=
    Balance.normalizer_oddCoreIn C
  have hzt'' : z⁻¹ * t ∈ X := by
    have := X.inv_mem hzt
    simpa using this
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K) IsPGroup.of_bot bot_le
  have hQ8 : 8 ≤ Nat.card Q := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hQ)
  have hQC : Q ≤ C := hQ.1.trans hKC
  have hQJ : ⁅Q, J⁆ ≤ oddCoreOf J :=
    comm_sylow_le_oddCoreOf_gen hΩ h62 hXc hJ hK ht hz (Ne.symm hzt') hzt'' hQ
  intro j hj
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  by_contra hne
  have hcardj : Nat.card (conjSub j Q) = Nat.card Q := Q3T7M.CentQ.natCard_conjSub_eq j Q
  have hjQle : conjSub j Q ≤ oddCoreOf C ⊔ Q := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hcomm : ⁅j, j⁻¹ * y * j⁆ ∈ oddCoreOf C := by
      have h1 : ⁅j, j⁻¹ * y * j⁆ ∈ ⁅J, Q⁆ := Subgroup.commutator_mem_commutator hj hy
      rw [Subgroup.commutator_comm] at h1
      exact hOJ (hQJ h1)
    have e : y = ⁅j, j⁻¹ * y * j⁆ * (j⁻¹ * y * j) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem_sup hcomm hy
  have hQN0 : Q ⊓ oddCoreOf C = ⊥ := S1916.inf_oddCoreOf_eq_bot hQ.2.1 C
  have hQnorm : Q ≤ Subgroup.normalizer ((oddCoreOf C : Subgroup G) : Set G) := fun q hq =>
    hCN (hQC hq)
  obtain ⟨n, hn, hnQ⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hQnorm hN₀odd hQN0 hQ.2.1
    (isPGroup_conjSub j hQ.2.1) hcardj hjQle
  have hKn : conjSub n K = K := conjSub_eq_of_mem_oddCore_gen hΩ hK hz hn
  have hjQK : conjSub j Q ≤ K := by
    have h1 : conjSub n Q ≤ conjSub n K := conjSub_mono hQ.1
    rw [hKn] at h1
    rw [← hnQ]
    exact h1
  have hK' : conjSub j K ∈ Ω := hΩ.conjInvariant j K hK
  have hle2 := Sec6Gen.card_le_two_of_le_inf hΩ hK hK' (Ne.symm hne) (isPGroup_conjSub j hQ.2.1) hjQK
    (conjSub_mono hQ.1)
  omega

theorem commutes_of_congr_gen (hΩ : HypOmegaGen Ω) (h62 : L6_2On Ω) {X : Subgroup G}
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hzt : t⁻¹ * z ∈ X) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J := by
  by_cases hzt' : z = t
  · exact Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hz (hzt' ▸ ht)
  have hzt'' : z⁻¹ * t ∈ X := by
    have := X.inv_mem hzt
    simpa using this
  have hJK : J ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_congr_gen hΩ h62 hXc hK hJ hz ht hzt' hzt
  have hKJ' : K ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_congr_gen hΩ h62 hXc hJ hK ht hz (Ne.symm hzt') hzt''
  have hcomm : ⁅K, J⁆ ≤ K ⊓ J := by
    refine Subgroup.commutator_le.mpr fun k hk j hj => ?_
    refine ⟨?_, ?_⟩
    · have h1 : j * k⁻¹ * j⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hJK hj) k⁻¹).mp (K.inv_mem hk)
      have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact K.mul_mem hk h1
    · have h1 : k * j * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hKJ' hk) j).mp hj
      rw [commutatorElement_def]
      exact J.mul_mem h1 (J.inv_mem hj)
  have hDnormK : K ≤ Subgroup.normalizer ((K ⊓ J : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨hdK, hdJ⟩
      exact ⟨K.mul_mem (K.mul_mem hk hdK) (K.inv_mem hk),
        (Subgroup.mem_normalizer_iff.mp (hKJ' hk) d).mp hdJ⟩
    · rintro ⟨hdK, hdJ⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hKJ' hk) d).mpr hdJ⟩
      have e : d = k⁻¹ * (k * d * k⁻¹) * k := by group
      rw [e]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hdK) hk
  have hDnormJ : J ≤ Subgroup.normalizer ((K ⊓ J : Subgroup G) : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨hdK, hdJ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hJK hj) d).mp hdK,
        J.mul_mem (J.mul_mem hj hdJ) (J.inv_mem hj)⟩
    · rintro ⟨hdK, hdJ⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hJK hj) d).mpr hdK, ?_⟩
      have e : d = j⁻¹ * (j * d * j⁻¹) * j := by group
      rw [e]
      exact J.mul_mem (J.mul_mem (J.inv_mem hj) hdJ) hj
  have hDodd : Odd (Nat.card ↥(K ⊓ J)) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card ↥(K ⊓ J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(K ⊓ J)) 2 h2
    have huG : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have husq : (u : G) * (u : G) = 1 := by
      have := pow_orderOf_eq_one (u : G)
      rwa [huG, pow_two] at this
    have hune : (u : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at huG
      omega
    have h1 : (u : G) = z := (hz.unique (u : G) u.2.1 husq).resolve_left hune
    have h2' : (u : G) = t := (ht.unique (u : G) u.2.2 husq).resolve_left hune
    exact hzt' (h1.symm.trans h2')
  have hDK : K ⊓ J ≤ oddCoreOf K := Balance.le_oddCoreIn_of_normalizes inf_le_left hDnormK hDodd
  have hDJ : K ⊓ J ≤ oddCoreOf J := Balance.le_oddCoreIn_of_normalizes inf_le_right hDnormJ hDodd
  exact le_inf (hcomm.trans hDK) (hcomm.trans hDJ)

end CentQ

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
