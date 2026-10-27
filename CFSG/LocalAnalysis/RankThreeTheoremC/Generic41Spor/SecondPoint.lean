module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointStageA
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G]

theorem second_point_false (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G) {p : ℕ}
    [Fact p.Prime] (h5 : 5 ≤ p) (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x u : G} (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hwc : U3LineWC x (P : Subgroup G))
    (hxD : x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hgen : IsGenericPoint p P M u) (hux : u ∉ Subgroup.zpowers x) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hperf : Group.IsPerfect J) (hlt : rankThreePrimeCore p J < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) (hnot : ¬ J ≤ M)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hQ : SecondPointFacts p Q) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hxP : x ∈ (P : Subgroup G) := spw_mem_of_centralizes P hxp hxC
  have hx1 : x ≠ 1 := by
    intro h
    apply hxD
    rw [h]
    exact Subgroup.one_mem _
  have huP : u ∈ (P : Subgroup G) := hgen.1
  have hu1 : u ≠ 1 := hgen.2.1.2.1
  have hup : u ^ p = 1 := hgen.2.1.2.2.1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have huo : orderOf u = p := orderOf_eq_prime hup hu1
  have hux' : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp (hxC huP)
  obtain ⟨Z, hZcyc, huZ, hZS, hZT, hTZ, hsup⟩ :=
    second_point_S_decomp hS h5 hgen hJC hCJ hperf hlt hmin hnot ψ hψ hker hQ
  set T : Subgroup G := u3T P u J with hT
  set S : Subgroup G := u3S P u with hS'
  have hTJ : T ≤ J := inf_le_right
  have hTS : T ≤ S := inf_le_left
  have hSP : S ≤ (P : Subgroup G) := inf_le_left
  have hTP : T ≤ (P : Subgroup G) := hTS.trans hSP
  have hxS : x ∈ S := ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hux'.symm⟩
  obtain ⟨t, htT, z, hzZ, hxtz⟩ := spw_mem_sup_of_commute
    (fun a ha b hb => (hZT b hb a ha).symm) (hsup ▸ hxS : x ∈ T ⊔ Z)
  have htz : t * z = z * t := (hZT z hzZ t htT).symm
  have hpow : t ^ p * z ^ p = 1 := by
    have h1 := Commute.mul_pow (show Commute t z from htz) p
    rw [← h1, ← hxtz]
    exact hxp
  have htp : t ^ p = 1 := by
    have h1 : t ^ p ∈ T ⊓ Z := ⟨T.pow_mem htT p, by
      have : t ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact Z.inv_mem (Z.pow_mem hzZ p)⟩
    rw [hTZ, Subgroup.mem_bot] at h1
    exact h1
  have hzp : z ^ p = 1 := by
    rw [htp, one_mul] at hpow
    exact hpow
  have hzu : z ∈ Subgroup.zpowers u := spw_mem_zpowers_of_cyclic hZcyc huZ hu1 hup hzZ hzp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hzu
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, one_mul] at hxtz
    exact hux (spw_mem_zpowers_of_mem_zpowers hxo huo (hxtz ▸ hzu))
  have hzc : ∀ s ∈ S, z * s = s * z := by
    intro s hs
    have hsu : s * u = u * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
    have h1 : Commute s (u ^ j) := Commute.zpow_right (show Commute s u from hsu) j
    rw [← hj]
    exact h1.eq.symm
  have htc : ∀ s ∈ S, t * s = s * t := by
    intro s hs
    have h1 : x * s = s * x := (Subgroup.mem_centralizer_singleton_iff.mp (hxC hs.1)).symm
    have h2 := hzc s hs
    have h3 : t * s * z = s * t * z := by
      calc t * s * z = t * (s * z) := by group
        _ = t * (z * s) := by rw [h2]
        _ = (t * z) * s := by group
        _ = x * s := by rw [← hxtz]
        _ = s * x := h1
        _ = s * (t * z) := by rw [← hxtz]
        _ = s * t * z := by group
    exact mul_right_cancel h3
  obtain ⟨Tsyl', hTsyl', hTinj, hcardS⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  have htJ : t ∈ J := hTJ htT
  have hmemT : (⟨t, htJ⟩ : J) ∈ (T.subgroupOf J) := htT
  have htbar : ψ ⟨t, htJ⟩ ∈ (Tsyl' : Subgroup Q) := by
    rw [hTsyl']
    exact ⟨⟨t, htJ⟩, hmemT, rfl⟩
  have htbar1 : ψ ⟨t, htJ⟩ ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val (hTinj _ hmemT h))
  have htbarp : (ψ ⟨t, htJ⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨t, htJ⟩ : J) ^ p = 1 := Subtype.ext htp
    rw [this, map_one]
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    rw [hker]
    have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
    have : Nat.card ((rankThreePrimeCore p J).subgroupOf J) = Nat.card (rankThreePrimeCore p J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hTp : IsPGroup p (T.subgroupOf J) := (P.isPGroup'.to_le hTP).comap_subtype
  have hkey : ∀ n ∈ Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q), ∃ k : ℤ,
      n * ψ ⟨t, htJ⟩ * n⁻¹ = (ψ ⟨t, htJ⟩) ^ k ∧ z ^ k = z := by
    intro n hn
    obtain ⟨j', rfl⟩ := hψ n
    have hj' : ψ j' ∈ Subgroup.normalizer (((T.subgroupOf J).map ψ : Subgroup Q) : Set Q) := by
      rw [← hTsyl']
      exact hn
    obtain ⟨n', hn', hψn'⟩ := typeII_frattini_ker ψ hcop hTp hj'
    have hhJ : (n' : G) ∈ J := n'.2
    have hhN : (n' : G) ∈ Subgroup.normalizer (T : Set G) := by
      have := u3main_mem_normalizer_map hn'
      rwa [Subgroup.map_subgroupOf_eq_of_le hTJ] at this
    have hhu : (n' : G) * u = u * (n' : G) := Subgroup.mem_centralizer_singleton_iff.mp (hJC hhJ)
    have hhz : (n' : G) * z = z * (n' : G) := by
      rw [← hj]
      exact (Commute.zpow_right (show Commute (n' : G) u from hhu) j).eq
    have hhtT : (n' : G) * t * (n' : G)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hhN t).mp htT
    have hxh : (n' : G) * x * (n' : G)⁻¹ = ((n' : G) * t * (n' : G)⁻¹) * z := by
      have e : (n' : G) * z * (n' : G)⁻¹ = z := by rw [hhz, mul_inv_cancel_right]
      calc (n' : G) * x * (n' : G)⁻¹ = (n' : G) * (t * z) * (n' : G)⁻¹ := by rw [← hxtz]
        _ = ((n' : G) * t * (n' : G)⁻¹) * ((n' : G) * z * (n' : G)⁻¹) := by group
        _ = ((n' : G) * t * (n' : G)⁻¹) * z := by rw [e]
    have hxhP : (n' : G) * x * (n' : G)⁻¹ ∈ (P : Subgroup G) := by
      rw [hxh]
      exact (P : Subgroup G).mul_mem (hTP hhtT) (hSP (hZS hzZ))
    have hle : (Subgroup.zpowers x).map (MulAut.conj (n' : G)).toMonoidHom ≤ (P : Subgroup G) := by
      rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.2 ?_
      simpa [MulAut.conj_apply] using hxhP
    have heq := hwc (n' : G) hle
    have hmem : (n' : G) * x * (n' : G)⁻¹ ∈ Subgroup.zpowers x := by
      rw [← heq]
      exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hdec : ((n' : G) * t * (n' : G)⁻¹) * z = t ^ k * z ^ k := by
      calc ((n' : G) * t * (n' : G)⁻¹) * z = (n' : G) * x * (n' : G)⁻¹ := hxh.symm
        _ = x ^ k := hk.symm
        _ = (t * z) ^ k := by rw [← hxtz]
        _ = t ^ k * z ^ k := Commute.mul_zpow (show Commute t z from htz) k
    have hu1 : (t ^ k)⁻¹ * ((n' : G) * t * (n' : G)⁻¹) = z ^ k * z⁻¹ := by
      calc (t ^ k)⁻¹ * ((n' : G) * t * (n' : G)⁻¹)
          = (t ^ k)⁻¹ * (((n' : G) * t * (n' : G)⁻¹) * z) * z⁻¹ := by group
        _ = (t ^ k)⁻¹ * (t ^ k * z ^ k) * z⁻¹ := by rw [hdec]
        _ = z ^ k * z⁻¹ := by group
    have hmemTZ : (t ^ k)⁻¹ * ((n' : G) * t * (n' : G)⁻¹) ∈ T ⊓ Z :=
      ⟨T.mul_mem (T.inv_mem (T.zpow_mem htT k)) hhtT, by
        rw [hu1]
        exact Z.mul_mem (Z.zpow_mem hzZ k) (Z.inv_mem hzZ)⟩
    rw [hTZ, Subgroup.mem_bot] at hmemTZ
    have hA : (n' : G) * t * (n' : G)⁻¹ = t ^ k := (inv_mul_eq_one.mp hmemTZ).symm
    have hB : z ^ k = z := by
      have h1 : z ^ k * z⁻¹ = 1 := by rw [← hu1]; exact hmemTZ
      exact mul_inv_eq_one.mp h1
    refine ⟨k, ?_, hB⟩
    have hJeq : n' * ⟨t, htJ⟩ * n'⁻¹ = (⟨t, htJ⟩ : J) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      exact hA
    have h2 := congrArg ψ hJeq
    rw [map_mul, map_mul, map_inv, map_zpow, hψn'] at h2
    exact h2
  rcases hQ.shape with ⟨hpl, hmove⟩ | ⟨hh3, htrans⟩
  ·
    obtain ⟨n, hn, hnt⟩ := hmove Tsyl' _ htbar htbar1
    obtain ⟨k, hk, -⟩ := hkey n hn
    exact hnt (Subgroup.mem_zpowers_iff.2 ⟨k, hk.symm⟩)
  ·
    obtain ⟨hTcard, hTexp, hTnab⟩ := spw_T_structure_heis hgen hJC hCJ ψ hψ hker hh3
    have hz1 : z ≠ 1 := by
      intro hz
      rw [hz, mul_one] at hxtz
      apply hxD
      rw [hxtz]
      exact spw_central_mem_commutator hTP hTcard hTnab htT (fun s hs => htc s (hTS hs))
    have hcen : (⟨ψ ⟨t, htJ⟩, htbar⟩ : ↥(Tsyl' : Subgroup Q)) ∈ Subgroup.center ↥(Tsyl' : Subgroup Q) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : Q) ∈ (T.subgroupOf J).map ψ := by
        rw [← hTsyl']
        exact g.2
      obtain ⟨a0, ha0, ha0'⟩ := hg
      have ha1 : (a0 : G) ∈ T := ha0
      have h1 : t * (a0 : G) = (a0 : G) * t := htc _ (hTS ha1)
      apply Subtype.ext
      show (g : Q) * ψ ⟨t, htJ⟩ = ψ ⟨t, htJ⟩ * (g : Q)
      rw [← ha0', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1.symm
    have htZin : ψ ⟨t, htJ⟩ ∈ Zin (Tsyl' : Subgroup Q) := Subgroup.mem_map.2 ⟨_, hcen, rfl⟩
    have hw : (ψ ⟨t, htJ⟩) ^ 2 ∈ Zin (Tsyl' : Subgroup Q) := (Zin _).pow_mem htZin 2
    have hto' : orderOf (ψ ⟨t, htJ⟩) = p := orderOf_eq_prime htbarp htbar1
    have hw1 : (ψ ⟨t, htJ⟩) ^ 2 ≠ 1 := by
      intro h
      have hdvd : p ∣ 2 := hto' ▸ orderOf_dvd_of_pow_eq_one h
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    obtain ⟨n, hn, hnt⟩ := htrans Tsyl' _ htZin htbar1 _ hw hw1
    obtain ⟨k, hk, hzk⟩ := hkey n hn
    have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
    have hk1 : (p : ℤ) ∣ k - 1 := by
      have h1 : z ^ (k - 1) = 1 := by rw [zpow_sub_one, hzk, mul_inv_cancel]
      rw [← hzo]
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have hto : t ^ k = t := by
      have h1 : t ^ (k - 1) = 1 :=
        orderOf_dvd_iff_zpow_eq_one.1
          ((Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one htp)).trans hk1)
      calc t ^ k = t ^ (k - 1) * t := by rw [zpow_sub_one, inv_mul_cancel_right]
        _ = t := by rw [h1, one_mul]
    have hbk : (ψ ⟨t, htJ⟩) ^ k = ψ ⟨t, htJ⟩ := by
      rw [← map_zpow]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hto
    have h2 : (ψ ⟨t, htJ⟩) ^ 2 = ψ ⟨t, htJ⟩ := by rw [← hnt, hk, hbk]
    apply htbar1
    have h3 : ψ ⟨t, htJ⟩ * ψ ⟨t, htJ⟩ = ψ ⟨t, htJ⟩ * 1 := by
      rw [mul_one, ← pow_two, h2]
    exact mul_left_cancel h3

theorem spw_lift {p : ℕ} [Fact p.Prime] {P : Sylow p G} {u : G}
    {J : Subgroup G} {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (Tsyl' : Sylow p Q)
    (hTsyl' : (Tsyl' : Subgroup Q) = ((u3T P u J).subgroupOf J).map ψ) :
    ∀ n ∈ Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q), ∃ (h : G) (hhJ : h ∈ J),
      h ∈ Subgroup.normalizer ((u3T P u J : Subgroup G) : Set G) ∧ ψ ⟨h, hhJ⟩ = n := by
  intro n hn
  have hp : p.Prime := Fact.out
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    rw [hker]
    have : Nat.card ((rankThreePrimeCore p J).subgroupOf J) = Nat.card (rankThreePrimeCore p J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hTJ : u3T P u J ≤ J := inf_le_right
  have hTP : u3T P u J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTp : IsPGroup p ((u3T P u J).subgroupOf J) := (P.isPGroup'.to_le hTP).comap_subtype
  obtain ⟨j', rfl⟩ := hψ n
  have hj' : ψ j' ∈ Subgroup.normalizer ((((u3T P u J).subgroupOf J).map ψ : Subgroup Q) : Set Q) := by
    rw [← hTsyl']
    exact hn
  obtain ⟨n', hn', hψn'⟩ := typeII_frattini_ker ψ hcop hTp hj'
  refine ⟨(n' : G), n'.2, ?_, ?_⟩
  · have := u3main_mem_normalizer_map hn'
    rwa [Subgroup.map_subgroupOf_eq_of_le hTJ] at this
  · exact hψn'


theorem second_point_false_ab (hS : Setting G) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {P : Sylow p G}
    {M : Subgroup G} {x u : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hD₁ : (conjLines x (P : Subgroup G)).ncard ≤ 3)
    (hD₂ : ∀ W : Subgroup G, W ≤ (P : Subgroup G) → Nat.card W = p ^ 2 →
      (∀ A ∈ conjLines x (P : Subgroup G), A ≤ W) →
        conjLines x (P : Subgroup G) = {Subgroup.zpowers x})
    (hPab : IsMulCommutative (P : Subgroup G))
    (hgen : IsGenericPoint p P M u) (hux : Subgroup.zpowers u ∉ conjLines x (P : Subgroup G))
    {J : Subgroup G} (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hperf : Group.IsPerfect J) (hlt : rankThreePrimeCore p J < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) (hnot : ¬ J ≤ M)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hQ : SecondPointFacts p Q)
    (hpow : SylowIsPlane p Q → NormalizerPowers p Q) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  haveI := hPab
  set D : Set (Subgroup G) := conjLines x (P : Subgroup G) with hDdef
  have hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : (P : Subgroup G)) ⟨b, hb⟩)
  have huP : u ∈ (P : Subgroup G) := hgen.1
  have hu1 : u ≠ 1 := hgen.2.1.2.1
  have hup : u ^ p = 1 := hgen.2.1.2.2.1
  have hxP : x ∈ (P : Subgroup G) := spw_mem_of_centralizes P hxp hxC
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have huo : orderOf u = p := orderOf_eq_prime hup hu1
  have hSP : u3S P u = (P : Subgroup G) :=
    le_antisymm inf_le_left (le_inf le_rfl fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hPc a ha u huP))
  rcases hQ.shape with ⟨hpl, hmove⟩ | ⟨hh3, -⟩
  swap
  ·
    obtain ⟨-, -, hTnab⟩ := spw_T_structure_heis hgen hJC hCJ ψ hψ hker hh3
    apply hTnab
    have hTP : u3T P u J ≤ (P : Subgroup G) := (inf_le_left : u3T P u J ≤ u3S P u).trans hSP.le
    exact ⟨⟨fun a b => Subtype.ext (hPc a (hTP a.2) b (hTP b.2))⟩⟩
  have hpow' := hpow hpl
  obtain ⟨Z, hZcyc, huZ, hZS, hZT, hTZ, hsup⟩ :=
    second_point_S_decomp hS h5 hgen hJC hCJ hperf hlt hmin hnot ψ hψ hker hQ
  obtain ⟨hTcard, hTel⟩ := spw_T_structure_plane hgen hJC hCJ ψ hψ hker hpl
  obtain ⟨Tsyl', hTsyl', hTinj, hcardS⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  set T : Subgroup G := u3T P u J with hT
  have hTJ : T ≤ J := inf_le_right
  have hTS : T ≤ u3S P u := inf_le_left
  have hTP : T ≤ (P : Subgroup G) := hTS.trans hSP.le
  have hZP : Z ≤ (P : Subgroup G) := hZS.trans hSP.le
  have huniq : ∀ a ∈ T, ∀ a' ∈ T, ∀ b ∈ Z, ∀ b' ∈ Z, a * b = a' * b' → a = a' ∧ b = b' := by
    intro a ha a' ha' b hb b' hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ T ⊓ Z :=
      ⟨T.mul_mem (T.inv_mem ha') ha, by rw [h1]; exact Z.mul_mem hb' (Z.inv_mem hb)⟩
    rw [hTZ, Subgroup.mem_bot] at h2
    refine ⟨(inv_mul_eq_one.mp h2).symm, ?_⟩
    have h3 : b' * b⁻¹ = 1 := by rw [← h1]; exact h2
    exact (mul_inv_eq_one.mp h3).symm
  have hdecomp : ∀ y ∈ (P : Subgroup G), y ^ p = 1 →
      ∃ t' ∈ T, t' ^ p = 1 ∧ ∃ j : ℤ, y = t' * u ^ j := by
    intro y hyP hyp
    have hyS : y ∈ T ⊔ Z := by rw [hsup, hSP]; exact hyP
    obtain ⟨t', ht', z', hz', hyz⟩ := spw_mem_sup_of_commute
      (fun a ha b hb => (hZT b hb a ha).symm) hyS
    have htz' : t' * z' = z' * t' := (hZT z' hz' t' ht').symm
    have hpow'' : t' ^ p * z' ^ p = 1 := by
      have h1 := Commute.mul_pow (show Commute t' z' from htz') p
      rw [← h1, ← hyz]
      exact hyp
    have htp' : t' ^ p = 1 := by
      have h1 : t' ^ p ∈ T ⊓ Z := ⟨T.pow_mem ht' p, by
        have : t' ^ p = (z' ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hpow''
        rw [this]
        exact Z.inv_mem (Z.pow_mem hz' p)⟩
      rw [hTZ, Subgroup.mem_bot] at h1
      exact h1
    have hzp' : z' ^ p = 1 := by
      rw [htp', one_mul] at hpow''
      exact hpow''
    have hzu' : z' ∈ Subgroup.zpowers u := spw_mem_zpowers_of_cyclic hZcyc huZ hu1 hup hz' hzp'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hzu'
    exact ⟨t', ht', htp', j, by rw [hj]; exact hyz⟩
  have hxself : Subgroup.zpowers x ∈ D :=
    ⟨1, by rw [spw_zpowers_conj]; simp, Subgroup.zpowers_le.2 hxP⟩
  have hmemD : ∀ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) → Subgroup.zpowers (g * x * g⁻¹) ∈ D :=
    fun g hg => ⟨g, (spw_zpowers_conj g x).symm, Subgroup.zpowers_le.2 hg⟩
  have hDdest : ∀ A ∈ D, ∃ g : G, A = Subgroup.zpowers (g * x * g⁻¹) ∧
      g * x * g⁻¹ ∈ (P : Subgroup G) := by
    rintro A ⟨g, hA, hAP⟩
    refine ⟨g, hA.trans (spw_zpowers_conj g x), hAP ?_⟩
    rw [hA, spw_zpowers_conj]
    exact Subgroup.mem_zpowers _
  obtain ⟨t, htT, htp, j, hxtj⟩ := hdecomp x hxP hxp
  have htJ : t ∈ J := hTJ htT
  have hmemT : (⟨t, htJ⟩ : J) ∈ T.subgroupOf J := htT
  have hmem : ∀ a : G, ∀ ha : a ∈ T, (⟨a, hTJ ha⟩ : J) ∈ T.subgroupOf J := fun a ha => ha
  have himg : ∀ a : G, ∀ ha : a ∈ T, ψ ⟨a, hTJ ha⟩ ∈ (Tsyl' : Subgroup Q) := by
    intro a ha
    rw [hTsyl']
    exact ⟨⟨a, hTJ ha⟩, hmem a ha, rfl⟩
  have hinj : ∀ (a b : G) (ha : a ∈ T) (hb : b ∈ T), ψ ⟨a, hTJ ha⟩ = ψ ⟨b, hTJ hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 : ψ ((⟨a, hTJ ha⟩ : J) * (⟨b, hTJ hb⟩ : J)⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 := hTinj _ ((T.subgroupOf J).mul_mem (hmem a ha) ((T.subgroupOf J).inv_mem (hmem b hb))) h1
    exact mul_inv_eq_one.mp (congrArg Subtype.val h2)
  have hlift' : ∀ n ∈ Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q), ∃ (h : G) (hhJ : h ∈ J),
      h ∈ Subgroup.normalizer (T : Set G) ∧ h * u = u * h ∧ ψ ⟨h, hhJ⟩ = n := by
    intro n hn
    obtain ⟨h, hhJ, hhN, hψh⟩ := spw_lift ψ hψ hker Tsyl' hTsyl' n hn
    exact ⟨h, hhJ, hhN, Subgroup.mem_centralizer_singleton_iff.mp (hJC hhJ), hψh⟩
  have hconjT : ∀ (h : G) (hhJ : h ∈ J) (a : G) (ha : a ∈ T) (hhaT : h * a * h⁻¹ ∈ T),
      ψ ⟨h * a * h⁻¹, hTJ hhaT⟩ = ψ ⟨h, hhJ⟩ * ψ ⟨a, hTJ ha⟩ * (ψ ⟨h, hhJ⟩)⁻¹ := by
    intro h hhJ a ha hhaT
    have : (⟨h * a * h⁻¹, hTJ hhaT⟩ : J) = ⟨h, hhJ⟩ * ⟨a, hTJ ha⟩ * (⟨h, hhJ⟩ : J)⁻¹ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
  have hψpow : ∀ (a : G) (ha : a ∈ T) (k : ℕ) (hak : a ^ k ∈ T),
      ψ ⟨a ^ k, hTJ hak⟩ = (ψ ⟨a, hTJ ha⟩) ^ k := by
    intro a ha k hak
    rw [← map_pow]
    exact congrArg ψ (Subtype.ext rfl)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, one_mul] at hxtj
    have hxu : x ∈ Subgroup.zpowers u := hxtj ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) j
    have hux' : u ∈ Subgroup.zpowers x := spw_mem_zpowers_of_mem_zpowers hxo huo hxu
    have heq : Subgroup.zpowers u = Subgroup.zpowers x :=
      le_antisymm (Subgroup.zpowers_le.2 hux') (Subgroup.zpowers_le.2 hxu)
    exact hux (by rw [heq]; exact hxself)
  have htbar : ψ ⟨t, htJ⟩ ∈ (Tsyl' : Subgroup Q) := himg t htT
  have htbar1 : ψ ⟨t, htJ⟩ ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val (hTinj _ hmemT h))
  have hFiniteD : D.Finite := Set.toFinite D
  have hzP : u ^ j ∈ (P : Subgroup G) := (P : Subgroup G).zpow_mem huP j
  have hzZ : u ^ j ∈ Z := Z.zpow_mem huZ j
  by_cases hz1 : u ^ j = 1
  ·
    have hxt : x = t := by rw [hxtj, hz1, mul_one]
    obtain ⟨n₀, hn₀, hn₀t⟩ := hmove Tsyl' (ψ ⟨t, htJ⟩) htbar htbar1
    obtain ⟨h₀, hh₀J, hh₀N, hh₀u, hψh₀⟩ := hlift' n₀ hn₀
    have ht'T : h₀ * t * h₀⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hh₀N t).mp htT
    have ht'D : Subgroup.zpowers (h₀ * t * h₀⁻¹) ∈ D := by
      have := hmemD h₀ (by rw [hxt]; exact hTP ht'T)
      rwa [hxt] at this
    have ht'ne : Subgroup.zpowers (h₀ * t * h₀⁻¹) ≠ Subgroup.zpowers x := by
      intro heq
      have hmem2 : h₀ * t * h₀⁻¹ ∈ Subgroup.zpowers t := by
        have : h₀ * t * h₀⁻¹ ∈ Subgroup.zpowers (h₀ * t * h₀⁻¹) := Subgroup.mem_zpowers _
        rw [heq, hxt] at this
        exact this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem2
      apply hn₀t
      have h1 : ψ ⟨h₀ * t * h₀⁻¹, hTJ ht'T⟩ = (ψ ⟨t, htJ⟩) ^ k := by
        rw [← map_zpow]
        refine congrArg ψ (Subtype.ext ?_)
        rw [Subgroup.coe_zpow]
        exact hk.symm
      rw [← hψh₀, ← hconjT h₀ hh₀J t htT ht'T, h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    have hnotT : ∃ A ∈ D, ¬ A ≤ T := by
      by_contra hcon
      push_neg at hcon
      have hD2 := hD₂ T hTP hTcard hcon
      have : Subgroup.zpowers (h₀ * t * h₀⁻¹) ∈ ({Subgroup.zpowers x} : Set (Subgroup G)) :=
        hD2 ▸ ht'D
      exact ht'ne this
    obtain ⟨A₃, hA₃D, hA₃T⟩ := hnotT
    obtain ⟨g, hA₃g, hgP⟩ := hDdest A₃ hA₃D
    set y₃ : G := g * x * g⁻¹ with hy₃def
    have hy₃p : y₃ ^ p = 1 := by rw [hy₃def, conj_pow, hxp]; simp
    have hy₃1 : y₃ ≠ 1 := by
      intro h
      apply hx1
      have : g * x = g := mul_inv_eq_one.mp h
      exact mul_left_cancel (a := g) (by rw [this, mul_one])
    have hy₃o : orderOf y₃ = p := orderOf_eq_prime hy₃p hy₃1
    have hy₃T : y₃ ∉ T := by
      intro h
      apply hA₃T
      rw [hA₃g]
      exact Subgroup.zpowers_le.2 h
    have hL1T : Subgroup.zpowers x ≤ T := by rw [hxt]; exact Subgroup.zpowers_le.2 htT
    have hL2T : Subgroup.zpowers (h₀ * t * h₀⁻¹) ≤ T := Subgroup.zpowers_le.2 ht'T
    have h12 : Subgroup.zpowers x ≠ Subgroup.zpowers (h₀ * t * h₀⁻¹) := fun h => ht'ne h.symm
    have h13 : Subgroup.zpowers x ≠ A₃ := fun h => hA₃T (h ▸ hL1T)
    have h23 : Subgroup.zpowers (h₀ * t * h₀⁻¹) ≠ A₃ := fun h => hA₃T (h ▸ hL2T)
    have hsub3 : ({Subgroup.zpowers x, Subgroup.zpowers (h₀ * t * h₀⁻¹), A₃} : Set (Subgroup G)) ⊆ D := by
      intro A hA
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with rfl | rfl | rfl
      · exact hxself
      · exact ht'D
      · exact hA₃D
    have hncard3 :
        ({Subgroup.zpowers x, Subgroup.zpowers (h₀ * t * h₀⁻¹), A₃} : Set (Subgroup G)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [h12, h13]) (Set.toFinite _), Set.ncard_pair h23]
    have hDeq : ({Subgroup.zpowers x, Subgroup.zpowers (h₀ * t * h₀⁻¹), A₃} : Set (Subgroup G)) = D :=
      Set.eq_of_subset_of_ncard_le hsub3 (by rw [hncard3]; exact hD₁) hFiniteD
    obtain ⟨t₃, ht₃T, ht₃p, μ, hy₃μ⟩ := hdecomp y₃ hgP hy₃p
    have hμ1 : u ^ μ ≠ 1 := by
      intro h
      rw [h, mul_one] at hy₃μ
      exact hy₃T (hy₃μ ▸ ht₃T)
    have hμp : (u ^ μ) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hup, one_zpow]
    have hμo : orderOf (u ^ μ) = p := orderOf_eq_prime hμp hμ1
    have hμu : u ∈ Subgroup.zpowers (u ^ μ) :=
      spw_mem_zpowers_of_mem_zpowers hμo huo (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) μ)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hμu
    have hcomm3 : Commute t₃⁻¹ y₃ := hPc _ ((P : Subgroup G).inv_mem (hTP ht₃T)) _ hgP
    have hu_eq : u = (t₃⁻¹) ^ m * y₃ ^ m := by
      have h1 : u ^ μ = t₃⁻¹ * y₃ := by rw [hy₃μ]; group
      calc u = (u ^ μ) ^ m := hm.symm
        _ = (t₃⁻¹ * y₃) ^ m := by rw [h1]
        _ = (t₃⁻¹) ^ m * y₃ ^ m := hcomm3.mul_zpow m
    have hwT : (t₃⁻¹) ^ m ∈ T := T.zpow_mem (T.inv_mem ht₃T) m
    have huniq' : ∀ a ∈ T, ∀ a' ∈ T, ∀ b ∈ Subgroup.zpowers y₃, ∀ b' ∈ Subgroup.zpowers y₃,
        a * b = a' * b' → a = a' := by
      intro a ha a' ha' b hb b' hb' h
      have h1 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
          _ = b' * b⁻¹ := by group
      have h2 : a'⁻¹ * a ∈ T ⊓ Subgroup.zpowers y₃ :=
        ⟨T.mul_mem (T.inv_mem ha') ha, by
          rw [h1]
          exact (Subgroup.zpowers y₃).mul_mem hb' ((Subgroup.zpowers y₃).inv_mem hb)⟩
      rw [spw_inf_zpowers_eq_bot hy₃o hy₃T, Subgroup.mem_bot] at h2
      exact (inv_mul_eq_one.mp h2).symm
    have hfix : ∀ (h : G), h ∈ J → h ∈ Subgroup.normalizer (T : Set G) → h * u = u * h →
        ∃ l : ℤ, h * y₃ * h⁻¹ = y₃ ^ l := by
      intro h hhJ hhN hhu
      have hhtT : h * t₃ * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hhN t₃).mp ht₃T
      have hhuμ : h * u ^ μ = u ^ μ * h := (Commute.zpow_right (show Commute h u from hhu) μ).eq
      have hhy₃ : h * y₃ * h⁻¹ = (h * t₃ * h⁻¹) * u ^ μ := by
        calc h * y₃ * h⁻¹ = (h * t₃ * h⁻¹) * (h * u ^ μ * h⁻¹) := by rw [hy₃μ]; group
          _ = (h * t₃ * h⁻¹) * u ^ μ := by rw [hhuμ, mul_inv_cancel_right]
      have hhy₃P : h * y₃ * h⁻¹ ∈ (P : Subgroup G) := by
        rw [hhy₃]
        exact (P : Subgroup G).mul_mem (hTP hhtT) ((P : Subgroup G).zpow_mem huP μ)
      have hconjx : h * y₃ * h⁻¹ = (h * g) * x * (h * g)⁻¹ := by rw [hy₃def]; group
      have hD3 : Subgroup.zpowers (h * y₃ * h⁻¹) ∈ D := by
        have := hmemD (h * g) (by rw [← hconjx]; exact hhy₃P)
        rwa [← hconjx] at this
      have hnotle : ¬ Subgroup.zpowers (h * y₃ * h⁻¹) ≤ T := by
        intro hle
        have hmemT' : h * y₃ * h⁻¹ ∈ T := hle (Subgroup.mem_zpowers _)
        exact hy₃T ((Subgroup.mem_normalizer_iff.mp hhN y₃).mpr hmemT')
      have hmemDeq : Subgroup.zpowers (h * y₃ * h⁻¹) ∈
          ({Subgroup.zpowers x, Subgroup.zpowers (h₀ * t * h₀⁻¹), A₃} : Set (Subgroup G)) := by
        rw [hDeq]
        exact hD3
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemDeq
      rcases hmemDeq with h' | h' | h'
      · exact absurd (h' ▸ hL1T) hnotle
      · exact absurd (h' ▸ hL2T) hnotle
      · have h1 : h * y₃ * h⁻¹ ∈ A₃ := by
          rw [← h']
          exact Subgroup.mem_zpowers _
        rw [hA₃g] at h1
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 h1
        exact ⟨l, hl.symm⟩
    have hwcent : ∀ (h : G), h ∈ J → h ∈ Subgroup.normalizer (T : Set G) → h * u = u * h →
        h * (t₃⁻¹) ^ m * h⁻¹ = (t₃⁻¹) ^ m := by
      intro h hhJ hhN hhu
      obtain ⟨l, hl⟩ := hfix h hhJ hhN hhu
      have hhwT : h * (t₃⁻¹) ^ m * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hhN _).mp hwT
      have h1 : h * u * h⁻¹ = u := by rw [hhu, mul_inv_cancel_right]
      have h2 : (t₃⁻¹) ^ m * y₃ ^ m = (h * (t₃⁻¹) ^ m * h⁻¹) * y₃ ^ (l * m) := by
        calc (t₃⁻¹) ^ m * y₃ ^ m = u := hu_eq.symm
          _ = h * u * h⁻¹ := h1.symm
          _ = h * ((t₃⁻¹) ^ m * y₃ ^ m) * h⁻¹ := by rw [← hu_eq]
          _ = (h * (t₃⁻¹) ^ m * h⁻¹) * (h * y₃ ^ m * h⁻¹) := by group
          _ = (h * (t₃⁻¹) ^ m * h⁻¹) * (h * y₃ * h⁻¹) ^ m := by rw [← conj_zpow (a := h) (b := y₃) (i := m)]
          _ = (h * (t₃⁻¹) ^ m * h⁻¹) * (y₃ ^ l) ^ m := by rw [hl]
          _ = (h * (t₃⁻¹) ^ m * h⁻¹) * y₃ ^ (l * m) := by rw [← zpow_mul]
      exact (huniq' _ hwT _ hhwT _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m) _
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) (l * m)) h2).symm
    have hw1 : (t₃⁻¹) ^ m = 1 := by
      by_contra hw1
      have hwbar1 : ψ ⟨(t₃⁻¹) ^ m, hTJ hwT⟩ ≠ 1 := by
        intro h
        exact hw1 (congrArg Subtype.val (hTinj _ (hmem _ hwT) h))
      have hp2' : ¬ p ∣ 2 := by
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      obtain ⟨n, hn, hnw⟩ := hpow' Tsyl' _ (himg _ hwT) hwbar1 2 hp2'
      obtain ⟨h, hhJ, hhN, hhu, hψh⟩ := hlift' n hn
      have hhwT : h * (t₃⁻¹) ^ m * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hhN _).mp hwT
      have h1 := hconjT h hhJ _ hwT hhwT
      have h2 := hwcent h hhJ hhN hhu
      have h3 : ψ ⟨h * (t₃⁻¹) ^ m * h⁻¹, hTJ hhwT⟩ = ψ ⟨(t₃⁻¹) ^ m, hTJ hwT⟩ :=
        congrArg ψ (Subtype.ext h2)
      rw [h1, hψh, hnw] at h3
      apply hwbar1
      have h4 : ψ ⟨(t₃⁻¹) ^ m, hTJ hwT⟩ * ψ ⟨(t₃⁻¹) ^ m, hTJ hwT⟩ =
          ψ ⟨(t₃⁻¹) ^ m, hTJ hwT⟩ * 1 := by
        rw [mul_one, ← pow_two, h3]
      exact mul_left_cancel h4
    have hu_in : u ∈ A₃ := by
      rw [hu_eq, hw1, one_mul, hA₃g]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
    have hA₃card : Nat.card A₃ = p := by rw [hA₃g, Nat.card_zpowers, hy₃o]
    have heq3 : Subgroup.zpowers u = A₃ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_in)
        (by rw [Nat.card_zpowers, huo, hA₃card])
    exact hux (heq3 ▸ hA₃D)
  ·
    have hzp : (u ^ j) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hup, one_zpow]
    have hzo : orderOf (u ^ j) = p := orderOf_eq_prime hzp hz1
    have hline : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → Subgroup.zpowers (t ^ k * u ^ j) ∈ D := by
      intro k hk1 hk4
      have hkp : ¬ p ∣ k := fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      obtain ⟨n, hn, hnk⟩ := hpow' Tsyl' (ψ ⟨t, htJ⟩) htbar htbar1 k hkp
      obtain ⟨h, hhJ, hhN, hhu, hψh⟩ := hlift' n hn
      have hhtT : h * t * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hhN t).mp htT
      have htk : t ^ k ∈ T := T.pow_mem htT k
      have hhtk : h * t * h⁻¹ = t ^ k := by
        apply hinj _ _ hhtT htk
        rw [hconjT h hhJ t htT hhtT, hψpow t htT k htk, hψh, hnk]
      have hhuj : h * u ^ j = u ^ j * h := (Commute.zpow_right (show Commute h u from hhu) j).eq
      have hhx : h * x * h⁻¹ = t ^ k * u ^ j := by
        calc h * x * h⁻¹ = (h * t * h⁻¹) * (h * u ^ j * h⁻¹) := by rw [hxtj]; group
          _ = t ^ k * u ^ j := by rw [hhtk, hhuj, mul_inv_cancel_right]
      have hP' : t ^ k * u ^ j ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem (hTP htk) hzP
      have := hmemD h (by rw [hhx]; exact hP')
      rwa [hhx] at this
    have htord : orderOf t = p := orderOf_eq_prime htp ht1
    have hdist : ∀ k k' : ℕ, 1 ≤ k → k ≤ 4 → 1 ≤ k' → k' ≤ 4 →
        Subgroup.zpowers (t ^ k * u ^ j) = Subgroup.zpowers (t ^ k' * u ^ j) → k = k' := by
      intro k k' hk1 hk4 hk1' hk4' heq
      have hmem2 : t ^ k' * u ^ j ∈ Subgroup.zpowers (t ^ k * u ^ j) :=
        heq ▸ Subgroup.mem_zpowers _
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem2
      have hcomm : Commute (t ^ k) (u ^ j) := hPc _ (hTP (T.pow_mem htT k)) _ hzP
      rw [hcomm.mul_zpow] at hm
      obtain ⟨h1, h2⟩ := huniq _ (T.zpow_mem (T.pow_mem htT k) m) _ (T.pow_mem htT k') _
        (Z.zpow_mem hzZ m) _ hzZ hm
      have hm1 : (p : ℤ) ∣ m - 1 := by
        have h3 : (u ^ j) ^ (m - 1) = 1 := by rw [zpow_sub_one, h2, mul_inv_cancel]
        rw [← hzo]
        exact orderOf_dvd_iff_zpow_eq_one.2 h3
      have htkp : (t ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, htp, one_pow]
      have htkm : (t ^ k) ^ m = t ^ k := by
        have h4 : (t ^ k) ^ (m - 1) = 1 :=
          orderOf_dvd_iff_zpow_eq_one.1
            ((Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one htkp)).trans hm1)
        calc (t ^ k) ^ m = (t ^ k) ^ (m - 1) * t ^ k := by rw [zpow_sub_one, inv_mul_cancel_right]
          _ = t ^ k := by rw [h4, one_mul]
      have h5 : t ^ k = t ^ k' := by rw [← htkm, h1]
      have h6 : t ^ ((k : ℤ) - k') = 1 := by
        rw [zpow_sub, zpow_natCast, zpow_natCast, h5, mul_inv_cancel]
      have h7 : (p : ℤ) ∣ (k : ℤ) - k' := by
        rw [← htord]
        exact orderOf_dvd_iff_zpow_eq_one.2 h6
      have h8 := Int.eq_zero_of_abs_lt_dvd h7 (by rw [abs_lt]; constructor <;> omega)
      omega
    let f : Fin 4 → Subgroup G := fun i => Subgroup.zpowers (t ^ (i.val + 1) * u ^ j)
    have hf : Function.Injective f := by
      intro a b hab
      have := hdist (a.val + 1) (b.val + 1) (by omega) (by omega) (by omega) (by omega) hab
      exact Fin.ext (by omega)
    have hsub : Set.range f ⊆ D := by
      rintro _ ⟨i, rfl⟩
      exact hline (i.val + 1) (by omega) (by omega)
    have hcard := Set.ncard_le_ncard hsub hFiniteD
    rw [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    omega

theorem second_point_false' (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G) {p : ℕ}
    [Fact p.Prime] (h5 : 5 ≤ p) (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x u : G} (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hxD : x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hD₁ : (conjLines x (P : Subgroup G)).ncard ≤ 3)
    (hD₂ : ∀ W : Subgroup G, W ≤ (P : Subgroup G) → Nat.card W = p ^ 2 →
      (∀ A ∈ conjLines x (P : Subgroup G), A ≤ W) →
        conjLines x (P : Subgroup G) = {Subgroup.zpowers x})
    (hab : conjLines x (P : Subgroup G) ≠ {Subgroup.zpowers x} → IsMulCommutative (P : Subgroup G))
    (hgen : IsGenericPoint p P M u) (hux : Subgroup.zpowers u ∉ conjLines x (P : Subgroup G))
    {J : Subgroup G} (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hperf : Group.IsPerfect J) (hlt : rankThreePrimeCore p J < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) (hnot : ¬ J ≤ M)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hQ : SecondPointFacts p Q)
    (hpow : conjLines x (P : Subgroup G) ≠ {Subgroup.zpowers x} → SylowIsPlane p Q →
      NormalizerPowers p Q) : False := by
  have hx1 : x ≠ 1 := by
    intro h
    apply hxD
    rw [h]
    exact Subgroup.one_mem _
  by_cases hwcr : conjLines x (P : Subgroup G) = {Subgroup.zpowers x}
  · have hwc : U3LineWC x (P : Subgroup G) := fun g hg => by
      have hmem : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∈
          conjLines x (P : Subgroup G) := ⟨g, rfl, hg⟩
      rw [hwcr] at hmem
      exact hmem
    have hux' : u ∉ Subgroup.zpowers x := by
      intro hu
      have hu1 : u ≠ 1 := hgen.2.1.2.1
      have hup : u ^ p = 1 := hgen.2.1.2.2.1
      have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
      have huo : orderOf u = p := orderOf_eq_prime hup hu1
      have heq : Subgroup.zpowers u = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, hxo])
      apply hux
      rw [heq, hwcr]
      exact Set.mem_singleton _
    exact second_point_false hS hU0 hD1 h5 hp hM hxp hxC hwc hxD hgen hux' hJC hCJ hperf hlt hmin
      hnot ψ hψ hker hQ
  · exact second_point_false_ab hS h5 hx1 hxp hxC hD₁ hD₂ (hab hwcr) hgen hux hJC hCJ hperf hlt hmin
      hnot ψ hψ hker hQ (hpow hwcr)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
