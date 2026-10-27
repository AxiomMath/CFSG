module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3T)
open scoped commutatorElement

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_y_not_mem_commutator (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hA : Sz32QDecomp P x J a c y)
    (hNJ : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤
      Subgroup.normalizer (J : Set G)) :
    y ∉ ⁅Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G),
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)⁆ := by
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) with hN
  set S : Subgroup G := (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) with hSdef
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ
      hker
  have hCN : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hg
  have hSN : ∀ g ∈ S, g ∈ N := fun g hg => hCN g hg.2
  have hyS : y ∈ S := hA.pres.y_mem
  have hyN : y ∈ N := hSN y hyS
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) hNJ ψ hψ hker
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hc.generic hc.le_cent hc.cent_le ψ hker
  let Tb : Sylow 5 Q := Tsyl.mapSurjective hψ
  have hTb : (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ := Sylow.coe_mapSurjective hψ Tsyl
  have hTconj : ∀ g ∈ S, ∀ t : ↥J, t ∈ (Tsyl : Subgroup ↥J) →
      ∃ hj : g * (t : G) * g⁻¹ ∈ J,
        (⟨g * (t : G) * g⁻¹, hj⟩ : ↥J) ∈ (Tsyl : Subgroup ↥J) := by
    intro g hg t ht
    have htS : (t : G) ∈ S ⊓ J := by
      have h : t ∈ (S ⊓ J).subgroupOf J := hTsyl ▸ ht
      exact h
    have hj : g * (t : G) * g⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hNJ (hSN g hg)) (t : G)).mp t.2
    refine ⟨hj, ?_⟩
    rw [hTsyl, Subgroup.mem_subgroupOf]
    exact ⟨S.mul_mem (S.mul_mem hg htS.1) (S.inv_mem hg), hj⟩
  have hOut : Nat.card (Outer Q) = 5 := hSz.outer Q hQ
  haveI : IsCyclic (Outer Q) := isCyclic_of_prime_card hOut
  let φ : ↥N →* Outer Q := (QuotientGroup.mk' (Inn Q)).comp ρ
  have hφcomm : ∀ g₁ g₂ : ↥N, φ ⁅g₁, g₂⁆ = 1 := by
    intro g₁ g₂
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  intro hy
  have hφy : φ ⟨y, hyN⟩ = 1 := by
    have hle : ⁅N, N⁆ ≤ φ.ker.map N.subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      exact ⟨⁅(⟨g₁, hg₁⟩ : ↥N), ⟨g₂, hg₂⟩⁆, hφcomm _ _, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hle hy
    have hz' : z = ⟨y, hyN⟩ := Subtype.ext hzy
    rw [← hz']
    exact hz
  obtain ⟨q, hq⟩ : ρ ⟨y, hyN⟩ ∈ Inn Q := (QuotientGroup.eq_one_iff _).mp hφy
  have hq5 : q ^ 5 = 1 := by
    have h1 : MulAut.conj (q ^ 5) = 1 := by
      rw [map_pow, hq, ← map_pow]
      have : (⟨y, hyN⟩ : ↥N) ^ 5 = 1 := Subtype.ext hA.pres.y5
      rw [this, map_one]
    have h2 : q ^ 5 ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h3 := congrArg (fun f : MulAut Q => f z) h1
      simp only [MulAut.one_apply, MulAut.conj_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [hZ] at h2
    exact Subgroup.mem_bot.mp h2
  have key : ∀ g (hg : g ∈ S) (q' : Q), MulAut.conj q' = ρ ⟨g, hSN g hg⟩ →
      ∀ b ∈ (Tb : Subgroup Q), q' * b * q'⁻¹ ∈ (Tb : Subgroup Q) := by
    intro g hg q' hq' b hb
    rw [hTb] at hb ⊢
    obtain ⟨t, ht, rfl⟩ := hb
    obtain ⟨hj, hjT⟩ := hTconj g hg t ht
    refine ⟨⟨g * (t : G) * g⁻¹, hj⟩, hjT, ?_⟩
    have h1 := hρ ⟨g, hSN g hg⟩ t hj
    rw [← hq', MulAut.conj_apply] at h1
    exact h1.symm
  have hqN : q ∈ Subgroup.normalizer ((Tb : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact fun hb => key y hyS q hq b hb
    · intro hb
      have hyS' : y⁻¹ ∈ S := S.inv_mem hyS
      have hq' : MulAut.conj q⁻¹ = ρ ⟨y⁻¹, hSN _ hyS'⟩ := by
        have : (⟨y⁻¹, hSN _ hyS'⟩ : ↥N) = (⟨y, hyN⟩ : ↥N)⁻¹ := rfl
        rw [this, map_inv, map_inv, ← hq]
      have h1 := key y⁻¹ hyS' q⁻¹ hq' (q * b * q⁻¹) hb
      have e : q⁻¹ * (q * b * q⁻¹) * q⁻¹⁻¹ = b := by group
      rwa [e] at h1
  have hSylTb : IsSylowOf 5 (Tb : Subgroup Q) (⊤ : Subgroup Q) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Tb.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Tb.not_dvd_index
  have hqT : q ∈ (Tb : Subgroup Q) := by
    refine CFSG.RankThree.PartOne.mem_of_pElement_mem_normalizer hSylTb (Subgroup.mem_top q) hqN ?_
    have hd : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  haveI hTbcyc : IsCyclic (Tb : Subgroup Q) := (hSz.sylow Q hQ Tb).1
  have haJ : a ∈ J := hA.a_J
  have haT : a ∈ S ⊓ J := by
    have : a ∈ u3T P x J := hA.T_eq ▸ Subgroup.mem_zpowers a
    exact this
  have haTsyl : (⟨a, haJ⟩ : ↥J) ∈ (Tsyl : Subgroup ↥J) := by
    rw [hTsyl, Subgroup.mem_subgroupOf]
    exact haT
  have hψaT : ψ ⟨a, haJ⟩ ∈ (Tb : Subgroup Q) := by
    rw [hTb]
    exact ⟨_, haTsyl, rfl⟩
  have hcomm : q * ψ ⟨a, haJ⟩ = ψ ⟨a, haJ⟩ * q := by
    have := mul_comm' (⟨q, hqT⟩ : (Tb : Subgroup Q)) ⟨ψ ⟨a, haJ⟩, hψaT⟩
    exact congrArg Subtype.val this
  have hya : y * a * y⁻¹ = a := by
    obtain ⟨hj, hjT⟩ := hTconj y hyS ⟨a, haJ⟩ haTsyl
    have h1 := hρ ⟨y, hyN⟩ ⟨a, haJ⟩ hj
    rw [← hq, MulAut.conj_apply] at h1
    have h2 : ψ ⟨y * a * y⁻¹, hj⟩ = ψ ⟨a, haJ⟩ := by
      rw [← h1, hcomm]
      group
    have h3 : (⟨y * a * y⁻¹, hj⟩ : ↥J) * (⟨a, haJ⟩ : ↥J)⁻¹ = 1 := by
      apply hTinj
      · exact (Tsyl : Subgroup ↥J).mul_mem hjT ((Tsyl : Subgroup ↥J).inv_mem haTsyl)
      · rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact congrArg Subtype.val (mul_inv_eq_one.mp h3)
  obtain ⟨n, hn, -, hn25⟩ := hA.pres.ya
  have h1 : a ^ n = a := by rw [← hn]; exact hya
  have h2 : a ^ (n - 1) = 1 := by rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 := (orderOf_dvd_iff_zpow_eq_one).mpr h2
  rw [hA.pres.ord_a] at h3
  push_cast at h3
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
