module

public import CFSG.ClassicalInvolution.AschTight.S19QSec
public import CFSG.ClassicalInvolution.AschTight.S19BFus
public import CFSG.ClassicalInvolution.AschTight.S19BCtl
public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.AschTight.S1911SecE

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_lt_of_ne_one [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {x : G} (hx1 : x ≠ 1) : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
    intro htop
    have hxZ : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hxZ
      exact hx1 hxZ
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  have hidx : (Subgroup.centralizer ({x} : Set G)).index ≠ 1 := fun h1 =>
    hne (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set G)) := Nat.card_pos
  have hidx0 : (Subgroup.centralizer ({x} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (Subgroup.centralizer ({x} : Set G)).index := by omega
  nlinarith

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem section_inputs_of_mem_sec19BPrime (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) :
    ∃ hzx : z ∈ Subgroup.centralizer ({x} : Set G),
      IsClassicalMember p f (S1911.perfectCoreIn K x) ⟨z, hzx⟩ ∧
      HypOmegaMod p f (S1911.conjFamily (S1911.perfectCoreIn K x)) ∧
      Disconnected.DEdgeless (S1911.conjFamily (S1911.perfectCoreIn K x)) ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) < Nat.card G ∧
      (⊤ : Subgroup (↥(S1911.conjGen (S1911.perfectCoreIn K x)) ⧸
        classicalInvolutionOddCore ↥(S1911.conjGen (S1911.perfectCoreIn K x)))) ∉
        oddQuotientFamily (restrictFamily (S1911.conjFamily (S1911.perfectCoreIn K x))
          (S1911.conjGen (S1911.perfectCoreIn K x))) := by
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  have hd0 := hd.toSec19Data
  have h5 : 5 ≤ p ^ f := hd0.tight.branch.five
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hxK : x ∈ centralizerModOdd ⊤ K := S19B.mem_centralizerModOdd_K hd hxS hxR
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hxS)).symm
  have hmem : IsClassicalMember p f (S1911.perfectCoreIn K x) ⟨z, hzx⟩ :=
    isClassicalMember_perfectCore_of_cStar hd0 hx2 hxK hzx
  obtain ⟨g, hgx, hgz⟩ := S19B.exists_conj_eq_t_of_centralizes hd hxS hxR hxW hxL
  have hgC : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgx
  have htS : t ∈ (S : Subgroup G) := hd.hWS (hd.leW hd.memT)
  have htz := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz htS)
  exact ⟨hzx, hmem, S1911.hypOmegaMod_conjFamily hd0 hzx hmem,
    S1911.dEdgeless_conjFamily hd0 h5 hzx hmem,
    card_centralizer_lt_of_ne_one hd0.tight.branch.nonabelian hx1,
    S19C.top_not_mem_secFamily hd0 hzx (Subgroup.mem_subgroupOf.mp hmem.mem)
      ⟨g, hgC⟩ (by rw [hgz]; exact hd.ne) (by rw [hgz]; exact htz)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
