module

public import CFSG.ClassicalInvolution.Asc77.AscC25J9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Lift

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {N : Subgroup Y} [N.Normal]


theorem exists_conj_omegaNbr_gen (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K J : Subgroup Y} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaNbr Ω (conjSub n K) := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨J₁, hJ₁, hRbsyl⟩ := exists_isSylow2In_of_mem_RSet hRb
  have hRb2 : IsPGroup 2 Rb := hRbsyl.2.1
  have h8 : 8 ≤ Nat.card Rb := Sec6Gen.eight_le_of_mem_RSet hΩ' hRb
  have hJ₁eq : J₁ = J.map (QuotientGroup.mk' N) :=
    Sec6Gen.eq_of_le_of_le hΩ' hJ₁ (map_mem_quotFamily hJ) hRb2 (by omega) hRbsyl.1 hRbJ
  rw [hJ₁eq] at hRbsyl
  obtain ⟨R₀, hR₀, hR₀J, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Y)) bot_le
  have hV₁ := isSylow2In_map_mk hN hR₀J
  obtain ⟨xb, hxbJ, hconj⟩ := exists_conjSub_eq_of_isSylow2In hV₁ hRbsyl
  obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp hxbJ
  have hRΩ : conjSub x R₀ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₀ x
  have hRJ : conjSub x R₀ ≤ J := by
    have := conjSub_mono (n := x) hR₀J.1
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hRmap : (conjSub x R₀).map (QuotientGroup.mk' N) = Rb := by
    rw [AscQuot.map_conjSub, hx]
    exact hconj
  have hR2 : IsPGroup 2 (conjSub x R₀) := isPGroup_conjSub x hR₀J.2.1
  have hperm : ∀ v ∈ conjSub x R₀, ∃ n ∈ N, conjSub v K = conjSub n K := by
    intro v hv
    have hvN : QuotientGroup.mk' N v ∈ Subgroup.normalizer
        ((K.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) :=
      hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hv)
    have himg : K.map (QuotientGroup.mk' N) = (conjSub v K).map (QuotientGroup.mk' N) := by
      rw [AscQuot.map_conjSub]
      exact (conjSub_eq_of_mem_normalizer hvN).symm
    obtain ⟨n, hn, hnK⟩ := exists_conj_of_map_eq_gen hΩ hN hK (hΩ.conjInvariant v K hK) himg
    exact ⟨n, hn, hnK⟩
  obtain ⟨n, hn, hRn⟩ := exists_conj_normalizer_of_perm hN K hR2 hperm
  refine ⟨n, hn, hJ, ?_, conjSub x R₀, hRΩ, hRJ, hRn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

end Lift

section Quot

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}


theorem crossIn_nbr_quot (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    (c₀ : ↥(Subgroup.centralizer ({a} : Set G)))
    {M : Subgroup (↥(conjGen (crossIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (crossIn K a)))}
    (hM : M ∈ omegaNbr (oddQuotientFamily (restrictFamily (conjFamily (crossIn K a))
      (conjGen (crossIn K a)))) (secImg (conjGen (crossIn K a))
        (conjSub c₀ (crossIn K a)))) :
    M = secImg (conjGen (crossIn K a)) (conjSub (c₀ * w) (crossIn K a)) := by
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff (crossIn K a) M).mp hM.1
  set L := crossIn K a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaModU (.sl2 3 1) (restrictFamily (conjFamily L) X) :=
    hypOmegaModU_restrict hΛ X
  have hΛ₁g : HypOmegaGen (restrictFamily (conjFamily L) X) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ₁
  have hΛ' : HypOmegaGen
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_oddQuotientFamily hΛ₁)
  have hK : (conjSub c₀ L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c₀ L, ⟨c₀, rfl⟩, le_conjGen ⟨c₀, rfl⟩, rfl⟩
  have hJ : (conjSub c L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c L, ⟨c, rfl⟩, le_conjGen ⟨c, rfl⟩, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr_gen hΛ₁g hΛ' hN hK hJ hM
  rw [conjSub_subgroupOf] at hnb
  have hnL : conjSub (n : ↥(Subgroup.centralizer ({a} : Set G))) (conjSub c₀ L) ≤ X :=
    le_conjGen ⟨(n : ↥(Subgroup.centralizer ({a} : Set G))) * c₀, conjSub_mul _ _ _⟩
  have hcL : conjSub c L ≤ X := le_conjGen ⟨c, rfl⟩
  have hnb' := omegaNbr_of_restrict hnL hcL hnb
  rw [← conjSub_mul] at hnb'
  have heq := crossIn_nbr_eq d hzKa hΛ hw hnb'
  rw [heq, mul_assoc, conjSub_mul]
  exact secImg_conjSub_odd L hn (le_conjGen ⟨c₀ * w, rfl⟩)

end Quot

end CFSG.ClassicalInvolution.Asc77.C25J
