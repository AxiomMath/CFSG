module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Star
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Crown
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Iso
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Normalize
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3TypeAMain

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

structure E1Data (Q : Sylow 2 J) (B : Subgroup J) (z u : J) (T : Sylow 2 (quasiNormalizer u))
    (L : Subgroup (QuasiQuotient u)) (S : Sylow 2 J) (y x m : J) : Prop where
  starLift : StarLift B z u
  setting : Setting J Q B
  fourGen : FourGen Q z
  oneComponent : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L
  caseC3BCD : CaseC3BCD (partCSylow T) (partCLeft T L) (partCRight T L) (S : Subgroup J)
    (centralElt J) u y x m (Subgroup.center J)

theorem StarLift.exists_e1Data (hu : StarLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (T : Sylow 2 (quasiNormalizer u)) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hP : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u) {y : J}
    (hyT : y ∈ partCSylow T) (hy : y ∉ partCLeft T L ⊔ partCRight T L)
    (hyy : y * y ∈ partCRight T L)
    (hψ : Nonempty ((partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup 4))
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup 2)) :
    ∃ (S : Sylow 2 J) (y' x m : J), E1Data Q B z u T L S y' x m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : ∀ x, x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := fun x => h.mem_center_iff
  obtain ⟨y', hy'⟩ := hP.exists_caseC3 (partCSylow_le_normalizer T) hyT hy hyy hφ hψ
  obtain ⟨S, hTS⟩ := (T.isPGroup'.map (quasiNormalizer u).subtype).exists_le_sylow
  by_cases hTSeq : partCSylow T = (S : Subgroup J)
  · exact (hy'.false_of_sylow h.perfect _ hZ S hTSeq.symm).elim
  · obtain ⟨x, hs⟩ := hy'.exists_caseC3Top (Subgroup.center J) hZ
      (partCSylow_maxInNormalizer T) S.isPGroup' hTS hTSeq
    have hx2 := hs.mul_self_mem_of_sylow h.perfect (Subgroup.center J) hZ S rfl
    obtain ⟨x', hs', hx'1, hx'y⟩ := hs.exists_normalized (Subgroup.center J) hZ hx2
    obtain ⟨m, hm, hm1, hm2⟩ := hs'.moved
    exact ⟨S, y', x', m, hu, h, hz, hL, ⟨hs', hZ, hx'1, hx'y, hm, hm1, hm2⟩⟩

section Membership

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {g : J}

omit [Finite J] in
theorem mem_quasiNormalizer_of_mem_partCSylow (hg : g ∈ partCSylow T) : g ∈ quasiNormalizer u :=
  Subgroup.map_subtype_le _ hg

omit [Finite J] in
theorem mem_sylow_of_mem_partCSylow (hg : g ∈ partCSylow T) :
    (⟨g, mem_quasiNormalizer_of_mem_partCSylow hg⟩ : quasiNormalizer u) ∈
      (T : Subgroup (quasiNormalizer u)) := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
  exact ht

omit [Finite J] in
theorem quasiMk_mem_of_mem_partCLeft (hg : g ∈ partCLeft T L) (hgX : g ∈ quasiNormalizer u) :
    quasiMk u ⟨g, hgX⟩ ∈ L := by
  obtain ⟨t, ⟨-, htL⟩, rfl⟩ := Subgroup.mem_map.mp hg
  exact htL

omit [Finite J] in
theorem quasiMk_mem_of_mem_partCRight (hg : g ∈ partCRight T L) (hgX : g ∈ quasiNormalizer u) :
    quasiMk u ⟨g, hgX⟩ ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  obtain ⟨t, ⟨-, htK⟩, rfl⟩ := Subgroup.mem_map.mp hg
  exact htK

omit [Finite J] in
theorem partCLeft_le : partCLeft T L ≤ partCSylow T :=
  Subgroup.map_mono inf_le_left

omit [Finite J] in
theorem partCRight_le : partCRight T L ≤ partCSylow T :=
  Subgroup.map_mono inf_le_left

end Membership

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem star : Nat.card (Subgroup.center L) = 2 ∧ quasiBar u ∉ L ∧
    Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) ∧
    ∀ g : QuasiQuotient u, orderOf g = 2 →
      g ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  obtain ⟨L', hL', h1, h2, h3, h4⟩ := d.starLift.star
  obtain rfl : L' = L := d.oneComponent.unique L' hL'.component
  exact ⟨h1, h2, h3, h4⟩

theorem baseConfig : BaseConfig (quasiImage B u) (quasiCentral u) :=
  d.starLift.toEscapingLift.baseConfig d.setting d.fourGen d.starLift.rank

@[expose] noncomputable def eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5) :=
  d.star.2.2.1.some

theorem quasiMk_centralElt :
    quasiMk u ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ = quasiCentral u :=
  d.starLift.toEscapingLift.quasiMk_centralElt d.setting

theorem quasiCentral_mul_self : quasiCentral u * quasiCentral u = 1 :=
  d.baseConfig.mul_self

theorem commute_quasiCentral (g : QuasiQuotient u) : g * quasiCentral u = quasiCentral u * g :=
  (d.baseConfig.commute_center g).eq

theorem quasiCentral_ne_one : quasiCentral u ≠ 1 := fun h1 => by
  have h2 := d.baseConfig.order
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem quasiCentral_mem : quasiCentral u ∈ L := d.oneComponent.mem

theorem quasiCentral_mem_centralizer :
    quasiCentral u ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) :=
  Subgroup.mem_centralizer_iff.mpr fun g _ => d.commute_quasiCentral g

theorem quasiBar_mem_centralizer :
    quasiBar u ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) :=
  d.oneComponent.mem_centralizer

theorem eq_of_mem_center {c : L} (hc : c ∈ Subgroup.center L) :
    (c : QuasiQuotient u) = 1 ∨ (c : QuasiQuotient u) = quasiCentral u := by
  rcases d.oneComponent.eq_one_or_eq_of_card_two d.baseConfig d.star.1 hc with h | h
  · exact Or.inl (by rw [h]; rfl)
  · exact Or.inr h

theorem eq_of_mem_of_mem_centralizer {l : QuasiQuotient u} (hl : l ∈ L)
    (hlK : l ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    l = 1 ∨ l = quasiCentral u :=
  d.eq_of_mem_center (OneComponent.mem_center_of_mem_centralizer (l := ⟨l, hl⟩) hlK)

theorem eq_of_mem_of_mul_self {l : QuasiQuotient u} (hl : l ∈ L) (hll : l * l = 1) :
    l = 1 ∨ l = quasiCentral u := by
  by_cases hl1 : l = 1
  · exact Or.inl hl1
  have h2 : orderOf (⟨l, hl⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hll) hl1
  exact d.eq_of_mem_center (mem_center_of_orderOf_eq_two_of_alternating d.oneComponent.perfect
    d.star.1 d.eA h2)

theorem eq_of_mem_centralizer_of_mul_self {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) (hkk : k * k = 1) :
    k = 1 ∨ k = quasiCentral u := by
  by_cases hk1 : k = 1
  · exact Or.inl hk1
  exact Or.inr (d.oneComponent.eq_of_mem_centralizer k hk
    (orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1))

omit d in
theorem eq_one_of_mem_oddCore {g : quasiNormalizer u} (hg : g ∈ pPrimeCore 2 (quasiNormalizer u))
    (hgg : g * g = 1) : g = 1 := by
  have h1 := Subgroup.orderOf_dvd_natCard _ hg
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  have h3 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.coprime_two_left.mpr (quasi_oddCore_odd u)).symm h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem y_mem : y ∈ quasiNormalizer u :=
  mem_quasiNormalizer_of_mem_partCSylow d.caseC3BCD.mem

theorem m_mem : m ∈ quasiNormalizer u :=
  mem_quasiNormalizer_of_mem_partCSylow (partCRight_le d.caseC3BCD.m_mem)

@[expose] noncomputable def yBar : QuasiQuotient u := quasiMk u ⟨y, d.y_mem⟩

@[expose] noncomputable def mBar : QuasiQuotient u := quasiMk u ⟨m, d.m_mem⟩

theorem yBar_mem_sylow : d.yBar ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) :=
  Subgroup.mem_map_of_mem _ (mem_sylow_of_mem_partCSylow d.caseC3BCD.mem)

theorem mBar_mem_centralizer :
    d.mBar ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) :=
  quasiMk_mem_of_mem_partCRight d.caseC3BCD.m_mem _

theorem yBar_mul_self : d.yBar * d.yBar = quasiCentral u := by
  rw [yBar, ← map_mul, ← d.quasiMk_centralElt]
  congr 1
  exact Subtype.ext d.caseC3BCD.mul_self

theorem yBar_not_mem : d.yBar ∉ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  intro hmem
  have hT' := Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective
    (pPrimeCore 2 (quasiNormalizer u))) T
  have hyT : d.yBar ∈ ((T.mapSurjective (QuotientGroup.mk'_surjective
      (pPrimeCore 2 (quasiNormalizer u))) : Sylow 2 (QuasiQuotient u)) :
        Subgroup (QuasiQuotient u)) := by
    rw [hT']
    exact d.yBar_mem_sylow
  obtain ⟨l, ⟨hlT, hlL⟩, k, ⟨hkT, hkK⟩, hlk⟩ :=
    d.oneComponent.exists_mul_eq_of_mem_sup d.star.1 _ hyT hmem
  rw [hT'] at hlT hkT
  obtain ⟨t₁, ht₁T, rfl⟩ := Subgroup.mem_map.mp hlT
  obtain ⟨t₂, ht₂T, rfl⟩ := Subgroup.mem_map.mp hkT
  have heq : t₁ * t₂ = ⟨y, d.y_mem⟩ := quasiMk_injOn_twoGroup u T.isPGroup'
    ((T : Subgroup (quasiNormalizer u)).mul_mem ht₁T ht₂T)
    (mem_sylow_of_mem_partCSylow d.caseC3BCD.mem) (by rw [map_mul]; exact hlk)
  apply d.caseC3BCD.not_mem
  have hy : y = (t₁ : J) * t₂ := by rw [← Subgroup.coe_mul, heq]
  rw [hy]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ ⟨ht₁T, hlL⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ ⟨ht₂T, hkK⟩))

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
