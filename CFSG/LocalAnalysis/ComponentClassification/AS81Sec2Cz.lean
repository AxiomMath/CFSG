module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Act
public import CFSG.RankThree.Literature.FSmithInvolution
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Sec2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_oddCoreIn_of_le_normalizer {X H : Subgroup G} (hXH : X ≤ H) (hX : Odd (Nat.card X))
    (hHX : H ≤ normalizer (X : Set G)) : X ≤ AS76b.oddCoreIn H := by
  have hn : (X.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hXH).mpr hHX
  have hodd : Odd (Nat.card (X.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv]
  have h := AS76b.le_assemblyOddCore hn hodd
  intro x hx
  exact ⟨⟨x, hXH hx⟩, h (show (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H from hx), rfl⟩

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem Q_le_centralizer (hQ : Sec2Q G A R g E F T₀ Q u y z) : Q ≤ centralizer ({z} : Set G) :=
  le_normalizer.trans hQ.normalizer_le_centralizer

theorem centralizer_le_normalizer_M (_hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) :
    centralizer ({z} : Set G) ≤ normalizer (sec2M Q (sec2T E T₀) : Set G) := by
  intro c hc
  refine mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
  · have h := Sec2.conj_mem_sec2M (inv_mem (hCN hc)) hm
    simpa using h
  · have h := Sec2.conj_mem_sec2M (hCN hc) hm
    have e : c⁻¹ * (c * m * c⁻¹) * c = m := by group
    rwa [e] at h

theorem oddCoreIn_M_inf_centralizer_eq_bot (hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) :
    AS76b.oddCoreIn (sec2M Q (sec2T E T₀) ⊓ centralizer (Q : Set G)) = ⊥ := by
  rw [← le_bot_iff, ← hO]
  have hMC : sec2M Q (sec2T E T₀) ≤ centralizer ({z} : Set G) :=
    hQ.M_le_normalizer.trans hQ.normalizer_le_centralizer
  refine Sec2.le_oddCoreIn_of_le_normalizer
    ((AS76b.oddCoreIn_le _).trans (inf_le_left.trans hMC)) (AS76b.odd_card_oddCoreIn _) ?_
  intro c hc
  refine AS76b.normalizer_le_normalizer_oddCoreIn _ (mem_normalizer_iff.mpr fun x => ?_)
  have e1 := mem_normalizer_iff.mp (hQ.centralizer_le_normalizer_M hCN hc) x
  have e2 := mem_normalizer_iff.mp (Sec2.normalizer_le_normalizer_centralizer Q (hCN hc)) x
  simp only [mem_inf] at e1 e2 ⊢
  exact ⟨fun h => ⟨e1.mp h.1, e2.mp h.2⟩, fun h => ⟨e1.mpr h.1, e2.mpr h.2⟩⟩

theorem centralizer_Q_eq (h24 : Step24) (h26 : Step26) (h212 : Step212) (h216 : Step216)
    (hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) :
    centralizer (Q : Set G) = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := hQ.sylow_zpowers_centralizer h24 h26 h212 h216
  have hzC : zpowers z ≤ centralizer (Q : Set G) := zpowers_le.mpr hQ.z_mem_centralizer_Q
  have hzc : zpowers z ≤ centralizer (centralizer (Q : Set G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.mpr fun c hc => (mem_centralizer_iff.mp hc z hQ.z_mem_Q).symm
  have hodd : Odd ((zpowers z).relIndex (centralizer (Q : Set G))) := by
    have h := (isSylowOf_iff.mp hsyl).2.2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  have heq := eq_sup_oddCoreIn_of_central hsyl.isPGroup hzC hzc hodd
  have hO' : AS76b.oddCoreIn (centralizer (Q : Set G)) = ⊥ := by
    rw [← le_bot_iff, ← hO]
    have hCz : centralizer (Q : Set G) ≤ centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hQ.z_mem_Q)
    refine Sec2.le_oddCoreIn_of_le_normalizer ((AS76b.oddCoreIn_le _).trans hCz)
      (AS76b.odd_card_oddCoreIn _) ?_
    intro c hc
    exact AS76b.normalizer_le_normalizer_oddCoreIn _
      (Sec2.normalizer_le_normalizer_centralizer Q (hCN hc))
  rw [heq, hO', sup_bot_eq]

theorem centralizer_subgroupOf_le (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) :
    centralizer ((Q.subgroupOf (centralizer ({z} : Set G)) :
      Subgroup ↥(centralizer ({z} : Set G))) : Set ↥(centralizer ({z} : Set G))) ≤
      Q.subgroupOf (centralizer ({z} : Set G)) := by
  intro c hc
  have hcQ : (c : G) ∈ centralizer (Q : Set G) := mem_centralizer_iff.mpr fun q hq =>
    congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨q, hQ.Q_le_centralizer hq⟩ hq)
  rw [hQ.centralizer_Q_eq h24 h26 h212 h216 hO hCN] at hcQ
  exact (zpowers_le.mpr hQ.z_mem_Q) hcQ

theorem le_Q_of_isPGroup (h24 : Step24) (h26 : Step26) (h212 : Step212) (h216 : Step216)
    (hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({z} : Set G))
    (hCP : centralizer ({z} : Set G) ≤ normalizer (P : Set G)) : P ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, ρ, hadd, hsurj, hker, -, hρ, -, hρker⟩ := h216 G A R g E F T₀ Q u y z hQ
  have hMN : sec2M Q (sec2T E T₀) ≤ normalizer (Q : Set G) := hQ.M_le_normalizer
  have hMC : sec2M Q (sec2T E T₀) ≤ centralizer ({z} : Set G) :=
    hMN.trans hQ.normalizer_le_centralizer
  have hCM := hQ.centralizer_le_normalizer_M hCN
  have hO' := hQ.oddCoreIn_M_inf_centralizer_eq_bot hO hCN
  rw [hO', sup_bot_eq] at hρker
  have hzQ := hQ.z_mem_Q
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := fun a ha b hb =>
    commutator_mem_of_extraspecial hQ.q8.1 hQ.centerIn_Q ha hb
  have hzcen : ∀ c ∈ centralizer ({z} : Set G), ∀ w ∈ zpowers z, c * w * c⁻¹ = w := by
    rintro c hc _ ⟨k, rfl⟩
    exact Sec2.conj_zpow_eq (mem_centralizer_singleton_iff.mp hc) k
  have hD₁ := hQ.acts_trivially_of_isPGroup h216 (D := P ⊓ sec2M Q (sec2T E T₀))
    (hP.to_le inf_le_left)
    (inf_le_right.trans hMN) (inf_le_left.trans hPC) (by
      intro m hm a ha hall d hd
      have hdm : m⁻¹ * d * m ∈ P ⊓ sec2M Q (sec2T E T₀) := by
        refine ⟨?_, ?_⟩
        · have := (mem_normalizer_iff.mp (hCP (inv_mem (hMC hm))) d).mp hd.1
          simpa using this
        · exact (sec2M Q (sec2T E T₀)).mul_mem ((sec2M Q (sec2T E T₀)).mul_mem
            ((sec2M Q (sec2T E T₀)).inv_mem hm) (Subgroup.mem_inf.mp hd).2) hm
      have h1 := hall _ hdm
      have h2 := hzcen m (hMC hm) _ h1
      have e : m * ((m⁻¹ * d * m) * a * (m⁻¹ * d * m)⁻¹ * a⁻¹) * m⁻¹ =
          d * (m * a * m⁻¹) * d⁻¹ * (m * a * m⁻¹)⁻¹ := by group
      rw [← e, h2]
      exact h1)
  have hPM : P ⊓ sec2M Q (sec2T E T₀) ≤ Q := by
    intro d hd
    have hρd : ρ ⟨d, hd.2⟩ = 1 := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨a, ha, rfl⟩ := hsurj v
      rw [← hρ ⟨d, hd.2⟩ a ha]
      change ψ (d * a * d⁻¹) = ψ a
      have hda := (mem_normalizer_iff.mp (hMN hd.2) a).mp ha
      exact (Sec2.psi_eq_iff hadd hker hda ha).mpr (hD₁ d hd a ha)
    have : (⟨d, hd.2⟩ : sec2M Q (sec2T E T₀)) ∈ ρ.ker := hρd
    rw [hρker] at this
    exact this
  have hPMc : ∀ p ∈ P, ∀ m ∈ sec2M Q (sec2T E T₀), p * m * p⁻¹ * m⁻¹ ∈ Q := by
    intro p hp m hm
    refine hPM ⟨?_, ?_⟩
    · have h1 : m * p⁻¹ * m⁻¹ ∈ P := (mem_normalizer_iff.mp (hCP (hMC hm)) _).mp (inv_mem hp)
      have := mul_mem hp h1
      simpa [mul_assoc] using this
    · have h1 : p * m * p⁻¹ ∈ sec2M Q (sec2T E T₀) :=
        (mem_normalizer_iff.mp (hCM (hPC hp)) m).mp hm
      exact (sec2M Q (sec2T E T₀)).mul_mem h1 ((sec2M Q (sec2T E T₀)).inv_mem hm)
  have hPN : P ≤ normalizer (Q : Set G) := hPC.trans hCN
  have hP₁ := hQ.acts_trivially_of_isPGroup h216 hP hPN hPC (by
    intro m hm a ha hall p hp
    have hc := hPMc p hp m hm
    have hma : m * a * m⁻¹ ∈ Q := (mem_normalizer_iff.mp (hMN hm) a).mp ha
    have hw := hall p hp
    have hcz : p * m * p⁻¹ * m⁻¹ ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hQ.z_mem_centralizer_Q _ hc)
    have hmw : m * (p * a * p⁻¹ * a⁻¹) * m⁻¹ = p * a * p⁻¹ * a⁻¹ := hzcen m (hMC hm) _ hw
    have hcw := hzcen _ hcz _ hw
    have e : p * (m * a * m⁻¹) * p⁻¹ * (m * a * m⁻¹)⁻¹ =
        ((p * m * p⁻¹ * m⁻¹) * (m * (p * a * p⁻¹ * a⁻¹) * m⁻¹) * (p * m * p⁻¹ * m⁻¹)⁻¹) *
          ((p * m * p⁻¹ * m⁻¹) * (m * a * m⁻¹) * (p * m * p⁻¹ * m⁻¹)⁻¹ * (m * a * m⁻¹)⁻¹) := by
      group
    rw [e, hmw, hcw]
    exact mul_mem hw (hcomm _ hc _ hma))
  intro p hp
  have hQC := hQ.Q_le_centralizer
  have hQn : (Q.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQC).mpr hCN
  have hQ' : CFSG.IsExtraspecialPGroup 2 (Q.subgroupOf (centralizer ({z} : Set G))) :=
    CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (subgroupOfEquivOfLe hQC).symm hQ.q8.1
  let _ := CFSG.GroupTheory.extraspecialQuotientModule hQ'
  have hCQ' := hQ.centralizer_subgroupOf_le h24 h26 h212 h216 hO hCN
  have hz₀ : ∀ c : ↥(centralizer ({z} : Set G)), c * zC z = zC z * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
  have hz₀1 : zC z ≠ 1 := fun h => by
    have h1 : z = 1 := congrArg Subtype.val h
    have := hQ.order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hρ1 : CFSG.RankThree.Literature.FSmith.extraspecialConjOrth hQ' hQn ⟨p, hPC hp⟩ = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := CFSG.RankThree.Literature.FSmith.exists_ofMul_of v
    rw [CFSG.RankThree.Literature.FSmith.extraspecialConjOrth_apply, OneMemClass.coe_one,
      LinearEquiv.coe_one, id, CFSG.RankThree.Literature.FSmith.ofMul_of_eq_iff hQ',
      CFSG.RankThree.Literature.FSmith.mem_center_iff_coe hQ' hz₀ hz₀1 hzQ]
    have hmem := hP₁ p hp (x : G) x.2
    have e : (((CFSG.RankThree.Literature.FSmith.conjAut hQn ⟨p, hPC hp⟩ x * x⁻¹ :
        ↥(Q.subgroupOf (centralizer ({z} : Set G)))) : ↥(centralizer ({z} : Set G)) ) : G) =
        p * (x : G) * p⁻¹ * (x : G)⁻¹ := by
      simp [CFSG.RankThree.Literature.FSmith.conjAut_apply]
    rcases Sec2.eq_one_or_eq_of_mem_zpowers hQ.order hmem with h | h
    · left
      exact Subtype.ext (e.trans h)
    · right
      exact Subtype.ext (e.trans h)
  exact CFSG.RankThree.Literature.FSmith.mem_of_extraspecialConjOrth_eq_one hQ' hQn hCQ' hρ1

end Sec2Q

end CFSG.ComponentClassification.AS81
