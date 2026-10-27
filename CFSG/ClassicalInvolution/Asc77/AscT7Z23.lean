module

public import CFSG.ClassicalInvolution.Asc77.AscExactDMain
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
open scoped commutatorElement MatrixGroups

namespace T7Z

section Elementary

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreOf_le_centralizer_conjSub {K : Subgroup G}
    (hK : oddCoreOf K ≤ Subgroup.centralizer (K : Set G)) (h : G) :
    oddCoreOf (conjSub h K) ≤ Subgroup.centralizer ((conjSub h K : Subgroup G) : Set G) := by
  rw [Thompson.oddCoreOf_conjSub_eq]
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hn' : h⁻¹ * n * h ∈ oddCoreOf K := mem_conjSub_iff.mp hn
  have hk' : h⁻¹ * k * h ∈ K := mem_conjSub_iff.mp hk
  have hc := Subgroup.mem_centralizer_iff.mp (hK hn') _ hk'
  calc k * n = h * ((h⁻¹ * k * h) * (h⁻¹ * n * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * n * h) * (h⁻¹ * k * h)) * h⁻¹ := by rw [hc]
    _ = n * k := by group

omit [Finite G] in
theorem le_of_cover_central {K₀ M N : Subgroup G} (hperf : ⁅K₀, K₀⁆ = K₀) (hMK : M ≤ K₀)
    (hNK : N ≤ K₀) (hNc : N ≤ Subgroup.centralizer (K₀ : Set G))
    (hcov : ∀ x ∈ K₀, ∃ i ∈ M, ∃ n ∈ N, x = i * n) : K₀ ≤ M := by
  refine hperf.symm.le.trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨i, hi, n, hn, rfl⟩ := hcov x hx
  obtain ⟨j, hj, m, hm, rfl⟩ := hcov y hy
  have hnc : ∀ w ∈ K₀, w * n = n * w := fun w hw =>
    Subgroup.mem_centralizer_iff.mp (hNc hn) w hw
  have hmc : ∀ w ∈ K₀, w * m = m * w := fun w hw =>
    Subgroup.mem_centralizer_iff.mp (hNc hm) w hw
  have hnj : n * j = j * n := (hnc j (hMK hj)).symm
  have hnm : n * m = m * n := hmc n (hNK hn)
  have hmi : Commute m i := (hmc i (hMK hi)).symm
  have c1 : i * n * (j * m) = i * j * m * n := by
    calc i * n * (j * m) = i * (n * j) * m := by group
      _ = i * (j * n) * m := by rw [hnj]
      _ = i * j * (n * m) := by group
      _ = i * j * (m * n) := by rw [hnm]
      _ = i * j * m * n := by group
  have c2 : m * i⁻¹ = i⁻¹ * m := (Commute.inv_right hmi).eq
  have key : ⁅i * n, j * m⁆ = i * j * i⁻¹ * j⁻¹ := by
    rw [commutatorElement_def]
    calc i * n * (j * m) * (i * n)⁻¹ * (j * m)⁻¹
        = i * j * m * n * (n⁻¹ * i⁻¹) * (m⁻¹ * j⁻¹) := by rw [c1]; group
      _ = i * j * m * i⁻¹ * m⁻¹ * j⁻¹ := by group
      _ = i * j * (m * i⁻¹) * m⁻¹ * j⁻¹ := by group
      _ = i * j * (i⁻¹ * m) * m⁻¹ * j⁻¹ := by rw [c2]
      _ = i * j * i⁻¹ * j⁻¹ := by group
  rw [key]
  exact M.mul_mem (M.mul_mem (M.mul_mem hi hj) (M.inv_mem hi)) (M.inv_mem hj)

end Elementary

section Core

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G}

omit [Fact p.Prime] [Finite G] in
theorem isOrthTag_ne {d : ℕ} {ε : Bool} {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h : IsOrthTag d ε t n) : t ≠ .G2 ∧ t ≠ .trialityD4 := by
  rcases h with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ |
    ⟨-, -, -, h, -⟩ <;> rw [h] <;> exact ⟨nofun, nofun⟩


theorem exactMembers_of_layerOrth (hst : AscStand p f Ω K)
    (hOK : oddCoreOf K ≤ Subgroup.centralizer (K : Set G)) {c : G} (hc2 : c * c = 1)
    (hOc : classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥) {d : ℕ} {ε : Bool}
    (hY : LayerOrthType p f Ω c d ε) : ExactMembers Ω := by
  classical
  have hp2 : p ≠ 2 := hst.odd
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  obtain ⟨t', n', hT, D, hcard, i, hit, hir⟩ := hY
  obtain ⟨hG2', hD4'⟩ := isOrthTag_ne hT
  have hG2 : D.tag i ≠ .G2 := hit ▸ hG2'
  have hD4 : D.tag i ≠ .trialityD4 := hit ▸ hD4'
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd h hD4
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨M', ⟨M, hMfam, hMY, rfl⟩, hMR⟩ := hRΦ
  obtain ⟨K₀, hK₀tq, rfl⟩ := hMfam
  have hfin : Finite (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i)
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (D.isFundTag i)
    (D.admissible i) hG2 hD4 hR
  have hcardR : Nat.card ↥R = Nat.card SL(2, GaloisField p (D.exp i)) := Nat.card_congr eR.toEquiv
  have hmapR : Nat.card ↥(R.map (D.hom i)) ≤ Nat.card ↥R :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd R (D.hom i))
  have hMcard : Nat.card ↥(exactCore c K₀) ≤ Nat.card SL(2, GaloisField p (D.exp i)) := by
    have h1 : Nat.card ↥(exactCore c K₀) =
        Nat.card ↥((exactCore c K₀).subgroupOf (exactLayer Ω c)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv).symm
    have hinj : Function.Injective
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c))) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOc]
    have h2 : Nat.card ↥(((exactCore c K₀).subgroupOf (exactLayer Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c)))) =
        Nat.card ↥((exactCore c K₀).subgroupOf (exactLayer Ω c)) :=
      Subgroup.card_map_of_injective hinj
    rw [hMR] at h2
    calc Nat.card ↥(exactCore c K₀) = Nat.card ↥((exactCore c K₀).subgroupOf (exactLayer Ω c)) := h1
      _ = Nat.card ↥(R.map (D.hom i)) := h2.symm
      _ ≤ Nat.card ↥R := hmapR
      _ = Nat.card SL(2, GaloisField p (D.exp i)) := hcardR
  obtain ⟨z₀, hz₀⟩ := hst.hyp.classical K₀ hK₀tq.1
  have hOM : classicalInvolutionOddCore ↥(exactCore c K₀) = ⊥ := by
    obtain ⟨eQ⟩ := nonempty_equiv_sl2_exactCore hz₀ hc2' hK₀tq.2
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (classicalInvolutionOddCore ↥(exactCore c K₀))
    rw [Nat.card_congr eQ.toEquiv] at h1
    rw [hexp] at hMcard
    have hpos : 0 < Nat.card SL(2, GaloisField p f) := by
      rw [← Nat.card_congr eQ.toEquiv]
      exact Nat.card_pos
    have hx : 0 < Nat.card ↥(classicalInvolutionOddCore ↥(exactCore c K₀)) := Nat.card_pos
    apply Subgroup.eq_bot_of_card_eq
    rw [h1] at hMcard
    nlinarith
  obtain ⟨h, hh⟩ := hst.trans K₀ hK₀tq.1
  have hOK₀ : oddCoreOf K₀ ≤ Subgroup.centralizer (K₀ : Set G) := by
    rw [← hh]
    exact oddCoreOf_le_centralizer_conjSub hOK h
  have hperf : ⁅K₀, K₀⁆ = K₀ := Subgroup.isPerfect_iff.mp hz₀.perfect
  have hK₀M : K₀ ≤ exactCore c K₀ :=
    le_of_cover_central hperf (exactCore_le_left c K₀) (oddCoreIn_le K₀) hOK₀
      (exactCore_cover hz₀ hc2' hK₀tq.2)
  have hO0 : oddCoreIn K₀ = ⊥ := by
    have h1 : oddCoreIn (exactCore c K₀) = exactCore c K₀ ⊓ oddCoreIn K₀ :=
      oddCoreIn_exactCore hz₀ hc2' hK₀tq.2
    have h2 : oddCoreIn (exactCore c K₀) = ⊥ := by
      show (classicalInvolutionOddCore ↥(exactCore c K₀)).map (exactCore c K₀).subtype = ⊥
      rw [hOM, Subgroup.map_bot]
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ exactCore c K₀ ⊓ oddCoreIn K₀ := ⟨hK₀M (oddCoreIn_le K₀ hx), hx⟩
    rw [← h1, h2] at hx'
    exact hx'
  have hO : classicalInvolutionOddCore ↥K₀ = ⊥ := by
    have h3 : (classicalInvolutionOddCore ↥K₀).map K₀.subtype = ⊥ := hO0
    exact (Subgroup.map_eq_bot_iff_of_injective _ K₀.subtype_injective).mp h3
  exact exactMembers_of_oddCore_eq_bot
    ⟨K, hst.mem, fun L hL => by
      obtain ⟨g, hg⟩ := hst.trans L hL
      exact ⟨g, hg.symm⟩⟩ hK₀tq.1 hO

theorem exactMembers_of_layer {K' W : Subgroup G} {z u e g : G}
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {c : G} (hc2 : c * c = 1)
    (hOc : classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥) {d : ℕ} {ε : Bool}
    (hY : LayerOrthType p f Ω c d ε) : ExactMembers Ω := by
  have hst := hs.stand
  have htw := ExactD.TwinPair.of_twinSet hst.odd hst.five hst.hyp hst.mem hs.hz hs.hK' hs.hne.symm
  exact exactMembers_of_layerOrth hst
    (htw.oddCoreOf_le_centralizer_of_alphaOf_bot hd.hu hd.hu2 hd.hu1 hd.huz hα) hc2 hOc hY

end Core

end T7Z

end CFSG.ClassicalInvolution.Asc77
