module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NPm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma conjSub_le_of_le {H K : Subgroup G} {x : G} (hHK : H ≤ K)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) : conjSub x H ≤ K := by
  intro y hy
  rw [mem_conjSub_iff'] at hy
  obtain ⟨h, hh, rfl⟩ := hy
  exact ((Subgroup.mem_normalizer_iff (H := K)).mp hx h).mp (hHK hh)

private lemma le_normalizer_conjSub {H K : Subgroup G} {x : G}
    (hHK : K ≤ Subgroup.normalizer (H : Set G)) (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (conjSub x H : Set G) := by
  have hxK : K.map (MulAut.conj x).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := x)).mp hx
  calc
    K = K.map (MulAut.conj x).toMonoidHom := hxK.symm
    _ ≤ (Subgroup.normalizer (H : Set G)).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hHK
    _ ≤ Subgroup.normalizer
          ((H.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map (H := H) (f := (MulAut.conj x).toMonoidHom)
    _ = Subgroup.normalizer (conjSub x H : Set G) := rfl

theorem y7n_card_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(M3 c.s) = 2 ^ 6 := by
  have hF : c.s.fr.F ≤ M3 c.s := (y54_M3_cand c hH).1
  have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M3 c.s)
  rw [inf_of_le_left hF] at h
  rw [y54_M3_relIndex c hH, (y54_F_isE3 hH).2] at h
  rw [← h]
  norm_num

theorem y7n_conj_M3 {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h7 : c.Upto79) {L1 : Subgroup G}
    (hL1 : IsCompPre c.s L1) {x : G} (hx : x ∈ normalizer (K7 c.s : Set G)) :
    conjSub x (M3 c.s) = M3 c.s := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, _⟩, _⟩, _⟩, _⟩, h76⟩, _⟩, _⟩, _⟩ := h7
  have hA : SimpleSec L1 (M3 c.s) := y7n_simpleSec_L1 (s := c.s) hL1
  have hB : SimpleSec (conjSub c.s.t L1) (M3 c.s) := y7n_simpleSec_L1t hH hL1
  have hM2 : IsPGroup 2 (M3 c.s) := y7n_M3_pgroup h71 h76
  have hKM : K7 c.s ≤ Subgroup.normalizer (M3 c.s : Set G) := by
    rw [← hL1.2.2.1]
    exact sup_le ((Subgroup.le_normalizer_iff (H := L1) (K := M3 c.s)).mpr hA.normal)
      ((Subgroup.le_normalizer_iff (H := conjSub c.s.t L1) (K := M3 c.s)).mpr hB.normal)
  have hMK : M3 c.s ≤ K7 c.s := by
    rw [← hL1.2.2.1]
    exact hL1.1.trans le_sup_left
  have hQK : conjSub x (M3 c.s) ≤ K7 c.s := conjSub_le_of_le hMK hx
  have hQn : ∀ k ∈ K7 c.s, ∀ q ∈ conjSub x (M3 c.s), k * q * k⁻¹ ∈ conjSub x (M3 c.s) :=
    fun k hk q hq => (Subgroup.le_normalizer_iff.mp (le_normalizer_conjSub hKM hx)) k hk q hq
  have hQ2 : IsPGroup 2 (conjSub x (M3 c.s)) := hM2.map (MulAut.conj x).toMonoidHom
  have hle : conjSub x (M3 c.s) ≤ M3 c.s :=
    y7n_normal_two_le hA hB hL1.2.2.1 hL1.2.2.2.1 hL1.2.2.2.2.1 hM2 hQK hQn hQ2
  have hcard : Nat.card (conjSub x (M3 c.s)) = Nat.card (M3 c.s) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

theorem y7n_comm_P_M3 {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    (h7 : c.Upto79) {L1 : Subgroup G} (hL1 : IsCompPre c.s L1) :
    ∀ x ∈ P7 c.e, ⁅c.g, x⁆ ∈ M3 c.s := by
  have h7' := h7
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h72⟩, _⟩, _⟩, h75⟩, h76⟩, h77⟩, _⟩, _⟩ := h7
  intro x hx
  change x ∈ (P7 c.e : Set G) at hx
  rw [h76.1, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hga : ⁅c.g, a⁆ ∈ M3 c.s := h72.2.2.2 hRT a ha
  have hgb : ⁅c.g, b⁆ ∈ M3 c.s := h75.2.2.2 hRT b hb
  have haP : a ∈ P7 c.e := Subgroup.mem_sup_left ha
  have hconj : conjSub a (M3 c.s) = M3 c.s :=
    y7n_conj_M3 hH h7' hL1 (Subgroup.le_normalizer (H := K7 c.s) (h77.1.1 haP))
  have hconjb : a * ⁅c.g, b⁆ * a⁻¹ ∈ M3 c.s := by
    have hmem : a * ⁅c.g, b⁆ * a⁻¹ ∈ conjSub a (M3 c.s) :=
      (mem_conjSub_iff' a (M3 c.s) _).mpr ⟨⁅c.g, b⁆, hgb, rfl⟩
    rwa [hconj] at hmem
  have hid : ⁅c.g, a * b⁆ = ⁅c.g, a⁆ * (a * ⁅c.g, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact (M3 c.s).mul_mem hga hconjb

end CFSG.OddStandard.HigherRank.YamadaG23
