module

public import CFSG.GH74.Uniqueness.SU.SU10Stmts
public import CFSG.GH74.Uniqueness.SU.SU10Setup
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.GH74.Uniqueness.SU.SU10Syl
public import CFSG.GH74.Uniqueness.SU.SU10Cl
public import CFSG.GH74.Uniqueness.SU.SU10Zbar
public import CFSG.GH74.GLS.TwoThin.Rank
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8

variable {G : Type} [Group G] [Finite G]

theorem rank3_centralizer {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z) {u : G}
    (hu : orderOf u = 2) : 3 ≤ Open.pRank 2 (centralizer ({u} : Set G)) := by
  have h3 : 3 ≤ CFSG.pRank 2 G := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 G]
    exact h.rank.trans (SU1.pRank_mono (by norm_num) le_top)
  have := CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G h.simple h.nonab h3 u hu
  rwa [CFSG.GH74.GLS.TwoThin.pRank_two_subgroup_eq_open] at this

omit [Finite G] in
theorem orderOf_eq_two_of_isConj {z x : G} (hz : orderOf z = 2) (hx : IsConj z x) :
    orderOf x = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  simpa [hz] using (MulAut.conj c).orderOf_eq z

theorem centralizer_ne_top_of_order_two {S : Sylow 2 G} {M : Subgroup G} {z : G}
    (h : Hyp21 S M z) {u : G} (hu : orderOf u = 2) : centralizer ({u} : Set G) ≠ ⊤ := by
  intro htop
  have hz : u ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({u} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have := h.simple
  rw [CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple G h.nonab,
    Subgroup.mem_bot] at hz
  rw [hz, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem centralizer_le_of_conj {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    (hHM : centralizer ({z} : Set G) ≤ M) {z' : G} (hz' : IsConj z z') (hz'M : z' ∈ M) :
    centralizer ({z'} : Set G) ≤ M := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hz'
  have hzM : z ∈ M := hHM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hrank2 : 2 ≤ Open.pRank 2 (S : Subgroup G) := le_trans (by norm_num) h.rank
  obtain ⟨m, hmM, hm⟩ := controls_involution_fusion S hrank2 h.gamma_le h.z_invol hzM
    (g := c⁻¹) (by rw [inv_inv, hc]; exact hz'M)
  have hz'm : m⁻¹ * z * m = z' := by
    rw [hm, inv_inv]
    exact hc
  intro g hg
  have hg := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hmg : m * g * m⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzz : z = m * z' * m⁻¹ := by rw [← hz'm]; group
    calc m * g * m⁻¹ * z = m * (g * z') * m⁻¹ := by rw [hzz]; group
      _ = m * (z' * g) * m⁻¹ := by rw [hg]
      _ = z * (m * g * m⁻¹) := by rw [hzz]; group
  have := M.mul_mem (M.mul_mem (M.inv_mem hmM) (hHM hmg)) hmM
  have h3 : m⁻¹ * (m * g * m⁻¹) * m = g := by group
  rw [h3] at this
  exact this

theorem exists_extremal_mem {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z) {u : G}
    (hu2 : orderOf u = 2) (huM : u ∈ M) :
    ∃ m ∈ M, m⁻¹ * u * m ∈ (S : Subgroup G) ∧
      IsSylowIn (centralizer ({m⁻¹ * u * m} : Set G))
        ((S : Subgroup G) ⊓ centralizer ({m⁻¹ * u * m} : Set G)) := by
  have hrank2 : 2 ≤ Open.pRank 2 (S : Subgroup G) := le_trans (by norm_num) h.rank
  have hSM : (S : Subgroup G) ≤ M := (le_gammaTwo_self hrank2).trans h.gamma_le
  obtain ⟨k, hkS, hk⟩ := exists_extremal_conj S hu2
  obtain ⟨m, hmM, hm⟩ := controls_involution_fusion S hrank2 h.gamma_le hu2 huM (g := k⁻¹)
    (by rw [inv_inv]; exact hSM hkS)
  rw [inv_inv] at hm
  refine ⟨m, hmM, ?_, ?_⟩
  · rw [hm]
    exact hkS
  · rw [hm]
    exact hk

theorem exists_conj_of_bar_conj {Hh : Subgroup G} {a b : G} (ha : a ∈ Hh) (hb : b ∈ Hh)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (h : ∃ c : Hbar Hh, c⁻¹ * QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨a, ha⟩ * c =
      QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨b, hb⟩) :
    ∃ c ∈ Hh, c⁻¹ * a * c = b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Hh) c
  have ha2' : orderOf (⟨a, ha⟩ : ↥Hh) = 2 :=
    (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥Hh)).symm.trans ha2
  have hb2' : orderOf (⟨b, hb⟩ : ↥Hh) = 2 :=
    (Subgroup.orderOf_coe (⟨b, hb⟩ : ↥Hh)).symm.trans hb2
  obtain ⟨y, hy⟩ := exists_conj_of_map_conj ha2' hb2' hc.symm
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem eq_of_map_eq_central {u a : G} (hu2 : orderOf u = 2) (ha2 : orderOf a = 2)
    (haH : a ∈ centralizer ({u} : Set G)) (h : QuotientGroup.mk'
      (pPrimeCore 2 (centralizer ({u} : Set G))) ⟨a, haH⟩ = zbar u) : a = u := by
  have hu2' : orderOf (⟨u, mem_centralizer_self u⟩ : ↥(centralizer ({u} : Set G))) = 2 :=
    (Subgroup.orderOf_coe (⟨u, mem_centralizer_self u⟩ : ↥(centralizer ({u} : Set G)))).symm.trans
      hu2
  have ha2' : orderOf (⟨a, haH⟩ : ↥(centralizer ({u} : Set G))) = 2 :=
    (Subgroup.orderOf_coe (⟨a, haH⟩ : ↥(centralizer ({u} : Set G)))).symm.trans ha2
  obtain ⟨n, -, hn⟩ := exists_conj_of_map_eq hu2' ha2' h.symm
  have hnu : (n : G) * u = u * (n : G) := Subgroup.mem_centralizer_singleton_iff.mp n.2
  have h1 := congrArg Subtype.val hn
  have h2 : (n : G)⁻¹ * u * (n : G) = a := h1
  rw [← h2]
  calc (n : G)⁻¹ * u * (n : G) = (n : G)⁻¹ * (u * (n : G)) := by group
    _ = (n : G)⁻¹ * ((n : G) * u) := by rw [hnu]
    _ = u := by group

end CFSG.GH74.Uniqueness.SU.SU10
