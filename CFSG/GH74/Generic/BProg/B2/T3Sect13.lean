module

public import CFSG.GH74.Generic.BProg.B2.T3Sect13Sylow
public import CFSG.GH74.Generic.BProg.B2.Prop111
import CFSG.GH74.Generic.BProg.Cor2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T3Sect13

open CFSG.GH74.GLS.C3.Layer1

theorem gammaK_conjugate_le {S M : Subgroup G} {k : ℕ} {m : G} (hm : m ∈ M)
    (h : gammaK 2 S k ≤ M) : gammaK 2 (conjugate S m⁻¹) k ≤ M := by
  refine iSup₂_le fun Q hQS => iSup_le fun hk => ?_
  intro g hg
  set Q' := conjugate Q m with hQ'
  have hQ'S : Q' ≤ S := by
    intro q hq
    rw [hQ', Back.mem_conjugate_iff'] at hq
    have := hQS hq
    rw [Back.mem_conjugate_iff', show m⁻¹ * (m * q * m⁻¹) * m⁻¹⁻¹ = q by group] at this
    exact this
  have hrank : k ≤ pRank 2 ↥Q' := by rw [hQ', Back.pRank_conjugate']; exact hk
  have hg' : m⁻¹ * g * m ∈ normalizer (Q' : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hQ', Back.mem_conjugate_iff', Back.mem_conjugate_iff']
    have e1 : m * (m⁻¹ * g * m * x * (m⁻¹ * g * m)⁻¹) * m⁻¹ = g * (m * x * m⁻¹) * g⁻¹ := by group
    rw [e1]
    exact mem_normalizer_iff.1 hg (m * x * m⁻¹)
  have hmem : m⁻¹ * g * m ∈ M :=
    h ((le_iSup₂_of_le Q' hQ'S (le_iSup_of_le hrank le_rfl) :
      normalizer (Q' : Set G) ≤ gammaK 2 S k) hg')
  have e : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hm hmem) (M.inv_mem hm)

theorem inU0_conjugate {A M : Subgroup G} (hA : InU0 M A) {u : G} (hu : u ∈ M) :
    InU0 M (conjugate A u⁻¹) := by
  obtain ⟨⟨hAM, hAel, hr2⟩, hrk, hγ⟩ := hA
  have hrank : pRank 2 ↥(conjugate A u⁻¹) = pRank 2 ↥A := Back.pRank_conjugate' A u⁻¹
  refine ⟨⟨?_, Back.isElementaryAbelian_conjugate hAel u⁻¹, hrank ▸ hr2⟩, hrank ▸ hrk, ?_⟩
  · intro a ha
    rw [Back.mem_conjugate_iff'] at ha
    have e : a = u * (u⁻¹ * a * u⁻¹⁻¹) * u⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hu (hAM ha)) (M.inv_mem hu)
  · rw [hrank]
    exact gammaK_conjugate_le hu hγ

end T3Sect13

theorem not_mem_M_of_commuting_conj (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (_hQM : Q ≤ M)
    {H : Subgroup G} (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K)
    (hr : pRank 2 (CMbar M K) ≤ 1) {h : G} (hne : h * x * h⁻¹ ≠ x)
    (hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹)) : h ∉ M := by
  intro hhM
  have hN := T3Sect13Sylow.barIn_normal_of_c1 hs hKM hH hc1 hr
  have hxX : x ∈ CMbar M K := T3Rank.Q_le_CMbar hs hKM hH hc1 (x_mem_Q hs)
  have hyX : h * x * h⁻¹ ∈ CMbar M K := T3Sect13Sylow.mem_CMbar_conj hKM hN hhM hxX
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hy2 : orderOf (h * x * h⁻¹) = 2 := by
    rw [← hx2]
    exact (isConj_iff.2 ⟨h, rfl⟩ : IsConj x (h * x * h⁻¹)).orderOf_eq.symm
  have := T3Sect13Sylow.two_le_pRank_of_commuting_involutions hxX hyX hx2 hy2 hcomm.symm hne.symm
  omega

theorem not_centralizes_conj_A_of (hZ : CenterlessS345) (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (hQM : Q ≤ M) (h2 : Stage2Concl2 M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) (hr : pRank 2 (CMbar M K) ≤ 1)
    {h : G} (hne : h * x * h⁻¹ ≠ x) (hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹)) {u : G}
    (hu : u ∈ M) :
    ¬ ∀ a ∈ A, (h * x * h⁻¹) * (u * a * u⁻¹) = (u * a * u⁻¹) * (h * x * h⁻¹) := by
  intro hall
  have hB : InU0 M (conjugate A u⁻¹) := T3Sect13.inU0_conjugate (inU0_A hs) hu
  have hBy : ∀ b ∈ conjugate A u⁻¹, b * (h * x * h⁻¹) = (h * x * h⁻¹) * b := by
    intro b hb
    rw [C3.Layer1.Back.mem_conjugate_iff'] at hb
    have := hall _ hb
    rw [show u * (u⁻¹ * b * u⁻¹⁻¹) * u⁻¹ = b by group] at this
    exact this.symm
  have hCx : centralizer ({x} : Set G) ≤ M := centralizer_x_le_M_of hZ hs hKM hQM h2
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({x} : Set G))
  have hconj : ∃ g : G, g * (h * x * h⁻¹) * g⁻¹ = x := ⟨h⁻¹, by group⟩
  obtain ⟨m, hmM, hm⟩ := prop92 h2 hconj hB hBy hS (hS.le.trans hCx)
  have hy : m⁻¹ * x * m⁻¹⁻¹ = h * x * h⁻¹ := by
    calc m⁻¹ * x * m⁻¹⁻¹ = m⁻¹ * (m * (h * x * h⁻¹) * m⁻¹) * m⁻¹⁻¹ := by rw [hm]
      _ = h * x * h⁻¹ := by group
  refine not_mem_M_of_commuting_conj hs hKM hQM hH hc1 hr (h := m⁻¹) ?_ ?_ (M.inv_mem hmM)
  · rw [hy]; exact hne
  · rw [hy]; exact hcomm

end CFSG.GH74.Generic.BProg.B2
