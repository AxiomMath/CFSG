module

public import CFSG.GH74.Generic.BProg.B2.T3S1Bar
import CFSG.GH74.Generic.BProg.Cor2
import CFSG.GH74.Generic.OuterInvolution
import CFSG.GH74.GLS.C3.Layer1.BackConj
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B2.T3Sect13C1

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem not_centralizes_conj_A_cx {x : G} {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (hQM : Q ≤ M) (h2 : Stage2Concl2 M) {H : Subgroup G}
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) (hr : pRank 2 (CMbar M K) ≤ 1)
    (hCx : centralizer ({x} : Set G) ≤ M) {h : G} (hne : h * x * h⁻¹ ≠ x)
    (hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹)) {u : G} (hu : u ∈ M) :
    ¬ ∀ a ∈ A, (h * x * h⁻¹) * (u * a * u⁻¹) = (u * a * u⁻¹) * (h * x * h⁻¹) := by
  intro hall
  have hB : InU0 M (conjugate A u⁻¹) := T3Sect13.inU0_conjugate (inU0_A hs) hu
  have hBy : ∀ b ∈ conjugate A u⁻¹, b * (h * x * h⁻¹) = (h * x * h⁻¹) * b := by
    intro b hb
    rw [C3.Layer1.Back.mem_conjugate_iff'] at hb
    have := hall _ hb
    rw [show u * (u⁻¹ * b * u⁻¹⁻¹) * u⁻¹ = b by group] at this
    exact this.symm
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({x} : Set G))
  have hconj : ∃ g : G, g * (h * x * h⁻¹) * g⁻¹ = x := ⟨h⁻¹, by group⟩
  obtain ⟨m, hmM, hm⟩ := prop92 h2 hconj hB hBy hS (hS.le.trans hCx)
  have hy : m⁻¹ * x * m⁻¹⁻¹ = h * x * h⁻¹ := by
    calc m⁻¹ * x * m⁻¹⁻¹ = m⁻¹ * (m * (h * x * h⁻¹) * m⁻¹) * m⁻¹⁻¹ := by rw [hm]
      _ = h * x * h⁻¹ := by group
  refine not_mem_M_of_commuting_conj hs hKM hQM hH hc1 hr (h := m⁻¹) ?_ ?_ (M.inv_mem hmM)
  · rw [hy]; exact hne
  · rw [hy]; exact hcomm

theorem false_of_c1_S1_of (hFacts : ∀ (Kt : Type) [Group Kt], QShape1 Kt → S1Facts Kt)
    {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (h2 : Stage2Concl2 M) (hAK : A ≤ K)
    (hsh : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hc1 : barIn M H = barIn M K)
    (hCx : centralizer ({x} : Set G) ≤ M) (hr : pRank 2 (CMbar M K) ≤ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ M := h1.K_le
  have hQM : Q ≤ M := h1.Q_le
  have hH : IsMinSubnormalIn K M H := h1.H_min
  obtain ⟨hN, T, hQT, hTM, hTx⟩ := sylow_center_of_c1 hs hKM hQM h2 hH hc1 hr
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hxT : x ∈ (T : Subgroup G) := hQT (x_mem_Q hs)
  have hxM : x ∈ M := hQM (x_mem_Q hs)
  obtain ⟨g, hgT, hgne⟩ := exists_conj_in_sylow_ne hs.hyp.simple hs.hyp.nonab hx2 T hxT hTx
  obtain ⟨h, rfl⟩ : ∃ h : G, g = h⁻¹ := ⟨g⁻¹, (inv_inv g).symm⟩
  have hyeq : h⁻¹⁻¹ * x * h⁻¹ = h * x * h⁻¹ := by rw [inv_inv]
  have hyM : h * x * h⁻¹ ∈ M := hyeq ▸ hTM hgT
  have hy2 : orderOf (h * x * h⁻¹) = 2 := by
    rw [← hx2]
    exact (isConj_iff.2 ⟨h, rfl⟩ : IsConj x (h * x * h⁻¹)).orderOf_eq.symm
  have hcomm : (h * x * h⁻¹) * x = x * (h * x * h⁻¹) := hyeq ▸ hTx _ hgT
  have hne : h * x * h⁻¹ ≠ x := hyeq ▸ hgne
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hH.2.1.2
  have hKc : IsComponent (barIn M K) := isComponent_barIn_of_isSubnormal hs hKM (hc1 ▸ hHsub)
  obtain ⟨e⟩ := T3Sect13C1.exists_equiv_barIn hKM hKc
  have hshK : QShape1 ↥(barIn M K) := CFSG.GH74.L5U5.IsSL4Model.of_mulEquiv hsh e
  have hF : S1Facts ↥(barIn M K) := hFacts _ hshK
  obtain ⟨-, hAel, hA8, -⟩ := hs.src
  obtain ⟨hxK, hzc⟩ := x_mem_and_center hF hs hKM hH hc1 hr hAK
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have := hN
  set yb : Mbar M := ρ ⟨h * x * h⁻¹, hyM⟩ with hyb
  have hyb2 : yb * yb = 1 := by
    rw [hyb, ← map_mul]
    rw [show (⟨h * x * h⁻¹, hyM⟩ : ↥M) * ⟨h * x * h⁻¹, hyM⟩ = 1 from
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hy2, pow_orderOf_eq_one]; rfl), map_one]
  set α : MulAut ↥(barIn M K) := MulAut.conjNormal yb with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hyb2, map_one]
  rcases hF.dich α hαα with ⟨E₀, hE₀, hfix⟩ | hQ8
  ·
    have hc : ∀ e ∈ E₀, yb * (e : Mbar M) = (e : Mbar M) * yb := by
      intro e he
      have h1 := congrArg (fun k : ↥(barIn M K) => (k : Mbar M)) (hfix e he)
      simp only [hα, MulAut.conjNormal_apply] at h1
      calc yb * (e : Mbar M) = (yb * (e : Mbar M) * yb⁻¹) * yb := by group
        _ = (e : Mbar M) * yb := by rw [h1]
    obtain ⟨u, huM, hu⟩ := exists_conj_centralized_E8 hF hKM hAK hAel hA8 hyM hy2 hE₀ hc
    exact not_centralizes_conj_A_cx hs hKM hQM h2 hH hc1 hr hCx hne hcomm huM hu
  ·
    have hshape : ShapeModel ↥(barIn M K) := Or.inl hshK
    have hLC : ∀ g ∈ barIn M K, g ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) →
        g = 1 ∨ g = ρ ⟨x, hxM⟩ := by
      intro g hg hgc
      have hcen : (⟨g, hg⟩ : ↥(barIn M K)) ∈ Subgroup.center ↥(barIn M K) := by
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc k k.2)
      rcases (hzc _).1 hcen with h0 | h0
      · left
        exact congrArg Subtype.val h0
      · right
        exact h0
    have hCinv : ∀ c ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)),
        c * c = 1 → c = 1 ∨ c = ρ ⟨x, hxM⟩ :=
      fun c hc hcc => cent_invol hs hKM hH hc1 hr hxM hxK hc hcc
    have hxbK : ρ ⟨x, hxM⟩ ∈ barIn M K := ⟨⟨x, hxM⟩, mem_subgroupOf.2 hxK, rfl⟩
    have ht := transfer_mem hshape hCx hxM hx2 hzc hLC hCinv hxbK hyM hy2 hcomm hQ8
    set xh : G := h⁻¹ * x * h with hxh
    have hxhC : xh * x = x * xh := by
      rw [hxh]
      calc h⁻¹ * x * h * x = h⁻¹ * (x * (h * x * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * x * h⁻¹) * x) * h := by rw [hcomm]
        _ = x * (h⁻¹ * x * h) := by group
    have hxhM : xh ∈ M := hCx (Subgroup.mem_centralizer_singleton_iff.2 hxhC)
    have hxh2 : orderOf xh = 2 := by
      rw [← hx2]
      exact (isConj_iff.2 ⟨h⁻¹, by rw [hxh, inv_inv]⟩ : IsConj x xh).orderOf_eq.symm
    set tb : ↥(barIn M K) := ⟨ρ ⟨xh, hxhM⟩, ht⟩ with htb
    have htt : tb * tb = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, htb, ← map_mul]
      rw [show (⟨xh, hxhM⟩ : ↥M) * ⟨xh, hxhM⟩ = 1 from
        Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hxh2, pow_orderOf_eq_one]; rfl), map_one]
      rfl
    obtain ⟨E₁, hE₁, htE₁⟩ := hF.invol tb htt
    have hc : ∀ e ∈ E₁, ρ ⟨xh, hxhM⟩ * (e : Mbar M) = (e : Mbar M) * ρ ⟨xh, hxhM⟩ := by
      intro e he
      have h1 := hE₁.1.toIsMulCommutative.is_comm.comm (⟨tb, htE₁⟩ : ↥E₁) ⟨e, he⟩
      have h2 := congrArg (fun k : ↥E₁ => ((k : ↥(barIn M K)) : Mbar M)) h1
      exact h2
    obtain ⟨u, huM, hu⟩ := exists_conj_centralized_E8 hF hKM hAK hAel hA8 hxhM hxh2 hE₁ hc
    have hxh' : h⁻¹ * x * h⁻¹⁻¹ = xh := by rw [hxh, inv_inv]
    refine not_centralizes_conj_A_cx hs hKM hQM h2 hH hc1 hr hCx (h := h⁻¹) ?_ ?_ huM ?_
    · rw [hxh']
      intro hx
      apply hne
      calc h * x * h⁻¹ = h * xh * h⁻¹ := by rw [hx]
        _ = x := by rw [hxh]; group
    · rw [hxh']
      exact hxhC
    · rw [hxh']
      exact hu

end CFSG.GH74.Generic.BProg.B2.T3S1
