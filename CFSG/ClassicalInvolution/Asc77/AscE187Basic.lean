module

public import CFSG.ClassicalInvolution.Asc77.AscE187Conj
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscSteps182

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

structure E187Hyps (p f : ℕ) [Fact p.Prime] : Prop where
  l67 : L6_7 p f
  l69 : L6_9 p f
  l611 : L6_11 p f
  e6 : E18_6 p f

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem orderOf_conj_mul_inv_eq (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) u
  simpa [MulAut.conj_apply] using this

theorem mem_dstarComp_of_twin (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) : K' ∈ dstarComp Ω K := by
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  by_cases hKK' : K' = K
  · rw [hKK']
    exact Relation.ReflTransGen.refl
  have hperp : K' ∈ KPerp Ω K := mem_kPerp_of_twin hΩ hK'Ω hK hzK' hzK
  rcases hperp with h | ⟨-, -, R, hR, hRK', hRN⟩
  · exact absurd h hKK'
  obtain ⟨U, hUR, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_cyclic_index_two
  have hRsyl : IsSylow2In R K' := hΩ.isSylow2In_of_mem_RSet_of_le hp hK'Ω hR hRK'
  have hU : U ∈ USet Ω := mem_USet_of_natCard hK'Ω hRsyl hUR hcyc hcard
  exact Relation.ReflTransGen.single
    ⟨hK'Ω, Or.inl ⟨hK'Ω, hKK', U, hU, hUR.trans hRK', hUR.trans hRN⟩⟩

omit [Finite G] in
theorem twinSet_subset_twinSet_of_mem {K K' : Subgroup G} (h : K' ∈ twinSet Ω K) :
    twinSet Ω K' ⊆ twinSet Ω K := by
  obtain ⟨-, z, hzK, hzK'⟩ := h
  rintro L ⟨hLΩ, z', hz'K', hz'L⟩
  obtain rfl : z' = z := hz'K'.eq hzK'
  exact ⟨hLΩ, z', hzK, hz'L⟩

omit [Finite G] in
theorem CentralizersTwinPerp.of_twin {K K' H : Subgroup G} (h : CentralizersTwinPerp Ω K H)
    (hK' : K' ∈ twinSet Ω K) : CentralizersTwinPerp Ω K' H :=
  fun L hL => h L (twinSet_subset_twinSet_of_mem hK' hL)

namespace E187Hyps

theorem etaAbelian (h : E187Hyps p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) :
    EtaAbelian Ω :=
  EtaAbelian.of_l6_9 h.l69 hp hq hΩ

theorem etaMeet (h : E187Hyps p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) :
    EtaMeet Ω :=
  EtaMeet.of_l6_11 h.l611 hp hq hΩ

end E187Hyps


section MinCex

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.mem_of_conj_mem_dstar_of {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K H : Subgroup G}
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J)
    (hmc : ∀ {u x : G}, u ∈ K → orderOf u = 4 → x * u * x⁻¹ ∈ H → x ∈ H)
    {M : Subgroup G} (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M)
    (hu4 : orderOf u = 4) {x : G} (hx : x * u * x⁻¹ ∈ H) : x ∈ H := by
  obtain ⟨k, hkH, hk⟩ := htrans M hMS
  rw [← hk, mem_conjSub_iff] at hu
  have hu4' : orderOf (k⁻¹ * u * k) = 4 := by
    have := orderOf_conj_mul_inv_eq k⁻¹ u
    simpa using this.trans hu4
  have hxk : (x * k) * (k⁻¹ * u * k) * (x * k)⁻¹ ∈ H := by
    have e : (x * k) * (k⁻¹ * u * k) * (x * k)⁻¹ = x * u * x⁻¹ := by group
    rw [e]
    exact hx
  have := hmc hu hu4' hxk
  have e2 : x = (x * k) * k⁻¹ := by group
  rw [e2]
  exact H.mul_mem this (H.inv_mem hkH)


theorem MinCex.mem_of_conj_mem_dstar (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {M : Subgroup G} (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M)
    (hu4 : orderOf u = 4) {x : G} (hx : x * u * x⁻¹ ∈ H) : x ∈ H := by
  exact E187C.mem_of_conj_mem_dstar_of c.hyp.trans
    (fun hu hu4 hx => c.mem_of_conj_mem hA hM hu hu4 hx) hMS hu hu4 hx

theorem MinCex.center_eq_bot (h6 : E18_6 p f) (c : MinCex p f Ω K S R W H) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, F, -, -, -, hF⟩ := h6 G Ω K S R W H c
  exact E187C.center_eq_bot_of_centralizer_eq_bot hF

theorem MinCex.centralizer_ne_top (h6 : E18_6 p f) (c : MinCex p f Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
  E187C.centralizer_singleton_ne_top (c.center_eq_bot h6) hx

end MinCex

end CFSG.ClassicalInvolution.Asc77
