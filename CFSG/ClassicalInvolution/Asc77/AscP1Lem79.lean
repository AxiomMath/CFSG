module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep
public import CFSG.ClassicalInvolution.AschTight.Sec71Main

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem eq_one_of_mem_inf_OCW (hW : W ∈ WSet Ω) {x : G} (hxW : x ∈ W) (hxO : x ∈ OCW W) :
    x = 1 :=
  eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hxO
    ((isPGroup_of_mem_WSet hW).to_le (Subgroup.zpowers_le.mpr hxW))

theorem Ctx.conj_inv_eq_conj (c : Ctx p f Ω W) (ρ : Rep Ω W) {x : G} (hx : x ∈ W) :
    ρ.r⁻¹ * x * ρ.r = ρ.r * x * ρ.r⁻¹ := by
  have hsq : ρ.r * ρ.r ∈ W := D_sq_mem c.hp c.hq c.hΩ c.hW ρ.hR ρ.hr
  have hrN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
  have hy : ρ.r⁻¹ * x * ρ.r ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) x).mp hx
    simpa using this
  have h := c.comm_W _ hsq _ hy
  calc ρ.r⁻¹ * x * ρ.r = ((ρ.r * ρ.r) * (ρ.r⁻¹ * x * ρ.r)) * (ρ.r * ρ.r)⁻¹ := by
        rw [h]; group
    _ = ρ.r * x * ρ.r⁻¹ := by group

theorem Ctx.rel_exact (c : Ctx p f Ω W) {ρ σ : Rep Ω W} (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {u : G} (hu : Subgroup.zpowers u = ρ.R ⊓ W) {v : G}
    (hv : Subgroup.zpowers v = σ.R ⊓ W) :
    ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧ σ.r * u * σ.r⁻¹ = u * v' ∧
      ρ.r * v' * ρ.r⁻¹ = v' * u := by
  have hρcl := eq_closure_pair c.hp c.hq c.hΩ c.hW ρ.hR hu ρ.hr ρ.hrW
  have hσcl := eq_closure_pair c.hp c.hq c.hΩ c.hW σ.hR hv σ.hr σ.hrW
  obtain ⟨-, hcases⟩ := Disconnected.AschTight.Sec71.l7_1_proved p f c.hp c.hq G Ω c.hΩ c.hA W
    c.hW ρ.R ρ.hR σ.R σ.hR u ρ.r v σ.r hu hρcl hv hσcl
  have h8 : ∀ (K : Subgroup G) (R : Subgroup G), IsSylow2In R K → R ∈ DSet Ω W → 4 ≤ Nat.card R :=
    fun K R hR hRD => by
      have := c.hΩ.eight_le_of_mem_RSet c.hp hRD.1
      omega
  have hρ2 : IsPGroup 2 ρ.R := ρ.hRK.2.1
  have hσ2 : IsPGroup 2 σ.R := σ.hRK.2.1
  have hρ8 := h8 ρ.K ρ.R ρ.hRK ρ.hR
  have hσ8 := h8 σ.K σ.R σ.hRK σ.hR
  rcases hcases with ⟨J, hJ, hRJ, hTJ⟩ | ⟨J, hJ, J', hJ', hRJ, hTJ', hnbr, -⟩ |
      ⟨J, hJ, J', hJ', hRJ, hTJ', -, -, v', hv', h1, h2⟩
  · exfalso
    exact hne ((c.hΩ.eq_of_le_of_le ρ.hK hJ hρ2 hρ8 ρ.hRK.1 hRJ).trans
      (c.hΩ.eq_of_le_of_le σ.hK hJ hσ2 hσ8 σ.hRK.1 hTJ).symm)
  · exfalso
    have e1 : ρ.K = J := c.hΩ.eq_of_le_of_le ρ.hK hJ hρ2 hρ8 ρ.hRK.1 hRJ
    have e2 : σ.K = J' := c.hΩ.eq_of_le_of_le σ.hK hJ' hσ2 hσ8 σ.hRK.1 hTJ'
    rw [e1, e2] at hnot
    exact hnot hnbr
  · have hv'W : v' ∈ W := by
      have : v' ∈ Subgroup.zpowers v := hv' ▸ Subgroup.mem_zpowers v'
      rw [hv] at this
      exact this.2
    have huW : u ∈ W := by
      have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
      rw [hu] at this
      exact this.2
    have hσN : σ.r ∈ Subgroup.normalizer (W : Set G) := σ.r_mem_normalizer
    have hρN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
    refine ⟨v', hv', ?_, ?_⟩
    · have ha : σ.r⁻¹ * u * σ.r ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hσN) u).mp huW
        simpa using this
      have hb : (u * v')⁻¹ ∈ W := W.inv_mem (W.mul_mem huW hv'W)
      have h3 := eq_one_of_mem_inf_OCW c.hW (W.mul_mem ha hb) h1
      have h4 : σ.r⁻¹ * u * σ.r = u * v' := mul_inv_eq_one.mp h3
      rw [← c.conj_inv_eq_conj σ huW, h4]
    · have ha : ρ.r⁻¹ * v' * ρ.r ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρN) v').mp hv'W
        simpa using this
      have hb : (v' * u)⁻¹ ∈ W := W.inv_mem (W.mul_mem hv'W huW)
      have h3 := eq_one_of_mem_inf_OCW c.hW (W.mul_mem ha hb) h2
      have h4 : ρ.r⁻¹ * v' * ρ.r = v' * u := mul_inv_eq_one.mp h3
      rw [← c.conj_inv_eq_conj ρ hv'W, h4]

end Thompson

end CFSG.ClassicalInvolution.Asc77
