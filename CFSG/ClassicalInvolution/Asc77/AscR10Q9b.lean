module

public import CFSG.ClassicalInvolution.Asc77.AscR10Q9a
public import CFSG.ClassicalInvolution.Asc77.AscR10Rho
public import CFSG.ClassicalInvolution.Asc77.AscT3SInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r9_fus_plus [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b) (hF : FusAt S z b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {s : G} (hs2 : s * s = 1)
    (hsb : s * b = b * s) (hsz : ∃ g : G, s = g * z * g⁻¹) :
    ∃ c : G, c * b = b * c ∧ s = c * z * c⁻¹ := by
  obtain ⟨c₀, hc₀b, hc₀S⟩ := d.r9_exists_conj_into_S c7 c9 h8 hb hF hk hu huo hact hs2 hsb
  generalize hs₁ : c₀⁻¹ * s * c₀ = s₁ at hc₀S
  have hs : s = c₀ * s₁ * c₀⁻¹ := by rw [← hs₁]; group
  have hs₁2 : s₁ * s₁ = 1 := by
    have : s₁ * s₁ = c₀⁻¹ * (s * s) * c₀ := by rw [← hs₁]; group
    rw [this, hs2]; group
  have hs₁b : s₁ * b = b * s₁ := by
    rw [← hs₁]
    calc c₀⁻¹ * s * c₀ * b = c₀⁻¹ * s * (c₀ * b) := by group
      _ = c₀⁻¹ * s * (b * c₀) := by rw [hc₀b]
      _ = c₀⁻¹ * (s * b) * c₀ := by group
      _ = c₀⁻¹ * (b * s) * c₀ := by rw [hsb]
      _ = (c₀⁻¹ * b) * s * c₀ := by group
      _ = (b * c₀⁻¹) * s * c₀ := by
        have : c₀⁻¹ * b = b * c₀⁻¹ := by
          calc c₀⁻¹ * b = c₀⁻¹ * b * c₀ * c₀⁻¹ := by group
            _ = c₀⁻¹ * (b * c₀) * c₀⁻¹ := by group
            _ = c₀⁻¹ * (c₀ * b) * c₀⁻¹ := by rw [hc₀b]
            _ = b * c₀⁻¹ := by group
        rw [this]
      _ = b * (c₀⁻¹ * s * c₀) := by group
  have hs₁z : ∃ g : G, s₁ = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := hsz
    exact ⟨c₀⁻¹ * g, by rw [← hs₁, hg]; group⟩
  obtain ⟨c₁, hc₁b, hc₁⟩ := hF s₁ hs₁2 hs₁b hc₀S hs₁z
  refine ⟨c₀ * c₁, ?_, ?_⟩
  · calc c₀ * c₁ * b = c₀ * (c₁ * b) := by group
      _ = c₀ * (b * c₁) := by rw [hc₁b]
      _ = (c₀ * b) * c₁ := by group
      _ = (b * c₀) * c₁ := by rw [hc₀b]
      _ = b * (c₀ * c₁) := by group
  · calc s = c₀ * s₁ * c₀⁻¹ := hs
      _ = c₀ * (c₁ * z * c₁⁻¹) * c₀⁻¹ := by rw [hc₁]
      _ = c₀ * c₁ * z * (c₀ * c₁)⁻¹ := by group


theorem Std20.r9_noConj_plus [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b) (hF : FusAt S z b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) (g : G) :
    g⁻¹ * b * g ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
  intro ha'
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hCz : g⁻¹ * b * g ∈ Subgroup.centralizer ({z} : Set G) := d.r10a_X_le_C ha'
  have hcomm : z * (g⁻¹ * b * g) = (g⁻¹ * b * g) * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp hCz).symm
  have hbs : (g * z * g⁻¹) * b = b * (g * z * g⁻¹) := by
    calc (g * z * g⁻¹) * b = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by rw [hcomm]
      _ = b * (g * z * g⁻¹) := by group
  have hs2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [d.viol.hzK.sq]; group
  obtain ⟨c, hca, hcz⟩ := d.r9_fus_plus c7 c9 h8 hb hF hk hu huo hact hs2 hbs ⟨g, rfl⟩
  have hd₀ : g⁻¹ * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = z := by
      calc (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
        _ = z := by rw [← hcz]; group
    calc (g⁻¹ * c) * z = ((g⁻¹ * c) * z * (g⁻¹ * c)⁻¹) * (g⁻¹ * c) := by group
      _ = z * (g⁻¹ * c) := by rw [this]
  have hinv : (g⁻¹ * c)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hd₀
  have hnorm' := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hinv
  have h5 : (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hnorm' _).mp ha'
  have h6 : (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ = b := by
    calc (g⁻¹ * c)⁻¹ * (g⁻¹ * b * g) * ((g⁻¹ * c)⁻¹)⁻¹ = c⁻¹ * b * c := by group
      _ = b := by rw [mul_assoc, ← hca, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h6] at h5
  exact hb.not_mem_X h5

theorem Std20.r9_noConj [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b)
    (hFall : ∀ b' : G, FieldInv20 S K K' W z t b' → (∃ (u : G) (k : ℕ), 2 ≤ k ∧
      Subgroup.zpowers u = K ⊓ W ∧ orderOf u = 2 ^ (k + 1) ∧
      ∀ x ∈ K ⊓ W, b' * x * b'⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) → FusAt S z b') (g : G) :
    g⁻¹ * b * g ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨u, k, hk, hu, huo, hact | hact⟩ := hb.modular
  · exact d.r9_noConj_plus c7 c9 h8 hb (hFall b hb ⟨u, k, hk, hu, huo, hact⟩) hk hu huo hact g
  · obtain ⟨ρ, hρKK, hρS, hρ2, hρ1, hρz, hbρ, hb', hplus'⟩ :=
      d.r_exists_plus_rho c7 c9 h8 hb hk hu huo hact
    obtain ⟨m, hm, hmt⟩ := T3S.exists_conj_of_involutions_sup_mod d.branch.odd d.branch.five
      d.hyp d.late_mem_K d.late_mem_K' d.ne d.viol.hzK d.late_hzK' d.htKK d.viol.hzJ.sq
      d.viol.hzJ.ne_one d.late_ne_inv hρKK hρ2 hρ1 hρz
    obtain ⟨c, -, hcz⟩ := hb.fuse
    have hρzG : ∃ g' : G, ρ = g' * z * g'⁻¹ := ⟨m * c, by
      calc ρ = m * t * m⁻¹ := hmt.symm
        _ = m * (c * z * c⁻¹) * m⁻¹ := by rw [hcz]
        _ = m * c * z * (m * c)⁻¹ := by group⟩
    have hρb' : ρ * (b * ρ) = (b * ρ) * ρ := by
      calc ρ * (b * ρ) = (ρ * b) * ρ := by group
        _ = (b * ρ) * ρ := by rw [← hbρ]
    have hFb' := hFall (b * ρ) hb' ⟨u, k, hk, hu, huo, hplus'⟩
    obtain ⟨c₁, hc₁b, hc₁⟩ := hFb' ρ hρ2 hρb' hρS hρzG
    have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
    obtain ⟨v₀, -, -, -, huz, -⟩ := d.v_W_gen hu huo
    have hb'sq := hb'.sq
    have hbρρ : b * ρ * ρ = b := by
      calc b * ρ * ρ = b * (ρ * ρ) := by group
        _ = b := by rw [hρ2, mul_one]
    have hu1 : (b * ρ) * u * (b * ρ)⁻¹ = z * u := by
      rw [hplus' u huKW, zpow_add_one]
      have e : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
      rw [e, zpow_natCast, huz]
    have hub : u * (b * ρ) * u⁻¹ = (b * ρ) * z := by
      have hbi : (b * ρ)⁻¹ = b * ρ := inv_eq_of_mul_eq_one_right hb'sq
      rw [hbi] at hu1
      calc u * (b * ρ) * u⁻¹ = (b * ρ) * ((b * ρ)⁻¹ * u * (b * ρ)) * u⁻¹ := by group
        _ = (b * ρ) * ((b * ρ) * u * (b * ρ)⁻¹) * u⁻¹ := by rw [hbi]
        _ = (b * ρ) * (z * u) * u⁻¹ := by rw [hbi] at *; rw [hu1]
        _ = (b * ρ) * z := by group
    have hy : b = (c₁ * u) * (b * ρ) * (c₁ * u)⁻¹ := by
      calc b = (b * ρ) * ρ := hbρρ.symm
        _ = (b * ρ) * (c₁ * z * c₁⁻¹) := by rw [← hc₁]
        _ = c₁ * ((b * ρ) * z) * c₁⁻¹ := by
          calc (b * ρ) * (c₁ * z * c₁⁻¹) = ((b * ρ) * c₁) * z * c₁⁻¹ := by group
            _ = (c₁ * (b * ρ)) * z * c₁⁻¹ := by rw [← hc₁b]
            _ = c₁ * ((b * ρ) * z) * c₁⁻¹ := by group
        _ = c₁ * (u * (b * ρ) * u⁻¹) * c₁⁻¹ := by rw [hub]
        _ = (c₁ * u) * (b * ρ) * (c₁ * u)⁻¹ := by group
    intro ha'
    refine d.r9_noConj_plus c7 c9 h8 hb' hFb' hk hu huo hplus' ((c₁ * u)⁻¹ * g) ?_
    have e : ((c₁ * u)⁻¹ * g)⁻¹ * (b * ρ) * ((c₁ * u)⁻¹ * g) = g⁻¹ * b * g := by
      conv_rhs => rw [hy]
      group
    rw [e]
    exact ha'

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
