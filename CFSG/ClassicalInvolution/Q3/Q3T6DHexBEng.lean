module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexAEng
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_hWc
    (d : Std20F K K' J S R R' W V z t) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  Q3CL.Thompson.commutes_of_mem_WSet d.late_hΩ d.hW

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_R_mem_D
    (d : Std20F K K' J S R R' W V z t) :
    R ∈ DSet (CoreAssembly.conjClass K) W :=
  ⟨mem_RSet_of_isSylow2In d.late_mem_K d.hR, fun _ hx => d.hWN (d.hRS hx)⟩

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_R'_mem_D
    (d : Std20F K K' J S R R' W V z t) :
    R' ∈ DSet (CoreAssembly.conjClass K) W :=
  ⟨mem_RSet_of_isSylow2In d.late_mem_K' d.hR', fun _ hx => d.hWN (d.hR'S hx)⟩

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_KW
    (d : Std20F K K' J S R R' W V z t) :
    K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
  (Q3CL.Thompson.inf_W_of_mem_D d.late_hΩ d.hW d.late_R_mem_D d.late_mem_K
    d.hR).2.1

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_K'W
    (d : Std20F K K' J S R R' W V z t) :
    K' ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
  (Q3CL.Thompson.inf_W_of_mem_D d.late_hΩ d.hW d.late_R'_mem_D d.late_mem_K'
    d.hR').2.1

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_z_mem_W
    (d : Std20F K K' J S R R' W V z t) : z ∈ W := by
  have hKW := d.late_KW
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet d.late_hΩ hKW
  exact (AscL62.mem_of_uniqueInvolution_of_pGroup d.viol.hzK inf_le_left
    (Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hKW) (by omega) : z ∈ K ⊓ W).2

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_t_mem_W
    (d : Std20F K K' J S R R' W V z t) : t ∈ W :=
  d.hVW d.htV

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_twin_eq
    (d : Std20F K K' J S R R' W V z t) {g : G}
    (hg : conjSub g K = J)
    {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K) (hLt : IsUniqueInvolution L t) :
    L = J ∨ L = conjSub g K' := by
  have htg : t = g * z * g⁻¹ := by
    have h1 : IsUniqueInvolution J (g * z * g⁻¹) := hg ▸ d.viol.hzK.conj g
    exact d.viol.hzJ.eq h1
  have hL₂ : conjSub g⁻¹ L ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant g⁻¹ L hL
  have hinv : g⁻¹ * t * g⁻¹⁻¹ = z := by rw [htg]; group
  have hL₂t : IsUniqueInvolution (conjSub g⁻¹ L) z := hinv ▸ hLt.conj g⁻¹
  have hmem : conjSub g⁻¹ L ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hL₂, z, d.viol.hzK, hL₂t⟩
  rw [d.twins] at hmem
  have hLe : L = conjSub g (conjSub g⁻¹ L) := (conjSub_conjSub_inv g L).symm
  rcases hmem with h | h
  · left
    rw [hLe, h, hg]
  · right
    rw [hLe, h]

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_exists_n
    (d : Std20F K K' J S R R' W V z t)
    (hdd : ∀ {R₀ K₀ : Subgroup G} {z₀ : G}, R₀ ∈ DSet (CoreAssembly.conjClass K) W →
      K₀ ∈ CoreAssembly.conjClass K → IsSylow2In R₀ K₀ → IsUniqueInvolution K₀ z₀ →
      ∃ u r : G, Sec71.DData (CoreAssembly.conjClass K) W R₀ K₀ u r z₀)
    (hpair : ∀ {R₀ K₀ T₀ L₀ : Subgroup G} {u r z₀ v s a : G},
      Sec71.DData (CoreAssembly.conjClass K) W R₀ K₀ u r z₀ →
      Sec71.DData (CoreAssembly.conjClass K) W T₀ L₀ v s a → K₀ ≠ L₀ → z₀ ≠ a →
      L₀ ∉ omegaNbr (CoreAssembly.conjClass K) K₀ →
      ∃ i k : ℤ, Odd i ∧ Odd k ∧ r * v * r⁻¹ = v * u ^ i ∧ s * u * s⁻¹ = u * v ^ k ∧
        r * a * r⁻¹ = a * z₀ ∧ s * z₀ * s⁻¹ = z₀ * a) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * z * n⁻¹ = t := by
  have hΩ := d.late_hΩ
  obtain ⟨L₀, hL₀, hVL₀⟩ := Sec6Gen.exists_member_of_mem_USet d.late_hΩ d.hV
  have hzL₀ : IsUniqueInvolution L₀ t := by
    obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution d.late_hΩ hL₀
    have : t = a := by
      rcases ha.unique t (hVL₀ d.htV) d.viol.hzJ.sq with h | h
      · exact absurd h d.viol.hzJ.ne_one
      · exact h
    rwa [this]
  obtain ⟨T, hTD, hTL₀⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ d.hW d.hWS hL₀ d.hV hVL₀
    d.hVS
  obtain ⟨u, r, hd⟩ := hdd d.late_R_mem_D d.late_mem_K d.hR d.viol.hzK
  obtain ⟨v, s, hd'⟩ := hdd hTD hL₀ hTL₀ hzL₀
  have hKL : K ≠ L₀ := by
    intro h
    exact d.late_ne_inv (d.viol.hzK.eq (h ▸ hzL₀)).symm
  have hnot : L₀ ∉ omegaNbr (CoreAssembly.conjClass K) K := by
    intro h
    obtain ⟨-, z', hz', hz'L⟩ := d.late_nbr L₀ h
    exact d.late_ne_inv ((hzL₀.eq hz'L).trans (d.viol.hzK.eq hz').symm)
  obtain ⟨i, k, hio, hko, hi, hk, hra, hsz⟩ := hpair hd hd' hKL d.late_ne_inv.symm hnot
  have hrz : r * z * r⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK)
  have hzt : z * t = t * z := d.late_hWc z d.late_z_mem_W t d.late_t_mem_W
  refine ⟨r * s, Subgroup.mul_mem _ hd.r_normW hd'.r_normW, ?_⟩
  calc r * s * z * (r * s)⁻¹ = r * (s * z * s⁻¹) * r⁻¹ := by group
    _ = r * (z * t) * r⁻¹ := by rw [hsz]
    _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
    _ = z * (t * z) := by rw [hrz, hra]
    _ = t := by rw [← hzt, ← mul_assoc, d.viol.hzK.sq, one_mul]

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.late_JW
    (d : Std20F K K' J S R R' W V z t)
    (hn : ∃ n ∈ Subgroup.normalizer (W : Set G), n * z * n⁻¹ = t) :
    J ⊓ W ∈ USet (CoreAssembly.conjClass K) := by
  obtain ⟨n, hn, hnz⟩ := hn
  obtain ⟨g, hg⟩ := d.late_mem_J
  have hnW : conjSub n W = W := mem_normalizer_iff_conjSub_eq.mp hn
  have h1 : IsUniqueInvolution (conjSub n K) t := hnz ▸ d.viol.hzK.conj n
  have h2 : IsUniqueInvolution (conjSub n K') t := hnz ▸ d.late_hzK'.conj n
  have hmK : conjSub n K ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant n K d.late_mem_K
  have hmK' : conjSub n K' ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant n K' d.late_mem_K'
  have hne : conjSub n K ≠ conjSub n K' := fun h => d.ne (conjSub_injective n h).symm
  have hJ : J = conjSub n K ∨ J = conjSub n K' := by
    rcases d.late_twin_eq hg hmK h1 with h | h
    · exact Or.inl h.symm
    · rcases d.late_twin_eq hg hmK' h2 with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hne
  rcases hJ with h | h
  · have e : J ⊓ W = conjSub n (K ⊓ W) := by rw [h, late_conjSub_infE, hnW]
    rw [e]
    exact USet.conj d.hyp.conjInvariant d.late_KW n
  · have e : J ⊓ W = conjSub n (K' ⊓ W) := by rw [h, late_conjSub_infE, hnW]
    rw [e]
    exact USet.conj d.hyp.conjInvariant d.late_K'W n

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
