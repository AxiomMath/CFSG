module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexA
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAll

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20.late_hWc (d : Std20 p f K K' J S R R' W V z t) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  Thompson.commutes_of_mem_WSet d.branch.odd d.branch.five d.hyp d.hW

theorem Std20.late_R_mem_D (d : Std20 p f K K' J S R R' W V z t) :
    R ∈ DSet (CoreAssembly.conjClass K) W :=
  ⟨mem_RSet_of_isSylow2In d.late_mem_K d.hR, fun _ hx => d.hWN (d.hRS hx)⟩

theorem Std20.late_R'_mem_D (d : Std20 p f K K' J S R R' W V z t) :
    R' ∈ DSet (CoreAssembly.conjClass K) W :=
  ⟨mem_RSet_of_isSylow2In d.late_mem_K' d.hR', fun _ hx => d.hWN (d.hR'S hx)⟩

theorem Std20.late_KW (d : Std20 p f K K' J S R R' W V z t) :
    K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
  (Thompson.inf_W_of_mem_D d.branch.odd d.branch.five d.hyp d.hW d.late_R_mem_D d.late_mem_K
    d.hR).2.1

theorem Std20.late_K'W (d : Std20 p f K K' J S R R' W V z t) :
    K' ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
  (Thompson.inf_W_of_mem_D d.branch.odd d.branch.five d.hyp d.hW d.late_R'_mem_D d.late_mem_K'
    d.hR').2.1

theorem Std20.late_z_mem_W (d : Std20 p f K K' J S R R' W V z t) : z ∈ W := by
  have hKW := d.late_KW
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet d.late_hΩ hKW
  exact (AscL62.mem_of_uniqueInvolution_of_pGroup d.viol.hzK inf_le_left
    (Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hKW) (by omega) : z ∈ K ⊓ W).2

theorem Std20.late_t_mem_W (d : Std20 p f K K' J S R R' W V z t) : t ∈ W :=
  d.hVW d.htV

theorem Std20.late_twin_eq (d : Std20 p f K K' J S R R' W V z t) {g : G} (hg : conjSub g K = J)
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

theorem Std20.late_exists_n (d : Std20 p f K K' J S R R' W V z t) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * z * n⁻¹ = t := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩ := d.hyp
  obtain ⟨L₀, hL₀, hVL₀⟩ := Sec6Gen.exists_member_of_mem_USet d.late_hΩ d.hV
  have hzL₀ : IsUniqueInvolution L₀ t := by
    obtain ⟨a, ha⟩ := Sec6Gen.exists_uniqueInvolution d.late_hΩ hL₀
    have : t = a := by
      rcases ha.unique t (hVL₀ d.htV) d.viol.hzJ.sq with h | h
      · exact absurd h d.viol.hzJ.ne_one
      · exact h
    rwa [this]
  obtain ⟨T, hTD, hTL₀⟩ := Thompson.exists_sylow_mem_DSet hp hq hΩ d.hW d.hWS hL₀ d.hV hVL₀
    d.hVS
  obtain ⟨u, r, hd⟩ := late_exists_dData hp hq hΩ d.hW d.late_R_mem_D d.late_mem_K d.hR
    d.viol.hzK
  obtain ⟨v, s, hd'⟩ := late_exists_dData hp hq hΩ d.hW hTD hL₀ hTL₀ hzL₀
  have hKL : K ≠ L₀ := by
    intro h
    exact d.late_ne_inv (d.viol.hzK.eq (h ▸ hzL₀)).symm
  have hnot : L₀ ∉ omegaNbr (CoreAssembly.conjClass K) K := by
    intro h
    obtain ⟨-, z', hz', hz'L⟩ := d.late_nbr L₀ h
    exact d.late_ne_inv ((hzL₀.eq hz'L).trans (d.viol.hzK.eq hz').symm)
  obtain ⟨i, k, hio, hko, hi, hk, hra, hsz⟩ := late_pair hp hq hΩ d.late_hWc hd hd' hKL
    d.late_ne_inv.symm hnot
  have hrz : r * z * r⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK)
  have hzt : z * t = t * z := d.late_hWc z d.late_z_mem_W t d.late_t_mem_W
  refine ⟨r * s, Subgroup.mul_mem _ hd.r_normW hd'.r_normW, ?_⟩
  calc r * s * z * (r * s)⁻¹ = r * (s * z * s⁻¹) * r⁻¹ := by group
    _ = r * (z * t) * r⁻¹ := by rw [hsz]
    _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
    _ = z * (t * z) := by rw [hrz, hra]
    _ = t := by rw [← hzt, ← mul_assoc, d.viol.hzK.sq, one_mul]

theorem Std20.late_JW (d : Std20 p f K K' J S R R' W V z t) :
    J ⊓ W ∈ USet (CoreAssembly.conjClass K) := by
  obtain ⟨n, hn, hnz⟩ := d.late_exists_n
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
  · have e : J ⊓ W = conjSub n (K ⊓ W) := by rw [h, late_conjSub_inf, hnW]
    rw [e]
    exact USet.conj d.hyp.conjInvariant d.late_KW n
  · have e : J ⊓ W = conjSub n (K' ⊓ W) := by rw [h, late_conjSub_inf, hnW]
    rw [e]
    exact USet.conj d.hyp.conjInvariant d.late_K'W n

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
