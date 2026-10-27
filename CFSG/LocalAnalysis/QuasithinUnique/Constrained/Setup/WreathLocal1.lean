module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer5

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem mem_map_oddOrderSubgroup {G K : Type*} [Group G] [Group K] [Finite G] (ρ : G →* K)
    (X : Subgroup G) {d : K} (hd : d ∈ X.map ρ) (hodd : Odd (orderOf d)) :
    d ∈ (oddOrderSubgroup X).map ρ := by
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hy : x ^ 2 ^ a ∈ oddOrderSubgroup X := by
    apply Subgroup.subset_closure
    refine ⟨X.pow_mem hx _, ?_⟩
    have hdvd : 2 ^ a ∣ orderOf x := ⟨b, hab⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
    exact hb
  exact mem_of_odd_orderOf_of_pow_mem (k := a) hodd ⟨x ^ 2 ^ a, hy, map_pow _ _ _⟩

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

@[expose] noncomputable def preD (i : Fin r) : Subgroup H := (h.Dat i).comap h.rho

@[expose] noncomputable def Yi (i : Fin r) : Subgroup H := oddOrderSubgroup (h.preD i)

include h

omit [Finite H] in
theorem Dat_le_B (i : Fin r) : h.Dat i ≤ h.B := by
  let _ := h.cg
  exact cubeAt_le_baseGp h.planeFamily i

omit [Finite H] in
theorem rho_smul_planes (x : H) (j : Fin r) :
    h.rho x • planesIn W I j = planesIn W I (h.piH x j) := by
  let _ := h.cg
  exact permHom_spec h.planeFamily
    ⟨h.rho x, wreathAut_le_permuting h.planeFamily Pm (h.rho_mem_wreathAut x)⟩ j

omit [Finite H] in
theorem conj_Dat_mem (x : H) {i : Fin r} {d : MulAut ↥W} (hd : d ∈ h.Dat i) :
    h.rho x * d * (h.rho x)⁻¹ ∈ h.Dat (h.piH x i) := by
  let _ := h.cg
  exact conj_cubeAt_mem h.planeFamily (h.rho_smul_planes x) hd

theorem rho_map_Yi (i : Fin r) : (h.Yi i).map h.rho = h.Dat i := by
  let _ := h.cg
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  · intro d hd
    have hdB : d ∈ baseGp (planesIn W I) := cubeAt_le_baseGp h.planeFamily i hd
    have hdr : d ∈ h.rho.range := by
      rw [h.rho_range]
      exact baseGp_le_wreathAut h.planeFamily Pm hdB
    obtain ⟨x, rfl⟩ := hdr
    have hx : x ∈ h.preD i := hd
    have h3 : h.rho x ^ 3 = 1 := pow_three_of_mem_cubeBase h.planeFamily (cubeAt_le_cubeBase h.planeFamily i hd)
    have hodd : Odd (orderOf (h.rho x)) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
    exact mem_map_oddOrderSubgroup h.rho (h.preD i) ⟨x, hx, rfl⟩ hodd

omit [Finite H] in
theorem Yi_le_N (i : Fin r) : h.Yi i ≤ oddOrderSubgroup (⊤ : Subgroup H) :=
  Subgroup.closure_mono fun _ hx => ⟨Subgroup.mem_top _, hx.2⟩

omit [Finite H] in
theorem preD_conj {x y : H} {i : Fin r} (hy : y ∈ h.preD i) : x * y * x⁻¹ ∈ h.preD (h.piH x i) := by
  show h.rho (x * y * x⁻¹) ∈ h.Dat (h.piH x i)
  rw [map_mul, map_mul, map_inv]
  exact h.conj_Dat_mem x hy

omit [Finite H] in
theorem Yi_conj {x y : H} {i : Fin r} (hy : y ∈ h.Yi i) : x * y * x⁻¹ ∈ h.Yi (h.piH x i) := by
  have h1 : (h.Yi i).map (MulAut.conj x).toMonoidHom ≤ h.Yi (h.piH x i) := by
    unfold Yi
    rw [oddOrderSubgroup_map_mulEquiv (MulAut.conj x)]
    refine Subgroup.closure_mono fun z hz => ⟨?_, hz.2⟩
    obtain ⟨y', hy', rfl⟩ := hz.1
    exact h.preD_conj hy'
  exact h1 ⟨y, hy, rfl⟩

theorem S_normalizes_Yi {s : H} (hs : s ∈ elemBaumannIn 2 R) (i : Fin r) :
    s ∈ Subgroup.normalizer (h.Yi i : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := h.exists_t
  have h1 : h.piH s = 1 := h.piH_eq_one_of_mem_S ht hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := h.Yi_conj (x := s) hy
    rwa [h1] at this
  · intro hy
    have := h.Yi_conj (x := s⁻¹) hy
    have h2 : h.piH s⁻¹ = 1 := by rw [map_inv, h1, inv_one]
    rw [h2] at this
    simpa [mul_assoc] using this

theorem Yi_not_le_M (i : Fin r) : ¬ h.Yi i ≤ M := by
  let _ := h.cg
  have hF := h.planeFamily
  intro hYM
  have hker : h.rho.ker ≤ M := by
    rw [h.ker_rho_eq_centralizer_V]
    intro x hx
    have := h.frattini.2.2.2.1 hx 1 (Subgroup.mem_top _)
    simpa using this
  have hDj : ∀ j, h.Dat j ≤ M.map h.rho := by
    intro j d hd
    obtain ⟨x, hxR, hx⟩ := h.transitive_R i j
    have hσ : h.piH x i = j := by
      have := h.map_conj_plane x i
      rw [hx] at this
      exact (h.I_injective this).symm
    have hd' : (h.rho x)⁻¹ * d * (h.rho x) ∈ h.Dat i := by
      have h1 := h.conj_Dat_mem x⁻¹ hd
      have h2 : h.piH x⁻¹ j = i := by
        rw [map_inv, ← hσ]
        simp
      rw [h2, map_inv, inv_inv] at h1
      exact h1
    obtain ⟨y, hy, hyd⟩ : (h.rho x)⁻¹ * d * (h.rho x) ∈ (h.Yi i).map h.rho := by
      rw [h.rho_map_Yi]
      exact hd'
    refine ⟨x * y * x⁻¹, M.mul_mem (M.mul_mem (h.le_M hxR) (hYM hy)) (M.inv_mem (h.le_M hxR)), ?_⟩
    rw [map_mul, map_mul, map_inv, hyd]
    group
  have hD : h.D ≤ M.map h.rho := by
    intro g hg
    have := cubeBase_le_iSup_cubeAt hF Finset.univ g hg
      (fun k hk => absurd (Finset.mem_univ k) hk)
    exact (iSup₂_le fun j _ => hDj j : (⨆ j ∈ (Finset.univ : Finset (Fin r)), h.Dat j) ≤
      M.map h.rho) this
  have htop : (⊤ : Subgroup H) ≤ M := by
    intro x _
    obtain ⟨n, hn, r', hr, rfl⟩ := h.exists_mul_odd_R x
    have hn' : h.rho n ∈ M.map h.rho := hD (h.rho_map_odd ▸ ⟨n, hn, rfl⟩)
    obtain ⟨m, hm, hmn⟩ := hn'
    have hnm : m⁻¹ * n ∈ h.rho.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmn]
      group
    have hn_M : n ∈ M := by
      have : n = m * (m⁻¹ * n) := by group
      rw [this]
      exact M.mul_mem hm (hker hnm)
    exact M.mul_mem hn_M (h.le_M hr)
  exact absurd h.M_lt (not_lt_of_ge htop)

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
