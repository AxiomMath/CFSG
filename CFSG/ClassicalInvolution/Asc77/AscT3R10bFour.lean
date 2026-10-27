module

public import CFSG.ClassicalInvolution.Asc77.AscT3R10bTX
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bQ8
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10B

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Cyclic

variable {G : Type} [Group G]

theorem exists_gen_of_cyclic_card_four {V : Subgroup G} (hc : IsCyclic ↥V)
    (h4 : Nat.card V = 4) :
    ∃ v : G, v ∈ V ∧ v ^ 4 = 1 ∧ v * v ≠ 1 ∧ ∀ w ∈ V, ∃ k : ℤ, w = v ^ k := by
  obtain ⟨g, hg⟩ := hc
  have hord : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  refine ⟨(g : G), g.2, ?_, ?_, ?_⟩
  · have : g ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
    have h := congrArg Subtype.val this
    simpa using h
  · intro h
    have : g ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h)
    have := orderOf_dvd_of_pow_eq_one this
    rw [hord] at this
    omega
  · intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this.symm

theorem sq_eq_of_involution {v t : G} (hv4 : v ^ 4 = 1) (hv2 : v * v ≠ 1)
    (ht : ∃ k : ℤ, t = v ^ k) (ht2 : t * t = 1) (ht1 : t ≠ 1) : v * v = t := by
  obtain ⟨k, rfl⟩ := ht
  have hk : v ^ k = v ^ (k % 4) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 4]
    rw [zpow_add, zpow_mul, show v ^ (4 : ℤ) = 1 by exact_mod_cast hv4, one_zpow, mul_one]
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rw [hk] at ht2 ht1 ⊢
  have hv6 : v ^ 3 * v ^ 3 = v * v := by
    rw [← pow_add, show 3 + 3 = 4 + 2 by norm_num, pow_add, hv4, one_mul, pow_two]
  rcases h4 with h | h | h | h <;> rw [h] at ht2 ht1 ⊢
  · exact absurd (by simp) ht1
  · exact absurd (by simpa using ht2) hv2
  · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
  · exfalso
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at ht2
    rw [hv6] at ht2
    exact hv2 ht2

end Cyclic

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r10b_four (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) (h8 : Nat.card R = 8) {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsX : s ∈ sec20X (CoreAssembly.conjClass K) z K K') (hs2 : s * s ≠ 1)
    (hs4 : (s * s) * (s * s) = 1) : s * s = z ∨ s ∈ W := by
  have hTX := d.r10b_TX c8 h8
  obtain ⟨b, hbS, hbK, hb2⟩ := d.late_exists_b h8 c3 hTX
  have hz2 := d.viol.hzK.sq
  have hz1 := d.viol.hzK.ne_one
  have ht2 := d.viol.hzJ.sq
  have ht1 := d.viol.hzJ.ne_one
  have hbz : b * z * b⁻¹ = z := d.late_S_act_z hbS
  obtain ⟨u, r, v₀, t₀, T, hh⟩ := d.late_exists_hex
  have hd := hh.hd
  have hu4 : orderOf u = 4 := by
    have := hd.card
    omega
  have huu : u * u = z := by
    have h := hd.z_eq
    rw [hu4] at h
    simpa [pow_two] using h
  have DR : Q8Dat R z u r :=
    { hu := hd.U_le_R (Subgroup.mem_zpowers u)
      hr := hd.r_mem
      hu2 := huu
      hr2 := hd.sq_r
      hru := hd.conj_u
      hrn := hd.r_not_mem
      hcover := hd.cover }
  have huW : u ∈ W := hd.u_memW
  have hRR'mem : ∀ x : G, x ∈ R' ↔ b⁻¹ * x * b ∈ R := by
    intro x
    rw [d.late_R'_eq, d.late_R_eq, Subgroup.mem_inf, Subgroup.mem_inf, ← hbK, mem_conjSub_iff]
    have : x ∈ (S : Subgroup G) ↔ b⁻¹ * x * b ∈ (S : Subgroup G) := by
      constructor
      · intro hx
        exact S.mul_mem (S.mul_mem (S.inv_mem hbS) hx) hbS
      · intro hx
        have := S.mul_mem (S.mul_mem hbS hx) (S.inv_mem hbS)
        simpa [mul_assoc] using this
    rw [this]
  have hu₀R' : b * u * b⁻¹ ∈ R' := (hRR'mem _).mpr (by
    have : b⁻¹ * (b * u * b⁻¹) * b = u := by group
    rw [this]
    exact DR.hu)
  have hr₀R' : b * r * b⁻¹ ∈ R' := (hRR'mem _).mpr (by
    have : b⁻¹ * (b * r * b⁻¹) * b = r := by group
    rw [this]
    exact DR.hr)
  have DR₀ : Q8Dat R' z (b * u * b⁻¹) (b * r * b⁻¹) :=
    { hu := hu₀R'
      hr := hr₀R'
      hu2 := by
        calc b * u * b⁻¹ * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
          _ = z := by rw [huu]; exact hbz
      hr2 := by
        calc b * r * b⁻¹ * (b * r * b⁻¹) = b * (r * r) * b⁻¹ := by group
          _ = z := by rw [DR.hr2]; exact hbz
      hru := by
        calc b * r * b⁻¹ * (b * u * b⁻¹) * (b * r * b⁻¹)⁻¹
            = b * (r * u * r⁻¹) * b⁻¹ := by group
          _ = b * u⁻¹ * b⁻¹ := by rw [DR.hru]
          _ = (b * u * b⁻¹)⁻¹ := by group
      hrn := by
        intro h
        apply DR.hrn
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
        rw [conj_zpow] at hj
        have hj' : u ^ j = r := by
          have := congrArg (fun y => b⁻¹ * y * b) hj
          simpa [mul_assoc] using this
        rw [← hj']
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) j
      hcover := by
        intro x hx
        have hx' : b⁻¹ * x * b ∈ R := (hRR'mem x).mp hx
        have hxe : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
        rcases DR.hcover _ hx' with h | ⟨y, hy, h⟩
        · left
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
          refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
          rw [conj_zpow, hj]
          rw [hxe]
          rw [← hj]
          group
        · right
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
          refine ⟨(b * u * b⁻¹) ^ j, Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩, ?_⟩
          rw [conj_zpow, hj, hxe, h]
          group }
  have hbbW : b * b ∈ W := by
    rcases hb2 with h | h
    · rw [h]
      exact d.late_t_mem_W
    · rw [h]
      exact W.mul_mem d.late_z_mem_W d.late_t_mem_W
  obtain ⟨hut', hbt⟩ := d.late_swap_sq_data hbS hbK hbbW hd.u_mem huu
  have hzu : z * u = u * z := by rw [← huu]; group
  have hu₀W : b * u * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hbS) u).mp huW
  obtain ⟨u₂, DR', hut, hu₂W⟩ : ∃ u₂ : G, Q8Dat R' z u₂ (b * r * b⁻¹) ∧ u * u₂ = t ∧ u₂ ∈ W := by
    rcases hut' with h | h
    · exact ⟨_, DR₀, h, hu₀W⟩
    · refine ⟨(b * u * b⁻¹)⁻¹, DR₀.inv hz2, ?_, W.inv_mem hu₀W⟩
      have h1 : (b * u * b⁻¹)⁻¹ = z * (b * u * b⁻¹) := by
        apply inv_eq_of_mul_eq_one_right
        calc b * u * b⁻¹ * (z * (b * u * b⁻¹))
            = (b * u * b⁻¹) * ((b * u * b⁻¹) * (b * u * b⁻¹)) * (b * u * b⁻¹) := by
              rw [DR₀.hu2]
              group
          _ = ((b * u * b⁻¹) * (b * u * b⁻¹)) * ((b * u * b⁻¹) * (b * u * b⁻¹)) := by group
          _ = 1 := by rw [DR₀.hu2, hz2]
      rw [h1]
      calc u * (z * (b * u * b⁻¹)) = (u * z) * (b * u * b⁻¹) := by group
        _ = (z * u) * (b * u * b⁻¹) := by rw [hzu]
        _ = z * (u * (b * u * b⁻¹)) := by group
        _ = z * (z * t) := by rw [h]
        _ = t := by rw [← mul_assoc, hz2, one_mul]
  have hVcyc : IsCyclic ↥V := by
    obtain ⟨R₀, -, -, hc, -⟩ := d.hV
    exact hc
  have hV4 : Nat.card V = 4 := by
    have := Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp d.hV d.late_mem_K d.hR
    omega
  obtain ⟨v, hvV, hv4, hv2, hvgen⟩ := exists_gen_of_cyclic_card_four hVcyc hV4
  have hvt : v * v = t := sq_eq_of_involution hv4 hv2 (hvgen t d.htV) ht2 ht1
  have hvW : v ∈ W := d.hVW hvV
  have hvS : v ∈ (S : Subgroup G) := d.hVS hvV
  have hWc := d.late_hWc
  have hvu : v * u = u * v := hWc v hvW u huW
  have hvu₂ : v * u₂ = u₂ * v := hWc v hvW u₂ hu₂W
  have hvR : ∀ x ∈ R, v * x * v⁻¹ ∈ R := by
    intro x hx
    rw [d.late_R_eq] at hx ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (d.late_W_le_N_K hvW) x).mp hx.1,
      S.mul_mem (S.mul_mem hvS hx.2) (S.inv_mem hvS)⟩
  have hvR' : ∀ x ∈ R', v * x * v⁻¹ ∈ R' := by
    intro x hx
    rw [d.late_R'_eq] at hx ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (d.late_W_le_N_K' hvW) x).mp hx.1,
      S.mul_mem (S.mul_mem hvS hx.2) (S.inv_mem hvS)⟩
  have hbt' : b⁻¹ * t * b = t := by
    calc b⁻¹ * t * b = b⁻¹ * (b * t * b⁻¹) * b := by rw [hbt]
      _ = t := by group
  have hrt₂ : b * r * b⁻¹ * t * (b * r * b⁻¹)⁻¹ = t * z := by
    calc b * r * b⁻¹ * t * (b * r * b⁻¹)⁻¹ = b * (r * (b⁻¹ * t * b) * r⁻¹) * b⁻¹ := by group
      _ = b * (r * t * r⁻¹) * b⁻¹ := by rw [hbt']
      _ = b * (t * z) * b⁻¹ := by rw [hh.hrt]
      _ = (b * t * b⁻¹) * (b * z * b⁻¹) := by group
      _ = t * z := by rw [hbt, hbz]
  have hsRV : s ∈ R ⊔ R' ⊔ V := by
    rw [← d.late_SX c3]
    exact ⟨hsS, hsX⟩
  obtain ⟨q, hq, w, hw, rfl⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer d.late_V_le_N_RR' hsRV
  obtain ⟨x, hx, x', hx', rfl⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer d.late_R'_le_N_R hq
  obtain ⟨k, rfl⟩ := hvgen w hw
  exact order_four_abstract hz2 hz1 ht2 DR DR' (fun x hx y hy => d.late_R_R'_comm hx hy) hvR
    hvR' hvu hvu₂ hvt hut hh.hrt hrt₂ huW hu₂W hvW ⟨x, hx, x', hx', k, rfl⟩ hs2 hs4

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
