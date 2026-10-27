module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9A

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Pure

variable {Q : Type*} [Group Q]

theorem late_swap_sq {a b c : Q} (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b)
    (hne : b ≠ c) (hab : a * b * a⁻¹ = c) (hac : a * c * a⁻¹ = b)
    (h : a * a = 1 ∨ a * a = b ∨ a * a = c ∨ a * a = b * c) :
    a * a = 1 ∨ (a * b) * (a * b) = 1 := by
  have hfix : a * (a * a) * a⁻¹ = a * a := by group
  rcases h with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, hab] at hfix
    exact hne hfix.symm
  · exfalso
    rw [h, hac] at hfix
    exact hne hfix
  · right
    calc (a * b) * (a * b) = (a * b * a⁻¹) * (a * a) * b := by group
      _ = c * (b * c) * b := by rw [hab, h]
      _ = c * (c * b) * b := by rw [hbc]
      _ = (c * c) * (b * b) := by group
      _ = 1 := by rw [hb, hc, one_mul]

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20.late_R_R'_comm (d : Std20 p f K K' J S R R' W V z t) {a b : G} (ha : a ∈ R)
    (hb : b ∈ R') : a * b = b * a := by
  have haK : a ∈ K := d.hR.1 ha
  have hbK' : b ∈ K' := d.hR'.1 hb
  have hc := (Sec6Gen.comm_le_oddCore_of_twin d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm
    d.viol.hzK d.late_hzK' (Subgroup.commutator_mem_commutator haK hbK')).1
  have hcS : ⁅a, b⁆ ∈ (S : Subgroup G) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (d.hRS ha) (d.hR'S hb))
      (Subgroup.inv_mem _ (d.hRS ha))) (Subgroup.inv_mem _ (d.hR'S hb))
  have h1 : ⁅a, b⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hc
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS))
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

omit [Finite G] in
theorem late_dData_cover {Ω : Set (Subgroup G)} {W R K : Subgroup G} {x r z g : G}
    (hd : Sec71.DData Ω W R K x r z) (hg : g ∈ R) (hgW : g ∉ W) : ∃ y ∈ W, g = y * r := by
  rcases hd.cover g hg with h | ⟨y, hy, rfl⟩
  · exact absurd (Subgroup.zpowers_le.mpr hd.u_memW h) hgW
  · exact ⟨y, Subgroup.zpowers_le.mpr hd.u_memW hy, rfl⟩

theorem Std20.late_R'_le_N_R (d : Std20 p f K K' J S R R' W V z t) :
    R' ≤ Subgroup.normalizer (R : Set G) := fun _ hb =>
  Subgroup.centralizer_le_normalizer (R : Set G)
    (Subgroup.mem_centralizer_iff.mpr fun _ ha => d.late_R_R'_comm ha hb)

theorem Std20.late_exists_sq_W (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    {u : G} (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K')
    (hX : u * u ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∃ σ ∈ (S : Subgroup G), conjSub σ K = K' ∧ σ * σ ∈ W := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨x, r₀, hd⟩ := late_exists_dData hp hq d.hyp d.hW d.late_R_mem_D d.late_mem_K d.hR
    d.viol.hzK
  obtain ⟨x', r₀', hd'⟩ := late_exists_dData hp hq d.hyp d.hW d.late_R'_mem_D d.late_mem_K'
    d.hR' d.late_hzK'
  obtain ⟨hK'u, hRu, -, hSu⟩ := d.late_swap_data hu huK
  have hRu' : conjSub u R' = R := by
    rw [d.late_R'_eq, late_conjSub_inf, hK'u, hSu, ← d.late_R_eq]
  have hzW := d.late_z_mem_W
  have hconjW : ∀ g ∈ (S : Subgroup G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hg) w).mp hw
  have hconjW' : ∀ g ∈ (S : Subgroup G), ∀ w ∈ W, g⁻¹ * w * g ∈ W := fun g hg w hw => by
    simpa using hconjW g⁻¹ (Subgroup.inv_mem _ hg) w hw
  have hr₀S : r₀ ∈ (S : Subgroup G) := d.hRS hd.r_mem
  have hr₀'S : r₀' ∈ (S : Subgroup G) := d.hR'S hd'.r_mem
  have hr₀W : r₀ ∉ W := fun h => hd.r_not_mem (by rw [← hd.inf_eq]; exact ⟨hd.r_memK, h⟩)
  have hr₀'W : r₀' ∉ W := fun h => hd'.r_not_mem (by rw [← hd'.inf_eq]; exact ⟨hd'.r_memK, h⟩)
  set Sg : Subgroup G := (S : Subgroup G) with hSg
  have hnorm : (W.subgroupOf Sg).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconjW (g : G) g.2 (n : G) hn
  let π : ↥Sg →* ↥Sg ⧸ W.subgroupOf Sg := QuotientGroup.mk' _
  have hπ : ∀ g h : ↥Sg, (g : G)⁻¹ * (h : G) ∈ W → π g = π h := by
    intro g h hgh
    show (QuotientGroup.mk g : ↥Sg ⧸ W.subgroupOf Sg) = QuotientGroup.mk h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hgh
  have hπ' : ∀ g h : ↥Sg, π g = π h → (g : G)⁻¹ * (h : G) ∈ W := by
    intro g h hgh
    have : (QuotientGroup.mk g : ↥Sg ⧸ W.subgroupOf Sg) = QuotientGroup.mk h := hgh
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hπ1 : ∀ g : ↥Sg, (g : G) ∈ W → π g = 1 := by
    intro g hg
    rw [← map_one π]
    exact hπ g 1 (by simpa using W.inv_mem hg)
  let σ₁ : ↥Sg := ⟨u, hu⟩
  let b₁ : ↥Sg := ⟨r₀, hr₀S⟩
  let c₁ : ↥Sg := ⟨r₀', hr₀'S⟩
  have hb2 : π b₁ * π b₁ = 1 := by
    rw [← map_mul]
    exact hπ1 _ (by show r₀ * r₀ ∈ W; rw [hd.sq_r]; exact hzW)
  have hc2 : π c₁ * π c₁ = 1 := by
    rw [← map_mul]
    exact hπ1 _ (by show r₀' * r₀' ∈ W; rw [hd'.sq_r]; exact hzW)
  have hbc : π b₁ * π c₁ = π c₁ * π b₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.late_R_R'_comm hd.r_mem hd'.r_mem)
  have hne : π b₁ ≠ π c₁ := by
    intro h
    have hw : r₀⁻¹ * r₀' ∈ W := hπ' b₁ c₁ h
    have hxR : x ∈ R := hd.U_le_R (Subgroup.mem_zpowers x)
    have hxW : x ∈ W := hd.u_memW
    have hc : x * r₀' = r₀' * x := d.late_R_R'_comm hxR hd'.r_mem
    have h1 : r₀' * x * r₀'⁻¹ = x := by
      rw [← hc]; group
    have h2 : (r₀⁻¹ * r₀') * x = x * (r₀⁻¹ * r₀') := d.late_hWc _ hw x hxW
    have h3 : r₀' * x * r₀'⁻¹ = x⁻¹ := by
      calc r₀' * x * r₀'⁻¹ = r₀ * ((r₀⁻¹ * r₀') * x * (r₀⁻¹ * r₀')⁻¹) * r₀⁻¹ := by group
        _ = r₀ * x * r₀⁻¹ := by rw [h2]; group
        _ = x⁻¹ := hd.conj_u
    have h4 : x * x = 1 := by
      have : x = x⁻¹ := h1.symm.trans h3
      calc x * x = x * x⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel x
    have h5 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h4)
    have h6 := Nat.le_of_dvd (by norm_num) h5
    have := hd.four_le
    omega
  have hab : π σ₁ * π b₁ * (π σ₁)⁻¹ = π c₁ := by
    have hmem : u * r₀ * u⁻¹ ∈ R' := hRu ▸ conj_mem_conjSub hd.r_mem
    have hnot : u * r₀ * u⁻¹ ∉ W := fun h => hr₀W (by
      have := hconjW' u hu _ h
      rwa [show u⁻¹ * (u * r₀ * u⁻¹) * u = r₀ by group] at this)
    obtain ⟨y, hy, hyeq⟩ := late_dData_cover hd' hmem hnot
    rw [← map_inv, ← map_mul, ← map_mul]
    refine hπ _ _ ?_
    show (u * r₀ * u⁻¹)⁻¹ * r₀' ∈ W
    rw [hyeq]
    simpa [mul_assoc] using hconjW' r₀' hr₀'S y⁻¹ (W.inv_mem hy)
  have hac : π σ₁ * π c₁ * (π σ₁)⁻¹ = π b₁ := by
    have hmem : u * r₀' * u⁻¹ ∈ R := hRu' ▸ conj_mem_conjSub hd'.r_mem
    have hnot : u * r₀' * u⁻¹ ∉ W := fun h => hr₀'W (by
      have := hconjW' u hu _ h
      rwa [show u⁻¹ * (u * r₀' * u⁻¹) * u = r₀' by group] at this)
    obtain ⟨y, hy, hyeq⟩ := late_dData_cover hd hmem hnot
    rw [← map_inv, ← map_mul, ← map_mul]
    refine hπ _ _ ?_
    show (u * r₀' * u⁻¹)⁻¹ * r₀ ∈ W
    rw [hyeq]
    simpa [mul_assoc] using hconjW' r₀ hr₀S y⁻¹ (W.inv_mem hy)
  have hs : u * u ∈ R ⊔ R' ⊔ V := by
    rw [← d.late_SX c3]
    exact ⟨Subgroup.mul_mem _ hu hu, hX⟩
  obtain ⟨m, hm, v, hv, hsmv⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer
    d.late_V_le_N_RR' hs
  obtain ⟨ρ, hρ, ρ', hρ', hmρ⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer
    d.late_R'_le_N_R hm
  have hρS : ρ ∈ (S : Subgroup G) := d.hRS hρ
  have hρ'S : ρ' ∈ (S : Subgroup G) := d.hR'S hρ'
  have hvW : v ∈ W := d.hVW hv
  have hcls : π ⟨u * u, Subgroup.mul_mem _ hu hu⟩ = π ⟨ρ, hρS⟩ * π ⟨ρ', hρ'S⟩ := by
    rw [← map_mul]
    refine hπ _ _ ?_
    show (u * u)⁻¹ * (ρ * ρ') ∈ W
    rw [hsmv, hmρ]
    simpa [mul_assoc] using W.inv_mem hvW
  have hρcls : π ⟨ρ, hρS⟩ = 1 ∨ π ⟨ρ, hρS⟩ = π b₁ := by
    by_cases hρW : ρ ∈ W
    · exact Or.inl (hπ1 _ hρW)
    · obtain ⟨y, hy, hyeq⟩ := late_dData_cover hd hρ hρW
      refine Or.inr (hπ _ _ ?_)
      show ρ⁻¹ * r₀ ∈ W
      rw [hyeq]
      simpa [mul_assoc] using hconjW' r₀ hr₀S y⁻¹ (W.inv_mem hy)
  have hρ'cls : π ⟨ρ', hρ'S⟩ = 1 ∨ π ⟨ρ', hρ'S⟩ = π c₁ := by
    by_cases hρW : ρ' ∈ W
    · exact Or.inl (hπ1 _ hρW)
    · obtain ⟨y, hy, hyeq⟩ := late_dData_cover hd' hρ' hρW
      refine Or.inr (hπ _ _ ?_)
      show ρ'⁻¹ * r₀' ∈ W
      rw [hyeq]
      simpa [mul_assoc] using hconjW' r₀' hr₀'S y⁻¹ (W.inv_mem hy)
  have hsq : π σ₁ * π σ₁ = 1 ∨ π σ₁ * π σ₁ = π b₁ ∨ π σ₁ * π σ₁ = π c₁ ∨
      π σ₁ * π σ₁ = π b₁ * π c₁ := by
    have h1 : π σ₁ * π σ₁ = π ⟨ρ, hρS⟩ * π ⟨ρ', hρ'S⟩ := by
      rw [← map_mul]
      exact hcls
    rw [h1]
    rcases hρcls with h | h <;> rcases hρ'cls with h' | h' <;> rw [h, h'] <;> simp
  rcases late_swap_sq hb2 hc2 hbc hne hab hac hsq with h | h
  · refine ⟨u, hu, huK, ?_⟩
    rw [← map_mul] at h
    have h2 : (u * u)⁻¹ * 1 ∈ W := hπ' (σ₁ * σ₁) 1 (h.trans (map_one π).symm)
    rw [mul_one] at h2
    exact W.inv_mem_iff.mp h2
  · refine ⟨u * r₀, Subgroup.mul_mem _ hu hr₀S, ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_self_of_mem hd.r_memK, huK]
    · rw [← map_mul, ← map_mul] at h
      have h2 : ((u * r₀) * (u * r₀))⁻¹ * 1 ∈ W :=
        hπ' ((σ₁ * b₁) * (σ₁ * b₁)) 1 (h.trans (map_one π).symm)
      rw [mul_one] at h2
      exact W.inv_mem_iff.mp h2

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
