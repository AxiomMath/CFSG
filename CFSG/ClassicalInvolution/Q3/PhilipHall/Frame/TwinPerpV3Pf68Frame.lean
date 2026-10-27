module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Asc77.C22G

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_rep_in_T {W : Subgroup G} (c : Q3CL.Thompson.Ctx Ω W) (hcl : Q3CL.ClassicalClause Ω)
    {t : G} {T : Subgroup G} (hT : IsSylow2In T (Subgroup.centralizer ({t} : Set G)))
    (hWT : W ≤ T) {J : Subgroup G} (hJ : J ∈ Ω) (ht : IsUniqueInvolution J t) :
    ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T ⊓ J := by
  have hR : IsSylow2In (T ⊓ J) J :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hcl.isSubnormal_of_uniqueInvolution hJ ht)
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hRD : T ⊓ J ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW (hWT.trans hTS) (mem_RSet_of_isSylow2In hJ hR)
      (inf_le_left.trans hTS)
  obtain ⟨r₀, hr₀, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D c.hΩ c.hW hRD
  exact ⟨⟨J, T ⊓ J, r₀, hJ, hRD, hR, hr₀, hr₀W⟩, rfl, rfl⟩

theorem exists_fuse_cent2W (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) {K₄ : Subgroup G} (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) {W : Subgroup G} (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ a₁ a₂ a₃ a₄ y : G, a₁ ∈ K ∧ orderOf a₁ = 4 ∧ a₂ ∈ K' ∧ orderOf a₂ = 4 ∧
      a₃ ∈ K₃ ∧ orderOf a₃ = 4 ∧ a₄ ∈ K₄ ∧ orderOf a₄ = 4 ∧
      a₁ * a₂ = a₂ * a₁ ∧ a₁ * a₃ = a₃ * a₁ ∧ a₁ * a₄ = a₄ * a₁ ∧ a₂ * a₃ = a₃ * a₂ ∧
      a₂ * a₄ = a₄ * a₂ ∧ a₃ * a₄ = a₄ * a₃ ∧ y * z * y⁻¹ = a₁ * a₂ * a₃ * a₄ ∧
      y * z * y⁻¹ ≠ z ∧ a₁ ∈ W ∧ a₂ ∈ W ∧ a₃ ∈ W ∧ a₄ ∈ W ∧ y ∈ Subgroup.centralizer ({a₁ * a₂} : Set G) ∧
      ∃ j : G, j * a₁ * j⁻¹ = a₁⁻¹ ∧ j * a₂ * j⁻¹ = a₂ ∧ j * a₃ * j⁻¹ = a₃ ∧ j * a₄ * j⁻¹ = a₄ := by
  classical
  have hΩ := hd.hyp
  have hK := hd.mem
  have hK' : K' ∈ Ω := hd.hK'.1
  have hK₃ : K₃ ∈ Ω := hd.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hd.hz
  have hz' : IsUniqueInvolution K' z := hd.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hd.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have c0 : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c0.comm_W w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  obtain ⟨ρ₀, hρ₀K, hρ₀R'⟩ := exists_rep_in_T c0 hP.cls hT hWT hK hz
  obtain ⟨ρ₁, hρ₁K, hρ₁R'⟩ := exists_rep_in_T c0 hP.cls hT hWT hK' hz'
  obtain ⟨ρ₂, hρ₂K, hρ₂R'⟩ := exists_rep_in_T c0 hP.cls hT hWT hK₃ hz₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R'⟩ := exists_rep_in_T c0 hP.cls hT hWT hK₄Ω hz₄
  obtain ⟨R₁, hρ₀R⟩ : ∃ R₁, ρ₀.R = R₁ := ⟨_, rfl⟩
  obtain ⟨R₂, hρ₁R⟩ : ∃ R₂, ρ₁.R = R₂ := ⟨_, rfl⟩
  obtain ⟨R₃, hρ₂R⟩ : ∃ R₃, ρ₂.R = R₃ := ⟨_, rfl⟩
  obtain ⟨R₄, hρ₃R⟩ : ∃ R₄, ρ₃.R = R₄ := ⟨_, rfl⟩
  have hR₁T : R₁ ≤ T ⊓ K := by rw [← hρ₀R, hρ₀R']
  have hR₂T : R₂ ≤ T ⊓ K' := by rw [← hρ₁R, hρ₁R']
  have hR₃T : R₃ ≤ T ⊓ K₃ := by rw [← hρ₂R, hρ₂R']
  have c13 : Commutes R₁ R₃ := Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK₃ hd.hK₃K.symm hz hz₃
    (hR₁T.trans inf_le_right) (hR₃T.trans inf_le_right)
    (hT.2.1.to_le (sup_le (hR₁T.trans inf_le_left) (hR₃T.trans inf_le_left)))
  have c23 : Commutes R₂ R₃ := Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK' hK₃ hd.hK₃K'.symm hz' hz₃
    (hR₂T.trans inf_le_right) (hR₃T.trans inf_le_right)
    (hT.2.1.to_le (sup_le (hR₂T.trans inf_le_left) (hR₃T.trans inf_le_left)))
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hd.hK'
    · exact hd.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hd.hne.symm
  have hKK₃ : K ≠ K₃ := hd.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hd.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact adj_of_twins' hd hperp (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hRσ⟩ := c.fuse_frame hP.cls hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid hP.cls (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have hj : ∃ j : G, j * g 0 * j⁻¹ = (g 0)⁻¹ ∧ j * g 1 * j⁻¹ = g 1 ∧ j * g 2 * j⁻¹ = g 2 ∧
      j * g 3 * j⁻¹ = g 3 := by
    refine ⟨(ρ 0).r, c.conj_inv (ρ 0) (hg 0).1, ?_, ?_, ?_⟩
    · rw [c.centralizes (ρ 0) (ρ 1) (hnbrρ 0 1 (by decide)) (hg 1).1, mul_inv_cancel_right]
    · rw [c.centralizes (ρ 0) (ρ 2) (hnbrρ 0 2 (by decide)) (hg 2).1, mul_inv_cancel_right]
    · rw [c.centralizes (ρ 0) (ρ 3) (hnbrρ 0 3 (by decide)) (hg 3).1, mul_inv_cancel_right]
  refine ⟨g 0, g 1, g 2, g 3, y, by simpa [hρ0K] using (hg 0).1.1, (hg 0).2,
    by simpa [hρ1K] using (hg 1).1.1, (hg 1).2, by simpa [hρ2K] using (hg 2).1.1, (hg 2).2,
    by simpa [hρ3K] using (hg 3).1.1, (hg 3).2, hcomm _ (hgW 0) _ (hgW 1),
    hcomm _ (hgW 0) _ (hgW 2), hcomm _ (hgW 0) _ (hgW 3), hcomm _ (hgW 1) _ (hgW 2),
    hcomm _ (hgW 1) _ (hgW 3), hcomm _ (hgW 2) _ (hgW 3), hyz.trans hrel, ?_, hgW 0, hgW 1, hgW 2, hgW 3, ?_, hj⟩
  swap
  ·
    have hr₂ : (ρ 2).r ∈ R₃ := hρ₂R ▸ (ρ 2).hr
    have hg0 : g 0 ∈ R₁ := hρ₀R ▸ hgR 0
    have hg1 : g 1 ∈ R₂ := hρ₁R ▸ hgR 1
    have hr2c : (ρ 2).r ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e0 : g 0 * (ρ 2).r = (ρ 2).r * g 0 := c13 _ hg0 _ hr₂
      have e1 : g 1 * (ρ 2).r = (ρ 2).r * g 1 := c23 _ hg1 _ hr₂
      calc (ρ 2).r * (g 0 * g 1) = ((ρ 2).r * g 0) * g 1 := by group
        _ = (g 0 * (ρ 2).r) * g 1 := by rw [e0]
        _ = g 0 * ((ρ 2).r * g 1) := by group
        _ = g 0 * (g 1 * (ρ 2).r) := by rw [e1]
        _ = (g 0 * g 1) * (ρ 2).r := by group
    have hσc : σ.r ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := hRσ σ.hr
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr2c hσc) (Subgroup.inv_mem _ hr2c)
  rw [hyz]
  intro h'
  have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
  have hperp' : σ.K ∈ KPerp Ω K := by rw [hperp]; exact hσK
  rcases hperp' with h'' | h''
  · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
  · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm

end Fam

section Bounds

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_or_inv_of_mem_USet (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∀ R, IsSylow2In R L → Nonempty (↥R ≃* QuaternionGroup 2)) {U : Subgroup G}
    (hU : U ∈ USet Ω) {x y : G} (hx : x ∈ U) (hy : y ∈ U) (ox : orderOf x = 4)
    (oy : orderOf y = 4) : x = y ∨ x = y⁻¹ := by
  obtain ⟨R, -, J, hJ, hRJ, -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨e⟩ := hq8 J hJ R hRJ
  have h8 : Nat.card R = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hU4 : Nat.card U = 4 := by omega
  have hz : Subgroup.zpowers y = U :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) (by rw [Nat.card_zpowers, oy, hU4])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hz ▸ hx : x ∈ Subgroup.zpowers y)
  have hy4 : y ^ 4 = 1 := by rw [← oy]; exact pow_orderOf_eq_one y
  have hmod : y ^ (k % 4) = y ^ k := by
    have := zpow_mod_orderOf y k
    rw [oy] at this
    simpa using this
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] at hmod
  · exfalso
    have hx1 : x = 1 := by rw [← hk, ← hmod]; simp
    rw [hx1, orderOf_one] at ox
    omega
  · left
    rw [← hk, ← hmod]; simp
  · exfalso
    have hxe : x = y * y := by rw [← hk, ← hmod]; exact zpow_two y
    have hx2 : x ^ 2 = 1 := by
      rw [hxe]
      calc (y * y) ^ 2 = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hy4
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [ox] at this
    omega
  · right
    have hxe : x = y ^ 3 := by rw [← hk, ← hmod]; exact zpow_ofNat y 3
    rw [hxe]
    apply eq_inv_of_mul_eq_one_left
    calc y ^ 3 * y = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hy4

theorem layer_cent_transfer (hΩ : ConjInvariant Ω) {N : Subgroup G} {a u j : G} (hj : j ∈ N)
    (hu : j * a * j⁻¹ = u) (hL : rLayer Ω a ≤ N)
    (hC : Subgroup.centralizer ({a} : Set G) ≤ N) :
    rLayer Ω u ≤ N ∧ Subgroup.centralizer ({u} : Set G) ≤ N := by
  refine ⟨?_, ?_⟩
  · refine rLayer_le_of_conj hΩ (N.inv_mem hj) ?_ hL
    rw [← hu]; group
  · intro x hx
    have hx' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have h1 : (j⁻¹ * x * j) ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : (j⁻¹ * x * j) * a = a * (j⁻¹ * x * j) := by
        have e1 : a = j⁻¹ * u * j := by rw [← hu]; group
        rw [e1]
        calc j⁻¹ * x * j * (j⁻¹ * u * j) = j⁻¹ * (x * u) * j := by group
          _ = j⁻¹ * (u * x) * j := by rw [hx']
          _ = j⁻¹ * u * j * (j⁻¹ * x * j) := by group
      exact this
    have h2 := hC h1
    have : x = j * (j⁻¹ * x * j) * j⁻¹ := by group
    rw [this]
    exact N.mul_mem (N.mul_mem hj h2) (N.inv_mem hj)

variable {n : ℕ}

end Bounds

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
