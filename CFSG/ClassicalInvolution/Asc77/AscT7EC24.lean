module

public import CFSG.ClassicalInvolution.Asc77.AscT7EInv
public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_frame4_of_sylow [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) {R R' : Subgroup G}
    (hRsyl : IsSylow2In R K) (hR'syl : IsSylow2In R' K') (hRD : R ∈ DSet Ω W)
    (hR'D : R' ∈ DSet Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.ρ.R = R ∧
      F.ρ'.R = R' ∧ F.z = z ∧ T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hS4
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hp hq hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, hρR, hρ'R, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)

theorem conjSub_rep_eq_of_mem_W (c : Thompson.Ctx p f Ω W) (ρ : Thompson.Rep Ω W) {w : G}
    (hw : w ∈ W) : conjSub w ρ.K = ρ.K := by
  have hn : w ∈ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer hw
  refine (T7D.conj_stable c hn ρ ?_).1
  rw [Thompson.piG_of_mem_sup (Subgroup.mem_sup_left hw), one_mul, inv_one, mul_one]

theorem mem_normalizer_conj_of_mem_W [IsSimpleGroup G] {K K' : Subgroup G} {z u g g₀ : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W)
    (hg₀ : g₀ ∈ Subgroup.normalizer (W : Set G)) (hg₀u : g₀⁻¹ * z * g₀ = u)
    (hgu : g⁻¹ * z * g = u) {w : G} (hw : w ∈ W) :
    w ∈ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) := by
  have hst : AscStand p f Ω K := hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨S, ρ, ρ', -, hρK, hρ'K, -⟩ := exists_twin_reps hs hW hzW
  have hn : g₀⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg₀
  have hJ' : conjSub (g₀ * g⁻¹) K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant _ K hst.mem, z, hs.hz, ?_⟩
    have h1 := hs.hz.conj (g₀ * g⁻¹)
    have h2 : (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = z := by
      calc (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = g₀ * (g⁻¹ * z * g) * g₀⁻¹ := by group
        _ = g₀ * u * g₀⁻¹ := by rw [hgu]
        _ = z := by rw [← hg₀u]; group
    rwa [h2] at h1
  rw [hs.twinSet_eq] at hJ'
  have hKg : conjSub g⁻¹ K = conjSub g₀⁻¹ (conjSub (g₀ * g⁻¹) K) := by
    rw [← conjSub_mul, inv_mul_cancel_left]
  rw [mem_normalizer_iff_conjSub_eq, hKg]
  rcases hJ' with h | h
  · rw [h, ← hρK]
    exact conjSub_rep_eq_of_mem_W c (T7D.conjRep c.hΩ hn ρ) hw
  · rw [h, ← hρ'K]
    exact conjSub_rep_eq_of_mem_W c (T7D.conjRep c.hΩ hn ρ') hw

omit [Finite G] in
theorem nf_mul {x₁ x₂ x₃ : G} (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃)
    (c23 : Commute x₂ x₃) (i j k i' j' k' : ℤ) :
    (x₁ ^ i * x₂ ^ j * x₃ ^ k) * (x₁ ^ i' * x₂ ^ j' * x₃ ^ k') =
      x₁ ^ (i + i') * x₂ ^ (j + j') * x₃ ^ (k + k') := by
  have hc12 : ∀ a b : ℤ, x₁ ^ a * x₂ ^ b = x₂ ^ b * x₁ ^ a := fun a b => (c12.zpow_zpow a b).eq
  have hc13 : ∀ a b : ℤ, x₁ ^ a * x₃ ^ b = x₃ ^ b * x₁ ^ a := fun a b => (c13.zpow_zpow a b).eq
  have hc23 : ∀ a b : ℤ, x₂ ^ a * x₃ ^ b = x₃ ^ b * x₂ ^ a := fun a b => (c23.zpow_zpow a b).eq
  calc x₁ ^ i * x₂ ^ j * x₃ ^ k * (x₁ ^ i' * x₂ ^ j' * x₃ ^ k')
      = x₁ ^ i * x₂ ^ j * (x₃ ^ k * x₁ ^ i') * x₂ ^ j' * x₃ ^ k' := by group
    _ = x₁ ^ i * x₂ ^ j * (x₁ ^ i' * x₃ ^ k) * x₂ ^ j' * x₃ ^ k' := by rw [← hc13 i' k]
    _ = x₁ ^ i * (x₂ ^ j * x₁ ^ i') * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by group
    _ = x₁ ^ i * (x₁ ^ i' * x₂ ^ j) * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by rw [← hc12 i' j]
    _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₃ ^ k * x₂ ^ j') * x₃ ^ k' := by group
    _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₂ ^ j' * x₃ ^ k) * x₃ ^ k' := by rw [← hc23 j' k]
    _ = x₁ ^ (i + i') * x₂ ^ (j + j') * x₃ ^ (k + k') := by
      rw [zpow_add, zpow_add, zpow_add]; group

theorem exists_mem_dGrp24_of_gt [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u g : G} (hyp : Hyp24 p f Ω K K' W S R R' z u)
    (hg : g⁻¹ * z * g = u) (h8R : 8 < Nat.card ↥R) :
    ∃ y ∈ dGrp24 K S R R' g, 4 ≤ orderOf y := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hd : Hyp24Data Ω K K' W S R R' z u := hyp.data
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW := hd.hW
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨g₀, hg₀N, hg₀u⟩ := c24_2_proved p f G Ω K K' W S R R' z u hyp
  obtain ⟨e, F, he, hρK, hρ'K, hρR, hρ'R, hFz, hab, hcomm, hac, hbc⟩ :=
    exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have c12 : Commute x₁ x₂ := c.comm_W _ m₁ _ m₂
  have c13 : Commute x₁ x₃ := c.comm_W _ m₁ _ m₃
  have c23 : Commute x₂ x₃ := c.comm_W _ m₂ _ m₃
  have hcardR : 2 * orderOf x₁ = Nat.card ↥R := by
    have h1 : orderOf x₁ = Nat.card ↥(F.ρ.R ⊓ W) := by rw [← Nat.card_zpowers, h₁]
    rw [h1, ← hρR]
    exact (Thompson.D_card c.hp c.hq c.hΩ c.hW F.ρ.hR).symm
  have hm1 : 1 < m := by omega
  set y : G := x₁ * x₂ * x₃ ^ 2 with hy
  have hyz : y = x₁ ^ (1 : ℤ) * x₂ ^ (1 : ℤ) * x₃ ^ (2 : ℤ) := by
    rw [hy]
    simp
  have hyW : y ∈ W := W.mul_mem (W.mul_mem m₁ m₂) (W.pow_mem m₃ 2)
  have hyr : F.ρ.r * y * F.ρ.r⁻¹ = y := by
    have h := A3Mod.conj_nf_r c12 c13 r₁ r₂ r₃ 1 1 2
    rw [show (2 : ℤ) - 1 = 1 by norm_num, ← hyz] at h
    exact h
  have hyt : F.ρ'.r * y * F.ρ'.r⁻¹ = y := by
    have h := A3Mod.conj_nf_t c23 t₁ t₂ t₃ 1 1 2
    rw [show (2 : ℤ) - 1 = 1 by norm_num, ← hyz] at h
    exact h
  have hsy : F.ρ₃.r * y * F.ρ₃.r⁻¹ = x₁ * x₂ := by
    have h := A3Mod.conj_nf_s c13 c23 s₁ s₂ s₃ 1 1 2
    rw [show (1 : ℤ) + 1 - 2 = 0 by norm_num, zpow_zero, mul_one, ← hyz] at h
    rw [h]
    simp
  have hypow : ∀ k : ℕ, y ^ k = x₁ ^ k * x₂ ^ k * x₃ ^ (2 * k) := fun k => by
    rw [hy, ((c13.pow_right 2).mul_left (c23.pow_right 2)).mul_pow k, ← pow_mul, c12.mul_pow]
  have hdvd : ∀ k : ℕ, y ^ k = 1 → 2 * m ∣ k := by
    intro k hk
    have h1 : (x₁ * x₂) ^ k = 1 := by
      have := congrArg (fun a => F.ρ₃.r * a * F.ρ₃.r⁻¹) hk
      simp only [mul_one, mul_inv_cancel] at this
      rw [← hsy, conj_pow]
      exact this
    rw [c12.mul_pow] at h1
    rw [hypow k, h1, one_mul] at hk
    have hdv := orderOf_dvd_of_pow_eq_one hk
    rw [o₃] at hdv
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by
      rw [← mul_assoc, show 2 * 2 = 4 by norm_num]; exact hdv)
  have hRcl : R = Subgroup.closure {x₁, F.ρ.r} := by
    have := Thompson.eq_closure_pair c.hp c.hq c.hΩ c.hW F.ρ.hR h₁ F.ρ.hr F.ρ.hrW
    rwa [hρR] at this
  have hR'cl : R' = Subgroup.closure {x₂, F.ρ'.r} := by
    have := Thompson.eq_closure_pair c.hp c.hq c.hΩ c.hW F.ρ'.hR h₂ F.ρ'.hr F.ρ'.hrW
    rwa [hρ'R] at this
  have hyC : y ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hle : R ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hRcl, Subgroup.closure_le]
      rintro b (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W _ hyW _ m₁).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyr)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hyC' : y ∈ Subgroup.centralizer (R' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hle : R' ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hR'cl, Subgroup.closure_le]
      rintro b (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W _ hyW _ m₂).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyt)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hyN : y ∈ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) :=
    mem_normalizer_conj_of_mem_W hs hW hd.hzW hg₀N hg₀u hg hyW
  have hyS : y ∈ (S : Subgroup G) := hd.hWS hyW
  refine ⟨y, ⟨⟨⟨hyC, hyN⟩, hyS⟩, hyC'⟩, ?_⟩
  have := Nat.le_of_dvd (orderOf_pos y) (hdvd (orderOf y) (pow_orderOf_eq_one y))
  omega

end T7E

variable (p f : ℕ) [Fact p.Prime]

theorem c24_7_of_c24_9 (h9 : C24_9 p f) : C24_7 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp g hg heq
  obtain ⟨y, hyD, hy4⟩ := T7E.exists_mem_dGrp24_of_gt hyp hg (h9 G Ω K K' W S R R' z u hyp)
  have hyz : y ∈ Subgroup.zpowers z := heq ▸ hyD
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
  have hz : IsUniqueInvolution K z := hyp.std.setting.hz
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz.sq
  have hyy : y ^ 2 = 1 := by
    calc y ^ 2 = (z ^ k) ^ 2 := by rw [hk]
      _ = z ^ (k * 2) := by rw [← zpow_natCast, ← zpow_mul]; rfl
      _ = 1 := by rw [mul_comm, zpow_mul, hz2, one_zpow]
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hyy)
  omega

end CFSG.ClassicalInvolution.Asc77
