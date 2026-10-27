module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import Certificates.Certificate36907

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.SuzPump
open CFSG.Sporadic.SuzOddCore (suzM suzT suzEquivM suzM_le_suzT)

section Generic

open scoped Pointwise

private theorem exists_conj_le_sylow_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P K : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hK : IsPGroup p K) : ∃ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ P := by
  obtain ⟨Q, hKQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  have hP' : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] using this.symm
  refine ⟨g, fun k hk => ?_⟩
  rw [hP']
  exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
    ⟨k, hKQ hk, by simp [MulAut.smul_def]⟩

private theorem map_conj_inv_centralizer_inf_suz {G : Type*} [Group G] {P : Subgroup G} {k y : G}
    (hk : k ∈ P) :
    (Subgroup.centralizer ({k * y * k⁻¹} : Set G) ⊓ P).map (MulAut.conj k⁻¹).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) ⊓ P := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨w, ⟨hwc, hwP⟩, rfl⟩
    refine ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩
    calc k⁻¹ * w * k * y = k⁻¹ * (w * (k * y * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y * k⁻¹) * w) * k := by rw [hwc]
      _ = y * (k⁻¹ * w * k) := by group
  · rintro ⟨hzc, hzP⟩
    refine ⟨k * z * k⁻¹, ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩, by group⟩
    calc k * z * k⁻¹ * (k * y * k⁻¹) = k * (z * y) * k⁻¹ := by group
      _ = k * (y * z) * k⁻¹ := by rw [hzc]
      _ = k * y * k⁻¹ * (k * z * k⁻¹) := by group

private theorem mem_zpowers_cases_of_pow_three {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a ∨ b = a ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
  rw [zpow_eq_zpow_emod k h3]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right; rw [h]; simp [zpow_two, sq]

private theorem commutator_eq_top_of_mulEquiv_suz {X X' : Type*} [Group X] [Group X']
    (f : X ≃* X') (h : commutator X = ⊤) : commutator X' = ⊤ := by
  rw [commutator_def] at h ⊢
  have h1 := Subgroup.map_commutator (⊤ : Subgroup X) ⊤ f.toMonoidHom
  rw [h, Subgroup.map_top_of_surjective _ f.surjective] at h1
  exact h1.symm

private theorem map_center_mulEquiv_suz {X X' : Type*} [Group X] [Group X'] (f : X ≃* X') :
    (Subgroup.center X).map f.toMonoidHom = Subgroup.center X' := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    obtain ⟨g', rfl⟩ := f.surjective g
    show f g' * f x = f x * f g'
    rw [← map_mul, ← map_mul, hx g']
  · intro h
    refine ⟨f.symm y, fun g => ?_, by simp⟩
    apply f.injective
    simp [h (f g)]

private theorem isHatSix_of_mulEquiv_suz {X X' : Type*} [Group X] [Group X'] (f : X ≃* X')
    (h : IsHatSix X) : IsHatSix X' := by
  obtain ⟨hc, hz, ⟨g⟩⟩ := h
  refine ⟨commutator_eq_top_of_mulEquiv_suz f hc, ?_,
    ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center X') f
      (map_center_mulEquiv_suz f)).symm.trans g⟩⟩
  rw [← map_center_mulEquiv_suz f, Subgroup.card_map_of_injective f.injective, hz]

private theorem isComponentOf_map_inj {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {K C : Subgroup G} (hK : IsComponentOf K C) :
    IsComponentOf (K.map f) (C.map f) :=
  ⟨Subgroup.map_mono hK.1, isSubnormal_map_open f hK.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (K.equivMapOfInjective f hf).symm hK.2.2⟩

end Generic

section Checks


private theorem okP_spec {g : Array ℕ} (h : okP (levels ()) g = true) :
    Rep 1782 g (permOfArr 1782 g) ∧ permOfArr 1782 g ∈ suzM := by
  simp only [okP, Bool.and_eq_true] at h
  exact ⟨rep_of_validA h.1, mem_suzM_of_inP (rep_of_validA h.1) h.2⟩

private theorem validA_of_okP {L : Array Level} {g : Array ℕ} (h : okP L g = true) :
    validA 1782 g = true := by
  simp only [okP, Bool.and_eq_true] at h
  exact h.1

private theorem fuseCheckG_sound {tab ts ns : Array (Array ℕ)} {xA y x1 : Array ℕ}
    {Y X1 : Equiv.Perm (Fin 1782)} (hY : Rep 1782 y Y) (hX1 : Rep 1782 x1 X1)
    {cs : ℕ → ArrCert} (h : fuseCheckG (levels ()) tab ts ns xA y x1 cs = true) :
    Rep 1782 xA (permOfArr 1782 xA) ∧ permOfArr 1782 xA ∈ suzM ∧ permOfArr 1782 xA ^ 3 = 1 ∧
    permOfArr 1782 xA ≠ 1 ∧
    (∀ i < 6, ∀ k < (cs i).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (cs i).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        ∃ n ∈ suzM, n * p * n⁻¹ = permOfArr 1782 xA ∨ n * p * n⁻¹ = Y) ∧
    (∀ k < (cs 0).pts.size, ∀ p : Equiv.Perm (Fin 1782), Rep 1782 (cs 0).pts[k]! p →
      p ^ 3 = 1 → p ≠ 1 → p * X1 ≠ X1 * p) := by
  simp only [fuseCheckG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hxA, hx3⟩, hx1⟩, hrows⟩, hcov⟩ := h
  obtain ⟨hXr, hXm⟩ := okP_spec hxA
  have hX3 : permOfArr 1782 xA ^ 3 = 1 :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hXr 3) rep_idA).1 hx3
  have hXne : permOfArr 1782 xA ≠ 1 := fun h1 => by
    have := (eqA_iff hXr rep_idA).2 h1
    rw [this] at hx1
    exact absurd hx1 (by decide)
  have hrow : ∀ j < tab.size, ∃ T N : Equiv.Perm (Fin 1782), Rep 1782 ts[j]! T ∧ N ∈ suzM ∧
      (N * T * N⁻¹ = permOfArr 1782 xA ∨ N * T * N⁻¹ = Y) := by
    intro j hj
    have hr := allLt_spec hrows hj
    simp only [Bool.and_eq_true] at hr
    obtain ⟨⟨hts, hns⟩, heq⟩ := hr
    obtain ⟨hTr, -⟩ := okP_spec hts
    obtain ⟨hNr, hNm⟩ := okP_spec hns
    have hc := rep_conjA (g := ns[j]!) (y := ts[j]!) (validA_of_okP hns) hTr
    refine ⟨permOfArr 1782 ts[j]!, permOfArr 1782 ns[j]!, hTr, hNm, ?_⟩
    unfold repOf at heq
    split_ifs at heq with hr0
    · exact Or.inl ((eqA_iff hc hXr).1 heq)
    · exact Or.inr ((eqA_iff hc hY).1 heq)
  refine ⟨hXr, hXm, hX3, hXne, ?_, ?_⟩
  · intro i hi k hk p hp hp3 hp1
    have hik := allLt_spec (allLt_spec hcov hi) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hik
    rcases hik with (h1 | h2) | ⟨h3, -⟩
    · rw [(eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hp 3) rep_idA).2 hp3] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hp rep_idA).1 h2) hp1
    · obtain ⟨j, hj, hjj⟩ := Co2T.anyLt_true h3
      simp only [Bool.and_eq_true, beq_iff_eq] at hjj
      obtain ⟨T, N, hTr, hNm, hNT⟩ := hrow j hj
      have hpT : p = T := (eqA_iff hp hTr).1 hjj.2
      subst hpT
      exact ⟨N, hNm, hNT⟩
  · intro k hk p hp hp3 hp1 hcomm
    have hik := allLt_spec (allLt_spec hcov (by norm_num : 0 < 6)) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hik
    rcases hik with (h1 | h2) | ⟨-, h4⟩
    · rw [(eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hp 3) rep_idA).2 hp3] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hp rep_idA).1 h2) hp1
    · simp only [bne_iff_ne, ne_eq, not_true_eq_false, false_or] at h4
      have hc := (commA_iff hp hX1).2 hcomm
      rw [hc] at h4
      exact absurd h4 (by decide)

private theorem permsA_two_suz {n : ℕ} {gs : Array (Array ℕ)} (h : gs.size = 2) :
    permsA n gs = {permOfArr n gs[0]!, permOfArr n gs[1]!} := by
  ext x
  simp only [permsA, h, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

private theorem pairCheckG_sound {xA : Array ℕ} {X : Equiv.Perm (Fin 1782)} (hX : Rep 1782 xA X)
    {gs : Array (Array ℕ)} {fuel : ℕ} (h : pairCheckG (levels ()) xA gs fuel = true) :
    ∃ g₁ g₂ : Equiv.Perm (Fin 1782), g₁ ∈ suzM ∧ g₂ ∈ suzM ∧ g₁ * X = X * g₁ ∧
      g₂ * X = X * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 1782)))) := by
  simp only [pairCheckG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hsz, hall⟩, henum, hbig⟩ := h
  have hspec := enumOK_spec suzFiveKeys_lt henum
  have hcard : Nat.card (Subgroup.closure (permsA 1782 gs)) =
      (enumBfs 1782 gs suzFiveKeys fuel).pts.size := hspec.2.1
  have hone : ∀ k, k < 2 → orderOf (permOfArr 1782 gs[k]!) = 5 ∧ permOfArr 1782 gs[k]! ∈ suzM ∧
      permOfArr 1782 gs[k]! * X = X * permOfArr 1782 gs[k]! := by
    intro k hk
    have := allLt_spec hall hk
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨⟨hok, hcm⟩, hpow⟩, hne⟩ := this
    obtain ⟨hrep, hmem⟩ := okP_spec hok
    refine ⟨?_, hmem, (commA_iff hrep hX).1 hcm⟩
    have h5 : permOfArr 1782 gs[k]! ^ 5 = 1 :=
      (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep 5) rep_idA).1 hpow
    have h1 : permOfArr 1782 gs[k]! ≠ 1 := fun h1 => by
      rw [(eqA_iff hrep rep_idA).2 h1] at hne
      exact absurd hne (by decide)
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime h5 h1
  obtain ⟨o0, m0, c0⟩ := hone 0 (by norm_num)
  obtain ⟨o1, m1, c1⟩ := hone 1 (by norm_num)
  refine ⟨_, _, m0, m1, c0, c1, o0, o1, ?_⟩
  have hs : Subgroup.closure (permsA 1782 gs) = Subgroup.closure ({permOfArr 1782 gs[0]!,
      permOfArr 1782 gs[1]!} : Set (Equiv.Perm (Fin 1782))) := by rw [permsA_two_suz hsz]
  rw [← hs, hcard]
  exact hbig

private theorem yCheckG_sound {y : Array ℕ} {Y : Equiv.Perm (Fin 1782)} (hY : Rep 1782 y Y)
    {ts : Array (Array ℕ)} {a b g : Array ℕ} {fuel : ℕ}
    (h : yCheckG (levels ()) y ts a b g fuel = true) :
    ∃ u v A B G : Equiv.Perm (Fin 1782), u ∈ suzM ∧ v ∈ suzM ∧ u * Y = Y * u ∧ v * Y = Y * v ∧
      u ^ 10 = 1 ∧ v ^ 10 = 1 ∧ Nat.card (Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782)))) =
        360 ∧ A ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) ∧
      B ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) ∧ A ^ 3 = 1 ∧ A ≠ 1 ∧
      B ^ 3 = 1 ∧ B ≠ 1 ∧ A * B = B * A ∧ B ≠ A ∧ B ≠ A ^ 2 ∧ G ∈ suzM ∧ G * A * G⁻¹ = A ∧
      G * B * G⁻¹ = B⁻¹ := by
  simp only [yCheckG, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hsz, hall⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨henum, hcnt⟩, hoka⟩, hokb⟩, hokg⟩, hanya⟩, hanyb⟩, hpa⟩, hna⟩, hpb⟩, hnb⟩, hcab⟩, hnba⟩, hnbp⟩, hga⟩, hgb⟩⟩ := h
  have hspec := enumOK_spec suzFiveKeys_lt henum
  have hone : ∀ k, k < 2 → permOfArr 1782 ts[k]! ∈ suzM ∧
      permOfArr 1782 ts[k]! * Y = Y * permOfArr 1782 ts[k]! ∧ permOfArr 1782 ts[k]! ^ 10 = 1 := by
    intro k hk
    have := allLt_spec hall hk
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨hok, hcm⟩, hpow⟩ := this
    obtain ⟨hrep, hmem⟩ := okP_spec hok
    exact ⟨hmem, (commA_iff hrep hY).1 hcm,
      (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep 10) rep_idA).1 hpow⟩
  obtain ⟨m0, c0, p0⟩ := hone 0 (by norm_num)
  obtain ⟨m1, c1, p1⟩ := hone 1 (by norm_num)
  obtain ⟨hra, hma⟩ := okP_spec hoka
  obtain ⟨hrb, hmb⟩ := okP_spec hokb
  obtain ⟨hrg, hmg⟩ := okP_spec hokg
  have hs : Subgroup.closure (permsA 1782 ts) = Subgroup.closure ({permOfArr 1782 ts[0]!,
      permOfArr 1782 ts[1]!} : Set (Equiv.Perm (Fin 1782))) := by rw [permsA_two_suz hsz]
  have hA : permOfArr 1782 a ∈ Subgroup.closure (permsA 1782 ts) :=
    enumOK_mem_of_any suzFiveKeys_lt henum hra hanya
  have hB : permOfArr 1782 b ∈ Subgroup.closure (permsA 1782 ts) :=
    enumOK_mem_of_any suzFiveKeys_lt henum hrb hanyb
  have hA3 : permOfArr 1782 a ^ 3 = 1 :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hra 3) rep_idA).1 hpa
  have hB3 : permOfArr 1782 b ^ 3 = 1 :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrb 3) rep_idA).1 hpb
  have hB2 : permOfArr 1782 b ^ 2 = (permOfArr 1782 b)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hB3]
  refine ⟨_, _, permOfArr 1782 a, permOfArr 1782 b, permOfArr 1782 g, m0, m1, c0, c1, p0, p1,
    ?_, ?_, ?_, hA3, ?_, hB3, ?_, ?_, ?_, ?_, hmg, ?_, ?_⟩
  · rw [← hs]; exact hspec.2.1.trans hcnt
  · rw [← hs]; exact hA
  · rw [← hs]; exact hB
  · intro h1
    rw [(eqA_iff hra rep_idA).2 h1] at hna
    exact absurd hna (by decide)
  · intro h1
    rw [(eqA_iff hrb rep_idA).2 h1] at hnb
    exact absurd hnb (by decide)
  · exact (commA_iff hra hrb).1 hcab
  · intro h1
    rw [(eqA_iff hrb hra).2 h1] at hnba
    exact absurd hnba (by decide)
  · intro h1
    rw [(eqA_iff hrb (CFSG.Monster.B.Mathieu.rep_powArr hra 2)).2 h1] at hnbp
    exact absurd hnbp (by decide)
  · exact (eqA_iff (rep_conjA (validA_of_okP hokg) hra) hra).1 hga
  · have := (eqA_iff (rep_conjA (validA_of_okP hokg) hrb)
      (CFSG.Monster.B.Mathieu.rep_powArr hrb 2)).1 hgb
    rw [this, hB2]

end Checks

section Facts


private noncomputable def xA : Equiv.Perm (Fin 1782) := permOfArr 1782 (rebuild (levels ()) xAβ)

private theorem fuse_facts :
    Rep 1782 (rebuild (levels ()) xAβ) xA ∧ xA ∈ suzM ∧ xA ^ 3 = 1 ∧ xA ≠ 1 ∧
    (∀ i < 6, ∀ k < (suzFiveCCert i).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (suzFiveCCert i).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        ∃ n ∈ suzM, n * p * n⁻¹ = xA ∨ n * p * n⁻¹ = yPerm) ∧
    (∀ k < (suzFiveCCert 0).pts.size, ∀ p : Equiv.Perm (Fin 1782),
      Rep 1782 (suzFiveCCert 0).pts[k]! p → p ^ 3 = 1 → p ≠ 1 →
        p * suzFiveLine 1 ≠ suzFiveLine 1 * p) := by
  have h := Certificates.certificate36907.1
  unfold fuseCheck at h
  have hrep : Rep 1782 (suzFiveLineArr 1) (suzFiveLine 1) := rep_suzFiveLine 1
  exact fuseCheckG_sound rep_y hrep h

private theorem pair_facts :
    ∃ g₁ g₂ : Equiv.Perm (Fin 1782), g₁ ∈ suzM ∧ g₂ ∈ suzM ∧ g₁ * xA = xA * g₁ ∧
      g₂ * xA = xA * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 1782)))) := by
  have h := Certificates.certificate36907.2.1
  unfold pairCheck at h
  exact pairCheckG_sound fuse_facts.1 h

private theorem y_facts :
    ∃ u v A B G : Equiv.Perm (Fin 1782), u ∈ suzM ∧ v ∈ suzM ∧ u * yPerm = yPerm * u ∧
      v * yPerm = yPerm * v ∧ u ^ 10 = 1 ∧ v ^ 10 = 1 ∧
      Nat.card (Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782)))) = 360 ∧
      A ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) ∧
      B ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) ∧ A ^ 3 = 1 ∧ A ≠ 1 ∧
      B ^ 3 = 1 ∧ B ≠ 1 ∧ A * B = B * A ∧ B ≠ A ∧ B ≠ A ^ 2 ∧ G ∈ suzM ∧ G * A * G⁻¹ = A ∧
      G * B * G⁻¹ = B⁻¹ := by
  have h := Certificates.certificate36907.2.2
  unfold yCheck at h
  exact yCheckG_sound rep_y h

end Facts

section Classes


private theorem orderOf_conj_eq {G : Type*} [Group G] (h s : G) :
    orderOf (h * s * h⁻¹) = orderOf s := by
  have := (MulAut.conj h : G ≃* G).orderOf_eq s
  simpa [MulAut.conj_apply] using this

private theorem card_suzFiveQ_sylow :
    Nat.card (suzFiveQ.subgroupOf suzM) = 5 ^ (Nat.card suzM).factorization 5 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzFiveQ_le_M).toEquiv, suzFiveQ_spec.2.1,
    factorization_card_suzM_five]
  norm_num

private theorem exists_conj_into_C {s g : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM) (hg : g ∈ suzM)
    (hg5 : orderOf g = 5) (hcomm : g * s = s * g) :
    ∃ h ∈ suzM, ∃ i : Fin 6, h * s * h⁻¹ ∈ suzFiveC i := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set E : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.zpowers g with hE
  have hEP : E ≤ suzM := (Subgroup.zpowers_le).2 hg
  have hEcard : Nat.card E = 5 := by rw [hE, Nat.card_zpowers, hg5]
  have hEG : IsPGroup 5 (E.subgroupOf suzM) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hEcard]
    norm_num
  obtain ⟨k, hk⟩ := exists_conj_le_sylow_of_card (suzFiveQ.subgroupOf suzM) (E.subgroupOf suzM)
    card_suzFiveQ_sylow hEG
  set kP : Equiv.Perm (Fin 1782) := (k : Equiv.Perm (Fin 1782)) with hkP
  have hgq : kP * g * kP⁻¹ ∈ suzFiveQ :=
    Subgroup.mem_subgroupOf.1 (hk ⟨g, hg⟩ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers g)))
  set g' := kP * g * kP⁻¹ with hg'
  have hg'5 : orderOf g' = 5 := by rw [hg', orderOf_conj_eq, hg5]
  have hH : Subgroup.zpowers g' ∈
      {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} :=
    ⟨(Subgroup.zpowers_le).2 hgq, by rw [Nat.card_zpowers, hg'5]⟩
  rw [suzFiveQ_lines.1] at hH
  obtain ⟨i, hi⟩ := hH
  have hxg : suzFiveLine i ∈ Subgroup.zpowers g' := by
    rw [← hi]
    exact Subgroup.mem_zpowers _
  set s' := kP * s * kP⁻¹ with hs'
  have hcomm' : g' * s' = s' * g' := by
    rw [hg', hs']
    calc kP * g * kP⁻¹ * (kP * s * kP⁻¹) = kP * (g * s) * kP⁻¹ := by group
      _ = kP * (s * g) * kP⁻¹ := by rw [hcomm]
      _ = kP * s * kP⁻¹ * (kP * g * kP⁻¹) := by group
  have hxs : suzFiveLine i * s' = s' * suzFiveLine i := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxg
    rw [← hm]
    exact (Commute.zpow_left (show Commute g' s' from hcomm') m).eq
  have hs'M : s' ∈ suzM := suzM.mul_mem (suzM.mul_mem k.2 hs) (suzM.inv_mem k.2)
  have hC : suzFiveC i = Subgroup.centralizer {suzFiveLine i} ⊓ suzT := suzFiveC_eq i.2
  refine ⟨kP, k.2, i, ?_⟩
  rw [hC]
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxs.symm, suzM_le_suzT hs'M⟩

private theorem exists_rep_of_mem_C {i : Fin 6} {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzFiveC i) :
    ∃ k < (suzFiveCCert i).pts.size, Rep 1782 (suzFiveCCert i).pts[k]! s :=
  enumOK_exists_rep suzFiveKeys_lt (suzFiveC_check_spec i.2).1 hs

private theorem no_order25_centralized {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) {E : Subgroup (Equiv.Perm (Fin 1782))} (hEP : E ≤ suzM)
    (hE : Nat.card E = 25) (hcomm : ∀ e ∈ E, e * s = s * e) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hEG : IsPGroup 5 (E.subgroupOf suzM) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE]
    norm_num
  obtain ⟨k, hk⟩ := exists_conj_le_sylow_of_card (suzFiveQ.subgroupOf suzM) (E.subgroupOf suzM)
    card_suzFiveQ_sylow hEG
  set kP : Equiv.Perm (Fin 1782) := (k : Equiv.Perm (Fin 1782)) with hkP
  set E' : Subgroup (Equiv.Perm (Fin 1782)) := E.map (MulAut.conj kP).toMonoidHom with hE'
  have hE'Q : E' ≤ suzFiveQ := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hk ⟨e, hEP he⟩ (Subgroup.mem_subgroupOf.2 he))
  have hE'card : Nat.card E' = 25 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj kP).injective, hE]
  have hE'eq : E' = suzFiveQ :=
    Subgroup.eq_of_le_of_card_ge hE'Q (by rw [hE'card, suzFiveQ_spec.2.1])
  set s' := kP * s * kP⁻¹ with hs'
  have hs'M : s' ∈ suzM := suzM.mul_mem (suzM.mul_mem k.2 hs) (suzM.inv_mem k.2)
  have hcomm' : ∀ e ∈ E', e * s' = s' * e := by
    rintro _ ⟨e, he, rfl⟩
    have := hcomm e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs']
    calc kP * e * kP⁻¹ * (kP * s * kP⁻¹) = kP * (e * s) * kP⁻¹ := by group
      _ = kP * (s * e) * kP⁻¹ := by rw [this]
      _ = kP * s * kP⁻¹ * (kP * e * kP⁻¹) := by group
  have hx0 : suzFiveLine 0 ∈ E' := by
    rw [hE'eq]
    exact suzFiveLine_mem_Q 0
  have hx1 : suzFiveLine 1 ∈ E' := by
    rw [hE'eq]
    exact suzFiveLine_mem_Q 1
  have hC0 : suzFiveC 0 = Subgroup.centralizer {suzFiveLine 0} ⊓ suzT := suzFiveC_eq (by norm_num)
  have hs'C : s' ∈ suzFiveC 0 := by
    rw [hC0]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm' _ hx0).symm,
      suzM_le_suzT hs'M⟩
  obtain ⟨j, hj, hjrep⟩ := exists_rep_of_mem_C hs'C
  have hs'3 : s' ^ 3 = 1 := by
    have := pow_orderOf_eq_one s'
    rwa [hs', orderOf_conj_eq, hs3] at this
  have hs'1 : s' ≠ 1 := fun h1 => by
    have : orderOf s' = 3 := by rw [hs', orderOf_conj_eq, hs3]
    rw [h1, orderOf_one] at this
    omega
  exact fuse_facts.2.2.2.2.2 j hj s' hjrep hs'3 hs'1 (hcomm' _ hx1).symm

private theorem not_25_dvd_centralizer {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) :
    ¬ 25 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782))) := by
  intro hd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.centralizer ({s} : Set _) ⊓ suzM with hC
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2) (by simpa using hd)
  refine no_order25_centralized hs hs3 (E := E.map C.subtype) ?_ ?_ ?_
  · rintro _ ⟨e, -, rfl⟩
    exact (Subgroup.mem_inf.1 e.2).2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE]
    norm_num
  · rintro _ ⟨e, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 e.2).1

private theorem classes_of_order_three {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782))) ∨
    (∃ k ∈ suzM, k * xA * k⁻¹ = s) ∨ (∃ k ∈ suzM, k * yPerm * k⁻¹ = s) := by
  by_cases h5 : 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
      Subgroup (Equiv.Perm (Fin 1782)))
  · right
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({s} :
      Set (Equiv.Perm (Fin 1782))) ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782)))) 5 h5
    have hxc := Subgroup.mem_inf.1 x.2
    have hg5 : orderOf (x : Equiv.Perm (Fin 1782)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨h, hh, i, hi⟩ := exists_conj_into_C hs hxc.2 hg5
      (Subgroup.mem_centralizer_singleton_iff.1 hxc.1)
    obtain ⟨j, hj, hjrep⟩ := exists_rep_of_mem_C hi
    have hs'3 : (h * s * h⁻¹) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (h * s * h⁻¹)
      rwa [orderOf_conj_eq, hs3] at this
    have hs'1 : h * s * h⁻¹ ≠ 1 := fun h1 => by
      have : orderOf (h * s * h⁻¹) = 3 := by rw [orderOf_conj_eq, hs3]
      rw [h1, orderOf_one] at this
      omega
    obtain ⟨n, hn, hcase⟩ := fuse_facts.2.2.2.2.1 i i.2 j hj _ hjrep hs'3 hs'1
    have hnh : (n * h)⁻¹ * (n * (h * s * h⁻¹) * n⁻¹) * (n * h) = s := by group
    have hnhM : (n * h)⁻¹ ∈ suzM := suzM.inv_mem (suzM.mul_mem hn hh)
    rcases hcase with hc | hc
    · left
      refine ⟨(n * h)⁻¹, hnhM, ?_⟩
      rw [← hnh, hc]
      group
    · right
      refine ⟨(n * h)⁻¹, hnhM, ?_⟩
      rw [← hnh, hc]
      group
  · exact Or.inl h5

end Classes

section Components


private theorem xA_ord : orderOf xA = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime fuse_facts.2.2.1 fuse_facts.2.2.2.1

private theorem yPerm_ne_one : yPerm ≠ 1 := fun h1 => by
  have := (eqA_iff rep_y rep_idA).2 h1
  rw [cCheck_parts.2.2.2.1] at this
  exact absurd this (by decide)

private theorem yPerm_ord : orderOf yPerm = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime yPerm_pow yPerm_ne_one

private theorem card_Cy : Nat.card (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓
    suzM : Subgroup (Equiv.Perm (Fin 1782))) = 3 ^ 1 * 1080 := by
  rw [← (Cy_eq).1, (Cy_eq).2]
  norm_num

private theorem coprime_three_of_pow_ten {x : Equiv.Perm (Fin 1782)} (h : x ^ 10 = 1) :
    Nat.Coprime (orderOf x) 3 :=
  Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h) (by norm_num)

private theorem not_hatSix_xA {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({xA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (h : IsHatSix ↥K) : False := by
  obtain ⟨g₁, g₂, hg₁, hg₂, hc₁, hc₂, ho₁, ho₂, hbig⟩ := pair_facts
  refine false_of_isHatSix_of_five_gen hK h (not_25_dvd_centralizer fuse_facts.2.1 xA_ord)
    (T := {g₁, g₂}) ?_ ?_ hbig
  · rintro x (rfl | rfl)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₁, hg₁⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₂, hg₂⟩
  · rintro x (rfl | rfl)
    · exact ho₁
    · exact ho₂

private theorem not_alt6_xA {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({xA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨g₁, g₂, hg₁, hg₂, hc₁, hc₂, ho₁, ho₂, hbig⟩ := pair_facts
  refine false_of_alt6_of_five_gen hK h (not_25_dvd_centralizer fuse_facts.2.1 xA_ord)
    (T := {g₁, g₂}) ?_ ?_ (lt_trans (by norm_num) hbig)
  · rintro x (rfl | rfl)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₁, hg₁⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₂, hg₂⟩
  · rintro x (rfl | rfl)
    · exact ho₁
    · exact ho₂

private theorem not_hatSix_y {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (h : IsHatSix ↥K) : False := by
  obtain ⟨u, v, A, B, G, hu, hv, huc, hvc, hu10, hv10, hD, -⟩ := y_facts
  refine false_of_isHatSix_of_threePrime_gen hK h (k := 1) card_Cy (T := {u, v}) ?_ ?_ hD
  · rintro x (rfl | rfl)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 huc, hu⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hvc, hv⟩
  · rintro x (rfl | rfl)
    · exact coprime_three_of_pow_ten hu10
    · exact coprime_three_of_pow_ten hv10

private theorem reflect_y {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (hA6 : Nonempty (↥K ≃* alternatingGroup (Fin 6))) :
    ∃ a ∈ K, ∃ b ∈ K, ∃ g ∈ suzM, a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ Subgroup.zpowers a ∧ g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b⁻¹ := by
  obtain ⟨u, v, A, B, G, hu, hv, huc, hvc, hu10, hv10, hD, hAD, hBD, hA3, hA1, hB3, hB1, hAB,
    hBA, hBA2, hG, hGA, hGB⟩ := y_facts
  set C : Subgroup (Equiv.Perm (Fin 1782)) :=
    Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM with hCdef
  have hcardK : Nat.card K = 360 := by
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.K426.card_A6]
  have hCcard : Nat.card C = 3240 := by
    rw [hCdef, card_Cy]
    norm_num
  have hrel : K.relIndex C = 9 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv, hcardK, hCcard] at h1
    unfold Subgroup.relIndex
    omega
  have hTC : ({u, v} : Set (Equiv.Perm (Fin 1782))) ⊆ C := by
    rintro x (rfl | rfl)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 huc, hu⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hvc, hv⟩
  have hTK : ({u, v} : Set (Equiv.Perm (Fin 1782))) ⊆ K := by
    intro g hg
    refine mem_of_isSubnormal_of_coprime hK.2.1 (hTC hg) ?_
    rw [hrel]
    rcases hg with rfl | rfl
    · exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hu10) (by norm_num)
    · exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hv10) (by norm_num)
  have hle : Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) ≤ K :=
    (Subgroup.closure_le K).2 hTK
  have heq : Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 1782))) = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardK, hD])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨A, heq ▸ hAD, B, heq ▸ hBD, G, hG, hAB, orderOf_eq_prime hA3 hA1,
    orderOf_eq_prime hB3 hB1, fun hmem => ?_, hGA, hGB⟩
  rcases mem_zpowers_cases_of_pow_three hA3 hmem with h | h | h
  · exact hB1 h
  · exact hBA h
  · exact hBA2 h

private theorem conj_component {c k : Equiv.Perm (Fin 1782)} (hk : k ∈ suzM)
    {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({k * c * k⁻¹} : Set (Equiv.Perm (Fin 1782))) ⊓
      suzM)) :
    IsComponentOf (K.map (MulAut.conj k⁻¹).toMonoidHom)
      (Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  have := isComponentOf_map_inj (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective hK
  rwa [map_conj_inv_centralizer_inf_suz hk] at this

private theorem not_hatSix_P {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM) (hs3 : orderOf s = 3)
    {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (h : IsHatSix ↥K) : False := by
  rcases classes_of_order_three hs hs3 with h5 | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact false_of_isHatSix_of_not_five hK.1 (Or.inl h) h5
  · exact not_hatSix_xA (conj_component hk hK) (isHatSix_of_mulEquiv_suz
      (K.equivMapOfInjective _ (MulAut.conj k⁻¹).injective) h)
  · exact not_hatSix_y (conj_component hk hK) (isHatSix_of_mulEquiv_suz
      (K.equivMapOfInjective _ (MulAut.conj k⁻¹).injective) h)

private theorem reflect_P {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM) (hs3 : orderOf s = 3)
    {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM))
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 6))) :
    ∃ a ∈ K, ∃ b ∈ K, ∃ g ∈ suzM, a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ Subgroup.zpowers a ∧ g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b⁻¹ := by
  rcases classes_of_order_three hs hs3 with h5 | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact (false_of_isHatSix_of_not_five hK.1 (Or.inr h) h5).elim
  · exact (not_alt6_xA (conj_component hk hK) (by
      obtain ⟨e⟩ := h
      exact ⟨(K.equivMapOfInjective _ (MulAut.conj k⁻¹).injective).symm.trans e⟩)).elim
  · set φ : Equiv.Perm (Fin 1782) →* Equiv.Perm (Fin 1782) := (MulAut.conj k⁻¹).toMonoidHom with hφ
    have hφinj : Function.Injective φ := (MulAut.conj k⁻¹).injective
    have hφx : ∀ x, φ x = k⁻¹ * x * k := fun x => by simp [hφ, MulAut.conj_apply]
    obtain ⟨a₀, ha₀, b₀, hb₀, g₀, hg₀, hab, ha3, hb3, hba, hga, hgb⟩ := reflect_y
      (conj_component hk hK) (by
        obtain ⟨e⟩ := h
        exact ⟨(K.equivMapOfInjective _ hφinj).symm.trans e⟩)
    obtain ⟨a, haK, rfl⟩ := Subgroup.mem_map.1 ha₀
    obtain ⟨b, hbK, rfl⟩ := Subgroup.mem_map.1 hb₀
    refine ⟨a, haK, b, hbK, k * g₀ * k⁻¹, suzM.mul_mem (suzM.mul_mem hk hg₀) (suzM.inv_mem hk),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply hφinj
      rw [map_mul, map_mul]
      exact hab
    · rw [← orderOf_injective φ hφinj a]
      exact ha3
    · rw [← orderOf_injective φ hφinj b]
      exact hb3
    · intro hmem
      apply hba
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨m, by rw [← map_zpow, hm]⟩
    · have h1 := hga
      rw [hφx] at h1
      calc k * g₀ * k⁻¹ * a * (k * g₀ * k⁻¹)⁻¹ = k * (g₀ * (k⁻¹ * a * k) * g₀⁻¹) * k⁻¹ := by group
        _ = k * (k⁻¹ * a * k) * k⁻¹ := by rw [h1]
        _ = a := by group
    · have h2 := hgb
      rw [hφx] at h2
      calc k * g₀ * k⁻¹ * b * (k * g₀ * k⁻¹)⁻¹ = k * (g₀ * (k⁻¹ * b * k) * g₀⁻¹) * k⁻¹ := by group
        _ = k * (k⁻¹ * b * k)⁻¹ * k⁻¹ := by rw [h2]
        _ = b⁻¹ := by group

end Components

section Assembly


private theorem map_centralizer_suz {G : Type*} [Group G] (φ : G ≃* ↥suzM) (s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (suzM.subtype.comp φ.toMonoidHom) =
      Subgroup.centralizer ({(suzM.subtype.comp φ.toMonoidHom) s} :
        Set (Equiv.Perm (Fin 1782))) ⊓ suzM := by
  have hι : Function.Injective (suzM.subtype.comp φ.toMonoidHom) :=
    suzM.subtype_injective.comp φ.injective
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (φ y).2⟩
    show (suzM.subtype.comp φ.toMonoidHom) y * (suzM.subtype.comp φ.toMonoidHom) s =
      (suzM.subtype.comp φ.toMonoidHom) s * (suzM.subtype.comp φ.toMonoidHom) y
    rw [← map_mul, ← map_mul, hy]
  · rintro ⟨hx, hxP⟩
    have hxι : (suzM.subtype.comp φ.toMonoidHom) (φ.symm ⟨x, hxP⟩) = x := by simp
    refine ⟨φ.symm ⟨x, hxP⟩, ?_, hxι⟩
    apply hι
    rw [map_mul, map_mul, hxι]
    exact hx

private theorem not_hatSix_of_mulEquiv {G : Type*} [Group G] (φ : G ≃* ↥suzM) {s : G}
    (hs : orderOf s = 3) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set G))) (h : IsHatSix ↥K) : False := by
  have hι : Function.Injective (suzM.subtype.comp φ.toMonoidHom) :=
    suzM.subtype_injective.comp φ.injective
  have hK' := isComponentOf_map_inj _ hι hK
  rw [map_centralizer_suz φ s] at hK'
  have hts : orderOf ((suzM.subtype.comp φ.toMonoidHom) s) = 3 := by
    rw [orderOf_injective _ hι s]
    exact hs
  exact not_hatSix_P (φ s).2 hts hK'
    (isHatSix_of_mulEquiv_suz (K.equivMapOfInjective _ hι) h)

private theorem reflect_of_mulEquiv {G : Type*} [Group G] (φ : G ≃* ↥suzM) {s : G}
    (hs : orderOf s = 3) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set G)))
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 6))) :
    ∃ a ∈ K, ∃ b ∈ K, ∃ g : G, a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ Subgroup.zpowers a ∧ g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b⁻¹ := by
  set ι : G →* Equiv.Perm (Fin 1782) := suzM.subtype.comp φ.toMonoidHom with hιdef
  have hι : Function.Injective ι := suzM.subtype_injective.comp φ.injective
  have hK' := isComponentOf_map_inj ι hι hK
  rw [hιdef, map_centralizer_suz φ s] at hK'
  have hts : orderOf (ι s) = 3 := by
    rw [orderOf_injective _ hι s]
    exact hs
  obtain ⟨e⟩ := h
  obtain ⟨a', ha', b', hb', g', hg', hab, ha3, hb3, hba, hga, hgb⟩ :=
    reflect_P (φ s).2 hts hK' ⟨(K.equivMapOfInjective ι hι).symm.trans e⟩
  obtain ⟨a, haK, rfl⟩ := Subgroup.mem_map.1 ha'
  obtain ⟨b, hbK, rfl⟩ := Subgroup.mem_map.1 hb'
  have hgι : ι (φ.symm ⟨g', hg'⟩) = g' := by simp [hιdef]
  refine ⟨a, haK, b, hbK, φ.symm ⟨g', hg'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hι
    rw [map_mul, map_mul]
    exact hab
  · rw [← orderOf_injective ι hι a]
    exact ha3
  · rw [← orderOf_injective ι hι b]
    exact hb3
  · intro hmem
    apply hba
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨m, by rw [← map_zpow, hm]⟩
  · apply hι
    simp only [map_mul, map_inv, hgι]
    exact hga
  · apply hι
    simp only [map_mul, map_inv, hgι]
    exact hgb

end Assembly

theorem sporNoPumpup_Suz
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .Suz := by
  let φ : (TauCeti.CFSGIndex.sporadic .Suz).Group ≃* ↥suzM :=
    (hbr .Suz).some.symm.trans suzEquivM
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Suz).Group :=
    Finite.of_equiv ↥suzM φ.symm.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (hbr .Suz).some.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  · exact OPrimeCoreTrivialAt.of_mulEquiv φ oPrimeCoreTrivialAt_suzM
  · intro s hs K hK h
    rcases h with h | ⟨hM, _⟩
    · exact not_hatSix_of_mulEquiv φ hs hK h
    · exact absurd hM (by decide)
  · intro _ s hs K hK h
    exact reflect_of_mulEquiv φ hs hK h

end CFSG.HardMathSupport.Solomon.Coordinator
