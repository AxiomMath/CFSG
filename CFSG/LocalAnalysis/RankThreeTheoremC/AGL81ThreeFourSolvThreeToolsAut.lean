module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup

namespace SolvNone

variable {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]

theorem eq_one_of_isPGroup_of_coprime {π : Y →* X} (hker : Nat.Coprime 3 (Nat.card π.ker))
    {P : Subgroup Y} (hP : IsPGroup 3 P) : ∀ x ∈ P, π x = 1 → x = 1 := by
  intro x hx h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hn' : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1' : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have h2 : orderOf x ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨x, MonoidHom.mem_ker.mpr h1⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (3 ^ n) (Nat.card π.ker) := Nat.Coprime.pow_left n hker
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1' h2)

theorem pRank_map_eq_of_coprime {π : Y →* X} (hker : Nat.Coprime 3 (Nat.card π.ker))
    {Q : Subgroup Y} (hQ : IsPGroup 3 Q) :
    CFSG.Open.pRank 3 (Q.map π) = CFSG.Open.pRank 3 Q :=
  CFSG.LocalAnalysis.RankThreeTheoremC.u3main_pRank_map Nat.prime_three π
    (eq_one_of_isPGroup_of_coprime hker hQ)

theorem map_normalizer_eq_of_coprime {π : Y →* X} (hπ : Function.Surjective π)
    (hker : Nat.Coprime 3 (Nat.card π.ker)) {Q : Subgroup Y} (hQ : IsPGroup 3 Q) :
    (normalizer (Q : Set Y)).map π = normalizer ((Q.map π : Subgroup X) : Set X) :=
  CFSG.SignalizerFunctor.Helpers.coprime_surjective_normalizer_image 3 Nat.prime_three π hπ Q
    hker hQ

private theorem exists_map_eq_of_le {π : Y →* X} {P : Subgroup Y} {Q' : Subgroup X}
    (hQ' : Q' ≤ P.map π) : ∃ Q : Subgroup Y, Q ≤ P ∧ Q.map π = Q' := by
  refine ⟨Q'.comap π ⊓ P, inf_le_right, le_antisymm ?_ ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.1
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := hQ' hx
    exact ⟨p, ⟨hx, hp⟩, rfl⟩

theorem map_glbCore_eq {π : Y →* X} (hπ : Function.Surjective π)
    (hker : Nat.Coprime 3 (Nat.card π.ker)) {P : Subgroup Y} (hP : IsPGroup 3 P) (k : ℕ) :
    (GLBCore 3 k P).map π = GLBCore 3 k (P.map π) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    obtain ⟨Q, hQP, hk, rfl⟩ := hN
    rw [← Subgroup.map_le_iff_le_comap, map_normalizer_eq_of_coprime hπ hker (hP.to_le hQP)]
    refine le_sSup ⟨Q.map π, Subgroup.map_mono hQP, ?_, rfl⟩
    rwa [pRank_map_eq_of_coprime hker (hP.to_le hQP)]
  · refine sSup_le fun N' hN' => ?_
    obtain ⟨Q', hQ'P, hk, rfl⟩ := hN'
    obtain ⟨Q, hQP, rfl⟩ := exists_map_eq_of_le hQ'P
    rw [← map_normalizer_eq_of_coprime hπ hker (hP.to_le hQP)]
    refine Subgroup.map_mono (le_sSup ⟨Q, hQP, ?_, rfl⟩)
    rwa [← pRank_map_eq_of_coprime hker (hP.to_le hQP)]

private theorem map_inf_centralizer_eq {π : Y →* X} (hker : Nat.Coprime 3 (Nat.card π.ker))
    {P Q : Subgroup Y} (hP : IsPGroup 3 P) (hQP : Q ≤ P) :
    (P ⊓ centralizer (Q : Set Y)).map π =
      P.map π ⊓ centralizer ((Q.map π : Subgroup X) : Set X) := by
  apply le_antisymm
  · rintro _ ⟨r, ⟨hrP, hrC⟩, rfl⟩
    refine ⟨⟨r, hrP, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hrC q hq]
  · rintro _ ⟨⟨r, hrP, rfl⟩, hrC⟩
    refine ⟨r, ⟨hrP, mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
    have h1 : π (q * r * q⁻¹ * r⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        mem_centralizer_iff.mp hrC (π q) ⟨q, hq, rfl⟩]
      group
    have h2 := eq_one_of_isPGroup_of_coprime hker hP _
      (P.mul_mem (P.mul_mem (P.mul_mem (hQP hq) hrP) (P.inv_mem (hQP hq))) (P.inv_mem hrP)) h1
    calc q * r = q * r * q⁻¹ * r⁻¹ * (r * q) := by group
      _ = r * q := by rw [h2, one_mul]

theorem map_glbWeakCore_eq {π : Y →* X} (hπ : Function.Surjective π)
    (hker : Nat.Coprime 3 (Nat.card π.ker)) {P : Subgroup Y} (hP : IsPGroup 3 P) :
    (GLBWeakCore 3 P).map π = GLBWeakCore 3 (P.map π) := by
  have hrank : ∀ Q : Subgroup Y, Q ≤ P →
      CFSG.Open.pRank 3 ((Q.map π) ⊔ (P.map π ⊓ centralizer ((Q.map π : Subgroup X) : Set X))) =
        CFSG.Open.pRank 3 (Q ⊔ (P ⊓ centralizer (Q : Set Y))) := by
    intro Q hQP
    have hle : Q ⊔ (P ⊓ centralizer (Q : Set Y)) ≤ P := sup_le hQP inf_le_left
    rw [← map_inf_centralizer_eq hker hP hQP, ← Subgroup.map_sup]
    exact pRank_map_eq_of_coprime hker (hP.to_le hle)
  apply le_antisymm
  · rw [GLBWeakCore, rankThreeAschCore, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    obtain ⟨Q, hQP, hk, h3, rfl⟩ := hN
    rw [← Subgroup.map_le_iff_le_comap, map_normalizer_eq_of_coprime hπ hker (hP.to_le hQP)]
    refine le_sSup ⟨Q.map π, Subgroup.map_mono hQP, ?_, ?_, rfl⟩
    · rwa [pRank_map_eq_of_coprime hker (hP.to_le hQP)]
    · rwa [hrank Q hQP]
  · rw [GLBWeakCore, rankThreeAschCore]
    refine sSup_le fun N' hN' => ?_
    obtain ⟨Q', hQ'P, hk, h3, rfl⟩ := hN'
    obtain ⟨Q, hQP, rfl⟩ := exists_map_eq_of_le hQ'P
    rw [← map_normalizer_eq_of_coprime hπ hker (hP.to_le hQP)]
    refine Subgroup.map_mono (le_sSup ⟨Q, hQP, ?_, ?_, rfl⟩)
    · rwa [← pRank_map_eq_of_coprime hker (hP.to_le hQP)]
    · rwa [← hrank Q hQP]

theorem map_threeFourCore_le {π : Y →* X} (hπ : Function.Surjective π)
    (hker : Nat.Coprime 3 (Nat.card π.ker)) (R : Sylow 3 Y) {E Y₀ : Subgroup Y}
    (hER : E ≤ R)
    (hcore : (if 3 ≤ CFSG.pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀) :
    (if 3 ≤ CFSG.pRank 3 ((R : Subgroup Y).map π) then GLBWeakCore 3 ((R : Subgroup Y).map π)
      else GLBCore 3 1 (E.map π)) ≤ Y₀.map π := by
  have hR : IsPGroup 3 (R : Subgroup Y) := R.isPGroup'
  have hrk : CFSG.pRank 3 ((R : Subgroup Y).map π) = CFSG.pRank 3 (R : Subgroup Y) := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact pRank_map_eq_of_coprime hker hR
  rw [hrk]
  split_ifs with h3
  · rw [if_pos h3] at hcore
    rw [← map_glbWeakCore_eq hπ hker hR]
    exact Subgroup.map_mono hcore
  · rw [if_neg h3] at hcore
    rw [← map_glbCore_eq hπ hker (hR.to_le hER)]
    exact Subgroup.map_mono hcore

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
  have h : a ∈ center K := Subgroup.mem_center_iff.mpr fun g => by
    have h1 := congrArg (fun φ : MulAut K => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rwa [hZ, Subgroup.mem_bot] at h

theorem centralizer_map_rangeRestrict_conjNormal_eq_bot {K : Subgroup Y} [K.Normal]
    (hZ : center K = ⊥) :
    Subgroup.centralizer
      (SetLike.coe (K.map (MulAut.conjNormal : Y →* MulAut ↥K).rangeRestrict)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨φ, hφ⟩ := x
  apply Subtype.ext
  change φ = 1
  refine MulEquiv.ext fun k => ?_
  have hk := mem_centralizer_iff.mp hx _ ⟨k, k.2, rfl⟩
  have h1 : (MulAut.conjNormal (k : Y) : MulAut ↥K) * φ = φ * MulAut.conjNormal (k : Y) :=
    congrArg Subtype.val hk
  rw [MulAut.conjNormal_val] at h1
  have h2 : MulAut.conj (φ k) = MulAut.conj k := by
    have : φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
      ext z
      simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
    rw [← this, ← h1, mul_inv_cancel_right]
  exact conj_injective_of_center_eq_bot hZ h2

theorem ker_rangeRestrict_conjNormal (K : Subgroup Y) [K.Normal] :
    (MulAut.conjNormal : Y →* MulAut ↥K).rangeRestrict.ker = centralizer (K : Set Y) := by
  ext y
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h m hm
    have := congrArg Subtype.val (DFunLike.congr_fun h ⟨m, hm⟩)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  · intro h
    refine MulEquiv.ext fun m => Subtype.ext ?_
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [(h m m.2).symm, mul_inv_cancel_right]

theorem nonempty_mulEquiv_map_rangeRestrict_conjNormal {K : Subgroup Y} [K.Normal]
    (hZ : center K = ⊥) :
    Nonempty (↥(K.map (MulAut.conjNormal : Y →* MulAut ↥K).rangeRestrict) ≃* ↥K) := by
  set θ := (MulAut.conjNormal : Y →* MulAut ↥K).rangeRestrict with hθ
  have hinj : Function.Injective (θ.comp K.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun k hk => ?_
    have h1 : (k : Y) ∈ centralizer (K : Set Y) := by
      rw [← ker_rangeRestrict_conjNormal K]
      exact hk
    have h2 : k ∈ center K := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (mem_centralizer_iff.mp h1 g g.2)
    rwa [hZ, Subgroup.mem_bot] at h2
  have hrange : (θ.comp K.subtype).range = K.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem le_or_commutator_eq_bot_of_isSubnormal {G : Type*} [Group G] {V H S : Subgroup G}
    (hVH : V ≤ H)
    (hV : ∀ W : Subgroup G, W ≤ H → V ≤ normalizer (W : Set G) → V ≤ W ∨ ⁅W, V⁆ = ⊥)
    (hS : IsSubnormal S H) : V ≤ S ∨ ⁅S, V⁆ = ⊥ := by
  induction hS with
  | refl K => exact Or.inl hVH
  | @step S M K hSM hn hMK ih =>
    rcases ih hVH hV with h | h
    · refine hV S (hSM.trans hMK.le) fun v hv => ?_
      have hvM : v ∈ M := h hv
      rw [mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        exact (Subgroup.normal_subgroupOf_iff hSM).mp hn s v hs hvM
      · intro hs
        have := (Subgroup.normal_subgroupOf_iff hSM).mp hn _ v⁻¹ hs (M.inv_mem hvM)
        simpa [mul_assoc] using this
    · exact Or.inr (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hSM le_rfl))

end SolvNone

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
