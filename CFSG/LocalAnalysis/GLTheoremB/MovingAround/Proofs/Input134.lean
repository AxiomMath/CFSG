module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1113b
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input134

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)

theorem innerAut_normal (K : Type) [Group K] :
    ((MulAut.conj : K →* MulAut K).range).Normal := by
  constructor
  intro n hn g
  obtain ⟨s, rfl⟩ := hn
  refine ⟨g s, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem conj_ker_eq_center (K : Type) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun τ : MulAut K => τ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h g).symm

theorem eq_one_of_commute_inner {K : Type} [Group K] (hK : commutator K = ⊤) (σ : MulAut K)
    (h : ∀ c : K, σ * MulAut.conj c = MulAut.conj c * σ) : σ = 1 := by
  apply CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hK
  rw [map_one]
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hu : x⁻¹ * σ x ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := σ.surjective z
    have e1 : σ x * σ y * (σ x)⁻¹ = x * σ y * x⁻¹ := by
      have := congrArg (fun τ : MulAut K => τ y) (h x)
      simpa [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc] using this
    calc σ y * (x⁻¹ * σ x) = x⁻¹ * (x * σ y * x⁻¹) * σ x := by group
      _ = x⁻¹ * (σ x * σ y * (σ x)⁻¹) * σ x := by rw [e1]
      _ = x⁻¹ * σ x * σ y := by group
  rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk, MulAut.one_apply]
  apply QuotientGroup.eq.2
  simpa [mul_inv_rev] using Subgroup.inv_mem _ hu

theorem pCoreOf_conj_mem {G : Type} [Group G] (p : ℕ) {C : Subgroup G} {g : G} (hg : g ∈ C)
    {n : G} (hn : n ∈ CFSG.Open.pCoreOf p C) : g * n * g⁻¹ ∈ CFSG.Open.pCoreOf p C := by
  unfold CFSG.Open.pCoreOf at hn ⊢
  obtain ⟨s, hs, hsn⟩ := Subgroup.mem_map.1 hn
  have hs' : (⟨g, hg⟩ : ↥C) * s * (⟨g, hg⟩ : ↥C)⁻¹ ∈ CFSG.pCore p ↥C :=
    (CFSG.pCore_normal (p := p) (G := ↥C)).conj_mem s hs ⟨g, hg⟩
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : ↥C) * s * (⟨g, hg⟩ : ↥C)⁻¹, hs', ?_⟩
  rw [map_mul, map_mul, map_inv, hsn]
  simp

theorem pCoreOf_subgroupOf_normal {G : Type} [Group G] (p : ℕ) (C : Subgroup G) :
    ((CFSG.Open.pCoreOf p C).subgroupOf C).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := pCoreOf_conj_mem p g.2 hn
  simpa using this

theorem pCoreOf_isPGroup {G : Type} [Group G] (p : ℕ) (C : Subgroup G) :
    IsPGroup p ↥(CFSG.Open.pCoreOf p C) := by
  unfold CFSG.Open.pCoreOf
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥C)).map C.subtype

theorem isPGroup_three_zpowers {H : Type} [Group H] [Finite H] {x : H} (hx : x ^ 3 = 1) :
    IsPGroup 3 ↥(Subgroup.zpowers x) := by
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx)
  · exact ⟨0, by rw [h1]; simp⟩
  · exact ⟨1, by rw [h3]; simp⟩

section Certified


theorem input13_4_holds :
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1113b.Input13_4 := by
  intro K _ _ H' _ _ φ hK hChev hinj hX x k hx3 hx1 _ hφx
  let A : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range
  let S : Subgroup H' := A.comap φ
  have hSn : S.Normal := (innerAut_normal K).comap φ
  have hSmap : S.map φ = A := Subgroup.map_comap_eq_self hX
  let e1 : ↥S ≃* ↥A := (S.equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr hSmap)
  let e2 : (K ⧸ Subgroup.center K) ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq (conj_ker_eq_center K).symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K))
  let e : ↥S ≃* (K ⧸ Subgroup.center K) := e1.trans e2.symm
  have hSs : IsSimpleGroup ↥S := e.isSimpleGroup_congr.2 hK.2
  have hSnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg (⇑e) h
    simpa using this
  have hSchev : IsChevOfChar 3 ↥S := by
    obtain ⟨d, hd, ⟨f⟩⟩ := hChev
    exact ⟨d, hd, ⟨e.trans f⟩⟩
  have hScent : Subgroup.centralizer (S : Set H') = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hcomm : ∀ c : K, φ g * MulAut.conj c = MulAut.conj c * φ g := by
      intro c
      have hc : MulAut.conj c ∈ (MulAut.conj : K →* MulAut K).range :=
        MonoidHom.mem_range.2 ⟨c, rfl⟩
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (hX hc)
      have hsS : s ∈ S := Subgroup.mem_comap.2 (by rw [hs]; exact hc)
      have h2 := congrArg φ (Subgroup.mem_centralizer_iff.1 hg s hsS)
      rw [map_mul, map_mul, hs] at h2
      exact h2.symm
    have hφg : φ g = 1 := eq_one_of_commute_inner hK.1 (φ g) hcomm
    exact hinj (by rw [hφg, map_one])
  have hxS : x ∈ S := Subgroup.mem_comap.2 (by
    rw [hφx]
    exact MonoidHom.mem_range.2 ⟨k, rfl⟩)
  have hQS : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.2 hxS
  have hQne : Subgroup.zpowers x ≠ ⊥ := by
    intro h
    apply hx1
    have hmem := Subgroup.mem_zpowers x
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hQp : IsPGroup 3 ↥(Subgroup.zpowers x) := isPGroup_three_zpowers hx3
  have hL3 : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_odd Nat.prime_three
      (by norm_num)
  have hc := hL3 H' S hSn hSs hSnab hSchev hScent (Subgroup.zpowers x) hQS hQne hQp
  set N : Subgroup H' := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup H') : Set H')
    with hNdef
  have hPX : CFSG.Open.pCoreOf 3 N ≤ N := by
    unfold CFSG.Open.pCoreOf
    exact Subgroup.map_subtype_le _
  have hPn : ((CFSG.Open.pCoreOf 3 N).subgroupOf N).Normal := pCoreOf_subgroupOf_normal 3 N
  have hPp : IsPGroup 3 ↥(CFSG.Open.pCoreOf 3 N) := pCoreOf_isPGroup 3 N
  have hcore : CFSG.Open.GLAPPrimeCoreOf 3 N = ⊥ := by
    have hY3 : Nat.Coprime 3 (Nat.card ↥(CFSG.Open.GLAPPrimeCoreOf 3 N)) :=
      CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf Nat.prime_three N
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    have hcop : Nat.Coprime (Nat.card ↥(CFSG.Open.GLAPPrimeCoreOf 3 N))
        (Nat.card ↥(CFSG.Open.pCoreOf 3 N)) := by
      rw [hn]
      exact Nat.Coprime.pow_right n hY3.symm
    have hdisj : CFSG.Open.GLAPPrimeCoreOf 3 N ⊓ CFSG.Open.pCoreOf 3 N = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hyN : y ∈ N :=
      CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le (p := 3) N hy
    have hyP : y ∈ CFSG.Open.pCoreOf 3 N := by
      refine hc y hyN (fun r hr => ?_)
      have hrN : r ∈ N := hPX hr
      have h1 : y * r * y⁻¹ * r⁻¹ ∈ CFSG.Open.GLAPPrimeCoreOf 3 N := by
        have h0 : r * y⁻¹ * r⁻¹ ∈ CFSG.Open.GLAPPrimeCoreOf 3 N :=
          CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem (p := 3) (C := N) r
            hrN y⁻¹ ((CFSG.Open.GLAPPrimeCoreOf 3 N).inv_mem hy)
        have h4 := (CFSG.Open.GLAPPrimeCoreOf 3 N).mul_mem hy h0
        simpa only [mul_assoc] using h4
      have h2 : y * r * y⁻¹ * r⁻¹ ∈ CFSG.Open.pCoreOf 3 N :=
        (CFSG.Open.pCoreOf 3 N).mul_mem (pCoreOf_conj_mem 3 (C := N) hyN hr)
          ((CFSG.Open.pCoreOf 3 N).inv_mem hr)
      have h3 : y * r * y⁻¹ * r⁻¹ ∈ CFSG.Open.GLAPPrimeCoreOf 3 N ⊓ CFSG.Open.pCoreOf 3 N :=
        ⟨h1, h2⟩
      rw [hdisj, Subgroup.mem_bot] at h3
      calc y * r = (y * r * y⁻¹ * r⁻¹) * (r * y) := by group
        _ = r * y := by rw [h3, one_mul]
    have h5 : y ∈ CFSG.Open.GLAPPrimeCoreOf 3 N ⊓ CFSG.Open.pCoreOf 3 N := ⟨hy, hyP⟩
    rw [hdisj, Subgroup.mem_bot] at h5
    exact h5
  have hnc := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.noComponent_of_pConstrained
    Nat.prime_three hcore hPX hPn hPp hc
  refine ⟨?_, hcore⟩
  show sSup {L : Subgroup H' | CFSG.Open.GLAPComponent 3 N L} = ⊥
  exact sSup_eq_bot.2 fun L hL => (hnc L hL).elim

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input134
