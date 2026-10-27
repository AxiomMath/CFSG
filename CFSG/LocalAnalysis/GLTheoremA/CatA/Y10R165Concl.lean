module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Cases
public import CFSG.GroupTheory.PLayer.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank

@[expose] def Concl165 (K : Type) [Group K] [Finite K] (p q : ℕ) (A : Subgroup K) : Prop :=
  ∃ D E F J : Subgroup K, D ≤ E ∧ E ≤ A ∧ Nat.card D = p ∧ Nat.card E = p ^ 2 ∧
    GLAPComponent p (Subgroup.centralizer (D : Set K)) J ∧
    A ≤ Subgroup.normalizer (J : Set K) ∧
    GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ ∧
    F ≤ Subgroup.centralizer (D : Set K) ∧ IsElemAbelian q F ∧
    F ≤ Subgroup.normalizer (J : Set K) ∧ 3 ≤ CFSG.Open.pRank q F

@[expose] def Concl165Avoid (K : Type) [Group K] [Finite K] (p q : ℕ) (A Z : Subgroup K) : Prop :=
  ∃ D E F J : Subgroup K, D ≤ E ∧ E ≤ A ∧ Nat.card D = p ∧ Nat.card E = p ^ 2 ∧
    GLAPComponent p (Subgroup.centralizer (D : Set K)) J ∧
    A ≤ Subgroup.normalizer (J : Set K) ∧
    GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ ∧
    F ≤ Subgroup.centralizer (D : Set K) ∧ IsElemAbelian q F ∧
    F ≤ Subgroup.normalizer (J : Set K) ∧ 3 ≤ CFSG.Open.pRank q F ∧ F ⊓ Z = ⊥

theorem concl165_map_of_central {H K : Type} [Group H] [Finite H] [Group K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (π : H →* K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) (hpk : ¬ p ∣ Nat.card π.ker) {A : Subgroup H}
    (h : Concl165Avoid H p q A π.ker) : Concl165 K p q (A.map π) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ := h
  have hDp : IsPGroup p D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 2) (by simpa using hE)
  have hmem_cent : ∀ {Q : Subgroup H}, IsPGroup p Q → ∀ {g : H},
      π g ∈ Subgroup.centralizer ((Q.map π : Subgroup K) : Set K) →
      g ∈ Subgroup.centralizer (Q : Set H) := by
    intro Q hQ g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro q hq
    have hcomm : π q * π g = π g * π q := hg (π q) (Subgroup.mem_map_of_mem π hq)
    set z : H := g * q * g⁻¹ * q⁻¹ with hzdef
    have hzker : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hzdef]
      calc π (g * q * g⁻¹ * q⁻¹) = π g * π q * (π g)⁻¹ * (π q)⁻¹ := by simp
        _ = π q * π g * (π g)⁻¹ * (π q)⁻¹ := by rw [← hcomm]
        _ = 1 := by group
    have hzcen : z ∈ Subgroup.center H := hker hzker
    have hzq : z * q = g * q * g⁻¹ := by rw [hzdef]; group
    have hsem : SemiconjBy g q (z * q) := by
      show g * q = (z * q) * g
      rw [hzq]; group
    have hord : orderOf (z * q) = orderOf q := (SemiconjBy.orderOf_eq g hsem).symm
    have hcop : Nat.Coprime (orderOf z) (orderOf q) := by
      have hzk : orderOf z ∣ Nat.card π.ker := by
        have := orderOf_dvd_natCard (⟨z, hzker⟩ : ↥π.ker)
        simpa [Subgroup.orderOf_mk] using this
      have hzp : Nat.Coprime (orderOf z) p :=
        ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hpk (hdvd.trans hzk)).symm
      obtain ⟨k, hk⟩ := hQ.exists_orderOf_dvd_pow (⟨q, hq⟩ : ↥Q)
      have hk' : orderOf q ∣ p ^ k := by simpa [Subgroup.orderOf_mk] using hk
      exact (Nat.Coprime.pow_right k hzp).coprime_dvd_right hk'
    have hcomm_zq : Commute z q := (Subgroup.mem_center_iff.mp hzcen q).symm
    have hordmul : orderOf z * orderOf q = orderOf q := by
      rw [← hcomm_zq.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord]
    have hz1 : z = 1 := by
      have hzo : orderOf z = 1 :=
        mul_right_cancel₀ (orderOf_pos q).ne' (by simpa using hordmul)
      exact orderOf_eq_one_iff.mp hzo
    have hgq : g * q = q * g := by
      rw [hz1, one_mul] at hzq
      calc g * q = (g * q * g⁻¹) * g := by group
        _ = q * g := by rw [← hzq]
    exact hgq.symm
  have hcent : ∀ Q : Subgroup H, IsPGroup p Q →
      Subgroup.centralizer ((Q.map π : Subgroup K) : Set K) =
        (Subgroup.centralizer (Q : Set H)).map π := by
    intro Q hQ
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨g, rfl⟩ := hπ x
      exact Subgroup.mem_map_of_mem π (hmem_cent hQ hx)
    · simpa only [Subgroup.coe_map] using
        Subgroup.map_centralizer_le_centralizer_image (Q : Set H) π
  have hDcard : Nat.card (D.map π) = p := by
    rw [CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot π D
      (CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpk hDp), hD]
  have hEcard : Nat.card (E.map π) = p ^ 2 := by
    rw [CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot π E
      (CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpk hEp), hE]
  have hJ' : GLAPComponent p (Subgroup.centralizer ((D.map π : Subgroup K) : Set K))
      (J.map π) := by
    have hcop : Nat.Coprime p (Nat.card ↥(Subgroup.centralizer (D : Set H) ⊓ π.ker)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    have h1 := glaPComponent_map hp π hcop hJ
    rwa [← hcent D hDp] at h1
  have hmapinf : (J ⊓ Subgroup.centralizer (E : Set H)).map π =
      J.map π ⊓ Subgroup.centralizer ((E.map π : Subgroup K) : Set K) := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.map_inf_le _ _ π).trans (le_inf inf_le_left ?_)
      refine inf_le_right.trans ?_
      simpa only [Subgroup.coe_map] using
        Subgroup.map_centralizer_le_centralizer_image (E : Set H) π
    · rintro x ⟨hxJ, hxE⟩
      obtain ⟨g, hgJ, rfl⟩ := Subgroup.mem_map.mp hxJ
      exact Subgroup.mem_map_of_mem π ⟨hgJ, hmem_cent hEp hxE⟩
  have hlay' : GLAPLayer p (J.map π ⊓
      Subgroup.centralizer ((E.map π : Subgroup K) : Set K)) ≠ ⊥ := by
    rw [← hmapinf]
    have hcop : Nat.Coprime p
        (Nat.card ↥((J ⊓ Subgroup.centralizer (E : Set H)) ⊓ π.ker)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    exact (glaPLayer_ne_bot_iff_map_ne_bot_of_coprime_ker hp π hcop).1 hlay
  have hAJ' : A.map π ≤ Subgroup.normalizer ((J.map π : Subgroup K) : Set K) :=
    (Subgroup.map_mono hAJ).trans (Subgroup.le_normalizer_map π)
  have hFD' : F.map π ≤ Subgroup.centralizer ((D.map π : Subgroup K) : Set K) := by
    refine (Subgroup.map_mono hFD).trans ?_
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (D : Set H) π
  have hFJ' : F.map π ≤ Subgroup.normalizer ((J.map π : Subgroup K) : Set K) :=
    (Subgroup.map_mono hFJ).trans (Subgroup.le_normalizer_map π)
  have hF3' : 3 ≤ CFSG.Open.pRank q (F.map π) := by
    have hinj : Function.Injective (π.comp F.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : ((x : H)) ∈ F ⊓ π.ker := ⟨x.2, hx⟩
      rw [hFZ, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have htop : (⊤ : Subgroup F).map (π.comp F.subtype) = F.map π := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have hrank : CFSG.Open.pRank q (F.map π) = CFSG.Open.pRank q F := by
      rw [← htop, pRank_eq_pRank_top_subgroup F]
      exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt
        (π.comp F.subtype) hinj ⊤
    rwa [hrank]
  exact ⟨D.map π, E.map π, F.map π, J.map π, Subgroup.map_mono hDE,
    Subgroup.map_mono hEA, hDcard, hEcard, hJ', hAJ', hlay', hFD',
    CFSG.SectionRank.isElemAbelian_map hF π, hFJ', hF3'⟩

theorem concl165_of_mulEquiv {K R : Type} [Group K] [Finite K] [Group R] [Finite R]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : K ≃* R) {A : Subgroup K}
    (h : Concl165 R p q (A.map e.toMonoidHom)) : Concl165 K p q A := by
  obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3⟩ := h
  have h' : Concl165Avoid R p q (A.map e.toMonoidHom) ⊥ :=
    ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, by simp⟩
  have hker : (e.symm.toMonoidHom).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.symm.injective
  have hker_le : (e.symm.toMonoidHom).ker ≤ Subgroup.center R := by rw [hker]; exact bot_le
  have hpk : ¬ p ∣ Nat.card (e.symm.toMonoidHom).ker := by
    rw [hker, Subgroup.card_bot]
    exact Nat.Prime.not_dvd_one hp
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
    ext x; simp
  have h'' : Concl165Avoid R p q (A.map e.toMonoidHom) e.symm.toMonoidHom.ker := by
    rw [hker]
    exact h'
  have key := concl165_map_of_central hp hq e.symm.toMonoidHom e.symm.surjective hker_le hpk h''
  simpa [Subgroup.map_map, hcomp] using key

theorem i165On_of_cover {P : GLALabel → ℕ → Prop}
    (hcov : ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p q : ℕ),
      HasLabel K (fun l : GLALabel => l = lab) → P lab p →
      p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
      evenRank K = GLATwoLocalRank q K → 4 ≤ evenRank K →
      ∃ (H : Type) (_ : Group H) (_ : Finite H) (π : H →* K),
        Function.Surjective π ∧ π.ker ≤ Subgroup.center H ∧ ¬ p ∣ Nat.card π.ker ∧
        ∀ Ã : Subgroup H, IsElemAbelian p Ã →
          CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p Ã →
          3 ≤ CFSG.Open.pRank p Ã → Concl165Avoid H p q Ã π.ker) :
    I165On P := by
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  have hm3 : 3 ≤ CFSG.Open.pRank p A := by omega
  have hm4K : 4 ≤ evenRank K := le_trans hm4 hm1
  obtain ⟨H, hHgrp, hHfin, π, hπ, hker, hpk, hconcl⟩ :=
    hcov K lab p q hK hP hp hp2 hq hq2 hqp hns he hm4K
  letI := hHgrp
  letI := hHfin
  obtain ⟨R, -, hRe, hRmap, -⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift hp hpk
      (Subgroup.map_comap_eq_self_of_surjective hπ A) hAe
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.pRank_quotient_eq π.ker hpk
  have hiso : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hRankH : CFSG.Open.pRank p (⊤ : Subgroup H) =
      CFSG.Open.pRank p (⊤ : Subgroup K) := hquot.symm.trans hiso
  have hRankR : CFSG.Open.pRank p R = CFSG.Open.pRank p A := by
    have hRp : IsPGroup p R :=
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.isPGroup_of_pow_eq_one hRe.2
    have hinj : Function.Injective (π.comp R.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : ((x : H)) ∈ R ⊓ π.ker := ⟨x.2, hx⟩
      rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpk hRp,
        Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have htop : (⊤ : Subgroup R).map (π.comp R.subtype) = R.map π := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hRmap, ← htop, pRank_eq_pRank_top_subgroup R]
    exact (CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (π.comp R.subtype) hinj ⊤).symm
  have hRmax : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p R := by
    rw [hRankH, hRankR]
    exact hmax
  have hR3 : 3 ≤ CFSG.Open.pRank p R := by
    rw [hRankR]
    exact hm3
  have hA' : Concl165 K p q (R.map π) :=
    concl165_map_of_central hp hq π hπ hker hpk (hconcl R hRe hRmax hR3)
  rw [hRmap] at hA'
  simpa only [Concl165] using hA'

theorem i165On_of_model {P : GLALabel → ℕ → Prop}
    (hmodel : ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p q : ℕ),
      HasLabel K (fun l : GLALabel => l = lab) → P lab p →
      p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
      evenRank K = GLATwoLocalRank q K → 4 ≤ evenRank K →
      ∀ A : Subgroup K, IsElemAbelian p A →
        CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A →
        3 ≤ CFSG.Open.pRank p A → Concl165 K p q A) : I165On P := by
  refine i165On_of_cover ?_
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns he hm4
  refine ⟨K, inferInstance, inferInstance, MonoidHom.id K, Function.surjective_id, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact bot_le
  · rw [MonoidHom.ker_id, Subgroup.card_bot]
    exact Nat.Prime.not_dvd_one hp
  · intro A hAe hmax hA3
    obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3⟩ :=
      hmodel K lab p q hK hP hp hp2 hq hq2 hqp hns he hm4 A hAe hmax hA3
    refine ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, ?_⟩
    rw [MonoidHom.ker_id]
    exact inf_bot_eq F

end CFSG.LocalAnalysis.GLTheoremA.Y10F
