module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ChainHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.CentralizerDFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Goldschmidt75.Closure

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private theorem mem_or_mul_mem_of_mem_sup_zpowers {F : Subgroup G} {t x : G}
    (ht : t * t = 1) (htF : Subgroup.zpowers t ≤ normalizer (F : Set G))
    (hx : x ∈ F ⊔ Subgroup.zpowers t) : x ∈ F ∨ x * t ∈ F := by
  have hx' : x ∈ (↑(F ⊔ Subgroup.zpowers t) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left F (Subgroup.zpowers t) htF] at hx'
  obtain ⟨f, hf, w, hw, rfl⟩ := hx'
  rcases (CFSG.EvenSporadicStandard.Fin76b.mem_zpowers_iff_two ht w).1 hw with rfl | rfl
  · left
    simpa using hf
  · right
    simpa [mul_assoc, ht] using hf

theorem ChainHyp.exists_fix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {F : Subgroup G}
    (hF : ChainHyp L A D t F) {Y : Subgroup G} (hYC : Y ≤ centralizer (D : Set G))
    (hY : IsPGroup 2 Y) (hFY : F ≤ Y) (hYF : ¬ Y ≤ F) :
    ∃ p ∈ centralizer (D : Set G), p ∈ normalizer (F : Set G) ∧ p ∉ F ∧
      p⁻¹ * (t * p * t⁻¹) ∈ F := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : t * t = 1 := H.t_sq
  have htinv : t⁻¹ = t := H.t_inv
  have hDC : D ≤ centralizer (D : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hD.comm y hy x hx
  have htC : t ∉ centralizer (D : Set G) := by
    intro htC
    have hDt : D ≤ centralizer ({t} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)
    have hDAa : D ≤ Aa := by
      rw [← H.centralizer_D_inf_centralizer_t W W2 hD]
      exact le_inf hDC hDt
    have hcard := Subgroup.card_le_of_le hDAa
    rw [hD.card, W2.Aa_card] at hcard
    norm_num at hcard
  have htFN : t ∈ normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hF.conj_t_mem x, fun hx => by
      have h2 := hF.conj_t_mem (t * x * t⁻¹) hx
      have h3 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [ht]; group
      rwa [h3] at h2⟩
  have hztF : Subgroup.zpowers t ≤ normalizer (F : Set G) := Subgroup.zpowers_le.mpr htFN
  let N : Subgroup G := centralizer (D : Set G) ⊓ normalizer (F : Set G)
  have hFN : F ≤ N := le_inf hF.le_centralizer Subgroup.le_normalizer
  have hconjC : ∀ x ∈ centralizer (D : Set G), t * x * t⁻¹ ∈ centralizer (D : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : t⁻¹ * d * t ∈ D := by
      have hmem : t⁻¹ ∈ normalizer ((W5 A t : Subgroup G) : Set G) := by
        rw [htinv]
        exact H.t_mem_normalizer W W2 hD
      simpa using hD.norm t⁻¹ hmem d hd
    have hx' : (t⁻¹ * d * t) * x = x * (t⁻¹ * d * t) :=
      mem_centralizer_iff.1 hx (t⁻¹ * d * t) hd'
    calc d * (t * x * t⁻¹) = t * ((t⁻¹ * d * t) * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * d * t)) * t⁻¹ := by rw [hx']
      _ = (t * x * t⁻¹) * d := by group
  have hFmap : F.map (MulAut.conj t : G →* G) = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htFN
  have hCmap : (centralizer (D : Set G)).map (MulAut.conj t : G →* G) =
      centralizer (D : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro - ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hconjC x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hNFmap : (normalizer (F : Set G)).map (MulAut.conj t : G →* G) =
      normalizer (F : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective (F : Subgroup G)
      (f := (MulAut.conj t : G →* G)) (MulAut.conj t).bijective, hFmap]
  have hNmap : N.map (MulAut.conj t : G →* G) = N := by
    show (centralizer (D : Set G) ⊓ normalizer (F : Set G)).map (MulAut.conj t : G →* G) = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hCmap, hNFmap]
  obtain ⟨P, hPsylow, hPt⟩ :=
    CFSG.GroupTheory.exists_conj_invariant_sylow H.sq_t (by simpa using hNmap)
  have hPp : IsPGroup 2 P := hPsylow.isPGroup
  have hPN : P ≤ N := hPsylow.le
  have hPnormF : P ≤ normalizer (F : Set G) := fun x hx => (Subgroup.mem_inf.mp (hPN hx)).2
  have hFp : IsPGroup 2 F := hF.pgroup W
  have hQp : IsPGroup 2 (P ⊔ F : Subgroup G) := IsPGroup.to_sup_of_normal_right' hPp hFp hPnormF
  have hQN : P ⊔ F ≤ N := sup_le hPN hFN
  have hQeq : P ⊔ F = P := hPsylow.eq_of_le le_sup_left hQN hQp
  have hFP : F ≤ P := hQeq ▸ le_sup_right
  have hFPne : F ≠ P := by
    intro hEq
    have hFsylow : IsSylowOf 2 F N := hEq.symm ▸ hPsylow
    have hne : F ≠ Y := fun h => hYF (le_of_eq h.symm)
    have hlt : F < Y := lt_of_le_of_ne hFY hne
    obtain ⟨y, hy, hyF⟩ :=
      SetLike.exists_of_lt (CFSG.Goldschmidt75.lt_inf_normalizer (p := 2) hY hlt)
    have hyY : y ∈ Y := hy.1
    have hyN : y ∈ normalizer (F : Set G) := hy.2
    have hzy : IsPGroup 2 (Subgroup.zpowers y) := hY.to_le (Subgroup.zpowers_le.mpr hyY)
    have hzyN : Subgroup.zpowers y ≤ normalizer (F : Set G) := Subgroup.zpowers_le.mpr hyN
    have hQ2p : IsPGroup 2 (F ⊔ Subgroup.zpowers y : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hFp hzy hzyN
    have hQ2N : F ⊔ Subgroup.zpowers y ≤ N :=
      sup_le hFN (le_inf (Subgroup.zpowers_le.mpr (hYC hyY)) hzyN)
    have hQ2eq : F ⊔ Subgroup.zpowers y = F :=
      hFsylow.eq_of_le le_sup_left hQ2N hQ2p
    exact hyF (hQ2eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have htPN : t ∈ normalizer (P : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPt
  have hzt : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, H.order_two, pow_one]
  have hP'p : IsPGroup 2 (P ⊔ Subgroup.zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hPp hzt (Subgroup.zpowers_le.mpr htPN)
  have hF'p : IsPGroup 2 (F ⊔ Subgroup.zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hFp hzt hztF
  have hF'leP' : F ⊔ Subgroup.zpowers t ≤ P ⊔ Subgroup.zpowers t :=
    sup_le (le_trans hFP le_sup_left) le_sup_right
  have hF'C : (F ⊔ Subgroup.zpowers t) ⊓ centralizer (D : Set G) = F := by
    refine le_antisymm ?_ (le_inf le_sup_left hF.le_centralizer)
    rintro x ⟨hx, hxC⟩
    rcases mem_or_mul_mem_of_mem_sup_zpowers ht hztF hx with h | h
    · exact h
    · exfalso
      have htC' : t ∈ centralizer (D : Set G) := by
        have hmem : x⁻¹ * (x * t) ∈ centralizer (D : Set G) :=
          (centralizer (D : Set G)).mul_mem ((centralizer (D : Set G)).inv_mem hxC)
            (hF.le_centralizer h)
        rwa [inv_mul_cancel_left] at hmem
      exact htC htC'
  have hF'neP' : F ⊔ Subgroup.zpowers t ≠ P ⊔ Subgroup.zpowers t := by
    intro hEq
    have hle : P ≤ F ⊔ Subgroup.zpowers t := by
      rw [hEq]
      exact le_sup_left
    have hPC : P ≤ centralizer (D : Set G) := fun x hx => (Subgroup.mem_inf.mp (hPN hx)).1
    have hPF : P ≤ F := fun x hx => by
      have hx' : x ∈ (F ⊔ Subgroup.zpowers t) ⊓ centralizer (D : Set G) :=
        ⟨hle hx, hPC hx⟩
      rwa [hF'C] at hx'
    exact hFPne (le_antisymm hFP hPF)
  have hF'ltP' : F ⊔ Subgroup.zpowers t < P ⊔ Subgroup.zpowers t :=
    lt_of_le_of_ne hF'leP' hF'neP'
  obtain ⟨z, hzP', hzF'⟩ :=
    SetLike.exists_of_lt (CFSG.Goldschmidt75.lt_inf_normalizer (p := 2) hP'p hF'ltP')
  have hzp : z ∈ P ⊔ Subgroup.zpowers t := hzP'.1
  have hzN : z ∈ normalizer ((F ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := hzP'.2
  have hz_or : z ∈ P ∨ z * t ∈ P :=
    mem_or_mul_mem_of_mem_sup_zpowers ht (Subgroup.zpowers_le.mpr htPN) hzp
  set p : G := if z ∈ P then z else z * t with hpdef
  have hpP : p ∈ P := by
    by_cases hz : z ∈ P
    · rw [hpdef, if_pos hz]
      exact hz
    · rw [hpdef, if_neg hz]
      exact hz_or.resolve_left hz
  have hpC : p ∈ centralizer (D : Set G) := (Subgroup.mem_inf.mp (hPN hpP)).1
  have hpNF : p ∈ normalizer (F : Set G) := (Subgroup.mem_inf.mp (hPN hpP)).2
  have htF' : t ∈ F ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hpNF' : p ∈ normalizer ((F ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    have htNF' : t ∈ normalizer ((F ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
      Subgroup.le_normalizer htF'
    by_cases hz : z ∈ P
    · rw [hpdef, if_pos hz]
      exact hzN
    · rw [hpdef, if_neg hz]
      exact (normalizer _).mul_mem hzN htNF'
  have hpF : p ∉ F := by
    by_cases hz : z ∈ P
    · rw [hpdef, if_pos hz]
      exact fun h => hzF' (Subgroup.mem_sup_left h)
    · rw [hpdef, if_neg hz]
      intro hztF
      apply hzF'
      have hmem : (z * t) * t ∈ F ⊔ Subgroup.zpowers t :=
        (F ⊔ Subgroup.zpowers t).mul_mem (Subgroup.mem_sup_left hztF) htF'
      rwa [mul_assoc, ht, mul_one] at hmem
  have hptpF' : p * t * p⁻¹ ∈ F ⊔ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.1 hpNF' t).1 htF'
  have hptpF : p * t * p⁻¹ ∉ F := by
    intro hmem
    have hmemC : p * t * p⁻¹ ∈ centralizer (D : Set G) := hF.le_centralizer hmem
    have htC' : t ∈ centralizer (D : Set G) := by
      have hconj : p⁻¹ * (p * t * p⁻¹) * p ∈ centralizer (D : Set G) :=
        (centralizer (D : Set G)).mul_mem
          ((centralizer (D : Set G)).mul_mem ((centralizer (D : Set G)).inv_mem hpC) hmemC)
          hpC
      rwa [show p⁻¹ * (p * t * p⁻¹) * p = t by group] at hconj
    exact htC htC'
  have hfF : (p * t * p⁻¹) * t ∈ F :=
    (mem_or_mul_mem_of_mem_sup_zpowers ht hztF hptpF').resolve_left hptpF
  have hEq : p⁻¹ * (t * p * t⁻¹) = (p⁻¹ * ((p * t * p⁻¹) * t) * p)⁻¹ := by
    rw [htinv]
    simp only [mul_inv_rev, inv_inv]
    rw [htinv]
    group
  refine ⟨p, hpC, hpNF, hpF, ?_⟩
  have hconjF : p⁻¹ * ((p * t * p⁻¹) * t) * p ∈ F := by
    have hpNF' : p⁻¹ ∈ normalizer (F : Set G) := (normalizer (F : Set G)).inv_mem hpNF
    simpa using (Subgroup.mem_normalizer_iff.1 hpNF' ((p * t * p⁻¹) * t)).1 hfF
  rw [hEq]
  exact F.inv_mem hconjF

theorem ChainHyp.exists_isLayer_commutator (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {F : Subgroup G} (hF : ChainHyp L A D t F) {p : G} (hpC : p ∈ centralizer (D : Set G))
    (hpF : p ∉ F) (hfp : p⁻¹ * (t * p * t⁻¹) ∈ F) :
    ∃ (Ft It : Subgroup G) (κ : G → G), (∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g) ∧
      (∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1) ∧ IsLayer L A Ft It κ := by
  classical
  have ht : t * t = 1 := H.t_sq
  have htinv : t⁻¹ = t := H.t_inv
  let φ : ↥F →* G :=
    { toFun := fun f => (f : G)⁻¹ * (t * (f : G) * t⁻¹)
      map_one' := by simp
      map_mul' := fun f g => by
        have hA : (f : G)⁻¹ * (t * (f : G) * t⁻¹) ∈ F :=
          F.mul_mem (F.inv_mem f.2) (hF.conj_t_mem f f.2)
        have hB : (g : G)⁻¹ ∈ F := F.inv_mem g.2
        calc ((f * g : ↥F) : G)⁻¹ * (t * ((f * g : ↥F) : G) * t⁻¹)
            = ((g : G)⁻¹ * ((f : G)⁻¹ * (t * (f : G) * t⁻¹))) *
                (t * (g : G) * t⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = (((f : G)⁻¹ * (t * (f : G) * t⁻¹)) * (g : G)⁻¹) *
                (t * (g : G) * t⁻¹) := by rw [hF.comm (g : G)⁻¹ hB _ hA]
          _ = ((f : G)⁻¹ * (t * (f : G) * t⁻¹)) *
                ((g : G)⁻¹ * (t * (g : G) * t⁻¹)) := by group }
  have hφ_apply : ∀ f : ↥F, φ f = (f : G)⁻¹ * (t * (f : G) * t⁻¹) := fun _ => rfl
  let Ft : Subgroup G := φ.range
  have hFt_mem : ∀ g, g ∈ Ft ↔ ∃ f ∈ F, f⁻¹ * (t * f * t⁻¹) = g := by
    intro g
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f.1, f.2, hf⟩
    · rintro ⟨f, hfF, rfl⟩
      exact ⟨⟨f, hfF⟩, rfl⟩
  have hFC : F ⊓ centralizer ({t} : Set G) = Aa := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxF, hxt⟩
      have hx : x ∈ centralizer (D : Set G) ⊓ centralizer ({t} : Set G) :=
        ⟨hF.le_centralizer hxF, hxt⟩
      rwa [H.centralizer_D_inf_centralizer_t W W2 hD] at hx
    · intro x hx
      exact ⟨hF.D_le (hD.Aa_le hx),
        mem_centralizer_singleton_iff.2
          (H.comm_of_mem_L (W.B_le (W2.Aa_le hx))).symm⟩
  have hkermap : φ.ker.map F.subtype = Aa := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      have hf1 : (f : G)⁻¹ * (t * (f : G) * t⁻¹) = 1 := MonoidHom.mem_ker.1 hf
      have htf : t * (f : G) * t⁻¹ = (f : G) := by
        have h := congrArg (fun y => (f : G) * y) hf1
        simpa [mul_assoc] using h
      have hft : (f : G) * t = t * (f : G) := by
        calc (f : G) * t = ((t * (f : G) * t⁻¹) * t) := by rw [htf]
          _ = t * (f : G) := by
            rw [htinv]
            calc t * (f : G) * t * t = t * (f : G) * (t * t) := by group
              _ = t * (f : G) := by rw [ht, mul_one]
      have hmem : (f : G) ∈ F ⊓ centralizer ({t} : Set G) :=
        ⟨f.2, mem_centralizer_singleton_iff.2 hft⟩
      rw [← hFC]
      exact hmem
    · intro hx
      have hAaF : x ∈ F := hF.D_le (hD.Aa_le hx)
      refine ⟨⟨x, hAaF⟩, ?_, rfl⟩
      have htx : t * x * t⁻¹ = x := by
        rw [H.comm_of_mem_L (W.B_le (W2.Aa_le hx))]
        group
      show x⁻¹ * (t * x * t⁻¹) = 1
      rw [htx, inv_mul_cancel]
  have hcardF : Nat.card F = Nat.card Ft * Nat.card Aa := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (↥F ⧸ φ.ker) = Nat.card Ft :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = Nat.card Aa := by
      rw [← hkermap, Subgroup.card_map_of_injective F.subtype_injective]
    rw [h2, h3] at h1
    exact h1
  let ν : ↥F →* G :=
    { toFun := fun f => (f : G) * (t * (f : G) * t⁻¹)
      map_one' := by simp
      map_mul' := fun f g => by
        have hA : t * (f : G) * t⁻¹ ∈ F := hF.conj_t_mem f f.2
        have hcomm : (g : G) * (t * (f : G) * t⁻¹) = (t * (f : G) * t⁻¹) * (g : G) :=
          hF.comm (g : G) g.2 _ hA
        simp only [Subgroup.coe_mul]
        rw [show (f : G) * (g : G) * (t * ((f : G) * (g : G)) * t⁻¹) =
          (f : G) * ((g : G) * (t * (f : G) * t⁻¹)) * (t * (g : G) * t⁻¹) by group,
          hcomm]
        group }
  let It : Subgroup G := ν.ker.map F.subtype
  have hIt_mem : ∀ g, g ∈ It ↔ g ∈ F ∧ g * (t * g * t⁻¹) = 1 := by
    intro g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.2, MonoidHom.mem_ker.1 hf⟩
    · rintro ⟨hgF, hg⟩
      exact ⟨⟨g, hgF⟩, hg, rfl⟩
  have hIt_le_F : It ≤ F := fun x hx => ((hIt_mem x).1 hx).1
  have hcardIt : Nat.card It = Nat.card ν.ker :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hAle : A ≤ ν.range := by
    intro a ha
    obtain ⟨v, hv, hvA⟩ := H.thV_surj W W2 hD hsq a ha
    exact ⟨⟨v, hF.D_le hv.1⟩, by simpa [ν, thV] using hvA⟩
  have hcardFν : Nat.card F = Nat.card ν.range * Nat.card It := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ν.ker
    have h2 : Nat.card (↥F ⧸ ν.ker) = Nat.card ν.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ν).toEquiv
    rw [h2, ← hcardIt] at h1
    exact h1
  have h16 : 16 * Nat.card It ≤ Nat.card F := by
    rw [hcardFν]
    calc 16 * Nat.card It = Nat.card A * Nat.card It := by rw [W.A_card]
      _ ≤ Nat.card ν.range * Nat.card It :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hAle)
  have hFt_le_F : Ft ≤ F := by
    intro x hx
    obtain ⟨f, hfF, rfl⟩ := (hFt_mem x).1 hx
    exact F.mul_mem (F.inv_mem hfF) (hF.conj_t_mem f hfF)
  have hFt_le_It : Ft ≤ It := by
    intro x hx
    obtain ⟨f, hfF, rfl⟩ := (hFt_mem x).1 hx
    refine (hIt_mem _).2 ⟨F.mul_mem (F.inv_mem hfF) (hF.conj_t_mem f hfF), ?_⟩
    rw [H.t_conj_efix, mul_inv_cancel]
  have hcomm_nt : ∀ n ∈ L ⊓ normalizer (A : Set G), n * t * n⁻¹ = t := by
    intro n hn
    calc n * t * n⁻¹ = t * n * n⁻¹ := by rw [← H.comm_of_mem_L hn.1]
      _ = t := by group
  have hconj_t : ∀ {n y : G}, n * t * n⁻¹ = t →
      t * (n * y * n⁻¹) * t⁻¹ = n * (t * y * t⁻¹) * n⁻¹ := by
    intro n y hnt
    have h1 : MulAut.conj n t = t := by rw [MulAut.conj_apply]; exact hnt
    have h2 : MulAut.conj n (t * y * t⁻¹) = t * (n * y * n⁻¹) * t⁻¹ := by
      rw [map_mul, map_mul, map_inv, h1, MulAut.conj_apply]
    rw [← h2, MulAut.conj_apply]
  have hFtN : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Ft, n * y * n⁻¹ ∈ Ft := by
    intro n hn y hy
    obtain ⟨f, hfF, rfl⟩ := (hFt_mem y).1 hy
    refine (hFt_mem _).2 ⟨n * f * n⁻¹, hF.conj_mem n hn f hfF, ?_⟩
    have hnt : n * t * n⁻¹ = t := hcomm_nt n hn
    calc (n * f * n⁻¹)⁻¹ * (t * (n * f * n⁻¹) * t⁻¹)
        = (n * f * n⁻¹)⁻¹ * (n * (t * f * t⁻¹) * n⁻¹) := by rw [hconj_t hnt]
      _ = n * (f⁻¹ * (t * f * t⁻¹)) * n⁻¹ := by group
  have hItN : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ It, n * y * n⁻¹ ∈ It := by
    intro n hn y hy
    obtain ⟨hyF, hy1⟩ := (hIt_mem y).1 hy
    refine (hIt_mem _).2 ⟨hF.conj_mem n hn y hyF, ?_⟩
    have hnt : n * t * n⁻¹ = t := hcomm_nt n hn
    calc n * y * n⁻¹ * (t * (n * y * n⁻¹) * t⁻¹)
        = n * y * n⁻¹ * (n * (t * y * t⁻¹) * n⁻¹) := by rw [hconj_t hnt]
      _ = n * (y * (t * y * t⁻¹)) * n⁻¹ := by group
      _ = 1 := by rw [hy1]; group
  have htypeA_F : IsTypeA L A Ft F := by
    have hsup : F ⊔ Ft ≤ F := sup_le le_rfl hFt_le_F
    have h := IsTypeA.sup W hF.typeA (Y'' := Ft) hFtN
      (fun x hx y hy => hF.comm x (hsup hx) y (hsup hy))
    rwa [bot_sup_eq, sup_eq_left.mpr hFt_le_F] at h
  have htypeA_It : IsTypeA L A Ft It := by
    have h := IsTypeA.inf W htypeA_F (Y' := It) hItN
    rwa [inf_eq_left.mpr hFt_le_It, inf_eq_right.mpr hIt_le_F] at h
  let fp : G := p⁻¹ * (t * p * t⁻¹)
  have hfpF : fp ∈ F := hfp
  have hfp_It : fp ∈ It := by
    refine (hIt_mem fp).2 ⟨hfpF, ?_⟩
    rw [H.t_conj_efix, mul_inv_cancel]
  have hfp_notFt : fp ∉ Ft := by
    intro hmem
    obtain ⟨f, hfF, hfeq⟩ := (hFt_mem fp).1 hmem
    have hfpinv : fp * (t * f * t⁻¹)⁻¹ = f⁻¹ := by
      rw [← hfeq]
      group
    have hcomm : t * (p * f⁻¹) * t⁻¹ = p * f⁻¹ := by
      have hX : t * p * t⁻¹ = p * fp := by
        rw [show fp = p⁻¹ * (t * p * t⁻¹) from rfl]
        group
      have hfinv : t * f⁻¹ * t⁻¹ = (t * f * t⁻¹)⁻¹ := by group
      calc t * (p * f⁻¹) * t⁻¹ = (t * p * t⁻¹) * (t * f⁻¹ * t⁻¹) := by group
        _ = (p * fp) * (t * f * t⁻¹)⁻¹ := by rw [hX, hfinv]
        _ = p * (fp * (t * f * t⁻¹)⁻¹) := by group
        _ = p * f⁻¹ := by rw [hfpinv]
    have hC : p * f⁻¹ ∈ centralizer (D : Set G) :=
      (centralizer (D : Set G)).mul_mem hpC (hF.le_centralizer (F.inv_mem hfF))
    have hAa : p * f⁻¹ ∈ Aa := by
      rw [← H.centralizer_D_inf_centralizer_t W W2 hD]
      refine ⟨hC, mem_centralizer_singleton_iff.2 ?_⟩
      calc (p * f⁻¹) * t = (t * (p * f⁻¹) * t⁻¹) * t := by rw [hcomm]
        _ = t * (p * f⁻¹) := by
          rw [htinv]
          calc t * (p * f⁻¹) * t * t = t * (p * f⁻¹) * (t * t) := by group
            _ = t * (p * f⁻¹) := by rw [ht, mul_one]
    have hpF' : p ∈ F := by
      have h1 : (p * f⁻¹) * f ∈ F := F.mul_mem (hF.D_le (hD.Aa_le hAa)) hfF
      simpa [mul_assoc] using h1
    exact hpF hpF'
  have hIt_ne_Ft : It ≠ Ft := fun h => hfp_notFt (h ▸ hfp_It)
  obtain ⟨r, hr⟩ := IsTypeA.exists_card_eq W htypeA_It
  have hFt_lt_It : Nat.card Ft < Nat.card It :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hFt_le_It (Ne.symm hIt_ne_Ft))
  have hrle : r ≤ 1 := by
    have hFpos : 0 < Nat.card Ft := Nat.card_pos
    have h256 : Nat.card F = 256 * Nat.card Ft := by
      rw [hcardF, W2.Aa_card, show (2 : ℕ) ^ 8 = 256 by norm_num]
      exact Nat.mul_comm _ _
    have h : 16 * (16 ^ r * Nat.card Ft) ≤ 256 * Nat.card Ft := by
      calc 16 * (16 ^ r * Nat.card Ft) = 16 * Nat.card It := by rw [hr]
        _ ≤ Nat.card F := h16
        _ = 256 * Nat.card Ft := h256
    have h2 : 16 * 16 ^ r ≤ 256 := by
      refine Nat.le_of_mul_le_mul_right ?_ hFpos
      rwa [← mul_assoc] at h
    have h3 : 16 ^ (r + 1) ≤ 16 ^ 2 := by
      rw [pow_succ, show (16 : ℕ) ^ 2 = 256 by norm_num]
      calc 16 ^ r * 16 = 16 * 16 ^ r := Nat.mul_comm _ _
        _ ≤ 256 := h2
    have h4 : r + 1 ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 16)).1 h3
    omega
  have hrge : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      have hcard : Nat.card It = Nat.card Ft := by rw [hr, h, pow_zero, one_mul]
      exact (ne_of_lt hFt_lt_It) hcard.symm
    · exact h
  have hc : Nat.card It = 16 * Nat.card Ft := by
    have hr1 : r = 1 := by omega
    rw [hr, hr1, pow_one]
  obtain ⟨κ, hκ⟩ := IsTypeA.exists_isLayer_of_card_eq W htypeA_It hc
  exact ⟨Ft, It, κ, hFt_mem, hIt_mem, hκ⟩

end CFSG.EvenSporadicStandard.ThStd

end
