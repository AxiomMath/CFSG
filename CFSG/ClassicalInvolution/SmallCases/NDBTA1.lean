module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dAct
public import CFSG.Goldschmidt75.B1Perfect
public import CFSG.LieType.HighestRoot.SL2Outer

public section

namespace CFSG.ClassicalInvolution.NDB.TA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

section Aut

variable {F : Type*} [Field F] [Finite F]

theorem eq_one_of_commute_conj (h4 : 4 ≤ Nat.card F) (α : MulAut SL(2, F))
    (hα : ∀ y : SL(2, F), α * MulAut.conj y = MulAut.conj y * α) : α = 1 := by
  have hcen : ∀ y : SL(2, F), y⁻¹ * α y ∈ Subgroup.center SL(2, F) := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro x
    have h := DFunLike.congr_fun (hα y) (α⁻¹ x)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self] at h
    calc x * (y⁻¹ * α y) = y⁻¹ * (y * x * y⁻¹) * α y := by group
      _ = y⁻¹ * (α y * x * (α y)⁻¹) * α y := by rw [h]
      _ = y⁻¹ * α y * x := by group
  have hfix : ∀ y₁ y₂ : SL(2, F), α ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆ := by
    intro y₁ y₂
    have e₁ : α y₁ = y₁ * (y₁⁻¹ * α y₁) := by group
    have e₂ : α y₂ = y₂ * (y₂⁻¹ * α y₂) := by group
    set c₁ := y₁⁻¹ * α y₁ with hc₁
    set c₂ := y₂⁻¹ * α y₂ with hc₂
    have k₁ := Subgroup.mem_center_iff.mp (hcen y₁)
    have k₂ := Subgroup.mem_center_iff.mp (hcen y₂)
    rw [map_commutatorElement, e₁, e₂, commutatorElement_def, commutatorElement_def]
    calc y₁ * c₁ * (y₂ * c₂) * (y₁ * c₁)⁻¹ * (y₂ * c₂)⁻¹
        = y₁ * (c₁ * (y₂ * c₂)) * c₁⁻¹ * y₁⁻¹ * c₂⁻¹ * y₂⁻¹ := by group
      _ = y₁ * ((y₂ * c₂) * c₁) * c₁⁻¹ * y₁⁻¹ * c₂⁻¹ * y₂⁻¹ := by rw [← k₁]
      _ = y₁ * y₂ * (c₂ * y₁⁻¹) * c₂⁻¹ * y₂⁻¹ := by group
      _ = y₁ * y₂ * (y₁⁻¹ * c₂) * c₂⁻¹ * y₂⁻¹ := by rw [← k₂]
      _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by group
  have hle : commutator SL(2, F) ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hfix a b
  have htop : commutator SL(2, F) = ⊤ := (sl2_isPerfect h4).commutator_eq_top
  refine MulEquiv.ext fun y => ?_
  have hy : y ∈ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) := hle (htop ▸ Subgroup.mem_top y)
  exact hy

end Aut

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem four_le_card_gf (hq : 5 ≤ p ^ f) : 4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  omega

theorem exists_action {P : Subgroup G} {t : G} (hP : IsClassicalMember p f P t) :
    ∃ ρ : Subgroup.normalizer (P : Set G) →* MulAut SL(2, GaloisField p f),
      ∀ g, ρ g = 1 → (g : G) ∈ trivialOnQuot P := by
  obtain ⟨e⟩ : Nonempty (P ⧸ CFSG.oddCore P ≃* SL(2, GaloisField p f)) := hP.nonempty_equiv
  refine ⟨(WC.autCongr e).comp (Q3.tl3Act P), fun g hg => ?_⟩
  rw [MonoidHom.comp_apply, WC.autCongr_eq_one_iff] at hg
  exact ⟨g.2, (Q3.tl3Act_eq_one_iff P g).mp hg⟩

theorem mem_trivialOnQuot_of_sl2_cent (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {P : Subgroup G} {t z : G}
    (hP : IsClassicalMember p f P t) (hz2 : z * z = 1)
    (htC : t ∈ Subgroup.centralizer ({z} : Set G))
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (P : Set G))
    (σ : SL(2, GaloisField p f) →* OddQuot z)
    (hσt : ∀ a, σ a * oddQuotMk z ⟨t, htC⟩ = oddQuotMk z ⟨t, htC⟩ * σ a)
    (hσz : oddQuotMk z ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ σ.range) :
    z ∈ trivialOnQuot P := by
  classical
  have hF : Odd (Nat.card (GaloisField p f)) := WC.odd_card_galoisField hp2 hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_card_gf hq
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set O : Subgroup ↥C := componentClassificationOddCore ↥C with hO
  set π : ↥C →* OddQuot z := oddQuotMk z with hπ
  have hOodd : Odd (Nat.card O) := OddCore.odd_card ↥C
  set tC : ↥C := ⟨t, htC⟩ with htCdef
  set zC : ↥C := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hzCdef
  have ht2 : t * t = 1 := (isCentralInvolution_of_isClassicalMember hP).sq
  have htz : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
  have hzN : z ∈ Subgroup.normalizer (P : Set G) :=
    hCt (Subgroup.mem_centralizer_singleton_iff.mpr htz)
  set T : Subgroup ↥C := Subgroup.zpowers tC with hT
  have hT2 : IsPGroup 2 ↥T := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext ht2
    · intro h
      apply (isCentralInvolution_of_isClassicalMember hP).ne_one
      exact congrArg Subtype.val h
  have : Fact (IsPGroup 2 ↥T) := ⟨hT2⟩
  have hcop : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr hOodd
  have hkey := CFSG.centralizer_map_quotient_eq_map_centralizer 2 T O inferInstance hcop
  have hσC : σ.range ≤ (Subgroup.centralizer (T : Set ↥C)).map π := by
    rintro _ ⟨a, rfl⟩
    have hmem : σ a ∈ Subgroup.centralizer ((T.map (QuotientGroup.mk' O) : Subgroup (OddQuot z)) :
        Set (OddQuot z)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have hc : Commute (σ a) (π tC) := hσt a
      have e : (QuotientGroup.mk' O) (tC ^ k) = π tC ^ k := by
        rw [map_zpow]
        rfl
      rw [e]
      exact (hc.zpow_right k).eq.symm
    exact hkey ▸ hmem
  set D₁ : Subgroup ↥C := Subgroup.centralizer (T : Set ↥C) ⊓ σ.range.comap π with hD₁
  have hD₁map : D₁.map π = σ.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨d, ⟨-, hd⟩, rfl⟩
      exact hd
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := hσC hx
      exact ⟨c, ⟨hc, hx⟩, rfl⟩
  have hσperf : ⁅σ.range, σ.range⁆ = σ.range := by
    have htop : ⁅(⊤ : Subgroup SL(2, GaloisField p f)), (⊤ : Subgroup SL(2, GaloisField p f))⁆ =
        ⊤ := by
      rw [← commutator_def]
      exact (sl2_isPerfect h4).commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  set D : Subgroup ↥C := Goldschmidt75.perfRes D₁ with hD
  have hDmap : D.map π = σ.range := by
    rw [hD, Goldschmidt75.map_perfRes, hD₁map]
    exact le_antisymm (Goldschmidt75.perfRes_le _) (Goldschmidt75.le_perfRes le_rfl hσperf)
  have hDperf : ⁅D, D⁆ = D := Goldschmidt75.commutator_perfRes D₁
  have hDT : D ≤ Subgroup.centralizer (T : Set ↥C) :=
    (Goldschmidt75.perfRes_le D₁).trans inf_le_left
  have hDN : ∀ d ∈ D, ((d : ↥C) : G) ∈ Subgroup.normalizer (P : Set G) := by
    intro d hd
    apply hCt
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.mp (hDT hd) tC (Subgroup.mem_zpowers tC)
    exact (congrArg Subtype.val h).symm
  obtain ⟨ρ, hρ1⟩ := exists_action hP
  set ι : ↥D →* Subgroup.normalizer (P : Set G) :=
    { toFun := fun d => ⟨((d : ↥C) : G), hDN d d.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  set ρD : ↥D →* MulAut SL(2, GaloisField p f) := ρ.comp ι with hρD
  set I : Subgroup (MulAut SL(2, GaloisField p f)) := ρD.range with hI
  have hIperf : ⁅I, I⁆ = I := by
    rw [hI, MonoidHom.range_eq_map, ← Subgroup.map_commutator, WC.commutator_top_of hDperf]
  set Inn : Subgroup (MulAut SL(2, GaloisField p f)) :=
    (MulAut.conj : SL(2, GaloisField p f) →* MulAut SL(2, GaloisField p f)).range with hInn
  have hIInn : I ≤ Inn := by
    rw [← hIperf, Subgroup.commutator_le]
    intro α _ β _
    obtain ⟨y, hy⟩ := CFSG.ComponentClassification.RankTwoOddLie.sl2OuterComm _ hF α β
    exact ⟨y, by rw [← hy, commutatorElement_def]⟩
  set πD : ↥D →* OddQuot z := π.comp D.subtype with hπD
  set E : Subgroup ↥D := πD.ker with hE
  set K₀ : Subgroup ↥D := ρD.ker with hK₀
  have hπDrange : ∀ d : ↥D, πD d ∈ σ.range := fun d => hDmap ▸ ⟨d, d.2, rfl⟩
  set πD' : ↥D →* ↥σ.range := πD.codRestrict σ.range hπDrange with hπD'
  have hπD'surj : Function.Surjective πD' := by
    rintro ⟨x, hx⟩
    rw [← hDmap] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨⟨d, hd⟩, rfl⟩
  set σ' : SL(2, GaloisField p f) →* ↥σ.range := σ.rangeRestrict with hσ'
  have hσ'surj : Function.Surjective σ' := MonoidHom.rangeRestrict_surjective σ
  set M' : Subgroup ↥σ.range := K₀.map πD' with hM'
  have hM'n : M'.Normal := Subgroup.Normal.map (MonoidHom.normal_ker ρD) πD' hπD'surj
  set S : Subgroup SL(2, GaloisField p f) := M'.comap σ' with hS
  have hSn : S.Normal := Subgroup.Normal.comap hM'n σ'
  have hSidx : S.index = M'.index := Subgroup.index_comap_of_surjective M' hσ'surj
  have hM'idx : M'.index ≤ K₀.index := by
    have hle : K₀ ≤ M'.comap πD' := fun k hk => ⟨k, hk, rfl⟩
    have h1 : (M'.comap πD').index = M'.index := Subgroup.index_comap_of_surjective M' hπD'surj
    rw [← h1]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have hK₀idx : K₀.index = Nat.card I := Subgroup.index_ker ρD
  have hInncard : Nat.card Inn * 2 = Nat.card SL(2, GaloisField p f) :=
    natCard_conj_range_of_equiv_sl2 hF (MulEquiv.refl _)
  have hdich : I = ⊥ ∨ I = Inn := by
    rcases sl2_normal_cases h4 S hSn with hS0 | hS0 | hS0
    · right
      refine Subgroup.eq_of_le_of_card_ge hIInn ?_
      rw [← hK₀idx]
      refine le_trans ?_ hM'idx
      rw [← hSidx, hS0, Subgroup.index_bot]
      omega
    · right
      refine Subgroup.eq_of_le_of_card_ge hIInn ?_
      rw [← hK₀idx]
      refine le_trans ?_ hM'idx
      have h1 := Subgroup.card_mul_index S
      rw [hS0, sl2_natCard_center hF] at h1
      rw [← hSidx, hS0]
      omega
    · left
      have hM'top : M' = ⊤ := by
        rw [← Subgroup.index_eq_one, ← hSidx, hS0, Subgroup.index_top]
      have hIE : I ≤ E.map ρD := by
        rintro _ ⟨d, rfl⟩
        have hd : πD' d ∈ M' := hM'top ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hkd⟩ := hd
        have hkE : k⁻¹ * d ∈ E := by
          rw [hE, MonoidHom.mem_ker, map_mul, map_inv]
          have := congrArg Subtype.val hkd
          simp only [hπD', MonoidHom.codRestrict_apply] at this
          rw [this, inv_mul_cancel]
        refine ⟨k⁻¹ * d, hkE, ?_⟩
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
      have hEodd : Odd (Nat.card E) := by
        have hle : E.map D.subtype ≤ O := by
          rintro _ ⟨e, he, rfl⟩
          have h1 : π (e : ↥C) = 1 := he
          exact (QuotientGroup.eq_one_iff _).mp h1
        have hc : Nat.card (E.map D.subtype) = Nat.card E :=
          Subgroup.card_map_of_injective D.subtype_injective
        rw [← hc]
        exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
      have hIodd : Odd (Nat.card I) :=
        (hEodd.of_dvd_nat (E.card_map_dvd ρD)).of_dvd_nat (Subgroup.card_dvd_of_le hIE)
      exact Goldschmidt75.eq_bot_of_perfect_of_odd hIperf hIodd
  set zN : Subgroup.normalizer (P : Set G) := ⟨z, hzN⟩ with hzNdef
  have hz1 : ρ zN = 1 := by
    rcases hdich with hI0 | hIinn
    ·
      have hzr : π zC ∈ σ.range := hσz
      rw [← hDmap] at hzr
      obtain ⟨d₀, hd₀, hd₀z⟩ := hzr
      set oC : ↥C := d₀⁻¹ * zC with hoC
      have hoO : oC ∈ O := by
        refine (QuotientGroup.eq_one_iff _).mp ?_
        show π (d₀⁻¹ * zC) = 1
        rw [map_mul, map_inv, hd₀z, inv_mul_cancel]
      have hoN : ((oC : ↥C) : G) ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hDN d₀ hd₀)) hzN
      have hsplit : zN = ι ⟨d₀, hd₀⟩ * ⟨((oC : ↥C) : G), hoN⟩ := by
        apply Subtype.ext
        show z = (d₀ : G) * ((d₀ : G)⁻¹ * z)
        group
      have hd₀1 : ρ (ι ⟨d₀, hd₀⟩) = 1 := by
        have : ρD ⟨d₀, hd₀⟩ ∈ I := ⟨⟨d₀, hd₀⟩, rfl⟩
        rw [hI0, Subgroup.mem_bot] at this
        exact this
      have hρz : ρ zN = ρ ⟨((oC : ↥C) : G), hoN⟩ := by
        rw [hsplit, map_mul, hd₀1, one_mul]
      have hodd : Odd (orderOf (ρ zN)) := by
        rw [hρz]
        refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ρ _)
        have h1 : orderOf (⟨((oC : ↥C) : G), hoN⟩ : Subgroup.normalizer (P : Set G)) =
            orderOf oC := by
          rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe oC]
        rw [h1, ← Subgroup.orderOf_mk oC hoO]
        exact hOodd.of_dvd_nat (orderOf_dvd_natCard _)
      have h2 : orderOf (ρ zN) ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, pow_two]
        have : zN * zN = 1 := Subtype.ext hz2
        rw [this, map_one]
      have h1 : orderOf (ρ zN) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      exact orderOf_eq_one_iff.mp h1
    ·
      refine eq_one_of_commute_conj h4 _ fun y => ?_
      have hy : MulAut.conj y ∈ I := hIinn ▸ ⟨y, rfl⟩
      obtain ⟨d, hd⟩ := hy
      rw [← hd]
      show ρ zN * ρ (ι d) = ρ (ι d) * ρ zN
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show z * ((d : ↥C) : G) = ((d : ↥C) : G) * z
      exact (Subgroup.mem_centralizer_singleton_iff.mp (d : ↥C).2).symm
  exact hρ1 zN hz1

end CFSG.ClassicalInvolution.NDB.TA
