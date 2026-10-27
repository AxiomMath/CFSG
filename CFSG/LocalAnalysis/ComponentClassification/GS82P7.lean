module

public import CFSG.LocalAnalysis.ComponentClassification.GS82P10

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P7

open CFSG Subgroup

theorem typC_of_isSLTwoOver_odd {T : Type} [Group T] [Finite T] {q : ℕ} (hq : Odd q)
    (h5 : 5 ≤ q) (hSL : HarrisLit.IsSLTwoOver q (T ⧸ pPrimeCore 2 T)) :
    TypC T ∧ center (T ⧸ pPrimeCore 2 T) ≠ ⊥ := by
  obtain ⟨p, k, hp, hp2, hk, rfl⟩ : ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ q = p ^ k := by
    obtain ⟨F, _, _, hF, -⟩ := hSL
    obtain ⟨p, hchar⟩ := CharP.exists F
    obtain ⟨f, hp, hcard⟩ := FiniteField.card F p
    refine ⟨p, f, hp, ?_, f.pos, hF.symm.trans hcard⟩
    rintro rfl
    rw [← hF, hcard] at hq
    exact Nat.not_even_iff_odd.mpr hq ((Nat.even_pow' f.ne_zero).mpr even_two)
  obtain ⟨-, hZ2, hL, -⟩ := HarrisLit.Lemma47.sl2_facts hp hp2 hk h5 hSL
  obtain ⟨eZ⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar T
  refine ⟨Or.inl (GSThmB.Soc.oddLieType_of_lieModel (Blueprint.LieModel.of_mulEquiv eZ hL) hp
    hp2), fun h => ?_⟩
  rw [h, Subgroup.card_bot] at hZ2
  exact absurd hZ2 (by norm_num)

theorem fixedSubgroup_conj {H : Type*} [Group H] (x : H) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj x) = centralizer ({x} : Set H) := by
  ext y
  rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, MulAut.conj_apply,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
      _ = y := by group

theorem map_conj_eq_of_mem_normalizer {H : Type*} [Group H] {M : Subgroup H} {x : H}
    (hx : x ∈ normalizer (M : Set H)) : M.map (MulAut.conj x).toMonoidHom = M := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.mp hx m).mp hm
  · intro hy
    have h1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    refine ⟨x⁻¹ * y * x, (mem_normalizer_iff.mp hx _).mpr (by rw [h1]; exact hy), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h1

end CFSG.ComponentClassification.GS82PumpInputs.P7

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

theorem sLTwoCentralPumpInput_of_typPump
    (hP : TypPumpInput) : SLTwoCentralPumpInput := by
  intro H _ _ hH M hM x hx hxN T hTM hTC hTpc q₀ q₁ _ h5 hq₁ hq₀₁ hSL w hw _ hwZ
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hβ : ∀ y, MulAut.conj x (MulAut.conj x y) = y := by
    intro y
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hxx]; group
  have hfix := P7.fixedSubgroup_conj x
  obtain ⟨hTyp, hZT⟩ := P7.typC_of_isSLTwoOver_odd hq₁ (h5.trans hq₀₁) hSL
  have hMT : TypC ↥M := P10.typC_pump_sub hP hH (MulAut.conj x) hβ hM
    (P7.map_conj_eq_of_mem_normalizer hxN) (P10.center_quot_ne_bot_of_mem_fusionZStar hw hwZ)
    (hfix ▸ hTC) (hfix ▸ hTpc) hTM hZT hTyp
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  exact P10.p10_disjunction hMq hMT q₀

end CFSG.ComponentClassification.GS82PumpInputs
