module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeStepsS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeIndex

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem stmt5_2_2_ne_index_of_F4 (h510 : Stmt5_1_10_F4) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : FactL2LieParabolic) : Stmt5_2_2_ne_index_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hL₂K hT₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKN : ∀ s ∈ T, s ∈ Subgroup.normalizer (oTwoUpper H : Set G) := fun s hs =>
    le_normalizer_oTwoUpper H (hTH.1 hs)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  ·
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hL₂K
    refine relIndex_eq_two_of_orbit hT₀ (Y := K₂) fun s hs => tc.cK _ ?_
    refine cComp_mem_of_le (map_conj_mem_cComp hK₁ (hTH.1 hs)) ?_ (oTwoUpper_le H)
    rw [← CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hKN s hs)]
    exact Subgroup.map_mono hL₂K.le
  ·
    have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
      A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
    obtain ⟨k, hk, htype, -, hMK⟩ :=
      nonBender_type_F4 h510 hyp.toHyp5_1_8 hyp.notation59 hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    obtain ⟨Pj, hPj, -, -⟩ := exists_parabolics hF hk htype hTK
    have hOS : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
    have hPs : ∀ s ∈ T, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H)
        (P.map (MulAut.conj s).toMonoidHom) := fun s hs =>
      hP.map_conj (hKN s hs)
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hKN s hs⟩)
    have hdet : ∀ A B : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) A →
        IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) B →
        modO2Image (oTwoUpper H) A = modO2Image (oTwoUpper H) B → A = B := by
      intro A B hA hB hAB
      rw [← map_comap_modO2Image_of_le hA.1 (hA.pCoreOf_le hTK.1 hOS),
        ← map_comap_modO2Image_of_le hB.1 (hB.pCoreOf_le hTK.1 hOS), hAB]
    have hL₂s : ∀ s : G, L₂.map (MulAut.conj s).toMonoidHom =
        perfectCore (P.map (MulAut.conj s).toMonoidHom) := fun s => by
      rw [hL₂eq, map_perfectCore]
    obtain ⟨t₁, ht₁, ht₁N⟩ : ∃ t₁ ∈ T, t₁ ∉ Subgroup.normalizer (L₂ : Set G) := by
      by_contra hall
      push Not at hall
      exact hT₀.ne (le_antisymm inf_le_left fun t ht => ⟨ht, hall t ht⟩)
    have hP1 : P.map (MulAut.conj (1 : G)).toMonoidHom = P :=
      CFSG.LieType.Steinberg.map_conj_one P
    obtain ⟨j₀, hj₀⟩ := hPj P hP
    obtain ⟨j₁, hj₁⟩ := hPj _ (hPs t₁ ht₁)
    have hj : j₀ ≠ j₁ := by
      intro hj
      apply ht₁N
      rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, hL₂s,
        hdet _ _ (hPs t₁ ht₁) hP (by rw [hj₁, hj₀, hj]), hL₂eq]
    refine relIndex_eq_two_of_orbit hT₀ (Y := L₂.map (MulAut.conj t₁).toMonoidHom)
      fun s hs => ?_
    obtain ⟨js, hjs⟩ := hPj _ (hPs s hs)
    have hfin : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b := by decide
    rcases hfin j₀ j₁ js hj with rfl | rfl
    · left
      rw [hL₂s, hdet _ _ (hPs s hs) hP (by rw [hjs, hj₀]), hL₂eq]
    · right
      rw [hL₂s, hL₂s, hdet _ _ (hPs s hs) (hPs t₁ ht₁) (by rw [hjs, hj₁])]

end CFSG.Quasithin.H13
