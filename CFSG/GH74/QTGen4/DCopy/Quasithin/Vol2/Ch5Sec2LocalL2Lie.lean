module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem521
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem524
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526S331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_L2Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D K₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → quasithinIsCComponent K₁ H →
    oTwoUpper H = conjClosure K₁ T → K₁ < oTwoUpper H → IsBenderAny (O2Q K₁) →
      borelOf K₁ T ≤ M ∧
        (∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          X ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
          Odd (Nat.card X) → X ≤ Subgroup.normalizer (K₁ : Set G)) ∧
        ∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
          (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
            X ≤ Subgroup.normalizer (P : Set G)) →
          X ≤ Subgroup.normalizer (K₁ : Set G)

theorem nonBender_type_F4 (h510 : Stmt5_1_10_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T M L H B D K₁ : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) (hK₁ : quasithinIsCComponent K₁ H)
    (hnb : ¬ IsBenderAny (O2Q K₁)) (hK1eq : K₁ = oTwoUpper H) :
    ∃ k : ℕ, 2 ≤ k ∧
      (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
      E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H) ∧
      M ⊓ oTwoUpper H =
        oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  obtain ⟨k, hk, hBorel, -, K₁', hK₁', -, hcases'⟩ := h510 G T M L H B D n hyp hN
  refine ⟨k, hk.1, ?_⟩
  rcases hcases' with ⟨hlt, -⟩ | ⟨-, h2⟩ | ⟨-, h2, h3⟩
  · exfalso
    rw [← hK1eq] at hlt
    exact not_subnormal_of_mem_cComp hK₁ hlt hK₁'.1 hK₁'.2.1 hK₁'.2.2.1
  · rw [hK1eq] at hnb
    exact absurd ⟨k, hk.1, h2⟩ hnb
  · exact ⟨h2, h3, hyp.borel_eq hBorel⟩

theorem stmt5_2_L2Lie_of_F4 (hU3 : FactU3Cover) (hF : FactL2LieParabolic) (hTwo : Stmt5_2_L2Two_F4)
    (h510 : Stmt5_1_10_F4) : Stmt5_2_L2Lie_F4 := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  have hMK := hyp.borel_eq hBorel
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨hbend, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  ·
    refine ⟨isRankOneListed_oTwoQuot_of_isBenderAny hU3 hbend, ?_⟩
    have hle : L₂ ≤ oTwoUpper H := by
      rw [hKeq]
      exact le_conjClosure L₂ T
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨h1, h2, -⟩ := hTwo G T M L H B D L₂ n hyp hN hK₁ hKeq hlt hbend
      exact ⟨h1, h2⟩
    · rw [heq]
      refine ⟨?_, fun X hXK _ _ => hXK⟩
      show oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤ M
      rw [← hMK]
      exact inf_le_left
  ·
    obtain ⟨k', hk', htype, -, -⟩ := nonBender_type_F4 h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨-, hpsl, hborel, hX⟩ := l2Lie_nonBender hF hk' htype hTK hMK hP hL₂P
    exact ⟨isRankOneListed_oTwoQuot (by omega) (Or.inl ⟨by simp [classicalTags], hpsl⟩), hborel,
      hX⟩

theorem stmt5_2_L2Gen_of_F4 (hF : FactL2LieParabolic) (h510 : Stmt5_1_10_F4) : Stmt5_2_L2Gen_F4 := by
  intro G _ _ T M L H B D K₁ P L₂ n hyp hN hK₁ _ hnb hK1eq hP hL₂P
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, hdiag, hMK⟩ := nonBender_type_F4 h510 hyp hN hK₁ hnb hK1eq
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [← hK1eq]
    exact hK₁.2.1
  obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (P : Set G) := by
    by_contra hall
    push Not at hall
    exact hdiag P (hP.isMaxParabolic2 hTK) hP.2.1 hall
  have htK : t ∈ Subgroup.normalizer (oTwoUpper H : Set G) :=
    le_normalizer_oTwoUpper H (hTH.1 ht)
  have htTK : t ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, htK⟩
  have hP' := hP.map_conj htK htTK
  have hne : P.map (MulAut.conj t).toMonoidHom ≠ P := fun he =>
    htP (CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr he)
  obtain ⟨Pj, hPj, -, hgen⟩ := exists_parabolics hF hk htype hTK
  obtain ⟨j, hPeq⟩ := hPj P hP
  obtain ⟨j', hP'eq⟩ := hPj _ hP'
  have hOS : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hjj : j ≠ j' := by
    rintro rfl
    apply hne
    calc P.map (MulAut.conj t).toMonoidHom = _ :=
          (map_comap_modO2Image_of_le hP'.1 (hP'.pCoreOf_le hTK.1 hOS)).symm
      _ = _ := by rw [hP'eq, ← hPeq]
      _ = P := map_comap_modO2Image_of_le hP.1 (hP.pCoreOf_le hTK.1 hOS)
  have hgen' : perfectCore (Pj j) ⊔ perfectCore (Pj j') = ⊤ := by
    fin_cases j <;> fin_cases j'
    · exact absurd rfl hjj
    · exact hgen
    · rw [sup_comm]
      exact hgen
    · exact absurd rfl hjj
  have hL₂K : L₂ ≤ oTwoUpper H := hL₂eq ▸ (perfectCore_le P).trans hP.1
  have hL₂tK : L₂.map (MulAut.conj t).toMonoidHom ≤ oTwoUpper H := by
    rw [← CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp htK]
    exact Subgroup.map_mono hL₂K
  have hL₂t : L₂.map (MulAut.conj t).toMonoidHom =
      perfectCore (P.map (MulAut.conj t).toMonoidHom) := by
    rw [hL₂eq, map_perfectCore]
  have hKle : oTwoUpper H ≤
      L₂ ⊔ L₂.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 (oTwoUpper H) := by
    refine Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top (sup_le hL₂K hL₂tK) ?_
    rw [modO2Image_sup hL₂K hL₂tK, hL₂t, hL₂eq, modO2Image_perfectCore hP.1,
      modO2Image_perfectCore hP'.1, hPeq, hP'eq]
    exact hgen'
  have hCK : conjClosure L₂ T ≤ oTwoUpper H := conjClosure_le fun s hs y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH.1 hs)) y).mp (hL₂K hy)
  have hle : oTwoUpper H ≤ conjClosure L₂ T ⊔ pCoreOf 2 (oTwoUpper H) := by
    refine hKle.trans (sup_le (sup_le ?_ ?_) le_sup_right)
    · exact (le_conjClosure L₂ T).trans le_sup_left
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_left (mem_conjClosure ht hy)
  have hOC : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (conjClosure L₂ T : Set G) :=
    (hOS.trans inf_le_left).trans (le_normalizer_conjClosure L₂ T)
  exact le_antisymm (le_of_perfect_of_le_sup hKperf hle (pCoreOf_isPGroup 2 _) hOC) hCK

theorem stmt5_2_1_par_of_F4 (hF : FactL2LieParabolic) (hTwo : Stmt5_2_L2Two_F4) (h510 : Stmt5_1_10_F4) :
    Stmt5_2_1_par_F4 := by
  intro G _ _ T M L H B D L₂ n hyp hN hL₂ _ X hXK hXP
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨hbend, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  · have hle : L₂ ≤ oTwoUpper H := by
      rw [hKeq]
      exact le_conjClosure L₂ T
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (hTwo G T M L H B D L₂ n hyp hN hK₁ hKeq hlt hbend).2.2 X hXK hXP
    · rw [heq]
      exact hXK
  · obtain ⟨k, hk, htype, -, hMK⟩ := nonBender_type_F4 h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    rw [hL₂eq]
    exact (hXP P (hP.isRankOneParabolicOver hF hk htype hTK)).trans
      (normalizer_le_normalizer_perfectCore P)

theorem IsL2Choice.inf_le_normalizer_F4 (hF : FactL2LieParabolic) (h510 : Stmt5_1_10_F4)
    {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_1_8 G T M L H n) (hN : IsNotation5_1_9 T M L H B D) (hL₂ : IsL2Choice T H L₂) :
    T ⊓ oTwoUpper H ≤ Subgroup.normalizer (L₂ : Set G) := by
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hL₂
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
  · refine inf_le_right.trans ?_
    rw [hKeq]
    exact conjClosure_le fun s hs y hy => le_normalizer_of_mem_cComp hK₁
      (map_conj_mem_cComp hK₁ (hTH.1 hs)) ⟨y, hy, rfl⟩
  · obtain ⟨k, hk, htype, -, hMK⟩ := nonBender_type_F4 h510 hyp hN hK₁ hnb hK1eq
    obtain ⟨hL₂eq, -, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
    rw [hL₂eq]
    exact ((le_inf inf_le_right Subgroup.le_normalizer).trans hP.2.1).trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))

theorem stmt5_2_6_borel_of_F4 (hF : FactL2LieParabolic) (hLie : Stmt5_2_L2Lie_F4)
    (h510 : Stmt5_1_10_F4) : Stmt5_2_6_borel_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  obtain ⟨-, hR, hX⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hSK : sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hMK := hyp.toHyp5_1_8.borel_eq hBorel
  have hL₂K : L₂ ≤ oTwoUpper H := hyp.choice.le_oTwoUpper
  have hSL₂ : sec52S M H ⊓ L₂ = T ⊓ L₂ := by
    calc sec52S M H ⊓ L₂ = sec52S M H ⊓ oTwoUpper H ⊓ L₂ := by
          rw [inf_assoc, inf_eq_right.mpr hL₂K]
      _ = T ⊓ oTwoUpper H ⊓ L₂ := by rw [hSK]
      _ = T ⊓ L₂ := by rw [inf_assoc, inf_eq_right.mpr hL₂K]
  have hborel : borelOf L₂ (sec52S M H) = borelOf L₂ T := by
    unfold borelOf
    rw [hSL₂]
  have hBKle : B ≤ oTwoUpper H := hBK.1.trans inf_le_right
  have hBTK : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    have := hBK.1
    rw [hMK] at this
    exact this.trans inf_le_right
  have hBL₂ : B ≤ Subgroup.normalizer (L₂ : Set G) :=
    hX B (hBKle.trans Subgroup.le_normalizer) hBTK hBK.2.1
  have hTKL₂ := hyp.choice.inf_le_normalizer_F4 hF h510 hyp.toHyp5_1_8 hN
  have hTKS : T ⊓ oTwoUpper H ≤ sec52S M H := hSK ▸ inf_le_left
  rw [hborel]
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  ·
    have hRMK : borelOf L₂ T ≤ T ⊓ oTwoUpper H ⊔ B := by
      have hTMK : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
        A4.isSylowTwoOf_mono hTK (inf_le_inf_right _ h.T_le) inf_le_right
      rw [sup_comm, sup_eq_of_isHall_of_isSylowTwoOf hBK hTMK]
      exact le_inf hR (inf_le_left.trans hL₂K)
    exact (le_sup_inf_of_odd hTK.2.1 hBK.2.1 hBTK hTKL₂ hRMK inf_le_left).trans
      (sup_le (hTKS.trans le_sup_left) le_sup_right)
  ·
    intro x hx
    refine Subgroup.mem_sup_right ⟨hx.2, ?_⟩
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hBTK hx.1, Subgroup.le_normalizer hx.2⟩
    rwa [inf_assoc, inf_eq_right.mpr hL₂K] at h1

end CFSG.Quasithin.H13
