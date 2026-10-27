module

public import CFSG.GH74.RouteH
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.AssemblyBridge
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

namespace C23List

variable {G : Type} [Group G]

theorem of_psl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (h : LieModel G .PSL 2 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h5, h⟩⟩

theorem of_psl3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .PSL 3 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inl h)⟩

theorem of_psu3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .PSU 3 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inl h))⟩

theorem of_psp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h : LieModel G .PSp 2 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inl h⟩)))⟩

theorem of_g2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h : LieModel G .G2 0 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, Or.inr h⟩)))⟩

theorem of_trialityD4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .trialityD4 0 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩

theorem of_psl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 1) (h : LieModel G .PSL 4 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inl ⟨h8, h⟩⟩))))⟩

theorem of_psu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f) : C23List G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inr ⟨h8, h⟩⟩))))⟩

theorem of_twistedG2 {f : ℕ} (h : LieModel G .twistedG2 0 3 f) : C23List G :=
  Or.inr (Or.inl ⟨f, h⟩)

theorem of_alt7 (h : Nonempty (G ≃* alternatingGroup (Fin 7))) : C23List G :=
  Or.inr (Or.inr (Or.inl h))

theorem of_alt9 (h : Nonempty (G ≃* alternatingGroup (Fin 9))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem of_alt10 (h : Nonempty (G ≃* alternatingGroup (Fin 10))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem of_alt11 (h : Nonempty (G ≃* alternatingGroup (Fin 11))) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem of_M11 (h : NativeSporadic.IsSporadic G .M11) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem of_U34 (h : LieModel G .PSU 3 2 2) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem of_M12 (h : NativeSporadic.IsSporadic G .M12) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem of_J1 (h : NativeSporadic.IsSporadic G .J1) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem of_McL (h : NativeSporadic.IsSporadic G .McL) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h))))))))))

theorem of_Ly (h : NativeSporadic.IsSporadic G .Ly) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h)))))))))))

theorem of_ONan (h : NativeSporadic.IsSporadic G .ONan) : C23List G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr h)))))))))))

theorem of_psl2_four (h : LieModel G .PSL 2 2 2) : C23List G := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model G h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact of_psl2 Nat.prime_five (by decide) le_rfl (by norm_num)
    (Or.inl ⟨by decide, ⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5,
      inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans e5.symm⟩⟩)

end C23List

namespace C2StarList

variable {G : Type} [Group G]

theorem toC23List (h : C2StarList G) : C23List G := by
  rcases h with ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ | h | h | h | h | h | h | h | h
  · have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rcases h with ⟨h3, h | h | h⟩ | h | h | h | ⟨h3, ⟨h8, h⟩ | ⟨h8, h⟩⟩
    · obtain ⟨k, hk⟩ := hodd
      exact C23List.of_psl2 hp hp2 hf (by omega) h
    · exact C23List.of_psp4 hp hp2 hf h3 h
    · exact C23List.of_g2 hp hp2 hf h3 h
    · exact C23List.of_psl3 hp hp2 hf h
    · exact C23List.of_psu3 hp hp2 hf h
    · exact C23List.of_trialityD4 hp hp2 hf h
    · exact C23List.of_psl4 hp hp2 hf h3 h8 h
    · exact C23List.of_psu4 hp hp2 hf h3 h8 h
  · exact C23List.of_twistedG2 h
  · exact C23List.of_U34 h
  · exact C23List.of_alt7 h
  · exact C23List.of_M11 h
  · exact C23List.of_M12 h
  · exact C23List.of_J1 h
  · exact C23List.of_McL h
  · exact C23List.of_Ly h
  · exact C23List.of_ONan h

theorem of_psp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h : LieModel G .PSp 2 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h3, Or.inr (Or.inl h)⟩⟩

theorem of_psl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 1) (h : LieModel G .PSL 4 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inl ⟨h8, h⟩⟩)))⟩

theorem of_psu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 < p ^ f)
    (h8 : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f) : C2StarList G := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Or.inr ⟨h8, h⟩⟩)))⟩

theorem of_McL (h : NativeSporadic.IsSporadic G .McL) : C2StarList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem of_Ly (h : NativeSporadic.IsSporadic G .Ly) : C2StarList G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

end C2StarList

theorem lieModel_psl_two_four_of_psl_two_five
    {X : Type} [Group X] (h : LieModel X .PSL 2 5 1) :
    LieModel X .PSL 2 2 2 := by
  have hc : StatedClassicalModel X .PSL 2 5 1 := by
    rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inr (by rw [hF]; norm_num))
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hcard)
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, by rw [hcard]; norm_num, ⟨(e.trans e5).trans e4.symm⟩⟩

theorem inTarget2Star_of_hasL2Model_odd
    {K : Type} [Group K] (h : HasL2Model K Odd) :
    InTarget2Star K := by
  obtain ⟨p, f, hp, hf, hodd, hL⟩ := h
  have hadm : StatedLieAdmissible .PSL 2 p f := by
    rcases hL with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc.1
    all_goals exact absurd h0 (by norm_num)
  have h3 : p ^ f ≠ 3 := fun h3 => hadm.2.2.2.2 (by rw [h3])
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) this
  have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨k, hk⟩ := hodd
  by_cases h5 : 5 < p ^ f
  · exact Or.inl (Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨h5, hL⟩⟩)
  · have : p ^ f = 5 := by omega
    have hp5 : p = 5 := by
      have : p ∣ 5 := this ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp this
    subst hp5
    have hf1 : f = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 5) (show 5 ^ f = 5 ^ 1 by rw [this, pow_one])
    subst hf1
    exact Or.inr (Or.inl (lieModel_psl_two_four_of_psl_two_five hL))

theorem S_stage1_of_thms
    (h1 : S_stage1_thm1) (h5 : S_stage1_thm5) (h6 : S_stage1_thm6) :
    ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLBStar2Type G →
      ∃ (Gs : Type) (_ : Group Gs), InTarget2Star Gs ∧ IsTwoTerminalGStarType G Gs := by
  intro G _ _ hG hLB
  have key1 : pRank 2 G ≤ 2 → ∃ (Gs : Type) (_ : Group Gs), InTarget2Star Gs ∧
      IsTwoTerminalGStarType G Gs := by
    intro h
    obtain ⟨Gs, _, hts, hcl⟩ := h1 G hG h
    refine ⟨Gs, inferInstance, ?_, hts⟩
    rcases hcl with hL | ⟨p, f, hp, hp2, hf, hL | hL⟩ | hL
    · exact inTarget2Star_of_hasL2Model_odd hL
    · exact Or.inl (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inl hL)⟩)
    · exact Or.inl (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inl hL))⟩)
    · exact Or.inr (Or.inr (Or.inl hL))
  rcases hLB with h | ⟨h, hmeet⟩ | hT
  · exact key1 h.le
  · by_cases h3 : pRank 2 G = 3
    · obtain ⟨Gs, _, hts, hcl⟩ := h6 G hG h3 hmeet
      refine ⟨Gs, inferInstance, ?_, hts⟩
      rcases hcl with ⟨f, hf⟩ | hJ | hM
      · exact Or.inl (Or.inr (Or.inl ⟨f, hf⟩))
      · exact Or.inr (Or.inr (Or.inr hJ))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM)))))
    · exact key1 (by omega)
  · obtain ⟨Gs, _, hInT, hts⟩ := h5 G hG hT
    exact ⟨Gs, inferInstance, Or.inl hInT, hts⟩

theorem S_corTwoThin_of_stage2_thm11 (h : S_stage2_thm11) : S_corTwoThin := by
  intro G _ _ hG _ hG2 hT
  exact (h G hG (Or.inr (Or.inr hT))).2 hG2

theorem isSporadic_of_isApproxTo {s : TauCeti.SporadicName} (hs11 : s ≠ .M11)
    (h161 : S_sixteenOne s) {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (h : IsApproxTo G (NativeSporadic.Carrier s)) : NativeSporadic.IsSporadic G s :=
  h161 G hG.1 hG.2.1 h.1 (fun h' => absurd h' hs11)

theorem L2Meets.mono {G : Type} [Group G] {P Q : Assembly.GroupProp}
    (h : ∀ (K : Type) [Group K], P K → Q K) : L2Meets G P → L2Meets G Q := by
  rintro ⟨x, hx, K, hK, hP⟩
  exact ⟨x, hx, K, hK, h _ hP⟩

theorem c23List_of_lb2_branch {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (hSO : IsSpecialOddType G) (hC3 : S_C3) (hLB : IsLB2Type G → C23List G) : C23List G := by
  have hsub := l2Sub_of_not_l2Meets_g2 hG hSO.2
  by_cases hB : L2Meets G InB2 ∨ pRank 2 G ≤ 3
  · exact hLB ⟨hsub, hB, hSO.1⟩
  · rw [not_or] at hB
    have hrank : 4 ≤ pRank 2 G := by omega
    have hLT : IsLT2oType G := by
      refine ⟨hrank, fun x hx K hK => ?_⟩
      rcases hsub x hx K hK with h | h
      · exact Or.inl h
      · refine Or.inr (inU2_of_inT2_of_center_bot h ?_)
        by_contra hz
        exact hB.1 ⟨x, hx, K, hK, ⟨h, hz⟩⟩
    rcases hC3 G hG hLT hSO.1 with h | h | h
    · exact C23List.of_alt9 h
    · exact C23List.of_alt10 h
    · exact C23List.of_alt11 h

@[expose] def S_C2list : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLB2Type G →
    ¬ HasTwoUniquenessSubgroup G → C23List G

theorem S_C2list_of_C2 (h : S_C2) : S_C2list :=
  fun G _ _ hG hLB hU => (h G hG hLB hU).1

theorem S_C23_of_C2list_C3_SUS
    (hC2 : S_C2list) (hC3 : S_C3) (hSUS : S_SUS) : S_C23 := by
  intro G _ _ hG hSO
  refine c23List_of_lb2_branch hG hSO hC3 fun hLB => ?_
  by_cases hU : HasTwoUniquenessSubgroup G
  · rcases hSUS G hG hLB hU with h | h | h
    · exact C23List.of_psl2_four h
    · exact C23List.of_U34 h
    · exact C23List.of_J1 h
  · exact hC2 G hG hLB hU

theorem S_C23_of_C2_C3_SUS
    (hC2 : S_C2) (hC3 : S_C3) (hSUS : S_SUS) : S_C23 :=
  S_C23_of_C2list_C3_SUS (S_C2list_of_C2 hC2) hC3 hSUS

theorem specialOdd_of_C23 (h : S_C23) : S_specialOdd := by
  intro G _ _ hs hnonab _ _ hK _ _ hSO
  exact h G (isKProperSimple_of_kgh hs hnonab hK) hSO

theorem isLBStar2Type_of_isLB2Type (hP27 : S_prop27) (hTT : S_twoThinOfB2) {G : Type} [Group G]
    [Finite G] (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G) (hLB : IsLB2Type G) :
    IsLBStar2Type G := by
  have hnoG2 : ¬ L2Meets G InG2 := hLB.isSpecialOddType.2
  by_cases hB : L2Meets G InB2
  · exact Or.inr (Or.inr (hTT G hG h3 hnoG2 hB))
  · have hle : pRank 2 G ≤ 3 := hLB.2.1.resolve_left hB
    refine Or.inr (Or.inl ⟨hle, ?_⟩)
    have h33 : pRank 2 G = 3 := le_antisymm hle h3
    by_cases hC2 : L2Sub G InC2
    · have := hP27 G hG hLB h33 hC2
      refine L2Meets.mono (fun K _ h => Or.inr ?_) this
      exact hasL2Model_odd_gt_three (fun q hq => isFM9_odd hq) h
    · simp only [L2Sub, not_forall] at hC2
      obtain ⟨x, hx, K, hK, hnK⟩ := hC2
      have hT : InT2 K := (hLB.1 x hx K hK).resolve_left hnK
      have hz : center K = ⊥ := by
        by_contra hz
        exact hB ⟨x, hx, K, hK, ⟨hT, hz⟩⟩
      refine ⟨x, hx, K, hK, ?_⟩
      rcases inT2_cases_of_center_bot hT hz with h | h
      · exact Or.inr (hasL2Model_odd_gt_three (fun q hq => hq.1) h)
      · exact Or.inl h

theorem hasC2StarHypothesis_of_isLB2Type
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) {G : Type}
    [Group G] [Finite G] (hG : IsKProperSimple G) (hLB : IsLB2Type G) :
    HasC2StarHypothesis G := by
  have : IsSimpleGroup G := hG.1
  have h2 : 2 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound G hG.2.1
      (even_card_of_nonabelian_simple hG.2.1)
  by_cases h3 : 3 ≤ pRank 2 G
  · rcases isLBStar2Type_of_isLB2Type hP27 hTT hG h3 hLB with h | ⟨h, ⟨x, hx, Kh, hKh, hP⟩⟩ | hT
    · omega
    · obtain ⟨K, hK, ⟨e⟩⟩ := exists_pComponent_of_component hKh
      refine Or.inr (Or.inl ⟨by omega, x, K, ⟨hx, hK⟩, ?_⟩)
      rcases hP with h7 | ⟨p, f, hp, hf, hq, hm⟩
      · obtain ⟨e7⟩ := h7
        exact Or.inl ⟨e.trans e7⟩
      · exact Or.inr ⟨p, f, hp, hf, hq, lieModel_of_mulEquiv e.symm hm⟩
    · exact Or.inr (Or.inr hT)
  · exact Or.inl (by omega)

theorem S_C2list_of_C2star
    (hC2star : S_C2star) (hP27 : S_prop27) (hTT : S_twoThinOfB2) :
    S_C2list :=
  fun G _ _ hG hLB _ =>
    (hC2star G hG (hasC2StarHypothesis_of_isLB2Type hP27 hTT hG hLB)).toC23List

theorem S_C23_of_C2star_C3
    (hC2star : S_C2star) (hC3 : S_C3) (hP27 : S_prop27)
    (hTT : S_twoThinOfB2) : S_C23 := by
  intro G _ _ hG hSO
  exact c23List_of_lb2_branch hG hSO hC3 fun hLB =>
    (hC2star G hG (hasC2StarHypothesis_of_isLB2Type hP27 hTT hG hLB)).toC23List

@[expose] def S_C2starGe3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G → HasC2StarHypothesis G →
    C2StarList G

theorem S_C2starGe3_of_C2star (h : S_C2star) : S_C2starGe3 :=
  fun G _ _ hG _ hH => h G hG hH

theorem specialOdd_of_C2starGe3 (hC2 : S_C2starGe3) (hC3 : S_C3)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) : S_specialOdd := by
  intro G _ _ hs hnonab hrank _ hK _ _ hSO
  have hG := isKProperSimple_of_kgh hs hnonab hK
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hrank
  exact c23List_of_lb2_branch hG hSO hC3 fun hLB =>
    (hC2 G hG h3 (hasC2StarHypothesis_of_isLB2Type hP27 hTT hG hLB)).toC23List

@[expose] def S_C2starFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → pRank 2 G = 4 →
    HasTwoThinConfiguration G → ¬ HasTwoUniquenessSubgroup G → C2StarList G

theorem S_C2starFour_of_C2star (h : S_C2star) : S_C2starFour :=
  fun G _ _ hG _ hT _ => h G hG (Or.inr (Or.inr hT))

@[expose] def S_stage2Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → pRank 2 G = 4 →
    HasTwoThinConfiguration G → ¬ HasTwoUniquenessSubgroup G →
      IsApproxTo G (NativeSporadic.Carrier .McL) ∨ IsApproxTo G (NativeSporadic.Carrier .Ly) ∨
        ∃ (Gs : Type) (_ : Group Gs),
          ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ LieModel Gs .PSp 2 p f) ∨
            (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
              ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨
                (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)))) ∧
          IsTwoCentralClassicalType G Gs

theorem S_C2starFour_of_stage5 (h2 : S_stage2Four) (hSP : S_stage5_SP) (hLU : S_stage5_LU)
    (hMcL : S_sixteenOne .McL) (hLy : S_sixteenOne .Ly) : S_C2starFour := by
  intro G _ _ hG h4 hT hU
  rcases h2 G hG h4 hT hU with h | h | ⟨Gs, _, hcl, hc⟩
  · exact C2StarList.of_McL (isSporadic_of_isApproxTo (by decide) hMcL hG h)
  · exact C2StarList.of_Ly (isSporadic_of_isApproxTo (by decide) hLy hG h)
  · rcases hcl with ⟨p, f, hp, hp2, h3, hL⟩ | ⟨p, f, hp, hp2, h5, hL⟩
    · obtain ⟨e⟩ := hSP G hG Gs ⟨p, f, hp, hp2, h3, hL⟩ hc
      exact C2StarList.of_psp4 hp hp2 h3 (lieModel_of_mulEquiv e.symm hL)
    · obtain ⟨e⟩ := hLU G hG Gs ⟨p, f, hp, hp2, h5, hL⟩ hc
      rcases hL with ⟨h8, hL⟩ | ⟨h8, hL⟩
      · exact C2StarList.of_psl4 hp hp2 (by omega) h8 (lieModel_of_mulEquiv e.symm hL)
      · exact C2StarList.of_psu4 hp hp2 (by omega) h8 (lieModel_of_mulEquiv e.symm hL)

theorem c23List_of_isLB2Type_rank34
    (hSUS : S_SUS) (hP27 : S_prop27) (hTT : S_twoThinOfB2)
    (hS4 : S_stage4) (hS5 : S_C2starFour) (h161M12 : S_sixteenOne .M12)
    (h161ON : S_sixteenOne .ONan) {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) (h4 : pRank 2 G ≤ 4) (hLB : IsLB2Type G) : C23List G := by
  by_cases hU : HasTwoUniquenessSubgroup G
  · rcases hSUS G hG hLB hU with h | h | h
    · exact C23List.of_psl2_four h
    · exact C23List.of_U34 h
    · exact C23List.of_J1 h
  · have hStar := isLBStar2Type_of_isLB2Type hP27 hTT hG h3 hLB
    rcases (by omega : pRank 2 G = 3 ∨ pRank 2 G = 4) with h | h
    · rcases hS4 G hG hStar h hU with ⟨f, h⟩ | ⟨p, f, hp, hp2, hf, h3', h⟩ |
          ⟨p, f, hp, hp2, hf, h⟩ | h | h
      · exact C23List.of_twistedG2 h
      · exact C23List.of_g2 hp hp2 hf h3' h
      · exact C23List.of_trialityD4 hp hp2 hf h
      · exact C23List.of_M12 (isSporadic_of_isApproxTo (by decide) h161M12 hG h)
      · exact C23List.of_ONan (isSporadic_of_isApproxTo (by decide) h161ON hG h)
    · have hT : HasTwoThinConfiguration G := by
        rcases hStar with h2 | ⟨h2, -⟩ | hT
        · omega
        · omega
        · exact hT
      exact (hS5 G hG h hT hU).toC23List

theorem specialOdd_of_gls6 (hSUS : S_SUS) (hC3 : S_C3)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS5 : S_C2starFour)
    (h161M12 : S_sixteenOne .M12) (h161ON : S_sixteenOne .ONan) : S_specialOdd := by
  intro G _ _ hs hnonab hrank hgen hK _ _ hSO
  have hG := isKProperSimple_of_kgh hs hnonab hK
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hrank
  have h4 : pRank 2 G ≤ 4 := hgen.pRank_two_le
  exact c23List_of_lb2_branch hG hSO hC3 fun hLB =>
    c23List_of_isLB2Type_rank34 hSUS hP27 hTT hS4 hS5 h161M12 h161ON hG h3 h4 hLB

theorem specialOdd_of_gls6_stages (hSUS : S_SUS) (hC3 : S_C3)
    (hP27 : S_prop27) (hTT : S_twoThinOfB2) (hS4 : S_stage4) (hS2 : S_stage2Four)
    (hSP : S_stage5_SP) (hLU : S_stage5_LU) (h161M12 : S_sixteenOne .M12)
    (h161ON : S_sixteenOne .ONan) (h161McL : S_sixteenOne .McL) (h161Ly : S_sixteenOne .Ly) :
    S_specialOdd :=
  specialOdd_of_gls6 hSUS hC3 hP27 hTT hS4
    (S_C2starFour_of_stage5 hS2 hSP hLU h161McL h161Ly) h161M12 h161ON

end CFSG.GH74.GLS
