module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1315
public import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

structure Core3Parts : Prop where
  small : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nat.card S < 40320 → Core3Group S
  sp48 : Core3At fun d => ∃ q : PrimePower, d = .B 2 q ∧ q.card = 8
  sp62 : Core3At fun d => ∃ q : PrimePower, d = .B 3 q ∧ q.card = 2
  d42 : Core3At fun d => ∃ q : PrimePower, d = .D 4 q ∧ q.card = 2
  u52 : Core3At fun d => ∃ q : PrimePower, d = .twistedA 4 q ∧ q.card = 2
  u62 : Core3At fun d => ∃ q : PrimePower, d = .twistedA 5 q ∧ q.card = 2
  td42 : Core3At fun d => ∃ q : PrimePower, d = .trialityD4 q ∧ q.card = 2
  tits : Core3At fun d => d = .tits
  g28 : Core3At fun d => ∃ q : PrimePower, d = .G2 q ∧ q.card = 8
  u48 : Core3At fun d => ∃ q : PrimePower, d = .twistedA 3 q ∧ q.card = 8
  ree8 : Core3At fun d => d = .reeF4 1
  l2 : Core3At fun d => ∃ q : PrimePower, d = .A 1 q ∧ q.p = 2
  u3 : Core3At fun d => ∃ q : PrimePower, d = .twistedA 2 q ∧ q.p = 2
  l3 : Core3At fun d => ∃ q : PrimePower, d = .A 2 q ∧ q.p = 2 ∧ Even q.exponent
  sl3 : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    (∃ n : ℕ, 1 ≤ n ∧ Even n ∧ FullLinearCover false 3 (2 ^ n) Q) →
      Core3Group (Q ⧸ Subgroup.center Q)
  su3 : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    (∃ n : ℕ, 1 < n ∧ Odd n ∧ FullLinearCover true 3 (2 ^ n) Q) →
      Core3Group (Q ⧸ Subgroup.center Q)
  su6 : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    FullLinearCover true 6 2 Q →
    Core3Group (Q ⧸ Subgroup.center Q)

theorem card_le_card_mulAut {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥) :
    Nat.card S ≤ Nat.card (MulAut S) := by
  haveI : Finite (MulAut S) := inferInstance
  refine Nat.card_le_card_of_injective (MulAut.conj : S →* MulAut S) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut S => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  rw [hZ] at hxZ
  exact Subgroup.mem_bot.1 hxZ

section Chev23


theorem card_lt_of_chev23 (S : Type) [Group S] [Finite S] (h2 : IsChevSimple 2 S)
    (h3 : IsChevSimple 3 S) (hZ : Subgroup.center S = ⊥) : Nat.card S < 40320 := by
  have hle : ∀ n, Nat.card (MulAut S) = n → Nat.card S ≤ n := fun n h =>
    h ▸ card_le_card_mulAut hZ
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h2 with ⟨t, n, f, hX⟩ | ⟨e6⟩ | hPSU
  · rcases h3 with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        have hd : d.1.characteristic = 3 := hi
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX
            (small_odd_lie (r := 3) (by norm_num) (by norm_num) hd e) with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have := hle _ (small_card_psl24 hX)
          omega
        · have := hle _ (small_card_psl32 hX)
          omega
        · rw [I1431Z.card_eq_of_u4two (small_u42_of_model hX)]
          norm_num
    · cases i with
      | cyclic _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | alternating n' hn' =>
        rcases hi with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨-, h⟩
        · norm_num at h
        · obtain ⟨eQ⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
          have := hle _ (CFSG.GH74.KGroups.A6.card_mulAut eQ)
          omega
        · norm_num at h
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases small_amb_lie (r := 3) (by norm_num) hv hi with
          ⟨q, rfl, hq8, -⟩ | ⟨q, rfl, hq2, -⟩
        · have hM := CFSG.Models.lieModel_A 1 q hv e
          obtain ⟨hq2', hq3⟩ := primePower_eq_of_card_eq (r := 2) (s := 3) Nat.prime_two
            (by norm_num) (hq8.trans (by norm_num))
          have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
          rw [hq2', hq3] at hBP
          have := hle _ (small_card_psl28 hBP)
          omega
        · rw [I1431Z.card_eq_of_u4two ⟨.lie ⟨.twistedA 3 q, hv⟩, hq2, ⟨e⟩⟩]
          norm_num
  · obtain ⟨eQ⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 e6
    have := hle _ (CFSG.GH74.KGroups.A6.card_mulAut eQ)
    omega
  · obtain ⟨eS⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩)
    have := hle _ (CFSG.GH74.KGroups.U33.card_mulAut eS)
    omega

end Chev23

section Main


theorem core3Group_of_k2 (h : Core3Parts) {S : Type} [Group S] [Finite S]
    (hsimp : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hch : IsChevSimple 2 S)
    (i : CFSGIndex) (hi : k2 3 i) (f : S ≃* i.Group) : Core3Group S := by
  cases i with
  | cyclic r hr => exact hi.elim
  | alternating n hn =>
    have hj : (3 = 3 ∧ (n = 5 ∨ n = 9)) ∨ (3 = 7 ∧ n = 7) := hi
    rcases hj with ⟨-, rfl | rfl⟩ | ⟨h37, -⟩
    · refine h.small S hsimp hnab ?_
      have h60 : Nat.card S = 60 := by
        rw [Nat.card_congr f.toEquiv]
        show Nat.card (alternatingGroup (Fin 5)) = 60
        rw [Nat.card_eq_fintype_card]
        decide
      omega
    · exact absurd hch (List93.notChev2_holds S _ (Or.inr (Or.inr (Or.inl ⟨hn, rfl⟩))) ⟨f⟩)
    · norm_num at h37
  | sporadic s =>
    have hs : k2Spor 3 s := hi
    exact absurd hch (List93.notChev2_holds S _ (Or.inl ⟨s, rfl, 3, hs⟩) ⟨f⟩)
  | lie i =>
    obtain ⟨d, hv⟩ := i
    have hk : k2Lie 3 d := hi
    cases d with
    | A n q =>
      match n, hk with
      | 1, hk =>
        obtain ⟨-, hn3⟩ := hk
        by_cases h2' : q.p = 2
        · exact h.l2 ⟨.A 1 q, hv⟩ ⟨q, rfl, h2'⟩ S ⟨f⟩
        · have hne3 : q.p ≠ 3 := by
            intro h3
            apply hn3
            rw [TauCeti.PrimePower.card_def, h3]
            exact dvd_pow_self 3 q.exponent_pos.ne'
          have hc : IsChevSimple q.p S :=
            Or.inl ⟨.lie ⟨.A 1 q, hv⟩, by simp [onLie], ⟨f⟩⟩
          refine h.small S hsimp hnab ?_
          rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315.inputChevTwoOdd_holds S q.p
              q.prime_p h2' hne3 hc hch with ⟨⟨e5⟩, -⟩ | ⟨⟨F, _, _, hF, ⟨e7⟩⟩, -⟩
          · rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card]
            decide
          · have hodd : Odd (Nat.card F) := by rw [hF]; decide
            rw [Nat.card_congr e7.toEquiv,
              CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd, hF]
            norm_num
      | 2, hk =>
        rcases hk with ⟨-, h2', he⟩ | ⟨h13, -⟩
        · exact h.l3 ⟨.A 2 q, hv⟩ ⟨q, rfl, h2', he⟩ S ⟨f⟩
        · norm_num at h13
      | n + 3, hk => exact False.elim hk
      | 0, hk => exact False.elim hk
    | twistedA n q =>
      match n, hk with
      | 2, hk =>
        obtain ⟨-, h2', -, -⟩ := hk
        exact h.u3 ⟨.twistedA 2 q, hv⟩ ⟨q, rfl, h2'⟩ S ⟨f⟩
      | 3, hk => exact h.u48 ⟨.twistedA 3 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | 4, hk => exact h.u52 ⟨.twistedA 4 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | 5, hk => exact h.u62 ⟨.twistedA 5 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | n + 6, hk => exact False.elim hk
      | 0, hk => exact False.elim hk
      | 1, hk => exact False.elim hk
    | B n q =>
      match n, hk with
      | 2, hk => exact h.sp48 ⟨.B 2 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | 3, hk => exact h.sp62 ⟨.B 3 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | n + 4, hk => exact False.elim hk
      | 0, hk => exact False.elim hk
      | 1, hk => exact False.elim hk
    | D n q =>
      match n, hk with
      | 4, hk => exact h.d42 ⟨.D 4 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
      | n + 5, hk => exact False.elim hk
      | 0, hk => exact False.elim hk
      | 1, hk => exact False.elim hk
      | 2, hk => exact False.elim hk
      | 3, hk => exact False.elim hk
    | C n q => exact False.elim hk
    | twistedD n q => exact False.elim hk
    | E6 q => exact False.elim hk
    | E7 q => exact False.elim hk
    | E8 q => exact False.elim hk
    | F4 q => exact False.elim hk
    | G2 q => exact h.g28 ⟨.G2 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
    | twistedE6 q => exact False.elim hk
    | trialityD4 q => exact h.td42 ⟨.trialityD4 q, hv⟩ ⟨q, rfl, hk.2⟩ S ⟨f⟩
    | suzuki m =>
      exfalso
      have h5 := hk.1
      norm_num at h5
    | reeG2 m => exact False.elim hk
    | reeF4 m =>
      rcases hk with ⟨-, rfl⟩ | ⟨h5, -⟩
      · exact h.ree8 ⟨.reeF4 1, hv⟩ rfl S ⟨f⟩
      · norm_num at h5
    | tits => exact h.tits ⟨.tits, hv⟩ rfl S ⟨f⟩

theorem i137LieCore3_of_parts (h : Core3Parts) : I137LieCore3 := by
  intro K _ _ hK hlev hch T A hT2 hT hA Q₀ _ hf hQ
  suffices hS : Core3Group (K ⧸ Subgroup.center K) from hS T A hT2 hT hA Q₀ hf hQ
  have hsimp : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (K ⧸ Subgroup.center K))
      with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center (K ⧸ Subgroup.center K) := ht ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  have h12 : K1Cover 3 K ∨ K2Cover 3 K := by
    by_cases h1 : K1Cover 3 K
    · exact Or.inl h1
    · by_cases h2 : K2Cover 3 K
      · exact Or.inr h2
      · exfalso
        unfold fullCoverLevel at hlev
        rw [if_neg h1, if_neg h2] at hlev
        split_ifs at hlev <;> omega
  rcases h12 with ⟨-, h3⟩ | ⟨hKq, hc⟩
  · exact h.small _ hsimp hnab (card_lt_of_chev23 _ hch h3 hZ)
  · rcases hc with ⟨hZK, i, hi, ⟨e⟩⟩ | ⟨-, i, hi, -⟩ | ⟨-, hlin⟩ | ⟨i, hi, hcov, -⟩
    · exact core3Group_of_k2 h hsimp hnab hch i hi
        (((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot).trans e)
    · exfalso
      rcases i with _ | _ | ⟨d, hv⟩ | _
      · exact hi
      · exact hi
      · have hs := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
        simp only [onLie] at hi
        split at hi
        · simp at hs
        · rename_i q
          have hq2 : q.card = 2 := hi.2
          have hp : q.p = 2 := by
            have := q.card_def
            rw [hq2] at this
            exact ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
              (this ▸ dvd_pow_self q.p q.exponent_pos.ne')).symm.symm
          exact hs.2 hp
        · exact hi
      · exact hi
    · rcases hlin with ⟨n, hn1, hne, hL⟩ | ⟨n, hn1, hno, hL⟩ | hL
      · exact h.sl3 K hKq ⟨n, hn1, hne, hL⟩
      · exact h.su3 K hKq ⟨n, hn1, hno, hL⟩
      · exact h.su6 K hKq hL
    · exfalso
      obtain ⟨-, -, -, -, π, hπs, hπk, -⟩ := hcov
      have f : K ⧸ Subgroup.center K ≃* i.Group :=
        (QuotientGroup.quotientMulEquivOfEq hπk.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective π hπs)
      rcases i with _ | _ | _ | s
      · exact hi
      · exact hi
      · exact hi
      · obtain ⟨-, hs⟩ := hi
        have hs' : k2Spor 3 s := by
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k2Spor]
        exact List93.notChev2_holds _ (.sporadic s) (Or.inl ⟨s, rfl, 3, hs'⟩) ⟨f⟩ hch

end Main

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
