module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Cop
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Cmp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227SL2
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Abs
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpC
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem pPrimeCore_eq_bot {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (W : Subgroup X) [W.Normal]
    (hW0 : ∀ N : Subgroup X, N.Normal → N ≤ W → Nat.Coprime q (Nat.card N) → N = ⊥) :
    CFSG.pPrimeCore q ↥W = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  set N := CFSG.pPrimeCore q ↥W with hNdef
  have hN : (N.map W.subtype).Normal := i227rk_normal_map W N
  have hcop : Nat.Coprime q (Nat.card (N.map W.subtype)) := by
    rw [← Nat.card_congr (N.equivMapOfInjective W.subtype W.subtype_injective).toEquiv]
    exact CFSG.pPrimeCore_coprime_card
  exact (Subgroup.map_eq_bot_iff_of_injective N W.subtype_injective).mp
    (hW0 _ hN (Subgroup.map_subtype_le N) hcop)

theorem quot_dichotomy {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hOut : ∀ J : Subgroup X, IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hperf : commutator X = ⊤) (R W : Subgroup X) [R.Normal] [W.Normal]
    (hW : W = ⁅R, (⊤ : Subgroup X)⁆)
    (hcov : ∀ C : Subgroup X, C.Normal → C ⊔ R = ⊤ → C = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1)
    (hW0 : ∀ N : Subgroup X, N.Normal → N ≤ W → Nat.Coprime q (Nat.card N) → N = ⊥)
    (Q : Subgroup X) (hQ : IsPGroup q Q) (hQc : Nat.card Q = q ^ (Nat.card X).factorization q) :
    W = ⊥ ∨ (coreIn q 3 Q ⊤ = ⊤ ∧
      (4 ≤ CFSG.Open.pRank q Q ∨ (NoCompIn W ∧ 3 ≤ CFSG.Open.pRank q (Q ⊓ W)))) := by
  have : Fact q.Prime := ⟨hq⟩
  have hWR : W ≤ R := hW ▸ Subgroup.commutator_le_left R ⊤
  have hcore : CFSG.pPrimeCore q ↥W = ⊥ := pPrimeCore_eq_bot hq W hW0
  by_cases hnc : NoCompIn W
  · set V : Subgroup X := (CFSG.pCore q ↥W).map W.subtype with hV
    by_cases h3 : 3 ≤ CFSG.Open.pRank q V
    · obtain ⟨h1, h2⟩ := coreIn_eq_top_of_rank_three hq W Q hQc h3
      exact Or.inr ⟨h1, Or.inr ⟨hnc, h2⟩⟩
    · left
      have hVn : V.Normal := i227rk_normal_map W (CFSG.pCore q ↥W)
      have hVp : IsPGroup q V :=
        (CFSG.pCore_isPGroup (p := q) (G := W)).of_equiv
          ((CFSG.pCore q ↥W).equivMapOfInjective W.subtype W.subtype_injective)
      exact eq_bot_of_centralizes hq hperf R W hW hcore hnc
        (centralizes_of_rank_le_two hq hq2 hperf hSL V hVp (card_le_sq_of_not_three_le hq h3))
  · right
    obtain ⟨J, hJW, hJsn, hJq⟩ : ∃ J : Subgroup X, J ≤ W ∧ CFSG.Open.IsSubnormal J ⊤ ∧
        CFSG.Open.IsQuasisimple ↥J := by
      by_contra hno
      exact hnc fun J hJW hJsn hJq => hno ⟨J, hJW, hJsn, hJq⟩
    have hJc : IsComponentOf J ⊤ := ⟨le_top, hJsn, hJq⟩
    have hTop : GLAPPrimeCoreOf q (⊤ : Subgroup X) = GLAPPrimeCore q X := by
      have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso q (Subgroup.topEquiv (G := X))
      have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
        MonoidHom.ext fun _ => rfl
      unfold GLAPPrimeCoreOf
      rw [hsub, h1]
    have hT : GLAPPrimeCore q X ⊓ W = ⊥ :=
      hW0 _ inferInstance inf_le_right
        ((CFSG.pPrimeCore_coprime_card (p := q) (G := X)).coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left))
    have hdvd : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ W → q ∣ Nat.card L := by
      intro L hL hLW
      by_contra hnd
      have hcop : Nat.Coprime q (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
      have h1 : L ≤ GLAPPrimeCoreOf q (⊤ : Subgroup X) := by
        rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.glaPPrimeCoreOf_eq_self_of_coprime
          hcop]
        exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hq hL.2.1
      rw [hTop] at h1
      have h2 : L ≤ GLAPPrimeCore q X ⊓ W := le_inf h1 hLW
      rw [hT, le_bot_iff] at h2
      have hnt : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h2
    set O : Set (Subgroup X) := Set.range fun k : X => GLBConj k J with hO
    have hOc : ∀ L ∈ O, IsComponentOf L ⊤ := by
      rintro _ ⟨k, rfl⟩
      exact CFSG.LocalAnalysis.GLTheoremB.isComponentOf_gLBConj hJc k
    have hOW : ∀ L ∈ O, L ≤ W := by
      rintro _ ⟨k, rfl⟩ x hx
      have h1 : k * x * k⁻¹ ∈ J := CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj.1 hx
      have h2 := (inferInstance : W.Normal).conj_mem _ (hJW h1) k⁻¹
      simpa [mul_assoc] using h2
    rcases i227cmp_orbit_dichotomy hperf J with h5 | hnorm
    · change 5 ≤ Nat.card O at h5
      have hconj : ∀ k : X, ∀ L ∈ O, GLBConj k L ∈ O := by
        rintro k _ ⟨k', rfl⟩
        exact ⟨k' * k, by simp only [CFSG.LocalAnalysis.GLTheoremB.gLBConj_gLBConj]⟩
      have hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = q ∧ ∃ y ∈ L, x * y ≠ y * x := by
        intro L hL
        obtain ⟨x, hx, hxc⟩ :=
          CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
            (hOc L hL).2.2 hq hq2 (hdvd L (hOc L hL) (hOW L hL))
        refine ⟨x, x.2, ?_, ?_⟩
        · rw [← hx]; exact Subgroup.orderOf_coe x
        · by_contra hno
          push Not at hno
          refine hxc (Subgroup.mem_center_iff.2 fun g => ?_)
          exact Subtype.ext (hno g g.2).symm
      have hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := by
        intro L hL L' hL' hne a ha b hb
        have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hOc L hL)
          (hOc L' hL') hne
        have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator ha hb
        rw [h, Subgroup.mem_bot] at hmem
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [hmem, one_mul]
      obtain ⟨h1, h2⟩ := core_comps hq O hconj (by omega) hx hcomm Q hQ hQc
      exact ⟨h1, Or.inl h2⟩
    · have hN : J.Normal := ⟨fun n hn g => by
        have : n ∈ GLBConj g J := by rw [hnorm g]; exact hn
        exact CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj.1 this⟩
      exact (i227cmp_not_normal hperf (hJW.trans hWR) hJq (hOut J hJc) hcov).elim

private theorem coreIn_eq_top_core {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hOut : ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A → ∀ {J : Subgroup A},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hK : CFSG.Open.IsKGroup X) (hperf : commutator X = ⊤) (R W : Subgroup X) [R.Normal]
    [W.Normal] (hW : W = ⁅R, (⊤ : Subgroup X)⁆)
    (hcov : ∀ C : Subgroup X, C.Normal → C ⊔ R = ⊤ → C = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1)
    (Q : Subgroup X) (hQ : IsPGroup q Q) (hQc : Nat.card Q = q ^ (Nat.card X).factorization q)
    (hrk : 4 ≤ CFSG.Open.pRank q (Q.map (QuotientGroup.mk' W)))
    (hquot : coreIn q 3 (Q.map (QuotientGroup.mk' W)) ⊤ = ⊤)
    (hres : CFSG.Open.pRank q (Q ⊓ W) = 3 → 4 ≤ CFSG.Open.pRank q Q ∨
      ∃ M : Subgroup X, ∃ _ : M.Normal, W ≤ M ∧ (∀ N : Subgroup X, N.Normal → N ≠ ⊤ → N ≤ M) ∧
        4 ≤ CFSG.Open.pRank q (Q.map (QuotientGroup.mk' M))) :
    coreIn q 3 Q ⊤ = ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  have hWR : W ≤ R := hW ▸ Subgroup.commutator_le_left R ⊤
  set Y : Subgroup X := GLAPPrimeCore q X ⊓ W with hY
  have hYcop : Nat.Coprime q (Nat.card Y) :=
    (CFSG.pPrimeCore_coprime_card (p := q) (G := X)).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hYW : Y ≤ W := inf_le_right
  set π : X →* X ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hker : π.ker = Y := QuotientGroup.ker_mk' Y
  have hQY : Q ⊓ Y = ⊥ := pGroup_inf_eq_bot_of_coprime hQ hYcop
  have hinjQ : ∀ {T : Subgroup X}, T ≤ Q → ∀ x ∈ T, π x = 1 → x = 1 := by
    intro T hT x hx h1
    have hxY : x ∈ Y := (QuotientGroup.eq_one_iff x).1 h1
    have : x ∈ Q ⊓ Y := ⟨hT hx, hxY⟩
    rwa [hQY, Subgroup.mem_bot] at this
  have hmemW : ∀ a w : X, w ∈ W → π w = π a → a ∈ W := by
    intro a w hw hwa
    have h1 : w⁻¹ * a ∈ Y := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hwa, inv_mul_cancel]
    have := W.mul_mem hw (hYW h1)
    simpa using this
  set R₁ : Subgroup (X ⧸ Y) := R.map π with hR₁
  set W₁ : Subgroup (X ⧸ Y) := W.map π with hW₁
  have hR₁n : R₁.Normal := Subgroup.Normal.map inferInstance π hπs
  have hW₁n : W₁.Normal := Subgroup.Normal.map inferInstance π hπs
  have hW₁eq : W₁ = ⁅R₁, (⊤ : Subgroup (X ⧸ Y))⁆ := by
    have h := congrArg (Subgroup.map π) hW
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs] at h
    exact h
  have hperf₁ : commutator (X ⧸ Y) = ⊤ := by
    have : Group.IsPerfect X := Group.isPerfect_def.2 hperf
    exact (Group.IsPerfect.ofSurjective hπs).commutator_eq_top
  have hK₁ : CFSG.Open.IsKGroup (X ⧸ Y) := hK.of_surjective π hπs
  have hcov₁ : ∀ C : Subgroup (X ⧸ Y), C.Normal → C ⊔ R₁ = ⊤ → C = ⊤ := by
    intro C hC hCR
    have hRc : R₁.comap π = R := by
      rw [hR₁, Subgroup.comap_map_eq, hker]
      exact sup_eq_left.2 (hYW.trans hWR)
    have h1 : C.comap π ⊔ R = ⊤ := by
      rw [← hRc, Subgroup.comap_sup_eq π C R₁ hπs, hCR, Subgroup.comap_top]
    have h2 := hcov (C.comap π) (Subgroup.Normal.comap hC π) h1
    rw [← Subgroup.map_comap_eq_self_of_surjective hπs C, h2,
      Subgroup.map_top_of_surjective π hπs]
  have hSL₁ : ∀ φ : X ⧸ Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1 := by
    intro φ
    have h := hSL (φ.comp π)
    refine MonoidHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hπs x
    exact DFunLike.congr_fun h y
  have hW0₁ : ∀ N : Subgroup (X ⧸ Y), N.Normal → N ≤ W₁ → Nat.Coprime q (Nat.card N) →
      N = ⊥ := by
    intro N hN hNW hNc
    have hpre : Nat.Coprime q (Nat.card (N.comap π)) := by
      have h : Nat.card (N.comap π) = Nat.card Y * Nat.card N :=
        QuotientGroup.card_preimage_mk Y (N : Set (X ⧸ Y))
      rw [h]
      exact hYcop.mul_right hNc
    have hle : N.comap π ≤ Y := by
      refine le_inf (le_sSup ⟨Subgroup.Normal.comap hN π, hpre⟩) ?_
      intro x hx
      obtain ⟨w, hw, hwx⟩ := hNW hx
      exact hmemW x w hw hwx
    have h2 : N ≤ Y.map π := by
      calc N = (N.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs N).symm
        _ ≤ _ := Subgroup.map_mono hle
    rw [(Subgroup.map_eq_bot_iff Y).2 (by rw [hker])] at h2
    exact le_bot_iff.1 h2
  have hQ₁ : IsPGroup q (Q.map π) := hQ.map π
  have hQ₁c : Nat.card (Q.map π) = q ^ (Nat.card (X ⧸ Y)).factorization q := by
    have := ((Sylow.ofCard Q hQc).mapSurjective hπs).card_eq_multiplicity
    rwa [Sylow.coe_mapSurjective, Sylow.coe_ofCard] at this
  rcases quot_dichotomy hq hq2 (fun J hJ => hOut _ hK₁ hJ) hperf₁ R₁ W₁ hW₁eq hcov₁ hSL₁ hW0₁
      (Q.map π) hQ₁ hQ₁c with hbot | ⟨hcore₁, hrk₁⟩
  · have hWY : W ≤ Y := by
      intro w hw
      have : π w ∈ W₁ := Subgroup.mem_map_of_mem π hw
      rw [hbot, Subgroup.mem_bot] at this
      rw [← hker]
      exact this
    have hWcop : Nat.Coprime q (Nat.card W) :=
      hYcop.coprime_dvd_right (Subgroup.card_dvd_of_le hWY)
    have hQW : Q ⊓ W = ⊥ := pGroup_inf_eq_bot_of_coprime hQ hWcop
    have hinjW : ∀ x ∈ Q, QuotientGroup.mk' W x = 1 → x = 1 := by
      intro x hx h1
      have hxW : x ∈ W := (QuotientGroup.eq_one_iff x).1 h1
      have : x ∈ Q ⊓ W := ⟨hx, hxW⟩
      rwa [hQW, Subgroup.mem_bot] at this
    have hrkQ : 4 ≤ CFSG.Open.pRank q Q :=
      hrk.trans (i227cop_pRank_map_le (QuotientGroup.mk' W) hinjW hq1)
    exact coreIn_eq_top_of_quotient hq W hWcop Q hQ hrkQ hquot
  · have hrkQ : 4 ≤ CFSG.Open.pRank q Q := by
      rcases hrk₁ with h4 | ⟨hnc₁, h3⟩
      · exact h4.trans (i227cop_pRank_map_le π (hinjQ le_rfl) hq1)
      · have hle : Q.map π ⊓ W₁ ≤ (Q ⊓ W).map π := by
          rintro _ ⟨⟨a, ha, rfl⟩, hw⟩
          obtain ⟨w, hw, hwa⟩ := hw
          exact ⟨a, ⟨ha, hmemW a w hw hwa⟩, rfl⟩
        have hr₁ : CFSG.Open.pRank q (Q.map π ⊓ W₁) ≤ CFSG.Open.pRank q (Q ⊓ W) :=
          (CFSG.SectionRank.pRank_mono hq1 hle).trans
            (i227cop_pRank_map_le π (hinjQ inf_le_left) hq1)
        have hQW3 : 3 ≤ CFSG.Open.pRank q (Q ⊓ W) := h3.trans hr₁
        rcases (show 4 ≤ CFSG.Open.pRank q (Q ⊓ W) ∨ CFSG.Open.pRank q (Q ⊓ W) = 3 by omega)
          with h | h
        · exact h.trans (CFSG.SectionRank.pRank_mono hq1 inf_le_left)
        · rcases hres h with h4 | ⟨M, hMn, hWM, hM, hrkM⟩
          · exact h4
          ·
            exfalso
            let φ₁ : X ⧸ Y →* X ⧸ M :=
              QuotientGroup.map Y M (MonoidHom.id X)
                (by rw [Subgroup.comap_id]; exact hYW.trans hWM)
            have hker₁ : ∀ N : Subgroup (X ⧸ Y), N.Normal → N ≠ ⊤ → N ≤ φ₁.ker := by
              intro N hN hNt n hn
              obtain ⟨x, rfl⟩ := hπs n
              have hne : N.comap π ≠ ⊤ := by
                intro htop
                apply hNt
                rw [← Subgroup.map_comap_eq_self_of_surjective hπs N, htop,
                  Subgroup.map_top_of_surjective π hπs]
              have hxM : x ∈ M := hM _ (Subgroup.Normal.comap hN π) hne hn
              rw [MonoidHom.mem_ker]
              exact (QuotientGroup.eq_one_iff x).2 hxM
            have hcomp : φ₁.comp π = QuotientGroup.mk' M := MonoidHom.ext fun _ => rfl
            have hmap : (Q.map π).map φ₁ = Q.map (QuotientGroup.mk' M) := by
              rw [Subgroup.map_map, hcomp]
            have hW₁bot : W₁ = ⊥ :=
              eq_bot_of_four_le_pRank_map hq hq2 hperf₁ R₁ W₁ hW₁eq (pPrimeCore_eq_bot hq W₁ hW0₁)
                hnc₁ φ₁ hker₁ (Q.map π) hQ₁ hQ₁c (hr₁.trans h.le) (by rw [hmap]; exact hrkM)
            rw [hW₁bot, inf_bot_eq] at h3
            have h0 : CFSG.Open.pRank q (⊥ : Subgroup (X ⧸ Y)) ≤ 0 :=
              CFSG.SectionRank.pRank_le hq1 fun E hE _ => by
                rw [le_bot_iff.1 hE, Subgroup.card_bot, pow_zero]
            omega
    exact coreIn_eq_top_of_quotient hq Y hYcop Q hQ hrkQ hcore₁

theorem coreIn_eq_top_of_rankM {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hOut : ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A → ∀ {J : Subgroup A},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J))
    (hK : CFSG.Open.IsKGroup X) (hperf : commutator X = ⊤) (R W : Subgroup X) [R.Normal]
    [W.Normal] (hW : W = ⁅R, (⊤ : Subgroup X)⁆)
    (hcov : ∀ C : Subgroup X, C.Normal → C ⊔ R = ⊤ → C = ⊤)
    (hSL : ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1)
    (Q : Subgroup X) (hQ : IsPGroup q Q) (hQc : Nat.card Q = q ^ (Nat.card X).factorization q)
    (hrk : 4 ≤ CFSG.Open.pRank q (Q.map (QuotientGroup.mk' W)))
    (hquot : coreIn q 3 (Q.map (QuotientGroup.mk' W)) ⊤ = ⊤) (M : Subgroup X) [M.Normal]
    (hWM : W ≤ M) (hM : ∀ N : Subgroup X, N.Normal → N ≠ ⊤ → N ≤ M)
    (hrkM : 4 ≤ CFSG.Open.pRank q (Q.map (QuotientGroup.mk' M))) :
    coreIn q 3 Q ⊤ = ⊤ :=
  coreIn_eq_top_core hq hq2 hOut hK hperf R W hW hcov hSL Q hQ hQc hrk hquot fun _ =>
    Or.inr ⟨M, inferInstance, hWM, hM, hrkM⟩

end CFSG.LocalAnalysis.GLTheoremA.H248L227
