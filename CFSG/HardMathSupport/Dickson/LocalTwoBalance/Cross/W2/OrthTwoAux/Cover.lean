module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Rank2

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem rank_two_cover' (hK : Nat.card K = 2) (ρ : Multiplicative Z3 →* Module.End K V)
    (h8 : 8 ≤ finrank K V) (hz₃ : act ρ ![0, 0, 1] = 1) (he1 : act ρ ![1, 0, 0] ≠ 1)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp0 : Even (finrank K (fixOf ρ Set.univ))) {G : V ≃ₗ[K] V}
    (hGact : ∀ z v, G (act ρ z v) = act ρ z (G v)) {k : ℕ} (hgk : Nat.Coprime 3 k)
    (hGk' : ∀ w, ((G : V →ₗ[K] V) ^ k) w = w)
    (hrefl : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → 4 ≤ finrank K (fixOf ρ {z}) →
      commSpace G ≤ fixOf ρ {z} → finrank K (commSpace G) ≠ 1)
    (hfixV : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → GoodSix ρ z → ∀ v ∈ fixOf ρ {z}, G v = v)
    (hfixU : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → 8 ≤ finrank K (LinearMap.ker (eCyc ρ z)) →
      ∀ v ∈ LinearMap.ker (eCyc ρ z), G v = v) :
    ∀ v, G v = v := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have h2 : ∀ v : V, v + v = 0 := two_smul_eq_zero K
  set r₀ := finrank K (LinearMap.range (e0 ρ)) with hr₀def
  set r : Z3 → ℕ := fun φ => finrank K (LinearMap.range (isoP ρ φ)) with hrdef
  have hr₀ : Even r₀ := by rw [hr₀def, range_e0]; exact hp0
  have hr : ∀ φ ∈ Rset, Even (r φ) := by
    intro φ hφ
    have h1 := hpN φ hφ
    rw [finrank_fixOf_N_eq ρ hφ] at h1
    exact (Nat.even_add.1 h1).1 hr₀
  have hN : r₀ + ∑ φ ∈ Rset, r φ = finrank K V := (finrank_eq_sum_isoP ρ).symm
  have heCyc₃ : eCyc ρ ![0, 0, 1] = 1 := by
    ext w
    simp only [eCyc, LinearMap.add_apply, act_zero, act_add, hz₃, mul_one, Module.End.one_apply]
    rw [h2, zero_add]
  have hisoP0 : ∀ φ ∈ Rset, dot φ ![0, 0, 1] ≠ 0 → ∀ v, isoP ρ φ v = 0 := by
    intro φ _ hd v
    have h1 := eCyc_isoP ρ φ ![0, 0, 1] v
    simp only [hd, ↓reduceIte, heCyc₃, Module.End.one_apply] at h1
    exact h1
  have hr0' : ∀ φ ∈ Rset, dot φ ![0, 0, 1] ≠ 0 → r φ = 0 := by
    intro φ hφ hd
    have : LinearMap.range (isoP ρ φ) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨v, rfl⟩
      rw [hisoP0 φ hφ hd v]
      exact Submodule.zero_mem _
    show finrank K (LinearMap.range (isoP ρ φ)) = 0
    rw [this, finrank_bot]
  have hdimx : ∀ φ ∈ Rset, dot φ ![0, 0, 1] = 0 →
      finrank K (fixOf ρ {xOf φ}) = r₀ + r φ := by
    intro φ hφ hd
    rw [finrank_fixOf_single_eq ρ (xOf φ)]
    congr 1
    refine Finset.sum_eq_single_of_mem φ (Finset.mem_filter.2 ⟨hφ, dot_xOf φ⟩) ?_
    intro ψ hψ hne
    obtain ⟨hψR, hψx⟩ := Finset.mem_filter.1 hψ
    by_cases hψd : dot ψ ![0, 0, 1] = 0
    · exact absurd (eq_of_dot_xOf φ hφ ψ hψR hd hψd hψx) hne
    · exact hr0' ψ hψR hψd
  have hsub_fix : ∀ φ ∈ Rset, ∀ x, dot φ x = 0 →
      LinearMap.range (isoP ρ φ) ≤ fixOf ρ {x} := by
    rintro φ - x hx _ ⟨w, rfl⟩
    have h1 := eCyc_isoP ρ φ x w
    simp only [hx, ↓reduceIte] at h1
    rw [← h1]
    exact eCyc_mem_fixOf ρ x _
  have hmoves : ∀ φ ∈ Rset, ∀ y, dot φ y ≠ 0 → ∀ u ∈ LinearMap.range (isoP ρ φ),
      act ρ y u = u → u = 0 := by
    rintro φ - y hy _ ⟨w, rfl⟩ hfix
    have h1 := eCyc_isoP ρ φ y w
    simp only [hy, ↓reduceIte] at h1
    have hyy : act ρ (y + y) (isoP ρ φ w) = isoP ρ φ w := by
      rw [act_add, Module.End.mul_apply, hfix, hfix]
    simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, hfix, hyy] at h1
    rw [h2, zero_add] at h1
    exact h1
  have hGe0 : ∀ v, G (e0 ρ v) = e0 ρ (G v) := fun v => by
    simp only [e0, LinearMap.sum_apply, map_sum, hGact]
  have hGeN : ∀ φ v, G (eN ρ φ v) = eN ρ φ (G v) := fun φ v => by
    simp only [eN, LinearMap.sum_apply, map_sum, hGact]
  have hGiso : ∀ φ v, G (isoP ρ φ v) = isoP ρ φ (G v) := fun φ v => by
    simp only [isoP, LinearMap.add_apply, map_add, hGe0, hGeN]
  have hF4 : ∀ φ ∈ Rset, r φ = 2 → ∀ v ∈ LinearMap.range (isoP ρ φ), G v = v := by
    intro φ hφ hrφ
    obtain ⟨y, hy⟩ := exists_dot_ne φ hφ
    refine eq_of_commute_of_cyc3 hK (W := LinearMap.range (isoP ρ φ)) hrφ (X := act ρ y)
      (G := (G : V →ₗ[K] V)) ?_ ?_ ?_ ?_ ?_ hgk fun w _ => hGk' w
    · rintro _ ⟨w, rfl⟩
      have : act ρ y (isoP ρ φ w) = isoP ρ φ (act ρ y w) := by
        simp only [isoP, LinearMap.add_apply, map_add, act_eN_comm, act_e0, e0_act]
      rw [this]
      exact ⟨_, rfl⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨G w, (hGiso φ w).symm⟩
    · rintro _ ⟨w, rfl⟩
      have h1 := eCyc_isoP ρ φ y w
      simp only [hy, ↓reduceIte, eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply,
        act_add, Module.End.mul_apply] at h1
      rw [← h1]
      abel
    · intro w _
      exact hGact y w
    · intro w _ hw
      exact G.injective (hw.trans (map_zero G).symm)
  have hY : ∀ φ ∈ Rset, ∀ v ∈ LinearMap.range (isoP ρ φ), G v = v := by
    intro φ hφ v hv
    have hzero : r φ = 0 → G v = v := fun h0 => by
      have : LinearMap.range (isoP ρ φ) = ⊥ := Submodule.finrank_eq_zero.1 h0
      rw [this, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    by_cases hd : dot φ ![0, 0, 1] = 0
    swap
    · exact hzero (hr0' φ hφ hd)
    obtain ⟨c, hc⟩ := hr φ hφ
    rcases (show c = 0 ∨ c = 1 ∨ 2 ≤ c by omega) with h0 | h1 | h4
    · exact hzero (by omega)
    · exact hF4 φ hφ (by omega) v hv
    · by_cases h6 : 6 ≤ r₀ + r φ
      ·
        have hne : LinearMap.range (isoP ρ φ) ≠ ⊥ := fun h => by
          have : r φ = 0 := by
            show finrank K (LinearMap.range (isoP ρ φ)) = 0
            rw [h, finrank_bot]
          omega
        obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        obtain ⟨y, hy⟩ := exists_dot_ne φ hφ
        have hgood : GoodSix ρ (xOf φ) := by
          refine ⟨fun h => ?_, by rw [hdimx φ hφ hd]; exact h6, y, u,
            hsub_fix φ hφ (xOf φ) (dot_xOf φ) hu, fun h => hu0 (hmoves φ hφ y hy u hu h)⟩
          rcases xOf_ne φ hφ hd with h' | h'
          · exact h' (by rw [h]; rfl)
          · exact h' (by rw [h]; rfl)
        exact hfixV (xOf φ) (xOf_ne φ hφ hd) hgood v
          (hsub_fix φ hφ (xOf φ) (dot_xOf φ) hv)
      ·
        have hr₀0 : r₀ = 0 := by
          obtain ⟨a, ha⟩ := hr₀
          omega
        have hrφ4 : r φ = 4 := by omega
        obtain ⟨ψ, hψ, hψd, hψφ, hψ8⟩ :
            ∃ ψ ∈ Rset, dot ψ ![0, 0, 1] = 0 ∧ ψ ≠ φ ∧ r ψ + 8 ≤ finrank K V := by
          by_contra hall
          push Not at hall
          set L := Rset.filter (fun ψ => dot ψ ![0, 0, 1] = 0) with hL
          have hφL : φ ∈ L := Finset.mem_filter.2 ⟨hφ, hd⟩
          have hNL : finrank K V = ∑ ψ ∈ L, r ψ := by
            rw [← hN, hr₀0, zero_add]
            exact (Finset.sum_subset (Finset.filter_subset _ _) fun ψ hψ hnot =>
              hr0' ψ hψ fun hd => hnot (Finset.mem_filter.2 ⟨hψ, hd⟩)).symm
          have hge : ∀ ψ ∈ L.erase φ, 2 ≤ r ψ ∧ finrank K V ≤ r ψ + 7 := by
            intro ψ hψ
            obtain ⟨hψR, hψd⟩ := Finset.mem_filter.1 (Finset.mem_of_mem_erase hψ)
            have hne := Finset.ne_of_mem_erase hψ
            have h' := hall ψ hψR hψd hne
            obtain ⟨a, ha⟩ := hr ψ hψR
            constructor <;> omega
          have hcardL : (L.erase φ).card = 3 := by
            rw [Finset.card_erase_of_mem hφL, hL, card_rank_two_points]
          have hs1 : ∑ _ψ ∈ L.erase φ, 2 ≤ ∑ ψ ∈ L.erase φ, r ψ :=
            Finset.sum_le_sum fun ψ hψ => (hge ψ hψ).1
          have hs2 : ∑ _ψ ∈ L.erase φ, (finrank K V - 7) ≤ ∑ ψ ∈ L.erase φ, r ψ :=
            Finset.sum_le_sum fun ψ hψ => by have := (hge ψ hψ).2; omega
          rw [Finset.sum_const, hcardL, smul_eq_mul] at hs1 hs2
          have hsplit : ∑ ψ ∈ L, r ψ = r φ + ∑ ψ ∈ L.erase φ, r ψ :=
            (Finset.add_sum_erase _ _ hφL).symm
          omega
        have hdimker : 8 ≤ finrank K (LinearMap.ker (eCyc ρ (xOf ψ))) := by
          have hrk := LinearMap.finrank_range_add_finrank_ker (eCyc ρ (xOf ψ))
          rw [range_eCyc ρ (xOf ψ), hdimx ψ hψ hψd] at hrk
          omega
        have hvker : v ∈ LinearMap.ker (eCyc ρ (xOf ψ)) := by
          obtain ⟨w, rfl⟩ := hv
          have hne : ¬ dot φ (xOf ψ) = 0 := fun h => hψφ (eq_of_dot_xOf ψ hψ φ hφ hψd hd h).symm
          rw [LinearMap.mem_ker, eCyc_isoP ρ φ (xOf ψ) w, if_neg hne]
        exact hfixU (xOf ψ) (xOf_ne ψ hψ hψd) hdimker v hvker
  have hdecomp : ∀ v, G v - v = G (e0 ρ v) - e0 ρ v := by
    intro v
    conv_lhs => rw [← e0_add_sum_isoP ρ v]
    rw [map_add, map_sum, Finset.sum_congr rfl fun φ hφ => hY φ hφ _ ⟨v, rfl⟩]
    abel
  have hW₀ : ∀ v ∈ LinearMap.range (e0 ρ), G v = v := by
    intro v hv
    have hGW : ∀ w ∈ LinearMap.range (e0 ρ), (G : V →ₗ[K] V) w ∈ LinearMap.range (e0 ρ) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨G w, (hGe0 w).symm⟩
    have hexists : ∃ φ ∈ Rset, dot φ ![0, 0, 1] = 0 ∧ r φ ≠ 0 := by
      by_contra hall
      push Not at hall
      have hsum0 : ∑ φ ∈ Rset, r φ = 0 := Finset.sum_eq_zero fun φ hφ => by
        by_cases hd : dot φ ![0, 0, 1] = 0
        · exact hall φ hφ hd
        · exact hr0' φ hφ hd
      have hfull : fixOf ρ Set.univ = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← range_e0, ← hr₀def]
        omega
      apply he1
      refine LinearMap.ext fun w => ?_
      have : w ∈ fixOf ρ Set.univ := hfull ▸ Submodule.mem_top
      exact this _ (Set.mem_univ _)
    have hlayer : ∀ φ ∈ Rset, dot φ ![0, 0, 1] = 0 → r φ ≠ 0 → 6 ≤ r₀ + r φ →
        ∀ v ∈ LinearMap.range (e0 ρ), G v = v := by
      intro φ hφ hd hrφ h6 v hv
      have hne : LinearMap.range (isoP ρ φ) ≠ ⊥ := fun h => hrφ (by
        show finrank K (LinearMap.range (isoP ρ φ)) = 0
        rw [h, finrank_bot])
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨y, hy⟩ := exists_dot_ne φ hφ
      have hgood : GoodSix ρ (xOf φ) := by
        refine ⟨fun h => ?_, by rw [hdimx φ hφ hd]; exact h6, y, u,
          hsub_fix φ hφ (xOf φ) (dot_xOf φ) hu, fun h => hu0 (hmoves φ hφ y hy u hu h)⟩
        rcases xOf_ne φ hφ hd with h' | h'
        · exact h' (by rw [h]; rfl)
        · exact h' (by rw [h]; rfl)
      exact hfixV (xOf φ) (xOf_ne φ hφ hd) hgood v
        (fixOf_univ_le ρ {xOf φ} (by rw [← range_e0]; exact hv))
    obtain ⟨c, hc⟩ := hr₀
    rcases (show c = 0 ∨ c = 1 ∨ 2 ≤ c by omega) with h0 | h1 | h4
    · have : LinearMap.range (e0 ρ) = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      rw [this, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    ·
      have hr₀2 : finrank K (LinearMap.range (e0 ρ)) = 2 := by omega
      by_cases hbig : ∃ φ ∈ Rset, dot φ ![0, 0, 1] = 0 ∧ 4 ≤ r φ
      · obtain ⟨φ, hφ, hd, hφ4⟩ := hbig
        exact hlayer φ hφ hd (by omega) (by omega) v hv
      · push Not at hbig
        have hcomm_le : commSpace G ≤ LinearMap.range (e0 ρ) := by
          rintro _ ⟨w, rfl⟩
          rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, hdecomp w]
          exact Submodule.sub_mem _ (hGW _ ⟨w, rfl⟩) ⟨w, rfl⟩
        have hle := Submodule.finrank_mono hcomm_le
        have hm1 : finrank K (commSpace G) ≠ 1 := by
          obtain ⟨φ, hφ, hd, hrφ⟩ := hexists
          obtain ⟨a, ha⟩ := hr φ hφ
          exact hrefl (xOf φ) (xOf_ne φ hφ hd) (by rw [hdimx φ hφ hd]; omega)
            (hcomm_le.trans ((range_e0 ρ).le.trans (fixOf_univ_le ρ _)))
        rcases (show finrank K (commSpace G) = 0 ∨ finrank K (commSpace G) = 2 by omega) with
          hm0 | hm2
        ·
          have : commSpace G = ⊥ := Submodule.finrank_eq_zero.1 hm0
          have h1 : G v - v ∈ commSpace G := sub_mem_commSpace G v
          rw [this, Submodule.mem_bot, sub_eq_zero] at h1
          exact h1
        ·
          have heq : commSpace G = LinearMap.range (e0 ρ) :=
            Submodule.eq_of_le_of_finrank_eq hcomm_le (by omega)
          have hfix : ∀ w ∈ LinearMap.range (e0 ρ), (G : V →ₗ[K] V) w = w → w = 0 := by
            intro w hw hGw
            let f : LinearMap.range (e0 ρ) →ₗ[K] LinearMap.range (e0 ρ) :=
              ((G : V →ₗ[K] V) - 1).restrict fun x hx => by
                rw [LinearMap.sub_apply, Module.End.one_apply]
                exact Submodule.sub_mem _ (hGW x hx) hx
            have hsurj : Function.Surjective f := by
              rintro ⟨u, hu⟩
              rw [← heq] at hu
              obtain ⟨x, hx⟩ := mem_commSpace.1 hu
              refine ⟨⟨e0 ρ x, ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
              change (G : V →ₗ[K] V) (e0 ρ x) - e0 ρ x = u
              rw [LinearEquiv.coe_coe, ← hdecomp x, hx]
            have hinjf : Function.Injective f := LinearMap.injective_iff_surjective.2 hsurj
            have h1 : f ⟨w, hw⟩ = 0 := Subtype.ext (by
              change (G : V →ₗ[K] V) w - w = 0
              rw [hGw, sub_self])
            have h2' := hinjf (h1.trans (map_zero f).symm)
            exact congrArg Subtype.val h2'
          have hGinj : ∀ w ∈ LinearMap.range (e0 ρ), (G : V →ₗ[K] V) w = 0 → w = 0 :=
            fun w _ hw => G.injective (hw.trans (map_zero G).symm)
          have hcyc := cyc3_of_no_fixed hK hr₀2 hGW hGinj hfix
          exact eq_of_commute_of_cyc3 hK hr₀2 hGW hGW hcyc (fun w _ => rfl) hGinj hgk
            (fun w _ => hGk' w) v hv
    ·
      obtain ⟨φ, hφ, hd, hrφ⟩ := hexists
      obtain ⟨a, ha⟩ := hr φ hφ
      exact hlayer φ hφ hd hrφ (by omega) v hv
  intro v
  have h1 := hdecomp v
  rw [hW₀ _ ⟨v, rfl⟩, sub_self, sub_eq_zero] at h1
  exact h1

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
