module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Two
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace)

section Points

@[expose] def xOf (φ : Z3) : Z3 := ![φ 1, 2 * φ 0, 0]

theorem dot_xOf : ∀ φ : Z3, dot φ (xOf φ) = 0 := by
  decide

theorem xOf_ne : ∀ φ ∈ Rset, dot φ ![0, 0, 1] = 0 → xOf φ 0 ≠ 0 ∨ xOf φ 1 ≠ 0 := by
  decide

theorem eq_of_dot_xOf : ∀ φ ∈ Rset, ∀ ψ ∈ Rset, dot φ ![0, 0, 1] = 0 →
    dot ψ ![0, 0, 1] = 0 → dot ψ (xOf φ) = 0 → ψ = φ := by
  decide

theorem e1_ne_zero : (![1, 0, 0] : Z3) 0 ≠ 0 := by
  decide

theorem exists_dot_ne : ∀ φ ∈ Rset, ∃ y : Z3, dot φ y ≠ 0 := by
  decide

theorem card_rank_two_points : (Rset.filter (fun φ => dot φ ![0, 0, 1] = 0)).card = 4 := by
  decide

end Points

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth2_fixes_fixedSpace_of_mem_delta (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H E) (x : orthDerived Q)
    (hxo : orderOf x = 3) (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    (h6 : 6 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))) {y : V ≃ₗ[K] V}
    (hyM : y ∈ isometryCentralizer Q (x : V ≃ₗ[K] V)) (hy3 : y ^ 3 = 1) {u : V}
    (hu : u ∈ fixedSpace (x : V ≃ₗ[K] V)) (hyu : y u ≠ u) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGx : G * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * G)
    (hGg : ∀ y : orthDerived Q, g (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q)) :
    ∀ v ∈ fixedSpace (x : V ≃ₗ[K] V), G v = v := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have hmk := mk_injective_of_card_two (Q := Q) hK
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxo
  obtain ⟨w, hw, hw3, hw1⟩ := orth_exists_supported_of_moves hx hyM hy3 hu hyu
  have hF := orth2_fixedComponentImage_le_fixSub hK hQ hT hinj (H := H) (E := E) hH hg x hxo he
    hw hw3 hw1 h6
  have hcommF : ∀ f ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V), G * f = f * G := by
    intro f hf
    have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
    have hmem : (QuotientGroup.mk (⟨f, hfΩ⟩ : orthDerived Q) : ProjOrthDerived Q) ∈
        fixedComponentImage Q (x : V ≃ₗ[K] V) :=
      ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    have h1 := mem_fixSub.1 (hF hmem)
    rw [hGg] at h1
    have h2 : G * f * G⁻¹ = f := congrArg Subtype.val (hmk h1)
    calc G * f = G * f * G⁻¹ * G := by group
      _ = f * G := by rw [h2]
  exact orth2_fixes_fixedSpace hK hQ hx h6 hGO hGx hcommF

omit [Finite K] in
theorem rank_two_cover (hK : Nat.card K = 2) (ρ : Multiplicative Z3 →* Module.End K V)
    (h8 : finrank K V = 8) (hz₃ : act ρ ![0, 0, 1] = 1) (he1 : act ρ ![1, 0, 0] ≠ 1)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp0 : Even (finrank K (fixOf ρ Set.univ))) {G : V ≃ₗ[K] V}
    (hGact : ∀ z v, G (act ρ z v) = act ρ z (G v)) {k : ℕ} (hgk : Nat.Coprime 3 k)
    (hGk' : ∀ w, ((G : V →ₗ[K] V) ^ k) w = w) (heven : Even (finrank K (commSpace G)))
    (hfixV : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → GoodSix ρ z → ∀ v ∈ fixOf ρ {z}, G v = v)
    (hfixU : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → finrank K (fixOf ρ {z}) = 0 → ∀ v, G v = v) :
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
  have hN : r₀ + ∑ φ ∈ Rset, r φ = 8 := by rw [← h8]; exact (finrank_eq_sum_isoP ρ).symm
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
        obtain ⟨ψ, hψ, hψd, hψ0⟩ : ∃ ψ ∈ Rset, dot ψ ![0, 0, 1] = 0 ∧ r ψ = 0 := by
          by_contra hall
          push Not at hall
          set L := Rset.filter (fun ψ => dot ψ ![0, 0, 1] = 0) with hL
          have hφL : φ ∈ L := Finset.mem_filter.2 ⟨hφ, hd⟩
          have hge : ∀ ψ ∈ L.erase φ, 2 ≤ r ψ := by
            intro ψ hψ
            obtain ⟨hψR, hψd⟩ := Finset.mem_filter.1 (Finset.mem_of_mem_erase hψ)
            obtain ⟨a, ha⟩ := hr ψ hψR
            have := hall ψ hψR hψd
            omega
          have hsumL : ∑ ψ ∈ L, r ψ ≤ ∑ ψ ∈ Rset, r ψ :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          have hsplit : ∑ ψ ∈ L, r ψ = r φ + ∑ ψ ∈ L.erase φ, r ψ :=
            (Finset.add_sum_erase _ _ hφL).symm
          have hlow : ∑ _ψ ∈ L.erase φ, 2 ≤ ∑ ψ ∈ L.erase φ, r ψ := Finset.sum_le_sum hge
          have hcardL : (L.erase φ).card = 3 := by
            rw [Finset.card_erase_of_mem hφL, hL, card_rank_two_points]
          rw [Finset.sum_const, hcardL, smul_eq_mul] at hlow
          omega
        exact hfixU (xOf ψ) (xOf_ne ψ hψ hψd) (by rw [hdimx ψ hψ hψd, hr₀0, hψ0]) v
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
    obtain ⟨c, hc⟩ := hr₀
    rcases (show c = 0 ∨ c = 1 ∨ 2 ≤ c by omega) with h0 | h1 | h4
    · have : LinearMap.range (e0 ρ) = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      rw [this, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    ·
      have hr₀2 : finrank K (LinearMap.range (e0 ρ)) = 2 := by omega
      have hcomm_le : commSpace G ≤ LinearMap.range (e0 ρ) := by
        rintro _ ⟨w, rfl⟩
        rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, hdecomp w]
        exact Submodule.sub_mem _ (hGW _ ⟨w, rfl⟩) ⟨w, rfl⟩
      have hle := Submodule.finrank_mono hcomm_le
      obtain ⟨m, hm⟩ := heven
      rcases (show m = 0 ∨ m = 1 by omega) with hm0 | hm1
      ·
        have : commSpace G = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
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
      obtain ⟨φ, hφ, hd, hrφ⟩ : ∃ φ ∈ Rset, dot φ ![0, 0, 1] = 0 ∧ r φ ≠ 0 := by
        by_contra hall
        push Not at hall
        have hsum0 : ∑ φ ∈ Rset, r φ = 0 := Finset.sum_eq_zero fun φ hφ => by
          by_cases hd : dot φ ![0, 0, 1] = 0
          · exact hall φ hφ hd
          · exact hr0' φ hφ hd
        have hfull : fixOf ρ Set.univ = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [← range_e0, ← hr₀def, h8]
          omega
        apply he1
        refine LinearMap.ext fun w => ?_
        have : w ∈ fixOf ρ Set.univ := hfull ▸ Submodule.mem_top
        exact this _ (Set.mem_univ _)
      obtain ⟨a, ha⟩ := hr φ hφ
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h : LinearMap.range
          (isoP ρ φ) = ⊥ => hrφ (by
        show finrank K (LinearMap.range (isoP ρ φ)) = 0
        rw [h, finrank_bot]))
      obtain ⟨y, hy⟩ := exists_dot_ne φ hφ
      have hgood : GoodSix ρ (xOf φ) := by
        refine ⟨fun h => ?_, by rw [hdimx φ hφ hd]; omega, y, u,
          hsub_fix φ hφ (xOf φ) (dot_xOf φ) hu, fun h => hu0 (hmoves φ hφ y hy u hu h)⟩
        rcases xOf_ne φ hφ hd with h' | h'
        · exact h' (by rw [h]; rfl)
        · exact h' (by rw [h]; rfl)
      exact hfixV (xOf φ) (xOf_ne φ hφ hd) hgood v
        (fixOf_univ_le ρ {xOf φ} (by rw [← range_e0]; exact hv))
  intro v
  have h1 := hdecomp v
  rw [hW₀ _ ⟨v, rfl⟩, sub_self, sub_eq_zero] at h1
  exact h1

theorem orth2_eq_one_of_inner_rank_two (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h8 : finrank K V = 8)
    {D : Subgroup (MulAut (ProjOrthDerived Q))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hDinn : D ≤ innerAut (ProjOrthDerived Q))
    {H : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H D)
    (hgin : g ∈ innerAut (ProjOrthDerived Q)) : g = 1 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : CharP K 2 := charP_two_of_card hK
  have : Finite V := Module.finite_of_finite K
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have h2 : ∀ v : V, v + v = 0 := two_smul_eq_zero K
  obtain ⟨-, -, -, hsimple, hnonab, -, -, -, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_bot' hcenter
  have hmk := mk_injective_of_card_two (Q := Q) hK
  set ι : orthDerived Q →* MulAut (ProjOrthDerived Q) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).comp
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) with hιdef
  have hι : Function.Injective ι := hinj.comp hmk
  have hιapp : ∀ y : orthDerived Q, ι y = MulAut.conj (QuotientGroup.mk y : ProjOrthDerived Q) :=
    fun y => rfl
  have hDι : D ≤ ι.range := by
    intro d hd
    obtain ⟨t, ht⟩ := hDinn hd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨y, ht⟩
  set Dh : Subgroup (orthDerived Q) := D.comap ι with hDh
  have hmemDh : ∀ x, x ∈ Dh ↔ ι x ∈ D := fun x => Iff.rfl
  have hDhcard : Nat.card Dh = 9 := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hDι, hcard]
    norm_num
  have hDh3 : ∀ x ∈ Dh, x ^ 3 = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hD.2 _ ((hmemDh x).1 hx)
  have hDhcomm : ∀ x ∈ Dh, ∀ y ∈ Dh, x * y = y * x := fun x hx y hy => by
    apply hι
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, (hmemDh x).1 hx⟩ ⟨_, (hmemDh y).1 hy⟩)
  let _ : CommGroup Dh := { (inferInstance : Group Dh) with
    mul_comm := fun a b => Subtype.ext (hDhcomm a a.2 b b.2) }
  obtain ⟨e⟩ := exists_mulEquiv_z3_two (G := Dh) (fun g => Subtype.ext (hDh3 g g.2))
    (by rw [hDhcard])
  let πa : Z3 →+ (Fin 2 → ZMod 3) :=
    { toFun := fun z => ![z 0, z 1]
      map_zero' := by
        ext i
        fin_cases i <;> rfl
      map_add' := fun a b => by
        ext i
        fin_cases i <;> rfl }
  let π : Multiplicative Z3 →* Multiplicative (Fin 2 → ZMod 3) := πa.toMultiplicative
  set xh : Z3 → orthDerived Q :=
    fun z => ((e.symm (π (Multiplicative.ofAdd z)) : Dh) : orthDerived Q) with hxh
  have hxhD : ∀ z, xh z ∈ Dh := fun z => (e.symm (π (Multiplicative.ofAdd z))).2
  let ρ : Multiplicative Z3 →* Module.End K V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((orthDerived Q).subtype.comp (Dh.subtype.comp (e.symm.toMonoidHom.comp π)))
  have hact : ∀ z v, act ρ z v = (xh z : V ≃ₗ[K] V) v := fun z v => rfl
  have hxh1 : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → xh z ≠ 1 := by
    intro z hz h1
    have h3 : e.symm (π (Multiplicative.ofAdd z)) = 1 := Subtype.ext h1
    have h4 : π (Multiplicative.ofAdd z) = 1 := by simpa using h3
    have h5 : (![z 0, z 1] : Fin 2 → ZMod 3) = 0 := h4
    rcases hz with hz | hz
    · exact hz (congrFun h5 0)
    · exact hz (congrFun h5 1)
  have hz₃ : act ρ ![0, 0, 1] = 1 := by
    have h1 : π (Multiplicative.ofAdd ![0, 0, 1]) = 1 := by
      show Multiplicative.ofAdd (πa ![0, 0, 1]) = 1
      rw [ofAdd_eq_one]
      ext i
      fin_cases i <;> rfl
    show ρ (Multiplicative.ofAdd ![0, 0, 1]) = 1
    simp only [ρ, MonoidHom.comp_apply, h1, map_one]
  have hxhO : ∀ z, (xh z : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun z => orthDerived_le_orthogonalGroup Q (xh z).2
  have hisoB : ∀ z u v, QuadraticMap.polarBilin Q (act ρ z u) (act ρ z v) =
      QuadraticMap.polarBilin Q u v := fun z u v => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply, hact, hact]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hxhO z) u v
  have hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})) := fun φ hφ =>
    even_finrank_fixOf_N (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB hφ
  have hp0 : Even (finrank K (fixOf ρ Set.univ)) := by
    have hodd : Odd (Nat.card (⊤ : AddSubgroup Z3)) := by
      rw [AddSubgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
        Fintype.card_fin]
      decide
    have h := even_finrank_fixOf (CFSG.AGLEmbedding.polarBilin_isAlt_of_charTwo Q) hQ ρ hisoB ⊤
      hodd
    rwa [AddSubgroup.coe_top] at h
  obtain ⟨t, rfl⟩ := hgin
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective t
  set G : V ≃ₗ[K] V := (x₀ : V ≃ₗ[K] V) with hGdef
  have hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup Q x₀.2
  have hGΩ : G ∈ orthDerived Q := x₀.2
  have hGg : ∀ y : orthDerived Q, (MulAut.conj (QuotientGroup.mk x₀ : ProjOrthDerived Q))
      (QuotientGroup.mk y) = QuotientGroup.mk
        (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q) := by
    intro y
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl
  set g := MulAut.conj (QuotientGroup.mk x₀ : ProjOrthDerived Q) with hgdef
  have hGcomm : ∀ z, G * (xh z : V ≃ₗ[K] V) = (xh z : V ≃ₗ[K] V) * G := by
    intro z
    have hc := commute_of_mem_localDeltaIn hg ((hmemDh (xh z)).1 (hxhD z))
    have h1 : MulAut.conj (g (QuotientGroup.mk (xh z))) =
        MulAut.conj (QuotientGroup.mk (xh z) : ProjOrthDerived Q) := by
      rw [← mul_conj_mul_inv, ← hιapp, hc, mul_assoc, mul_inv_cancel, mul_one]
    have h2' := hinj h1
    rw [hGg] at h2'
    have h3 : G * (xh z : V ≃ₗ[K] V) * G⁻¹ = xh z := congrArg Subtype.val (hmk h2')
    calc G * (xh z : V ≃ₗ[K] V) = G * (xh z : V ≃ₗ[K] V) * G⁻¹ * G := by group
      _ = (xh z : V ≃ₗ[K] V) * G := by rw [h3]
  have hGact : ∀ z v, G (act ρ z v) = act ρ z (G v) := fun z v => by
    rw [hact, hact]
    exact congrArg (fun f : V ≃ₗ[K] V => f v) (hGcomm z)
  have hGe0 : ∀ v, G (e0 ρ v) = e0 ρ (G v) := fun v => by
    simp only [e0, LinearMap.sum_apply, map_sum, hGact]
  have hGeN : ∀ φ v, G (eN ρ φ v) = eN ρ φ (G v) := fun φ v => by
    simp only [eN, LinearMap.sum_apply, map_sum, hGact]
  have hGiso : ∀ φ v, G (isoP ρ φ v) = isoP ρ φ (G v) := fun φ v => by
    simp only [isoP, LinearMap.add_apply, map_add, hGe0, hGeN]
  have hgk : Nat.Coprime 3 (orderOf g) := by
    refine coprime_orderOf_of_mem_localDeltaIn hp hg ((hmemDh _).1 (hxhD ![1, 0, 0])) ?_
    intro h1
    exact hxh1 ![1, 0, 0] (Or.inl e1_ne_zero) (hι (h1.trans (map_one ι).symm))
  have hGk : G ^ orderOf g = 1 :=
    orth2_isometry_eq_one hK hQ (by omega) (pow_mem hGO _)
      (orth2_conj_eq_of_eq_one hK (pow_mem hGO _) (orth2_conj_pow hGO hGg _)
        (pow_orderOf_eq_one g))
  have hGpow : ∀ (n : ℕ) (w : V), ((G : V →ₗ[K] V) ^ n) w = (G ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih w, pow_succ', LinearEquiv.mul_apply]
      rfl
  have hGk' : ∀ w : V, ((G : V →ₗ[K] V) ^ orderOf g) w = w := fun w => by
    rw [hGpow, hGk]
    rfl
  have hfixV : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → GoodSix ρ z → ∀ v ∈ fixOf ρ {z}, G v = v := by
    intro z hz0 hz v hv
    obtain ⟨-, h6, y, u, hu, hyu⟩ := hz
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hfix : ∀ w, w ∈ fixedSpace (xh z : V ≃ₗ[K] V) ↔ w ∈ fixOf ρ {z} := by
      intro w
      rw [mem_fixedSpace, mem_fixOf]
      constructor
      · intro hw x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hact]
        exact hw
      · intro hw
        rw [← hact]
        exact hw z rfl
    have h6' : 6 ≤ finrank K (fixedSpace (xh z : V ≃ₗ[K] V)) := by
      have : fixedSpace (xh z : V ≃ₗ[K] V) = fixOf ρ {z} := Submodule.ext hfix
      rw [this]
      exact h6
    have hyM : (xh y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (xh z : V ≃ₗ[K] V) := by
      rw [mem_isometryCentralizer]
      refine ⟨fun w => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).1 (hxhO y) w,
        fun w => ?_⟩
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V) w)
        (hDhcomm _ (hxhD y) _ (hxhD z))
      simpa using this
    have hy3 : (xh y : V ≃ₗ[K] V) ^ 3 = 1 := by
      have := congrArg (fun t : orthDerived Q => (t : V ≃ₗ[K] V)) (hDh3 _ (hxhD y))
      simpa using this
    exact orth2_fixes_fixedSpace_of_mem_delta hK hQ hT hinj hH hg (xh z) hxo
      ((hmemDh _).1 (hxhD z)) h6' hyM hy3 ((hfix u).2 hu) (by rw [← hact]; exact hyu) hGO
      (hGcomm z) hGg v ((hfix v).2 hv)
  have hfixU : ∀ z : Z3, (z 0 ≠ 0 ∨ z 1 ≠ 0) → finrank K (fixOf ρ {z}) = 0 → ∀ v, G v = v := by
    intro z hz0 hz v
    have hx3 : xh z ^ 3 = 1 := hDh3 _ (hxhD z)
    have hxo : orderOf (xh z) = 3 := orderOf_eq_prime hx3 (hxh1 z hz0)
    have hE : eCyc ρ z = (xh z : V ≃ₗ[K] V).toLinearMap ^ 2 +
        (xh z : V ≃ₗ[K] V).toLinearMap + 1 := by
      ext w
      simp only [eCyc, LinearMap.add_apply, act_zero, Module.End.one_apply, act_add,
        Module.End.mul_apply, hact, pow_two, LinearEquiv.coe_coe]
      abel
    have hker : LinearMap.ker (eCyc ρ z) =
        primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K) := by
      rw [primaryComponent, aeval_cyc3, hE]
    have hrk := LinearMap.finrank_range_add_finrank_ker (eCyc ρ z)
    rw [range_eCyc ρ z, hz, zero_add, h8] at hrk
    have h8' : 8 ≤ finrank K (primaryComponent (xh z : V ≃ₗ[K] V).toLinearMap (cyc3 K)) := by
      rw [← hker, hrk]
    have hvker : v ∈ LinearMap.ker (eCyc ρ z) := by
      have htop : LinearMap.ker (eCyc ρ z) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [hrk, h8])
      rw [htop]
      exact Submodule.mem_top
    exact orth2_fixes_unitary hQ hT hK hinj hH hg (xh z) hxo ((hmemDh _).1 (hxhD z)) h8' hGO
      (hGcomm z) hmk hGg hgk hGk v (hker ▸ hvker)
  have he1 : act ρ ![1, 0, 0] ≠ 1 := fun h1 => hxh1 ![1, 0, 0] (Or.inl e1_ne_zero)
    (Subtype.ext (LinearEquiv.ext fun w => by rw [← hact, h1]; rfl))
  have hall := rank_two_cover hK ρ h8 hz₃ he1 hpN hp0 hGact hgk hGk'
    (even_finrank_commSpace_of_mem_orthDerived hQ hGΩ) hfixV hfixU
  have hG : G = 1 := LinearEquiv.ext hall
  ext t
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  rw [hGg y, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change G * (y : V ≃ₗ[K] V) * G⁻¹ = y
  rw [hG, one_mul, inv_one, mul_one]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
