module

public import CFSG.ClassicalInvolution.Q3.Q3MTTD4Struct
public import CFSG.ClassicalInvolution.Q3.Q3MTU5
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTD4
public import CFSG.ClassicalInvolution.Uniform.U3Thm7
public import CFSG.ClassicalInvolution.Q3.Q3MTG2Chart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups


section Core

theorem edge_node_three (i : Fin (Tag.rank .G2))
    (g₀ g : twistedGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1))
    {R : Subgroup (twistedGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1))}
    (hRJ : R ≤ conjSub g (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) i)))
    (hR2 : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup (twistedGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)),
      T ≤ conjSub g (conjSub g₀ (rankOne (twistedRootGroup
        (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) i)) → IsPGroup 2 T → R ≤ T → T = R)
    (hRN : R ≤ Subgroup.normalizer ((conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) i) : Subgroup _) : Set _)) :
    conjSub g (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) i)) =
      conjSub g₀ (rankOne (twistedRootGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) i) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he : 1 ≤ 1 := le_rfl
  have hfin := finite_galoisField_three (p := 3) 1 he
  have hσ := sigma_three_td4 (p := 3) 1 he
  have hK1 := neg_one_ne_one_galoisField_td4 (p := 3) hp2 (3 * 1)
  have hrange := range_twistedIncl_eq (p := 3) hp2 1 he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField 3 (3 * 1))
      (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) ≤
      (twistedIncl (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1),
      twistedIncl (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField 3 (3 * 1))
          (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) := fun g => hrange ▸ ⟨g, rfl⟩
  have h2K := two_ne_zero_galoisField_td4 (p := 3) hp2 (3 * 1)
  have hK27 : Nat.card (GaloisField 3 (3 * 1)) = 27 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  have hσ3 : ∀ c, iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 c = c ^ 3 := fun c => by
    rw [iterateFrobenius_def]
    simp
  match i with
  | ⟨0, _⟩ =>
    have h2F : (2 : fixedField (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)) ≠ 0 :=
      fun h => h2K (congrArg Subtype.val h)
    have hrk := ModelFacts.rankOne_long_eq_range hσ
    rw [hrk] at hRJ hmax hRN ⊢
    exact eq_of_sylow_le_normalizer_of_chart3 (odd_natCard_of_two_ne_zero_td4 h2F)
      (slLong_injective hσ)
      (fun x hx => linAct_of_centralizes_long hσ hK1 h2F hC₀ hgF hx)
      (fun Ψ hΨ hc => chart_neg_one_eq_td4 hσ hσ3 hK27 hC₀ hgF hΨ hc) g₀ g hRJ hR2 hmax hRN
  | ⟨1, _⟩ =>
    have h4 : 4 ≤ Nat.card (GaloisField 3 (3 * 1)) := by rw [hK27]; norm_num
    have hrk := ModelFacts.rankOne_short_eq_range hσ
    rw [hrk] at hRJ hmax hRN ⊢
    exact edge_of_chart hp2 he (odd_natCard_of_two_ne_zero_td4 h2K) h4 (slShort_injective hσ) hrk
      (fun x hx => linAct_of_centralizes_short hσ hK1 h2K hC₀ hgF hx) g₀ g hRJ hR2 hmax hRN

end Core

section Shape

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem td4_exp_eq_one (M : Ih8Model 3 1 Ω .trialityD4 0 e) : e = 1 := by
  rcases M.exp_eq with h | ⟨-, h⟩
  · exact h
  · omega

theorem eq_of_isMaxPGroup_le_normalizer_td4_three (hadm : StatedLieAdmissible .trialityD4 0 3 1) :
    ∀ Q ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 3 1 Fact.out).D,
      ∀ g : (modelUniv .trialityD4 0 3 1 Fact.out).K,
        ∀ R : Subgroup (modelUniv .trialityD4 0 3 1 Fact.out).K,
          R ≤ conjSub g Q → IsPGroup 2 R →
          (∀ T : Subgroup (modelUniv .trialityD4 0 3 1 Fact.out).K,
            T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
          R ≤ Subgroup.normalizer (Q : Set (modelUniv .trialityD4 0 3 1 Fact.out).K) →
          conjSub g Q = Q := by
  intro Q hQ g R hRJ hR2 hmax hRN
  obtain ⟨i, g₀, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 0 3 1 hadm hQ
  exact edge_node_three i g₀ g hRJ hR2 hmax hRN

theorem dEdgeless_td4_three (M : Ih8Model 3 1 Ω .trialityD4 0 e)
    (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) : Disconnected.DEdgeless Ω := by
  have he1 := td4_exp_eq_one M
  subst he1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center (by norm_num : (3 : ℕ) ≠ 2) (Or.inr rfl) 0 le_rfl M.ψ
      M.ker_le_center
  exact dEdgeless_of_model M.ψ hinj M.surj M.mem_iff htrans fun Q hQ =>
    eq_of_isMaxPGroup_le_normalizer_td4_three M.admissible Q (M.cls_sub hQ)

theorem td4_omegaStarNbr_nonempty_three (M : Ih8Model 3 1 Ω .trialityD4 0 e)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L)
    (hne : Ω.Nonempty) : ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty := by
  have he1 := td4_exp_eq_one M
  subst he1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 le_rfl M.ψ M.ker_le_center
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :=
    MuTab.td4_exists_orderFour hp2 M.admissible (M.cls_sub hR)
  obtain ⟨h, hh⟩ : ∃ h : (modelUniv .trialityD4 0 3 1 Fact.out).K, h * d * h⁻¹ = c :=
    Balance.Bootstrap.trialityD4_involutions_conj hp2 le_rfl hd hc.sq hd1 hc.ne_one
  have hL : conjSub h R ∈ M.cls := M.cls_conj R hR h
  have hJΩ : R.map M.ψ ∈ Ω := M.map_mem hR
  have hLΩ : (conjSub h R).map M.ψ ∈ Ω := M.map_mem hL
  have ha : IsUniqueInvolution (R.map M.ψ) (M.ψ c) := muTab_isUniqueInvolution_map hinj hc
  have hg : M.ψ (h * j * h⁻¹) ∈ (conjSub h R).map M.ψ :=
    Subgroup.mem_map_of_mem _ (conj_mem_conjSub hj)
  have hg4 : orderOf (M.ψ (h * j * h⁻¹)) = 4 := by
    rw [orderOf_injective M.ψ hinj]
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective j
    rw [hj4] at this
    exact this
  have hga : M.ψ c * M.ψ (h * j * h⁻¹) * (M.ψ c)⁻¹ = M.ψ (h * j * h⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [← hh]
    have hdj : d * j * d⁻¹ = j := by rw [← hjd]; group
    calc h * d * h⁻¹ * (h * j * h⁻¹) * (h * d * h⁻¹)⁻¹ = h * (d * j * d⁻¹) * h⁻¹ := by group
      _ = h * j * h⁻¹ := by rw [hdj]
  have hN : M.ψ (h * j * h⁻¹) ∈ Subgroup.normalizer ((R.map M.ψ : Subgroup G) : Set G) := by
    have hK' : conjSub (M.ψ (h * j * h⁻¹)) (R.map M.ψ) ∈ Ω := hΩ.conjInvariant _ _ hJΩ
    have hz' : IsUniqueInvolution (conjSub (M.ψ (h * j * h⁻¹)) (R.map M.ψ)) (M.ψ c) := by
      have := ha.conj (M.ψ (h * j * h⁻¹))
      have e : M.ψ (h * j * h⁻¹) * M.ψ c * (M.ψ (h * j * h⁻¹))⁻¹ = M.ψ c := by
        have hcomm : M.ψ c * M.ψ (h * j * h⁻¹) = M.ψ (h * j * h⁻¹) * M.ψ c := by
          calc M.ψ c * M.ψ (h * j * h⁻¹) = M.ψ c * M.ψ (h * j * h⁻¹) * (M.ψ c)⁻¹ * M.ψ c := by
                group
            _ = M.ψ (h * j * h⁻¹) * M.ψ c := by rw [hga]
        calc M.ψ (h * j * h⁻¹) * M.ψ c * (M.ψ (h * j * h⁻¹))⁻¹
            = M.ψ c * M.ψ (h * j * h⁻¹) * (M.ψ (h * j * h⁻¹))⁻¹ := by rw [hcomm]
          _ = M.ψ c := by group
      rwa [e] at this
    have htw : conjSub (M.ψ (h * j * h⁻¹)) (R.map M.ψ) ∈ twinSet Ω (R.map M.ψ) :=
      ⟨hK', M.ψ c, ha, hz'⟩
    exact normalizer_iff_conjSub_eq.mpr (noTwins_of_g2d4_datum M htrans (Or.inr rfl) _ hJΩ _ htw)
  have hne' : (conjSub h R).map M.ψ ≠ R.map M.ψ := by
    intro heq
    have hRh : conjSub h R = R := Subgroup.map_injective hinj heq
    have hcc : h * c * h⁻¹ = c := hc.conj_eq hRh
    apply hdc
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = h⁻¹ * c * h := by rw [hh]
      _ = h⁻¹ * (h * c * h⁻¹) * h := by rw [hcc]
      _ = c := by group
  exact ⟨R.map M.ψ, hJΩ, _, hLΩ, hne', Subgroup.zpowers (M.ψ (h * j * h⁻¹)),
    mem_USet3 hΩ hLΩ hg hg4, Subgroup.zpowers_le.mpr hg, Subgroup.zpowers_le.mpr hN⟩

theorem trialityD4Shape3 : SmallShape3 .trialityD4 0 := by
  intro G _ _ _ Ω hΩ hA hne htrans hL
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  rw [show MuTab.muKind false .trialityD4 0 = .s3 by simp [MuTab.muKind]]
  exact ⟨dEdgeless_td4_three M htrans, td4_omegaStarNbr_nonempty_three M hΩ htrans hne⟩

end Shape

end CFSG.ClassicalInvolution.Q3.Q3MT
