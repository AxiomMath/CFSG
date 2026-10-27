module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8Omega
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusCover
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusHat
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.OmegaMinusEight

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

theorem exists_perfect_map_eq {H G : Type*} [Group H] [Finite H] [Group G] (β : H →* G)
    {S : Subgroup G} (hS : S ≤ β.range) (hperf : ⁅S, S⁆ = S) :
    ∃ W : Subgroup H, ⁅W, W⁆ = W ∧ W.map β = S := by
  have hne : ∃ W : Subgroup H, W.map β = S :=
    ⟨S.comap β, by rw [Subgroup.map_comap_eq, inf_eq_right.2 hS]⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min {W | W.map β = S} hne
  refine ⟨W, ?_, hW⟩
  by_contra hne'
  have h1 : (⁅W, W⁆).map β = S := by
    rw [Subgroup.map_commutator, hW, hperf]
  exact hmin ⁅W, W⁆ h1 (lt_of_le_of_ne (Subgroup.commutator_le_self W) hne')

theorem card_dvd_prod_of_levi {Q : Type*} [Group Q] {ι : Type} [Fintype ι] {G : ι → Type}
    [∀ j, Group (G j)] (β : Q →* ∀ j, G j) (hker : IsPGroup 2 β.ker)
    (Tj : ∀ j, Subgroup (G j)) (hmem : ∀ x j, β x j ∈ Tj j) {T : Subgroup Q} (hT : IsPGroup 3 T) :
    Nat.card T ∣ ∏ j, Nat.card (Tj j) := by
  let γ : ↥T →* ∀ j, ↥(Tj j) := MonoidHom.pi fun j =>
    ((Pi.evalMonoidHom G j).comp (β.comp T.subtype)).codRestrict (Tj j) fun x => hmem x j
  have hinj : Function.Injective γ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : β (x : Q) = 1 := by
      funext j
      exact congrArg Subtype.val (congrFun hx j)
    obtain ⟨k, hk⟩ := hker ⟨(x : Q), h1⟩
    obtain ⟨l, hl⟩ := hT x
    have h2 : orderOf (x : Q) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h3 : orderOf (x : Q) ∣ 3 ^ l :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hl)
    have hcop : Nat.Coprime (2 ^ k) (3 ^ l) := Nat.Coprime.pow _ _ (by norm_num)
    have h4 : orderOf (x : Q) ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h3
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))
  have h := Subgroup.card_dvd_of_injective γ hinj
  rwa [Nat.card_pi] at h

theorem three_dvd_ordTwistedD_two {m : ℕ} (h1 : 1 ≤ m) (h3 : m ≤ 3) :
    3 ∣ CFSG.Open.ordTwistedD (m + 1) (2 ^ 1) := by
  interval_cases m <;> decide

theorem exists_perfect_of_residual {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {K : Type}
    [Field K] [Finite K] [CharP K 2] {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ}
    (C : OmCover Y P 3 K b c d) (hd : OrthCuts 3 d) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hK : Nat.card K = 2) (hPY : P ≤ Y) (hm : d (Fin.last s) < 3) :
    ∃ J : Subgroup A, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J := by
  classical
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
    Finite.of_equiv _ C.ρ.symm.toEquiv
  have hm1 : 1 ≤ 3 - d (Fin.last s) := by omega
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  obtain ⟨-, hna, hcard⟩ := orthResDer_facts hK' hm1 hirr
  haveI : IsSimpleGroup ↥(orthResDer K b c (3 - d (Fin.last s))) :=
    (orthResDer_facts hK' hm1 hirr).1
  set S : Subgroup (orthLeviGroup K 3 d (.inr ())) := orthResDer K b c (3 - d (Fin.last s))
    with hS
  have hperfS : ⁅S, S⁆ = S := by
    have h1 : ⁅(⊤ : Subgroup ↥S), ⊤⁆ = ⊤ := (orthMinus_isQuasisimple_of_simple hna).1.1
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥S) ⊤ S.subtype
    rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm
  set β := orthLeviHom b c hd with hβ
  set S' : Subgroup (∀ j, orthLeviGroup K 3 d j) :=
    S.map (MonoidHom.mulSingle (orthLeviGroup K 3 d) (.inr ())) with hS'
  have hS'perf : ⁅S', S'⁆ = S' := by
    rw [hS', ← Subgroup.map_commutator, hperfS]
  have hS'le : S' ≤ β.range := by
    refine le_trans ?_ (pi_orthLeviBlock_le_range hd (by norm_num)
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr))
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_pi]
    intro j _
    rcases j with l | u
    · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
      exact one_mem _
    · obtain rfl : u = () := rfl
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
      exact hx
  obtain ⟨W, hWperf, hWmap⟩ := exists_perfect_map_eq β hS'le hS'perf
  refine ⟨(W.map C.toP).map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWperf]
  · rw [Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective C.toP_injective]
    have h1 : Nat.card ↥(W.map β) ∣ Nat.card W := Subgroup.card_map_dvd W β
    rw [hWmap, hS', Subgroup.card_map_of_injective
      (Pi.mulSingle_injective (M := orthLeviGroup K 3 d) (Sum.inr () : Fin s ⊕ Unit)), hcard] at h1
    exact (three_dvd_ordTwistedD_two hm1 (by omega)).trans h1

theorem card_GL_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (GL (Fin 3) K) = 168 := by
  haveI := Fintype.ofFinite K
  have h := Matrix.card_GL_field (n := 3) (𝔽 := K)
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [h]
  decide

theorem card_orthogonalGroup_zero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hK : Nat.card K = 2) {m : ℕ} (hm : m = 0) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) = 6 := by
  subst hm
  rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_card_orthogonalGroup_tail_zero
    hirr, hK]

theorem orthCuts_zero_three : OrthCuts 3 (![0, 3] : Fin 2 → ℕ) :=
  ⟨Fin.strictMono_iff_lt_succ.2 (by decide), rfl, by decide⟩

theorem orthParab_le_zero_three {K : Type} [Field K] {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hm : d (Fin.last s) = 3) :
    orthParab 3 (minusTailForm K b c) d ≤ orthParab 3 (minusTailForm K b c) ![0, 3] := by
  intro x hx
  rw [mem_orthParab] at hx ⊢
  intro i
  fin_cases i
  · simp [tailFlag_zero]
  · simpa [hm] using hx (Fin.last s)

theorem card_dvd_of_flag_three {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hK : Nat.card K = 2)
    {T : Subgroup ↥(orthParab 3 (minusTailForm K b c) ![0, 3])} (hT : IsPGroup 3 T) :
    Nat.card T ∣ 1008 := by
  classical
  let Tj : ∀ j : Fin 1 ⊕ Unit, Subgroup (orthLeviGroup K 3 ![0, 3] j) := fun j =>
    match j with
    | .inl _ => ⊤
    | .inr _ => TauCeti.QuadraticMap.orthogonalGroup
        (quadTail (3 - (![0, 3] : Fin 2 → ℕ) (Fin.last 1)) (minusTailForm K b c))
  have hmem : ∀ x j, orthLeviHom b c orthCuts_zero_three x j ∈ Tj j := by
    intro x j
    rcases j with l | u
    · exact Subgroup.mem_top _
    · obtain rfl : u = () := rfl
      exact orthResHom_mem_orthogonalGroup orthCuts_zero_three x
  have hdvd := card_dvd_prod_of_levi (orthLeviHom b c orthCuts_zero_three)
    (isPGroup_ker_orthLeviHom orthCuts_zero_three) Tj hmem hT
  have h1 : Nat.card ↥(Tj (.inl 0)) = 168 := by
    show Nat.card ↥(⊤ : Subgroup (GL (Fin 3) K)) = 168
    rw [Subgroup.card_top]
    exact card_GL_three hK
  have h2 : Nat.card ↥(Tj (.inr ())) = 6 :=
    card_orthogonalGroup_zero hirr hK (by decide)
  have hprod : ∏ j, Nat.card ↥(Tj j) = 1008 := by
    rw [Fintype.prod_sum_type]
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.default_eq_zero]
    rw [h1, h2]
    norm_num
  rwa [hprod] at hdvd

theorem card_le_nine_of_flag_three {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {K : Type}
    [Field K] [Finite K] [CharP K 2] {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ}
    (C : OmCover Y P 3 K b c d) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hK : Nat.card K = 2)
    (hPY : P ≤ Y) (hm : d (Fin.last s) = 3) {T : Subgroup A} (hTP : T ≤ P) (hT : IsPGroup 3 T) :
    Nat.card T ≤ 9 := by
  classical
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
    Finite.of_equiv _ C.ρ.symm.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let τ : ↥(orthParab 3 (minusTailForm K b c) d) ≃* ↥P :=
    MulEquiv.ofBijective C.toP ⟨C.toP_injective, C.toP_surjective hPY⟩
  let TQ : Subgroup ↥(orthParab 3 (minusTailForm K b c) d) :=
    (T.subgroupOf P).map τ.symm.toMonoidHom
  have hTQp : IsPGroup 3 ↥TQ := (hT.comap_of_injective P.subtype P.subtype_injective).map _
  have hTQcard : Nat.card TQ = Nat.card T := by
    rw [Subgroup.card_map_of_injective τ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  let TQ' : Subgroup ↥(orthParab 3 (minusTailForm K b c) ![0, 3]) :=
    TQ.map (Subgroup.inclusion (orthParab_le_zero_three hm))
  have hTQ'p : IsPGroup 3 ↥TQ' := hTQp.map _
  have hTQ'card : Nat.card TQ' = Nat.card TQ :=
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
  have hdvd := card_dvd_of_flag_three hirr hK hTQ'p
  rw [hTQ'card, hTQcard] at hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  rcases Nat.lt_or_ge n 3 with h | h
  · rw [hn]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  · exfalso
    have h27 : 27 ∣ Nat.card T := by
      rw [hn]
      exact (pow_dvd_pow 3 h : 3 ^ 3 ∣ 3 ^ n)
    have h' := h27.trans hdvd
    omega

theorem card_le_nine_of_parabolic {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (h : IsLieOver ↥Y (.twistedD 4) 2 1) (hP : IsParabolicTwo Y P)
    (hperf : ∀ J : Subgroup A, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J)
    {T : Subgroup A} (hTP : T ≤ P) (hT : IsPGroup 3 T) : Nat.card T ≤ 9 := by
  obtain ⟨K, _, _, _, b, c, hK, hirr, ⟨φ⟩⟩ := exists_model h
  obtain ⟨ρ, s, d, hd, hρ⟩ :=
    LeviBlock.exists_comap_eq_orthParab (by norm_num) hirr hP φ.symm
  let C : OmCover Y P 3 K b c d := ⟨ρ, hρ⟩
  by_cases hm : d (Fin.last s) = 3
  · exact card_le_nine_of_flag_three C hirr hK hP.1 hm hTP hT
  · exfalso
    obtain ⟨J, hJP, hJperf, hJ3⟩ := exists_perfect_of_residual C hd hirr hK hP.1
      (by have := hd.last; omega)
    exact hperf J hJP hJperf hJ3

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.OmegaMinusEight
