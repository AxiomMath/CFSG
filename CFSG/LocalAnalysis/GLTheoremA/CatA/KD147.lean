module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Multiplier
open scoped MatrixGroups


private theorem kd147_table {p f : ℕ} (hq3 : ¬ (p = 3 ∧ f = 1)) :
    ∃ c d : ℕ, exceptionalOrders .G2 0 p f = (c, d) ∧ 0 < c * d ∧ c * d ∣ 2 := by
  by_cases h22 : p = 2 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h22
    exact ⟨2, 1, rfl, by norm_num, by norm_num⟩
  by_cases h31 : p = 3 ∧ f = 1
  · exact (hq3 h31).elim
  refine ⟨1, 1, ?_, by norm_num, by norm_num⟩
  unfold exceptionalOrders
  split <;> first | rfl | simp_all | omega

theorem kd147_clause_a {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq3 : ¬ 3 ∣ q.card)
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    ∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
      IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
        Subgroup.center E = ⊥ := by
  intro E _ _ hQ hZ ⟨eQ⟩
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hm : CFSG.Models.LieModel (E ⧸ Subgroup.center E) .G2 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, hq ▸ hr⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ (eQ.trans eS)
  have hg : genericOrders .G2 0 q.p q.exponent = (1, 1) := rfl
  have hq3' : ¬ (q.p = 3 ∧ q.exponent = 1) := by
    rintro ⟨h1, h2⟩
    apply hq3
    rw [hq, h1, h2]
    norm_num
  obtain ⟨c, d, he, hpos, hdiv⟩ := kd147_table hq3'
  have hdvd := card_center_dvd_of_table hGA hQ hm hg he
    (by simpa using hpos.ne')
  have h2 : Nat.card (Subgroup.center E) ∣ 2 := hdvd.trans (by simpa using hdiv)
  by_contra hne
  haveI : Nontrivial (Subgroup.center E) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact false_of_pGroup_dvd Nat.prime_three hZ h2 (by norm_num)

private def kd147M (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem kd147M_pow_three (K : Type) [Field K] : kd147M K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kd147M, Matrix.mul_apply, Fin.sum_univ_two]

private theorem kd147M_ne_one (K : Type) [Field K] : kd147M K ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp [kd147M] at this

private theorem kd147M_not_comm (K : Type) [Field K] :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, A * kd147M K ≠ kd147M K * A := by
  refine ⟨⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩, fun h => ?_⟩
  have h00 := congrArg
    (fun B : Matrix.SpecialLinearGroup (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) * (kd147M K : Matrix (Fin 2) (Fin 2) K)) 0 0 =
    (((kd147M K : Matrix (Fin 2) (Fin 2) K)) * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) 0 0 at h00
  simp [kd147M, Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem kd147_e9_of_commuting {K G : Type} [Field K] [Group G] [Finite G]
    (ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂)
    (hc : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) K, ι₁ A * ι₂ B = ι₂ B * ι₁ A) :
    ∃ P : Subgroup G, IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : ι₁ (kd147M K) ^ 3 = 1 := by rw [← map_pow, kd147M_pow_three, map_one]
  have hy3 : ι₂ (kd147M K) ^ 3 = 1 := by rw [← map_pow, kd147M_pow_three, map_one]
  have hx1 : ι₁ (kd147M K) ≠ 1 := fun h => kd147M_ne_one K (h₁ (by rw [h, map_one]))
  have hxy : Commute (ι₁ (kd147M K)) (ι₂ (kd147M K)) := hc _ _
  have hox : orderOf (ι₁ (kd147M K)) = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf (ι₂ (kd147M K)) = 3 := by
    rw [orderOf_injective ι₂ h₂, orderOf_eq_prime (kd147M_pow_three K) (kd147M_ne_one K)]
  have hxR : ι₁ (kd147M K) ∉ ι₂.range := by
    intro hmem
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.1 hmem
    obtain ⟨A, hA⟩ := kd147M_not_comm K
    apply hA
    apply h₁
    rw [map_mul, map_mul]
    have := hc A B
    rw [hB] at this
    exact this
  have hpow : ∀ k : ℤ, ι₁ (kd147M K) ^ k ∈ ι₂.range → ι₁ (kd147M K) ^ k = 1 := by
    intro k hk
    have e1 : ι₁ (kd147M K) ^ (k % ((3 : ℕ) : ℤ)) = ι₁ (kd147M K) ^ k := by
      rw [← hox]
      exact zpow_mod_orderOf _ _
    rw [← e1] at hk ⊢
    have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      omega
    rcases hk3 with h | h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hk
      exact absurd hk hxR
    · rw [h] at hk
      have h2 : ι₁ (kd147M K) ^ (2 : ℕ) ∈ ι₂.range := by simpa using hk
      have h4 : ι₁ (kd147M K) ^ (4 : ℕ) = ι₁ (kd147M K) := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hx3, one_mul, pow_one]
      exact absurd (by
        rw [← h4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
        exact Subgroup.pow_mem _ h2 2) hxR
  have hint : Subgroup.zpowers (ι₁ (kd147M K)) ⊓ Subgroup.zpowers (ι₂ (kd147M K)) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgx, hgy⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgy
    have hgR : g ∈ ι₂.range := by
      rw [← hk]
      exact Subgroup.zpow_mem _ (MonoidHom.mem_range.2 ⟨kd147M K, rfl⟩) k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgx
    rw [Subgroup.mem_bot, ← hj]
    rw [← hj] at hgR
    exact hpow j hgR
  have hcx : Nat.card (Subgroup.zpowers (ι₁ (kd147M K))) = 3 := by
    rw [Nat.card_zpowers, hox]
  have hcy : Nat.card (Subgroup.zpowers (ι₂ (kd147M K))) = 3 := by
    rw [Nat.card_zpowers, hoy]
  have hnorm : Subgroup.zpowers (ι₂ (kd147M K)) ≤
      Subgroup.normalizer ((Subgroup.zpowers (ι₁ (kd147M K)) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hxy.zpow_zpow j k).eq
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hint, hcx, hcy, Subgroup.card_bot] at hcard
  have hPeq : Subgroup.closure ({ι₁ (kd147M K), ι₂ (kd147M K)} : Set G) =
      Subgroup.zpowers (ι₁ (kd147M K)) ⊔ Subgroup.zpowers (ι₂ (kd147M K)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.insert_eq]
  have hcomm : Set.Pairwise ({ι₁ (kd147M K), ι₂ (kd147M K)} : Set G) Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  haveI : IsMulCommutative (Subgroup.closure ({ι₁ (kd147M K), ι₂ (kd147M K)} : Set G)) :=
    Subgroup.isMulCommutative_closure hcomm
  have hexp : ∀ g ∈ Subgroup.closure ({ι₁ (kd147M K), ι₂ (kd147M K)} : Set G), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hx3
      · exact hy3
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      have hab : Commute a b :=
        congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : Subgroup.closure _) ⟨b, hb⟩)
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  refine ⟨Subgroup.closure ({ι₁ (kd147M K), ι₂ (kd147M K)} : Set G), ⟨inferInstance, hexp⟩, ?_⟩
  rw [hPeq]
  simpa using hcard

private def kd147α : Fin 2 → Fin CFSG.Blueprint.Chevalley.Tag.G2.rank → ℤ := ![![1, 0], ![1, 2]]

private theorem kd147_g2_of_catalog {T : Type} [Group T] (h : catalogIs T (onLie isG2Big)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
      2 < q.card ∧ ¬ 3 ∣ q.card ∧
        Nonempty (T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | G2 q =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨q, hv, h1, h2, ⟨e⟩⟩
  | _ => exact hP.elim

theorem kd147_clause_b {S : Type} [Group S] [Finite S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    (GaloisField q.p q.exponent) hK
  have hZ : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.G2 (GaloisField q.p q.exponent)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := CFSG.Blueprint.Chevalley.Tag.G2)
      (K := GaloisField q.p q.exponent)
  let e := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (eQ.trans eS.symm)
  obtain ⟨ι, hι, hc⟩ := CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2
    (K := GaloisField q.p q.exponent) CFSG.Blueprint.Chevalley.Tag.G2 kd147α (by decide)
  obtain ⟨P, hP, hcard⟩ := kd147_e9_of_commuting (K := GaloisField q.p q.exponent) (G := S)
    (e.toMonoidHom.comp (ι 0)) (e.toMonoidHom.comp (ι 1))
    (e.injective.comp (hι 0)) (e.injective.comp (hι 1))
    (fun A B => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul,
        hc 0 1 (by decide) A B])
  exact ⟨P, hP, hcard⟩

theorem kd147_of_clause_c
    (hc : ∀ (S : Type) [Group S] [Finite S], catalogIs S (onLie isG2Big) → ∀ z : S,
      orderOf z = 3 → GLAPLayer 3 (Subgroup.centralizer ({z} : Set S)) ≠ ⊥) : KD147 := by
  intro S _ _ hS
  obtain ⟨q, hv, -, hq3, ⟨eS⟩⟩ := kd147_g2_of_catalog hS
  exact ⟨kd147_clause_a hv hq3 eS, kd147_clause_b hv eS, hc S hS⟩

end CFSG.LocalAnalysis.GLTheoremA
