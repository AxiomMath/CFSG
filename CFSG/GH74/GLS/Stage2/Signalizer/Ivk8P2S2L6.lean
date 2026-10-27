module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Rk
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.LocalAnalysis.ComponentInitial (exists_isPComponent_of_isComponent)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (comp_le_or_le_of_commute comp_eq_of_le_quasisimple)
open CFSG.GH74.GLS.Stage2.Final.L26 (isSolvable_of_hasSL2Model_three')
open CFSG.DisconnectedInvolutionGraph.Helpers (NoCommutingDistinctInvolutions)

section G2

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem z_mem_map_of_toBar_mem {J : Subgroup ↥(Cen z)} (hz : orderOf z = 2)
    (h : zBar z ∈ J.map (toBar z)) : z ∈ J.map (Cen z).subtype := by
  obtain ⟨j, hj, hjz⟩ := h
  have hzE2 : (zElt z) ^ 2 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact this
  have hd : j⁻¹ * zElt z ∈ pPrimeCore 2 ↥(Cen z) := QuotientGroup.eq.1 hjz
  have hodd : Odd (orderOf (j⁻¹ * zElt z)) :=
    Nat.coprime_two_right.1 (coprime_orderOf_of_mem_pPrimeCore hd)
  have hjc : Commute j (zElt z) :=
    Subtype.ext (mem_centralizer_singleton_iff.1 j.2)
  set d : ↥(Cen z) := j⁻¹ * zElt z with hd_def
  have hcomm : Commute j d := (Commute.refl j).inv_right.mul_right hjc
  obtain ⟨m, hm⟩ := hodd
  have h1 : j * d = zElt z := mul_inv_cancel_left j (zElt z)
  have h2 : (zElt z) ^ orderOf d = j ^ orderOf d := by
    calc (zElt z) ^ orderOf d = (j * d) ^ orderOf d := by rw [h1]
      _ = j ^ orderOf d * d ^ orderOf d := hcomm.mul_pow _
      _ = j ^ orderOf d := by rw [pow_orderOf_eq_one, mul_one]
  have hz1 : zElt z = j ^ orderOf d := by
    rw [← h2, hm, pow_succ, pow_mul, hzE2, one_pow, one_mul]
  refine ⟨zElt z, ?_, rfl⟩
  rw [hz1]
  exact pow_mem hj _


theorem orderOf_toBar_of_orderOf_two {j : ↥(Cen z)} (hj : orderOf j = 2) :
    orderOf (toBar z j) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj2 : j ^ 2 = 1 := by
    have := pow_orderOf_eq_one j
    rwa [hj] at this
  have h2 : (toBar z j) ^ 2 = 1 := by
    rw [← map_pow, hj2, map_one]
  refine orderOf_eq_prime h2 ?_
  intro h1
  have hmem : j ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h1
  have hcop := coprime_orderOf_of_mem_pPrimeCore hmem
  rw [hj] at hcop
  exact absurd hcop (by decide)

theorem noCommuting_map_subtype {J : Subgroup ↥(Cen z)} {A : Subgroup (CentralizerBar z)}
    (hJA : J.map (toBar z) ≤ A)
    (hA : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → x = y) :
    NoCommutingDistinctInvolutions ↥(J.map (Cen z).subtype) := by
  intro a b hab
  obtain ⟨ja, hja, hjaa⟩ := a.1.2
  obtain ⟨jb, hjb, hjbb⟩ := b.1.2
  have hoa : orderOf ja = 2 := by
    have h1 : orderOf (ja : G) = 2 := by
      rw [show (ja : G) = (a.1 : G) from hjaa, Subgroup.orderOf_coe]
      exact a.2
    rwa [Subgroup.orderOf_coe] at h1
  have hob : orderOf jb = 2 := by
    have h1 : orderOf (jb : G) = 2 := by
      rw [show (jb : G) = (b.1 : G) from hjbb, Subgroup.orderOf_coe]
      exact b.2
    rwa [Subgroup.orderOf_coe] at h1
  have hcomm : Commute ja jb := by
    apply Subtype.ext
    have := congrArg Subtype.val hab
    have e1 : (ja : G) = (a.1 : G) := hjaa
    have e2 : (jb : G) = (b.1 : G) := hjbb
    simp only [Subgroup.coe_mul] at this
    show (ja : G) * jb = jb * ja
    rw [e1, e2]
    exact this
  have hbar : toBar z ja = toBar z jb :=
    hA _ (hJA ⟨ja, hja, rfl⟩) _ (hJA ⟨jb, hjb, rfl⟩) (orderOf_toBar_of_orderOf_two hoa)
      (orderOf_toBar_of_orderOf_two hob)
  have hja2 : ja ^ (2 ^ 1) = 1 := by rw [pow_one, ← hoa, pow_orderOf_eq_one]
  have hjb2 : jb ^ (2 ^ 1) = 1 := by rw [pow_one, ← hob, pow_orderOf_eq_one]
  have hjeq : ja = jb := eq_of_mk_eq_of_commute hcomm hja2 hjb2 hbar
  apply Subtype.ext
  apply Subtype.ext
  rw [← show (ja : G) = (a.1 : G) from hjaa, ← show (jb : G) = (b.1 : G) from hjbb, hjeq]

theorem pRank_eq_one_and_mem {J : Subgroup ↥(Cen z)} {A : Subgroup (CentralizerBar z)}
    (hz : orderOf z = 2) (hJA : J.map (toBar z) = A) (hzA : zBar z ∈ A)
    (hA : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → x = y) :
    pRank 2 ↥(J.map (Cen z).subtype) = 1 ∧ z ∈ J.map (Cen z).subtype := by
  have hzJ : z ∈ J.map (Cen z).subtype := z_mem_map_of_toBar_mem hz (hJA ▸ hzA)
  refine ⟨le_antisymm (pRank_le_one_of_noCommuting (noCommuting_map_subtype hJA.le hA)) ?_, hzJ⟩
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  exact CFSG.GH74.Uniqueness.SU.SU1.le_pRank one_lt_two (E := zpowers z) (zpowers_le.2 hzJ)
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hz2) (k := 1)
    (by rw [pow_one, Nat.card_zpowers, hz])


omit [Finite G] in
theorem not_le_of_commute_of_isComponent {Y : Type} [Group Y] {A B : Subgroup Y}
    (hB : IsComponent B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ¬ B ≤ A := by
  intro hBA
  have hcomm : ⁅B, B⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun b hb => ?_
    rw [mem_centralizer_iff]
    intro b' hb'
    exact hc b' (hBA hb') b hb
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
  have hbot : B = ⊥ := hperf.symm.trans hcomm
  have : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot

theorem layer_facts_of_single {A B : Subgroup (CentralizerBar z)} (hz : orderOf z = 2)
    (hB : IsComponent B) (hcomps : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = A ∨ K = B)
    (hBA : ¬ B ≤ A) (hzA : zBar z ∈ A)
    (hA : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → x = y)
    {J : Subgroup ↥(Cen z)} (hJ : IsComponent J) (hJA : J.map (toBar z) = A)
    (hnB : ¬ ∃ J' : Subgroup ↥(Cen z), IsComponent J' ∧ J'.map (toBar z) = B) :
    (pRank 2 ↥(Em (Cen z)) = 1 ∧ z ∈ Em (Cen z)) ∧ pLayerOf 2 (Cen z) ≠ Em (Cen z) := by
  have hu : ∀ J' : Subgroup ↥(Cen z), IsComponent J' → J' = J := by
    intro J' hJ'
    rcases hcomps _ (isComponent_map_pPrimeCore hJ') with h | h
    · exact eq_of_isComponent_of_map_eq hJ' hJ (h.trans hJA.symm)
    · exact absurd ⟨J', hJ', h⟩ hnB
  have hlayer : layer ↥(Cen z) = J := layer_eq_of_forall_eq hJ hu
  have hEm : Em (Cen z) = J.map (Cen z).subtype := by rw [Em_eq, hlayer]
  refine ⟨?_, ?_⟩
  · rw [hEm]
    exact pRank_eq_one_and_mem hz hJA hzA hA
  · intro hLE
    have hpl : pLayer ↥(Cen z) 2 = layer ↥(Cen z) := by
      rw [pLayerOf_eq_map, Em_eq] at hLE
      exact Subgroup.map_injective (Cen z).subtype_injective hLE
    obtain ⟨L, hLp, hLmap⟩ := exists_isPComponent_of_isComponent 2 hB
    have hLJ : L ≤ J := by
      rw [← hlayer, ← hpl]
      exact le_sSup hLp
    apply hBA
    rw [← hLmap, ← hJA]
    exact Subgroup.map_mono hLJ

end G2

section G2Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem lemma17_6_g2 (hW : Lemma17_6W) {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (ctx : Stage2Ctx G z Kind.g2 S) (hF : Fail17 G z Kind.g2 S (Cen z)) (hE : Em (Cen z) ≠ ⊥)
    (hsh : G2Shape z S r₁ r₂ L₁ L₂) :
    (pRank 2 ↥(Em (Cen z)) = 1 ∧ z ∈ Em (Cen z) ∧ Kind.g2 = Kind.g2) ∧
      (pLayerOf 2 (Cen z) = Em (Cen z) → G2Three z S ∧
        O22Of (O2Of (Cen z)) = pPrimeCoreOf 2 (O22Of (O2Of (Cen z))) ⊔
          (S ⊓ O22Of (O2Of (Cen z))) ∧
        Nonempty (↥(S ⊓ O22Of (O2Of (Cen z))) ≃* QuaternionGroup 2) ∧
        S ⊓ O22Of (O2Of (Cen z)) ⊓ centralizer (pPrimeCoreOf 2 (O22Of (O2Of (Cen z))) : Set G) =
          zpowers z) := by
  have hz : orderOf z = 2 := ctx.central.1
  have hsh' := hsh
  obtain ⟨hr₁, hr₂, hgt₁, hprod, m₁, m₂, -, h3, h4, -, -, -⟩ := hsh
  have hr₂ge : 2 ≤ r₂ := by
    obtain ⟨F, _, _, hF', -⟩ := m₂
    rw [← hF']
    exact Finite.one_lt_card
  have hq₁ : IsQuasisimple ↥L₁ := (sl2_model_facts hr₁ (by omega) m₁).1
  have hinv₁ := (sl2_model_facts hr₁ (by omega) m₁).2.2
  have hLn : (LBar z).Normal := LBar_normal z
  have hc21 : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hprod.2.1 b hb a ha).symm
  have hK₁ : IsComponent L₁ := ⟨hq₁, isSubnormal_of_commute hLn hprod.1 hprod.2.1⟩
  have hFL : generalizedFitting (CentralizerBar z) ≤ LBar z := by
    rcases Nat.lt_or_ge 3 r₂ with hgt | hle
    · exact ((h4 hgt).2).le
    · have hr₃ : r₂ = 3 := by
        obtain ⟨m, hm⟩ := hr₂
        omega
      rw [(h3 hr₃).2]
      exact Subgroup.map_subtype_le _
  have hcompsLe : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K ≤ L₁ ⊔ L₂ := fun K hK => by
    rw [hprod.1]
    exact ((le_sSup hK : K ≤ layer (CentralizerBar z)).trans le_sup_right).trans hFL
  have hzL : zBar z ∈ L₁ ⊔ L₂ := by
    rw [hprod.1]
    exact hFL (zBar_mem_generalizedFitting z)
  have hzI : zBar z ∈ L₁ ⊓ L₂ :=
    central_le_inf hr₁ hr₂ m₁ m₂ hprod.2.1 hprod.2.2 hzL (fun y _ => zBar_central z y)
  have hz₁ : zBar z ∈ L₁ := hzI.1
  have hz₂ : zBar z ∈ L₂ := hzI.2
  obtain ⟨J, hJ⟩ := exists_component_of_Em_ne_bot hE
  rcases Nat.lt_or_ge 3 r₂ with hgt | hle
  · have hq₂ : IsQuasisimple ↥L₂ := (sl2_model_facts hr₂ (by omega) m₂).1
    have hinv₂ := (sl2_model_facts hr₂ (by omega) m₂).2.2
    have hK₂ : IsComponent L₂ :=
      ⟨hq₂, isSubnormal_of_commute hLn (by rw [sup_comm]; exact hprod.1) hc21⟩
    have hcomps : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ ∨ K = L₂ := by
      intro K hK
      rcases comp_le_or_le_of_commute hprod.2.1 hK (hcompsLe K hK) with h | h
      · exact Or.inl (comp_eq_of_le_quasisimple hq₁ hK h)
      · exact Or.inr (comp_eq_of_le_quasisimple hq₂ hK h)
    by_cases P₁ : ∃ J' : Subgroup ↥(Cen z), IsComponent J' ∧ J'.map (toBar z) = L₁
    · by_cases P₂ : ∃ J' : Subgroup ↥(Cen z), IsComponent J' ∧ J'.map (toBar z) = L₂
      · exfalso
        have hI : ∀ K : Subgroup (CentralizerBar z), IsComponent K →
            ∃ J' : Subgroup ↥(Cen z), IsComponent J' ∧ J'.map (toBar z) = K := by
          intro K hK
          rcases hcomps K hK with rfl | rfl
          · exact P₁
          · exact P₂
        exact hF.fail (thm4Concl_of_images hz ctx.sylow hI (h4 hgt).1.le)
      · obtain ⟨J₁, hJ₁, hJ₁A⟩ := P₁
        have key := layer_facts_of_single hz hK₂ hcomps
          (not_le_of_commute_of_isComponent hK₂ hprod.2.1) hz₁ hinv₁ hJ₁ hJ₁A P₂
        exact ⟨⟨key.1.1, key.1.2, rfl⟩, fun hLE => absurd hLE key.2⟩
    · by_cases P₂ : ∃ J' : Subgroup ↥(Cen z), IsComponent J' ∧ J'.map (toBar z) = L₂
      · obtain ⟨J₂, hJ₂, hJ₂A⟩ := P₂
        have key := layer_facts_of_single hz hK₁ (fun K hK => (hcomps K hK).symm)
          (not_le_of_commute_of_isComponent hK₁ hc21) hz₂ hinv₂ hJ₂ hJ₂A P₁
        exact ⟨⟨key.1.1, key.1.2, rfl⟩, fun hLE => absurd hLE key.2⟩
      · exfalso
        rcases hcomps _ (isComponent_map_pPrimeCore hJ) with h | h
        · exact P₁ ⟨J, hJ, h⟩
        · exact P₂ ⟨J, hJ, h⟩
  · have hr₂3 : r₂ = 3 := by
      obtain ⟨m, hm⟩ := hr₂
      omega
    subst hr₂3
    have hsolv₂ : Group.IsSolvable ↥L₂ := isSolvable_of_hasSL2Model_three' m₂
    have hcomps : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ := by
      intro K hK
      rcases comp_le_or_le_of_commute hprod.2.1 hK (hcompsLe K hK) with h | h
      · exact comp_eq_of_le_quasisimple hq₁ hK h
      · exfalso
        have : Group.IsSolvable ↥K :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
        have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
        have : Group.IsPerfect ↥K := hK.1.1
        exact Group.IsPerfect.not_isSolvable ↥K inferInstance
    have hJA : J.map (toBar z) = L₁ := hcomps _ (isComponent_map_pPrimeCore hJ)
    have hu : ∀ J' : Subgroup ↥(Cen z), IsComponent J' → J' = J := fun J' hJ' =>
      eq_of_isComponent_of_map_eq hJ' hJ
        ((hcomps _ (isComponent_map_pPrimeCore hJ')).trans hJA.symm)
    have hlayer : layer ↥(Cen z) = J := layer_eq_of_forall_eq hJ hu
    have hEm : Em (Cen z) = J.map (Cen z).subtype := by rw [Em_eq, hlayer]
    obtain ⟨hrk, hzmem⟩ := pRank_eq_one_and_mem hz hJA hz₁ hinv₁
    refine ⟨⟨by rw [hEm]; exact hrk, by rw [hEm]; exact hzmem, rfl⟩, fun hLE => ?_⟩
    have hG3 : G2Three z S := ⟨r₁, L₁, L₂, hsh'⟩
    obtain ⟨w1, w2, w3⟩ := hW G z Kind.g2 S (Cen z) hF rfl hE hLE hG3
    exact ⟨hG3, w1, w2, w3⟩

end G2Main

theorem lemma17_6_of (h171 : Prop17_1) (hW : Lemma17_6W) : Lemma17_6 := by
  intro G _ _ z k S M h hE
  obtain ⟨hMC, -⟩ := h171 G z k S M h.ctx h.fail
  subst hMC
  have ctx : Stage2Ctx G z k S := h.ctx.ctx
  cases ctx.data with
  | g2 hg =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
    exact lemma17_6_g2 hW ctx h hE hsh
  | m12 hm => exact (false_of_m12 hm hE).elim
  | psp4 hp =>
    obtain ⟨q, L₁, L₂, hP⟩ := hp
    exact (false_of_pair ctx h hE hP.pair).elim
  | l4 ε hl =>
    obtain ⟨q, L₁, L₂, hP⟩ := hl
    exact (false_of_pair ctx h hE hP.pair).elim
  | mcl hm =>
    obtain ⟨n, -, hS⟩ := hm
    exact (false_of_cover ctx h hE hS.cover).elim
  | ly hm =>
    obtain ⟨n, -, hS⟩ := hm
    exact (false_of_cover ctx h hE hS.cover).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
