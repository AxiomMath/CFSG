module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotFrontier
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SlotProp65Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 5 P M x z T → SmallRankCover 5 M x →
        smallRankIsQ8D8 (smallRankR x z T) →
          ∀ F : Subgroup G, F ≤ M → F ≠ ⊥ → Nat.Coprime (Nat.card F) 10 →
            zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

variable {G : Type} [Group G] [Finite G]

theorem fitting628_five {P : Sylow 5 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    (hf : Prop627Failure G 5 P M x z T) (hS : Setting G)
    (h65 : ∀ F : Subgroup G, F ≤ M → F ≠ ⊥ → Nat.Coprime (Nat.card F) 10 →
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD 5 x)) ⊓ M = ⊥ := by
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD 5 x with hD
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  set F : Subgroup G := CFSG.fittingSubgroupOf O with hF
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(F ⊓ M) ≠ 1 from fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hgo : orderOf (g : G) = q := by rw [Subgroup.orderOf_coe]; exact hg
  have hgF : (g : G) ∈ F := g.2.1
  have hgM : (g : G) ∈ M := g.2.2
  have hDspec : D ≤ C ∧ C ≤ normalizer (D : Set G) ∧ Nat.Coprime 5 (Nat.card D) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 C
  have hOspec : O ≤ D ∧ D ≤ normalizer (O : Set G) ∧ Nat.Coprime 2 (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := sr628_centralizer_le_normalizer_oddCore 5 x
  have hOF : normalizer (O : Set G) ≤ normalizer (F : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.fittingSubgroup O)
  have : Group.IsNilpotent F := sr628_isNilpotent_fitting O
  obtain ⟨Q₀, hQ₀p, hQ₀F, hgQ₀, hFQ₀⟩ := sr628_exists_pGroup hgF hgo
  have hCQ₀ : C ≤ normalizer (Q₀ : Set G) := hCO.trans (hOF.trans hFQ₀)
  have hFO : F ≤ O := Subgroup.map_subtype_le _
  have hqO : q ∣ Nat.card O := hgo ▸ Subgroup.orderOf_dvd_natCard O (hFO hgF)
  have hq2 : q ≠ 2 := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd hOspec.2.2 (h ▸ hqO)) (by norm_num)
  have hqD : q ∣ Nat.card D := hqO.trans (Subgroup.card_dvd_of_le hOspec.1)
  have hq5 : q ≠ 5 := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDspec.2.2 (h ▸ hqD))
  have hQ₀D : Q₀ ≤ D := hQ₀F.trans (hFO.trans hOspec.1)
  have hnormQ₀ : (Q₀.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ₀D).mpr (hDspec.1.trans hCQ₀)
  have hQ₀Q : Q₀ ≤ pCoreOf q D := CFSG.LieType.BorelTits.le_pCoreOf q hQ₀D hnormQ₀ hQ₀p
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgo
    exact hq.one_lt.ne hgo
  have hQ₁ne : pCoreOf q D ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ pCoreOf q D ⊓ M := ⟨hQ₀Q hgQ₀, hgM⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg1 hmem
  have hQp : IsPGroup q (pCoreOf q D) := CFSG.LieType.BorelTits.pCoreOf_isPGroup q D
  have hCQ : C ≤ normalizer (pCoreOf q D : Set G) :=
    hDspec.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q D)
  have hxz : x * z = z * x := mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem
  have hBC : zpowers x ⊔ zpowers z ≤ C :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hBM : zpowers x ⊔ zpowers z ≤ M := hf.B_le_M hS
  have hBQ₁ : zpowers x ⊔ zpowers z ≤ normalizer ((pCoreOf q D ⊓ M : Subgroup G) : Set G) :=
    (le_inf (hBC.trans hCQ) (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hcop : Nat.Coprime (Nat.card ↥(pCoreOf q D ⊓ M)) 10 := by
    have hXp : IsPGroup q ↥(pCoreOf q D ⊓ M) := hQp.to_le inf_le_left
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    have h2 : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hq2
    have h5 : Nat.Coprime q 5 := (Nat.coprime_primes hq hp).mpr hq5
    exact (show (10 : ℕ) = 2 * 5 by norm_num) ▸ Nat.Coprime.mul_right h2 h5
  have hN₁ : normalizer ((pCoreOf q D ⊓ M : Subgroup G) : Set G) ≤ M :=
    h65 (pCoreOf q D ⊓ M) inf_le_right hQ₁ne hcop hBQ₁
  have hQM : pCoreOf q D ≤ M := by
    by_contra hQM
    have hlt : pCoreOf q D ⊓ M < pCoreOf q D :=
      lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyQ, hyN, hyY⟩ := sr628_exists_mem_normalizer_not_mem hQp hlt
    exact hyY ⟨hyQ, hN₁ hyN⟩
  rw [inf_eq_left.mpr hQM] at hN₁
  exact hf.point.not_centralizer_le (hCQ.trans hN₁)

theorem slotFitting628Five_of_prop65 (h : SlotProp65Five) : SlotFitting628Five :=
  fun G _ _ hS hD1 P M x z T hf hcov hR =>
    fitting628_five hf hS (h G hS hD1 P M x z T hf hcov hR)

theorem evasion_five {P : Sylow 5 G} {M : Subgroup G} {x z : G} {T : Subgroup G} {f : ℕ}
    (hS : Setting G) (h : Lemma630Hyp G 5 P M x z T f)
    (h65 : ∀ F : Subgroup G, F ≤ M → F ≠ ⊥ → Nat.Coprime (Nat.card F) 10 →
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M) :
    ∀ E, SmallRankSBSylow 5 f x z T E → E ⊓ M = ⊥ := by
  intro E hE
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := h
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact f.Prime := ⟨hfp⟩
  have hf5 : f ≠ 5 := sr629_ne_prime hp hfp x hfD
  obtain ⟨-, -, -, hFe, hF4, -⟩ := h29
  have hFM : smallRankF 5 f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← h28.2.2.2]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFne : smallRankF 5 f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF 5 f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFE : smallRankF 5 f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hE.1 hE.2.1 hE.2.2.1
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hBM : zpowers x ⊔ zpowers z ≤ M := hf.B_le_M hS
  have hBX : zpowers x ⊔ zpowers z ≤ normalizer ((E ⊓ M : Subgroup G) : Set G) :=
    (le_inf hBE (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  by_contra hne
  have hXp : IsPGroup f ↥(E ⊓ M) := hE.2.1.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ M)) 10 := by
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    have h2 : Nat.Coprime f 2 := (Nat.coprime_primes hfp Nat.prime_two).mpr hf2
    have h5 : Nat.Coprime f 5 := (Nat.coprime_primes hfp hp).mpr hf5
    exact (show (10 : ℕ) = 2 * 5 by norm_num) ▸ Nat.Coprime.mul_right h2 h5
  have hN : normalizer ((E ⊓ M : Subgroup G) : Set G) ≤ M :=
    h65 (E ⊓ M) inf_le_right hne hcop hBX
  have hEM : E ≤ M := by
    by_contra hEM
    have hlt : E ⊓ M < E :=
      lt_of_le_of_ne inf_le_left fun heq => hEM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyE, hyN, hyX⟩ := sr628_exists_mem_normalizer_not_mem hE.2.1 hlt
    exact hyX ⟨hyE, hN hyN⟩
  refine hFne (eq_bot_iff.mpr ?_)
  calc smallRankF 5 f x ≤ smallRankF 5 f x ⊓ M := le_inf le_rfl (hFE.trans hEM)
    _ = ⊥ := hFM
    _ ≤ ⊥ := le_rfl

theorem slotLemma630Five_evasion_of_prop65 (h : SlotProp65Five) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
      ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
        Lemma630Hyp G 5 P M x z T f → ∀ E : Subgroup G, SmallRankSBSylow 5 f x z T E → E ⊓ M = ⊥ :=
  fun G _ _ hS hD1 P M x z T f hyp =>
    evasion_five hS hyp (h G hS hD1 P M x z T hyp.failure hyp.cover (hyp.lemma628.2.2.1 rfl))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
