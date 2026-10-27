module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.LemmaR
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Factors

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem fc_sylow_inf (h : K2Setup G Y Q) {N K : Subgroup G} (hN : N.Normal) (hKN : K ≤ N)
    (hKn : (K.subgroupOf N).Normal) : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ K) K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, h.pgroup, by rw [Subgroup.relIndex_top_right]; exact h.index⟩
  have hQN : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ N) N :=
    hQ.inf_of_le_normalizer le_top (by
      haveI := hN
      exact Subgroup.le_normalizer_of_normal)
  have hNK : N ≤ normalizer (K : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hKN
  have := hQN.inf_of_le_normalizer hKN hNK
  rwa [inf_assoc, inf_eq_right.mpr hKN] at this

theorem fc_dvd_card {T K : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T K)
    (hK : 3 ∣ Nat.card K) : 3 ∣ Nat.card T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hT.card_eq]
  exact dvd_pow_self 3
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hK).ne'

theorem fc_exists_order_three {T K : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T K)
    (hK : 3 ∣ Nat.card K) : ∃ a : G, a ∈ T ∧ orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (fc_dvd_card hT hK)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem fc_le_normalizer_inf {K : Subgroup G} (hQ : Q ≤ normalizer (K : Set G)) :
    Q ≤ normalizer ((Q ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer (H := Q)) hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp (hQ hg) x
  simp only [Subgroup.mem_inf]
  exact and_congr h1 h2

theorem fc_card_closure_pair {a₁ a₂ : G} (h₁ : orderOf a₁ = 3) (h₂ : orderOf a₂ = 3)
    (hc : a₁ * a₂ = a₂ * a₁) (hn : a₂ ∉ Subgroup.zpowers a₁) :
    IsElemAbelian 3 (Subgroup.closure ({a₁, a₂} : Set G)) ∧
      Nat.card (Subgroup.closure ({a₁, a₂} : Set G)) = 3 ^ 2 := by
  have hcomm : ∀ a ∈ ({a₁, a₂} : Set G), ∀ b ∈ ({a₁, a₂} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · rw [ha, hb]
      · rw [ha, Set.mem_singleton_iff.mp hb]
        exact hc
    · rw [Set.mem_singleton_iff.mp ha]
      rcases hb with hb | hb
      · rw [hb]
        exact hc.symm
      · rw [Set.mem_singleton_iff.mp hb]
  have hpow : ∀ a ∈ ({a₁, a₂} : Set G), a ^ 3 = 1 := by
    intro a ha
    rcases ha with ha | ha
    · rw [ha]
      have := pow_orderOf_eq_one a₁
      rwa [h₁] at this
    · rw [Set.mem_singleton_iff.mp ha]
      have := pow_orderOf_eq_one a₂
      rwa [h₂] at this
  have hE : IsElemAbelian 3 (Subgroup.closure ({a₁, a₂} : Set G)) :=
    IsElemAbelian.closure_of_commute hcomm hpow
  refine ⟨hE, ?_⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hmem₁ : a₁ ∈ Subgroup.closure ({a₁, a₂} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmem₂ : a₂ ∈ Subgroup.closure ({a₁, a₂} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hf1 : a₁ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h₁
    omega
  have hx1 : a₂ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h₂
    omega
  have hcl : Subgroup.closure ({a₁, a₂} : Set G) = Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hnorm : Subgroup.zpowers a₂ ≤ Subgroup.normalizer (Subgroup.zpowers a₁ : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have hxf : Commute a₂ a₁ := hc.symm
    exact (hxf.zpow_right n).eq.symm
  have hdisj : Disjoint (Subgroup.zpowers a₁) (Subgroup.zpowers a₂) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (Subgroup.zpowers a₁ ⊓ Subgroup.zpowers a₂ : Subgroup G) ∣ 3 := by
      rw [← h₂, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpc
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : (Subgroup.zpowers a₁ ⊓ Subgroup.zpowers a₂ : Subgroup G) =
          Subgroup.zpowers a₂ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hpc, Nat.card_zpowers, h₂])
      exact hn ((heq ▸ inf_le_left : Subgroup.zpowers a₂ ≤ _) (Subgroup.mem_zpowers a₂))
  rw [hcl, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, h₁, h₂, sq]

theorem K2Setup.le_of_commute (h : K2Setup G Y Q) {N K₁ K₂ : Subgroup G} (hN : N.Normal)
    (hK₂N : K₂ ≤ N) (hK₂n : (K₂.subgroupOf N).Normal) (h3 : 3 ∣ Nat.card K₂)
    (hQ₂ : Q ≤ normalizer (K₂ : Set G)) (hK₁ : K₁ ≤ centralizer (K₂ : Set G)) : K₁ ≤ Y := by
  have hT := fc_sylow_inf h hN hK₂N hK₂n
  have hTne : Q ⊓ K₂ ≠ ⊥ := by
    intro hbot
    have hd := fc_dvd_card hT h3
    rw [hbot, Subgroup.card_bot] at hd
    exact absurd (Nat.le_of_dvd one_pos hd) (by norm_num)
  have hY := h.normalizer_le_of_normal inf_le_left (fc_le_normalizer_inf hQ₂) hTne
  exact hK₁.trans ((centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).2)).trans
    ((centralizer_le_normalizer _).trans hY))

theorem K2Setup.le_of_three_commuting (h : K2Setup G Y Q) {N K₀ K₁ K₂ : Subgroup G}
    (hN : N.Normal) (h₁N : K₁ ≤ N) (h₂N : K₂ ≤ N) (h₁n : (K₁.subgroupOf N).Normal)
    (h₂n : (K₂.subgroupOf N).Normal) (h₁3 : 3 ∣ Nat.card K₁) (h₂3 : 3 ∣ Nat.card K₂)
    (h₀₁ : K₀ ≤ centralizer (K₁ : Set G)) (h₀₂ : K₀ ≤ centralizer (K₂ : Set G))
    (h₁₂ : K₁ ≤ centralizer (K₂ : Set G)) (hd : K₁ ⊓ K₂ = ⊥) : K₀ ≤ Y := by
  have hT₁ := fc_sylow_inf h hN h₁N h₁n
  have hT₂ := fc_sylow_inf h hN h₂N h₂n
  obtain ⟨a₁, ha₁T, ha₁⟩ := fc_exists_order_three hT₁ h₁3
  obtain ⟨a₂, ha₂T, ha₂⟩ := fc_exists_order_three hT₂ h₂3
  have ha₁Q : a₁ ∈ Q := (Subgroup.mem_inf.mp ha₁T).1
  have ha₁K : a₁ ∈ K₁ := (Subgroup.mem_inf.mp ha₁T).2
  have ha₂Q : a₂ ∈ Q := (Subgroup.mem_inf.mp ha₂T).1
  have ha₂K : a₂ ∈ K₂ := (Subgroup.mem_inf.mp ha₂T).2
  have ha₂1 : a₂ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha₂
    omega
  have hcomm : a₁ * a₂ = a₂ * a₁ :=
    ((Subgroup.mem_centralizer_iff.mp (h₁₂ ha₁K)) a₂ ha₂K).symm
  have hnot : a₂ ∉ Subgroup.zpowers a₁ := by
    intro hz
    have hmem : a₂ ∈ K₁ ⊓ K₂ :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.zpowers_le.mpr ha₁K) hz, ha₂K⟩
    rw [hd, Subgroup.mem_bot] at hmem
    exact ha₂1 hmem
  obtain ⟨hE, hcard⟩ := fc_card_closure_pair ha₁ ha₂ hcomm hnot
  have hEQ : Subgroup.closure ({a₁, a₂} : Set G) ≤ Q := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact ha₁Q
    · rw [Set.mem_singleton_iff.mp hx]
      exact ha₂Q
  have hrank : 2 ≤ CFSG.Open.pRank 3 (Subgroup.closure ({a₁, a₂} : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hcard
  have hyE := h.y1 _ hEQ hrank
  have hK₀E : K₀ ≤ centralizer ((Subgroup.closure ({a₁, a₂} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_centralizer_iff.mp (h₀₁ hk) a₁ ha₁K
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_iff.mp (h₀₂ hk) a₂ ha₂K
  exact hK₀E.trans ((centralizer_le_normalizer _).trans hyE)

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

open CFSG.LocalAnalysis.RankThreeTheoremC (SimpleFactorData)

theorem K2Setup.minimal_normal_data (h : K2Setup G Y Q)
    (hG : primeComplementCore (G := G) 3 = ⊥) {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ SimpleFactorData N S ∧
      ∀ i, 3 ∣ Nat.card (S i) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : N.Normal := hN
  have h3 : 3 ∣ Nat.card N := by
    by_contra hnd
    have hcop : Nat.Coprime 3 (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
    have hle := normal_coprime_le_primeComplementCore 3 N hN hcop
    rw [hG] at hle
    exact hN1 (le_bot_iff.mp hle)
  have hnonab : ∃ a b : N, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hsolv : Group.IsSolvable N := Group.isSolvable_of_comm hab
    have hminN : CFSG.RankThreeEvenClassification.Helpers.MinimalNontrivialNormal N := by
      refine ⟨⟨hN, hN1⟩, fun M hM hMN => ?_⟩
      rcases hmin M hM.1 hMN with hM1 | hMeq
      · exact absurd hM1 hM.2
      · exact hMeq.ge
    obtain ⟨p, hp, -, d, -, hcard⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary N hminN hsolv
    have hp3 : p = 3 := by
      have h3p : 3 ∣ p ^ d := by
        rw [← hcard]
        exact h3
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3p)).symm
    subst hp3
    have hNp : IsPGroup 3 N := IsPGroup.of_card hcard
    have hNQ : N ≤ Q := hNp.le_sylow_of_normal (h.pgroup.toSylow h.index)
    exact h.not_normal_le hN h3 (hNQ.trans h.le)
  obtain ⟨r, S, hr, hSle, hSsimple, hSconj, hSnormal, hprod⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN hN1 hmin
  have hSnonab : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    intro i
    by_contra hi
    push Not at hi
    have hcomm : ∀ j, ∀ u ∈ S j, ∀ v ∈ S j, u * v = v * u := by
      intro j u hu v hv
      obtain ⟨g, hg⟩ := hSconj i j
      rw [hg] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hi ⟨u', hu'⟩ ⟨v', hv'⟩))
    obtain ⟨a, b, hab⟩ := hnonab
    obtain ⟨e, -⟩ := hprod
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    refine hab ?_
    rw [← map_mul, ← map_mul]
    congr 1
    funext j
    exact Subtype.ext (hcomm j _ (x j).2 _ (y j).2)
  have hcardconj : ∀ i j, Nat.card (S j) = Nat.card (S i) := by
    intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    rw [hg]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulEquiv.injective (MulAut.conj g⁻¹))
  have hprodcard : Nat.card N = ∏ i, Nat.card (S i) := by
    obtain ⟨e, -⟩ := hprod
    rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
  have hdvd : ∀ i, 3 ∣ Nat.card (S i) := by
    have h3prod : 3 ∣ ∏ i, Nat.card (S i) := by
      rw [← hprodcard]
      exact h3
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h3prod
    intro j
    rw [hcardconj i j]
    exact hi
  exact ⟨r, S, hr, ⟨hSle, hSsimple, hSnonab, hSnormal, hprod⟩, hdvd⟩

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

open CFSG.LocalAnalysis.RankThreeTheoremC (SimpleFactorData)

theorem simpleFactorData_le_iSup {N : Subgroup G} {r : ℕ} {S : Fin r → Subgroup G}
    (hS : SimpleFactorData N S) : N ≤ ⨆ i, S i := by
  obtain ⟨e, he⟩ := hS.prod
  have key : ∀ s : Finset (Fin r), ∀ x : (j : Fin r) → S j, (∀ j ∉ s, x j = 1) →
      ((e x : N) : G) ∈ ⨆ i, S i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro x hx
      have hx1 : x = 1 := funext fun j => hx j (Finset.notMem_empty j)
      rw [hx1]
      simp
    · intro i t hi ih x hx
      have hfac : x = Pi.mulSingle (M := fun k => ↥(S k)) i (x i) * Function.update x i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · have h0 : Pi.mulSingle (M := fun k => ↥(S k)) i (x i) j = 1 :=
            Pi.mulSingle_eq_of_ne (M := fun k => ↥(S k)) hji (x i)
          rw [Pi.mul_apply, h0, Function.update_of_ne hji, one_mul]
      have hupd : ∀ j ∉ t, Function.update x i 1 j = 1 := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact hx j (by simp [hji, hj])
      have h1 : ((e (Pi.mulSingle (M := fun k => ↥(S k)) i (x i)) : N) : G) ∈ ⨆ j, S j := by
        have hval : ((e (Pi.mulSingle (M := fun k => ↥(S k)) i (x i)) : N) : G) = (x i : G) := by
          rw [he i (Pi.mulSingle (M := fun k => ↥(S k)) i (x i))
            (fun j hj => Pi.mulSingle_eq_of_ne (M := fun k => ↥(S k)) hj (x i))]
          simp
        rw [hval]
        exact (le_iSup S i) (x i).2
      have h2 := ih (Function.update x i 1) hupd
      rw [hfac, map_mul, Subgroup.coe_mul]
      exact mul_mem h1 h2
  intro n hn
  have h := key Finset.univ (e.symm ⟨n, hn⟩) (fun j hj => absurd (Finset.mem_univ j) hj)
  rwa [MulEquiv.apply_symm_apply] at h

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

open CFSG.LocalAnalysis.RankThreeTheoremC (SimpleFactorData)

theorem K2Setup.card_not_ge_three (h : K2Setup G Y Q) {N : Subgroup G} (hN : N.Normal) {r : ℕ}
    {S : Fin r → Subgroup G} (hS : SimpleFactorData N S) (h3 : ∀ i, 3 ∣ Nat.card (S i))
    (hr : 3 ≤ r) : False := by
  have hpick : ∀ i : Fin r, ∃ j k : Fin r, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    intro i
    obtain ⟨m, hm⟩ := i
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · rcases Nat.lt_or_ge m 1 with hlt1 | hge1
      · obtain rfl : m = 0 := by omega
        exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
          by simp [Fin.ext_iff]⟩
      · obtain rfl : m = 1 := by omega
        exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
          by simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, (by simp [Fin.ext_iff]; omega),
        (by simp [Fin.ext_iff]; omega), by simp [Fin.ext_iff]⟩
  have hcomm : ∀ {i j : Fin r}, i ≠ j → S i ≤ centralizer ((S j : Subgroup G) : Set G) := by
    intro i j hij x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hS.commute hij.symm (SetLike.mem_coe.1 hg) hx
  have hSY : ∀ i : Fin r, S i ≤ Y := by
    intro i
    obtain ⟨j, k, hji, hki, hjk⟩ := hpick i
    exact h.le_of_three_commuting hN (hS.le j) (hS.le k) (hS.normal j) (hS.normal k)
      (h3 j) (h3 k) (hcomm hji.symm) (hcomm hki.symm) (hcomm hjk) (hS.inf_eq_bot hjk)
  have hNY : N ≤ Y := (simpleFactorData_le_iSup hS).trans (iSup_le fun i => hSY i)
  have h3N : 3 ∣ Nat.card N :=
    dvd_trans (h3 ⟨0, by omega⟩) (Subgroup.card_dvd_of_le (hS.le ⟨0, by omega⟩))
  exact h.not_normal_le hN h3N hNY

end Cards

open CFSG.LocalAnalysis.RankThreeTheoremC (SimpleFactorData)

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

private lemma fcc_conj_mul (x y : G) :
    (MulAut.conj (x * y)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
  ext z
  simp [MulAut.conj_apply, mul_assoc]

private lemma fcc_map_conj_mul (K : Subgroup G) (x y : G) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [fcc_conj_mul, Subgroup.map_map]

private lemma fcc_odd_fix (X Z : Subgroup G) (hXZ : X ≠ Z)
    (h1 : ∀ g : G, X.map (MulAut.conj g).toMonoidHom = X ∨ X.map (MulAut.conj g).toMonoidHom = Z)
    (h2 : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom = X ∨ Z.map (MulAut.conj g).toMonoidHom = Z)
    (g : G) (m : ℕ) (hg : g ^ (2 * m + 1) = 1) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  by_contra hne
  have hgXZ : X.map (MulAut.conj g).toMonoidHom = Z := (h1 g).resolve_left hne
  have hgZX : Z.map (MulAut.conj g).toMonoidHom = X := by
    rcases h2 g with h | h
    · exact h
    · exact absurd (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective (hgXZ.trans h.symm)) hXZ
  have hsq : X.map (MulAut.conj (g * g)).toMonoidHom = X := by
    rw [fcc_map_conj_mul, hgXZ, hgZX]
  have hodd : ∀ n : ℕ, X.map (MulAut.conj (g ^ (2 * n + 1))).toMonoidHom = Z := by
    intro n
    induction n with
    | zero => simpa using hgXZ
    | succ n ih =>
      have e : g ^ (2 * (n + 1) + 1) = g ^ (2 * n + 1) * (g * g) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add g (2 * n + 1) 2, sq]
      rw [e, fcc_map_conj_mul, hsq, ih]
  have h := hodd m
  rw [hg, show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from
    MonoidHom.ext fun z => by simp [MulAut.conj_apply], Subgroup.map_id] at h
  exact hXZ h

theorem normalizes_factors_of_two {N : Subgroup G} (hN : N.Normal) {S : Fin 2 → Subgroup G}
    (hS : SimpleFactorData N S) {Q : Subgroup G} (hQ : IsPGroup 3 Q) (i : Fin 2) :
    Q ≤ normalizer (S i : Set G) := by
  haveI : N.Normal := hN
  have hne : S 0 ≠ S 1 := by
    intro heq
    have h01 : S 0 ⊓ S 1 = ⊥ := hS.inf_eq_bot (by decide)
    rw [← heq, inf_idem] at h01
    obtain ⟨a, b, hab⟩ := hS.nonabelian 0
    have ha : a = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h01 a a.2)
    have hb : b = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h01 b b.2)
    exact hab (by rw [ha, hb])
  have dich : ∀ (j : Fin 2) (g : G), (S j).map (MulAut.conj g).toMonoidHom = S 0 ∨
      (S j).map (MulAut.conj g).toMonoidHom = S 1 := by
    intro j g
    obtain ⟨l, hl⟩ := hS.exists_conj_eq g j
    rw [hl]
    fin_cases l <;> simp
  have fix : ∀ q ∈ Q, ∀ j : Fin 2, (S j).map (MulAut.conj q).toMonoidHom = S j := by
    intro q hq j
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    have hk' : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : Odd (3 : ℕ) := Nat.odd_iff.mpr (by norm_num)
    obtain ⟨m, hm⟩ := h3.pow (n := k)
    rw [hm] at hk'
    fin_cases j
    · exact fcc_odd_fix (S 0) (S 1) hne (dich 0) (dich 1) q m hk'
    · exact fcc_odd_fix (S 1) (S 0) hne.symm (fun g => (dich 1 g).symm)
        (fun g => (dich 0 g).symm) q m hk'
  intro q hq
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (fix q hq i)

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

open CFSG.LocalAnalysis.RankThreeTheoremC (SimpleFactorData)

theorem K2Setup.card_ne_two (h : K2Setup G Y Q) {N : Subgroup G} (hN : N.Normal)
    {S : Fin 2 → Subgroup G} (hS : SimpleFactorData N S) (h3 : ∀ i, 3 ∣ Nat.card (S i)) :
    False := by
  have h0 : S 0 ≤ Y := by
    refine h.le_of_commute hN (hS.le 1) (hS.normal 1) (h3 1)
      (normalizes_factors_of_two hN hS h.pgroup 1) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hS.commute (i := 1) (j := 0) (by decide) (SetLike.mem_coe.1 hy) hx
  have h1 : S 1 ≤ Y := by
    refine h.le_of_commute hN (hS.le 0) (hS.normal 0) (h3 0)
      (normalizes_factors_of_two hN hS h.pgroup 0) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hS.commute (i := 0) (j := 1) (by decide) (SetLike.mem_coe.1 hy) hx
  have hall : ∀ i : Fin 2, S i ≤ Y := Fin.forall_fin_two.2 ⟨h0, h1⟩
  have hsup : (⨆ i, S i) ≤ Y := iSup_le hall
  have hNY : N ≤ Y := (simpleFactorData_le_iSup hS).trans hsup
  exact h.not_normal_le hN (dvd_trans (h3 0) (Subgroup.card_dvd_of_le (hS.le 0))) hNY

theorem K2Setup.card_eq_one (h : K2Setup G Y Q) {N : Subgroup G} (hN : N.Normal) {r : ℕ}
    {S : Fin r → Subgroup G} (hS : SimpleFactorData N S) (h3 : ∀ i, 3 ∣ Nat.card (S i))
    (hr : 1 ≤ r) : r = 1 := by
  by_contra hne
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hge
  · exact h.card_ne_two hN hS h3
  · exact h.card_not_ge_three hN hS h3 hge

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem K2Setup.centralizer_eq_bot (h : K2Setup G Y Q)
    (hG : primeComplementCore (G := G) 3 = ⊥) {L : Subgroup G} (hL : L.Normal)
    (hLs : IsSimpleGroup L) (hLn : ∃ a b : L, a * b ≠ b * a) (h3 : 3 ∣ Nat.card L) :
    centralizer (L : Set G) = ⊥ := by
  by_contra hne
  haveI : L.Normal := hL
  obtain ⟨M, hMn, hMC, hMne, -⟩ :=
    CFSG.exists_minimal_normal_le (centralizer (L : Set G)) inferInstance hne
  haveI : M.Normal := hMn
  have h3M : 3 ∣ Nat.card M := by
    by_contra hnd
    have hcop : Nat.Coprime 3 (Nat.card M) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
    have hle : M ≤ primeComplementCore (G := G) 3 :=
      normal_coprime_le_primeComplementCore 3 M hMn hcop
    rw [hG] at hle
    exact hMne (eq_bot_iff.2 hle)
  have hLM : L ≤ centralizer (M : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact ((Subgroup.mem_centralizer_iff.1 (hMC hm)) x hx).symm
  have hMY : L ≤ Y := by
    refine K2Setup.le_of_commute h (N := M) (K₁ := L) (K₂ := M) hMn le_rfl ?_ h3M ?_ hLM
    · rw [Subgroup.subgroupOf_self]
      infer_instance
    · rw [Subgroup.normalizer_eq_top]
      exact le_top
  exact K2Setup.not_normal_le h hL h3 hMY

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem K2Setup.exists_simple_normal (h : K2Setup G Y Q)
    (hG : primeComplementCore (G := G) 3 = ⊥) :
    ∃ L : Subgroup G, L.Normal ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      3 ∣ Nat.card L ∧ centralizer (L : Set G) = ⊥ := by
  obtain ⟨x, hx3, -⟩ := h.elt
  have hTB : (⊤ : Subgroup G) ≠ ⊥ := by
    intro hTop
    have hxt : x ∈ (⊤ : Subgroup G) := Subgroup.mem_top x
    rw [hTop, Subgroup.mem_bot] at hxt
    rw [hxt, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  obtain ⟨N, hN, -, hN1, hminN⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance hTB
  have hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hMN
    by_cases hM1 : M = ⊥
    · exact Or.inl hM1
    · exact Or.inr (hminN M hM hMN hM1)
  obtain ⟨r, S, hr, hS, h3⟩ := h.minimal_normal_data hG hN hN1 hmin
  have hr1 : r = 1 := h.card_eq_one hN hS h3 hr
  subst hr1
  have hNS : N = S 0 := by
    refine le_antisymm ?_ (hS.le 0)
    obtain ⟨e, he⟩ := hS.prod
    intro n hn
    have key : ((e (e.symm (⟨n, hn⟩ : N)) : N) : G) = n :=
      congrArg Subtype.val (e.apply_symm_apply (⟨n, hn⟩ : N))
    have key2 := he 0 (e.symm (⟨n, hn⟩ : N)) (fun j hj => absurd (Subsingleton.elim j 0) hj)
    have hval : (((e.symm (⟨n, hn⟩ : N)) 0 : S 0) : G) = n := key2.symm.trans key
    have hmem : (((e.symm (⟨n, hn⟩ : N)) 0 : S 0) : G) ∈ S 0 := ((e.symm (⟨n, hn⟩ : N)) 0).2
    rwa [hval] at hmem
  subst hNS
  exact ⟨S 0, hN, hS.simple 0, hS.nonabelian 0, h3 0,
    h.centralizer_eq_bot hG hN (hS.simple 0) (hS.nonabelian 0) (h3 0)⟩

end Cards

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
