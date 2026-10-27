module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSClass
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSData
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Certificate2219
public import Certificates.Certificate2220
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSA6Inputs
public import Certificates.Certificate4066
public import Certificates.Certificate4081
public import Certificates.Certificate2218

public noncomputable section

namespace CFSG.QuasithinUnique.Id2519.UHS

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def letterPerm (l : ℕ) : Equiv.Perm (Fin 3850) :=
  if l = 0 then hsGen 0 else if l = 1 then hsGen 1 else (hsGen 1)⁻¹

theorem rep_letter (l : ℕ) : Rep 3850 (letterArr l) (letterPerm l) ∧ letterPerm l ∈ PP := by
  have h0 := hs_gens 0 (by decide)
  have h1 := hs_gens 1 (by decide)
  unfold letterArr letterPerm
  split_ifs
  · exact ⟨h0.1, h0.2.2⟩
  · exact ⟨h1.1, h1.2.2⟩
  · exact ⟨h1.2.1, inv_mem h1.2.2⟩

@[expose] def wElt (ws : List ℕ) : Equiv.Perm (Fin 3850) := (ws.map letterPerm).prod

theorem repW_wArr (ws : List ℕ) : RepW 3850 (wArr ws) (wElt ws) := by
  have h : List.Forall₂ (Rep 3850) (ws.map letterArr) (ws.map letterPerm) := by
    induction ws with
    | nil => exact List.Forall₂.nil
    | cons l ws ih => exact List.Forall₂.cons (rep_letter l).1 ih
  exact repW_reverse h

theorem wElt_mem (ws : List ℕ) : wElt ws ∈ PP := by
  unfold wElt
  refine PP.list_prod_mem fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  exact (rep_letter l).2

theorem wElt_append (ws₁ ws₂ : List ℕ) : wElt (ws₁ ++ ws₂) = wElt ws₁ * wElt ws₂ := by
  simp [wElt]

theorem wElt_cLetters : wElt cLetters = hsC := by
  simp [wElt, cLetters, letterPerm, hsC, List.replicate, pow_succ, mul_assoc]

theorem a6_check : a6Check = true :=
  Certificates.certificate4066

@[expose] def nodeElt (k : ℕ) : Equiv.Perm (Fin 3850) := wElt (nodeWord k)

theorem a6_facts :
    orderOf (wElt y1Letters) = 3 ∧ orderOf (wElt y2Letters) = 5 ∧
      wElt y1Letters * hsC = hsC * wElt y1Letters ∧
      wElt y2Letters * hsC = hsC * wElt y2Letters ∧
      (∀ k < 360, ∀ k' < 360, nodeElt k = nodeElt k' → k = k') ∧
      (∀ k < 360, orderOf (nodeElt k) = 2 →
        ∃ d ∈ PP, d * hsC * d⁻¹ = hsC * nodeElt k) := by
  have h := a6_check
  simp only [a6Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩, h8⟩ := h
  have hbs := hs_bs_lt
  have hbf := hs_baseFaithful
  have hnodeW : ∀ k, RepW 3850 (wArr (nodeWord k)) (nodeElt k) := fun k => repW_wArr _
  refine ⟨(ordB_iff hbf hbs (repW_wArr _) (wElt_mem _) (by norm_num)).1 h1,
    (ordB_iff hbf hbs (repW_wArr _) (wElt_mem _) (by norm_num)).1 h2, ?_, ?_, ?_, ?_⟩
  · have := eq_of_baseImgs_eq hbf hbs (repW_wArr _) (repW_wArr _) (wElt_mem _) (wElt_mem _) h3
    rwa [wElt_append, wElt_append, wElt_cLetters] at this
  · have := eq_of_baseImgs_eq hbf hbs (repW_wArr _) (repW_wArr _) (wElt_mem _) (wElt_mem _) h4
    rwa [wElt_append, wElt_append, wElt_cLetters] at this
  · intro k hk k' hk' hkk
    have hkey : ∀ j, imgKey 3850 (baseImgs PairHS.bs (wArr (nodeWord j))) =
        keyElt 3850 PairHS.bs (nodeElt j) := fun j => imgKey_baseImgs hbs (hnodeW j)
    have hnd := (List.mergeSort_perm _ _).nodup_iff.1
      ((pairwise_of_strictInc h7).imp (fun hab => Nat.ne_of_lt hab))
    have hfun : (fun k => imgKey 3850 (baseImgs PairHS.bs (wArr (nodeWord k)))) =
        fun j => keyElt 3850 PairHS.bs (nodeElt j) := funext hkey
    rw [hfun] at hnd
    have hnd' : ((List.range 360).map fun j => keyElt 3850 PairHS.bs (nodeElt j)).Nodup := hnd
    have := (List.nodup_map_iff_inj_on (List.nodup_range)).1 hnd'
    exact this k (List.mem_range.2 hk) k' (List.mem_range.2 hk') (by rw [hkk])
  · intro k hk hord
    have hk' := h8 k hk
    have hord' : ordB PairHS.bs (wArr (nodeWord k)) 2 = true :=
      (ordB_iff hbf hbs (hnodeW k) (wElt_mem _) (by norm_num)).2 hord
    rcases hk' with hk' | hk'
    · rw [hord'] at hk'
      exact absurd hk' (by decide)
    · have := eq_of_baseImgs_eq hbf hbs (repW_wArr _) (repW_wArr _) (wElt_mem _) (wElt_mem _) hk'
      rw [wElt_append, wElt_append, wElt_append, wElt_cLetters] at this
      refine ⟨wElt conjWords[k]!, wElt_mem _, ?_⟩
      rw [mul_inv_eq_iff_eq_mul, this]
      rfl

@[expose] def sC : PP := ⟨hsC, hsC_mem⟩

@[expose] def yElt0 : PP := ⟨wElt y1Letters, wElt_mem _⟩

@[expose] def yElt1 : PP := ⟨wElt y2Letters, wElt_mem _⟩

theorem nodeElt_mem {K : Subgroup PP} (h0 : yElt0 ∈ K) (h1 : yElt1 ∈ K) :
    ∀ fuel k, (⟨wElt (nodeWordFuel fuel k), wElt_mem _⟩ : PP) ∈ K := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    have : (⟨wElt (nodeWordFuel 0 k), wElt_mem _⟩ : PP) = 1 :=
      Subtype.ext (by simp [nodeWordFuel, wElt])
    rw [this]
    exact K.one_mem
  | succ fuel ih =>
    intro k
    by_cases hk : k = 0
    · have : (⟨wElt (nodeWordFuel (fuel + 1) k), wElt_mem _⟩ : PP) = 1 :=
        Subtype.ext (by simp [nodeWordFuel, hk, wElt])
      rw [this]
      exact K.one_mem
    · by_cases hl : nodeLab[k]! = 0
      · have h : (⟨wElt (nodeWordFuel (fuel + 1) k), wElt_mem _⟩ : PP) =
            ⟨wElt (nodeWordFuel fuel nodePar[k]!), wElt_mem _⟩ * yElt0 := by
          refine Subtype.ext ?_
          simp only [nodeWordFuel, hk, hl, ite_false, ite_true, Subgroup.coe_mul, yElt0]
          rw [wElt_append]
        rw [h]
        exact K.mul_mem (ih _) h0
      · have h : (⟨wElt (nodeWordFuel (fuel + 1) k), wElt_mem _⟩ : PP) =
            ⟨wElt (nodeWordFuel fuel nodePar[k]!), wElt_mem _⟩ * yElt1 := by
          refine Subtype.ext ?_
          simp only [nodeWordFuel, hk, hl, ite_false, Subgroup.coe_mul, yElt1]
          rw [wElt_append]
        rw [h]
        exact K.mul_mem (ih _) h1

theorem hs_core_c (K : Subgroup PP) (hK : Nat.card K = 360) (hKc : ∀ k ∈ K, k * sC = sC * k)
    (hnorm : ∀ c : PP, c * sC = sC * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    ∀ u ∈ K, u * u = 1 → ∃ d : PP, d * sC * d⁻¹ = sC * u := by
  obtain ⟨ho1, ho2, hc1, hc2, hinj, hconj⟩ := a6_facts
  set Cs : Subgroup PP := Subgroup.centralizer ({sC} : Set PP) with hCsdef
  have hCs : Nat.card Cs = 2880 := card_centralizer_c
  have hKle : K ≤ Cs := fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hKc k hk)
  have hCle : Cs ≤ Subgroup.normalizer (K : Set PP) := fun c hc => by
    have hcc : c * sC = sC * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcc' : c⁻¹ * sC = sC * c⁻¹ := by
      calc c⁻¹ * sC = c⁻¹ * (sC * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * sC) * c⁻¹ := by rw [hcc]
        _ = sC * c⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm c hcc h hh, fun hh => ?_⟩
    have := hnorm c⁻¹ hcc' _ hh
    simpa [mul_assoc] using this
  have hN : (K.subgroupOf Cs).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKle]
    exact hCle
  have hidx : (K.subgroupOf Cs).index = 8 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf Cs)
    have h2 : Nat.card (K.subgroupOf Cs) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
    rw [h2, hK, hCs] at h1
    omega
  have hpow : ∀ g ∈ Cs, g ^ 8 ∈ K := fun g hg => by
    have := Subgroup.pow_index_mem (K.subgroupOf Cs) (⟨g, hg⟩ : Cs)
    rw [hidx, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hy : ∀ y : PP, y * sC = sC * y → y ^ 16 = y → y ∈ K := by
    intro y hcomm h16
    have hmem : y ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hcomm
    rw [← h16]
    have : y ^ 16 = (y ^ 8) ^ 2 := by rw [← pow_mul]
    rw [this]
    exact K.pow_mem (hpow _ hmem) 2
  have hy0 : yElt0 ∈ K := by
    refine hy _ (Subtype.ext hc1) ?_
    refine Subtype.ext ?_
    have h3 : wElt y1Letters ^ 3 = 1 := by
      have := pow_orderOf_eq_one (wElt y1Letters)
      rwa [ho1] at this
    simp only [yElt0, Subgroup.coe_pow]
    calc wElt y1Letters ^ 16 = (wElt y1Letters ^ 3) ^ 5 * wElt y1Letters := by
          rw [← pow_mul, ← pow_succ]
      _ = wElt y1Letters := by rw [h3]; simp
  have hy1 : yElt1 ∈ K := by
    refine hy _ (Subtype.ext hc2) ?_
    refine Subtype.ext ?_
    have h5 : wElt y2Letters ^ 5 = 1 := by
      have := pow_orderOf_eq_one (wElt y2Letters)
      rwa [ho2] at this
    simp only [yElt1, Subgroup.coe_pow]
    calc wElt y2Letters ^ 16 = (wElt y2Letters ^ 5) ^ 3 * wElt y2Letters := by
          rw [← pow_mul, ← pow_succ]
      _ = wElt y2Letters := by rw [h5]; simp
  set f : Fin 360 → PP := fun k => ⟨nodeElt k, wElt_mem _⟩ with hf
  have hfinj : Function.Injective f := by
    intro k k' h
    exact Fin.ext (hinj k k.2 k' k'.2 (congrArg Subtype.val h))
  have hfK : ∀ k, f k ∈ K := fun k => nodeElt_mem hy0 hy1 360 k
  have hSsub : Set.range f ⊆ (K : Set PP) := by
    rintro _ ⟨k, rfl⟩
    exact hfK k
  have hSncard : (Set.range f).ncard = 360 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hfinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hKncard : (K : Set PP).ncard = 360 := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  have hSeq : Set.range f = (K : Set PP) :=
    Set.eq_of_subset_of_ncard_le hSsub (by rw [hSncard, hKncard])
  intro u hu hu2
  obtain ⟨k, hk⟩ : u ∈ Set.range f := hSeq ▸ hu
  by_cases hu1 : u = 1
  · exact ⟨1, by rw [hu1]; simp⟩
  · have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have hord' : orderOf (nodeElt k) = 2 := by
      rw [← Subgroup.orderOf_coe u, ← hk] at hord
      exact hord
    obtain ⟨d, hdP, hd⟩ := hconj k k.2 hord'
    refine ⟨⟨d, hdP⟩, Subtype.ext ?_⟩
    rw [← hk]
    exact hd

end CFSG.QuasithinUnique.Id2519.UHS
