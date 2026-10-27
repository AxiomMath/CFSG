module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import Certificates.Certificate117031

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup

@[expose] def FiveLocal {M : Type*} [Group M] (P : Subgroup M) (u f : M) : Prop :=
  Nat.card ↥(P ⊓ centralizer ({f} : Set M)) = 300 ∧
    ∃ A : Subgroup M, A ≤ P ⊓ centralizer ({f} : Set M) ∧
      Nonempty (↥A ≃* alternatingGroup (Fin 5)) ∧ u ∈ A ∧
      P ⊓ centralizer ({f} : Set M) = zpowers f ⊔ A ∧
      Nat.card ↥(A ⊓ centralizer ({u} : Set M)) = 4

theorem map_centralizer_single {K M : Type*} [Group K] [Group M] (φ : K →* M)
    (hφ : Function.Injective φ) (y : K) :
    (centralizer ({y} : Set K)).map φ = φ.range ⊓ centralizer ({φ y} : Set M) := by
  ext z
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, ha]
  · rintro ⟨⟨a, rfl⟩, h⟩
    refine ⟨a, ?_, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact h

theorem fiveLocal_top_iff {K M : Type*} [Group K] [Group M] (φ : K →* M)
    (hφ : Function.Injective φ) (x y : K) :
    FiveLocal (⊤ : Subgroup K) x y ↔ FiveLocal φ.range (φ x) (φ y) := by
  have hC : ∀ z : K, (⊤ ⊓ centralizer ({z} : Set K)).map φ =
      φ.range ⊓ centralizer ({φ z} : Set M) := by
    intro z
    rw [top_inf_eq]
    exact map_centralizer_single φ hφ z
  constructor
  · rintro ⟨hcard, A, hA, ⟨e⟩, hx, hsup, hAx⟩
    refine ⟨?_, A.map φ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hC y, Subgroup.card_map_of_injective hφ]
      exact hcard
    · rw [← hC y]
      exact Subgroup.map_mono hA
    · exact ⟨(A.equivMapOfInjective φ hφ).symm.trans e⟩
    · exact mem_map_of_mem φ hx
    · rw [← hC y, hsup, Subgroup.map_sup, MonoidHom.map_zpowers]
    · rw [← hAx, ← (Subgroup.card_map_of_injective hφ :
        Nat.card ↥((A ⊓ centralizer ({x} : Set K)).map φ) = _),
        Subgroup.map_inf_eq _ _ φ hφ, map_centralizer_single φ hφ x]
      have h2 : A.map φ ≤ φ.range := fun z hz => by
        obtain ⟨a, -, rfl⟩ := hz
        exact ⟨a, rfl⟩
      congr 2
      rw [← inf_assoc, inf_of_le_left h2]
  · rintro ⟨hcard, A, hA, ⟨e⟩, hx, hsup, hAx⟩
    have hAr : A ≤ φ.range := fun z hz => (inf_le_left : _ ≤ φ.range) (hA hz)
    set A' : Subgroup K := A.comap φ with hA'
    have hmapA : A'.map φ = A := Subgroup.map_comap_eq_self hAr
    refine ⟨?_, A', ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective hφ, hC y]
      exact hcard
    · rw [← Subgroup.map_le_map_iff_of_injective hφ, hC y, hmapA]
      exact hA
    · exact ⟨(A'.equivMapOfInjective φ hφ).trans ((MulEquiv.subgroupCongr hmapA).trans e)⟩
    · exact hx
    · apply Subgroup.map_injective hφ
      rw [hC y, Subgroup.map_sup, MonoidHom.map_zpowers, hmapA]
      exact hsup
    · rw [← hAx, ← (Subgroup.card_map_of_injective hφ :
        Nat.card ↥((A' ⊓ centralizer ({x} : Set K)).map φ) = _),
        Subgroup.map_inf_eq _ _ φ hφ, map_centralizer_single φ hφ x, hmapA]
      congr 2
      rw [← inf_assoc, inf_of_le_left hAr]

theorem FiveLocal.map_equiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {x y : K}
    (h : FiveLocal (⊤ : Subgroup K) x y) : FiveLocal (⊤ : Subgroup K') (e x) (e y) := by
  have := (fiveLocal_top_iff e.toMonoidHom e.injective x y).1 h
  rwa [MonoidHom.range_eq_top.2 e.surjective] at this

theorem card_centralizer_subtype_five {M : Type*} [Group M] (P : Subgroup M) (x : ↥P) :
    Nat.card ↥(centralizer ({x} : Set ↥P)) =
      Nat.card ↥(P ⊓ centralizer ({(x : M)} : Set M)) := by
  have h := map_centralizer_single P.subtype P.subtype_injective x
  rw [Subgroup.range_subtype] at h
  have h' : (centralizer ({x} : Set ↥P)).map P.subtype =
      P ⊓ centralizer ({(x : M)} : Set M) := h
  rw [← h']
  exact (Subgroup.card_map_of_injective P.subtype_injective).symm

theorem exists_conj_le_sylow_prime {p : ℕ} [Fact p.Prime] {W : Type*} [Group W] [Finite W]
    {F T : Subgroup W} (hF : IsPGroup p F) (hT : IsPGroup p T) (hTi : ¬ p ∣ T.index) :
    ∃ g : W, ∀ y ∈ F, g⁻¹ * y * g ∈ T := by
  obtain ⟨P₂, hP₂⟩ := hF.exists_le_sylow
  let P₁ : Sylow p W := hT.toSylow hTi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P₁ P₂
  refine ⟨g, fun y hy => ?_⟩
  have h1 : y ∈ (P₂ : Subgroup W) := hP₂ hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : ∀ x : W, x ∈ (P₁ : Subgroup W) ↔ x ∈ T := fun x => hT.mem_toSylow hTi
  rw [h2] at h1
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using h1

theorem isConj_of_orderOf_eq_three {W : Type*} [Group W] (hW : Nat.card W = 44352000)
    {T : Subgroup W} (hT : Nat.card T = 9) {t : W}
    (hconj : ∀ s ∈ T, s ≠ 1 → IsConj t s) {a b : W} (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj a b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT]; norm_num)
  have hTi : ¬ 3 ∣ T.index := by
    have h := T.index_mul_card
    rw [hT, hW] at h
    intro hd
    omega
  have key : ∀ c : W, orderOf c = 3 → IsConj c t := by
    intro c hc
    have hcp : IsPGroup 3 (zpowers c) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hc]
      norm_num
    obtain ⟨g, hg⟩ := exists_conj_le_sylow_prime hcp hTp hTi
    have hs := hg c (mem_zpowers c)
    have hs1 : g⁻¹ * c * g ≠ 1 := by
      intro h1
      have : c = 1 := by
        have h2 : g * (g⁻¹ * c * g) * g⁻¹ = 1 := by rw [h1]; group
        simpa [mul_assoc] using h2
      rw [this, orderOf_one] at hc
      omega
    have h3 := hconj _ hs hs1
    refine (isConj_iff.2 ⟨g⁻¹, ?_⟩).trans h3.symm
    group
  exact (key a ha).trans (key b hb).symm

namespace HSFive

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd

theorem keys_lt : ∀ p ∈ keys, p < 100 := by
  intro p hp
  simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem rep_pw {x : Array ℕ} {X : Equiv.Perm (Fin 100)} (h : Rep 100 x X) :
    ∀ k, Rep 100 (pw x k) (X ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pw, pow_succ']
    exact rep_compA h (rep_pw h k)

theorem closure_pGens :
    Subgroup.closure (permsA 100 pGens) = hs100P := by
  have : permsA 100 pGens = {hs100A, hs100B} := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := by simpa [pGens] using hk
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [pGens], rfl⟩
      · exact ⟨1, by simp [pGens], rfl⟩
  rw [this]
  rfl

noncomputable abbrev U0 : Equiv.Perm (Fin 100) := permOfArr 100 u0

noncomputable abbrev F0 : Equiv.Perm (Fin 100) := permOfArr 100 f0

section Perm


theorem hsFive_check : hsFiveOK = true := Certificates.certificate117031

theorem inP_iff {a : Array ℕ} (hv : validA 100 a = true) :
    s5InP a = true ↔ permOfArr 100 a ∈ hs100P := s5InP_iff hv

theorem u0_spec : U0 ∈ hs100P ∧ orderOf U0 = 2 ∧
    Nat.card ↥(hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100)))) = 2880 := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, -⟩ := h
  have hrU : Rep 100 u0 U0 := rep_of_validA hvu
  have hU2 : U0 ^ 2 = 1 := by
    rw [pow_two]
    exact (eqA_iff (rep_compA hrU hrU) rep_idA).1 hu2
  have hU1 : U0 ≠ 1 := fun h1 => by
    have := (eqA_iff hrU rep_idA).2 h1
    rw [this] at hune
    exact absurd hune (by simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(inP_iff hvu).1 hPu, orderOf_eq_prime hU2 hU1, ?_⟩
  have hgs : ∀ k < pGens.size, validA 100 pGens[k]! = true := fun k hk => allLt_spec hvP hk
  obtain ⟨-, hcard⟩ := CFSG.RankThree.PartOne.card_closure_eq_card_mul_card_centralizer
    (n := 100) (gs := pGens) (ps := keys) keys_lt hgs horb
  rw [closure_pGens, card_hs100P, hosz] at hcard
  have hcard' : 44352000 = 15400 *
      Nat.card ↥(hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100)))) := hcard
  omega

theorem cu_eq : Subgroup.closure (permsA 100 cuGens) =
    hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100))) := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, henum, hsz, hgen, -⟩ := h
  have hrU : Rep 100 u0 U0 := rep_of_validA hvu
  obtain ⟨-, -, hcardU⟩ := u0_spec
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hv := enumOK_gens_valid henum hk
    have hg := allLt_spec hgen hk
    rw [Bool.and_eq_true] at hg
    refine Subgroup.mem_inf.2 ⟨(inP_iff hv).1 hg.2, mem_centralizer_singleton_iff.2 ?_⟩
    exact (commA_iff (rep_of_validA hv) hrU).1 hg.1
  · rw [hcardU, (enumOK_spec keys_lt henum).2.1, hsz]

theorem f0_spec : F0 ∈ hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100))) ∧
    orderOf F0 = 5 ∧
    ∀ X ∈ hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100))), orderOf X = 5 →
      ∃ Y ∈ hs100P ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100))), Y * X * Y⁻¹ = F0 := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, henum, hsz, hgen, hvf, hPf, hf5, hfne, hcomm,
    hconj, -⟩ := h
  have hrU : Rep 100 u0 U0 := rep_of_validA hvu
  have hrF : Rep 100 f0 F0 := rep_of_validA hvf
  have hF5 : F0 ^ 5 = 1 := (eqA_iff (rep_pw hrF 5) rep_idA).1 hf5
  have hF1 : F0 ≠ 1 := fun h1 => by
    have := (eqA_iff hrF rep_idA).2 h1
    rw [this] at hfne
    exact absurd hfne (by simp)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨Subgroup.mem_inf.2 ⟨(inP_iff hvf).1 hPf, mem_centralizer_singleton_iff.2 ?_⟩,
    orderOf_eq_prime hF5 hF1, fun X hX hX5 => ?_⟩
  · exact (commA_iff hrF hrU).1 hcomm
  rw [← cu_eq] at hX
  obtain ⟨hmem, -, hval⟩ := enumOK_spec keys_lt henum
  obtain ⟨i, hi, rfl⟩ := (hmem X).1 hX
  have hrx := rep_of_validA (hval i hi)
  have hxmem : cuCert.pts[i]! ∈ cuCert.pts.toList := by
    rw [getElem!_pos _ i hi]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
  have hc := List.all_eq_true.1 hconj _ hxmem
  have hX5' : permOfArr 100 cuCert.pts[i]! ^ 5 = 1 := by
    rw [← hX5]
    exact pow_orderOf_eq_one _
  have hX1 : permOfArr 100 cuCert.pts[i]! ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hX5
    omega
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at hc
  rcases hc with (hc | hc) | ⟨y, hy, hyx⟩
  · have := (eqA_iff (rep_pw hrx 5) rep_idA).2 hX5'
    rw [this] at hc
    exact absurd hc (by simp)
  · exact absurd ((eqA_iff hrx rep_idA).1 hc) hX1
  · have hry : Rep 100 y (permOfArr 100 y) := by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      have hj' : j < cuCert.pts.size := by simpa using hj
      rw [Array.getElem_toList]
      rw [← getElem!_pos cuCert.pts j hj']
      exact rep_of_validA (hval j hj')
    have hYX := (eqA_iff (rep_compA hry hrx) (rep_compA hrF hry)).1 hyx
    refine ⟨permOfArr 100 y, ?_, ?_⟩
    · rw [← cu_eq]
      exact enumOK_mem_of_mem keys_lt henum hry hy
    · rw [mul_inv_eq_iff_eq_mul]
      exact hYX

theorem cf_eq : Subgroup.closure (permsA 100 cfGens) =
    hs100P ⊓ centralizer ({F0} : Set (Equiv.Perm (Fin 100))) := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, henum, hsz, hgen, hvf, hPf, hf5, hfne, hcomm,
    hconj, hrels, hcf, hcfsz, hcfgen, htail, -⟩ := h
  have hrF : Rep 100 f0 F0 := rep_of_validA hvf
  have hcomm' : allLt cfGens.size (fun k => commA 100 cfGens[k]! f0) = true :=
    allLt_iff.2 fun k hk => (Bool.and_eq_true_iff.1 (allLt_iff.1 hcfgen k hk)).1
  have hsift : allLt cfGens.size
      (fun k => siftA 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) hs100BaseArr 0
        cfGens[k]!) = true :=
    allLt_iff.2 fun k hk => (Bool.and_eq_true_iff.1 (allLt_iff.1 hcfgen k hk)).2
  have := centralizer_eq_of_ptailOK hs100ChainArrays hs100_chain_check.1 hrF hrels keys_lt hcf
    hcomm' hsift htail
  rw [this, ← hs100P_eq_original, inf_comm]

theorem cf_card : Nat.card ↥(hs100P ⊓ centralizer ({F0} : Set (Equiv.Perm (Fin 100)))) = 300 := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, henum, hsz, hgen, hvf, hPf, hf5, hfne, hcomm,
    hconj, hrels, hcf, hcfsz, -⟩ := h
  rw [← cf_eq, (enumOK_spec keys_lt hcf).2.1, hcfsz]

theorem a_spec : ∃ A : Subgroup (Equiv.Perm (Fin 100)),
    A ≤ hs100P ⊓ centralizer ({F0} : Set (Equiv.Perm (Fin 100))) ∧
    IsSimpleGroup A ∧ Nat.card A = 60 ∧ U0 ∈ A ∧
    hs100P ⊓ centralizer ({F0} : Set (Equiv.Perm (Fin 100))) = zpowers F0 ⊔ A ∧
    Nat.card ↥(A ⊓ centralizer ({U0} : Set (Equiv.Perm (Fin 100)))) = 4 := by
  classical
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hvP, hvu, hPu, hu2, hune, horb, hosz, henum, hsz, hgen, hvf, hPf, hf5, hfne, hcomm,
    hconj, hrels, hcf, hcfsz, hcfgen, htail, ha, haz, hagen, hsimple, huA, hsplit, hacount,
    -⟩ := h
  have hrU : Rep 100 u0 U0 := rep_of_validA hvu
  have hrF : Rep 100 f0 F0 := rep_of_validA hvf
  have hF1 : F0 ∈ hs100P := (inP_iff hvf).1 hPf
  obtain ⟨hmemA, hcardA, hvalA⟩ := enumOK_spec keys_lt ha
  have hAle : Subgroup.closure (permsA 100 aGens) ≤
      hs100P ⊓ centralizer ({F0} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hv := enumOK_gens_valid ha hk
    have hg := allLt_spec hagen hk
    rw [Bool.and_eq_true] at hg
    exact Subgroup.mem_inf.2 ⟨(inP_iff hv).1 hg.2,
      mem_centralizer_singleton_iff.2 ((commA_iff (rep_of_validA hv) hrF).1 hg.1)⟩
  refine ⟨Subgroup.closure (permsA 100 aGens), hAle, ?_, ?_, ?_, ?_, ?_⟩
  · exact isSimpleGroup_of_conjSimpleOK keys_lt ha (by omega) hsimple
  · rw [hcardA, haz]
  · exact enumOK_mem_of_any keys_lt ha hrU huA
  · apply le_antisymm
    · intro g hg
      rw [← cf_eq] at hg
      obtain ⟨hmemC, -, hvalC⟩ := enumOK_spec keys_lt hcf
      obtain ⟨k, hk, rfl⟩ := (hmemC g).1 hg
      have hrk := rep_of_validA (hvalC k hk)
      have hkmem : cfCert.pts[k]! ∈ cfCert.pts.toList := by
        rw [getElem!_pos _ k hk]
        exact Array.mem_toList_iff.2 (Array.getElem_mem hk)
      have hc := List.all_eq_true.1 hsplit _ hkmem
      simp only [List.any_eq_true, List.mem_range] at hc
      obtain ⟨e, he, a, ha', hxe⟩ := hc
      have hra : Rep 100 a (permOfArr 100 a) := by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha'
        have hj' : j < aCert.pts.size := by simpa using hj
        rw [Array.getElem_toList]
        rw [← getElem!_pos aCert.pts j hj']
        exact rep_of_validA (hvalA j hj')
      have hx := (eqA_iff hrk (rep_compA (rep_pw hrF e) hra)).1 hxe
      rw [hx]
      exact Subgroup.mul_mem_sup ((Subgroup.zpowers F0).pow_mem (Subgroup.mem_zpowers F0) e)
        (enumOK_mem_of_mem keys_lt ha hra ha')
    · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hF1,
        mem_centralizer_singleton_iff.2 rfl⟩)) hAle
  · have hcs := card_subtype_enum (Subgroup.closure (permsA 100 aGens))
      (fun i => permOfArr 100 aCert.pts[i]!) (fun x => by
        rw [hmemA x]) hcardA (fun y => y ∈ centralizer ({U0} : Set (Equiv.Perm (Fin 100))))
    have h1 : Nat.card ↥(Subgroup.closure (permsA 100 aGens) ⊓
        centralizer ({U0} : Set (Equiv.Perm (Fin 100)))) =
        Nat.card {y : Subgroup.closure (permsA 100 aGens) //
          y.1 ∈ centralizer ({U0} : Set (Equiv.Perm (Fin 100)))} :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [h1, hcs, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hacount, aCommCount]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    have hrk := rep_of_validA (hvalA i.1 i.2)
    rw [mem_centralizer_singleton_iff, commA_iff hrU hrk]
    exact eq_comm

theorem fiveLocal_perm : FiveLocal hs100P U0 F0 := by
  obtain ⟨A, hA, hsimple, hcard, hu, hsup, hAu⟩ := a_spec
  have : Finite A := inferInstance
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := A) hcard
  exact ⟨cf_card, A, hA, ⟨e⟩, hu, hsup, hAu⟩

theorem three_spec : ∃ T : Subgroup (Equiv.Perm (Fin 100)), T ≤ hs100P ∧ Nat.card T = 9 ∧
    ∃ t ∈ T, orderOf t = 3 ∧ ∀ s ∈ T, s ≠ 1 → ∃ c ∈ hs100P, c * t * c⁻¹ = s := by
  have h := hsFive_check
  simp only [hsFiveOK, centralizerOK, fiveCentralizerOK, sylowThreeOK, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hS, hSz, hSgen, hva, hpow, hne, hmem, hall⟩ := h
  have hra : Rep 100 a3 (permOfArr 100 a3) := rep_of_validA hva
  obtain ⟨hmemS, hcardS, hvalS⟩ := enumOK_spec keys_lt hS
  have hA3 : (permOfArr 100 a3) ^ 3 = 1 := (eqA_iff (rep_pw hra 3) rep_idA).1 hpow
  have hA1 : permOfArr 100 a3 ≠ 1 := fun h1 => by
    have := (eqA_iff hra rep_idA).2 h1
    rw [this] at hne
    exact absurd hne (by simp)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.closure (permsA 100 sGens), ?_, hcardS.trans hSz, permOfArr 100 a3,
    enumOK_mem_of_any keys_lt hS hra hmem, orderOf_eq_prime hA3 hA1, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (inP_iff (enumOK_gens_valid hS hk)).1 (allLt_spec hSgen hk)
  · intro s hs hs1
    obtain ⟨i, hi, rfl⟩ := (hmemS s).1 hs
    have hrs := rep_of_validA (hvalS i hi)
    have himem : sCert.pts[i]! ∈ sCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have hc := List.all_eq_true.1 hall _ himem
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨c, hcm, ⟨hvc, hPc⟩, hce⟩
    · exact absurd ((eqA_iff hrs rep_idA).1 hc) hs1
    · have hx := (eqA_iff (rep_conjA hvc hra) hrs).1 hce
      exact ⟨permOfArr 100 c, (inP_iff hvc).1 hPc, hx⟩

end Perm

end HSFive

open HSFive CFSG.RankThree.Native CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Model


theorem fiveLocal_model (u' f' : ↥hs100P) (hu2 : orderOf u' = 2)
    (hcu : Nat.card ↥(centralizer ({u'} : Set ↥hs100P)) = 2880)
    (hf : f' ∈ centralizer ({u'} : Set ↥hs100P)) (hf5 : orderOf f' = 5) :
    FiveLocal (⊤ : Subgroup ↥hs100P) u' f' := by
  obtain ⟨hUP, hU2, hUcard⟩ := u0_spec
  obtain ⟨hFmem, hF5, hconj⟩ := f0_spec
  have hFP : F0 ∈ hs100P := (Subgroup.mem_inf.1 hFmem).1
  set U0' : ↥hs100P := ⟨U0, hUP⟩ with hU0'
  set F0' : ↥hs100P := ⟨F0, hFP⟩ with hF0'
  have hY : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have hU0'2 : orderOf U0' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hU2
  have hU0'card : Nat.card ↥(centralizer ({U0'} : Set ↥hs100P)) = 2880 := by
    rw [card_centralizer_subtype_five]
    exact hUcard
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_card_centralizer_eq_hs hY U0' u' hU0'2 hu2
    (hU0'card.trans hcu.symm))
  have hu'c : c⁻¹ * u' * c = U0' := by
    rw [← hc]
    group
  have hf1comm : (c⁻¹ * f' * c) * U0' = U0' * (c⁻¹ * f' * c) := by
    have hff := mem_centralizer_singleton_iff.1 hf
    calc (c⁻¹ * f' * c) * U0' = c⁻¹ * f' * c * (c⁻¹ * u' * c) := by rw [hu'c]
      _ = c⁻¹ * (f' * u') * c := by group
      _ = c⁻¹ * (u' * f') * c := by rw [hff]
      _ = (c⁻¹ * u' * c) * (c⁻¹ * f' * c) := by group
      _ = U0' * (c⁻¹ * f' * c) := by rw [hu'c]
  have hf1ord : orderOf (c⁻¹ * f' * c) = 5 := by
    have := (MulAut.conj c⁻¹).orderOf_eq f'
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hf5]
  obtain ⟨Y, hYmem, hYX⟩ := hconj ((c⁻¹ * f' * c : ↥hs100P) : Equiv.Perm (Fin 100))
    (Subgroup.mem_inf.2 ⟨(c⁻¹ * f' * c).2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hf1comm)⟩)
    (by rw [Subgroup.orderOf_coe]; exact hf1ord)
  have hYP : Y ∈ hs100P := (Subgroup.mem_inf.1 hYmem).1
  have hYU : Y * U0 = U0 * Y := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hYmem).2
  set d : ↥hs100P := ⟨Y, hYP⟩ with hd
  have hdU : d * U0' = U0' * d := Subtype.ext hYU
  have hdf : d * (c⁻¹ * f' * c) * d⁻¹ = F0' := Subtype.ext hYX
  set h : ↥hs100P := c * d⁻¹ with hh
  have hhU : h * U0' * h⁻¹ = u' := by
    have hdU' : d⁻¹ * U0' = U0' * d⁻¹ := by
      calc d⁻¹ * U0' = d⁻¹ * U0' * d * d⁻¹ := by group
        _ = d⁻¹ * (U0' * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * U0') * d⁻¹ := by rw [hdU]
        _ = U0' * d⁻¹ := by group
    calc h * U0' * h⁻¹ = c * (d⁻¹ * U0') * d * c⁻¹ := by rw [hh]; group
      _ = c * (U0' * d⁻¹) * d * c⁻¹ := by rw [hdU']
      _ = c * U0' * c⁻¹ := by group
      _ = u' := hc
  have hhF : h * F0' * h⁻¹ = f' := by
    calc h * F0' * h⁻¹ = c * d⁻¹ * (d * (c⁻¹ * f' * c) * d⁻¹) * d * c⁻¹ := by
          rw [hdf, hh]; group
      _ = f' := by group
  have hc1 : FiveLocal (⊤ : Subgroup ↥hs100P) U0' F0' := by
    have := (fiveLocal_top_iff hs100P.subtype hs100P.subtype_injective U0' F0').2
    rw [Subgroup.range_subtype] at this
    exact this fiveLocal_perm
  have hc2 := FiveLocal.map_equiv (MulAut.conj h) hc1
  rw [MulAut.conj_apply, MulAut.conj_apply, hhU, hhF] at hc2
  exact hc2

end Model

section Final


theorem hs_five_local {G : Type} [Group G] {L : Subgroup G}
    (hL : IsSporadic ↥L .HS) {u f : G}
    (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hcu : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880)
    (hf : f ∈ L ⊓ centralizer ({u} : Set G)) (hf5 : orderOf f = 5) :
    Nat.card ↥(L ⊓ centralizer ({f} : Set G)) = 300 ∧
      ∃ A : Subgroup G, A ≤ L ⊓ centralizer ({f} : Set G) ∧
        Nonempty (↥A ≃* alternatingGroup (Fin 5)) ∧ u ∈ A ∧
        L ⊓ centralizer ({f} : Set G) = zpowers f ⊔ A ∧
        Nat.card ↥(A ⊓ centralizer ({u} : Set G)) = 4 := by
  obtain ⟨e₀⟩ := hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  have hfL : f ∈ L := (Subgroup.mem_inf.1 hf).1
  set u₁ : ↥L := ⟨u, hu⟩ with hu₁
  set f₁ : ↥L := ⟨f, hfL⟩ with hf₁
  have hu₁2 : orderOf u₁ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu2
  have hf₁5 : orderOf f₁ = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hf5
  have hcu₁ : Nat.card ↥(centralizer ({u₁} : Set ↥L)) = 2880 := by
    rw [card_centralizer_subtype_five]
    exact hcu
  have hf₁c : f₁ ∈ centralizer ({u₁} : Set ↥L) :=
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 hf).2))
  have hmodel := fiveLocal_model (σ u₁) (σ f₁) ((σ.orderOf_eq u₁).trans hu₁2)
    ((card_centralizer_equiv σ u₁).trans hcu₁)
    (mem_centralizer_singleton_iff.2 (by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hf₁c]))
    ((σ.orderOf_eq f₁).trans hf₁5)
  have h1 := FiveLocal.map_equiv σ.symm hmodel
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  have h2 := (fiveLocal_top_iff L.subtype L.subtype_injective u₁ f₁).1 h1
  rw [Subgroup.range_subtype] at h2
  exact h2

theorem hs_five_local_of_commutator {G : Type} [Group G] {L : Subgroup G}
    (hL : IsSporadic ↥L .HS) {u f : G} (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hcu : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880)
    (hf : f ∈ ⁅L ⊓ centralizer ({u} : Set G), L ⊓ centralizer ({u} : Set G)⁆)
    (hf5 : orderOf f = 5) :
    Nat.card ↥(L ⊓ centralizer ({f} : Set G)) = 300 ∧
      ∃ A : Subgroup G, A ≤ L ⊓ centralizer ({f} : Set G) ∧
        Nonempty (↥A ≃* alternatingGroup (Fin 5)) ∧ u ∈ A ∧
        L ⊓ centralizer ({f} : Set G) = zpowers f ⊔ A ∧
        Nat.card ↥(A ⊓ centralizer ({u} : Set G)) = 4 :=
  hs_five_local hL hu hu2 hcu
    (Subgroup.commutator_le.2 (fun a ha b hb => by
      rw [commutatorElement_def]
      exact (L ⊓ centralizer ({u} : Set G)).mul_mem
        ((L ⊓ centralizer ({u} : Set G)).mul_mem
          ((L ⊓ centralizer ({u} : Set G)).mul_mem ha hb)
          ((L ⊓ centralizer ({u} : Set G)).inv_mem ha))
        ((L ⊓ centralizer ({u} : Set G)).inv_mem hb)) hf) hf5

theorem hs_three_conj {G : Type} [Group G] {L : Subgroup G}
    (hL : IsSporadic ↥L .HS) {a b : G}
    (ha : a ∈ L) (hb : b ∈ L) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    ∃ l ∈ L, l * a * l⁻¹ = b := by
  obtain ⟨e₀⟩ := hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  obtain ⟨T, hTP, hT9, t, htT, ht3, hTconj⟩ := three_spec
  have hordA : orderOf (σ ⟨a, ha⟩) = 3 := by
    rw [σ.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ha3
  have hordB : orderOf (σ ⟨b, hb⟩) = 3 := by
    rw [σ.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hb3
  have hT' : Nat.card ↥(T.subgroupOf hs100P) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv).trans hT9
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_orderOf_eq_three card_hs100P hT'
    (t := (⟨t, hTP htT⟩ : ↥hs100P)) (fun s hs hs1 => by
      obtain ⟨c, hcP, hct⟩ := hTconj (s : Equiv.Perm (Fin 100)) hs (fun h1 => hs1 (Subtype.ext h1))
      exact isConj_iff.2 ⟨⟨c, hcP⟩, Subtype.ext hct⟩) hordA hordB)
  refine ⟨((σ.symm c : ↥L) : G), (σ.symm c).2, ?_⟩
  have := congrArg (fun x => ((σ.symm x : ↥L) : G)) hc
  simpa using this

end Final

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
