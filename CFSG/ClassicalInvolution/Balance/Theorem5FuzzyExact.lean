module

public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyRigid

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ne_of_card_closure_eq_eight {z : Fin 3 → G} (hsq : ∀ i, z i * z i = 1)
    (hcomm : ∀ i j, z i * z j = z j * z i) (hcard : Nat.card (Subgroup.closure (Set.range z)) = 8)
    {i j : Fin 3} (hij : i ≠ j) : z i ≠ z j := by
  intro hzij
  obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j :=
    (by decide : ∀ i j : Fin 3, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j) i j hij
  have hrange : Set.range z ⊆ ({z i, z k} : Set G) := by
    rintro _ ⟨m, rfl⟩
    have hm : m = i ∨ m = j ∨ m = k :=
      (by decide : ∀ i j k m : Fin 3, i ≠ j → k ≠ i → k ≠ j → m = i ∨ m = j ∨ m = k)
        i j k m hij hki hkj
    rcases hm with rfl | rfl | rfl
    · simp
    · simp [← hzij]
    · simp
  have hle : Subgroup.closure (Set.range z) ≤ Subgroup.closure ({z i, z k} : Set G) :=
    Subgroup.closure_mono hrange
  have h1 := Subgroup.card_le_of_le hle
  have h2 := card_closure_pair_le_four (hsq i) (hsq k) (hcomm i k)
  omega

theorem localOddCentral_of_indepTriple_of_balancedFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A')
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hA : A ∈ 𝒯) {i j : Fin 3} (hij : i ≠ j) {x : G}
    (hx : x ∈ Subgroup.closure ({z i, z j} : Set G)) (hx1 : x ≠ 1) : LocalOddCentral Ω {x} := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hα := alphaCore_eq_bot_of_connected_frames hO hinv hbal hcon
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal A hA)
  exact localOddCentral_of_indepTriple_pair hnab hp2 hq hΩ hIH hex hlay hK hcomm hAdef hel hcard
    hF₀ (hα A hA F₀ hF₀) hij hx hx1

theorem localOddCentral_mul_of_indepTriple_of_balancedFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A')
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hA : A ∈ 𝒯) {i j : Fin 3} (hij : i ≠ j) :
    LocalOddCentral Ω {z i * z j} := by
  have hsq : ∀ m, z m * z m = 1 := fun m => (hK m).2.isCentralInvolution.sq
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hAc : ∀ m n, z m * z n = z n * z m := fun m n =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hzA m⟩ : A) ⟨_, hzA n⟩)
  have hne : z i ≠ z j := ne_of_card_closure_eq_eight hsq hAc (hAdef ▸ hcard) hij
  have h1 : z i * z j ≠ 1 := by
    intro h
    apply hne
    calc z i = z i * (z j * z j) := by rw [hsq j, mul_one]
      _ = (z i * z j) * z j := by rw [mul_assoc]
      _ = z j := by rw [h, one_mul]
  exact localOddCentral_of_indepTriple_of_balancedFamily hnab hp2 hq hΩ hIH hex hlay hbal hinv hcon
    hK hcomm hAdef hel hcard hA hij
    (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) h1


section Exact

theorem commutes_of_fuzzyFrame_of_exact [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω) {J : Fin 3 → Subgroup G}
    {z : Fin 3 → G} (hJ : ∀ i, J i ∈ Ω ∧ IsClassicalMember p f (J i) (z i)) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (htriv : ∀ i, A ≤ trivialOnQuot (J i)) {i j : Fin 3} (hij : i ≠ j)
    {x : G} (hx : x ∈ J i) {y : G} (hy : y ∈ J j) : x * y = y * x := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hsq : ∀ m, z m * z m = 1 := fun m => (hJ m).2.isCentralInvolution.sq
  have hAc : ∀ m n, z m * z n = z n * z m := fun m n =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hzA m⟩ : A) ⟨_, hzA n⟩)
  have hne : ∀ i j, i ≠ j → z i ≠ z j := fun i j hij =>
    ne_of_card_closure_eq_eight hsq hAc (hAdef ▸ hcard) hij
  have hOJ : ∀ m, oddCoreIn (J m) = ⊥ := fun m => by
    have h' : componentClassificationOddCore (J m) = ⊥ := hex _ (hJ m).1
    show (componentClassificationOddCore (J m)).map (J m).subtype = ⊥
    rw [h']
    exact Subgroup.map_bot _
  have hcent : ∀ m n, ∀ x ∈ J m, x * z n = z n * x := by
    intro m n x hx
    have h1 : ⁅z n, x⁆ ∈ oddCoreIn (J m) := (htriv m (hzA n)).2 x hx
    rw [hOJ m, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hJC : ∀ m n, J m ≤ Subgroup.centralizer ({z n} : Set G) := fun m n x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent m n x hx)
  have hnotcommon : ¬ InCommonComponent (z i) (J i) (J j) := by
    rintro ⟨Q, hQ, hiQ, hjQ⟩
    have hopen : IsComponentOf (modOdd (z i) (J i)) ⊤ := isComponentOf_modOdd (hJ i).2 hq
    have hcI : CFSG.IsComponent (modOdd (z i) (J i)) :=
      (CFSG.isComponent_iff_open _).mpr hopen
    have heq : modOdd (z i) (J i) = Q := by
      rcases CFSG.LocalCores.distinct_components_commute hcI hQ with h | h
      · exact h
      · exfalso
        refine not_commutes_self_of_isQuasisimple hopen.2.2 fun u hu v hv => ?_
        have h1 := Subgroup.commutator_mem_commutator hu (hiQ hv)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
    have hzjC : z j ∈ Subgroup.centralizer ({z i} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hAc j i)
    have himg : oddQuotMk (z i) ⟨z j, hzjC⟩ ∈ modOdd (z i) (J i) := by
      rw [heq]
      exact hjQ (oddQuotMk_mem_modOdd (hJ j).2.mem hzjC)
    obtain ⟨k, hkJ, hk⟩ := mem_modOdd_iff.mp himg
    set N : Subgroup G := oddCoreIn (Subgroup.centralizer ({z i} : Set G)) with hN
    have hn : (k : G)⁻¹ * z j ∈ N := by
      have h1 : k⁻¹ * (⟨z j, hzjC⟩ : ↥(Subgroup.centralizer ({z i} : Set G))) ∈
          componentClassificationOddCore ↥(Subgroup.centralizer ({z i} : Set G)) := by
        apply oddQuotMk_eq_one_iff.mp
        rw [map_mul, map_inv, hk, inv_mul_cancel]
      exact ⟨_, h1, rfl⟩
    have hkz : (k : G) * z j = z j * k := hcent i j k hkJ
    set n : G := (k : G)⁻¹ * z j with hndef
    have hzn : (k : G) * n = z j := by rw [hndef]; group
    have hnk : n * k = z j := by
      calc n * k = (k : G)⁻¹ * (z j * k) := by rw [hndef]; group
        _ = (k : G)⁻¹ * (k * z j) := by rw [hkz]
        _ = z j := by group
    have hkn : (k : G) * n = n * k := hzn.trans hnk.symm
    have hkk : (k : G) * k * (n * n) = 1 := by
      calc (k : G) * k * (n * n) = k * (k * n) * n := by group
        _ = k * (n * k) * n := by rw [hkn]
        _ = (k * n) * (k * n) := by group
        _ = z j * z j := by rw [hzn]
        _ = 1 := hsq j
    have hkkN : (k : G) * k ∈ N := by
      rw [eq_inv_of_mul_eq_one_left hkk]
      exact N.inv_mem (N.mul_mem hn hn)
    have hbot := exact_inf_oddCoreIn_eq_bot hex (hJ i).1 (hJC i i)
    have hkk1 : (k : G) * k = 1 := by
      have h3 : (k : G) * k ∈ (J i ⊓ N : Subgroup G) := ⟨(J i).mul_mem hkJ hkJ, hkkN⟩
      rw [hbot, Subgroup.mem_bot] at h3
      exact h3
    have hnn : n * n = 1 := by rwa [hkk1, one_mul] at hkk
    have hn1 : n = 1 := eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _) hn hnn
    have hkzj : (k : G) = z j := by rw [← hzn, hn1, mul_one]
    have hzjJ : z j ∈ J i := hkzj ▸ hkJ
    exact hne i j hij
      ((hJ i).2.eq_of_isCentralInvolution hp2 hf
        ⟨hzjJ, (hJ j).2.isCentralInvolution.ne_one, hsq j, fun x hx => (hcent i j x hx).symm⟩).symm
  have hnc : ¬ ({z i} : Set G) ⊆ Subgroup.center G :=
    not_subset_center_of_ne_one hnab (hJ i).2.ne_one
  have hcommmod := comm_mem_oddCoreIn_of_not_inCommonComponent hp2 hΩ hIH hnc
    ⟨(hJ i).1, hJC i i⟩ ⟨(hJ j).1, hJC j i⟩ hnotcommon
  exact centralizes_of_exact_of_comm_mem_oddCoreIn hq hΩ hex (hJ j).1 (hJC j i) (hJ j).2
    (by rw [hcent i j x hx]; group) (fun y' hy' => hcommmod x hx y' hy') y hy

theorem FuzzyFrameOn.indepTripleOn_of_exact [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω) {A : Subgroup G}
    (h : FuzzyFrameOn p f Ω A) : IndepTripleOn p f Ω A := by
  obtain ⟨J, z, hJ, hAdef, hel, hcard, htriv⟩ := h
  exact ⟨J, z, hJ, fun i j hij x hx y hy =>
    commutes_of_fuzzyFrame_of_exact hnab hp2 hq hΩ hIH hex hJ hAdef hel hcard htriv hij hx hy,
    hAdef, hel, hcard⟩

theorem localOddCentral_mul_of_frameAdj [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    (hbal : ∀ A ∈ fuzzyFrames p f Ω, RankThreeBalance A)
    (hcon : ∀ A ∈ fuzzyFrames p f Ω, ∀ A' ∈ fuzzyFrames p f Ω,
      Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f Ω)) A A') {z w : G} (hzw : z ≠ w)
    (hadj : FrameAdj (fuzzyFrames p f Ω) (fuzzyVertices p f Ω) z w) :
    LocalOddCentral Ω {z * w} := by
  have hinv : ∀ A ∈ fuzzyFrames p f Ω, ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ fuzzyFrames p f Ω := fun A hA g =>
    FuzzyFrameOn.map hΩ.conjInvariant hA g
  obtain ⟨A, hA, ⟨hzA, M, hMΩ, hM, hMtriv⟩, ⟨hwA, N, hNΩ, hN, hNtriv⟩⟩ := hadj
  have hA' : FuzzyFrameOn p f Ω A := hA
  obtain ⟨J, y, hJ, hAdef, hel, hcard, htriv⟩ := hA'
  have hyA : ∀ m, y m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hAc : ∀ {x x' : G}, x ∈ A → x' ∈ A → x * x' = x' * x := fun hx hx' =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hx'⟩)
  have hz2 : z * z = 1 := hM.isCentralInvolution.sq
  have hw2 : w * w = 1 := hN.isCentralInvolution.sq
  have hzw1 := hM.isCentralInvolution.ne_one
  have hw1 := hN.isCentralInvolution.ne_one
  have hc4 : Nat.card (Subgroup.closure ({z, w} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hw2 hzw1 hw1 hzw (hAc hzA hwA)
  obtain ⟨k, hk⟩ : ∃ k, y k ∉ Subgroup.closure ({z, w} : Set G) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hle : A ≤ Subgroup.closure ({z, w} : Set G) := by
      rw [hAdef, Subgroup.closure_le]
      rintro _ ⟨m, rfl⟩
      exact hall m
    have := Subgroup.card_le_of_le hle
    omega
  have hzAw : Subgroup.closure ({z, w} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | hx)
    · exact hzA
    · rw [Set.mem_singleton_iff.mp hx]
      exact hwA
  have hB : Subgroup.closure ({z, w, y k} : Set G) = A := by
    set B : Subgroup G := Subgroup.closure ({z, w, y k} : Set G) with hBdef
    have hBA : B ≤ A := by
      rw [hBdef, Subgroup.closure_le]
      rintro _ (rfl | rfl | hx)
      · exact hzA
      · exact hwA
      · rw [Set.mem_singleton_iff.mp hx]
        exact hyA k
    have hzwB : Subgroup.closure ({z, w} : Set G) ≤ B := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | hx)
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff.mp hx]
        exact Subgroup.subset_closure (by simp)
    have hdvd : 4 ∣ Nat.card B := hc4 ▸ Subgroup.card_dvd_of_le hzwB
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hle8 : Nat.card B ≤ 8 := hcard ▸ Subgroup.card_le_of_le hBA
    have hB8 : Nat.card B = 8 := by
      by_contra hne
      have h4 : Nat.card B = 4 := by omega
      have hFeq : Subgroup.closure ({z, w} : Set G) = B :=
        Subgroup.eq_of_le_of_card_ge hzwB (by rw [h4, hc4])
      exact hk (hFeq ▸ Subgroup.subset_closure (by simp))
    exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hB8, hcard])
  have hrange : Set.range ![z, w, y k] = ({z, w, y k} : Set G) := by
    ext x
    simp
    tauto
  have hK : ∀ m, (![M, N, J k] : Fin 3 → Subgroup G) m ∈ Ω ∧
      IsClassicalMember p f ((![M, N, J k] : Fin 3 → Subgroup G) m) (![z, w, y k] m) := by
    intro m
    fin_cases m
    exacts [⟨hMΩ, hM⟩, ⟨hNΩ, hN⟩, hJ k]
  have hAdef' : A = Subgroup.closure (Set.range ![z, w, y k]) := by rw [hrange, hB]
  have htriv' : ∀ m, A ≤ trivialOnQuot ((![M, N, J k] : Fin 3 → Subgroup G) m) := by
    intro m
    fin_cases m
    exacts [hMtriv, hNtriv, htriv k]
  have hcomm' : ∀ i j, i ≠ j → ∀ x ∈ (![M, N, J k] : Fin 3 → Subgroup G) i,
      ∀ x' ∈ (![M, N, J k] : Fin 3 → Subgroup G) j, x * x' = x' * x := fun i j hij x hx x' hx' =>
    commutes_of_fuzzyFrame_of_exact hnab hp2 hq hΩ hIH hex hK hAdef' hel hcard htriv' hij hx hx'
  have hzwmem : z * w ∈ Subgroup.closure
      ({(![z, w, y k] : Fin 3 → G) 0, (![z, w, y k] : Fin 3 → G) 1} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hzw1' : z * w ≠ 1 := by
    intro h
    apply hzw
    calc z = z * (w * w) := by rw [hw2, mul_one]
      _ = (z * w) * w := by rw [mul_assoc]
      _ = w := by rw [h, one_mul]
  exact localOddCentral_of_indepTriple_of_balancedFamily hnab hp2 hq hΩ hIH hex hlay hbal hinv hcon
    hK hcomm' hAdef' hel hcard hA (i := 0) (j := 1) (by decide) hzwmem hzw1'

end Exact

end CFSG.ClassicalInvolution.Balance.Theorem5
