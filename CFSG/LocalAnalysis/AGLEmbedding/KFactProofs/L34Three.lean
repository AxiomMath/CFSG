module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.RankThree.PartOne.KS.ModelR
public import Certificates.Certificate19767
public import Certificates.Certificate19768

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.Assembly.LowTwoRank

theorem nonempty_equiv_S_of_index {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {K : Type} [Group K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (K ≃* S) := by
  obtain ⟨q, hq2, hqe, hd'⟩ := hd
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd'
  subst hd'
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : StatedClassicalModel K .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  rw [hq2, hqe] at hm
  exact exact_model.2.2.2.1 K hm

theorem autModel_S_R :
    CFSG.Sporadic.SmallOddCore.AutModel S R := by
  obtain ⟨e, he, -⟩ := full_automorphism_action
  exact CFSG.RankThree.PartOne.autModel_of_conj_equiv S_le_R S_normal e he

theorem exists_embedding_l34 {X : Type} [Group X] {K : Subgroup X}
    [K.Normal] (hC : Subgroup.centralizer (K : Set X) = ⊥) (θ : K ≃* S) :
    ∃ ι : X →* Equiv.Perm (Fin 42), Function.Injective ι ∧
      (∀ k : K, ι k = (θ k : Equiv.Perm (Fin 42))) ∧ ι.range ≤ R := by
  have hmodel := autModel_S_R
  refine ⟨hmodel.embed K θ, hmodel.embed_injective K θ hC, hmodel.embed_coe K θ, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hmodel.embed_mem K θ x

section Frattini

variable {X : Type*} [Group X] [Finite X]

theorem maximal_normalizer_of_normal {K : Subgroup X} [K.Normal] {p : ℕ} [Fact p.Prime]
    (A : Subgroup X) (hAK : A ≤ K) (hsyl : Nat.card A = p ^ (Nat.card K).factorization p)
    (hmax : ∀ Y' : Subgroup K, Subgroup.normalizer ((A.subgroupOf K : Subgroup K) : Set K) ≤ Y' →
      Y' = Subgroup.normalizer ((A.subgroupOf K : Subgroup K) : Set K) ∨ Y' = ⊤) :
    ∀ Y : Subgroup X, Subgroup.normalizer (A : Set X) ≤ Y →
      Y = Subgroup.normalizer (A : Set X) ∨ Y = ⊤ := by
  intro Y hY
  let P : Sylow p K := Sylow.ofCard (A.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hsyl)
  have hfr : Subgroup.normalizer (A : Set X) ⊔ K = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top P
    have hP : ((P : Subgroup K).map K.subtype : Subgroup X) = A :=
      Subgroup.map_subgroupOf_eq_of_le hAK
    rwa [hP] at h
  have hdec : ∀ x : X, ∃ n ∈ Subgroup.normalizer (A : Set X), ∃ k ∈ K, n * k = x := by
    intro x
    exact Subgroup.mem_sup_of_normal_right.1 (hfr ▸ Subgroup.mem_top x)
  have hnorm : Subgroup.normalizer ((A.subgroupOf K : Subgroup K) : Set K) =
      (Subgroup.normalizer (A : Set X)).subgroupOf K :=
    (Subgroup.subgroupOf_normalizer_eq hAK).symm
  rcases hmax (Y.subgroupOf K) (by
      rw [hnorm]
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hY (Subgroup.mem_subgroupOf.1 hx))) with h | h
  · left
    refine le_antisymm (fun y hy => ?_) hY
    obtain ⟨n, hn, k, hk, rfl⟩ := hdec y
    have hkY : k ∈ Y := by
      have : n⁻¹ * (n * k) ∈ Y := Y.mul_mem (Y.inv_mem (hY hn)) hy
      simpa using this
    have hkN : k ∈ Subgroup.normalizer (A : Set X) := by
      have h1 : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.2 hkY
      rw [h, hnorm] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    exact (Subgroup.normalizer (A : Set X)).mul_mem hn hkN
  · right
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨n, hn, k, hk, rfl⟩ := hdec x
    have hkY : k ∈ Y := by
      have : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    exact Y.mul_mem (hY hn) hkY

end Frattini

theorem S_closure_eq : Subgroup.closure {g | g ∈ [g₁, g₂, g₃]} = S := by
  unfold S
  congr 1
  ext g
  simp

theorem l34InnerData_hS : ∀ j, TabRep (Certificates.MaxD2Perm.l34InnerData.gT.getD j (idTab 42))
    ([g₁, g₂, g₃].getD j 1) :=
  rep_getD_of_forall (L := [g₁T, g₂T, g₃T]) (P := [g₁, g₂, g₃]) rfl (by
    intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact tabRep_g₁
    · exact tabRep_g₂
    · exact tabRep_g₃)

theorem l34_inner_check :
    Certificates.MaxD2Perm.check Certificates.MaxD2Perm.l34InnerData = true :=
  Certificates.certificate19767

theorem l34_inner_localData :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 42)), LocalData 3 2 2 6 S R₀ := by
  have h := localData_of_check (S := [g₁, g₂, g₃]) (D := Certificates.MaxD2Perm.l34InnerData) rfl
    (by show Nat.Prime 3; norm_num) l34InnerData_hS
    (by
      have h1 : [g₁, g₂, g₃].length = 3 := rfl
      have h2 : Certificates.MaxD2Perm.l34InnerData.gT.size = 3 := rfl
      rw [h1, h2])
    (by rw [S_closure_eq]; exact card_S)
    ⟨3, 0, by show (72 : ℕ) = 3 ^ 2 * (2 ^ 3 * 3 ^ 0); norm_num⟩ l34_inner_check
  rwa [S_closure_eq] at h

theorem kFactL34Inner :
    KFactL34Inner := by
  intro d hd X _ _ K hKn hC ⟨e⟩ A hAe hA9 hAK Y hY
  have hlam : orderOf ((2 : ℕ) : ZMod 3) = 3 - 1 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd e
  obtain ⟨R₀, hR₀⟩ := l34_inner_localData
  have hT := torusLocal_of_localData hR₀ (le_refl 2) hlam (by norm_num)
  have hfS : (Nat.card S).factorization 3 = 2 := by
    rw [card_S]
    exact factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hcardK : Nat.card K = 20160 := by
    rw [Nat.card_congr θ.toEquiv, card_S]
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [hcardK]
    exact factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hT' := torusLocal_sylow θ hT (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1, hfS])
    (Sylow.ofCard (A.subgroupOf K) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9, hfK]))
  exact maximal_normalizer_of_normal A hAK (by rw [hA9, hfK]) hT'.2.1 Y hY

theorem kFactL34NormalizerSolvable :
    KFactL34NormalizerSolvable := by
  intro d hd K _ _ ⟨e⟩ A hA9
  have hlam : orderOf ((2 : ℕ) : ZMod 3) = 3 - 1 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd e
  obtain ⟨R₀, hR₀⟩ := l34_inner_localData
  have hT := torusLocal_of_localData hR₀ (le_refl 2) hlam (by norm_num)
  have hfS : (Nat.card S).factorization 3 = 2 := by
    rw [card_S]
    exact factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hcardK : Nat.card K = 20160 := by
    rw [Nat.card_congr θ.toEquiv, card_S]
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [hcardK]
    exact factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hT' := torusLocal_sylow θ hT (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1, hfS])
    (Sylow.ofCard A (by rw [hA9, hfK]))
  exact hT'.2.2.2.1

section OuterModel

open CFSG.AGLEmbedding.L34Outer
open Certificates.L34Outer (Data EData)

theorem exists_pair_closure {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hcard : Nat.card A = 9) (h3 : ∀ x ∈ A, x ^ 3 = 1) :
    ∃ x ∈ A, ∃ y ∈ A, Subgroup.closure {x, y} = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hord : orderOf x = 3 := orderOf_eq_prime (h3 x hx) hx1'
  have hxA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 hx
  have hne : ¬ A ≤ Subgroup.zpowers x := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, hcard] at this
    omega
  obtain ⟨y, hy, hyx⟩ := IsConcreteLE.not_le_iff_exists.1 hne
  refine ⟨x, hx, y, hy, ?_⟩
  have hH : Subgroup.closure {x, y} ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hxH : Subgroup.zpowers x ≤ Subgroup.closure {x, y} :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hyH : y ∈ Subgroup.closure {x, y} := Subgroup.subset_closure (by simp)
  have hd1 : 3 ∣ Nat.card (Subgroup.closure {x, y}) := by
    have := Subgroup.card_dvd_of_le hxH
    rwa [Nat.card_zpowers, hord] at this
  have hd2 : Nat.card (Subgroup.closure {x, y}) ∣ 9 := hcard ▸ Subgroup.card_dvd_of_le hH
  have h9 : Nat.card (Subgroup.closure {x, y}) = 9 := by
    have : Nat.card (Subgroup.closure {x, y}) ∈ Nat.divisors 9 := by simpa using hd2
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at hd1
      omega
    · exfalso
      have heq : Subgroup.zpowers x = Subgroup.closure {x, y} :=
        Subgroup.eq_of_le_of_card_ge hxH (by rw [h, Nat.card_zpowers, hord])
      exact hyx (heq ▸ hyH)
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hH (by rw [h9, hcard])

theorem T_le_of_not_le_S (hT : Nat.card L34T = 60480)
    (hO : ∀ r ∈ R, r ^ 3 = 1 → r ∈ L34T) {B : Subgroup (Equiv.Perm (Fin 42))} (hSB : S ≤ B)
    (hBR : B ≤ R) {a : Equiv.Perm (Fin 42)} (haB : a ∈ B) (ha3 : a ^ 3 = 1) (haS : a ∉ S) :
    L34T ≤ B := by
  have haT : a ∈ L34T := hO a (hBR haB) ha3
  set H : Subgroup (Equiv.Perm (Fin 42)) := S ⊔ Subgroup.zpowers a with hH
  have hHT : H ≤ L34T := sup_le S_le_T (Subgroup.zpowers_le.2 haT)
  have hHB : H ≤ B := sup_le hSB (Subgroup.zpowers_le.2 haB)
  have hd1 : Nat.card S ∣ Nat.card H := Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card H ∣ Nat.card L34T := Subgroup.card_dvd_of_le hHT
  obtain ⟨k, hk⟩ := hd1
  rw [hk, hT, card_S] at hd2
  have hk3 : k ∣ 3 := by
    have : 20160 * k ∣ 20160 * 3 := by simpa using hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hHeq : H = L34T := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with rfl | rfl
    · exfalso
      have heq : S = H := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, card_S, mul_one])
      exact haS (heq ▸ (le_sup_right : Subgroup.zpowers a ≤ H) (Subgroup.mem_zpowers a))
    · exact Subgroup.eq_of_le_of_card_ge hHT (by rw [hk, hT, card_S])
  exact hHeq ▸ hHB

theorem mem_normalizer_zpowers_conj {G : Type*} [Group G] [Finite G] {h y c : G}
    (hn : h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    c * h * c⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (c * y * c⁻¹) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn'
  have h1 : h * y ^ k * h⁻¹ ∈ Subgroup.zpowers y :=
    (Subgroup.mem_normalizer_iff.1 hn (y ^ k)).1 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
  refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
  rw [conj_zpow, conj_zpow]
  calc c * y ^ j * c⁻¹ = c * (h * y ^ k * h⁻¹) * c⁻¹ := by rw [hj]
    _ = c * h * c⁻¹ * (c * y ^ k * c⁻¹) * (c * h * c⁻¹)⁻¹ := by group

theorem exists_conj_le_P {P : Subgroup (Equiv.Perm (Fin 42))} (hPT : P ≤ L34T)
    (hPcard : Nat.card P = 27) (hT : Nat.card L34T = 60480)
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAT : A ≤ L34T) (hA3 : ∀ x ∈ A, x ^ 3 = 1) :
    ∃ c ∈ L34T, ∀ x ∈ A, c⁻¹ * x * c ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfT : (Nat.card L34T).factorization 3 = 3 := by
    rw [hT]
    exact factorization_eq_of_pow_dvd Nat.prime_three (k := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have hp : IsPGroup 3 (A.subgroupOf L34T) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hA3 _ (Subgroup.mem_subgroupOf.1 x.2)⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  let PT : Sylow 3 L34T := Sylow.ofCard (P.subgroupOf L34T) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv, hPcard, hfT]
    norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L34T PT Q
  have hQg : (Q : Subgroup L34T) = (PT : Subgroup L34T).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hmem : (⟨x, hAT hx⟩ : L34T) ∈ (Q : Subgroup L34T) := hQ (Subgroup.mem_subgroupOf.2 hx)
  rw [hQg] at hmem
  obtain ⟨p, hp, hpx⟩ := hmem
  have h1 : (g : Equiv.Perm (Fin 42)) * p * (g : Equiv.Perm (Fin 42))⁻¹ = x :=
    congrArg Subtype.val hpx
  have h2 : (g : Equiv.Perm (Fin 42))⁻¹ * x * g = p := by
    rw [← h1]
    group
  rw [h2]
  exact Subgroup.mem_subgroupOf.1 hp

theorem exhibit_B {D : Data} (facts : OuterFacts D) {e : EData} (he : e ∈ D.es)
    (hS : e.inS = false) {B : Subgroup (Equiv.Perm (Fin 42))} (hTB : L34T ≤ B) (hBR : B ≤ R) :
    ∃ H : Set (Equiv.Perm (Fin 42)),
      (∀ h ∈ H, h ∈ B ∧ ∃ y ∈ Esub e, y ≠ 1 ∧
        h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (Equiv.Perm (Fin 42)))) ∧
      B ≤ Subgroup.closure H := by
  obtain ⟨L, hL, hLT⟩ := facts.exhibit e he hS
  obtain ⟨X, hX, hcov⟩ := facts.extras
  refine ⟨{h | h ∈ L} ∪ {x | x ∈ X ∧ x ∈ B}, ?_, ?_⟩
  · rintro h (hh | ⟨hx, hxB⟩)
    · obtain ⟨hhT, y, hy, hy1, hn⟩ := hL h hh
      exact ⟨hTB hhT, y, hy, hy1, hn⟩
    · exact ⟨hxB, zel D, facts.z_mem e he, facts.z_ne, (hX h hx).2⟩
  · intro b hb
    have hTle : L34T ≤ Subgroup.closure ({h | h ∈ L} ∪ {x | x ∈ X ∧ x ∈ B}) := by
      rw [← hLT]
      exact Subgroup.closure_mono Set.subset_union_left
    rcases hcov b (hBR hb) with hbT | ⟨x, hx, hxb⟩
    · exact hTle hbT
    · have hxB : x ∈ B := by
        have : x = b * (x⁻¹ * b)⁻¹ := by group
        rw [this]
        exact B.mul_mem hb (B.inv_mem (hTB hxb))
      have hxH : x ∈ Subgroup.closure ({h | h ∈ L} ∪ {x | x ∈ X ∧ x ∈ B}) :=
        Subgroup.subset_closure (Or.inr ⟨hx, hxB⟩)
      have : b = x * (x⁻¹ * b) := by group
      rw [this]
      exact Subgroup.mul_mem _ hxH (hTle hxb)

theorem outer_model {D : Data} (facts : OuterFacts D)
    {B A : Subgroup (Equiv.Perm (Fin 42))} (hSB : S ≤ B) (hBR : B ≤ R) (hAB : A ≤ B)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hA9 : Nat.card A = 9) (hAS : ¬ A ≤ S) :
    ∃ H : Set (Equiv.Perm (Fin 42)),
      (∀ h ∈ H, h ∈ B ∧ ∃ y ∈ A, y ≠ 1 ∧
        h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (Equiv.Perm (Fin 42)))) ∧
      B ≤ Subgroup.closure H := by
  obtain ⟨a, haA, haS⟩ := IsConcreteLE.not_le_iff_exists.1 hAS
  have hTB : L34T ≤ B := T_le_of_not_le_S facts.cardT facts.order3 hSB hBR (hAB haA)
    (hA3 a haA) haS
  have hAT : A ≤ L34T := fun x hx => facts.order3 x (hBR (hAB hx)) (hA3 x hx)
  obtain ⟨c, hcT, hc⟩ := exists_conj_le_P facts.P_le_T facts.cardP facts.cardT hAT hA3
  let A' : Subgroup (Equiv.Perm (Fin 42)) := A.map (MulAut.conj c⁻¹).toMonoidHom
  have hmemA' : ∀ y, y ∈ A' ↔ ∃ x ∈ A, c⁻¹ * x * c = y := by
    intro y
    simp only [A', Subgroup.mem_map]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    simp
  have hA'P : A' ≤ Psub D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemA' y).1 hy
    exact hc x hx
  have hA'card : Nat.card A' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hA9]
  have hA'3 : ∀ y ∈ A', y ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemA' y).1 hy
    have h := conj_pow (a := c⁻¹) (b := x) (i := 3)
    simp only [inv_inv] at h
    rw [h, hA3 x hx]
    group
  have hSn : ∀ s ∈ S, c * s * c⁻¹ ∈ S := fun s hs => by
    have := S_normal.conj_mem ⟨s, S_le_R hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨c, T_le_R hcT⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hA'S : ¬ A' ≤ S := by
    intro hle
    apply hAS
    intro x hx
    have h1 : c⁻¹ * x * c ∈ S := hle ((hmemA' _).2 ⟨x, hx, rfl⟩)
    have h2 := hSn _ h1
    have : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [this] at h2
  obtain ⟨u, hu, v, hv, huv⟩ := exists_pair_closure hA'card hA'3
  obtain ⟨e, he, hAe⟩ := facts.pairs u (hA'P hu) v (hA'P hv) (by rw [huv, hA'card])
  have hinS : e.inS = false := by
    by_contra hne
    have hS' : e.inS = true := by simpa using hne
    exact hA'S (huv ▸ hAe ▸ facts.inS e he hS')
  obtain ⟨H', hH', hBH'⟩ := exhibit_B facts he hinS hTB hBR
  refine ⟨(fun h => c * h * c⁻¹) '' H', ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨hhB, y, hy, hy1, hn⟩ := hH' h hh
    have hy' : y ∈ A' := huv ▸ hAe ▸ hy
    obtain ⟨x, hx, hxy⟩ := (hmemA' y).1 hy'
    refine ⟨B.mul_mem (B.mul_mem (hTB hcT) hhB) (B.inv_mem (hTB hcT)), x, hx, ?_, ?_⟩
    · intro h1
      apply hy1
      rw [← hxy, h1]
      group
    · have := mem_normalizer_zpowers_conj (c := c) hn
      rwa [← hxy, show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
  · intro b hb
    have hb' : c⁻¹ * b * c ∈ B := B.mul_mem (B.mul_mem (B.inv_mem (hTB hcT)) hb) (hTB hcT)
    have h1 := hBH' hb'
    have h2 : c * (c⁻¹ * b * c) * c⁻¹ ∈ (Subgroup.closure H').map (MulAut.conj c).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    rw [MonoidHom.map_closure, show c * (c⁻¹ * b * c) * c⁻¹ = b by group] at h2
    have himg : (MulAut.conj c).toMonoidHom '' H' = (fun h => c * h * c⁻¹) '' H' := by
      ext z
      simp [MulAut.conj_apply]
    rwa [himg] at h2

end OuterModel

theorem one_le_pRank_zpowers {G : Type*} [Group G] [Finite G] {y : G} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hmem : (1 : ℕ) ∈ {k | ∃ E : Subgroup G, E ≤ Subgroup.zpowers y ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨Subgroup.zpowers y, le_rfl, hE, by rw [Nat.card_zpowers, hord]; norm_num⟩
  refine le_csSup ⟨Nat.card G, ?_⟩ hmem
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem l34_outer_check :
    CFSG.AGLEmbedding.L34Outer.OuterFacts Certificates.L34Outer.l34OuterData :=
  Certificates.certificate19768

theorem kFactL34Outer :
    KFactL34Outer := by
  intro d hd X _ _ K hKn hC ⟨e⟩ A hAe hA9 hAK
  have : K.Normal := hKn
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd e
  obtain ⟨ι, hinj, hιK, hιR⟩ := exists_embedding_l34 hC θ
  have facts := l34_outer_check
  have hSB : S ≤ ι.range := fun s hs => ⟨(θ.symm ⟨s, hs⟩ : K), by
    rw [hιK, MulEquiv.apply_symm_apply]⟩
  have hA'3 : ∀ x ∈ A.map ι, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAe.2 a ha, map_one]
  have hA'9 : Nat.card (A.map ι) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, hA9]
    norm_num
  have hA'S : ¬ A.map ι ≤ S := by
    intro hle
    apply hAK
    intro a ha
    have h1 : ι a ∈ S := hle ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := θ.surjective ⟨ι a, h1⟩
    have : ι k = ι a := by rw [hιK]; exact congrArg Subtype.val hk
    exact (hinj this) ▸ k.2
  obtain ⟨H, hH, hBH⟩ := outer_model facts hSB hιR
    (Subgroup.map_le_range ι A) hA'3 hA'9 hA'S
  refine eq_top_iff.2 fun x _ => ?_
  have hgen : ∀ h ∈ H, h ∈ (CFSG.Open.GLBCore 3 1 A).map ι := by
    intro h hh
    obtain ⟨hhB, y', hy', hy1', hn⟩ := hH h hh
    obtain ⟨xh, hxh⟩ := hhB
    obtain ⟨y, hyA, rfl⟩ := hy'
    have hy1 : y ≠ 1 := fun h1 => hy1' (by rw [h1, map_one])
    have hy3 : y ^ 3 = 1 := hAe.2 y hyA
    have hxn : xh ∈ Subgroup.normalizer (Subgroup.zpowers y : Set X) := by
      apply Subgroup.mem_normalizer_fintype
      intro n hn'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn'
      have h1 : ι (xh * y ^ k * xh⁻¹) ∈ Subgroup.zpowers (ι y) := by
        rw [map_mul, map_mul, map_inv, map_zpow, hxh]
        exact (Subgroup.mem_normalizer_iff.1 hn (ι y ^ k)).1
          (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
      refine Subgroup.mem_zpowers_iff.2 ⟨j, hinj ?_⟩
      rw [map_zpow, hj]
    have hrank := one_le_pRank_zpowers hy3 hy1
    have hle : Subgroup.normalizer (Subgroup.zpowers y : Set X) ≤ CFSG.Open.GLBCore 3 1 A :=
      le_sSup ⟨Subgroup.zpowers y, Subgroup.zpowers_le.2 hyA, hrank, rfl⟩
    exact ⟨xh, hle hxn, hxh⟩
  have hx : ι x ∈ (CFSG.Open.GLBCore 3 1 A).map ι :=
    ((Subgroup.closure_le _).2 hgen) (hBH ⟨x, rfl⟩)
  obtain ⟨x', hx', hxx'⟩ := hx
  exact (hinj hxx') ▸ hx'

end CFSG.AGLEmbeddingD2
