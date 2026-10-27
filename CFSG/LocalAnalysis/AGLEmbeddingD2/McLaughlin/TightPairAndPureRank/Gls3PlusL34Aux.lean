module

public import CFSG.RankThree.PartOne.SP4GA.Unique
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusGLB

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section Plane

variable {X : Type} [Group X] [Finite X]

theorem zpowers_eq_of_mem_of_orderOf {y z : X} (hy : orderOf y = 3) (hz : z ∈ Subgroup.zpowers y)
    (hz1 : z ≠ 1) : Subgroup.zpowers z = Subgroup.zpowers y := by
  have hzo : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := hy ▸ orderOf_dvd_of_mem_zpowers hz
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hy, hzo]

theorem exists_plane_not_le {K P : Subgroup X} (hP : IsPGroup 3 P) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hT : ∃ t ∈ P ⊓ K, t ≠ 1) (hnot : ¬ P ≤ K) :
    ∃ A : Subgroup X, A ≤ P ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 ∧ ¬ A ≤ K := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyP, hyK⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := fun h => hyK (h ▸ one_mem K)
  have hyo : orderOf y = 3 := orderOf_eq_prime (hexp y hyP) hy1
  have hz : ∃ z ∈ P, z ≠ 1 ∧ y * z = z * y ∧ z ∉ Subgroup.zpowers y := by
    have hPnt : Nontrivial ↥P := ⟨⟨⟨y, hyP⟩, 1, fun h => hy1 (congrArg Subtype.val h)⟩⟩
    have hcen := hP.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥P)
    have hc1' : ((c : ↥P) : X) ≠ 1 := by
      intro h
      exact hc1 (Subtype.ext (Subtype.ext h))
    have hcP : ((c : ↥P) : X) ∈ P := (c : ↥P).2
    have hcomm : ∀ x ∈ P, x * ((c : ↥P) : X) = ((c : ↥P) : X) * x := fun x hx =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩)
    by_cases hmem : ((c : ↥P) : X) ∈ Subgroup.zpowers y
    ·
      have heq := zpowers_eq_of_mem_of_orderOf hyo hmem hc1'
      have hyc : y ∈ Subgroup.zpowers ((c : ↥P) : X) := heq ▸ Subgroup.mem_zpowers y
      have hycomm : ∀ x ∈ P, y * x = x * y := by
        intro x hx
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyc
        rw [← hi]
        exact ((Commute.zpow_right (show Commute x ((c : ↥P) : X) from hcomm x hx) i).eq).symm
      obtain ⟨t, htPK, ht1⟩ := hT
      refine ⟨t, htPK.1, ht1, hycomm t htPK.1, fun hty => ?_⟩
      have heq' := zpowers_eq_of_mem_of_orderOf hyo hty ht1
      have : y ∈ Subgroup.zpowers t := heq' ▸ Subgroup.mem_zpowers y
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp this
      apply hyK
      rw [← hi]
      exact Subgroup.zpow_mem K htPK.2 i
    · exact ⟨_, hcP, hc1', hcomm y hyP, hmem⟩
  obtain ⟨z, hzP, hz1, hyz, hzy⟩ := hz
  have hzo : orderOf z = 3 := orderOf_eq_prime (hexp z hzP) hz1
  have hS : ({y, z} : Set X) ⊆ P := by
    intro w hw
    rcases hw with rfl | rfl
    · exact hyP
    · exact hzP
  have hA : Subgroup.closure ({y, z} : Set X) = Subgroup.zpowers y ⊔ Subgroup.zpowers z := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  refine ⟨Subgroup.closure ({y, z} : Set X), (Subgroup.closure_le P).2 hS, ?_, ?_, ?_⟩
  · refine CFSG.AGLEmbedding.isElemAbelian_closure ?_ ?_
    · intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hyz
      · exact hyz.symm
      · rfl
    · intro a ha
      rcases ha with rfl | rfl
      · exact hexp _ hyP
      · exact hexp _ hzP
  · rw [hA]
    have hinf : Subgroup.zpowers y ⊓ Subgroup.zpowers z = ⊥ := by
      by_contra hne
      obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hwy : (w : X) ∈ Subgroup.zpowers y := w.2.1
      have hwz : (w : X) ∈ Subgroup.zpowers z := w.2.2
      have hw1 : (w : X) ≠ 1 := fun h => hw (Subtype.ext h)
      have h1 := zpowers_eq_of_mem_of_orderOf hyo hwy hw1
      have h2 := zpowers_eq_of_mem_of_orderOf hzo hwz hw1
      exact hzy (by
        have : z ∈ Subgroup.zpowers (w : X) := h2.symm ▸ Subgroup.mem_zpowers z
        rwa [h1] at this)
    rw [CFSG.RankThree.PartOne.SP4GA.card_sup_zpowers hyz hinf, hyo, hzo]
    norm_num
  · intro hle
    exact hyK (hle (Subgroup.subset_closure (by simp)))

end Plane

section Gamma

variable {X : Type} [Group X] [Finite X]

theorem gammaCore_eq_top_of_glbCore_le {A P : Subgroup X} (hAP : A ≤ P)
    (h : CFSG.Open.GLBCore 3 1 A = ⊤) : gammaCore 3 1 ⊤ P = ⊤ := by
  have hle : CFSG.Open.GLBCore 3 1 A ≤ gammaCore 3 1 ⊤ P := by
    unfold CFSG.Open.GLBCore
    refine sSup_le ?_
    rintro N ⟨Q, hQA, hrk, rfl⟩ x hx
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, Q, hQA.trans hAP, hrk, hx⟩
  rw [h] at hle
  exact top_le_iff.mp hle

theorem gammaCore_eq_map_normalizer {K : Subgroup X} (T : Subgroup K)
    (hti : ∀ t ∈ T, t ≠ 1 → ∀ y : K, y⁻¹ * t * y ∈ T → y ∈ Subgroup.normalizer (T : Set K))
    (hdvd : 3 ∣ Nat.card T) :
    gammaCore 3 1 K (T.map K.subtype) = (Subgroup.normalizer (T : Set K)).map K.subtype := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · rw [gammaCore, Subgroup.closure_le]
    rintro x ⟨hxK, R, hRQ, hrk, hxR⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have hR : R ≠ ⊥ := by
      rintro rfl
      have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup X) ≤ 0 := by
        refine csSup_le' ?_
        rintro k ⟨E, hE, -, hcard⟩
        rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
        by_contra hk
        have : 1 < 3 ^ k := Nat.one_lt_pow (by omega) (by norm_num)
        omega
      omega
    obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    obtain ⟨t, ht, htr⟩ := hRQ r.2
    have hxr : x * (r : X) * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR r).mp r.2
    obtain ⟨t', ht', ht'r⟩ := hRQ hxr
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hr (Subtype.ext (by simpa using htr.symm))
    have hconj : (⟨x, hxK⟩ : K) * t * (⟨x, hxK⟩ : K)⁻¹ = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (t : X) = r from htr, show (t' : X) = x * r * x⁻¹ from ht'r]
    have hmem : ((⟨x, hxK⟩ : K)⁻¹)⁻¹ * t * (⟨x, hxK⟩ : K)⁻¹ ∈ T := by
      rw [inv_inv, hconj]; exact ht'
    have := hti t ht ht1 _ hmem
    simpa using Subgroup.inv_mem _ this
  · rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.subset_closure ⟨k.2, T.map K.subtype, le_rfl, ?_, ?_⟩
    · have h1 := KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd Nat.prime_three
        (T := T) hdvd
      exact h1.trans (pRank_le_pRank_map (by norm_num) K.subtype K.subtype_injective T)
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨t, ht, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp hk t).mp ht
        exact ⟨k * t * k⁻¹, this, rfl⟩
      · rintro ⟨t', ht', hh⟩
        have hk' : k⁻¹ ∈ Subgroup.normalizer (T : Set K) := Subgroup.inv_mem _ hk
        have := (Subgroup.mem_normalizer_iff.mp hk' t').mp ht'
        refine ⟨k⁻¹ * t' * k, ?_, ?_⟩
        · simpa using this
        · have h1 : (t' : X) = (k : X) * h * (k : X)⁻¹ := by
            exact hh
          calc ((k⁻¹ * t' * k : K) : X) = (k : X)⁻¹ * (t' : X) * (k : X) := rfl
            _ = h := by rw [h1]; group

theorem mem_normalizer_of_conj_mem_of_ti {G : Type*} [Group G] {T : Subgroup G}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hcent : ∀ t ∈ T, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ T) [Finite G] {x y : G} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hy : y⁻¹ * x * y ∈ T) : y ∈ Subgroup.normalizer (T : Set G) := by
  have hx1' : y⁻¹ * x * y ≠ 1 := by
    intro h1
    apply hx1
    have h2 : y * (y⁻¹ * x * y) * y⁻¹ = y * 1 * y⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2
  have key : ∀ w ∈ T, y⁻¹ * w * y ∈ T := by
    intro w hw
    refine hcent (y⁻¹ * x * y) hy hx1' (y⁻¹ * w * y) ?_
    calc y⁻¹ * w * y * (y⁻¹ * x * y) = y⁻¹ * (w * x) * y := by group
      _ = y⁻¹ * (x * w) * y := by rw [hcomm w hw x hx]
      _ = y⁻¹ * x * y * (y⁻¹ * w * y) := by group
  have hinv : y⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_fintype (fun n hn => by simpa using key n hn)
  simpa using Subgroup.inv_mem _ hinv

end Gamma

section Normal

variable {X : Type} [Group X] {K : Subgroup X} [K.Normal]

theorem coe_mem_normalizer_map_iff (T : Subgroup K) (k : ↥K) :
    (k : X) ∈ Subgroup.normalizer ((T.map K.subtype : Subgroup X) : Set X) ↔
      k ∈ Subgroup.normalizer (T : Set K) := by
  have hQmem : ∀ k : ↥K, (k : X) ∈ T.map K.subtype ↔ k ∈ T := fun k =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hk t
    exact (hQmem t).symm.trans ((hk (t : X)).trans (hQmem (k * t * k⁻¹)))
  · intro hk h
    by_cases hhK : h ∈ K
    · exact (hQmem ⟨h, hhK⟩).trans ((hk ⟨h, hhK⟩).trans (hQmem (k * ⟨h, hhK⟩ * k⁻¹)).symm)
    · have hmapK : T.map K.subtype ≤ K := Subgroup.map_subtype_le T
      have h1 : h ∉ T.map K.subtype := fun hh => hhK (hmapK hh)
      have h2 : (k : X) * h * (k : X)⁻¹ ∉ T.map K.subtype := by
        intro hh
        have hh' : (k : X) * h * (k : X)⁻¹ ∈ K := hmapK hh
        apply hhK
        have := (inferInstance : K.Normal).conj_mem _ hh' (k : X)⁻¹
        have e : (k : X)⁻¹ * ((k : X) * h * (k : X)⁻¹) * ((k : X)⁻¹)⁻¹ = h := by group
        rwa [e] at this
      exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩

theorem inf_normalizer_map_eq (T : Subgroup K) :
    K ⊓ Subgroup.normalizer ((T.map K.subtype : Subgroup X) : Set X) =
      (Subgroup.normalizer (T : Set K)).map K.subtype := by
  ext x
  constructor
  · rintro ⟨hxK, hxN⟩
    exact ⟨⟨x, hxK⟩, (coe_mem_normalizer_map_iff T ⟨x, hxK⟩).mp hxN, rfl⟩
  · intro hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k.2, (coe_mem_normalizer_map_iff T k).mpr hk⟩

end Normal

section Quaternion

open CFSG.RankThree.Asc83Table

theorem nonempty_mulEquiv_quaternion_of_automizer {G : Type*} [Group G] [Finite G]
    {E S : Subgroup G} (hS : S ≤ Subgroup.normalizer (E : Set G)) (hSc : Nat.card S = 8)
    (hEc : Nat.card E = 9) (hcent : ∀ g : G, (∀ x ∈ E, g * x = x * g) → g ∈ E)
    (hQ : Nonempty (Automizer E ≃* QuaternionGroup 2)) : Nonempty (S ≃* QuaternionGroup 2) := by
  obtain ⟨φ⟩ := hQ
  set N := Subgroup.normalizer (E : Set G) with hN
  let f : S →* Automizer E := (QuotientGroup.mk' ((Subgroup.centralizer (E : Set G)).subgroupOf N)).comp
    (Subgroup.inclusion hS)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs' : (Subgroup.inclusion hS s) ∈ (Subgroup.centralizer (E : Set G)).subgroupOf N :=
      (QuotientGroup.eq_one_iff _).mp hs
    have hsC : (s : G) ∈ Subgroup.centralizer (E : Set G) := Subgroup.mem_subgroupOf.mp hs'
    have hsE : (s : G) ∈ E := hcent (s : G) (fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hsC x hx).symm)
    have hbot : S ⊓ E = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hSc, hEc]; norm_num))
    have : (s : G) ∈ S ⊓ E := ⟨s.2, hsE⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hcard : Nat.card (Automizer E) = 8 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hbij : Function.Bijective f := by
    have : Finite (Automizer E) := Finite.of_equiv _ φ.symm.toEquiv
    refine (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, ?_⟩
    rw [hSc, hcard]
  exact ⟨(MulEquiv.ofBijective f hbij).trans φ⟩

end Quaternion

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
