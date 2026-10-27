module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.Red2Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification CFSG.Goldschmidt.Red2
open CFSG.RankThreeCoreUniqueness.Helpers (pCore_isPGroup pCore_normal pCore_eq_sSup)

private theorem N23_R8 (h17 : S_N17) {G : Type} [Group G] [Finite G] {S : Sylow 2 G}
    {A : Subgroup G} (hA : CoreHyp G S A) (hIH : IH (Nat.card G)) {K : Subgroup G}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hKA : ⁅K, A⁆ ≠ ⊥) (hKtop : K ≠ ⊤)
    (htype : goldschmidtSimpleType (K ⧸ Subgroup.center K)) (hInd : InducesOmega1 A K S) :
    K ⊓ Subgroup.centralizer (K : Set G) ≤ A ∧
      A ⊓ K ≤ CFSG.Open.pCore 2 G ⊔ Omega1 ((S : Subgroup G) ⊓ goldschmidtLayer G) := by
  have hO := hA.oddCore
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hKn.isSubnormal
  set AK : Subgroup K := A.subgroupOf K with hAKdef
  have hAKT : (A ⊓ K).subgroupOf K ≤ T := by
    intro x hx
    have hxS : (x : G) ∈ (S : Subgroup G) ⊓ K :=
      ⟨hA.le (Subgroup.mem_subgroupOf.mp hx).1, x.2⟩
    rw [← hT] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [show y = x from Subtype.ext hyx] at hy
  have hclAK : fusionStronglyClosed (AK : Set K) (T : Subgroup K) := by
    have h := stronglyClosed_subgroupOf S (stronglyClosed_inf_normal hA.closed K) inf_le_right
      T hAKT
    rwa [Subgroup.inf_subgroupOf_right] at h
  rw [Subgroup.inf_subgroupOf_right] at hAKT
  have hAKcomm : IsMulCommutative AK := isMulCommutative_subgroupOf hA.comm K
  have hgen : Subgroup.normalClosure (AK : Set K) = ⊤ := by
    have := Subgroup.normalClosure_normal (s := (AK : Set K))
    rcases Quasisimple.normal_le_center_or_eq_top hK.2.2 (Subgroup.normalClosure (AK : Set K))
      with hc | ht
    · exfalso
      apply hKA
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      obtain ⟨x, hx, hconj⟩ := h17 G S A K hA.le hA.comm hA.closed hO hK htype hInd a ha
      have hxZ : (⟨x, hx.2⟩ : K) ∈ Subgroup.center K :=
        hc (Subgroup.le_normalClosure (show (⟨x, hx.2⟩ : K) ∈ AK from hx.1))
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : k * x = x * k := congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨k, hk⟩)
      have h2 : x⁻¹ * k * x = k := by rw [mul_assoc, h1]; group
      calc k * a = a * (a⁻¹ * k * a) := by group
        _ = a * k := by rw [hconj k hk, h2]
    · exact ht
  have hOK : goldschmidtOddCore K = ⊥ := OddCore.subnormal_corefree hO K hK.2.1
  have hcardK : Nat.card K < Nat.card G := by
    have h1 := K.card_le_card_group
    have h2 : Nat.card K ≠ Nat.card G := fun h => hKtop ((Subgroup.card_eq_iff_eq_top K).mp h)
    omega
  obtain ⟨-, hAeq, -⟩ := hIH K hcardK T AK hAKT hAKcomm hclAK hgen hOK
  have hZK : Subgroup.center K ≤ CFSG.Open.pCore 2 K := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
    exact le_sSup ⟨inferInstance, (N8d G hO).1 K hK⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hzK, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
    have hzA : (⟨z, hzK⟩ : K) ∈ AK := by
      rw [hAeq]
      exact Subgroup.mem_sup_left (hZK hzZ)
    exact hzA
  ·
    have hmap : A ⊓ K = (CFSG.Open.pCore 2 K).map K.subtype ⊔
        (Subgroup.closure {t | t ∈ (T : Subgroup K) ⊓ goldschmidtLayer K ∧ t ^ 2 = 1}).map
          K.subtype := by
      rw [← Subgroup.map_sup, ← hAeq, hAKdef, Subgroup.subgroupOf_map_subtype]
    rw [hmap]
    refine sup_le_sup ?_ ?_
    · rw [CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup, CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
      exact PrimeCore.normal_monotone 2 K
    · rw [MonoidHom.map_closure, Omega1]
      apply Subgroup.closure_mono
      rintro _ ⟨t, ⟨⟨htT, -⟩, ht2⟩, rfl⟩
      have htS : (t : G) ∈ (S : Subgroup G) ⊓ K := by
        rw [← hT]
        exact ⟨t, htT, rfl⟩
      refine ⟨⟨htS.1, Layer.component_le hK t.2⟩, ?_⟩
      have := congrArg Subtype.val ht2
      simpa using this

theorem N23_of (h17 : S_N17) (h19 : S_N19) : S_N23 := by
  intro G _ _ S A hA hIH hnq hcomp hQE hCE
  have hO := hA.oddCore
  set E := goldschmidtLayer G with hEdef
  set Q := CFSG.Open.pCore 2 G with hQdef
  set 𝒦 : Set (Subgroup G) := {K | IsComponentOf K ⊤} with h𝒦def
  have hE𝒦 : E = sSup 𝒦 := rfl
  have hEn : E.Normal := Layer.normal G
  have hQn : Q.Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have hfin : 𝒦.Finite := Set.toFinite 𝒦
  have hcomm : ∀ K ∈ 𝒦, ∀ L ∈ 𝒦, K ≠ L → K ≤ Subgroup.centralizer (L : Set G) :=
    fun K hK L hL hne => component_le_centralizer hK hL hne
  have h19' := fun K (hK : K ∈ 𝒦) => h19 G S A hA.le hA.comm hA.closed hA.gen K hK
  have hnorm : ∀ K ∈ 𝒦, K.Normal := fun K hK => (h19' K hK).1
  have hR8 := fun K (hK : K ∈ 𝒦) => N23_R8 h17 hA hIH hK (hnorm K hK) (h19' K hK).2
    (fun h => hnq (by subst h; exact hK)) (hcomp K hK).1 (hcomp K hK).2
  have hd := N8d G hO
  have h17' : ∀ a ∈ A, ∀ K ∈ 𝒦, ∃ x ∈ A ⊓ K, a * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro a ha K hK
    obtain ⟨x, hx, hconj⟩ :=
      h17 G S A K hA.le hA.comm hA.closed hO hK (hcomp K hK).1 (hcomp K hK).2 a ha
    exact ⟨x, hx, mul_inv_mem_centralizer_of_conj_eq hconj⟩
  have hAKA : (⨆ K ∈ 𝒦, A ⊓ K) ≤ A := iSup₂_le fun K _ => inf_le_left
  have hAKE : (⨆ K ∈ 𝒦, A ⊓ K) ≤ E := by
    rw [hE𝒦, sSup_eq_iSup]
    exact iSup₂_mono fun K _ => inf_le_right
  have hdec : ∀ g : G, (∀ K ∈ 𝒦, ∃ x ∈ A ⊓ K, g * x⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∃ y ∈ ⨆ K ∈ 𝒦, A ⊓ K, g * y⁻¹ ∈ Q := by
    intro g hg
    obtain ⟨y, hy, hyc⟩ := exists_mem_iSup_mul_inv_mem_centralizer 𝒦 hfin hcomm
      (fun K => A ⊓ K) (fun _ _ => inf_le_right) g hg
    refine ⟨y, hy, ?_⟩
    have hmem : g * y⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
      rw [hE𝒦]
      exact mem_centralizer_sSup hyc
    rw [hCE] at hmem
    exact hmem
  have hle : A ≤ Q ⊔ Omega1 ((S : Subgroup G) ⊓ E) := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := hdec a (h17' a ha)
    have hy' : y ∈ Q ⊔ Omega1 ((S : Subgroup G) ⊓ E) :=
      (iSup₂_le fun K hK => (hR8 K hK).2) hy
    have : a = a * y⁻¹ * y := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hay) hy'
  have hZE : E ⊓ Q ≤ A := by
    intro z hz
    obtain ⟨hzE, hzQ⟩ := Subgroup.mem_inf.mp hz
    have hzQ' : z ∈ Subgroup.centralizer (E : Set G) := by
      rw [hCE]
      exact hzQ
    have hzc : ∀ K ∈ 𝒦, z ∈ Subgroup.centralizer (K : Set G) := fun K hK =>
      Subgroup.centralizer_le (le_sSup hK : K ≤ E) hzQ'
    exact (iSup₂_le fun K hK => (hR8 K hK).1)
      (mem_iSup_inf_centralizer 𝒦 hfin hnorm hcomm hzE hzc)
  have hQS : Q ≤ S := IsPGroup.le_sylow_of_normal (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2) S
  have hAE : A ⊔ E = ⊤ := by
    have hAEn : (A ⊔ E).Normal := by
      constructor
      intro n hn g
      obtain ⟨a, ha, e', he', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
      have hg : g ∈ Q ⊔ E := by
        rw [hQE]
        exact Subgroup.mem_top g
      obtain ⟨q, hq, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      have h1 : q * a * q⁻¹ ∈ A := by
        have := conj_mem_of_stronglyClosed hA.le hA.closed (S.inv_mem (hQS hq)) ha
        simpa using this
      have h2 : q * (a⁻¹ * e * a * e' * e⁻¹) * q⁻¹ ∈ E := by
        refine hEn.conj_mem _ ?_ q
        refine E.mul_mem (E.mul_mem ?_ he') (E.inv_mem he)
        have := hEn.conj_mem e he a⁻¹
        simpa [mul_assoc] using this
      have heq : q * e * (a * e') * (q * e)⁻¹ =
          q * a * q⁻¹ * (q * (a⁻¹ * e * a * e' * e⁻¹) * q⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    rw [eq_top_iff, ← hA.gen]
    exact Subgroup.normalClosure_le_normal (le_sup_left : A ≤ A ⊔ E)
  have hQA : Q ≤ A := by
    intro q hq
    have hq' : q ∈ A ⊔ E := by
      rw [hAE]
      exact Subgroup.mem_top q
    obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hq'
    obtain ⟨y, hy, hay⟩ := hdec a (h17' a ha)
    have hye : y * e ∈ E ⊓ Q := by
      refine ⟨E.mul_mem (hAKE hy) he, ?_⟩
      have := Q.mul_mem (Q.inv_mem hay) hq
      simpa [mul_assoc] using this
    have : a * e = a * y⁻¹ * (y * e) := by group
    rw [this]
    exact A.mul_mem (A.mul_mem ha (A.inv_mem (hAKA hy))) (hZE hye)
  have hΩA : Omega1 ((S : Subgroup G) ⊓ E) ≤ A := by
    rw [Omega1, Subgroup.closure_le]
    rintro t ⟨⟨htS, htE⟩, ht2⟩
    have hg : ∀ K ∈ 𝒦, ∃ x ∈ A ⊓ K, t * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      intro K hK
      have := hnorm K hK
      have hEK : E ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
        rw [hE𝒦]
        refine sSup_le fun L hL => ?_
        by_cases hLK : L = K
        · rw [hLK]
          exact le_sup_left
        · exact (hcomm L hL K hK hLK).trans le_sup_right
      obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp (hEK htE)
      have hkt : k⁻¹ * t ∈ Subgroup.centralizer (K : Set G) := by
        rw [← hkc]
        simpa using hc
      obtain ⟨s, hs, hts⟩ := exists_mem_inf_mul_inv_mem_centralizer S (hnorm K hK)
        ((N8d G hO).1 K hK) htS hk hkt
      have hs2 : s ^ 2 ∈ Subgroup.centralizer (K : Set G) :=
        sq_mem_centralizer_of_mul_inv_mem hs.2 hts (by rw [ht2]; exact Subgroup.one_mem _)
      obtain ⟨a, ha, has⟩ := (hcomp K hK).2.2 s hs hs2
      obtain ⟨x, hx, hxa⟩ := h17' a ha K hK
      refine ⟨x, hx, ?_⟩
      have hxs : x * s⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
        have hconj := conj_eq_of_mul_inv_mem_centralizer hxa
        refine mul_inv_mem_centralizer_of_conj_eq fun z hz => ?_
        rw [← hconj z hz, has z hz]
      have : t * x⁻¹ = t * s⁻¹ * (x * s⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hts (Subgroup.inv_mem _ hxs)
    obtain ⟨y, hy, hty⟩ := hdec t hg
    have : t = t * y⁻¹ * y := by group
    rw [this]
    exact A.mul_mem (hQA hty) (hAKA hy)
  exact le_antisymm hle (sup_le hQA hΩA)

end CFSG.Goldschmidt
