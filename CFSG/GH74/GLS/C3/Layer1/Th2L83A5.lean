module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83L2
public import CFSG.GH74.GLS.C3.Layer1.Th2L83Alt

public section

namespace CFSG.GH74.GLS.Th2.L83

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.C3.Layer1

section S5

@[expose] def S5Closed (a b : Perm (Fin 5)) : Prop :=
  ∀ c : Perm (Fin 5), c * c = 1 → c * a = a * c → c * b = b * c → c = 1 ∨ c = a ∨ c = b ∨ c = a * b

instance (a b : Perm (Fin 5)) : Decidable (S5Closed a b) := by
  unfold S5Closed; infer_instance

set_option maxRecDepth 100000 in
theorem s5_no_rank_three : ∀ a : Perm (Fin 5), a * a = 1 → a ≠ 1 → ∀ b : Perm (Fin 5), b * b = 1 →
    b ≠ 1 → b ≠ a → a * b = b * a → S5Closed a b := by decide +kernel

theorem card_le_four_of_elem_S5 (E : Subgroup (Perm (Fin 5))) (hE : CFSG.IsElementaryAbelian 2 ↥E) :
    Nat.card ↥E ≤ 4 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hcomm, hsq⟩ := Back.forall_of_isElementaryAbelian hE
  have hEc : (E : Set (Perm (Fin 5))).ncard = Nat.card ↥E := Nat.card_coe_set_eq _
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    have h1 : ({1} : Set (Perm (Fin 5))).ncard < (E : Set (Perm (Fin 5))).ncard := by
      rw [Set.ncard_singleton, hEc]; omega
    obtain ⟨a, haE, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
    exact ⟨a, haE, by simpa using ha⟩
  obtain ⟨b, hbE, hb1, hba⟩ : ∃ b ∈ E, b ≠ 1 ∧ b ≠ a := by
    have h1 : ({1, a} : Set (Perm (Fin 5))).ncard < (E : Set (Perm (Fin 5))).ncard := by
      rw [hEc]
      have := Set.ncard_insert_le (1 : Perm (Fin 5)) ({a} : Set (Perm (Fin 5)))
      rw [Set.ncard_singleton] at this
      omega
    obtain ⟨b, hbE, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
    exact ⟨b, hbE, hb.1, hb.2⟩
  obtain ⟨c, hcE, hc⟩ : ∃ c ∈ E, c ∉ ({1, a, b, a * b} : Set (Perm (Fin 5))) := by
    have h1 : ({1, a, b, a * b} : Set (Perm (Fin 5))).ncard < (E : Set (Perm (Fin 5))).ncard := by
      rw [hEc]
      have h2 := Set.ncard_insert_le (1 : Perm (Fin 5)) ({a, b, a * b} : Set (Perm (Fin 5)))
      have h3 := Set.ncard_insert_le a ({b, a * b} : Set (Perm (Fin 5)))
      have h4 := Set.ncard_insert_le b ({a * b} : Set (Perm (Fin 5)))
      rw [Set.ncard_singleton] at h4
      omega
    exact Set.exists_mem_notMem_of_ncard_lt_ncard h1
  have hsq' : ∀ x ∈ E, x * x = 1 := fun x hx => hsq x hx
  have := s5_no_rank_three a (hsq' a haE) ha1 b (hsq' b hbE) hb1 hba (hcomm a haE b hbE)
    c (hsq' c hcE) (hcomm c hcE a haE) (hcomm c hcE b hbE)
  apply hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this

theorem card_le_four_of_aut_A5 {K : Type} [Group K] (e5 : K ≃* alternatingGroup (Fin 5))
    (W : Subgroup (MulAut K)) (hW : CFSG.IsElementaryAbelian 2 ↥W) : Nat.card ↥W ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : Perm (Fin 5) ≃* MulAut K := altAut (by norm_num) (by norm_num) e5
  have h1 : CFSG.IsElementaryAbelian 2 ↥(W.map e.symm.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map (A := W) e.symm.toMonoidHom
  have h2 := card_le_four_of_elem_S5 _ h1
  rwa [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective] at h2

end S5

section Triv

variable {G : Type} [Group G] {K X A : Subgroup G}

@[expose] noncomputable def trivSub (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X) : Subgroup G :=
  (actOn hKX hAX).ker.map A.subtype

theorem mem_trivSub_iff (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X) {e : G} :
    e ∈ trivSub hKX hAX ↔ ∃ he : e ∈ A, Back.actHom hKX ⟨e, hAX he⟩ = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, h, rfl⟩

theorem trivSub_le (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X) :
    trivSub hKX hAX ≤ A := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

theorem card_trivSub_mul_range (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X) :
    Nat.card ↥(trivSub hKX hAX) * Nat.card ↥(actOn hKX hAX).range = Nat.card ↥A := by
  have h := Subgroup.card_ker_mul_card_range (actOn hKX hAX)
  have e : Nat.card ↥(trivSub hKX hAX) = Nat.card ↥(actOn hKX hAX).ker :=
    Subgroup.card_map_of_injective A.subtype_injective
  rw [e]
  exact h

theorem isElementaryAbelian_range_actOn (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) :
    CFSG.IsElementaryAbelian 2 ↥(actOn hKX hAX).range := by
  obtain ⟨hc, hs⟩ := Back.forall_of_isElementaryAbelian hAel
  refine Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc a a.2 b b.2)
  · obtain ⟨a, rfl⟩ := hu
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hs a a.2)
    rw [this, map_one]

theorem pRank_le_trivSub_add_two [Finite G] (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hAX : A ≤ X)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hAel : CFSG.IsElementaryAbelian 2 ↥A) :
    pRank 2 ↥A ≤ pRank 2 ↥(trivSub hKX hAX) + 2 := by
  have hEel : CFSG.IsElementaryAbelian 2 ↥(trivSub hKX hAX) :=
    Th2.elemAbelian_of_le hAel (trivSub_le hKX hAX)
  have h4 := card_le_four_of_aut_A5 e5 _ (isElementaryAbelian_range_actOn hKX hAX hAel)
  have hc := card_trivSub_mul_range hKX hAX
  rw [Back.card_eq_two_pow_pRank hAel, Back.card_eq_two_pow_pRank hEel] at hc
  have h1 : 2 ^ pRank 2 ↥A ≤ 2 ^ (pRank 2 ↥(trivSub hKX hAX) + 2) := by
    rw [← hc, pow_add]
    exact Nat.mul_le_mul_left _ (by omega)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1

theorem K_le_of_trivial [Finite G] {M E : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hEX : E ≤ X)
    (hE2 : IsPGroup 2 ↥E) (hEtriv : ∀ (e : G) (he : e ∈ E), Back.actHom hKX ⟨e, hEX he⟩ = 1)
    (hEM : normalizer (E : Set G) ≤ M) (hO : pPrimeCoreOf 2 K ≤ M) : K ≤ M := by
  refine K_le_of_cover hKX {E} (fun F hF => ?_) (fun F hF => ?_) hO ?_
  · rw [Set.mem_singleton_iff] at hF
    subst hF
    exact ⟨hEX, hE2⟩
  · rw [Set.mem_singleton_iff] at hF
    subst hF
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (F : Set G)).trans hEM)
  · refine top_le_iff.1 (le_iSup₂_of_le E (Set.mem_singleton E) ?_)
    intro z _
    rw [mem_fixBar_iff]
    intro f hf
    show Back.actHom hKX ⟨f.1, hEX hf⟩ z = z
    rw [hEtriv f.1 hf]
    rfl

theorem l83_A5_two [Finite G] {M : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hAX : A ≤ X) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hA4 : 4 ≤ pRank 2 ↥A)
    (hN : ∀ F : Subgroup G, F ≤ A → 2 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) : K ≤ M := by
  have hEA := trivSub_le hKX hAX
  have hEel : CFSG.IsElementaryAbelian 2 ↥(trivSub hKX hAX) := Th2.elemAbelian_of_le hAel hEA
  have hErk : 2 ≤ pRank 2 ↥(trivSub hKX hAX) := by
    have := pRank_le_trivSub_add_two hKX hAX e5 hAel
    omega
  have hO : pPrimeCoreOf 2 K ≤ M := pPrimeCoreOf_le_of_normalizers hKX 2 hAel hAX (by omega) hN
  exact K_le_of_trivial hKX (hEA.trans hAX) (CFSG.IsElementaryAbelian.isPGroup 2 _)
    (fun e he => ((mem_trivSub_iff hKX hAX).1 he).choose_spec) (hN _ hEA hErk) hO

theorem l83_A5_three_klein [Finite G] {M : Subgroup G}
    (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hAX : A ≤ X)
    (hE2 : pRank 2 ↥(trivSub hKX hAX) = 2)
    (hgam : Bk.gammaAut (kBar K) (actOn hKX hAX).range = ⊤)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A)
    (hN : ∀ F : Subgroup G, F ≤ A → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) :
    K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, hs⟩ := Back.forall_of_isElementaryAbelian hAel
  have hEA := trivSub_le hKX hAX
  have hEX : trivSub hKX hAX ≤ X := hEA.trans hAX
  have hEel : CFSG.IsElementaryAbelian 2 ↥(trivSub hKX hAX) := Th2.elemAbelian_of_le hAel hEA
  have hEtriv : ∀ (e : G) (he : e ∈ trivSub hKX hAX), Back.actHom hKX ⟨e, hEX he⟩ = 1 :=
    fun e he => ((mem_trivSub_iff hKX hAX).1 he).choose_spec
  have hO : pPrimeCoreOf 2 K ≤ M := pPrimeCoreOf_le_of_normalizers hKX 3 hAel hAX hA4 hN
  have hinv : ∀ w ∈ (actOn hKX hAX).range, orderOf w = 2 →
      ∃ (u : G) (hu : u ∈ A), orderOf u = 2 ∧ actOn hKX hAX ⟨u, hu⟩ = w := by
    rintro w ⟨⟨u, hu⟩, rfl⟩ hord
    have hu1 : u ≠ 1 := by
      intro h1
      subst h1
      rw [show (⟨1, hu⟩ : ↥A) = 1 from rfl, map_one, orderOf_one] at hord
      omega
    have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hs u hu
    exact ⟨u, hu, orderOf_eq_prime hu2 hu1, rfl⟩
  have hgen := fixBar_gen_of_gamma hKX hAX hEX hEtriv (fun p hp e he => hc p hp e (hEA he))
    hgam hinv
  refine K_le_of_cover hKX (fixFam hKX hAX (trivSub hKX hAX)) ?_ ?_ hO hgen
  · rintro F ⟨u, hu, hu2, hne, rfl⟩
    have hFA : zpowers u ⊔ trivSub hKX hAX ≤ A := sup_le (zpowers_le.2 hu) hEA
    exact ⟨hFA.trans hAX, (CFSG.IsElementaryAbelian.isPGroup 2 ↥A).to_le hFA⟩
  · rintro F ⟨u, hu, hu2, hne, rfl⟩
    have hFA : zpowers u ⊔ trivSub hKX hAX ≤ A := sup_le (zpowers_le.2 hu) hEA
    have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) :=
      isElementaryAbelian_zpowers_of_orderOf_two hu2
    have huE : u ∉ trivSub hKX hAX := fun huE =>
      hne (by
        obtain ⟨he, h1⟩ := (mem_trivSub_iff hKX hAX).1 huE
        exact h1)
    have hcd : CommDisj (zpowers u) (trivSub hKX hAX) := by
      refine ⟨fun a ha b hb => ?_, eq_bot_iff.2 fun z hz => ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (hc u hu b (hEA hb)) m).eq
      · rcases mem_zpowers_two hu2 hz.1 with h0 | h0
        · simp [h0]
        · exact absurd (h0 ▸ hz.2) huE
    have hrkF : 3 ≤ pRank 2 ↥(zpowers u ⊔ trivSub hKX hAX) := by
      rw [hcd.pRank_sup hzel hEel le_rfl le_rfl, pRank_zpowers_of_orderOf_two hu2]
      omega
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans (hN _ hFA hrkF))

theorem l83_A5_three [Finite G] {M : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hL2 : HasL2Model (kBar K) Odd) (h6 : Bk.B_ivk_6)
    (hAX : A ≤ X) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A)
    (hout : ∃ (a : G) (ha : a ∈ A), actOn hKX hAX ⟨a, ha⟩ ∉
      (MulAut.conj : kBar K →* MulAut (kBar K)).range)
    (hN : ∀ F : Subgroup G, F ≤ A → 3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) : K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, hs⟩ := Back.forall_of_isElementaryAbelian hAel
  have hEA := trivSub_le hKX hAX
  have hEX : trivSub hKX hAX ≤ X := hEA.trans hAX
  have hEel : CFSG.IsElementaryAbelian 2 ↥(trivSub hKX hAX) := Th2.elemAbelian_of_le hAel hEA
  have hEtriv : ∀ (e : G) (he : e ∈ trivSub hKX hAX), Back.actHom hKX ⟨e, hEX he⟩ = 1 :=
    fun e he => ((mem_trivSub_iff hKX hAX).1 he).choose_spec
  have hO : pPrimeCoreOf 2 K ≤ M := pPrimeCoreOf_le_of_normalizers hKX 3 hAel hAX hA4 hN
  have hrk := pRank_le_trivSub_add_two hKX hAX e5 hAel
  by_cases hE3 : 3 ≤ pRank 2 ↥(trivSub hKX hAX)
  · exact K_le_of_trivial hKX hEX (CFSG.IsElementaryAbelian.isPGroup 2 _) hEtriv (hN _ hEA hE3) hO
  · have hE2 : pRank 2 ↥(trivSub hKX hAX) = 2 := by omega
    have hW := isElementaryAbelian_range_actOn hKX hAX hAel
    have hWp : IsPGroup 2 ↥(actOn hKX hAX).range := CFSG.IsElementaryAbelian.isPGroup 2 _
    have hWrk : 2 ≤ CFSG.pRank 2 ↥(actOn hKX hAX).range := by
      have hcard := card_trivSub_mul_range hKX hAX
      rw [Back.card_eq_two_pow_pRank hAel, Back.card_eq_two_pow_pRank hEel, hE2] at hcard
      have h16 : 2 ^ 4 ≤ 2 ^ pRank 2 ↥A := Nat.pow_le_pow_right (by norm_num) hA4
      rw [Back.card_eq_two_pow_pRank hW] at hcard
      by_contra hlt
      have : 2 ^ pRank 2 ↥(actOn hKX hAX).range ≤ 2 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hgam : Bk.gammaAut (kBar K) (actOn hKX hAX).range = ⊤ := by
      by_contra hne
      obtain ⟨-, -, hWinn⟩ := h6 (kBar K) (actOn hKX hAX).range (Or.inl hL2) hWp hWrk hne
      obtain ⟨a, ha, hnotin⟩ := hout
      exact hnotin (hWinn ⟨⟨a, ha⟩, rfl⟩)
    exact l83_A5_three_klein hKX hAX hE2 hgam hAel hA4 hN

end Triv

end CFSG.GH74.GLS.Th2.L83
