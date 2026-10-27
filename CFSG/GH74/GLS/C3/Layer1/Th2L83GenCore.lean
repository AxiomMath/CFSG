module

public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk61L29

public section

namespace CFSG.GH74.GLS.Th2.L83

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

theorem exists_fixed_mem_coset {O F : Subgroup G} (hOodd : ¬ 2 ∣ Nat.card O) (hF : IsPGroup 2 ↥F)
    (hFO : ∀ f ∈ F, ∀ o ∈ O, f * o * f⁻¹ ∈ O) {k : G}
    (hk : ∀ f ∈ F, k⁻¹ * (f * k * f⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ f ∈ F, f * (k * o) * f⁻¹ = k * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction F {g : G // k⁻¹ * g ∈ O} :=
    { smul := fun f g => ⟨(f : G) * g.1 * (f : G)⁻¹, by
        have h1 : k⁻¹ * ((f : G) * g.1 * (f : G)⁻¹) =
            (k⁻¹ * ((f : G) * k * (f : G)⁻¹)) * ((f : G) * (k⁻¹ * g.1) * (f : G)⁻¹) := by group
        rw [h1]
        exact O.mul_mem (hk f f.2) (hFO f f.2 _ g.2)⟩
      one_smul := fun g => Subtype.ext (by simp [HSMul.hSMul, SMul.smul])
      mul_smul := fun f f' g => Subtype.ext (by simp [HSMul.hSMul, SMul.smul, mul_assoc]) }
  have hcard : Nat.card {g : G // k⁻¹ * g ∈ O} = Nat.card O := by
    refine Nat.card_congr ⟨fun g => ⟨k⁻¹ * g.1, g.2⟩, fun o => ⟨k * o.1, by simp⟩, ?_, ?_⟩
    · intro g; apply Subtype.ext; simp
    · intro o; apply Subtype.ext; simp
  obtain ⟨g, hg⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card {g : G // k⁻¹ * g ∈ O}
    (by rw [hcard]; exact hOodd)
  refine ⟨k⁻¹ * g.1, g.2, fun f hf => ?_⟩
  have := congrArg Subtype.val (hg ⟨f, hf⟩)
  have h2 : (f : G) * g.1 * (f : G)⁻¹ = g.1 := this
  calc f * (k * (k⁻¹ * g.1)) * f⁻¹ = f * g.1 * f⁻¹ := by group
    _ = g.1 := h2
    _ = k * (k⁻¹ * g.1) := by group

theorem mem_centralizer_sup_of_forall {F : Subgroup G} {b v : G} (hF : ∀ f ∈ F, v * f = f * v)
    (hb : v * b = b * v) : v ∈ centralizer ((F ⊔ zpowers b : Subgroup G) : Set G) := by
  have hle : F ⊔ zpowers b ≤ centralizer ({v} : Set G) := by
    refine sup_le (fun f hf => ?_) (zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hF f hf).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hb.symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := hle hh
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

variable [Finite G]

theorem le_of_forall_inf_centralizer_rank {W : Subgroup G} :
    ∀ (r : ℕ) {A V : Subgroup G}, CFSG.IsElementaryAbelian 2 ↥A → r + 1 ≤ pRank 2 ↥A →
      ¬ 2 ∣ Nat.card V → A ≤ normalizer (V : Set G) →
      (∀ F : Subgroup G, F ≤ A → r ≤ pRank 2 ↥F → V ⊓ centralizer (F : Set G) ≤ W) → V ≤ W := by
  intro r
  induction r with
  | zero =>
    intro A V _ _ _ _ hle
    have := hle ⊥ bot_le (Nat.zero_le _)
    intro v hv
    refine this (Subgroup.mem_inf.2 ⟨hv, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : h = 1 := hh
    rw [this]; simp
  | succ r ih =>
    intro A V hA hrk hV hAV hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨E, hEA, hEel, hEcard⟩ := Th2.CaseI.exists_elemAbelian_four (Q := A) (by omega)
    refine Asc75.le_of_forall_inf_centralizer_le' hEel hEcard hV (hEA.trans hAV) ?_
    intro b hb hb1
    have hbA : b ∈ A := hEA hb
    have hb2 : orderOf b = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b hbA) hb1
    obtain ⟨A₀, hA₀A, hA₀b, hA₀card⟩ := IVK.Proofs2.exists_complement_zpowers hA hbA hb2
    have hA₀el : CFSG.IsElementaryAbelian 2 ↥A₀ := Th2.elemAbelian_of_le hA hA₀A
    have hA₀rk : r + 1 ≤ pRank 2 ↥A₀ := by
      have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hA₀el
      have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hA
      rw [h1, h2, ← pow_succ] at hA₀card
      have := Nat.pow_right_injective (le_refl 2) hA₀card
      omega
    have hcomm : ∀ a ∈ A, a * b = b * a := fun a ha =>
      (C3.Layer1.Back.forall_of_isElementaryAbelian hA).1 a ha b hbA
    refine ih (A := A₀) (V := V ⊓ centralizer ({b} : Set G)) hA₀el hA₀rk ?_ ?_ ?_
    · intro h2
      exact hV (h2.trans (Subgroup.card_dvd_of_le inf_le_left))
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro v
      have hAV' := Subgroup.mem_normalizer_iff.1 (hAV (hA₀A ha)) v
      have hab := hcomm a (hA₀A ha)
      have hab' : a⁻¹ * b = b * a⁻¹ := by
        calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * b) * a⁻¹ := by rw [hab]
          _ = b * a⁻¹ := by group
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hAV', Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h
        calc a * v * a⁻¹ * b = a * v * (a⁻¹ * b) := by group
          _ = a * v * (b * a⁻¹) := by rw [hab']
          _ = a * (v * b) * a⁻¹ := by group
          _ = a * (b * v) * a⁻¹ := by rw [h]
          _ = (a * b) * v * a⁻¹ := by group
          _ = (b * a) * v * a⁻¹ := by rw [hab]
          _ = b * (a * v * a⁻¹) := by group
      · intro h
        have h' : a * v * a⁻¹ * b = b * (a * v * a⁻¹) := h
        have hb' : a⁻¹ * b * a = b := by
          calc a⁻¹ * b * a = (b * a⁻¹) * a := by rw [hab']
            _ = b := by group
        calc v * b = v * (a⁻¹ * b * a) := by rw [hb']
          _ = a⁻¹ * (a * v * a⁻¹ * b) * a := by group
          _ = a⁻¹ * (b * (a * v * a⁻¹)) * a := by rw [h']
          _ = (a⁻¹ * b * a) * v := by group
          _ = b * v := by rw [hb']
    · intro F hFA₀ hFrk
      have hFA : F ≤ A := hFA₀.trans hA₀A
      have hFel : CFSG.IsElementaryAbelian 2 ↥F := Th2.elemAbelian_of_le hA hFA
      have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers b) :=
        isElementaryAbelian_zpowers_of_orderOf_two hb2
      have hcd : CommDisj F (zpowers b) := by
        refine ⟨fun f hf t ht => ?_, ?_⟩
        · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
          exact (Commute.zpow_right (hcomm f (hFA hf)) m).symm.eq.symm |>.symm |>.symm
        · refine eq_bot_iff.2 fun z hz => ?_
          have : z ∈ A₀ ⊓ zpowers b := ⟨hFA₀ hz.1, hz.2⟩
          rw [hA₀b] at this
          exact this
      have hrk' : pRank 2 ↥(F ⊔ zpowers b) = pRank 2 ↥F + 1 := by
        rw [hcd.pRank_sup hFel hzel le_rfl le_rfl, pRank_zpowers_of_orderOf_two hb2]
      have hle' := hle (F ⊔ zpowers b) (sup_le hFA (zpowers_le.2 hbA)) (by omega)
      intro v hv
      obtain ⟨⟨hvV, hvb⟩, hvF⟩ := hv
      refine hle' ⟨hvV, mem_centralizer_sup_of_forall ?_ ?_⟩
      · intro f hf
        exact (Subgroup.mem_centralizer_iff.1 hvF f hf).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.1 hvb)

theorem pPrimeCoreOf_le_of_normalizers {K X M A : Subgroup G}
    (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (r : ℕ) (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hAX : A ≤ X) (hArk : r + 1 ≤ pRank 2 ↥A)
    (hN : ∀ F : Subgroup G, F ≤ A → r ≤ pRank 2 ↥F → (normalizer (F : Set G)) ≤ M) :
    pPrimeCoreOf 2 K ≤ M := by
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCoreOf 2 K) := by
    have := TwoThin.card_pPrimeCoreOf_odd K
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact this
  refine le_of_forall_inf_centralizer_rank r hA hArk hodd (fun a ha => ?_) (fun F hFA hFr => ?_)
  · exact U1a.mem_normalizer_pPrimeCoreOf hKX (hAX ha)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (F : Set G)).trans (hN F hFA hFr))

noncomputable def fixBar {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (F : Subgroup G) : Subgroup (kBar K) :=
  ⨅ (f : ↥X) (_ : (f : G) ∈ F), Bk.fixSub (kBar K) (Back.actHom hKX f)

omit [Finite G] in
theorem mem_fixBar_iff {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    {F : Subgroup G} {z : kBar K} :
    z ∈ fixBar hKX F ↔ ∀ f : ↥X, (f : G) ∈ F → Back.actHom hKX f z = z := by
  simp only [fixBar, Subgroup.mem_iInf]
  rfl

theorem K_le_of_cover {K X M : Subgroup G}
    (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (𝔉 : Set (Subgroup G)) (hF : ∀ F ∈ 𝔉, F ≤ X ∧ IsPGroup 2 ↥F)
    (hFM : ∀ F ∈ 𝔉, K ⊓ centralizer (F : Set G) ≤ M) (hO : pPrimeCoreOf 2 K ≤ M)
    (hgen : ⨆ F ∈ 𝔉, fixBar hKX F = ⊤) : K ≤ M := by
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCoreOf 2 K) := by
    have := TwoThin.card_pPrimeCoreOf_odd K
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact this
  set Hbar : Subgroup (kBar K) :=
    ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) with hHbar
  have hfix : ∀ F ∈ 𝔉, fixBar hKX F ≤ Hbar := by
    intro F hFmem z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨hFX, hF2⟩ := hF F hFmem
    have hk : ∀ f ∈ F, (k : G)⁻¹ * (f * (k : G) * f⁻¹) ∈ pPrimeCoreOf 2 K := by
      intro f hf
      have h1 := (mem_fixBar_iff hKX).1 hz ⟨f, hFX hf⟩ hf
      rw [Back.actHom_mk] at h1
      have h2 := QuotientGroup.eq.1 h1.symm
      exact Back.Setup91.mem_pPrimeCoreOf_iff.2
        ⟨K.mul_mem (K.inv_mem k.2) (hKX f (hFX hf) k k.2), h2⟩
    obtain ⟨o, ho, hfixo⟩ := exists_fixed_mem_coset hodd hF2
      (fun f hf o ho => U1a.pPrimeCoreOf_norm hKX (hFX hf) ho) hk
    have hkoK : (k : G) * o ∈ K := K.mul_mem k.2 (TwoThin.pPrimeCoreOf_le K ho)
    have hkoM : (k : G) * o ∈ M := by
      refine hFM F hFmem ⟨hkoK, ?_⟩
      show (k : G) * o ∈ centralizer (F : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have := hfixo f hf
      calc f * ((k : G) * o) = f * ((k : G) * o) * f⁻¹ * f := by group
        _ = ((k : G) * o) * f := by rw [this]
    refine ⟨⟨(k : G) * o, hkoK⟩, ⟨hkoK, hkoM⟩, ?_⟩
    show QuotientGroup.mk (⟨(k : G) * o, hkoK⟩ : ↥K) = QuotientGroup.mk k
    rw [QuotientGroup.eq]
    obtain ⟨hoK, hoO⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
    have : (⟨(k : G) * o, hkoK⟩ : ↥K)⁻¹ * k = ⟨o, hoK⟩⁻¹ := by
      apply Subtype.ext; simp
    rw [this]
    exact (pPrimeCore 2 ↥K).inv_mem hoO
  have htop : Hbar = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le fun F hF' => hfix F hF'
  intro k hk
  have : QuotientGroup.mk (⟨k, hk⟩ : ↥K) ∈ Hbar := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hh, hmk⟩ := this
  have hmk' : QuotientGroup.mk h = (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) := hmk
  have hdiff : h⁻¹ * (⟨k, hk⟩ : ↥K) ∈ pPrimeCore 2 ↥K := QuotientGroup.eq.1 hmk'
  have hdiffG : (h : G)⁻¹ * k ∈ pPrimeCoreOf 2 K :=
    Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (K.inv_mem h.2) hk, hdiff⟩
  have hhM : (h : G) ∈ M := (Subgroup.mem_subgroupOf.1 hh).2
  have : k = (h : G) * ((h : G)⁻¹ * k) := by group
  rw [this]
  exact M.mul_mem hhM (hO hdiffG)

end CFSG.GH74.GLS.Th2.L83
