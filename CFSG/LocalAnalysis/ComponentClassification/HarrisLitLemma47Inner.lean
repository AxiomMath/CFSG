module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Layer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Center
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitRankFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

namespace Lemma47

variable {G : Type*} [Group G]

theorem sup_zpowers_spec [Finite G] {E : Subgroup G} {x : G} (hc : ∀ a ∈ E, a * x = x * a) :
    Nat.card (E ⊔ zpowers x : Subgroup G) * Nat.card (E ⊓ zpowers x : Subgroup G) =
        Nat.card E * Nat.card (zpowers x) ∧
      ((E ⊔ zpowers x : Subgroup G) : Set G) = (E : Set G) * (zpowers x : Set G) :=
  GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers x) fun a ha y hy => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute a x from hc a ha) n).eq

theorem card_sup_zpowers [Finite G] {E : Subgroup G} {x : G} (hc : ∀ a ∈ E, a * x = x * a)
    (hx : orderOf x = 2) (hxE : x ∉ E) :
    Nat.card (E ⊔ zpowers x : Subgroup G) = 2 * Nat.card E := by
  obtain ⟨h1, -⟩ := sup_zpowers_spec hc
  have hinf : E ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyE, hyx⟩
    rcases eq_one_or_eq_of_mem_zpowers_two hx hyx with rfl | rfl
    · exact one_mem _
    · exact absurd hyE hxE
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, hx] at h1
  rw [h1, mul_comm]

theorem isElemTwo_sup_zpowers [Finite G] {E : Subgroup G} {x : G} (hE : GrSLit.IsElemTwo E)
    (hc : ∀ a ∈ E, a * x = x * a) (hx : x * x = 1) :
    GrSLit.IsElemTwo (E ⊔ zpowers x : Subgroup G) := by
  obtain ⟨-, hset⟩ := sup_zpowers_spec hc
  have hmem : ∀ g ∈ (E ⊔ zpowers x : Subgroup G), ∃ a ∈ E, ∃ n : ℤ, g = a * x ^ n := by
    intro g hg
    have hg' : g ∈ ((E ⊔ zpowers x : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨a, ha, y, hy, rfl⟩ := hg'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact ⟨a, ha, n, rfl⟩
  have hcomm : ∀ a ∈ E, ∀ n : ℤ, Commute a (x ^ n) := fun a ha n =>
    Commute.zpow_right (show Commute a x from hc a ha) n
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, n, rfl⟩ := hmem g hg
    obtain ⟨a', ha', n', rfl⟩ := hmem g' hg'
    have h1 : a * a' = a' * a := hE.1 a ha a' ha'
    have h2 := (hcomm a ha n').eq
    have h3 := (hcomm a' ha' n).eq
    calc a * x ^ n * (a' * x ^ n') = a * (x ^ n * a') * x ^ n' := by group
      _ = a * (a' * x ^ n) * x ^ n' := by rw [h3]
      _ = (a * a') * (x ^ n * x ^ n') := by group
      _ = (a' * a) * (x ^ n' * x ^ n) := by rw [h1, ← zpow_add, ← zpow_add, add_comm]
      _ = a' * (a * x ^ n') * x ^ n := by group
      _ = a' * (x ^ n' * a) * x ^ n := by rw [h2]
      _ = a' * x ^ n' * (a * x ^ n) := by group
  · obtain ⟨a, ha, n, rfl⟩ := hmem g hg
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
    calc a * x ^ n * (a * x ^ n) = (a * a) * (x ^ n * x ^ n) := by
          rw [show a * x ^ n * (a * x ^ n) = a * (x ^ n * a) * x ^ n by group,
            ← (hcomm a ha n).eq]
          group
      _ = 1 := by
        rw [hE.2 a ha, one_mul, ← zpow_add, ← two_mul, zpow_mul, hx2, one_zpow]

theorem mem_sup_zpowers_two [Finite G] {E : Subgroup G} {x : G} (hc : ∀ a ∈ E, a * x = x * a)
    (hx : orderOf x = 2) {g : G} (hg : g ∈ (E ⊔ zpowers x : Subgroup G)) :
    ∃ a ∈ E, g = a ∨ g = a * x := by
  obtain ⟨-, hset⟩ := sup_zpowers_spec hc
  have hg' : g ∈ ((E ⊔ zpowers x : Subgroup G) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨a, ha, y, hy, rfl⟩ := hg'
  rcases eq_one_or_eq_of_mem_zpowers_two hx hy with rfl | rfl
  · exact ⟨a, ha, .inl (mul_one a)⟩
  · exact ⟨a, ha, .inr rfl⟩

theorem exists_elemTwo_thirtyTwo [Finite G] {tb bb : G} (hbbZ : bb ∈ center G)
    (hbb2 : orderOf bb = 2) (htb2 : orderOf tb = 2) (hne : tb ≠ bb) {B A : Subgroup G}
    (hB : B ≤ centralizer {tb}) (hZB : center ↥B = ⊥) (hAB : A ≤ B) (hA : GrSLit.IsElemTwo A)
    (hA8 : Nat.card A = 8) :
    ∃ E : Subgroup G, E ≤ centralizer {tb} ∧ GrSLit.IsElemTwo E ∧ Nat.card E = 32 := by
  have hbbc : ∀ g : G, g * bb = bb * g := fun g => (mem_center_iff.mp hbbZ g)
  have hZB' : ∀ b ∈ B, (∀ c ∈ B, c * b = b * c) → b = 1 := by
    intro b hb hcb
    have : (⟨b, hb⟩ : ↥B) ∈ center ↥B := by
      rw [mem_center_iff]
      intro c
      exact Subtype.ext (hcb c c.2)
    rw [hZB, mem_bot] at this
    exact congrArg Subtype.val this
  have hbb1 : bb ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hbb2; exact absurd hbb2 (by norm_num)
  have hbbA : bb ∉ A := fun h1 => hbb1 (hZB' bb (hAB h1) fun c _ => hbbc c)
  have hE1c : ∀ a ∈ A, a * bb = bb * a := fun a _ => hbbc a
  have hE1 := isElemTwo_sup_zpowers hA hE1c (by rw [← sq, ← hbb2, pow_orderOf_eq_one])
  have hE1card := card_sup_zpowers hE1c hbb2 hbbA
  have htbB : ∀ c ∈ B, c * tb = tb * c := fun c hc => mem_centralizer_singleton_iff.mp (hB hc)
  have htbE1 : tb ∉ (A ⊔ zpowers bb : Subgroup G) := by
    intro h1
    obtain ⟨a, ha, h2 | h2⟩ := mem_sup_zpowers_two hE1c hbb2 h1
    · have : tb = 1 := by
        rw [h2]
        exact hZB' a (hAB ha) fun c hc => by rw [← h2]; exact htbB c hc
      rw [this, orderOf_one] at htb2
      exact absurd htb2 (by norm_num)
    · have ha1 : a = 1 := by
        refine hZB' a (hAB ha) fun c hc => ?_
        have h3 : a = tb * bb⁻¹ := by rw [h2]; group
        have hcb : c * bb⁻¹ = bb⁻¹ * c := by
          calc c * bb⁻¹ = bb⁻¹ * (bb * c) * bb⁻¹ := by group
            _ = bb⁻¹ * (c * bb) * bb⁻¹ := by rw [hbbc c]
            _ = bb⁻¹ * c := by group
        rw [h3]
        calc c * (tb * bb⁻¹) = c * tb * bb⁻¹ := by group
          _ = tb * c * bb⁻¹ := by rw [htbB c hc]
          _ = tb * (c * bb⁻¹) := by group
          _ = tb * (bb⁻¹ * c) := by rw [hcb]
          _ = tb * bb⁻¹ * c := by group
      rw [ha1, one_mul] at h2
      exact hne h2
  have hE2c : ∀ a ∈ (A ⊔ zpowers bb : Subgroup G), a * tb = tb * a := by
    intro a ha
    obtain ⟨a', ha', h3 | h3⟩ := mem_sup_zpowers_two hE1c hbb2 ha
    · rw [h3]; exact htbB a' (hAB ha')
    · rw [h3, mul_assoc, ← hbbc tb, ← mul_assoc, htbB a' (hAB ha'), mul_assoc]
  refine ⟨(A ⊔ zpowers bb : Subgroup G) ⊔ zpowers tb, ?_,
    isElemTwo_sup_zpowers hE1 hE2c (by rw [← sq, ← htb2, pow_orderOf_eq_one]), ?_⟩
  · refine sup_le (sup_le (hAB.trans hB) ?_) ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (hbbc tb).symm
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr rfl
  · rw [card_sup_zpowers hE2c htb2 htbE1, hE1card, hA8]

end Lemma47

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem tBar_ne_betaBar (hσ : Setup42 h hS w z) (i j : ℕ) :
    hσ.tBar i j ≠ betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  intro heq
  have ht2 : t * t = 1 := by rw [← sq, ← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 1 :=
    by
      have h1 := pow_orderOf_eq_one (w ^ (orderOf w / 2) * t ^ i * z ^ j)
      rw [hσ.orderOf_beta i j, sq] at h1
      exact h1
  have htβ : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t :=
    (mem_centralizer_singleton_iff.mp (hσ.t_mem_centralizer_beta i j))
  set y : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
    ⟨t, hσ.t_mem_centralizer_beta i j⟩ *
      (⟨_, mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))⁻¹ with hy
  have hyO : y ∈ pPrimeCore 2 ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) := by
    rw [← QuotientGroup.eq_one_iff, hy, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change hσ.tBar i j * (betaBar _)⁻¹ = 1
    rw [heq, mul_inv_cancel]
  have hy1 : (y : X) ≠ 1 := by
    intro h1
    have h1' : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ = 1 := h1
    have htb : t = w ^ (orderOf w / 2) * t ^ i * z ^ j := mul_inv_eq_one.mp h1'
    apply hσ.rho_beta_ne_one i j
    rw [show (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) =
        ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ from Subtype.ext htb.symm]
    exact h.rho_t
  have hy2 : y * y = 1 := by
    apply Subtype.ext
    change t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ *
      (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹) = 1
    have hinv : (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ = w ^ (orderOf w / 2) * t ^ i * z ^ j :=
      inv_eq_of_mul_eq_one_left hβ2
    rw [hinv, show t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
        (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        t * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * t) * (w ^ (orderOf w / 2) * t ^ i * z ^ j)
        by group, ← htβ, show t * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
          (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        (t * t) * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j))
        by group, ht2, hβ2, one_mul]
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2)
    (fun h1 => hy1 (by rw [h1]; rfl))
  have hdvd := Subgroup.orderOf_dvd_natCard _ hyO
  rw [hord] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem not_inner_of_lemma47 (hKG : AutPSL2SylowInput) (hσ : Setup42 h hS w z) (i j : ℕ)
    {B A : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hB : B ≤ centralizer {hσ.tBar i j}) (hZB : center ↥B = ⊥) (hAB : A ≤ B)
    (hA : GrSLit.IsElemTwo A) (hA8 : Nat.card A = 8) : False := by
  have hbb2 : orderOf (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
    refine orderOf_eq_prime ?_ (hσ.betaBar_ne_one i j)
    rw [betaBar, ← QuotientGroup.mk_pow]
    have h1 := pow_orderOf_eq_one (w ^ (orderOf w / 2) * t ^ i * z ^ j)
    rw [hσ.orderOf_beta i j] at h1
    have : (⟨_, mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨E, hEt, hE, hE32⟩ := Lemma47.exists_elemTwo_thirtyTwo (betaBar_mem_center _) hbb2
    (hσ.orderOf_tBar i j) (hσ.tBar_ne_betaBar i j) hB hZB hAB hA hA8
  have hle := h.card_le_sixteen_of_le_centralizer_bar hKG (hσ.t_mem_centralizer_beta i j) hEt hE
  omega

theorem graph_of_lemma47 [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput) (hGA : TBLit.GriessMultipliersOdd)
    (hT1 : Harris82Theorem1KProper) (hC3 : L4U4InvolutionCentralizerFact)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hc : IsLemma46c L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hd : IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hσ.tBar i j))
    (he : IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    {J : Subgroup ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))}
    (hJ : IsPComponent 2 J) {k : ℕ} (hk : 1 ≤ k)
    (htype : IsOfType (fun (Y : Type) [Group Y] =>
      Blueprint.LieModel Y .PSL 4 p k ∨ Blueprint.LieModel Y .PSU 4 p k) ↥J) :
    f / 2 = 2 * k ∧
      ∀ w' ∈ GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {hσ.tBar i j}), orderOf w' = 2 →
        ∃ X₁ X₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), X₁ ≠ X₂ ∧
          X₁ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
          X₂ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
          (X₁.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
            centralizer {w'})).IsSubnormal ∧
          (X₂.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
            centralizer {w'})).IsSubnormal ∧
          X₁ ≤ centralizer (X₂ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
          X₁ ⊓ X₂ = zpowers w' ∧ IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂ := by
  obtain ⟨hE, hm, -⟩ := Lemma47.layer_of_isPComponent_four h.config.ne_two hd hJ htype
  have hZc := hσ.center_layer_cases hnonab hK hcat hGA hT1 i j hc hE hm
  have htc := hσ.tBar_not_mem_centralizer_layer hnonab hK hSch hFC hKC i j he hE hm
  have hlie : Blueprint.LieModel ↥(GSThmB.layerIn
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j}))
      .PSL 2 p (f / 2) := by
    rw [hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j]
    exact hσ.lieModel_KBar hFC hKC i j he
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have htN : hσ.tBar i j ∈ normalizer
      ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : Subgroup _) : Set _) := by
    rw [normalizer_eq_top_iff.mpr hEn]
    exact mem_top _
  have ht2 : hσ.tBar i j * hσ.tBar i j = 1 := by
    have h1 := pow_orderOf_eq_one (hσ.tBar i j)
    rw [hσ.orderOf_tBar i j, sq] at h1
    exact h1
  obtain ⟨hm2, hcase⟩ := hC3 _ _ (hσ.tBar i j) p k (f / 2) h.config.prime h.config.ne_two hk
    hE hZc htN ht2 htc hlie
  refine ⟨hm2, ?_⟩
  rcases hcase with ⟨B, hB, hZB, A, hAB, hA, hA8⟩ | hgraph
  · exact (hσ.not_inner_of_lemma47 hKG i j (hB.trans inf_le_right) hZB hAB hA hA8).elim
  · exact hgraph

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
