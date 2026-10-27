module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFiveMain
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Fusion

open SectionSix Involution

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem hyp71_of_conj (hC : Counterexample G D r Abar) {a : G} (ha2 : orderOf a = 2)
    (haC : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (D : Set G)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G))
    (hag : g⁻¹ * a * g ∈ Subgroup.normalizer (D : Set G)) : Hyp71 D (g⁻¹ * a * g) g where
  mem := hag
  orderOf_eq := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) a
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ha2]
  centralizer_le := by
    intro x hx
    rw [mem_rightConjugate_iff]
    apply haC
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [hx]
      _ = a * (g * x * g⁻¹) := by group
  ne := fun h => hg ((rightConjugate_normalizer_eq_iff hC.hyp g).mp h)

theorem lemma_8_1 (hin : SectionSevenInputs) (hC : Counterexample G D r Abar) {a : G}
    (ha2 : orderOf a = 2) {i : Fin r}
    (hai : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) a) :
    (∀ g : G, a ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g ↔
        g ∈ Subgroup.normalizer (D : Set G)) ∨
      (r = 2 ∧ (∀ k, 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k))) ∧
        ∀ g : G, g ∉ Subgroup.normalizer (D : Set G) →
          g⁻¹ * a * g ∈ Subgroup.normalizer (D : Set G) → ∀ k,
            (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (g⁻¹ * a * g)).toMonoidHom ≠
              aschbacherThm5Preimage D (Abar k)) := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  have haC := centralizer_le_of_centralizes hC i (two_power_of_orderOf ha2) ha1 hai
  have haH : a ∈ Subgroup.normalizer (D : Set G) :=
    haC (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  by_cases hall : ∀ g : G, a ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g ↔
      g ∈ Subgroup.normalizer (D : Set G)
  · exact Or.inl hall
  right
  obtain ⟨g, hgH, hag⟩ : ∃ g : G, g ∉ Subgroup.normalizer (D : Set G) ∧
      a ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
    by_contra hno
    push Not at hno
    apply hall
    intro g
    constructor
    · intro hag
      by_contra hgH
      exact hno g hgH hag
    · intro hgH
      rw [mem_rightConjugate_iff]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH haH) (Subgroup.inv_mem _ hgH)
  have hg' : g⁻¹ ∉ Subgroup.normalizer (D : Set G) := fun h =>
    hgH (inv_inv g ▸ (Subgroup.normalizer (D : Set G)).inv_mem h)
  have hag' : (g⁻¹)⁻¹ * a * g⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    rw [inv_inv]
    exact (mem_rightConjugate_iff _ g a).mp hag
  obtain ⟨hr2, hrank⟩ :=
    r_eq_two_and_rank hin.toSectionSevenBase hC (hyp71_of_conj hC ha2 haC hg' hag')
  refine ⟨hr2, hrank, fun g' hg'H hag'H k => ?_⟩
  refine lemma_7_5 hin hC (hyp71_of_conj hC ha2 haC hg'H hag'H) ⟨i, ?_⟩ k
  have : g' * (g'⁻¹ * a * g') * g'⁻¹ = a := by group
  rw [this]
  exact hai

theorem false_of_isolated (hC : Counterexample G D r Abar) {z : G} (hz2 : orderOf z = 2)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hiso : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v)
    (huC : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (D : Set G))
    (huvC : Subgroup.centralizer ({u * v} : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    False := by
  let : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz hiso
  have hNK : N ≤ CFSG.oddCore G := le_sSup ⟨hNn, hNodd⟩
  have hcen : (QuotientGroup.mk z : G ⧸ CFSG.oddCore G) ∈
      Subgroup.center (G ⧸ CFSG.oddCore G) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := hNK (hN g⁻¹)
    rw [inv_inv, ← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one] at h1
    calc (QuotientGroup.mk g : G ⧸ CFSG.oddCore G) * QuotientGroup.mk z
        = QuotientGroup.mk g * ((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk z *
            QuotientGroup.mk g) := by rw [h1]
      _ = QuotientGroup.mk z * QuotientGroup.mk g := by group
  have hKodd : Odd (Nat.card (CFSG.pPrimeCore 2 G)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  have hKH : CFSG.pPrimeCore 2 G ≤ Subgroup.normalizer (D : Set G) := by
    have hKn : (CFSG.pPrimeCore 2 G).Normal := CFSG.pPrimeCore_normal
    have hgen :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.four_group_odd_centralizer_generation
        (CFSG.pPrimeCore 2 G) u v hu hv huv hne hKodd (by
          rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
          exact le_top)
    rw [hgen]
    exact sup_le (sup_le (inf_le_right.trans huC) (inf_le_right.trans hvC))
      (inf_le_right.trans huvC)
  have hOK : CFSG.oddCore G ≤ CFSG.pPrimeCore 2 G :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  apply hC.proper
  apply eq_top_iff.mpr
  intro g _
  obtain ⟨c, hc, k, hk, rfl⟩ := CFSG.Adapters.eq_centralizer_mul_oddCore hzz hcen g
  exact Subgroup.mul_mem _ (hzC hc) (hKH (hOK hk))

theorem lemma_8_3 (hin : SectionSevenInputs) (hC : Counterexample G D r Abar) (k : Fin r) :
    2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 := hin.lemma_8_2 hC
  have hyp := hC.hyp
  by_contra hlt
  push Not at hlt
  have hrk : CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) ≤ 1 := by omega
  obtain ⟨c, hc⟩ := exists_rankOneFactors hin.toSectionSevenBase hC hrk
  have hrank : ∀ l, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar l)) ≤ 1 := by
    intro l
    obtain ⟨x, -, hxl⟩ := hin.lemma_6_3 hC k l
    rw [← hxl, pRank_map_conj]
    exact hrk
  have hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j := by
    intro i j m hij hmi
    rw [Ne, Fin.ext_iff] at hij hmi
    rw [Fin.ext_iff]
    omega
  obtain ⟨i, j, hij, hcij⟩ : ∃ i j : Fin r, i ≠ j ∧ c i ≠ c j := by
    by_contra hno
    push Not at hno
    apply hC.fails
    refine conclusion_of_rankOne hyp hr2 hc (fun k l => ?_) hrank
    by_cases hkl : k = l
    · rw [hkl]
    · exact hno k l hkl
  have hcc : c i * c j = c j * c i :=
    commute_of_mem_centralizer_all hyp (fun m => c_mem_centralizer hyp hc i m) (c j)
  have hcii : c i * c i = 1 := by rw [← pow_two, ← hc.orderOf_eq i, pow_orderOf_eq_one]
  have hcjj : c j * c j = 1 := by rw [← pow_two, ← hc.orderOf_eq j, pow_orderOf_eq_one]
  obtain ⟨W, -, hW4, hWV⟩ := exists_fourGroup_lift (aschbacherThm5OddCore D) (oddCore_odd D)
    (C := ⊤) (isFourGroup_fourGroupOfPair (hc.orderOf_eq i) (hc.orderOf_eq j) hcc hcij)
    (by
      intro v _
      obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) v
      exact ⟨d, Subgroup.mem_top d, rfl⟩)
  have hci : c i ∈ W.map (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [hWV]
    exact Or.inr (Or.inl rfl)
  have hcj : c j ∈ W.map (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [hWV]
    exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨w₁, hw₁, hw₁c⟩ := hci
  obtain ⟨w₂, hw₂, hw₂c⟩ := hcj
  have hWc := hW4.1.1
  have hw12 : w₁ * w₂ = w₂ * w₁ := congrArg Subtype.val (mul_comm' (⟨w₁, hw₁⟩ : W) ⟨w₂, hw₂⟩)
  have horder : ∀ w ∈ W, ∀ x : D ⧸ aschbacherThm5OddCore D,
      QuotientGroup.mk' (aschbacherThm5OddCore D) w = x → orderOf x = 2 →
      orderOf (w : G) = 2 := by
    intro w hw x hwx hx2
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime (hW4.1.2 w hw)
    rintro rfl
    rw [map_one] at hwx
    rw [← hwx, orderOf_one] at hx2
    omega
  set a₁ : G := (w₁ : G)
  set a₂ : G := (w₂ : G)
  have ha₁ : a₁ ∈ aschbacherThm5Preimage D (Abar i) :=
    (mem_preimage_iff D _ w₁).mpr (by rw [hw₁c]; exact hc.mem i)
  have ha₂ : a₂ ∈ aschbacherThm5Preimage D (Abar j) :=
    (mem_preimage_iff D _ w₂).mpr (by rw [hw₂c]; exact hc.mem j)
  have ha₁2 : orderOf a₁ = 2 := horder w₁ hw₁ _ hw₁c (hc.orderOf_eq i)
  have ha₂2 : orderOf a₂ = 2 := horder w₂ hw₂ _ hw₂c (hc.orderOf_eq j)
  have ha12 : a₁ * a₂ = a₂ * a₁ := congrArg Subtype.val hw12
  have hne : a₁ ≠ a₂ := by
    intro heq
    apply hcij
    rw [← hw₁c, ← hw₂c]
    exact congrArg _ (Subtype.ext heq)
  have ha₁sq : a₁ * a₁ = 1 := by rw [← pow_two, ← ha₁2, pow_orderOf_eq_one]
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two, ← ha₂2, pow_orderOf_eq_one]
  obtain ⟨z, hz⟩ : ∃ z : G, z = a₁ * a₂ := ⟨_, rfl⟩
  have hzD : z ∈ D := hz ▸ D.mul_mem w₁.2 w₂.2
  have hzq : QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨z, hzD⟩ : D) = c i * c j := by
    rw [← hw₁c, ← hw₂c, ← map_mul]
    congr 1
    exact Subtype.ext hz
  have hz2 : orderOf z = 2 := by
    rw [hz]
    apply orderOf_eq_prime
    · rw [pow_two]
      calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [ha12]
        _ = (a₁ * a₁) * (a₂ * a₂) := by group
        _ = 1 := by rw [ha₁sq, ha₂sq, one_mul]
    · intro h1
      apply hne
      calc a₁ = a₁ * (a₂ * a₂) := by rw [ha₂sq, mul_one]
        _ = (a₁ * a₂) * a₂ := by group
        _ = a₂ := by rw [h1, one_mul]
  have hzi : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i))
      z := by
    apply (centralizes_iff_mem_centralizer_quotient (Abar i) ⟨z, hzD⟩).mpr
    rw [hzq]
    exact Subgroup.mul_mem _ (c_mem_centralizer hyp hc i i) (c_mem_centralizer hyp hc j i)
  have hz1 : z ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hz2
    omega
  have hzC := centralizer_le_of_centralizes hC i (two_power_of_orderOf hz2) hz1 hzi
  have h81 : ∀ g : G, z ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g ↔
      g ∈ Subgroup.normalizer (D : Set G) := by
    rcases lemma_8_1 hin hC hz2 hzi with h | ⟨-, hr, -⟩
    · exact h
    · exact absurd (hr k) (by omega)
  have hiso : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hcomm
    have htH : g * z * g⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      hzC (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    have hgH : g ∈ Subgroup.normalizer (D : Set G) :=
      (h81 g).mp ((mem_rightConjugate_iff _ g z).mpr htH)
    have htD : g * z * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgH z).mp hzD
    obtain ⟨i', hi'⟩ := hyp.hperm g hgH i
    obtain ⟨j', hj'⟩ := hyp.hperm g hgH j
    have hσi := onQuotient_c hc ⟨g, hgH⟩ hi'
    have hσj := onQuotient_c hc ⟨g, hgH⟩ hj'
    have hi'j' : i' ≠ j' := by
      rintro rfl
      apply hij
      apply hyp.hdistinct
      apply preimage_injective D
      apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [hi', hj']
    have hfix : onQuotient D ⟨g, hgH⟩ (c i * c j) = c i * c j := by
      rw [map_mul, hσi, hσj]
      by_cases hii : i' = i
      · rw [hii, hfin i j j' hij (by rw [← hii]; exact hi'j'.symm)]
      · rw [hfin i j i' hij hii, hfin j i j' hij.symm (by
          intro h
          rw [h] at hi'j'
          exact hi'j' (hfin i j i' hij hii))]
        exact hcc.symm
    have htq : QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨g * z * g⁻¹, htD⟩ : D) =
        QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨z, hzD⟩ : D) := by
      rw [hzq, ← hfix, ← hzq, onQuotient_mk]
      rfl
    have ho : (⟨z, hzD⟩ : D)⁻¹ * ⟨g * z * g⁻¹, htD⟩ ∈ aschbacherThm5OddCore D :=
      QuotientGroup.eq.mp htq.symm
    set o : D := (⟨z, hzD⟩ : D)⁻¹ * ⟨g * z * g⁻¹, htD⟩ with hodef
    have hzinv : z⁻¹ = z := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz2, pow_orderOf_eq_one]
    have ho2 : o ^ 2 = 1 := by
      apply Subtype.ext
      change (z⁻¹ * (g * z * g⁻¹)) ^ 2 = 1
      rw [hzinv, pow_two]
      have htt : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
        calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
          _ = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]; group
      calc z * (g * z * g⁻¹) * (z * (g * z * g⁻¹)) =
          z * ((g * z * g⁻¹) * z) * (g * z * g⁻¹) := by group
        _ = z * (z * (g * z * g⁻¹)) * (g * z * g⁻¹) := by rw [hcomm]
        _ = (z * z) * ((g * z * g⁻¹) * (g * z * g⁻¹)) := by group
        _ = 1 := by rw [htt, ← pow_two, ← hz2, pow_orderOf_eq_one, one_mul]
    have ho1 : o = 1 := by
      have hdvd := orderOf_dvd_of_pow_eq_one ho2
      have hodd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) ho
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact orderOf_eq_one_iff.mp h1
      · rw [h2] at hodd
        exact absurd (even_iff_two_dvd.mpr hodd) (Nat.not_even_iff_odd.mpr (oddCore_odd D))
    have := congrArg Subtype.val ho1
    change z⁻¹ * (g * z * g⁻¹) = 1 at this
    rw [inv_mul_eq_one] at this
    exact this.symm
  exact false_of_isolated hC hz2 hzC hiso ha₁2 ha₂2 ha12 hne
    (centralizer_le_of_mem_factor hC ha₁ (two_power_of_orderOf ha₁2) (by
      rintro h; rw [h, orderOf_one] at ha₁2; omega))
    (centralizer_le_of_mem_factor hC ha₂ (two_power_of_orderOf ha₂2) (by
      rintro h; rw [h, orderOf_one] at ha₂2; omega)) (hz ▸ hzC)

end Fusion

end CFSG.ComponentClassification.AschbacherTheorem5
