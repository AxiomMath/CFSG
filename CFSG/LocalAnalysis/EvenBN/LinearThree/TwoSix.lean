module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26
public import CFSG.CGT.Timmesfeld75.StronglyClosedSimple

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (Datum)
open scoped MatrixGroups

namespace TwoSix

theorem card_ker_le {K : Type*} [Field K] [Finite K] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0) :
    Nat.card {v : Fin 2 → K // N *ᵥ v = 0} ≤ Nat.card K := by
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (Matrix.ext h)
  have hrow : ∀ v : Fin 2 → K, N *ᵥ v = 0 → N i 0 * v 0 + N i 1 * v 1 = 0 := fun v hv => by
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  let k : Fin 2 := if j = 0 then 1 else 0
  have hinj : Function.Injective (fun v : {v : Fin 2 → K // N *ᵥ v = 0} => v.1 k) := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    simp only at h
    apply Subtype.ext
    have hv' := hrow v hv
    have hw' := hrow w hw
    fin_cases j
    ·
      have hk : k = 1 := rfl
      rw [hk] at h
      have h0 : v 0 = w 0 := by
        have : N i 0 * (v 0 - w 0) = 0 := by linear_combination hv' - hw' - N i 1 * h
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
      ext a; fin_cases a
      · exact h0
      · exact h
    · have hk : k = 0 := rfl
      rw [hk] at h
      have h1 : v 1 = w 1 := by
        have : N i 1 * (v 1 - w 1) = 0 := by linear_combination hv' - hw' - N i 0 * h
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
      ext a; fin_cases a
      · exact h
      · exact h1
  exact Nat.card_le_card_of_injective _ hinj

theorem le_card_fix {G : Type*} [Group G] [Finite G] {V : Subgroup G} {q : ℕ}
    (hV : IsElemAbelian 2 V) (hcard : Nat.card V = q ^ 2) {s : G} (hs2 : s * s = 1)
    (hsV : s ∈ normalizer (V : Set G)) : q ≤ Nat.card ↥(V ⊓ centralizer ({s} : Set G)) := by
  have h1 := OddStandard.Seitz77.Sec26.card_commutator_mul_card_centralizer hV hsV hs2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hle : ⁅V, zpowers s⁆ ≤ V ⊓ centralizer ({s} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    rcases OddStandard.Seitz77.Sec26.zpow_involution hs2 k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact one_mem _
    · rw [hk, commutatorElement_def]
      have hsv : s * v⁻¹ * s⁻¹ ∈ V := (mem_normalizer_iff.mp hsV _).mp (inv_mem hv)
      have hmem : v * s * v⁻¹ * s⁻¹ ∈ V := by
        rw [show v * s * v⁻¹ * s⁻¹ = v * (s * v⁻¹ * s⁻¹) by group]
        exact mul_mem hv hsv
      refine ⟨hmem, mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 : (v * s * v⁻¹ * s⁻¹) * (v * s * v⁻¹ * s⁻¹) = 1 := by
        rw [← sq]; exact hV.2 _ hmem
      have h3 : s * (v * s * v⁻¹ * s⁻¹) * s⁻¹ = (v * s * v⁻¹ * s⁻¹)⁻¹ := by
        rw [hsinv]
        calc s * (v * s * v⁻¹ * s) * s = s * v * (s * v⁻¹) * (s * s) := by group
          _ = s * v * (s * v⁻¹) := by rw [hs2, mul_one]
          _ = (v * s * v⁻¹ * s)⁻¹ := by
            rw [show (v * s * v⁻¹ * s)⁻¹ = s⁻¹ * v * s⁻¹ * v⁻¹ by group, hsinv]
            group
      rw [inv_eq_of_mul_eq_one_right h2] at h3
      calc v * s * v⁻¹ * s⁻¹ * s = s * (v * s * v⁻¹ * s⁻¹) * s⁻¹ * s := by rw [h3]
        _ = s * (v * s * v⁻¹ * s⁻¹) := by group
  have h4 := Subgroup.card_le_of_le hle
  have h5 : q ^ 2 ≤ Nat.card ↥(V ⊓ centralizer ({s} : Set G)) ^ 2 := by
    rw [← hcard, ← h1, sq]
    exact Nat.mul_le_mul_right _ h4
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5

theorem le_of_dvd_count {m k f b : ℕ} (hm : 0 < m) (hf : 1 ≤ f) (hk : k = 2 ^ b)
    (hdvd : m * k ∣ m * (2 ^ f) ^ 2 + (m * k - m) * 2 ^ f) : k ≤ 2 ^ f := by
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_two_pow
  have e : m * (2 ^ f) ^ 2 + (m * k - m) * 2 ^ f =
      m * (2 ^ f * (2 ^ f - 1) + k * 2 ^ f) := by
    have h1 : m * k - m = m * (k - 1) := by rw [Nat.mul_sub, mul_one]
    rw [h1]
    zify [hq, hk1, Nat.le_mul_of_pos_right m hk1]
    ring
  rw [e] at hdvd
  have h2 := Nat.dvd_of_mul_dvd_mul_left hm hdvd
  have h3 : k ∣ 2 ^ f * (2 ^ f - 1) := (Nat.dvd_add_left (dvd_mul_right k _)).mp h2
  have hodd : Odd (2 ^ f - 1) := by
    have : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
    rcases this with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime k (2 ^ f - 1) := by
    rw [hk]
    exact Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hodd)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h3)

theorem relIndex_le_of_card_fix {G : Type*} [Group G] [Finite G] {V B X : Subgroup G} {f : ℕ}
    (hf : 1 ≤ f) (hB : IsPGroup 2 B) (hBV : B ≤ normalizer (V : Set G))
    (hcard : Nat.card V = (2 ^ f) ^ 2)
    (hX : ∀ b ∈ B, b ∈ X → b ∈ centralizer (V : Set G))
    (hfix : ∀ b ∈ B, b ∉ X → Nat.card ↥(V ⊓ centralizer ({b} : Set G)) = 2 ^ f) :
    X.relIndex B ≤ 2 ^ f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction B V :=
    { smul := fun b v => ⟨b * v * (b : G)⁻¹, (mem_normalizer_iff.mp (hBV b.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext
        (show ((1 : B) : G) * v * ((1 : B) : G)⁻¹ = v by simp)
      mul_smul := fun b c v => Subtype.ext
        (show ((b * c : B) : G) * v * ((b * c : B) : G)⁻¹ = b * (c * v * (c : G)⁻¹) * (b : G)⁻¹ by
          simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group) }
  have hsmul : ∀ (b : B) (v : V), ((b • v : V) : G) = b * v * (b : G)⁻¹ := fun _ _ => rfl
  have : Fintype B := Fintype.ofFinite B
  have : Fintype V := Fintype.ofFinite V
  have hfixcard : ∀ b : B, Fintype.card (MulAction.fixedBy V b) =
      if (b : G) ∈ X then (2 ^ f) ^ 2 else 2 ^ f := by
    intro b
    have e : MulAction.fixedBy V b ≃ ↥(V ⊓ centralizer ({(b : G)} : Set G)) :=
      { toFun := fun v => ⟨v.1, v.1.2, mem_centralizer_singleton_iff.mpr (by
          have h1 : ((b • v.1 : V) : G) = v.1 := congrArg Subtype.val v.2
          rw [hsmul] at h1
          calc ((v.1 : V) : G) * b = b * v.1 * (b : G)⁻¹ * b := by rw [h1]
            _ = b * v.1 := by group)⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (by
          rw [hsmul]
          have h1 := mem_centralizer_singleton_iff.mp v.2.2
          show (b : G) * v.1 * (b : G)⁻¹ = v.1
          rw [← h1, mul_inv_cancel_right])⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    split_ifs with hbX
    · have hle : V ≤ V ⊓ centralizer ({(b : G)} : Set G) := fun v hv =>
        ⟨hv, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hX b b.2 hbX) v hv)⟩
      rw [inf_eq_left.mpr (le_trans hle inf_le_right), hcard]
    · exact hfix b b.2 hbX
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B V
  simp only [hfixcard] at hburn
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hburn
  set m := (Finset.univ.filter fun b : B => (b : G) ∈ X).card with hm
  have hm' : m = Nat.card (X.subgroupOf B) := by
    rw [hm, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  have hn : (Finset.univ.filter fun b : B => (b : G) ∉ X).card = Fintype.card B - m := by
    rw [hm, ← Finset.card_compl, Finset.compl_filter]
  rw [hn] at hburn
  have hBc : Fintype.card B = m * X.relIndex B := by
    rw [← Nat.card_eq_fintype_card, hm', Subgroup.relIndex, Subgroup.card_mul_index]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hB
  have hkdvd : X.relIndex B ∣ 2 ^ a := by
    rw [← ha, Nat.card_eq_fintype_card, hBc]
    exact dvd_mul_left _ _
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
  have hm0 : 0 < m := by
    rw [hm']
    exact Nat.card_pos
  refine le_of_dvd_count hm0 hf hb ?_
  rw [← hBc]
  exact ⟨_, by rw [hburn, mul_comm]⟩

open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate rightConjugate_card)

theorem weak_closure {G : Type} [Group G] [Finite G] {S W V₁ : Subgroup G} {t : G} {q : ℕ}
    (hq : 4 ≤ q) (hSN : S ≤ normalizer (W : Set G)) (hW : IsElemAbelian 2 W)
    (hcardW : Nat.card W = q ^ 4) (htS : t ∈ S) (ht2 : t * t = 1)
    (hCt : W ⊓ centralizer ({t} : Set G) = V₁) (hcardV₁ : Nat.card V₁ = q ^ 2)
    (hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers t → s * s = 1 →
      Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ q ^ 2)
    (hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 2 * q) :
    ∀ g : G, rightConjugate W g ≤ S → rightConjugate W g = W := by
  intro g hgS
  set U := rightConjugate W g with hU
  have hUel : IsElemAbelian 2 U := isElemAbelian_map _ hW
  have hcardU : Nat.card U = q ^ 4 := by rw [hU, rightConjugate_card, hcardW]
  have hbig : q ^ 2 < Nat.card ↥(W ⊓ U) := by
    have h := Subgroup.relIndex_mul_card (H := W) (K := U)
    rw [hcardU] at h
    by_contra hle
    push Not at hle
    have h1 : W.relIndex U * Nat.card ↥(W ⊓ U) ≤ 2 * q * q ^ 2 :=
      Nat.mul_le_mul (hR1 U hgS hUel) hle
    have h2 : 2 * q * q ^ 2 < q ^ 4 := by
      have : 2 * q < q ^ 2 := by nlinarith
      calc 2 * q * q ^ 2 < q ^ 2 * q ^ 2 := by
            exact Nat.mul_lt_mul_of_pos_right this (by positivity)
        _ = q ^ 4 := by ring
    omega
  have hcent : ∀ u ∈ U, W ⊓ U ≤ centralizer ({u} : Set G) := by
    intro u hu x hx
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_isElemAbelian hUel hu hx.2).symm
  have hUY : ∀ u ∈ U, u ∈ W ⊔ zpowers t := by
    intro u hu
    by_contra hnY
    have h1 := hR2 u (hgS hu) hnY (by rw [← sq]; exact hUel.2 u hu)
    have h2 : Nat.card ↥(W ⊓ U) ≤ Nat.card ↥(W ⊓ centralizer ({u} : Set G)) :=
      Subgroup.card_le_of_le (le_inf inf_le_left (hcent u hu))
    omega
  have hUW : U ≤ W := by
    intro u hu
    by_contra huW
    have hle : W ⊓ U ≤ W ⊓ centralizer ({t} : Set G) :=
      (le_inf inf_le_left (hcent u hu)).trans
        (OddStandard.Seitz77.Sec26.inf_centralizer_le_of_mem_sup hW (hSN htS) ht2 (hUY u hu)
          huW)
    have h4 := Subgroup.card_le_of_le (hCt ▸ hle)
    omega
  exact Subgroup.eq_of_le_of_card_ge hUW (by rw [hcardU, hcardW])

theorem core {G : Type} [Group G] [Finite G] {S W V₁ : Subgroup G} {t : G} {q : ℕ}
    (hq : 4 ≤ q) (hS : IsSylowOf 2 S (normalizer (W : Set G))) (hWS : W ≤ S)
    (hW : IsElemAbelian 2 W) (hcardW : Nat.card W = q ^ 4) (htS : t ∈ S) (ht2 : t * t = 1)
    (htW : t ∉ W) (hCt : W ⊓ centralizer ({t} : Set G) = V₁) (hcardV₁ : Nat.card V₁ = q ^ 2)
    (hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers t → s * s = 1 →
      Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ q ^ 2)
    (hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 2 * q)
    (hA : ∀ (T : Sylow 2 G) (A : Subgroup G), A ≠ ⊥ → A ≤ (T : Subgroup G) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) →
      ∀ x ∈ (T : Subgroup G), x * x = 1 → x ∈ A) :
    False := by
  have hSN : S ≤ normalizer (W : Set G) := hS.le
  have hweak := weak_closure hq hSN hW hcardW htS ht2 hCt hcardV₁ hR2 hR1
  obtain ⟨T, hT⟩ := OddStandard.Seitz77.Sec26.exists_sylow_eq_of_isSylowOf_top
    (OddStandard.Seitz77.Sec26.isSylowOf_top_of_weakly_closed hS hWS hweak)
  subst hT
  have hlow : ∀ x ∈ (T : Subgroup G), x ∉ W → x * x = 1 →
      2 * q < Nat.card ↥⁅W, zpowers x⁆ := by
    intro x hxT hxW hx2
    have hcard := OddStandard.Seitz77.Sec26.card_commutator_mul_card_centralizer hW
      (hSN hxT) hx2
    have hC : Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ q ^ 2 := by
      by_cases hxY : x ∈ W ⊔ zpowers t
      · have hle := OddStandard.Seitz77.Sec26.inf_centralizer_le_of_mem_sup hW (hSN htS) ht2
          hxY hxW
        have := Subgroup.card_le_of_le (hCt ▸ hle)
        omega
      · exact hR2 x hxT hxY hx2
    rw [hcardW] at hcard
    by_contra hle
    push Not at hle
    have h1 := Nat.mul_le_mul hle hC
    have h2 : 2 * q * q ^ 2 < q ^ 4 := by
      have : 2 * q < q ^ 2 := by nlinarith
      calc 2 * q * q ^ 2 < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right this (by positivity)
        _ = q ^ 4 := by ring
    omega
  have hclosed := OddStandard.Seitz77.Sec26.stronglyClosed_of_cor4 T W hWS hW hweak (2 * q)
    (fun B hB hBel => hR1 B hB hBel) hlow
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardW
    have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  exact htW (hA T W hWne hWS (fun a ha b hb => comm_of_isElemAbelian hW ha hb) hclosed t htS ht2)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem card_fix_le (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) {c : G}
    (hcA : c ∈ normalizer (A : Set G)) (hcV : c ∈ normalizer (Vi : Set G))
    (hc : ∃ v ∈ Vi, c * v * c⁻¹ ≠ v) :
    Nat.card ↥(Vi ⊓ centralizer ({c} : Set G)) ≤ 2 ^ f := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := h.exists_model
  have hR' : Radicals d.V V₁ V₂ (Nat.card K) := hK ▸ hR
  obtain ⟨hWV, hWe, -⟩ := hR.property hW
  have hf1 : 1 ≤ f := by have := h.three_le; omega
  rw [← hK]
  by_cases hin : c ∈ A ⊔ centralizer (A : Set G)
  · obtain ⟨a, ha, k, hk, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a ha) hin
    have hkv : ∀ v ∈ Vi, a * k * v * (a * k)⁻¹ = a * v * a⁻¹ := fun v hv => by
      have h1 : k * v = v * k := (mem_centralizer_iff.mp hk v (hWV hv).2).symm
      calc a * k * v * (a * k)⁻¹ = a * (k * v) * k⁻¹ * a⁻¹ := by group
        _ = a * v * a⁻¹ := by rw [h1]; group
    have haN : a ∈ normalizer (Vi : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun v hv => ?_
      rw [← hkv v hv]
      exact (mem_normalizer_iff.mp hcV v).mp hv
    obtain ⟨D⟩ := exists_leviData e d.V_isSylow hR' hW
    obtain ⟨c₀, M, hM⟩ := D.exists_actsBy ⟨ha, haN⟩
    set N : Matrix (Fin 2) (Fin 2) K := (c₀ : K) • (M : Matrix (Fin 2) (Fin 2) K) - 1 with hN
    have hNv : ∀ v : Fin 2 → K, N *ᵥ v = (c₀ : K) • (M • v) - v := fun v => by
      rw [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    have hfixv : ∀ v : Fin 2 → K, a * D.ι (Multiplicative.ofAdd v) * a⁻¹ =
        D.ι (Multiplicative.ofAdd v) ↔ N *ᵥ v = 0 := fun v => by
      rw [hM v, hNv, sub_eq_zero]
      exact ⟨fun h1 => Multiplicative.ofAdd.injective (D.ι_injective h1), fun h1 => by rw [h1]⟩
    have hN0 : N ≠ 0 := by
      obtain ⟨v, hv, hne⟩ := hc
      obtain ⟨w, rfl⟩ : v ∈ D.ι.range := by rw [D.range_ι]; exact hv
      intro h0
      apply hne
      rw [hkv _ hv]
      exact (hfixv (Multiplicative.toAdd w)).mpr (by rw [h0, Matrix.zero_mulVec])
    refine (Nat.card_le_card_of_surjective
      (fun v : {v : Fin 2 → K // N *ᵥ v = 0} =>
        (⟨D.ι (Multiplicative.ofAdd v.1), D.ι_mem_W _, mem_centralizer_singleton_iff.mpr (by
          have h1 := (hfixv v.1).mpr v.2
          rw [← hkv _ (D.ι_mem_W _)] at h1
          calc D.ι (Multiplicative.ofAdd v.1) * (a * k) =
              (a * k) * D.ι (Multiplicative.ofAdd v.1) * (a * k)⁻¹ * (a * k) := by rw [h1]
            _ = (a * k) * D.ι (Multiplicative.ofAdd v.1) := by group)⟩ :
          ↥(Vi ⊓ centralizer ({a * k} : Set G)))) ?_).trans (TwoSix.card_ker_le hN0)
    rintro ⟨x, hxV, hxC⟩
    obtain ⟨w, rfl⟩ : x ∈ D.ι.range := by rw [D.range_ι]; exact hxV
    refine ⟨⟨Multiplicative.toAdd w, (hfixv _).mp ?_⟩, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp hxC
    simp only [ofAdd_toAdd]
    rw [← hkv _ hxV, ← h1, mul_inv_cancel_right]
  · have hxi : act e ⟨c, hcA⟩ ∉
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
      fun h1 => hin ((act_mem_range_iff e hcA).mp h1)
    let ιA : projectiveSL 3 K →* G := A.subtype.comp e.symm.toMonoidHom
    have hιA : Function.Injective ιA := A.subtype_injective.comp e.symm.injective
    set F := (Vi ⊓ centralizer ({c} : Set G)).comap ιA with hF
    have hFel : IsElemAbelian 2 F := isElemAbelian_comap hιA (IsElemAbelian.mono hWe inf_le_left)
    have hfix : ∀ p ∈ F, act e ⟨c, hcA⟩ p = p := by
      intro p hp
      have h1 := mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hp).2
      have h2 := (act_apply_eq_iff e ⟨c, hcA⟩ (e.symm p)).mpr h1.symm
      rwa [MulEquiv.apply_symm_apply] at h2
    have hle : Vi ⊓ centralizer ({c} : Set G) ≤ (⊤ : Subgroup (projectiveSL 3 K)).map ιA := by
      intro x hx
      refine ⟨e ⟨x, (hWV hx.1).2⟩, trivial, ?_⟩
      simp [ιA]
    have hcard : Nat.card F = Nat.card ↥(Vi ⊓ centralizer ({c} : Set G)) := by
      conv_rhs => rw [eq_map_comap_of_le hle]
      rw [Subgroup.card_map_of_injective hιA]
    rw [← hcard]
    exact card_le_of_forall_fix hf1 hK hFel hfix hxi

theorem card_fix_le_of_mem_normalizer (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {s : G}
    (hs : s ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))
    (hsX : s ∉ w.W ⊔ zpowers d.t) :
    Nat.card ↥(Vi ⊓ centralizer ({s} : Set G)) ≤ 2 ^ f := by
  have hsV := h.normalizer_adj_le d hR hW hs
  have ht' : s * d.t * s⁻¹ ∈ Vi ⊔ zpowers d.t :=
    (mem_normalizer_iff.mp hs d.t).mp (mem_sup_right (mem_zpowers _))
  have htV : s * d.t * s⁻¹ ∉ Vi := fun h1 => by
    have h2 := (mem_normalizer_iff.mp hsV d.t).mpr h1
    exact w.t_not_mem (w.le_W h2)
  have hv := (w.mem_adj_iff.mp ht').resolve_left htV
  obtain ⟨x, hxW, hxv⟩ := w.comm_onto _ hv
  have hxX : x ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer (Vi : Set G) := by
    rw [← h.sup_eq d hR hW w]; exact mem_sup_left hxW
  have hvt := mem_centralizer_singleton_iff.mp (w.le_centralizer_t hv)
  have hxt : x * d.t * x⁻¹ = s * d.t * s⁻¹ := by
    calc x * d.t * x⁻¹ = d.t * (d.t * x * d.t * x⁻¹) := by
          rw [show d.t * (d.t * x * d.t * x⁻¹) = (d.t * d.t) * x * d.t * x⁻¹ by group,
            d.t_mul_self, one_mul]
      _ = d.t * (s * d.t * s⁻¹ * d.t) := by rw [hxv]
      _ = s * d.t * s⁻¹ * d.t * d.t := hvt.symm
      _ = s * d.t * s⁻¹ := by rw [mul_assoc _ d.t d.t, d.t_mul_self, mul_one]
  set c := x⁻¹ * s with hc
  have hct : c ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, hc]
    calc x⁻¹ * s * d.t = x⁻¹ * (s * d.t * s⁻¹) * s := by group
      _ = x⁻¹ * (x * d.t * x⁻¹) * s := by rw [hxt]
      _ = d.t * (x⁻¹ * s) := by group
  have hcA : c ∈ normalizer (A : Set G) := (OddStandard.centralizer_t_facts d.sector).1 hct
  have hxV : x ∈ normalizer (Vi : Set G) := h.normalizer_adj_le d hR hW hxX.1
  have hcV : c ∈ normalizer (Vi : Set G) := mul_mem (inv_mem hxV) hsV
  have hcs : ∀ v ∈ Vi, c * v * c⁻¹ = s * v * s⁻¹ := fun v hv => by
    have h1 : s * v * s⁻¹ ∈ Vi := (mem_normalizer_iff.mp hsV v).mp hv
    have h2 : x⁻¹ * (s * v * s⁻¹) * x = s * v * s⁻¹ := by
      rw [mul_assoc, mem_centralizer_iff.mp hxX.2 _ h1, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hc, ← h2]; group
  have heq : Vi ⊓ centralizer ({c} : Set G) = Vi ⊓ centralizer ({s} : Set G) := by
    ext v
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hv, hvc⟩
      refine ⟨hv, ?_⟩
      have h1 := hcs v hv
      rw [← hvc, mul_inv_cancel_right] at h1
      calc v * s = s * v * s⁻¹ * s := by rw [← h1]
        _ = s * v := by group
    · rintro ⟨hv, hvs⟩
      refine ⟨hv, ?_⟩
      have h1 := hcs v hv
      rw [← hvs, mul_inv_cancel_right] at h1
      calc v * c = c * v * c⁻¹ * c := by rw [h1]
        _ = c * v := by group
  rw [← heq]
  refine card_fix_le h d hR hW hcA hcV ?_
  by_contra hcon
  push Not at hcon
  apply hsX
  rw [h.sup_eq d hR hW w]
  refine ⟨hs, mem_centralizer_iff.mpr fun v hv => ?_⟩
  have h1 := hcon v hv
  rw [hcs v hv] at h1
  calc v * s = s * v * s⁻¹ * s := by rw [h1]
    _ = s * v := by group

theorem card_centralizer_le (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {s : G}
    (hs : s ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))
    (hsX : s ∉ w.W ⊔ zpowers d.t) :
    Nat.card ↥(w.W ⊓ centralizer ({s} : Set G)) ≤ (2 ^ f) ^ 2 := by
  have hC := card_fix_le_of_mem_normalizer h d hR hW w hs hsX
  set T := w.W ⊓ centralizer ({s} : Set G) with hT
  have hTV : T ≤ centralizer (Vi : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun v hv => comm_of_isElemAbelian w.elem (w.le_W hv) hx.1
  have hTt : ∀ x ∈ T, d.t * (x * d.t * x⁻¹) ∈ Vi := fun x hx => by
    have := w.comm_mem x hx.1
    rwa [show d.t * x * d.t * x⁻¹ = d.t * (x * d.t * x⁻¹) by group] at this
  obtain ⟨φ, hφ⟩ := exists_commMap d.t_mul_self hTV hTt
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at hcard
  have hrange : Nat.card φ.range ≤ Nat.card ↥(Vi ⊓ centralizer ({s} : Set G)) := by
    let g : φ.range → ↥(Vi ⊓ centralizer ({s} : Set G)) := fun y => ⟨((y : Vi) : G), (y : Vi).2,
      by
        obtain ⟨x, hx⟩ := y.2
        rw [← hx, hφ]
        have hxs : s * (x : G) * s⁻¹ = x := by
          rw [← mem_centralizer_singleton_iff.mp x.2.2, mul_inv_cancel_right]
        have h1 := w.comm_conj hs x.2.1
        rw [hxs] at h1
        refine mem_centralizer_singleton_iff.mpr ?_
        rw [show d.t * ((x : G) * d.t * (x : G)⁻¹) = d.t * x * d.t * (x : G)⁻¹ by group]
        calc d.t * x * d.t * (x : G)⁻¹ * s = s * (d.t * x * d.t * (x : G)⁻¹) * s⁻¹ * s := by
              rw [h1]
          _ = s * (d.t * x * d.t * (x : G)⁻¹) := by group⟩
    exact Nat.card_le_card_of_injective g fun a b hab => by
      have := congrArg (fun z : ↥(Vi ⊓ centralizer ({s} : Set G)) => (z : G)) hab
      exact Subtype.ext (Subtype.ext this)
  have hker : Nat.card φ.ker ≤ Nat.card ↥(Vi ⊓ centralizer ({s} : Set G)) := by
    let g : φ.ker → ↥(Vi ⊓ centralizer ({s} : Set G)) := fun y => ⟨((y : T) : G), by
      have h1 : φ y = 1 := y.2
      have h2 : d.t * (((y : T) : G) * d.t * ((y : T) : G)⁻¹) = 1 := by
        rw [← hφ, h1]; rfl
      have h3 : ((y : T) : G) * d.t = d.t * ((y : T) : G) := by
        have h4 : ((y : T) : G) * d.t * ((y : T) : G)⁻¹ = d.t := by
          calc ((y : T) : G) * d.t * ((y : T) : G)⁻¹ =
              d.t * (d.t * (((y : T) : G) * d.t * ((y : T) : G)⁻¹)) := by
                rw [← mul_assoc, d.t_mul_self, one_mul]
            _ = d.t := by rw [h2, mul_one]
        calc ((y : T) : G) * d.t = ((y : T) : G) * d.t * ((y : T) : G)⁻¹ * (y : T) := by group
          _ = d.t * ((y : T) : G) := by rw [h4]
      have h5 : ((y : T) : G) ∈ w.W ⊓ centralizer ({d.t} : Set G) :=
        ⟨(y : T).2.1, mem_centralizer_singleton_iff.mpr h3⟩
      rw [w.fix] at h5
      exact ⟨h5, (y : T).2.2⟩⟩
    exact Nat.card_le_card_of_injective g fun a b hab => by
      have := congrArg (fun z : ↥(Vi ⊓ centralizer ({s} : Set G)) => (z : G)) hab
      exact Subtype.ext (Subtype.ext this)
  rw [hcard]
  calc Nat.card φ.range * Nat.card φ.ker ≤ 2 ^ f * 2 ^ f :=
        Nat.mul_le_mul (hrange.trans hC) (hker.trans hC)
    _ = (2 ^ f) ^ 2 := by ring

omit [Finite G] in
theorem _root_.CFSG.LocalAnalysis.EvenBN.LinearThree.WData.relIndex_sup {d : Datum A}
    {Vi : Subgroup G} {q : ℕ} (w : WData d Vi q) : w.W.relIndex (w.W ⊔ zpowers d.t) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨d.t, mem_sup_right (mem_zpowers _)⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  rcases w.mem_sup_iff.mp b.2 with hb | hb
  · refine Or.inr ⟨hb, fun h1 => w.t_not_mem ?_⟩
    have := mul_mem (inv_mem hb) h1
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨hb, fun h1 => w.t_not_mem ?_⟩
    have := mul_mem (inv_mem h1) hb
    rwa [inv_mul_cancel_left] at this

theorem relIndex_le (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f))
    {B : Subgroup G} (hBN : B ≤ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))
    (hB : IsElemAbelian 2 B) : w.W.relIndex B ≤ 2 * 2 ^ f := by
  obtain ⟨-, hVe, hVc⟩ := hR.property hW
  have hf1 : 1 ≤ f := by have := h.three_le; omega
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact hB.2 x x.2)⟩
  have hBV : B ≤ normalizer (Vi : Set G) := hBN.trans (h.normalizer_adj_le d hR hW)
  have hk : (w.W ⊔ zpowers d.t).relIndex B ≤ 2 ^ f := by
    refine TwoSix.relIndex_le_of_card_fix hf1 hB2 hBV hVc (fun b _ hbX => ?_)
      (fun b hb hbX => le_antisymm (card_fix_le_of_mem_normalizer h d hR hW w (hBN hb) hbX)
        (TwoSix.le_card_fix hVe hVc (by rw [← sq]; exact hB.2 b hb) (hBV hb)))
    rw [h.sup_eq d hR hW w] at hbX
    exact hbX.2
  have h1 := Subgroup.relIndex_inf_mul_relIndex w.W (w.W ⊔ zpowers d.t) B
  rw [inf_eq_left.mpr (le_sup_left : w.W ≤ w.W ⊔ zpowers d.t)] at h1
  have h2 : w.W.relIndex ((w.W ⊔ zpowers d.t) ⊓ B) ≤ 2 :=
    calc w.W.relIndex ((w.W ⊔ zpowers d.t) ⊓ B) ≤ w.W.relIndex (w.W ⊔ zpowers d.t) :=
          Subgroup.relIndex_le_of_le_right inf_le_left (by rw [w.relIndex_sup]; norm_num)
      _ = 2 := w.relIndex_sup
  rw [← h1]
  exact Nat.mul_le_mul h2 hk

theorem sup_le_of_isSylowOf (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f))
    {S : Subgroup G} (hS : IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))) :
    w.W ⊔ zpowers d.t ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) with hN
  have hXN : w.W ⊔ zpowers d.t ≤ N := by rw [h.sup_eq d hR hW w]; exact inf_le_left
  have hnorm : ((w.W ⊔ zpowers d.t).subgroupOf N).Normal := by
    refine ⟨fun x hx n => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    rw [h.sup_eq d hR hW w] at hx ⊢
    have hnV : (n : G) ∈ normalizer (Vi : Set G) := h.normalizer_adj_le d hR hW n.2
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem n.2 (Subgroup.mem_inf.mp hx).1) (inv_mem n.2),
      mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : (n : G)⁻¹ * v * n ∈ Vi := by
      have := (mem_normalizer_iff.mp (inv_mem hnV) v).mp hv
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ hv'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * ((n : G) * x * (n : G)⁻¹) = n * (((n : G)⁻¹ * v * n) * x) * (n : G)⁻¹ := by group
      _ = n * (x * ((n : G)⁻¹ * v * n)) * (n : G)⁻¹ := by rw [hc]
      _ = (n : G) * x * (n : G)⁻¹ * v := by group
  obtain ⟨Q, rfl⟩ := hS
  have : ((w.W ⊔ zpowers d.t).comap N.subtype).Normal := hnorm
  have hle := IsPGroup.le_sylow_of_normal (w.isPGroup_sup.comap_subtype (K := N)) Q
  intro x hx
  exact ⟨⟨x, hXN hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

end TwoSix

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem not_isSylowOf_normalizer (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974) (h : Hyp G A f)
    (d : Datum A) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {S : Subgroup G}
    (hS : IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))) :
    ¬ IsSylowOf 2 S (normalizer (w.W : Set G)) := fun hSW => by
  have := h.simple
  have hSE : S ≤ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) := hS.le
  have hXS := TwoSix.sup_le_of_isSylowOf h d hR hW w hS
  have hq : 4 ≤ 2 ^ f := by have := h.four_lt; omega
  exact TwoSix.core hq hSW (le_sup_left.trans hXS) w.elem w.card
    (hXS (mem_sup_right (mem_zpowers _))) d.t_mul_self w.t_not_mem w.fix (hR.property hW).2.2
    (fun s hs hsX _ => TwoSix.card_centralizer_le h d hR hW w (hSE hs) hsX)
    (fun B hB hBel => TwoSix.relIndex_le h d hR hW w (hB.trans hSE) hBel)
    (fun T _ hA1 hAT hAab hcl x hx hx2 =>
      CFSG.CGT.Timmesfeld75.stronglyClosed_contains_involutions hG h.nonab T hA1 hAT
        ⟨⟨fun a b => Subtype.ext (hAab a.1 a.2 b.1 b.2)⟩⟩ hcl x hx hx2)

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
