module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41FusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41E8K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49C
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_e8_comm {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI : IsMulCommutative E := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))

theorem l41_e8_inv {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a : G}
    (ha : a ∈ E) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 a ha)

theorem l41_e8_t_mem_S (h : L41GPh1 t L S x₁ x₂ lam rho) : t ∈ S :=
  h.basic.normal_W.1 (Subgroup.mem_sup_left h.hyp.mem_twoCore)

theorem l41_e8_fourGrp_le_ctxE (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
  rw [fourGrp]
  refine (Subgroup.closure_le (K := ctxE t x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with ha | ha
  · rw [ha]
    exact Subgroup.subset_closure (by simp)
  · rw [ha]
    exact Subgroup.subset_closure (by simp)

theorem l41_e8_fourGrp_le_ctxW (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxW t x₁ x₂ := by
  have hy : x₁ ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hz : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2
  rw [fourGrp]
  refine (Subgroup.closure_le (K := ctxW t x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with ha | ha
  · rw [ha]
    exact Subgroup.mem_sup_right hy
  · rw [ha]
    exact Subgroup.mem_sup_right hz

theorem l41_e8_card_S (h : L41GPh5 t L S x₁ x₂ lam rho) : Nat.card S = 2 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : twoCore t = zpowers t := h.p2
  have hord : orderOf t = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact t_mul_self h.hyp) (t_ne_one h.hyp)
  have h1 := h.basic.card_S
  rw [hp2, Nat.card_zpowers, hord] at h1
  rw [h1]
  norm_num

theorem l41_two_pow_nine_dvd (h : L41GPh5 t L S x₁ x₂ lam rho) : 2 ^ 9 ∣ Nat.card G := by
  have hW : Nat.card (ctxW t x₁ x₂) = 2 ^ 5 := by
    have hmul := Subgroup.relIndex_mul_card (H := ctxW t x₁ x₂) (K := S)
    rw [inf_eq_left.mpr h.basic.normal_W.1, h.basic.index_W, l41_e8_card_S h] at hmul
    norm_num at hmul ⊢
    omega
  have hV : Nat.card (l41V S t x₁ x₂) = 2 ^ 8 := by
    norm_num [h.normalizerFacts.card_V, hW]
  obtain ⟨i, hi⟩ := h.normalizerFacts.V_not_sylow
  rw [← Subgroup.card_mul_index (l41V S t x₁ x₂), hV, hi]
  exact ⟨i, by ring⟩

theorem l41_e8_no_conj (h : L41GPh5 t L S x₁ x₂ lam rho) {𝒮 : Sylow 2 G} {E : Subgroup G}
    (hE𝒮 : E ≤ (𝒮 : Subgroup G)) (hEn : (E.subgroupOf (𝒮 : Subgroup G)).Normal)
    (hEc : Nat.card E = 8) : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e := by
  intro g e he hge
  have hne1 : e ≠ 1 := by
    rintro rfl
    apply t_ne_one h.hyp
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hge]; group
  refine false_of_mem_normal_E8_of_le_two_pow 6 hE𝒮 hEn hEc (l41_two_pow_nine_dvd h) he hne1 ?_
  intro Q hQ hQc
  rw [← hge] at hQc
  have hle := card_le_card_of_isPGroup_le_centralizer_conj h.toCtx0.le_invCent
    h.toCtx0.isPGroup h.toCtx0.relIndex_odd g hQ hQc
  rwa [l41_e8_card_S h] at hle

structure L41E8Data (t : G) (S 𝒮 E : Subgroup G) : Prop where
  S_le : S ≤ 𝒮
  cent : invCent t ⊓ 𝒮 = S
  le_𝒮 : E ≤ 𝒮
  normal_𝒮 : (E.subgroupOf 𝒮).Normal
  elem : CFSG.Open.IsElemAbelian 2 E
  card : Nat.card E = 8
  no_conj : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e

theorem L41E8Data.mem_conj {𝒮 E : Subgroup G} (d : L41E8Data t S 𝒮 E) {e k : G} (he : e ∈ E)
    (hk : k ∈ 𝒮) : k * e * k⁻¹ ∈ E :=
  (Subgroup.normal_subgroupOf_iff d.le_𝒮).mp d.normal_𝒮 e k he hk

theorem L41E8Data.cent_eq {𝒮 E : Subgroup G} (d : L41E8Data t S 𝒮 E) (hSt : S ≤ invCent t) :
    E ⊓ centralizer ({t} : Set G) = E ⊓ S := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hx' : x ∈ invCent t ⊓ 𝒮 := ⟨hx.2, d.le_𝒮 hx.1⟩
    rwa [d.cent] at hx'
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨hx.1, hSt hx.2⟩

theorem L41E8Data.inf_S_eq (h : L41GPh2 t L S x₁ x₂ lam rho) {𝒮 E : Subgroup G}
    (d : L41E8Data t S 𝒮 E) : E ⊓ S = fourGrp x₁ x₂ := by
  have htS : t ∈ S := l41_e8_t_mem_S h.toL41GPh1
  have hCE := four_le_card_inf_centralizer d.le_𝒮 d.normal_𝒮 d.elem d.card (d.S_le htS)
    (t_mul_self h.hyp)
  have hE0 := d.cent_eq h.toCtx0.le_invCent
  have hES_A : E ⊓ S ≤ ctxE t x₁ x₂ := by
    have hN : NormalIn (E ⊓ S) S := by
      refine ⟨inf_le_right, ?_⟩
      intro g hg k hk
      rw [Subgroup.mem_inf] at hk ⊢
      exact ⟨d.mem_conj hk.1 (d.S_le hg), S.mul_mem (S.mul_mem hg hk.2) (S.inv_mem hg)⟩
    exact h.basic.normal_elem_le _ hN (CFSG.Open.IsElemAbelian.mono d.elem inf_le_left)
  have hES_F : E ⊓ S ≤ fourGrp x₁ x₂ := by
    intro a ha
    obtain ⟨f, hf, hfa | hfa⟩ := mem_ctxE_cases h.toCtx0 (hES_A ha)
    · rw [hfa]
      exact hf
    · exfalso
      obtain ⟨g, hg⟩ := (l41_tG_A h a (hES_A ha)).mpr ⟨f, hf, hfa⟩
      exact d.no_conj g a (Subgroup.mem_inf.mp ha).1 hg
  have hcardF : Nat.card (fourGrp x₁ x₂) = 4 := (h.wreath.fourGrp_eq_omega).2.2
  refine Subgroup.eq_of_le_of_card_ge hES_F ?_
  rw [hcardF, ← hE0]
  exact hCE

theorem L41E8Data.le_N (h : L41GPh2 t L S x₁ x₂ lam rho) {𝒮 E : Subgroup G}
    (d : L41E8Data t S 𝒮 E) : E ≤ l41N t x₁ x₂ := by
  have htS : t ∈ S := l41_e8_t_mem_S h.toL41GPh1
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hEF : E ⊓ S = fourGrp x₁ x₂ := d.inf_S_eq h
  have hE0 := d.cent_eq h.toCtx0.le_invCent
  have hFE : fourGrp x₁ x₂ ≤ E := hEF ▸ inf_le_left
  have hFA := l41_e8_fourGrp_le_ctxE t x₁ x₂
  have htA : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  have hyF : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  intro e he
  have ht𝒮 : t ∈ 𝒮 := d.S_le htS
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = t * e * t⁻¹ := ⟨_, rfl⟩
  have huE : u ∈ E := by
    rw [hu_def]
    exact d.mem_conj he ht𝒮
  have hte : t * e = u * t := by
    rw [hu_def]
    group
  have htu : t * u = e * t := by
    rw [hu_def]
    calc t * (t * e * t⁻¹) = (t * t) * e * t⁻¹ := by group
      _ = e * t := by rw [ht2, one_mul, htinv]
  have hcommu : u * e = e * u := l41_e8_comm d.elem huE he
  have hcent : e * u ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc t * (e * u) = (t * e) * u := by rw [mul_assoc]
      _ = (u * t) * u := by rw [hte]
      _ = u * (t * u) := by rw [mul_assoc]
      _ = u * (e * t) := by rw [htu]
      _ = (u * e) * t := by rw [mul_assoc]
      _ = (e * u) * t := by rw [hcommu]
  have hfu : e * u ∈ fourGrp x₁ x₂ := by
    have hmem : e * u ∈ E ⊓ centralizer ({t} : Set G) := ⟨E.mul_mem he huE, hcent⟩
    rw [hE0, hEF] at hmem
    exact hmem
  have hconj : e * t * e⁻¹ = (e * u) * t := by
    have hui : u⁻¹ = u := l41_e8_inv d.elem huE
    calc e * t * e⁻¹ = e * (t * e⁻¹ * t⁻¹) * t := by group
      _ = e * (t * e * t⁻¹)⁻¹ * t := by group
      _ = e * u⁻¹ * t := by rw [← hu_def]
      _ = (e * u) * t := by rw [hui]
  have hfix : ∀ f ∈ fourGrp x₁ x₂, e * f * e⁻¹ = f := fun f hf => by
    rw [l41_e8_comm d.elem he (hFE hf)]
    group
  have hconjA : ∀ a ∈ ctxE t x₁ x₂, e * a * e⁻¹ ∈ ctxE t x₁ x₂ := by
    intro a ha
    have ha' : a ∈ closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := ha
    refine Subgroup.closure_induction
      (p := fun a _ => e * a * e⁻¹ ∈ ctxE t x₁ x₂) ?_ ?_ ?_ ?_ ha'
    · intro x hx
      show e * x * e⁻¹ ∈ ctxE t x₁ x₂
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · rw [hx, hconj]
        exact (ctxE t x₁ x₂).mul_mem (hFA hfu) htA
      · rw [hx, hfix _ hyF]
        exact hFA hyF
      · rw [hx, hfix _ hzF]
        exact hFA hzF
    · show e * 1 * e⁻¹ ∈ ctxE t x₁ x₂
      simp
    · intro x y _ _ hx hy
      show e * (x * y) * e⁻¹ ∈ ctxE t x₁ x₂
      have hxy : e * (x * y) * e⁻¹ = (e * x * e⁻¹) * (e * y * e⁻¹) := by group
      rw [hxy]
      exact (ctxE t x₁ x₂).mul_mem hx hy
    · intro x _ hx
      show e * x⁻¹ * e⁻¹ ∈ ctxE t x₁ x₂
      have hxi : e * x⁻¹ * e⁻¹ = (e * x * e⁻¹)⁻¹ := by group
      rw [hxi]
      exact (ctxE t x₁ x₂).inv_mem hx
  exact mem_normalizer_of_conj_mem hconjA

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
