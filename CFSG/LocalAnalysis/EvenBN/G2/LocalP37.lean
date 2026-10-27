module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalP35B
public import CFSG.LocalAnalysis.EvenBN.G2.LocalPDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

theorem comm_mem_of_mul_self_mem {G : Type*} [Group G] {P N : Subgroup G}
    (hPN : P ≤ normalizer (N : Set G)) (hsq : ∀ x ∈ P, x * x ∈ N) :
    ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N := fun x hx y hy => by
  rw [show x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by group]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
    ((mem_normalizer_iff.1 (inv_mem (hPN hy)) _).1 (inv_mem (hsq x hx)))) (inv_mem (hsq y hy))

theorem mem_normalizer_closure_sq_of_mem_normalizer {G : Type*} [Group G] [Finite G]
    {S : Subgroup G} {j : G} (hj : j ∈ normalizer (S : Set G)) :
    j ∈ normalizer ((closure {z | ∃ g ∈ S, z = g ^ 2} : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g, hg, rfl⟩ := hz
    exact subset_closure ⟨j * g * j⁻¹, (mem_normalizer_iff.1 hj g).1 hg, by rw [sq, sq]; group⟩
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    rw [show j * (x * y) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show j * x⁻¹ * j⁻¹ = (j * x * j⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem le_normalizer_of_forall_commutator_mem {G : Type*} [Group G] [Finite G]
    {P N A B : Subgroup G}
    (hc : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) (hNB : N ≤ B) (hAP : A ≤ P) (hBP : B ≤ P) :
    A ≤ normalizer (B : Set G) := fun a ha =>
  mem_normalizer_of_conj_mem fun b hb => by
    rw [show a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b by group]
    exact mul_mem (hNB (hc a (hAP ha) b (hBP hb))) hb

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_5_37_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaL₅ d t : Set G) = (yamadaL₃ d t : Set G) * (yamadaL₄ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaL₃ d t : Set G) ∧
      yamadaR₅ d t = yamadaL₅ d t ⊔ yamadaR₃ d t ∧
      yamadaL₅ d t ⊓ yamadaR₃ d t = yamadaL₃ d t ∧
      yamadaR₅ d t ≤ normalizer (yamadaL₅ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaR₃ d t : Set G) ∧
      (∀ x ∈ yamadaR₅ d t, x * x ∈ yamadaL₃ d t) ∧
      (∀ x ∈ yamadaR₅ d t, ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaL₃ d t) ∧
      Nat.card (yamadaR₅ d t) = Nat.card K ^ 2 * Nat.card (yamadaL₃ d t) := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨hR₅eq, hR₃R₄, hR₅R₃, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  obtain ⟨⟨-, -, -, hL₃R₃, -⟩, -, -, -, hLc, -⟩ := h.yamada_5_35_4 hW d hK hQ
  obtain ⟨-, hR₄eq, hL₄R₂, -, hsqR₄, hcommR₄, -⟩ := h.yamada_5_32_1_L₄ hW d hK hD
  obtain ⟨hL₂L₃, -, hR₃L₃, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := le_sup_left.trans hR₅eq.ge
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := le_sup_right.trans hR₅eq.ge
  have hR₂R₃ : yamadaR₂ d t ≤ yamadaR₃ d t := hR₃R₄.ge.trans inf_le_left
  have hR₂R₄ : yamadaR₂ d t ≤ yamadaR₄ d t := hR₃R₄.ge.trans inf_le_right
  have hL₄R₄ : yamadaL₄ d t ≤ yamadaR₄ d t := hR₄eq ▸ le_sup_left
  have hSR₂ : d.S ≤ yamadaR₂ d t := le_sup_right
  have hSR₃ : d.S ≤ yamadaR₃ d t := le_sup_right
  have hR₅L₃ : yamadaR₅ d t ≤ normalizer (yamadaL₃ d t : Set G) := by
    have := hLc
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t))
    rw [subgroupOf_map_subtype, inf_of_le_left hL₃R₃] at h1
    exact hR₅R₃.trans h1
  have hsqS : ∀ s ∈ d.S, s * s ∈ yamadaL₃ d t := fun s hs => by
    have h1 : s * s ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, (sq s).symm⟩
    rw [(d.yamada_3_12_mho hK4).2.2] at h1
    obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
    exact (hL₃S.ge.trans inf_le_left) (hFM h1)
  have hSL₃ : d.S ≤ normalizer (yamadaL₃ d t : Set G) := fun s hs => hR₃L₃ (hSR₃ hs)
  have hR₃sq := mul_self_mem_of_sup (A := d.S) (B := yamadaL₃ d t) (N := yamadaL₃ d t) hSL₃
    (sup_le hSL₃ Subgroup.le_normalizer) hsqS (fun b hb => mul_mem hb hb)
    (fun a ha b hb => mul_mem ((mem_normalizer_iff.1 (hSL₃ ha) b).1 hb) (inv_mem hb))
  have hR₃sq' : ∀ x ∈ yamadaR₃ d t, x * x ∈ yamadaL₃ d t := fun x hx =>
    hR₃sq.1 x ((sup_comm (yamadaL₃ d t) d.S).le hx)
  have hR₅eq' : yamadaR₅ d t = yamadaL₄ d t ⊔ yamadaR₃ d t := by
    rw [hR₅eq]
    refine le_antisymm (sup_le le_sup_right ?_) (sup_le ?_ le_sup_left)
    · exact hR₄eq.le.trans (sup_le le_sup_left (hR₂R₃.trans le_sup_right))
    · exact hL₄R₄.trans le_sup_right
  have hc : ∀ a ∈ yamadaL₄ d t, ∀ b ∈ yamadaR₃ d t, a * b * a⁻¹ * b⁻¹ ∈ yamadaL₃ d t := by
    intro a ha b hb
    obtain ⟨n, hn, s, hs, rfl⟩ :=
      Common.exists_mul_of_le_normalizer (A := yamadaL₃ d t) (B := d.S) hSL₃ b hb
    have haR₅ : a ∈ yamadaR₅ d t := hR₄R₅ (hL₄R₄ ha)
    have h1 : a * s * a⁻¹ * s⁻¹ ∈ yamadaL₂ d t := hcommR₄ a (hL₄R₄ ha) s (hR₂R₄ (hSR₂ hs))
    rw [show a * (n * s) * a⁻¹ * (n * s)⁻¹ = (a * n * a⁻¹) * (a * s * a⁻¹ * s⁻¹) * n⁻¹ by group]
    exact mul_mem (mul_mem ((mem_normalizer_iff.1 (hR₅L₃ haR₅) n).1 hn) (hL₂L₃ h1))
      (inv_mem hn)
  have hR₅sq := mul_self_mem_of_sup (A := yamadaL₄ d t) (B := yamadaR₃ d t) (N := yamadaL₃ d t)
    (fun a ha => hR₅R₃ (hR₄R₅ (hL₄R₄ ha))) (hR₅eq'.ge.trans hR₅L₃)
    (fun a ha => hL₂L₃ (hsqR₄ a (hL₄R₄ ha))) hR₃sq' hc
  have hsq : ∀ x ∈ yamadaR₅ d t, x * x ∈ yamadaL₃ d t := fun x hx => hR₅sq.1 x (hR₅eq'.le hx)
  have hcomm : ∀ x ∈ yamadaR₅ d t, ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaL₃ d t :=
    fun x hx y hy => hR₅sq.2 x (hR₅eq'.le hx) y (hR₅eq'.le hy)
  have hL₃R₅ : yamadaL₃ d t ≤ yamadaR₅ d t := hL₃R₃.trans hR₃R₅
  have hL₄R₅ : yamadaL₄ d t ≤ yamadaR₅ d t := hL₄R₄.trans hR₄R₅
  have hL₅R₅ : yamadaL₅ d t ≤ yamadaR₅ d t := sup_le hL₃R₅ hL₄R₅
  refine ⟨?_, hR₅L₃, ?_, ?_, ?_, hR₅R₃, hsq, hcomm, ?_⟩
  · exact coe_mul_of_right_le_normalizer_left _ _ fun a ha => hR₅L₃ (hL₄R₅ ha)
  · rw [hR₅eq']
    exact le_antisymm (sup_le_sup_right le_sup_right _)
      (sup_le (sup_le (hL₃R₃.trans le_sup_right) le_sup_left) le_sup_right)
  · refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hL₃R₃)
    obtain ⟨hxL₅, hxR₃⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨n, hn, l, hl, rfl⟩ := Common.exists_mul_of_le_normalizer (A := yamadaL₃ d t)
      (B := yamadaL₄ d t) (fun l hl => hR₅L₃ (hL₄R₅ hl)) x hxL₅
    have hlR₃ : l ∈ yamadaR₃ d t := by
      have := mul_mem (inv_mem (hL₃R₃ hn)) hxR₃
      rwa [inv_mul_cancel_left] at this
    have hlR₂ : l ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hlR₃, hL₄R₄ hl⟩
    exact mul_mem hn (hL₂L₃ (hL₄R₂.le (Subgroup.mem_inf.2 ⟨hl, hlR₂⟩)))
  · intro g hg
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 := hcomm g hg x (hL₅R₅ hx)
    have h2 : yamadaL₃ d t ≤ yamadaL₅ d t := le_sup_left
    rw [show g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x by group]
    exact mul_mem (h2 h1) hx
  · have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaR₃ d t) (B := yamadaR₄ d t)
      (hR₄R₅.trans hR₅R₃)
    rw [← hR₅eq, hR₃R₄, (h.yamadaR₄_facts hW d hK hD).2.2.2.2.2,
      (h.card_yamadaL₃_R₃ hW d hK hD).2, h.card_yamadaR₂ d hK] at h1
    rw [(h.card_yamadaL₃_R₃ hW d hK hD).1]
    have hq : 0 < 2 * Nat.card K ^ 8 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [h1]
    ring

theorem mul_self_mem_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaRstar d t) : x * x ∈ yamadaCstar d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨c, hc, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaCstar d) x hx
  have hC₁C : yamadaC₁ d t ≤ yamadaCstar d t := (h.yamadaCstar_eq d hK hD) ▸
    h.yamadaC₁_le_yamadaV d hK hD
  have hss : s * s ∈ yamadaCstar d t := by
    have h1 : s * s ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, (sq s).symm⟩
    rw [(d.yamada_3_12_mho hK4).2.2] at h1
    obtain ⟨-, -, -, -, -, hFD, -⟩ := d.inclusions
    exact hC₁C ((h.yamadaD₁_le_yamadaC₁ d hK) ((le_sup_right : d.D ≤ yamadaD₁ d t) (hFD h1)))
  rw [show c * s * (c * s) = c * (s * c * s⁻¹) * (s * s) by group]
  exact mul_mem (mul_mem hc ((mem_normalizer_iff.1 (h.S_le_normalizer_yamadaCstar d hs) c).1 hc))
    hss

theorem mul_self_mem_yamadaE₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₅ d t) : x * x ∈ yamadaE₂ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, hxL₃, -⟩ := h.yamada_5_37_1 hW d hK hQ
  obtain ⟨⟨hR₅eq, hR₃R₄, hR₅R₃, hR₅R₄⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  obtain ⟨-, -, -, -, -, hsqR₃, -, -⟩ := h.yamada_5_30_1_R₃ hW d hK hD
  obtain ⟨-, -, -, -, -, hsqR₄, -, -⟩ := h.yamada_5_32_1_R₄ hW d hK hD
  obtain ⟨-, -, -, -, hC₂⟩ := h.yamadaR₃_facts hW d hK hD
  have hR₅R₂ : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := le_sup_left.trans hR₅eq.ge
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := le_sup_right.trans hR₅eq.ge
  have hC₂R₂ : yamadaC₂ d t ≤ yamadaR₂ d t := hC₂.le.trans inf_le_right
  have hsqR₂ : x * x ∈ yamadaR₂ d t := by
    refine (mul_self_mem_of_sup (A := yamadaR₃ d t) (B := yamadaR₄ d t) (N := yamadaR₂ d t)
      (fun a ha => hR₅R₄ (hR₃R₅ ha)) (hR₅eq.ge.trans hR₅R₂) (fun a ha => hC₂R₂ (hsqR₃ a ha))
      (fun b hb => hC₂R₂ (hsqR₄ b hb)) (fun a ha b hb => ?_)).1 x (hR₅eq.le hx)
    rw [← hR₃R₄]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact mul_mem ha ((mem_normalizer_iff.1 (hR₅R₃ (hR₄R₅ hb)) a⁻¹).1 (inv_mem ha))
    · exact mul_mem ((mem_normalizer_iff.1 (hR₅R₄ (hR₃R₅ ha)) b).1 hb) (inv_mem hb)
  have hR₅eq' := h.yamada_5_27_3 hW d hK hD
  have hxR : x ∈ yamadaRstar d t :=
    ((h.mem_yamadaR₅star_iff d hK hD).1 (hR₅eq' ▸ hx)).1
  have hsqC : x * x ∈ yamadaCstar d t := h.mul_self_mem_yamadaCstar d hK hD hxR
  rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [← h.yamadaL₃_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hxL₃ x hx, hsqR₂⟩
  · rw [hC₂]
    exact Subgroup.mem_inf.2 ⟨hsqC, hsqR₂⟩

theorem mul_self_mem_yamadaF₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₅ d t) : x * x ∈ yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨htN, htF⟩ := h.t_mem_normalizer_yamadaF₂ d hK hD
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rcases (mem_sup_zpowers_iff_of htt htN).1 (h.mul_self_mem_yamadaE₂ hW d hK hQ hx) with
    h1 | ⟨a, ha, hxa⟩
  · exact h1
  exfalso
  obtain ⟨⟨hR₅eq, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hR₂R₅ : yamadaR₂ d t ≤ yamadaR₅ d t :=
    (hR₃R₄.ge.trans inf_le_left).trans (le_sup_left.trans hR₅eq.ge)
  obtain ⟨-, -, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨hRE, hEF, -⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hNY₂ : normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) :=
    hRE.trans (hEF.trans hFY)
  have ha' : t * a * t ∈ yamadaF₂ d t := by
    have := (mem_normalizer_iff.1 htN a).1 ha
    rwa [htinv] at this
  obtain ⟨g, hg, y, hy, hgt⟩ := (h.yamada_5_21_3 hW d hK hD).2.1 _ ha'
  have hgt' : g * t * g⁻¹ = a * t * y := by
    rw [hgt, show t * (t * a * t) * y = (t * t) * a * t * y by group, htt, one_mul]
  have hgR₅ : g ∈ normalizer (yamadaR₅ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg
  set z := g⁻¹ * x * g with hzdef
  have hzR₅ : z ∈ yamadaR₅ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hgR₅) x).1 hx
    rwa [inv_inv] at this
  have hzN : z ∈ normalizer (yamadaR₂ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hzR₅
  set η := g⁻¹ * y⁻¹ * g with hηdef
  have hη : η ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (hNY₂ hg)) y⁻¹).1 (inv_mem hy)
    rwa [inv_inv] at this
  have hzz : z * z = t * η := by
    calc z * z = g⁻¹ * (x * x) * g := by rw [hzdef]; group
      _ = g⁻¹ * ((a * t * y) * y⁻¹) * g := by rw [hxa]; group
      _ = g⁻¹ * ((g * t * g⁻¹) * y⁻¹) * g := by rw [hgt']
      _ = t * η := by rw [hηdef]; group
  have hzt : ∃ y' ∈ yamadaY₂ d t, z * t * z⁻¹ = t * y' := by
    have hzη : z * η * z⁻¹ ∈ yamadaY₂ d t := (mem_normalizer_iff.1 (hNY₂ hzN) η).1 hη
    refine ⟨η * (z * η * z⁻¹)⁻¹, mul_mem hη (inv_mem hzη), ?_⟩
    have hcomm : z * (t * η) * z⁻¹ = t * η := by
      rw [← hzz]
      group
    calc z * t * z⁻¹ = z * (t * η) * z⁻¹ * (z * η * z⁻¹)⁻¹ := by group
      _ = t * η * (z * η * z⁻¹)⁻¹ := by rw [hcomm]
      _ = t * (η * (z * η * z⁻¹)⁻¹) := by group
  obtain ⟨y', hy', hzt⟩ := hzt
  have hzmem := ((h.yamada_5_21_3 hW d hK hD).2.2.1 z).1 ⟨hzN, y', hy', hzt⟩
  have hzR₂ : z ∈ yamadaR₂ d t := by
    obtain ⟨r, hr, n, hn, e⟩ := Common.exists_mul_of_le_normalizer
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1 _ hzmem
    have hnR : n ∈ yamadaR d t := by
      rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
      refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hn).1⟩
      have hn' : n = r⁻¹ * z := by
        rw [e]
        group
      rw [hn']
      exact mul_mem (inv_mem (hR₂R₅ hr)) hzR₅
    rw [e]
    exact mul_mem hr ((h.yamadaR₂_inf_centralizer d hK).1 hnR)
  have hz2 : z * z ∈ yamadaF₁ d t := by
    rw [← (h.yamada_5_15_3 d hK hD).1]
    exact subset_closure ⟨z, hzR₂, (sq z).symm⟩
  have hF₁F₂ : yamadaF₁ d t ≤ yamadaF₂ d t := by
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) d.F
  have htη : t * η ∈ yamadaF₂ d t := hzz ▸ hF₁F₂ hz2
  have : t ∈ yamadaF₂ d t := by
    have := mul_mem htη (inv_mem ((le_sup_right : yamadaY₂ d t ≤ yamadaF₂ d t) hη))
    rwa [mul_inv_cancel_right] at this
  exact htF this

theorem eq_or_eq_of_le_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {B : Subgroup G} (hY₁B : yamadaY₁ d t ≤ B)
    (hBY₂ : B ≤ yamadaY₂ d t) (hJ : d.J ≤ normalizer (B : Set G)) :
    B = yamadaY₁ d t ∨ B = yamadaY₂ d t := by
  obtain ⟨hwY, -⟩ := d.wb_mem_normalizer
  have hwJ := h.wb_mem_normalizer_J d hK
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  obtain ⟨hUY, -⟩ := d.inclusions
  have hYY₁ : d.Y ≤ yamadaY₁ d t := le_sup_left
  have hU₁Y₁ : yamadaU₁ d t ≤ yamadaY₁ d t := le_sup_right
  set C : Subgroup G := (B.comap (MulAut.conj d.wb).toMonoidHom) ⊓ yamadaU₁ d t with hCdef
  have hmemC : ∀ c, c ∈ C ↔ d.wb * c * d.wb⁻¹ ∈ B ∧ c ∈ yamadaU₁ d t := fun c => by
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_comap]
    rfl
  have hwY' : ∀ y ∈ d.Y, d.wb * y * d.wb⁻¹ ∈ d.Y := fun y hy =>
    (mem_normalizer_iff.1 hwY.2 y).1 hy
  have hUC : d.U ≤ C := fun c hc => (hmemC c).2
    ⟨hY₁B (hYY₁ (hwY' c (hUY hc))), hUU₁ hc⟩
  have hCU₁ : C ≤ yamadaU₁ d t := inf_le_right
  have hJC : d.J₃ ≤ normalizer (C : Set G) := fun j hj =>
    mem_normalizer_of_conj_mem fun c hc => by
      obtain ⟨hcB, hcU₁⟩ := (hmemC c).1 hc
      have hjJ := hJ₃J hj
      have hj' : d.wb * j * d.wb⁻¹ ∈ d.J := (mem_normalizer_iff.1 hwJ j).1 hjJ
      refine (hmemC _).2 ⟨?_, (mem_normalizer_iff.1 (h.J_le_normalizer_yamadaU₁ d hK hD hjJ) c).1
        hcU₁⟩
      have := (mem_normalizer_iff.1 (hJ hj') _).1 hcB
      rwa [show d.wb * j * d.wb⁻¹ * (d.wb * c * d.wb⁻¹) * (d.wb * j * d.wb⁻¹)⁻¹ =
        d.wb * (j * c * j⁻¹) * d.wb⁻¹ by group] at this
  rcases h.eq_or_eq_of_le_yamadaU₁ d hK hD hUC hCU₁ hJC with hCU | hCU₁'
  · left
    refine le_antisymm (fun b hb => ?_) hY₁B
    obtain ⟨u, hu, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.map_wb_yamadaU₁_le_normalizer d hK hD) b (hBY₂ hb)
    have hvB : v ∈ B := by
      have := mul_mem (inv_mem (hY₁B (hU₁Y₁ hu))) hb
      rwa [inv_mul_cancel_left] at this
    obtain ⟨u', hu', rfl⟩ := hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvB ⊢
    have hu'C : u' ∈ C := (hmemC u').2 ⟨hvB, hu'⟩
    rw [hCU] at hu'C
    exact mul_mem (hU₁Y₁ hu) (hYY₁ (hwY' u' (hUY hu'C)))
  · right
    refine le_antisymm hBY₂ (sup_le (hU₁Y₁.trans hY₁B) ?_)
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ C := by rw [hCU₁']; exact hu
    exact ((hmemC u).1 hu').1

theorem yamadaF₂_le_closure_sq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {A : Subgroup G}
    (hS₂A : yamadaS₂ d t ≤ A) (hAR₅ : A ≤ yamadaR₅ d t) (hJ : d.J ≤ normalizer (A : Set G))
    (hAR₂ : ¬ A ≤ yamadaR₂ d t) :
    yamadaF₂ d t ≤ closure {z | ∃ g ∈ A, z = g ^ 2} := by
  have hD := hQ.doubling
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hYF : d.Y ≤ d.F := hYX.trans hXF
  have hFS : d.F ≤ d.S := hFD.trans hDS
  set Q : Subgroup G := closure {z | ∃ g ∈ A, z = g ^ 2} with hQdef
  have hF₁Q : yamadaF₁ d t ≤ Q := by
    rw [← (h.yamada_5_15_3 d hK hD).2.1]
    exact closure_mono fun z ⟨g, hg, hz⟩ => ⟨g, hS₂A hg, hz⟩
  have hQF₂ : Q ≤ yamadaF₂ d t := by
    rw [hQdef, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    show g ^ 2 ∈ yamadaF₂ d t
    rw [sq]
    exact h.mul_self_mem_yamadaF₂ hW d hK hQ (hAR₅ hg)
  have hJQ : d.J ≤ normalizer (Q : Set G) := fun j hj =>
    mem_normalizer_closure_sq_of_mem_normalizer (hJ hj)
  have hFF₁ : d.F ≤ yamadaF₁ d t := by
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact le_sup_left
  have hY₁Q : yamadaY₁ d t ≤ Q := by
    refine le_trans ?_ hF₁Q
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact sup_le_sup_right hYF _
  have hB := h.eq_or_eq_of_le_yamadaY₂ d hK hD (B := Q ⊓ yamadaY₂ d t)
    (le_inf hY₁Q (h.yamadaY₁_le_yamadaY₂ d hK hD)) inf_le_right
    (fun j hj => Common.mem_normalizer_inf (hJQ hj)
      (h.J_le_normalizer_yamadaY₂ d hK hD hj))
  rcases hB with hB | hB
  · exfalso
    have hQF₁ : Q ≤ yamadaF₁ d t := by
      intro a ha
      obtain ⟨φ, hφ, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
        (h.yamadaY₂_le_normalizer_F d hK hD) a (hQF₂ ha)
      have hφQ : φ ∈ Q := hF₁Q (hFF₁ hφ)
      have hyQ : y ∈ Q := by
        have := mul_mem (inv_mem hφQ) ha
        rwa [inv_mul_cancel_left] at this
      have hyY₁ : y ∈ yamadaY₁ d t := by
        rw [← hB]
        exact Subgroup.mem_inf.2 ⟨hyQ, hy⟩
      refine mul_mem (hFF₁ hφ) ?_
      rw [h.yamadaF₁_eq_sup d hK hD]
      exact (sup_le_sup_right hYF _ : yamadaY₁ d t ≤ d.F ⊔ yamadaU₁ d t) hyY₁
    have hQeq : Q = yamadaF₁ d t := le_antisymm hQF₁ hF₁Q
    have hAN : A ≤ normalizer (yamadaF₁ d t : Set G) := fun a ha => by
      rw [← hQeq]
      exact mem_normalizer_closure_sq_of_mem_normalizer (Subgroup.le_normalizer ha)
    have hsqA : ∀ x ∈ A, x * x ∈ yamadaF₁ d t := fun x hx => by
      rw [← hQeq]
      exact subset_closure ⟨x, hx, (sq x).symm⟩
    have hcomA := comm_mem_of_mul_self_mem hAN hsqA
    have hS₁eq := h.yamadaS₁_eq_sup d hK hD
    have hS₁A : yamadaS₁ d t ≤ A := by
      refine le_trans ?_ hS₂A
      rw [hS₁eq]
      exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) d.S
    have hF₁S₁ : yamadaF₁ d t ≤ yamadaS₁ d t := by
      rw [h.yamadaF₁_eq_sup d hK hD, hS₁eq]
      exact sup_le_sup_right hFS _
    have hAS₁ : A ≤ normalizer (yamadaS₁ d t : Set G) := fun a ha =>
      mem_normalizer_of_conj_mem fun z hz => by
        have h1 := hcomA a ha z (hS₁A hz)
        rw [show a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z by group]
        exact mul_mem (hF₁S₁ h1) hz
    have h28 := (h.yamada_5_28 hW d hK hD).2.1
    refine hAR₂ fun a ha => ?_
    rw [← h28]
    exact Subgroup.mem_inf.2 ⟨hAR₅ ha, hAS₁ ha⟩
  · have hY₂Q : yamadaY₂ d t ≤ Q := by
      rw [← hB]
      exact inf_le_left
    exact sup_le (hFF₁.trans hF₁Q) hY₂Q

theorem t_mem_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    t ∈ yamadaR₂ d t :=
  (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)
    (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))

theorem yamada_5_37_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaS₃ d t, z = g ^ 2} = yamadaF₂ d t ∧
      closure {z | ∃ g ∈ yamadaS₄ d t, z = g ^ 2} = yamadaF₂ d t ∧
      closure {z | ∃ g ∈ yamadaR₅ d t, z = g ^ 2} = yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hR₅eq, -, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := le_sup_left.trans hR₅eq.ge
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := le_sup_right.trans hR₅eq.ge
  have hpow : Nat.card K ^ 8 < Nat.card K ^ 9 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  have hup : ∀ A : Subgroup G, A ≤ yamadaR₅ d t →
      closure {z | ∃ g ∈ A, z = g ^ 2} ≤ yamadaF₂ d t := fun A hA => by
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    show g ^ 2 ∈ yamadaF₂ d t
    rw [sq]
    exact h.mul_self_mem_yamadaF₂ hW d hK hQ (hA hg)
  have hJS₂ := h.J_le_normalizer_yamadaS₂ d hK hD
  obtain ⟨-, -, -, -, ⟨hR₃S, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, hJW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  have hS₃R₃ : yamadaS₃ d t ≤ yamadaR₃ d t := le_sup_left.trans hR₃S.le
  have hS₃R₅ : yamadaS₃ d t ≤ yamadaR₅ d t := hS₃R₃.trans hR₃R₅
  have hS₃R₂ : ¬ yamadaS₃ d t ≤ yamadaR₂ d t := fun hle => by
    have h1 : yamadaR₃ d t ≤ yamadaR₂ d t := by
      rw [← hR₃S]
      exact sup_le hle ((zpowers_le).2 (h.t_mem_yamadaR₂ d hK))
    have h2 := Subgroup.card_le_of_le h1
    rw [(h.card_yamadaL₃_R₃ hW d hK hD).2, h.card_yamadaR₂ d hK] at h2
    omega
  have hS₃ : closure {z | ∃ g ∈ yamadaS₃ d t, z = g ^ 2} = yamadaF₂ d t :=
    le_antisymm (hup _ hS₃R₅) (h.yamadaF₂_le_closure_sq hW d hK hQ le_sup_right hS₃R₅
      (fun j hj => mem_normalizer_sup (hJW₃ hj) (hJS₂ hj)) hS₃R₂)
  obtain ⟨-, -, -, -, ⟨hR₄S, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨-, -, hJX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR₄S.le
  have hS₄R₅ : yamadaS₄ d t ≤ yamadaR₅ d t := hS₄R₄.trans hR₄R₅
  have hS₄R₂ : ¬ yamadaS₄ d t ≤ yamadaR₂ d t := fun hle => by
    have h1 : yamadaR₄ d t ≤ yamadaR₂ d t := by
      rw [← hR₄S]
      exact sup_le hle ((zpowers_le).2 (h.t_mem_yamadaR₂ d hK))
    have h2 := Subgroup.card_le_of_le h1
    rw [(h.yamadaR₄_facts hW d hK hD).2.2.2.2.2, h.card_yamadaR₂ d hK] at h2
    omega
  have hS₄ : closure {z | ∃ g ∈ yamadaS₄ d t, z = g ^ 2} = yamadaF₂ d t :=
    le_antisymm (hup _ hS₄R₅) (h.yamadaF₂_le_closure_sq hW d hK hQ le_sup_right hS₄R₅
      (fun j hj => mem_normalizer_sup (hJX₄ hj) (hJS₂ hj)) hS₄R₂)
  refine ⟨hS₃, hS₄, le_antisymm (hup _ le_rfl) ?_⟩
  rw [← hS₃]
  exact closure_mono fun z ⟨g, hg, hz⟩ => ⟨g, hS₃R₅ hg, hz⟩

theorem D_le_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.D ≤ yamadaCstar d t :=
  ((le_sup_right : d.D ≤ yamadaD₁ d t).trans (h.yamadaD₁_le_yamadaC₁ d hK)).trans
    ((h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD)

theorem S_inf_yamadaCstar_le_D (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.S ⊓ yamadaCstar d t ≤ d.D := fun s hs => by
  obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.1 hs
  refine h.mem_D_of_mem_yamadaC₂ d hK hD ?_ (d.image_le _ hsS)
  rw [(h.yamadaR₃_facts hW d hK hD).2.2.2.2]
  exact Subgroup.mem_inf.2 ⟨hsC, (le_sup_right : d.S ≤ yamadaR₂ d t) hsS⟩

theorem exists_mem_inf_mul_M (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {Li Ri : Subgroup G} (hLR : Li ≤ Ri) (hRR : Ri ≤ yamadaRstar d t)
    (hML : d.M ≤ Li) :
    ∀ l ∈ Li, ∃ c ∈ Li ⊓ (Ri ⊓ yamadaCstar d t), ∃ m ∈ d.M, l = c * m := by
  intro l hl
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  obtain ⟨c₀, hc₀, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaCstar d) l (hRR (hLR hl))
  have hsDM : s ∈ d.D ⊔ d.M := by
    rw [(d.yamada_defs).2.2.2.2.2.2.2.2]
    exact hs
  obtain ⟨δ, hδ, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun x hx => d.S_le_normalizers.2.2.2.2.2.1 (hMS hx)) s hsDM
  have hδC := h.D_le_yamadaCstar d hK hD hδ
  refine ⟨c₀ * δ, Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_inf.2 ⟨?_, mul_mem hc₀ hδC⟩⟩, m, hm,
    by group⟩
  · have := mul_mem hl (inv_mem (hML hm))
    rwa [show c₀ * (δ * m) * m⁻¹ = c₀ * δ by group] at this
  · have := mul_mem (hLR hl) (inv_mem (hLR (hML hm)))
    rwa [show c₀ * (δ * m) * m⁻¹ = c₀ * δ by group] at this

theorem yamada_5_37_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ((yamadaS₅ d t : Set G) = (yamadaS₃ d t : Set G) * (yamadaS₄ d t : Set G) ∧
      (yamadaM₅ d t : Set G) = (yamadaM₃ d t : Set G) * (yamadaM₄ d t : Set G) ∧
      (yamadaD₅ d t : Set G) = (yamadaD₃ d t : Set G) * (yamadaD₄ d t : Set G) ∧
      (yamadaF₅ d t : Set G) = (yamadaF₃ d t : Set G) * (yamadaF₄ d t : Set G)) ∧
    (yamadaS₅ d t ⊔ zpowers t = yamadaR₅ d t ∧ t ∈ normalizer (yamadaS₅ d t : Set G) ∧
      t ∉ yamadaS₅ d t) ∧
    (yamadaM₅ d t ⊔ zpowers t = yamadaL₅ d t ∧ t ∈ normalizer (yamadaM₅ d t : Set G) ∧
      t ∉ yamadaM₅ d t) ∧
    (yamadaD₅ d t ⊔ zpowers t = yamadaC₅ d t ∧ t ∈ normalizer (yamadaD₅ d t : Set G) ∧
      t ∉ yamadaD₅ d t) ∧
    (yamadaF₅ d t ⊔ zpowers t = yamadaE₅ d t ∧ t ∈ normalizer (yamadaF₅ d t : Set G) ∧
      t ∉ yamadaF₅ d t) := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨⟨hR₅eq, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := le_sup_left.trans hR₅eq.ge
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := le_sup_right.trans hR₅eq.ge
  have hR₅R₂N : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hR₅F₂N : yamadaR₅ d t ≤ normalizer (yamadaF₂ d t : Set G) := by
    obtain ⟨hRE, hEF, -⟩ := h.normalizer_yamadaR₂_le d hK hD
    exact hR₅R₂N.trans (hRE.trans hEF)
  have hcommF : ∀ x ∈ yamadaR₅ d t, ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₂ d t :=
    comm_mem_of_mul_self_mem hR₅F₂N fun x hx => h.mul_self_mem_yamadaF₂ hW d hK hQ hx
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hFS : d.F ≤ d.S := hFD.trans hDS
  obtain ⟨-, ⟨hV₃N, hV₃eq, -, -⟩, ⟨hE₃eq, -⟩, ⟨hL₃eq, -⟩, ⟨hR₃eq, htS₃⟩, ⟨hC₃eq, -⟩⟩ :=
    h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, ⟨hU₄N, hU₄eq, -, -⟩, ⟨hE₄eq, -⟩, ⟨hL₄eq, -⟩, ⟨hR₄eq, -⟩, ⟨hC₄eq, -⟩⟩ :=
    h.yamada_5_32_2 hW d hK hD
  obtain ⟨hE₂E₄, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hL₄R₄, -⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨hR₃R, -, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨hR₄R, -, -, -, -, -⟩ := h.yamadaR₄_facts hW d hK hD
  have hF₂M₂ : yamadaF₂ d t ≤ yamadaM₂ d t := (h.yamadaE₂_le_yamadaL₂ d hK hD).1
  have hM₂S₂ : yamadaM₂ d t ≤ yamadaS₂ d t := sup_le_sup_right hMS _
  have hF₂S₂ : yamadaF₂ d t ≤ yamadaS₂ d t := sup_le_sup_right hFS _
  have hS₂S₃ : yamadaS₂ d t ≤ yamadaS₃ d t := le_sup_right
  have hS₂S₄ : yamadaS₂ d t ≤ yamadaS₄ d t := le_sup_right
  have hSS₂ : d.S ≤ yamadaS₂ d t := le_sup_left
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := le_sup_left
  have hS₃R₃ : yamadaS₃ d t ≤ yamadaR₃ d t := le_sup_left.trans hR₃eq.le
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR₄eq.le
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := le_sup_left.trans hL₃eq.le
  have hM₄L₄ : yamadaM₄ d t ≤ yamadaL₄ d t := le_sup_left.trans hL₄eq.le
  have hF₃E₃ : yamadaF₃ d t ≤ yamadaE₃ d t := le_sup_left.trans hE₃eq.le
  have hF₄E₄ : yamadaF₄ d t ≤ yamadaE₄ d t := le_sup_left.trans hE₄eq.le
  have hE₃L₃ : yamadaE₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hE₄L₄ : yamadaE₄ d t ≤ yamadaL₄ d t := inf_le_left
  have hE₃C₃ : yamadaE₃ d t ≤ yamadaC₃ d t := inf_le_right
  have hE₄C₄ : yamadaE₄ d t ≤ yamadaC₄ d t := inf_le_right
  have hF₂E₂ : yamadaF₂ d t ≤ yamadaE₂ d t := le_sup_left
  have hS₃R₅ : yamadaS₃ d t ≤ yamadaR₅ d t := hS₃R₃.trans hR₃R₅
  have hS₄R₅ : yamadaS₄ d t ≤ yamadaR₅ d t := hS₄R₄.trans hR₄R₅
  have hM₃S₃ : yamadaM₃ d t ≤ yamadaS₃ d t := sup_le_sup_left hM₂S₂ _
  have hM₄S₄ : yamadaM₄ d t ≤ yamadaS₄ d t := sup_le_sup_left hM₂S₂ _
  have hF₃S₃ : yamadaF₃ d t ≤ yamadaS₃ d t := sup_le_sup_left hF₂S₂ _
  have hF₄S₄ : yamadaF₄ d t ≤ yamadaS₄ d t := sup_le_sup_left hF₂S₂ _
  have hD₃S₃ : yamadaD₃ d t ≤ yamadaS₃ d t := inf_le_left
  have hD₄S₄ : yamadaD₄ d t ≤ yamadaS₄ d t := inf_le_left
  have hF₂S₄ : yamadaF₂ d t ≤ yamadaS₄ d t := hF₂S₂.trans hS₂S₄
  have hF₂M₄ : yamadaF₂ d t ≤ yamadaM₄ d t := hF₂M₂.trans le_sup_right
  have hF₂F₃ : yamadaF₂ d t ≤ yamadaF₃ d t := le_sup_right
  have hF₂F₄ : yamadaF₂ d t ≤ yamadaF₄ d t := le_sup_right
  have hF₂D₄ : yamadaF₂ d t ≤ yamadaD₄ d t :=
    le_inf hF₂S₄ (hF₂E₂.trans (hE₂E₄.trans hE₄C₄))
  have hM₃R₅ : yamadaM₃ d t ≤ yamadaR₅ d t := hM₃S₃.trans hS₃R₅
  have hM₄R₅ : yamadaM₄ d t ≤ yamadaR₅ d t := hM₄S₄.trans hS₄R₅
  have hD₃R₅ : yamadaD₃ d t ≤ yamadaR₅ d t := hD₃S₃.trans hS₃R₅
  have hD₄R₅ : yamadaD₄ d t ≤ yamadaR₅ d t := hD₄S₄.trans hS₄R₅
  have hF₃R₅ : yamadaF₃ d t ≤ yamadaR₅ d t := hF₃S₃.trans hS₃R₅
  have hF₄R₅ : yamadaF₄ d t ≤ yamadaR₅ d t := hF₄S₄.trans hS₄R₅
  have hnS : yamadaS₃ d t ≤ normalizer (yamadaS₄ d t : Set G) :=
    le_normalizer_of_forall_commutator_mem hcommF hF₂S₄ hS₃R₅ hS₄R₅
  have hsetS : (yamadaS₅ d t : Set G) = (yamadaS₃ d t : Set G) * (yamadaS₄ d t : Set G) :=
    coe_sup_eq_mul hnS
  have hsetM : (yamadaM₅ d t : Set G) = (yamadaM₃ d t : Set G) * (yamadaM₄ d t : Set G) :=
    coe_sup_eq_mul (le_normalizer_of_forall_commutator_mem hcommF hF₂M₄ hM₃R₅ hM₄R₅)
  have hsetD : (yamadaD₅ d t : Set G) = (yamadaD₃ d t : Set G) * (yamadaD₄ d t : Set G) :=
    coe_sup_eq_mul (le_normalizer_of_forall_commutator_mem hcommF hF₂D₄ hD₃R₅ hD₄R₅)
  have hsetF : (yamadaF₅ d t : Set G) = (yamadaF₃ d t : Set G) * (yamadaF₄ d t : Set G) :=
    coe_sup_eq_mul (le_normalizer_of_forall_commutator_mem hcommF hF₂F₄ hF₃R₅ hF₄R₅)
  have htR₂ := h.t_mem_yamadaR₂ d hK
  have htR₃ : t ∈ yamadaR₃ d t := (hR₃R₄.ge.trans inf_le_left) htR₂
  have htR₄ : t ∈ yamadaR₄ d t := (hR₃R₄.ge.trans inf_le_right) htR₂
  have htR₅ : t ∈ yamadaR₅ d t := hR₃R₅ htR₃
  obtain ⟨hR₃F, hR₃M, hR₃S⟩ := h.yamadaR₃_le_normalizers hW d hK hD
  obtain ⟨hR₄F, hR₄M, hR₄S⟩ := h.yamadaR₄_le_normalizers hW d hK hD
  have htW₃N : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    hV₃N (hV₃eq.le (mem_sup_right (mem_zpowers t)))
  have htX₄N : t ∈ normalizer (yamadaX₄ d t : Set G) :=
    hU₄N (hU₄eq.le (mem_sup_right (mem_zpowers t)))
  have htS₃N : t ∈ normalizer (yamadaS₃ d t : Set G) := mem_normalizer_sup htW₃N (hR₃S htR₃)
  have htS₄N : t ∈ normalizer (yamadaS₄ d t : Set G) := mem_normalizer_sup htX₄N (hR₄S htR₄)
  have htM₃N : t ∈ normalizer (yamadaM₃ d t : Set G) := mem_normalizer_sup htW₃N (hR₃M htR₃)
  have htM₄N : t ∈ normalizer (yamadaM₄ d t : Set G) := mem_normalizer_sup htX₄N (hR₄M htR₄)
  have htF₃N : t ∈ normalizer (yamadaF₃ d t : Set G) := mem_normalizer_sup htW₃N (hR₃F htR₃)
  have htF₄N : t ∈ normalizer (yamadaF₄ d t : Set G) := mem_normalizer_sup htX₄N (hR₄F htR₄)
  have htC₃ : t ∈ yamadaC₃ d t := hC₃eq.le (mem_sup_right (mem_zpowers t))
  have htC₄ : t ∈ yamadaC₄ d t := hC₄eq.le (mem_sup_right (mem_zpowers t))
  have htD₃N : t ∈ normalizer (yamadaD₃ d t : Set G) :=
    Common.mem_normalizer_inf htS₃N (Subgroup.le_normalizer htC₃)
  have htD₄N : t ∈ normalizer (yamadaD₄ d t : Set G) :=
    Common.mem_normalizer_inf htS₄N (Subgroup.le_normalizer htC₄)
  have htS₅ : t ∉ yamadaS₅ d t := fun ht => by
    have ht' : t ∈ ((yamadaS₅ d t : Subgroup G) : Set G) := ht
    rw [hsetS] at ht'
    obtain ⟨s₃, hs₃, s₄, hs₄, hts⟩ := Set.mem_mul.1 ht'
    have hs₄R₃ : s₄ ∈ yamadaR₃ d t := by
      have := mul_mem (inv_mem (hS₃R₃ hs₃)) htR₃
      rw [eq_inv_mul_of_mul_eq hts]
      exact this
    have hs₄R₂ : s₄ ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hs₄R₃, hS₄R₄ hs₄⟩
    have hs₄S₂ : s₄ ∈ yamadaS₂ d t := by
      rw [← h.yamadaS₄_inf_yamadaR₂ hW d hK hD]
      exact Subgroup.mem_inf.2 ⟨hs₄, hs₄R₂⟩
    have := mul_mem hs₃ (hS₂S₃ hs₄S₂)
    rw [hts] at this
    exact htS₃ this
  have hM₅S₅ : yamadaM₅ d t ≤ yamadaS₅ d t := sup_le_sup hM₃S₃ hM₄S₄
  have hD₅S₅ : yamadaD₅ d t ≤ yamadaS₅ d t := sup_le_sup hD₃S₃ hD₄S₄
  have hF₅S₅ : yamadaF₅ d t ≤ yamadaS₅ d t := sup_le_sup hF₃S₃ hF₄S₄
  have hR₅S : yamadaS₅ d t ⊔ zpowers t = yamadaR₅ d t := by
    refine le_antisymm (sup_le (sup_le hS₃R₅ hS₄R₅) ((zpowers_le).2 htR₅)) ?_
    rw [hR₅eq]
    exact sup_le (hR₃eq.ge.trans (sup_le_sup_right le_sup_left _))
      (hR₄eq.ge.trans (sup_le_sup_right le_sup_right _))
  have htL₃ : t ∈ yamadaL₃ d t := hL₃eq.le (mem_sup_right (mem_zpowers t))
  have hL₃L₅ : yamadaL₃ d t ≤ yamadaL₅ d t := le_sup_left
  have hL₄L₅ : yamadaL₄ d t ≤ yamadaL₅ d t := le_sup_right
  have hL₅M : yamadaM₅ d t ⊔ zpowers t = yamadaL₅ d t := by
    refine le_antisymm (sup_le (sup_le (hM₃L₃.trans hL₃L₅) (hM₄L₄.trans hL₄L₅))
      ((zpowers_le).2 (hL₃L₅ htL₃))) ?_
    show yamadaL₃ d t ⊔ yamadaL₄ d t ≤ _
    exact sup_le (hL₃eq.ge.trans (sup_le_sup_right le_sup_left _))
      (hL₄eq.ge.trans (sup_le_sup_right le_sup_right _))
  have hS₅N : t ∈ normalizer (yamadaS₅ d t : Set G) := mem_normalizer_sup htS₃N htS₄N
  have hR₅R : yamadaR₅ d t ≤ yamadaRstar d t := by
    intro x hx
    have hR₅star := h.yamada_5_27_3 hW d hK hD
    exact ((h.mem_yamadaR₅star_iff d hK hD).1 (hR₅star ▸ hx)).1
  have hRC : yamadaRstar d t ≤ normalizer (yamadaCstar d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaCstar d)
  have hSC : ∀ y ∈ yamadaS₅ d t, y ∈ yamadaCstar d t → y ∈ yamadaD₅ d t := by
    intro y hy hyC
    have hy' : y ∈ ((yamadaS₅ d t : Subgroup G) : Set G) := hy
    rw [hsetS] at hy'
    obtain ⟨s₃, hs₃, s₄, hs₄, rfl⟩ := Set.mem_mul.1 hy'
    obtain ⟨c₄, hc₄, s', hs', rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.S_le_normalizer_yamadaCstar d) s₄ (hR₄R (hS₄R₄ hs₄))
    have hs'S₄ : s' ∈ yamadaS₄ d t := hS₂S₄ (hSS₂ hs')
    have hs'S₃ : s' ∈ yamadaS₃ d t := hS₂S₃ (hSS₂ hs')
    have hc₄S : c₄ ∈ yamadaS₄ d t := by
      have := mul_mem hs₄ (inv_mem hs'S₄)
      rwa [mul_inv_cancel_right] at this
    have he₄S : s₃ * c₄ * s₃⁻¹ ∈ yamadaS₄ d t := (mem_normalizer_iff.1 (hnS hs₃) c₄).1 hc₄S
    have he₄C : s₃ * c₄ * s₃⁻¹ ∈ yamadaCstar d t :=
      (mem_normalizer_iff.1 (hRC (hR₅R (hS₃R₅ hs₃))) c₄).1 hc₄
    have he₄ : s₃ * c₄ * s₃⁻¹ ∈ yamadaD₄ d t :=
      Subgroup.mem_inf.2 ⟨he₄S, Subgroup.mem_inf.2 ⟨hS₄R₄ he₄S, he₄C⟩⟩
    have hs₃s' : s₃ * s' ∈ yamadaD₃ d t := by
      have hC : s₃ * s' ∈ yamadaCstar d t := by
        have := mul_mem (inv_mem he₄C) hyC
        rwa [show (s₃ * c₄ * s₃⁻¹)⁻¹ * (s₃ * (c₄ * s')) = s₃ * s' by group] at this
      exact Subgroup.mem_inf.2 ⟨mul_mem hs₃ hs'S₃,
        Subgroup.mem_inf.2 ⟨hS₃R₃ (mul_mem hs₃ hs'S₃), hC⟩⟩
    rw [show s₃ * (c₄ * s') = (s₃ * c₄ * s₃⁻¹) * (s₃ * s') by group]
    exact mul_mem (mem_sup_right he₄) (mem_sup_left hs₃s')
  have htC : t ∈ yamadaCstar d t := (Subgroup.mem_inf.1 htC₃).2
  have hC₃C₅ : yamadaC₃ d t ≤ yamadaC₅ d t := inf_le_inf_right _ hR₃R₅
  have hC₄C₅ : yamadaC₄ d t ≤ yamadaC₅ d t := inf_le_inf_right _ hR₄R₅
  have hC₅ : yamadaD₅ d t ⊔ zpowers t = yamadaC₅ d t := by
    refine le_antisymm (sup_le (sup_le (inf_le_right.trans hC₃C₅) (inf_le_right.trans hC₄C₅))
      ((zpowers_le).2 (hC₃C₅ htC₃))) fun x hx => ?_
    obtain ⟨hxR₅, hxC⟩ := Subgroup.mem_inf.1 hx
    rcases (mem_sup_zpowers_iff_of htt hS₅N).1 (hR₅S.ge hxR₅) with h1 | ⟨a, ha, rfl⟩
    · exact mem_sup_left (hSC x h1 hxC)
    · have haC : a ∈ yamadaCstar d t := by
        have := mul_mem hxC (inv_mem htC)
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (mem_sup_left (hSC a ha haC)) (mem_sup_right (mem_zpowers t))
  obtain ⟨hsetL, -⟩ := h.yamada_5_37_1 hW d hK hQ
  obtain ⟨-, -, -, hR₄L₄N, -, -, -⟩ := h.yamada_5_32_1_L₄ hW d hK hD
  obtain ⟨-, -, -, hR₄C₄N, -, -, -, -⟩ := h.yamada_5_32_1_R₄ hW d hK hD
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have hR₂R₄ : yamadaR₂ d t ≤ yamadaR₄ d t := hR₃R₄.ge.trans inf_le_right
  have hMR₄ : d.M ≤ yamadaR₄ d t :=
    (hML₂.trans (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)).trans hR₂R₄
  have hML₃ : d.M ≤ yamadaL₃ d t := hL₃S.ge.trans inf_le_left
  have hML₄ : d.M ≤ yamadaL₄ d t := hML₂.trans le_sup_right
  have hR₄E₄ : yamadaR₄ d t ≤ normalizer (yamadaE₄ d t : Set G) := fun g hg =>
    Common.mem_normalizer_inf (hR₄L₄N hg) (hR₄C₄N hg)
  have hF₅F₅ : yamadaF₃ d t ⊔ zpowers t ≤ yamadaF₅ d t ⊔ zpowers t :=
    sup_le_sup_right le_sup_left _
  have hF₄F₅ : yamadaF₄ d t ⊔ zpowers t ≤ yamadaF₅ d t ⊔ zpowers t :=
    sup_le_sup_right le_sup_right _
  have hE₅ : yamadaF₅ d t ⊔ zpowers t = yamadaE₅ d t := by
    refine le_antisymm (sup_le (sup_le ?_ ?_) ((zpowers_le).2 ?_)) fun x hx => ?_
    · exact le_inf (hF₃E₃.trans (hE₃L₃.trans hL₃L₅)) (hF₃E₃.trans (hE₃C₃.trans hC₃C₅))
    · exact le_inf (hF₄E₄.trans (hE₄L₄.trans hL₄L₅)) (hF₄E₄.trans (hE₄C₄.trans hC₄C₅))
    · exact Subgroup.mem_inf.2 ⟨hL₃L₅ htL₃, hC₃C₅ htC₃⟩
    obtain ⟨hxL₅, hxC₅⟩ := Subgroup.mem_inf.1 hx
    have hxC : x ∈ yamadaCstar d t := (Subgroup.mem_inf.1 hxC₅).2
    have hxL' : x ∈ ((yamadaL₅ d t : Subgroup G) : Set G) := hxL₅
    rw [hsetL] at hxL'
    obtain ⟨l₃, hl₃, l₄, hl₄, rfl⟩ := Set.mem_mul.1 hxL'
    obtain ⟨c₃, hc₃, m₃, hm₃, rfl⟩ := h.exists_mem_inf_mul_M d hK hD hL₃R₃ (hR₃R) hML₃ l₃ hl₃
    obtain ⟨c₄, hc₄, m₄, hm₄, rfl⟩ := h.exists_mem_inf_mul_M d hK hD hL₄R₄ (hR₄R) hML₄ l₄ hl₄
    have hc₃E : c₃ ∈ yamadaE₃ d t := hc₃
    have hc₄E : c₄ ∈ yamadaE₄ d t := hc₄
    have he₄ : m₃ * c₄ * m₃⁻¹ ∈ yamadaE₄ d t :=
      (mem_normalizer_iff.1 (hR₄E₄ (hMR₄ hm₃)) c₄).1 hc₄E
    have hfC : m₃ * m₄ ∈ yamadaCstar d t := by
      have h1 : c₃ ∈ yamadaCstar d t := (Subgroup.mem_inf.1 (hE₃C₃ hc₃E)).2
      have h2 : m₃ * c₄ * m₃⁻¹ ∈ yamadaCstar d t := (Subgroup.mem_inf.1 (hE₄C₄ he₄)).2
      have := mul_mem (inv_mem (mul_mem h1 h2)) hxC
      rwa [show (c₃ * (m₃ * c₄ * m₃⁻¹))⁻¹ * (c₃ * m₃ * (c₄ * m₄)) = m₃ * m₄ by group] at this
    have hfF : m₃ * m₄ ∈ d.F := by
      rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
      exact Subgroup.mem_inf.2 ⟨h.S_inf_yamadaCstar_le_D hW d hK hD
        (Subgroup.mem_inf.2 ⟨hMS (mul_mem hm₃ hm₄), hfC⟩), mul_mem hm₃ hm₄⟩
    rw [show c₃ * m₃ * (c₄ * m₄) = c₃ * (m₃ * c₄ * m₃⁻¹) * (m₃ * m₄) by group]
    refine mul_mem (mul_mem (hF₅F₅ (hE₃eq.ge hc₃E)) (hF₄F₅ (hE₄eq.ge he₄))) ?_
    exact hF₅F₅ (mem_sup_left (hF₂F₃ ((le_sup_left : d.F ≤ yamadaF₂ d t) hfF)))
  have hF₅N : t ∈ normalizer (yamadaF₅ d t : Set G) := mem_normalizer_sup htF₃N htF₄N
  have hM₅N : t ∈ normalizer (yamadaM₅ d t : Set G) := mem_normalizer_sup htM₃N htM₄N
  have hD₅N : t ∈ normalizer (yamadaD₅ d t : Set G) := mem_normalizer_sup htD₃N htD₄N
  exact ⟨⟨hsetS, hsetM, hsetD, hsetF⟩, ⟨hR₅S, hS₅N, htS₅⟩,
    ⟨hL₅M, hM₅N, fun ht => htS₅ (hM₅S₅ ht)⟩, ⟨hC₅, hD₅N, fun ht => htS₅ (hD₅S₅ ht)⟩,
    ⟨hE₅, hF₅N, fun ht => htS₅ (hF₅S₅ ht)⟩⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
