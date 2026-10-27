module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalN60

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace LocalN60FourAux

section Generic

variable {G : Type*} [Group G]

theorem exists_isSylowOf_ge {A B : Subgroup G} (hAB : A ≤ B) (hA : IsPGroup 2 A) :
    ∃ V : Subgroup G, IsSylowOf 2 V B ∧ A ≤ V := by
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (hA.comap_subtype (K := B))
  refine ⟨(Q : Subgroup B).map B.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAB ha⟩, hQ (mem_subgroupOf.2 ha), rfl⟩

theorem mul_self_of_isElementaryAbelian {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 E)
    {e : G} (he : e ∈ E) : e * e = 1 := by
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
  rwa [sq] at this

theorem mul_comm_of_isElementaryAbelian {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 E)
    {e e' : G} (he : e ∈ E) (he' : e' ∈ E) : e * e' = e' * e :=
  congrArg Subtype.val (mul_comm' (⟨e, he⟩ : E) ⟨e', he'⟩)

end Generic

section SetupLevel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaL₆_inf_centralizer_J₁_le_four (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) :
    yamadaL₆ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaL₂ d t := by
  intro x hx
  obtain ⟨hxL₆, hxJ⟩ := Subgroup.mem_inf.1 hx
  have ht := h.t_mem_centralizer_J₁ d
  have hκM₂ : t * x * t * x⁻¹ ∈ yamadaM₂ d t :=
    h.crossed_mem_yamadaM₂ d hK hD (yamadaL₆_le d t hxL₆)
  have hκY₂ : t * x * t * x⁻¹ ∈ yamadaY₂ d t := by
    rw [← h.yamadaM₂_inf_centralizer_J₁_four d hK hD hK4]
    exact Subgroup.mem_inf.2 ⟨hκM₂, mul_mem (mul_mem (mul_mem ht hxJ) ht) (inv_mem hxJ)⟩
  exact (h.crossed_mem_yamadaY₂_iff hW d hK hD hxL₆).1 hκY₂

theorem yamadaM₆_inf_yamadaL₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ yamadaL₂ d t ≤ yamadaM₂ d t := by
  have hD := hQ.doubling
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  intro x hx
  obtain ⟨hxM₆, hxL₂⟩ := Subgroup.mem_inf.1 hx
  rw [h.yamadaL₂_eq_sup d hK hD] at hxL₂
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htM₂).1 hxL₂ with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    have htM₆ : t ∈ yamadaM₆ d t := by
      have := mul_mem (inv_mem (h.yamadaM₂_le_yamadaM₆ hW d hK hQ ha)) hxM₆
      rwa [inv_mul_cancel_left] at this
    exact (h.yamada_5_44_1 hW d hK hQ).1.2.2 htM₆

theorem yamadaD₁_le_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₁ d t ≤ yamadaP d t := by
  obtain ⟨-, -, -, hS₅S₆, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have hS₂S₅ : yamadaS₂ d t ≤ yamadaS₅ d t :=
    (le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans le_sup_left
  have hS₂P : yamadaS₂ d t ≤ yamadaP d t := hS₂S₅.trans (hS₅S₆.trans hS₆P)
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t :=
    (Setup.yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  rw [hQ.doubling.D₁_eq]
  exact sup_le (hDS.trans ((le_sup_left : d.S ≤ yamadaS₂ d t).trans hS₂P)) (hU₁S₂.trans hS₂P)

theorem yamadaP_inf_centralizer_J₁_le_yamadaB (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaB d := by
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  have hP2 : IsPGroup 2 (yamadaP d t) := h.isPGroup_yamadaP d hPR₈
  have hJP : d.J ≤ normalizer (yamadaP d t : Set G) := h.J_le_normalizer_yamadaP hW d hK hQ
  have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
  refine h.le_yamadaB_of_four d hK (hP2.to_le inf_le_left) inf_le_right (fun j hj => ?_)
    (fun x hx => ?_)
  · exact Common.mem_normalizer_inf (hJP (hJ₃J hj))
      (mem_normalizer_centralizer_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun j' hj' => d.J₁_comm_J₃ hj' hj)))
  · obtain ⟨⟨hxP, hxJ₁⟩, hxJ₃⟩ := hx
    have hxJ : x ∈ centralizer (d.J : Set G) := by
      have hle : d.J ≤ centralizer ({x} : Set G) := by
        rw [← Setup.Q52.J₁_sup_J₃ d]
        exact sup_le
          (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxJ₁ j hj))
          (fun j hj => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxJ₃ j hj))
      exact mem_centralizer_iff.2 fun j hj => mem_centralizer_singleton_iff.1 (hle hj)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (h.q49_yamadaR₈_inf_centralizer_J_le hW d hK hQ ⟨hPR₈ hxP, hxJ⟩)
    obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
    rcases h.zpow_eq_one_or_eq k with hk1 | hk1
    · rw [hk1] at hk
      rw [← hk]
      exact one_mem _
    · rw [hk1] at hk
      exact absurd (hk ▸ hxP) htP

theorem yamadaY₂_le_yamadaP_inf_centralizer_J₁_four (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hK4 : Nat.card K = 4) : yamadaY₂ d t ≤ yamadaP d t ⊓ centralizer (d.J₁ : Set G) :=
  le_inf ((h.yamadaY₂_le_yamadaM₆ hW d hK hQ).trans (h.yamadaM₆_le_yamadaP hW d hK hQ))
    (h.yamadaY₂_le_centralizer_J₁_four d hQ.doubling hK4)

end SetupLevel

end LocalN60FourAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section LocalFour

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaM₆_inf_centralizer_J₄_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ centralizer (d.J₄ : Set G) ≤ yamadaY₂ d t := by
  intro x hx
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  · rw [N60.eq_one_of_mem_yamadaM₆_of_forall_J₄ hW h d hK h8 hxM
      fun j hj => mem_centralizer_iff.1 hxC j hj]
    exact one_mem _
  · have hD := hQ.doubling
    rw [← (d.yamada_3_9_4_four_G hK4).1] at hxC
    have hxL₂ := LocalN60FourAux.yamadaL₆_inf_centralizer_J₁_le_four hW h d hK hD hK4
      ⟨h.yamadaM₆_le_yamadaL₆ hW d hK hQ hxM, hxC⟩
    have hxM₂ := LocalN60FourAux.yamadaM₆_inf_yamadaL₂_le hW h d hK hQ ⟨hxM, hxL₂⟩
    rw [← h.yamadaM₂_inf_centralizer_J₁_four d hK hD hK4]
    exact ⟨hxM₂, hxC⟩

theorem yamada_5_60_3_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊓ yamadaM₆ d t ≤ yamadaY₂ d t := fun x hx =>
  h.yamadaM₆_inf_centralizer_J₄_le hW d hK hQ
    ⟨(Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩

theorem yamadaM₆_inf_centralizer_J₄_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4) :
    yamadaM₆ d t ⊓ centralizer (d.J₄ : Set G) = yamadaY₂ d t := by
  refine le_antisymm (h.yamadaM₆_inf_centralizer_J₄_le hW d hK hQ)
    (le_inf (h.yamadaY₂_le_yamadaM₆ hW d hK hQ) ?_)
  rw [← (d.yamada_3_9_4_four_G hK4).1]
  exact h.yamadaY₂_le_centralizer_J₁_four d hQ.doubling hK4

theorem yamada_5_60_3_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4) :
    (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊓ yamadaM₆ d t = yamadaY₂ d t := by
  refine le_antisymm (h.yamada_5_60_3_le hW d hK hQ) ?_
  rw [← h.yamadaM₆_inf_centralizer_J₄_four hW d hK hQ hK4]
  exact le_inf (le_inf (inf_le_left.trans (yamadaM₆_le_yamadaN₂ d t)) inf_le_right) inf_le_left

theorem yamada_5_60_3_sylow_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4) :
    ∃ V E : Subgroup G, IsSylowOf 2 V (yamadaB d) ∧
      yamadaP d t ⊓ centralizer (d.J₄ : Set G) ≤ V ∧ V ≤ normalizer (yamadaY₂ d t : Set G) ∧
      E ≤ V ∧ yamadaY₂ d t ⊓ E = ⊥ ∧ yamadaY₂ d t ⊔ E = V ∧ CFSG.IsElementaryAbelian 2 E := by
  have hD := hQ.doubling
  have hQ4 : h.QFourFacts d := (hQ.branch.resolve_left (by omega)).2
  rw [← (d.yamada_3_9_4_four_G hK4).1]
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  set A : Subgroup G := yamadaP d t ⊓ centralizer (d.J₁ : Set G)
  have hA2 : IsPGroup 2 A := (h.isPGroup_yamadaP d hPR₈).to_le inf_le_left
  have hAB : A ≤ yamadaB d :=
    LocalN60FourAux.yamadaP_inf_centralizer_J₁_le_yamadaB hW h d hK hQ
  have hXA : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ A := fun x hx =>
    Subgroup.mem_inf.2 ⟨LocalN60FourAux.yamadaD₁_le_yamadaP hW h d hK hQ (Subgroup.mem_inf.1 hx).1,
      (Subgroup.mem_inf.1 hx).2⟩
  have hYA : yamadaY₂ d t ≤ A :=
    LocalN60FourAux.yamadaY₂_le_yamadaP_inf_centralizer_J₁_four hW h d hK hQ hK4
  obtain ⟨V, hV, hAV⟩ := LocalN60FourAux.exists_isSylowOf_ge hAB hA2
  have hYV : yamadaY₂ d t ≤ V := hYA.trans hAV
  obtain ⟨E, hEV, hYE, hYEV⟩ := hQ4.exists_complement hV hYV
    (fun e he => h.yamadaY₂_mul_self hW d hK hD he)
    (fun e he e' he' => h.yamadaY₂_mul_comm d hK hD he he') (h.card_yamadaY₂ d hK hD)
  have hEl : ElemModulo (yamadaU₁ d t) V := by
    rcases hD.branch with h8 | ⟨-, -, -, hE⟩
    · omega
    · exact hE V hV.le hV.isPGroup (hXA.trans hAV)
  have hU₁Y₂ := Setup.yamadaU₁_le_yamadaY₂ d t
  have hVN : V ≤ normalizer (yamadaY₂ d t : Set G) := by
    refine le_normalizer_of_conj_mem fun v hv y hy => ?_
    have := mul_mem (hU₁Y₂ (hEl v hv y (hYV hy)).2) hy
    rwa [show ⁅v, y⁆ * y = v * y * v⁻¹ by simp only [commutatorElement_def]; group] at this
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have h1 : e * e ∈ yamadaY₂ d t ⊓ E :=
      Subgroup.mem_inf.2 ⟨hU₁Y₂ (hEl e (hEV he) e (hEV he)).1, mul_mem he he⟩
    rwa [hYE, Subgroup.mem_bot] at h1
  have hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' => by
    have h1 : ⁅e, e'⁆ ∈ yamadaY₂ d t ⊓ E := Subgroup.mem_inf.2
      ⟨hU₁Y₂ (hEl e (hEV he) e' (hEV he')).2, by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem he he') (inv_mem he)) (inv_mem he')⟩
    rwa [hYE, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact ⟨V, E, hV, hAV, hVN, hEV, hYE, hYEV, isElementaryAbelian_of_forall hEc hEsq⟩

theorem yamada_5_60_3_complement_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hK4 : Nat.card K = 4) :
    ∃ E : Subgroup G, E ≤ yamadaP d t ⊓ centralizer (d.J₄ : Set G) ∧ yamadaY₂ d t ⊓ E = ⊥ ∧
      yamadaY₂ d t ⊔ E = yamadaP d t ⊓ centralizer (d.J₄ : Set G) ∧
      CFSG.IsElementaryAbelian 2 E := by
  obtain ⟨V, E, hV, hAV, hVN, hEV, hYE, hYEV, hEel⟩ :=
    h.yamada_5_60_3_sylow_four hW d hK hQ hK4
  have hYA := LocalN60FourAux.yamadaY₂_le_yamadaP_inf_centralizer_J₁_four hW h d hK hQ hK4
  rw [← (d.yamada_3_9_4_four_G hK4).1] at hAV ⊢
  refine ⟨E ⊓ (yamadaP d t ⊓ centralizer (d.J₁ : Set G)), inf_le_right, ?_, ?_, ?_⟩
  · rw [eq_bot_iff, ← hYE]
    exact inf_le_inf_left _ inf_le_left
  · refine le_antisymm (sup_le hYA inf_le_right) fun a ha => ?_
    have hs : a ∈ E ⊔ yamadaY₂ d t := by
      rw [sup_comm, hYEV]
      exact hAV ha
    obtain ⟨e, he, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' (hEV.trans hVN) a hs
    have heA : e ∈ yamadaP d t ⊓ centralizer (d.J₁ : Set G) := by
      have := mul_mem ha (inv_mem (hYA hy))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_right ⟨he, heA⟩) (mem_sup_left hy)
  · exact isElementaryAbelian_of_forall
      (fun x hx y hy => LocalN60FourAux.mul_comm_of_isElementaryAbelian hEel hx.1 hy.1)
      (fun x hx => LocalN60FourAux.mul_self_of_isElementaryAbelian hEel hx.1)

end LocalFour

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
