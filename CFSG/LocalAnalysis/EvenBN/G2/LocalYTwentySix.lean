module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyFive

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaW₃_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaW₃ d t ≤ yamadaV₃ d t ∧ yamadaV₃ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
      d.J ≤ normalizer (yamadaW₃ d t : Set G) ∧ yamadaW₂ d t ≤ yamadaW₃ d t ∧
      t ∉ yamadaW₃ d t ∧ yamadaW₃ d t ⊔ zpowers t = yamadaV₃ d t ∧
      Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, -, hV₃c, -, -, hV₃W₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨hJV₃, hJV₂⟩ := h.J_le_normalizer_yamadaV₃ hW d hK hD
  obtain ⟨hR₃R, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨hJ₄J, -⟩ := h.J₄_facts d hK
  obtain ⟨-, htW'⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  have hV₃R₃ : yamadaV₃ d t ≤ yamadaR₃ d t := hV₃E₃.trans (inf_le_left.trans le_sup_left)
  have hV₃p : IsPGroup 2 (yamadaV₃ d t) :=
    (h.isPGroup_yamadaRstar d).to_le (hV₃R₃.trans hR₃R)
  have hW₂V₃ : yamadaW₂ d t ≤ yamadaV₃ d t := le_sup_left.trans hV₂V₃
  have htV₃ : t ∈ yamadaV₃ d t := hV₂V₃ (mem_sup_right (mem_zpowers t))
  have hJW₂ : d.J ≤ normalizer (yamadaW₂ d t : Set G) :=
    hJV₂.trans (h.normalizer_yamadaV₂_le hW d hK hD).1
  have hW₃V₃ : yamadaW₃ d t ≤ yamadaV₃ d t := by
    show ⁅yamadaV₃ d t, d.J⁆ ≤ yamadaV₃ d t
    refine (Subgroup.commutator_le).2 fun v hv j hj => ?_
    rw [commutatorElement_def, show v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) by group]
    exact mul_mem hv ((mem_normalizer_iff.1 (hJV₃ hj) _).1 (inv_mem hv))
  have hV₃N : yamadaV₃ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    le_normalizer_commutator_left _ _
  have hJN : d.J ≤ normalizer (yamadaW₃ d t : Set G) := fun j hj =>
    mem_normalizer_commutator (hJV₃ hj) (Subgroup.le_normalizer hj)
  have hcomm : ∀ v ∈ yamadaV₃ d t, ∀ j ∈ d.J, v⁻¹ * (j * v * j⁻¹) ∈ yamadaW₃ d t :=
    fun v hv j hj => by
      rw [show v⁻¹ * (j * v * j⁻¹) = ⁅v⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact commutator_mem_commutator (inv_mem hv) hj
  have hsq : ∀ x ∈ yamadaV₃ d t, x * x ∈ yamadaW₂ d t := fun x hx =>
    h.mul_self_mem_yamadaW₂ hW d hK hD hx
  have hab : ∀ x ∈ yamadaV₃ d t, ∀ y ∈ yamadaV₃ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₂ d t :=
    fun x hx y hy => by
      rw [show x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by
        group]
      exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
        ((mem_normalizer_iff.1 (inv_mem (hV₃W₂ hy)) _).1 (inv_mem (hsq x hx))))
        (inv_mem (hsq y hy))
  have htW₃ : t ∉ yamadaW₃ d t := fun ht => htW' (mem_of_mem_commutator_of_forall hW₂V₃ hV₃W₂
    hab hJV₃ hJW₂ (coprime_card_J d hV₃p) ht fun j hj => by
      have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d hj)).1
      rw [hjt, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _)
  have hW₂W₃ : yamadaW₂ d t ≤ yamadaW₃ d t := fun w hw => by
    have hWp : IsPGroup 2 (yamadaW₂ d t) := hV₃p.to_le hW₂V₃
    have : Group.IsNilpotent (yamadaW₂ d t) := hWp.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaW₂ d t) (N := yamadaW₂ d t ⊓ yamadaW₃ d t) (S := d.J) inf_le_left
      (fun x hx => Common.mem_normalizer_inf (Subgroup.le_normalizer hx) (hV₃N (hW₂V₃ hx)))
      hJW₂ (fun j hj => Common.mem_normalizer_inf (hJW₂ hj) (hJN hj)) inferInstance
      (coprime_card_J d hWp) hw fun j hj => Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJW₂ hj) w).1 hw),
          hcomm w (hW₂V₃ hw) j hj⟩
    have hc1 : c = 1 := h.eq_one_of_mem_yamadaW₂_of_forall_J d hK hD (Subgroup.mem_inf.1 hc).1
      fun k hk => mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 k hk
    rw [hc1, one_mul]
    exact (Subgroup.mem_inf.1 hn).2
  have hV₃eq : yamadaW₃ d t ⊔ zpowers t = yamadaV₃ d t := by
    refine le_antisymm (sup_le hW₃V₃ ((zpowers_le).2 htV₃)) fun v hv => ?_
    have : Group.IsNilpotent (yamadaV₃ d t) := hV₃p.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaV₃ d t) (N := yamadaW₃ d t) (S := d.J) hW₃V₃ hV₃N hJV₃ hJN inferInstance
      (coprime_card_J d hV₃p) hv (hcomm v hv)
    obtain ⟨hcV, hcJ⟩ := Subgroup.mem_inf.1 hc
    have hcL₂ : c ∈ yamadaL₂ d t := h.mem_yamadaL₂_of_forall_J₄ hW d hK hD
      ((hV₃E₃.trans inf_le_left) hcV) fun k hk => by
        rw [mem_centralizer_iff.1 hcJ k (hJ₄J hk), mul_inv_cancel_right, inv_mul_cancel]
        exact one_mem _
    have hcV₂ : c ∈ yamadaV₂ d t := hV₃L₂.le (Subgroup.mem_inf.2 ⟨hcV, hcL₂⟩)
    have hV₂le : yamadaV₂ d t ≤ yamadaW₃ d t ⊔ zpowers t :=
      sup_le (hW₂W₃.trans le_sup_left) le_sup_right
    exact mul_mem (hV₂le hcV₂) (mem_sup_left hn)
  have hW₃c : Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 := by
    have h1 := h.card_sup_zpowers (hV₃N htV₃) htW₃
    rw [hV₃eq, hV₃c] at h1
    exact (Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) h1).symm
  exact ⟨hW₃V₃, hV₃N, hJN, hW₂W₃, htW₃, hV₃eq, hW₃c⟩

theorem t_not_mem_yamadaW₃_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {X : Subgroup G}
    (hW₃X : yamadaW₃ d t ≤ normalizer (X : Set G)) (hWX : yamadaW₂ d t ≤ X) (htX : t ∉ X)
    (hVX : yamadaV₃ d t ⊓ X ≤ yamadaV₂ d t) : t ∉ yamadaW₃ d t ⊔ X := by
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  have htV₃ : t ∈ yamadaV₃ d t := hV₃eq.le (mem_sup_right (mem_zpowers t))
  intro ht
  obtain ⟨w, hw, x, hx, e⟩ := Common.exists_mul_of_le_normalizer' hW₃X t ht
  have hxV₃ : x ∈ yamadaV₃ d t := by
    have : x = w⁻¹ * t := by rw [e, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem (hW₃V₃ hw)) htV₃
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1
      (hVX (Subgroup.mem_inf.2 ⟨hxV₃, hx⟩)) with hxW | ⟨a, ha, rfl⟩
  · have h1 : w * x ∈ yamadaW₃ d t := mul_mem hw (hW₂W₃ hxW)
    rw [← e] at h1
    exact htW₃ h1
  · refine htX ?_
    have := mul_mem (inv_mem (hWX ha)) hx
    rwa [inv_mul_cancel_left] at this

theorem yamadaR₃_le_normalizers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃ d t ≤ normalizer (yamadaF₂ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaM₂ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaS₂ d t : Set G) := by
  obtain ⟨-, -, hR₃R₂, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, -, hR₃V₂, -⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨hRE, hEF, -⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hLM : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) := by
    have := normalizer_le_normalizer_thompsonSubgroup (yamadaL₂ d t)
    rwa [h.yamada_5_13_2 d hK hD] at this
  have hRS : normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaS₂ d t : Set G) := by
    have := (h.yamada_5_15_6 d hK hD).2.2.2
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaS₂ d t).subgroupOf (yamadaR₂ d t))
    rwa [subgroupOf_map_subtype, inf_of_le_left (h.yamada_5_13_3 d hK hD).2.1] at h1
  exact ⟨(hR₃R₂.trans hRE).trans hEF,
    hR₃V₂.trans ((h.normalizer_le_normalizer_yamadaL₂ hW d hK hD).trans hLM), hR₃R₂.trans hRS⟩

theorem yamada_5_30_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ((yamadaF₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaF₂ d t : Set G) ∧
      (yamadaM₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaM₂ d t : Set G) ∧
      (yamadaS₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaS₂ d t : Set G)) ∧
    (yamadaV₃ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
      yamadaW₃ d t ⊔ zpowers t = yamadaV₃ d t ∧ t ∉ yamadaW₃ d t ∧
      yamadaW₂ d t < yamadaW₃ d t) ∧
    (yamadaF₃ d t ⊔ zpowers t = yamadaE₃ d t ∧ t ∉ yamadaF₃ d t) ∧
    (yamadaM₃ d t ⊔ zpowers t = yamadaL₃ d t ∧ t ∉ yamadaM₃ d t) ∧
    (yamadaS₃ d t ⊔ zpowers t = yamadaR₃ d t ∧ t ∉ yamadaS₃ d t) ∧
    (yamadaD₃ d t ⊔ zpowers t = yamadaC₃ d t ∧ t ∉ yamadaD₃ d t) := by
  obtain ⟨hW₃V₃, hV₃N, -, hW₂W₃, htW₃, hV₃eq, hW₃c⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, hV₃R₂, -, hsup, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hE₃eq, hV₃E₂, -⟩ := h.yamada_5_30_1_E₃ hW d hK hD
  obtain ⟨hRF, hRM, hRS⟩ := h.yamadaR₃_le_normalizers hW d hK hD
  obtain ⟨-, -, -, -, hWF, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨hE₂E₃, -⟩ := h.yamadaE₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, hS₂R₂, -, htS₂, hR₂S₂⟩ := h.yamada_5_13_3 d hK hD
  have hV₃R₃ : yamadaV₃ d t ≤ yamadaR₃ d t := hV₃E₃.trans (inf_le_left.trans le_sup_left)
  have hW₃R₃ : yamadaW₃ d t ≤ yamadaR₃ d t := hW₃V₃.trans hV₃R₃
  have htV₃ : t ∈ yamadaV₃ d t := hV₃eq.le (mem_sup_right (mem_zpowers t))
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := le_sup_left.trans hL₂eq.ge
  have hM₂S₂ : yamadaM₂ d t ≤ yamadaS₂ d t := sup_le_sup_right hMS _
  have hW₂F₂ : yamadaW₂ d t ≤ yamadaF₂ d t := sup_le_sup_right hWF _
  have hsetF := coe_sup_eq_mul (hW₃R₃.trans hRF)
  have hsetM := coe_sup_eq_mul (hW₃R₃.trans hRM)
  have hsetS := coe_sup_eq_mul (hW₃R₃.trans hRS)
  have htF₃ : t ∉ yamadaF₃ d t := h.t_not_mem_yamadaW₃_sup hW d hK hD (hW₃R₃.trans hRF) hW₂F₂
    (h.t_mem_normalizer_yamadaF₂ d hK hD).2 (hV₃E₂.le.trans' (inf_le_inf_left _ le_sup_left))
  have htM₃ : t ∉ yamadaM₃ d t := h.t_not_mem_yamadaW₃_sup hW d hK hD (hW₃R₃.trans hRM)
    (hW₂F₂.trans (h.yamadaE₂_le_yamadaL₂ d hK hD).1) (h.yamada_5_13_1 d hK hD).2.2.2.2
    (hV₃L₂.le.trans' (inf_le_inf_left _ hM₂L₂))
  have htS₃ : t ∉ yamadaS₃ d t := h.t_not_mem_yamadaW₃_sup hW d hK hD (hW₃R₃.trans hRS)
    ((hW₂F₂.trans (h.yamadaE₂_le_yamadaL₂ d hK hD).1).trans hM₂S₂) htS₂
    (hV₃R₂.le.trans' (inf_le_inf_left _ hS₂R₂))
  have hE : yamadaF₃ d t ⊔ zpowers t = yamadaE₃ d t := by
    refine le_antisymm (sup_le (sup_le (hW₃V₃.trans hV₃E₃) (le_sup_left.trans hE₂E₃))
      ((zpowers_le).2 (hV₃E₃ htV₃))) ?_
    rw [hE₃eq, ← hV₃eq]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hL : yamadaM₃ d t ⊔ zpowers t = yamadaL₃ d t := by
    refine le_antisymm (sup_le (sup_le ((hW₃V₃.trans hV₃E₃).trans inf_le_left)
      (hM₂L₂.trans (h.yamadaL₃_facts hW d hK hD).1))
      ((zpowers_le).2 ((hV₃E₃.trans inf_le_left) htV₃))) ?_
    rw [← hsup, ← hV₃eq, hL₂eq]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hR : yamadaS₃ d t ⊔ zpowers t = yamadaR₃ d t := by
    refine le_antisymm (sup_le (sup_le hW₃R₃ (hS₂R₂.trans hR₂R₃))
      ((zpowers_le).2 (hV₃R₃ htV₃))) ?_
    show yamadaL₃ d t ⊔ d.S ≤ _
    rw [← hL]
    exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hM₂S₂.trans (le_sup_right.trans le_sup_left))) le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_left)
  have htC₃ : t ∈ yamadaC₃ d t := by
    have htC₂ : t ∈ yamadaC₂ d t := mem_sup_right (mem_zpowers t)
    rw [← (h.yamada_5_30_1_R₃ hW d hK hD).2.2.1] at htC₂
    exact (Subgroup.mem_inf.1 htC₂).1
  have htS₃N : t ∈ normalizer (yamadaS₃ d t : Set G) :=
    mem_normalizer_sup (hV₃N htV₃) (hR₂S₂ ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)
      (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))))
  have hC : yamadaD₃ d t ⊔ zpowers t = yamadaC₃ d t := by
    refine le_antisymm (sup_le inf_le_right ((zpowers_le).2 htC₃)) fun x hx => ?_
    have hxR : x ∈ yamadaS₃ d t ⊔ zpowers t := hR.ge (Subgroup.mem_inf.1 hx).1
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htS₃N).1 hxR with hxS | ⟨s, hs, rfl⟩
    · exact mem_sup_left (Subgroup.mem_inf.2 ⟨hxS, hx⟩)
    · have hsC : s ∈ yamadaC₃ d t := by
        have := mul_mem hx (inv_mem htC₃)
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hs, hsC⟩)) (mem_sup_right (mem_zpowers t))
  refine ⟨⟨hsetF, hsetM, hsetS⟩, ⟨hV₃N, hV₃eq, htW₃, lt_of_le_of_ne hW₂W₃ fun e => ?_⟩,
    ⟨hE, htF₃⟩, ⟨hL, htM₃⟩, ⟨hR, htS₃⟩, ⟨hC, fun ht => htS₃ (Subgroup.mem_inf.1 ht).1⟩⟩
  have h56 := hW₃c
  rw [← e, h.card_yamadaW₂ d hK hD] at h56
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have := Nat.pow_right_injective (show 2 ≤ Nat.card K by omega) h56
  omega

theorem yamadaM₃_inf_yamadaL₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaM₃ d t ⊓ yamadaL₂ d t = yamadaM₂ d t := by
  obtain ⟨⟨-, hsetM, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, hV₃L₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := le_sup_left.trans hL₂eq.ge
  have hW₂M₂ : yamadaW₂ d t ≤ yamadaM₂ d t :=
    (sup_le_sup_right d.inclusions.2.2.2.2.1 _).trans (h.yamadaE₂_le_yamadaL₂ d hK hD).1
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hM₂L₂)
  obtain ⟨hxM₃, hxL₂⟩ := Subgroup.mem_inf.1 hx
  have hxM₃' : x ∈ ((yamadaM₃ d t : Subgroup G) : Set G) := hxM₃
  rw [hsetM] at hxM₃'
  obtain ⟨w, hw, m, hm, rfl⟩ := Set.mem_mul.1 hxM₃'
  have hwL₂ : w ∈ yamadaL₂ d t := by
    have := mul_mem hxL₂ (inv_mem (hM₂L₂ hm))
    rwa [mul_inv_cancel_right] at this
  have hwV₂ : w ∈ yamadaV₂ d t := hV₃L₂.le (Subgroup.mem_inf.2 ⟨hW₃V₃ hw, hwL₂⟩)
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hwV₂ with
    hwW | ⟨a, ha, rfl⟩
  · exact mul_mem (hW₂M₂ hwW) hm
  · exfalso
    refine htW₃ ?_
    have := mul_mem (inv_mem (hW₂W₃ ha)) hw
    rwa [inv_mul_cancel_left] at this

theorem yamadaM₃_eq_commutator_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaM₃ d t = ⁅yamadaL₃ d t, d.J₄⁆ ⊔ yamadaM₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hV₃N, -, -, -⟩, -, ⟨hL, htM₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hL₂L₃, -, hR₃L₃, hR₃V₂, -⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨-, hRM, -⟩ := h.yamadaR₃_le_normalizers hW d hK hD
  obtain ⟨hJ₄J, -⟩ := h.J₄_facts d hK
  obtain ⟨hR₃R, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, hJL₃, -, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨-, -, hJW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hLM : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) := by
    have := normalizer_le_normalizer_thompsonSubgroup (yamadaL₂ d t)
    rwa [h.yamada_5_13_2 d hK hD] at this
  have hJM₂ : d.J ≤ normalizer (yamadaM₂ d t : Set G) := fun j hj => hLM
    (le_normalizer_yamadaL₂ d t ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK
      hD).2 (mem_sup_right (hJC hj))))
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := le_sup_left
  have hL₃p : IsPGroup 2 (yamadaL₃ d t) := (h.isPGroup_yamadaRstar d).to_le (hL₃R₃.trans hR₃R)
  have hL₃M₂ : yamadaL₃ d t ≤ normalizer (yamadaM₂ d t : Set G) := hL₃R₃.trans hRM
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM₃N : t ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_sup (hV₃N ((h.yamadaV₃_facts hW d hK hD).1 (mem_sup_right (mem_zpowers t))))
      (hL₃M₂ (hL₂L₃ htL₂))
  have hkM₃ : ∀ k ∈ d.J₄, k ∈ normalizer (yamadaM₃ d t : Set G) := fun k hk =>
    mem_normalizer_sup (hJW₃ (hJ₄J hk)) (hJM₂ (hJ₄J hk))
  have hCM₃ : ⁅yamadaL₃ d t, d.J₄⁆ ≤ yamadaM₃ d t := (Subgroup.commutator_le).2 fun l hl k hk => by
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (hJC (hJ₄J hk))).1
    have hkM := hkM₃ k hk
    rw [← hL] at hl
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htM₃N).1 hl with hm | ⟨m, hm, rfl⟩
    · rw [commutatorElement_def, show l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) by group]
      exact mul_mem hm ((mem_normalizer_iff.1 hkM _).1 (inv_mem hm))
    · rw [commutatorElement_def, show m * t * k * (m * t)⁻¹ * k⁻¹ =
        m * (t * k) * t⁻¹ * m⁻¹ * k⁻¹ by group, ← hkt,
        show m * (k * t) * t⁻¹ * m⁻¹ * k⁻¹ = m * (k * m⁻¹ * k⁻¹) by group]
      exact mul_mem hm ((mem_normalizer_iff.1 hkM _).1 (inv_mem hm))
  set N := ⁅yamadaL₃ d t, d.J₄⁆ ⊔ yamadaM₂ d t with hN
  have hNM₃ : N ≤ yamadaM₃ d t := sup_le hCM₃ le_sup_right
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := le_sup_left.trans hL.le
  have hL₃N : yamadaL₃ d t ≤ normalizer (N : Set G) := fun l hl =>
    mem_normalizer_sup (le_normalizer_commutator_left _ _ hl) (hL₃M₂ hl)
  have hJ₄N : d.J₄ ≤ normalizer (N : Set G) := fun k hk =>
    mem_normalizer_sup (mem_normalizer_commutator (hJL₃ (hJC (hJ₄J hk)))
      (Subgroup.le_normalizer hk)) (hJM₂ (hJ₄J hk))
  have hJ₄odd : Odd (Nat.card d.J₄) := (odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₄J)
  have hcop : Nat.Coprime (Nat.card d.J₄) (Nat.card (yamadaL₃ d t)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hL₃p
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hJ₄odd)
  have hsup : N ⊔ yamadaL₂ d t = yamadaL₃ d t := by
    refine le_antisymm (sup_le (hNM₃.trans hM₃L₃) hL₂L₃) fun l hl => ?_
    have : Group.IsNilpotent (yamadaL₃ d t) := hL₃p.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaL₃ d t) (N := N) (S := d.J₄) (hNM₃.trans hM₃L₃) hL₃N
      (fun k hk => hJL₃ (hJC (hJ₄J hk))) hJ₄N inferInstance hcop hl fun k hk => by
        rw [show l⁻¹ * (k * l * k⁻¹) = ⁅l⁻¹, k⁆ by simp only [commutatorElement_def]; group]
        exact mem_sup_left (commutator_mem_commutator (inv_mem hl) hk)
    obtain ⟨hcL₃, hcJ⟩ := Subgroup.mem_inf.1 hc
    have hcL₂ : c ∈ yamadaL₂ d t := h.mem_yamadaL₂_of_forall_J₄ hW d hK hD hcL₃ fun k hk => by
      rw [mem_centralizer_iff.1 hcJ k hk, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
    have := mul_mem (mem_sup_right hcL₂ : c ∈ N ⊔ yamadaL₂ d t) (mem_sup_left hn)
    exact this
  have hq : 0 < Nat.card K := Nat.card_pos
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂c : Nat.card (yamadaM₂ d t) = Nat.card K ^ 7 := by
    have h1 := h.card_sup_zpowers (hLM (Subgroup.le_normalizer htL₂))
      (h.yamada_5_13_1 d hK hD).2.2.2.2
    rw [← hL₂eq, h.card_yamadaL₂ d hK] at h1
    exact (Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) h1).symm
  have hM₃c : Nat.card (yamadaM₃ d t) = Nat.card K ^ 8 := by
    have h1 := h.card_sup_zpowers htM₃N htM₃
    rw [hL, (h.card_yamadaL₃_R₃ hW d hK hD).1] at h1
    exact (Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) h1).symm
  have hNc : Nat.card K ^ 8 ≤ Nat.card N := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := N) (B := yamadaL₂ d t)
      (hL₂L₃.trans hL₃N)
    rw [hsup, (h.card_yamadaL₃_R₃ hW d hK hD).1, h.card_yamadaL₂ d hK] at h1
    have h2 : Nat.card K ^ 7 ≤ Nat.card (N ⊓ yamadaL₂ d t : Subgroup G) := by
      rw [← hM₂c]
      exact Subgroup.card_le_of_le (le_inf le_sup_right (le_sup_left.trans hL₂eq.ge))
    refine Nat.le_of_mul_le_mul_right (c := 2 * Nat.card K ^ 7) ?_ (by positivity)
    calc Nat.card K ^ 8 * (2 * Nat.card K ^ 7) = 2 * Nat.card K ^ 8 * Nat.card K ^ 7 := by ring
      _ ≤ 2 * Nat.card K ^ 8 * Nat.card (N ⊓ yamadaL₂ d t : Subgroup G) :=
          Nat.mul_le_mul_left _ h2
      _ = Nat.card N * (2 * Nat.card K ^ 7) := h1
  exact (Subgroup.eq_of_le_of_card_ge hNM₃ (hM₃c ▸ hNc)).symm

theorem yamada_5_30_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaM₃ d t : Set G) := by
  obtain ⟨hNY, -, -, hJB, -⟩ := d.yamada_3_13_3_G
  obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
  have hLM : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) := by
    have := normalizer_le_normalizer_thompsonSubgroup (yamadaL₂ d t)
    rwa [h.yamada_5_13_2 d hK hD] at this
  have hNtY : L ⊓ normalizer (d.Y : Set G) ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
    fun g hg => h.centralizer_inf_normalizer_Y_le d (Subgroup.mem_inf.2
      ⟨h.L_le_centralizer (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩)
  have hNL₃ : L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaL₃ d t : Set G) :=
    (hNtY.trans (h.normalizer_tY_le d hK hD).2.2).trans
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hNM₂ : L ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaM₂ d t : Set G) :=
    (hNtY.trans (le_normalizer_yamadaL₂ d t)).trans hLM
  have hle : d.M ⊔ (d.leviB ⊔ d.J₄) ≤ L ⊓ normalizer (d.Y : Set G) := hNY.ge
  rw [h.yamadaM₃_eq_commutator_sup hW d hK hD, hNY]
  refine sup_le (fun m hm => Subgroup.le_normalizer (mem_sup_right
    (mem_sup_left hm : m ∈ yamadaM₂ d t))) (sup_le (fun b hb => ?_) fun k hk => ?_)
  · have hbN := hle (mem_sup_right (mem_sup_left hb))
    refine mem_normalizer_sup (mem_normalizer_commutator (hNL₃ hbN)
      (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk =>
        (mem_centralizer_iff.1 (hJB hk) b hb).symm))) (hNM₂ hbN)
  · have hkN := hle (mem_sup_right (mem_sup_right hk))
    exact mem_normalizer_sup (mem_normalizer_commutator (hNL₃ hkN) (Subgroup.le_normalizer hk))
      (hNM₂ hkN)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
