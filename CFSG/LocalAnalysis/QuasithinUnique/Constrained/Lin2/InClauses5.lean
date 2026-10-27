module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Coord9

variable {F : Type} [Field F] [Fintype F]

omit [Finite G] in
theorem Adapted.second_coord_zero {L P : Subgroup G} {n : ℕ} (A : Adapted L P n F)
    {z : G} (hzU : z ∈ blockU L) (hzc : ∀ p ∈ P, z * p = p * z) :
    Multiplicative.toAdd (A.β ⟨z, hzU⟩) 1 = 0 := by
  obtain ⟨q, hq⟩ := A.α_surj (slUpper 1)
  have hqP : (q : G) ∈ P := (A.mem_P q).2 (hq ▸ slUpper_mem_slUni 1)
  have hcomm : (q : G) * z * (q : G)⁻¹ = z := by
    have := hzc q hqP
    rw [← this]
    exact mul_inv_cancel_right z (q : G)
  have h1 := A.toAdd_beta_conj q hzU
  have e : (⟨(q : G) * z * (q : G)⁻¹, mem_blockU_conj q.2 hzU⟩ : blockU L) = ⟨z, hzU⟩ :=
    Subtype.ext hcomm
  rw [e, hq, slUpper_mulVec] at h1
  have h2 := congrFun h1 0
  simp at h2
  exact h2

end Coord9

section Clause9

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.clause9 : ∀ V : Subgroup G, centerOf (thompsonJ S) ≤ V → V ≤ blockU L →
    D ≤ Subgroup.normalizer (V : Set G) → V = centerOf (thompsonJ S) ∨ V = blockU L := by
  intro V hWV hVU hDV
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  obtain ⟨W, hWeq, -, hWcard, hWU⟩ := dat.exists_W h hx hxS
  have hWc : centerOf (thompsonJ S) = W := by
    rw [← dat.U_inf_conjU_eq_center h hx hxS, ← hWeq]
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  let ev : Multiplicative (Fin 2 → F) →* Multiplicative F :=
    AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => F) 1)
  let β₁ : blockU L →* Multiplicative F := ev.comp A.β
  have hβ₁ : ∀ u, Multiplicative.toAdd (β₁ u) = Multiplicative.toAdd (A.β u) 1 := fun _ => rfl
  have hβ₁s : Function.Surjective β₁ := by
    intro c
    obtain ⟨u, hu⟩ := A.β_surj (Multiplicative.ofAdd (![0, Multiplicative.toAdd c] : Fin 2 → F))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ₁, hu]
    simp
  have hcardF : Nat.card (Multiplicative F) = 2 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, A.card_eq]
  have hker_card : Nat.card β₁.ker * 2 ^ n = Nat.card (blockU L) := by
    have := Subgroup.card_ker_mul_card_of_surjective hβ₁s
    rwa [hcardF] at this
  have hWker : W.subgroupOf (blockU L) ≤ β₁.ker := by
    intro u hu
    have hu' : (u : G) ∈ centerOf (thompsonJ S) := by
      rw [hWc]
      exact hu
    have hcent : ∀ p ∈ S ⊓ L, (u : G) * p = p * u := fun p hp =>
      (Subgroup.mem_centralizer_iff.1 hu'.2 p (dat.P_le_R h hp)).symm
    have h0 := A.second_coord_zero u.2 hcent
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [hβ₁]
    exact h0
  have hcardW : Nat.card (W.subgroupOf (blockU L)) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv
  have hker_eq : β₁.ker = W.subgroupOf (blockU L) := by
    refine (Subgroup.eq_of_le_of_card_ge hWker ?_).symm
    rw [hcardW]
    have h2n : 0 < 2 ^ n := by positivity
    have : Nat.card β₁.ker * 2 ^ n = Nat.card W * 2 ^ n := by rw [hker_card, hWcard]
    exact (Nat.eq_of_mul_eq_mul_right h2n this).le
  rw [hWc] at hWV ⊢
  by_cases hVW : V ≤ W
  · left
    exact le_antisymm hVW hWV
  right
  have hex : ∃ v ∈ V, v ∉ W := by
    by_contra hcon
    push Not at hcon
    exact hVW hcon
  obtain ⟨v, hvV, hvW⟩ := hex
  have hvU : v ∈ blockU L := hVU hvV
  have hy₀ne : Multiplicative.toAdd (A.β ⟨v, hvU⟩) 1 ≠ 0 := by
    intro h0
    apply hvW
    have hk : (⟨v, hvU⟩ : blockU L) ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [hβ₁]
      exact h0
    rw [hker_eq] at hk
    exact hk
  have hZW : blockZ L ≤ W := by
    intro z hz
    rw [← hWc]
    refine ⟨dat.U_le_R h (blockZ_le_blockU L hz), Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hz.2 r (dat.R_le_L h hr)
  set S' : Subgroup (Multiplicative (Fin 2 → F)) := (V.subgroupOf (blockU L)).map A.β with hS'
  have hvS' : A.β ⟨v, hvU⟩ ∈ S' := Subgroup.mem_map_of_mem _ hvV
  have hℓ : ∀ c : F, Multiplicative.ofAdd (![c, 0] : Fin 2 → F) ∈ S' := by
    intro c
    obtain ⟨u, hu⟩ := A.β_surj (Multiplicative.ofAdd (![c, 0] : Fin 2 → F))
    have hk : u ∈ β₁.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [hβ₁, hu]
      simp
    rw [hker_eq] at hk
    have huV : (u : G) ∈ V := hWV hk
    rw [← hu]
    exact Subgroup.mem_map_of_mem _ huV
  have hinv : ∀ d : G, ∀ hd : d ∈ D, ∀ t ∈ S', ∃ t' ∈ S', Multiplicative.toAdd t' =
      (A.α ⟨d, h.D_le_L hd⟩ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd t) := by
    intro d hd t ht
    obtain ⟨u, huV, rfl⟩ := Subgroup.mem_map.1 ht
    have huV' : (u : G) ∈ V := huV
    have hd' : d * (u : G) * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hDV hd) u).1 huV'
    have hU' : d * (u : G) * d⁻¹ ∈ blockU L := mem_blockU_conj (h.D_le_L hd) u.2
    exact ⟨A.β ⟨d * u * d⁻¹, hU'⟩, Subgroup.mem_map_of_mem _ hd',
      A.toAdd_beta_conj ⟨d, h.D_le_L hd⟩ u.2⟩
  have hy : ∀ y : F, Multiplicative.ofAdd (![0, y] : Fin 2 → F) ∈ S' := by
    intro y
    by_cases hy0 : y = 0
    · have h1 : (Multiplicative.ofAdd (![0, y] : Fin 2 → F)) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp [hy0]
      rw [h1]
      exact S'.one_mem
    · have hu0 : Multiplicative.ofAdd
          (![0, Multiplicative.toAdd (A.β ⟨v, hvU⟩) 1] : Fin 2 → F) ∈ S' := by
        have e : Multiplicative.ofAdd (![0, Multiplicative.toAdd (A.β ⟨v, hvU⟩) 1] : Fin 2 → F) =
            A.β ⟨v, hvU⟩ * (Multiplicative.ofAdd
              (![Multiplicative.toAdd (A.β ⟨v, hvU⟩) 0, 0] : Fin 2 → F))⁻¹ := by
          apply Multiplicative.toAdd.injective
          funext i
          fin_cases i <;> simp
        rw [e]
        exact S'.mul_mem hvS' (S'.inv_mem (hℓ _))
      set y₀ : F := Multiplicative.toAdd (A.β ⟨v, hvU⟩) 1 with hy₀
      have ha0 : y₀ * y⁻¹ ≠ 0 := mul_ne_zero hy₀ne (inv_ne_zero hy0)
      obtain ⟨d, hd, hdL, hχ⟩ := h.exists_chi_eq A ha0
      obtain ⟨t', ht', hte⟩ := hinv d hd _ hu0
      have hup : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h.upper_of_mem_D A hd
      obtain ⟨hm0, hm1⟩ := mulVec_of_apply_one_zero hup
        (Multiplicative.toAdd (Multiplicative.ofAdd (![0, y₀] : Fin 2 → F)))
      have hdet := apply_zero_zero_mul_apply_one_one hup
      have h00 : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 = y₀ * y⁻¹ := hχ
      have h11 : (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 1 1 = y * y₀⁻¹ := by
        rw [h00] at hdet
        have hne : y₀ * y⁻¹ ≠ 0 := ha0
        field_simp at hdet ⊢
        linear_combination hdet
      have ht'0 : Multiplicative.toAdd t' 0 =
          (A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 * y₀ := by
        rw [hte, hm0]
        simp
      have ht'1 : Multiplicative.toAdd t' 1 = y := by
        rw [hte, hm1, h11]
        simp
        field_simp
      have e : Multiplicative.ofAdd (![0, y] : Fin 2 → F) =
          t' * (Multiplicative.ofAdd (![(A.α ⟨d, hdL⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 * y₀, 0] :
            Fin 2 → F))⁻¹ := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · simp [ht'0]
        · simp [ht'1]
      rw [e]
      exact S'.mul_mem ht' (S'.inv_mem (hℓ _))
  have htop : ∀ t : Multiplicative (Fin 2 → F), t ∈ S' := by
    intro t
    have e : t = Multiplicative.ofAdd (![Multiplicative.toAdd t 0, 0] : Fin 2 → F) *
        Multiplicative.ofAdd (![0, Multiplicative.toAdd t 1] : Fin 2 → F) := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> simp
    rw [e]
    exact S'.mul_mem (hℓ _) (hy _)
  apply le_antisymm hVU
  intro u hu
  obtain ⟨w, hwV, hwe⟩ := Subgroup.mem_map.1 (htop (A.β ⟨u, hu⟩))
  have hker : (⟨u, hu⟩ : blockU L) * w⁻¹ ∈ A.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, mul_inv_cancel]
  rw [A.β_ker] at hker
  have hZ' : ((⟨u, hu⟩ * w⁻¹ : blockU L) : G) ∈ blockZ L := hker
  have hZ : u * (w : G)⁻¹ ∈ blockZ L := by simpa using hZ'
  have hZV : u * (w : G)⁻¹ ∈ V := hWV (hZW hZ)
  have hwV' : (w : G) ∈ V := hwV
  have := V.mul_mem hZV hwV'
  simpa using this

end Clause9


end CFSG.QuasithinUnique.Lin2
