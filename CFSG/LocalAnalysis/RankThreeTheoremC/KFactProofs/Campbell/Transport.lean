module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.GL32Facts
public import CFSG.Quasithin.MS93.ASC134Ord

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem fieldCard_sl3Order_ge {n : ℕ} (hn : 2 ≤ n) :
    60480 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 64 ≤ (2 ^ n) ^ 3 :=
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ (2 ^ n) ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
  calc 60480 = 64 * 15 * 63 := by norm_num
    _ ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)

theorem CampbellHyp.card_field_eq_two (h : CampbellHyp X K R P) {F : Type} [Field F] [Fintype F]
    {n : ℕ} (hF : Fintype.card F = 2 ^ n) (α : ↥K →* ↥(StatedSL 3 F))
    (hα : CFSG.Quasithin.IsModO2Surj K α) : Fintype.card F = 2 := by
  have h1 := CFSG.Quasithin.MS93.card_quot_of_isModO2Surj hα
  rw [h.card_quot, CFSG.Quasithin.MS93.card_statedSL3_eq hF] at h1
  have hn : 1 ≤ n := CFSG.Quasithin.MS93.one_le_of_card_eq_two_pow hF
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    simpa using hF
  · have := fieldCard_sl3Order_ge hn2
    omega
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

@[expose] def transport_coord {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') (n : ℕ) :
    Multiplicative (Fin n → Fin 3 → F) ≃* Multiplicative (Fin n → Fin 3 → F') :=
  AddEquiv.toMultiplicative
    (AddEquiv.piCongrRight fun _ : Fin n => AddEquiv.piCongrRight fun _ : Fin 3 => e.toAddEquiv)

theorem transport_coord_apply {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') (n : ℕ)
    (x : Multiplicative (Fin n → Fin 3 → F)) (i : Fin n) (j : Fin 3) :
    Multiplicative.toAdd (transport_coord e n x) i j = e (Multiplicative.toAdd x i j) := rfl

theorem transport_mulVec_map {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    (M : Matrix (Fin 3) (Fin 3) F) (w : Fin 3 → F) :
    (fun j => e ((M.mulVec w) j)) = (M.map e).mulVec (fun j => e (w j)) := by
  funext j
  exact RingHom.map_mulVec e.toRingHom M w j

theorem transport_map_bijective {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    Function.Bijective (Matrix.GeneralLinearGroup.map (n := Fin 3) e.toRingHom) := by
  constructor
  · intro x y h
    ext i j
    have := congrArg (fun z : GL (Fin 3) F' => (z : Matrix (Fin 3) (Fin 3) F') i j) h
    simpa using this
  · intro y
    refine ⟨Matrix.GeneralLinearGroup.map (n := Fin 3) e.symm.toRingHom y, ?_⟩
    ext i j
    simp

theorem transport_section_data {K D : Subgroup A} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥K →* ↥(StatedSL 3 F)}
    (hα : CFSG.Quasithin.IsModO2Surj K α) (n : ℕ)
    (β : ↥D →* Multiplicative (Fin n → Fin 3 → F)) :
    ∃ (a : ↥K →* GL32) (b : ↥D →* Multiplicative (Fin n → Fin 3 → ZMod 2)),
      Function.Surjective a ∧ a.ker = CFSG.pCore 2 ↥K ∧
      (Function.Surjective β → Function.Surjective b) ∧ b.ker = β.ker ∧
      ∀ (k : ↥K) (u v : ↥D),
        (∀ i : Fin n, Multiplicative.toAdd (β v) i =
          (((α k : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
            (Multiplicative.toAdd (β u) i)) →
        ∀ i : Fin n, Multiplicative.toAdd (b v) i =
          ((a k : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            (Multiplicative.toAdd (b u) i) := by
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  have hbij := transport_map_bijective e
  let g : GL (Fin 3) F →* GL32 := Matrix.GeneralLinearGroup.map (n := Fin 3) e.toRingHom
  have htop : StatedSL 3 F = ⊤ := statedSL_eq_top_of_card_two hF
  refine ⟨(g.comp (StatedSL 3 F).subtype).comp α, (transport_coord e n).toMonoidHom.comp β,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    have hxmem : x ∈ StatedSL 3 F := by rw [htop]; exact Subgroup.mem_top x
    obtain ⟨k, hk⟩ := hα.1 ⟨x, hxmem⟩
    exact ⟨k, by simp only [MonoidHom.comp_apply, hk]; exact hx⟩
  · rw [MonoidHom.ker_comp_of_injective α _ (hbij.1.comp Subtype.val_injective)]
    exact hα.2
  · exact fun hβ => (transport_coord e n).surjective.comp hβ
  · exact MonoidHom.ker_comp_of_injective β _ (transport_coord e n).injective
  · intro k u v h i
    funext j
    have hv := h i
    have hmap : (((g ((StatedSL 3 F).subtype (α k)) : GL32)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (((α k : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map e := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, transport_coord_apply]
    rw [hmap, hv]
    exact congrFun (transport_mulVec_map e _ (Multiplicative.toAdd (β u) i)) j

theorem hasNatSection_of_via {K D C₀ : Subgroup A} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥K →* ↥(StatedSL 3 F)} (hα : CFSG.Quasithin.IsModO2Surj K α)
    (hsec : CFSG.Quasithin.IsSumOfNaturalModulesVia K D C₀ α false 1) :
    HasNatSection K D C₀ := by
  obtain ⟨hKN, hC₀, β, hβs, hβk, hβe⟩ := hsec
  obtain ⟨a, b, ha, hak, hb, hbk, hbe⟩ := transport_section_data hF hα 1 β
  let c : Multiplicative (Fin 1 → Fin 3 → ZMod 2) ≃* Multiplicative (Fin 3 → ZMod 2) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → ZMod 2))
  refine ⟨hKN, hC₀, a, c.toMonoidHom.comp b, ha, hak, c.surjective.comp (hb hβs), ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective b _ c.injective, hbk, hβk]
  · intro k u v huv
    have := hbe k u v (fun i => by simpa [CFSG.Quasithin.moduleAct] using hβe k u v huv i) 0
    exact this

theorem hasNatSum2_of_via {K Q : Subgroup A} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥K →* ↥(StatedSL 3 F)} (hα : CFSG.Quasithin.IsModO2Surj K α)
    (hsec : CFSG.Quasithin.IsSumOfNaturalModulesVia K Q ⊥ α false 2) : HasNatSum2 K Q := by
  obtain ⟨hKN, -, β, hβs, hβk, hβe⟩ := hsec
  obtain ⟨a, b, ha, hak, hb, hbk, hbe⟩ := transport_section_data hF hα 2 β
  refine ⟨hKN, a, b, ha, hak, hb hβs, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, hbk, hβk, Subgroup.bot_subgroupOf]
  · intro k u v huv i
    exact hbe k u v (fun i => by simpa [CFSG.Quasithin.moduleAct] using hβe k u v huv i) i
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
