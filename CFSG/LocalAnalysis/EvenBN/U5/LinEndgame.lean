module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.EvenBN.Common.Endgames
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.LocalAnalysis.SteinbergBNPerfectFirstTransferExclusion

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

namespace LinCase

section SwapEndgame

variable {G : Type} [Group G]

theorem swap_map_conj_apply (n : G) (X : Subgroup G) (x : G) :
    x ∈ X.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨n⁻¹ * x * n, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem swap_mem_normalizer_of_map_eq {n : G} {X : Subgroup G}
    (h : X.map (MulAut.conj n).toMonoidHom = X) : n ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : n * x * n⁻¹ ∈ X.map (MulAut.conj n).toMonoidHom := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by simpa [MulAut.conj_apply] using hyx
    rwa [← this]

theorem swap_map_eq_of_mem_normalizer {n : G} {X : Subgroup G}
    (hn : n ∈ normalizer (X : Set G)) : X.map (MulAut.conj n).toMonoidHom = X := by
  ext x
  rw [swap_map_conj_apply]
  have := mem_normalizer_iff.1 (inv_mem hn) x
  simpa using this.symm

variable [Finite G]

theorem swap_exists_elemAb_of_not_mem {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 B) {v : G}
    (hv2 : v * v = 1) (hvN : v ∈ normalizer (B : Set G)) (hvB : v ∉ B) :
    ∃ C X : Subgroup G, C ≤ B ∧ X ≤ centralizer ({v} : Set G) ∧ CFSG.IsElementaryAbelian 2 X ∧
      Nat.card X = 2 * Nat.card C ∧ Nat.card B ≤ Nat.card C * Nat.card C := by
  classical
  haveI := hB
  have hsq : ∀ b : G, b ∈ B → b * b = 1 := fun b hb => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    simpa [sq] using this
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hmem : ∀ b : B, v * (b : G) * v⁻¹ ∈ B := fun b => (mem_normalizer_iff.1 hvN b).1 b.2
  have hcomm : ∀ a b : G, a ∈ B → b ∈ B → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : B) ⟨b, hb⟩)
  let φ : B →* B := MonoidHom.mk' (fun b => ⟨v * (b : G) * v⁻¹ * (b : G), mul_mem (hmem b) b.2⟩) (by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h1 : (a : G) * (v * (b : G) * v⁻¹) = (v * (b : G) * v⁻¹) * a :=
      hcomm _ _ a.2 (hmem b)
    have e : v * ((a : G) * b) * v⁻¹ * ((a : G) * b) =
        (v * (a : G) * v⁻¹) * (v * (b : G) * v⁻¹) * ((a : G) * b) := by group
    have e2 : (v * (a : G) * v⁻¹ * a) * (v * (b : G) * v⁻¹ * b) =
        (v * (a : G) * v⁻¹) * ((a : G) * (v * (b : G) * v⁻¹)) * b := by group
    rw [e, e2, h1]
    group)
  have hφ : ∀ b : B, ((φ b : B) : G) = v * (b : G) * v⁻¹ * (b : G) := fun b => rfl
  have hker : ∀ b : B, b ∈ φ.ker ↔ v * (b : G) = (b : G) * v := by
    intro b
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : v * (b : G) * v⁻¹ * (b : G) = 1 := by rw [← hφ]; exact congrArg Subtype.val h
      have hb2 := hsq b b.2
      have h2 : v * (b : G) * v⁻¹ = (b : G) := by
        have h3 : v * (b : G) * v⁻¹ * (b : G) * (b : G) = (b : G) := by rw [h1, one_mul]
        rwa [mul_assoc (v * (b : G) * v⁻¹), hb2, mul_one] at h3
      calc v * (b : G) = v * (b : G) * v⁻¹ * v := by group
        _ = (b : G) * v := by rw [h2]
    · intro h
      apply Subtype.ext
      show v * (b : G) * v⁻¹ * (b : G) = 1
      have h2 : v * (b : G) * v⁻¹ = (b : G) := by rw [h]; group
      rw [h2]
      exact hsq b b.2
  have hrange : φ.range ≤ φ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [hker]
    set u : G := v * (b : G) * v⁻¹ with hu
    have huB : u ∈ B := hmem b
    have hbB : (b : G) ∈ B := b.2
    have hub : u * (b : G) = (b : G) * u := hcomm _ _ huB hbB
    have hc : ((φ b : B) : G) = u * (b : G) := hφ b
    rw [hc]
    have hvu : v * u = (b : G) * v := by
      rw [hu]
      calc v * (v * (b : G) * v⁻¹) = (v * v) * (b : G) * v⁻¹ := by group
        _ = (b : G) * v⁻¹ := by rw [hv2, one_mul]
        _ = (b : G) * v := by rw [hvinv]
    have hvb : v * (b : G) = u * v := by
      rw [hu]; group
    calc v * (u * (b : G)) = (v * u) * (b : G) := by group
      _ = ((b : G) * v) * (b : G) := by rw [hvu]
      _ = (b : G) * (v * (b : G)) := by group
      _ = (b : G) * (u * v) := by rw [hvb]
      _ = ((b : G) * u) * v := by group
      _ = (u * (b : G)) * v := by rw [← hub]
  set C : Subgroup B := φ.ker with hC
  set C₀ : Subgroup G := C.map B.subtype with hC₀
  have hC₀B : C₀ ≤ B := fun x ⟨b, _, hb⟩ => hb ▸ b.2
  have hC₀cent : C₀ ≤ centralizer ({v} : Set G) := by
    rintro x ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact ((hker b).1 hb).symm
  have hvC₀ : v ∉ C₀ := fun h => hvB (hC₀B h)
  have hcardC₀ : Nat.card C₀ = Nat.card C := Subgroup.card_map_of_injective B.subtype_injective
  refine ⟨C₀, C₀ ⊔ zpowers v, hC₀B, sup_le hC₀cent (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)),
    ?_, ?_, ?_⟩
  · haveI : CFSG.IsElementaryAbelian 2 C₀ := CFSG.IsElementaryAbelian.of_le hB hC₀B
    haveI : CFSG.IsElementaryAbelian 2 (zpowers v) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hv2)
    exact CFSG.IsElementaryAbelian.sup_of_le_centralizer (E := C₀) (C := zpowers v)
      (zpowers_le.2 (mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hC₀cent hx)))
  · exact Common.SwapUnique.card_sup_zpowers_of_le_centralizer hv2 hC₀cent hvC₀
  · have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrange
    rw [hcardC₀]
    calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ Nat.card C * Nat.card C := Nat.mul_le_mul le_rfl h2

theorem swap_map_conj_mul (b t : G) (X : Subgroup G) :
    X.map (MulAut.conj (b * t)).toMonoidHom =
      (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem swap_pow_arith {q : ℕ} (hq : 4 ≤ q) : 2 * q ^ 4 < q ^ 12 ∧ 2 * q ^ 4 < 2 * q ^ 6 := by
  have h4 : 0 < q ^ 4 := by positivity
  have h8 : 2 < q ^ 8 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 8)
  have h2 : 1 < q ^ 2 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 2)
  constructor
  · calc 2 * q ^ 4 < q ^ 8 * q ^ 4 := Nat.mul_lt_mul_of_pos_right h8 h4
      _ = q ^ 12 := by ring
  · calc 2 * q ^ 4 < 2 * (q ^ 2 * q ^ 4) := by
          have := Nat.mul_lt_mul_of_pos_right h2 h4
          omega
      _ = 2 * q ^ 6 := by ring

theorem swap_endgame :
    ∀ (G : Type) [Group G] [Finite G] [Group.IsPerfect G] (f : ℕ), 2 ≤ f →
      ∀ (t : G) (B D R : Subgroup G), orderOf t = 2 → CFSG.IsElementaryAbelian 2 B →
        Nat.card B = (2 ^ f) ^ 12 → B ≠ B.map (MulAut.conj t).toMonoidHom →
        D = B ⊔ B.map (MulAut.conj t).toMonoidHom →
        (∀ Y : Subgroup G, Y ≤ D → CFSG.IsElementaryAbelian 2 Y →
          Y ≤ B ∨ Y ≤ B.map (MulAut.conj t).toMonoidHom) →
        (∀ X : Subgroup G, X ≤ centralizer ({t} : Set G) → CFSG.IsElementaryAbelian 2 X →
          Nat.card X ≤ 2 * (2 ^ f) ^ 4) →
        IsSylowOf 2 R (normalizer (D : Set G)) → D ≤ R → t ∈ R →
        (∀ Y : Subgroup G, Y ≤ R → CFSG.IsElementaryAbelian 2 Y → (2 ^ f) ^ 12 ≤ Nat.card Y →
          Y = B ∨ Y = B.map (MulAut.conj t).toMonoidHom) → False := by
  intro G _ _ _ f hf t B D R ht2 hBel hBcard hBne hD hDel hbound hR hDR htR hKC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hBel
  set Bt : Subgroup G := B.map (MulAut.conj t).toMonoidHom with hBt
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hBD : B ≤ D := hD ▸ le_sup_left
  have hBtD : Bt ≤ D := hD ▸ le_sup_right
  have hBR : B ≤ R := hBD.trans hDR
  have hBtR : Bt ≤ R := hBtD.trans hDR
  have hBt_card : Nat.card Bt = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  haveI : CFSG.IsElementaryAbelian 2 Bt := CFSG.IsElementaryAbelian.map _
  have hperm : ∀ r ∈ normalizer (R : Set G),
      (B.map (MulAut.conj r).toMonoidHom = B ∧ Bt.map (MulAut.conj r).toMonoidHom = Bt) ∨
      (B.map (MulAut.conj r).toMonoidHom = Bt ∧ Bt.map (MulAut.conj r).toMonoidHom = B) := by
    intro r hr
    have hmapR : ∀ X : Subgroup G, X ≤ R → X.map (MulAut.conj r).toMonoidHom ≤ R := by
      rintro X hX _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hr x).1 (hX hx)
    have hcard : ∀ X : Subgroup G, Nat.card X = (2 ^ f) ^ 12 →
        Nat.card (X.map (MulAut.conj r).toMonoidHom) = (2 ^ f) ^ 12 := fun X hX => by
      rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, hX]
    have h1 := hKC (B.map (MulAut.conj r).toMonoidHom) (hmapR B hBR)
      (by haveI := hBel; exact CFSG.IsElementaryAbelian.map _) (le_of_eq (hcard B hBcard).symm)
    have h2 := hKC (Bt.map (MulAut.conj r).toMonoidHom) (hmapR Bt hBtR)
      (by exact CFSG.IsElementaryAbelian.map _) (le_of_eq (hcard Bt (hBt_card.trans hBcard)).symm)
    have hne : B.map (MulAut.conj r).toMonoidHom ≠ Bt.map (MulAut.conj r).toMonoidHom := fun h =>
      hBne (Subgroup.map_injective (MulAut.conj r).injective h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  have hN : normalizer (R : Set G) ≤ normalizer (D : Set G) := by
    intro n hn
    apply swap_mem_normalizer_of_map_eq
    rcases hperm n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hD, Subgroup.map_sup, h1, h2]
    · rw [hD, Subgroup.map_sup, h1, h2, sup_comm]
  set R₀ : Subgroup G := R ⊓ normalizer (B : Set G) with hR₀
  have hR₀R : R₀ ≤ R := inf_le_left
  have hmemR₀ : ∀ r ∈ R, r ∈ R₀ ↔ B.map (MulAut.conj r).toMonoidHom = B := fun r hr =>
    ⟨fun h => swap_map_eq_of_mem_normalizer h.2, fun h => ⟨hr, swap_mem_normalizer_of_map_eq h⟩⟩
  have htR₀ : t ∉ R₀ := fun h => hBne (swap_map_eq_of_mem_normalizer h.2).symm
  have hidx : R₀.relIndex R = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, htR, fun b hb => ?_⟩
    have hbt : b * t ∈ R := mul_mem hb htR
    have e : B.map (MulAut.conj (b * t)).toMonoidHom = Bt.map (MulAut.conj b).toMonoidHom :=
      swap_map_conj_mul b t B
    rw [hmemR₀ _ hbt, hmemR₀ _ hb, e]
    rcases hperm b (le_normalizer hb) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨h1, ?_⟩
      rw [h2]
      exact fun h => hBne h.symm
    · left
      refine ⟨h2, ?_⟩
      rw [h1]
      exact fun h => hBne h.symm
  have hfus : ∀ g : G, g⁻¹ * t * g ∉ R₀ := by
    intro g hg
    set v : G := g⁻¹ * t * g with hv
    have hv2 : v * v = 1 := by
      calc v * v = g⁻¹ * (t * t) * g := by rw [hv]; group
        _ = 1 := by rw [htt]; group
    have hvR₀ := hg
    have hvN : v ∈ normalizer (B : Set G) := hg.2
    have hbound' : ∀ X : Subgroup G, X ≤ centralizer ({v} : Set G) → CFSG.IsElementaryAbelian 2 X →
        Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
      intro X hX hXel
      haveI := hXel
      have hXc : X.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have e : x * v = v * x := mem_centralizer_singleton_iff.1 (hX hx)
        calc (MulAut.conj g).toMonoidHom x * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by
              simp [MulAut.conj_apply]; group
          _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [← hv, e]
          _ = t * (MulAut.conj g).toMonoidHom x := by simp [MulAut.conj_apply]; group
      have := hbound _ hXc (CFSG.IsElementaryAbelian.map _)
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
    by_cases hvB : v ∈ B
    · have hBc : B ≤ centralizer ({v} : Set G) := by
        intro b hb
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨v, hvB⟩)
      have := hbound' B hBc hBel
      rw [hBcard] at this
      have := (swap_pow_arith hq).1
      omega
    · obtain ⟨C, X, hCB, hXc, hXel, hXcard, hBC⟩ :=
        swap_exists_elemAb_of_not_mem hBel hv2 hvN hvB
      have h1 := hbound' X hXc hXel
      rw [hXcard] at h1
      have h6 : (2 ^ f) ^ 6 ≤ Nat.card C := by
        by_contra hlt
        push Not at hlt
        have : Nat.card C * Nat.card C < (2 ^ f) ^ 6 * (2 ^ f) ^ 6 := Nat.mul_self_lt_mul_self hlt
        have e12 : (2 ^ f) ^ 6 * (2 ^ f) ^ 6 = (2 ^ f) ^ 12 := by ring
        rw [e12] at this
        omega
      have := (swap_pow_arith hq).2
      omega
  have hFT := (Common.sylow_and_firstTransferData_of_relIndex_eq_two hR hN hR₀R hidx htR htR₀ ht2
    hfus).2
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨R, R₀, t, hFT⟩

end SwapEndgame

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
