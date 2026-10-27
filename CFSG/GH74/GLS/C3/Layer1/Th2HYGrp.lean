module

public import CFSG.GroupTheory.SylowInfSup

public section

namespace CFSG.GH74.GLS.Th2.HY

open Subgroup CFSG CFSG.ABGLocalTools

variable {G : Type} [Group G]

@[expose] def twoGen (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ X ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1}

theorem twoGen_le (X : Subgroup G) : twoGen X ≤ X := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hg, -⟩
  exact hg

theorem subset_twoGen {X : Subgroup G} {g : G} (hg : g ∈ X) {k : ℕ} (h : g ^ (2 ^ k) = 1) :
    g ∈ twoGen X :=
  Subgroup.subset_closure ⟨hg, k, h⟩

theorem twoGen_le_of_forall {X W : Subgroup G}
    (h : ∀ g ∈ X, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ W) : twoGen X ≤ W := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hg, k, hk⟩
  exact h g hg k hk

theorem le_twoGen_of_isPGroup {X P : Subgroup G} (hP : IsPGroup 2 ↥P) (hPX : P ≤ X) :
    P ≤ twoGen X := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  refine subset_twoGen (hPX hg) (k := k) ?_
  have := congrArg Subtype.val hk
  simpa using this

theorem map_conj_twoGen (n : G) (X : Subgroup G) :
    (twoGen X).map (MulAut.conj n).toMonoidHom = twoGen (X.map (MulAut.conj n).toMonoidHom) := by
  unfold twoGen
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, ⟨hg, k, hk⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, k, ?_⟩
    rw [← map_pow, hk, map_one]
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    rw [← map_pow] at hk
    exact (MulAut.conj n).injective (by simpa using hk)

theorem conj_mem_of_le_normalizer {A B : Subgroup G} (hA : A ≤ normalizer (B : Set G)) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B) : a * b * a⁻¹ ∈ B :=
  (mem_normalizer_iff.mp (hA ha) b).mp hb

theorem mem_sup_iff_mul_of_le_normalizer {A B : Subgroup G} (hA : A ≤ normalizer (B : Set G))
    {g : G} : g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let T : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', a'⁻¹ * b * a' * b', B.mul_mem ?_ hb', ?_⟩
        · simpa using conj_mem_of_le_normalizer hA (A.inv_mem ha') hb
        · group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, ?_⟩
        · exact conj_mem_of_le_normalizer hA ha (B.inv_mem hb)
        · group }
  have hT : A ⊔ B = T := by
    refine le_antisymm (sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)) ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  rw [hT]
  exact Iff.rfl

theorem card_sup_mul_card_inf_of_le_normalizer [Finite G] {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAK : A ≤ A ⊔ B := le_sup_left
  have hBK : B ≤ A ⊔ B := le_sup_right
  have hKn : A ⊔ B ≤ normalizer (B : Set G) := sup_le hAB le_normalizer
  have : (B.subgroupOf (A ⊔ B)).Normal := (normal_subgroupOf_iff_le_normalizer hBK).mpr hKn
  have h1 := relIndex_sup_eq_relIndex_of_normal (B.subgroupOf (A ⊔ B)) (A.subgroupOf (A ⊔ B))
  have h2 : B.subgroupOf (A ⊔ B) ⊔ A.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← subgroupOf_sup hBK hAK, sup_comm B A, subgroupOf_self]
  rw [h2, relIndex_top_right] at h1
  have h3 := relIndex_mul_card (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  have h4 := Subgroup.index_mul_card (H := A.subgroupOf (A ⊔ B))
  have e1 : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have e2 : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  have e3 : Nat.card ↥(A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B)) = Nat.card ↥(A ⊓ B) := by
    have e : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = (A ⊓ B).subgroupOf (A ⊔ B) :=
      (Subgroup.comap_inf A B (A ⊔ B).subtype).symm
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAK)).toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = (A.subgroupOf (A ⊔ B)).relIndex (B.subgroupOf (A ⊔ B)) * Nat.card ↥A *
        Nat.card ↥(A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B)) := by
        rw [← h4, h1, e1, e3]
    _ = Nat.card ↥A * ((A.subgroupOf (A ⊔ B)).relIndex (B.subgroupOf (A ⊔ B)) *
        Nat.card ↥(A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B))) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h3, e2]

theorem twoElt_mem_sup [Finite G] {X O : Subgroup G} (hXO : X ≤ normalizer (O : Set G))
    (hO : Odd (Nat.card ↥O)) {t : G} (ht : t ∈ X ⊔ O) {k : ℕ} (htk : t ^ (2 ^ k) = 1) :
    t ∈ twoGen X ⊔ O := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hXO).mp ht
  have hpow : ∀ n : ℕ, ∃ o ∈ O, (a * b) ^ n = a ^ n * o := by
    intro n
    induction n with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨o, ho, h⟩ := ih
      refine ⟨(a⁻¹ * o * a) * b, O.mul_mem ?_ hb, ?_⟩
      · simpa using conj_mem_of_le_normalizer hXO (X.inv_mem ha) ho
      · rw [pow_succ, h, pow_succ]
        group
  obtain ⟨o, ho, h⟩ := hpow (2 ^ k)
  rw [htk] at h
  have hw : a ^ (2 ^ k) ∈ O := by
    have : a ^ (2 ^ k) = o⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact O.inv_mem ho
  have hwm : (a ^ (2 ^ k)) ^ Nat.card ↥O = 1 := by
    have := pow_card_eq_one' (G := ↥O) (x := ⟨a ^ (2 ^ k), hw⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  obtain ⟨j, hj1, hj2⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨j', hj'⟩ := (Nat.modEq_zero_iff_dvd.mp hj2)
  have ha₂ : a ^ j ∈ X := X.pow_mem ha j
  have ha₂1 : (a ^ j) ^ (2 ^ k) = 1 := by
    have : (a ^ j) ^ (2 ^ k) = ((a ^ (2 ^ k)) ^ Nat.card ↥O) ^ j' := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, hj']
      congr 1
      ring
    rw [this, hwm, one_pow]
  have hu : a⁻¹ * a ^ j ∈ O := by
    obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.mp hj1
    have : a⁻¹ * a ^ j = (a ^ (2 ^ k)) ^ (-q) := by
      rw [← zpow_neg_one, ← zpow_natCast a j, ← zpow_add, ← zpow_natCast a (2 ^ k), ← zpow_mul]
      congr 1
      push_cast at hq ⊢
      linarith
    rw [this]
    exact O.zpow_mem hw _
  have hmem : a * b = a ^ j * ((a⁻¹ * a ^ j)⁻¹ * b) := by group
  rw [hmem]
  exact Subgroup.mul_mem_sup (subset_twoGen ha₂ ha₂1) (O.mul_mem (O.inv_mem hu) hb)

theorem isSylowOf_sup_of_normalizes [Finite G] {X O S : Subgroup G}
    (hXO : X ≤ normalizer (O : Set G)) (hO : Odd (Nat.card ↥O)) (hS : IsSylowOf 2 S X) :
    IsSylowOf 2 S (X ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSX, hSp, hSidx⟩ := isSylowOf_iff.mp hS
  rw [isSylowOf_iff]
  refine ⟨hSX.trans le_sup_left, hSp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S X (X ⊔ O) hSX le_sup_left]
  have hPF := card_sup_mul_card_inf_of_le_normalizer hXO
  have h1 := relIndex_mul_card X (X ⊔ O)
  rw [inf_eq_left.mpr le_sup_left] at h1
  have hpos : 0 < Nat.card ↥X := Nat.card_pos
  have h2 : X.relIndex (X ⊔ O) * Nat.card ↥(X ⊓ O) = Nat.card ↥O := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← h1] at hPF
    calc Nat.card ↥X * (X.relIndex (X ⊔ O) * Nat.card ↥(X ⊓ O))
        = X.relIndex (X ⊔ O) * Nat.card ↥X * Nat.card ↥(X ⊓ O) := by ring
      _ = Nat.card ↥X * Nat.card ↥O := hPF
  have hodd : Odd (X.relIndex (X ⊔ O)) := hO.of_dvd_nat (Dvd.intro _ h2)
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hSidx h
  · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem isSylowOf_sup_of_prod_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {H Y R₁ R₂ : Subgroup G}
    (hHY : H ≤ normalizer (Y : Set G))
    (h₁ : IsSylowOf p R₁ H) (h₂ : IsSylowOf p R₂ Y)
    (hRp : IsPGroup p ↥(R₁ ⊔ R₂)) :
    IsSylowOf p (R₁ ⊔ R₂) (H ⊔ Y) := by
  let K : Subgroup G := H ⊔ Y
  have hR₁H : R₁ ≤ H := h₁.le
  have hR₂Y : R₂ ≤ Y := h₂.le
  have hRK : R₁ ⊔ R₂ ≤ K := sup_le (hR₁H.trans le_sup_left) (hR₂Y.trans le_sup_right)
  have hRpK : IsPGroup p ↥((R₁ ⊔ R₂).subgroupOf K) := hRp.comap_subtype
  obtain ⟨S, hRS⟩ := hRpK.exists_le_sylow
  let T : Subgroup G := (S : Subgroup K).map K.subtype
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  have hTp : IsPGroup p ↥T := S.isPGroup'.map K.subtype
  have hRT : R₁ ⊔ R₂ ≤ T := by
    intro x hx
    exact ⟨⟨x, hRK hx⟩, hRS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTH : T ⊓ H = R₁ :=
    h₁.eq_of_le (le_inf (le_sup_left.trans hRT) hR₁H) inf_le_right hTp.to_inf_left
  have hTY : T ⊓ Y = R₂ :=
    h₂.eq_of_le (le_inf (le_sup_right.trans hRT) hR₂Y) inf_le_right hTp.to_inf_left
  have hsplit := CFSG.GroupTheory.inf_sup_eq_sup_of_isSylowOf (p := p) (T := T)
    (A := H) (B := Y) hTp hHY (by rw [hTH]; exact h₁) (by rw [hTY]; exact h₂)
  have hTeq : T = R₁ ⊔ R₂ := by
    have hK : H ⊔ Y = K := rfl
    rw [hK, inf_eq_left.mpr hTK, hTH, hTY] at hsplit
    exact hsplit
  have hTsyl : IsSylowOf p T K := ⟨S, rfl⟩
  simpa [K, hTeq] using hTsyl

theorem isSylowOf_sup_of_prod [Finite G] {H Y R₁ R₂ : Subgroup G}
    (hHY : H ≤ normalizer (Y : Set G)) (hinf : Odd (Nat.card ↥(H ⊓ Y)))
    (h₁ : IsSylowOf 2 R₁ H) (h₂ : IsSylowOf 2 R₂ Y)
    (hcomm : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) : IsSylowOf 2 (R₁ ⊔ R₂) (H ⊔ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : R₁ ≤ normalizer (R₂ : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcomm a ha h hh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    · intro hh
      have h3 := hcomm a⁻¹ (R₁.inv_mem ha) _ hh
      have e : a * h * a⁻¹ = h :=
        calc a * h * a⁻¹ = a⁻¹ * (a * h * a⁻¹) * a := by rw [h3]; group
          _ = h := by group
      rwa [e] at hh
  exact isSylowOf_sup_of_prod_of_isPGroup hHY h₁ h₂
    (IsPGroup.to_sup_of_normal_right' h₁.isPGroup h₂.isPGroup hR)

end CFSG.GH74.GLS.Th2.HY
