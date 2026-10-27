module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open scoped Pointwise commutatorElement

variable {Q : Type*} [Group Q]

theorem inf_centralizer_ne_bot_of_isPGroup [Finite Q] {p : ℕ} [Fact p.Prime] {P Y : Subgroup Q}
    (hP : IsPGroup p P) (hY : IsPGroup p Y) (hY1 : Y ≠ ⊥)
    (hPY : P ≤ normalizer (Y : Set Q)) : Y ⊓ centralizer (P : Set Q) ≠ ⊥ := by
  set H : Subgroup Q := Y ⊔ P with hHdef
  have hH : IsPGroup p H := hY.to_sup_of_normal_left' hP hPY
  have : Group.IsNilpotent H := hH.isNilpotent
  have hYH : Y ≤ H := le_sup_left
  have hnorm : (Y.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYH).2 (sup_le le_normalizer hPY)
  have hne : Y.subgroupOf H ≠ ⊥ := by
    intro h
    apply hY1
    have e := Subgroup.subgroupOf_map_subtype Y H
    rw [h, Subgroup.map_bot, inf_of_le_left hYH] at e
    exact e.symm
  obtain ⟨a, ha⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hY', hC'⟩ := mem_inf.1 a.2
  intro hbot
  have hY'' : ((a : H) : Q) ∈ Y := mem_subgroupOf.1 hY'
  have hC'' : ((a : H) : Q) ∈ centralizer (P : Set Q) := by
    rw [mem_centralizer_iff]
    intro x hx
    have := (mem_center_iff.1 hC') ⟨x, (le_sup_right : P ≤ Y ⊔ P) hx⟩
    exact (congrArg Subtype.val this)
  have hmem : ((a : H) : Q) ∈ Y ⊓ centralizer (P : Set Q) := mem_inf.2 ⟨hY'', hC''⟩
  rw [hbot, mem_bot] at hmem
  exact ha (Subtype.ext (Subtype.ext hmem))

theorem map_inf_centralizer (e : MulAut Q) (X H : Subgroup Q) :
    (X ⊓ centralizer (H : Set Q)).map e.toMonoidHom =
      X.map e.toMonoidHom ⊓ centralizer ((H.map e.toMonoidHom : Subgroup Q) : Set Q) := by
  ext y
  rw [mem_map_equiv, mem_inf, mem_inf, mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨hX, hC⟩
    refine ⟨hX, fun h hh => ?_⟩
    rw [SetLike.mem_coe, mem_map_equiv] at hh
    have := congrArg e (hC _ hh)
    simpa using this
  · rintro ⟨hX, hC⟩
    refine ⟨hX, fun h hh => ?_⟩
    have hh' : e h ∈ ((H.map e.toMonoidHom : Subgroup Q) : Set Q) := by
      rw [SetLike.mem_coe, mem_map_equiv]
      simpa using hh
    have := congrArg e.symm (hC _ hh')
    simpa using this

theorem map_conj_of_normal (H : Subgroup Q) [H.Normal] (g : Q) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_equiv]
  constructor
  · intro hy
    have := ‹H.Normal›.conj_mem _ hy g
    rwa [show g * (MulAut.conj g).symm y * g⁻¹ = y by simp [MulAut.conj_symm_apply]; group]
      at this
  · intro hy
    have := ‹H.Normal›.conj_mem _ hy g⁻¹
    simpa [MulAut.conj_symm_apply] using this

theorem mem_normalizer_of_normal (H : Subgroup Q) [H.Normal] (g : Q) :
    g ∈ normalizer (H : Set Q) := by
  rw [normalizer_eq_top H]
  exact mem_top g

theorem centralizer_sup_eq (A B : Subgroup Q) :
    centralizer ((A ⊔ B : Subgroup Q) : Set Q) =
      centralizer (A : Set Q) ⊓ centralizer (B : Set Q) := by
  refine le_antisymm (le_inf (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
    (centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))) fun x hx => ?_
  have h1 : zpowers x ≤ centralizer (A : Set Q) := (zpowers_le).2 (mem_inf.1 hx).1
  have h2 : zpowers x ≤ centralizer (B : Set Q) := (zpowers_le).2 (mem_inf.1 hx).2
  rw [le_centralizer_iff] at h1 h2
  have h3 : A ⊔ B ≤ centralizer ((zpowers x : Subgroup Q) : Set Q) := sup_le h1 h2
  rw [le_centralizer_iff] at h3
  exact h3 (mem_zpowers x)

variable [Finite Q]

theorem card_mul_card_le_card_sup_mul_card_inf (A B : Subgroup Q) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  have e1 : A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
    rw [Subgroup.relIndex_mul_card]
  have e2 : A.relIndex (A ⊔ B) * Nat.card A = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.relIndex_mul_card A (A ⊔ B)
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hne0 : A.relIndex (A ⊔ B) ≠ 0 := by
    intro h
    rw [h] at e2
    have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have hle : A.relIndex B ≤ A.relIndex (A ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_right hne0
  calc Nat.card A * Nat.card B = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by rw [e1]
    _ ≤ Nat.card A * (A.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ B)) := by gcongr
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [← e2]; ring

theorem exists_split {σ : MulAut Q} {X Λ V F : Subgroup Q} {r : Q} {q : ℕ} (hq : 2 ≤ q)
    [X.Normal] [Λ.Normal] (hσX : X.map σ.toMonoidHom = X) (hcen : X ⊓ center Q = ⊥)
    (hΛσ : Λ ⊔ Λ.map σ.toMonoidHom = ⊤)
    (hV : IsPGroup 2 V) (hVΛ : V ≤ Λ) (hXV : X ≤ V)
    (hrΛ : r ∈ normalizer (Λ : Set Q))
    (hgen : Λ ≤ V ⊔ V.map (MulAut.conj r).toMonoidHom)
    (hVn : V ≤ normalizer
      (((V.map σ.toMonoidHom).map (MulAut.conj r).toMonoidHom : Subgroup Q) : Set Q))
    (hFX : F ≤ X) (hFV : F ≤ centralizer (V : Set Q)) (hσF : F.map σ.toMonoidHom = F)
    (hFr : F ⊓ F.map (MulAut.conj r).toMonoidHom = ⊥)
    (hFS : ∀ B : Subgroup Q, B ≤ X → B.Normal →
      ¬ Λ.map σ.toMonoidHom ≤ centralizer (B : Set Q) → q ^ 2 ≤ Nat.card B)
    (hcX : Nat.card X = q ^ 4) (hcF : q ^ 2 ≤ Nat.card F) :
    (X ⊓ centralizer (Λ : Set Q)) ⊔ (X ⊓ centralizer (Λ : Set Q)).map σ.toMonoidHom = X ∧
      (X ⊓ centralizer (Λ : Set Q)) ⊓ (X ⊓ centralizer (Λ : Set Q)).map σ.toMonoidHom = ⊥ ∧
      Nat.card (X ⊓ centralizer (Λ : Set Q) : Subgroup Q) = q ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : MulAut Q := MulAut.conj r with hρ
  set B : Subgroup Q := X ⊓ centralizer (Λ : Set Q) with hBdef
  set D : Subgroup Q := X ⊓ centralizer (V : Set Q) with hDdef
  set W' : Subgroup Q := (V.map σ.toMonoidHom).map ρ.toMonoidHom with hW'
  set D' : Subgroup Q := X ⊓ centralizer (W' : Set Q) with hD'def
  have hXρ : X.map ρ.toMonoidHom = X := by
    rw [hρ]
    exact map_conj_of_normal _ r
  have hΛρ : Λ.map ρ.toMonoidHom = Λ := by
    rw [hρ]
    exact map_conj_of_normal _ r
  have hD' : D' = (D.map σ.toMonoidHom).map ρ.toMonoidHom := by
    rw [hDdef, map_inf_centralizer, map_inf_centralizer, hσX, hXρ]
  have hFD : F ≤ D := le_inf hFX hFV
  have hFrD' : F.map ρ.toMonoidHom ≤ D' := by
    rw [hD']
    refine map_mono ?_
    rw [← hσF]
    exact map_mono hFD
  have hX2 : IsPGroup 2 X := hV.to_le hXV
  have hFne : F ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcF
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have hDF : ¬ D ≤ F := by
    intro hle
    have hD'le : D' ≤ F.map ρ.toMonoidHom := by
      rw [hD']
      refine map_mono ?_
      rw [← hσF]
      exact map_mono hle
    have hD'ne : D' ≠ ⊥ := by
      intro h
      apply hFne
      have : F.map ρ.toMonoidHom = ⊥ := le_bot_iff.1 (h ▸ hFrD')
      exact (map_eq_bot_iff_of_injective _ ρ.injective).1 this
    have hD'2 : IsPGroup 2 D' := hX2.to_le inf_le_left
    have hVD' : V ≤ normalizer (D' : Set Q) := by
      intro v hv
      rw [mem_normalizer_iff]
      intro x
      have hvX : v ∈ normalizer (X : Set Q) := mem_normalizer_of_normal X v
      have hvW : v ∈ normalizer (W' : Set Q) := hVn hv
      rw [mem_inf, mem_inf]
      constructor
      · rintro ⟨hxX, hxC⟩
        refine ⟨(mem_normalizer_iff.1 hvX x).1 hxX, ?_⟩
        rw [mem_centralizer_iff] at hxC ⊢
        intro w hw
        have hw' : v⁻¹ * w * v⁻¹⁻¹ ∈ W' := (mem_normalizer_iff.1 (inv_mem hvW) w).1 hw
        have := hxC _ hw'
        calc w * (v * x * v⁻¹) = v * ((v⁻¹ * w * v⁻¹⁻¹) * x) * v⁻¹ := by group
          _ = v * (x * (v⁻¹ * w * v⁻¹⁻¹)) * v⁻¹ := by rw [this]
          _ = v * x * v⁻¹ * w := by group
      · rintro ⟨hxX, hxC⟩
        refine ⟨(mem_normalizer_iff.1 hvX x).2 hxX, ?_⟩
        rw [mem_centralizer_iff] at hxC ⊢
        intro w hw
        have hw' : v * w * v⁻¹ ∈ W' := (mem_normalizer_iff.1 hvW w).1 hw
        have := hxC _ hw'
        have e1 : v * (w * x) * v⁻¹ = v * (x * w) * v⁻¹ := by
          calc v * (w * x) * v⁻¹ = (v * w * v⁻¹) * (v * x * v⁻¹) := by group
            _ = (v * x * v⁻¹) * (v * w * v⁻¹) := this
            _ = v * (x * w) * v⁻¹ := by group
        have e2 : w * x = x * w := by
          have := congrArg (fun z => v⁻¹ * z * v) e1
          simpa [mul_assoc] using this
        exact e2
    have hne := inf_centralizer_ne_bot_of_isPGroup hV hD'2 hD'ne hVD'
    apply hne
    rw [eq_bot_iff, ← hFr]
    intro x hx
    obtain ⟨hxD', hxC⟩ := mem_inf.1 hx
    have hxD : x ∈ D := mem_inf.2 ⟨(mem_inf.1 hxD').1, hxC⟩
    exact mem_inf.2 ⟨hle hxD, hD'le hxD'⟩
  have hcD : 2 * Nat.card F ≤ Nat.card D := by
    have hD2 : IsPGroup 2 D := hX2.to_le inf_le_left
    have hidx := relIndex_mul_card F D
    rw [inf_of_le_left hFD] at hidx
    have hne1 : F.relIndex D ≠ 1 := fun h => hDF (relIndex_eq_one.1 h)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hD2
    have hdvd : F.relIndex D ∣ 2 ^ k := hk ▸ Dvd.intro _ hidx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne1 hj
    have : 2 ≤ F.relIndex D := by
      rw [hj]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj0)
    calc 2 * Nat.card F ≤ F.relIndex D * Nat.card F := Nat.mul_le_mul_right _ this
      _ = Nat.card D := hidx
  have hDr : D.map ρ.toMonoidHom =
      X ⊓ centralizer ((V.map ρ.toMonoidHom : Subgroup Q) : Set Q) := by
    rw [hDdef, map_inf_centralizer, hXρ]
  have hBD : B = D ⊓ D.map ρ.toMonoidHom := by
    rw [hDr]
    refine le_antisymm (le_inf (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hVΛ)))
      (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 ?_)))) ?_
    · rw [← hΛρ]
      exact map_mono hVΛ
    · intro x hx
      obtain ⟨⟨hxX, hxC₁⟩, ⟨-, hxC₂⟩⟩ := hx
      refine mem_inf.2 ⟨hxX, ?_⟩
      have : x ∈ centralizer ((V ⊔ V.map ρ.toMonoidHom : Subgroup Q) : Set Q) := by
        rw [centralizer_sup_eq]
        exact mem_inf.2 ⟨hxC₁, hxC₂⟩
      exact centralizer_le (SetLike.coe_subset_coe.2 hgen) this
  have hcDr : Nat.card (D.map ρ.toMonoidHom) = Nat.card D :=
    card_map_of_injective ρ.injective
  have hcB4 : 4 * Nat.card (⊥ : Subgroup Q) < Nat.card B + 1 := by
    have h1 : Nat.card D * Nat.card (D.map ρ.toMonoidHom) ≤
        Nat.card (D ⊔ D.map ρ.toMonoidHom : Subgroup Q) *
          Nat.card (D ⊓ D.map ρ.toMonoidHom : Subgroup Q) :=
      card_mul_card_le_card_sup_mul_card_inf D (D.map ρ.toMonoidHom)
    have h2 : Nat.card (D ⊔ D.map ρ.toMonoidHom : Subgroup Q) ≤ Nat.card X :=
      card_le_of_le (sup_le inf_le_left (by rw [hDr]; exact inf_le_left))
    rw [hcDr, ← hBD] at h1
    rw [card_bot]
    have h3 : (2 * q ^ 2) * (2 * q ^ 2) ≤ Nat.card D * Nat.card D := by
      have : 2 * q ^ 2 ≤ Nat.card D := le_trans (Nat.mul_le_mul_left 2 hcF) hcD
      exact Nat.mul_le_mul this this
    have h4 : Nat.card D * Nat.card D ≤ q ^ 4 * Nat.card B := by
      calc Nat.card D * Nat.card D ≤ _ := h1
        _ ≤ Nat.card X * Nat.card B := Nat.mul_le_mul_right _ h2
        _ = q ^ 4 * Nat.card B := by rw [hcX]
    have hq4 : 0 < q ^ 4 := by positivity
    have : 4 * q ^ 4 ≤ q ^ 4 * Nat.card B := by
      calc 4 * q ^ 4 = (2 * q ^ 2) * (2 * q ^ 2) := by ring
        _ ≤ _ := h3.trans h4
    have : 4 ≤ Nat.card B := Nat.le_of_mul_le_mul_left (by rwa [mul_comm] at this) hq4
    omega
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcB4
    omega
  have hσB : B.map σ.toMonoidHom =
      X ⊓ centralizer ((Λ.map σ.toMonoidHom : Subgroup Q) : Set Q) := by
    rw [hBdef, map_inf_centralizer, hσX]
  have hBσB : B ⊓ B.map σ.toMonoidHom = ⊥ := by
    rw [hσB, eq_bot_iff, ← hcen]
    intro x hx
    obtain ⟨⟨hxX, hxC₁⟩, ⟨-, hxC₂⟩⟩ := hx
    refine mem_inf.2 ⟨hxX, ?_⟩
    have : x ∈ centralizer ((Λ ⊔ Λ.map σ.toMonoidHom : Subgroup Q) : Set Q) := by
      rw [centralizer_sup_eq]
      exact mem_inf.2 ⟨hxC₁, hxC₂⟩
    rw [hΛσ] at this
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.1 this) g (mem_top g)
  have hBn : B.Normal := by
    rw [hBdef]
    infer_instance
  have hnc : ¬ Λ.map σ.toMonoidHom ≤ centralizer (B : Set Q) := by
    intro hle
    apply hBne
    rw [eq_bot_iff, ← hBσB]
    intro x hx
    refine mem_inf.2 ⟨hx, ?_⟩
    rw [hσB]
    refine mem_inf.2 ⟨(mem_inf.1 hx).1, ?_⟩
    rw [mem_centralizer_iff]
    intro g hg
    exact ((mem_centralizer_iff.1 (hle hg)) x hx).symm
  have hcB := hFS B inf_le_left hBn hnc
  have hcσB : Nat.card (B.map σ.toMonoidHom) = Nat.card B := card_map_of_injective σ.injective
  have hle : B ⊔ B.map σ.toMonoidHom ≤ X := sup_le inf_le_left (by rw [hσB]; exact inf_le_left)
  have hprod := card_mul_card_le_card_sup_mul_card_inf B (B.map σ.toMonoidHom)
  rw [hBσB, card_bot, mul_one, hcσB] at hprod
  have hsupc : Nat.card (B ⊔ B.map σ.toMonoidHom : Subgroup Q) ≤ q ^ 4 := hcX ▸ card_le_of_le hle
  have hB2 : Nat.card B * Nat.card B ≤ q ^ 2 * q ^ 2 := by
    calc Nat.card B * Nat.card B ≤ _ := hprod
      _ ≤ q ^ 4 := hsupc
      _ = q ^ 2 * q ^ 2 := by ring
  have hBc : Nat.card B = q ^ 2 := le_antisymm (Nat.mul_self_le_mul_self_iff.1 hB2) hcB
  refine ⟨?_, hBσB, hBc⟩
  refine eq_of_le_of_card_ge hle ?_
  rw [hcX]
  calc q ^ 4 = Nat.card B * Nat.card B := by rw [hBc]; ring
    _ ≤ _ := hprod

theorem commutatorElement_mem_centralizer_of_stability {H A : Subgroup Q}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {j₁ j₂ : Q}
    (h₁ : j₁ ∈ normalizer (H : Set Q)) (h₂ : j₂ ∈ normalizer (H : Set Q))
    (hA₁ : ∀ a ∈ A, j₁ * a = a * j₁) (hA₂ : ∀ a ∈ A, j₂ * a = a * j₂)
    (hH₁ : ∀ h ∈ H, h⁻¹ * (j₁ * h * j₁⁻¹) ∈ A) (hH₂ : ∀ h ∈ H, h⁻¹ * (j₂ * h * j₂⁻¹) ∈ A) :
    j₁ * j₂ * j₁⁻¹ * j₂⁻¹ ∈ centralizer (H : Set Q) := by
  have key : ∀ h ∈ H, (j₁ * j₂) * h * (j₁ * j₂)⁻¹ = (j₂ * j₁) * h * (j₂ * j₁)⁻¹ := by
    intro h hh
    have hd₁ := hH₁ h hh
    have hd₂ := hH₂ h hh
    have c₁ : j₁ * (h⁻¹ * (j₂ * h * j₂⁻¹)) * j₁⁻¹ = h⁻¹ * (j₂ * h * j₂⁻¹) := by
      rw [hA₁ _ hd₂]; group
    have c₂ : j₂ * (h⁻¹ * (j₁ * h * j₁⁻¹)) * j₂⁻¹ = h⁻¹ * (j₁ * h * j₁⁻¹) := by
      rw [hA₂ _ hd₁]; group
    have hc := hAab _ hd₁ _ hd₂
    calc (j₁ * j₂) * h * (j₁ * j₂)⁻¹
        = (j₁ * h * j₁⁻¹) * (j₁ * (h⁻¹ * (j₂ * h * j₂⁻¹)) * j₁⁻¹) := by group
      _ = h * ((h⁻¹ * (j₁ * h * j₁⁻¹)) * (h⁻¹ * (j₂ * h * j₂⁻¹))) := by rw [c₁]; group
      _ = h * ((h⁻¹ * (j₂ * h * j₂⁻¹)) * (h⁻¹ * (j₁ * h * j₁⁻¹))) := by rw [hc]
      _ = (j₂ * h * j₂⁻¹) * (j₂ * (h⁻¹ * (j₁ * h * j₁⁻¹)) * j₂⁻¹) := by rw [c₂]; group
      _ = (j₂ * j₁) * h * (j₂ * j₁)⁻¹ := by group
  rw [mem_centralizer_iff]
  intro g hg
  have hj : j₂ * j₁ ∈ normalizer (H : Set Q) := mul_mem h₂ h₁
  have hh : (j₂ * j₁)⁻¹ * g * (j₂ * j₁)⁻¹⁻¹ ∈ H := (mem_normalizer_iff.1 (inv_mem hj) g).1 hg
  have e := key _ hh
  rw [show (j₂ * j₁) * ((j₂ * j₁)⁻¹ * g * (j₂ * j₁)⁻¹⁻¹) * (j₂ * j₁)⁻¹ = g by group] at e
  calc g * (j₁ * j₂ * j₁⁻¹ * j₂⁻¹) =
      ((j₁ * j₂) * ((j₂ * j₁)⁻¹ * g * (j₂ * j₁)⁻¹⁻¹) * (j₁ * j₂)⁻¹) *
        (j₁ * j₂ * j₁⁻¹ * j₂⁻¹) := by rw [e]
    _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ * g := by group

theorem le_centralizer_of_stability {H A J : Subgroup Q}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hJ : ⁅J, J⁆ = J)
    (hJN : J ≤ normalizer (H : Set Q)) (hJA : ∀ j ∈ J, ∀ a ∈ A, j * a = a * j)
    (hJH : ∀ j ∈ J, ∀ h ∈ H, h⁻¹ * (j * h * j⁻¹) ∈ A) :
    J ≤ centralizer (H : Set Q) := by
  rw [← hJ, commutator_le]
  intro j₁ hj₁ j₂ hj₂
  rw [commutatorElement_def]
  exact commutatorElement_mem_centralizer_of_stability hAab (hJN hj₁) (hJN hj₂)
    (hJA j₁ hj₁) (hJA j₂ hj₂) (hJH j₁ hj₁) (hJH j₂ hj₂)

theorem commutator_sup_le_of_le_centralizer {K B : Subgroup Q}
    (hB : B ≤ centralizer ((K ⊔ B : Subgroup Q) : Set Q)) :
    ⁅K ⊔ B, K ⊔ B⁆ ≤ ⁅K, K⁆ := by
  have hzB : ∀ b ∈ B, ∀ y ∈ K ⊔ B, y * b = b * y := fun b hb y hy =>
    (mem_centralizer_iff.1 (hB hb)) y hy
  have hKC : K ≤ centralizer (B : Set Q) := by
    have := le_centralizer_iff.1 hB
    exact le_sup_left.trans this
  have hKN : K ≤ normalizer (B : Set Q) := hKC.trans (centralizer_le_normalizer _)
  have hKB := coe_mul_of_left_le_normalizer_right K B hKN
  have hdec : ∀ x ∈ K ⊔ B, ∃ k ∈ K, ∃ b ∈ B, x = k * b := by
    intro x hx
    rw [← SetLike.mem_coe, hKB] at hx
    obtain ⟨k, hk, b, hb, rfl⟩ := Set.mem_mul.1 hx
    exact ⟨k, hk, b, hb, rfl⟩
  rw [commutator_le]
  intro a ha c hc
  obtain ⟨k₁, hk₁, b₁, hb₁, rfl⟩ := hdec a ha
  obtain ⟨k₂, hk₂, b₂, hb₂, rfl⟩ := hdec c hc
  have h1 : b₁ * k₂ = k₂ * b₁ := (hzB b₁ hb₁ k₂ (mem_sup_left hk₂)).symm
  have h2 : b₁ * b₂ = b₂ * b₁ := (hzB b₁ hb₁ b₂ (mem_sup_right hb₂)).symm
  have h3 : b₂ * k₁⁻¹ = k₁⁻¹ * b₂ := (hzB b₂ hb₂ k₁⁻¹ (inv_mem (mem_sup_left hk₁))).symm
  have e : ⁅k₁ * b₁, k₂ * b₂⁆ = ⁅k₁, k₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc k₁ * b₁ * (k₂ * b₂) * (k₁ * b₁)⁻¹ * (k₂ * b₂)⁻¹
        = k₁ * (b₁ * k₂) * (b₂ * b₁⁻¹) * k₁⁻¹ * b₂⁻¹ * k₂⁻¹ := by group
      _ = k₁ * (k₂ * b₁) * (b₂ * b₁⁻¹) * k₁⁻¹ * b₂⁻¹ * k₂⁻¹ := by rw [h1]
      _ = k₁ * k₂ * ((b₁ * b₂) * b₁⁻¹) * k₁⁻¹ * b₂⁻¹ * k₂⁻¹ := by group
      _ = k₁ * k₂ * ((b₂ * b₁) * b₁⁻¹) * k₁⁻¹ * b₂⁻¹ * k₂⁻¹ := by rw [h2]
      _ = k₁ * k₂ * (b₂ * k₁⁻¹) * b₂⁻¹ * k₂⁻¹ := by group
      _ = k₁ * k₂ * (k₁⁻¹ * b₂) * b₂⁻¹ * k₂⁻¹ := by rw [h3]
      _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by group
  rw [e]
  exact commutator_mem_commutator hk₁ hk₂

theorem normal_inf_centralizer (X H : Subgroup Q) [X.Normal] [H.Normal] :
    (X ⊓ centralizer (H : Set Q)).Normal := by
  refine ⟨fun x hx g => mem_inf.2 ⟨‹X.Normal›.conj_mem x (mem_inf.1 hx).1 g, ?_⟩⟩
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh g⁻¹
  have := (mem_centralizer_iff.1 (mem_inf.1 hx).2) _ hh'
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * h := by group

theorem commutator_eq_bot_of_split {σ : MulAut Q} {X Λ Y P : Subgroup Q} [X.Normal] [Λ.Normal]
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hσX : X.map σ.toMonoidHom = X)
    (hcomm : ⁅Λ, Λ.map σ.toMonoidHom⁆ ≤ X)
    (hsplit : (X ⊓ centralizer (Λ : Set Q)) ⊔ (X ⊓ centralizer (Λ : Set Q)).map σ.toMonoidHom = X)
    (hYX : Y ⊓ X = ⊥) (hYsup : Y ⊔ X = Λ)
    (hPΛ : P ≤ ⁅Λ, Λ⁆) (hP : ⁅P, P⁆ = P) [P.Normal] :
    ⁅P, P.map σ.toMonoidHom⁆ = ⊥ := by
  set B : Subgroup Q := X ⊓ centralizer (Λ : Set Q) with hBdef
  have hΛσn : (Λ.map σ.toMonoidHom).Normal := Subgroup.Normal.map ‹Λ.Normal› _ σ.surjective
  have hσB : B.map σ.toMonoidHom =
      X ⊓ centralizer ((Λ.map σ.toMonoidHom : Subgroup Q) : Set Q) := by
    rw [hBdef, map_inf_centralizer, hσX]
  set Bσ : Subgroup Q := X ⊓ centralizer ((Λ.map σ.toMonoidHom : Subgroup Q) : Set Q)
    with hBσdef
  have hsplit' : B ⊔ Bσ = X := by rw [← hσB]; exact hsplit
  have hBσn : Bσ.Normal := normal_inf_centralizer _ _
  have hBσX : Bσ ≤ X := inf_le_left
  have hΛeq : (Y ⊔ Bσ) ⊔ B = Λ := by
    rw [← hYsup, ← hsplit', sup_assoc, sup_comm Bσ B]
  have hBc : B ≤ centralizer (((Y ⊔ Bσ) ⊔ B : Subgroup Q) : Set Q) := by
    rw [hΛeq]
    exact inf_le_right
  have hself : ∀ K : Subgroup Q, ⁅K, K⁆ ≤ K := fun K => by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hΛΛ : ⁅Λ, Λ⁆ ≤ Y ⊔ Bσ := by
    rw [← hΛeq]
    exact (commutator_sup_le_of_le_centralizer hBc).trans (hself _)
  have hYN : Y ≤ normalizer (Bσ : Set Q) := fun y _ => mem_normalizer_of_normal Bσ y
  have hYB := coe_mul_of_left_le_normalizer_right Y Bσ hYN
  have hPX : P ⊓ X ≤ Bσ := by
    intro x hx
    obtain ⟨hxP, hxX⟩ := mem_inf.1 hx
    have hxK : x ∈ ((Y ⊔ Bσ : Subgroup Q) : Set Q) := hΛΛ (hPΛ hxP)
    rw [hYB] at hxK
    obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.1 hxK
    have hyX : y ∈ X := by
      have := mul_mem hxX (inv_mem (hBσX hb))
      rwa [mul_inv_cancel_right] at this
    have hy1 : y = 1 := by
      have : y ∈ Y ⊓ X := mem_inf.2 ⟨hy, hyX⟩
      rwa [hYX, mem_bot] at this
    rw [hy1, one_mul]
    exact hb
  have hPΛ' : P ≤ Λ := hPΛ.trans (commutator_le_left _ _)
  have hσPΛ : P.map σ.toMonoidHom ≤ Λ.map σ.toMonoidHom := map_mono hPΛ'
  have hJ : ⁅P.map σ.toMonoidHom, P.map σ.toMonoidHom⁆ = P.map σ.toMonoidHom := by
    rw [← map_commutator, hP]
  have hle := le_centralizer_of_stability (H := P) (A := P ⊓ X) (J := P.map σ.toMonoidHom)
    (fun a ha b hb => hXab a (mem_inf.1 ha).2 b (mem_inf.1 hb).2) hJ
    (fun j _ => mem_normalizer_of_normal P j)
    (fun j hj a ha => by
      have haC := (mem_inf.1 (hPX ha)).2
      exact ((mem_centralizer_iff.1 haC) j (hσPΛ hj)))
    (fun j hj h hh => by
      refine mem_inf.2 ⟨mul_mem (inv_mem hh) (‹P.Normal›.conj_mem h hh j), hcomm ?_⟩
      have : h⁻¹ * (j * h * j⁻¹) = ⁅h⁻¹, j⁆ := by rw [commutatorElement_def]; group
      rw [this]
      exact commutator_mem_commutator (inv_mem (hPΛ' hh)) (hσPΛ hj))
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  exact hle

theorem exists_complement_of_sylow {X Λ V C : Subgroup Q} (hXΛ : X ≤ Λ)
    (hXn : Λ ≤ normalizer (X : Set Q)) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hX2 : IsPGroup 2 X) (hV : ∃ P : Sylow 2 Λ, (P : Subgroup Λ).map Λ.subtype = V)
    (hCV : C ≤ V) (hCX : C ⊓ X = ⊥) (hCsup : C ⊔ X = V) :
    ∃ Y : Subgroup Q, Y ≤ Λ ∧ Y ⊓ X = ⊥ ∧ Y ⊔ X = Λ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hV
  have hVΛ : V ≤ Λ := by rw [← hP]; exact map_subtype_le _
  have hCΛ : C ≤ Λ := hCV.trans hVΛ
  set X' : Subgroup Λ := X.subgroupOf Λ with hX'
  have hX'n : X'.Normal := (normal_subgroupOf_iff_le_normalizer hXΛ).2 hXn
  have hX'ab : IsMulCommutative X' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hXab _ (mem_subgroupOf.1 a.2) _
      (mem_subgroupOf.1 b.2)))⟩⟩
  have hX'2 : IsPGroup 2 X' := hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXΛ).symm
  have hPV : (P : Subgroup Λ) = V.subgroupOf Λ := by
    ext x
    rw [mem_subgroupOf, ← hP]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hKP : C.subgroupOf Λ ≤ P := by
    rw [hPV]
    exact fun x hx => mem_subgroupOf.2 (hCV (mem_subgroupOf.1 hx))
  have h1 : X' ⊓ C.subgroupOf Λ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
    have : (x : Q) ∈ C ⊓ X := mem_inf.2 ⟨mem_subgroupOf.1 hxC, mem_subgroupOf.1 hxX⟩
    rw [hCX, mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this
  have h2 : X' ⊔ C.subgroupOf Λ = P := by
    rw [hPV, ← hCsup, sup_comm, hX', Subgroup.subgroupOf_sup hCΛ hXΛ]
  obtain ⟨K, hK1, hK2⟩ := (CFSG.Quasithin.gaschutz hX'2 P).2 ⟨_, hKP, h1, h2⟩
  refine ⟨K.map Λ.subtype, map_subtype_le K, ?_, ?_⟩
  · rw [show X = X'.map Λ.subtype by
      rw [hX', Subgroup.subgroupOf_map_subtype, inf_of_le_left hXΛ]]
    rw [← map_inf_eq _ _ Λ.subtype Λ.subtype_injective, inf_comm, hK1, Subgroup.map_bot]
  · rw [show X = X'.map Λ.subtype by
      rw [hX', Subgroup.subgroupOf_map_subtype, inf_of_le_left hXΛ]]
    rw [← Subgroup.map_sup, sup_comm, hK2, Subgroup.map_top, range_subtype]

theorem exists_complement_of_elementary {X V E : Subgroup Q} (hEV : E ≤ V)
    (hE : IsElementaryAbelian 2 E) (hsup : X ⊔ E = V) :
    ∃ C : Subgroup Q, C ≤ V ∧ C ⊓ X = ⊥ ∧ C ⊔ X = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 E ((E ⊓ X).subgroupOf E)
  have hdis := disjoint_iff.1 hC.disjoint
  have hcod := codisjoint_iff.1 hC.codisjoint
  refine ⟨C.map E.subtype, (map_subtype_le C).trans hEV, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxX⟩ := mem_inf.1 hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hxC
    have hyEX : y ∈ (E ⊓ X).subgroupOf E := mem_subgroupOf.2 (mem_inf.2 ⟨y.2, hxX⟩)
    have : y ∈ (E ⊓ X).subgroupOf E ⊓ C := mem_inf.2 ⟨hyEX, hy⟩
    rw [hdis, mem_bot] at this
    rw [this]
    exact one_mem _
  · rw [← hsup]
    refine le_antisymm (sup_le ((map_subtype_le C).trans le_sup_right) le_sup_left)
      (sup_le le_sup_right ?_)
    have hEmap : ((E ⊓ X).subgroupOf E ⊔ C).map E.subtype = E := by
      rw [hcod, Subgroup.map_top, range_subtype]
    calc E = ((E ⊓ X).subgroupOf E ⊔ C).map E.subtype := hEmap.symm
      _ = ((E ⊓ X).subgroupOf E).map E.subtype ⊔ C.map E.subtype := Subgroup.map_sup _ _ _
      _ ≤ C.map E.subtype ⊔ X := by
          rw [sup_comm]
          refine sup_le_sup_left ?_ _
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_le_left.trans inf_le_right

theorem commutator_sup_le_sup_of_normal (A X : Subgroup Q) [X.Normal] :
    ⁅A ⊔ X, A ⊔ X⁆ ≤ ⁅A, A⁆ ⊔ X := by
  have hker : (QuotientGroup.mk' X).ker = X := QuotientGroup.ker_mk' X
  have hmapX : X.map (QuotientGroup.mk' X) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).2 hx
  have h : (⁅A ⊔ X, A ⊔ X⁆).map (QuotientGroup.mk' X) ≤ (⁅A, A⁆).map (QuotientGroup.mk' X) := by
    rw [map_commutator, map_commutator, Subgroup.map_sup, hmapX, sup_bot_eq]
  calc ⁅A ⊔ X, A ⊔ X⁆ ≤ ((⁅A, A⁆).map (QuotientGroup.mk' X)).comap (QuotientGroup.mk' X) :=
        map_le_iff_le_comap.1 h
    _ = ⁅A, A⁆ ⊔ X := by rw [comap_map_eq, hker]

@[expose] def derivedChain (H : Subgroup Q) : ℕ → Subgroup Q
  | 0 => H
  | k + 1 => ⁅derivedChain H k, derivedChain H k⁆

theorem derivedChain_zero (H : Subgroup Q) : derivedChain H 0 = H := rfl

theorem derivedChain_succ (H : Subgroup Q) (k : ℕ) :
    derivedChain H (k + 1) = ⁅derivedChain H k, derivedChain H k⁆ := rfl

theorem derivedChain_normal (H : Subgroup Q) [H.Normal] (k : ℕ) : (derivedChain H k).Normal := by
  induction k with
  | zero => exact ‹H.Normal›
  | succ k ih =>
    rw [derivedChain_succ]
    haveI := ih
    exact Subgroup.commutator_normal _ _

theorem derivedChain_succ_le (H : Subgroup Q) (k : ℕ) :
    derivedChain H (k + 1) ≤ derivedChain H k := by
  rw [derivedChain_succ, commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_perfect_normal_sup_eq {X H : Subgroup Q} [X.Normal] [H.Normal] (hXH : X ≤ H)
    (hH : H ≤ ⁅H, H⁆ ⊔ X) :
    ∃ P : Subgroup Q, P.Normal ∧ ⁅P, P⁆ = P ∧ P ≤ ⁅H, H⁆ ∧ P ⊔ X = H ∧
      ∀ R : Subgroup Q, R ≤ H → ⁅R, R⁆ = R → R ≤ P := by
  have hDH : ∀ k, derivedChain H k ≤ H := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (derivedChain_succ_le H k).trans ih
  have hcov : ∀ k, H ≤ derivedChain H k ⊔ X := by
    intro k
    induction k with
    | zero => exact le_sup_left
    | succ k ih =>
      calc H ≤ ⁅H, H⁆ ⊔ X := hH
        _ ≤ ⁅derivedChain H k ⊔ X, derivedChain H k ⊔ X⁆ ⊔ X :=
            sup_le_sup_right (commutator_mono ih ih) _
        _ ≤ (⁅derivedChain H k, derivedChain H k⁆ ⊔ X) ⊔ X :=
            sup_le_sup_right (commutator_sup_le_sup_of_normal _ _) _
        _ = derivedChain H (k + 1) ⊔ X := by rw [derivedChain_succ, sup_assoc, sup_idem]
  have hstab : ∃ k, derivedChain H (k + 1) = derivedChain H k := by
    refine Classical.byContradiction fun hne => ?_
    have hne' : ∀ k, derivedChain H (k + 1) ≠ derivedChain H k := fun k hk => hne ⟨k, hk⟩
    have hlt : ∀ k, Nat.card (derivedChain H (k + 1)) < Nat.card (derivedChain H k) :=
      fun k => card_lt_of_lt (lt_of_le_of_ne (derivedChain_succ_le H k) (hne' k))
    have hbound : ∀ k, Nat.card (derivedChain H k) + k ≤ Nat.card H := by
      intro k
      induction k with
      | zero => simp [derivedChain_zero]
      | succ k ih => have := hlt k; omega
    have h1 := hbound (Nat.card H)
    have h2 : 0 < Nat.card (derivedChain H (Nat.card H)) := Nat.card_pos
    omega
  obtain ⟨k, hk⟩ := hstab
  refine ⟨derivedChain H (k + 1), derivedChain_normal H _, ?_, ?_, ?_, ?_⟩
  · rw [hk, ← derivedChain_succ, hk]
  · have : ∀ m, derivedChain H (m + 1) ≤ derivedChain H 1 := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ih => exact (derivedChain_succ_le H (m + 1)).trans ih
    exact this k
  · exact le_antisymm (sup_le (hDH _) hXH) (hcov _)
  · intro R hRH hR
    have hRD : ∀ j, R ≤ derivedChain H j := by
      intro j
      induction j with
      | zero => exact hRH
      | succ j ih =>
        calc R = ⁅R, R⁆ := hR.symm
          _ ≤ ⁅derivedChain H j, derivedChain H j⁆ := commutator_mono ih ih
          _ = derivedChain H (j + 1) := rfl
    exact hRD (k + 1)

theorem exists_perfect_commuting_factor
    {K : Type*} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m)
    {σ : MulAut Q} {X Λ V F E : Subgroup Q} {r : Q} [X.Normal] [Λ.Normal]
    (hXsq : ∀ x ∈ X, x * x = 1) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hσX : X.map σ.toMonoidHom = X) (hcen : X ⊓ center Q = ⊥)
    (hXΛ : X ≤ Λ) (hΛσ : Λ ⊔ Λ.map σ.toMonoidHom = ⊤) (hcomm : ⁅Λ, Λ.map σ.toMonoidHom⁆ ≤ X)
    (θ₁ : Λ →* Matrix.SpecialLinearGroup (Fin 2) K) (hθ₁ : Function.Surjective θ₁)
    (hker : θ₁.ker = X.subgroupOf Λ)
    (hV : ∃ P : Sylow 2 Λ, (P : Subgroup Λ).map Λ.subtype = V) (hXV : X ≤ V)
    (hEV : E ≤ V) (hE : IsElementaryAbelian 2 E) (hEX : X ⊔ E = V)
    (hrΛ : r ∈ normalizer (Λ : Set Q)) (hgen : Λ ≤ V ⊔ V.map (MulAut.conj r).toMonoidHom)
    (hVn : V ≤ normalizer
      (((V.map σ.toMonoidHom).map (MulAut.conj r).toMonoidHom : Subgroup Q) : Set Q))
    (hFX : F ≤ X) (hFV : F ≤ centralizer (V : Set Q)) (hσF : F.map σ.toMonoidHom = F)
    (hFr : F ⊓ F.map (MulAut.conj r).toMonoidHom = ⊥)
    (hcX : Nat.card X = (2 ^ m) ^ 4) (hcF : (2 ^ m) ^ 2 ≤ Nat.card F) :
    ∃ P : Subgroup Q, P.Normal ∧ ⁅P, P⁆ = P ∧ P ≤ Λ ∧ P ⊔ X = Λ ∧
      ⁅P, P.map σ.toMonoidHom⁆ = ⊥ ∧ ∀ R : Subgroup Q, R ≤ Λ → ⁅R, R⁆ = R → R ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hV
  have hVΛ : V ≤ Λ := by rw [← hS₀]; exact map_subtype_le _
  have hV2 : IsPGroup 2 V := by
    rw [← hS₀]
    exact S₀.isPGroup'.map Λ.subtype
  have hX2 : IsPGroup 2 X := hV2.to_le hXV
  obtain ⟨C, hCV, hCX, hCsup⟩ := exists_complement_of_elementary hEV hE hEX
  obtain ⟨Y, hYΛ, hYX, hYsup⟩ := exists_complement_of_sylow hXΛ
    (fun g _ => mem_normalizer_of_normal X g) hXab hX2 ⟨S₀, hS₀⟩ hCV hCX hCsup
  set f : Y →* Matrix.SpecialLinearGroup (Fin 2) K := θ₁.comp (inclusion hYΛ) with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyker : inclusion hYΛ y ∈ θ₁.ker := hy
    rw [hker, mem_subgroupOf] at hyker
    have : (y : Q) ∈ Y ⊓ X := mem_inf.2 ⟨y.2, hyker⟩
    rw [hYX, mem_bot] at this
    exact Subtype.ext this
  have hfsurj : Function.Surjective f := by
    intro g
    obtain ⟨l, rfl⟩ := hθ₁ g
    have hl : (l : Q) ∈ ((Y ⊔ X : Subgroup Q) : Set Q) := by rw [hYsup]; exact l.2
    rw [coe_mul_of_left_le_normalizer_right Y X (fun g _ => mem_normalizer_of_normal X g)]
      at hl
    obtain ⟨y, hy, x, hx, hyx⟩ := Set.mem_mul.1 hl
    refine ⟨⟨y, hy⟩, ?_⟩
    have hx' : (⟨x, hXΛ hx⟩ : Λ) ∈ θ₁.ker := by rw [hker, mem_subgroupOf]; exact hx
    have hl' : l = inclusion hYΛ ⟨y, hy⟩ * ⟨x, hXΛ hx⟩ := Subtype.ext hyx.symm
    rw [hf, MonoidHom.comp_apply, hl', map_mul, MonoidHom.mem_ker.1 hx', mul_one]
  set eY : Y ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩ with heY
  set eσY : (Y.map σ.toMonoidHom) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (σ.subgroupMap Y).symm.trans eY with heσY
  have hσΛ : Λ.map σ.toMonoidHom = Y.map σ.toMonoidHom ⊔ X := by
    rw [← hYsup, Subgroup.map_sup, hσX]
  have hFS : ∀ B : Subgroup Q, B ≤ X → B.Normal →
      ¬ Λ.map σ.toMonoidHom ≤ centralizer (B : Set Q) → (2 ^ m) ^ 2 ≤ Nat.card B := by
    intro B hBX hBn hnc
    have hnc' : ¬ Y.map σ.toMonoidHom ≤ centralizer (B : Set Q) := by
      intro hle
      apply hnc
      rw [hσΛ]
      refine sup_le hle fun x hx => ?_
      rw [mem_centralizer_iff]
      intro b hb
      exact hXab _ (hBX hb) _ hx
    have := Common.sl2_card_sq_le_of_not_le_centralizer eσY hK hm
      (fun b hb => hXsq b (hBX hb)) (fun g _ => mem_normalizer_of_normal B g) hnc'
    rwa [hK] at this
  have hsplit := (exists_split (q := 2 ^ m) (Nat.le_self_pow (by omega) 2) hσX hcen hΛσ hV2
    hVΛ hXV hrΛ hgen hVn hFX hFV hσF hFr hFS hcX hcF).1
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
  have hYperf : ⁅Y, Y⁆ = Y := by
    have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y) := by
      have h1 : (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆).map
          eY.symm.toMonoidHom = ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ := by
        rw [map_commutator, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.2 eY.symm.surjective]
      rw [← h1, ← commutator_def, Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 eY.symm.surjective]
    have h2 := congrArg (Subgroup.map Y.subtype) htop
    rwa [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hΛperf : Λ ≤ ⁅Λ, Λ⁆ ⊔ X :=
    calc Λ = Y ⊔ X := hYsup.symm
      _ ≤ ⁅Λ, Λ⁆ ⊔ X :=
          sup_le_sup_right ((le_of_eq hYperf.symm).trans (commutator_mono hYΛ hYΛ)) _
  obtain ⟨P, hPn, hP, hPΛΛ, hPX, hPmax⟩ := exists_perfect_normal_sup_eq hXΛ hΛperf
  haveI := hPn
  have hPΛ : P ≤ Λ := hPΛΛ.trans (commutator_le_left _ _)
  exact ⟨P, hPn, hP, hPΛ, hPX,
    commutator_eq_bot_of_split hXab hσX hcomm hsplit hYX hYsup hPΛΛ hP, hPmax⟩

end CFSG.LocalAnalysis.EvenBN.Common
