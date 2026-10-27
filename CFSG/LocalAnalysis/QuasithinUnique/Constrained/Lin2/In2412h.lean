module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412g
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414a

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Abstract

variable {G : Type*} [Group G]

theorem transitive_of_card_fixed [Finite G] {N : Subgroup G} {f : G} (hff : f * f = 1)
    (hfN : ∀ n ∈ N, f * n * f⁻¹ ∈ N) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNsq : ∀ a ∈ N, a * a = 1)
    (hcard : Nat.card (N ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
      Nat.card (N ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = Nat.card N) :
    ∀ x ∈ N, (f * x) * (f * x) = 1 → ∃ m ∈ N, m⁻¹ * f * m = f * x := by
  intro x hx hx2
  have hti : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have h1 : (f * x * f⁻¹) * x = 1 := by
    calc (f * x * f⁻¹) * x = (f * x) * (f * x) := by rw [hti]; group
      _ = 1 := hx2
  obtain ⟨m, hm, hmx⟩ := H3_of_card hff hfN hNab hNsq hcard x hx h1
  refine ⟨m⁻¹, N.inv_mem hm, ?_⟩
  calc m⁻¹⁻¹ * f * m⁻¹ = f * ((f⁻¹ * m * f) * m⁻¹) := by group
    _ = f * ((f * m * f⁻¹) * m⁻¹) := by rw [hti]
    _ = f * x := by rw [← hmx]

theorem mem_normalizer_centerOf_of_mem {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((centerOf L : Subgroup G) : Set G) := by
  rw [← conjR_eq_self_iff, conjR_centerOf, conjR_eq_of_mem_normalizer hg]

end Abstract

section Torus

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.exists_noncentral (h : Lin2Cfg G T M H S L n D) {K : Type} [Field K] [Fintype K]
    (A : Adapted L (S ⊓ L) n K) {f : G} (hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L) {σ : K ≃+* K}
    (hσ : σ ≠ 1)
    (hdiag : ∀ ℓ : L, (A.α ℓ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
      (A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 =
        σ ((A.α ℓ : Matrix (Fin 2) (Fin 2) K) 0 0)) :
    ∃ d ∈ D, f * d * f⁻¹ ≠ d := by
  by_contra hcon
  have hall : ∀ d ∈ D, f * d * f⁻¹ = d := fun d hd => by
    by_contra hne
    exact hcon ⟨d, hd, hne⟩
  apply hσ
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · subst hx
    simp
  · obtain ⟨d, hd, hdL, hdx⟩ := h.exists_chi_eq A hx
    have h1 := hdiag ⟨d, hdL⟩ (h.upper_of_mem_D A hd)
    have e : A.chi ⟨f * d * f⁻¹, hfL d hdL⟩ = A.chi ⟨d, hdL⟩ :=
      congrArg (fun ℓ : L => A.chi ℓ)
        (Subtype.ext (hall d hd) : (⟨f * d * f⁻¹, hfL d hdL⟩ : L) = ⟨d, hdL⟩)
    have h3 : A.chi ⟨d, hdL⟩ = σ (A.chi ⟨d, hdL⟩) :=
      calc A.chi ⟨d, hdL⟩ = A.chi ⟨f * d * f⁻¹, hfL d hdL⟩ := e.symm
        _ = σ (A.chi ⟨d, hdL⟩) := h1
    rw [hdx] at h3
    exact h3.symm

theorem Lin2Cfg.card_center_fixed (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L ≠ ⊥) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hff : f * f = 1)
    (hnc : ∃ d ∈ D, f * d * f⁻¹ ≠ d) :
    Nat.card (centerOf L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ^ 2 =
      Nat.card (centerOf L) := by
  have hf1 : f ≠ 1 := by
    rintro rfl
    obtain ⟨d, -, hd⟩ := hnc
    exact hd (by simp)
  have hB0 := hB
  obtain ⟨hDB, -, hBab, -, -, -, -, -, hRT, -, hBx⟩ := hB
  obtain ⟨⟨-, hTnS, -⟩, -, -, h4, -, -, -, ⟨-, hDcard⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x, hxTB, hxS⟩ : ∃ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S := by
    by_contra hcon
    obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
    apply hx₀S
    have hle : T ⊓ Subgroup.normalizer (B : Set G) ≤ S := fun y hy => by
      by_contra hyS
      exact hcon ⟨y, hy, hyS⟩
    exact sup_le (thompsonJ_le_self S) hle (hRT.ge hx₀T)
  have hxT : x ∈ T := hxTB.1
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := hxTB.2
  obtain ⟨hDxL, hreg⟩ := h4 x hxT hxS
  obtain ⟨hZel, hZcard, hDreg⟩ := hreg.resolve_left hc
  have hBeq : B = D ⊔ conjR D x := hBx x hxTB hxS
  have hD'B : conjR D x ≤ B := by rw [hBeq]; exact le_sup_right
  have hZcent : ∀ d ∈ D, ∀ z ∈ centerOf L, d * z = z * d := fun d hd z hz =>
    Subgroup.mem_centralizer_iff.1 hz.2 d (hcfg.D_le_L hd)
  have hfNL : f ∈ Subgroup.normalizer (L : Set G) := hcfg.S_le_normalizer hf.1
  have hfZ : ∀ z ∈ centerOf L, f * z * f⁻¹ ∈ centerOf L := fun z hz =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centerOf_of_mem hfNL) z).1 hz
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hfree : ∀ b ∈ conjR D x, (∀ z ∈ centerOf L, b * z = z * b) → b = 1 := by
    intro b hb hbz
    refine hDreg.2.2 z₀ ⟨hz₀, hz₀1'⟩ b hb ?_
    have h1 := hbz z₀ hz₀
    calc b⁻¹ * z₀ * b = b⁻¹ * (z₀ * b) := by group
      _ = b⁻¹ * (b * z₀) := by rw [h1]
      _ = z₀ := by group
  have hFcyc : IsCyclic ↥(S ⊓ Subgroup.normalizer (B : Set G)) :=
    (lemma2_4_12_one h8 G T M H S L D n hcfg B hB0).1
  have hxf : x * f * x⁻¹ = f := by
    have hxfS : x * f * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hTnS hxT) f).1 hf.1
    have hxfB : x * f * x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxB hf.2) (Subgroup.inv_mem _ hxB)
    have hsq : (x * f * x⁻¹) ^ 2 = 1 := by
      rw [sq]
      calc (x * f * x⁻¹) * (x * f * x⁻¹) = x * (f * f) * x⁻¹ := by group
        _ = 1 := by rw [hff]; group
    have hne : x * f * x⁻¹ ≠ 1 := fun h => hf1 (by
      calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    have hf2 : f ^ 2 = 1 := by rw [sq]; exact hff
    have := hFcyc
    have := eq_of_sq_eq_one_of_isCyclic
      (x := (⟨x * f * x⁻¹, hxfS, hxfB⟩ : ↥(S ⊓ Subgroup.normalizer (B : Set G))))
      (y := (⟨f, hf⟩ : ↥(S ⊓ Subgroup.normalizer (B : Set G))))
      (Subtype.ext hsq) (Subtype.ext hf2) (fun h => hne (congrArg Subtype.val h))
      (fun h => hf1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hxf' : f * x = x * f := by
    calc f * x = (x * f * x⁻¹) * x := by rw [hxf]
      _ = x * f := by group
  have hBD : ∀ b ∈ B, ∃ d ∈ D, ∃ d' ∈ conjR D x, d * d' = b := by
    intro b hb
    have hD'norm : conjR D x ≤ Subgroup.normalizer (D : Set G) := by
      intro y hy
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hBab d (hDB hd) y (hD'B hy)
    rw [hBeq] at hb
    obtain ⟨d, hd, d', hd', hdd⟩ := (mem_sup_iff_of_le_normalizer hD'norm).1 hb
    exact ⟨d, hd, d', hd', hdd.symm⟩
  have hfD : ∀ d ∈ D, f * d * f⁻¹ ∈ D := by
    intro d hd
    have hdB : f * d * f⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hf.2 d).1 (hDB hd)
    obtain ⟨d₁, hd₁, d₁', hd₁', hdd⟩ := hBD _ hdB
    have hcz : ∀ z ∈ centerOf L, (f * d * f⁻¹) * z = z * (f * d * f⁻¹) := by
      intro z hz
      have hz' : f⁻¹ * z * f ∈ centerOf L := by
        have := (Subgroup.mem_normalizer_iff.1
          (Subgroup.inv_mem _ (mem_normalizer_centerOf_of_mem hfNL)) z).1 hz
        simpa using this
      have e := hZcent d hd _ hz'
      calc (f * d * f⁻¹) * z = f * (d * (f⁻¹ * z * f)) * f⁻¹ := by group
        _ = f * ((f⁻¹ * z * f) * d) * f⁻¹ := by rw [e]
        _ = z * (f * d * f⁻¹) := by group
    have hd₁'c : ∀ z ∈ centerOf L, d₁' * z = z * d₁' := by
      intro z hz
      have e := hcz z hz
      rw [← hdd] at e
      have e2 : d₁ * z = z * d₁ := hZcent d₁ hd₁ z hz
      calc d₁' * z = d₁⁻¹ * (d₁ * d₁' * z) := by group
        _ = d₁⁻¹ * (z * (d₁ * d₁')) := by rw [e]
        _ = d₁⁻¹ * (z * d₁) * d₁' := by group
        _ = d₁⁻¹ * (d₁ * z) * d₁' := by rw [e2]
        _ = z * d₁' := by group
    have hd₁'1 : d₁' = 1 := hfree d₁' hd₁' hd₁'c
    rw [← hdd, hd₁'1, mul_one]
    exact hd₁
  have hfD' : ∀ y ∈ conjR D x, f * y * f⁻¹ ∈ conjR D x := by
    intro y hy
    rw [mem_conjR] at hy ⊢
    have e : x * (f * y * f⁻¹) * x⁻¹ = f * (x * y * x⁻¹) * f⁻¹ := by
      calc x * (f * y * f⁻¹) * x⁻¹ = (x * f) * y * (x * f)⁻¹ := by group
        _ = (f * x) * y * (f * x)⁻¹ := by rw [hxf'.symm]
        _ = f * (x * y * x⁻¹) * f⁻¹ := by group
    rw [e]
    exact hfD _ hy
  have hsing := singer_involution (Z := centerOf L) (D := conjR D x) (e := n) hcfg.one_pos hZel
    hZcard (fun y hy => mem_normalizer_centerOf_of_mem (hDxL hy))
    (fun a ha b hb => hBab a (hD'B ha) b (hD'B hb)) hDreg (by rw [card_conjR]; exact hDcard) hff
    hfZ (fun d hd => ⟨f * d * f⁻¹, hfD' d hd, fun z _ => rfl⟩)
  rcases hsing with hcent | hcard
  · exfalso
    have hfz : ∀ w ∈ centerOf L, f * w * f⁻¹ = w := fun w hw => by
      calc f * w * f⁻¹ = (w * f) * f⁻¹ := by rw [hcent w hw]
        _ = w := by group
    have hcD' : ∀ δ ∈ conjR D x, f * δ * f⁻¹ = δ := by
      intro δ hδ
      have hbD' : δ⁻¹ * (f * δ * f⁻¹) ∈ conjR D x :=
        (conjR D x).mul_mem ((conjR D x).inv_mem hδ) (hfD' δ hδ)
      have h1 : δ⁻¹ * (f * δ * f⁻¹) = 1 := by
        refine hfree _ hbD' (fun z hz => ?_)
        have hz1 : f⁻¹ * z * f = z := by
          calc f⁻¹ * z * f = f⁻¹ * (z * f) := by group
            _ = f⁻¹ * (f * z) := by rw [hcent z hz]
            _ = z := by group
        have hδz : δ * z * δ⁻¹ ∈ centerOf L :=
          (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centerOf_of_mem (hDxL hδ)) z).1 hz
        have h : (f * δ * f⁻¹) * z * (f * δ * f⁻¹)⁻¹ = δ * z * δ⁻¹ := by
          calc (f * δ * f⁻¹) * z * (f * δ * f⁻¹)⁻¹ = f * (δ * (f⁻¹ * z * f) * δ⁻¹) * f⁻¹ := by
                group
            _ = f * (δ * z * δ⁻¹) * f⁻¹ := by rw [hz1]
            _ = δ * z * δ⁻¹ := hfz _ hδz
        calc δ⁻¹ * (f * δ * f⁻¹) * z
            = δ⁻¹ * ((f * δ * f⁻¹) * z * (f * δ * f⁻¹)⁻¹) * (f * δ * f⁻¹) := by group
          _ = δ⁻¹ * (δ * z * δ⁻¹) * (f * δ * f⁻¹) := by rw [h]
          _ = z * (δ⁻¹ * (f * δ * f⁻¹)) := by group
      calc f * δ * f⁻¹ = δ * (δ⁻¹ * (f * δ * f⁻¹)) := by group
        _ = δ := by rw [h1, mul_one]
    obtain ⟨d, hd, hnd⟩ := hnc
    apply hnd
    have hδd : x * (x⁻¹ * d * x) * x⁻¹ = d := by group
    have hδ : x⁻¹ * d * x ∈ conjR D x := by
      rw [mem_conjR, hδd]
      exact hd
    have h1 := hcD' _ hδ
    calc f * d * f⁻¹ = f * (x * (x⁻¹ * d * x) * x⁻¹) * f⁻¹ := by rw [hδd]
      _ = (f * x) * (x⁻¹ * d * x) * (f * x)⁻¹ := by group
      _ = (x * f) * (x⁻¹ * d * x) * (x * f)⁻¹ := by rw [hxf']
      _ = x * (f * (x⁻¹ * d * x) * f⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * d * x) * x⁻¹ := by rw [h1]
      _ = d := hδd
  · exact hcard

end Torus

section Counts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem counts_Zne1 (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L ≠ ⊥)
    {f : G} (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hf2 : f ^ 2 = 1) :
    (∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 → ∃ s ∈ thompsonJ S, s⁻¹ * f * s = f * r) ∧
      Nat.card (lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
        2 ^ (n / 2) ∧
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
        2 ^ (2 * n) ∧
      (∀ x ∈ blockU L, (f * x) * (f * x) = 1 → ∃ m ∈ blockU L, m⁻¹ * f * m = f * x) ∧
      ∀ x ∈ centerOf L, (f * x) * (f * x) = 1 → ∃ m ∈ centerOf L, m⁻¹ * f * m = f * x := by
  have hff : f * f = 1 := by rw [← sq]; exact hf2
  obtain ⟨hQL, -, -, hF3, hF4⟩ := complement_facts h8 hcfg hB
  obtain ⟨⟨-, -, -⟩, ⟨hOL, hUQ⟩, ⟨-, hRsyl, h3⟩, h4, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRUU, -, -, -⟩ := h3 x₀ hx₀T hx₀S
  have hUel : IsElemAbelian 2 (blockU L) := (h7 x₀ hx₀T hx₀S).1
  obtain ⟨hZel, hZcard, -⟩ := ((h4 x₀ hx₀T hx₀S).2).resolve_left hc
  have hSL : S ⊓ L = thompsonJ S :=
    hRsyl.eq_of_le (le_inf (thompsonJ_le_self S) hRsyl.1) inf_le_right
      hcfg.S_isPGroup.to_inf_left
  obtain ⟨K, _, _, ⟨A⟩⟩ := hcfg.coord
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card hcfg.one_pos A.card_eq
  have hfS : f ∈ S := hf.1
  have hfNL : f ∈ Subgroup.normalizer (L : Set G) := hcfg.S_le_normalizer hfS
  have hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hfNL x).1 hx
  have hHU : H ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [hUQ]; exact hcfg.H_le_normalizer_Q
  have hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hHU (hcfg.S_le_H hfS)) x).1 hx
  have hfR : ∀ x ∈ S ⊓ L, f * x * f⁻¹ ∈ S ⊓ L := fun x hx =>
    ⟨S.mul_mem (S.mul_mem hfS hx.1) (S.inv_mem hfS), hfL x hx.2⟩
  obtain ⟨σ, a, c', -, hσσ, hc3, hc2, hc1, hT, hU, hN, hdiag, -, hσ1⟩ :=
    hcfg.link A hOL hff hfL hfU hfR
  have hFp : IsPGroup 2 ((S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G)) :=
    hcfg.S_isPGroup.to_le inf_le_left
  have hσ : σ ≠ 1 := by
    intro hσ
    obtain ⟨k, hk⟩ := hσ1 hσ
    exact hf1 (hcfg.eq_one_of_inner hQL hFp (by rw [inf_comm]; exact hF3) hF4 A hf hfL k hk)
  obtain ⟨⟨θ, hθ⟩, m, hnm, hfixcard⟩ := exists_half_of_twisted hK2 A.card_eq σ hσσ hσ
  have hnc := hcfg.exists_noncentral A hfL hσ hdiag
  have hsq := hcfg.card_center_fixed h8 hB hc hf hff hnc
  have hZC : Nat.card (centerOf L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 2 ^ m := by
    have h1 : (Nat.card (centerOf L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) ^ 2 =
        (2 ^ m) ^ 2 := by
      rw [hsq, hZcard, hnm, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_left_injective (by norm_num) h1
  have hfZ : ∀ z ∈ centerOf L, f * z * f⁻¹ ∈ centerOf L := fun z hz =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centerOf_of_mem hfNL) z).1 hz
  have hZab : ∀ a ∈ centerOf L, ∀ b ∈ centerOf L, a * b = b * a := fun a ha b hb =>
    IsElemAbelian.comm hZel ha hb
  have hZsq : ∀ a ∈ centerOf L, a * a = 1 := fun a ha => by rw [← sq]; exact hZel.2 a ha
  have hTrZ := transitive_of_card_fixed hff hfZ hZab hZsq (by rw [← sq]; exact hsq)
  have hUR : blockU L ≤ S ⊓ L := by rw [hSL, hRUU]; exact le_sup_left
  have hUcond : ∀ ℓ : L, (ℓ : G) ∈ blockU L ↔ A.α ℓ = 1 := fun ℓ => by
    rw [← hOL]; exact A.mem_pCoreOf_iff ℓ
  have hZeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hβk : ∀ u : blockU L, A.β u = 1 ↔ (u : G) ∈ centerOf L := fun u => by
    rw [← hZeq, ← MonoidHom.mem_ker, A.β_ker, Subgroup.mem_subgroupOf]
  obtain ⟨γ₃, hγ₃s, hγ₃k, hγ₃v⟩ := exists_gamma_top A hUcond
  obtain ⟨N', hN'U, γ₂, γ₁, hγ₂s, hγ₂k, hγ₂v, hγ₁s, hγ₁k, hγ₁v, hmemN⟩ :=
    exists_gamma_mid A.β A.β_surj hβk
  have hZN' : centerOf L ≤ N' := by
    intro z hz
    have hzU : z ∈ blockU L := by
      rw [← hZeq] at hz
      exact blockZ_le_blockU L hz
    refine (hmemN z).2 ⟨hzU, ?_⟩
    have h1 : A.β ⟨z, hzU⟩ = 1 := (hβk ⟨z, hzU⟩).2 hz
    rw [h1]
    simp
  have hfN' : ∀ x ∈ N', f * x * f⁻¹ ∈ N' := by
    intro x hx
    obtain ⟨hxU, hx1⟩ := (hmemN x).1 hx
    refine (hmemN _).2 ⟨hfU x hxU, ?_⟩
    have h1 := hU ⟨x, hxU⟩
    rw [hx1, map_zero, mul_zero] at h1
    exact h1
  obtain ⟨hTr1, hcard1⟩ := layer_step σ (c' * a) hK2 hσσ θ hθ hc1 hZN' hff hfN' hfZ γ₁ hγ₁s hγ₁k
    (fun y => by
      rw [hγ₁v, hγ₁v]
      obtain ⟨hyU, hy1⟩ := (hmemN y).1 y.2
      exact hN ⟨y, hyU⟩ hy1)
    hZab hZsq hTrZ
  obtain ⟨hTr2, hcard2⟩ := layer_step σ (c' * a⁻¹) hK2 hσσ θ hθ hc2 hN'U hff hfU hfN' γ₂ hγ₂s
    hγ₂k (fun u => by rw [hγ₂v, hγ₂v]; exact hU u)
    (fun x hx y hy => IsElemAbelian.comm hUel (hN'U hx) (hN'U hy))
    (fun x hx => by rw [← sq]; exact hUel.2 x (hN'U hx)) hTr1
  obtain ⟨hTr3, hcard3⟩ := layer_step σ (a * a) hK2 hσσ θ hθ hc3 hUR hff hfR hfU γ₃ hγ₃s hγ₃k
    (fun r => by rw [hγ₃v, hγ₃v]; exact hT ⟨r, A.P_le r.2⟩ r.2)
    (fun x hx y hy => IsElemAbelian.comm hUel hx hy)
    (fun x hx => by rw [← sq]; exact hUel.2 x hx) hTr2
  have hlin : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
  have hN1 : Nat.card (N' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 2 ^ (m + m) := by
    rw [hcard1, hZC, hfixcard _ hc1, pow_add]
  have hU1 : Nat.card (blockU L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      2 ^ (m + m + m) := by
    rw [hcard2, hN1, hfixcard _ hc2, ← pow_add]
  have hR1 : Nat.card (S ⊓ L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      2 ^ (m + m + m + m) := by
    rw [hcard3, hU1, hfixcard _ hc3, ← pow_add]
  have e1 : n / 2 = m := by omega
  have e2 : 2 * n = m + m + m + m := by omega
  refine ⟨fun r hr hr2 => ?_, ?_, ?_, hTr2, hTrZ⟩
  · have hr' : r ∈ S ⊓ L := by rw [hSL]; exact hr
    obtain ⟨s, hs, e⟩ := hTr3 r hr' (by rw [← sq]; exact hr2)
    exact ⟨s, by rw [← hSL]; exact hs, e⟩
  · rw [hlin, e1]; exact hZC
  · rw [← hSL, hR1, e2]

end Counts

theorem lemma2_4_12_Zne1 (h8 : Lemma2_4_8) : Lemma2_4_12_Zne1 := by
  intro G _ _ T M H S L D n hcfg B hB f hf hf1 hf2 hc
  obtain ⟨h1, h2, h3, -, -⟩ := counts_Zne1 h8 hcfg hB hc hf hf1 hf2
  exact ⟨h1, h2, h3⟩

end CFSG.QuasithinUnique.Lin2
