module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.SecModel

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module Equiv Equiv.Perm CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem a7_section [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hLB : ⁅L, B⁆ = L) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    {Z₀ Z₁ : Submodule (ZMod 2) W} (hmin : IsMinSec ρ (L ⊔ B) Z₀ Z₁)
    (hnt : ¬ SecTrivial ρ L Z₀ Z₁)
    (hbud : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card B) :
    ∃ r : ℕ, 2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B ∧
      r < 2 * secCod ρ B Z₀ Z₁ ∧ 4 ≤ finrank (ZMod 2) (SecQ Z₀ Z₁) ∧
      finrank (ZMod 2) (SecQ Z₀ Z₁) ≤ 6 ∧
      (∀ z ∈ Z₁, (∀ l ∈ L, ρ l z - z ∈ Z₀) → z ∈ Z₀) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  set H := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  obtain ⟨h₀, h₁, hlt, hbet⟩ := hmin
  have hle : Z₀ ≤ Z₁ := hlt.le
  set Q := SecQ Z₀ Z₁ with hQ
  set σ := secRep ρ H h₀ h₁ with hσ
  obtain ⟨hQnt, hirrQ⟩ := secRep_irreducible ⟨h₀, h₁, hlt, hbet⟩
  have : Finite Q := Module.finite_of_finite (ZMod 2)
  set τ : Representation (ZMod 2) ↥L Q := σ.comp (Subgroup.inclusion hLH) with hτ
  have hτnt : ∃ k : ↥L, τ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnt
    rw [secTrivial_iff h₀ h₁ hLH]
    intro k hk q
    have h1 := hcon ⟨k, Subgroup.mem_subgroupOf.mp hk⟩
    have h2 : Subgroup.inclusion hLH ⟨(k : G), Subgroup.mem_subgroupOf.mp hk⟩ = k :=
      Subtype.ext rfl
    have h3 := congrArg (fun u : Module.End (ZMod 2) Q => u q) h1
    simp only [hτ, MonoidHom.comp_apply, h2, Module.End.one_apply] at h3
    exact h3
  have h4 : 4 ≤ finrank (ZMod 2) Q := four_le_finrank_of_alt7 eL τ hτnt
  set Ls : Subgroup ↥H := L.subgroupOf H with hLs
  have hLsN : Ls.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  let φ : ↥Ls ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLH).trans eL
  obtain ⟨e, he1, hconj, hker1, hker2⟩ := exists_conj_embedding7 Ls φ
  have hLA : ∀ l ∈ Ls, e l ∈ alternatingGroup (Fin 7) := by
    intro l hl
    have := he1 ⟨l, hl⟩
    rw [this]
    exact (φ ⟨l, hl⟩).2
  have hsimpL : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact eL.isSimpleGroup
  have hcenLs : ∀ y : ↥Ls, (∀ x : ↥Ls, y * x = x * y) → y = 1 := by
    intro y hy
    have hc : φ y ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨x, rfl⟩ := φ.surjective z
      rw [← map_mul, ← map_mul, hy x]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num),
      Subgroup.mem_bot] at hc
    exact φ.injective (by rw [hc, map_one])
  set Pc : Subgroup ↥H := Subgroup.centralizer (Ls : Set ↥H) with hPc
  have hPcN : Pc.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hPc, Subgroup.mem_centralizer_iff] at hn ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Ls := by
      have := hLsN.conj_mem x hx g⁻¹
      simpa [mul_assoc] using this
    have := hn _ hx'
    calc x * (g * n * g⁻¹) = g * ((g⁻¹ * x * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * x := by group
  have hPc2 : ∀ h ∈ Pc, h * h = 1 := by
    intro h hh
    have hh' := Subgroup.mem_centralizer_iff.1 hh
    have hmem : (h : G) ∈ ((L ⊔ B : Subgroup G) : Set G) := h.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hBN] at hmem
    obtain ⟨l, hl, b, hb, hlb⟩ := hmem
    have hbl : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hBN hb) l).mp hl
    have hb2 : b * b = 1 := by simpa [pow_two] using hB2 b hb
    have hsq : ((h * h : ↥H) : G) ∈ L := by
      show (h : G) * (h : G) ∈ L
      rw [← hlb]
      have e1 : l * b * (l * b) = l * (b * l * b⁻¹) * (b * b) := by group
      rw [e1, hb2, mul_one]
      exact L.mul_mem hl hbl
    have hsqLs : h * h ∈ Ls := Subgroup.mem_subgroupOf.2 hsq
    have hcomm : ∀ x : ↥Ls, (⟨h * h, hsqLs⟩ : ↥Ls) * x = x * ⟨h * h, hsqLs⟩ := by
      intro x
      apply Subtype.ext
      show h * h * (x : ↥H) = (x : ↥H) * (h * h)
      have hx := hh' (x : ↥H) x.2
      calc h * h * (x : ↥H) = h * (h * x) := by rw [mul_assoc]
        _ = h * (x * h) := by rw [hx]
        _ = (h * x) * h := by rw [mul_assoc]
        _ = (x * h) * h := by rw [hx]
        _ = x * (h * h) := by rw [mul_assoc]
    have := hcenLs _ hcomm
    exact congrArg Subtype.val this
  have hPc2' : IsPGroup 2 Pc := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hPc2 g.1 g.2⟩
  have hPcTriv : ∀ p ∈ Pc, σ p = 1 :=
    rep_trivial_of_normal_two σ (fun N hN => hirrQ N hN) hPcN hPc2'
  have hker : ∀ h : ↥H, e h = 1 → ∀ q, σ h q = q := by
    intro h hh q
    have hhPc : h ∈ Pc := by
      rw [hPc, Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 : h * x * h⁻¹ = x := hker1 h hh ⟨x, hx⟩
      calc x * h = (h * x * h⁻¹) * h := by rw [h2]
        _ = h * x := by group
    have := hPcTriv h hhPc
    rw [this]
    rfl
  have hfixLs : fixSub σ Ls = ⊥ := by
    rcases hirrQ _ (invariant_fixSub σ hLsN) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hτnt
      apply hk
      refine LinearMap.ext fun q => ?_
      have hq : q ∈ fixSub σ Ls := by rw [h]; exact Submodule.mem_top
      have := mem_fixSub.1 hq (Subgroup.inclusion hLH k) (Subgroup.mem_subgroupOf.2 k.2)
      simpa [hτ] using this
  have hfixL : ∀ v : Q, (∀ l ∈ Ls, σ l v = v) → v = 0 := by
    intro v hv
    have : v ∈ fixSub σ Ls := mem_fixSub.2 hv
    rw [hfixLs, Submodule.mem_bot] at this
    exact this
  set B' : Subgroup ↥H := B.subgroupOf H with hB'
  have hBc' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hB2' : ∀ b ∈ B', b * b = 1 := by
    intro b hb
    apply Subtype.ext
    simpa [pow_two] using hB2 _ (Subgroup.mem_subgroupOf.1 hb)
  have hconjEq : ∀ b : ↥H, (e b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G)) := by
    intro b
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      let xl : ↥Ls := ⟨⟨l, hLH hl⟩, Subgroup.mem_subgroupOf.2 hl⟩
      have h2 : b * (xl : ↥H) * b⁻¹ = (xl : ↥H) := hker1 b h1 xl
      have h3 : (b : G) * l * (b : G)⁻¹ = l := congrArg (fun y : ↥H => (y : G)) h2
      calc l * (b : G) = (b : G) * l * (b : G)⁻¹ * (b : G) := by rw [h3]
        _ = (b : G) * l := by group
    · intro h1
      apply hker2
      intro x
      have h2 := Subgroup.mem_centralizer_iff.1 h1 (x : G) x.2
      apply Subtype.ext
      show (b : G) * (x : G) * (b : G)⁻¹ = (x : G)
      calc (b : G) * (x : G) * (b : G)⁻¹ = (x : G) * (b : G) * (b : G)⁻¹ := by rw [← h2]
        _ = (x : G) := by group
  set eB : Subgroup (Perm (Fin 7)) := B'.map e with heB
  have heB1 : eB ≠ ⊥ := by
    intro hbot
    have hcB : ∀ b ∈ B, ∀ l ∈ L, l * b = b * l := by
      intro b hb l hl
      have : e ⟨b, hBH hb⟩ = 1 := by
        have hm : e ⟨b, hBH hb⟩ ∈ eB := Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 hb, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hm
        exact hm
      exact Subgroup.mem_centralizer_iff.1 ((hconjEq _).1 this) l hl
    have : ⁅L, B⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcB b hb l hl
    rw [hLB] at this
    have hne : Nontrivial ↥L := eL.toEquiv.nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    apply hx
    exact Subtype.ext (by simpa using (Subgroup.eq_bot_iff_forall L).1 this x x.2)
  have heBc : ∀ a ∈ eB, ∀ b ∈ eB, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc' a ha b hb]
  have heB2 : ∀ a ∈ eB, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hB2' a ha, map_one]
  obtain ⟨k, f, hfA, hbound, hcl⟩ := CFSG.QuasithinUnique.B42A57.gen7 heB1 heBc heB2
  let g : Fin k → ↥H := fun i =>
    ⟨((eL.symm ⟨f i, hfA i⟩ : ↥L) : G), hLH (eL.symm ⟨f i, hfA i⟩).2⟩
  have hg : ∀ i, e (g i) = f i := by
    intro i
    have h1 := he1 ⟨g i, Subgroup.mem_subgroupOf.2 (eL.symm ⟨f i, hfA i⟩).2⟩
    simp only at h1
    rw [h1]
    show ((eL ⟨(g i : G), _⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = f i
    have : (⟨(g i : G), (eL.symm ⟨f i, hfA i⟩).2⟩ : ↥L) = eL.symm ⟨f i, hfA i⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hgen := finrank_le_of_generation σ e Ls B' hker hfixL hLA g f hg hcl
  have hker_card : Nat.card eB * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card B := by
    set eb : ↥B' →* Perm (Fin 7) := e.comp B'.subtype with heb
    have h1 := Subgroup.card_ker_mul_card_range eb
    have hrange : eb.range = eB := by
      rw [heb, MonoidHom.range_comp, Subgroup.range_subtype]
    have hkercard : Nat.card eb.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_congr
        { toFun := fun b => ⟨((b.1 : ↥H) : G), Subgroup.mem_subgroupOf.1 b.1.2,
            (hconjEq _).1 b.2⟩
          invFun := fun c => ⟨⟨⟨c.1, hBH c.2.1⟩, Subgroup.mem_subgroupOf.2 c.2.1⟩,
            (hconjEq _).2 c.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hBcard : Nat.card ↥B' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    rw [← hrange, ← hkercard, mul_comm, ← hBcard]
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heBp : IsPGroup 2 eB := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    exact heB2 a a.2)⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp heBp
  have hrcard : 2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B := by
    rw [← hr]
    exact hker_card
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hs_le : secCod ρ B Z₀ Z₁ ≤ r := by
    have h1 : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hrcard]
      exact hbud
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hsc : secCod ρ B Z₀ Z₁ = finrank (ZMod 2) Q - finrank (ZMod 2) ↥(fixSub σ B') :=
    secCod_eq h₀ h₁ hle hBH
  have hrk : r * k ≤ 6 := by
    have h1 : (2 ^ r) ^ k ≤ 2 ^ 6 := by rw [← hr]; exact hbound
    rw [← pow_mul] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hgen' : finrank (ZMod 2) Q ≤ k * secCod ρ B Z₀ Z₁ := by rw [hsc]; exact hgen
  refine ⟨r, hrcard, ?_, h4, ?_, ?_⟩
  · by_contra hlt2
    push Not at hlt2
    have h1 : 2 * (k * secCod ρ B Z₀ Z₁) ≤ r * k := by nlinarith
    omega
  · have h1 : k * secCod ρ B Z₀ Z₁ ≤ k * r := Nat.mul_le_mul_left k hs_le
    nlinarith
  · intro z hz hzL
    have hq : (Submodule.Quotient.mk ⟨z, hz⟩ : Q) ∈ fixSub σ Ls := by
      rw [mem_fixSub]
      intro l hl
      have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
      show secRep ρ H h₀ h₁ l (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk ⟨z, hz⟩
      rw [secRep_mk, Submodule.Quotient.eq]
      exact hzL _ hl'
    rw [hfixLs, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hq
    exact hq

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
