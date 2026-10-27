module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs71
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1312b
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentInitial.BinaryNonsingularStabilizer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims139b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section QLevel

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_isMaxEA {p : ℕ} (hp : p.Prime) (Y : Subgroup Q) : ∃ E, Sec13h.IsMaxEA p Y E := by
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Y
  refine ⟨E, hEY, hE, fun F hFY hF => ?_⟩
  rw [hcard, Claims139.card_eq_pow_pRank hp hF]
  exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.pRank_mono hp.one_lt hFY)

theorem card_le_of_split {p : ℕ} {Y C B : Subgroup Q}
    (hYC : ∀ y ∈ Y, ∀ c ∈ C, y * c = c * y) (hYC1 : Y ⊓ C = ⊥) (hB : IsElemAbelian p B)
    (hsplit : ∀ b ∈ B, ∃ y ∈ Y, ∃ c ∈ C, b = y * c)
    (hmax : ∀ A : Subgroup Q, IsElemAbelian p A → Nat.card ↥A ≤ Nat.card ↥B)
    {E : Subgroup Q} (hEY : E ≤ Y) (hE : IsElemAbelian p E) :
    Nat.card ↥E ≤ Nat.card ↥(B ⊓ Y) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hB hx hy
  have huniq : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ c ∈ C, ∀ c' ∈ C, y * c = y' * c' → y = y' ∧ c = c' := by
    intro y hy y' hy' c hc c' hc' h
    have h1 : y'⁻¹ * y = c' * c⁻¹ := by
      calc y'⁻¹ * y = y'⁻¹ * (y * c) * c⁻¹ := by group
        _ = y'⁻¹ * (y' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have h2 : y'⁻¹ * y ∈ Y ⊓ C :=
      ⟨Y.mul_mem (Y.inv_mem hy') hy, h1 ▸ C.mul_mem hc' (C.inv_mem hc)⟩
    rw [hYC1, Subgroup.mem_bot] at h2
    have hyy : y = y' := by
      calc y = y' * (y'⁻¹ * y) := by group
        _ = y' := by rw [h2, mul_one]
    subst hyy
    exact ⟨rfl, mul_left_cancel h⟩
  let P₁ : Subgroup Q :=
    { carrier := {y | y ∈ Y ∧ ∃ c ∈ C, y * c ∈ B}
      mul_mem' := by
        rintro a b ⟨ha, c, hc, hac⟩ ⟨hb, d, hd, hbd⟩
        refine ⟨Y.mul_mem ha hb, c * d, C.mul_mem hc hd, ?_⟩
        have e : a * b * (c * d) = (a * c) * (b * d) := by
          calc a * b * (c * d) = a * (b * c) * d := by group
            _ = a * (c * b) * d := by rw [hYC b hb c hc]
            _ = (a * c) * (b * d) := by group
        rw [e]
        exact B.mul_mem hac hbd
      one_mem' := ⟨Y.one_mem, 1, C.one_mem, by rw [mul_one]; exact B.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, c, hc, hac⟩
        refine ⟨Y.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
          rw [mul_inv_rev, hYC _ (Y.inv_mem ha) _ (C.inv_mem hc)]
        rw [e]
        exact B.inv_mem hac }
  let P₂ : Subgroup Q :=
    { carrier := {c | c ∈ C ∧ ∃ y ∈ Y, y * c ∈ B}
      mul_mem' := by
        rintro c d ⟨hc, a, ha, hac⟩ ⟨hd, b, hb, hbd⟩
        refine ⟨C.mul_mem hc hd, a * b, Y.mul_mem ha hb, ?_⟩
        have e : a * b * (c * d) = (a * c) * (b * d) := by
          calc a * b * (c * d) = a * (b * c) * d := by group
            _ = a * (c * b) * d := by rw [hYC b hb c hc]
            _ = (a * c) * (b * d) := by group
        rw [e]
        exact B.mul_mem hac hbd
      one_mem' := ⟨C.one_mem, 1, Y.one_mem, by rw [mul_one]; exact B.one_mem⟩
      inv_mem' := by
        rintro c ⟨hc, a, ha, hac⟩
        refine ⟨C.inv_mem hc, a⁻¹, Y.inv_mem ha, ?_⟩
        have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
          rw [mul_inv_rev, hYC _ (Y.inv_mem ha) _ (C.inv_mem hc)]
        rw [e]
        exact B.inv_mem hac }
  have hP₁Y : P₁ ≤ Y := fun y hy => hy.1
  have hP₂C : P₂ ≤ C := fun c hc => hc.1
  have hpow : ∀ y ∈ Y, ∀ c ∈ C, y * c ∈ B → y ^ p = 1 ∧ c ^ p = 1 := by
    intro y hy c hc hyc
    have h1 : y ^ p * c ^ p = 1 * 1 := by
      rw [← (show Commute y c from hYC y hy c hc).mul_pow, one_mul]
      exact hB.2 _ hyc
    exact huniq _ (Y.pow_mem hy p) 1 Y.one_mem _ (C.pow_mem hc p) 1 C.one_mem h1
  have hcomm : ∀ y ∈ Y, ∀ c ∈ C, y * c ∈ B → ∀ y' ∈ Y, ∀ c' ∈ C, y' * c' ∈ B →
      y * y' = y' * y ∧ c * c' = c' * c := by
    intro y hy c hc hyc y' hy' c' hc' hyc'
    have h1 := hBc _ hyc _ hyc'
    have e1 : y * c * (y' * c') = (y * y') * (c * c') := by
      calc y * c * (y' * c') = y * (c * y') * c' := by group
        _ = y * (y' * c) * c' := by rw [hYC y' hy' c hc]
        _ = (y * y') * (c * c') := by group
    have e2 : y' * c' * (y * c) = (y' * y) * (c' * c) := by
      calc y' * c' * (y * c) = y' * (c' * y) * c := by group
        _ = y' * (y * c') * c := by rw [hYC y hy c' hc']
        _ = (y' * y) * (c' * c) := by group
    rw [e1, e2] at h1
    exact huniq _ (Y.mul_mem hy hy') _ (Y.mul_mem hy' hy) _ (C.mul_mem hc hc') _
      (C.mul_mem hc' hc) h1
  have hP₁ : IsElemAbelian p P₁ := by
    refine isElemAbelian_of_comm_pow (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨hxY, c, hc, hxc⟩ := hx
      obtain ⟨hyY, d, hd, hyd⟩ := hy
      exact (hcomm x hxY c hc hxc y hyY d hd hyd).1
    · obtain ⟨hxY, c, hc, hxc⟩ := hx
      exact (hpow x hxY c hc hxc).1
  have hP₂ : IsElemAbelian p P₂ := by
    refine isElemAbelian_of_comm_pow (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨hxC, a, ha, hax⟩ := hx
      obtain ⟨hyC, b, hb, hby⟩ := hy
      exact (hcomm a ha x hxC hax b hb y hyC hby).2
    · obtain ⟨hxC, a, ha, hax⟩ := hx
      exact (hpow a ha x hxC hax).2
  have hc12 : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x := fun x hx y hy => hYC x hx.1 y hy.1
  have hbot12 : P₁ ⊓ P₂ = ⊥ := le_bot_iff.1 (hYC1 ▸ inf_le_inf hP₁Y hP₂C)
  have hBP : B ≤ P₁ ⊔ P₂ := by
    intro b hb
    obtain ⟨y, hy, c, hc, rfl⟩ := hsplit b hb
    exact (P₁ ⊔ P₂).mul_mem (Subgroup.mem_sup_left ⟨hy, c, hc, hb⟩)
      (Subgroup.mem_sup_right ⟨hc, y, hy, hb⟩)
  have hBeq : B = P₁ ⊔ P₂ :=
    Subgroup.eq_of_le_of_card_ge hBP (hmax _ (Claims137.isElemAbelian_sup hP₁ hP₂ hc12))
  have hcB : Nat.card ↥B = Nat.card ↥P₁ * Nat.card ↥P₂ := by
    rw [hBeq]
    exact Claims137.card_sup_of_comm hc12 hbot12
  have hP₁B : P₁ ≤ B ⊓ Y := le_inf (hBeq ▸ le_sup_left) hP₁Y
  have hcE : ∀ x ∈ E, ∀ y ∈ P₂, x * y = y * x := fun x hx y hy => hYC x (hEY hx) y hy.1
  have hbotE : E ⊓ P₂ = ⊥ := le_bot_iff.1 (hYC1 ▸ inf_le_inf hEY hP₂C)
  have h1 := hmax _ (Claims137.isElemAbelian_sup hE hP₂ hcE)
  rw [Claims137.card_sup_of_comm hcE hbotE, hcB] at h1
  have hpos : 0 < Nat.card ↥P₂ := Nat.card_pos
  exact (Nat.le_of_mul_le_mul_right h1 hpos).trans (Subgroup.card_le_of_le hP₁B)

theorem exists_split_of_inner (𝒮 : Finset (Subgroup Q)) (h𝒮 : ∀ X ∈ 𝒮, IsComponentOf X ⊤)
    {b : Q} (hinn : ∀ X ∈ 𝒮, ∃ x ∈ X, ∀ z ∈ X, b * z * b⁻¹ = x * z * x⁻¹) :
    ∃ y ∈ ⨆ X ∈ 𝒮, X, y⁻¹ * b ∈ Subgroup.centralizer ((⨆ X ∈ 𝒮, X : Subgroup Q) : Set Q) := by
  classical
  induction 𝒮 using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    have hz1 : z = 1 := by simpa using hz
    rw [hz1, one_mul, mul_one]
  | insert X S hXS ih =>
    obtain ⟨yS, hyS, hcS⟩ := ih (fun X' hX' => h𝒮 X' (Finset.mem_insert_of_mem hX'))
      (fun X' hX' => hinn X' (Finset.mem_insert_of_mem hX'))
    have hX : IsComponentOf X ⊤ := h𝒮 X (Finset.mem_insert_self X S)
    obtain ⟨x, hxX, hx⟩ := hinn X (Finset.mem_insert_self X S)
    rw [Finset.iSup_insert]
    have hSX : (⨆ X' ∈ S, X') ≤ Subgroup.centralizer (X : Set Q) := by
      refine iSup₂_le fun X' hX' => Claims139.le_centralizer_of_ne_comp hX
        (h𝒮 X' (Finset.mem_insert_of_mem hX')) ?_
      rintro rfl
      exact hXS hX'
    have hxyS : Commute x yS := Subgroup.mem_centralizer_iff.1 (hSX hyS) x hxX
    refine ⟨x * yS, Subgroup.mul_mem _ (Subgroup.mem_sup_left hxX) (Subgroup.mem_sup_right hyS), ?_⟩
    have e1 : (x * yS)⁻¹ * b = yS⁻¹ * (x⁻¹ * b) := by group
    have e2 : (x * yS)⁻¹ * b = x⁻¹ * (yS⁻¹ * b) := by
      rw [hxyS.eq]
      group
    have hle : X ⊔ (⨆ X' ∈ S, X') ≤ Subgroup.centralizer ({(x * yS)⁻¹ * b} : Set Q) := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff, e1]
        have c1 : Commute z yS⁻¹ :=
          (show Commute z yS from Subgroup.mem_centralizer_iff.1 (hSX hyS) z hz).inv_right
        have c2 : Commute z (x⁻¹ * b) := by
          have h1 := hx z hz
          show z * (x⁻¹ * b) = x⁻¹ * b * z
          calc z * (x⁻¹ * b) = x⁻¹ * (x * z * x⁻¹) * b := by group
            _ = x⁻¹ * (b * z * b⁻¹) * b := by rw [h1]
            _ = x⁻¹ * b * z := by group
        exact (c1.mul_right c2).eq
      · rw [Subgroup.mem_centralizer_singleton_iff, e2]
        have c1 : Commute z x⁻¹ :=
          (show Commute x z from Subgroup.mem_centralizer_iff.1 (hSX hz) x hxX).symm.inv_right
        have c2 : Commute z (yS⁻¹ * b) := (Subgroup.mem_centralizer_iff.1 hcS z hz)
        exact (c1.mul_right c2).eq
    exact Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle hz))

theorem sSup_eq_iSup_toFinset (𝒞 : Set (Subgroup Q)) :
    sSup 𝒞 = ⨆ X ∈ (Set.toFinite 𝒞).toFinset, X := by
  rw [sSup_eq_iSup]
  refine iSup_congr fun X => ?_
  rw [Set.Finite.mem_toFinset]

theorem le_normalizer_of_comp {X X' : Subgroup Q} (hX : IsComponentOf X ⊤)
    (hX' : IsComponentOf X' ⊤) : X' ≤ Subgroup.normalizer (X : Set Q) := by
  by_cases h : X' = X
  · subst h
    exact Subgroup.le_normalizer
  · exact (Claims139.le_centralizer_of_ne_comp hX hX' (Ne.symm h)).trans
      (Subgroup.centralizer_le_normalizer _)

theorem iSup_inf_eq_bot {S : Finset (Subgroup Q)} (hS : ∀ X' ∈ S, IsComponentOf X' ⊤)
    {X : Subgroup Q} (hX : IsComponentOf X ⊤) (hZ : Subgroup.center ↥X = ⊥) (hXS : X ∉ S) :
    (⨆ X' ∈ S, X') ⊓ X = ⊥ := by
  have hle : (⨆ X' ∈ S, X') ≤ Subgroup.centralizer (X : Set Q) := by
    refine iSup₂_le fun X' hX' => Claims139.le_centralizer_of_ne_comp hX (hS X' hX') ?_
    rintro rfl
    exact hXS hX'
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  have hcen : (⟨z, hz2⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hle hz1) g g.2
  rw [hZ, Subgroup.mem_bot] at hcen
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hcen)

theorem conjMaxEA_sSup {p : ℕ} (hp : p.Prime) {𝒞 : Set (Subgroup Q)}
    (h𝒞 : ∀ X ∈ 𝒞, IsComponentOf X ⊤) (hZ : ∀ X ∈ 𝒞, Subgroup.center ↥X = ⊥)
    (hconj : ∀ X ∈ 𝒞, Claims137.ConjMaxEA p ↥X) : Claims137.ConjMaxEA p ↥(sSup 𝒞) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set 𝓛 := (Set.toFinite 𝒞).toFinset with h𝓛
  have hmem : ∀ X, X ∈ 𝓛 ↔ X ∈ 𝒞 := fun X => Set.Finite.mem_toFinset _
  have hc𝓛 : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := fun X hX => h𝒞 X ((hmem X).1 hX)
  choose F hF using fun L : Subgroup Q => exists_isMaxEA hp L
  have hFc : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∀ x ∈ F L, ∀ y ∈ F L', x * y = y * x := by
    intro L hL L' hL' x hx y hy
    by_cases hLL : L = L'
    · subst hLL
      exact CFSG.Open.IsElemAbelian.comm (hF L).2.1 hx hy
    · exact Claims139.mul_comm_of_ne_comp (hc𝓛 L hL) (hc𝓛 L' hL') hLL ((hF L).1 hx) ((hF L').1 hy)
  obtain ⟨-, hEA, hbound, hcj⟩ := Claims137.conj_join 𝓛
    (fun L hL L' hL' => le_normalizer_of_comp (hc𝓛 L hL) (hc𝓛 L' hL'))
    (fun L hL S hS hLS => by
      rw [iSup_inf_eq_bot (fun X' hX' => hc𝓛 X' (hS hX')) (hc𝓛 L hL) (hZ L ((hmem L).1 hL)) hLS,
        Subgroup.card_bot]
      exact hp.not_dvd_one)
    F (fun L _ => hF L) hFc
    (fun L hL E₁ E₂ h₁ h₂ => Claims137.conj_of_conjMaxEA (hconj L ((hmem L).1 hL)) h₁ h₂)
  set Y : Subgroup Q := sSup 𝒞 with hY
  have hY' : Y = ⨆ L ∈ 𝓛, L := sSup_eq_iSup_toFinset 𝒞
  set EF : Subgroup Q := ⨆ L ∈ 𝓛, F L with hEF
  have hEFY : EF ≤ Y := by
    rw [hY']
    exact iSup₂_le fun L hL => (hF L).1.trans (le_iSup₂_of_le (f := fun L (_ : L ∈ 𝓛) => L) L hL le_rfl)
  intro F₁ F₂ hF₁ hF₂ hm₁ hm₂
  have hcardmap : ∀ F' : Subgroup ↥Y, Nat.card ↥(F'.map Y.subtype) = Nat.card ↥F' := fun F' =>
    Subgroup.card_map_of_injective Y.subtype_injective
  have hEFc : Nat.card ↥(EF.subgroupOf Y) = Nat.card ↥EF :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEFY).toEquiv
  have hcard : ∀ F' : Subgroup ↥Y, IsElemAbelian p F' →
      (∀ F : Subgroup ↥Y, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥F') →
      Nat.card ↥(F'.map Y.subtype) = Nat.card ↥EF := by
    intro F' hF' hm
    refine le_antisymm ?_ ?_
    · refine hbound _ ?_ (CFSG.SectionRank.isElemAbelian_map hF' _)
      rw [← hY']
      exact Subgroup.map_subtype_le F'
    · rw [hcardmap, ← hEFc]
      exact hm _ (CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hEA Y)
  obtain ⟨g, hg, hgE⟩ := hcj (F₁.map Y.subtype) (F₂.map Y.subtype)
    (by rw [← hY']; exact Subgroup.map_subtype_le F₁) (by rw [← hY']; exact Subgroup.map_subtype_le F₂)
    (CFSG.SectionRank.isElemAbelian_map hF₁ _) (CFSG.SectionRank.isElemAbelian_map hF₂ _)
    (hcard F₁ hF₁ hm₁) (hcard F₂ hF₂ hm₂)
  have hgY : g ∈ Y := by rw [hY']; exact hg
  refine ⟨⟨g, hgY⟩, Subgroup.map_injective Y.subtype_injective ?_⟩
  rw [Claims137.map_gLBConj]
  exact hgE

theorem sSup_inf_centralizer_eq_bot {𝒞 : Set (Subgroup Q)} (h𝒞 : ∀ X ∈ 𝒞, IsComponentOf X ⊤)
    (hZ : ∀ X ∈ 𝒞, Subgroup.center ↥X = ⊥) :
    sSup 𝒞 ⊓ Subgroup.centralizer ((sSup 𝒞 : Subgroup Q) : Set Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  refine Subgroup.mem_bot.2 (Claims139.eq_one_of_centralizes_all h𝒞 hZ hz1 fun X hX => ?_)
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sSup hX)) hz2

theorem card_le_inf_sSup {p : ℕ} (hp : p.Prime) {𝒞 : Set (Subgroup Q)}
    (h𝒞 : ∀ X ∈ 𝒞, IsComponentOf X ⊤) (hZ : ∀ X ∈ 𝒞, Subgroup.center ↥X = ⊥)
    (hinner : ∀ X ∈ 𝒞, Inputs71.PPowInner p ↥X) {B : Subgroup Q} (hB : IsElemAbelian p B)
    (hBX : ∀ X ∈ 𝒞, B ≤ Subgroup.normalizer (X : Set Q))
    (hmax : ∀ A : Subgroup Q, IsElemAbelian p A → Nat.card ↥A ≤ Nat.card ↥B)
    {E : Subgroup Q} (hEY : E ≤ sSup 𝒞) (hE : IsElemAbelian p E) :
    Nat.card ↥E ≤ Nat.card ↥(B ⊓ sSup 𝒞) := by
  classical
  set Y : Subgroup Q := sSup 𝒞 with hY
  set C : Subgroup Q := Subgroup.centralizer (Y : Set Q) with hC
  refine card_le_of_split (C := C) (fun y hy c hc => Subgroup.mem_centralizer_iff.1 hc y hy)
    (sSup_inf_centralizer_eq_bot h𝒞 hZ) hB (fun b hb => ?_) hmax hEY hE
  have hinn : ∀ X ∈ (Set.toFinite 𝒞).toFinset, ∃ x ∈ X, ∀ z ∈ X, b * z * b⁻¹ = x * z * x⁻¹ := by
    intro X hX
    rw [Set.Finite.mem_toFinset] at hX
    have hbN : b ∈ Subgroup.normalizer (X : Set Q) := hBX X hX hb
    have hσ : (X.normalizerMonoidHom ⟨b, hbN⟩) ^ (p ^ 1) = 1 := by
      rw [← map_pow, pow_one]
      have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set Q))) ^ p = 1 :=
        Subtype.ext (by simpa using hB.2 b hb)
      rw [this, map_one]
    obtain ⟨x, hx⟩ := hinner X hX _ 1 hσ
    refine ⟨x, x.2, fun z hz => ?_⟩
    have h1 := congrArg (fun σ : MulAut ↥X => ((σ ⟨z, hz⟩ : ↥X) : Q)) hx
    exact h1
  obtain ⟨y, hy, hyc⟩ := exists_split_of_inner _ (fun X hX => h𝒞 X ((Set.Finite.mem_toFinset _).1 hX))
    hinn
  rw [← sSup_eq_iSup_toFinset] at hy hyc
  exact ⟨y, hy, y⁻¹ * b, hyc, by group⟩

theorem exists_mul_centralizer {𝒞 𝒞₀ : Set (Subgroup Q)} (h0 : 𝒞₀ ⊆ 𝒞)
    (h𝒞 : ∀ X ∈ 𝒞, IsComponentOf X ⊤) {y : Q} (hy : y ∈ sSup 𝒞) :
    ∃ y₀ ∈ sSup 𝒞₀, y₀⁻¹ * y ∈ Subgroup.centralizer ((sSup 𝒞₀ : Subgroup Q) : Set Q) := by
  have hsplit : sSup 𝒞 = sSup 𝒞₀ ⊔ sSup (𝒞 \ 𝒞₀) := by
    rw [← sSup_union, Set.union_diff_cancel h0]
  have hle : sSup (𝒞 \ 𝒞₀) ≤ Subgroup.centralizer ((sSup 𝒞₀ : Subgroup Q) : Set Q) := by
    refine sSup_le fun X hX => Subgroup.le_centralizer_iff.2 (sSup_le fun X₀ hX₀ => ?_)
    refine Claims139.le_centralizer_of_ne_comp (h𝒞 X hX.1) (h𝒞 X₀ (h0 hX₀)) ?_
    rintro rfl
    exact hX.2 hX₀
  rw [hsplit] at hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Lemma137.mem_sup_of_comm
    (fun a ha c hc => Subgroup.mem_centralizer_iff.1 (hle hc) a ha) y hy
  refine ⟨a, ha, ?_⟩
  rw [inv_mul_cancel_left]
  exact hle hc

end QLevel

section Types

theorem isMulCommutative_of_card_le_three {H : Type*} [Group H] [Finite H] (h : Nat.card H ≤ 3) :
    IsMulCommutative H := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  interval_cases hc : Nat.card H
  · haveI : Subsingleton H := (Finite.card_le_one_iff_subsingleton).1 hc.le
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := isCyclic_of_prime_card hc
    infer_instance
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := isCyclic_of_prime_card hc
    infer_instance

theorem isMulCommutative_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : IsMulCommutative Y) : IsMulCommutative X :=
  ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hY.is_comm.comm (e a) (e b))⟩⟩

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model in
theorem pPowInner_alt6 {p : ℕ} (hp : Odd p) : Inputs71.PPowInner p ↥(alternatingGroup (Fin 6)) := by
  intro α k hαk
  have hα : Odd (orderOf α) := Odd.of_dvd_nat hp.pow (orderOf_dvd_of_pow_eq_one hαk)
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  set φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm with hφ
  set b : ↥A6Models.autA6 := thetaEquiv φ α with hb
  have hbodd : Odd (orderOf b) := by
    rw [hb, MulEquiv.orderOf_eq]
    exact hα
  have hmem : (b : P10) ∈ A6Models.psl29 := by
    let N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6
    haveI hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using psl29_normal (g : P10) g.2 (n : P10) hn⟩
    have hcardN : Nat.card N = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
    have hQ : Nat.card (↥A6Models.autA6 ⧸ N) = 4 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [card_autA6, hcardN] at this
      omega
    have h1 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ orderOf b :=
      orderOf_map_dvd (QuotientGroup.mk' N) b
    have h2 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ 4 := by
      rw [← hQ]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) = 1 := by
      have hodd := Odd.of_dvd_nat hbodd h1
      have hdiv : ∀ m, m ∣ 4 → m = 1 ∨ m = 2 ∨ m = 4 := by
        intro m hm
        have := Nat.le_of_dvd (by norm_num) hm
        interval_cases m <;> simp_all
      rcases hdiv _ h2 with h | h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
      · rw [h] at hodd; exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h3
    have := (QuotientGroup.eq_one_iff b).1 h3
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨ψ ⟨(b : P10), hmem⟩, MulEquiv.ext fun k => ?_⟩
  apply φ.injective
  apply Subtype.ext
  have hspec := thetaEquiv_spec φ α k
  rw [← hb] at hspec
  rw [hspec, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have : φ (ψ ⟨(b : P10), hmem⟩) = ⟨(b : P10), hmem⟩ := by simp [hφ]
  rw [this]
  rfl

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Assembly.LowTwoRank in
theorem allInner_projSp {r : ℕ} (hr : 3 ≤ r) (α : MulAut (StatedProj (StatedSp r (ZMod 2)))) :
    ∃ y, α = MulAut.conj y := by
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := r) (K := ZMod 2) hr).2 α
  have hσ : σ = 1 := Subsingleton.elim _ _
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hm : A ∈ (multiplier r (ZMod 2)).ker := MonoidHom.mem_ker.2 (Subsingleton.elim _ _)
  rw [ker_multiplier, Subgroup.mem_subgroupOf] at hm
  refine ⟨proj r (ZMod 2) ⟨A, hm⟩, ?_⟩
  rw [hα, hσ, map_one, mul_one]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem pPowInner_statedSp {r : ℕ} (hr : 3 ≤ r) (p : ℕ) :
    Inputs71.PPowInner p ↥(StatedSp r (ZMod 2)) :=
  Inputs71.PPowInner.of_mulEquiv (CFSG.LocalAnalysis.ComponentInitial.BinaryStabilizer.statedSpEquivProj r)
    (fun σ _ _ => allInner_projSp hr σ)

noncomputable def spCommEquiv (n : ℕ) :
    ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))) ≃*
      ↥(commutator ↥(StatedSp n (ZMod 2))) :=
  (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (StatedSp n (ZMod 2))).symm).trans
    (Subgroup.equivMapOfInjective (commutator ↥(StatedSp n (ZMod 2))) (StatedSp n (ZMod 2)).subtype
      (StatedSp n (ZMod 2)).subtype_injective).symm

theorem isMulCommutative_commutator_statedSp_one :
    IsMulCommutative ↥(commutator ↥(StatedSp 1 (ZMod 2))) := by
  set S := StatedSp 1 (ZMod 2) with hS
  have h6 : Nat.card ↥S = 6 := by
    rw [hS, OmegaFacts.card_statedSp_zmod_two]
    decide
  have hne : commutator ↥S ≠ ⊤ := by
    intro htop
    haveI : Nontrivial ↥S := by
      rw [← Finite.one_lt_card_iff_nontrivial, h6]
      norm_num
    have hsolv : Group.IsSolvable ↥S :=
      CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
        (by rw [h6]; decide +kernel)
    exact OmegaFacts.not_isSolvable_of_perfect htop hsolv
  have hlt : Nat.card ↥(commutator ↥S) < 6 := by
    have := card_lt_of_lt' (lt_top_iff_ne_top.2 hne)
    rwa [Subgroup.card_top, h6] at this
  have hdvd : Nat.card ↥(commutator ↥S) ∣ 6 := by
    rw [← h6]
    exact Subgroup.card_subgroup_dvd_card _
  refine isMulCommutative_of_card_le_three ?_
  have hpos : 0 < Nat.card ↥(commutator ↥S) := Nat.card_pos
  interval_cases h : Nat.card ↥(commutator ↥S)
  all_goals first | omega | (norm_num at hdvd)

theorem nonempty_commutator_statedSp_two_mulEquiv :
    Nonempty (↥(commutator ↥(StatedSp 2 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨e0⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
  have hmap : (commutator ↥(StatedSp 2 (ZMod 2))).map e0.toMonoidHom =
      alternatingGroup (Fin 6) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e0.surjective, ← _root_.commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  exact ⟨(Subgroup.equivMapOfInjective _ e0.toMonoidHom e0.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem pPowInner_commutator_statedSp {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : Odd p) :
    Inputs71.PPowInner p ↥(commutator ↥(StatedSp n (ZMod 2))) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · obtain ⟨f⟩ := nonempty_commutator_statedSp_two_mulEquiv
    exact Inputs71.PPowInner.of_mulEquiv f (pPowInner_alt6 hp)
  · have hperf : commutator ↥(StatedSp n (ZMod 2)) = ⊤ :=
      (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n (ZMod 2)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, h3⟩))).commutator_eq_top
    exact Inputs71.PPowInner.of_mulEquiv ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv)
      (pPowInner_statedSp h3 p)

theorem conj_inner_of_types {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnc : ¬ IsMulCommutative X)
    (htype : (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) X) ∨ (∃ k : ℕ, IsAltType (k * p + 2) X) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (X ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
          Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) X ∧ HasFixedPointFreeOrder ε n p)) :
    Claims137.ConjMaxEA p X ∧ Inputs71.PPowInner p X := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases htype with ⟨k, hk5, ⟨e⟩⟩ | ⟨k, ⟨e⟩⟩ | ⟨ε, n, hn, -, ⟨e⟩⟩ | ⟨ε, n, hn, hO, hfp⟩
  · refine ⟨Claims137.ConjMaxEA.of_mulEquiv e.symm (Claims137.conjMaxEA_alt hp hp2 hk5), ?_⟩
    by_cases h6 : k * p = 6
    · have e6 : IsAltType 6 X := h6 ▸ ⟨e⟩
      obtain ⟨e'⟩ := e6
      exact Inputs71.PPowInner.of_mulEquiv e' (pPowInner_alt6 hodd)
    · exact Inputs71.PPowInner.of_mulEquiv e (Inputs71.pPowInner_alt _ hk5 h6 hodd)
  · have hk : 1 ≤ k := by
      by_contra hk0
      obtain rfl : k = 0 := by omega
      exact hnc (isMulCommutative_of_mulEquiv e
        (alternatingGroup.isMulCommutative_of_card_le_three (by simp)))
    have h5 : 5 ≤ k * p + 2 := by nlinarith
    exact ⟨Claims137.ConjMaxEA.of_mulEquiv e.symm (Claims137.conjMaxEA_alt hp hp2 h5),
      Inputs71.PPowInner.of_mulEquiv e
        (Inputs71.pPowInner_alt _ h5 (Inputs71.mul_add_two_ne_six hp hp2) hodd)⟩
  · have e' : X ≃* ↥(commutator ↥(StatedSp n (ZMod 2))) := e.trans (spCommEquiv n)
    have hn2 : 2 ≤ n := by
      by_contra hn1
      obtain rfl : n = 1 := by omega
      exact hnc (isMulCommutative_of_mulEquiv e' isMulCommutative_commutator_statedSp_one)
    exact ⟨Claims137.ConjMaxEA.of_mulEquiv e'.symm
        (ClassicalEA2.conjMaxEA_commutator_statedSp hn2 hp hp2),
      Inputs71.PPowInner.of_mulEquiv e' (pPowInner_commutator_statedSp hn2 hodd)⟩
  · exact ⟨Claims137.conjMaxEA_of_input102
        (OmegaFacts2.input10_2Omega_of_isom ClassicalEA.inputIsomMaxEAConj_holds) hp hp2 hn hfp hO,
      Inputs71.pPowInner_of_isPiTypeGroup hp hp2 (Or.inr (Or.inl ⟨n, ε, hn, hO, hfp⟩))⟩

end Types

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem barX_iSup' {p : ℕ} {C : Subgroup G} {ι : Sort*} (X : ι → Subgroup G)
    (hX : ∀ i, X i ≤ C) : barX p C (⨆ i, X i) = ⨆ i, barX p C (X i) := by
  have h1 : (⨆ i, X i).subgroupOf C = ⨆ i, (X i).subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [inf_eq_right.2 (iSup_le hX)]
    exact iSup_congr fun i => (inf_eq_right.2 (hX i)).symm
  unfold barX
  rw [h1, Subgroup.map_iSup]

theorem gLBConj_sSup_le {Q : Type} [Group Q] (q : Q) {S S' : Set (Subgroup Q)}
    (h : ∀ X ∈ S, GLBConj q X ∈ S') : GLBConj q (sSup S) ≤ sSup S' := by
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (h X hX)

theorem center_eq_bot_of_simple {H : Type*} [Group H] [IsSimpleGroup H] (hnc : ¬ IsMulCommutative H) :
    Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.1 h) hnc

@[expose] def kTilde0 (p : ℕ) (M D T : Subgroup G) :
    Set (Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) :=
  {X | ∃ L, Prop139.BigComp p M D L ∧ X = barX p (Nof T) (derivedInf (Nof T ⊓ L))}

@[expose] def kTildeStar (p : ℕ) (M D T : Subgroup G) :
    Set (Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) :=
  {X | ∃ L, Prop139.BigComp p M D L ∧
    ∃ q, X = GLBConj q (barX p (Nof T) (derivedInf (Nof T ⊓ L)))}

theorem kTilde0_subset (p : ℕ) (M D T : Subgroup G) : kTilde0 p M D T ⊆ kTildeStar p M D T := by
  rintro X ⟨L, hL, rfl⟩
  exact ⟨L, hL, 1, (gLBConj_one _).symm⟩

theorem kBig_le (p : ℕ) (M D T : Subgroup G) : Prop139.KBig p M D T ≤ Nof T :=
  iSup₂_le fun _ _ => (Sec13d.derivedInf_le _).trans inf_le_left

theorem kBig_le_kstar (p : ℕ) (M D T : Subgroup G) :
    Prop139.KBig p M D T ≤ Claims139.KstarOf p M D T := by
  have h1 := le_iSup₂_of_le (f := fun n (_ : n ∈ Nof T) => GLBConj n (Prop139.KBig p M D T))
    (1 : G) (Nof T).one_mem le_rfl
  rw [gLBConj_one] at h1
  exact h1

theorem barX_kBig (p : ℕ) (M D T : Subgroup G) :
    barX p (Nof T) (Prop139.KBig p M D T) = sSup (kTilde0 p M D T) := by
  have hle : ∀ L : Subgroup G, (⨆ (_ : Prop139.BigComp p M D L), derivedInf (Nof T ⊓ L)) ≤ Nof T :=
    fun L => iSup_le fun _ => (Sec13d.derivedInf_le _).trans inf_le_left
  have hle' : ∀ L : Subgroup G, ∀ _ : Prop139.BigComp p M D L, derivedInf (Nof T ⊓ L) ≤ Nof T :=
    fun L _ => (Sec13d.derivedInf_le _).trans inf_le_left
  unfold Prop139.KBig
  rw [barX_iSup' _ hle]
  refine le_antisymm (iSup_le fun L => ?_) (sSup_le ?_)
  · rw [barX_iSup' _ (hle' L)]
    exact iSup_le fun hL => le_sSup ⟨L, hL, rfl⟩
  · rintro X ⟨L, hL, rfl⟩
    refine le_iSup_of_le L ?_
    rw [barX_iSup' _ (hle' L)]
    exact le_iSup_of_le hL le_rfl

theorem barX_kstar (p : ℕ) (M D T : Subgroup G) :
    barX p (Nof T) (Claims139.KstarOf p M D T) = sSup (kTildeStar p M D T) := by
  have hKN := kBig_le p M D T
  have hconjN : ∀ n ∈ Nof T, GLBConj n (Prop139.KBig p M D T) ≤ Nof T := fun n hn =>
    (gLBConj_mono n hKN).trans (mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hn)).le
  unfold Claims139.KstarOf
  rw [barX_iSup' _ (fun n => iSup_le fun hn => hconjN n hn)]
  refine le_antisymm (iSup_le fun n => ?_) (sSup_le ?_)
  · rw [barX_iSup' _ (fun hn => hconjN n hn)]
    refine iSup_le fun hn => ?_
    rw [barX_gLBConj_eq p hn, barX_kBig]
    refine gLBConj_sSup_le _ ?_
    rintro X ⟨L, hL, rfl⟩
    exact ⟨L, hL, _, rfl⟩
  · rintro X ⟨L, hL, q, rfl⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥(Nof T)) q
    refine le_iSup_of_le (n : G) ?_
    rw [barX_iSup' _ (fun hn => hconjN _ hn)]
    refine le_iSup_of_le n.2 ?_
    rw [barX_gLBConj_eq p n.2, barX_kBig]
    exact gLBConj_mono _ (le_sSup ⟨L, hL, rfl⟩)

theorem kTildeStar_data (h138 : Lemma138Statement) (h137 : Lemma137_ii_iiiStatement)
    {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T) {X}
    (hX : X ∈ kTildeStar p M D T) : IsComponentOf X ⊤ ∧ Subgroup.center ↥X = ⊥ := by
  obtain ⟨L, hL, q, rfl⟩ := hX
  have hc := h138 h hL.1 hL.2
  obtain ⟨-, hs, hnc, -⟩ := h137 h hL.1 hL.2
  refine ⟨isComponentOf_gLBConj hc q, ?_⟩
  haveI := hs
  haveI : IsSimpleGroup ↥(GLBConj q (barX p (Nof T) (derivedInf (Nof T ⊓ L)))) :=
    (conjEquiv q (barX p (Nof T) (derivedInf (Nof T ⊓ L)))).symm.isSimpleGroup
  exact center_eq_bot_of_simple fun hab =>
    hnc (isMulCommutative_of_mulEquiv (conjEquiv q _) hab)

theorem kt_conj_inner (h133 : Lemma133Statement) (h137 : Lemma137_ii_iiiStatement)
    (hPi : InputPiCenter) (hNo7 : Lemma137_noA7Statement) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (hBN : B ≤ Nof T) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L) :
    Claims137.ConjMaxEA p ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
      Inputs71.PPowInner p ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have h133' := (h133 h).2 L hL
  have hPiL : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L) := h133'.1.2.1
  have hnhL : ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L) := h133'.1.2.2
  have hrankBL : CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := h133'.2.2.2.2
  have h137' := h137 h hL hL1
  have hKeq := h137'.1
  have hsimp : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := h137'.2.1
  have hnc := h137'.2.2.1
  have hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) := by
    intro ε n hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137'.2.2.2.1 ε n hX).1 hc)
    · exact Or.inr ((h137'.2.2.2.1 ε n hX).2 hc)
  have hA : ∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) := by
    intro k hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137'.2.2.2.2 k hX).1 hc)
    · exact Or.inr ((h137'.2.2.2.2 k hX).2 hc)
  have hLnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := by
    haveI := hPiL.1.2
    exact Function.Surjective.nontrivial
      (f := QuotientGroup.mk (s := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      QuotientGroup.mk_surjective
  have hdvdL : p ∣ Nat.card ↥L :=
    (Lemma137.dvd_card_of_pPrimeCore_eq_bot hp hPiL.2.1).trans (Subgroup.card_quotient_dvd_card _)
  have hJt1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (Nof T ⊓ L)) := by
    have hBLp : IsPGroup p ↥(B ⊓ L) :=
      Lemma137.isPGroup_of_isElemAbelian (Lemma137.isElemAbelian_mono (E := B ⊓ L) (F := B)
        inf_le_left hBel)
    have hBLN : B ⊓ L ≤ Nof T := inf_le_left.trans hBN
    have h1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (B ⊓ L)) := by
      rw [rank_barX_of_isPGroup hp hBLp hBLN, hrankBL]
      exact Lemma137.one_le_pRank_of_dvd hp hdvdL
    exact h1.trans (CFSG.SectionRank.pRank_mono hp1 (barX_mono_of_le p (inf_le_inf_right L hBN)))
  have hdvdJt : p ∣ Nat.card ↥(barX p (Nof T) (Nof T ⊓ L)) :=
    Lemma137.dvd_card_of_one_le_pRank hp hJt1
  have hJtTypes : (∃ k : ℕ, IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L))) ∨
      (∃ k : ℕ, Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∧
        HasFixedPointFreeOrder ε n p) := by
    have hz : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := hPi _ p hp hp2 hPiL hnhL
    let hY : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    obtain ⟨-, -, hcases⟩ := hPiL
    rcases hcases with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn, hΩX, hfp⟩ | ⟨h3, ⟨e⟩⟩
    · have hAX : IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) := ⟨hY.symm.trans e⟩
      rcases hA k hAX with h1 | ⟨e1⟩
      · exact Or.inl ⟨k, h1⟩
      · exact Or.inr (Or.inl ⟨k, e1⟩)
    · have hΩX' : IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Sec13d.isOmegaTwo_of_mulEquiv hY.symm hΩX
      rcases hΩ ε n hΩX' with h1 | ⟨e1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ε, n, hn, h1, hfp⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨ε, n, hn, hfp, e1⟩))
    · exact absurd ⟨hY.symm.trans e⟩ (hNo7 h hL h3)
  haveI := hsimp
  exact conj_inner_of_types hp hp2 hnc
    (Lemma137.kt_types hp hp2 OmegaFacts.inputOmegaTwoPerfect_holds hKeq hnc hdvdJt hJtTypes)

theorem kTildeStar_conj_inner (h133 : Lemma133Statement) (h137 : Lemma137_ii_iiiStatement)
    (hPi : InputPiCenter) (hNo7 : Lemma137_noA7Statement) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (hBN : B ≤ Nof T) {X} (hX : X ∈ kTildeStar p M D T) :
    Claims137.ConjMaxEA p ↥X ∧ Inputs71.PPowInner p ↥X := by
  obtain ⟨L, hL, q, rfl⟩ := hX
  obtain ⟨hc, hi⟩ := kt_conj_inner h133 h137 hPi hNo7 h hBN hL.1 hL.2
  exact ⟨Claims137.ConjMaxEA.of_mulEquiv (conjEquiv q _) hc,
    Inputs71.PPowInner.of_mulEquiv (conjEquiv q _).symm hi⟩

end GLevel

section Steps

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_of_bar {p : ℕ} (hp : p.Prime) {N H P : Subgroup G} (hHN : H ≤ N)
    (hNH : N ≤ Subgroup.normalizer (H : Set G)) (hPH : P ≤ H) (hP : IsPGroup p ↥P) {x : G}
    (hxH : x ∈ H)
    (hx : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hHN hxH⟩ ∈
      Subgroup.centralizer ((barX p N P : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) : Set _)) :
    ∃ c ∈ H ⊓ Subgroup.centralizer (P : Set G), c⁻¹ * x ∈ GLAPPrimeCoreOf p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsn : IsSubnormal H N :=
    IsSubnormal.step hHN ((Subgroup.normal_subgroupOf_iff_le_normalizer hHN).2 hNH)
      (IsSubnormal.refl N)
  set V := GLAPPrimeCore p ↥H with hV
  have hVp : ¬ p ∣ Nat.card ↥V := not_dvd_card_pPrimeCore hp H
  set A : Subgroup ↥H := P.subgroupOf H with hA
  have hAp : IsPGroup p ↥A := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hcen := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p V hVp A hAp
  have hmem : QuotientGroup.mk' V ⟨x, hxH⟩ ∈
      Subgroup.centralizer ((A.map (QuotientGroup.mk' V) : Subgroup (↥H ⧸ V)) : Set (↥H ⧸ V)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have haP : (a : G) ∈ P := Subgroup.mem_subgroupOf.1 ha
    have h1 := Subgroup.mem_centralizer_iff.1 hx (QuotientGroup.mk' _ ⟨a, hHN a.2⟩)
      ⟨⟨a, hHN a.2⟩, Subgroup.mem_subgroupOf.2 haP, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 : ((a : G) * x)⁻¹ * (x * a) ∈ GLAPPrimeCoreOf p N := ⟨_, h1, by simp⟩
    have h3 : ((a : G) * x)⁻¹ * (x * a) ∈ GLAPPrimeCoreOf p H := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
      exact ⟨H.mul_mem (H.inv_mem (H.mul_mem a.2 hxH)) (H.mul_mem hxH a.2), h2⟩
    obtain ⟨w, hw, hwe⟩ := h3
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hwe' : (w : G) = ((a : G) * x)⁻¹ * (x * a) := hwe
    have hw' : (a * ⟨x, hxH⟩)⁻¹ * (⟨x, hxH⟩ * a) = w := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hwe', mul_inv_rev])
    rw [hw']
    exact hw
  rw [← hcen] at hmem
  obtain ⟨c, hc, hcx⟩ := hmem
  refine ⟨c, ⟨c.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩, ?_⟩
  · exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.1 hc ⟨a, hPH ha⟩ (Subgroup.mem_subgroupOf.2 ha))
  · have h1 := (QuotientGroup.eq).1 hcx
    exact ⟨_, h1, by simp⟩

theorem inputFactKstar139_of_siblings (h138 : Lemma138Statement) :
    ClassicalEA2.InputFactKstar139 := by
  intro G _ _ m p B M E A D T h hBN
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hBel : IsElemAbelian p B := h.bOne.1.1
  obtain ⟨hKsN, hNKs⟩ := ClassicalEA2.kstar_le_and_normal p M D T
  have hKN := kBig_le p M D T
  have hKKs := kBig_le_kstar p M D T
  have hcomp : ∀ X ∈ kTildeStar p M D T, IsComponentOf X ⊤ := by
    rintro X ⟨L, hL, q, rfl⟩
    exact isComponentOf_gLBConj (h138 h hL.1 hL.2) q
  intro x hx
  have hxN : x ∈ Nof T := hKsN hx
  have hmx : QuotientGroup.mk' (GLAPPrimeCore p ↥(Nof T)) ⟨x, hxN⟩ ∈ sSup (kTildeStar p M D T) := by
    rw [← barX_kstar]
    exact (mem_barX_iff p _).2 ⟨⟨x, hxN⟩, hx, rfl⟩
  obtain ⟨y₀, hy₀, hc⟩ := exists_mul_centralizer (kTilde0_subset p M D T) hcomp hmx
  rw [← barX_kBig] at hy₀ hc
  obtain ⟨k, hk, rfl⟩ := (mem_barX_iff p _).1 hy₀
  set x' : G := (k : G)⁻¹ * x with hx'
  have hx'Ks : x' ∈ Claims139.KstarOf p M D T :=
    (Claims139.KstarOf p M D T).mul_mem ((Claims139.KstarOf p M D T).inv_mem (hKKs hk)) hx
  have hmk : QuotientGroup.mk' (GLAPPrimeCore p ↥(Nof T)) ⟨x', hKsN hx'Ks⟩ =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(Nof T)) k)⁻¹ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Nof T)) ⟨x, hxN⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  have hx'c : QuotientGroup.mk' (GLAPPrimeCore p ↥(Nof T)) ⟨x', hKsN hx'Ks⟩ ∈
      Subgroup.centralizer ((barX p (Nof T) (B ⊓ Prop139.KBig p M D T) :
        Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) : Set _) := by
    rw [hmk]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (barX_mono_of_le p inf_le_right)) hc
  have hPp : IsPGroup p ↥(B ⊓ Prop139.KBig p M D T) :=
    Lemma137.isPGroup_of_isElemAbelian (Lemma137.isElemAbelian_mono inf_le_left hBel)
  obtain ⟨c, hcK, hcO⟩ := exists_centralizer_of_bar hp hKsN hNKs (inf_le_right.trans hKKs) hPp
    hx'Ks hx'c
  have hxeq : x = (k : G) * (c * (c⁻¹ * x')) := by rw [hx']; group
  rw [hxeq]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hk))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcK) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hcO)))

theorem inputConjKstar139_of_siblings (h138 : Lemma138Statement) (h137 : Lemma137_ii_iiiStatement)
    (h133 : Lemma133Statement) (hNo7 : Lemma137_noA7Statement) (hPi : InputPiCenter) :
    ClassicalEA2.InputConjKstar139 := by
  intro G _ _ m p B M E A D T h hBN
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKsN, hNKs⟩ := ClassicalEA2.kstar_le_and_normal p M D T
  have hQ : Claims137.ConjMaxEA p ↥(sSup (kTildeStar p M D T)) :=
    conjMaxEA_sSup hp (fun X hX => (kTildeStar_data h138 h137 h hX).1)
      (fun X hX => (kTildeStar_data h138 h137 h hX).2)
      (fun X hX => (kTildeStar_conj_inner h133 h137 hPi hNo7 h hBN hX).1)
  rw [← barX_kstar] at hQ
  have hsn : IsSubnormal (Claims139.KstarOf p M D T) (Nof T) :=
    IsSubnormal.step hKsN ((Subgroup.normal_subgroupOf_iff_le_normalizer hKsN).2 hNKs)
      (IsSubnormal.refl _)
  exact Claims137.conjMaxEA_of_quotient (GLAPPrimeCore p ↥(Claims139.KstarOf p M D T))
    (not_dvd_card_pPrimeCore hp _)
    (Claims137.ConjMaxEA.of_mulEquiv (quotEquivBarX hp hKsN hsn).symm hQ)

theorem le_normalizer_of_mem (h113 : Input11_3) (h138 : Lemma138Statement)
    (h137 : Lemma137_ii_iiiStatement) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (hBN : B ≤ Nof T) {X} (hX : X ∈ kTildeStar p M D T) :
    barX p (Nof T) B ≤ Subgroup.normalizer (X : Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hXc, hXZ⟩ := kTildeStar_data h138 h137 h hX
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hTne : T ≠ ⊥ := by
    intro hT0
    obtain ⟨P, hP, -, hPle⟩ := exists_ne_bot_le_pCoreOf h.pre.1.1
    exact hP (eq_bot_iff.2 (hPle.trans (h.hT1.trans hT0.le)))
  have hN2 : IsTwoLocal (Nof T) := ⟨T, hTne, hT2, rfl⟩
  have hNtop : Nof T ≠ ⊤ := isTwoLocal_ne_top hS hN2
  have hNK : CFSG.Open.IsKGroup ↥(Nof T) := isKGroup_of_isKProper hS.kProper hNtop
  have hBmax : GLAIsBmax p (B.subgroupOf (Nof T)) := glaIsBmax_subgroupOf hS h.bOne hN2 hBN
  obtain ⟨Lp, hLp, rfl⟩ := exists_glaPComponent_barX_eq (p := p) (Nof T) hXc
  have hLpN : Lp ≤ Nof T := hLp.1
  by_contra hnot
  have hnotB : ¬ B ≤ Subgroup.normalizer (Lp : Set G) := fun hB => hnot (barX_le_normalizer hB)
  have hcomp : GLAPComponent p (⊤ : Subgroup ↥(Nof T)) (Lp.subgroupOf (Nof T)) :=
    glaPComponent_top hLp
  have hnot' : ¬ B.subgroupOf (Nof T) ≤
      Subgroup.normalizer ((Lp.subgroupOf (Nof T) : Subgroup ↥(Nof T)) : Set ↥(Nof T)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hLpN]
    intro hle
    exact hnotB fun b hb => Subgroup.mem_subgroupOf.1
      (hle (Subgroup.mem_subgroupOf.2 hb : (⟨b, hBN hb⟩ : ↥(Nof T)) ∈ B.subgroupOf (Nof T)))
  have h1 := h113 ↥(Nof T) hNK p hp hp2 (B.subgroupOf (Nof T)) hBmax (Lp.subgroupOf (Nof T)) hcomp
    hnot'
  let e1 : (↥(Lp.subgroupOf (Nof T)) ⧸ GLAPPrimeCore p ↥(Lp.subgroupOf (Nof T))) ≃*
      (↥Lp ⧸ GLAPPrimeCore p ↥Lp) :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLpN)
      (glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hLpN))
  let e : (↥(Lp.subgroupOf (Nof T)) ⧸ GLAPPrimeCore p ↥(Lp.subgroupOf (Nof T))) ≃*
      ↥(barX p (Nof T) Lp) :=
    e1.trans (quotEquivBarX hp hLpN hLp.2.1)
  apply h1
  have hcen := Subgroup.map_center_eq e
  rw [hXZ] at hcen
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcen

theorem inputMaxBKstar139_of_siblings (h138 : Lemma138Statement) (h137 : Lemma137_ii_iiiStatement)
    (h133 : Lemma133Statement) (hNo7 : Lemma137_noA7Statement) (hPi : InputPiCenter)
    (h113 : Input11_3) : ClassicalEA2.InputMaxBKstar139 := by
  intro G _ _ m p B M E A D T h hBN
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBp : IsPGroup p ↥B := Lemma137.isPGroup_of_isElemAbelian hBel
  obtain ⟨hKsN, hNKs⟩ := ClassicalEA2.kstar_le_and_normal p M D T
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hTne : T ≠ ⊥ := by
    intro hT0
    obtain ⟨P, hP, -, hPle⟩ := exists_ne_bot_le_pCoreOf h.pre.1.1
    exact hP (eq_bot_iff.2 (hPle.trans (h.hT1.trans hT0.le)))
  have hN2 : IsTwoLocal (Nof T) := ⟨T, hTne, hT2, rfl⟩
  have hrankN : CFSG.Open.pRank p (Nof T) ≤ m :=
    (pRank_le_glaTwoLocalRank hp1 hN2).trans hS.rank_eq.le
  have hcardBt : Nat.card ↥(barX p (Nof T) B) = p ^ m :=
    (Lemma138b.card_barX_of_isPGroup hp hBp hBN).trans (hS.card_eq h.bOne)
  have hmaxQ : ∀ A' : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)), IsElemAbelian p A' →
      Nat.card ↥A' ≤ Nat.card ↥(barX p (Nof T) B) := fun A' hA' => by
    rw [hcardBt]
    exact Lemma138b.card_le_pow_of_isElemAbelian_quot hp hrankN hA'
  refine ⟨inf_le_right, Lemma137.isElemAbelian_mono inf_le_left hBel, fun F hFKs hF => ?_⟩
  have hFp : IsPGroup p ↥F := Lemma137.isPGroup_of_isElemAbelian hF
  have hFle : barX p (Nof T) F ≤ sSup (kTildeStar p M D T) := by
    rw [← barX_kstar]
    exact barX_mono_of_le p hFKs
  have h1 := card_le_inf_sSup hp (fun X hX => (kTildeStar_data h138 h137 h hX).1)
    (fun X hX => (kTildeStar_data h138 h137 h hX).2)
    (fun X hX => (kTildeStar_conj_inner h133 h137 hPi hNo7 h hBN hX).2) (isElemAbelian_barX hBel)
    (fun X hX => le_normalizer_of_mem h113 h138 h137 h hBN hX) hmaxQ hFle (isElemAbelian_barX hF)
  rw [← barX_kstar] at h1
  have hle : barX p (Nof T) B ⊓ barX p (Nof T) (Claims139.KstarOf p M D T) ≤
      barX p (Nof T) (B ⊓ Claims139.KstarOf p M D T) := by
    rintro y ⟨hyB, hyK⟩
    obtain ⟨b, hbB, rfl⟩ := (mem_barX_iff p _).1 hyB
    have hbpre : (b : G) ∈ preimBarX p (Nof T) (Claims139.KstarOf p M D T) := ⟨b, hyK, rfl⟩
    have hnormal : ((Claims139.KstarOf p M D T).subgroupOf
        (preimBarX p (Nof T) (Claims139.KstarOf p M D T))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hKsN)).2
        ((preimBarX_le p _ _).trans hNKs)
    have hbK : (b : G) ∈ Claims139.KstarOf p M D T :=
      Lemma1312b.mem_of_pPower_of_normal_preim hp hKsN hnormal hbpre (k := 1)
        (by rw [pow_one]; exact hBel.2 _ hbB)
    exact (mem_barX_iff p _).2 ⟨b, ⟨hbB, hbK⟩, rfl⟩
  have hBKp : IsPGroup p ↥(B ⊓ Claims139.KstarOf p M D T) :=
    Lemma137.isPGroup_of_isElemAbelian (Lemma137.isElemAbelian_mono inf_le_left hBel)
  calc Nat.card ↥F = Nat.card ↥(barX p (Nof T) F) :=
        (Lemma138b.card_barX_of_isPGroup hp hFp (hFKs.trans hKsN)).symm
    _ ≤ Nat.card ↥(barX p (Nof T) B ⊓ barX p (Nof T) (Claims139.KstarOf p M D T)) := h1
    _ ≤ Nat.card ↥(barX p (Nof T) (B ⊓ Claims139.KstarOf p M D T)) := Subgroup.card_le_of_le hle
    _ = Nat.card ↥(B ⊓ Claims139.KstarOf p M D T) :=
        Lemma138b.card_barX_of_isPGroup hp hBKp (inf_le_right.trans hKsN)

theorem inputFrattini139_of_siblings (h138 : Lemma138Statement) (h137 : Lemma137_ii_iiiStatement)
    (h133 : Lemma133Statement) (hNo7 : Lemma137_noA7Statement) (hPi : InputPiCenter)
    (h113 : Input11_3) : Claims139.InputFrattini139 :=
  ClassicalEA2.inputFrattini139_of_inputs (inputConjKstar139_of_siblings h138 h137 h133 hNo7 hPi)
    (inputMaxBKstar139_of_siblings h138 h137 h133 hNo7 hPi h113)
    (inputFactKstar139_of_siblings h138)

end Steps

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims139b
