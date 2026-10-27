module

public import CFSG.Certificates.Kernel.SporCov.Words
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPath
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTwoCent

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape

variable {G : Type} [Group G] {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G}

theorem isConj_of_conj {t g x : G} (h : t * g = g * x) : IsConj t x :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]⟩

namespace Model

variable (hM : Model L E ev)
include hM

theorem conj_word {c x ci : List ℕ} (hci : ev ci = (ev c)⁻¹) :
    ev (c ++ x ++ ci) = (ev c)⁻¹ * ev x * ev c := by
  rw [hM.append, hM.append, hci, mul_assoc]

theorem generating_of_ctlA [Finite G] {p : ℕ} (hp : p.Prime) {a ai b bi : List ℕ}
    (hg : genOK E L a ai b bi = true) (hab : Subgroup.closure ({ev a, ev b} : Set G) = ⊤)
    {t g x z₁ h₁ z₂ h₂ : List ℕ} (h : ctlA E L p t g x z₁ h₁ z₂ h₂ a ai b bi = true)
    (ht : chW L t = true) : ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  obtain ⟨oa, oai, ob, obi, ea, eb⟩ := hM.genOK_facts hg
  unfold ctlA at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨og, ox⟩, oz₁⟩, oh₁⟩, oz₂⟩, oh₂⟩, h3⟩, hgt⟩, hl₁⟩, hl₂⟩ := h
  unfold link at hl₁ hl₂
  simp only [Bool.and_eq_true] at hl₁ hl₂
  obtain ⟨⟨e₁, c₁⟩, d₁⟩ := hl₁
  obtain ⟨⟨e₂, c₂⟩, d₂⟩ := hl₂
  have r₁ := hM.comm oz₁ (chW_append_of (chW_append_of oa ox) oai) d₁
  have r₂ := hM.comm oz₂ (chW_append_of (chW_append_of ob ox) obi) d₂
  rw [hM.conj_word ea] at r₁
  rw [hM.conj_word eb] at r₂
  have hgen : SporKRestGenerating p (ev x) :=
    sporKRest_generating_of_paths hp (ev a) (ev b) hab (hM.pow ox h3)
      ⟨_, _, hM.conj' ox oh₁ oz₁ e₁, hM.comm ox oz₁ c₁, r₁⟩
      ⟨_, _, hM.conj' ox oh₂ oz₂ e₂, hM.comm ox oz₂ c₂, r₂⟩
  intro y hy
  exact hgen.of_isConj ((isConj_of_conj (hM.conj ht og ox hgt)).symm.trans hy)

theorem generating_of_ctlB [Finite G] {p : ℕ} (hp : p.Prime) {a ai b bi : List ℕ}
    (hg : genOK E L a ai b bi = true) (hab : Subgroup.closure ({ev a, ev b} : Set G) = ⊤)
    {t g x y h : List ℕ} (hc : ctlB E L p t g x y h a b = true) (ht : chW L t = true) :
    ∀ w, IsConj (ev t) w → SporKRestGenerating p w := by
  obtain ⟨oa, -, ob, -, -, -⟩ := hM.genOK_facts hg
  unfold ctlB at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨og, ox⟩, oy⟩, oh⟩, h3⟩, hgt⟩, hxb⟩, hxy⟩, hxh⟩, hya⟩ := hc
  have hya' : ev y * ev a = ev a * ev y ∨ ev h = ev a := by
    rcases hya with hya | hya
    · exact Or.inl (hM.comm oy oa hya)
    · exact Or.inr (hM.eq oh oa hya)
  have hgen : SporKRestGenerating p (ev x) :=
    sporKRest_generating_of_ctrl hp (ev a) (ev b) hab (hM.pow ox h3) (hM.comm ox ob hxb)
      (hM.comm ox oy hxy) (hM.conj' ox oh oy hxh) hya'
  intro w hw
  exact hgen.of_isConj ((isConj_of_conj (hM.conj ht og ox hgt)).symm.trans hw)

theorem clH_facts {p nL : ℕ} {t y₁ y₂ g₁ g₂ : List ℕ} {M : List (List ℕ)}
    (h : clH E L p t y₁ y₂ g₁ g₂ M nL = true) (ht : chW L t = true) :
    lenLe M (2 * nL) = true ∧ chA L M = true ∧ chW L y₁ = true ∧ chW L y₂ = true ∧
      ev y₁ ^ p = 1 ∧ ev y₂ ^ p = 1 ∧ ev y₁ * ev y₂ = ev y₂ * ev y₁ ∧
      ev t * ev g₁ = ev g₁ * ev y₁ ∧ ev t * ev g₂ = ev g₂ * ev y₂ := by
  unfold clH at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM2, o₁⟩, o₂⟩, og₁⟩, og₂⟩, hMc⟩, h₁⟩, h₂⟩, e₁⟩, e₂⟩, hc⟩ := h
  exact ⟨hM2, hMc, o₁, o₂, hM.pow o₁ h₁, hM.pow o₂ h₂, hM.comm o₁ o₂ hc,
    hM.conj ht og₁ o₁ e₁, hM.conj ht og₂ o₂ e₂⟩

theorem mem_of_cl_letters {p nL n : ℕ} {t y₁ y₂ g₁ g₂ : List ℕ} {M : List (List ℕ)}
    (h : clH E L p t y₁ y₂ g₁ g₂ M nL = true) (ht : chW L t = true)
    (hL : ∀ j < nL, clL E y₁ y₂ n M j = true) (k : ℕ) :
    ev (nthW M k) ∈ Subgroup.closure
      ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂}) := by
  obtain ⟨hM2, hMc, o₁, o₂, -⟩ := hM.clH_facts h ht
  exact hM.mem_of_letters hM2 hMc o₁ o₂ hL k

theorem mem_of_cl_cm {y₁ y₂ s : List ℕ} (o₁ : chW L y₁ = true) (os : chW L s = true)
    (hs : cm E s y₁ = true) :
    ev s ∈ Subgroup.closure
      ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂}) :=
  Subgroup.subset_closure (Or.inl (Subgroup.mem_centralizer_singleton_iff.2 (hM.comm os o₁ hs)))

theorem generating_of_cl [Finite G] {p nL : ℕ} (hp : p.Prime) {t y₁ y₂ g₁ g₂ : List ℕ}
    {M : List (List ℕ)} (h : clH E L p t y₁ y₂ g₁ g₂ M nL = true) (ht : chW L t = true)
    (htop : Subgroup.closure
      ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂}) = ⊤) :
    ∀ y, IsConj (ev t) y → SporKRestGenerating p y := by
  obtain ⟨-, -, -, -, h₁, h₂, hc, hT₁, hT₂⟩ := hM.clH_facts h ht
  have hY₁ : ev y₁ = (ev g₁)⁻¹ * ev t * ev g₁ := by
    rw [mul_assoc, hT₁, ← mul_assoc, inv_mul_cancel, one_mul]
  have hY₂ : ev y₂ = (ev g₂)⁻¹ * ev t * ev g₂ := by
    rw [mul_assoc, hT₂, ← mul_assoc, inv_mul_cancel, one_mul]
  have hh : ev y₁ * ((ev g₁)⁻¹ * ev g₂) = (ev g₁)⁻¹ * ev g₂ * ev y₂ := by
    rw [hY₁, hY₂]
    group
  intro y hy
  exact sporKRest_generating_of_twoCent hp h₁ h₂ hc hh htop
    ((isConj_of_conj hT₁).symm.trans hy)

theorem cover_of_val_two [Finite G] {p : ℕ} (hp : p.Prime) (hval : (Nat.card G).factorization p = 2)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {t : List ℕ} (ht : chW L t = true)
    (hne : neOK E t = true) (hpow : E (repW t p) [] = true)
    (hgen : ∀ y, IsConj (ev t) y → SporKRestGenerating p y) : SporKRestCover p G :=
  sporKRest_cover_of_orderE hp hval (ev t) (hM.ne_one hc ht hne)
    (isPGroup_zpowers_of_pow (hM.pow ht hpow)) hgen

theorem cover_of_cl [Finite G] {p nL : ℕ} (hp : p.Prime) (hval : (Nat.card G).factorization p = 2)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {t y₁ y₂ g₁ g₂ : List ℕ}
    {M : List (List ℕ)} (h : clH E L p t y₁ y₂ g₁ g₂ M nL = true) (ht : chW L t = true)
    (hne : neOK E t = true)
    (htop : Subgroup.closure
      ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂}) = ⊤) :
    SporKRestCover p G := by
  obtain ⟨-, -, -, -, h₁, -, -, hT₁, -⟩ := hM.clH_facts h ht
  have hY : ev t = ev g₁ * ev y₁ * (ev g₁)⁻¹ := by
    rw [← hT₁, mul_inv_cancel_right]
  have hpow : ev t ^ p = 1 := by
    rw [hY, conj_pow, h₁, mul_one, mul_inv_cancel]
  exact sporKRest_cover_of_orderE hp hval (ev t) (hM.ne_one hc ht hne)
    (isPGroup_zpowers_of_pow hpow) (hM.generating_of_cl hp h ht htop)

end Model

end CFSG.KD.SporCov

end
