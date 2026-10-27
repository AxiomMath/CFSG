module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlpha
public import CFSG.ClassicalInvolution.Balance.BootstrapFunctor

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy
open scoped commutatorElement

structure RankThreeBalance {G : Type} [Group G] (A : Subgroup G) : Prop where
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  weak : WeakBalanced A
  two : TwoBalancedWrt A

namespace RankThreeBalance

variable {G : Type} [Group G] {A : Subgroup G}

theorem comm (h : RankThreeBalance A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (h.elem.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem mul_self (h : RankThreeBalance A) {x : G} (hx : x ∈ A) : x * x = 1 := by
  rw [← pow_two]
  exact h.elem.2 x hx

end RankThreeBalance

section Generation

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_zpowers_of_card_prime {p : ℕ} (hp : p.Prime) {S : Subgroup G}
    (hS : Nat.card S = p) : ∃ b ∈ S, b ≠ 1 ∧ S = Subgroup.zpowers b := by
  have hne : S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS
    exact hp.one_lt.ne hS
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb1 : (b : G) ≠ 1 := fun e => hb (Subtype.ext e)
  have hord : orderOf (b : G) = p := by
    have hdvd : orderOf (b : G) ∣ p := hS ▸ Subgroup.orderOf_dvd_natCard S b.2
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  refine ⟨b, b.2, hb1, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr b.2) ?_
  rw [Nat.card_zpowers, hord, hS]

omit [Finite G] in
theorem centralizer_zpowers_eq_singleton' (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer {a} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem iSup_inf_centralizer_two {B X : Subgroup G} (hB : IsElemAbelian 2 B)
    (hrank : 4 ≤ Nat.card B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Odd (Nat.card X)) :
    (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), X ⊓ Subgroup.centralizer {b}) = X := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two B X hB (by simpa using hrank) hBX (Nat.coprime_two_left.mpr hX)
  apply le_antisymm
  · exact iSup_le fun b => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · refine le_of_eq_of_le hgen.symm (iSup_le fun S => iSup_le fun hS => ?_)
    obtain ⟨b, hbS, hb1, rfl⟩ := exists_eq_zpowers_of_card_prime Nat.prime_two
      (by simpa using hS.2)
    rw [centralizer_zpowers_eq_singleton']
    exact le_iSup_of_le b (le_iSup_of_le (hS.1 hbS) (le_iSup_of_le hb1 le_rfl))

theorem iSup_inf_centralizer_sdiff_two {A E X : Subgroup G} (hA : IsElemAbelian 2 A)
    (hEA : E ≤ A) (hrank : 4 * Nat.card E ≤ Nat.card A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Odd (Nat.card X)) :
    (⨆ (b : G) (_ : b ∈ A) (_ : b ∉ E), X ⊓ Subgroup.centralizer {b}) = X := by
  obtain ⟨F, hFA, -, hEF, hsup⟩ := exists_complement_containing Nat.prime_two hA hEA bot_le
    (inf_bot_eq E)
  have hcard := card_mul_card_complement hA hEA hFA hEF hsup
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hF2 : 4 ≤ Nat.card F := by
    refine Nat.le_of_mul_le_mul_left ?_ hEpos
    rw [hcard, mul_comm]
    exact hrank
  have hgen := iSup_inf_centralizer_two
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hFA) hF2 (hFA.trans hAX) hX
  apply le_antisymm
  · exact iSup_le fun b => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · refine le_of_eq_of_le hgen.symm ?_
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    refine le_iSup_of_le b (le_iSup_of_le (hFA hb) (le_iSup_of_le ?_ le_rfl))
    intro hbE
    exact hb1 (Subgroup.mem_bot.mp (hEF ▸ Subgroup.mem_inf.mpr ⟨hbE, hb⟩))

end Generation

section Constancy

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem comm_of_mem_subgroup (h : RankThreeBalance A) {F : Subgroup G} (hFA : F ≤ A) :
    ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun _ hf _ hf' => h.comm (hFA hf) (hFA hf')

omit [Finite G] in
theorem commute_of_mem (h : RankThreeBalance A) {F : Subgroup G} (hFA : F ≤ A) {g : G}
    (hg : g ∈ A) : ∀ f ∈ F, g * f = f * g := fun _ hf => h.comm hg (hFA hf)

theorem commutator_mem_alphaCore (h : RankThreeBalance A) {F : Subgroup G} (hFA : F ≤ A)
    (hF4 : Nat.card F = 4) {u g : G} (hu : u ∈ uCore F) (hg : g ∈ A) :
    ⁅u, g⁆ ∈ alphaCore F := by
  have hcardA : Nat.card A = 2 * Nat.card F := by rw [h.card, hF4]
  have hAα : ∀ g ∈ A, ∀ x ∈ alphaCore F, g * x * g⁻¹ ∈ alphaCore F := fun g hg x hx =>
    conj_mem_alphaCore (commute_of_mem h hFA hg) hx
  let M : Subgroup G :=
    { carrier := {u | u ∈ uCore F ∧ ∀ g ∈ A, ⁅u, g⁆ ∈ alphaCore F}
      one_mem' := ⟨one_mem _, fun g _ => by simp⟩
      mul_mem' := fun {u v} hu hv => ⟨(uCore F).mul_mem hu.1 hv.1, fun g hg => by
        have e : ⁅u * v, g⁆ = u * ⁅v, g⁆ * u⁻¹ * ⁅u, g⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (alphaCore F).mul_mem (conj_mem_alphaCore_of_mem_uCore hu.1 (hv.2 g hg))
          (hu.2 g hg)⟩
      inv_mem' := fun {u} hu => ⟨(uCore F).inv_mem hu.1, fun g hg => by
        have e : ⁅u⁻¹, g⁆ = u⁻¹ * ⁅u, g⁆⁻¹ * u⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact conj_mem_alphaCore_of_mem_uCore ((uCore F).inv_mem hu.1)
          ((alphaCore F).inv_mem (hu.2 g hg))⟩ }
  have hUM : uCore F ≤ M := by
    refine iSup₂_le fun d hd => iSup_le fun hd1 => ?_
    have hdA : d ∈ A := hFA hd
    have hd2 : d * d = 1 := h.mul_self hdA
    have hPodd : Odd (Nat.card (involutionOddCore d)) := odd_card_oddCoreIn _
    have hAP : A ≤ Subgroup.normalizer (involutionOddCore d : Set G) := fun x hx =>
      normalizer_oddCoreIn _ (mem_centralizer_singleton_of_mem h.elem.1 hx hdA)
    have hgen := iSup_inf_centralizer_sdiff_two h.elem (E := Subgroup.zpowers d)
      (Subgroup.zpowers_le.mpr hdA)
      (by rw [card_zpowers_of_involution hd2 hd1, h.card]) hAP hPodd
    refine le_of_eq_of_le hgen.symm (iSup_le fun b => iSup_le fun hbA => iSup_le fun hbd => ?_)
    rintro c ⟨hcP, hcb⟩
    have hcU : c ∈ uCore F := involutionOddCore_le_uCore hd hd1 hcP
    refine ⟨hcU, fun g hg => ?_⟩
    have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer d hcP)
    have hcbc : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcb
    by_cases hbF : b ∈ F
    ·
      have hb1 : b ≠ 1 := fun e => hbd (e ▸ one_mem _)
      have hdb1 : d * b ≠ 1 := fun e => hbd (by
        have : b = d⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [this]
        exact (Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d))
      have hFelems : ∀ f ∈ F, f = 1 ∨ f = d ∨ f = b ∨ f = d * b := by
        intro f hf
        have hcardF : Nat.card F = 2 * Nat.card (Subgroup.zpowers d) := by
          rw [card_zpowers_of_involution hd2 hd1, hF4]
        rcases mem_or_inv_mul_mem (Subgroup.zpowers_le.mpr hd) hcardF hbF hbd hf with h1 | h1
        · rcases mem_zpowers_involution hd2 h1 with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · rcases mem_zpowers_involution hd2 h1 with e | e
          · right; right; left
            exact (inv_mul_eq_one.mp e).symm
          · right; right; right
            have : f = b * d := by
              calc f = b * (b⁻¹ * f) := by group
                _ = b * d := by rw [e]
            rw [this]
            exact h.comm hbA hdA
      have hdc : ⁅c, g⁆ ∈ involutionOddCore d := by
        have e : ⁅c, g⁆ = c * (g * c⁻¹ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (involutionOddCore d).mul_mem hcP
          (conj_mem_oddCoreIn (mem_centralizer_singleton_of_mem h.elem.1 hg hdA)
            ((involutionOddCore d).inv_mem hcP))
      have hcdb : c ∈ Subgroup.centralizer ({d * b} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc c * (d * b) = (c * d) * b := by group
            _ = (d * c) * b := by rw [hcd]
            _ = d * (c * b) := by group
            _ = d * (b * c) := by rw [hcbc]
            _ = (d * b) * c := by group)
      have hmem : ⁅c, g⁆ ∈ deltaCore F := by
        rw [mem_deltaCore_iff]
        intro f hf hf1
        rcases hFelems f hf with rfl | rfl | rfl | rfl
        · exact absurd rfl hf1
        · exact hdc
        · exact h.weak d hdA hd1 f hbA hb1 (Subgroup.commutator_mem_commutator ⟨hcP, hcb⟩ hg)
        · exact h.weak d hdA hd1 (d * b) (A.mul_mem hdA hbA) hdb1
            (Subgroup.commutator_mem_commutator ⟨hcP, hcdb⟩ hg)
      exact deltaCore_le_alphaCore hmem
    ·
      rcases mem_or_inv_mul_mem hFA hcardA hbA hbF hg with hgF | hgF
      · exact commutator_le_alphaCore (Subgroup.commutator_mem_commutator hcU hgF)
      · have hcf : ⁅c, b⁻¹ * g⁆ ∈ alphaCore F :=
          commutator_le_alphaCore (Subgroup.commutator_mem_commutator hcU hgF)
        have hcb1 : ⁅c, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcbc
        have e : ⁅c, g⁆ = ⁅c, b⁆ * (b * ⁅c, b⁻¹ * g⁆ * b⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hcb1, one_mul]
        exact hAα b hbA _ hcf
  exact (hUM hu).2 g hg

omit [Finite G] in
theorem uCore_le_completion {F : Subgroup G} (hFA : F ≤ A) : uCore F ≤ deltaStarCompletion A :=
  iSup₂_le fun f hf => iSup_le fun hf1 =>
    (le_sup_left : involutionOddCore f ≤ deltaStar A f).trans
      (deltaStar_le_deltaStarCompletion (hFA hf) hf1)

theorem completion_le_uCore_sup (h : RankThreeBalance A) {F : Subgroup G} (hFA : F ≤ A)
    (hF4 : Nat.card F = 4) : deltaStarCompletion A ≤ uCore F ⊔ centralOddCore A := by
  obtain ⟨hodd, hnorm, hfix, -, -⟩ := deltaStar_isCompletion h.elem (by rw [h.card]) h.weak
  have hFel : IsElemAbelian 2 F :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 h.elem hFA
  have hgen := iSup_inf_centralizer_two hFel (by rw [hF4]) (hFA.trans hnorm) hodd
  refine le_of_eq_of_le hgen.symm (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
  rw [hfix b (hFA hb) hb1]
  exact sup_le_sup_right (involutionOddCore_le_uCore hb hb1) _

omit [Finite G] in
theorem centralOddCore_le_normalizer_uCore {F : Subgroup G} (hFA : F ≤ A) :
    centralOddCore A ≤ Subgroup.normalizer (uCore F : Set G) := by
  intro t ht
  have htF : ∀ f ∈ F, t * f = f * t := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht) f (hFA hf)).symm
  have htF' : ∀ f ∈ F, t⁻¹ * f = f * t⁻¹ := fun f hf => by
    have := htF f hf
    calc t⁻¹ * f = t⁻¹ * (f * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * f) * t⁻¹ := by rw [this]
      _ = f * t⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_uCore htF hy, fun hy => ?_⟩
  have := conj_mem_uCore htF' hy
  simpa [mul_assoc] using this

theorem conj_mem_alphaCore_of_mem_completion (h : RankThreeBalance A) {F : Subgroup G}
    (hFA : F ≤ A) (hF4 : Nat.card F = 4) {w : G} (hw : w ∈ deltaStarCompletion A) {x : G}
    (hx : x ∈ alphaCore F) : w * x * w⁻¹ ∈ alphaCore F := by
  have hwU := completion_le_uCore_sup h hFA hF4 hw
  obtain ⟨n, hn, t, ht, rfl⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _
    (centralOddCore_le_normalizer_uCore hFA) w).mp hwU
  have htF : ∀ f ∈ F, t * f = f * t := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht) f (hFA hf)).symm
  have e : n * t * x * (n * t)⁻¹ = n * (t * x * t⁻¹) * n⁻¹ := by group
  rw [e]
  exact conj_mem_alphaCore_of_mem_uCore hn (conj_mem_alphaCore htF hx)

theorem commutator_mem_alphaCore_of_mem_completion (h : RankThreeBalance A) {F : Subgroup G}
    (hFA : F ≤ A) (hF4 : Nat.card F = 4) {w g : G} (hw : w ∈ deltaStarCompletion A)
    (hg : g ∈ A) : ⁅w, g⁆ ∈ alphaCore F := by
  have hwU := completion_le_uCore_sup h hFA hF4 hw
  obtain ⟨n, hn, t, ht, rfl⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _
    (centralOddCore_le_normalizer_uCore hFA) w).mp hwU
  have htg : t * g = g * t :=
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht) g hg).symm
  have ht1 : ⁅t, g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr htg
  have e : ⁅n * t, g⁆ = n * ⁅t, g⁆ * n⁻¹ * ⁅n, g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, ht1]
  simpa using commutator_mem_alphaCore h hFA hF4 hn hg

end Constancy

end CFSG.ClassicalInvolution.Balance.Bootstrap
