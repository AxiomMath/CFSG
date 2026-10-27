module

public import CFSG.GH74.GLS.Stage2.Final.L26.Pair
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG
open CFSG.GH74.GLS.Stage2.Local (sl2_model_facts sl2_model_center_inv central_mem_of_card_inf
  mem_center_of_commutators_central InducedPGL2 normal_commutator_top commutator_mul_right_of_commute)
open scoped commutatorElement

section Outer

variable {Y : Type} [Group Y]

theorem exists_mul_of_mem_sup_centralizer {L : Subgroup Y} {x : Y}
    (hx : x ∈ L ⊔ centralizer (L : Set Y)) : ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), x = a * c :=
  exists_mul_of_mem_sup_of_commute (fun a ha _ hc => Subgroup.mem_centralizer_iff.mp hc a ha) hx

theorem not_mem_mul_centralizer_of_inducedPGL2 {L SB RB : Subgroup Y} {r : ℕ} (hodd : Odd r)
    (hL : HasSL2Model ↥L (fun q => q = r)) (hind : InducedPGL2 L SB r) {y : Y}
    (hS : ∀ s ∈ SB, s ∈ RB ∨ y⁻¹ * s ∈ RB)
    (hR : ∀ s ∈ RB, ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), s = a * c) :
    ¬ ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), y = a * c := by
  rintro ⟨a₀, ha₀, c₀, hc₀, hy⟩
  have hSLC : SB ≤ L ⊔ centralizer (L : Set Y) := by
    intro s hs
    rcases hS s hs with h | h
    · obtain ⟨a, ha, c, hc, rfl⟩ := hR s h
      exact Subgroup.mul_mem_sup ha hc
    · obtain ⟨a, ha, c, hc, hac⟩ := hR _ h
      have hca : c₀ * a = a * c₀ := (Subgroup.mem_centralizer_iff.mp hc₀ a ha).symm
      have hs' : s = (a₀ * a) * (c₀ * c) := by
        have h1 : s = y * (y⁻¹ * s) := by group
        rw [h1, hac, hy]
        calc a₀ * c₀ * (a * c) = a₀ * (c₀ * a) * c := by group
          _ = a₀ * (a * c₀) * c := by rw [hca]
          _ = a₀ * a * (c₀ * c) := by group
      rw [hs']
      exact Subgroup.mul_mem_sup (L.mul_mem ha₀ ha) ((centralizer (L : Set Y)).mul_mem hc₀ hc)
  have hM : L ⊔ SB ≤ L ⊔ centralizer (L : Set Y) := sup_le le_sup_left hSLC
  have hr : 2 ≤ r := by
    obtain ⟨F, hF, hFin, hq, -⟩ := hL
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 : Nat.card F = r := hq
    omega
  have hZ : Nat.card (center ↥L) = 2 := (sl2_model_center_inv hodd hL).1
  have hLcard : Nat.card ↥L = r * (r ^ 2 - 1) := by
    obtain ⟨F, hF, hFin, hq, ⟨eL⟩⟩ := hL
    rw [Nat.card_congr (eL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).toEquiv,
      GorensteinWalter.sl2_card_formula F]
    have h2 : Nat.card F = r := hq
    rw [h2]
  obtain ⟨hn, F₀, hF₀, hFin₀, hcard₀, ⟨e⟩⟩ := hind
  have hPcard : Nat.card (↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB)) =
      r * (r ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.pgl2_card_formula F₀]
    have h2 : Nat.card F₀ = r := hcard₀
    rw [h2]
  let f : ↥L →* ↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB) :=
    (QuotientGroup.mk' ((centralizer (L : Set Y)).subgroupOf (L ⊔ SB))).comp
      (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ SB))
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, c, hc, hmac⟩ := exists_mul_of_mem_sup_centralizer (hM m.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ SB) ⟨a, ha⟩) = QuotientGroup.mk m
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show a⁻¹ * (m : Y) ∈ centralizer (L : Set Y)
    have h1 : a⁻¹ * (a * c) = c := by group
    rw [hmac, h1]
    exact hc
  have hker : f.ker = center ↥L := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    show QuotientGroup.mk (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ SB) ⟨a, ha⟩) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g.1 g.2)
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  have hcard : Nat.card ↥L =
      Nat.card (↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB)) * Nat.card (center ↥L) := by
    have h1 := Subgroup.index_ker f
    have h2 := f.ker.index_mul_card
    rw [h1] at h2
    have h3 : Nat.card f.range =
        Nat.card (↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB)) := by
      rw [MonoidHom.range_eq_top.mpr hfs]
      exact Subgroup.card_top
    have h4 : Nat.card f.ker = Nat.card (center ↥L) := by rw [hker]
    rw [h3, h4] at h2
    exact h2.symm
  rw [hLcard, hPcard, hZ] at hcard
  have hpos : 0 < r * (r ^ 2 - 1) := by
    apply Nat.mul_pos (by omega)
    have : 2 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
    omega
  omega

end Outer

section Component

variable {Y : Type} [Group Y] [Finite Y]

theorem le_commutator_of_isComponent {L : Subgroup Y} (hL : IsComponent L) {y : Y}
    (hy : ¬ ∀ a ∈ L, y * a = a * y) : L ≤ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
  have hN : (⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆).Normal := normal_commutator_top _
  rcases CFSG.LocalCores.component_normal_subgroup hL hN with h | h
  · exact h
  · exfalso
    have hperf : Group.IsPerfect ↥L := hL.1.1
    have hdbl : ⁅⁅L, Subgroup.zpowers y⁆, L⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅L, Subgroup.zpowers y⁆, L⁆ ≤ ⁅⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆, L⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_rfl) le_rfl
        _ = ⁅L, ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := h
    have hbot := CFSG.LocalCores.perfect_double_commutator hperf hdbl
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact hy fun a ha => Subgroup.mem_centralizer_iff.mp (hbot ha) y (Subgroup.mem_zpowers y)

omit [Finite Y] in
theorem le_normalizer_of_pairwise_commute {A B : Subgroup Y} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set Y) := fun b hb =>
  (Subgroup.centralizer_le_normalizer (A : Set Y))
    (Subgroup.mem_centralizer_iff.mpr fun a ha => h a ha b hb)

omit [Finite Y] in
theorem isComponent_of_sl2_pair {L₁ L₂ Lb : Subgroup Y} {q : ℕ} (hsup : L₁ ⊔ L₂ = Lb)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hLb : Lb.Normal) (hodd : Odd q) (h4 : 4 ≤ q)
    (h : HasSL2Model ↥L₁ (fun r => r = q)) : IsComponent L₁ := by
  have hq := (sl2_model_facts hodd h4 h).1
  have hLle : L₁ ≤ Lb := hsup ▸ le_sup_left
  have hN : (L₁.subgroupOf Lb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLle, ← hsup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_pairwise_commute hcomm)
  exact ⟨hq, Subgroup.IsSubnormal.step L₁ Lb hLle (Subgroup.Normal.isSubnormal hLb) hN⟩

theorem le_of_normal_twoGroup_of_two_comps {L₁ L₂ W : Subgroup Y} [hW : W.Normal]
    (hq₁ : IsQuasisimple ↥L₁) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ₁ : ∀ a ∈ L₁, (∀ c ∈ L₁, c * a = a * c) → a ∈ L₂)
    (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) = 1) (hWle : W ≤ L₁ ⊔ L₂) : W ≤ L₂ := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hWle hw)
  have hD : (W.subgroupOf L₁).Normal := hW.subgroupOf L₁
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq₁ hD with htop | hcen
  · exfalso
    have hall : ∀ x : ↥L₁, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
      intro x
      have hx : (x : Y) ∈ W := by
        have : x ∈ W.subgroupOf L₁ := by rw [htop]; trivial
        exact this
      obtain ⟨k, hk⟩ := hW2 x hx
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hp : IsPGroup 2 ↥L₁ := hall
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent ↥L₁ := hp.isNilpotent
    have hsol : Group.IsSolvable ↥L₁ := inferInstance
    have : Nontrivial ↥L₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq₁
    have : Group.IsPerfect ↥L₁ := hq₁.1
    exact Group.IsPerfect.not_isSolvable ↥L₁ hsol
  · have hacen : (⟨a, ha⟩ : ↥L₁) ∈ center ↥L₁ := by
      apply mem_center_of_commutators_central hq₁
      intro g
      apply hcen
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hg : (g : Y) * b = b * (g : Y) := hcomm g g.2 b hb
      have e1 : ⁅(g : Y), a * b⁆ = ⁅(g : Y), a⁆ := commutator_mul_right_of_commute hg
      have e2 : ((⁅g, (⟨a, ha⟩ : ↥L₁)⁆ : ↥L₁) : Y) = ⁅(g : Y), a⁆ := by
        simp [commutatorElement_def]
      rw [e2, ← e1]
      have h3 : (g : Y) * (a * b) * (g : Y)⁻¹ ∈ W := hW.conj_mem _ hw _
      have h4 : ⁅(g : Y), a * b⁆ = ((g : Y) * (a * b) * (g : Y)⁻¹) * (a * b)⁻¹ := by
        simp [commutatorElement_def]
      rw [h4]
      exact W.mul_mem h3 (W.inv_mem hw)
    have hc : ∀ c ∈ L₁, c * a = a * c := fun c hc =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hacen ⟨c, hc⟩)
    exact L₂.mul_mem (hZ₁ a ha hc) hb

end Component

end CFSG.GH74.GLS.Stage2.Final.L26
