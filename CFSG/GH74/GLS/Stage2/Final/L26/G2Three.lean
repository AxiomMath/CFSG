module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG
open CFSG.GH74.GLS.Stage2.Local (InducedPGL2 SL23 slMapEquiv sl2_model_center_inv commutator_mul_right_of_commute)
open scoped commutatorElement

section SL23

theorem sl23_key3 : ∀ l b : SL23,
    (∀ g : SL23, g * l ^ 3 = l ^ 3 * g) → ¬ (∀ g : SL23, g * l = l * g) → b ^ 8 = 1 →
    (∀ g : SL23, g * b = b * g) ∨ ∃ s : SL23, (∀ g : SL23, g * s = s * g) ∧
      (b = s * (l * ⁅l, b⁆ * l⁻¹) ∨ b = s * (l⁻¹ * ⁅l⁻¹, b⁆ * l)) := by
  decide +kernel

theorem sl2_three_key' {Y : Type} [Group Y] {L : Subgroup Y} (h : HasSL2Model ↥L (fun r => r = 3)) :
    ∀ l ∈ L, (∀ g ∈ L, g * l ^ 3 = l ^ 3 * g) → ¬ (∀ g ∈ L, g * l = l * g) →
      ∀ b ∈ L, b ^ 8 = 1 → (∀ g ∈ L, g * b = b * g) ∨ ∃ s ∈ L, (∀ g ∈ L, g * s = s * g) ∧
        (b = s * (l * ⁅l, b⁆ * l⁻¹) ∨ b = s * (l⁻¹ * ⁅l⁻¹, b⁆ * l)) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : ↥L ≃* SL23 :=
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)
  intro l hl hl3 hlnc b hb hb8
  have hcen3 : ∀ g : SL23, g * (Φ ⟨l, hl⟩) ^ 3 = (Φ ⟨l, hl⟩) ^ 3 * g := by
    intro g
    obtain ⟨g', rfl⟩ := Φ.surjective g
    have h1 := hl3 g' g'.2
    have h2 : g' * (⟨l, hl⟩ : ↥L) ^ 3 = (⟨l, hl⟩ : ↥L) ^ 3 * g' := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
      exact h1
    have h3 := congrArg Φ h2
    rwa [map_mul, map_mul, map_pow] at h3
  have hnc : ¬ ∀ g : SL23, g * Φ ⟨l, hl⟩ = Φ ⟨l, hl⟩ * g := by
    intro hall
    apply hlnc
    intro g hg
    have h1 := hall (Φ ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥L) * ⟨l, hl⟩ = ⟨l, hl⟩ * ⟨g, hg⟩ :=
      Φ.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have hb8' : (Φ ⟨b, hb⟩) ^ 8 = 1 := by
    have : (⟨b, hb⟩ : ↥L) ^ 8 = 1 := Subtype.ext (by simpa using hb8)
    rw [← map_pow, this, map_one]
  rcases sl23_key3 (Φ ⟨l, hl⟩) (Φ ⟨b, hb⟩) hcen3 hnc hb8' with h1 | ⟨s, hs, hbs⟩
  · left
    intro g hg
    have := h1 (Φ ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥L) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨g, hg⟩ :=
      Φ.injective (by rw [map_mul, map_mul]; exact this)
    exact congrArg Subtype.val h2
  · right
    refine ⟨((Φ.symm s : ↥L) : Y), (Φ.symm s).2, ?_, ?_⟩
    · intro g hg
      have := hs (Φ ⟨g, hg⟩)
      have h2 : (⟨g, hg⟩ : ↥L) * Φ.symm s = Φ.symm s * ⟨g, hg⟩ :=
        Φ.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact this)
      exact congrArg Subtype.val h2
    · have key : ∀ (e₁ e₂ : ↥L) (u : SL23),
          Φ e₂ = u * (Φ e₁ * ⁅Φ e₁, Φ e₂⁆ * (Φ e₁)⁻¹) →
          (e₂ : Y) = ((Φ.symm u : ↥L) : Y) * ((e₁ : Y) * ⁅(e₁ : Y), (e₂ : Y)⁆ * (e₁ : Y)⁻¹) := by
        intro e₁ e₂ u hu
        have h2 : e₂ = Φ.symm u * (e₁ * ⁅e₁, e₂⁆ * e₁⁻¹) := by
          apply Φ.injective
          rw [map_mul, map_mul, map_mul, map_inv, map_commutatorElement, MulEquiv.apply_symm_apply]
          exact hu
        have := congrArg Subtype.val h2
        simpa [commutatorElement_def] using this
      have key' : ∀ (e₁ e₂ : ↥L) (u : SL23),
          Φ e₂ = u * ((Φ e₁)⁻¹ * ⁅(Φ e₁)⁻¹, Φ e₂⁆ * Φ e₁) →
          (e₂ : Y) = ((Φ.symm u : ↥L) : Y) * ((e₁ : Y)⁻¹ * ⁅(e₁ : Y)⁻¹, (e₂ : Y)⁆ * (e₁ : Y)) := by
        intro e₁ e₂ u hu
        have h2 : e₂ = Φ.symm u * (e₁⁻¹ * ⁅e₁⁻¹, e₂⁆ * e₁) := by
          apply Φ.injective
          rw [map_mul, map_mul, map_mul, map_inv, map_commutatorElement, map_inv,
            MulEquiv.apply_symm_apply]
          exact hu
        have := congrArg Subtype.val h2
        simpa [commutatorElement_def] using this
      rcases hbs with hbs | hbs
      · exact Or.inl (key ⟨l, hl⟩ ⟨b, hb⟩ s hbs)
      · exact Or.inr (key' ⟨l, hl⟩ ⟨b, hb⟩ s hbs)

theorem card_eq_of_hasSL2Model_three {Q : Type} [Group Q] (h : HasSL2Model Q (fun r => r = 3)) :
    Nat.card Q = 24 := by
  obtain ⟨F, hF, hFin, hq, ⟨eL⟩⟩ := h
  rw [Nat.card_congr (eL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).toEquiv,
    GorensteinWalter.sl2_card_formula F]
  have h2 : Nat.card F = 3 := hq
  rw [h2]
  norm_num

end SL23

section S4

theorem key_s4 : ∀ σ : Equiv.Perm (Fin 4), σ * σ = 1 → Equiv.Perm.sign σ = -1 →
    ∃ x : Equiv.Perm (Fin 4), ⁅x, σ⁆ ≠ 1 ∧ ⁅x, σ⁆ ^ 3 = 1 := by
  decide +kernel

theorem alternatingGroup_le_of_pow_three {A : Subgroup (Equiv.Perm (Fin 4))}
    (h : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 → σ ∈ A) : alternatingGroup (Fin 4) ≤ A := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine (Subgroup.closure_le A).2 fun σ hσ => h σ ?_
  have := hσ.orderOf
  rw [← this]
  exact pow_orderOf_eq_one σ

theorem mem_of_pow_three_of_index_two {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) {x : G}
    (hx : x ^ 3 = 1) : x ∈ H := by
  have h2 : x * x ∈ H := (Subgroup.mul_mem_iff_of_index_two hH).2 Iff.rfl
  have h3 : (x * x) * x ∈ H := by
    have : (x * x) * x = x ^ 3 := by rw [pow_succ, pow_two]
    rw [this, hx]
    exact H.one_mem
  exact ((Subgroup.mul_mem_iff_of_index_two hH).1 h3).1 h2

end S4

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem three_case_core {L SB : Subgroup Y} {y : Y}
    (hL : HasSL2Model ↥L (fun q => q = 3)) (hind : InducedPGL2 L SB 3) (hyS : y ∈ SB) (hy2 : y * y = 1)
    (hout : ¬ ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), y = a * c)
    {T : Subgroup Y} [hT : T.Normal]
    (hZT : ∀ b ∈ L, (∀ g ∈ L, g * b = b * g) → b ∈ T)
    (hodd : ∀ n ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆, Nat.Coprime (orderOf n) 2 → n ∈ T) :
    ∀ b ∈ L, b ^ 8 = 1 → b ∈ T := by
  obtain ⟨hn, F₀, hF₀, hFin₀, hcard₀, ⟨e⟩⟩ := hind
  have hF3 : Nat.card F₀ = 3 := hcard₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hcardF : Fintype.card F₀ = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF3, ZMod.card]
  let φ : F₀ ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcardF
  let ε : ↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB) ≃* Equiv.Perm (Fin 4) :=
    (e.trans (GorensteinWalter.pgl2RingEquiv φ)).trans GorensteinWalter.pgl2_three_equiv_perm
  let C' : Subgroup ↥(L ⊔ SB) := (centralizer (L : Set Y)).subgroupOf (L ⊔ SB)
  let Θ : ↥(L ⊔ SB) →* Equiv.Perm (Fin 4) := ε.toMonoidHom.comp (QuotientGroup.mk' C')
  have hΘs : Function.Surjective Θ := ε.surjective.comp (QuotientGroup.mk'_surjective C')
  have hΘone : ∀ m : ↥(L ⊔ SB), Θ m = 1 ↔ m ∈ C' := by
    intro m
    show ε (QuotientGroup.mk m) = 1 ↔ _
    rw [map_eq_one_iff ε ε.injective, QuotientGroup.eq_one_iff]
  have hΘeq : ∀ m m' : ↥(L ⊔ SB), Θ m = Θ m' ↔ m⁻¹ * m' ∈ C' := by
    intro m m'
    rw [← hΘone, map_mul, map_inv, inv_mul_eq_one]
  have hLM : L ≤ L ⊔ SB := le_sup_left
  have hyM : y ∈ L ⊔ SB := Subgroup.mem_sup_right hyS
  let y' : ↥(L ⊔ SB) := ⟨y, hyM⟩
  have hσ2 : Θ y' * Θ y' = 1 := by
    rw [← map_mul]
    have : y' * y' = 1 := Subtype.ext hy2
    rw [this, map_one]
  let g : ↥L →* Equiv.Perm (Fin 4) := Θ.comp (Subgroup.inclusion hLM)
  have hgone : ∀ a : ↥L, g a = 1 ↔ a ∈ center ↥L := by
    intro a
    show Θ (Subgroup.inclusion hLM a) = 1 ↔ _
    rw [hΘone, Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g'
      exact Subtype.ext (h g' g'.2)
    · intro h g' hg'
      exact congrArg Subtype.val (h ⟨g', hg'⟩)
  have hgker : g.ker = center ↥L := by
    ext a
    rw [MonoidHom.mem_ker]
    exact hgone a
  have hLcard : Nat.card ↥L = 24 := card_eq_of_hasSL2Model_three hL
  have hZ : Nat.card (center ↥L) = 2 := (sl2_model_center_inv ⟨1, rfl⟩ hL).1
  have hrange : Nat.card g.range = 12 := by
    have h1 := Subgroup.index_ker g
    have h2 := g.ker.index_mul_card
    rw [h1] at h2
    have h3 : Nat.card g.ker = 2 := by rw [hgker, hZ]
    rw [h3, hLcard] at h2
    omega
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hidx : g.range.index = 2 := by
    have := g.range.index_mul_card
    rw [hrange, hperm] at this
    omega
  have hA : alternatingGroup (Fin 4) ≤ g.range :=
    alternatingGroup_le_of_pow_three fun σ hσ => mem_of_pow_three_of_index_two hidx hσ
  have hodd_sign : Equiv.Perm.sign (Θ y') = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Θ y')) with h | h
    · exfalso
      have hmem : Θ y' ∈ g.range := hA ((Equiv.Perm.mem_alternatingGroup).2 h)
      obtain ⟨a, ha⟩ := hmem
      have h1 : (Subgroup.inclusion hLM a)⁻¹ * y' ∈ C' := (hΘeq _ _).1 ha
      apply hout
      refine ⟨a, a.2, (a : Y)⁻¹ * y, ?_, by group⟩
      simpa using Subgroup.mem_subgroupOf.mp h1
    · exact h
  obtain ⟨x, hx1, hx3⟩ := key_s4 (Θ y') hσ2 hodd_sign
  obtain ⟨m, hm⟩ := hΘs x
  obtain ⟨n₀', hn₀'⟩ : ∃ n₀' : ↥(L ⊔ SB), n₀' = ⁅m, y'⁆ := ⟨_, rfl⟩
  have hΘn₀ : Θ n₀' = ⁅x, Θ y'⁆ := by rw [hn₀', map_commutatorElement, hm]
  have hord3 : orderOf (⁅x, Θ y'⁆ : Equiv.Perm (Fin 4)) = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨a₂, m₂, hm₂, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n₀').ne' 2 (by norm_num)
  obtain ⟨n₁', hn₁'⟩ : ∃ n₁' : ↥(L ⊔ SB), n₁' = n₀' ^ (2 ^ a₂) := ⟨_, rfl⟩
  have hn₁ord : orderOf n₁' = m₂ := by
    rw [hn₁', orderOf_pow_of_dvd (pow_ne_zero a₂ (by norm_num)) (Dvd.intro _ hord.symm), hord,
      Nat.mul_div_cancel_left m₂ (pow_pos (by norm_num) a₂)]
  have hn₁cop : Nat.Coprime (orderOf n₁') 2 := by
    rw [hn₁ord]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm₂)
  have hΘn₁ : Θ n₁' = (⁅x, Θ y'⁆ : Equiv.Perm (Fin 4)) ^ (2 ^ a₂) := by
    rw [hn₁', map_pow, hΘn₀]
  have hρ₁3 : (Θ n₁') ^ 3 = 1 := by
    rw [hΘn₁, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hρ₁ne : Θ n₁' ≠ 1 := by
    rw [hΘn₁]
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord3] at h2
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  obtain ⟨l', hl'⟩ := mem_of_pow_three_of_index_two hidx hρ₁3
  have hcl' : (Subgroup.inclusion hLM l')⁻¹ * n₁' ∈ C' := (hΘeq _ _).1 hl'
  have hlL : (l' : Y) ∈ L := l'.2
  obtain ⟨l, hl⟩ : ∃ l : Y, l = (l' : Y) := ⟨_, rfl⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : Y, n₁ = (n₁' : Y) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Y, c = l⁻¹ * n₁ := ⟨_, rfl⟩
  have hlL' : l ∈ L := hl ▸ hlL
  have hcC : c ∈ centralizer (L : Set Y) := by
    have := Subgroup.mem_subgroupOf.mp hcl'
    rw [hcdef, hl, hn₁]
    simpa using this
  have hn₁lc : n₁ = l * c := by rw [hcdef]; group
  have hn₀N : ((n₀' : ↥(L ⊔ SB)) : Y) ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
    have : ((n₀' : ↥(L ⊔ SB)) : Y) = ⁅(m : Y), y⁆ := by
      rw [hn₀']
      simp [y', commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_zpowers y)
  have hn₁N : n₁ ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
    have : n₁ = ((n₀' : ↥(L ⊔ SB)) : Y) ^ (2 ^ a₂) := by
      rw [hn₁, hn₁']
      simp
    rw [this]
    exact Subgroup.pow_mem _ hn₀N _
  have hn₁T : n₁ ∈ T := by
    refine hodd n₁ hn₁N ?_
    rw [hn₁, Subgroup.orderOf_coe]
    exact hn₁cop
  have hgl : g l' = Θ n₁' := hl'
  have hl3 : ∀ g' ∈ L, g' * l ^ 3 = l ^ 3 * g' := by
    intro g' hg'
    have h1 : Θ ((Subgroup.inclusion hLM l') ^ 3) = 1 := by
      rw [map_pow]
      have h0 : Θ (Subgroup.inclusion hLM l') = Θ n₁' := hgl
      rw [h0]
      exact hρ₁3
    have h2 : (Subgroup.inclusion hLM l') ^ 3 ∈ C' := (hΘone _).1 h1
    have h3 : l ^ 3 ∈ centralizer (L : Set Y) := by
      rw [hl]
      simpa using Subgroup.mem_subgroupOf.mp h2
    exact Subgroup.mem_centralizer_iff.mp h3 g' hg'
  have hlnc : ¬ ∀ g' ∈ L, g' * l = l * g' := by
    intro hall
    have h1 : Subgroup.inclusion hLM l' ∈ C' := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_centralizer_iff.mpr (fun g' hg' => ?_)
      have h0 := hall g' hg'
      rw [hl] at h0
      exact h0
    have h2 := (hΘone _).2 h1
    apply hρ₁ne
    rw [← hgl]
    exact h2
  have hcomm : ∀ b ∈ L, ⁅b, l⁆ ∈ T := by
    intro b hb
    have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcC b hb
    have h1 : ⁅b, n₁⁆ = ⁅b, l⁆ := by
      rw [hn₁lc]
      exact commutator_mul_right_of_commute hbc
    have h2 : ⁅b, n₁⁆ ∈ T := by
      have : ⁅b, n₁⁆ = (b * n₁ * b⁻¹) * n₁⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact T.mul_mem (hT.conj_mem n₁ hn₁T b) (T.inv_mem hn₁T)
    rw [← h1]
    exact h2
  intro b hb hb8
  rcases sl2_three_key' hL l hlL' hl3 hlnc b hb hb8 with hcen | ⟨s, hsL, hscen, hbs⟩
  · exact hZT b hb hcen
  · have hsT : s ∈ T := hZT s hsL hscen
    have hlb : ⁅l, b⁆ ∈ T := by
      have : ⁅l, b⁆ = (⁅b, l⁆)⁻¹ := (commutatorElement_inv b l).symm
      rw [this]
      exact T.inv_mem (hcomm b hb)
    have hlb' : ⁅l⁻¹, b⁆ ∈ T := by
      have : ⁅l⁻¹, b⁆ = l⁻¹ * ⁅b, l⁆ * (l⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact hT.conj_mem _ (hcomm b hb) l⁻¹
    rcases hbs with hbs | hbs
    · rw [hbs]
      exact T.mul_mem hsT (hT.conj_mem _ hlb l)
    · rw [hbs]
      exact T.mul_mem hsT (by simpa using hT.conj_mem _ hlb' l⁻¹)

end Core

section Solvable

private theorem q3_mul : ∀ a b : SL23, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem q3_conj : ∀ g a : SL23, a ^ 4 = 1 → (g * a * g⁻¹) ^ 4 = 1 := by
  decide +kernel

private theorem q3_comm : ∀ a b : SL23, ((a * b)⁻¹ * (b * a)) ^ 4 = 1 := by
  decide +kernel

private def q3 : Subgroup SL23 where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => q3_mul a b ha hb
  inv_mem' := fun {a} ha => by
    have h : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, h, inv_one]

private instance q3_normal : q3.Normal := ⟨fun a ha g => q3_conj g a ha⟩

theorem isSolvable_sl23 : Group.IsSolvable SL23 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 q3 := fun x => ⟨2, by
    apply Subtype.ext
    have h : (x : SL23) ^ 4 = 1 := x.2
    simpa [Subgroup.coe_pow] using h⟩
  have := hp.isNilpotent
  have : Group.IsSolvable q3 := inferInstance
  have : IsMulCommutative (SL23 ⧸ q3) := ⟨⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact q3_comm x y⟩⟩
  exact Group.isSolvable_of_subgroup_quotient q3

theorem isSolvable_of_hasSL2Model_three' {Q : Type} [Group Q]
    (h : HasSL2Model Q (fun r => r = 3)) : Group.IsSolvable Q := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : Q ≃* SL23 :=
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)
  have := isSolvable_sl23
  exact Group.isSolvable_of_surjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective

theorem pow_eight_of_two_pow {X : Type*} [Group X] (hX : Nat.card X = 24) (w : X)
    (h : ∃ a : ℕ, w ^ (2 ^ a) = 1) : w ^ 8 = 1 := by
  obtain ⟨a, ha⟩ := h
  have h1 : orderOf w ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf w ∣ 24 := hX ▸ orderOf_dvd_natCard w
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj3 : j ≤ 3 := by
    by_contra hj4
    have : 2 ^ 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    rw [← hj] at this
    have := this.trans h2
    omega
  have : orderOf w ∣ 8 := by
    rw [hj]
    exact (Nat.pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp this

end Solvable

end CFSG.GH74.GLS.Stage2.Final.L26
