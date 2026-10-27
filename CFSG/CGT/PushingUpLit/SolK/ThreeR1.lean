module

public import CFSG.CGT.PushingUpLit.SolK.ThreeBlock
public import CFSG.CGT.PushingUpLit.SolK.ThreeSuzuki
public import CFSG.CGT.PushingUpLit.SolK.QStruct

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_pCore_of_rOf_bot (hchar : IsCharTwoType G) {M X : Subgroup G}
    (hMloc : IsTwoLocal M) (hXn : XNorm M X) {a : G} (haX : a ∈ X) (ha3 : a ^ 3 = 1)
    (hdec : ∀ x ∈ X, ∃ y ∈ pCoreOf 2 X, ∃ j : ℕ, x = y * a ^ j)
    (hab : ∀ y ∈ pCoreOf 2 X, ∀ y' ∈ pCoreOf 2 X, y * y' = y' * y)
    (hcard : Nat.card ↥(pCoreOf 2 X) = 4)
    (hfix : ∀ y ∈ pCoreOf 2 X, a * y * a⁻¹ = y → y = 1) (hR : rOf M X = ⊥) :
    ∀ k ∈ M, (∀ w ∈ pCoreOf 2 X, k * w * k⁻¹ = w) → k ∈ pCoreOf 2 X := by
  classical
  intro k hkM hkW
  set W : Subgroup G := pCoreOf 2 X with hW
  have hWX : W ≤ X := pCoreOf_le_self X
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : W = ⊥ := (Subgroup.eq_bot_iff_forall W).2 hcon
    rw [this, Subgroup.card_bot] at hcard
    omega
  have haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun w hw => pCoreOf_normalized X haX hw
  have haW' : ∀ w ∈ W, a⁻¹ * w * a ∈ W := fun w hw => by
    have := pCoreOf_normalized X (X.inv_mem haX) hw
    simpa using this
  set z : G := k * a * k⁻¹ * a⁻¹ with hz
  have hzX : z ∈ X := X.mul_mem (hXn.normal k hkM a haX) (X.inv_mem haX)
  have hzW : ∀ w ∈ W, z * w * z⁻¹ = w := by
    intro w hw
    have hw' : a⁻¹ * w * a ∈ W := haW' w hw
    have h1 : k * (a⁻¹ * w * a) * k⁻¹ = a⁻¹ * w * a := hkW _ hw'
    have h2 : k⁻¹ * (a⁻¹ * w * a) * k = a⁻¹ * w * a := by
      calc k⁻¹ * (a⁻¹ * w * a) * k = k⁻¹ * (k * (a⁻¹ * w * a) * k⁻¹) * k := by rw [h1]
        _ = a⁻¹ * w * a := by group
    calc z * w * z⁻¹ = k * a * (k⁻¹ * (a⁻¹ * w * a) * k) * a⁻¹ * k⁻¹ := by rw [hz]; group
      _ = k * a * (a⁻¹ * w * a) * a⁻¹ * k⁻¹ := by rw [h2]
      _ = k * w * k⁻¹ := by group
      _ = w := hkW w hw
  have hzWmem : z ∈ W := by
    obtain ⟨y, hy, j, hyj⟩ := hdec z hzX
    have hajW : ∀ w ∈ W, a ^ j * w * (a ^ j)⁻¹ = w := by
      intro w hw
      have hconj : ∀ i : ℕ, ∀ v ∈ W, a ^ i * v * (a ^ i)⁻¹ ∈ W := by
        intro i
        induction i with
        | zero => intro v hv; simpa using hv
        | succ i ih =>
          intro v hv
          have h1 := haW _ (ih v hv)
          have e : a ^ (i + 1) * v * (a ^ (i + 1))⁻¹ = a * (a ^ i * v * (a ^ i)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
          rw [e]
          exact h1
      have hyc : y * (a ^ j * w * (a ^ j)⁻¹) * y⁻¹ = a ^ j * w * (a ^ j)⁻¹ := by
        have := hab y hy _ (hconj j w hw)
        rw [this]
        group
      calc a ^ j * w * (a ^ j)⁻¹ = y * (a ^ j * w * (a ^ j)⁻¹) * y⁻¹ := hyc.symm
        _ = (y * a ^ j) * w * (y * a ^ j)⁻¹ := by group
        _ = z * w * z⁻¹ := by rw [← hyj]
        _ = w := hzW w hw
    have hj : j % 3 = 0 := by
      by_contra hne
      have hj12 : j % 3 = 1 ∨ j % 3 = 2 := by omega
      have haj : a ^ j = a ^ (j % 3) := by
        conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, ha3, one_pow, one_mul]
      rcases hj12 with h | h
      · rw [haj, h, pow_one] at hajW
        exact hw₀1 (hfix w₀ hw₀ (hajW w₀ hw₀))
      · rw [haj, h] at hajW
        apply hw₀1
        apply hfix w₀ hw₀
        have h2 := hajW w₀ hw₀
        have ha2 : a ^ 2 = a⁻¹ := by
          calc a ^ 2 = a ^ 3 * a⁻¹ := by group
            _ = a⁻¹ := by rw [ha3, one_mul]
        rw [ha2, inv_inv] at h2
        calc a * w₀ * a⁻¹ = a * (a⁻¹ * w₀ * a) * a⁻¹ := by
              rw [h2]
          _ = w₀ := by group
    have haj0 : a ^ j = 1 := by
      have : a ^ j = a ^ (j % 3) := by
        conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, ha3, one_pow, one_mul]
      rw [this, hj, pow_zero]
    rw [hyj, haj0, mul_one]
    exact hy
  let h : ↥W → ↥W := fun w => ⟨(w : G) * a * (w : G)⁻¹ * a⁻¹, by
    have : (w : G) * a * (w : G)⁻¹ * a⁻¹ = (w : G) * (a * (w : G)⁻¹ * a⁻¹) := by group
    rw [this]
    exact W.mul_mem w.2 (haW _ (W.inv_mem w.2))⟩
  have hinj : Function.Injective h := by
    intro w₁ w₂ hw
    have hw' : (w₁ : G) * a * (w₁ : G)⁻¹ * a⁻¹ = (w₂ : G) * a * (w₂ : G)⁻¹ * a⁻¹ :=
      congrArg Subtype.val hw
    have h1 : (w₁ : G) * a * (w₁ : G)⁻¹ = (w₂ : G) * a * (w₂ : G)⁻¹ := mul_right_cancel hw'
    have hva : (w₂ : G)⁻¹ * (w₁ : G) * a * ((w₂ : G)⁻¹ * (w₁ : G))⁻¹ = a := by
      calc (w₂ : G)⁻¹ * (w₁ : G) * a * ((w₂ : G)⁻¹ * (w₁ : G))⁻¹
          = (w₂ : G)⁻¹ * ((w₁ : G) * a * (w₁ : G)⁻¹) * (w₂ : G) := by group
        _ = a := by rw [h1]; group
    have hcomm : (w₂ : G)⁻¹ * (w₁ : G) * a = a * ((w₂ : G)⁻¹ * (w₁ : G)) :=
      mul_inv_eq_iff_eq_mul.1 hva
    have hc : a * ((w₂ : G)⁻¹ * (w₁ : G)) * a⁻¹ = (w₂ : G)⁻¹ * (w₁ : G) := by
      rw [← hcomm]
      group
    have hmem : (w₂ : G)⁻¹ * (w₁ : G) ∈ W := W.mul_mem (W.inv_mem w₂.2) w₁.2
    have h1' := hfix _ hmem hc
    exact Subtype.ext (by
      calc (w₁ : G) = (w₂ : G) * ((w₂ : G)⁻¹ * (w₁ : G)) := by group
        _ = (w₂ : G) := by rw [h1', mul_one])
  have hsurj : Function.Surjective h := Finite.injective_iff_surjective.1 hinj
  obtain ⟨w', hw'⟩ := hsurj ⟨z, hzWmem⟩
  have hw'z : (w' : G) * a * (w' : G)⁻¹ * a⁻¹ = z := congrArg Subtype.val hw'
  have hw'W : (w' : G) ∈ W := w'.2
  set k' : G := (w' : G)⁻¹ * k with hk'
  have hk'M : k' ∈ M := M.mul_mem (M.inv_mem (hXn.le (hWX hw'W))) hkM
  have hk'a : k' * a * k'⁻¹ = a := by
    have e : k * a * k⁻¹ = z * a := by rw [hz]; group
    have e2 : z * a = (w' : G) * a * (w' : G)⁻¹ := by
      rw [← hw'z]
      group
    calc k' * a * k'⁻¹ = (w' : G)⁻¹ * (k * a * k⁻¹) * (w' : G) := by rw [hk']; group
      _ = (w' : G)⁻¹ * ((w' : G) * a * (w' : G)⁻¹) * (w' : G) := by rw [e, e2]
      _ = a := by group
  have hk'W : ∀ w ∈ W, k' * w * k'⁻¹ = w := by
    intro w hw
    calc k' * w * k'⁻¹ = (w' : G)⁻¹ * (k * w * k⁻¹) * (w' : G) := by rw [hk']; group
      _ = (w' : G)⁻¹ * w * (w' : G) := by rw [hkW w hw]
      _ = w := by
        have := hab _ (W.inv_mem hw'W) w hw
        rw [this]
        group
  have hk'X : ∀ x ∈ X, k' * x * k'⁻¹ = x := by
    intro x hx
    obtain ⟨y, hy, j, rfl⟩ := hdec x hx
    calc k' * (y * a ^ j) * k'⁻¹ = (k' * y * k'⁻¹) * (k' * a * k'⁻¹) ^ j := by
          rw [conj_pow]
          group
      _ = y * a ^ j := by rw [hk'W y hy, hk'a]
  have hk'C : k' ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (comm_of_conj_eq (hk'X x hx)).symm
  have hCnorm : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer (X : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : m⁻¹ * x * m ∈ X := by
      have := hXn.normal m⁻¹ (M.inv_mem hm) x hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * x := by group
  have hcentQ : ∀ q ∈ pCoreOf 2 M, k' * q * k'⁻¹ = q := by
    intro q hq
    have hqM : q ∈ M := pCoreOf_le_self M hq
    have h1 : k' * q * k'⁻¹ * q⁻¹ ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).mul_mem (pCoreOf_normalized M hk'M hq) ((pCoreOf 2 M).inv_mem hq)
    have h2 : k' * q * k'⁻¹ * q⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
      have : k' * q * k'⁻¹ * q⁻¹ = k' * (q * k'⁻¹ * q⁻¹) := by group
      rw [this]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hk'C
        (hCnorm q hqM _ ((Subgroup.centralizer (X : Set G)).inv_mem hk'C))
    have h3 : k' * q * k'⁻¹ * q⁻¹ ∈ rOf M X := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hR, Subgroup.mem_bot] at h3
    calc k' * q * k'⁻¹ = (k' * q * k'⁻¹ * q⁻¹) * q := by group
      _ = q := by rw [h3, one_mul]
  have hk'Q : k' ∈ pCoreOf 2 M := by
    refine hchar M hMloc (Subgroup.mem_inf.2 ⟨hk'M, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (comm_of_conj_eq (hcentQ q hq)).symm
  have hk'R : k' ∈ rOf M X := Subgroup.mem_inf.2 ⟨hk'Q, hk'C⟩
  rw [hR, Subgroup.mem_bot] at hk'R
  have hkw : k = (w' : G) := by
    calc k = (w' : G) * ((w' : G)⁻¹ * k) := by group
      _ = (w' : G) := by rw [← hk', hk'R, mul_one]
  rw [hkw]
  exact hw'W

theorem sectionalTwoRankLE_four_of_three_rOf_bot (hchar : IsCharTwoType G) {M X : Subgroup G}
    (hMmax : CFSG.IsMaximalTwoLocal M) (hXM : X ≤ M) (hnorm : (X.subgroupOf M).Normal)
    (hshort : IsShortGroup ↥X) (hnat : IsNaturalAltModule ↥X 1)
    (huniq : CFSG.maximalTwoLocalsContaining (X : Set G) = {M}) (hR : rOf M X = ⊥) :
    CFSG.GH74.SectionalTwoRankLE G 4 := by
  classical
  have hXn : XNorm M X := ⟨hXM, fun m hm x hx => by
    have h1 := hnorm.conj_mem ⟨x, hXM hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.1 h1⟩
  obtain ⟨a, haX, ha3, hdec, hab, hsq, hcard, hfix⟩ := three_block_ambient hshort hnat
  have hMloc : IsTwoLocal M := hMmax.1
  have hB2 := centralizer_le_pCore_of_rOf_bot hchar hMloc hXn haX ha3 hdec hab hcard hfix hR
  have hW2 : IsPGroup 2 (pCoreOf 2 X) := isPGroup_pCoreOf' X
  have hWne : pCoreOf 2 X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hNM : Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) ≤ M := by
    refine local_le_of_unique huniq ⟨pCoreOf 2 X, hWne, hW2, rfl⟩ ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact pCoreOf_normalized X hx hw
    · intro hw
      have h1 := pCoreOf_normalized X (X.inv_mem hx) hw
      have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
      rw [e] at h1
      exact h1
  obtain ⟨S, hWS⟩ := hW2.exists_le_sylow
  have hCW : ∀ g ∈ (S : Subgroup G), g ∈ Subgroup.normalizer ((pCoreOf 2 X : Subgroup G) : Set G) →
      (∀ w ∈ pCoreOf 2 X, g * w * g⁻¹ = w) → g ∈ pCoreOf 2 X :=
    fun g _ hgN hgc => hB2 g (hNM hgN) hgc
  exact sectionalTwoRankLE_of_sylow S
    (sectionalTwoRankLE_four_of_selfCentralizing_four S.isPGroup' hWS hcard hsq hCW)

end CFSG.CGT.PushingUpLit.SolK
