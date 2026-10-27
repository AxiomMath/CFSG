module

public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Components

variable {Q : Type*} [Group Q]

private theorem false_of_quasisimple_le_centralizer {L : Subgroup Q} (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : L ≤ Subgroup.centralizer (L : Set Q)) : False := by
  have h1 : commutator ↥L = ⊥ := by
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun a _ b _ => ?_)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have := (Subgroup.mem_centralizer_iff.1 (h a.2)) b b.2
    show ⁅(a : Q), (b : Q)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.2 this.symm
  have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥L)
  have hgt : g ∈ (⊤ : Subgroup ↥L) := trivial
  rw [← hq.1, h1] at hgt
  exact hg (Subgroup.mem_bot.1 hgt)

private theorem isSubnormal_top_of_normal {F : Subgroup Q} (hF : F.Normal) : IsSubnormal F ⊤ :=
  IsSubnormal.step le_top (hF.subgroupOf ⊤) (IsSubnormal.refl ⊤)

private theorem isSubnormal_sup₃ [Finite Q] {X₁ X₂ X₃ : Subgroup Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤) :
    IsSubnormal (X₁ ⊔ X₂ ⊔ X₃) ⊤ := by
  have hAE : X₁ ⊔ X₂ ⊔ X₃ ≤ CFSG.ComponentClassification.Layer.subgroup Q :=
    sup_le (sup_le (CFSG.ComponentClassification.Layer.component_le h₁)
      (CFSG.ComponentClassification.Layer.component_le h₂))
      (CFSG.ComponentClassification.Layer.component_le h₃)
  have hEN : CFSG.ComponentClassification.Layer.subgroup Q ≤
      Subgroup.normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q) := by
    refine sSup_le fun K hK => ?_
    by_cases hKX : K = X₁ ∨ K = X₂ ∨ K = X₃
    · have : K ≤ X₁ ⊔ X₂ ⊔ X₃ := by
        rcases hKX with h | h | h <;> rw [h]
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
        · exact le_sup_right
      exact this.trans Subgroup.le_normalizer
    · push Not at hKX
      obtain ⟨n1, n2, n3⟩ := hKX
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q))
      refine Subgroup.le_centralizer_iff.2 (sup_le (sup_le ?_ ?_) ?_)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₁ K h₁ hK (Ne.symm n1))
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₂ K h₂ hK (Ne.symm n2))
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₃ K h₃ hK (Ne.symm n3))
  have hEA : IsSubnormal (X₁ ⊔ X₂ ⊔ X₃) (CFSG.ComponentClassification.Layer.subgroup Q) :=
    IsSubnormal.step hAE ((Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEN)
      (IsSubnormal.refl _)
  exact isSubnormal_trans' hEA
    (isSubnormal_top_of_normal (CFSG.ComponentClassification.Layer.normal Q))

private theorem isComponentOf_of_le {K X : Subgroup Q} (hK : IsComponentOf K ⊤) (hKX : K ≤ X) :
    IsComponentOf K X :=
  ⟨hKX, isSubnormal_of_le_of_le hK.2.1 hKX le_top, hK.2.2⟩

theorem components_of_product [Finite Q] {X₁ X₂ X₃ : Subgroup Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (h12 : X₁ ≠ X₂) (h23 : X₂ ≠ X₃) (h31 : X₃ ≠ X₁) :
    GLALayer (X₁ ⊔ X₂ ⊔ X₃) = X₁ ⊔ X₂ ⊔ X₃ ∧
      ∀ L : Subgroup Q, IsComponentOf L (X₁ ⊔ X₂ ⊔ X₃) → L = X₁ ∨ L = X₂ ∨ L = X₃ := by
  have _ := And.intro h12 (And.intro h23 h31)
  have hX := isSubnormal_sup₃ h₁ h₂ h₃
  have c1 : IsComponentOf X₁ (X₁ ⊔ X₂ ⊔ X₃) := isComponentOf_of_le h₁ (le_sup_left.trans le_sup_left)
  have c2 : IsComponentOf X₂ (X₁ ⊔ X₂ ⊔ X₃) :=
    isComponentOf_of_le h₂ (le_sup_right.trans le_sup_left)
  have c3 : IsComponentOf X₃ (X₁ ⊔ X₂ ⊔ X₃) := isComponentOf_of_le h₃ le_sup_right
  refine ⟨le_antisymm (sSup_le fun K hK => hK.1)
    (sup_le (sup_le (le_sSup c1) (le_sSup c2)) (le_sSup c3)), fun L hL => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  have hLc : IsComponentOf L ⊤ := ⟨le_top, isSubnormal_trans' hL.2.1 hX, hL.2.2⟩
  have hXL : X₁ ⊔ X₂ ⊔ X₃ ≤ Subgroup.centralizer (L : Set Q) :=
    sup_le (sup_le
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₁ L h₁ hLc (Ne.symm n1)))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₂ L h₂ hLc (Ne.symm n2))))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₃ L h₃ hLc (Ne.symm n3)))
  exact false_of_quasisimple_le_centralizer hL.2.2 (hL.1.trans hXL)

private theorem gLBConj_sup (g : Q) (A B : Subgroup Q) :
    GLBConj g (A ⊔ B) = GLBConj g A ⊔ GLBConj g B :=
  Subgroup.map_sup _ _ _

private theorem mem_zpowers_cases {x e : Q} (hx3 : x ^ 3 = 1) (he : e ∈ Subgroup.zpowers x) :
    e = 1 ∨ e = x ∨ e = x * x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hn : x ^ n = x ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [hn, h]
  · left; simp
  · right; left; simp
  · right; right; rw [zpow_two]

theorem regular_of_cycle [Finite Q] {X₁ X₂ X₃ : Subgroup Q} {x : Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (h12 : X₁ ≠ X₂) (h23 : X₂ ≠ X₃) (h31 : X₃ ≠ X₁)
    (hx₁ : GLBConj x X₁ = X₂) (hx₂ : GLBConj x X₂ = X₃) (hx₃ : GLBConj x X₃ = X₁)
    (hx3 : x ^ 3 = 1) :
    (∀ L L' : Subgroup Q, IsComponentOf L (X₁ ⊔ X₂ ⊔ X₃) → IsComponentOf L' (X₁ ⊔ X₂ ⊔ X₃) →
        ∃ e ∈ Subgroup.zpowers x, GLBConj e L = L') ∧
    (∀ e ∈ Subgroup.zpowers x, e ≠ 1 → ∀ L : Subgroup Q,
        IsComponentOf L (X₁ ⊔ X₂ ⊔ X₃) → GLBConj e L ≠ L) ∧
    Subgroup.zpowers x ≤ Subgroup.normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q) ∧
    IsElemAbelian 3 (Subgroup.zpowers x) := by
  have hmem := (components_of_product h₁ h₂ h₃ h12 h23 h31).2
  have hxx₁ : GLBConj (x * x) X₁ = X₃ := by rw [← gLBConj_gLBConj, hx₁, hx₂]
  have hxx₂ : GLBConj (x * x) X₂ = X₁ := by rw [← gLBConj_gLBConj, hx₂, hx₃]
  have hxx₃ : GLBConj (x * x) X₃ = X₂ := by rw [← gLBConj_gLBConj, hx₃, hx₁]
  have hxz : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have hxxz : x * x ∈ Subgroup.zpowers x := mul_mem hxz hxz
  refine ⟨fun L L' hL hL' => ?_, fun e he hne L hL => ?_, ?_, ?_⟩
  · rcases hmem L hL with h | h | h <;> rcases hmem L' hL' with h' | h' | h' <;> rw [h, h']
    · exact ⟨1, one_mem _, gLBConj_one _⟩
    · exact ⟨x, hxz, hx₁⟩
    · exact ⟨x * x, hxxz, hxx₁⟩
    · exact ⟨x * x, hxxz, hxx₂⟩
    · exact ⟨1, one_mem _, gLBConj_one _⟩
    · exact ⟨x, hxz, hx₂⟩
    · exact ⟨x, hxz, hx₃⟩
    · exact ⟨x * x, hxxz, hxx₃⟩
    · exact ⟨1, one_mem _, gLBConj_one _⟩
  · rcases mem_zpowers_cases hx3 he with h | h | h
    · exact absurd h hne
    · rw [h]
      rcases hmem L hL with h' | h' | h' <;> rw [h']
      · rw [hx₁]; exact h12.symm
      · rw [hx₂]; exact h23.symm
      · rw [hx₃]; exact h31.symm
    · rw [h]
      rcases hmem L hL with h' | h' | h' <;> rw [h']
      · rw [hxx₁]; exact h31
      · rw [hxx₂]; exact h12
      · rw [hxx₃]; exact h23
  · refine Subgroup.zpowers_le.2 (mem_normalizer_iff_gLBConj_eq.2 ?_)
    rw [gLBConj_sup, gLBConj_sup, hx₁, hx₂, hx₃, sup_comm (X₂ ⊔ X₃) X₁, ← sup_assoc]
  · refine ⟨inferInstance, fun g hg => ?_⟩
    rcases mem_zpowers_cases hx3 hg with h | h | h
    · rw [h, one_pow]
    · rw [h, hx3]
    · have : (x * x) ^ 3 = (x ^ 3) ^ 2 := by
        rw [← pow_two, ← pow_mul, ← pow_mul]
      rw [h, this, hx3, one_pow]

private theorem commute_of_mem_gLBConj {x q : Q} {H : Subgroup Q} (hqx : q * x = x * q)
    (hq : ∀ y ∈ H, q * y = y * q) : ∀ y ∈ GLBConj x H, q * y = y * q := by
  intro y hy
  have h : Commute q (x * y * x⁻¹) := hq _ (mem_gLBConj.1 hy)
  have hqx' : Commute q x := hqx
  have h2 : Commute q (x⁻¹ * (x * y * x⁻¹) * x) := (hqx'.inv_right.mul_right h).mul_right hqx'
  have h3 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rw [h3] at h2
  exact h2

private theorem gLBConj_component_mem [Finite Q] {X₁ X₂ X₃ : Subgroup Q} {b : Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (h12 : X₁ ≠ X₂) (h23 : X₂ ≠ X₃) (h31 : X₃ ≠ X₁)
    (hb : b ∈ Subgroup.normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q))
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) (hKX : K ≤ X₁ ⊔ X₂ ⊔ X₃) :
    GLBConj b K = X₁ ∨ GLBConj b K = X₂ ∨ GLBConj b K = X₃ := by
  have hc := isComponentOf_gLBConj hK b
  have hle : GLBConj b K ≤ X₁ ⊔ X₂ ⊔ X₃ := by
    calc GLBConj b K ≤ GLBConj b (X₁ ⊔ X₂ ⊔ X₃) := gLBConj_mono b hKX
      _ = X₁ ⊔ X₂ ⊔ X₃ := gLBConj_eq_of_mem_normalizer hb
  exact (components_of_product h₁ h₂ h₃ h12 h23 h31).2 _ (isComponentOf_of_le hc hle)

theorem exists_centralizing_of_rank [Finite Q] {X₁ X₂ X₃ Bb : Subgroup Q} {x : Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (h12 : X₁ ≠ X₂) (h23 : X₂ ≠ X₃) (h31 : X₃ ≠ X₁)
    (hx₁ : GLBConj x X₁ = X₂) (hx₂ : GLBConj x X₂ = X₃) (hx₃ : GLBConj x X₃ = X₁)
    (hx3 : x ^ 3 = 1) (hBel : IsElemAbelian 3 Bb) (hBc : Nat.card Bb = 81) (hxB : x ∈ Bb)
    (hBn : Bb ≤ Subgroup.normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q))
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥X₁)) ≤ 2) :
    ∃ b ∈ Bb, b ≠ 1 ∧ b ∈ Subgroup.centralizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q) := by
  classical
  have _ := And.intro hx₃ hx3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c1 : X₁ ≤ X₁ ⊔ X₂ ⊔ X₃ := le_sup_left.trans le_sup_left
  let act : MulAction ↥Bb (Subgroup Q) :=
    { smul := fun b H => GLBConj (b : Q)⁻¹ H
      one_smul := fun H => by
        show GLBConj ((1 : ↥Bb) : Q)⁻¹ H = H
        rw [OneMemClass.coe_one, inv_one, gLBConj_one]
      mul_smul := fun b c H => by
        show GLBConj ((b * c : ↥Bb) : Q)⁻¹ H = GLBConj (b : Q)⁻¹ (GLBConj (c : Q)⁻¹ H)
        rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev] }
  have hsmul : ∀ (b : ↥Bb) (H : Subgroup Q), b • H = GLBConj (b : Q)⁻¹ H := fun _ _ => rfl
  have hmemS : ∀ b : ↥Bb, b ∈ MulAction.stabilizer ↥Bb X₁ →
      (b : Q) ∈ Subgroup.normalizer (X₁ : Set Q) := by
    intro b hb
    rw [MulAction.mem_stabilizer_iff, hsmul] at hb
    have := mem_normalizer_iff_gLBConj_eq.2 hb
    exact (Subgroup.inv_mem_iff _).1 this
  have horb : MulAction.orbit ↥Bb X₁ ⊆ {X₁, X₂, X₃} := by
    rintro _ ⟨b, rfl⟩
    show b • X₁ ∈ _
    rw [hsmul]
    have := gLBConj_component_mem h₁ h₂ h₃ h12 h23 h31 (hBn (Bb.inv_mem b.2)) h₁ c1
    simpa using this
  have hncard : (MulAction.orbit ↥Bb X₁).ncard ≤ 3 := by
    refine (Set.ncard_le_ncard horb (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    exact Nat.succ_le_succ (Set.ncard_singleton _).le
  have hidx : (MulAction.stabilizer ↥Bb X₁).index ≤ 3 := by
    rw [MulAction.index_stabilizer]; exact hncard
  have hcard27 : 27 ≤ Nat.card (MulAction.stabilizer ↥Bb X₁) := by
    have h := Subgroup.card_mul_index (MulAction.stabilizer ↥Bb X₁)
    rw [hBc] at h
    generalize (MulAction.stabilizer ↥Bb X₁).index = i at h hidx
    generalize Nat.card (MulAction.stabilizer ↥Bb X₁) = n at h ⊢
    interval_cases i <;> omega
  set Stab := MulAction.stabilizer ↥Bb X₁ with hStab
  let φ : ↥Stab →* ↥(Subgroup.normalizer (X₁ : Set Q)) :=
    MonoidHom.codRestrict ((Bb.subtype).comp Stab.subtype) (Subgroup.normalizer (X₁ : Set Q))
      (fun b => hmemS b.1 b.2)
  let ψ : ↥Stab →* MulAut ↥X₁ := X₁.normalizerMonoidHom.comp φ
  have hψ : ∀ (b : ↥Stab) (y : ↥X₁),
      ((ψ b y : ↥X₁) : Q) = ((b : ↥Bb) : Q) * y * ((b : ↥Bb) : Q)⁻¹ := fun _ _ => rfl
  have hker : ∃ b : ↥Stab, b ≠ 1 ∧ ψ b = 1 := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective ψ :=
      (injective_iff_map_eq_one ψ).2 fun b hb => by_contra fun hb1 => hno b hb1 hb
    have hBcomm : ∀ a b : ↥Bb, a * b = b * a :=
      fun a b => Subtype.ext (elemAbelian_comm hBel a.2 b.2)
    have hcomm : ∀ a b : ↥Stab, ψ a * ψ b = ψ b * ψ a := fun a b => by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hBcomm a.1 b.1))
    have hexp : ∀ a : ↥Stab, ψ a ^ 3 = 1 := fun a => by
      have : a ^ 3 = 1 := Subtype.ext (Subtype.ext (hBel.2 _ a.1.2))
      rw [← map_pow, this, map_one]
    have hRel : IsElemAbelian 3 ψ.range := by
      refine ⟨⟨⟨fun r s => ?_⟩⟩, fun r hr => ?_⟩
      · obtain ⟨a, ha⟩ := r.2
        obtain ⟨b, hb⟩ := s.2
        apply Subtype.ext
        show (r : MulAut ↥X₁) * s = s * r
        rw [← ha, ← hb]
        exact hcomm a b
      · obtain ⟨a, rfl⟩ := hr
        exact hexp a
    have hpg : IsPGroup 3 ψ.range := fun g =>
      ⟨1, Subtype.ext (by simpa using hRel.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := exists_card_eq_pow hpg
    have hk2 : k ≤ 2 := by
      refine le_trans ?_ hrank
      refine le_csSup ?_ ⟨ψ.range, le_top, hRel, hk⟩
      refine ⟨Nat.card (MulAut ↥X₁), ?_⟩
      rintro j ⟨E, -, -, hE⟩
      calc j ≤ 3 ^ j := (Nat.lt_pow_self (by norm_num)).le
        _ = Nat.card E := hE.symm
        _ ≤ Nat.card (MulAut ↥X₁) := Subgroup.card_le_card_group E
    have h9 : Nat.card ψ.range ≤ 9 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 9 := by norm_num
    have hle : Nat.card Stab ≤ Nat.card ψ.range :=
      Nat.card_le_card_of_injective ψ.rangeRestrict (MonoidHom.rangeRestrict_injective_iff.2 hinj)
    omega
  obtain ⟨b, hb1, hψb⟩ := hker
  have hbB : ((b : ↥Bb) : Q) ∈ Bb := (b : ↥Bb).2
  set q : Q := ((b : ↥Bb) : Q) with hq
  refine ⟨q, hbB, ?_, ?_⟩
  · intro h
    exact hb1 (Subtype.ext (Subtype.ext h))
  · have hq1 : ∀ y ∈ X₁, q * y = y * q := by
      intro y hy
      have h2 : ((ψ b ⟨y, hy⟩ : ↥X₁) : Q) = y := by rw [hψb]; rfl
      rw [hψ] at h2
      calc q * y = (q * y * q⁻¹) * q := by group
        _ = y * q := by rw [h2]
    have hqx : q * x = x * q := elemAbelian_comm hBel hbB hxB
    have hq2 : ∀ y ∈ X₂, q * y = y * q := by
      rw [← hx₁]; exact commute_of_mem_gLBConj hqx hq1
    have hq3 : ∀ y ∈ X₃, q * y = y * q := by
      rw [← hx₂]; exact commute_of_mem_gLBConj hqx hq2
    have hle : X₁ ⊔ X₂ ⊔ X₃ ≤ Subgroup.centralizer ({q} : Set Q) :=
      sup_le (sup_le
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hq1 y hy).symm)
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hq2 y hy).symm))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hq3 y hy).symm)
    exact Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

private theorem sup₃_le_normalizer [Finite Q] {X₁ X₂ X₃ Y : Subgroup Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (hY : IsComponentOf Y ⊤) : X₁ ⊔ X₂ ⊔ X₃ ≤ Subgroup.normalizer (Y : Set Q) := by
  have key : ∀ {Z : Subgroup Q}, IsComponentOf Z ⊤ → Z ≤ Subgroup.normalizer (Y : Set Q) := by
    intro Z hZ
    by_cases hZY : Z = Y
    · rw [hZY]; exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne Z Y hZ hY hZY)).trans
        (Subgroup.centralizer_le_normalizer _)
  exact sup_le (sup_le (key h₁) (key h₂)) (key h₃)

private theorem central_of_commutes [Finite Q] {X₁ X₂ X₃ Y : Subgroup Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (hY : IsComponentOf Y ⊤) {w : Q} (hwY : ∀ y ∈ Y, y * w = w * y) (hw : w ∈ Y) :
    ∀ g ∈ X₁ ⊔ X₂ ⊔ X₃, g * w = w * g := by
  have key : ∀ {Z : Subgroup Q}, IsComponentOf Z ⊤ → Z ≤ Subgroup.centralizer ({w} : Set Q) := by
    intro Z hZ
    by_cases hZY : Z = Y
    · rw [hZY]
      exact fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hwY y hy)
    · have h := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne Z Y hZ hY hZY)
      exact fun z hz => Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 (h hz)) w hw).symm
  have hle := sup_le (sup_le (key h₁) (key h₂)) (key h₃)
  exact fun g hg => Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

private theorem le_centralizer_of_perfect {Y I M : Subgroup Q} (hq : CFSG.Open.IsQuasisimple ↥Y)
    (hYI : Y ≤ I) (hIN : I ≤ Subgroup.normalizer (Y : Set Q)) (hMI : M ≤ I)
    (hMn : (M.subgroupOf I).Normal) (hMperf : ⁅M, M⁆ = M)
    (hZ : ∀ w ∈ Y, (∀ y ∈ Y, y * w = w * y) → ∀ g ∈ I, g * w = w * g) (hYM : ¬ Y ≤ M) :
    M ≤ Subgroup.centralizer (Y : Set Q) := by
  have hMconj : ∀ g ∈ I, ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun g hg m hm =>
    hMn.conj_mem ⟨m, hMI hm⟩ hm ⟨g, hg⟩
  have hN : ((M ⊓ Y).subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Q) ∈ M ⊓ Y := hn
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact hMconj _ (hYI g.2) _ hn'.1
    · exact Y.mul_mem (Y.mul_mem g.2 n.2) (Y.inv_mem g.2)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    ((M ⊓ Y).subgroupOf Y) with hc | ht
  · have hcent : ∀ w ∈ M ⊓ Y, ∀ g ∈ I, g * w = w * g := fun w hw g hg =>
      hZ w hw.2 (fun y hy => by
        have := Subgroup.mem_center_iff.1
          (hc (show (⟨w, hw.2⟩ : ↥Y) ∈ (M ⊓ Y).subgroupOf Y from hw)) ⟨y, hy⟩
        exact congrArg Subtype.val this) g hg
    have hcomm_le : ⁅M, Y⁆ ≤ M ⊓ Y := by
      refine Subgroup.commutator_le.2 fun m hm y hy => ⟨?_, ?_⟩
      · have : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by
          rw [commutatorElement_def]; group
        rw [this]
        exact M.mul_mem hm (hMconj y (hYI hy) m⁻¹ (M.inv_mem hm))
      · rw [commutatorElement_def]
        exact Y.mul_mem ((Subgroup.mem_normalizer_iff.1 (hIN (hMI hm)) y).1 hy) (Y.inv_mem hy)
    have h1 : ⁅⁅M, Y⁆, M⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun m hm => hcent z (hcomm_le hz) m (hMI hm)
    have h2 : ⁅⁅Y, M⁆, M⁆ = ⊥ := by rw [Subgroup.commutator_comm Y M]; exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := M) (H₂ := M) (H₃ := Y) h1 h2
    rw [hMperf] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  · exfalso
    apply hYM
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ (M ⊓ Y).subgroupOf Y := ht ▸ trivial
    exact (Subgroup.mem_subgroupOf.1 this).1

private theorem not_le_of_gLBConj_ne {Y Y' M : Subgroup Q} {x : Q} (hxY : GLBConj x Y = Y')
    (hne : Y' ≠ Y) (hMx : M ≤ Subgroup.centralizer ({x} : Set Q)) : ¬ Y ≤ M := by
  intro h
  have hx : x ∈ Subgroup.centralizer (Y : Set Q) :=
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.1 (hMx (h hy))
  have := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.centralizer_le_normalizer _ hx)
  exact hne (hxY.symm.trans this)

theorem false_of_normal_perfect_cycled [Finite Q]
    {X₁ X₂ X₃ M : Subgroup Q} {x : Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤)
    (h12 : X₁ ≠ X₂) (h23 : X₂ ≠ X₃) (h31 : X₃ ≠ X₁)
    (hx₁ : GLBConj x X₁ = X₂) (hx₂ : GLBConj x X₂ = X₃) (hx₃ : GLBConj x X₃ = X₁)
    (hMI : M ≤ X₁ ⊔ X₂ ⊔ X₃) (hMn : (M.subgroupOf (X₁ ⊔ X₂ ⊔ X₃)).Normal)
    (hMx : M ≤ Subgroup.centralizer ({x} : Set Q)) (hMperf : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) :
    False := by
  have P1 := le_centralizer_of_perfect h₁.2.2 (le_sup_left.trans le_sup_left)
    (sup₃_le_normalizer h₁ h₂ h₃ h₁) hMI hMn hMperf
    (fun w hw hwY => central_of_commutes h₁ h₂ h₃ h₁ hwY hw)
    (not_le_of_gLBConj_ne hx₁ h12.symm hMx)
  have P2 := le_centralizer_of_perfect h₂.2.2 (le_sup_right.trans le_sup_left)
    (sup₃_le_normalizer h₁ h₂ h₃ h₂) hMI hMn hMperf
    (fun w hw hwY => central_of_commutes h₁ h₂ h₃ h₂ hwY hw)
    (not_le_of_gLBConj_ne hx₂ h23.symm hMx)
  have P3 := le_centralizer_of_perfect h₃.2.2 le_sup_right
    (sup₃_le_normalizer h₁ h₂ h₃ h₃) hMI hMn hMperf
    (fun w hw hwY => central_of_commutes h₁ h₂ h₃ h₃ hwY hw)
    (not_le_of_gLBConj_ne hx₃ h31.symm hMx)
  have hI : X₁ ⊔ X₂ ⊔ X₃ ≤ Subgroup.centralizer (M : Set Q) :=
    sup_le (sup_le (Subgroup.le_centralizer_iff.1 P1) (Subgroup.le_centralizer_iff.1 P2))
      (Subgroup.le_centralizer_iff.1 P3)
  have hbot : ⁅M, M⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hMI.trans hI)
  exact hM1 (hMperf ▸ hbot)

end Components

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
