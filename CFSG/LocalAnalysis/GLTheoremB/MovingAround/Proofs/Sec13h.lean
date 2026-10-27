module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec13h

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

@[expose] def IsMaxEA {G : Type} [Group G] (p : ℕ) (Y E : Subgroup G) : Prop :=
  E ≤ Y ∧ IsElemAbelian p E ∧
    ∀ F : Subgroup G, F ≤ Y → IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E

@[expose] def InputSylowCentIstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) (h : Sec13 G m p B M E A D T),
    ∃ P : Subgroup G, P ≤ Istar p M D ∧ IsPGroup p ↥P ∧
      Nat.card ↥P = p ^ (Nat.card ↥(Istar p M D)).factorization p ∧
      ∀ x ∈ P, ∀ g ∈ gammaStar p D, x * g * x⁻¹ * g⁻¹ ∈ pCoreOf 2 M

@[expose] def InputConjIstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) (h : Sec13 G m p B M E A D T)
    (E₁ E₂ : Subgroup G), IsMaxEA p (Istar p M D) E₁ → IsMaxEA p (Istar p M D) E₂ →
      ∃ g ∈ Istar p M D, GLBConj g E₁ = E₂

@[expose] def InputANormGamma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) (h : Sec13 G m p B M E A D T),
    A ≤ Subgroup.normalizer (gammaStar p D : Set G)

section Helpers

variable {G : Type} [Group G]

theorem isPGroup_of_isElemAbelian' {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p ↥E := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using hE.2 x.1 x.2)

theorem card_eq_pow_of_dvd [Finite G] {p : ℕ} [hp : Fact p.Prime] {Y S : Subgroup G}
    (hS : IsPGroup p ↥S) (hSY : S ≤ Y)
    (hdvd : p ^ (Nat.card ↥Y).factorization p ∣ Nat.card ↥S) :
    Nat.card ↥S = p ^ (Nat.card ↥Y).factorization p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  have hY0 : Nat.card ↥Y ≠ 0 := Nat.card_pos.ne'
  have hkY : p ^ k ∣ Nat.card ↥Y := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hSY
  have hk' : k ≤ (Nat.card ↥Y).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out hY0).1 hkY
  have hv : (Nat.card ↥Y).factorization p ≤ k := by
    rw [hk] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd
  rw [hk]
  congr 1
  omega

theorem exists_max_ea [Finite G] (p : ℕ) (Y : Subgroup G) :
    ∃ E : Subgroup G, E ≤ Y ∧ IsElemAbelian p E ∧
      ∀ F : Subgroup G, F ≤ Y → IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E := by
  let s : Set ℕ := {k | ∃ F : Subgroup G, F ≤ Y ∧ IsElemAbelian p F ∧ Nat.card ↥F = k}
  have hbdd : BddAbove s := by
    refine ⟨Nat.card ↥Y, ?_⟩
    rintro k ⟨F, hFY, -, rfl⟩
    exact Subgroup.card_le_of_le hFY
  have hbot : IsElemAbelian p (⊥ : Subgroup G) := by
    refine ⟨?_, fun x hx => ?_⟩
    · infer_instance
    · rw [Subgroup.mem_bot.1 hx, one_pow]
  have hne : s.Nonempty := ⟨Nat.card ↥(⊥ : Subgroup G), ⊥, bot_le, hbot, rfl⟩
  obtain ⟨E, hEY, hEea, hEc⟩ : ∃ E : Subgroup G, E ≤ Y ∧ IsElemAbelian p E ∧
      Nat.card ↥E = sSup s := by
    obtain ⟨F, hF, hFea, hFc⟩ := Nat.sSup_mem hne hbdd
    exact ⟨F, hF, hFea, hFc⟩
  refine ⟨E, hEY, hEea, fun F hFY hFea => ?_⟩
  rw [hEc]
  exact le_csSup hbdd ⟨F, hFY, hFea, rfl⟩

theorem card_inf_normal_ge {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (N Q : Subgroup Y) [N.Normal] (hQc : Nat.card ↥Q = p ^ (Nat.card Y).factorization p) :
    p ^ (Nat.card ↥N).factorization p ∣ Nat.card ↥(Q ⊓ N) := by
  have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hI0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : N.relIndex Q * Nat.card ↥(N ⊓ Q) = Nat.card ↥Q := Subgroup.relIndex_mul_card N Q
  have h2 : N.relIndex Q ∣ N.index := by
    have e1 : N.relIndex (N ⊔ Q) = N.relIndex Q := Subgroup.relIndex_sup_left Q N
    have e2 : N.relIndex (N ⊔ Q) * (N ⊔ Q).index = N.index :=
      Subgroup.relIndex_mul_index le_sup_left
    rw [← e1]
    exact Dvd.intro _ e2
  have h3 : Nat.card Y = Nat.card ↥N * N.index := (Subgroup.card_mul_index N).symm
  have hv : (Nat.card Y).factorization p =
      (Nat.card ↥N).factorization p + N.index.factorization p := by
    rw [h3, Nat.factorization_mul hN0 hI0]
    rfl
  have hr : N.relIndex Q ∣ p ^ (Nat.card Y).factorization p := by
    rw [← hQc]
    exact Dvd.intro _ h1
  obtain ⟨a, -, hra⟩ := (Nat.dvd_prime_pow hp.out).1 hr
  have ha : p ^ a ∣ N.index := hra ▸ h2
  have hw : a ≤ N.index.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out hI0).1 ha
  have key : p ^ a * Nat.card ↥(N ⊓ Q) =
      p ^ ((Nat.card ↥N).factorization p + N.index.factorization p) := by
    rw [← hra, h1, hQc, hv]
  have hX : Nat.card ↥(N ⊓ Q) =
      p ^ ((Nat.card ↥N).factorization p + (N.index.factorization p - a)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos a)
    rw [key, show (Nat.card ↥N).factorization p + N.index.factorization p =
      a + ((Nat.card ↥N).factorization p + (N.index.factorization p - a)) by omega, pow_add]
  rw [inf_comm, hX]
  exact pow_dvd_pow p (Nat.le_add_right _ _)

theorem sylow_card_dvd_of_normal {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (N X : Subgroup Y) [N.Normal] (hX : IsPGroup p ↥X) :
    ∃ Q : Subgroup Y, X ≤ Q ∧ IsPGroup p ↥Q ∧
      p ^ (Nat.card ↥N).factorization p ∣ Nat.card ↥(Q ⊓ N) := by
  obtain ⟨Qs, hXQ⟩ := IsPGroup.exists_le_sylow hX
  exact ⟨(Qs : Subgroup Y), hXQ, Qs.isPGroup', card_inf_normal_ge N (Qs : Subgroup Y)
    (Sylow.card_eq_multiplicity Qs)⟩

theorem sylow_inf_normal_dvd [Finite G] {p : ℕ} [hp : Fact p.Prime] (K C X : Subgroup G)
    (hCK : C ≤ K) (hCn : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ ∈ C) (hXK : X ≤ K) (hX : IsPGroup p ↥X) :
    ∃ Q : Subgroup G, Q ≤ K ∧ X ≤ Q ∧ IsPGroup p ↥Q ∧
      p ^ (Nat.card ↥C).factorization p ∣ Nat.card ↥(Q ⊓ C) := by
  haveI : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hCK).2 (fun h k hh hk => hCn k hk h hh)
  have hX' : IsPGroup p ↥(X.subgroupOf K) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  obtain ⟨Q', hXQ', hQ'p, hQ'd⟩ := sylow_card_dvd_of_normal (C.subgroupOf K) (X.subgroupOf K) hX'
  have hcardC : Nat.card ↥(C.subgroupOf K) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv
  have hEq : (Q'.map K.subtype) ⊓ C = (Q' ⊓ C.subgroupOf K).map K.subtype := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx1
      exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_subgroupOf.2 hx2⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      exact ⟨Subgroup.mem_map.2 ⟨y, hy1, rfl⟩, Subgroup.mem_subgroupOf.1 hy2⟩
  refine ⟨Q'.map K.subtype, ?_, ?_, hQ'p.map K.subtype, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  · intro x hx
    have hxK : x ∈ K := hXK hx
    exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hXQ' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · rw [hEq, Subgroup.card_map_of_injective Subtype.val_injective, ← hcardC]
    exact hQ'd

theorem exists_conj_le_of_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] (Y S E₀ : Subgroup G)
    (hSY : S ≤ Y) (hSc : Nat.card ↥S = p ^ (Nat.card ↥Y).factorization p)
    (hE₀Y : E₀ ≤ Y) (hE₀ : IsPGroup p ↥E₀) :
    ∃ g ∈ Y, GLBConj g E₀ ≤ S := by
  let E' : Subgroup ↥Y := E₀.subgroupOf Y
  have hE' : IsPGroup p ↥E' := hE₀.of_equiv (Subgroup.subgroupOfEquivOfLe hE₀Y).symm
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow hE'
  let S' : Subgroup ↥Y := S.subgroupOf Y
  have hS'c : Nat.card ↥S' = p ^ (Nat.card ↥Y).factorization p := by
    rw [← hSc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Y T (Sylow.ofCard S' hS'c)
  have hST : MulAut.conj h • (T : Subgroup ↥Y) = S' := by
    have := congrArg (fun P : Sylow p ↥Y => (P : Subgroup ↥Y)) hh
    rw [Sylow.coe_subgroup_smul] at this
    exact this
  refine ⟨(h⁻¹ : ↥Y).1, (h⁻¹ : ↥Y).2, ?_⟩
  intro z hz
  rw [mem_gLBConj] at hz
  have hxE : (h⁻¹ : ↥Y).1 * z * ((h⁻¹ : ↥Y).1)⁻¹ ∈ E₀ := hz
  let xY : ↥Y := ⟨(h⁻¹ : ↥Y).1 * z * ((h⁻¹ : ↥Y).1)⁻¹, hE₀Y hxE⟩
  have hxT : xY ∈ (T : Subgroup ↥Y) := hT (Subgroup.mem_subgroupOf.2 hxE)
  have hmem : MulAut.conj h • xY ∈ MulAut.conj h • (T : Subgroup ↥Y) :=
    Subgroup.smul_mem_pointwise_smul xY (MulAut.conj h) (T : Subgroup ↥Y) hxT
  rw [hST] at hmem
  have hval : ((MulAut.conj h • xY : ↥Y) : G) = z := by
    simp [MulAut.conj_apply, xY, mul_assoc]
  have hmem' := Subgroup.mem_subgroupOf.1 hmem
  rwa [hval] at hmem'

end Helpers

@[expose] def cmSubgroup {G : Type} [Group G] (M N O : Subgroup G)
    (hO : ∀ a ∈ M, ∀ o ∈ O, a * o * a⁻¹ ∈ O) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ g ∈ N, x * g * x⁻¹ * g⁻¹ ∈ O}
  one_mem' := ⟨M.one_mem, fun g _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxg⟩ ⟨hy, hyg⟩
    refine ⟨M.mul_mem hx hy, fun g hg => ?_⟩
    have e : x * y * g * (x * y)⁻¹ * g⁻¹ =
        (x * (y * g * y⁻¹ * g⁻¹) * x⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
    rw [e]
    exact O.mul_mem (hO x hx _ (hyg g hg)) (hxg g hg)
  inv_mem' := by
    rintro x ⟨hx, hxg⟩
    refine ⟨M.inv_mem hx, fun g hg => ?_⟩
    have e : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ = x⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hO x⁻¹ (M.inv_mem hx) _ (O.inv_mem (hxg g hg))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec13h

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem Sec13h.inputANormGamma_holds : Sec13h.InputANormGamma := by
  intro G _ _ m p B M E A D T h
  have hAel : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1
  have hDA : D ≤ A := h.hD.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  refine le_trans ?_ (normalizer_le_normalizer_gammaStar p D)
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    rw [hcomm a ha d (hDA hd), mul_assoc, mul_inv_cancel, mul_one]
    exact hd
  · intro hd
    have hx : a * d * a⁻¹ ∈ A := hDA hd
    have hda : d = a⁻¹ * (a * d * a⁻¹) * a := by group
    rw [hda, hcomm a⁻¹ (inv_mem ha) _ hx, mul_assoc, inv_mul_cancel, mul_one]
    exact hd

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
