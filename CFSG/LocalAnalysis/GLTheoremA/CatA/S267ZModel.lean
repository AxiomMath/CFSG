module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S267
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def Z1AutData (p : ℕ) (M : Type) [Group M] (α : MulAut M) : Prop :=
  ∃ R : Subgroup M, IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧ (∀ s ∈ R, α s = s) ∧
    ∃ r ∈ R, r ≠ 1 ∧
      GLAPComponent p (Subgroup.centralizer ({r} : Set M))
        (GLAPLayer p (Subgroup.centralizer ({r} : Set M))) ∧
      (∀ (k : ℤ) (s : M), s ∈ R →
        (∀ j ∈ GLAPLayer p (Subgroup.centralizer ({r} : Set M)),
          (α ^ k * MulAut.conj s) j * j⁻¹ ∈
            GLAPPrimeCoreOf p (GLAPLayer p (Subgroup.centralizer ({r} : Set M)))) →
        α ^ k = 1 ∧ s ∈ Subgroup.zpowers r) ∧
      GLAPLayer p (GLAPLayer p (Subgroup.centralizer ({r} : Set M)) ⊓ fixSubgroup α) ≠ ⊥ ∧
      (∃ T : Subgroup M, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map α.toMonoidHom = T ∧
        R ≤ Subgroup.normalizer (T : Set M)) ∧
      ∃ u : M, u ≠ 1 ∧ u ^ 2 = 1 ∧ u * r = r * u ∧
        ∀ j ∈ GLAPLayer p (Subgroup.centralizer ({r} : Set M)), j * u = u * j

@[expose] def Z1Model (p : ℕ) (M : Type) [Group M] : Prop :=
  (∀ E : Subgroup (MulAut M), IsElemAbelian p E → Nat.card E ≤ p ^ 3) ∧
    ∀ E : Subgroup (MulAut M), IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∃ α ∈ E, α ∉ (MulAut.conj : M →* MulAut M).range ∧ Z1AutData p M α

@[expose] def Z3Data (p : ℕ) (M : Type) [Group M] (E : Subgroup (MulAut M)) : Prop :=
  ∃ β ∈ E, β ≠ 1 ∧
    GLAPComponent p (fixSubgroup β) (GLAPLayer p (fixSubgroup β)) ∧
    (∀ γ ∈ E, (∀ j ∈ GLAPLayer p (fixSubgroup β),
        γ j * j⁻¹ ∈ GLAPPrimeCoreOf p (GLAPLayer p (fixSubgroup β))) →
      γ ∈ Subgroup.zpowers β) ∧
    (∃ α ∈ E, α ∉ Subgroup.zpowers β ∧
      GLAPLayer p (GLAPLayer p (fixSubgroup β) ⊓ fixSubgroup α) ≠ ⊥) ∧
    (∃ T : Subgroup M, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ γ ∈ E, T.map γ.toMonoidHom = T) ∧
    ∃ u : M, u ≠ 1 ∧ u ^ 2 = 1 ∧ β u = u ∧
      ∀ j ∈ GLAPLayer p (fixSubgroup β), j * u = u * j

@[expose] def Z3Model (p : ℕ) (M : Type) [Group M] : Prop :=
  (∀ E : Subgroup (MulAut M), IsElemAbelian p E → Nat.card E ≤ p ^ 3) ∧
    ∀ E : Subgroup (MulAut M), IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ AM : Subgroup M, IsMulCommutative AM → Subgroup.center M ≤ AM →
        E ⊓ (MulAut.conj : M →* MulAut M).range = AM.map (MulAut.conj : M →* MulAut M) →
        Z3Data p M E

@[expose] def Z1LinBranch : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (M : Type) [Group M] [Finite M], catalogIs M (onLie fun d => d = .A 2 Q) → Z1Model p M

@[expose] def Z1UniBranch : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (M : Type) [Group M] [Finite M], catalogIs M (onLie fun d => d = .twistedA 2 Q) → Z1Model p M

@[expose] def Z3LinBranch : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (M : Type) [Group M] [Finite M], CFSG.Open.IsQuasisimple M → GLAPPrimeCore p M = ⊥ →
      Subgroup.center M ≠ ⊥ → catalogIs (M ⧸ Subgroup.center M) (onLie fun d => d = .A 2 Q) →
        Z3Model p M

@[expose] def Z3UniBranch : Prop :=
  ∀ (p : ℕ) (Q : TauCeti.PrimePower), p.Prime → p ≠ 2 → Q.p ≠ 2 → Q.p ≠ p →
    ∀ (M : Type) [Group M] [Finite M], CFSG.Open.IsQuasisimple M → GLAPPrimeCore p M = ⊥ →
      Subgroup.center M ≠ ⊥ →
        catalogIs (M ⧸ Subgroup.center M) (onLie fun d => d = .twistedA 2 Q) → Z3Model p M


section Helpers

variable {Ω : Type} [Group Ω]

private theorem mem_ker_conjNormal {S : Subgroup Ω} [S.Normal] {x : Ω} :
    x ∈ (MulAut.conjNormal : Ω →* MulAut ↥S).ker ↔ x ∈ Subgroup.centralizer (S : Set Ω) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨s, hs⟩)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc s * x = x * s * x⁻¹ * x := by rw [h1]
      _ = x * s := by group
  · intro h
    ext ⟨s, hs⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h s hs]
    group

private theorem conjNormal_coe {S : Subgroup Ω} [S.Normal] (s : ↥S) :
    MulAut.conjNormal (s : Ω) = MulAut.conj s := by
  ext x
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

private theorem card_eq_card_map_mul {G H : Type*} [Group G] [Group H] (f : G →* H) (A : Subgroup G) :
    Nat.card A = Nat.card (A.map f) * Nat.card ↥(A ⊓ f.ker) := by
  have h1 := Subgroup.card_ker_mul_card_range (f.comp A.subtype)
  have hr : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : (f.comp A.subtype).ker = f.ker.subgroupOf A := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hk2 : Nat.card (f.ker.subgroupOf A) = Nat.card ↥(A ⊓ f.ker) := by
    rw [← Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hr, hk, hk2] at h1
  rw [← h1, mul_comm]

private theorem map_subtype_centralizer (S : Subgroup Ω) (x : ↥S) :
    (Subgroup.centralizer ({x} : Set ↥S)).map S.subtype =
      S ⊓ Subgroup.centralizer ({(x : Ω)} : Set Ω) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hgS, hg⟩
    exact ⟨⟨g, hgS⟩, Subtype.ext hg, rfl⟩

private theorem map_subtype_inf_fixSubgroup (S : Subgroup Ω) [S.Normal] (X : Subgroup ↥S) (a : Ω) :
    (X ⊓ fixSubgroup (MulAut.conjNormal a)).map S.subtype =
      X.map S.subtype ⊓ Subgroup.centralizer ({a} : Set Ω) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype, mem_fixSubgroup]
  constructor
  · rintro ⟨y, ⟨hyX, hy⟩, rfl⟩
    refine ⟨⟨y, hyX, rfl⟩, ?_⟩
    have h1 := congrArg Subtype.val hy
    rw [MulAut.conjNormal_apply] at h1
    calc (y : Ω) * a = a * y * a⁻¹ * a := by rw [h1]
      _ = a * y := by group
  · rintro ⟨⟨y, hyX, rfl⟩, hy⟩
    refine ⟨y, ⟨hyX, ?_⟩, rfl⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hy]
    group

private theorem map_subtype_fixSubgroup (S : Subgroup Ω) [S.Normal] (a : Ω) :
    (fixSubgroup (MulAut.conjNormal a : MulAut ↥S)).map S.subtype =
      S ⊓ Subgroup.centralizer ({a} : Set Ω) := by
  have h := map_subtype_inf_fixSubgroup S ⊤ a
  rwa [top_inf_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

private theorem mem_normalizer_map_subtype {S : Subgroup Ω} [S.Normal] {X : Subgroup ↥S} {a : Ω}
    (h : X.map (MulAut.conjNormal a : MulAut ↥S).toMonoidHom = X) :
    a ∈ Subgroup.normalizer ((X.map S.subtype : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (MulAut.conjNormal a : MulAut ↥S) x ∈ X := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    refine ⟨_, hx', ?_⟩
    simp [MulAut.conjNormal_apply]
  · rintro ⟨y, hy, hyg⟩
    have hgS : g ∈ S := by
      have hy' : a⁻¹ * (y : Ω) * a ∈ S := by
        have := (inferInstance : S.Normal).conj_mem (y : Ω) y.2 a⁻¹
        simpa using this
      rw [Subgroup.coe_subtype] at hyg
      rw [hyg] at hy'
      simpa [mul_assoc] using hy'
    have hy2 : y ∈ X.map (MulAut.conjNormal a : MulAut ↥S).toMonoidHom := by rw [h]; exact hy
    obtain ⟨x, hx, hxy⟩ := hy2
    have hxg : x = ⟨g, hgS⟩ := by
      apply (MulAut.conjNormal a : MulAut ↥S).injective
      apply Subtype.ext
      have : ((MulAut.conjNormal a : MulAut ↥S) x : Ω) = (y : Ω) := congrArg Subtype.val hxy
      rw [this, MulAut.conjNormal_apply]
      simpa using hyg
    exact ⟨x, hx, by rw [hxg]; rfl⟩

private theorem map_centralizer_singleton {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (r : M) :
    (Subgroup.centralizer ({r} : Set M)).map (e : M →* M') =
      Subgroup.centralizer ({e r} : Set M') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

private theorem fixSubgroup_congr' {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (α : MulAut M) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map (e : M →* M') := by
  ext y
  simp only [Subgroup.mem_map, mem_fixSubgroup, MulAut.congr_apply, MonoidHom.coe_coe]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    simp [hx]

private theorem congr_conj {M M' : Type} [Group M] [Group M'] (e : M ≃* M') (m : M) :
    MulAut.congr e (MulAut.conj m) = MulAut.conj (e m) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem map_glaPLayer_eq {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (γ : MulAut M)
    {X : Subgroup M} (h : X.map γ.toMonoidHom = X) :
    (GLAPLayer p X).map γ.toMonoidHom = GLAPLayer p X := by
  rw [CFSG.glaPLayer_map_eq_of_injective hp γ.toMonoidHom γ.injective, h]

private theorem map_centralizer_eq_of_fix {M : Type} [Group M] (γ : MulAut M) {r : M} (h : γ r = r) :
    (Subgroup.centralizer ({r} : Set M)).map γ.toMonoidHom = Subgroup.centralizer ({r} : Set M) := by
  have := map_centralizer_singleton γ r
  rw [h] at this
  exact this

private theorem map_conj_eq_of_mem_normalizer {M : Type} [Group M] {T : Subgroup M} {s : M}
    (hs : s ∈ Subgroup.normalizer (T : Set M)) : T.map (MulAut.conj s).toMonoidHom = T := by
  ext y
  rw [Subgroup.mem_normalizer_iff] at hs
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hs x).1 hx
  · intro hy
    refine ⟨s⁻¹ * y * s, (hs _).2 (by simpa [mul_assoc] using hy), ?_⟩
    group

private theorem exists_of_mem_zpowers_sup {G : Type*} [Group G] {a : G} {R : Subgroup G}
    (hR : ∀ s ∈ R, a * s = s * a) {b : G} (hb : b ∈ Subgroup.zpowers a ⊔ R) :
    ∃ k : ℤ, ∃ s ∈ R, b = a ^ k * s := by
  let H : Subgroup G :=
    { carrier := {x | ∃ k : ℤ, ∃ s ∈ R, x = a ^ k * s}
      mul_mem' := by
        rintro x y ⟨k, s, hs, rfl⟩ ⟨l, t, ht, rfl⟩
        have hc : Commute (a ^ l) s := (Commute.zpow_left (hR s hs) l)
        refine ⟨k + l, s * t, R.mul_mem hs ht, ?_⟩
        rw [zpow_add]
        calc a ^ k * s * (a ^ l * t) = a ^ k * (s * a ^ l) * t := by group
          _ = a ^ k * (a ^ l * s) * t := by rw [hc.eq]
          _ = a ^ k * a ^ l * (s * t) := by group
      one_mem' := ⟨0, 1, R.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨k, s, hs, rfl⟩
        have hc : Commute (a ^ (-k)) s⁻¹ := (Commute.zpow_left (hR s hs) (-k)).inv_right
        refine ⟨-k, s⁻¹, R.inv_mem hs, ?_⟩
        rw [mul_inv_rev, ← zpow_neg]
        exact hc.eq.symm }
  have hle : Subgroup.zpowers a ⊔ R ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨1, 1, R.one_mem, by simp⟩
    · intro s hs
      exact ⟨0, s, hs, by simp⟩
  exact hle hb

private theorem centMod_pointwise {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {S : Subgroup Ω} [S.Normal]
    {J : Subgroup ↥S} {b : Ω} (h : CentMod p (J.map S.subtype) b) :
    ∀ j ∈ J, (MulAut.conjNormal b : MulAut ↥S) j * j⁻¹ ∈ GLAPPrimeCoreOf p J := by
  intro j hj
  obtain ⟨-, hc⟩ := mem_centModSubgroup.1 (centMod_iff.1 h)
  have h1 := hc (j : Ω) ⟨j, hj, rfl⟩
  rw [CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map S.subtype_injective p J] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have he : (MulAut.conjNormal b : MulAut ↥S) j * j⁻¹ = o⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    simp only [Subgroup.coe_subtype] at hoeq
    rw [hoeq, commutatorElement_def]
    group
  rw [he]
  exact (GLAPPrimeCoreOf p J).inv_mem ho

private theorem isPGroup_center_of_core {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (h : GLAPPrimeCore p H = ⊥) : IsPGroup p (Subgroup.center H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro z
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.ne_one
  refine ⟨a, ?_⟩
  set y : Subgroup.center H := z ^ (p ^ a) with hy
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow' z (pow_ne_zero a hp.ne_zero), hn, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  have hN : (Subgroup.zpowers (y : H)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : ((y : H) ^ k) ∈ Subgroup.center H := Subgroup.zpow_mem _ y.2 k
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hc : Nat.Coprime p (Nat.card (Subgroup.zpowers (y : H))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyo]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hle : Subgroup.zpowers (y : H) ≤ GLAPPrimeCore p H := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨hN, hc⟩
  rw [h] at hle
  have h1 : (y : H) = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  exact Subtype.ext h1


private theorem card_inf_centralizer {p : ℕ} (hp : p.Prime) [Finite Ω] {S A : Subgroup Ω} [S.Normal]
    (hA : IsElemAbelian p A) (hA4 : Nat.card A = p ^ 4) (hcyc : CycModSylow p S)
    (hb : ∀ E : Subgroup (MulAut ↥S), IsElemAbelian p E → Nat.card E ≤ p ^ 3) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (S : Set Ω)) = p ∧
      Nat.card (A.map (MulAut.conjNormal : Ω →* MulAut ↥S)) = p ^ 3 := by
  set C := A ⊓ Subgroup.centralizer (S : Set Ω) with hC
  have hcent : ∀ g ∈ C, CentMod p S g := by
    intro g hg
    refine ⟨by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top g, ?_⟩
    have hbot : ⁅S, Subgroup.zpowers g⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro s hs z hz
      have hzc : z ∈ Subgroup.centralizer (S : Set Ω) :=
        (Subgroup.zpowers_le.2 hg.2) hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 hzc s hs)
    rw [hbot]
    exact bot_le
  have hpg : IsPGroup p C := (hA.mono inf_le_left).isPGroup
  have hcycC : IsCyclic C := hcyc C hcent hpg
  have hdvd : Nat.card C ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun c =>
      Subtype.ext (by simpa using hA.2 c (Subgroup.mem_inf.1 c.2).1)
  have hker : A ⊓ (MulAut.conjNormal : Ω →* MulAut ↥S).ker = C := by
    rw [hC]
    congr 1
    ext x
    exact mem_ker_conjNormal
  have hcard := card_eq_card_map_mul (MulAut.conjNormal : Ω →* MulAut ↥S) A
  rw [hker, hA4] at hcard
  have hE := hb _ (hA.map (MulAut.conjNormal : Ω →* MulAut ↥S))
  have hp1 := hp.one_lt
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exfalso
    rw [h1, mul_one] at hcard
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  · refine ⟨h1, ?_⟩
    rw [h1] at hcard
    have h4 : p ^ 4 = p ^ 3 * p := by ring
    rw [h4] at hcard
    exact (Nat.eq_of_mul_eq_mul_right hp.pos hcard).symm
end Helpers


private theorem map_fixSubgroup_of_commute {M : Type} [Group M] {γ β : MulAut M} (h : γ * β = β * γ) :
    (fixSubgroup β).map γ.toMonoidHom = fixSubgroup β := by
  have h' : γ⁻¹ * β = β * γ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]
  ext y
  simp only [Subgroup.mem_map, mem_fixSubgroup, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := congrArg (fun φ : MulAut M => φ z) h
    simp only [MulAut.mul_apply] at this
    rw [← this, hz]
  · intro hy
    refine ⟨γ⁻¹ y, ?_, by simp⟩
    have := congrArg (fun φ : MulAut M => φ y) h'
    simp only [MulAut.mul_apply] at this
    rw [← this, hy]

private theorem isMulCommutative_map {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : IsMulCommutative K) : IsMulCommutative (K.map f) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hK.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem z1AutData_congr {p : ℕ} (hp : p.Prime) {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M']
    (e : M ≃* M') {α : MulAut M} (h : Z1AutData p M α) : Z1AutData p M' (MulAut.congr e α) := by
  obtain ⟨R, hRel, hRcard, hRfix, r, hrR, hr1, hcomp, hcm, hlay, ⟨T, hT1, hT2, hTα, hRT⟩, u, hu1, hu2,
    hur, huJ⟩ := h
  have hfi : Function.Injective (e : M →* M') := e.injective
  set X := Subgroup.centralizer ({r} : Set M) with hX
  have hX' : X.map (e : M →* M') = Subgroup.centralizer ({e r} : Set M') := map_centralizer_singleton e r
  have hJ' : GLAPLayer p (Subgroup.centralizer ({e r} : Set M')) = (GLAPLayer p X).map (e : M →* M') := by
    rw [← hX', CFSG.glaPLayer_map_eq_of_injective hp (e : M →* M') hfi]
  refine ⟨R.map (e : M →* M'), hRel.map _, by rw [Subgroup.card_map_of_injective hfi]; exact hRcard, ?_,
    e r, ⟨r, hrR, rfl⟩, ?_, ?_, ?_, ?_, ⟨T.map (e : M →* M'), ?_, hT2.map _, ?_, ?_⟩, e u, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    simp [MulAut.congr_apply, hRfix s hs]
  · intro h1
    exact hr1 (e.injective (by rw [h1, map_one]))
  · rw [← hX', ← CFSG.glaPLayer_map_eq_of_injective hp (e : M →* M') hfi]
    exact (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hfi p X _).2 hcomp
  · intro k s' hs' hj
    obtain ⟨s, hs, rfl⟩ := hs'
    have key : ∀ j ∈ GLAPLayer p X,
        (α ^ k * MulAut.conj s) j * j⁻¹ ∈ GLAPPrimeCoreOf p (GLAPLayer p X) := by
      intro j hj0
      have h1 := hj (e j) (by rw [hJ']; exact ⟨j, hj0, rfl⟩)
      rw [hJ', CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map hfi] at h1
      have h2 : (MulAut.congr e α ^ k * MulAut.conj ((e : M →* M') s)) (e j) * (e j)⁻¹ =
          (e : M →* M') ((α ^ k * MulAut.conj s) j * j⁻¹) := by
        rw [← map_zpow]
        simp [MulAut.congr_apply, MulAut.conj_apply]
      rw [h2] at h1
      exact (Subgroup.mem_map_iff_mem hfi).1 h1
    obtain ⟨hk1, hk2⟩ := hcm k s hs key
    refine ⟨by rw [← map_zpow, hk1, map_one], ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk2
    exact ⟨m, by simp⟩
  · rw [hJ', fixSubgroup_congr' e α, ← Subgroup.map_inf_eq _ _ _ hfi,
      ← CFSG.glaPLayer_map_eq_of_injective hp (e : M →* M') hfi]
    intro h1
    exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ hfi).1 h1)
  · intro h1
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hfi).1 h1)
  · rw [Subgroup.map_map]
    have hcomp' : (MulAut.congr e α).toMonoidHom.comp (e : M →* M') =
        (e : M →* M').comp α.toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [hcomp', ← Subgroup.map_map, hTα]
  · exact (Subgroup.map_mono hRT).trans (Subgroup.le_normalizer_map _)
  · intro h1
    exact hu1 (e.injective (by rw [h1, map_one]))
  · rw [← map_pow, hu2, map_one]
  · rw [← map_mul, hur, map_mul]
  · rw [hJ']
    rintro _ ⟨j, hj, rfl⟩
    simp only [MonoidHom.coe_coe]
    rw [← map_mul, huJ j hj, map_mul]

theorem z1AutData_conj {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M] (h : MulAut M)
    {α : MulAut M} (hα : Z1AutData p M α) : Z1AutData p M (h * α * h⁻¹) := by
  have he : MulAut.congr h α = h * α * h⁻¹ := MulEquiv.ext fun _ => rfl
  rw [← he]
  exact z1AutData_congr hp h hα

theorem z1Model_congr {p : ℕ} (hp : p.Prime) {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M']
    (e : M ≃* M') (h : Z1Model p M) : Z1Model p M' := by
  obtain ⟨hb, hd⟩ := h
  set φ : MulAut M' ≃* MulAut M := MulAut.congr e.symm with hφ
  refine ⟨fun E' hE' => ?_, fun E' hE' hc => ?_⟩
  · have := hb (E'.map φ.toMonoidHom) (hE'.map _)
    rwa [Subgroup.card_map_of_injective φ.injective] at this
  · obtain ⟨α, hαE, hαn, hαd⟩ := hd (E'.map φ.toMonoidHom) (hE'.map _)
      (by rw [Subgroup.card_map_of_injective φ.injective]; exact hc)
    obtain ⟨β, hβ, rfl⟩ := hαE
    have h2 : MulAut.congr e (φ.toMonoidHom β) = β := by
      ext x
      simp [hφ, MulAut.congr_apply]
    refine ⟨β, hβ, ?_, ?_⟩
    · rintro ⟨m', hm'⟩
      apply hαn
      refine ⟨e.symm m', ?_⟩
      rw [← congr_conj, hm']
      rfl
    · have := z1AutData_congr hp e hαd
      rwa [h2] at this

theorem z3Data_congr {p : ℕ} (hp : p.Prime) {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M']
    (e : M ≃* M') {E : Subgroup (MulAut M)} (h : Z3Data p M E) :
    Z3Data p M' (E.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨β, hβE, hβ1, hcomp, hcm, ⟨α, hαE, hαβ, hlay⟩, ⟨T, hT1, hT2, hTE⟩, u, hu1, hu2, huβ, huJ⟩ := h
  have hfi : Function.Injective (e : M →* M') := e.injective
  have hF : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : M →* M') := fixSubgroup_congr' e β
  have hJ : GLAPLayer p (fixSubgroup (MulAut.congr e β)) =
      (GLAPLayer p (fixSubgroup β)).map (e : M →* M') := by
    rw [hF, CFSG.glaPLayer_map_eq_of_injective hp (e : M →* M') hfi]
  have hmapT : ∀ γ : MulAut M, ∀ T : Subgroup M,
      (T.map (e : M →* M')).map (MulAut.congr e γ).toMonoidHom = (T.map γ.toMonoidHom).map (e : M →* M') := by
    intro γ T
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.congr_apply]
  refine ⟨MulAut.congr e β, ⟨β, hβE, rfl⟩, ?_, ?_, ?_, ⟨MulAut.congr e α, ⟨α, hαE, rfl⟩, ?_, ?_⟩,
    ⟨T.map (e : M →* M'), ?_, hT2.map _, ?_⟩, e u, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hβ1 ((MulAut.congr e).injective (by rw [h1, map_one]))
  · rw [hJ, hF]
    exact (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hfi p _ _).2 hcomp
  · rintro _ ⟨γ, hγ, rfl⟩ hj
    have key : ∀ j ∈ GLAPLayer p (fixSubgroup β),
        γ j * j⁻¹ ∈ GLAPPrimeCoreOf p (GLAPLayer p (fixSubgroup β)) := by
      intro j hj0
      have h1 := hj (e j) (by rw [hJ]; exact ⟨j, hj0, rfl⟩)
      rw [hJ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPPrimeCoreOf_map hfi] at h1
      have h2 : ((MulAut.congr e).toMonoidHom γ) (e j) * (e j)⁻¹ = (e : M →* M') (γ j * j⁻¹) := by
        simp [MulAut.congr_apply]
      rw [h2] at h1
      exact (Subgroup.mem_map_iff_mem hfi).1 h1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hcm γ hγ key)
    exact ⟨m, (map_zpow (MulAut.congr e) β m).symm⟩
  · rintro ⟨m, hm⟩
    apply hαβ
    refine ⟨m, (MulAut.congr e).injective ?_⟩
    rw [map_zpow]
    exact hm
  · rw [hJ, fixSubgroup_congr' e α, ← Subgroup.map_inf_eq _ _ _ hfi,
      ← CFSG.glaPLayer_map_eq_of_injective hp (e : M →* M') hfi]
    intro h1
    exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ hfi).1 h1)
  · intro h1
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hfi).1 h1)
  · rintro _ ⟨γ, hγ, rfl⟩
    show (T.map (e : M →* M')).map (MulAut.congr e γ).toMonoidHom = _
    rw [hmapT, hTE γ hγ]
  · intro h1
    exact hu1 (e.injective (by rw [h1, map_one]))
  · rw [← map_pow, hu2, map_one]
  · simp [MulAut.congr_apply, huβ]
  · rw [hJ]
    rintro _ ⟨j, hj, rfl⟩
    simp only [MonoidHom.coe_coe]
    rw [← map_mul, huJ j hj, map_mul]

theorem z3Model_congr {p : ℕ} (hp : p.Prime) {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M']
    (e : M ≃* M') (h : Z3Model p M) : Z3Model p M' := by
  obtain ⟨hb, hd⟩ := h
  set φ : MulAut M' ≃* MulAut M := MulAut.congr e.symm with hφ
  refine ⟨fun E' hE' => ?_, fun E' hE' hc AM' hAM' hZ' hEq' => ?_⟩
  · have := hb (E'.map φ.toMonoidHom) (hE'.map _)
    rwa [Subgroup.card_map_of_injective φ.injective] at this
  · have hc' : Nat.card (E'.map φ.toMonoidHom) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective φ.injective]; exact hc
    have hAM : IsMulCommutative (AM'.map (e.symm : M' →* M)) := isMulCommutative_map _ hAM'
    have hZ : Subgroup.center M ≤ AM'.map (e.symm : M' →* M) := by
      intro z hz
      refine ⟨e z, hZ' ?_, by simp⟩
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := hz (e.symm g)
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply, this]
    have hrange : (MulAut.conj : M' →* MulAut M').range.map φ.toMonoidHom = (MulAut.conj : M →* MulAut M).range := by
      rw [← MonoidHom.range_comp]
      have : φ.toMonoidHom.comp (MulAut.conj : M' →* MulAut M') =
          (MulAut.conj : M →* MulAut M).comp (e.symm : M' →* M) := by
        ext m x
        simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
      rw [this, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, ← MonoidHom.range_eq_map]
    have hEq : E'.map φ.toMonoidHom ⊓ (MulAut.conj : M →* MulAut M).range =
        (AM'.map (e.symm : M' →* M)).map (MulAut.conj : M →* MulAut M) := by
      rw [← hrange, ← Subgroup.map_inf_eq _ _ _ φ.injective, hEq', Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext m x
      simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
    have hdat := hd _ (hE'.map _) hc' _ hAM hZ hEq
    have h2 := z3Data_congr hp e hdat
    have hE'' : (E'.map φ.toMonoidHom).map (MulAut.congr e).toMonoidHom = E' := by
      rw [Subgroup.map_map]
      have : (MulAut.congr e).toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
        ext β x
        simp [hφ, MulAut.congr_apply]
      rw [this, Subgroup.map_id]
    rwa [hE''] at h2

theorem z1_of_model {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] (S A : Subgroup Ω)
    (hSn : S.Normal) (hZ : Subgroup.center ↥S = ⊥) (hA : IsElemAbelian p A)
    (hA4 : Nat.card A = p ^ 4) (hcyc : CycModSylow p S) (hM : Z1Model p ↥S) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (S : Set Ω)) = p ∧
    ∃ a ∈ A, a ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
      ∃ R : Subgroup Ω, R ≤ S ∧ IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧
        (∀ s ∈ R, a * s = s * a) ∧
        ∃ r ∈ R, r ≠ 1 ∧
          GLAPComponent p (S ⊓ Subgroup.centralizer ({r} : Set Ω))
            (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω))) ∧
          Subgroup.zpowers a ⊔ R ≤
            Subgroup.normalizer
              ((GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)) : Subgroup Ω) : Set Ω) ∧
          (∀ b ∈ Subgroup.zpowers a ⊔ R,
            CentMod p (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω))) b →
              b ∈ Subgroup.zpowers r) ∧
          GLAPLayer p (GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)) ⊓
            Subgroup.centralizer ({a} : Set Ω)) ≠ ⊥ ∧
          (∃ T : Subgroup Ω, T ≤ S ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
            Subgroup.zpowers a ⊔ R ≤ Subgroup.normalizer (T : Set Ω)) ∧
          ∃ u ∈ S, u ≠ 1 ∧ u ^ 2 = 1 ∧ u * r = r * u ∧
            ∀ j ∈ GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)), j * u = u * j := by
  haveI := hSn
  haveI : Fact p.Prime := ⟨hp⟩
  have hsi := S.subtype_injective
  obtain ⟨hcard, hEcard⟩ := card_inf_centralizer hp hA hA4 hcyc hM.1
  obtain ⟨α, hαE, hαn, hdat⟩ := hM.2 _ (hA.map (MulAut.conjNormal : Ω →* MulAut ↥S)) hEcard
  obtain ⟨a, haA, rfl⟩ := hαE
  obtain ⟨R, hRel, hRcard, hRfix, r, hrR, hr1, hcomp, hcm, hlay, ⟨T, hT1, hT2, hTα, hRT⟩, u, hu1, hu2,
    hur, huJ⟩ := hdat
  set X : Subgroup ↥S := Subgroup.centralizer ({r} : Set ↥S) with hXdef
  set J : Subgroup ↥S := GLAPLayer p X with hJdef
  have hXΩ : S ⊓ Subgroup.centralizer ({(r : Ω)} : Set Ω) = X.map S.subtype :=
    (map_subtype_centralizer S r).symm
  have hJΩ : GLAPLayer p (S ⊓ Subgroup.centralizer ({(r : Ω)} : Set Ω)) = J.map S.subtype := by
    rw [hXΩ, ← CFSG.glaPLayer_map_eq_of_injective hp S.subtype hsi]
  have hJα : J.map (MulAut.conjNormal a : MulAut ↥S).toMonoidHom = J :=
    map_glaPLayer_eq hp _ (map_centralizer_eq_of_fix _ (hRfix r hrR))
  have hJs : ∀ s ∈ R, J.map (MulAut.conj s).toMonoidHom = J := by
    intro s hs
    refine map_glaPLayer_eq hp _ (map_centralizer_eq_of_fix _ ?_)
    rw [MulAut.conj_apply]
    have h1 := congrArg Subtype.val (hRel.1.is_comm.comm ⟨s, hs⟩ ⟨r, hrR⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [h1, mul_inv_cancel_right]
  have hα1 : (MulAut.conjNormal a : MulAut ↥S) ≠ 1 := fun h => hαn ⟨1, by rw [h, map_one]⟩
  have hap : a ^ p = 1 := hA.2 a haA
  have hcomm : ∀ s ∈ R.map S.subtype, a * s = s * a := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := congrArg Subtype.val (hRfix s hs)
    rw [MulAut.conjNormal_apply] at h1
    simp only [Subgroup.coe_subtype]
    calc a * (s : Ω) = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h1]
  refine ⟨hcard, a, haA, ?_, R.map S.subtype, Subgroup.map_subtype_le R, hRel.map _,
    by rw [Subgroup.card_map_of_injective hsi]; exact hRcard, hcomm, (r : Ω), ⟨r, hrR, rfl⟩,
    fun h => hr1 (Subtype.ext h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    have hmem' : a ∈ ((S ⊔ Subgroup.centralizer (S : Set Ω) : Subgroup Ω) : Set Ω) := hmem
    rw [Subgroup.normal_mul] at hmem'
    obtain ⟨s, hs, c, hc, hsc⟩ := Set.mem_mul.1 hmem'
    apply hαn
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← hsc, map_mul, MonoidHom.mem_ker.1 (mem_ker_conjNormal.2 hc), mul_one]
    exact (conjNormal_coe (S := S) ⟨s, hs⟩).symm
  · rw [hJΩ, hXΩ]
    exact (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hsi p X J).2 hcomp
  · rw [hJΩ]
    refine sup_le (Subgroup.zpowers_le.2 (mem_normalizer_map_subtype hJα)) ?_
    rintro _ ⟨s, hs, rfl⟩
    apply mem_normalizer_map_subtype
    rw [show (MulAut.conjNormal (S.subtype s) : MulAut ↥S) = MulAut.conj s from conjNormal_coe s]
    exact hJs s hs
  · intro b hb hbc
    obtain ⟨k, s', hs', rfl⟩ := exists_of_mem_zpowers_sup hcomm hb
    obtain ⟨s, hs, rfl⟩ := hs'
    rw [hJΩ] at hbc
    have hpt := centMod_pointwise hbc
    have hψb : (MulAut.conjNormal (a ^ k * S.subtype s) : MulAut ↥S) =
        (MulAut.conjNormal a : MulAut ↥S) ^ k * MulAut.conj s := by
      rw [map_mul, map_zpow]
      congr 1
      exact conjNormal_coe s
    rw [hψb] at hpt
    obtain ⟨hk1, hk2⟩ := hcm k s hs hpt
    have hak : a ^ k = 1 := by
      have ho : orderOf (MulAut.conjNormal a : MulAut ↥S) = p :=
        orderOf_eq_prime (by rw [← map_pow, hap, map_one]) hα1
      have hdk : (p : ℤ) ∣ k := by rw [← ho]; exact orderOf_dvd_iff_zpow_eq_one.2 hk1
      have hoa : (orderOf a : ℤ) ∣ k :=
        (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hap)).trans hdk
      exact orderOf_dvd_iff_zpow_eq_one.1 hoa
    rw [hak, one_mul]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk2
    exact ⟨m, by simp⟩
  · rw [hJΩ, ← map_subtype_inf_fixSubgroup S J a, ← CFSG.glaPLayer_map_eq_of_injective hp S.subtype hsi]
    intro h
    exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ hsi).1 h)
  · refine ⟨T.map S.subtype, Subgroup.map_subtype_le T,
      fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hsi).1 h), hT2.map _, ?_⟩
    refine sup_le (Subgroup.zpowers_le.2 (mem_normalizer_map_subtype hTα)) ?_
    rintro _ ⟨s, hs, rfl⟩
    apply mem_normalizer_map_subtype
    rw [show (MulAut.conjNormal (S.subtype s) : MulAut ↥S) = MulAut.conj s from conjNormal_coe s]
    exact map_conj_eq_of_mem_normalizer (hRT hs)
  · refine ⟨(u : Ω), u.2, fun h => hu1 (Subtype.ext h), ?_, congrArg Subtype.val hur, ?_⟩
    · rw [← Subgroup.coe_pow, hu2, Subgroup.coe_one]
    · rw [hJΩ]
      rintro _ ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (huJ j hj)

theorem z3_of_model {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] (S A : Subgroup Ω)
    (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥) (hA : IsElemAbelian p A)
    (hA4 : Nat.card A = p ^ 4) (hcyc : CycModSylow p S) (hM : Z3Model p ↥S) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (S : Set Ω)) = p ∧
    ∃ b ∈ A, b ∉ Subgroup.centralizer (S : Set Ω) ∧
      GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω))
        (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω))) ∧
      A ≤ Subgroup.normalizer
        ((GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) : Subgroup Ω) : Set Ω) ∧
      (∀ x ∈ A, CentMod p (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω))) x →
        x ∈ Subgroup.zpowers b ⊔ (A ⊓ Subgroup.centralizer (S : Set Ω))) ∧
      (∃ a ∈ A, a ∉ Subgroup.zpowers b ⊔ (A ⊓ Subgroup.centralizer (S : Set Ω)) ∧
        GLAPLayer p (GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ⊓
          Subgroup.centralizer ({a} : Set Ω)) ≠ ⊥) ∧
      (∃ T : Subgroup Ω, T ≤ S ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set Ω)) ∧
      ∃ u ∈ S, u ≠ 1 ∧ u ^ 2 = 1 ∧ u * b = b * u ∧
        ∀ j ∈ GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)), j * u = u * j := by
  haveI := hSn
  haveI : Fact p.Prime := ⟨hp⟩
  have hsi := S.subtype_injective
  set C := Subgroup.centralizer (S : Set Ω) with hCdef
  obtain ⟨hcard, hEcard⟩ := card_inf_centralizer hp hA hA4 hcyc hM.1
  have hmulAC : ∀ g ∈ A ⊔ C, ∃ x ∈ A, ∃ c ∈ C, g = x * c := by
    intro g hg
    have hg' : g ∈ ((A ⊔ C : Subgroup Ω) : Set Ω) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
    exact ⟨x, hx, c, hc, rfl⟩
  set W := (A ⊔ S) ⊓ C with hWdef
  have hZp : IsPGroup p (Subgroup.center ↥S) := isPGroup_center_of_core hp hcore
  have hWp : IsPGroup p W := by
    intro w
    obtain ⟨hwAS, hwC⟩ := Subgroup.mem_inf.1 w.2
    have hwp : (w : Ω) ^ p ∈ S := by
      have hw' : (w : Ω) ∈ ((A ⊔ S : Subgroup Ω) : Set Ω) := hwAS
      rw [Subgroup.mul_normal] at hw'
      obtain ⟨x, hx, s, hs, hxs⟩ := Set.mem_mul.1 hw'
      have h1 : (((w : Ω)) : Ω ⧸ S) = ((x : Ω) : Ω ⧸ S) := by
        rw [← hxs, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).2 hs, mul_one]
      have h2 : ((((w : Ω) ^ p : Ω)) : Ω ⧸ S) = 1 := by
        rw [QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow, hA.2 x hx, QuotientGroup.mk_one]
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hwpC : (w : Ω) ^ p ∈ C := Subgroup.pow_mem _ hwC p
    have hzc : (⟨(w : Ω) ^ p, hwp⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hwpC g g.2
    obtain ⟨k, hk⟩ := hZp ⟨_, hzc⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h3 := congrArg (fun z : Subgroup.center ↥S => ((z : ↥S) : Ω)) hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul]
    exact h3
  have hWcent : ∀ g ∈ W, CentMod p S g := by
    intro g hg
    refine ⟨by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top g, ?_⟩
    have hbot : ⁅S, Subgroup.zpowers g⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro s hs z hz
      have hzc : z ∈ C := (Subgroup.zpowers_le.2 (Subgroup.mem_inf.1 hg).2) hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 hzc s hs
    rw [hbot]
    exact bot_le
  have hWcyc : IsCyclic W := hcyc W hWcent hWp
  have hWcomm : ∀ c ∈ W, ∀ c' ∈ W, c * c' = c' * c := by
    intro c hc c' hc'
    letI := hWcyc.commGroup
    exact congrArg Subtype.val (mul_comm (⟨c, hc⟩ : W) ⟨c', hc'⟩)
  set AM : Subgroup ↥S := (A ⊔ C).subgroupOf S with hAMdef
  have hAMmem : ∀ s : ↥S, s ∈ AM ↔ (s : Ω) ∈ A ⊔ C := fun s => Subgroup.mem_subgroupOf
  have hAMab : IsMulCommutative AM := by
    refine ⟨⟨fun t t' => ?_⟩⟩
    set σ : Ω := ((t : ↥S) : Ω)
    set σ' : Ω := ((t' : ↥S) : Ω)
    obtain ⟨x, hx, c, hc, hxc⟩ := hmulAC σ ((hAMmem t).1 t.2)
    obtain ⟨x', hx', c', hc', hxc'⟩ := hmulAC σ' ((hAMmem t').1 t'.2)
    have hcW : c ∈ W := by
      refine ⟨?_, hc⟩
      have : c = x⁻¹ * σ := by rw [hxc]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem hx))
        (Subgroup.mem_sup_right (t : ↥S).2)
    have hc'W : c' ∈ W := by
      refine ⟨?_, hc'⟩
      have : c' = x'⁻¹ * σ' := by rw [hxc']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem hx'))
        (Subgroup.mem_sup_right (t' : ↥S).2)
    have hcc := hWcomm c hcW c' hc'W
    have hxx : x * x' = x' * x := congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
    have hC1 : Commute c σ' := (Subgroup.mem_centralizer_iff.1 hc σ' (t' : ↥S).2).symm
    have hC2 : Commute c' σ := (Subgroup.mem_centralizer_iff.1 hc' σ (t : ↥S).2).symm
    have e1 : x = σ * c⁻¹ := by rw [hxc]; group
    have e2 : x' = σ' * c'⁻¹ := by rw [hxc']; group
    have h1 : σ * c⁻¹ * (σ' * c'⁻¹) = σ * σ' * (c⁻¹ * c'⁻¹) := by
      rw [show σ * c⁻¹ * (σ' * c'⁻¹) = σ * (c⁻¹ * σ') * c'⁻¹ by group, hC1.inv_left.eq]
      group
    have h2 : σ' * c'⁻¹ * (σ * c⁻¹) = σ' * σ * (c'⁻¹ * c⁻¹) := by
      rw [show σ' * c'⁻¹ * (σ * c⁻¹) = σ' * (c'⁻¹ * σ) * c⁻¹ by group, hC2.inv_left.eq]
      group
    have h3 : c⁻¹ * c'⁻¹ = c'⁻¹ * c⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hcc]
    rw [e1, e2, h1, h2, h3] at hxx
    apply Subtype.ext
    apply Subtype.ext
    exact mul_right_cancel hxx
  have hZAM : Subgroup.center ↥S ≤ AM := by
    intro z hz
    rw [hAMmem]
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  have hEq : A.map (MulAut.conjNormal : Ω →* MulAut ↥S) ⊓ (MulAut.conj : ↥S →* MulAut ↥S).range =
      AM.map (MulAut.conj : ↥S →* MulAut ↥S) := by
    ext γ
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ⟨s, hs⟩⟩
      refine ⟨s, (hAMmem s).2 ?_, hs⟩
      have hc : x⁻¹ * (s : Ω) ∈ C := by
        refine mem_ker_conjNormal.1 ?_
        rw [MonoidHom.mem_ker, map_mul, map_inv, conjNormal_coe]
        rw [hs, inv_mul_cancel]
      have : (s : Ω) = x * (x⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨x, hx, c, hc, hxc⟩ := hmulAC _ ((hAMmem s).1 hs)
      refine ⟨⟨x, hx, ?_⟩, ⟨s, rfl⟩⟩
      rw [← conjNormal_coe, hxc, map_mul, MonoidHom.mem_ker.1 (mem_ker_conjNormal.2 hc), mul_one]
  obtain ⟨β, hβE, hβ1, hcomp, hcm, ⟨α, hαE, hαβ, hlay⟩, ⟨T, hT1, hT2, hTE⟩, u, hu1, hu2, huβ, huJ⟩ :=
    hM.2 _ (hA.map (MulAut.conjNormal : Ω →* MulAut ↥S)) hEcard AM hAMab hZAM hEq
  obtain ⟨b, hbA, rfl⟩ := hβE
  set F : Subgroup ↥S := fixSubgroup (MulAut.conjNormal b : MulAut ↥S) with hFdef
  set J : Subgroup ↥S := GLAPLayer p F with hJdef
  have hXΩ : S ⊓ Subgroup.centralizer ({b} : Set Ω) = F.map S.subtype :=
    (map_subtype_fixSubgroup S b).symm
  have hJΩ : GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) = J.map S.subtype := by
    rw [hXΩ, ← CFSG.glaPLayer_map_eq_of_injective hp S.subtype hsi]
  have hJE : ∀ x ∈ A, J.map (MulAut.conjNormal x : MulAut ↥S).toMonoidHom = J := by
    intro x hx
    apply map_glaPLayer_eq hp
    apply map_fixSubgroup_of_commute
    exact congrArg Subtype.val ((hA.map (MulAut.conjNormal : Ω →* MulAut ↥S)).1.is_comm.comm
      ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨b, hbA, rfl⟩⟩)
  refine ⟨hcard, b, hbA, fun h => hβ1 (MonoidHom.mem_ker.1 (mem_ker_conjNormal.2 h)), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hJΩ, hXΩ]
    exact (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hsi p F J).2 hcomp
  · intro x hx
    rw [hJΩ]
    exact mem_normalizer_map_subtype (hJE x hx)
  · intro x hx hxc
    rw [hJΩ] at hxc
    have hγ := hcm _ ⟨x, hx, rfl⟩ (centMod_pointwise hxc)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hγ
    have hc : (b ^ m)⁻¹ * x ∈ A ⊓ C := by
      refine ⟨A.mul_mem (A.inv_mem (A.zpow_mem hbA m)) hx, mem_ker_conjNormal.1 ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hm, inv_mul_cancel]
    have : x = b ^ m * ((b ^ m)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b m))
      (Subgroup.mem_sup_right hc)
  · obtain ⟨a, haA, rfl⟩ := hαE
    refine ⟨a, haA, ?_, ?_⟩
    · intro hmem
      apply hαβ
      have h1 : (MulAut.conjNormal a : MulAut ↥S) ∈
          (Subgroup.zpowers b ⊔ (A ⊓ C)).map (MulAut.conjNormal : Ω →* MulAut ↥S) := ⟨a, hmem, rfl⟩
      rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
      have h2 : (A ⊓ C).map (MulAut.conjNormal : Ω →* MulAut ↥S) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨y, hy, rfl⟩
        exact Subgroup.mem_bot.2 (MonoidHom.mem_ker.1 (mem_ker_conjNormal.2 (Subgroup.mem_inf.1 hy).2))
      rw [h2, sup_bot_eq] at h1
      exact h1
    · rw [hJΩ, ← map_subtype_inf_fixSubgroup S J a,
        ← CFSG.glaPLayer_map_eq_of_injective hp S.subtype hsi]
      intro h
      exact hlay ((Subgroup.map_eq_bot_iff_of_injective _ hsi).1 h)
  · refine ⟨T.map S.subtype, Subgroup.map_subtype_le T,
      fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ hsi).1 h), hT2.map _, ?_⟩
    intro x hx
    exact mem_normalizer_map_subtype (hTE _ ⟨x, hx, rfl⟩)
  · refine ⟨(u : Ω), u.2, fun h => hu1 (Subtype.ext h), ?_, ?_, ?_⟩
    · rw [← Subgroup.coe_pow, hu2, Subgroup.coe_one]
    · have h1 := congrArg Subtype.val huβ
      rw [MulAut.conjNormal_apply] at h1
      calc (u : Ω) * b = b * u * b⁻¹ * b := by rw [h1]
        _ = b * u := by group
    · rw [hJΩ]
      rintro _ ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (huJ j hj)

theorem s267FactZ1_of_branches (hl : Z1LinBranch) (hu : Z1UniBranch) : S267FactZ1 := by
  intro p Q hp hp2 hQ2 hQp Ω _ _ S A hSn _ hZ hcat hA hA4 hcyc
  have hM : Z1Model p ↥S := hcat.elim (hl p Q hp hp2 hQ2 hQp ↥S) (hu p Q hp hp2 hQ2 hQp ↥S)
  exact z1_of_model hp S A hSn hZ hA hA4 hcyc hM

theorem s267FactZ3_of_branches (hl : Z3LinBranch) (hu : Z3UniBranch) : S267FactZ3 := by
  intro p Q hp hp2 hQ2 hQp Ω _ _ S A hSn hqs hcore hZ hcat hA hA4 hcyc
  have hM : Z3Model p ↥S := hcat.elim (hl p Q hp hp2 hQ2 hQp ↥S hqs hcore hZ)
    (hu p Q hp hp2 hQ2 hQp ↥S hqs hcore hZ)
  exact z3_of_model hp S A hSn hcore hA hA4 hcyc hM

end CFSG.LocalAnalysis.GLTheoremA.S267Z

end
