module

public import CFSG.LieType.SeitzGeneration.OuterLinearField
public import CFSG.LieType.SeitzGeneration.ClassicalOuterLeaves

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Defs

variable {n : ℕ} {F : Type} [Field F]

@[expose] def OutdiagPlane (p : ℕ) (E : Subgroup (MulAut (projectiveSL n F))) : Prop :=
  IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ E ≤ linearAutGroup n F ∧
    ¬ E ≤ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range

@[expose] def LiftStable (E : Subgroup (MulAut (projectiveSL n F)))
    (W : Submodule F (Fin n → F)) : Prop :=
  ∀ A : GL (Fin n) F, conjAut n F A ∈ E → ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W

end Defs

@[expose] def OutdiagReduciblePlanes : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n p : ℕ), 4 ≤ n → p.Prime → p ≠ 2 → (p : F) ≠ 0 →
    ∀ E : Subgroup (MulAut (projectiveSL n F)), OutdiagPlane p E →
      (∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W) → PlaneGen E

@[expose] def OutdiagHeisenbergPlanes : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ), 5 ≤ p → p.Prime → (p : F) ≠ 0 →
    ∀ E : Subgroup (MulAut (projectiveSL p F)), OutdiagPlane p E →
      (∀ W : Submodule F (Fin p → F), LiftStable E W → W = ⊥ ∨ W = ⊤) →
      (∃ A B : GL (Fin p) F, conjAut p F A ∈ E ∧ conjAut p F B ∈ E ∧ A * B ≠ B * A) →
      PlaneGen E

section Group

theorem exists_notMem_zpowers_of_card_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) :
    ∃ e' ∈ E, e' ∉ Subgroup.zpowers e := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hord : orderOf e = p := orderOf_eq_prime (hexp e he) he1
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers e := hcon
  have hfin' : Finite (Subgroup.zpowers e) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, Nat.card_zpowers, hord] at h1
  nlinarith [hp.two_le]

theorem zpowers_sup_zpowers_eq_of_card_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) {e e' : G}
    (he : e ∈ E) (he1 : e ≠ 1) (he' : e' ∈ E) (hne : e' ∉ Subgroup.zpowers e) :
    Subgroup.zpowers e ⊔ Subgroup.zpowers e' = E := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hord : orderOf e = p := orderOf_eq_prime (hexp e he) he1
  set H := Subgroup.zpowers e ⊔ Subgroup.zpowers e' with hH
  have hHE : H ≤ E := sup_le (Subgroup.zpowers_le.2 he) (Subgroup.zpowers_le.2 he')
  have hle1 : Subgroup.zpowers e ≤ H := le_sup_left
  have hdvd1 : Nat.card (Subgroup.zpowers e) ∣ Nat.card H := Subgroup.card_dvd_of_le hle1
  have hdvd2 : Nat.card H ∣ Nat.card E := Subgroup.card_dvd_of_le hHE
  rw [Nat.card_zpowers, hord] at hdvd1
  rw [hcard] at hdvd2
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).1 hdvd2
  have hHne : Nat.card H ≠ p := by
    intro h
    have hfinH : Finite H :=
      Finite.of_injective (Subgroup.inclusion hHE) (Subgroup.inclusion_injective hHE)
    have h2 : Subgroup.zpowers e = H :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [Nat.card_zpowers, hord, h])
    apply hne
    rw [h2]
    exact (le_sup_right : Subgroup.zpowers e' ≤ H) (Subgroup.mem_zpowers e')
  have hk2 : k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · rw [pow_zero] at hkH
      rw [hkH] at hdvd1
      exact absurd (Nat.le_of_dvd one_pos hdvd1) (by have := hp.two_le; omega)
    · exact absurd (by simpa using hkH) hHne
    · rfl
  exact Subgroup.eq_of_le_of_card_ge hHE (by rw [hkH, hk2, hcard])

end Group

section Arith

variable {n : ℕ} {F : Type} [Field F]

theorem outdiag_dvd [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hlin : E ≤ linearAutGroup n F)
    (hout : ¬ E ≤ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range) :
    p ∣ n ∧ p ∣ Nat.card F - 1 := by
  obtain ⟨e, heE, heI⟩ : ∃ e ∈ E,
      e ∉ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 (hlin heE)
  have h1 : conjAut n F (A ^ p) = 1 := by
    rw [map_pow]
    exact hE.2 _ heE
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp h1
  have hup : (GeneralLinearGroup.det A) ^ p = c ^ n := by
    have h2 := congrArg GeneralLinearGroup.det hc
    rw [CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units, map_pow] at h2
    exact h2.symm
  have hnotpow : ∀ v : Fˣ, v ^ n ≠ GeneralLinearGroup.det A := by
    intro v hv
    apply heI
    set A' : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) v⁻¹ * A with hA'
    have hdet : (A' : Matrix (Fin n) (Fin n) F).det = 1 := by
      have h3 : GeneralLinearGroup.det A' = 1 := by
        rw [hA', map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units, inv_pow, hv,
          inv_mul_cancel]
      have h4 := congrArg (fun u : Fˣ => (u : F)) h3
      simpa [GeneralLinearGroup.val_det_apply] using h4
    let X : SpecialLinearGroup (Fin n) F := ⟨A', hdet⟩
    refine ⟨proj n F X, ?_⟩
    rw [← conjAut_toGL]
    have hX : SpecialLinearGroup.toGL X = A' := Units.ext rfl
    rw [hX, hA', map_mul, conjAut_scalar, one_mul]
  constructor
  · by_contra hpn
    obtain ⟨v, hv⟩ := exists_pow_of_pow_eq ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn) hup
    exact hnotpow v hv
  · by_contra hpq
    have hcop : Nat.Coprime (Nat.card Fˣ) p := by
      rw [Nat.card_units]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm
    obtain ⟨w, hw⟩ := exists_pow_of_coprime_card hcop c
    have hu : (GeneralLinearGroup.det A) ^ p = (w ^ n) ^ p := by
      rw [hup, ← hw, ← pow_mul, ← pow_mul, mul_comm]
    have h5 : GeneralLinearGroup.det A = w ^ n :=
      (powCoprime hcop).injective (by simpa [powCoprime_apply] using hu)
    exact hnotpow w h5.symm

end Arith

section Class2

variable {G : Type*} [Group G]

theorem qcomm_pow_left {A B w : G} (hw : ∀ g : G, g * w = w * g)
    (hBA : B * A = w * (A * B)) (k : ℕ) : B * A ^ k = w ^ k * (A ^ k * B) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc B * A ^ (k + 1) = (B * A ^ k) * A := by rw [pow_succ, mul_assoc]
      _ = (w ^ k * (A ^ k * B)) * A := by rw [ih]
      _ = w ^ k * (A ^ k * (B * A)) := by simp only [mul_assoc]
      _ = w ^ k * (A ^ k * (w * (A * B))) := by rw [hBA]
      _ = w ^ k * (w * (A ^ k * (A * B))) := by
        rw [← mul_assoc (A ^ k) w, hw (A ^ k), mul_assoc]
      _ = w ^ (k + 1) * (A ^ (k + 1) * B) := by
        rw [pow_succ w k, pow_succ A k]
        simp only [mul_assoc]

theorem qcomm_pow_eq_one {p : ℕ} {A B w c : G} (hw : ∀ g : G, g * w = w * g)
    (hc : ∀ g : G, g * c = c * g) (hBA : B * A = w * (A * B)) (hAp : A ^ p = c) : w ^ p = 1 := by
  have h1 := qcomm_pow_left hw hBA p
  rw [hAp, hc B] at h1
  exact mul_right_cancel (b := c * B) (by rw [one_mul]; exact h1.symm)

end Class2

section Lift

variable {n : ℕ} {F : Type} [Field F]

theorem mul_scalarGL_comm (c : Fˣ) (g : GL (Fin n) F) :
    g * GeneralLinearGroup.scalar (Fin n) c = GeneralLinearGroup.scalar (Fin n) c * g :=
  (commute_scalarGL c g).symm.eq

theorem exists_scalarGL_comm [Finite F] (hn : 3 ≤ n) {p : ℕ}
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) {A B : GL (Fin n) F}
    (hA : conjAut n F A ∈ E) (hB : conjAut n F B ∈ E) :
    ∃ u : Fˣ, B * A = GeneralLinearGroup.scalar (Fin n) u * (A * B) := by
  have hcomm : conjAut n F B * conjAut n F A = conjAut n F A * conjAut n F B :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hB⟩ ⟨_, hA⟩)
  obtain ⟨u, hu⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn
    (B * A * (A * B)⁻¹)).mp (by rw [map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel])
  exact ⟨u, by rw [hu]; group⟩

theorem exists_scalarGL_pow [Finite F] (hn : 3 ≤ n) {p : ℕ}
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) {A : GL (Fin n) F}
    (hA : conjAut n F A ∈ E) : ∃ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : conjAut n F (A ^ p) = 1 := by
    rw [map_pow]
    exact hE.2 _ hA
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp h1
  exact ⟨c, hc.symm⟩

end Lift

section Arith2

theorem pow_mul_pow_ne_one_of_indep {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e₁ e₂ : G}
    (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1) (he₂ : e₂ ≠ 1) (hne : e₁ ∉ Subgroup.zpowers e₂)
    {i j : ℕ} (hij : ¬ (p ∣ i ∧ p ∣ j)) : e₁ ^ i * e₂ ^ j ≠ 1 := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have hord₂ : orderOf e₂ = p := orderOf_eq_prime h₂ he₂
  by_cases hpi : p ∣ i
  · obtain ⟨k, rfl⟩ := hpi
    rw [pow_mul, h₁, one_pow, one_mul] at h
    exact hij ⟨dvd_mul_right _ _, hord₂ ▸ orderOf_dvd_of_pow_eq_one h⟩
  · apply hne
    have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have h3 : e₁ ^ i = (e₂ ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h4 : e₁ = (e₁ ^ i) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (i * m) h₁, hm, pow_one]
    rw [h4, h3]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)) _

theorem exists_pow_mul_pow_eq_pow_of_cyclic {G : Type*} [CommGroup G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) (a b : G) : ∃ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) ∧ ∃ l : G, a ^ i * b ^ j = l ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  have : Fact p.Prime := ⟨hp⟩
  by_cases hs : (p : ℤ) ∣ s
  · obtain ⟨m, hm⟩ := hs
    refine ⟨1, 0, fun h => hp.one_lt.not_ge (Nat.le_of_dvd one_pos h.1), g ^ m, ?_⟩
    rw [pow_one, pow_zero, mul_one, hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  · have hs0 : (s : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    set i₀ : ℕ := (-(t : ZMod p) / (s : ZMod p)).val with hi₀
    have hdvd : (p : ℤ) ∣ s * i₀ + t := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hi₀, ZMod.natCast_zmod_val]
      field_simp
      ring
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨i₀, 1, fun h => hp.one_lt.not_ge (Nat.le_of_dvd one_pos h.2), g ^ m, ?_⟩
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add, ← zpow_natCast,
      ← _root_.zpow_mul, hm, mul_comm]

end Arith2

section Root

variable {n : ℕ} {F : Type} [Field F]

theorem exists_pth_root_element [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) {X Y : GL (Fin n) F}
    (hX : conjAut n F X ∈ E) (hY : conjAut n F Y ∈ E) :
    ∃ (i j : ℕ) (z₀ : GL (Fin n) F), ¬ (p ∣ i ∧ p ∣ j) ∧
      conjAut n F z₀ = conjAut n F X ^ i * conjAut n F Y ^ j ∧ z₀ ^ p = 1 := by
  obtain ⟨cX, hcX⟩ := exists_scalarGL_pow hn hE hX
  obtain ⟨cY, hcY⟩ := exists_scalarGL_pow hn hE hY
  obtain ⟨i, j, hij, l, hl⟩ := exists_pow_mul_pow_eq_pow_of_cyclic hp cX cY
  have hXi : conjAut n F (X ^ i) ∈ E := by
    rw [map_pow]
    exact E.pow_mem hX i
  have hYj : conjAut n F (Y ^ j) ∈ E := by
    rw [map_pow]
    exact E.pow_mem hY j
  obtain ⟨u, hu⟩ := exists_scalarGL_comm hn hE hXi hYj
  have hXip : (X ^ i) ^ p = GeneralLinearGroup.scalar (Fin n) (cX ^ i) := by
    rw [← pow_mul, mul_comm, pow_mul, hcX, map_pow]
  have hYjp : (Y ^ j) ^ p = GeneralLinearGroup.scalar (Fin n) (cY ^ j) := by
    rw [← pow_mul, mul_comm, pow_mul, hcY, map_pow]
  have hup : (GeneralLinearGroup.scalar (Fin n) u) ^ p = 1 :=
    qcomm_pow_eq_one (A := X ^ i) (B := Y ^ j) (mul_scalarGL_comm u) (mul_scalarGL_comm _) hu hXip
  have hz : (X ^ i * Y ^ j) ^ p = GeneralLinearGroup.scalar (Fin n) (l ^ p) := by
    rw [mul_pow_prime_eq hp hp2 (fun g => commute_scalarGL u g) hu hup, hXip, hYjp,
      ← map_mul, ← hl]
  refine ⟨i, j, GeneralLinearGroup.scalar (Fin n) l⁻¹ * (X ^ i * Y ^ j), hij, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul, map_mul, map_pow, map_pow]
  · rw [(commute_scalarGL l⁻¹ (X ^ i * Y ^ j)).mul_pow, hz, ← map_pow, ← map_mul, inv_pow,
      inv_mul_cancel, map_one]

end Root

section Stab

variable {n : ℕ} {F : Type} [Field F]

theorem mem_of_conjAut_mem_of_sup_eq [Finite F] (hn : 3 ≤ n)
    {E : Subgroup (MulAut (projectiveSL n F))} {e₁ e₂ : MulAut (projectiveSL n F)}
    (hgen : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = E) {K : Subgroup (GL (Fin n) F)}
    (hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ K) {A₁ A₂ : GL (Fin n) F}
    (hA₁ : A₁ ∈ K) (hA₂ : A₂ ∈ K) (h₁ : conjAut n F A₁ = e₁) (h₂ : conjAut n F A₂ = e₂)
    {A : GL (Fin n) F} (hA : conjAut n F A ∈ E) : A ∈ K := by
  have hle : E ≤ K.map (conjAut n F) := by
    rw [← hgen]
    exact sup_le (Subgroup.zpowers_le.2 ⟨A₁, hA₁, h₁⟩) (Subgroup.zpowers_le.2 ⟨A₂, hA₂, h₂⟩)
  obtain ⟨g, hgK, hg⟩ := hle hA
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (g⁻¹ * A)).mp
    (by rw [map_mul, map_inv, hg, inv_mul_cancel])
  have hAeq : A = g * GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc]
    group
  rw [hAeq]
  exact K.mul_mem hgK (hK c)

def stabSubGL (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {A | (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) ∧
    ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W}
  one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hA1 _ (hB1 w hw)
    · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hB2 _ (hA2 w hw)
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    exact ⟨hA2, by simpa using hA1⟩

theorem inv_mulVec_mem_of_pow_scalar {A : GL (Fin n) F} {p : ℕ} (hp : 0 < p) {c : Fˣ}
    (hAp : A ^ p = GeneralLinearGroup.scalar (Fin n) c) {W : Submodule F (Fin n → F)}
    (hW : ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) :
    ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  intro w hw
  have hpow : ∀ k : ℕ, ∀ w ∈ W, ((A ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW _ (ih w hw)
  have hAp' : A * A ^ (p - 1) = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← pow_succ', Nat.sub_add_cancel hp, hAp]
  have hinv : A⁻¹ = GeneralLinearGroup.scalar (Fin n) c⁻¹ * A ^ (p - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc A * (GeneralLinearGroup.scalar (Fin n) c⁻¹ * A ^ (p - 1))
        = GeneralLinearGroup.scalar (Fin n) c⁻¹ * (A * A ^ (p - 1)) := by
          rw [← mul_assoc, mul_scalarGL_comm c⁻¹ A, mul_assoc]
      _ = 1 := by rw [hAp', ← map_mul, inv_mul_cancel, map_one]
  rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec, scalarGL_coe_eq_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  exact W.smul_mem _ (hpow _ w hw)

end Stab

section Dichotomy

variable {n : ℕ} {F : Type} [Field F]

theorem outdiag_dichotomy [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : OutdiagPlane p E) (hpn : p ∣ n)
    (hpq : p ∣ Nat.card F - 1) :
    (∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W) ∨
      (n = p ∧ (∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) ∧
        ∃ A B : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F B ∈ E ∧ A * B ≠ B * A) := by
  classical
  obtain ⟨hE1, hc, hlin, hout⟩ := hE
  have hn0 : 0 < n := by omega
  have : Fact p.Prime := ⟨hp⟩
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W
  · exact Or.inl hred
  right
  have hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hcon
    push Not at hcon
    exact hred ⟨W, hcon.1, hcon.2, hW⟩
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp E hE1.2 hc
  obtain ⟨X, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₁)
  obtain ⟨Y, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₂)
  obtain ⟨i, j, z₀, hij, hz₀c, hz₀p⟩ := exists_pth_root_element hn hp hp2 hE1 he₁ he₂
  have hz₀E : conjAut n F z₀ ∈ E := by
    rw [hz₀c]
    exact E.mul_mem (E.pow_mem he₁ i) (E.pow_mem he₂ j)
  have hē₀ : conjAut n F z₀ ≠ 1 := by
    rw [hz₀c]
    exact pow_mul_pow_ne_one_of_indep hp (hE1.2 _ he₁) (hE1.2 _ he₂) he₂1 he₁₂ hij
  have hz₀pM : (z₀ : Matrix (Fin n) (Fin n) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz₀p, Units.val_one]
  obtain ⟨ξ, v, -, hv0, hzv⟩ := exists_eigenvector_of_pow_eq_one hp.pos
    (exists_primitiveRoot_of_dvd_card_sub_one hp hpq) hn0 hz₀pM
  have hz₀ns : ∀ a : F, (z₀ : Matrix (Fin n) (Fin n) F) ≠ a • 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_scalarGL_of_gl_coe_eq_smul hn0 ha
    apply hē₀
    rw [← hu, conjAut_scalar]
  have hnonab : ∃ A B : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F B ∈ E ∧ A * B ≠ B * A := by
    by_contra hab
    push Not at hab
    let W : Submodule F (Fin n → F) :=
      LinearMap.ker (Matrix.toLin' ((z₀ : Matrix (Fin n) (Fin n) F) - ξ • 1))
    have hW : ∀ w, w ∈ W ↔ (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w = ξ • w := fun w => by
      simp [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
    have hWs : LiftStable E W := by
      intro A hA w hw
      rw [hW] at hw ⊢
      have hcm : (z₀ : Matrix (Fin n) (Fin n) F) * A = A * z₀ :=
        congrArg Units.val (hab z₀ A hz₀E hA)
      rw [Matrix.mulVec_mulVec, hcm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    rcases hirr W hWs with h | h
    · have hv : v ∈ (⊥ : Submodule F (Fin n → F)) := h ▸ (hW v).2 hzv
      exact hv0 (by simpa using hv)
    · have hall : ∀ w, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w = ξ • w := fun w =>
        (hW w).1 (h ▸ Submodule.mem_top)
      apply hz₀ns ξ
      rw [Matrix.ext_iff_mulVec]
      intro w
      rw [hall, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨?_, hirr, hnonab⟩
  obtain ⟨e'', he''E, he''⟩ := exists_notMem_zpowers_of_card_sq hp hE1.2 hc hz₀E hē₀
  obtain ⟨z', rfl⟩ := mem_linearAutGroup_iff.1 (hlin he''E)
  have hgen := zpowers_sup_zpowers_eq_of_card_sq hp hE1.2 hc hz₀E hē₀ he''E he''
  obtain ⟨ζ, hζ⟩ := exists_scalarGL_comm hn hE1 he''E hz₀E
  have hncomm : z₀ * z' ≠ z' * z₀ := by
    intro hcomm
    obtain ⟨A, B, hA, hB, hAB⟩ := hnonab
    set S : Set (GL (Fin n) F) := {z₀, z'} ∪ Set.range (GeneralLinearGroup.scalar (Fin n)) with hS
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_range] at hx hy
      rcases hx with (rfl | rfl) | ⟨c, rfl⟩ <;> rcases hy with (rfl | rfl) | ⟨d, rfl⟩
      all_goals first
        | rfl
        | exact hcomm
        | exact hcomm.symm
        | exact (mul_scalarGL_comm _ _).symm
        | exact mul_scalarGL_comm _ _
    have hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.closure S := fun c =>
      Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    have hz₀K : z₀ ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hz'K : z' ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
    have hAK := mem_of_conjAut_mem_of_sup_eq hn hgen hK hz₀K hz'K rfl rfl hA
    have hBK := mem_of_conjAut_mem_of_sup_eq hn hgen hK hz₀K hz'K rfl rfl hB
    letI : CommGroup (Subgroup.closure S) :=
      Subgroup.closureCommGroupOfComm fun x hx y hy _ => hSc x hx y hy
    exact hAB (congrArg Subtype.val (mul_comm (⟨A, hAK⟩ : Subgroup.closure S) ⟨B, hBK⟩))
  have hzvk : ∀ k : ℕ, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ
      (((z' ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) =
      (((ζ ^ k : Fˣ) : F) * ξ) • (((z' ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) := by
    intro k
    have h1 := qcomm_pow_left (A := z') (B := z₀) (mul_scalarGL_comm ζ) hζ k
    have h2 : (z₀ : Matrix (Fin n) (Fin n) F) * ((z' ^ k : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = ((ζ ^ k : Fˣ) : F) • (((z' ^ k : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * (z₀ : Matrix (Fin n) (Fin n) F)) := by
      have h3 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1
      simp only [Units.val_mul] at h3
      rw [← map_pow, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h3
      exact h3
    rw [Matrix.mulVec_mulVec, h2, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hzv,
      Matrix.mulVec_smul, smul_smul]
  set vk : Fin p → (Fin n → F) :=
    fun k => ((z' ^ (k : ℕ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v with hvk
  set W : Submodule F (Fin n → F) := Submodule.span F (Set.range vk) with hWdef
  have hvW : v ∈ W := by
    have h0 : vk ⟨0, hp.pos⟩ = v := by simp [hvk]
    rw [← h0]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hz₀W : ∀ w ∈ W, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    have hle : W ≤ W.comap (Matrix.mulVecLin (z₀ : Matrix (Fin n) (Fin n) F)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      rw [hvk]
      show (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ (((z' ^ (k : ℕ) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ W
      rw [hzvk (k : ℕ)]
      exact W.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    exact fun w hw => hle hw
  obtain ⟨c', hc'⟩ := exists_scalarGL_pow hn hE1 he''E
  have hz'W : ∀ w ∈ W, (z' : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    have hle : W ≤ W.comap (Matrix.mulVecLin (z' : Matrix (Fin n) (Fin n) F)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      have hstep : (z' : Matrix (Fin n) (Fin n) F) *ᵥ vk k =
          ((z' ^ ((k : ℕ) + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := by
        rw [hvk, pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [hstep]
      by_cases hk : (k : ℕ) + 1 < p
      · exact Submodule.subset_span ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
      · have hkp : (k : ℕ) + 1 = p := by omega
        rw [hkp, hc', scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem _ hvW
    exact fun w hw => hle hw
  have hKs : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ stabSubGL W := by
    intro c
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
    · rw [← map_inv, scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
  have hz₀S : z₀ ∈ stabSubGL W :=
    ⟨hz₀W, inv_mulVec_mem_of_pow_scalar hp.pos (c := 1) (by rw [hz₀p, map_one]) hz₀W⟩
  have hz'S : z' ∈ stabSubGL W := ⟨hz'W, inv_mulVec_mem_of_pow_scalar hp.pos hc' hz'W⟩
  have hWs : LiftStable E W := fun A hA =>
    (mem_of_conjAut_mem_of_sup_eq hn hgen hKs hz₀S hz'S rfl rfl hA).1
  rcases hirr W hWs with h | h
  · exact absurd (h ▸ hvW) (by simpa using hv0)
  · have hle : n ≤ p := by
      calc n = Module.finrank F (Fin n → F) := (Module.finrank_fin_fun F).symm
        _ = Module.finrank F W := by rw [h, finrank_top]
        _ ≤ Fintype.card (Fin p) := finrank_range_le_card vk
        _ = p := Fintype.card_fin p
    exact le_antisymm hle (Nat.le_of_dvd hn0 hpn)

end Dichotomy

section Bridge

variable {n : ℕ} {F : Type} [Field F]

theorem conjAut_proj_eq_of_mem_fixSL (hn : 0 < n) {A : GL (Fin n) F}
    {k : SpecialLinearGroup (Fin n) F} (hk : k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)) :
    conjAut n F A (proj n F k) = proj n F k := by
  obtain ⟨ζ, hζ⟩ := hk
  have hdet : (A : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hζn : ζ ^ n = 1 := by
    have h := congrArg Matrix.det hζ
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, k.2, Fintype.card_fin] at h
    have h' : (ζ ^ n - 1) * (A : Matrix (Fin n) (Fin n) F).det = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hdet)
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hn.ne'] at hζn
    exact zero_ne_one hζn
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, (u : F) = ζ := ⟨Units.mk0 ζ hζ0, rfl⟩
  have hun : u ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hζn, Units.val_one])
  have hz : proj n F (scalarElement u hun) = 1 :=
    proj_eq_one_iff.2 (scalarElement_mem_scalars u hun)
  rw [conjAut_proj]
  have hconj : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A k =
      k * scalarElement u hun := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement,
      Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, hu, hζ, Matrix.smul_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hconj, map_mul, hz, mul_one]

theorem planeGen_of_closure_fixSL (hn : 0 < n) {E : Subgroup (MulAut (projectiveSL n F))}
    (h : Subgroup.closure {k : SpecialLinearGroup (Fin n) F | ∃ A : GL (Fin n) F,
      conjAut n F A ∈ E ∧ conjAut n F A ≠ 1 ∧ k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)} = ⊤) :
    PlaneGen E := by
  refine planeGen_of_comap_eq_top (eq_top_iff.mpr fun k _ => ?_)
  have hk : k ∈ Subgroup.closure {k : SpecialLinearGroup (Fin n) F | ∃ A : GL (Fin n) F,
      conjAut n F A ∈ E ∧ conjAut n F A ≠ 1 ∧ k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)} :=
    h ▸ Subgroup.mem_top k
  refine (Subgroup.closure_le ((planeClosure E).comap (proj n F))).2 ?_ hk
  rintro k' ⟨A, hA, hA1, hk'⟩
  exact mem_planeClosure_of_fixed hA hA1 (conjAut_proj_eq_of_mem_fixSL hn hk')

end Bridge

section Assembly

theorem planeGen_of_outdiag {n : ℕ} {F : Type} [Field F] [Finite F]
    (hR : OutdiagReduciblePlanes) (hH : OutdiagHeisenbergPlanes) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hex : ¬ (n = 3 ∧ p = 3 ∧ Nat.card F = 4))
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : OutdiagPlane p E) : PlaneGen E := by
  obtain ⟨hpn, hpq⟩ := outdiag_dvd hn hp hE.1 hE.2.2.1 hE.2.2.2
  by_cases h3 : n = 3
  · subst h3
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpn
    subst hp3
    have h4 : 4 < Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      have h2 : Nat.card F ≠ 4 := fun h => hex ⟨rfl, rfl, h⟩
      omega
    exact planeGen_of_linearAut outerHeisCore hpq h4 hE.1 hE.2.1 hE.2.2.1
  · rcases outdiag_dichotomy hn hp hp2 hE hpn hpq with hred | ⟨hnp, hirr, hnonab⟩
    · exact hR F n p (by omega) hp hp2 hpF E hE hred
    · subst hnp
      have hp5 : 5 ≤ n := by
        rcases (by omega : n = 4 ∨ 5 ≤ n) with rfl | h
        · exact absurd hp (by norm_num)
        · exact h
      exact hH F n hp5 hp hpF E hE hirr hnonab

theorem planeGen_outer_matrix (hR : OutdiagReduciblePlanes)
    (hH : OutdiagHeisenbergPlanes) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hex : ¬ (n = 3 ∧ p = 3 ∧ Nat.card K = 4))
    {E : Subgroup (MulAut (projectiveSL n K))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ E ≤ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    PlaneGen E := by
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hpK : (p : K) ≠ 0 := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h)).symm
  by_cases hD : E ≤ linearAutGroup n K
  · exact planeGen_of_outdiag hR hH hn hp hp2 hpK hex ⟨hE, hc, hD, hout⟩
  · exact planeGen_of_field_outer hℓ hf hn hK hp hp2 hpℓ hE hc hD

theorem primePower_card_four_aux {q : TauCeti.PrimePower} (h : q.card = 4) :
    q.p = 2 ∧ q.exponent = 2 := by
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, h] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (q.prime_p.dvd_of_dvd_pow (show q.p ∣ 2 ^ 2 by simpa using h1))
  refine ⟨hp2, ?_⟩
  have h2 : 2 ^ q.exponent = 2 ^ 2 := by
    have h3 := h
    rw [TauCeti.PrimePower.card_def, hp2] at h3
    rw [h3]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h2


theorem seitzOuterLinearWide_of_outdiag (hR : OutdiagReduciblePlanes)
    (hH : OutdiagHeisenbergPlanes) : SeitzOuterLinearWide := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, m, q, hd, hm⟩
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A m q, hv⟩ ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hpq : p ≠ q.p := by simpa using hpd
  have hKcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine planeGen_of_outer_model e ?_
  refine planeGen_outer_matrix hR hH q.prime_p q.exponent_pos hKcard (by omega) hp hp2 hpq ?_
    (isElemAbelian_map_congr e hE) ((card_map_congr e E).trans hc)
    (not_le_range_conj_map_congr e hout)
  rintro ⟨h3, rfl, h4⟩
  have hm2 : m = 2 := by omega
  subst hm2
  have hq4 : q.card = 4 := by
    rw [TauCeti.PrimePower.card_def, ← hKcard]
    exact h4
  exact hex (Or.inl ⟨rfl, Or.inr (Or.inl ⟨q, (primePower_card_four_aux hq4).1,
    (primePower_card_four_aux hq4).2, rfl⟩)⟩)

end Assembly

end CFSG.LieType.SeitzGeneration
