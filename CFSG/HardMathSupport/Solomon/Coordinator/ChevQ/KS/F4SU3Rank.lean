module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompSU3
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Rank

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun β : MulAut G => β x) hg
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

section Act

variable {X : Type} [Group X] {K B : Subgroup X}

@[expose] noncomputable def actK (hBN : B ≤ Subgroup.normalizer (K : Set X)) : ↥B →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)

theorem coe_actK (hBN : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) (y : ↥K) :
    ((actK hBN b y : ↥K) : X) = (b : X) * (y : X) * (b : X)⁻¹ := rfl

@[expose] noncomputable def innerPart (hBN : B ≤ Subgroup.normalizer (K : Set X)) : Subgroup ↥K :=
  (actK hBN).range.comap (MulAut.conj : ↥K →* MulAut ↥K)

theorem mem_innerPart {hBN : B ≤ Subgroup.normalizer (K : Set X)} {e : ↥K} :
    e ∈ innerPart hBN ↔ ∃ b : ↥B, actK hBN b = MulAut.conj e := by
  simp [innerPart, MonoidHom.mem_range, eq_comm]

theorem mem_innerPart' {hBN : B ≤ Subgroup.normalizer (K : Set X)} {e : ↥K} :
    e ∈ innerPart hBN ↔ ∃ b ∈ B, ∀ y : ↥K, (b : X) * (y : X) * b⁻¹ = (e : X) * (y : X) * (e : X)⁻¹ := by
  rw [mem_innerPart]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, b.2, fun y => ?_⟩
    have := congrArg (fun β : MulAut ↥K => ((β y : ↥K) : X)) hb
    simpa [coe_actK, MulAut.conj_apply] using this
  · rintro ⟨b, hb, h⟩
    refine ⟨⟨b, hb⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
    simpa [coe_actK, MulAut.conj_apply] using h y

theorem isElemAbelian_innerPart (hZ : Subgroup.center ↥K = ⊥) (hB : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) : IsElemAbelian 3 (innerPart hBN) := by
  have hinj := conj_injective hZ
  refine ⟨⟨⟨fun e e' => ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨b, hb⟩ := mem_innerPart.1 e.2
    obtain ⟨b', hb'⟩ := mem_innerPart.1 e'.2
    apply Subtype.ext
    apply hinj
    have hbb : b * b' = b' * b := hB.1.is_comm.comm b b'
    have h1 : MulAut.conj ((e : ↥K) * (e' : ↥K)) = MulAut.conj ((e' : ↥K) * (e : ↥K)) := by
      rw [map_mul, map_mul, ← hb, ← hb', ← map_mul, ← map_mul, hbb]
    exact h1
  · obtain ⟨b, hb⟩ := mem_innerPart.1 he
    apply hinj
    have : b ^ 3 = 1 := Subtype.ext (hB.2 b b.2)
    rw [map_pow, ← hb, ← map_pow, this, map_one, map_one]

theorem zmod_six_aux : ∀ u v : Multiplicative (ZMod (2 * 3)), u ^ 3 = 1 → v ^ 3 = 1 → v ≠ 1 →
    ∃ i : Fin 3, u * v ^ (i : ℕ) = 1 := by
  decide

theorem exists_pow_innerAt
    (Θ : MulAut ↥K →* Multiplicative (ZMod (2 * 3)))
    (hΘ : Θ.ker ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) {x : X} (hxB : x ∈ B)
    (hxI : ¬ Bal209F4Aux.InnerAt K x) :
    ∀ b ∈ B, ∃ i : ℕ, Bal209F4Aux.InnerAt K (x ^ i * b) := by
  intro b hb
  have hcube : ∀ c : ↥B, (Θ (actK hBN c)) ^ 3 = 1 := fun c => by
    rw [← map_pow, ← map_pow]
    have : c ^ 3 = 1 := Subtype.ext (hB.2 c c.2)
    rw [this, map_one, map_one]
  have hxne : Θ (actK hBN ⟨x, hxB⟩) ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := hΘ (MonoidHom.mem_ker.2 h)
    apply hxI
    refine ⟨k, k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (k : X) * y * (k : X)⁻¹ = x * y * x⁻¹ :=
      congrArg (fun β : MulAut ↥K => ((β ⟨y, hy⟩ : ↥K) : X)) hk
    show y * ((k : X)⁻¹ * x) = ((k : X)⁻¹ * x) * y
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = ((k : X)⁻¹ * x) * y := by group
  obtain ⟨i, hi⟩ := zmod_six_aux (Θ (actK hBN ⟨b, hb⟩)) (Θ (actK hBN ⟨x, hxB⟩))
    (hcube ⟨b, hb⟩) (hcube ⟨x, hxB⟩) hxne
  refine ⟨(i : ℕ), ?_⟩
  have hmem : actK hBN (⟨x, hxB⟩ ^ (i : ℕ) * ⟨b, hb⟩) ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    calc Θ (actK hBN (⟨x, hxB⟩ ^ (i : ℕ) * ⟨b, hb⟩))
        = Θ (actK hBN ⟨x, hxB⟩) ^ (i : ℕ) * Θ (actK hBN ⟨b, hb⟩) := by
          simp only [map_mul, map_pow]
      _ = Θ (actK hBN ⟨b, hb⟩) * Θ (actK hBN ⟨x, hxB⟩) ^ (i : ℕ) :=
          mul_comm (Θ (actK hBN ⟨x, hxB⟩) ^ (i : ℕ)) (Θ (actK hBN ⟨b, hb⟩))
      _ = 1 := hi
  obtain ⟨k, hk⟩ := hΘ hmem
  refine ⟨k, k.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : (k : X) * y * (k : X)⁻¹ = (x ^ (i : ℕ) * b) * y * (x ^ (i : ℕ) * b)⁻¹ := by
    have := congrArg (fun β : MulAut ↥K => ((β ⟨y, hy⟩ : ↥K) : X)) hk
    simpa [coe_actK] using this
  show y * ((k : X)⁻¹ * (x ^ (i : ℕ) * b)) = ((k : X)⁻¹ * (x ^ (i : ℕ) * b)) * y
  calc y * ((k : X)⁻¹ * (x ^ (i : ℕ) * b))
      = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * (x ^ (i : ℕ) * b) := by group
    _ = (k : X)⁻¹ * ((x ^ (i : ℕ) * b) * y * (x ^ (i : ℕ) * b)⁻¹) * (x ^ (i : ℕ) * b) := by
        rw [h1]
    _ = ((k : X)⁻¹ * (x ^ (i : ℕ) * b)) * y := by group

end Act

@[expose] def F4OutStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → IsLieQuot Y IsF4EightIndex →
    Subgroup.center Y = ⊥ ∧ ∃ Θ : MulAut Y →* Multiplicative (ZMod (2 * 3)),
      Θ.ker ≤ (MulAut.conj : Y →* MulAut Y).range

@[expose] def F4TwoNoNineteen : Prop :=
  ∀ (F : Type) [Group F] [Finite F], IsSimpleGroup F → CFSG.Open.IsQuasisimple F →
    IsLieQuot F Bal209F4Aux.IsF4TwoIndex → ¬ 19 ∣ Nat.card F

theorem nineteen_dvd_card {J : Type} [Group J] [Finite J]
    (h : IsLieQuot J KSF4SU3.IsU3EightIndexTwo) : 19 ∣ Nat.card J := by
  obtain ⟨⟨d, hv⟩, ⟨q, hq, rfl⟩, ⟨φ⟩⟩ := h
  obtain ⟨hp2, he3⟩ := hq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv φ
  rw [hp2, he3] at hm
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hm
  let _ := hfield
  let _ := hfinite
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd (K := K) Nat.prime_two
    (by norm_num : 1 ≤ 3) hK
  have h1 : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (StatedProj (StatedSU 3 (2 ^ 3) K)) := Nat.card_congr e.toEquiv
  have h19 : 19 ∣ Nat.card (StatedProj (StatedSU 3 (2 ^ 3) K)) := by
    have hgcd : Nat.gcd 3 (2 ^ 3 + 1) = 3 := by norm_num
    rw [hgcd] at hcard
    have : 19 ∣ Nat.card (StatedProj (StatedSU 3 (2 ^ 3) K)) * 3 := by
      rw [hcard]; norm_num
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) this)
  rw [← Subgroup.card_mul_index (Subgroup.center J), Subgroup.index_eq_card]
  exact Dvd.dvd.mul_left (h1 ▸ h19) _

section Main

variable {X : Type} [Group X] {K : Subgroup X}

theorem conj_eq_of_inner {k b : X} (hkc : k⁻¹ * b ∈ Subgroup.centralizer (K : Set X)) {y : X}
    (hy : y ∈ K) : b * y * b⁻¹ = k * y * k⁻¹ := by
  have hcy : (k⁻¹ * b) * y = y * (k⁻¹ * b) := (Subgroup.mem_centralizer_iff.1 hkc y hy).symm
  calc b * y * b⁻¹ = (k * (k⁻¹ * b)) * y * (k * (k⁻¹ * b))⁻¹ := by rw [mul_inv_cancel_left]
    _ = k * ((k⁻¹ * b) * y) * (k⁻¹ * b)⁻¹ * k⁻¹ := by group
    _ = k * (y * (k⁻¹ * b)) * (k⁻¹ * b)⁻¹ * k⁻¹ := by rw [hcy]
    _ = k * y * k⁻¹ := by group

theorem innerAt_of_conj_eq {k b : X} (hk : k ∈ K)
    (h : ∀ y : X, y ∈ K → b * y * b⁻¹ = k * y * k⁻¹) : Bal209F4Aux.InnerAt K b := by
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := h y hy
  show y * (k⁻¹ * b) = (k⁻¹ * b) * y
  calc y * (k⁻¹ * b) = k⁻¹ * (k * y * k⁻¹) * b := by group
    _ = k⁻¹ * (b * y * b⁻¹) * b := by rw [h1]
    _ = (k⁻¹ * b) * y := by group

theorem fixSubgroup_conj_eq' {P : Type*} [Group P] (x : P) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set P) := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]; group

end Main

end KSF4Rank

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
