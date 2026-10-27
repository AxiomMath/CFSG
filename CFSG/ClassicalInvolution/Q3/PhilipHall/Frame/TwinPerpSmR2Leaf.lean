module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmR2Out
public import CFSG.Holt.H78.Sec4Prop46A
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallFam

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
  CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem q8_pow_four : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide

theorem q8_sq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 ∨ x ^ 2 = QuaternionGroup.a 2 := by decide

theorem q8_comm :
    ∀ x y : QuaternionGroup 2, x * y = y * x ∨ x * y = QuaternionGroup.a 2 * (y * x) := by
  decide

theorem q8_center :
    ∀ x : QuaternionGroup 2, QuaternionGroup.a 2 * x = x * QuaternionGroup.a 2 := by
  decide

theorem q8_orderOf_four {x : QuaternionGroup 2} (hx : x ^ 2 ≠ 1) : orderOf x = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hx) (by simpa using q8_pow_four x)

theorem q8_isPGroup : IsPGroup 2 (QuaternionGroup 2) :=
  IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num)

theorem eq_one_of_mem_oddCoreOf {Y : Type} [Group Y] [Finite Y] {J V : Subgroup Y}
    (hV : IsPGroup 2 V) {w : Y} (hwV : w ∈ V) (hwJ : w ∈ oddCoreOf J) : w = 1 := by
  obtain ⟨w', hw', rfl⟩ := hwJ
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥J)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥J
  have h1 : orderOf w' ∣ Nat.card (classicalInvolutionOddCore ↥J) :=
    Subgroup.orderOf_dvd_natCard _ hw'
  have h2 : orderOf (J.subtype w') = orderOf w' := orderOf_injective _ J.subtype_injective w'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hV) ⟨_, hwV⟩
  rw [Subgroup.orderOf_mk, h2] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    have h3 : 2 ∣ orderOf w' := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h1)) (even_iff_two_dvd.mpr h3)
  rw [hk0, pow_zero] at hk
  rw [orderOf_eq_one_iff] at hk
  rw [hk, map_one]

section RankArgument

variable {Y : Type} [Group Y]

theorem eq_of_rankLeTwo {O : Type*} [Group O] (h : RankLeTwo O) {x y z : O} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hz : z ^ 2 = 1) (hxy : x * y = y * x) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) (hne : x ≠ y) :
    z = x ∨ z = y ∨ z = x * y := by
  rcases h x y z hx hy hz hxy hxz hyz with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd h1 hx1
  · exact absurd h1 hy1
  · exact absurd h1 hz1
  · exact absurd h1 hne
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inl h1.symm)
  · exact Or.inr (Or.inr h1.symm)

theorem false_of_e8 {T : Subgroup Y} {t : Y} (ht1 : t ≠ 1) (htT : t ∈ T)
    (hcent : RankLeTwo ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)))
    {φ φ' : QuaternionGroup 2 →* Y} (hφt : φ (QuaternionGroup.a 2) = t)
    (hφ't : φ' (QuaternionGroup.a 2) = t) (hcomm : ∀ x y, φ x * φ' y = φ' y * φ x)
    (hsep : ∀ q q', q ^ 2 ≠ 1 → φ q ≠ φ' q') {c d : QuaternionGroup 2}
    (hc : c ^ 2 = QuaternionGroup.a 2) (hd : d ^ 2 = QuaternionGroup.a 2)
    (hcd : c * d = QuaternionGroup.a 2 * (d * c)) (h1 : (d⁻¹ * c) ^ 2 ≠ 1)
    (h2 : (d⁻¹ * (QuaternionGroup.a 2 * c)) ^ 2 ≠ 1)
    (hx : φ c * (φ' (QuaternionGroup.a 1))⁻¹ ∈ T)
    (hy : φ d * (φ' (QuaternionGroup.xa 0))⁻¹ ∈ T) : False := by
  set z : QuaternionGroup 2 := QuaternionGroup.a 2 with hz
  set a : QuaternionGroup 2 := QuaternionGroup.a 1 with ha
  set b : QuaternionGroup 2 := QuaternionGroup.xa 0 with hb
  have hc1 : c ^ 2 ≠ 1 := by rw [hc, hz]; decide
  have hd1 : d ^ 2 ≠ 1 := by rw [hd, hz]; decide
  have haa : a * a = z := by rw [ha, hz]; decide
  have hbb : b * b = z := by rw [hb, hz]; decide
  have hba : b * a = z * (a * b) := by rw [ha, hb, hz]; decide
  have hzz : z * z = 1 := by rw [hz]; decide
  have hcomm' : ∀ p q, (φ' p)⁻¹ * φ q = φ q * (φ' p)⁻¹ := by
    intro p q
    have := hcomm q p
    calc (φ' p)⁻¹ * φ q = (φ' p)⁻¹ * (φ q * φ' p) * (φ' p)⁻¹ := by group
      _ = (φ' p)⁻¹ * (φ' p * φ q) * (φ' p)⁻¹ := by rw [this]
      _ = φ q * (φ' p)⁻¹ := by group
  have hmul : ∀ p p' q q', (φ p * (φ' p')⁻¹) * (φ q * (φ' q')⁻¹) =
      φ (p * q) * (φ' (q' * p'))⁻¹ := by
    intro p p' q q'
    calc (φ p * (φ' p')⁻¹) * (φ q * (φ' q')⁻¹) = φ p * ((φ' p')⁻¹ * φ q) * (φ' q')⁻¹ := by
          group
      _ = φ p * (φ q * (φ' p')⁻¹) * (φ' q')⁻¹ := by rw [hcomm']
      _ = φ (p * q) * (φ' (q' * p'))⁻¹ := by rw [map_mul, map_mul]; group
  have htc : ∀ q, t * φ q = φ q * t := fun q => by
    rw [← hφt, ← map_mul, ← map_mul, hz, q8_center]
  have htc' : ∀ q, t * φ' q = φ' q * t := fun q => by
    rw [← hφ't, ← map_mul, ← map_mul, hz, q8_center]
  have htt : t * t = 1 := by rw [← hφt, ← map_mul, hzz, map_one]
  have htw : ∀ p p', t * (φ p * (φ' p')⁻¹) = (φ p * (φ' p')⁻¹) * t := by
    intro p p'
    have h3 : t * (φ' p')⁻¹ = (φ' p')⁻¹ * t := by
      have := htc' p'
      calc t * (φ' p')⁻¹ = (φ' p')⁻¹ * (φ' p' * t) * (φ' p')⁻¹ := by group
        _ = (φ' p')⁻¹ * (t * φ' p') * (φ' p')⁻¹ := by rw [this]
        _ = (φ' p')⁻¹ * t := by group
    calc t * (φ p * (φ' p')⁻¹) = (t * φ p) * (φ' p')⁻¹ := by group
      _ = φ p * (t * (φ' p')⁻¹) := by rw [htc]; group
      _ = φ p * ((φ' p')⁻¹ * t) := by rw [h3]
      _ = (φ p * (φ' p')⁻¹) * t := by group
  set x := φ c * (φ' a)⁻¹ with hxdef
  set y := φ d * (φ' b)⁻¹ with hydef
  have hxx : x * x = 1 := by
    rw [hxdef, hmul, ← pow_two, hc, haa, hφt, hφ't, mul_inv_cancel]
  have hyy : y * y = 1 := by
    rw [hydef, hmul, ← pow_two, hd, hbb, hφt, hφ't, mul_inv_cancel]
  have hxy : x * y = y * x := by
    rw [hxdef, hydef, hmul, hmul, hcd, hba, map_mul φ z (d * c), map_mul φ' z (a * b), hφt, hφ't]
    have := htw (d * c) (a * b)
    calc t * φ (d * c) * (t * φ' (a * b))⁻¹ = (t * (φ (d * c) * (φ' (a * b))⁻¹)) * t⁻¹ := by
          group
      _ = φ (d * c) * (φ' (a * b))⁻¹ := by rw [this]; group
  have hmemC : ∀ w, t * w = w * t → w ∈ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr hw.symm
  let tt : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) := ⟨t, htT, hmemC t rfl⟩
  let xx : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) := ⟨x, hx, hmemC x (htw c a)⟩
  let yy : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) := ⟨y, hy, hmemC y (htw d b)⟩
  have sq : ∀ {w : Y} (hw : w ∈ T ⊓ Subgroup.centralizer ({t} : Set Y)), w * w = 1 →
      (⟨w, hw⟩ : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y))) ^ 2 = 1 := fun hw h => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact h
  have cm : ∀ {v w : Y} (hv : v ∈ T ⊓ Subgroup.centralizer ({t} : Set Y))
      (hw : w ∈ T ⊓ Subgroup.centralizer ({t} : Set Y)), v * w = w * v →
      (⟨v, hv⟩ : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y))) * ⟨w, hw⟩ = ⟨w, hw⟩ * ⟨v, hv⟩ :=
    fun _ _ h => Subtype.ext h
  rcases hcent tt xx yy (sq _ htt) (sq _ hxx) (sq _ hyy) (cm _ _ (htw c a)) (cm _ _ (htw d b))
      (cm _ _ hxy) with e | e | e | e | e | e | e
  · exact ht1 (congrArg Subtype.val e)
  ·
    have e' : x = 1 := congrArg Subtype.val e
    exact hsep c a hc1 (mul_inv_eq_one.mp e')
  ·
    have e' : y = 1 := congrArg Subtype.val e
    exact hsep d b hd1 (mul_inv_eq_one.mp e')
  ·
    have e' : t = x := congrArg Subtype.val e
    refine hsep c (z * a) hc1 ?_
    calc φ c = x * φ' a := by rw [hxdef]; group
      _ = φ' (z * a) := by rw [← e', map_mul, hφ't]
  ·
    have e' : t = y := congrArg Subtype.val e
    refine hsep d (z * b) hd1 ?_
    calc φ d = y * φ' b := by rw [hydef]; group
      _ = φ' (z * b) := by rw [← e', map_mul, hφ't]
  ·
    have e' : x = y := congrArg Subtype.val e
    refine hsep (d⁻¹ * c) (b⁻¹ * a) h1 ?_
    calc φ (d⁻¹ * c) = (φ d)⁻¹ * x * φ' a := by rw [hxdef, map_mul, map_inv]; group
      _ = (φ d)⁻¹ * y * φ' a := by rw [e']
      _ = φ' (b⁻¹ * a) := by rw [hydef, map_mul, map_inv]; group
  ·
    have e' : t * x = y := congrArg Subtype.val e
    refine hsep (d⁻¹ * (z * c)) (b⁻¹ * a) h2 ?_
    calc φ (d⁻¹ * (z * c)) = (φ d)⁻¹ * (t * x) * φ' a := by
          rw [hxdef, map_mul, map_mul, map_inv, hφt]; group
      _ = (φ d)⁻¹ * y * φ' a := by rw [e']
      _ = φ' (b⁻¹ * a) := by rw [hydef, map_mul, map_inv]; group

theorem false_of_twin_q8 {T : Subgroup Y} [T.Normal]
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) {t : Y} (ht1 : t ≠ 1) (htT : t ∈ T)
    (hout : RankLeTwo (Outer ↥T)) (hcent : RankLeTwo ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)))
    {φ φ' : QuaternionGroup 2 →* Y} (hφt : φ (QuaternionGroup.a 2) = t)
    (hφ't : φ' (QuaternionGroup.a 2) = t) (hcomm : ∀ x y, φ x * φ' y = φ' y * φ x)
    (hsep : ∀ q q', q ^ 2 ≠ 1 → φ q ≠ φ' q') (hb : ∀ q, q ^ 2 ≠ 1 → φ q ∉ T)
    (hb' : ∀ q, q ^ 2 ≠ 1 → φ' q ∉ T) : False := by
  set π := outerHom T with hπdef
  have hπ : ∀ w, π w = 1 ↔ w ∈ T := fun w => outerHom_eq_one_iff hC
  have hπt : π t = 1 := (hπ t).mpr htT
  have sq1 : ∀ (ψ : QuaternionGroup 2 →* Y), ψ (QuaternionGroup.a 2) = t →
      ∀ q, π (ψ q) ^ 2 = 1 := by
    intro ψ hψ q
    rw [← map_pow, ← map_pow]
    rcases q8_sq q with h | h
    · rw [h, map_one, map_one]
    · rw [h, hψ, hπt]
  have cm1 : ∀ (ψ : QuaternionGroup 2 →* Y), ψ (QuaternionGroup.a 2) = t →
      ∀ q q', π (ψ q) * π (ψ q') = π (ψ q') * π (ψ q) := by
    intro ψ hψ q q'
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    rcases q8_comm q q' with h | h
    · rw [h]
    · rw [h, map_mul, map_mul, hψ, hπt, one_mul]
  have cmx : ∀ q q', π (φ q) * π (φ' q') = π (φ' q') * π (φ q) := by
    intro q q'
    rw [← map_mul, ← map_mul, hcomm]
  have ne1 : ∀ (ψ : QuaternionGroup 2 →* Y), (∀ q, q ^ 2 ≠ 1 → ψ q ∉ T) →
      ∀ q, q ^ 2 ≠ 1 → π (ψ q) ≠ 1 := fun ψ hψ q hq h => hψ q hq ((hπ _).mp h)
  have neq : ∀ (ψ : QuaternionGroup 2 →* Y), (∀ q, q ^ 2 ≠ 1 → ψ q ∉ T) →
      ∀ q q', (q * q'⁻¹) ^ 2 ≠ 1 → π (ψ q) ≠ π (ψ q') := by
    intro ψ hψ q q' hq h
    apply ne1 ψ hψ _ hq
    rw [map_mul, map_inv, map_mul, map_inv, h, mul_inv_cancel]
  set a : QuaternionGroup 2 := QuaternionGroup.a 1 with ha
  set b : QuaternionGroup 2 := QuaternionGroup.xa 0 with hb2
  have hsa : a ^ 2 ≠ 1 := by rw [ha]; decide
  have hsb : b ^ 2 ≠ 1 := by rw [hb2]; decide
  have hsab : (a * b⁻¹) ^ 2 ≠ 1 := by rw [ha, hb2]; decide
  have hmatch : ∀ q', q' ^ 2 ≠ 1 → ∃ c : QuaternionGroup 2, (c = a ∨ c = b ∨ c = a * b) ∧
      φ c * (φ' q')⁻¹ ∈ T := by
    intro q' hq'
    rcases eq_of_rankLeTwo hout (sq1 φ hφt a) (sq1 φ hφt b) (sq1 φ' hφ't q') (cm1 φ hφt a b)
        (cmx a q') (cmx b q') (ne1 φ hb a hsa) (ne1 φ hb b hsb) (ne1 φ' hb' q' hq')
        (neq φ hb a b hsab) with h | h | h
    · exact ⟨a, Or.inl rfl, (hπ _).mp (by rw [map_mul, map_inv, h, mul_inv_cancel])⟩
    · exact ⟨b, Or.inr (Or.inl rfl), (hπ _).mp (by rw [map_mul, map_inv, h, mul_inv_cancel])⟩
    · exact ⟨a * b, Or.inr (Or.inr rfl),
        (hπ _).mp (by rw [map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel])⟩
  obtain ⟨c, hc, hcT⟩ := hmatch a hsa
  obtain ⟨d, hd, hdT⟩ := hmatch b hsb
  have hcd : ∀ e : QuaternionGroup 2, φ e * (φ' a)⁻¹ ∈ T → φ e * (φ' b)⁻¹ ∈ T → False := by
    intro e h1 h2
    have h3 : (φ e * (φ' b)⁻¹)⁻¹ * (φ e * (φ' a)⁻¹) ∈ T := T.mul_mem (T.inv_mem h2) h1
    have h4 : (φ e * (φ' b)⁻¹)⁻¹ * (φ e * (φ' a)⁻¹) = φ' (b * a⁻¹) := by
      rw [map_mul, map_inv]; group
    rw [h4] at h3
    exact hb' (b * a⁻¹) (by rw [ha, hb2]; decide) h3
  have e8 := fun {c d : QuaternionGroup 2} (hc : c ^ 2 = QuaternionGroup.a 2)
      (hd : d ^ 2 = QuaternionGroup.a 2) (hcd : c * d = QuaternionGroup.a 2 * (d * c))
      (h1 : (d⁻¹ * c) ^ 2 ≠ 1) (h2 : (d⁻¹ * (QuaternionGroup.a 2 * c)) ^ 2 ≠ 1)
      (hx : φ c * (φ' (QuaternionGroup.a 1))⁻¹ ∈ T)
      (hy : φ d * (φ' (QuaternionGroup.xa 0))⁻¹ ∈ T) =>
    false_of_e8 ht1 htT hcent hφt hφ't hcomm hsep hc hd hcd h1 h2 hx hy
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · exact hcd _ hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact hcd _ hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact e8 (by decide) (by decide) (by decide) (by decide) (by decide) hcT hdT
  · exact hcd _ hcT hdT

end RankArgument

theorem fusionIsSylowIn_conjSub {Y : Type} [Group Y] {P K : Subgroup Y}
    (h : fusionIsSylowIn 2 P K) (g : Y) : fusionIsSylowIn 2 (conjSub g P) (conjSub g K) := by
  refine ⟨conjSub_mono h.1, h.2.1.map (MulAut.conj g).toMonoidHom, fun P' hP'K hP'2 hle => ?_⟩
  have h1 : conjSub g⁻¹ P' ≤ K := by
    have := conjSub_mono (n := g⁻¹) hP'K
    rwa [conjSub_inv_conjSub] at this
  have h2 : P ≤ conjSub g⁻¹ P' := by
    have := conjSub_mono (n := g⁻¹) hle
    rwa [conjSub_inv_conjSub] at this
  have h3 := h.2.2 _ h1 (hP'2.map (MulAut.conj g⁻¹).toMonoidHom) h2
  rw [← h3, conjSub_conjSub_inv]


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_twin_q8 (h : PerpHypS n Y R S t) {φ : QuaternionGroup 2 →* Y}
    (hφ : Function.Injective φ) (hφK : ∀ x, φ x ∈ tightCore R) :
    ∃ (φ' : QuaternionGroup 2 →* Y) (c : Y), (∀ x, φ' x = c * φ x * c⁻¹) ∧
      φ' (QuaternionGroup.a 2) = t ∧ (∀ x y, φ x * φ' y = φ' y * φ x) ∧
      ∀ q q', q ^ 2 ≠ 1 → φ q ≠ φ' q' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hne, hK'Ω, hz'⟩ := exists_twin h
  set K := tightCore R with hKdef
  set K' := conjSub g K with hK'def
  have hz : IsUniqueInvolution K t := uniqueInv_core h
  have hΩ := h.core.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self _
  have hcomm : ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' :=
    Sec6Gen.comm_le_oddCore_of_twin hΩ hKΩ hK'Ω (Ne.symm hne) hz hz'
  have key : ∀ k ∈ K, ∀ y ∈ K', k * y * k⁻¹ ∈ K' := by
    intro k hk y hy
    have h1 : ⁅k, y⁆ ∈ oddCoreOf K' :=
      (Subgroup.mem_inf.mp (hcomm (Subgroup.commutator_mem_commutator hk hy))).2
    have h2 : oddCoreOf K' ≤ K' := Subgroup.map_subtype_le _
    have h3 : k * y * k⁻¹ = ⁅k, y⁆ * y := by rw [commutatorElement_def]; group
    rw [h3]
    exact K'.mul_mem (h2 h1) hy
  have hnorm : K ≤ Subgroup.normalizer (K' : Set Y) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key k hk y, fun hy => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ hy
    simpa [mul_assoc] using this
  set H := Subgroup.normalizer (K' : Set Y) with hH
  have hK'H : K' ≤ H := Subgroup.le_normalizer
  have hK'n : (K'.subgroupOf H).Normal := Subgroup.normal_in_normalizer
  set Q := φ.range with hQ
  have hQ2 : IsPGroup 2 Q := q8_isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hQK : Q ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hφK x
  have hQcard : Nat.card Q = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hSK := h.core.datum.sylow_core
  have hScard : Nat.card ((S : Subgroup R).map R.subtype) = 8 := by
    obtain ⟨e⟩ := h.core.q8
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).toEquiv, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hQsyl : fusionIsSylowIn 2 Q K := hSK.of_natCard_le hQ2 hQK (by rw [hScard, hQcard])
  have hgQ : fusionIsSylowIn 2 (conjSub g Q) K' := fusionIsSylowIn_conjSub hQsyl g
  obtain ⟨V, hQV, hV⟩ := CFSG.Holt.exists_fusionIsSylowIn_ge hQ2 (hQK.trans hnorm)
  have hVK' := CFSG.Holt.H78.fusionIsSylowIn_inf_of_normal_subgroupOf hV hK'H hK'n
  obtain ⟨k, -, hk⟩ := CFSG.Holt.exists_mem_conj_of_fusionIsSylowIn hgQ hVK'
  set c := k * g with hc
  let φ' : QuaternionGroup 2 →* Y := (MulAut.conj c).toMonoidHom.comp φ
  have hφ' : ∀ x, φ' x = c * φ x * c⁻¹ := fun x => rfl
  have hφ'V : ∀ x, φ' x ∈ V ⊓ K' := by
    intro x
    refine (hk _).mpr ?_
    rw [hφ', hc]
    have e : k⁻¹ * (k * g * φ x * (k * g)⁻¹) * k = g * φ x * g⁻¹ := by group
    rw [e]
    exact conj_mem_conjSub ⟨x, rfl⟩
  have hφ'inj : Function.Injective φ' := (MulAut.conj c).injective.comp hφ
  refine ⟨φ', c, hφ', ?_, ?_, ?_⟩
  · have hmem := (Subgroup.mem_inf.mp (hφ'V (QuaternionGroup.a 2))).2
    have hsq : φ' (QuaternionGroup.a 2) * φ' (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, show (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 by
        decide, map_one]
    have hne1 : φ' (QuaternionGroup.a 2) ≠ 1 := by
      intro h1
      have := hφ'inj (h1.trans (map_one φ').symm)
      exact absurd this (by decide)
    exact (hz'.unique _ hmem hsq).resolve_left hne1
  · intro x y
    have hxV : φ x ∈ V := hQV ⟨x, rfl⟩
    have hyV : φ' y ∈ V := (Subgroup.mem_inf.mp (hφ'V y)).1
    have hyK' : φ' y ∈ K' := (Subgroup.mem_inf.mp (hφ'V y)).2
    have h1 : ⁅φ x, φ' y⁆ ∈ oddCoreOf K' :=
      (Subgroup.mem_inf.mp (hcomm (Subgroup.commutator_mem_commutator (hφK x) hyK'))).2
    have h2 : ⁅φ x, φ' y⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hxV hyV) (V.inv_mem hxV)) (V.inv_mem hyV)
    exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_oddCoreOf hV.2.1 h2 h1)
  · intro q q' hq heq
    have hmK : φ q ∈ K := hφK q
    have hmK' : φ q ∈ K' := heq ▸ (Subgroup.mem_inf.mp (hφ'V q')).2
    have hord : orderOf (φ q) = 4 := by
      rw [orderOf_injective φ hφ q]
      exact q8_orderOf_four hq
    have hdvd : 2 ^ 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (Subgroup.mem_inf.mpr ⟨hmK, hmK'⟩)
      rw [hord] at this
      simpa using this
    have h4 := (hΩ.omega4 K hKΩ K' hK'Ω (Ne.symm hne)).1
    have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
    omega

theorem false_of_rank (h : PerpHypS n Y R S t) (hcyc : TwinCyc4 ↥(genFittingFStar Y))
    (hab : SocleOutAbelian ↥(genFittingFStar Y))
    (hout : RankLeTwo (Outer ↥(genFittingFStar Y)))
    (hcent : t ∈ genFittingFStar Y →
      RankLeTwo ↥(genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y))) : False := by
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  set T := genFittingFStar Y with hT
  have hC : Subgroup.centralizer (T : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have hz := uniqueInv_core h
  obtain ⟨φ, hφ, hφK⟩ := exists_q8 h
  have hφt : φ (QuaternionGroup.a 2) = t := by
    have hsq : φ (QuaternionGroup.a 2) * φ (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, show (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 by
        decide, map_one]
    have hne1 : φ (QuaternionGroup.a 2) ≠ 1 := by
      intro h1
      have := hφ (h1.trans (map_one φ).symm)
      exact absurd this (by decide)
    exact (hz.unique _ (hφK _) hsq).resolve_left hne1
  by_cases ha : ∃ q : QuaternionGroup 2, q ^ 2 ≠ 1 ∧ φ q ∈ T
  ·
    obtain ⟨q, hq, hqT⟩ := ha
    refine not_twinPair_of_twinCyc4 hcyc (exists_twinPair_of_u1 h (hφK q) hqT ?_)
    rw [orderOf_injective φ hφ q]
    exact q8_orderOf_four hq
  ·
    push Not at ha
    set π := outerHom T with hπdef
    have hπ : ∀ w, π w = 1 ↔ w ∈ T := fun w => outerHom_eq_one_iff hC
    have htT : t ∈ T := by
      have hP2 : IsPGroup 2 (π.comp φ).range :=
        q8_isPGroup.of_surjective (π.comp φ).rangeRestrict (π.comp φ).rangeRestrict_surjective
      have hab' := (hab _ hP2).is_comm.comm
        (⟨π (φ (QuaternionGroup.a 1)), ⟨QuaternionGroup.a 1, rfl⟩⟩ : (π.comp φ).range)
        ⟨π (φ (QuaternionGroup.xa 0)), ⟨QuaternionGroup.xa 0, rfl⟩⟩
      have h1 : π (φ (QuaternionGroup.a 1)) * π (φ (QuaternionGroup.xa 0)) =
          π (φ (QuaternionGroup.xa 0)) * π (φ (QuaternionGroup.a 1)) := congrArg Subtype.val hab'
      have h2 : π (φ (QuaternionGroup.a 1 * QuaternionGroup.xa 0 * (QuaternionGroup.a 1)⁻¹ *
          (QuaternionGroup.xa 0)⁻¹)) = 1 := by
        simp only [map_mul, map_inv, h1]
        group
      rw [show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
        (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 by decide,
        hφt] at h2
      exact (hπ t).mp h2
    obtain ⟨φ', c, hφ'c, hφ't, hcomm, hsep⟩ := exists_twin_q8 h hφ hφK
    have hb' : ∀ q, q ^ 2 ≠ 1 → φ' q ∉ T := by
      intro q hq hmem
      apply ha q hq
      rw [hφ'c] at hmem
      have := hTn.conj_mem _ hmem c⁻¹
      simpa [mul_assoc] using this
    exact false_of_twin_q8 hC hz.ne_one htT hout (hcent htT) hφt hφ't hcomm hsep ha hb'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem leaf_l2 {n : ℕ} : TwinLeafS n SmallL2 :=
  TwinLeafS.of_no fun _ _ _ _ _ _ h _ hF =>
    R2.false_of_rank h (twinCyc4_l2 hF) (socleOutAbelian_l2 hF) (R2.rankLeTwo_outer_l2 hF)
      (fun htT => R2.rankLeTwo_cent_l2 hF htT h.core.datum.order)

theorem leaf_l3Ne3 {n : ℕ} : TwinLeafS n SmallL3Ne3 :=
  TwinLeafS.of_no fun _ _ _ _ _ _ h _ hF =>
    R2.false_of_rank h (twinCyc4_l3 hF) (socleOutAbelian_l3 hF) (R2.rankLeTwo_outer_l3 hF)
      (fun htT => R2.rankLeTwo_cent_l3 hF htT h.core.datum.order)

theorem leaf_u3Ne3 {n : ℕ} : TwinLeafS n SmallU3Ne3 :=
  TwinLeafS.of_no fun _ _ _ _ _ _ h _ hF => by
    haveI := h.core.simple
    obtain ⟨p, f, -, -, -, -, hm⟩ := id hF
    have hodd : Odd (Nat.gcd 3 (p ^ f + 1)) :=
      (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
    exact false_of_outTwoCyclic_of_noTwinPair h (outTwoCyclic_PSU hm hodd)
      (not_twinPair_of_twinCyc4 (twinCyc4_u3 hF))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
