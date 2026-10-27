module

public import CFSG.CGT.PushingUpLit.A78L3.Base
public import CFSG.CGT.PushingUpLit.A78L3.Heis
public import CFSG.CGT.PushingUpLit.A78.LQ4Core
public import CFSG.CGT.PushingUpLit.A78T2.Cut
public import CFSG.CGT.PushingUpLit.SolK.GenFour

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78.LQ4 CFSG.CGT.PushingUpLit.A78.LQ4Fin
open CFSG.ABGLocalTools
open scoped commutatorElement

namespace GF4

variable {F : Type} [Field F] [CharP F 2]

@[expose] def θ (ω : F) (n : ℕ) : F := ((n % 2 : ℕ) : F) + ((n / 2 % 2 : ℕ) : F) * ω

theorem cast_mod_two (k : ℕ) : ((k % 2 : ℕ) : F) = (k : F) := (CharP.cast_eq_mod F 2 k).symm

theorem xor_bits : ∀ n < 4, ∀ m < 4, (n ^^^ m) % 2 = (n % 2 + m % 2) % 2 ∧
    (n ^^^ m) / 2 % 2 = (n / 2 % 2 + m / 2 % 2) % 2 := by decide

theorem mul4_bits : ∀ n < 4, ∀ m < 4,
    mul4 n m % 2 = (n % 2 * (m % 2) + n / 2 % 2 * (m / 2 % 2)) % 2 ∧
    mul4 n m / 2 % 2 = (n % 2 * (m / 2 % 2) + n / 2 % 2 * (m % 2) +
      n / 2 % 2 * (m / 2 % 2)) % 2 := by decide

theorem θ_xor (ω : F) {n m : ℕ} (hn : n < 4) (hm : m < 4) :
    θ ω (n ^^^ m) = θ ω n + θ ω m := by
  obtain ⟨h1, h2⟩ := xor_bits n hn m hm
  rw [θ, θ, θ, h1, h2, cast_mod_two, cast_mod_two]
  push_cast
  ring

theorem θ_mul4 {ω : F} (hω : ω * ω = ω + 1) {n m : ℕ} (hn : n < 4) (hm : m < 4) :
    θ ω (mul4 n m) = θ ω n * θ ω m := by
  obtain ⟨h1, h2⟩ := mul4_bits n hn m hm
  rw [θ, θ, θ, h1, h2, cast_mod_two, cast_mod_two]
  push_cast
  linear_combination (-(((n / 2 % 2 : ℕ) : F) * ((m / 2 % 2 : ℕ) : F))) * hω

omit [CharP F 2] in
theorem θ_zero (ω : F) : θ ω 0 = 0 := by simp [θ]

theorem θ_eq_zero {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {k : ℕ} (hk : k < 4) (h0 : θ ω k = 0) :
    k = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  interval_cases k
  · rfl
  · simp [θ] at h0
  · simp [θ] at h0; exact absurd h0 hω0
  · exfalso
    simp [θ] at h0
    apply hω1
    linear_combination h0 - h2

theorem θ_injective {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {n m : ℕ} (hn : n < 4) (hm : m < 4)
    (h : θ ω n = θ ω m) : n = m := by
  have hx : n ^^^ m < 4 := by
    have := Nat.xor_lt_two_pow (n := 2) (x := n) (y := m) (by simpa using hn) (by simpa using hm)
    simpa using this
  have h1 : θ ω (n ^^^ m) = 0 := by rw [θ_xor ω hn hm, h, CharTwo.add_self_eq_zero]
  have key : ∀ n < 4, ∀ m < 4, n ^^^ m = 0 → n = m := by decide
  exact key n hn m hm (θ_eq_zero hω0 hω1 hx h1)

end GF4

theorem exists_omega {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω * ω = ω + 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at h1
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨ω, hω0, hω1, ?_⟩
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h4 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd (sub_eq_zero.1 h5) hω1
  · linear_combination h5 - (ω + 1) * h2

section Coords

variable {G : Type} [Group G] [Finite G]

@[expose] def shift2 : Bits 2 →* Bits 4 where
  toFun v := ⟨v.1 * 4, by have := Bits.lt4 v; show v.1 * 4 < 2 ^ 4; norm_num; omega⟩
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    show (a.1 ^^^ b.1) * 4 = a.1 * 4 ^^^ b.1 * 4
    have key : ∀ x < 4, ∀ y < 4, (x ^^^ y) * 4 = x * 4 ^^^ y * 4 := by decide
    exact key _ (Bits.lt4 a) _ (Bits.lt4 b)

@[expose] def low2 (v : Bits 4) : Bits 2 :=
  ⟨v.1 % 4, by have := Nat.mod_lt v.1 (show 0 < 4 by norm_num); simpa using this⟩

@[expose] def high2 (v : Bits 4) : Bits 2 :=
  ⟨v.1 / 4, by have := Bits.lt16 v; show v.1 / 4 < 2 ^ 2; norm_num; omega⟩

theorem low2_val (v : Bits 4) : (low2 v).1 = v.1 % 4 := rfl

theorem high2_val (v : Bits 4) : (high2 v).1 = v.1 / 4 := rfl

theorem bits_lo_hi : ∀ x < 4, ∀ y < 4, ((x ^^^ (y * 4)) &&& 3 = x ∧
    ((x ^^^ (y * 4)) >>> 2) &&& 3 = y) := by decide

theorem mul4_lt : ∀ n < 4, ∀ m < 4, mul4 n m < 4 := by decide

theorem bits_split : ∀ v < 16, v = (v % 4) ^^^ ((v / 4) * 4) := by decide

theorem bits_eq_zero : ∀ x < 4, ∀ y < 4, (x ^^^ (y * 4) = 0 ↔ x = 0 ∧ y = 0) := by decide

end Coords

theorem t2Two : A78T2.T2Two := by
  intro G _ _ L₁ L₂ T e cfg hZ he hns
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst he
  set V := oTwoIn (L₁ ⊔ T) with hV
  set W := oTwoIn (L₂ ⊔ T) with hW
  have P := cfg.l3Pair hZ
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge P.side₁.pT (le_top : T ≤ ⊤)
  have hsw : ∃ s ∈ S, s ∉ T := by
    by_contra hcon
    push Not at hcon
    apply hns
    rw [le_antisymm hTS hcon]
    exact hS
  have base := P.t2Base hS hTS hsw
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  have hF4 : Nat.card (GaloisField 2 2) = 4 := by rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  obtain ⟨ω, hω0, hω1, hω⟩ := exists_omega hF4
  let θ' : Bits 2 → GaloisField 2 2 := fun v => GF4.θ ω v.1
  have hθinj : Function.Injective θ' := fun v w hvw =>
    Subtype.ext (GF4.θ_injective hω0 hω1 (Bits.lt4 v) (Bits.lt4 w) hvw)
  have hθbij : Function.Bijective θ' := by
    refine (Function.Injective.bijective_of_nat_card_le hθinj ?_)
    rw [hF4, Bits.card_eq]
    norm_num
  let enc : GaloisField 2 2 ≃ Bits 2 := (Equiv.ofBijective θ' hθbij).symm
  have hθenc : ∀ x, θ' (enc x) = x := fun x => (Equiv.ofBijective θ' hθbij).apply_symm_apply x
  have henc_add : ∀ x y, enc (x + y) = enc x * enc y := by
    intro x y
    apply hθinj
    rw [hθenc]
    show x + y = GF4.θ ω ((enc x).1 ^^^ (enc y).1)
    rw [GF4.θ_xor ω (Bits.lt4 _) (Bits.lt4 _)]
    exact congrArg₂ (· + ·) (hθenc x).symm (hθenc y).symm
  have henc_mul : ∀ x y, (enc (x * y)).1 = mul4 (enc x).1 (enc y).1 := by
    intro x y
    have h1 : θ' (enc (x * y)) = GF4.θ ω (mul4 (enc x).1 (enc y).1) := by
      rw [hθenc, GF4.θ_mul4 hω (Bits.lt4 _) (Bits.lt4 _)]
      exact congrArg₂ (· * ·) (hθenc x).symm (hθenc y).symm
    have hlt : mul4 (enc x).1 (enc y).1 < 4 := mul4_lt _ (Bits.lt4 _) _ (Bits.lt4 _)
    exact GF4.θ_injective hω0 hω1 (Bits.lt4 _) hlt h1
  have henc0 : enc 0 = 1 := by
    apply hθinj
    rw [hθenc]
    exact (GF4.θ_zero ω).symm
  set J := (V ⊔ W).subgroupOf S with hJdef
  have hJn : J.Normal := base.normal_J
  have hJS : V ⊔ W ≤ S := base.J_le.trans hTS
  have hmemJ : ∀ j : ↥J, ((j : ↥S) : G) ∈ V ⊔ W := fun j => j.2
  have hab0 : ∀ x ∈ V ⊔ W, (fr.a x = 0 ∧ fr.b x = 0 ↔ x ∈ V ⊓ W) := by
    intro x hx
    rw [← fr.mem_W_iff_a hx, ← fr.mem_V_iff_b hx]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  let ε : ↥J →* Bits 4 :=
    { toFun := fun j => incl (enc (fr.a ((j : ↥S) : G))) * shift2 (enc (fr.b ((j : ↥S) : G)))
      map_one' := by
        show incl (enc (fr.a 1)) * shift2 (enc (fr.b 1)) = 1
        have ha : fr.a 1 = 0 := (fr.mem_W_iff_a (Subgroup.one_mem _)).1 (Subgroup.one_mem _)
        have hb : fr.b 1 = 0 := (fr.mem_V_iff_b (Subgroup.one_mem _)).1 (Subgroup.one_mem _)
        rw [ha, hb, henc0, map_one, map_one, one_mul]
      map_mul' := fun j k => by
        show incl (enc (fr.a (((j : ↥S) : G) * ((k : ↥S) : G)))) *
            shift2 (enc (fr.b (((j : ↥S) : G) * ((k : ↥S) : G)))) = _
        rw [fr.a_mul (hmemJ j) (hmemJ k), fr.b_mul (hmemJ j) (hmemJ k), henc_add, henc_add,
          map_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hεval : ∀ j : ↥J, (ε j).1 = (enc (fr.a ((j : ↥S) : G))).1 ^^^
      ((enc (fr.b ((j : ↥S) : G))).1 * 4) := fun j => rfl
  have hεker : ∀ j : ↥J, ε j = 1 ↔ ((j : ↥S) : G) ∈ V ⊓ W := by
    intro j
    rw [← hab0 _ (hmemJ j)]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      rw [hεval, Bits.val_one, bits_eq_zero _ (Bits.lt4 _) _ (Bits.lt4 _)] at h2
      refine ⟨?_, ?_⟩
      · have : enc (fr.a ((j : ↥S) : G)) = enc 0 := by rw [henc0]; exact Subtype.ext h2.1
        exact enc.injective this
      · have : enc (fr.b ((j : ↥S) : G)) = enc 0 := by rw [henc0]; exact Subtype.ext h2.2
        exact enc.injective this
    · rintro ⟨h1, h2⟩
      apply Subtype.ext
      rw [hεval, h1, h2, henc0, Bits.val_one]
      rfl
  have hcen : ∀ j : ↥J, j ∈ Subgroup.center ↥J ↔ ((j : ↥S) : G) ∈ V ⊓ W := by
    intro j
    rw [← P.side₁.jst.center_eq, Subgroup.mem_center_iff]
    constructor
    · intro hc
      refine ⟨hmemJ j, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have := congrArg (fun z : ↥J => ((z : ↥S) : G)) (hc ⟨⟨y, hJS hy⟩, hy⟩)
      exact this
    · rintro ⟨-, hc⟩ g
      apply Subtype.ext; apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hc _ (hmemJ g)
  have hker : ε.ker = Subgroup.center ↥J := by
    ext j
    rw [MonoidHom.mem_ker, hεker, hcen]
  let ηh : ε.ker →* Bits 2 :=
    { toFun := fun z => enc (fr.c (((z : ↥J) : ↥S) : G))
      map_one' := by
        show enc (fr.c 1) = 1
        rw [fr.c_one, henc0]
      map_mul' := fun z z' => by
        show enc (fr.c ((((z : ↥J) : ↥S) : G) * (((z' : ↥J) : ↥S) : G))) = _
        rw [fr.c_mul ((hεker _).1 z.2) ((hεker _).1 z'.2), henc_add] }
  have hηbij : Function.Bijective ηh := by
    refine ⟨fun z z' hzz => ?_, fun v => ?_⟩
    · have h1 : fr.c (((z : ↥J) : ↥S) : G) = fr.c (((z' : ↥J) : ↥S) : G) := enc.injective hzz
      have h2 := fr.c_inj ((hεker _).1 z.2) ((hεker _).1 z'.2) h1
      exact Subtype.ext (Subtype.ext (Subtype.ext h2))
    · obtain ⟨z, hz, hzc⟩ := fr.c_surj (enc.symm v)
      have hzJ : z ∈ V ⊔ W := Subgroup.mem_sup_left hz.1
      let zJ : ↥J := ⟨⟨z, hJS hzJ⟩, hzJ⟩
      have hzk : zJ ∈ ε.ker := (hεker zJ).2 hz
      refine ⟨⟨zJ, hzk⟩, ?_⟩
      show enc (fr.c z) = v
      rw [hzc, Equiv.apply_symm_apply]
  let η : ε.ker ≃* Bits 2 := MulEquiv.ofBijective ηh hηbij
  have hεsurj : Function.Surjective ε := by
    intro v
    obtain ⟨x, hxJ, hxa, hxb⟩ := fr.surj_ab (enc.symm (low2 v)) (enc.symm (high2 v))
    refine ⟨⟨⟨x, hJS hxJ⟩, hxJ⟩, Subtype.ext ?_⟩
    show (enc (fr.a x)).1 ^^^ ((enc (fr.b x)).1 * 4) = v.1
    have e1 : (enc (fr.a x)).1 = v.1 % 4 := by
      rw [hxa, Equiv.apply_symm_apply, low2_val]
    have e2 : (enc (fr.b x)).1 = v.1 / 4 := by
      rw [hxb, Equiv.apply_symm_apply, high2_val]
    rw [e1, e2]
    exact (bits_split v.1 (Bits.lt16 v)).symm
  let c : Coords ↥J :=
    { ε := ε
      surj := hεsurj
      ker_eq := hker
      η := η
      sq := fun j hj => by
        show (enc (fr.c ((((⟨j ^ 2, hj⟩ : ε.ker) : ↥J) : ↥S) : G))).1 = qv (ε j).1
        have e1 : ((((⟨j ^ 2, hj⟩ : ε.ker) : ↥J) : ↥S) : G) =
            ((j : ↥S) : G) * ((j : ↥S) : G) := by
          simp [pow_two]
        rw [e1, fr.c_sq (hmemJ j), henc_mul, qv, hεval,
          (bits_lo_hi _ (Bits.lt4 _) _ (Bits.lt4 _)).1,
          (bits_lo_hi _ (Bits.lt4 _) _ (Bits.lt4 _)).2] }
  have hF : ∀ s : ↥S, (∀ j : ↥J, c.ε (MulAut.conjNormal s j) = c.ε j) → s ∈ J := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    refine base.cent_S s s.2 fun j hj => ?_
    have h1 := hs ⟨⟨j, hJS hj⟩, hj⟩
    have h2 : c.ε (MulAut.conjNormal s ⟨⟨j, hJS hj⟩, hj⟩ * (⟨⟨j, hJS hj⟩, hj⟩ : ↥J)⁻¹) = 1 := by
      rw [map_mul, h1, map_inv, mul_inv_cancel]
    have h3 := (hεker _).1 h2
    have e1 : (((MulAut.conjNormal s ⟨⟨j, hJS hj⟩, hj⟩ * (⟨⟨j, hJS hj⟩, hj⟩ : ↥J)⁻¹ : ↥J) :
        ↥S) : G) = ⁅(s : G), j⁆ := by
      simp [commutatorElement_def, MulAut.conjNormal_apply, mul_assoc]
    rwa [e1] at h3
  have hSp : IsPGroup 2 ↥S := hS.isPGroup
  have hno := noE32_of_coords hSp c hF
  have hdvd : ¬ 2 ∣ S.index := by
    have h1 := (isSylowOf_iff.1 hS).2.2
    rwa [Subgroup.relIndex_top_right] at h1
  let Q : Sylow 2 G := hSp.toSylow hdvd
  have hQ : (Q : Subgroup G) = S := IsPGroup.toSylow_coe hSp hdvd
  refine CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow Q ?_
  rw [hQ]
  intro R hR
  exact CFSG.OddStandard.Harada75.gen4_of_noE32 hSp hno R

end CFSG.CGT.PushingUpLit.A78L3
