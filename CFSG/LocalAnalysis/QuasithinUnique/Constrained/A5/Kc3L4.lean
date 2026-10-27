module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.A5.Kc3L4

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank

theorem eq_one_of_smul_eq {F : Type} [Field F] (g : GL (Fin 4) F)
    (h : ∀ w : Fin 4 → F, g • w = w) : g = 1 := by
  ext i j
  have h2 : (g : Matrix (Fin 4) (Fin 4) F).mulVec (Pi.single j 1) = Pi.single j 1 := h _
  rw [Matrix.mulVec_single_one] at h2
  have := congrFun h2 i
  simpa [Pi.single_apply, Matrix.one_apply] using this

theorem card_fun_four {F : Type} (hF : Nat.card F = 2) : Nat.card (Fin 4 → F) = 16 := by
  rw [Nat.card_fun, hF]
  simp

@[expose] def fixedAdd {F : Type} [Field F] (S : Set (GL (Fin 4) F)) : AddSubgroup (Fin 4 → F) where
  carrier := {w | ∀ g ∈ S, g • w = w}
  add_mem' := by
    intro a b ha hb g hg
    have h1 : g • a = a := ha g hg
    have h2 : g • b = b := hb g hg
    show (g : Matrix (Fin 4) (Fin 4) F).mulVec (a + b) = a + b
    rw [Matrix.mulVec_add]
    exact congrArg₂ (· + ·) h1 h2
  zero_mem' := by
    intro g _
    show (g : Matrix (Fin 4) (Fin 4) F).mulVec 0 = 0
    simp
  neg_mem' := by
    intro a ha g hg
    have h1 : g • a = a := ha g hg
    show (g : Matrix (Fin 4) (Fin 4) F).mulVec (-a) = -a
    rw [Matrix.mulVec_neg]
    exact congrArg Neg.neg h1

theorem mem_fixedAdd {F : Type} [Field F] {S : Set (GL (Fin 4) F)} {w : Fin 4 → F} :
    w ∈ fixedAdd S ↔ ∀ g ∈ S, g • w = w := Iff.rfl

theorem card_fixedAdd_dvd {F : Type} [Field F] (hF : Nat.card F = 2) (S : Set (GL (Fin 4) F)) :
    Nat.card (fixedAdd S) ∣ 16 := by
  have := AddSubgroup.card_addSubgroup_dvd_card (fixedAdd S)
  rwa [card_fun_four hF] at this

theorem eq_one_or_sixteen {n : ℕ} (h : n ∣ 16) (h5 : n ≡ 1 [MOD 5]) : n = 1 ∨ n = 16 := by
  have hle : n ≤ 16 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> simp_all [Nat.ModEq]

@[expose, instance_reducible] def actOn {F : Type} [Field F] (A : Subgroup (GL (Fin 4) F))
    (C : AddSubgroup (Fin 4 → F)) (h : ∀ a ∈ A, ∀ c ∈ C, a • c ∈ C) : MulAction A C where
  smul a c := ⟨(a : GL (Fin 4) F) • (c : Fin 4 → F), h a a.2 c c.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

theorem card_fixedPoints_eq {F : Type} [Field F] (S : Subgroup (GL (Fin 4) F)) :
    Nat.card (MulAction.fixedPoints S (Fin 4 → F)) =
      Nat.card (fixedAdd (S : Set (GL (Fin 4) F))) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  simp only [MulAction.mem_fixedPoints, mem_fixedAdd, SetLike.mem_coe, Subtype.forall]
  rfl

theorem fixed_zero_of_order_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {x : GL (Fin 4) F} (hx : orderOf x = 5) {w : Fin 4 → F} (hw : x • w = w) : w = 0 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : Subgroup (GL (Fin 4) F) := Subgroup.zpowers x with hA
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [hA, Nat.card_zpowers, hx]; norm_num)
  have hmod := hAp.card_modEq_card_fixedPoints (Fin 4 → F)
  rw [card_fixedPoints_eq, card_fun_four hF] at hmod
  have hdvd := card_fixedAdd_dvd hF (A : Set (GL (Fin 4) F))
  have h1 : Nat.card (fixedAdd (A : Set (GL (Fin 4) F))) ≡ 1 [MOD 5] := by
    have : (16 : ℕ) ≡ 1 [MOD 5] := by decide
    exact hmod.symm.trans this
  have hw' : w ∈ fixedAdd (A : Set (GL (Fin 4) F)) := by
    intro g hg
    have hx' : x ∈ MulAction.stabilizer (GL (Fin 4) F) w := hw
    have hle : A ≤ MulAction.stabilizer (GL (Fin 4) F) w := (Subgroup.zpowers_le).2 hx'
    exact hle hg
  rcases eq_one_or_sixteen hdvd h1 with h | h
  · have hs : Subsingleton (fixedAdd (A : Set (GL (Fin 4) F))) :=
      (Nat.card_eq_one_iff_unique.1 h).1
    exact congrArg Subtype.val (hs.elim ⟨w, hw'⟩ ⟨0, zero_mem _⟩)
  · exfalso
    have htop : fixedAdd (A : Set (GL (Fin 4) F)) = ⊤ := by
      rw [← AddSubgroup.card_eq_iff_eq_top, h, card_fun_four hF]
    have hx1 : x = 1 := by
      refine eq_one_of_smul_eq x fun v => ?_
      have hv : v ∈ fixedAdd (A : Set (GL (Fin 4) F)) := by
        rw [htop]; trivial
      exact hv x (Subgroup.mem_zpowers x)
    rw [hx1, orderOf_one] at hx
    omega

theorem gl4_no_block {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (H Q : Subgroup (GL (Fin 4) F)) (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal)
    (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) {x : GL (Fin 4) F} (hxH : x ∈ H) (hx5 : orderOf x = 5) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : Subgroup (GL (Fin 4) F) := Subgroup.zpowers x with hA
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [hA, Nat.card_zpowers, hx5]; norm_num)
  set C : AddSubgroup (Fin 4 → F) := fixedAdd (Q : Set (GL (Fin 4) F)) with hC
  have hAH : A ≤ H := (Subgroup.zpowers_le).2 hxH
  have hCinv : ∀ a ∈ A, ∀ c ∈ C, a • c ∈ C := by
    intro a ha c hc q hq
    have haH : a ∈ H := hAH ha
    have hqa : a⁻¹ * q * a ∈ Q := by
      have := hQn.conj_mem ⟨q, hQH hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨a⁻¹, H.inv_mem haH⟩
      simpa [Subgroup.mem_subgroupOf] using this
    have h1 : (a⁻¹ * q * a) • c = c := hc _ hqa
    calc q • (a • c) = (q * a) • c := (mul_smul q a c).symm
      _ = (a * (a⁻¹ * q * a)) • c := by rw [mul_assoc, ← mul_assoc a, mul_inv_cancel, one_mul]
      _ = a • ((a⁻¹ * q * a) • c) := mul_smul _ _ _
      _ = a • c := by rw [h1]
  let _ : MulAction A C := actOn A C hCinv
  have hcardC : Nat.card C ≡ 1 [MOD 5] := by
    have hm := hAp.card_modEq_card_fixedPoints C
    have hfp : Nat.card (MulAction.fixedPoints A C) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨0, zero_mem _⟩, ?_⟩⟩⟩
      · have key : ∀ c : MulAction.fixedPoints A C, (c : C) = 0 := by
          intro c
          have h1 := c.2 ⟨x, Subgroup.mem_zpowers x⟩
          have h2 : x • ((c : C) : Fin 4 → F) = ((c : C) : Fin 4 → F) := congrArg Subtype.val h1
          exact Subtype.ext (fixed_zero_of_order_five hF hx5 h2)
        exact Subtype.ext ((key a).trans (key b).symm)
      · intro g
        exact Subtype.ext (by
          show ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec 0 = 0
          simp)
    rwa [hfp] at hm
  have hdvd := card_fixedAdd_dvd hF (Q : Set (GL (Fin 4) F))
  rcases eq_one_or_sixteen hdvd hcardC with h | h
  · have hQmod := hQ2.card_modEq_card_fixedPoints (Fin 4 → F)
    rw [card_fixedPoints_eq, card_fun_four hF, ← hC, h] at hQmod
    exact absurd hQmod (by decide)
  · have htop : C = ⊤ := by rw [← AddSubgroup.card_eq_iff_eq_top, h, card_fun_four hF]
    apply hQ1
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    refine eq_one_of_smul_eq q fun v => ?_
    have hv : v ∈ C := by rw [htop]; trivial
    exact hv q hq


theorem scalars_eq_bot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    StatedScalars (Fin 4) F = ⊥ := by
  classical
  have := Fintype.ofFinite F
  have hu : Subsingleton Fˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units]
    have : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
    omega
  rw [eq_bot_iff]
  rintro g ⟨u, rfl⟩
  rw [Subsingleton.elim u 1, map_one]
  exact Subgroup.one_mem _

@[expose] def psi {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    StatedProj (StatedSL 4 F) →* GL (Fin 4) F :=
  QuotientGroup.lift _ (StatedSL 4 F).subtype (by
    intro x hx
    have hx' : (x : GL (Fin 4) F) ∈ StatedScalars (Fin 4) F := Subgroup.mem_subgroupOf.1 hx
    rw [scalars_eq_bot hF] at hx'
    rw [MonoidHom.mem_ker]
    exact Subgroup.mem_bot.1 hx')

theorem psi_mk {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (s : ↥(StatedSL 4 F)) :
    psi hF (QuotientGroup.mk s) = (s : GL (Fin 4) F) := rfl

theorem psi_injective {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Function.Injective (psi hF) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (s : GL (Fin 4) F) = 1 := by
    rw [MonoidHom.mem_ker, psi_mk] at hx
    exact hx
  have : s = 1 := Subtype.ext h1
  simp [this]

end CFSG.QuasithinUnique.A5.Kc3L4

namespace CFSG.QuasithinUnique.A5

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3L4

theorem kc3For_L4 : Kc3For Kc3L4 := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  exfalso
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmod
  have hF2 : Nat.card F = 2 := by simpa using hF
  let φ : ↥K →* GL (Fin 4) F :=
    (psi hF2).comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
  have hker : ∀ k : ↥K, φ k = 1 → k ∈ Subgroup.center ↥K := by
    intro k hk
    have h1 : e (QuotientGroup.mk k) = 1 := by
      apply psi_injective hF2
      rw [map_one]
      exact hk
    have h2 : (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = 1 := e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff k).1 h2
  let pL : Subgroup ↥K := L.subgroupOf K
  let pQ : Subgroup ↥K := (blockQ L).subgroupOf K
  let H : Subgroup (GL (Fin 4) F) := pL.map φ
  let Q : Subgroup (GL (Fin 4) F) := pQ.map φ
  have hQL : blockQ L ≤ L := C1.blockQ_le L
  have hQH : Q ≤ H := by
    refine Subgroup.map_mono ?_
    intro y hy
    exact Subgroup.mem_subgroupOf.2 (hQL (Subgroup.mem_subgroupOf.1 hy))
  have hconj : ∀ (l : ↥K), (l : G) ∈ L → ∀ p : ↥K, (p : G) ∈ blockQ L → ((l * p * l⁻¹ : ↥K) : G) ∈ blockQ L := by
    intro l hl p hp
    have hn := C1.le_normalizer_blockQ L hl
    rw [Subgroup.mem_normalizer_iff] at hn
    exact (hn _).1 hp
  have hQn : (Q.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨p, hp, hpn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.1 g.2
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.2 ⟨l * p * l⁻¹, Subgroup.mem_subgroupOf.2 (hconj l hl p hp), ?_⟩
    rw [map_mul, map_mul, map_inv, hpn, hlg]
    simp
  have hQ2 : IsPGroup 2 Q := by
    have hb : IsPGroup 2 ↥(blockQ L) := C1.blockQ_isPGroup L
    have hp : IsPGroup 2 ↥pQ := hb.of_equiv (Subgroup.subgroupOfEquivOfLe
      ((hQL.trans hLK))).symm
    exact hp.of_surjective (φ.subgroupMap pQ) (φ.subgroupMap_surjective pQ)
  have hQ1 : Q ≠ ⊥ := by
    intro hQ0
    have hc : ∀ p : ↥K, (p : G) ∈ blockQ L → p ∈ Subgroup.center ↥K := by
      intro p hp
      apply hker
      have : φ p ∈ Q := Subgroup.mem_map.2 ⟨p, Subgroup.mem_subgroupOf.2 hp, rfl⟩
      rw [hQ0] at this
      exact Subgroup.mem_bot.1 this
    have hcomm : ⁅blockQ L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := Subgroup.mem_center_iff.1 (hc ⟨p, hLK (hQL hp)⟩ hp) ⟨l, hLK hl⟩
      exact congrArg Subtype.val this
    have hU : blockU L = ⊥ := hcomm
    have hlt := hL.2.2.2.2.1
    rw [hU] at hlt
    exact not_lt_bot hlt
  obtain ⟨α, hα, -, -⟩ := h5
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hcard]; norm_num)
  obtain ⟨ℓ, hℓ⟩ := hα y
  have h5dvd : 5 ∣ orderOf ℓ := by
    rw [← hy, ← hℓ]
    exact orderOf_map_dvd α ℓ
  have hℓ0 : orderOf ℓ ≠ 0 := (orderOf_pos ℓ).ne'
  set k : ↥L := ℓ ^ (orderOf ℓ / 5) with hk
  have hk5 : orderOf k = 5 := orderOf_pow_orderOf_div hℓ0 h5dvd
  let k₀ : ↥K := ⟨(k : G), hLK k.2⟩
  have hk₀5 : orderOf k₀ = 5 := by
    have : orderOf (k₀ : ↥K) = orderOf k := by
      rw [← Subgroup.orderOf_coe k, ← Subgroup.orderOf_coe k₀]
    rw [this, hk5]
  have hxH : φ k₀ ∈ H := Subgroup.mem_map.2 ⟨k₀, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  have hx1 : φ k₀ ≠ 1 := by
    intro h1
    have hc := hker k₀ h1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hZ) ⟨k₀, hc⟩
    have : orderOf k₀ = 2 ^ j := by
      rw [← hj]
      exact Subgroup.orderOf_coe ⟨k₀, hc⟩
    rw [hk₀5] at this
    rcases j with _ | j
    · omega
    · have : 2 ∣ 5 := by rw [this]; exact dvd_pow_self 2 (Nat.succ_ne_zero j)
      omega
  have hx5 : orderOf (φ k₀) = 5 := by
    refine orderOf_eq_prime ?_ hx1
    rw [← map_pow, ← hk₀5, pow_orderOf_eq_one, map_one]
  exact gl4_no_block hF2 H Q hQH hQn hQ2 hQ1 hxH hx5


end CFSG.QuasithinUnique.A5
