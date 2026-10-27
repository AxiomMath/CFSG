module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviCentral
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonabBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {G G' : Type*} [Group G] [Group G']

private theorem eq_one_of_odd_of_dvd_two_pow {n k : ℕ} (hodd : Odd n) (hd : n ∣ 2 ^ k) :
    n = 1 := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩))

private theorem exists_two_part_map {A B : Type*} [Group A] [Finite A] [Group B] (ψ : A →* B)
    (x : A) {k : ℕ} (hk : orderOf (ψ x) = 2 ^ k) :
    ∃ x₂ ∈ Subgroup.zpowers x, (∃ j : ℕ, orderOf x₂ = 2 ^ j) ∧ ψ x₂ = ψ x := by
  obtain ⟨x₂, hx₂, xo, hxo, hx, h2, hodd⟩ := exists_two_odd_decomp x
  refine ⟨x₂, hx₂, h2, ?_⟩
  have h1 : ψ xo ∈ Subgroup.zpowers (ψ x) := by
    rw [← MonoidHom.map_zpowers]
    exact ⟨xo, hxo, rfl⟩
  have hd1 : orderOf (ψ xo) ∣ 2 ^ k := hk ▸ orderOf_dvd_of_mem_zpowers h1
  have hd2 : Odd (orderOf (ψ xo)) := Odd.of_dvd_nat hodd (orderOf_map_dvd ψ xo)
  have : ψ xo = 1 := orderOf_eq_one_iff.1 (eq_one_of_odd_of_dvd_two_pow hd2 hd1)
  conv_rhs => rw [hx]
  rw [map_mul, this, mul_one]

theorem map_pElementSubgroup_two [Finite G] (φ : G →* G') (X : Subgroup G) :
    (pElementSubgroup 2 X).map φ = pElementSubgroup 2 (X.map φ) := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hk ▸ orderOf_map_dvd φ x)
    exact ⟨j, hj⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨x, hx, rfl⟩, k, hk⟩
    obtain ⟨x₂, hx₂, ⟨j, hj⟩, hφ⟩ := exists_two_part_map φ x hk
    rw [← hφ]
    exact Subgroup.subset_closure ⟨x₂, ⟨(Subgroup.zpowers_le.2 hx) hx₂, j, hj⟩, rfl⟩

theorem map_twoResidual [Finite G] (φ : G →* G') (X : Subgroup G) :
    (twoResidual X).map φ = twoResidual (X.map φ) := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_twoResidual_iff]
    intro N' hN'X hN'norm hN'2
    have key : twoResidual X ≤ N'.comap φ ⊓ X := by
      refine twoResidual_le_of_isTwoQuotient inf_le_right ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro n
        have h1 : φ (x * n * x⁻¹) ∈ N' ↔ φ n ∈ N' := by
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.mp (hN'norm ⟨x, hx, rfl⟩) (φ n)).symm
        have h2 : x * n * x⁻¹ ∈ X ↔ n ∈ X := by
          constructor
          · intro h
            have := X.mul_mem (X.mul_mem (X.inv_mem hx) h) hx
            rwa [show x⁻¹ * (x * n * x⁻¹) * x = n by group] at this
          · intro h
            exact X.mul_mem (X.mul_mem hx h) (X.inv_mem hx)
        simp only [Subgroup.mem_inf, Subgroup.mem_comap, h1, h2]
      · intro y hy
        obtain ⟨k, hk⟩ := hN'2 (φ y) ⟨y, hy, rfl⟩
        exact ⟨k, by simpa [map_pow] using hk, X.pow_mem hy _⟩
    exact (key hm).1
  · refine twoResidual_le_of_isTwoQuotient (Subgroup.map_mono (twoResidual_le X)) ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨x * m * x⁻¹,
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual X hx) m).mp hm, by simp⟩
      · rintro ⟨m, hm, hmn⟩
        refine ⟨x⁻¹ * m * x, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_twoResidual X (X.inv_mem hx)) m).mp hm
          simpa using this
        · rw [map_mul, map_mul, hmn, map_inv]
          group
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X x hx
      exact ⟨k, ⟨x ^ 2 ^ k, hk, by simp [map_pow]⟩⟩

theorem map_conjClosure (φ : G →* G') (P R : Subgroup G) :
    (conjClosure P R).map φ = conjClosure (P.map φ) (R.map φ) := by
  unfold conjClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨φ h, ⟨h, hh, rfl⟩, φ z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩

private theorem subgroupMap_ker_le_center (φ : G →* G') {W : Subgroup G}
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k) :
    (φ.subgroupMap W).ker ≤ Subgroup.center ↥W := by
  intro k hk
  have hk1 : φ (k : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
  exact Subgroup.mem_center_iff.2 fun w => Subtype.ext (hc _ k.2 hk1 _ w.2).symm

theorem isSolvable_of_map_of_central [Finite G] (φ : G →* G') (W : Subgroup G)
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k)
    (h : Group.IsSolvable ↥(W.map φ)) : Group.IsSolvable ↥W := by
  have hker := subgroupMap_ker_le_center φ hc
  have hab : IsMulCommutative ↥(φ.subgroupMap W).ker :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hker b.2) a)⟩⟩
  have : Group.IsSolvable ↥(φ.subgroupMap W).ker := inferInstance
  exact Group.isSolvable_of_ker_le_range (φ.subgroupMap W).ker.subtype (φ.subgroupMap W)
    (by rw [Subgroup.range_subtype])

private theorem exists_char_two_subgroup {D : Type*} [Group D] [Finite D] [Group.IsNilpotent D] :
    ∃ P : Subgroup D, P.Characteristic ∧ IsPGroup 2 ↥P ∧
      ∀ y : D, (∃ k : ℕ, orderOf y = 2 ^ k) → y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 D) := Sylow.nonempty
  have hN : (P₂ : Subgroup D).Normal := inferInstance
  refine ⟨(P₂ : Subgroup D), Sylow.characteristic_of_normal P₂ hN, P₂.isPGroup', ?_⟩
  rintro y ⟨k, hk⟩
  have hp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P₂ Q
  have hQP : Q = P₂ := by rw [← hg]; exact Sylow.smul_eq_of_normal
  exact hQP ▸ hQ (Subgroup.mem_zpowers y)

private theorem isPGroup_two_of_closure_eq_top {Q : Type*} [Group Q] [Finite Q]
    [Group.IsNilpotent Q] (h : Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤) :
    IsPGroup 2 Q := by
  obtain ⟨P, -, hP2, hP⟩ := exists_char_two_subgroup (D := Q)
  have htop : (⊤ : Subgroup Q) ≤ P := h ▸ (Subgroup.closure_le P).2 hP
  intro q
  obtain ⟨k, hk⟩ := hP2 ⟨q, htop (Subgroup.mem_top q)⟩
  exact ⟨k, congrArg Subtype.val hk⟩

private theorem exists_pCore_mul_ker_of_map_mem_pCore {A B : Type*} [Group A] [Finite A] [Group B]
    (φ : A →* B) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A) {n : A}
    (hn : φ n ∈ CFSG.pCore 2 B) :
    ∃ y ∈ CFSG.pCore 2 A, ∃ z ∈ φ.ker, Odd (orderOf z) ∧ n = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective φ hφ
  set N : Subgroup A := (CFSG.pCore 2 B).comap φ
  have hNn : N.Normal := CFSG.pCore_normal.comap φ
  have hNnil : Group.IsNilpotent ↥N := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 B) := CFSG.pCore_isPGroup.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center
      ((φ.comp N.subtype).codRestrict (CFSG.pCore 2 B) (fun m => m.2)) ?_
    intro m hm
    have hm1 : φ (m : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hm1)) g
  obtain ⟨P, hPc, hP2, hP⟩ := exists_char_two_subgroup (D := ↥N)
  set N₂ : Subgroup A := P.map N.subtype
  have hN₂n : N₂.Normal := inferInstance
  have hN₂p : IsPGroup 2 ↥N₂ := hP2.map _
  have hN₂le : N₂ ≤ CFSG.pCore 2 A := le_sSup ⟨hN₂n, hN₂p⟩
  obtain ⟨n₂, hn₂, no, hno, hnn, ⟨k, hk⟩, hodd⟩ := exists_two_odd_decomp n
  have hzN : Subgroup.zpowers n ≤ N := (Subgroup.zpowers_le).2 hn
  have hφno : φ no = 1 := by
    have hmem : φ no ∈ CFSG.pCore 2 B := (hzN hno)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 CFSG.pCore_isPGroup) ⟨φ no, hmem⟩
    have hj' : orderOf (φ no) = 2 ^ j := by simpa using hj
    have hodd' : Odd (orderOf (φ no)) := Odd.of_dvd_nat hodd (orderOf_map_dvd φ no)
    exact orderOf_eq_one_iff.1 (eq_one_of_odd_of_dvd_two_pow hodd' (dvd_of_eq hj'))
  refine ⟨n₂, hN₂le ?_, no, hφno, hodd, hnn⟩
  have hn₂N : n₂ ∈ N := hzN hn₂
  have hn₂o : orderOf (⟨n₂, hn₂N⟩ : ↥N) = 2 ^ k := by
    rw [← hk]; exact Subgroup.orderOf_mk n₂ hn₂N
  exact ⟨⟨n₂, hn₂N⟩, hP _ ⟨k, hn₂o⟩, rfl⟩

private theorem conj_mem_pCoreOf {K : Subgroup G} {k o : G} (hk : k ∈ K) (ho : o ∈ pCoreOf 2 K) :
    k * o * k⁻¹ ∈ pCoreOf 2 K := by
  rw [pCoreOf] at ho ⊢
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

private theorem exists_pCoreOf_mul_of_map_mem [Finite G] (φ : G →* G') {W : Subgroup G}
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k) {c : G} (hcW : c ∈ W)
    (hφc : φ c ∈ pCoreOf 2 (W.map φ)) :
    ∃ t ∈ pCoreOf 2 W, ∃ z ∈ W, φ z = 1 ∧ Odd (orderOf z) ∧ c = t * z := by
  have hker := subgroupMap_ker_le_center φ hc
  have hn : (φ.subgroupMap W) ⟨c, hcW⟩ ∈ CFSG.pCore 2 ↥(W.map φ) := by
    obtain ⟨m, hm, hmc⟩ := hφc
    have : m = (φ.subgroupMap W) ⟨c, hcW⟩ := Subtype.ext hmc
    exact this ▸ hm
  obtain ⟨y, hy, z, hz, hodd, hyz⟩ := exists_pCore_mul_ker_of_map_mem_pCore (φ.subgroupMap W)
    (φ.subgroupMap_surjective W) hker hn
  refine ⟨(y : G), ⟨y, hy, rfl⟩, (z : G), z.2, congrArg Subtype.val (MonoidHom.mem_ker.1 hz), ?_,
    congrArg Subtype.val hyz⟩
  rwa [Subgroup.orderOf_coe]

private theorem commutator_mem_pCoreOf_of_two_pow [Finite G] (φ : G →* G') {W : Subgroup G}
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k) {x y : G} (hxW : x ∈ W) (hyW : y ∈ W)
    {k : ℕ} (hxk : x ^ 2 ^ k = 1) (h : φ ⁅x, y⁆ ∈ pCoreOf 2 (W.map φ)) :
    ⁅x, y⁆ ∈ pCoreOf 2 W := by
  have hTW : pCoreOf 2 W ≤ W := Subgroup.map_subtype_le _
  have hcW : ⁅x, y⁆ ∈ W :=
    W.mul_mem (W.mul_mem (W.mul_mem hxW hyW) (W.inv_mem hxW)) (W.inv_mem hyW)
  obtain ⟨t, ht, z, hzW, hφz, hodd, hxy⟩ := exists_pCoreOf_mul_of_map_mem φ hc hcW h
  have hxy' : x * y * x⁻¹ = t * z * y := by
    rw [← hxy, commutatorElement_def]; group
  have hzx : ∀ n : ℕ, x * z ^ n * x⁻¹ = z ^ n := fun n => by
    have : Commute x z := (hc z hzW hφz x hxW).symm
    rw [(this.pow_right n).eq]; group
  have hzt : ∀ n : ℕ, z ^ n * t = t * z ^ n := fun n => by
    have : Commute z t := hc z hzW hφz t (hTW ht)
    exact (this.pow_left n).eq
  have key : ∀ n : ℕ, ∃ s ∈ pCoreOf 2 W, x ^ n * y * (x ^ n)⁻¹ = s * z ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨1, (pCoreOf 2 W).one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs, hsn⟩ := ih
      refine ⟨(x * s * x⁻¹) * t, (pCoreOf 2 W).mul_mem (conj_mem_pCoreOf hxW hs) ht, ?_⟩
      calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹
          = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by rw [pow_succ']; group
        _ = x * (s * z ^ n * y) * x⁻¹ := by rw [hsn]
        _ = (x * s * x⁻¹) * (x * z ^ n * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * s * x⁻¹) * z ^ n * (t * z * y) := by rw [hzx, hxy']
        _ = (x * s * x⁻¹) * (z ^ n * t) * z * y := by group
        _ = ((x * s * x⁻¹) * t) * z ^ (n + 1) * y := by rw [hzt n, pow_succ]; group
  obtain ⟨s, hs, hsn⟩ := key (2 ^ k)
  have hzpow : z ^ 2 ^ k ∈ pCoreOf 2 W := by
    rw [hxk] at hsn
    have h1 : s * z ^ 2 ^ k = 1 := by
      simpa using hsn.symm
    have : z ^ 2 ^ k = s⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (pCoreOf 2 W).inv_mem hs
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hz : z ∈ pCoreOf 2 W := by
    rw [← hm]
    exact (pCoreOf 2 W).pow_mem hzpow m
  rw [hxy]
  exact (pCoreOf 2 W).mul_mem ht hz

theorem commutator_le_pCoreOf_of_map [Finite G] (φ : G →* G') {W C C' : Subgroup G}
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k)
    (hCW : C ≤ W) (hC'W : C' ≤ W) (hC2 : C ≤ pElementSubgroup 2 C)
    (h : ⁅C.map φ, C'.map φ⁆ ≤ pCoreOf 2 (W.map φ)) : ⁅C, C'⁆ ≤ pCoreOf 2 W := by
  rw [Subgroup.commutator_le]
  let D : Subgroup G :=
    { carrier := {x | x ∈ W ∧ ∀ y ∈ C', ⁅x, y⁆ ∈ pCoreOf 2 W}
      one_mem' := ⟨W.one_mem, fun y _ => by simpa using (pCoreOf 2 W).one_mem⟩
      mul_mem' := fun {x₁ x₂} hx₁ hx₂ => ⟨W.mul_mem hx₁.1 hx₂.1, fun y hy => by
        have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (pCoreOf 2 W).mul_mem (conj_mem_pCoreOf hx₁.1 (hx₂.2 y hy)) (hx₁.2 y hy)⟩
      inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, fun y hy => by
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact conj_mem_pCoreOf (W.inv_mem hx.1) ((pCoreOf 2 W).inv_mem (hx.2 y hy))⟩ }
  have hgen : pElementSubgroup 2 C ≤ D := by
    unfold pElementSubgroup
    rw [Subgroup.closure_le]
    rintro x ⟨hxC, k, hk⟩
    refine ⟨hCW hxC, fun y hy => ?_⟩
    refine commutator_mem_pCoreOf_of_two_pow φ hc (hCW hxC) (hC'W hy) (k := k)
      (by rw [← hk]; exact pow_orderOf_eq_one x) ?_
    rw [map_commutatorElement]
    exact h (Subgroup.commutator_mem_commutator ⟨x, hxC, rfl⟩ ⟨y, hy, rfl⟩)
  intro x hx y hy
  exact (hgen (hC2 hx)).2 y hy

private theorem exists_cover_pCore_quotient {A B : Type*} [Group A] [Finite A] [Group B]
    (ψ : A →* B) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center A) :
    ∃ ψ' : A ⧸ CFSG.pCore 2 A →* B ⧸ CFSG.pCore 2 B, Function.Surjective ψ' ∧
      ∀ e ∈ ψ'.ker, e ∈ Subgroup.center (A ⧸ CFSG.pCore 2 A) ∧ Odd (orderOf e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective ψ hψ
  set pA := CFSG.pCore 2 A
  set pB := CFSG.pCore 2 B
  have hmap : pA.map ψ ≤ pB :=
    le_sSup ⟨CFSG.pCore_normal.map ψ hψ, CFSG.pCore_isPGroup.map ψ⟩
  have hle : pA ≤ pB.comap ψ := Subgroup.map_le_iff_le_comap.1 hmap
  refine ⟨QuotientGroup.map pA pB ψ hle, ?_, ?_⟩
  · intro x
    induction x using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨a, rfl⟩ := hψ b
      exact ⟨a, rfl⟩
  · intro e he
    induction e using QuotientGroup.induction_on with
    | H n =>
      have hn : ψ n ∈ pB := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 he)
      obtain ⟨y, hy, z, hz, hodd, rfl⟩ := exists_pCore_mul_ker_of_map_mem_pCore ψ hψ hker hn
      have e : (QuotientGroup.mk (y * z) : A ⧸ pA) = QuotientGroup.mk z := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
      rw [e]
      refine ⟨Subgroup.mem_center_iff.2 fun g => ?_, ?_⟩
      · induction g using QuotientGroup.induction_on with
        | H g =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.1 (hker hz) g]
      · exact Odd.of_dvd_nat hodd (orderOf_map_dvd (QuotientGroup.mk' pA) z)

private theorem isQuasisimpleTwoNonab_of_central_odd_cover {X X₁ : Type*} [Group X] [Finite X]
    [Group X₁] (ψ : X →* X₁) (hψ : Function.Surjective ψ)
    (hker : ∀ e ∈ ψ.ker, e ∈ Subgroup.center X ∧ Odd (orderOf e))
    (hperf : commutator X = ⊤) (h : IsQuasisimpleTwoNonab X₁) : IsQuasisimpleTwoNonab X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X₁ := Finite.of_surjective ψ hψ
  obtain ⟨-, h2, h3, h4, Q₁, hQ₁, a, ha, b, hb, hab⟩ := h
  obtain ⟨eq⟩ := centerQuotientEquiv ψ hψ (fun e he => (hker e he).1) hperf
  refine ⟨hperf, ?_, ?_, ?_, ?_⟩
  · have := h2
    exact eq.isSimpleGroup
  · rw [Nat.card_congr eq.toEquiv]
    exact h3
  · intro z hz
    have hz1 : ψ z ∈ Subgroup.center X₁ := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      obtain ⟨u, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    have hodd := h4 _ hz1
    have hzm : z ^ orderOf (ψ z) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have hdvd : orderOf z ∣ orderOf (ψ z) * orderOf (z ^ orderOf (ψ z)) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat (hodd.mul (hker _ hzm).2) hdvd
  · set D : Subgroup X := Q₁.comap ψ with hD
    have hnilD : Group.IsNilpotent ↥D := by
      have : Group.IsNilpotent ↥Q₁ := hQ₁.isNilpotent
      refine Subgroup.isNilpotent_of_ker_le_center (ψ.subgroupComap Q₁) ?_
      intro d hd
      have hd1 : ψ (d : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
      refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
      exact Subgroup.mem_center_iff.1 (hker _ (MonoidHom.mem_ker.2 hd1)).1 g
    obtain ⟨P, -, hP2, hP⟩ := exists_char_two_subgroup (D := ↥D)
    have lift : ∀ q ∈ Q₁, ∃ s ∈ P.map D.subtype, ψ s = q := by
      intro q hq
      obtain ⟨s, rfl⟩ := hψ q
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQ₁ ⟨ψ s, hq⟩
      have hk' : orderOf (ψ s) = 2 ^ k := by simpa using hk
      obtain ⟨s₂, -, ⟨j, hj⟩, hs₂⟩ := exists_two_part_map ψ s hk'
      have hs₂D : s₂ ∈ D := by rw [hD, Subgroup.mem_comap, hs₂]; exact hq
      exact ⟨s₂, ⟨⟨s₂, hs₂D⟩, hP _ ⟨j, (Subgroup.orderOf_mk s₂ hs₂D).trans hj⟩, rfl⟩, hs₂⟩
    obtain ⟨s, hs, hsa⟩ := lift a ha
    obtain ⟨t, ht, htb⟩ := lift b hb
    refine ⟨P.map D.subtype, hP2.map _, s, hs, t, ht, fun hst => hab ?_⟩
    rw [← hsa, ← htb, ← map_mul, ← map_mul, hst]

private theorem map_commutator_top {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Surjective f) : (commutator H).map f = commutator K := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf]

private theorem commutator_quotient_pCore_eq_top {Γ B : Type*} [Group Γ] [Finite Γ] [Group B]
    (A : Subgroup Γ) [A.Normal] (hA2 : ∀ y : Γ, ∃ k : ℕ, y ^ 2 ^ k ∈ A)
    (hAmin : ∀ N : Subgroup Γ, N.Normal → (∀ y : Γ, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → A ≤ N)
    (hgen : Subgroup.closure {x : Γ | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤)
    (ψ : ↥A →* B) (hψ : Function.Surjective ψ)
    (hker : ∀ a : ↥A, ψ a = 1 → (a : Γ) ∈ Subgroup.center Γ)
    (hperf : commutator (B ⧸ CFSG.pCore 2 B) = ⊤) :
    commutator (↥A ⧸ CFSG.pCore 2 ↥A) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NA : Subgroup ↥A := commutator ↥A ⊔ CFSG.pCore 2 ↥A
  have : NA.Characteristic := inferInstance
  set N : Subgroup Γ := NA.map A.subtype
  have hNn : N.Normal := inferInstance
  have hNA_le : N ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hkerA : ψ.ker ≤ Subgroup.center ↥A := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker a (MonoidHom.mem_ker.1 ha)) g)
  have step2 : ∀ a : ↥A, ∃ n ∈ NA, ∃ z : ↥A, ψ z = 1 ∧ a = n * z := by
    intro a
    have h1 : (QuotientGroup.mk (ψ a) : B ⧸ CFSG.pCore 2 B) ∈
        commutator (B ⧸ CFSG.pCore 2 B) := hperf ▸ Subgroup.mem_top _
    rw [← map_commutator_top (QuotientGroup.mk' (CFSG.pCore 2 B))
      (QuotientGroup.mk'_surjective _)] at h1
    obtain ⟨c₁, hc₁, hc₁a⟩ := h1
    rw [← map_commutator_top ψ hψ] at hc₁
    obtain ⟨c, hc, rfl⟩ := hc₁
    have hmem : ψ (c⁻¹ * a) ∈ CFSG.pCore 2 B := by
      rw [map_mul, map_inv]
      exact QuotientGroup.eq.1 hc₁a
    obtain ⟨y, hy, z, hz, -, hyz⟩ := exists_pCore_mul_ker_of_map_mem_pCore ψ hψ hkerA hmem
    refine ⟨c * y, Subgroup.mul_mem_sup hc hy, z, MonoidHom.mem_ker.1 hz, ?_⟩
    rw [mul_assoc, ← hyz]
    group
  have step3 : ∀ y : Γ, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    have hΓA : IsPGroup 2 (Γ ⧸ A) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := hA2 x
        exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hk⟩
    have : Group.IsNilpotent (Γ ⧸ A) := hΓA.isNilpotent
    have hle : N ≤ A.comap (MonoidHom.id Γ) := hNA_le
    have hnil : Group.IsNilpotent (Γ ⧸ N) := by
      refine Subgroup.isNilpotent_of_ker_le_center
        (QuotientGroup.map N A (MonoidHom.id Γ) hle) ?_
      intro e he
      induction e using QuotientGroup.induction_on with
      | H x =>
        have hxA : x ∈ A := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 he)
        obtain ⟨n, hn, z, hz, hxz⟩ := step2 ⟨x, hxA⟩
        have hxz' : x = (n : Γ) * z := congrArg Subtype.val hxz
        have hnN : (n : Γ) ∈ N := ⟨n, hn, rfl⟩
        have hmk : (QuotientGroup.mk x : Γ ⧸ N) = QuotientGroup.mk (z : Γ) := by
          rw [hxz', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (n : Γ)).2 hnN, one_mul]
        rw [hmk]
        refine Subgroup.mem_center_iff.2 fun w => ?_
        induction w using QuotientGroup.induction_on with
        | H w =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.1 (hker z hz) w]
    have hgenQ : Subgroup.closure {x : Γ ⧸ N | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
      have h1 : (Subgroup.closure {x : Γ | ∃ k : ℕ, orderOf x = 2 ^ k}).map
          (QuotientGroup.mk' N) = ⊤ := by
        rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      rw [MonoidHom.map_closure] at h1
      refine eq_top_iff.2 (h1 ▸ Subgroup.closure_mono ?_)
      rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (hk ▸ orderOf_map_dvd (QuotientGroup.mk' N) x)
      exact ⟨j, hj⟩
    have hQ2 := isPGroup_two_of_closure_eq_top hgenQ
    intro y
    obtain ⟨k, hk⟩ := hQ2 (QuotientGroup.mk y)
    exact ⟨k, (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hk)⟩
  have hAN : A ≤ N := hAmin N hNn step3
  have hNAtop : NA = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨n, hn, hna⟩ := hAN a.2
    have : n = a := Subtype.ext hna
    exact this ▸ hn
  rw [← map_commutator_top (QuotientGroup.mk' (CFSG.pCore 2 ↥A)) (QuotientGroup.mk'_surjective _),
    eq_top_iff]
  intro x _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a ∈ NA := hNAtop ▸ Subgroup.mem_top a
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥A)) a ∈
      (commutator ↥A ⊔ CFSG.pCore 2 ↥A).map (QuotientGroup.mk' (CFSG.pCore 2 ↥A)) := ⟨a, ha, rfl⟩
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h2

private theorem quasisimpleModTwoNonab_of_mulEquiv_self {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : QuasisimpleModTwoNonab A) : QuasisimpleModTwoNonab B :=
  (quasisimpleModTwoNonab_iff B).2 (IsQuasisimpleTwoNonab.of_mulEquiv
    (QuotientGroup.congr (CFSG.pCore 2 A) (CFSG.pCore 2 B) e (CFSG.pCore_map_iso 2 e))
    ((quasisimpleModTwoNonab_iff A).1 h))

private theorem exists_mulEquiv_twoResidual_top (K : Subgroup G) [Finite ↥K] :
    Nonempty (↥(twoResidual (⊤ : Subgroup ↥K)) ≃* ↥(twoResidual K)) := by
  have h : (twoResidual (⊤ : Subgroup ↥K)).map K.subtype = twoResidual K := by
    rw [map_twoResidual, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact ⟨(Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr h)⟩

private theorem closure_two_elements_eq_top {W : Subgroup G} (hW2 : W ≤ pElementSubgroup 2 W) :
    Subgroup.closure {x : ↥W | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  have h1 : (γ : G) ∈
      (Subgroup.closure {x : ↥W | ∃ k : ℕ, orderOf x = 2 ^ k}).map W.subtype := by
    rw [MonoidHom.map_closure]
    have himg : W.subtype '' {x : ↥W | ∃ k : ℕ, orderOf x = 2 ^ k} =
        {x : G | x ∈ W ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
      ext x
      constructor
      · rintro ⟨y, ⟨k, hk⟩, rfl⟩
        exact ⟨y.2, k, by rw [← hk]; exact Subgroup.orderOf_coe y⟩
      · rintro ⟨hx, k, hk⟩
        exact ⟨⟨x, hx⟩, ⟨k, by rw [← Subgroup.orderOf_mk x hx] at hk; exact hk⟩, rfl⟩
    rw [himg]
    exact hW2 γ.2
  obtain ⟨γ', hγ', hγγ'⟩ := h1
  exact (Subtype.ext hγγ' : γ' = γ) ▸ hγ'

private theorem quasisimpleModTwoNonab_twoResidual_top_of_central {Γ Γ₁ : Type*} [Group Γ]
    [Finite Γ] [Group Γ₁] (f : Γ →* Γ₁) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Γ)
    (hgen : Subgroup.closure {x : Γ | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤)
    (h : QuasisimpleModTwoNonab ↥(twoResidual (⊤ : Subgroup Γ₁))) :
    QuasisimpleModTwoNonab ↥(twoResidual (⊤ : Subgroup Γ)) := by
  set A : Subgroup Γ := twoResidual ⊤ with hA
  set A₁ : Subgroup Γ₁ := twoResidual ⊤ with hA₁
  have hAn : A.Normal := ⟨fun n hn g =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual ⊤ (Subgroup.mem_top g)) n).mp hn⟩
  have hmapA : A.map f = A₁ := by
    rw [hA, hA₁, map_twoResidual, Subgroup.map_top_of_surjective f hf]
  let ψ : ↥A →* ↥A₁ := (f.comp A.subtype).codRestrict A₁ (fun a => by
    rw [← hmapA]
    exact ⟨a, a.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    rw [← hmapA] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨⟨a, ha⟩, rfl⟩
  have hψ1 : ∀ a : ↥A, ψ a = 1 → (a : Γ) ∈ Subgroup.center Γ := fun a ha =>
    hker (MonoidHom.mem_ker.2 (congrArg Subtype.val ha))
  have hkerA : ψ.ker ≤ Subgroup.center ↥A := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hψ1 a (MonoidHom.mem_ker.1 ha)) g)
  have hA2 : ∀ y : Γ, ∃ k : ℕ, y ^ 2 ^ k ∈ A := fun y =>
    twoResidual_isTwoQuotient ⊤ y (Subgroup.mem_top y)
  have hAmin : ∀ N : Subgroup Γ, N.Normal → (∀ y : Γ, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → A ≤ N :=
    fun N hN hN2 => twoResidual_le_of_isTwoQuotient le_top
      (fun x _ => (Subgroup.normalizer_eq_top_iff.mpr hN) ▸ Subgroup.mem_top x)
      (fun y _ => hN2 y)
  have hperf := commutator_quotient_pCore_eq_top A hA2 hAmin hgen ψ hψ hψ1
    ((quasisimpleModTwoNonab_iff _).1 h).1
  obtain ⟨ψ', hψ', hψ'ker⟩ := exists_cover_pCore_quotient ψ hψ hkerA
  exact isQuasisimpleTwoNonab_of_central_odd_cover ψ' hψ' hψ'ker hperf
    ((quasisimpleModTwoNonab_iff _).1 h)

theorem quasisimpleModTwoNonab_twoResidual_of_map [Finite G] (φ : G →* G') {W : Subgroup G}
    (hc : ∀ k ∈ W, φ k = 1 → ∀ w ∈ W, k * w = w * k)
    (hW2 : W ≤ pElementSubgroup 2 W)
    (h : QuasisimpleModTwoNonab ↥(twoResidual (W.map φ))) :
    QuasisimpleModTwoNonab ↥(twoResidual W) := by
  have : Finite ↥(W.map φ) := Finite.of_surjective _ (φ.subgroupMap_surjective W)
  obtain ⟨e₁⟩ := exists_mulEquiv_twoResidual_top (W.map φ)
  obtain ⟨e⟩ := exists_mulEquiv_twoResidual_top W
  exact quasisimpleModTwoNonab_of_mulEquiv_self e
    (quasisimpleModTwoNonab_twoResidual_top_of_central (φ.subgroupMap W)
      (φ.subgroupMap_surjective W) (subgroupMap_ker_le_center φ hc)
      (closure_two_elements_eq_top hW2)
      (quasisimpleModTwoNonab_of_mulEquiv_self e₁.symm h))

end CFSG.AGLEmbeddingD2.Tits.GN516
