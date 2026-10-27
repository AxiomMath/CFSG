module

public import CFSG.CGT.PushingUpLit.T2K.Nat
public import CFSG.CGT.PushingUpLit.T2K.Basic

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] {L M : Subgroup G} {n : ℕ}

theorem nsmul_odd_eq {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0) {m : ℕ}
    (hm : Odd m) (a : A) : m • a = a := by
  obtain ⟨j, rfl⟩ := hm
  induction j with
  | zero => simp
  | succ j ih =>
    have : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
    rw [this, add_nsmul, ih, two_nsmul, hA, add_zero]

theorem sl2_center_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
  have h3 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  apply Subtype.ext
  rw [← hrA, h3]
  simp

namespace NatBlock

variable [Finite G]

theorem comm_mem_blockU (h : NatBlock L n) {x : G} (hc : ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L) :
    ∀ l ∈ L, ⁅x, l⁆ ∈ blockU L :=
  fun l hl => comm_mem_of_perfect h.perfect (oTwoIn_le L) (blockU_le_oTwoIn L) le_rfl hc l hl

theorem center_le (h : NatBlock L n) :
    L ⊓ Subgroup.centralizer (L : Set G) ≤ oTwoIn L := by
  rintro z ⟨hzL, hzc⟩
  let D := h.natData
  have h1 : D.φ ⟨z, hzL⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := D.φ_surj g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hzc l l.2
  rw [sl2_center_eq_bot, Subgroup.mem_bot] at h1
  exact (D.φ_ker _).1 h1

theorem odd_centralizes (h : NatBlock L n) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hodd : Odd (orderOf x)) (hz : ∀ v ∈ blockU L, ⁅x, v⁆ ∈ blockZ L) :
    ∀ l ∈ L, ⁅x, l⁆ = 1 := by
  let D := h.natData
  have hmemV : ∀ v : ↥(blockU L), ⁅x, (v : G)⁆ ∈ blockU L := fun v =>
    blockZ_le_blockU L (hz v v.2)
  have htriv : ∀ v : ↥(blockU L), D.ψ (conjU hx v) = D.ψ v := by
    intro v
    have e : conjU hx v = ⟨⁅x, (v : G)⁆, hmemV v⟩ * v := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e, map_mul, (D.ψ_ker _).2 (hz v v.2), one_mul]
  have hcO : ∀ l : ↥L, (⁅x, (l : G)⁆ : G) ∈ oTwoIn L := D.comm_mem_oTwoIn hx htriv
  have hcV : ∀ l ∈ L, ⁅x, l⁆ ∈ blockU L := fun l hl =>
    h.comm_mem_blockU (fun l' hl' => hcO ⟨l', hl'⟩) l hl
  have hexp : ∀ w : Fin 2 → GaloisField 2 n, w + w = 0 := fun w => by
    funext j
    exact CharTwo.add_self_eq_zero (w j)
  have hZ : ∀ l ∈ L, ⁅x, l⁆ ∈ blockZ L := by
    intro l hl
    set w : Fin 2 → GaloisField 2 n := Multiplicative.toAdd (D.ψ ⟨⁅x, l⁆, hcV l hl⟩) with hw
    have hy : ∀ k : ℕ, ∃ hk : x ^ k * l * (x ^ k)⁻¹ * l⁻¹ ∈ blockU L,
        D.ψ ⟨x ^ k * l * (x ^ k)⁻¹ * l⁻¹, hk⟩ = Multiplicative.ofAdd (k • w) := by
      intro k
      induction k with
      | zero =>
        refine ⟨by simp, ?_⟩
        have : (⟨x ^ 0 * l * (x ^ 0)⁻¹ * l⁻¹, by simp⟩ : ↥(blockU L)) = 1 :=
          Subtype.ext (by simp)
        rw [this, map_one]
        simp
      | succ k ih =>
        obtain ⟨hk, hψk⟩ := ih
        have e : x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ * l⁻¹ =
            (x * (x ^ k * l * (x ^ k)⁻¹ * l⁻¹) * x⁻¹) * ⁅x, l⁆ := by
          simp only [commutatorElement_def, pow_succ']
          group
        have hmem : x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ * l⁻¹ ∈ blockU L := by
          rw [e]
          exact mul_mem (conj_mem_blockU hx hk) (hcV l hl)
        refine ⟨hmem, ?_⟩
        have e2 : (⟨x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ * l⁻¹, hmem⟩ : ↥(blockU L)) =
            conjU hx ⟨_, hk⟩ * ⟨⁅x, l⁆, hcV l hl⟩ := Subtype.ext e
        rw [e2, map_mul, htriv, hψk, succ_nsmul, ofAdd_add]
        rfl
    obtain ⟨hm, hψm⟩ := hy (orderOf x)
    have hm1 : (⟨x ^ orderOf x * l * (x ^ orderOf x)⁻¹ * l⁻¹, hm⟩ : ↥(blockU L)) = 1 :=
      Subtype.ext (by simp)
    rw [hm1, map_one] at hψm
    have h0 : orderOf x • w = 0 := Multiplicative.ofAdd.injective hψm.symm
    rw [nsmul_odd_eq hexp hodd] at h0
    apply (D.ψ_ker ⟨⁅x, l⁆, hcV l hl⟩).1
    apply Multiplicative.toAdd.injective
    rw [← hw, h0]
    rfl
  exact fun l hl => comm_eq_one_of_perfect h.perfect hx
    (fun l' hl' => blockZ_le_centralizer L (hZ l' hl')) l hl

def cenQuot (L M : Subgroup G) (hMN : M ≤ Subgroup.normalizer (L : Set G)) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ v ∈ blockU L, ⁅x, v⁆ ∈ blockZ L}
  one_mem' := ⟨M.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun v hv => ?_⟩
    have e : ⁅x * y, v⁆ = (x * ⁅y, v⁆ * x⁻¹) * ⁅x, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (blockZ L).mul_mem (conj_mem_blockZ (hMN hxM) (hy v hv)) (hx v hv)
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun v hv => ?_⟩
    have e : ⁅x⁻¹, v⁆ = x⁻¹ * (⁅x, v⁆)⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_blockZ (hMN (M.inv_mem hxM)) ((blockZ L).inv_mem (hx v hv))

omit [Finite G] in
theorem mem_cenQuot {hMN : M ≤ Subgroup.normalizer (L : Set G)} {x : G} :
    x ∈ cenQuot L M hMN ↔ x ∈ M ∧ ∀ v ∈ blockU L, ⁅x, v⁆ ∈ blockZ L := Iff.rfl

theorem exists_pow_mem_centralizer (h : NatBlock L n)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ cenQuot L M hMN) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨k, hk⟩ := SixThree.exists_pow_two_pow_odd_orderOf x
  refine ⟨k, ?_⟩
  have hxk : x ^ 2 ^ k ∈ cenQuot L M hMN := (cenQuot L M hMN).pow_mem hx _
  have := h.odd_centralizes (hMN hxk.1) hk hxk.2
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := this l hl
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

omit [Finite G] in
theorem conj_mem_cenQuot {hMN : M ≤ Subgroup.normalizer (L : Set G)} {m y : G} (hm : m ∈ M)
    (hy : y ∈ cenQuot L M hMN) : m * y * m⁻¹ ∈ cenQuot L M hMN := by
  refine ⟨M.mul_mem (M.mul_mem hm hy.1) (M.inv_mem hm), fun v hv => ?_⟩
  have hv' : m⁻¹ * v * m ∈ blockU L := by
    have := conj_mem_blockU (hMN (M.inv_mem hm)) hv
    simpa using this
  have e : ⁅m * y * m⁻¹, v⁆ = m * ⁅y, m⁻¹ * v * m⁆ * m⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact conj_mem_blockZ (hMN hm) (hy.2 _ hv')

omit [Finite G] in
theorem le_normalizer_cenQuot (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (cenQuot L M hMN : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_cenQuot hm hy, fun hy => ?_⟩
  have := conj_mem_cenQuot (M.inv_mem hm) hy
  simpa [mul_assoc] using this

theorem centralizes_of_pow (h : NatBlock L n) {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hA : ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L) {k : ℕ}
    (hk : ∀ v ∈ blockU L, x ^ 2 ^ k * v * (x ^ 2 ^ k)⁻¹ = v) :
    x ∈ Subgroup.centralizer (blockU L : Set G) := by
  let D := h.natData
  obtain ⟨a, ha⟩ := D.exists_scalar hxN (fun l => hA l l.2)
  have ha1 : a = 1 := D.scalar_eq_one hxN ha hk
  have htriv : ∀ v : ↥(blockU L), D.ψ (conjU hxN v) = D.ψ v := by
    intro v
    rw [ha v, ha1]
    simp
  have hz : ∀ v ∈ blockU L, ⁅x, v⁆ ∈ blockZ L := by
    intro v hv
    have hmem : ⁅x, v⁆ ∈ blockU L := by
      have e : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact mul_mem (conj_mem_blockU hxN hv) (inv_mem hv)
    have e : (⟨⁅x, v⁆, hmem⟩ : ↥(blockU L)) = conjU hxN ⟨v, hv⟩ * (⟨v, hv⟩ : ↥(blockU L))⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def, mul_assoc])
    have : D.ψ ⟨⁅x, v⁆, hmem⟩ = 1 := by
      rw [e, map_mul, map_inv, htriv, mul_inv_cancel]
    exact (D.ψ_ker _).1 this
  have hxv := h.centralizes_blockU hxN hA hz
  refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
  have := hxv v hv
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem le_centralizer_of_two_quot (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {X : Subgroup G} (hXM : X ≤ M)
    (hXn : M ≤ Subgroup.normalizer (X : Set G))
    (hX : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G)) :
    X ≤ Subgroup.centralizer (blockU L : Set G) := by
  let D := h.natData
  intro x hxX
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hMN (hXM hxX)
  have hXL : X ⊓ L ≤ oTwoIn L := by
    refine SixThree.le_oTwoIn_of_isPGroup inf_le_right ?_ ?_
    · intro g
      obtain ⟨k, hk⟩ := hX g g.2.1
      have hg : (g : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨L.pow_mem g.2.2 _, hk⟩
      have hO : (g : G) ^ 2 ^ k ∈ oTwoIn L := h.center_le hg
      obtain ⟨i, hi⟩ := (isPGroup_oTwoIn L) ⟨_, hO⟩
      refine ⟨k + i, Subtype.ext ?_⟩
      have hi' : ((g : G) ^ 2 ^ k) ^ 2 ^ i = 1 := congrArg Subtype.val hi
      show (g : G) ^ 2 ^ (k + i) = 1
      rw [pow_add, pow_mul]
      exact hi'
    · intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hX' := Subgroup.mem_normalizer_iff.1 (hXn (hLM hl)) y
      have hL' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) y
      simp only [Subgroup.mem_inf, hX', hL']
  have hA : ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L := by
    intro l hl
    apply hXL
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : l * x⁻¹ * l⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (hXn (hLM hl)) x⁻¹).1 (X.inv_mem hxX)
      have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact X.mul_mem hxX h1
    · have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hxN l).1 hl
      have e : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact L.mul_mem h1 (L.inv_mem hl)
  obtain ⟨k, hk⟩ := hX x hxX
  have hk' : ∀ v ∈ blockU L, x ^ 2 ^ k * v * (x ^ 2 ^ k)⁻¹ = v := by
    intro v hv
    have := Subgroup.mem_centralizer_iff.1 hk v (blockU_le L hv)
    rw [← this, mul_inv_cancel_right]
  exact h.centralizes_of_pow hxN hA hk'

theorem centralizer_of_mem_cenQuot (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ cenQuot L M hMN) :
    x ∈ Subgroup.centralizer (blockU L : Set G) :=
  h.le_centralizer_of_two_quot hLM hMN (X := cenQuot L M hMN) (fun _ hy => hy.1)
    (le_normalizer_cenQuot hMN) (fun _ hy => h.exists_pow_mem_centralizer hMN hy) hx

omit [Finite G] in
theorem mem_cenQuot_of_centralizes (hMN : M ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hxM : x ∈ M) (hx : x ∈ Subgroup.centralizer (blockU L : Set G)) : x ∈ cenQuot L M hMN := by
  refine ⟨hxM, fun v hv => ?_⟩
  have := Subgroup.mem_centralizer_iff.1 hx v hv
  have e : ⁅x, v⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact this.symm
  rw [e]
  exact (blockZ L).one_mem

theorem two_quot_of_centralizes (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hxM : x ∈ M) (hx : x ∈ Subgroup.centralizer (blockU L : Set G)) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G) :=
  h.exists_pow_mem_centralizer hMN (mem_cenQuot_of_centralizes hMN hxM hx)

theorem comm_centralizer_mem_oTwoIn (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) {l : G} (hl : l ∈ L) :
    ⁅u, l⁆ ∈ oTwoIn L := by
  have huN : u ∈ Subgroup.normalizer (L : Set G) := hMN hu.1
  rw [← h.inf_centralizer_blockU]
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  · have h1 : u * l * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 huN l).1 hl
    have e : ⁅u, l⁆ = (u * l * u⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hl)
  · have hv' : l⁻¹ * v * l ∈ blockU L := by
      have := conj_mem_blockU (Subgroup.le_normalizer (L.inv_mem hl)) hv
      simpa using this
    have h1 : (l⁻¹ * v * l) * u = u * (l⁻¹ * v * l) := Subgroup.mem_centralizer_iff.1 hu.2 _ hv'
    have h2 : v * u = u * v := Subgroup.mem_centralizer_iff.1 hu.2 _ hv
    have h3 : u⁻¹ * (l⁻¹ * v * l) * u = l⁻¹ * v * l := by
      rw [mul_assoc, h1, inv_mul_cancel_left]
    have h4 : (u * l * u⁻¹ * l⁻¹) * v * (u * l * u⁻¹ * l⁻¹)⁻¹ = v := by
      calc (u * l * u⁻¹ * l⁻¹) * v * (u * l * u⁻¹ * l⁻¹)⁻¹
          = u * l * (u⁻¹ * (l⁻¹ * v * l) * u) * l⁻¹ * u⁻¹ := by group
        _ = u * l * (l⁻¹ * v * l) * l⁻¹ * u⁻¹ := by rw [h3]
        _ = u * v * u⁻¹ := by group
        _ = v := by rw [← h2, mul_inv_cancel_right]
    have h5 : ⁅u, l⁆ * v * ⁅u, l⁆⁻¹ = v := by
      simpa [commutatorElement_def] using h4
    exact (mul_inv_eq_iff_eq_mul.1 h5).symm

theorem comm_centralizer_mem_blockU (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    ∀ l ∈ L, ⁅u, l⁆ ∈ blockU L :=
  h.comm_mem_blockU (fun _ hl => h.comm_centralizer_mem_oTwoIn hMN hu hl)

theorem comm_mem_centralizer (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u u' : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (hu' : u' ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    ⁅u, u'⁆ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hκ : u⁻¹ * (l * u * l⁻¹) ∈ blockU L := by
    have := h.comm_centralizer_mem_blockU hMN (u := u⁻¹)
      ⟨M.inv_mem hu.1, Subgroup.inv_mem _ hu.2⟩ l hl
    simpa [commutatorElement_def, mul_assoc] using this
  have hκ' : u'⁻¹ * (l * u' * l⁻¹) ∈ blockU L := by
    have := h.comm_centralizer_mem_blockU hMN (u := u'⁻¹)
      ⟨M.inv_mem hu'.1, Subgroup.inv_mem _ hu'.2⟩ l hl
    simpa [commutatorElement_def, mul_assoc] using this
  set κ := u⁻¹ * (l * u * l⁻¹) with hκdef
  set κ' := u'⁻¹ * (l * u' * l⁻¹) with hκ'def
  have e1 : l * u * l⁻¹ = u * κ := by rw [hκdef]; group
  have e2 : l * u' * l⁻¹ = u' * κ' := by rw [hκ'def]; group
  have c1 : κ * u = u * κ := Subgroup.mem_centralizer_iff.1 hu.2 _ hκ
  have c2 : κ * u' = u' * κ := Subgroup.mem_centralizer_iff.1 hu'.2 _ hκ
  have c3 : κ' * u = u * κ' := Subgroup.mem_centralizer_iff.1 hu.2 _ hκ'
  have c4 : κ' * u' = u' * κ' := Subgroup.mem_centralizer_iff.1 hu'.2 _ hκ'
  have c5 : κ * κ' = κ' * κ := h.blockU_comm _ hκ _ hκ'
  have c3' : κ' * u⁻¹ = u⁻¹ * κ' := by
    calc κ' * u⁻¹ = u⁻¹ * (u * κ') * u⁻¹ := by group
      _ = u⁻¹ * (κ' * u) * u⁻¹ := by rw [c3]
      _ = u⁻¹ * κ' := by group
  have key : l * ⁅u, u'⁆ * l⁻¹ = ⁅u, u'⁆ := by
    calc l * ⁅u, u'⁆ * l⁻¹ = (l * u * l⁻¹) * (l * u' * l⁻¹) * (l * u * l⁻¹)⁻¹ *
          (l * u' * l⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      _ = u * κ * (u' * κ') * (u * κ)⁻¹ * (u' * κ')⁻¹ := by rw [e1, e2]
      _ = u * (κ * u') * κ' * κ⁻¹ * u⁻¹ * κ'⁻¹ * u'⁻¹ := by group
      _ = u * (u' * κ) * κ' * κ⁻¹ * u⁻¹ * κ'⁻¹ * u'⁻¹ := by rw [c2]
      _ = u * u' * (κ * κ' * κ⁻¹) * u⁻¹ * κ'⁻¹ * u'⁻¹ := by group
      _ = u * u' * κ' * u⁻¹ * κ'⁻¹ * u'⁻¹ := by rw [c5]; group
      _ = u * u' * (κ' * u⁻¹) * κ'⁻¹ * u'⁻¹ := by group
      _ = u * u' * (u⁻¹ * κ') * κ'⁻¹ * u'⁻¹ := by rw [c3']
      _ = ⁅u, u'⁆ := by simp only [commutatorElement_def]; group
  have := key
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem sq_mem_centralizer (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    u ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hκ : u⁻¹ * (l * u * l⁻¹) ∈ blockU L := by
    have := h.comm_centralizer_mem_blockU hMN (u := u⁻¹)
      ⟨M.inv_mem hu.1, Subgroup.inv_mem _ hu.2⟩ l hl
    simpa [commutatorElement_def, mul_assoc] using this
  set κ := u⁻¹ * (l * u * l⁻¹) with hκdef
  have e1 : l * u * l⁻¹ = u * κ := by rw [hκdef]; group
  have c1 : Commute κ u := Subgroup.mem_centralizer_iff.1 hu.2 _ hκ
  have hκ2 : κ ^ 2 = 1 := h.sq_eq_one_of_mem_blockU hκ
  have key : l * u ^ 2 * l⁻¹ = u ^ 2 := by
    calc l * u ^ 2 * l⁻¹ = (l * u * l⁻¹) ^ 2 := by rw [conj_pow]
      _ = (u * κ) ^ 2 := by rw [e1]
      _ = u ^ 2 * κ ^ 2 := c1.symm.mul_pow 2
      _ = u ^ 2 := by rw [hκ2, mul_one]
  have := key
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
