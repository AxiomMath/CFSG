module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Adapters.TauCetiExceptional.Interface
import CFSG.Certificates.Kernel.G2Three.Tables
import Certificates.Data.Kernel.G2Three.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.KC.G2Three CFSG.KD.G2Three CFSG.KC.Ord CFSG.KS.Mat3
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

private theorem consts : consts3OK 14 5 196 LO RM CI ONE UP = true := by quickRfl

private abbrev Dat (c : List ℕ) (A : ℕ) : Prop := canon14 c = true ∧ pk c = A

private theorem dx0 : Dat x0c (pk x0c) := ⟨by quickRfl, rfl⟩
private theorem dx1 : Dat x1c (pk x1c) := ⟨by quickRfl, rfl⟩
private theorem dy0 : Dat y0c (pk y0c) := ⟨by quickRfl, rfl⟩
private theorem done : Dat one14 ONE := ⟨canon14_one14, Nat.eq_of_beq_eq_true (by quickRfl)⟩

private noncomputable def B₁ : ℕ := MUL (pk x0c) (pk x0c)

private noncomputable def B₂ : ℕ :=
  MUL (MUL (MUL (MUL (MUL (pk y0c) (pk y0c)) (pk x0c)) (pk x1c)) (MUL (pk x0c) (pk x0c))) (pk y0c)

private noncomputable def B₃ : ℕ :=
  MUL (MUL (MUL (MUL (MUL (pk x1c) (pk x1c)) (pk x0c)) (MUL (pk x1c) (pk x1c))) (pk x0c))
    (MUL (pk x1c) (pk x1c))

private noncomputable def B₄ : ℕ :=
  MUL (MUL (MUL (MUL (pk x1c) (pk x0c)) (pk x1c)) (pk x0c)) (pk x1c)

private theorem d₁ : Dat (sq14 x0c) B₁ := mulE consts dx0 dx0

private theorem d₂ : Dat (mul14 (mul14 (mul14 (mul14 (sq14 y0c) x0c) x1c) (sq14 x0c)) y0c) B₂ :=
  mulE consts (mulE consts (mulE consts (mulE consts (mulE consts dy0 dy0) dx0) dx1)
    (mulE consts dx0 dx0)) dy0

private theorem d₃ :
    Dat (mul14 (mul14 (mul14 (mul14 (sq14 x1c) x0c) (sq14 x1c)) x0c) (sq14 x1c)) B₃ :=
  mulE consts (mulE consts (mulE consts (mulE consts (mulE consts dx1 dx1) dx0)
    (mulE consts dx1 dx1)) dx0) (mulE consts dx1 dx1)

private theorem d₄ : Dat (mul14 (mul14 (mul14 (mul14 x1c x0c) x1c) x0c) x1c) B₄ :=
  mulE consts (mulE consts (mulE consts (mulE consts dx1 dx0) dx1) dx0) dx1

private theorem comm_ok : Nat.beq (MUL B₁ B₂) (MUL B₂ B₁) = true ∧
    Nat.beq (MUL B₁ B₃) (MUL B₃ B₁) = true ∧ Nat.beq (MUL B₁ B₄) (MUL B₄ B₁) = true ∧
    Nat.beq (MUL B₂ B₃) (MUL B₃ B₂) = true ∧ Nat.beq (MUL B₂ B₄) (MUL B₄ B₂) = true ∧
    Nat.beq (MUL B₃ B₄) (MUL B₄ B₃) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

private theorem cube_ok : Nat.beq (MUL B₁ (MUL B₁ B₁)) ONE = true ∧
    Nat.beq (MUL B₂ (MUL B₂ B₂)) ONE = true ∧ Nat.beq (MUL B₃ (MUL B₃ B₃)) ONE = true ∧
    Nat.beq (MUL B₄ (MUL B₄ B₄)) ONE = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

private def pw3 (c : List ℕ) : ℕ → List ℕ
  | 0 => one14
  | 1 => c
  | _ + 2 => sq14 c

private noncomputable def pwP (A : ℕ) : ℕ → ℕ
  | 0 => ONE
  | 1 => A
  | _ + 2 => MUL A A

private theorem dat_pw {c : List ℕ} {A : ℕ} (hc : Dat c A) (k : ℕ) : Dat (pw3 c k) (pwP A k) := by
  rcases k with _ | _ | k
  · rw [pw3.eq_1, pwP.eq_1]
    exact done
  · rw [pw3.eq_2, pwP.eq_2]
    exact hc
  · rw [pw3.eq_3, pwP.eq_3]
    exact mulE consts hc hc

private noncomputable def pv (n : ℕ) : ℕ :=
  MUL (MUL (MUL (pwP B₁ (n % 3)) (pwP B₂ (n / 3 % 3))) (pwP B₃ (n / 9 % 3))) (pwP B₄ (n / 27 % 3))

private def distinctB : List ℕ → Bool
  | [] => true
  | a :: l => l.all (fun b => !Nat.beq a b) && distinctB l

private theorem nodup_of_distinctB : ∀ {l : List ℕ}, distinctB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [distinctB, Bool.and_eq_true, List.all_eq_true] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodup_of_distinctB h.2⟩
    have := h.1 a ha
    rw [Nat.beq_refl, Bool.not_true] at this
    exact Bool.false_ne_true this

private theorem distinct_ok : distinctB ((List.range 81).map pv) = true := by quickRfl

private theorem pv_inj {m n : ℕ} (hm : m < 81) (hn : n < 81) (h : pv m = pv n) : m = n :=
  List.inj_on_of_nodup_map (nodup_of_distinctB distinct_ok) (List.mem_range.2 hm)
    (List.mem_range.2 hn) h

private theorem commutes_of {c d : List ℕ} {C D : ℕ} (hc : Dat c C) (hd : Dat d D)
    (h : Nat.beq (MUL C D) (MUL D C) = true) : commutes c d = true :=
  (beq_pk (canon14_mul14 c d) (canon14_mul14 d c)).trans
    ((congrArg₂ Nat.beq (mulE consts hc hd).2 (mulE consts hd hc).2).trans h)

private theorem cube_of {c : List ℕ} {C : ℕ} (hc : Dat c C)
    (h : Nat.beq (MUL C (MUL C C)) ONE = true) : mul14 c (sq14 c) = one14 :=
  pk_inj (canon14_mul14 _ _) canon14_one14
    (((mulE consts hc (mulE consts hc hc)).2.trans (Nat.eq_of_beq_eq_true h)).trans done.2.symm)

private theorem coe_pow {g : GL14} {c : List ℕ} (hg : (g : M14) = dec14 c) :
    ∀ {k : ℕ}, k < 3 → ((g ^ k : GL14) : M14) = dec14 (pw3 c k)
  | 0, _ => by rw [pow_zero, Units.val_one, pw3.eq_1, dec14_one14]
  | 1, _ => by rw [pow_one, hg, pw3.eq_2]
  | 2, _ => by
    rw [pw3.eq_3]
    exact coe_sq hg
  | _ + 3, h => absurd h (by omega)

private theorem isElemAbelian_closure_four {G : Type*} [Group G] {a₁ a₂ a₃ a₄ : G}
    (h12 : a₁ * a₂ = a₂ * a₁) (h13 : a₁ * a₃ = a₃ * a₁) (h14 : a₁ * a₄ = a₄ * a₁)
    (h23 : a₂ * a₃ = a₃ * a₂) (h24 : a₂ * a₄ = a₄ * a₂) (h34 : a₃ * a₄ = a₄ * a₃)
    (c1 : a₁ ^ 3 = 1) (c2 : a₂ ^ 3 = 1) (c3 : a₃ ^ 3 = 1) (c4 : a₄ ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure {a₁, a₂, a₃, a₄}) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a₁, a₂, a₃, a₄} : Set G)) := by
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption | exact Eq.symm ‹_›
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [Commute.mul_pow hxy 3, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

private theorem mem_closure_four {G : Type*} [Group G] (a₁ a₂ a₃ a₄ : G) (i j k l : ℕ) :
    a₁ ^ i * a₂ ^ j * a₃ ^ k * a₄ ^ l ∈ Subgroup.closure {a₁, a₂, a₃, a₄} := by
  have hmem : ∀ g ∈ ({a₁, a₂, a₃, a₄} : Set G), g ∈ Subgroup.closure {a₁, a₂, a₃, a₄} :=
    fun g hg => Subgroup.subset_closure hg
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_ <;>
    refine Subgroup.pow_mem _ (hmem _ ?_) _ <;> simp

section


private noncomputable def b₁ : GL14 := gX 0 ^ 2

private noncomputable def b₂ : GL14 := gY 0 ^ 2 * gX 0 * gX 1 * gX 0 ^ 2 * gY 0

private noncomputable def b₃ : GL14 := gX 1 ^ 2 * gX 0 * gX 1 ^ 2 * gX 0 * gX 1 ^ 2

private noncomputable def b₄ : GL14 := gX 1 * gX 0 * gX 1 * gX 0 * gX 1

private theorem coe_b₁ : (b₁ : M14) = dec14 (sq14 x0c) := coe_sq coe_gX0

private theorem coe_b₂ :
    (b₂ : M14) = dec14 (mul14 (mul14 (mul14 (mul14 (sq14 y0c) x0c) x1c) (sq14 x0c)) y0c) :=
  coe_mul (coe_mul (coe_mul (coe_mul (coe_sq coe_gY0) coe_gX0) coe_gX1) (coe_sq coe_gX0)) coe_gY0

private theorem coe_b₃ :
    (b₃ : M14) = dec14 (mul14 (mul14 (mul14 (mul14 (sq14 x1c) x0c) (sq14 x1c)) x0c) (sq14 x1c)) :=
  coe_mul (coe_mul (coe_mul (coe_mul (coe_sq coe_gX1) coe_gX0) (coe_sq coe_gX1)) coe_gX0)
    (coe_sq coe_gX1)

private theorem coe_b₄ : (b₄ : M14) = dec14 (mul14 (mul14 (mul14 (mul14 x1c x0c) x1c) x0c) x1c) :=
  coe_mul (coe_mul (coe_mul (coe_mul coe_gX1 coe_gX0) coe_gX1) coe_gX0) coe_gX1

private theorem mem_b : b₁ ∈ R3 ∧ b₂ ∈ R3 ∧ b₃ ∈ R3 ∧ b₄ ∈ R3 := by
  have x0 := gX_mem 0
  have x1 := gX_mem 1
  have y0 := gY_mem 0
  refine ⟨R3.pow_mem x0 2, ?_, ?_, ?_⟩
  · exact R3.mul_mem (R3.mul_mem (R3.mul_mem (R3.mul_mem (R3.pow_mem y0 2) x0) x1)
      (R3.pow_mem x0 2)) y0
  · exact R3.mul_mem (R3.mul_mem (R3.mul_mem (R3.mul_mem (R3.pow_mem x1 2) x0)
      (R3.pow_mem x1 2)) x0) (R3.pow_mem x1 2)
  · exact R3.mul_mem (R3.mul_mem (R3.mul_mem (R3.mul_mem x1 x0) x1) x0) x1

private theorem comm_b : b₁ * b₂ = b₂ * b₁ ∧ b₁ * b₃ = b₃ * b₁ ∧ b₁ * b₄ = b₄ * b₁ ∧
    b₂ * b₃ = b₃ * b₂ ∧ b₂ * b₄ = b₄ * b₂ ∧ b₃ * b₄ = b₄ * b₃ := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := comm_ok
  exact ⟨commute_of_commutes coe_b₁ coe_b₂ (commutes_of d₁ d₂ h12),
    commute_of_commutes coe_b₁ coe_b₃ (commutes_of d₁ d₃ h13),
    commute_of_commutes coe_b₁ coe_b₄ (commutes_of d₁ d₄ h14),
    commute_of_commutes coe_b₂ coe_b₃ (commutes_of d₂ d₃ h23),
    commute_of_commutes coe_b₂ coe_b₄ (commutes_of d₂ d₄ h24),
    commute_of_commutes coe_b₃ coe_b₄ (commutes_of d₃ d₄ h34)⟩

private theorem cube_b : b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₃ ^ 3 = 1 ∧ b₄ ^ 3 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := cube_ok
  exact ⟨pow_three_of_code coe_b₁ (cube_of d₁ h1), pow_three_of_code coe_b₂ (cube_of d₂ h2),
    pow_three_of_code coe_b₃ (cube_of d₃ h3), pow_three_of_code coe_b₄ (cube_of d₄ h4)⟩

private noncomputable def π (n : ℕ) : GL14 :=
  b₁ ^ (n % 3) * b₂ ^ (n / 3 % 3) * b₃ ^ (n / 9 % 3) * b₄ ^ (n / 27 % 3)

private theorem π_inj {m n : ℕ} (hm : m < 81) (hn : n < 81) (h : π m = π n) : m = n := by
  have h3 : ∀ k, k % 3 < 3 := fun k => Nat.mod_lt _ (by norm_num)
  have hc : ∀ k, ((π k : GL14) : M14) = dec14 (mul14 (mul14 (mul14
      (pw3 (sq14 x0c) (k % 3))
      (pw3 (mul14 (mul14 (mul14 (mul14 (sq14 y0c) x0c) x1c) (sq14 x0c)) y0c) (k / 3 % 3)))
      (pw3 (mul14 (mul14 (mul14 (mul14 (sq14 x1c) x0c) (sq14 x1c)) x0c) (sq14 x1c)) (k / 9 % 3)))
      (pw3 (mul14 (mul14 (mul14 (mul14 x1c x0c) x1c) x0c) x1c) (k / 27 % 3))) := fun k =>
    coe_mul (coe_mul (coe_mul (coe_pow coe_b₁ (h3 k)) (coe_pow coe_b₂ (h3 _)))
      (coe_pow coe_b₃ (h3 _))) (coe_pow coe_b₄ (h3 _))
  have hd : ∀ k, Dat (mul14 (mul14 (mul14
      (pw3 (sq14 x0c) (k % 3))
      (pw3 (mul14 (mul14 (mul14 (mul14 (sq14 y0c) x0c) x1c) (sq14 x0c)) y0c) (k / 3 % 3)))
      (pw3 (mul14 (mul14 (mul14 (mul14 (sq14 x1c) x0c) (sq14 x1c)) x0c) (sq14 x1c)) (k / 9 % 3)))
      (pw3 (mul14 (mul14 (mul14 (mul14 x1c x0c) x1c) x0c) x1c) (k / 27 % 3))) (pv k) := fun k =>
    mulE consts (mulE consts (mulE consts (dat_pw d₁ _) (dat_pw d₂ _)) (dat_pw d₃ _)) (dat_pw d₄ _)
  have heq := dec14_injective (hd m).1 (hd n).1
    ((hc m).symm.trans ((congrArg Units.val h).trans (hc n)))
  exact pv_inj hm hn (((hd m).2.symm.trans (congrArg pk heq)).trans (hd n).2)

private noncomputable def E : Subgroup GL14 := Subgroup.closure {b₁, b₂, b₃, b₄}

private theorem E_le : E ≤ R3 := by
  obtain ⟨m1, m2, m3, m4⟩ := mem_b
  rw [E, Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
    Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨m1, m2, m3, m4⟩

theorem four_le_pRank_three_R3 : 4 ≤ CFSG.Open.pRank 3 R3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := comm_b
  obtain ⟨c1, c2, c3, c4⟩ := cube_b
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_closure_four h12 h13 h14 h23 h24 h34 c1 c2 c3 c4
  have hp : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h81 : 81 ≤ Nat.card E := by
    have hinj : Function.Injective (fun n : Fin 81 =>
        (⟨π n, mem_closure_four b₁ b₂ b₃ b₄ _ _ _ _⟩ : E)) := fun m n h =>
      Fin.ext (π_inj m.2 n.2 (congrArg Subtype.val h))
    simpa using Nat.card_le_card_of_injective _ hinj
  have hk4 : 4 ≤ k := by
    rw [hk] at h81
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk4.trans (CFSG.SectionRank.le_pRank (by norm_num) E_le hE hk)


theorem four_le_pRank_of_G2_three
    (hG2 : CFSG.TauCetiBridge.UntwistedBridge .G2 TauCeti.LieTypeIndex.G2) {K : Type} [Group K]
    [Finite K] {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hp : q.p = 3)
    (he : q.exponent = 1) (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, he, pow_one]
  obtain ⟨φ⟩ := hG2 q hv (by rw [hp]; decide) (ZMod 3) hK
  have h1 := @CFSG.SectionRank.pRank_top_eq_of_mulEquiv K _ _ 3 H3 R3.toGroup _ (by norm_num)
    ((e.trans φ.symm).trans adjointQuotientEquivR3)
  have h2 := @CFSG.SectionRank.pRank_eq_pRank_top_subgroup GL14 _ _ 3 R3
  exact (four_le_pRank_three_R3.trans_eq h2).trans_eq h1.symm
end

end CFSG.LocalAnalysis.AGL81I.Section3
