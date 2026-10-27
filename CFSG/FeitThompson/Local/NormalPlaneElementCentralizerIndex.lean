module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.ContinuousFunctionalCalculus

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup MulAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ} {P B Z P₂ : Subgroup G} {b : G}

theorem coe_inf_centralizer_self (P : Subgroup G) :
    ((P ⊓ centralizer (P : Set G) : Subgroup G) : Set G)
      = {z | z ∈ P ∧ ∀ x ∈ P, z * x = x * z} := by
  ext z
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_centralizer_iff,
    SetLike.mem_coe]
  exact ⟨fun h => ⟨h.1, fun x hx => (h.2 x hx).symm⟩, fun h => ⟨h.1, fun x hx => (h.2 x hx).symm⟩⟩

theorem inf_centralizer_self_subgroupOf (P : Subgroup G) :
    (P ⊓ centralizer (P : Set G)).subgroupOf P = Subgroup.center ↥P := by
  ext x
  simp only [mem_subgroupOf, Subgroup.mem_inf, SetLike.mem_coe, mem_centralizer_iff,
    Subgroup.mem_center_iff, Subtype.forall]
  exact ⟨fun h y hy => Subtype.ext (h.2 y hy),
    fun h => ⟨x.2, fun y hy => congrArg Subtype.val (h y hy)⟩⟩

theorem natCard_eq_sq_of_mulEquiv (hp : p.Prime)
    (h : Nonempty (↥B ≃* Multiplicative (ZMod p × ZMod p))) : Nat.card B = p ^ 2 := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, sq]

theorem sup_zpowers_eq_of_notMem [Finite G] (hp : p.Prime) (hB : Nat.card B = p ^ 2)
    (hZB : Z ≤ B) (hZ : Nat.card Z = p) (hbB : b ∈ B) (hbZ : b ∉ Z) :
    Z ⊔ zpowers b = B := by
  have hle : Z ⊔ zpowers b ≤ B := sup_le hZB (zpowers_le.mpr hbB)
  obtain ⟨j, hj2, hjeq⟩ := (Nat.dvd_prime_pow hp).mp (hB ▸ Subgroup.card_dvd_of_le hle)
  have hj : j = 2 := by
    by_contra hne
    have hcard : Nat.card (Z ⊔ zpowers b : Subgroup G) ≤ Nat.card Z := by
      rw [hjeq, hZ]
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    exact hbZ ((Subgroup.eq_of_le_of_card_ge le_sup_left hcard).ge (mem_sup_right (mem_zpowers b)))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hjeq, hj, hB])

theorem mem_centralizer_iff_le_centralizer_singleton {x : G} (B : Subgroup G) :
    x ∈ centralizer (B : Set G) ↔ B ≤ centralizer ({x} : Set G) := by
  simp only [SetLike.le_def, mem_centralizer_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  exact ⟨fun h y hy z hz => hz ▸ (h y hy).symm, fun h y hy => (h hy x rfl).symm⟩

theorem inf_centralizer_singleton_eq_inf_centralizer
    (hZP : Z ≤ centralizer (P : Set G)) (hBZb : Z ⊔ zpowers b = B) :
    P ⊓ centralizer ({b} : Set G) = P ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxP, hxb⟩ := hx
    refine ⟨hxP, ?_⟩
    rw [mem_centralizer_iff_le_centralizer_singleton, ← hBZb]
    refine sup_le (fun z hz => ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hZP hz) x hxP).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxb).symm
  · exact inf_le_inf_left P (centralizer_le (by
      rw [← hBZb]; exact Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers b))))

theorem inf_centralizer_singleton_eq_inf_centralizer' [Finite G] (hp : p.Prime)
    (hB : Nat.card B = p ^ 2) (hZB : Z ≤ B) (hZP : Z ≤ centralizer (P : Set G))
    (hZ : Nat.card Z = p) (hbB : b ∈ B) (hbZ : b ∉ Z) :
    P ⊓ centralizer ({b} : Set G) = P ⊓ centralizer (B : Set G) :=
  inf_centralizer_singleton_eq_inf_centralizer hZP
    (sup_zpowers_eq_of_notMem hp hB hZB hZ hbB hbZ)

theorem centralizer_subgroupOf (hBP : B ≤ P) :
    centralizer (↑(B.subgroupOf P) : Set ↥P) = (P ⊓ centralizer (B : Set G)).subgroupOf P := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_subgroupOf, Subgroup.mem_inf,
    Subtype.forall]
  exact ⟨fun h => ⟨x.2, fun y hy => congrArg Subtype.val (h y (hBP hy) hy)⟩,
    fun h y _ hy' => Subtype.ext (h.2 y hy')⟩

theorem normal_subgroupOf_inf_centralizer (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) :
    ((P ⊓ centralizer (B : Set G)).subgroupOf P).Normal := by
  rw [← centralizer_subgroupOf hBP]
  exact Subgroup.normal_centralizer

theorem normal_subgroupOf_inf_centralizer_singleton [Finite G] (hp : p.Prime)
    (hB : Nat.card B = p ^ 2) (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hZB : Z ≤ B)
    (hZP : Z ≤ centralizer (P : Set G)) (hZ : Nat.card Z = p) (hbB : b ∈ B) (hbZ : b ∉ Z) :
    ((P ⊓ centralizer ({b} : Set G)).subgroupOf P).Normal := by
  rw [inf_centralizer_singleton_eq_inf_centralizer' hp hB hZB hZP hZ hbB hbZ]
  exact normal_subgroupOf_inf_centralizer hBP hBn

theorem relIndex_inf_centralizer_singleton_le [Finite G] (hp : p.Prime) (hP : IsPGroup p ↥P)
    (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hB : Nat.card B = p ^ 2) (hbB : b ∈ B)
    (hb1 : b ≠ 1) : (P ⊓ centralizer ({b} : Set G)).relIndex P ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulAction ↥P G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  have hsmul : ∀ (x : ↥P) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun _ _ => rfl
  have hstab : stabilizer ↥P b = (P ⊓ centralizer ({b} : Set G)).subgroupOf P := by
    ext x
    rw [mem_stabilizer_iff, hsmul, mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨fun h => ⟨x.2, mem_centralizer_singleton_iff.mpr ?_⟩, fun h => ?_⟩
    · conv_rhs => rw [← h]
      group
    · rw [mem_centralizer_singleton_iff.mp h.2]; group
  have horb : orbit ↥P b ⊆ (B : Set G) \ {1} := by
    rintro y ⟨x, hy⟩
    simp only at hy
    rw [hsmul] at hy
    subst hy
    refine ⟨(Subgroup.normal_subgroupOf_iff hBP).mp hBn b x hbB x.2, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun h => hb1 (by simpa using h)
  have hindex : (P ⊓ centralizer ({b} : Set G)).relIndex P = (orbit ↥P b).ncard := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  have hBcard : ((B : Set G) \ {1}).ncard = p ^ 2 - 1 := by
    rw [Set.ncard_sdiff (by simp), Set.ncard_singleton, ← Nat.card_coe_set_eq]
    congr 1
  have hle : (P ⊓ centralizer ({b} : Set G)).relIndex P ≤ p ^ 2 - 1 := by
    rw [hindex]; exact hBcard ▸ Set.ncard_le_ncard horb
  obtain ⟨n, hn⟩ := hP.index ((P ⊓ centralizer ({b} : Set G)).subgroupOf P)
  rw [show ((P ⊓ centralizer ({b} : Set G)).subgroupOf P).index
      = (P ⊓ centralizer ({b} : Set G)).relIndex P from rfl] at hn
  rw [hn] at hle ⊢
  rcases Nat.lt_or_ge n 2 with h | h
  · calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  · exact absurd hle (by
      have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h
      have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      have hp1 : 1 < p ^ 2 := by
        calc 1 < p := hp.one_lt
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos one_le_two
      omega)

private theorem relIndex_le_of_natCard_le {P₁ : Subgroup G} [Finite G]
    (h₁₂ : P₁ ≤ P₂) (h₁P : P₁ ≤ P) (hcard : Nat.card P₂ ≤ Nat.card P)
    (hPle : P₁.relIndex P ≤ p) : P₁.relIndex P₂ ≤ p := by
  have key : ∀ {K : Subgroup G} (_ : P₁ ≤ K), P₁.relIndex K * Nat.card P₁ = Nat.card K := by
    intro K hK
    rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv,
      Subgroup.index_mul_card]
  have h2 := key h₁₂
  have h1 := key h₁P
  have hpos : 0 < Nat.card P₁ := Nat.card_pos
  have : P₁.relIndex P₂ * Nat.card P₁ ≤ P₁.relIndex P * Nat.card P₁ := by
    rw [h1, h2]; exact hcard
  have := Nat.le_of_mul_le_mul_right this hpos
  exact this.trans hPle

theorem relIndex_le_of_isPGroup_sylow [Finite G] (hp : p.Prime) (hPsylow : ∀ Q : Sylow p G,
      Nat.card Q ≤ Nat.card P) (hP : IsPGroup p ↥P) (hP₂ : IsPGroup p ↥P₂)
    (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hB : Nat.card B = p ^ 2) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (h₁₂ : P ⊓ centralizer ({b} : Set G) ≤ P₂) :
    (P ⊓ centralizer ({b} : Set G)).relIndex P₂ ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hP₂.exists_le_sylow
  have hcard : Nat.card P₂ ≤ Nat.card P :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hQ)).trans (hPsylow Q)
  exact relIndex_le_of_natCard_le h₁₂ inf_le_left hcard
    (relIndex_inf_centralizer_singleton_le hp hP hBP hBn hB hbB hb1)

theorem normal_subgroupOf_of_isPGroup_sylow [Finite G] (hp : p.Prime) (hPsylow : ∀ Q : Sylow p G,
      Nat.card Q ≤ Nat.card P) (hP : IsPGroup p ↥P) (hP₂ : IsPGroup p ↥P₂)
    (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hB : Nat.card B = p ^ 2) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (h₁₂ : P ⊓ centralizer ({b} : Set G) ≤ P₂) :
    ((P ⊓ centralizer ({b} : Set G)).subgroupOf P₂).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  set P₁ := P ⊓ centralizer ({b} : Set G) with hP₁def
  have hle : P₁.relIndex P₂ ≤ p :=
    relIndex_le_of_isPGroup_sylow hp hPsylow hP hP₂ hBP hBn hB hbB hb1 h₁₂
  obtain ⟨n, hn⟩ := hP₂.index (P₁.subgroupOf P₂)
  have hnn : (P₁.subgroupOf P₂).index = p ^ n := hn
  have hn01 : n = 0 ∨ n = 1 := by
    by_contra hcon
    have h2 : 2 ≤ n := by omega
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h2
    have hlt : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt one_lt_two
    have : (P₁.subgroupOf P₂).index ≤ p := hle
    rw [hnn] at this
    omega
  rcases hn01 with rfl | rfl
  ·
    exact Subgroup.normal_of_index_eq_one (by rw [hnn]; simp)
  ·
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    obtain ⟨m, hm⟩ := hP₂.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      have hdvd : (P₁.subgroupOf P₂).index ∣ Nat.card ↥P₂ := Subgroup.index_dvd_card _
      rw [hnn, hm, pow_one, pow_zero] at hdvd
      exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hp.one_lt; omega)
    rw [hnn, pow_one, hm]
    exact (hp.pow_minFac hm0).symm

theorem centralizer_eq_and_normal_and_relIndex_le [Finite G] (hp : p.Prime)
    (hP : IsPGroup p ↥P) (hPsylow : ∀ Q : Sylow p G, Nat.card Q ≤ Nat.card P)
    (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal) (hB : Nat.card B = p ^ 2)
    (hZB : Z ≤ B) (hZP : Z ≤ centralizer (P : Set G)) (hZ : Nat.card Z = p)
    (hbB : b ∈ B) (hbZ : b ∉ Z) :
    P ⊓ centralizer ({b} : Set G) = P ⊓ centralizer (B : Set G) ∧
      ((P ⊓ centralizer ({b} : Set G)).subgroupOf P).Normal ∧
      (P ⊓ centralizer ({b} : Set G)).relIndex P ≤ p ∧
      ∀ P₂ : Subgroup G, IsPGroup p ↥P₂ → P ⊓ centralizer ({b} : Set G) ≤ P₂ →
        (P ⊓ centralizer ({b} : Set G)).relIndex P₂ ≤ p ∧
          ((P ⊓ centralizer ({b} : Set G)).subgroupOf P₂).Normal := by
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Z.one_mem)
  refine ⟨inf_centralizer_singleton_eq_inf_centralizer' hp hB hZB hZP hZ hbB hbZ,
    normal_subgroupOf_inf_centralizer_singleton hp hB hBP hBn hZB hZP hZ hbB hbZ,
    relIndex_inf_centralizer_singleton_le hp hP hBP hBn hB hbB hb1,
    fun P₂ hP₂ h₁₂ => ⟨?_, ?_⟩⟩
  · exact relIndex_le_of_isPGroup_sylow hp hPsylow hP hP₂ hBP hBn hB hbB hb1 h₁₂
  · exact normal_subgroupOf_of_isPGroup_sylow hp hPsylow hP hP₂ hBP hBn hB hbB hb1 h₁₂

end

end CFSG.FeitThompson
