module


public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

private lemma normalizes_closure_commutator {B Y : Subgroup G} {b : G}
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hb : b ∈ B) :
    B ≤ Subgroup.normalizer
      (Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆} : Set G) := by
  rw [Subgroup.le_normalizer_closure_iff]
  rintro b' hb' z ⟨y, hy, rfl⟩
  have hby : b' * y * b'⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hBY hb') y).mp hy
  have hbb : b' * b * b'⁻¹ = b := by
    rw [hB b' hb' b hb]
    group
  have heq : b' * ⁅y, b⁆ * b'⁻¹ = ⁅b' * y * b'⁻¹, b⁆ := by
    calc
      b' * ⁅y, b⁆ * b'⁻¹ = ⁅b' * y * b'⁻¹, b' * b * b'⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      _ = ⁅b' * y * b'⁻¹, b⁆ := by rw [hbb]
  rw [heq]
  exact Subgroup.subset_closure ⟨b' * y * b'⁻¹, hby, rfl⟩

private lemma le_sup_closure_commutator_of_coprime {B X C Y : Subgroup G} {b : G}
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card X))
    (hsolv : Group.IsSolvable X)
    (hfix : ∀ b ∈ B, b ≠ 1 → ∀ x ∈ X, b * x * b⁻¹ = x → x ∈ C)
    (hYleX : Y ≤ X) (hb : b ∈ B) (hb1 : b ≠ 1) :
    Y ≤ Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆} ⊔ C := by
  let Yb : Subgroup G := Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆}
  change Y ≤ Yb ⊔ C
  have hB_Yb : B ≤ Subgroup.normalizer (Yb : Set G) :=
    normalizes_closure_commutator hB hBY hb
  have hbY : b ∈ Subgroup.normalizer (Y : Set G) := hBY hb
  have hcardZ : Nat.card (Subgroup.zpowers b) ∣ Nat.card B := by
    rw [Nat.card_zpowers]
    exact Subgroup.orderOf_dvd_natCard B hb
  have hcardY : Nat.card Y ∣ Nat.card X := Subgroup.card_dvd_of_le hYleX
  have hcopY : Nat.Coprime (Nat.card (Subgroup.zpowers b)) (Nat.card Y) :=
    Nat.Coprime.of_dvd_right hcardY (Nat.Coprime.of_dvd_left hcardZ hcop)
  have hsolvY : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYleX)
      (Subgroup.inclusion_injective hYleX)
  have hcopAction := CFSG.AGLEmbedding.le_commutator_sup_inf_centralizer_of_coprime
    (R := Y) (A := Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hbY) hcopY hsolvY
  have hYinf_le_C : Y ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) ≤ C := by
    intro y hy
    have hcomm : b * y * b⁻¹ = y := by
      have hcomm' : b * y = y * b :=
        Subgroup.mem_centralizer_iff.mp hy.2 b (Subgroup.mem_zpowers b)
      calc b * y * b⁻¹ = (y * b) * b⁻¹ := by rw [hcomm']
        _ = y := by simp
    exact hfix b hb hb1 y (hYleX hy.1) hcomm
  have hpow_nat : ∀ n : ℕ, ∀ y ∈ Y, ⁅y, b ^ n⁆ ∈ Yb := by
    intro n
    induction n with
    | zero =>
        intro y _
        simp
    | succ n ih =>
        intro y hy
        rw [pow_succ, CFSG.commutator_mul_right]
        have hbpow : b ^ n ∈ Subgroup.normalizer (Yb : Set G) :=
          (Subgroup.zpowers_le.mpr (hB_Yb hb))
            (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) n)
        have hconj : b ^ n * ⁅y, b⁆ * (b ^ n)⁻¹ ∈ Yb :=
          (Subgroup.mem_normalizer_iff.mp hbpow ⁅y, b⁆).mp
            (Subgroup.subset_closure ⟨y, hy, rfl⟩)
        rw [show ⁅y, b ^ n⁆ * b ^ n * ⁅y, b⁆ * (b ^ n)⁻¹ =
            ⁅y, b ^ n⁆ * (b ^ n * ⁅y, b⁆ * (b ^ n)⁻¹) by group]
        exact Yb.mul_mem (ih y hy) hconj
  have hpow_neg : ∀ n : ℕ, ∀ z ∈ Yb, (b ^ n)⁻¹ * z * b ^ n ∈ Yb := by
    intro n z hz
    have hbpow : (b ^ n)⁻¹ ∈ Subgroup.normalizer (Yb : Set G) :=
      Subgroup.inv_mem _ ((Subgroup.zpowers_le.mpr (hB_Yb hb))
        (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) n))
    simpa using (Subgroup.mem_normalizer_iff.mp hbpow z).mp hz
  have hcomm_le_Yb : ⁅Y, Subgroup.zpowers b⁆ ≤ Yb := by
    rw [Subgroup.commutator_le]
    intro y hy z hz
    obtain ⟨n, rfl⟩ := (Subgroup.mem_zpowers_iff).mp hz
    cases n with
    | ofNat n => simpa using hpow_nat n y hy
    | negSucc n =>
        rw [zpow_negSucc, CFSG.commutator_inv_right]
        exact hpow_neg (n + 1) _ (Yb.inv_mem (hpow_nat (n + 1) y hy))
  calc Y ≤ ⁅Y, Subgroup.zpowers b⁆ ⊔
        (Y ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G)) := hcopAction
    _ ≤ Yb ⊔ C := sup_le (hcomm_le_Yb.trans le_sup_left)
        (hYinf_le_C.trans le_sup_right)

private lemma closure_commutator_eq_of_minimal {B X C Y : Subgroup G} {b : G}
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card X))
    (hsolv : Group.IsSolvable X)
    (hfix : ∀ b ∈ B, b ≠ 1 → ∀ x ∈ X, b * x * b⁻¹ = x → x ∈ C)
    (hYleX : Y ≤ X) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hXY : X ≤ Y ⊔ C)
    (hminY : ∀ Z : Subgroup G, Z ≤ X → B ≤ Subgroup.normalizer (Z : Set G) →
      X ≤ Z ⊔ C → Z ≤ Y → Y ≤ Z)
    (hb : b ∈ B) (hb1 : b ≠ 1) :
    Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆} = Y := by
  let Yb : Subgroup G := Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆}
  change Yb = Y
  have hY_le_Yb_sup_C : Y ≤ Yb ⊔ C :=
    le_sup_closure_commutator_of_coprime hB hBY hcop hsolv hfix hYleX hb hb1
  have hYb_le_Y : Yb ≤ Y := by
    refine (Subgroup.closure_le Y).2 ?_
    rintro z ⟨y, hy, rfl⟩
    have hby : b * y⁻¹ * b⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hBY hb) y⁻¹).mp (Y.inv_mem hy)
    simpa [commutatorElement_def, mul_assoc] using Y.mul_mem hy hby
  have hB_Yb : B ≤ Subgroup.normalizer (Yb : Set G) :=
    normalizes_closure_commutator hB hBY hb
  have hYb_mem : Yb ∈ {Z : Subgroup G | Z ≤ X ∧
      B ≤ Subgroup.normalizer (Z : Set G) ∧ X ≤ Z ⊔ C} :=
    ⟨hYb_le_Y.trans hYleX, hB_Yb, hXY.trans (sup_le hY_le_Yb_sup_C le_sup_right)⟩
  exact (le_antisymm (hminY Yb hYb_mem.1 hYb_mem.2.1 hYb_mem.2.2 hYb_le_Y)
    hYb_le_Y).symm

theorem exists_closure_commutator_eq_of_coprime {B X C : Subgroup G}
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card X))
    (hsolv : Group.IsSolvable X)
    (hfix : ∀ b ∈ B, b ≠ 1 → ∀ x ∈ X, b * x * b⁻¹ = x → x ∈ C) :
    ∃ Y ≤ X, B ≤ Subgroup.normalizer (Y : Set G) ∧ X ≤ Y ⊔ C ∧
      ∀ b ∈ B, b ≠ 1 → Subgroup.closure {z : G | ∃ y ∈ Y, z = ⁅y, b⁆} = Y := by
  classical
  let S : Set (Subgroup G) :=
    {Y | Y ≤ X ∧ B ≤ Subgroup.normalizer (Y : Set G) ∧ X ≤ Y ⊔ C}
  have hSne : S.Nonempty := ⟨X, le_rfl, hBX, by simp⟩
  obtain ⟨Y, hYmin⟩ := (Set.toFinite S).exists_minimal hSne
  have hYleX : Y ≤ X := hYmin.prop.1
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := hYmin.prop.2.1
  have hXY : X ≤ Y ⊔ C := hYmin.prop.2.2
  have hminY : ∀ Z : Subgroup G, Z ≤ X → B ≤ Subgroup.normalizer (Z : Set G) →
      X ≤ Z ⊔ C → Z ≤ Y → Y ≤ Z :=
    fun Z hZX hBZ hXZ hZY => hYmin.le_of_le ⟨hZX, hBZ, hXZ⟩ hZY
  exact ⟨Y, hYleX, hBY, hXY,
    fun b hb hb1 => closure_commutator_eq_of_minimal hB hcop hsolv hfix hYleX hBY hXY
      hminY hb hb1⟩

private lemma exists_commutator_mem_of_fixed_coset {p : ℕ} [Fact p.Prime]
    {P X C : Subgroup G} (hP : IsPGroup p P) (hXP : X ≤ P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hPC : P ≤ Subgroup.normalizer (C : Set G))
    (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (hCX : C < X) :
    ∃ x ∈ X, x ∉ C ∧ ∀ s ∈ P, ⁅s, x⁆ ∈ C := by
  classical
  have hCnormal : (C.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_lt hCX)).mpr hXC
  letI : (C.subgroupOf X).Normal := hCnormal
  let : SMul P X :=
    ⟨fun a x => ⟨(a : G) * (x : G) * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPX a.2) (x : G)).mp x.2⟩⟩
  have hsmul : ∀ (a : P) (x : X), ((a • x : X) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  let : MulAction P X :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun a b x => Subtype.ext (by simp only [hsmul]; simp [mul_assoc]) }
  letI : MulAction.QuotientAction P (C.subgroupOf X) :=
    ⟨fun a x y h => by
      rw [Subgroup.mem_subgroupOf] at h ⊢
      have hconj : (a : G) * ((x⁻¹ * y : X) : G) * (a : G)⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hPC a.2) ((x⁻¹ * y : X) : G)).mp h
      have heq : (((a • x)⁻¹ * a • y : X) : G) =
          (a : G) * ((x⁻¹ * y : X) : G) * (a : G)⁻¹ := by
        simp only [hsmul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact hconj⟩
  have hfix1 : (QuotientGroup.mk 1 : X ⧸ C.subgroupOf X) ∈
      MulAction.fixedPoints P (X ⧸ C.subgroupOf X) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [MulAction.Quotient.smul_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by rw [hsmul]; simp))
  have hidx : p ∣ Nat.card (X ⧸ C.subgroupOf X) := by
    obtain ⟨n, hn⟩ := (hP.to_le hXP).index (C.subgroupOf X)
    have hn1 : n ≠ 0 := by
      rintro rfl
      have h1 : (C.subgroupOf X).index = 1 := by simpa using hn
      rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
      exact (ne_of_lt hCX) (le_antisymm (le_of_lt hCX) h1)
    change p ∣ (C.subgroupOf X).index
    rw [hn]
    exact dvd_pow_self p hn1
  obtain ⟨q, hqfix, hqne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (X ⧸ C.subgroupOf X) hidx hfix1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hxC : (x : G) ∉ C := by
    intro hxc
    apply hqne
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hxc
  refine ⟨x, x.2, hxC, ?_⟩
  intro s hs
  let sP : P := ⟨s, hs⟩
  have h1 : (QuotientGroup.mk (sP • x) : X ⧸ C.subgroupOf X) = QuotientGroup.mk x := by
    simpa using (MulAction.mem_fixedPoints.1 hqfix) sP
  have h2 : QuotientGroup.mk' (C.subgroupOf X) ((sP • x) * x⁻¹) = 1 := by
    rw [map_mul, map_inv]
    have h1' : QuotientGroup.mk' (C.subgroupOf X) (sP • x) =
        QuotientGroup.mk' (C.subgroupOf X) x := by
      simpa [QuotientGroup.mk'_apply] using h1
    rw [h1', mul_inv_cancel]
  have hmem : ((sP • x) * x⁻¹ : X) ∈ C.subgroupOf X :=
    (QuotientGroup.eq_one_iff _).1 h2
  have hmemG : (((sP • x) * x⁻¹ : X) : G) ∈ C := (Subgroup.mem_subgroupOf).1 hmem
  have heq : (((sP • x) * x⁻¹ : X) : G) = ⁅(s : G), (x : G)⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul sP x, commutatorElement_def]
    rfl
  rwa [heq] at hmemG

theorem commutator_mem_of_minimal_of_isPGroup {p : ℕ} [Fact p.Prime]
    {H P X C : Subgroup G} (hP : IsPGroup p P) (hPH : P ≤ H)
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hCX : C < X) (hXP : X ≤ P)
    (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hHC : H ≤ Subgroup.normalizer (C : Set G))
    (hmin : ∀ Y : Subgroup G, C ≤ Y → Y ≤ X →
      H ≤ Subgroup.normalizer (Y : Set G) → Y = C ∨ Y = X) :
    ∀ s ∈ P, ∀ x ∈ X, ⁅s, x⁆ ∈ C := by
  classical
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := hPH.trans hHX
  have hPC : P ≤ Subgroup.normalizer (C : Set G) := hPH.trans hHC
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := hXP.trans hPC
  let Y : Subgroup G :=
    { carrier := {x : G | x ∈ X ∧ ∀ s ∈ P, ⁅s, x⁆ ∈ C}
      one_mem' := by
        refine ⟨X.one_mem, ?_⟩
        intro s _
        simp
      mul_mem' := by
        rintro x y ⟨hxX, hx⟩ ⟨hyX, hy⟩
        refine ⟨X.mul_mem hxX hyX, ?_⟩
        intro s hs
        rw [CFSG.commutator_mul_right]
        have hconj : x * ⁅s, y⁆ * x⁻¹ ∈ C :=
          (Subgroup.mem_normalizer_iff.mp (hXC hxX) ⁅s, y⁆).mp (hy s hs)
        rw [show ⁅s, x⁆ * x * ⁅s, y⁆ * x⁻¹ = ⁅s, x⁆ * (x * ⁅s, y⁆ * x⁻¹) by group]
        exact C.mul_mem (hx s hs) hconj
      inv_mem' := by
        rintro x ⟨hxX, hx⟩
        refine ⟨X.inv_mem hxX, ?_⟩
        intro s hs
        rw [CFSG.commutator_inv_right]
        simpa using (Subgroup.mem_normalizer_iff.mp (hXC (X.inv_mem hxX)) ⁅s, x⁆⁻¹).mp
          (C.inv_mem (hx s hs)) }
  have hCY : C ≤ Y := by
    intro c hc
    refine ⟨(le_of_lt hCX) hc, ?_⟩
    intro s hs
    exact C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPC hs) c).mp hc) (C.inv_mem hc)
  have hYX : Y ≤ X := fun y hy => hy.1
  have hmapY : ∀ h ∈ H, ∀ y : G, y ∈ Y → h * y * h⁻¹ ∈ Y := by
    intro h hh y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHX hh) y).mp hy.1, ?_⟩
    intro s hs
    have hs' : h⁻¹ * s * h ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hHP (H.inv_mem hh)) s).mp hs
    have hconj : h * ⁅h⁻¹ * s * h, y⁆ * h⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hHC hh) ⁅h⁻¹ * s * h, y⁆).mp (hy.2 _ hs')
    have heq : ⁅s, h * y * h⁻¹⁆ = h * ⁅h⁻¹ * s * h, y⁆ * h⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [heq]
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hmapY h hh y, fun hy => by
      have := hmapY h⁻¹ (H.inv_mem hh) (h * y * h⁻¹) hy
      simpa [mul_assoc] using this⟩
  obtain ⟨x, hxX, hxC, hxP⟩ :=
    exists_commutator_mem_of_fixed_coset hP hXP hPX hPC hXC hCX
  have hxY : (x : G) ∈ Y := ⟨hxX, hxP⟩
  have hYne : Y ≠ C := fun hYC => hxC (hYC ▸ hxY)
  have hYXeq : Y = X := (hmin Y hCY hYX hHY).resolve_left hYne
  intro s hs x hx
  exact (hYXeq ▸ hx).2 s hs

end CFSG.GroupTheory
