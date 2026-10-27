module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

@[expose] def IsSplitCover {X : Type} [Group X] (p : ℕ) (L W : Subgroup X) : Prop :=
  centralizer (L : Set X) ≤ W ∧ W ⊓ L ≤ centralizer (L : Set X) ∧
    oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
    (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ centralizer (L : Set X)) ∧
      ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ centralizer (L : Set X)) ∧
    ∀ w ∈ W, w ^ p ∈ centralizer (L : Set X) → ∃ z ∈ L, orderOf z = p ∧ w * z = z * w

variable {X : Type} [Group X] [Finite X] {p : ℕ}

omit [Finite X] in
theorem exists_mul_of_mem_sup (hp : p.Prime) {L W : Subgroup X} (hLn : L.Normal)
    (hWL : ∀ x ∈ W ⊓ L, Nat.Coprime (orderOf x) p) {e : X} (he : e ∈ L ⊔ W) {k : ℕ}
    (hek : e ^ (p ^ k) = 1) : ∃ l ∈ L, ∃ w ∈ W, w ^ (p ^ k) = 1 ∧ e = l * w := by
  haveI := hLn
  obtain ⟨l₀, hl₀, w₀, hw₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he
  rcases k with - | k
  · refine ⟨1, L.one_mem, 1, W.one_mem, by simp, ?_⟩
    have h1 : l₀ * w₀ = 1 := by simpa using hek
    rw [h1, mul_one]
  · have hp1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (Nat.succ_ne_zero k) hp.one_lt
    set c : X := w₀ ^ (p ^ (k + 1)) with hc
    have hcW : c ∈ W := by rw [hc]; exact pow_mem hw₀ _
    have hcL : c ∈ L := by
      rw [hc]
      have hq : QuotientGroup.mk' L (l₀ * w₀) = QuotientGroup.mk' L w₀ := by
        rw [map_mul]
        have h1 : QuotientGroup.mk' L l₀ = 1 := (QuotientGroup.eq_one_iff _).mpr hl₀
        rw [h1, one_mul]
      have hqe : QuotientGroup.mk' L (l₀ * w₀) ^ (p ^ (k + 1)) = 1 := by
        rw [← map_pow, hek, map_one]
      have hc1 : QuotientGroup.mk' L (w₀ ^ (p ^ (k + 1))) = 1 := by
        rw [map_pow, ← hq, hqe]
      exact (QuotientGroup.eq_one_iff _).mp hc1
    have hcop : Nat.Coprime (orderOf c) (p ^ (k + 1)) :=
      (hWL c ⟨hcW, hcL⟩).pow_right (k + 1)
    set m : ℕ := orderOf c with hm
    obtain ⟨v, -, hvmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp1
    set t : ℕ := m * v / p ^ (k + 1) with ht
    have hmv : m * v = p ^ (k + 1) * t + 1 := by
      have h := Nat.div_add_mod (m * v) (p ^ (k + 1))
      rw [hvmod] at h
      calc m * v = p ^ (k + 1) * ((m * v) / p ^ (k + 1)) + 1 := h.symm
        _ = p ^ (k + 1) * t + 1 := by rw [ht]
    refine ⟨l₀ * (c ^ t)⁻¹, L.mul_mem hl₀ (L.inv_mem (Subgroup.pow_mem L hcL t)),
      w₀ ^ (m * v), Subgroup.pow_mem W hw₀ _, ?_, ?_⟩
    · have h1 : (w₀ ^ (m * v)) ^ (p ^ (k + 1)) = c ^ (m * v) := by
        conv_lhs => rw [← pow_mul, mul_comm, pow_mul, ← hc]
      rw [h1, pow_mul, hm, pow_orderOf_eq_one, one_pow]
    · have h3 : w₀ ^ (m * v) = c ^ t * w₀ := by
        rw [hmv, pow_add, pow_mul, ← hc, pow_one]
      have h2 : w₀ = (c ^ t)⁻¹ * (w₀ ^ (m * v)) := by
        rw [h3]; group
      conv_lhs => rw [h2]
      group

namespace IsSplitCover

variable {L W : Subgroup X}

omit [Finite X] in
theorem pow_mem (hLn : L.Normal) (hW : IsSplitCover p L W) {w : X} (hw : w ∈ W) :
    ∃ k : ℕ, w ^ (p ^ k) ∈ centralizer (L : Set X) := by
  haveI := hLn
  obtain ⟨g, -, ⟨k, hgk⟩, hgen⟩ := hW.2.2.2.1
  obtain ⟨n, hn⟩ := hgen w hw
  refine ⟨k, ?_⟩
  have hπw : QuotientGroup.mk' (centralizer (L : Set X)) w
      = (QuotientGroup.mk' (centralizer (L : Set X)) g) ^ n := by
    have h1 : QuotientGroup.mk' (centralizer (L : Set X)) (w * (g ^ n)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hn
    rw [map_mul, map_inv, map_pow] at h1
    exact mul_inv_eq_one.mp h1
  have hπg : (QuotientGroup.mk' (centralizer (L : Set X)) g) ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hgk
  have hlast : QuotientGroup.mk' (centralizer (L : Set X)) (w ^ (p ^ k)) = 1 := by
    rw [map_pow, hπw, ← pow_mul, mul_comm, pow_mul, hπg, one_pow]
  exact (QuotientGroup.eq_one_iff _).mp hlast

omit [Finite X] in
theorem commutator_mem (hLn : L.Normal) (hW : IsSplitCover p L W) {w₁ w₂ : X} (h₁ : w₁ ∈ W)
    (h₂ : w₂ ∈ W) : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ centralizer (L : Set X) := by
  haveI := hLn
  let Y : Subgroup X := centralizer (L : Set X)
  obtain ⟨g, -, -, hgen⟩ := hW.2.2.2.1
  obtain ⟨a, ha⟩ := hgen w₁ h₁
  obtain ⟨b, hb⟩ := hgen w₂ h₂
  have hπa : QuotientGroup.mk' Y w₁ = (QuotientGroup.mk' Y g) ^ a := by
    have h1 : QuotientGroup.mk' Y (w₁ * (g ^ a)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [map_mul, map_inv, map_pow] at h1
    exact mul_inv_eq_one.mp h1
  have hπb : QuotientGroup.mk' Y w₂ = (QuotientGroup.mk' Y g) ^ b := by
    have h1 : QuotientGroup.mk' Y (w₂ * (g ^ b)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hb
    rw [map_mul, map_inv, map_pow] at h1
    exact mul_inv_eq_one.mp h1
  have hlast : QuotientGroup.mk' Y (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπa, hπb]
    rw [Commute.pow_pow_self (QuotientGroup.mk' Y g) a b |>.eq]
    group
  exact (QuotientGroup.eq_one_iff _).mp hlast

theorem coprime_orderOf (hp : p.Prime) (hW : IsSplitCover p L W)
    (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1) {x : X} (hx : x ∈ W ⊓ L) :
    Nat.Coprime (orderOf x) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpdvd
  have hxL : x ∈ L := hx.2
  have hxY : x ∈ centralizer (L : Set X) := hW.2.1 hx
  let z : X := x ^ (orderOf x / p)
  have hzord : orderOf z = p := by
    exact orderOf_pow_orderOf_div (orderOf_pos x).ne' hpdvd
  have hzL : z ∈ L := Subgroup.pow_mem L hxL _
  have hzY : z ∈ centralizer (L : Set X) := Subgroup.pow_mem (centralizer (L : Set X)) hxY _
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hz1 : z = 1 := hZ z hzL hzY hzp
  rw [hz1, orderOf_one] at hzord
  exact hp.one_lt.ne' hzord.symm

theorem pRank_le_two (hp : p.Prime) (hLn : L.Normal) (hW : IsSplitCover p L W)
    (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) : CFSG.Open.pRank p W ≤ 2 := by
  haveI := hLn
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEW hE
  let Y : Subgroup X := centralizer (L : Set X)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := p) (G := E)).mp hE.isPGroup
  suffices r ≤ 2 by rw [hr]; exact Nat.pow_le_pow_right hp.pos this
  obtain ⟨g, -, -, hgen⟩ := hW.2.2.2.1
  have hWmap : W.map (QuotientGroup.mk' Y) ≤ Subgroup.zpowers (QuotientGroup.mk' Y g) := by
    rintro - ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := hgen w hw
    have hπ : QuotientGroup.mk' Y w = (QuotientGroup.mk' Y g) ^ n := by
      have h1 : QuotientGroup.mk' Y (w * (g ^ n)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      rw [map_mul, map_inv, map_pow] at h1
      exact mul_inv_eq_one.mp h1
    rw [hπ]
    exact Subgroup.npow_mem_zpowers _ _
  have hEmap : E.map (QuotientGroup.mk' Y) ≤ Subgroup.zpowers (QuotientGroup.mk' Y g) :=
    (Subgroup.map_mono hEW).trans hWmap
  haveI : IsCyclic (E.map (QuotientGroup.mk' Y)) := Subgroup.isCyclic_of_le hEmap
  obtain ⟨x₀, hx₀⟩ := IsCyclic.exists_generator (α := E.map (QuotientGroup.mk' Y))
  obtain ⟨a, haE, hax⟩ := Subgroup.mem_map.mp x₀.2
  have haW : a ∈ W := hEW haE
  have hapY : a ^ p ∈ Y := by rw [hE.2 a haE]; exact Y.one_mem
  obtain ⟨z, hzL, hzord, haz⟩ := hW.2.2.2.2 a haW hapY
  have hazc : Commute a z := haz
  have hzYmem : ∀ y ∈ Y, z * y = y * z := by
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hy z hzL
  have hzc : ∀ e ∈ E, Commute z e := by
    intro e he
    have hmem : QuotientGroup.mk' Y e ∈ E.map (QuotientGroup.mk' Y) :=
      Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hx₀ ⟨QuotientGroup.mk' Y e, hmem⟩)
    have h2 : (x₀ : X ⧸ Y) ^ i = QuotientGroup.mk' Y e := by
      have h := congrArg Subtype.val hi
      simpa [Subgroup.coe_zpow] using h
    have hπe : QuotientGroup.mk' Y e = (QuotientGroup.mk' Y a) ^ i := by
      rw [← h2, hax]
    have hyY : (a ^ i)⁻¹ * e ∈ Y := by
      have hy1 : QuotientGroup.mk' Y ((a ^ i)⁻¹ * e) = 1 := by
        rw [map_mul, map_inv, map_zpow, hπe]
        group
      exact (QuotientGroup.eq_one_iff _).mp hy1
    have h1 : Commute z (a ^ i) := (hazc.zpow_left i).symm
    have h2' : Commute z ((a ^ i)⁻¹ * e) := hzYmem _ hyY
    have h3 : Commute z (a ^ i * ((a ^ i)⁻¹ * e)) := h1.mul_right h2'
    rwa [show a ^ i * ((a ^ i)⁻¹ * e) = e from by group] at h3
  let Z : Subgroup X := Subgroup.zpowers z
  have hZcard : Nat.card Z = p := by
    change Nat.card (Subgroup.zpowers z) = p
    rw [Nat.card_zpowers, hzord]
  have hz_notin : z ∉ E := by
    intro hzE
    have hzW : z ∈ W := hEW hzE
    have hzY' : z ∈ Y := hW.2.1 ⟨hzW, hzL⟩
    have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    have hz1 : z = 1 := hZ z hzL hzY' hzp
    rw [hz1, orderOf_one] at hzord
    exact hp.one_lt.ne' hzord.symm
  haveI : Fact (Nat.card Z).Prime := ⟨by rw [hZcard]; exact hp⟩
  have hinf : Z ⊓ E = ⊥ := by
    rcases (E.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hy' : (⟨y, hy.1⟩ : Z) ∈ E.subgroupOf Z := by
        rw [Subgroup.mem_subgroupOf]; exact hy.2
      rw [hbot] at hy'
      have h1 : (⟨y, hy.1⟩ : Z) = 1 := Subgroup.mem_bot.mp hy'
      simpa using congrArg Subtype.val h1
    · exfalso
      have hle : Z ≤ E := by
        intro y hy
        have : (⟨y, hy⟩ : Z) ∈ E.subgroupOf Z := by rw [htop]; exact Subgroup.mem_top _
        rwa [Subgroup.mem_subgroupOf] at this
      exact hz_notin (hle (Subgroup.mem_zpowers z))
  have hcZE : ∀ a ∈ Z, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hzc b hb).zpow_left j
  have hElem : CFSG.Open.IsElemAbelian p (Z ⊔ E) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (by rw [← hzord]; exact pow_orderOf_eq_one z)) hE hcZE
  have hcard : Nat.card ↥(Z ⊔ E) = p ^ (r + 1) := by
    have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := Z) (B := E) hcZE
    rw [hinf, Subgroup.card_bot, hZcard, hr, mul_one, ← pow_succ' p r] at hprod
    exact hprod
  have hle3 : r + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hElem hcard
  omega

omit [Finite X] in
theorem centralizer_pCore_le (hLn : L.Normal) (hW : IsSplitCover p L W)
    (hRY : CFSG.pCore p X ≤ centralizer (L : Set X))
    (hYR : centralizer (L : Set X) ⊓ centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X) :
    centralizer (CFSG.pCore p ↥W : Set ↥W) ≤ CFSG.pCore p ↥W := by
  haveI := hLn
  let Y : Subgroup X := centralizer (L : Set X)
  let R : Subgroup X := CFSG.pCore p X
  let C : Subgroup ↥W := centralizer (CFSG.pCore p ↥W : Set ↥W)
  have hRW : R ≤ W := hRY.trans hW.1
  have hRn : R.Normal := CFSG.pCore_normal
  have hRsub : R.subgroupOf W ≤ CFSG.pCore p ↥W :=
    le_sSup ⟨hRn.subgroupOf W, (CFSG.pCore_isPGroup (p := p) (G := X)).comap_subtype⟩
  have hCp : IsPGroup p C := by
    intro x
    have hxcentR : (x : X) ∈ centralizer (R : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hrR
      have hrW : r ∈ W := hRW hrR
      have hmem : (⟨r, hrW⟩ : ↥W) ∈ CFSG.pCore p ↥W :=
        hRsub (by rw [Subgroup.mem_subgroupOf]; exact hrR)
      have hxc := (Subgroup.mem_centralizer_iff.mp x.2) ⟨r, hrW⟩ hmem
      exact congrArg Subtype.val hxc
    obtain ⟨k, hkY⟩ := pow_mem hLn hW (w := (x : X)) x.1.2
    have hxcentRpow : (x : X) ^ (p ^ k) ∈ centralizer (R : Set X) :=
      Subgroup.pow_mem (centralizer (R : Set X)) hxcentR (p ^ k)
    have hxR : (x : X) ^ (p ^ k) ∈ R := hYR ⟨hkY, hxcentRpow⟩
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := p) (G := X) ⟨(x : X) ^ (p ^ k), hxR⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h ⊢
    rw [pow_add, pow_mul]
    exact h
  have hCn : C.Normal := by
    change (centralizer (CFSG.pCore p ↥W : Set ↥W)).Normal
    infer_instance
  change C ≤ CFSG.pCore p ↥W
  exact le_sSup ⟨hCn, hCp⟩

omit [Finite X] in
theorem le_centralizer_of_commutator_eq (hLn : L.Normal) (hW : IsSplitCover p L W)
    {V : Subgroup X} (hVW : V ≤ W) (hVV : ⁅V, V⁆ = V) : V ≤ centralizer (L : Set X) := by
  rw [← hVV]
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  exact commutator_mem hLn hW (hVW hg₁) (hVW hg₂)

theorem normal_sup_pCore_of_isPGroup (hp : p.Prime) (hLn : L.Normal) (hW : IsSplitCover p L W)
    (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hRY : CFSG.pCore p X ≤ centralizer (L : Set X)) {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian p E) (hEW : E ≤ L ⊔ W)
    (hV : IsPGroup p ↥(closure {x : X | x ∈ W ∧ orderOf x = p})) :
    IsPGroup p ↥(E ⊔ CFSG.pCore p X) ∧
      ((E ⊔ CFSG.pCore p X).subgroupOf (E ⊔ centralizer (L : Set X))).Normal := by
  haveI := hLn
  haveI : Fact p.Prime := ⟨hp⟩
  let Y : Subgroup X := centralizer (L : Set X)
  let R : Subgroup X := CFSG.pCore p X
  let V : Subgroup X := closure {x : X | x ∈ W ∧ orderOf x = p}
  have hYn : Y.Normal := inferInstance
  have hRn : R.Normal := CFSG.pCore_normal
  haveI : Y.Normal := hYn
  haveI : R.Normal := hRn
  have hVW : V ≤ W := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxW, -⟩
    exact hxW
  have hVnorm : ∀ g ∈ W, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
        exact Subgroup.subset_closure
          ⟨W.mul_mem (W.mul_mem hg hx.1) (W.inv_mem hg), by
            rw [← SemiconjBy.orderOf_eq g
              (show SemiconjBy g x (g * x * g⁻¹) from by
                change g * x = (g * x * g⁻¹) * g
                group)]
            exact hx.2⟩
    | one => simpa using V.one_mem
    | mul x y hx hy ihx ihy =>
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
        exact V.mul_mem ihx ihy
    | inv x hx ihx =>
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
        exact V.inv_mem ihx
  have hDle : V ⊓ Y ≤ R := by
    have hDnorm : ((V ⊓ Y).subgroupOf Y).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro d y hd hy
      exact ⟨hVnorm y (hW.1 hy) d hd.1, hYn.conj_mem d hd.2 y⟩
    have hVp : IsPGroup p V := hV
    have hDp : IsPGroup p ↥(V ⊓ Y) :=
      IsPGroup.to_le (G := X) (H := V ⊓ Y) (K := V) hVp inf_le_left
    have hDsub : (V ⊓ Y).subgroupOf Y ≤ CFSG.pCore p ↥Y :=
      le_sSup ⟨hDnorm, hDp.comap_of_injective Y.subtype Subtype.coe_injective⟩
    have hpYnorm : ((CFSG.pCore p ↥Y).map Y.subtype).Normal := inferInstance
    have hpYp : IsPGroup p ((CFSG.pCore p ↥Y).map Y.subtype) :=
      (CFSG.pCore_isPGroup (p := p) (G := ↥Y)).map Y.subtype
    have hpYle : (CFSG.pCore p ↥Y).map Y.subtype ≤ R := le_sSup ⟨hpYnorm, hpYp⟩
    calc V ⊓ Y = ((V ⊓ Y).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
      _ ≤ (CFSG.pCore p ↥Y).map Y.subtype := Subgroup.map_mono hDsub
      _ ≤ R := hpYle
  have hConj : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E ⊔ R := by
    intro y hy e he
    obtain ⟨l, hlL, w, hwW, hwp, he_lw⟩ :=
      exists_mul_of_mem_sup hp hLn (fun x hx => coprime_orderOf hp hW hZ hx) (hEW he)
        (k := 1) (by simpa using hE.2 e he)
    have hwp' : w ^ p = 1 := by simpa using hwp
    have hwV : w ∈ V := by
      rcases eq_or_ne w 1 with rfl | hw1
      · exact V.one_mem
      · exact Subgroup.subset_closure ⟨hwW, orderOf_eq_prime hwp' hw1⟩
    have hd : w⁻¹ * (y * w * y⁻¹) ∈ V ⊓ Y := by
      refine ⟨V.mul_mem (V.inv_mem hwV) (hVnorm y (hW.1 hy) w hwV), ?_⟩
      have h1 : w⁻¹ * y * w ∈ Y := by simpa using hYn.conj_mem y hy w⁻¹
      have h2 : w⁻¹ * (y * w * y⁻¹) = (w⁻¹ * y * w) * y⁻¹ := by group
      rw [h2]
      exact Y.mul_mem h1 (Y.inv_mem hy)
    have hdR : w⁻¹ * (y * w * y⁻¹) ∈ R := hDle hd
    have hyl : y * l = l * y := (Subgroup.mem_centralizer_iff.mp hy l hlL).symm
    have hkey : y * e * y⁻¹ = e * (w⁻¹ * (y * w * y⁻¹)) := by
      rw [he_lw]
      calc y * (l * w) * y⁻¹ = (y * l) * w * y⁻¹ := by group
        _ = (l * y) * w * y⁻¹ := by rw [hyl]
        _ = l * (y * w * y⁻¹) := by group
        _ = (l * w) * (w⁻¹ * (y * w * y⁻¹)) := by group
    rw [hkey]
    exact (E ⊔ R).mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hdR)
  have hA : IsPGroup p ↥(E ⊔ R) :=
    IsPGroup.to_sup_of_normal_right hE.isPGroup (CFSG.pCore_isPGroup (p := p) (G := X))
  have hEnorm : E ≤ Subgroup.normalizer ((E ⊔ R : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he u hu
    exact (E ⊔ R).mul_mem ((E ⊔ R).mul_mem (Subgroup.mem_sup_left he) hu)
      ((E ⊔ R).inv_mem (Subgroup.mem_sup_left he))
  have hYnorm : Y ≤ Subgroup.normalizer ((E ⊔ R : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy u hu
    obtain ⟨e, heE, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    have h1 : y * e * y⁻¹ ∈ E ⊔ R := hConj y hy e heE
    have h2 : y * r * y⁻¹ ∈ R := hRn.conj_mem r hrR y
    rw [show y * (e * r) * y⁻¹ = (y * e * y⁻¹) * (y * r * y⁻¹) by group]
    exact (E ⊔ R).mul_mem h1 (Subgroup.mem_sup_right h2)
  have hEYnorm : E ⊔ Y ≤ Subgroup.normalizer ((E ⊔ R : Subgroup X) : Set X) := sup_le hEnorm hYnorm
  refine ⟨hA, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff (sup_le_sup_left hRY E)]
  intro u s hu hs
  exact (Subgroup.le_normalizer_iff.mp hEYnorm) s hs u hu

end IsSplitCover

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
