module

public import CFSG.CGT.Harada80.Dual
public import CFSG.CGT.Harada80.Block
public import CFSG.CGT.Hall82.Tight

public section

namespace CFSG.CGT.Harada80

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo

noncomputable abbrev blockW {G : Type} [Group G] (J : Subgroup G) : Subgroup G :=
  pCoreOf 2 (Subgroup.centralizer (J : Set G))

structure BlockCase {G : Type} [Group G] (J : Subgroup G) (m : ℕ) : Prop where
  h1 : H1Natural m
  le_blockW : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (J : Set G) →
    P ≤ blockW J
  comm : ∀ a ∈ blockW J, ∀ b ∈ blockW J, a * b = b * a

structure EvenCase {G : Type} [Group G] (J : Subgroup G) (m : ℕ) : Prop
    extends BlockCase J m where
  ne_bot : blockW J ≠ ⊥

theorem blockW_eq_bot {G : Type} [Group G] {J : Subgroup G}
    (hC : Subgroup.centralizer (J : Set G) = ⊥) : blockW J = ⊥ :=
  eq_bot_iff.mpr (hC ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem BlockCase.of_centralizer_eq_bot {G : Type} [Group G] {J : Subgroup G} {m : ℕ}
    (hH1 : H1Natural m) (hC : Subgroup.centralizer (J : Set G) = ⊥) : BlockCase J m where
  h1 := hH1
  le_blockW P _ hP := by rw [blockW_eq_bot hC]; exact hC ▸ hP
  comm a ha b hb := by
    rw [blockW_eq_bot hC, Subgroup.mem_bot] at ha hb
    rw [ha, hb]

noncomputable abbrev vOmega {G : Type} [Group G] (M : Subgroup G) : Subgroup G :=
  CFSG.ComponentClassification.AschbacherTheorem3.omegaOne (pCoreOf 2 M)

theorem vOmega_le_pCoreOf {G : Type} [Group G] (M : Subgroup G) :
    vOmega M ≤ pCoreOf 2 M :=
  CFSG.ComponentClassification.AschbacherTheorem3.omegaOne_le (pCoreOf 2 M)

namespace Setting

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}

theorem exists_involution_blockW (hE : EvenCase J m) :
    ∃ z ∈ blockW J, z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 (blockW J) :=
    CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' _
  have hcard_gt : 1 < Nat.card ↥(blockW J) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := blockW J)).2 hE.ne_bot
  have hcard : 2 ∣ Nat.card ↥(blockW J) := by
    rcases hW2.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blockW J)) 2 hcard
  refine ⟨(z : G), z.2, ?_, ?_⟩
  · intro h1
    have hz1 : z = 1 := Subtype.ext h1
    rw [hz1, orderOf_one] at hz
    omega
  · have hzo : orderOf (z : G) = 2 := by rwa [Subgroup.orderOf_coe]
    rw [← hzo]
    exact orderOf_dvd_iff_pow_eq_one.mp dvd_rfl

variable (S : Setting G M J m)
include S

theorem conj_mem_blockW {x w : G} (hx : x ∈ M) (hw : w ∈ blockW J) :
    x * w * x⁻¹ ∈ blockW J := by
  have hxN : x ∈ Subgroup.normalizer
      (Subgroup.centralizer (J : Set G) : Subgroup G) :=
    CFSG.CGT.Hall82.le_normalizer_centralizer_of_normalizer_eq S.normalizer_eq hx
  have hxN' : x ∈ Subgroup.normalizer (blockW J : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxN
  exact (Subgroup.mem_normalizer_iff.mp hxN' w).mp hw

theorem blockW_le_pCoreOf : blockW J ≤ pCoreOf 2 M := by
  change pCoreOf 2 (Subgroup.centralizer (J : Set G)) ≤ pCoreOf 2 M
  rw [CFSG.CGT.Hall82.pCoreOf_centralizer_eq_inf S.normalizer_eq]
  exact inf_le_left

theorem blockU_le_pCoreOf : blockU J ≤ pCoreOf 2 M := by
  have hA2 : IsPGroup 2 (blockU J) :=
    CFSG.CGT.PushingUpLit.SolK.isPGroup_of_le
      (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' J) (blockU_le_blockQ S)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((blockU_le_blockQ S).trans ((blockQ_le S).trans S.le)) ?_ hA2
  rw [S.normalizer_blockU_eq]

theorem commute_blockU_blockW {a w : G} (ha : a ∈ blockU J) (hw : w ∈ blockW J) :
    a * w = w * a := by
  have haJ : a ∈ J := (blockQ_le S) (blockU_le_blockQ S ha)
  have hwC : w ∈ Subgroup.centralizer (J : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  exact Subgroup.mem_centralizer_iff.mp hwC a haJ

theorem blockU_inf_blockW (hZ : blockZ J = ⊥) : blockU J ⊓ blockW J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.mp hx
  have hxC : x ∈ Subgroup.centralizer (J : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxW
  have hxZ : x ∈ blockZ J := Subgroup.mem_inf.mpr ⟨hxA, hxC⟩
  rw [hZ] at hxZ
  exact Subgroup.mem_bot.mp hxZ

theorem eq_of_mul_eq (hZ : blockZ J = ⊥) {a a' w w' : G} (ha : a ∈ blockU J)
    (ha' : a' ∈ blockU J) (hw : w ∈ blockW J) (hw' : w' ∈ blockW J)
    (h : a * w = a' * w') : a = a' ∧ w = w' := by
  have h1 : a'⁻¹ * a = w' * w⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * w) * w⁻¹ := by group
      _ = a'⁻¹ * (a' * w') * w⁻¹ := by rw [h]
      _ = w' * w⁻¹ := by group
  have hbot : a'⁻¹ * a = 1 := by
    have hmem : a'⁻¹ * a ∈ blockU J ⊓ blockW J := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (blockU J).mul_mem ((blockU J).inv_mem ha') ha
      · rw [h1]
        exact (blockW J).mul_mem hw' ((blockW J).inv_mem hw)
    rwa [blockU_inf_blockW S hZ, Subgroup.mem_bot] at hmem
  have hbot' : w' * w⁻¹ = 1 := by rw [← h1, hbot]
  constructor
  · calc a = a' * (a'⁻¹ * a) := by group
      _ = a' * 1 := by rw [hbot]
      _ = a' := by group
  · calc w = (w' * w⁻¹)⁻¹ * w' := by group
      _ = 1⁻¹ * w' := by rw [hbot']
      _ = w' := by group

theorem centralizer_le_of_mem_blockW {w : G} (hw : w ∈ blockW J) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set G) ≤ M :=
  CFSG.CGT.Hall82.centralizer_le_of_mem_pCoreOf (M := M) (X := J) S.uniq hw hw1

theorem blockU_le_vOmega : blockU J ≤ vOmega M :=
  (CFSG.ComponentClassification.AschbacherTheorem3.le_omegaOne
    fun x hx => S.elemU.2 x hx).trans
    (CFSG.ComponentClassification.AschbacherTheorem3.omegaOne_mono
      (blockU_le_pCoreOf S))

private theorem commutator_mem_blockQ_of_mem_pCoreOf {H : Subgroup G}
    (hHM : H ≤ M) (hJH : J ≤ H) {y : G} (hy : y ∈ pCoreOf 2 H) {g : G} (hg : g ∈ J) :
    y * g * y⁻¹ * g⁻¹ ∈ blockQ J := by
  have hgH : g ∈ H := hJH hg
  have hyM : y ∈ M := hHM (CFSG.LieType.BorelTits.pCoreOf_le 2 H hy)
  have hD : pCoreOf 2 H ⊓ J ≤ blockQ J := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · intro j hj
      rw [Subgroup.mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        obtain ⟨hdO, hdJ⟩ := Subgroup.mem_inf.mp hd
        exact Subgroup.mem_inf.mpr
          ⟨CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized H (hJH hj) hdO,
            S.normal (S.le hj) hdJ⟩
      · intro hd
        obtain ⟨hdO, hdJ⟩ := Subgroup.mem_inf.mp hd
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : j⁻¹ * (j * d * j⁻¹) * (j⁻¹)⁻¹ ∈ pCoreOf 2 H :=
            CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized H
              (hJH (J.inv_mem hj)) hdO
          have h2 : j⁻¹ * (j * d * j⁻¹) * (j⁻¹)⁻¹ = d := by group
          rwa [h2] at h1
        · have h3 : j⁻¹ * (j * d * j⁻¹) * (j⁻¹)⁻¹ ∈ J :=
            S.normal (S.le (J.inv_mem hj)) hdJ
          have h4 : j⁻¹ * (j * d * j⁻¹) * (j⁻¹)⁻¹ = d := by group
          rwa [h4] at h3
    · exact CFSG.CGT.PushingUpLit.SolK.isPGroup_of_le
        (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' H) inf_le_left
  have hmem : y * g * y⁻¹ * g⁻¹ ∈ pCoreOf 2 H ⊓ J := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hcong : g * y⁻¹ * g⁻¹ ∈ pCoreOf 2 H :=
        CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized H hgH
          ((pCoreOf 2 H).inv_mem hy)
      have heq : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
      rw [heq]
      exact (pCoreOf 2 H).mul_mem hy hcong
    · have h1 : y * g * y⁻¹ ∈ J := S.normal hyM hg
      have h2 := J.mul_mem h1 (J.inv_mem hg)
      simpa [mul_assoc] using h2
  exact hD hmem

variable {S}

theorem exists_mul_of_centralizes (hE : BlockCase J m) {x : G} (hx : x ∈ M)
    (h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) :
    ∃ a ∈ blockU J, ∃ w ∈ blockW J, x = a * w := by
  obtain ⟨v, hv, hvx⟩ :=
    exists_mul_mem_centralizer_of_centralizer S hE.h1 (S.blockZ_eq_bot hE.h1) hx hxA
  have hv2 : v ^ 2 = 1 := S.elemU.2 v hv
  have hcomm : v * x = x * v := by
    have h := hxA v hv
    calc v * x = (x * v * x⁻¹) * x := by rw [h]
      _ = x * v := by group
  obtain ⟨k, hk⟩ := h2
  have hc2 : (v * x) ^ (2 ^ (k + 1)) = 1 := by
    rw [Commute.mul_pow hcomm (2 ^ (k + 1))]
    have h1 : v ^ (2 ^ (k + 1)) = 1 := by
      rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, pow_mul, hv2, one_pow]
    have h2' : x ^ (2 ^ (k + 1)) = 1 := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 by ring, pow_mul, hk, one_pow]
    rw [h1, h2', mul_one]
  have hW2 : IsPGroup 2 (Subgroup.zpowers (v * x)) :=
    IsPGroup.of_card_dvd_pow (n := k + 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hc2)
  have hw : v * x ∈ blockW J :=
    hE.le_blockW _ hW2 (Subgroup.zpowers_le.mpr hvx) (Subgroup.mem_zpowers (v * x))
  exact ⟨v⁻¹, (blockU J).inv_mem hv, v * x, hw, by group⟩

theorem exists_mul_of_mem_pCoreOf (hE : BlockCase J m) {x : G}
    (hx : x ∈ pCoreOf 2 M) :
    ∃ a ∈ blockU J, ∃ w ∈ blockW J, x = a * w := by
  have hxM : x ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hx
  have hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ :=
      CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' M ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxJ : ∀ g ∈ J, x * g * x⁻¹ * g⁻¹ ∈ blockQ J :=
    fun g hg => commutator_mem_blockQ_of_mem_pCoreOf S le_rfl S.le hx hg
  exact exists_mul_of_centralizes (S := S) hE hxM hx2
    (fun v hv => conj_eq_of_isPGroup S (S.blockZ_eq_bot hE.h1) hxM hx2 hxJ hv)

theorem pCoreOf_eq (hE : BlockCase J m) : pCoreOf 2 M = blockU J ⊔ blockW J := by
  refine le_antisymm ?_ (sup_le (blockU_le_pCoreOf S) (blockW_le_pCoreOf S))
  intro x hx
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hx
  exact Subgroup.mul_mem_sup ha hw

theorem pCoreOf_eq_blockU (hH1 : H1Natural m) (hC : Subgroup.centralizer (J : Set G) = ⊥) :
    pCoreOf 2 M = blockU J := by
  rw [pCoreOf_eq (S := S) (BlockCase.of_centralizer_eq_bot hH1 hC), blockW_eq_bot hC,
    sup_bot_eq]

theorem card_pCoreOf (hE : BlockCase J m) :
    Nat.card (pCoreOf 2 M) = Nat.card (blockU J) * Nat.card (blockW J) := by
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(blockU J) × ↥(blockW J) => (⟨(p.1 : G) * p.2,
      (pCoreOf 2 M).mul_mem (blockU_le_pCoreOf S p.1.2) (blockW_le_pCoreOf S p.2.2)⟩ :
        ↥(pCoreOf 2 M))) ⟨?_, ?_⟩)).symm
  · rintro ⟨a, w⟩ ⟨a', w'⟩ h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq S hZ a.2 a'.2 w.2 w'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hx
    exact ⟨(⟨a, ha⟩, ⟨w, hw⟩), rfl⟩

theorem pCoreOf_comm (hE : BlockCase J m) {x y : G} (hx : x ∈ pCoreOf 2 M)
    (hy : y ∈ pCoreOf 2 M) : x * y = y * x := by
  obtain ⟨va, hva, wa, hwa, rfl⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hx
  obtain ⟨vb, hvb, wb, hwb, rfl⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hy
  calc (va * wa) * (vb * wb) = va * (wa * vb) * wb := by group
    _ = va * (vb * wa) * wb := by rw [← commute_blockU_blockW S hvb hwa]
    _ = (va * vb) * (wa * wb) := by group
    _ = (vb * va) * (wb * wa) := by
          rw [blockU_comm S hva hvb, hE.comm wa hwa wb hwb]
    _ = vb * (va * wb) * wa := by group
    _ = vb * (wb * va) * wa := by rw [← commute_blockU_blockW S hva hwb]
    _ = (vb * wb) * (va * wa) := by group

theorem conj_mul_eq_iff (hE : BlockCase J m) {y a w : G} (hy : y ∈ M)
    (ha : a ∈ blockU J) (hw : w ∈ blockW J) :
    y * (a * w) * y⁻¹ = a * w ↔ y * a * y⁻¹ = a ∧ y * w * y⁻¹ = w := by
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  constructor
  · intro h
    have hprod : (y * a * y⁻¹) * (y * w * y⁻¹) = a * w := by
      rw [← h]
      group
    have ha' : y * a * y⁻¹ ∈ blockU J := conj_mem_blockU S hy ha
    have hw' : y * w * y⁻¹ ∈ blockW J := conj_mem_blockW S hy hw
    exact eq_of_mul_eq S hZ ha' ha hw' hw hprod
  · rintro ⟨ha', hw'⟩
    calc y * (a * w) * y⁻¹ = (y * a * y⁻¹) * (y * w * y⁻¹) := by group
      _ = a * w := by rw [ha', hw']

theorem pCoreOf_centralizer_eq (hE : BlockCase J m) {w : G} (hw : w ∈ blockW J)
    (hw1 : w ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) = pCoreOf 2 M := by
  let H : Subgroup G := Subgroup.centralizer ({w} : Set G)
  have hHM : H ≤ M := centralizer_le_of_mem_blockW S hw hw1
  have hwO : w ∈ pCoreOf 2 M := blockW_le_pCoreOf S hw
  have hwC : w ∈ Subgroup.centralizer (J : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  have hOH : pCoreOf 2 M ≤ H := by
    intro x hx
    change x ∈ Subgroup.centralizer ({w} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (pCoreOf_comm (S := S) hE hx hwO)
  have hJH : J ≤ H := by
    intro j hj
    change j ∈ Subgroup.centralizer ({w} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hwC) j hj)
  have hle : pCoreOf 2 M ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOH
      (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' M)
  refine le_antisymm ?_ hle
  intro y hy
  have hyH : y ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hy
  have hyM : y ∈ M := hHM hyH
  have hy2 : ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' H ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hyJ : ∀ g ∈ J, y * g * y⁻¹ * g⁻¹ ∈ blockQ J :=
    fun g hg => commutator_mem_blockQ_of_mem_pCoreOf S hHM hJH hy hg
  have hyA : ∀ v ∈ blockU J, y * v * y⁻¹ = v :=
    fun v hv => conj_eq_of_isPGroup S (S.blockZ_eq_bot hE.h1) hyM hy2 hyJ hv
  obtain ⟨a, ha, w', hw', rfl⟩ := exists_mul_of_centralizes (S := S) hE hyM hy2 hyA
  rw [pCoreOf_eq (S := S) hE]
  exact Subgroup.mul_mem_sup ha hw'

theorem mem_vOmega_iff (hE : BlockCase J m) {x : G} :
    x ∈ vOmega M ↔ x ∈ pCoreOf 2 M ∧ x ^ 2 = 1 := by
  have hcomm : IsMulCommutative ↥(pCoreOf 2 M) :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (pCoreOf_comm (S := S) hE a.2 b.2)
  exact CFSG.ComponentClassification.AschbacherTheorem3.mem_omegaOne_iff hcomm

theorem isElemAbelian_vOmega (hE : BlockCase J m) : IsElemAbelian 2 (vOmega M) := by
  constructor
  · refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
    exact pCoreOf_comm (S := S) hE
      ((mem_vOmega_iff (S := S) hE).mp x.2).1
      ((mem_vOmega_iff (S := S) hE).mp y.2).1
  · intro x hx
    exact ((mem_vOmega_iff (S := S) hE).mp hx).2

theorem vOmega_ne_bot (hE : BlockCase J m) : vOmega M ≠ ⊥ := by
  intro hbot
  have hAne : blockU J ≠ ⊥ := by
    have hlt := S.short.blockZ_lt_blockU
    rw [S.blockZ_eq_bot hE.h1] at hlt
    exact bot_lt_iff_ne_bot.mp hlt
  apply hAne
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ vOmega M := blockU_le_vOmega S hx
  rw [hbot] at hxV
  exact Subgroup.mem_bot.mp hxV

theorem normalizer_vOmega (hE : BlockCase J m) :
    Subgroup.normalizer (vOmega M : Set G) = M := by
  have hMle : M ≤ Subgroup.normalizer (vOmega M : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [mem_vOmega_iff (S := S) hE] at hv ⊢
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx) v).mp hv.1
      · calc (x * v * x⁻¹) ^ 2 = (x * v * x⁻¹) * (x * v * x⁻¹) := by
              rw [pow_two]
          _ = x * (v * v) * x⁻¹ := by group
          _ = x * v ^ 2 * x⁻¹ := by rw [pow_two]
          _ = x * 1 * x⁻¹ := by rw [hv.2]
          _ = 1 := by group
    · intro hv
      rw [mem_vOmega_iff (S := S) hE] at hv ⊢
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx) v).mpr hv.1
      · have hsq : (x * v * x⁻¹) * (x * v * x⁻¹) = 1 := by
          have h := hv.2
          rwa [pow_two] at h
        calc v ^ 2 = x⁻¹ * ((x * v * x⁻¹) * (x * v * x⁻¹)) * x := by
              rw [pow_two]
              group
          _ = x⁻¹ * 1 * x := by rw [hsq]
          _ = 1 := by group
  have hV2 : IsPGroup 2 (vOmega M) :=
    CFSG.CGT.PushingUpLit.SolK.isPGroup_of_le
      (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' M) (vOmega_le_pCoreOf M)
  have hloc : IsPLocal 2 (Subgroup.normalizer (vOmega M : Set G)) :=
    ⟨vOmega M, vOmega_ne_bot (S := S) hE, hV2, rfl⟩
  by_contra hne
  exact S.maxLocal.2 _ (lt_of_le_of_ne hMle (Ne.symm hne)) hloc

theorem centralizer_vOmega_le (hE : BlockCase J m) :
    Subgroup.centralizer (vOmega M : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans (normalizer_vOmega (S := S) hE).le

theorem mem_vOmega_of_centralizer (hE : BlockCase J m) {x : G}
    (hx : x ∈ Subgroup.centralizer (vOmega M : Set G)) (hx2 : x ^ 2 = 1) :
    x ∈ vOmega M := by
  have hxM : x ∈ M := centralizer_vOmega_le (S := S) hE hx
  have hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v := by
    intro v hv
    have hcomm := hx v (blockU_le_vOmega S hv)
    calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [hcomm.symm]
      _ = v := by group
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    exists_mul_of_centralizes (S := S) hE hxM ⟨1, by simpa using hx2⟩ hxA
  rw [mem_vOmega_iff (S := S) hE]
  refine ⟨?_, hx2⟩
  rw [pCoreOf_eq (S := S) hE]
  exact Subgroup.mul_mem_sup ha hw

end Setting

end CFSG.CGT.Harada80
