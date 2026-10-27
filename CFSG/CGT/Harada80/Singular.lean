module

public import CFSG.CGT.Harada80.Core
public import CFSG.CGT.Harada80.RhoLin
public import CFSG.CGT.Harada80.OrthoFacts
public import CFSG.CGT.Hall82.Fusion
public import CFSG.RankThree.GF2n.Tim78Normal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} {S : Setting G M J m}

theorem le_pCoreOf_of_centralizes (S : Setting G M J m) {t : G}
    (ht : t ∈ pCoreOf 2 M) (ht1 : t ≠ 1) {x : G}
    (hx : x ∈ Subgroup.centralizer ({t} : Set G))
    (hxR : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)), x * y = y * x) :
    x ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hF : CFSG.generalizedFitting ↥H = CFSG.pCore 2 ↥H := S.cent ht ht1
  have h := CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq
    (M := H) hF
  have hx' : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hxR y hy).symm
  exact h ⟨hx, hx'⟩

private theorem blockU_le_centralizer_mul (S : Setting G M J m) {u : ↥(blockU J)}
    {w : G} (hw : w ∈ blockW J) :
    blockU J ≤ Subgroup.centralizer ({(u : G) * w} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc a * ((u : G) * w) = (a * (u : G)) * w := by group
    _ = ((u : G) * a) * w := by rw [blockU_comm S ha u.2]
    _ = (u : G) * (a * w) := by group
    _ = (u : G) * (w * a) := by rw [commute_blockU_blockW S ha hw]
    _ = ((u : G) * w) * a := by group

private theorem blockW_le_centralizer_mul (S : Setting G M J m) (hE : BlockCase J m)
    {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) :
    blockW J ≤ Subgroup.centralizer ({(u : G) * w} : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc b * ((u : G) * w) = (b * (u : G)) * w := by group
    _ = ((u : G) * b) * w := by rw [(commute_blockU_blockW S u.2 hb).symm]
    _ = (u : G) * (b * w) := by group
    _ = (u : G) * (w * b) := by rw [hE.comm b hb w hw]
    _ = ((u : G) * w) * b := by group

private theorem conj_eq_blockW_of_mem_J {w ℓ : G} (hw : w ∈ blockW J) (hℓJ : ℓ ∈ J) :
    ℓ * w * ℓ⁻¹ = w := by
  have hwC : w ∈ Subgroup.centralizer (J : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  have hcomm : ℓ * w = w * ℓ := (Subgroup.mem_centralizer_iff.mp hwC) ℓ hℓJ
  calc ℓ * w * ℓ⁻¹ = (w * ℓ) * ℓ⁻¹ := by rw [hcomm]
    _ = w := by group

theorem exists_mul_of_lin_eq_one (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) {x : G} (hx : x ∈ T)
    (h : S.lin hZ ⟨x, hTM hx⟩ = 1) :
    ∃ a ∈ blockU J, ∃ w ∈ blockW J, x = a * w := by
  have hxM : x ∈ M := hTM hx
  obtain ⟨k, hk⟩ := hT.exists_pow_pow_eq_one ⟨x, hx⟩
  have h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1 :=
    ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hA : ∀ v ∈ blockU J, x * v * x⁻¹ = v :=
    fun v hv => (S.lin_eq_one_iff hZ ⟨x, hxM⟩).mp h v hv
  exact S.exists_mul_of_centralizes hE hxM h2 hA

theorem mem_pCoreOf_of_lin_eq_one (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T) {x : G} (hx : x ∈ T)
    (h : S.lin hZ ⟨x, hTM hx⟩ = 1) : x ∈ pCoreOf 2 M := by
  obtain ⟨a, ha, w, hw, hxeq⟩ := exists_mul_of_lin_eq_one (S := S) hE hZ hTM hT hx h
  rw [hxeq, pCoreOf_eq (S := S) hE]
  exact Subgroup.mul_mem_sup ha hw

theorem conj_eq_of_mem_centralizer_mul (S : Setting G M J m) (hE : BlockCase J m)
    {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) {x : G} (hxM : x ∈ M)
    (hx : x ∈ Subgroup.centralizer ({(u : G) * w} : Set G)) :
    x * (u : G) * x⁻¹ = u := by
  have hcomm : x * ((u : G) * w) = ((u : G) * w) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hconj : x * ((u : G) * w) * x⁻¹ = (u : G) * w := by
    rw [hcomm]; group
  exact ((S.conj_mul_eq_iff hE hxM u.2 hw).mp hconj).1

theorem mem_centralizer_mul_of_mem {u : ↥(blockU J)} {w ℓ : G} (hw : w ∈ blockW J)
    (hℓJ : ℓ ∈ J) (hℓu : ℓ * (u : G) * ℓ⁻¹ = u) :
    ℓ ∈ Subgroup.centralizer ({(u : G) * w} : Set G) := by
  have hℓw : ℓ * w * ℓ⁻¹ = w := conj_eq_blockW_of_mem_J hw hℓJ
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc ℓ * ((u : G) * w) = (ℓ * (u : G) * ℓ⁻¹) * (ℓ * w * ℓ⁻¹) * ℓ := by group
    _ = ((u : G) * w) * ℓ := by rw [hℓu, hℓw]

theorem mul_notMem_blockW (S : Setting G M J m) (hZ : blockZ J = ⊥)
    {u : ↥(blockU J)} (hu1 : u ≠ 1) {w : G} (hw : w ∈ blockW J) :
    (u : G) * w ∉ blockW J := by
  intro h
  have huW : (u : G) ∈ blockW J := by
    have h2 : (u : G) = ((u : G) * w) * w⁻¹ := by group
    rw [h2]
    exact (blockW J).mul_mem h ((blockW J).inv_mem hw)
  have hbot : (u : G) ∈ blockU J ⊓ blockW J := Subgroup.mem_inf.mpr ⟨u.2, huW⟩
  rw [blockU_inf_blockW S hZ, Subgroup.mem_bot] at hbot
  exact hu1 (Subtype.ext hbot)

theorem pCoreOf_le_centralizer_mul (S : Setting G M J m) (hE : BlockCase J m)
    {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) :
    pCoreOf 2 M ≤ Subgroup.centralizer ({(u : G) * w} : Set G) := by
  rw [pCoreOf_eq (S := S) hE]
  exact sup_le (blockU_le_centralizer_mul S hw) (blockW_le_centralizer_mul S hE hw)

theorem conj_mem_pCoreOf_centralizer_of_centralizes {u : ↥(blockU J)}
    {w ℓ x : G} (hw : w ∈ blockW J) (hℓJ : ℓ ∈ J)
    (hℓu : ℓ * (u : G) * ℓ⁻¹ = u)
    (hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G))) :
    ℓ * x * ℓ⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) := by
  let H : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  have hℓw : ℓ * w * ℓ⁻¹ = w := conj_eq_blockW_of_mem_J hw hℓJ
  have hℓH : ℓ ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ℓ * ((u : G) * w) = (ℓ * (u : G) * ℓ⁻¹) * (ℓ * w * ℓ⁻¹) * ℓ := by group
      _ = ((u : G) * w) * ℓ := by rw [hℓu, hℓw]
  have hℓN : ℓ ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hℓH
  have hℓN' : ℓ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H hℓN
  exact (Subgroup.mem_normalizer_iff.mp hℓN' x).mp hx

theorem isPGroup_inf_sup_pCoreOf_centralizer (S : Setting G M J m)
    (hE : BlockCase J m) {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) :
    IsPGroup 2 ↥((pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) ⊔
      pCoreOf 2 M) ⊓ M) := by
  let H : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE hw
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_normalizer (H := H)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hJR : AW ≤ Subgroup.normalizer (R : Set G) := hAWleH.trans hHleNR
  have hsup : IsPGroup 2 ↥(R ⊔ AW) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_sup_of_normal_left'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hJR
  simpa [H, R, AW] using hsup.to_le inf_le_left

theorem conj_eq_of_mem_inf_sup_pCoreOf_centralizer (S : Setting G M J m)
    (hE : BlockCase J m) {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) {t : G}
    (ht : t ∈ (pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) ⊔
      pCoreOf 2 M) ⊓ M) : t * (u : G) * t⁻¹ = u := by
  let H : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE hw
  have htH : t ∈ H :=
    (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hAWleH) (by simpa [R, AW] using ht.1)
  exact conj_eq_of_mem_centralizer_mul (S := S) hE hw ht.2 (by simpa [H] using htH)

theorem conj_mem_inf_sup_pCoreOf_centralizer_of_centralizes (S : Setting G M J m)
    (hE : BlockCase J m) {u : ↥(blockU J)} {w : G} (hw : w ∈ blockW J) {ℓ t : G}
    (hℓJ : ℓ ∈ J)
    (hℓu : ℓ * (u : G) * ℓ⁻¹ = u)
    (ht : t ∈ (pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) ⊔
      pCoreOf 2 M) ⊓ M) :
    ℓ * t * ℓ⁻¹ ∈ (pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) ⊔
      pCoreOf 2 M) ⊓ M := by
  let H : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE hw
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_normalizer (H := H)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hℓM : ℓ ∈ M := S.le hℓJ
  have hℓH : ℓ ∈ H := by
    simpa [H] using mem_centralizer_mul_of_mem hw hℓJ hℓu
  have hℓR : ℓ ∈ Subgroup.normalizer (R : Set G) := hHleNR hℓH
  have hℓAW : ℓ ∈ Subgroup.normalizer (AW : Set G) := by
    rw [show AW = pCoreOf 2 M from rfl,
      CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
    exact hℓM
  have hℓsup : ℓ ∈ Subgroup.normalizer ((R ⊔ AW : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup R AW
      (Subgroup.mem_inf.mpr ⟨hℓR, hℓAW⟩)
  have h1 : t ∈ R ⊔ AW := by simpa [R, AW] using ht.1
  have hmem : ℓ * t * ℓ⁻¹ ∈ (R ⊔ AW) ⊓ M :=
    Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hℓsup t).mp h1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hℓM) t).mp ht.2⟩
  simpa [R, AW] using hmem

private theorem eq_bot_of_card (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {B : Subgroup G} (hBM : B ≤ M)
    (hcard : Nat.card (pCoreOf 2 M) ≤ Nat.card B)
    {E : Subgroup (Vec m ≃ₗ[ZMod 2] Vec m)}
    {f : ↥(B.subgroupOf M) →* (Vec m ≃ₗ[ZMod 2] Vec m)}
    (hEdef : E = f.range) (hroot : ∀ g ∈ E, IsRootElt (quadQ m) (S.vec u) g)
    (hker_le : Nat.card ↥f.ker ≤ Nat.card {v : Vec m // ∀ g ∈ E, g v = v} *
      Nat.card ↥(blockW J)) : E = ⊥ := by
  classical
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  have hu0 : S.vec u ≠ 0 := fun h => hu1 ((S.vec_eq_zero_iff hZ).mp h)
  by_contra hEne
  have hroot_card := card_mul_card_fixed_le (V := Vec m) (Q := quadQ m)
    (nondegenerate_quadQ m) hu hu0 E hroot hEne
  have hcardA : Nat.card (blockU J) = Nat.card (Vec m) :=
    Nat.card_congr (Equiv.ofBijective S.vec ⟨S.vec_injective hZ, S.vec_surjective⟩)
  have hBcard : Nat.card ↥B = Nat.card ↥E * Nat.card ↥f.ker := by
    have hB'card : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
    have h := Subgroup.card_ker_mul_card_range f
    rw [← hEdef, hB'card, mul_comm] at h
    exact h.symm
  have hle : Nat.card ↥B * 2 ≤ Nat.card ↥B := by
    calc Nat.card ↥B * 2
        = (Nat.card ↥E * Nat.card ↥f.ker) * 2 := by rw [hBcard]
      _ ≤ (Nat.card ↥E * (Nat.card {v : Vec m // ∀ g ∈ E, g v = v} *
            Nat.card ↥(blockW J))) * 2 := by
          exact Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left _ hker_le)
      _ = (Nat.card ↥E * Nat.card {v : Vec m // ∀ g ∈ E, g v = v} * 2) *
            Nat.card ↥(blockW J) := by ring
      _ ≤ Nat.card (Vec m) * Nat.card ↥(blockW J) :=
          Nat.mul_le_mul_right _ hroot_card
      _ = Nat.card (pCoreOf 2 M) := by rw [S.card_pCoreOf hE, hcardA]
      _ ≤ Nat.card ↥B := hcard
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hle' : Nat.card ↥B * 2 ≤ Nat.card ↥B * 1 := by simpa using hle
  have h21 : 2 ≤ 1 := (Nat.mul_le_mul_left_iff hBpos).mp hle'
  omega

private noncomputable abbrev fB (S : Setting G M J m) (hZ : blockZ J = ⊥)
    (B : Subgroup G) : ↥(B.subgroupOf M) →* (Vec m ≃ₗ[ZMod 2] Vec m) :=
  (S.lin hZ).comp (B.subgroupOf M).subtype

private theorem exists_pOf_fixed (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {B : Subgroup G} (hBT : B ≤ T) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hZ : blockZ J = ⊥) :
    ∃ pOf : ↥(fB S hZ B).ker → ↥(blockU J) × G,
      (∀ x, (pOf x).2 ∈ blockW J ∧ (((x.1.1 : ↥M) : G)) = ((pOf x).1 : G) * (pOf x).2) ∧
      (∀ x, ∀ g ∈ (fB S hZ B).range, g (S.vec (pOf x).1) = S.vec (pOf x).1) := by
  classical
  have hBM : B ≤ M := hBT.trans hTM
  have hex : ∀ x : ↥(fB S hZ B).ker,
      ∃ p : ↥(blockU J) × G, p.2 ∈ blockW J ∧ (((x.1.1 : ↥M) : G)) = (p.1 : G) * p.2 := by
    intro x
    have hxB : (((x.1.1 : ↥M) : G)) ∈ B := Subgroup.mem_subgroupOf.mp x.1.2
    have h1 : S.lin hZ (x.1.1 : ↥M) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨a, ha, w', hw', hxeq⟩ :=
      exists_mul_of_lin_eq_one (S := S) hE hZ hBM (hT.to_le hBT) hxB (by simpa using h1)
    exact ⟨(⟨a, ha⟩, w'), hw', hxeq⟩
  let pOf (x : ↥(fB S hZ B).ker) : ↥(blockU J) × G := Classical.choose (hex x)
  have hpOf (x : ↥(fB S hZ B).ker) :
      (pOf x).2 ∈ blockW J ∧ (((x.1.1 : ↥M) : G)) = ((pOf x).1 : G) * (pOf x).2 :=
    Classical.choose_spec (hex x)
  have hfixOf : ∀ x, ∀ g ∈ (fB S hZ B).range, g (S.vec (pOf x).1) = S.vec (pOf x).1 := by
    intro x g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
    have hyB : (((y.1 : ↥M) : G)) ∈ B := Subgroup.mem_subgroupOf.mp y.2
    have hxB : (((x.1.1 : ↥M) : G)) ∈ B := Subgroup.mem_subgroupOf.mp x.1.2
    have hcomm : (((y.1 : ↥M) : G)) * ((pOf x).1 : G) *
        ((((y.1 : ↥M) : G)))⁻¹ = (pOf x).1 := by
      have hab := hB (((y.1 : ↥M) : G)) hyB (((x.1.1 : ↥M) : G)) hxB
      have hconj : (((y.1 : ↥M) : G)) * (((x.1.1 : ↥M) : G)) *
          ((((y.1 : ↥M) : G)))⁻¹ = (((x.1.1 : ↥M) : G)) := by
        rw [hab]; group
      rw [(hpOf x).2] at hconj
      exact ((S.conj_mul_eq_iff hE y.1.2 (pOf x).1.2 (hpOf x).1).mp hconj).1
    calc S.lin hZ y.1 (S.vec (pOf x).1)
        = S.vec ⟨(((y.1 : ↥M) : G)) * ((pOf x).1 : G) * ((((y.1 : ↥M) : G)))⁻¹,
            conj_mem_blockU S y.1.2 (pOf x).1.2⟩ := S.lin_vec hZ y.1 _
      _ = S.vec (pOf x).1 := congrArg S.vec (Subtype.ext hcomm)
  exact ⟨pOf, hpOf, hfixOf⟩

private theorem exists_ker_le_fixed (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {B : Subgroup G} (hBT : B ≤ T) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hZ : blockZ J = ⊥) :
    ∃ (E : Subgroup (Vec m ≃ₗ[ZMod 2] Vec m))
      (f : ↥(B.subgroupOf M) →* (Vec m ≃ₗ[ZMod 2] Vec m)),
      E = f.range ∧ (∀ x, f x = S.lin hZ x.1) ∧
      (∀ g ∈ E, IsRootElt (quadQ m) (S.vec u) g) ∧
      Nat.card ↥f.ker ≤ Nat.card {v : Vec m // ∀ g ∈ E, g v = v} *
        Nat.card ↥(blockW J) := by
  classical
  have hBM : B ≤ M := hBT.trans hTM
  let f : ↥(B.subgroupOf M) →* (Vec m ≃ₗ[ZMod 2] Vec m) := fB S hZ B
  let E : Subgroup (Vec m ≃ₗ[ZMod 2] Vec m) := f.range
  have hxT : ∀ x : ↥(B.subgroupOf M), (((x.1 : ↥M) : G)) ∈ T := fun x =>
    hBT (Subgroup.mem_subgroupOf.mp x.2)
  have hroot : ∀ g ∈ E, IsRootElt (quadQ m) (S.vec u) g := by
    intro g hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨S.lin_mem_orthogonalGroup hZ x.1, ?_, ?_⟩
    · exact (S.lin_vec_eq_iff hZ x.1 u).mpr (hTu _ (hxT x))
    · intro z hz
      exact S.lin_sub_mem_span_of_singular hZ hu hTM hT hTu hTn (hxT x) hz
  obtain ⟨pOf, hpOf, hfixOf⟩ :=
    exists_pOf_fixed (S := S) hE hu1 hu hTM hT hTu hTn hBT hB hZ
  let φ : ↥f.ker → {v : Vec m // ∀ g ∈ E, g v = v} × ↥(blockW J) := fun x =>
    (⟨S.vec (pOf x).1, hfixOf x⟩, ⟨(pOf x).2, (hpOf x).1⟩)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hfix_eq : S.vec (pOf x).1 = S.vec (pOf y).1 :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have hw_eq : (pOf x).2 = (pOf y).2 := congrArg Subtype.val (congrArg Prod.snd hxy)
    have ha_eq : (pOf x).1 = (pOf y).1 := S.vec_injective hZ hfix_eq
    have hx_eq : (((x.1.1 : ↥M) : G)) = (((y.1.1 : ↥M) : G)) := by
      calc (((x.1.1 : ↥M) : G)) = ((pOf x).1 : G) * (pOf x).2 := (hpOf x).2
        _ = ((pOf y).1 : G) * (pOf y).2 := by rw [ha_eq, hw_eq]
        _ = (((y.1.1 : ↥M) : G)) := (hpOf y).2.symm
    exact Subtype.ext (Subtype.ext (Subtype.ext hx_eq))
  refine ⟨E, f, rfl, fun x => rfl, hroot, ?_⟩
  have h := Nat.card_le_card_of_injective φ hinj
  simpa [Nat.card_prod] using h

theorem eq_pCoreOf_of_singular (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {B : Subgroup G} (hBT : B ≤ T) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcard : Nat.card (pCoreOf 2 M) ≤ Nat.card B) : B = pCoreOf 2 M := by
  classical
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  have hBM : B ≤ M := hBT.trans hTM
  obtain ⟨E, f, hEdef, hfmap, hroot, hker_le⟩ :=
    exists_ker_le_fixed (S := S) hE hu1 hu hTM hT hTu hTn hBT hB hZ
  have hEbot : E = ⊥ :=
    eq_bot_of_card (S := S) hE hu1 hu hBM hcard hEdef hroot hker_le
  have hf_one : ∀ x : ↥(B.subgroupOf M), S.lin hZ x.1 = 1 := by
    intro x
    have hxr : S.lin hZ x.1 ∈ E := by
      rw [hEdef, ← hfmap x]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rw [hEbot] at hxr
    exact Subgroup.mem_bot.mp hxr
  have hB_le : B ≤ pCoreOf 2 M := by
    intro x hx
    have hxM : x ∈ M := hBM hx
    let xM : ↥M := ⟨x, hxM⟩
    let x' : ↥(B.subgroupOf M) := ⟨xM, Subgroup.mem_subgroupOf.mpr hx⟩
    have hx1 : S.lin hZ xM = 1 := hf_one x'
    exact mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hBM (hT.to_le hBT) hx (by simpa using hx1)
  exact Subgroup.eq_of_le_of_card_ge hB_le hcard

theorem pCoreOf_centralizer_conj {x y g : G} (h : g * x * g⁻¹ = y) :
    pCoreOf 2 (Subgroup.centralizer ({y} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({x} : Set G))).map (MulAut.conj g).toMonoidHom := by
  rw [← h, ← CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton g x]
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g)
    (Subgroup.centralizer ({x} : Set G))

theorem pCoreOf_centralizer_le_of_singular (hE : BlockCase J m) {u : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) :
    pCoreOf 2 (Subgroup.centralizer ({(u : G) * w} : Set G)) ≤ M := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE hw
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_normalizer (H := H)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hJR : AW ≤ Subgroup.normalizer (R : Set G) := hAWleH.trans hHleNR
  have hJM : AW ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hNJ : Subgroup.normalizer (AW : Set G) ≤ M := by
    rw [show AW = pCoreOf 2 M from rfl,
      CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
  refine CFSG.CGT.Hall82.le_of_forall_eq (p := 2) (M := M) (J := AW) (R := R)
    hJM hNJ ?_ ?_ ?_ hJR ?_
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  · intro a ha b hb
    exact pCoreOf_comm (S := S) hE ha hb
  · intro A hA hab hcardA
    have hTleM : (R ⊔ AW) ⊓ M ≤ M := inf_le_right
    have hT : IsPGroup 2 ↥((R ⊔ AW) ⊓ M) := by
      simpa [H, R, AW] using
        isPGroup_inf_sup_pCoreOf_centralizer (S := S) hE (u := u) hw
    have hTu : ∀ t ∈ (R ⊔ AW) ⊓ M, t * (u : G) * t⁻¹ = u := by
      intro t ht
      exact conj_eq_of_mem_inf_sup_pCoreOf_centralizer (S := S) hE hw
        (by simpa [H, R, AW] using ht)
    have hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u →
        ∀ t ∈ (R ⊔ AW) ⊓ M, ℓ * t * ℓ⁻¹ ∈ (R ⊔ AW) ⊓ M := by
      intro ℓ hℓJ hℓu t ht
      exact conj_mem_inf_sup_pCoreOf_centralizer_of_centralizes (S := S) hE hw hℓJ hℓu
        (by simpa [H, R, AW] using ht)
    exact eq_pCoreOf_of_singular (S := S) hE hu1 hu hTleM hT hTu hTn hA hab hcardA

theorem conj_ne_of_singular (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) {z : G} (hz : z ∈ blockW J)
    (hz1 : z ≠ 1) (g : G) : g * z * g⁻¹ ≠ (u : G) * w := by
  intro hg
  let Cz : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let Ct : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  have hRmap : pCoreOf 2 Ct = (pCoreOf 2 Cz).map (MulAut.conj g).toMonoidHom :=
    pCoreOf_centralizer_conj hg
  have hCz_eq : pCoreOf 2 Cz = pCoreOf 2 M := pCoreOf_centralizer_eq (S := S) hE hz hz1
  have hR_eq : pCoreOf 2 Ct = (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom := by
    rw [hRmap, hCz_eq]
  have hRleM : pCoreOf 2 Ct ≤ M := pCoreOf_centralizer_le_of_singular (S := S) hE hu1 hu hw
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 Ct) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ct
  have hRab : ∀ x ∈ pCoreOf 2 Ct, ∀ y ∈ pCoreOf 2 Ct, x * y = y * x := by
    intro x hx y hy
    rw [hR_eq] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, pCoreOf_comm (S := S) hE ha hb]
  have hRu : ∀ x ∈ pCoreOf 2 Ct, x * (u : G) * x⁻¹ = u := by
    intro x hx
    exact conj_eq_of_mem_centralizer_mul (S := S) hE hw (hRleM hx)
      (by simpa [Ct] using CFSG.LieType.BorelTits.pCoreOf_le 2 Ct hx)
  have hRn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u →
      ∀ x ∈ pCoreOf 2 Ct, ℓ * x * ℓ⁻¹ ∈ pCoreOf 2 Ct :=
    fun ℓ hℓJ hℓu x hx =>
      conj_mem_pCoreOf_centralizer_of_centralizes hw hℓJ hℓu hx
  have hRcard : Nat.card (pCoreOf 2 Ct) = Nat.card (pCoreOf 2 M) := by
    rw [hR_eq]
    exact Subgroup.card_map_of_injective (K := pCoreOf 2 M)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hReq : pCoreOf 2 Ct = pCoreOf 2 M :=
    eq_pCoreOf_of_singular (S := S) hE hu1 hu hRleM hR2 hRu hRn le_rfl hRab hRcard.ge
  have hmap : (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom = pCoreOf 2 M := by
    rw [← hR_eq, hReq]
  have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hmap
  have hgM : g ∈ M := by
    rw [← CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
    exact hgN
  have htW : ((u : G) * w) ∈ blockW J := by
    simpa [hg] using conj_mem_blockW S hgM hz
  exact mul_notMem_blockW S (S.blockZ_eq_bot hE.h1) hu1 hw htW

theorem mem_of_conj_eq_of_singular_of_le (hE : BlockCase J m) {u u' : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu1' : u' ≠ 1) (hu : quadQ m (S.vec u) = 0)
    (hu' : quadQ m (S.vec u') = 0) {w w' : G} (hw : w ∈ blockW J) (hw' : w' ∈ blockW J)
    (hC : Subgroup.centralizer ({(u : G) * w} : Set G) ≤ M) {g : G}
    (hg : g * ((u : G) * w) * g⁻¹ = (u' : G) * w') : g ∈ M := by
  classical
  let Cx : Subgroup G := Subgroup.centralizer ({(u : G) * w} : Set G)
  let Cy : Subgroup G := Subgroup.centralizer ({(u' : G) * w'} : Set G)
  let AW : Subgroup G := pCoreOf 2 M
  have hAWCx : AW ≤ Cx := pCoreOf_le_centralizer_mul S hE hw
  have hCxM : Cx ≤ M := hC
  have hCxN : Cx ≤ Subgroup.normalizer (AW : Set G) := by
    rw [show AW = pCoreOf 2 M from rfl,
      CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
    exact hCxM
  have hAWRx : AW ≤ pCoreOf 2 Cx :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAWCx hCxN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hRymap : pCoreOf 2 Cy = (pCoreOf 2 Cx).map (MulAut.conj g).toMonoidHom :=
    pCoreOf_centralizer_conj hg
  have hBle : AW.map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 Cy := by
    rw [hRymap]
    exact Subgroup.map_mono hAWRx
  have hRyM : pCoreOf 2 Cy ≤ M :=
    pCoreOf_centralizer_le_of_singular (S := S) hE hu1' hu' hw'
  have hRy2 : IsPGroup 2 ↥(pCoreOf 2 Cy) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Cy
  have hRyu : ∀ x ∈ pCoreOf 2 Cy, x * (u' : G) * x⁻¹ = u' := by
    intro x hx
    exact conj_eq_of_mem_centralizer_mul (S := S) hE hw' (hRyM hx)
      (by simpa [Cy] using CFSG.LieType.BorelTits.pCoreOf_le 2 Cy hx)
  have hRyn : ∀ ℓ ∈ J, ℓ * (u' : G) * ℓ⁻¹ = u' →
      ∀ x ∈ pCoreOf 2 Cy, ℓ * x * ℓ⁻¹ ∈ pCoreOf 2 Cy :=
    fun ℓ hℓJ hℓu' x hx =>
      conj_mem_pCoreOf_centralizer_of_centralizes hw' hℓJ hℓu' hx
  have hRab : ∀ x ∈ AW.map (MulAut.conj g).toMonoidHom,
      ∀ y ∈ AW.map (MulAut.conj g).toMonoidHom, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, pCoreOf_comm (S := S) hE ha hb]
  have hBcard : Nat.card (pCoreOf 2 M) ≤
      Nat.card ↥(AW.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (K := pCoreOf 2 M)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  have hBeq : AW.map (MulAut.conj g).toMonoidHom = pCoreOf 2 M :=
    eq_pCoreOf_of_singular (S := S) hE hu1' hu' hRyM hRy2 hRyu hRyn hBle hRab hBcard
  have hmap : (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom = pCoreOf 2 M := hBeq
  have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hmap
  rw [← CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
  exact hgN

end CFSG.CGT.Harada80.Setting
