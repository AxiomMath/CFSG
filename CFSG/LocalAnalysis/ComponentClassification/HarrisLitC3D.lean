module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks

section Blocks

variable {K : Type} [Field K]

abbrev bl : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 4) K :=
  bdSL.comp (MonoidHom.inl _ _)

abbrev br : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 4) K :=
  bdSL.comp (MonoidHom.inr _ _)

theorem coe_bl (a : SpecialLinearGroup (Fin 2) K) :
    ((bl a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd (a : Matrix (Fin 2) (Fin 2) K) 1 := rfl

theorem coe_br (b : SpecialLinearGroup (Fin 2) K) :
    ((br b : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd 1 (b : Matrix (Fin 2) (Fin 2) K) := rfl

theorem bl_mul_br (a b : SpecialLinearGroup (Fin 2) K) : bl a * br b = br b * bl a := by
  simp only [bl, br, MonoidHom.comp_apply, ← map_mul]
  congr 1
  ext <;> simp

abbrev entry (i j : Fin 2) (g : SpecialLinearGroup (Fin 2) K) : K :=
  (g : Matrix (Fin 2) (Fin 2) K) i j

theorem bd_inj {a b a' b' : Matrix (Fin 2) (Fin 2) K} (h : bd a b = bd a' b') :
    a = a' ∧ b = b' :=
  ⟨by rw [← ul_bd a b, h, ul_bd], by rw [← lr_bd a b, h, lr_bd]⟩

theorem scalar_eq_bd (c : K) : scalar (Fin 4) c = bd (c • 1) (c • 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bl_comm {t : SpecialLinearGroup (Fin 4) K} {l : K}
    (ht : (t : Matrix (Fin 4) (Fin 4) K) = X1 l) (a : SpecialLinearGroup (Fin 2) K) :
    bl a * t = t * bl a :=
  Subtype.ext (by
    change (bl a : Matrix (Fin 4) (Fin 4) K) * t = t * (bl a : Matrix (Fin 4) (Fin 4) K)
    rw [ht, coe_bl]
    exact bd_comm_X1 _ _ l)

theorem br_comm {t : SpecialLinearGroup (Fin 4) K} {l : K}
    (ht : (t : Matrix (Fin 4) (Fin 4) K) = X1 l) (b : SpecialLinearGroup (Fin 2) K) :
    br b * t = t * br b :=
  Subtype.ext (by
    change (br b : Matrix (Fin 4) (Fin 4) K) * t = t * (br b : Matrix (Fin 4) (Fin 4) K)
    rw [ht, coe_br]
    exact bd_comm_X1 _ _ l)

theorem exists_bd_of_comm (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0)
    {n : SpecialLinearGroup (Fin 4) K}
    (hn : (n : Matrix (Fin 4) (Fin 4) K) * X1 l = X1 l * n) :
    ∃ A D A' D' : Matrix (Fin 2) (Fin 2) K, (n : Matrix (Fin 4) (Fin 4) K) = bd A D ∧
      ((n⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = bd A' D' ∧
      A * A' = 1 ∧ D * D' = 1 := by
  set N : Matrix (Fin 4) (Fin 4) K := (n : Matrix (Fin 4) (Fin 4) K) with hN
  set N' : Matrix (Fin 4) (Fin 4) K :=
    ((n⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hN'
  have h1 : N * N' = 1 := by
    rw [hN, hN', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h1' : N' * N = 1 := by
    rw [hN, hN', ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hn' : N' * X1 l = X1 l * N' := by
    calc N' * X1 l = N' * X1 l * (N * N') := by rw [h1, Matrix.mul_one]
      _ = N' * (X1 l * N) * N' := by simp only [Matrix.mul_assoc]
      _ = N' * (N * X1 l) * N' := by rw [hn]
      _ = (N' * N) * X1 l * N' := by simp only [Matrix.mul_assoc]
      _ = X1 l * N' := by rw [h1', Matrix.one_mul]
  have hb := eq_bd (isBD_of_comm_X1 h2 hl hn)
  have hb' := eq_bd (isBD_of_comm_X1 h2 hl hn')
  refine ⟨ul N, lr N, ul N', lr N', hb, hb', ?_⟩
  have h3 : bd (ul N * ul N') (lr N * lr N') = bd 1 1 := by
    rw [← bd_mul, ← hb, ← hb', h1, bd_one]
  exact bd_inj h3

theorem conj_bl (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) {n : SpecialLinearGroup (Fin 4) K}
    (hn : (n : Matrix (Fin 4) (Fin 4) K) * X1 l = X1 l * n) (a : SpecialLinearGroup (Fin 2) K) :
    ∃ a' : SpecialLinearGroup (Fin 2) K, n * bl a * n⁻¹ = bl a' := by
  obtain ⟨A, D, A', D', hA, hA', hAA, hDD⟩ := exists_bd_of_comm h2 hl hn
  have hdet : (A * (a : Matrix (Fin 2) (Fin 2) K) * A').det = 1 := by
    rw [det_mul, det_mul, mul_comm (A.det), mul_assoc, ← det_mul, hAA, det_one, mul_one, a.2]
  refine ⟨⟨A * (a : Matrix (Fin 2) (Fin 2) K) * A', hdet⟩, Subtype.ext ?_⟩
  change (n : Matrix (Fin 4) (Fin 4) K) * (bl a : Matrix (Fin 4) (Fin 4) K) *
    ((n⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd (A * (a : Matrix (Fin 2) (Fin 2) K) * A') 1
  rw [hA, hA', coe_bl, bd_mul, bd_mul, Matrix.mul_one, hDD]

theorem conj_br (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) {n : SpecialLinearGroup (Fin 4) K}
    (hn : (n : Matrix (Fin 4) (Fin 4) K) * X1 l = X1 l * n) (b : SpecialLinearGroup (Fin 2) K) :
    ∃ b' : SpecialLinearGroup (Fin 2) K, n * br b * n⁻¹ = br b' := by
  obtain ⟨A, D, A', D', hA, hA', hAA, hDD⟩ := exists_bd_of_comm h2 hl hn
  have hdet : (D * (b : Matrix (Fin 2) (Fin 2) K) * D').det = 1 := by
    rw [det_mul, det_mul, mul_comm (D.det), mul_assoc, ← det_mul, hDD, det_one, mul_one, b.2]
  refine ⟨⟨D * (b : Matrix (Fin 2) (Fin 2) K) * D', hdet⟩, Subtype.ext ?_⟩
  change (n : Matrix (Fin 4) (Fin 4) K) * (br b : Matrix (Fin 4) (Fin 4) K) *
    ((n⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd 1 (D * (b : Matrix (Fin 2) (Fin 2) K) * D')
  rw [hA, hA', coe_br, bd_mul, bd_mul, Matrix.mul_one, hAA]

theorem eq_of_bl_inv_mul_br_mem {a b : SpecialLinearGroup (Fin 2) K}
    (h : (bl a)⁻¹ * br b ∈ scalars 4 K) :
    (a = 1 ∧ b = 1) ∨ (a = negOne2 ∧ b = negOne2) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have hm : ((bl a)⁻¹ * br b : SpecialLinearGroup (Fin 4) K) = bdSL (a⁻¹, b) := by
    rw [← map_inv]
    change bdSL _ * bdSL _ = _
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [hm, coe_bdSL, scalar_eq_bd] at hc
  obtain ⟨ha, hb⟩ := bd_inj hc
  simp only at ha hb
  have hc2 : (c : K) * c = 1 := by
    have h1 := b.2
    rw [hb, det_smul, det_one, mul_one, Fintype.card_fin, pow_two] at h1
    exact h1
  have hainv : (a : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    have h1 : (a : Matrix (Fin 2) (Fin 2) K) * ((a⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [ha, Matrix.mul_smul, Matrix.mul_one] at h1
    calc (a : Matrix (Fin 2) (Fin 2) K) = ((c : K) * c) • (a : Matrix (Fin 2) (Fin 2) K) := by
          rw [hc2, one_smul]
      _ = (c : K) • ((c : K) • (a : Matrix (Fin 2) (Fin 2) K)) := by rw [smul_smul]
      _ = (c : K) • 1 := by rw [h1]
  rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
  · left
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [hainv, h1, one_smul]
      rfl
    · rw [hb, h1, one_smul]
      rfl
  · right
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [hainv, h1, neg_one_smul]
      rfl
    · rw [hb, h1, neg_one_smul]
      rfl

theorem bl_negOne2 : bl (negOne2 : SpecialLinearGroup (Fin 2) K) = negOne4 * br negOne2 := by
  rw [← bdSL_negOne]
  change bdSL _ = bdSL _ * bdSL _
  rw [← map_mul]
  congr 1
  apply Prod.ext
  · simp
  · simp only [MonoidHom.inr_apply, MonoidHom.inl_apply, Prod.snd_mul]
    rw [← pow_two, negOne2_sq]

end Blocks

variable {G : Type} [Group G] {Q : Subgroup G} {K : Type} [Field K] [Finite K]

theorem x_alternative (hK2 : ringChar K ≠ 2) {θ : SpecialLinearGroup (Fin 4) K →* ↥Q}
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ scalars 4 K) (hθ1 : θ negOne4 = 1)
    {t : SpecialLinearGroup (Fin 4) K} {l : K} (hl : l = 1 ∨ l = -1)
    (ht : (t : Matrix (Fin 4) (Fin 4) K) = X1 l) :
    ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {((θ t : ↥Q) : G)} ∧
      X₂ ≤ Q ⊓ centralizer {((θ t : ↥Q) : G)} ∧
      (X₁.subgroupOf (Q ⊓ centralizer {((θ t : ↥Q) : G)})).IsSubnormal ∧
      (X₂.subgroupOf (Q ⊓ centralizer {((θ t : ↥Q) : G)})).IsSubnormal ∧
      X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers ((θ t : ↥Q) : G) ∧
      IsSLTwoOver (Nat.card K) ↥X₁ ∧ IsSLTwoOver (Nat.card K) ↥X₂ := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hl0 : l ≠ 0 := by rcases hl with rfl | rfl <;> norm_num
  set w : G := ((θ t : ↥Q) : G) with hw
  set CW := Q ⊓ centralizer ({w} : Set G) with hCW
  set X₁ : Subgroup G := ((θ.comp bl).range).map Q.subtype with hX₁
  set X₂ : Subgroup G := ((θ.comp br).range).map Q.subtype with hX₂
  set N₀ : Subgroup G :=
    ((θ.comp (centralizer ({t} : Set (SpecialLinearGroup (Fin 4) K))).subtype).range).map
      Q.subtype with hN₀
  have hmemX₁ : ∀ g, g ∈ X₁ ↔ ∃ a, ((θ (bl a) : ↥Q) : G) = g := fun g => by
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have hmemX₂ : ∀ g, g ∈ X₂ ↔ ∃ b, ((θ (br b) : ↥Q) : G) = g := fun g => by
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
  have hcw : ∀ n : SpecialLinearGroup (Fin 4) K, n * t = t * n → ((θ n : ↥Q) : G) ∈ CW := by
    intro n hn
    refine ⟨(θ n).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hw, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hn]
  have hX₁N : X₁ ≤ N₀ := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨bl a, mem_centralizer_singleton_iff.mpr (bl_comm ht a)⟩, rfl⟩, rfl⟩
  have hX₂N : X₂ ≤ N₀ := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨br b, mem_centralizer_singleton_iff.mpr (br_comm ht b)⟩, rfl⟩, rfl⟩
  have hNC : N₀ ≤ CW := by
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    exact hcw n (mem_centralizer_singleton_iff.mp hn)
  have hcommX : ∀ n : SpecialLinearGroup (Fin 4) K, n * t = t * n →
      (n : Matrix (Fin 4) (Fin 4) K) * X1 l = X1 l * n := fun n hn => by
    rw [← ht, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hn]
  have hNX₁ : N₀ ≤ normalizer (X₁ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩ _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨a', ha'⟩ := conj_bl h2 hl0 (hcommX n (mem_centralizer_singleton_iff.mp hn)) a
    refine ⟨_, ⟨a', rfl⟩, ?_⟩
    change ((θ (bl a') : ↥Q) : G) = _
    rw [← ha', map_mul, map_mul, map_inv]
    rfl
  have hNX₂ : N₀ ≤ normalizer (X₂ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨b', hb'⟩ := conj_br h2 hl0 (hcommX n (mem_centralizer_singleton_iff.mp hn)) b
    refine ⟨_, ⟨b', rfl⟩, ?_⟩
    change ((θ (br b') : ↥Q) : G) = _
    rw [← hb', map_mul, map_mul, map_inv]
    rfl
  have hCN : CW ≤ normalizer (N₀ : Set G) := by
    apply Sol76.le_normalizer_of_forall_conj_mem
    rintro y ⟨hyQ, hyw⟩ _ ⟨_, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ := hθs ⟨y, hyQ⟩
    have hmt : m * t * m⁻¹ * t⁻¹ ∈ scalars 4 K := hθk (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hm]
      apply Subtype.ext
      have h1 := mem_centralizer_singleton_iff.mp hyw
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hw] at h1
      calc y * (θ t : G) * y⁻¹ * (θ t : G)⁻¹ = (y * (θ t : G)) * y⁻¹ * (θ t : G)⁻¹ := rfl
        _ = ((θ t : G) * y) * y⁻¹ * (θ t : G)⁻¹ := by rw [h1]
        _ = 1 := by group)
    obtain ⟨z, hz, hzt⟩ : ∃ z ∈ scalars 4 K, m * t * m⁻¹ = z * t := ⟨_, hmt, by group⟩
    have hzc : z ∈ center (SpecialLinearGroup (Fin 4) K) := scalars_le_center 4 K hz
    have hzc' : ∀ g, g * z = z * g := mem_center_iff.mp hzc
    have hzi : ∀ g, g * z⁻¹ = z⁻¹ * g := mem_center_iff.mp (inv_mem hzc)
    have hm1 : m⁻¹ * t * m = z⁻¹ * t := by
      have h3 : m⁻¹ * (z * t) * m = z * (m⁻¹ * t * m) := by
        rw [show m⁻¹ * (z * t) * m = (m⁻¹ * z) * t * m by group, hzc' m⁻¹]
        group
      rw [← hzt] at h3
      have h4 : t = z * (m⁻¹ * t * m) := by rw [← h3]; group
      calc m⁻¹ * t * m = z⁻¹ * (z * (m⁻¹ * t * m)) := by group
        _ = z⁻¹ * t := by rw [← h4]
    have hn' : m * n * m⁻¹ ∈ centralizer ({t} : Set (SpecialLinearGroup (Fin 4) K)) := by
      rw [mem_centralizer_singleton_iff]
      have hnt := mem_centralizer_singleton_iff.mp hn
      calc m * n * m⁻¹ * t = m * n * (m⁻¹ * t * m) * m⁻¹ := by group
        _ = m * n * (z⁻¹ * t) * m⁻¹ := by rw [hm1]
        _ = m * (n * z⁻¹) * t * m⁻¹ := by group
        _ = m * (z⁻¹ * n) * t * m⁻¹ := by rw [hzi n]
        _ = (m * z⁻¹) * n * t * m⁻¹ := by group
        _ = (z⁻¹ * m) * n * t * m⁻¹ := by rw [hzi m]
        _ = z⁻¹ * (m * (n * t) * m⁻¹) := by group
        _ = z⁻¹ * (m * (t * n) * m⁻¹) := by rw [hnt]
        _ = z⁻¹ * (m * t * m⁻¹) * (m * n * m⁻¹) := by group
        _ = t * (m * n * m⁻¹) := by rw [hzt]; group
    refine ⟨_, ⟨⟨m * n * m⁻¹, hn'⟩, rfl⟩, ?_⟩
    change ((θ (m * n * m⁻¹) : ↥Q) : G) = _
    rw [map_mul, map_mul, map_inv, hm]
    rfl
  have hs₁ : (X₁.subgroupOf CW).IsSubnormal :=
    Sol76.isSubnormal_subgroupOf_of_le_normalizer hX₁N hNC hNX₁ hCN
  have hs₂ : (X₂.subgroupOf CW).IsSubnormal :=
    Sol76.isSubnormal_subgroupOf_of_le_normalizer hX₂N hNC hNX₂ hCN
  have hinter : ∀ a b, θ (bl a) = θ (br b) → (a = 1 ∧ b = 1) ∨ (a = negOne2 ∧ b = negOne2) := by
    intro a b hab
    apply eq_of_bl_inv_mul_br_mem
    apply hθk
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hwbl : θ (bl negOne2) = θ t ∧ θ (br negOne2) = θ t := by
    have hbl : bl (negOne2 : SpecialLinearGroup (Fin 2) K) = negOne4 * br negOne2 := bl_negOne2
    have hbr : θ (br (negOne2 : SpecialLinearGroup (Fin 2) K)) = θ (bl negOne2) := by
      rw [hbl, map_mul, hθ1, one_mul]
    rcases hl with rfl | rfl
    · have htbr : t = br negOne2 := Subtype.ext (by
        rw [ht, coe_br, X1_eq_bd]
        congr 1
        · rw [one_smul]
        · change (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) = -1
          rw [neg_one_smul])
      rw [htbr]
      exact ⟨hbr.symm, rfl⟩
    · have htbl : t = bl negOne2 := Subtype.ext (by
        rw [ht, coe_bl, X1_eq_bd]
        congr 1
        · change (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) = -1
          rw [neg_one_smul]
        · rw [neg_neg, one_smul])
      rw [htbl]
      exact ⟨rfl, hbr⟩
  have hX₁X₂ : X₁ ⊓ X₂ = zpowers w := by
    apply le_antisymm
    · rintro g ⟨hg₁, hg₂⟩
      obtain ⟨a, rfl⟩ := (hmemX₁ g).mp hg₁
      obtain ⟨b, hb⟩ := (hmemX₂ _).mp hg₂
      rcases hinter a b (Subtype.ext hb.symm) with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [map_one, map_one]
        exact one_mem _
      · rw [hwbl.1]
        exact mem_zpowers _
    · rw [zpowers_le]
      exact ⟨(hmemX₁ w).mpr ⟨negOne2, by rw [hwbl.1]⟩, (hmemX₂ w).mpr ⟨negOne2, by rw [hwbl.2]⟩⟩
  have hne : X₁ ≠ X₂ := by
    intro hEq
    set u : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hu : ((θ (bl u) : ↥Q) : G) ∈ X₂ := hEq ▸ (hmemX₁ _).mpr ⟨u, rfl⟩
    obtain ⟨b, hb⟩ := (hmemX₂ _).mp hu
    rcases hinter u b (Subtype.ext hb.symm) with ⟨h, -⟩ | ⟨h, -⟩
    · have := congrArg (entry 0 1) h
      simp [entry, u] at this
    · have := congrArg (entry 0 1) h
      simp [entry, u, negOne2] at this
  have hinj₁ : Function.Injective (Q.subtype.comp (θ.comp bl)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at ha
    have ha' : θ (bl a) = θ (br 1) := by
      rw [map_one, map_one]
      exact Subtype.ext ha
    rcases hinter a 1 ha' with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      have := congrArg (entry 0 0) h
      simp [entry, negOne2] at this
      have h1 : (1 : K) + 1 = 0 := by linear_combination this
      exact h2 (by rw [← h1]; norm_num)
  have hinj₂ : Function.Injective (Q.subtype.comp (θ.comp br)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at hb
    have hb' : θ (bl 1) = θ (br b) := by
      rw [map_one, map_one]
      exact (Subtype.ext hb).symm
    rcases hinter 1 b hb' with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exfalso
      have := congrArg (entry 0 0) h
      simp [entry, negOne2] at this
      have h1 : (1 : K) + 1 = 0 := by linear_combination this
      exact h2 (by rw [← h1]; norm_num)
  have hrange₁ : (Q.subtype.comp (θ.comp bl)).range = X₁ := by
    rw [MonoidHom.range_comp]
  have hrange₂ : (Q.subtype.comp (θ.comp br)).range = X₂ := by
    rw [MonoidHom.range_comp]
  have := Fintype.ofFinite K
  have hSL : ∀ (X : Subgroup G) (f : SpecialLinearGroup (Fin 2) K →* G),
      Function.Injective f → f.range = X → IsSLTwoOver (Nat.card K) ↥X := by
    intro X f hf hX
    refine ⟨K, inferInstance, inferInstance, (Nat.card_eq_fintype_card).symm, ⟨?_⟩⟩
    exact ((MulEquiv.subgroupCongr hX).symm.trans (MonoidHom.ofInjective hf).symm)
  refine ⟨X₁, X₂, hne, hX₁N.trans hNC, hX₂N.trans hNC, hs₁, hs₂, ?_, hX₁X₂,
    hSL _ _ hinj₁ hrange₁, hSL _ _ hinj₂ hrange₂⟩
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  change ((θ (br b) : ↥Q) : G) * ((θ (bl a) : ↥Q) : G) =
    ((θ (bl a) : ↥Q) : G) * ((θ (br b) : ↥Q) : G)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, bl_mul_br]

end CFSG.ComponentClassification.HarrisLit.C3
