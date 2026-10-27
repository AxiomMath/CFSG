module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma124A
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Type167 (p : ℕ) (X J : Subgroup G) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 J) (isLnA n 2) ∧
      (catalogIs (PSimple 3 X) (isLnA (n + 2) 2) ∨ catalogIs (PSimple 3 X) (isLnA n 8))) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
      (catalogIs (PSimple 3 X) (isOmPA (n + 1) 2) ∨ catalogIs (PSimple 3 X) (isOmMA n 8))) ∨
  (∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
      (catalogIs (PSimple p X) (isOmMA (n + 1) (2 ^ k)) ∨ catalogIs (PSimple p X) (isOmPA n (2 ^ (p * k))) ∨
        (p = 5 ∧ n = 3 ∧ k = 2 ∧ catalogIs (PSimple p X) (isLnA 6 4))))

@[expose] def Type167J (p : ℕ) (J : Subgroup G) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ catalogIs (PSimple 3 J) (isLnA n 2)) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ 6 ≤ n ∧ catalogIs (PSimple 3 J) (isOmMA n 2)) ∨
  (∃ n k : ℕ, Odd n ∧ 3 ≤ n ∧ (k = 1 → 5 ≤ n) ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
    catalogIs (PSimple p J) (isOmPA n (2 ^ k)))

@[expose] def I167At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (B X D J : Subgroup G), p.Prime → p ≠ 2 → IsElemAbelian p B →
    CFSG.Open.IsQuasisimple ↥X → IsChevSimple 2 (PSimple p X) → B ≤ Subgroup.normalizer (X : Set G) →
    GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B →
    (∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set G) → orderOf g = p → g ∈ B) →
    Nat.card ↥(B ⊓ cs X) = p → IsE2 p B D → GLAPComponent p (X ⊓ cs D) J → D = B ⊓ cs J → Type167J p J →
    (HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X) → Type167 p X J

theorem isLnA_facts {m q : ℕ} {i : TauCeti.CFSGIndex} (h : isLnA m q i) : 2 ≤ m ∧ (m = 2 → 4 ≤ q) := by
  rcases h with h | ⟨hm, hq, -⟩ | ⟨hm, hq, -⟩ | ⟨hm, hq, -⟩ | ⟨hm, hq, -⟩
  · cases i with
    | cyclic _ _ => simp [onLie] at h
    | alternating _ _ => simp [onLie] at h
    | sporadic _ => simp [onLie] at h
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d <;> simp [onLie, isLnEps] at h
      rename_i r qq
      simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
      omega
  · omega
  · omega
  · omega
  · omega

theorem isUnA_facts {m q : ℕ} {i : TauCeti.CFSGIndex} (h : isUnA m q i) :
    2 ≤ m ∧ (m = 2 → 4 ≤ q) ∧ (m = 3 → 3 ≤ q) := by
  rcases h with h | ⟨hm, h⟩
  · cases i with
    | cyclic _ _ => simp [onLie] at h
    | alternating _ _ => simp [onLie] at h
    | sporadic _ => simp [onLie] at h
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d <;> simp [onLie, isLnEps] at h
      rename_i r qq
      simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
      omega
  · have := isLnA_facts h
    omega

theorem type167J_of_type172 {p : ℕ} {L K J K₁ KE : Subgroup G} (h : Type172 p L K J K₁ KE) : Type167J p K₁ := by
  rcases h with ⟨hp3, n, hn, -, -, -, hK₁, ⟨i, hi, -⟩⟩ | ⟨hp3, n, hn, -, -, -, hK₁, ⟨i, hi, -⟩⟩ |
    ⟨n, k, hn, hk, hpk, -, -, -, hK₁, ⟨i, hi, -⟩⟩
  · have h1 := isLnA_facts hi
    obtain ⟨t, rfl⟩ := hn
    left
    exact ⟨hp3, 2 * t + 1 - 2, ⟨t - 1, by omega⟩, by omega, hK₁⟩
  · have h1 := isUnA_facts hi
    obtain ⟨t, rfl⟩ := hn
    right; left
    exact ⟨hp3, 2 * t + 1 - 1, ⟨t, by omega⟩, by omega, hK₁⟩
  · have h1 := isUnA_facts hi
    right; right
    obtain ⟨t, rfl⟩ : ∃ t, n = t + t := hn
    refine ⟨t + t - 1, k, ⟨t - 1, by omega⟩, by omega, fun hk1 => ?_, hk, hpk, hK₁⟩
    subst hk1
    simp at h1
    omega

namespace S12

variable {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem B_inf_cs_eq {y : G} {L₁ D₁ K₁ : Subgroup G} (hnb : NbrCfg G m p B x L D₁ K₁ y L₁) :
    B ⊓ cs L₁ = Subgroup.zpowers y := by
  ext b
  constructor
  · rintro ⟨hbB, hb⟩
    exact (hnb.J_cent b hbB).1 (centMod_of_mem_centralizer hb)
  · intro hb
    refine ⟨(Subgroup.zpowers_le.2 hnb.yB) hb, ?_⟩
    show b ∈ Subgroup.centralizer (L₁ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hly : Commute l y := Subgroup.mem_centralizer_singleton_iff.1 (hnb.J_le_cy hl)
    exact (hly.zpow_right n).eq

theorem card_B_inf_cs {y : G} {L₁ D₁ K₁ : Subgroup G} (hnb : NbrCfg G m p B x L D₁ K₁ y L₁) :
    Nat.card ↥(B ⊓ cs L₁) = p := by
  rw [B_inf_cs_eq hnb]
  exact card_zpowers_eq_of_pow hnb.cfg.prime (hnb.cfg.tri.bmax.1.2 y hnb.yB) hnb.y_ne_one

theorem pcomp_cs_D₁ {y : G} {L₁ D₁ K₁ : Subgroup G} (hnb : NbrCfg G m p B x L D₁ K₁ y L₁)
    (hK₁ : GLAPComponent p (L₁ ⊓ cx x) K₁) : GLAPComponent p (L₁ ⊓ cs D₁) K₁ := by
  have h1 : cs D₁ = cx x ⊓ cx y := hnb.cfg.cs_eq hnb.y_mem_D hnb.y_not_mem
  have heq : L₁ ⊓ cs D₁ = L₁ ⊓ cx x := by
    rw [h1]
    exact le_antisymm (inf_le_inf_left L₁ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hnb.J_comp.1)))
  rw [heq]
  exact hK₁

theorem twoRank_L₁B_le {y : G} {L₁ D₁ K₁ : Subgroup G} (hnb : NbrCfg G m p B x L D₁ K₁ y L₁) :
    GLATwoLocalRank p ↥(L₁ ⊔ B) ≤ CFSG.Open.pRank p B := by
  rw [hnb.pRank_B]
  exact (twoRank_le_top hnb.cfg.prime _).trans hnb.cfg.ctx.rank.le

theorem M_layer (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y x' : G} (hyB : y ∈ B) (hx'D : x' ∈ D)
    {L₁ M : Subgroup G} (hL₁ : GLAPComponent p (cx y) L₁) (hM : GLAPComponent p (L₁ ⊓ cx x') M) :
    GLAPComponent p (cx y ⊓ cx x') M ∧ M ≤ GLAPLayer p (cx x') := by
  have hp := h.prime
  have hsub : IsSubnormal (L₁ ⊓ (cx y ⊓ cx x')) (cx y ⊓ cx x') := hL₁.2.1.inf_of_le inf_le_left
  have heq : L₁ ⊓ (cx y ⊓ cx x') = L₁ ⊓ cx x' := by
    rw [← inf_assoc, inf_eq_left.2 hL₁.1]
  rw [heq] at hsub
  have hM' : GLAPComponent p (cx y ⊓ cx x') M := glaPComponent_of_isSubnormal' hp hsub hM
  refine ⟨hM', ?_⟩
  have hle : M ≤ GLAPLayer p (cx y ⊓ cx x') := le_sSup hM'
  have hx'B : x' ∈ B := h.DB hx'D
  have hxp : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem h.tri.bmax.1 hx'B
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_mem h.tri.bmax.1 hyB
  have hcomm : ∀ d ∈ Subgroup.zpowers x', ∀ e ∈ Subgroup.zpowers y, d * e = e * d := fun d hd e he => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (Commute.zpow_zpow (isElemAbelian_commute h.tri.bmax.1 hx'B hyB) i j).eq
  have hbal := hin.bal hp h.ctx.ctx.ctx.kProper (Subgroup.zpowers x') (Subgroup.zpowers y) hxp hyp hcomm
  rw [S3.centralizer_zpowers x', S3.centralizer_zpowers y] at hbal
  rw [inf_comm (cx y), ← hbal] at hle
  exact hle.trans ((layer_le_self p _).trans inf_le_left)

theorem M_quasi (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y x' : G} (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hx'D : x' ∈ D) {L₁ M : Subgroup G} (hL₁ : GLAPComponent p (cx y) L₁) (hL₁q : CFSG.Open.IsQuasisimple ↥L₁)
    (hM : GLAPComponent p (L₁ ⊓ cx x') M) : CFSG.Open.IsQuasisimple ↥M := by
  have hp := h.prime
  obtain ⟨hM', hMlay⟩ := M_layer h hin hyB hx'D hL₁ hM
  have hx'B : x' ∈ B := h.DB hx'D
  have hKy : CFSG.Open.IsKGroup ↥(cx y) := kGroup_centralizer h.ctx.toS6 hy1
  have hD : Subgroup.zpowers x' ≤ cx y :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.tri.bmax.1 hx'B hyB))
  have hI := hin.i145 hp h.odd (cx y) (Subgroup.zpowers x') hKy hD (isPGroup_zpowers_of_mem h.tri.bmax.1 hx'B)
  rw [S3.centralizer_zpowers x'] at hI
  have hMlay' : M ≤ GLAPLayer p (cx y ⊓ cx x') := le_sSup hM'
  have hOM : GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p (cx y ⊓ cx x') :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hM'.2.1
  have hOMle : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  have hperf : (⁅M, M⁆ : Subgroup G) = M := glaPComponent_perfect hM
  have hM_L₁ : M ≤ L₁ := hM.1.trans inf_le_left
  have hY1 : (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (cx y) :=
    (Subgroup.commutator_mono hMlay' hOM).trans hI
  have hY2 : (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) ≤ L₁ :=
    ((Subgroup.commutator_mono le_rfl hOMle).trans hperf.le).trans hM_L₁
  have hY : (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L₁ := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL₁.2.1]
    exact le_inf hY2 hY1
  have hOL : (⁅L₁, GLAPPrimeCoreOf p L₁⁆ : Subgroup G) = ⊥ := S9.commutator_eq_bot_of_isQuasisimple hp hL₁ hL₁q
  rw [Subgroup.commutator_comm] at hOL
  have hc : (⁅(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G), M⁆ : Subgroup G) = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hY hM_L₁).trans hOL.le)
  exact isQuasisimple_of_core_comm hp hM (core_comm_eq_bot hM hc)

theorem anchor_le_K (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hyB : y ∈ B) {L₁ P : Subgroup G}
    (hL₁ : GLAPComponent p (cx y) L₁) (hP : GLAPComponent p (L₁ ⊓ cs D) P) : P ≤ K := by
  have hp := h.prime
  have hsub : IsSubnormal (L₁ ⊓ (cx y ⊓ cs D)) (cx y ⊓ cs D) := hL₁.2.1.inf_of_le inf_le_left
  have heq : L₁ ⊓ (cx y ⊓ cs D) = L₁ ⊓ cs D := by
    rw [← inf_assoc, inf_eq_left.2 hL₁.1]
  rw [heq] at hsub
  have hP' : GLAPComponent p (cx y ⊓ cs D) P := glaPComponent_of_isSubnormal' hp hsub hP
  have hle : P ≤ GLAPLayer p (cx y ⊓ cs D) := le_sSup hP'
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_mem h.tri.bmax.1 hyB
  have hcomm : ∀ d ∈ D, ∀ e ∈ Subgroup.zpowers y, d * e = e * d := fun d hd e he => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (Commute.zpow_right (isElemAbelian_commute h.tri.bmax.1 (h.DB hd) hyB) j).eq
  have hbal := hin.bal hp h.ctx.ctx.ctx.kProper D (Subgroup.zpowers y) (isPGroup_of_isElemAbelian h.elem) hyp hcomm
  rw [S3.centralizer_zpowers y, std_layer h hin] at hbal
  rw [inf_comm (cx y), ← hbal] at hle
  exact hle.trans ((layer_le_self p _).trans inf_le_left)

theorem x_norm_M (h : Cfg12 G m p B x L D K) {x' : G} (hx'D : x' ∈ D) {L₁ M P X₀ : Subgroup G}
    (hBL₁ : B ≤ Subgroup.normalizer (L₁ : Set G)) (hM : GLAPComponent p (L₁ ⊓ cx x') M)
    (hP : GLAPComponent p X₀ P) (hPK : P ≤ K) (hPM : P ≤ M) : x ∈ Subgroup.normalizer (M : Set G) := by
  have hp := h.prime
  set X := L₁ ⊓ cx x' with hX
  have hxcx : x ∈ cx x' := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.elem h.xD hx'D)
  have hxX : x ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_inf' (hBL₁ h.tri.mem) (Subgroup.le_normalizer hxcx)
  have hMx : GLAPComponent p X (GLBConj x M) := by
    have := glaPComponent_gLBConj hM x
    rwa [gLBConj_eq_of_mem_normalizer hxX] at this
  have hPx : P ≤ GLBConj x M := by
    intro u hu
    rw [mem_gLBConj]
    have huK : u ∈ K := hPK hu
    have hcomm : x * u * x⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.1 (h.K_le_cs huK) x h.xD
      rw [this, mul_inv_cancel_right]
    rw [hcomm]
    exact hPM hu
  by_cases hMeq : M = GLBConj x M
  · rw [mem_normalizer_iff_gLBConj_eq]
    exact hMeq.symm
  · exfalso
    have hcomm := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp hM hMx hMeq
    have hPle : P ≤ GLAPPrimeCoreOf p X := by
      have hperf : (⁅P, P⁆ : Subgroup G) = P := glaPComponent_perfect hP
      rw [← hperf]
      exact (Subgroup.commutator_mono hPM hPx).trans hcomm
    have hPX : P ≤ X := hPM.trans hM.1
    have hPO : P ≤ GLAPPrimeCoreOf p P := fun z hz => inf_primeCore_le hp hPX ⟨hz, hPle hz⟩
    apply glaPPrimeCore_ne_top_of_glaPComponent hP
    rw [eq_top_iff]
    intro u _
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 (hPO u.2)
    have : v = u := Subtype.ext hvu
    exact this ▸ hv

theorem not_centMod_of_layer (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y x' : G} (hyB : y ∈ B)
    (hy1 : y ≠ 1) (hx'D : x' ∈ D) (hx'x : x' ∉ Subgroup.zpowers x) {L₁ M P X₀ : Subgroup G}
    (hL₁ : GLAPComponent p (cx y) L₁) (hL₁q : CFSG.Open.IsQuasisimple ↥L₁)
    (hBL₁ : B ≤ Subgroup.normalizer (L₁ : Set G)) (hM : GLAPComponent p (L₁ ⊓ cx x') M)
    (hP : GLAPComponent p X₀ P) (hPK : P ≤ K) (hPM : P ≤ M) (hnc : ¬ CentMod p M x) :
    ∀ L' : Subgroup G, GLAPComponent p (cx x') L' → L' ≤ Ky p K x' → ¬ CentMod p L' x := by
  intro L' hL' hL'Ky hcent
  have hp := h.prime
  have hxM : x ∈ Subgroup.normalizer (M : Set G) := x_norm_M h hx'D hBL₁ hM hP hPK hPM
  have hx'B : x' ∈ B := h.DB hx'D
  obtain ⟨hM', hMlay⟩ := M_layer h hin hyB hx'D hL₁ hM
  have hMq := M_quasi h hin hyB hy1 hx'D hL₁ hL₁q hM
  have hKyeq : Ky p K x' = L' := ky_single_of_centMod h hin hx'D hx'x hL' hL'Ky hcent.1
  have hPKy : P ≤ Ky p K x' := hPK.trans (le_closureIn_self K _)
  set O := GLAPPrimeCoreOf p (cx x') with hO
  have hMcx : M ≤ cx x' := hM.1.trans (inf_le_right)
  have hMN_Ky : M ≤ Subgroup.normalizer (Ky p K x' : Set G) := hMlay.trans (le_normalizer_closureIn_self K _)
  have hMN_O : M ≤ Subgroup.normalizer (O : Set G) := hMcx.trans (le_normalizer_glaPPrimeCoreOf p (cx x'))
  have hWn : M ≤ Subgroup.normalizer ((M ⊓ (Ky p K x' ⊔ O) : Subgroup G) : Set G) := fun m' hm' =>
    mem_normalizer_inf' (Subgroup.le_normalizer hm') (mem_normalizer_sup' (hMN_Ky hm') (hMN_O hm'))
  have hWnormal : ((M ⊓ (Ky p K x' ⊔ O)).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hWn
  have hMKyO : M ≤ Ky p K x' ⊔ O := by
    by_contra hne
    have hW_ne : (M ⊓ (Ky p K x' ⊔ O)).subgroupOf M ≠ ⊤ := by
      intro htop
      apply hne
      intro m' hm'
      have hmem : (⟨m', hm'⟩ : ↥M) ∈ (M ⊓ (Ky p K x' ⊔ O)).subgroupOf M := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
    have hcen := le_center_of_normal_of_isQuasisimple hMq hWnormal hW_ne
    have hPW : P ≤ M ⊓ (Ky p K x' ⊔ O) := le_inf hPM (hPKy.trans le_sup_left)
    have hmem : ∀ (a : G) (ha : a ∈ P), (⟨a, hPM ha⟩ : ↥M) ∈ Subgroup.center ↥M := fun a ha =>
      hcen (Subgroup.mem_subgroupOf.2 (hPW ha))
    have hPcomm : (⁅P, P⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := Subgroup.mem_center_iff.1 (hmem a ha) ⟨b, hPM hb⟩
      exact congrArg Subtype.val this
    have hPbot : P = ⊥ := by rw [← glaPComponent_perfect hP, hPcomm]
    exact glaPComponent_ne_bot' hP hPbot
  rw [hKyeq] at hMKyO
  apply hnc
  refine ⟨hxM, ?_⟩
  rw [Subgroup.commutator_le]
  intro m' hm' g hg
  have hgM : g ∈ Subgroup.normalizer (M : Set G) := (Subgroup.zpowers_le.2 hxM) hg
  have hmem1 : ⁅m', g⁆ ∈ M := by
    have e : ⁅m', g⁆ = m' * (g * m'⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact M.mul_mem hm' ((Subgroup.mem_normalizer_iff.1 hgM m'⁻¹).1 (M.inv_mem hm'))
  have hxcx : x ∈ cx x' := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.elem h.xD hx'D)
  have hgcx : g ∈ cx x' := (Subgroup.zpowers_le.2 hxcx) hg
  have hL'cx : L' ≤ cx x' := hL'.1
  have hOL' : GLAPPrimeCoreOf p L' ≤ O := glaPPrimeCoreOf_le_of_isSubnormal hp hL'.2.1
  have hL'O : L' ≤ Subgroup.normalizer (O : Set G) := hL'cx.trans (le_normalizer_glaPPrimeCoreOf p (cx x'))
  have hmem2 : ⁅m', g⁆ ∈ O := by
    have hm'' : m' ∈ L' ⊔ O := hMKyO hm'
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L' O hL'O] at hm''
    obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp hm''
    have e : ⁅l * o, g⁆ = l * ⁅o, g⁆ * l⁻¹ * ⁅l, g⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    have hgO : g ∈ Subgroup.normalizer (O : Set G) := (le_normalizer_glaPPrimeCoreOf p (cx x')) hgcx
    have hog : ⁅o, g⁆ ∈ O := by
      have e2 : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
      rw [e2]
      exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.1 hgO o⁻¹).1 (O.inv_mem ho))
    have hlog : l * ⁅o, g⁆ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hL'O hl) _).1 hog
    have hlg : ⁅l, g⁆ ∈ O := hOL' (hcent.2 (Subgroup.commutator_mem_commutator hl hg))
    exact O.mul_mem hlog hlg
  exact inf_primeCore_le hp hMcx ⟨hmem1, hmem2⟩

end S12

end CFSG.LocalAnalysis.GLTheoremA
