module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInnerInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2LongRoot
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Unipotent
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley.G2FieldFour CFSG.LieType.Chevalley.RootOps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement Pointwise

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem le_commutator_of_map_subtype {M : Type*} [Group M] {H : Subgroup M} {Z : Subgroup H}
    (h : Z.map H.subtype ≤ ⁅Z.map H.subtype, Z.map H.subtype⁆) : Z ≤ ⁅Z, Z⁆ := by
  rwa [← Subgroup.map_commutator, Subgroup.map_le_map_iff_of_injective H.subtype_injective] at h

theorem commutator_eq_of_le {M : Type*} [Group M] {H : Subgroup M} (h : H ≤ ⁅H, H⁆) :
    ⁅H, H⁆ = H :=
  le_antisymm (Subgroup.commutator_le.2 fun _ ha _ hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) h

theorem conj_mem_commutator {M : Type*} [Group M] {H : Subgroup M} {n w : M} (hn : n ∈ H)
    (hw : w ∈ ⁅H, H⁆) : n * w * n⁻¹ ∈ ⁅H, H⁆ := by
  have hwH : w ∈ H := Subgroup.commutator_le_self H hw
  have h := mul_mem (Subgroup.commutator_mem_commutator hn hwH) hw
  rwa [commutatorElement_def, inv_mul_cancel_right] at h

theorem map_subtype_centralizer {M : Type*} [Group M] (H : Subgroup M) (x : H) :
    (Subgroup.centralizer {x}).map H.subtype = H ⊓ Subgroup.centralizer {(x : M)} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
    simpa using this
  · rintro ⟨hg, hgx⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
    simpa using Subgroup.mem_centralizer_singleton_iff.1 hgx

theorem commutator_subgroupOf_eq {M : Type*} [Group M] {H M' : Subgroup M} (hle : H ≤ M')
    (h : ⁅H, H⁆ = H) : ⁅H.subgroupOf M', H.subgroupOf M'⁆ = H.subgroupOf M' := by
  refine commutator_eq_of_le (le_commutator_of_map_subtype ?_)
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle, h]

theorem pinnedX_mem_commutator
    {S : Subgroup (ModGL .G2 K)} {α : Fin Tag.G2.rank → ℤ}
    {g : ModGL .G2 K} {e : K} (he : e ≠ 1) (hg : ∀ c, g * X α c * g⁻¹ = X α (e * c))
    (hgS : g ∈ S) (hS : ∀ c, X α c ∈ S) (c : K) : X α c ∈ ⁅S, S⁆ := by
  have he' : e - 1 ≠ 0 := sub_ne_zero.2 he
  have key : ⁅g, X α ((e - 1)⁻¹ * c)⁆ = X α c := by
    rw [commutatorElement_def, hg, pinnedX_neg, ← pinnedX_add]
    congr 1
    field_simp
    ring
  rw [← key]
  exact Subgroup.commutator_mem_commutator hgS (hS _)

theorem torus_conj_pow
    (i : Fin Tag.G2.rank) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (t : Kˣ) {m : ℤ} (hm : ∑ j, Tag.G2.cartan i j * α j = m) (c : K) :
    torusElt .G2 K i t * X α c * (torusElt .G2 K i t)⁻¹ = X α (((t ^ m : Kˣ) : K) * c) := by
  rw [root_torus_conjugation i hα t c, hm]

section CharTwo

variable [CharP K 2]

omit [CharP K 2] in
theorem sq_add_self_add_one (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hpow : (Units.mk0 ω h0) ^ 3 = 1 := by rw [← h3]; exact pow_card_eq_one'
  have hpow' : ω ^ 3 = 1 := by
    have := congrArg Units.val hpow
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hpow'
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)

omit [CharP K 2] in
theorem eq_or_eq_sq_of_sq_add {ω d : K} (hω : ω ^ 2 + ω + 1 = 0) (hd : d ^ 2 + d + 1 = 0) :
    d = ω ∨ d = ω ^ 2 := by
  have h : (d - ω) * (d - ω ^ 2) = 0 := by
    linear_combination hd + (ω - 1 - d) * hω
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem exists_unit_ne_one (hK : Nat.card K = 4) :
    ∃ ω : Kˣ, (ω : K) ≠ 1 ∧ (ω : K) ^ 2 ≠ 1 ∧ (ω : K) ^ 2 + (ω : K) + 1 = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units, hK]
    norm_num
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  have hω' : (ω : K) ≠ 1 := fun h => hω (Units.ext h)
  have hsq := sq_add_self_add_one hK ω.ne_zero hω'
  refine ⟨ω, hω', fun h => hω' ?_, hsq⟩
  have h' : ((ω : K) - 1) ^ 2 = 0 := by
    linear_combination h + (1 - (ω : K)) * (CharTwo.two_eq_zero (R := K))
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')

omit [CharP K 2] in
theorem ringEquiv_apply_eq_or (hK : Nat.card K = 4) (σ : K ≃+* K) (c : K) :
    σ c = c ∨ σ c = c ^ 2 := by
  by_cases h0 : c = 0
  · subst h0; simp
  by_cases h1 : c = 1
  · subst h1; simp
  have hc := sq_add_self_add_one hK h0 h1
  have hσ : σ c ^ 2 + σ c + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one σ, ← map_add, hc, map_zero]
  exact eq_or_eq_sq_of_sq_add hc hσ

omit [CharP K 2] in
theorem ringEquiv_mul_self (hK : Nat.card K = 4) (σ : K ≃+* K) : σ * σ = 1 := by
  refine RingEquiv.ext fun c => ?_
  change σ (σ c) = c
  by_cases h0 : c = 0
  · subst h0; simp
  by_cases h1 : c = 1
  · subst h1; simp
  have hc := sq_add_self_add_one hK h0 h1
  rcases ringEquiv_apply_eq_or hK σ c with h | h
  · rw [h, h]
  · rw [h, map_pow, h]
    linear_combination c * (c - 1) * hc

omit [CharP K 2] in
theorem ringEquiv_eq_sq (hK : Nat.card K = 4) {σ : K ≃+* K} (hσ : σ ≠ 1) (c : K) :
    σ c = c ^ 2 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, σ c₀ ≠ c₀ := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have h00 : c₀ ≠ 0 := fun h => hc₀ (by rw [h, map_zero])
  have h01 : c₀ ≠ 1 := fun h => hc₀ (by rw [h, map_one])
  have hc₀sq := sq_add_self_add_one hK h00 h01
  have hσc₀ : σ c₀ = c₀ ^ 2 := (ringEquiv_apply_eq_or hK σ c₀).resolve_left hc₀
  by_cases h0 : c = 0
  · subst h0; simp
  by_cases h1 : c = 1
  · subst h1; simp
  rcases eq_or_eq_sq_of_sq_add hc₀sq (sq_add_self_add_one hK h0 h1) with rfl | rfl
  · exact hσc₀
  · rw [map_pow, hσc₀]

omit [CharP K 2] in
theorem xUnit_inv
    (i : Fin Tag.G2.rank) (c : K) : (xUnit .G2 K i c)⁻¹ = xUnit .G2 K i (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [← xUnit_add, add_neg_cancel, xUnit_zero])

theorem commutator_rankOne
    (hK : Nat.card K = 4) (i : Fin Tag.G2.rank) :
    ⁅g2RankOne K i, g2RankOne K i⁆ = g2RankOne K i := by
  obtain ⟨ω, -, hω2, -⟩ := exists_unit_ne_one (K := K) hK
  have hx : ∀ c, xUnit .G2 K i c ∈ ⁅g2RankOne K i, g2RankOne K i⁆ := fun c => by
    have he : (ω : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hω2
    have key : ⁅torusElt .G2 K i ω, xUnit .G2 K i (((ω : K) ^ 2 - 1)⁻¹ * c)⁆ =
        xUnit .G2 K i c := by
      rw [commutatorElement_def, torusElt_mul_xUnit_mul_inv, xUnit_inv, ← xUnit_add]
      congr 1
      field_simp
      ring
    rw [← key]
    exact Subgroup.commutator_mem_commutator (torusElt_mem_g2RankOne i ω)
      (xUnit_mem_g2RankOne i _)
  refine commutator_eq_of_le ((Subgroup.closure_le _).2 ?_)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hx c
  · rw [SetLike.mem_coe, yUnit_eq_conj]
    exact conj_mem_commutator (weylElt_mem_g2RankOne i 1) (hx _)

theorem le_commutator_centralizer_c
    [Finite K] (hK : Nat.card K = 4) :
    adjointGroup .G2 K ⊓ Subgroup.centralizer {X g2c 1} ≤
      ⁅adjointGroup .G2 K ⊓ Subgroup.centralizer {X g2c 1},
        adjointGroup .G2 K ⊓ Subgroup.centralizer {X g2c 1}⁆ := by
  obtain ⟨-, -, -, hC, -⟩ := even_G2_highest_long_root_centralizer K
  set C := adjointGroup .G2 K ⊓ Subgroup.centralizer {X g2c 1} with hCdef
  obtain ⟨ω, hω1, -, -⟩ := exists_unit_ne_one (K := K) hK
  have hLr : g2RankOne K g2ir ≤ C := by rw [hC]; exact le_sup_right
  have hQ : g2LongRadical K ≤ C := by rw [hC]; exact le_sup_left
  have hLr' : g2RankOne K g2ir ≤ ⁅C, C⁆ := by
    rw [← commutator_rankOne hK g2ir]
    exact Subgroup.commutator_mono hLr hLr
  have hQmem : ∀ {d : Fin Tag.G2.rank → ℤ}, (∀ c, X d c ∈ g2LongRadical K) → ∀ c, X d c ∈ C :=
    fun h c => hQ (h c)
  have hu : ∀ c, X g2u c ∈ g2LongRadical K := fun c => by
    rw [pinnedX_u_eq_g2N]; exact g2N_mem_g2LongRadical _ _ _ _ _
  have hv : ∀ c, X g2v c ∈ g2LongRadical K := fun c => by
    rw [pinnedX_v_eq_g2N]; exact g2N_mem_g2LongRadical _ _ _ _ _
  have hr : ∀ c, X g2r c ∈ C := fun c => hLr (by
    rw [← xUnit_g2ir]; exact xUnit_mem_g2RankOne _ _)
  have hnr : ∀ c, X g2nr c ∈ C := fun c => hLr (by
    rw [← yUnit_g2ir]; exact yUnit_mem_g2RankOne _ _)
  have htor : torusElt .G2 K g2ir ω ∈ C := hLr (torusElt_mem_g2RankOne _ _)
  have huC : ∀ c, X g2u c ∈ ⁅C, C⁆ := by
    refine pinnedX_mem_commutator (g := torusElt .G2 K g2ir ω) (e := ((ω ^ (-1 : ℤ) : Kˣ) : K))
      ?_ (torus_conj_pow g2ir isRoot_g2u ω (m := -1) (by decide)) htor (hQmem hu)
    rw [zpow_neg_one, Units.val_inv_eq_inv_val]
    exact fun h => hω1 (inv_eq_one.1 h)
  have hvC : ∀ c, X g2v c ∈ ⁅C, C⁆ := by
    refine pinnedX_mem_commutator (g := torusElt .G2 K g2ir ω) (e := ((ω ^ (1 : ℤ) : Kˣ) : K))
      ?_ (torus_conj_pow g2ir isRoot_g2v ω (m := 1) (by decide)) htor (hQmem hv)
    rwa [zpow_one]
  have hbC : ∀ c, X g2b c ∈ ⁅C, C⁆ := fun c => by
    have h := comm_r_v (K := K) 1 c
    rw [one_mul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (hr 1) (hQmem hv c)
  have hcC : ∀ c, X g2c c ∈ ⁅C, C⁆ := fun c => by
    have h := comm_u_v (K := K) 1 c
    rw [one_mul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (hQmem hu 1) (hQmem hv c)
  have haC : ∀ c, X g2a c ∈ ⁅C, C⁆ := fun c => by
    have h := comm_v_nr (K := K) c 1
    rw [one_pow, mul_one, mul_one] at h
    have h' : X g2a c = ⁅X g2v c, X g2nr 1⁆ * (X g2c (c ^ 2))⁻¹ := by
      rw [h, mul_inv_cancel_right]
    rw [h']
    exact mul_mem (Subgroup.commutator_mem_commutator (hQmem hv c) (hnr 1)) (inv_mem (hcC _))
  refine hC.le.trans (sup_le ?_ hLr')
  rintro _ ⟨B, C', D, E, F, rfl⟩
  simp only [g2N, pinnedX_zero, one_mul]
  exact mul_mem (mul_mem (mul_mem (mul_mem (haC B) (huC C')) (hvC D)) (hbC E)) (hcC F)

theorem commutator_centralizer_rootX_c
    [Finite K] (hK : Nat.card K = 4) :
    ⁅Subgroup.centralizer {rootX rootC (1 : K)}, Subgroup.centralizer {rootX rootC (1 : K)}⁆ =
      Subgroup.centralizer {rootX rootC (1 : K)} := by
  refine commutator_eq_of_le (le_commutator_of_map_subtype ?_)
  rw [map_subtype_centralizer]
  exact le_commutator_centralizer_c hK

theorem rootX_v_mem_centralizer_c :
    rootX rootV (1 : K) ∈ Subgroup.centralizer {rootX rootC (1 : K)} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_rootX_vc (K := K) 1 1).eq

theorem posU_le_centralizer_c
    : posU K ≤ Subgroup.centralizer {rootX rootC (1 : K)} := by
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (commute_pinnedX_c_of_mem_posUnipotent 1
    (Subgroup.mem_subgroupOf.1 hu)).eq.symm

abbrev rankOneA
    (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  (g2RankOne K g2ia).subgroupOf (adjointGroup .G2 K)

theorem commutator_rankOneA
    (hK : Nat.card K = 4) :
    ⁅rankOneA K, rankOneA K⁆ = rankOneA K :=
  commutator_subgroupOf_eq (g2RankOne_le_adjointGroup g2ia) (commutator_rankOne hK g2ia)

theorem rankOneA_le_centralizer
    [Finite K] :
    rankOneA K ≤ Subgroup.centralizer {rootX rootV (1 : K)} := by
  obtain ⟨-, -, -, -, -, -, -, -, hcomm, -⟩ := even_G2_highest_short_root_centralizer K
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 hl) 1).eq

theorem eq_one_of_commute_uSL_vSL {M : SL2 K} (hu : M * uSL 1 = uSL 1 * M)
    (hv : M * vSL 1 = vSL 1 * M) : M = 1 := by
  have hu' := congrArg (fun N : SL2 K => (N : Matrix (Fin 2) (Fin 2) K)) hu
  have hv' := congrArg (fun N : SL2 K => (N : Matrix (Fin 2) (Fin 2) K)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hu' hv'
  have e00 := congrFun (congrFun hu' 0) 0
  have e01 := congrFun (congrFun hu' 0) 1
  have f00 := congrFun (congrFun hv' 0) 0
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 f00
  have hr : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    linear_combination e00
  have hq : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    linear_combination f00
  have hps : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    linear_combination e01
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  have hp : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h2 : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (M : Matrix (Fin 2) (Fin 2) K) 0 0 * hps +
        (M : Matrix (Fin 2) (Fin 2) K) 0 1 * hr +
        (1 - (M : Matrix (Fin 2) (Fin 2) K) 0 0) * (CharTwo.two_eq_zero (R := K))
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hs : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := hps ▸ hp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]

omit [CharP K 2] in
theorem entrywise_mem_g2RankOne_a
    (σ : K ≃+* K) {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia) :
    Units.map (entrywiseHom σ.toRingHom) l ∈ g2RankOne K g2ia := by
  rw [g2RankOne_a_eq] at hl ⊢
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [units_map_entrywise_pinnedX]; exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [units_map_entrywise_pinnedX]; exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem mul_self_eq_one_of_fix
    (hK : Nat.card K = 4) {α : MulAut (adjointGroup .G2 K)}
    (hv : α (rootX rootV 1) = rootX rootV 1) (hL : ∀ l ∈ rankOneA K, α l = l) : α * α = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [hK]; norm_num)).1 α
  simp only at hgσ
  obtain ⟨-, -, hA, -, hset, hnorm, hinf, ⟨ρ, hρu, hρv, hρr, hρi⟩, -, -⟩ :=
    even_G2_highest_short_root_centralizer K
  have hgv : (g : ModGL .G2 K) ∈ adjointGroup .G2 K ⊓ Subgroup.centralizer {X g2v 1} := by
    refine ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := congrArg Subtype.val hv
    rw [hgσ, coe_rootX] at h
    change (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (X g2v 1) *
      (g : ModGL .G2 K)⁻¹ = X g2v 1 at h
    rw [units_map_entrywise_pinnedX, map_one] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hgv' : (g : ModGL .G2 K) ∈ ((g2ShortRadical K : Set (ModGL .G2 K)) *
      (g2RankOne K g2ia : Set (ModGL .G2 K))) := by
    rw [← hset]; exact hgv
  obtain ⟨m, hm, l₀, hl₀, hml₀⟩ := hgv'
  have hfix : ∀ l ∈ g2RankOne K g2ia, (g : ModGL .G2 K) *
      Units.map (entrywiseHom σ.toRingHom) l * (g : ModGL .G2 K)⁻¹ = l := fun l hl => by
    have h := congrArg Subtype.val (hL ⟨l, g2RankOne_le_adjointGroup g2ia hl⟩
      (Subgroup.mem_subgroupOf.2 hl))
    rw [hgσ] at h
    exact h
  have hfix' : ∀ l ∈ g2RankOne K g2ia,
      l₀ * Units.map (entrywiseHom σ.toRingHom) l * l₀⁻¹ = l := fun l hl => by
    set w := l₀ * Units.map (entrywiseHom σ.toRingHom) l * l₀⁻¹ with hw
    have hwL : w ∈ g2RankOne K g2ia :=
      mul_mem (mul_mem hl₀ (entrywise_mem_g2RankOne_a σ hl)) (inv_mem hl₀)
    have hmw : m * w * m⁻¹ = l := by
      rw [← hfix l hl, ← hml₀, hw]
      group
    have hA' : w * l⁻¹ ∈ g2ShortRadical K := by
      have h1 : l * m * l⁻¹ ∈ g2ShortRadical K :=
        (Subgroup.mem_normalizer_iff.1 (hnorm hl) m).1 hm
      have h2 : w * l⁻¹ = m⁻¹ * (l * m * l⁻¹) := by
        rw [← hmw]; group
      rw [h2]
      exact mul_mem (inv_mem hm) h1
    have hL' : w * l⁻¹ ∈ g2RankOne K g2ia := mul_mem hwL (inv_mem hl)
    have h0 : w * l⁻¹ ∈ g2ShortRadical K ⊓ g2RankOne K g2ia := ⟨hA', hL'⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h0
    exact h0
  have hxa : X g2a 1 ∈ g2RankOne K g2ia := by
    rw [← xUnit_g2ia]; exact xUnit_mem_g2RankOne _ _
  have hxna : X g2na 1 ∈ g2RankOne K g2ia := by
    rw [← yUnit_g2ia]; exact yUnit_mem_g2RankOne _ _
  have hl₀1 : l₀ = 1 := by
    obtain ⟨M, rfl⟩ : l₀ ∈ ρ.range := hρr ▸ hl₀
    have hcomm : ∀ N : SL2 K, ρ N ∈ g2RankOne K g2ia →
        Units.map (entrywiseHom σ.toRingHom) (ρ N) = ρ N →
          ρ (M * N) = ρ (N * M) := fun N hN hNσ => by
      have h := hfix' (ρ N) hN
      rw [hNσ] at h
      rw [map_mul, map_mul]
      exact mul_inv_eq_iff_eq_mul.1 h
    have hu1 := hcomm (uSL 1) (by rw [hρu, ← xUnit_g2ia]; exact xUnit_mem_g2RankOne _ _)
      (by rw [hρu, units_map_entrywise_pinnedX, map_one])
    have hv1 := hcomm (vSL 1) (by rw [hρv, ← yUnit_g2ia]; exact yUnit_mem_g2RankOne _ _)
      (by rw [hρv, units_map_entrywise_pinnedX, map_one])
    rw [eq_one_of_commute_uSL_vSL (hρi hu1) (hρi hv1), map_one]
  subst hl₀1
  change m * 1 = (g : ModGL .G2 K) at hml₀
  rw [mul_one] at hml₀
  have hσ : σ = 1 := by
    by_contra hσ
    obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
      by_contra h
      push Not at h
      exact hσ (RingEquiv.ext h)
    have h := hfix' (X g2a c) (by rw [← xUnit_g2ia]; exact xUnit_mem_g2RankOne _ _)
    rw [one_mul, inv_one, mul_one, units_map_entrywise_pinnedX] at h
    exact hc (pinnedX_injective .G2 K _ h)
  subst hσ
  have hm2 : m * m = 1 := by
    obtain ⟨D, E, F, rfl⟩ := hm
    rw [g2N_mul_self, ← g2N_zero]
    refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_ <;> ring
  refine MulEquiv.ext fun h => Subtype.ext ?_
  change ((α (α h) : adjointGroup .G2 K) : ModGL .G2 K) = h
  rw [hgσ, hgσ]
  change (g : ModGL .G2 K) * Units.map (entrywiseHom (RingEquiv.refl K).toRingHom)
    ((g : ModGL .G2 K) * Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (h : ModGL .G2 K) *
      (g : ModGL .G2 K)⁻¹) * (g : ModGL .G2 K)⁻¹ = h
  rw [units_map_entrywise_refl, units_map_entrywise_refl, ← hml₀]
  calc m * (m * (h : ModGL .G2 K) * m⁻¹) * m⁻¹ = (m * m) * h * (m * m)⁻¹ := by group
    _ = h := by rw [hm2, one_mul, inv_one, mul_one]

variable (K) in
@[expose] def longF2
    : Subgroup (ModGL .G2 K) :=
  Subgroup.closure {g | ∃ γ ∈ g2LongRoots, g = X γ 1}

omit [CharP K 2] in
theorem pinnedX_mem_longF2
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ g2LongRoots) :
    X γ 1 ∈ longF2 K :=
  Subgroup.subset_closure ⟨γ, hγ, rfl⟩

omit [CharP K 2] in
theorem longF2_le_adjointGroup
    : longF2 K ≤ adjointGroup .G2 K :=
  (Subgroup.closure_le _).2 fun _ ⟨γ, _, h⟩ => h ▸ pinnedX_mem_adjointGroup γ 1

omit [CharP K 2] in
theorem entrywise_eq_of_mem_longF2
    (σ : K ≃+* K) {g : ModGL .G2 K} (hg : g ∈ longF2 K) :
    Units.map (entrywiseHom σ.toRingHom) g = g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, -, rfl⟩ := hx
    rw [units_map_entrywise_pinnedX, map_one]
  | one => rw [map_one]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

theorem g2a_mem_g2LongRoots : g2a ∈ g2LongRoots := Or.inl rfl

theorem g2b_mem_g2LongRoots : g2b ∈ g2LongRoots := Or.inr (Or.inl rfl)

theorem pinnedX_mem_commutator_longF2
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ g2LongRoots) :
    X γ 1 ∈ ⁅longF2 K, longF2 K⁆ := by
  obtain ⟨w, hw, hwa, hwb⟩ := exists_smul_long hγ
  have hr7 : IsRoot .G2 (orbitCertRoot .G2 7) := isRoot_decodeVec_witness (by decide)
  have hr10 : IsRoot .G2 (orbitCertRoot .G2 10) := isRoot_decodeVec_witness (by decide)
  have hr11 : IsRoot .G2 (orbitCertRoot .G2 11) := isRoot_decodeVec_witness (by decide)
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr7
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr10
  obtain ⟨ε₃, hε₃, h₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr11
  rw [eq_one_of_mul_self_eq_one_two hε₁] at h₁
  rw [eq_one_of_mul_self_eq_one_two hε₂] at h₂
  rw [eq_one_of_mul_self_eq_one_two hε₃] at h₃
  set n := canonicalRep (coxeterSystem .G2) K w
  have hid := congrArg (fun y => n * y * n⁻¹) (g2_pinnedX_commutator_long (K := K) 1 1)
  have e : ∀ a₁ a₂ a₃ a₄ : ModGL .G2 K, n * (a₁ * a₂ * a₃ * a₄) * n⁻¹ =
      (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) * (n * a₃ * n⁻¹) * (n * a₄ * n⁻¹) := fun _ _ _ _ => by
    group
  rw [e, h₁, h₁, h₂, h₂, h₃, hw] at hid
  simp only [one_mul, mul_one] at hid
  rw [← pinnedX_neg, ← pinnedX_neg, ← commutatorElement_def] at hid
  rw [← hid]
  exact Subgroup.commutator_mem_commutator (pinnedX_mem_longF2 hwa) (pinnedX_mem_longF2 hwb)

theorem commutator_longF2 :
    ⁅longF2 K, longF2 K⁆ = longF2 K :=
  commutator_eq_of_le ((Subgroup.closure_le _).2 fun _ ⟨_, hγ, h⟩ =>
    h ▸ pinnedX_mem_commutator_longF2 hγ)

omit [CharP K 2] in
theorem mul_self_mem_inner
    (hK : Nat.card K = 4) (α : MulAut (adjointGroup .G2 K)) :
    α * α ∈ inner (adjointGroup .G2 K) := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [hK]; norm_num)
  have h : α * α ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact ringEquiv_mul_self hK _
  rw [hker] at h
  exact h

omit [CharP K 2] in
theorem exists_conj_eq_frobenius
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2)
    {α : MulAut (adjointGroup .G2 K)} (hα : orderOf α = 2)
    (hout : α ∉ inner (adjointGroup .G2 K)) :
    ∃ x : adjointGroup .G2 K, ∀ h : adjointGroup .G2 K,
      ((MulAut.conj x * α * (MulAut.conj x)⁻¹) h : ModGL .G2 K) =
        Units.map (entrywiseHom δ) (h : ModGL .G2 K) := by
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ := even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [hK]; norm_num)
  rcases even_G2_involution_inner_or_canonical_field (f := 2) le_rfl K (by rw [hK]; norm_num) α
    hα with h | ⟨-, h⟩
  · exact absurd h hout
  obtain ⟨β, ψ, hβ, hψ, -⟩ := h δ (fun c => by rw [hδ]; norm_num)
  have key : ∃ ψ' : MulAut (adjointGroup .G2 K), ψ' ∈ inner (adjointGroup .G2 K) ∧
      ψ' * α * ψ'⁻¹ = β := by
    by_cases hψ1 : Θ ψ = 1
    · exact ⟨ψ, by rw [← MonoidHom.mem_ker, hker] at hψ1; exact hψ1, hψ⟩
    · have hΘψ : ∀ c, Θ ψ c = c ^ 2 := ringEquiv_eq_sq hK hψ1
      have hδ' : δ = (Θ ψ).toRingHom :=
        RingHom.ext fun c => by rw [hδ]; exact (hΘψ c).symm
      have hΘβ : Θ β = Θ ψ := by
        refine hΘ β 1 (Θ ψ) fun h => ?_
        rw [hβ, Subgroup.coe_one, one_mul, inv_one, mul_one, hδ']
      refine ⟨β⁻¹ * ψ, ?_, ?_⟩
      · show β⁻¹ * ψ ∈ (MulAut.conj : adjointGroup .G2 K →* _).range
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΘβ, inv_mul_cancel]
      · calc β⁻¹ * ψ * α * (β⁻¹ * ψ)⁻¹ = β⁻¹ * (ψ * α * ψ⁻¹) * β := by group
          _ = β := by rw [hψ]; group
  obtain ⟨ψ', hψ'in, hψ'⟩ := key
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hψ'in
  exact ⟨x, fun h => by rw [hψ', hβ]⟩

end CharTwo

end CFSG.EvenSmallLie.GTwoFour
