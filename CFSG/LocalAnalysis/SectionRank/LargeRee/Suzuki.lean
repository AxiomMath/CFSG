module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneB2
public import CFSG.LocalAnalysis.SectionRank.LargeRee.LeviCentralizer
public import CFSG.Blueprint.CatalogGenerators
public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneData

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section Commute

theorem mem_centralizer_singleton_of_conj {G : Type*} [Group G] {s x : G}
    (h : s * x * s⁻¹ = x) : x ∈ Subgroup.centralizer {s} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * s = s * x * s⁻¹ * s := by rw [h]
    _ = s * x := by group

theorem conj_eq_of_mem_centralizer_singleton {G : Type*} [Group G] {s x : G}
    (h : x ∈ Subgroup.centralizer {s}) : s * x * s⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  rw [← h]
  group

variable {K : Type} [Field K] [Finite K]

theorem commute_evalV
    {s : adjointGroup ReeTag.F4.tag K} (hs : s ∈ (nativeData ReeTag.F4.tag K).H)
    (h1 : simpleChar s (fi 1) = 1) (h2 : simpleChar s (fi 2) = 1) (w : List (VLetter K)) :
    evalV w ∈ Subgroup.centralizer {s} := by
  have hx : ∀ i, simpleChar s i = 1 → ∀ c, xElement i c ∈ Subgroup.centralizer {s} := by
    intro i hi c
    have := conj_xElement_of_mem_H hs i c
    rw [hi, one_mul] at this
    exact mem_centralizer_singleton_of_conj this
  have hy : ∀ i, simpleChar s i = 1 → ∀ c, yElement i c ∈ Subgroup.centralizer {s} := by
    intro i hi c
    have := conj_yElement_of_mem_H hs i c
    rw [hi, inv_one, one_mul] at this
    exact mem_centralizer_singleton_of_conj this
  have hn : ∀ i, simpleChar s i = 1 → weylElement ReeTag.F4.tag K i ∈ Subgroup.centralizer {s} :=
    fun i hi => by
      rw [weylElement_eq_mul]
      exact mul_mem (mul_mem (hx i hi 1) (hy i hi (-1))) (hx i hi 1)
  induction w with
  | nil => exact one_mem _
  | cons l w ih =>
    rw [evalV, List.map_cons, List.prod_cons]
    refine mul_mem ?_ ih
    cases l with
    | x1 c => exact hx _ h1 c
    | x2 c => exact hx _ h2 c
    | n1 => exact hn _ h1
    | n2 => exact hn _ h2
    | n1i => exact inv_mem (hn _ h1)
    | n2i => exact inv_mem (hn _ h2)

end Commute

section R2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem coe_blockGen_one :
    (blockGen 1 : WeylGroup ReeTag.F4.tag) = ReeTag.F4.blockElt (fi 1) :=
  rfl

theorem coe_relNrepHom_blockGen_one :
    (relNrepHom K a (blockGen 1) : adjointGroup ReeTag.F4.tag K) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) :=
  rfl

theorem mem_blockX_one
    {x : reeFixed ReeTag.F4 K a} :
    x ∈ blockX (K := K) a 1 ↔
      (x : adjointGroup ReeTag.F4.tag K) ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) :=
  Iff.rfl

theorem blockT_one
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    blockT a hK 1 = reeTorusSub a hK fi_one_mem_longSet :=
  rfl

variable (K a) in
@[expose] noncomputable def r2
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    Subgroup (reeFixed ReeTag.F4 K a) :=
  Subgroup.closure ((blockX (K := K) a 1 : Set (reeFixed ReeTag.F4 K a)) ∪
    (blockT a hK 1 : Set (reeFixed ReeTag.F4 K a)) ∪ {relNrepHom K a (blockGen 1)})

variable (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))

theorem blockX_le_r2
    : blockX (K := K) a 1 ≤ r2 K a hK :=
  fun _ hx => Subgroup.subset_closure (.inl (.inl hx))

theorem blockT_le_r2
    : blockT a hK 1 ≤ r2 K a hK :=
  fun _ ht => Subgroup.subset_closure (.inl (.inr ht))

theorem relNrepHom_mem_r2
    : relNrepHom K a (blockGen 1) ∈ r2 K a hK :=
  Subgroup.subset_closure (.inr rfl)

theorem r2_le
    {P : Subgroup (reeFixed ReeTag.F4 K a)}
    (hX : ∀ x : reeFixed ReeTag.F4 K a,
      (x : adjointGroup ReeTag.F4.tag K) ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) →
        x ∈ P)
    (hT : ∀ u : Kˣ, reeTorusHom a hK fi_one_mem_longSet u ∈ P)
    (hn : relNrepHom K a (blockGen 1) ∈ P) : r2 K a hK ≤ P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ((hx | ⟨u, rfl⟩) | rfl)
  · exact hX x hx
  · exact hT u
  · exact hn

theorem mem_vStab_of_mem_r2
    {g : reeFixed ReeTag.F4 K a} (hg : g ∈ r2 K a hK) :
    (g : adjointGroup ReeTag.F4.tag K) ∈ vStab K := by
  refine r2_le hK (P := (vStab K).comap (reeFixed ReeTag.F4 K a).subtype) (fun x hx => ?_)
    (fun u => mem_vStab_of_mem_H (ReeTag.F4.reeTorus_mem_H a _ u))
    nrep_blockElt_one_mem_vStab hg
  obtain ⟨c₁, c₂, c₃, c₄, hc⟩ := exists_eq_nfU hx
  change (x : adjointGroup ReeTag.F4.tag K) ∈ vStab K
  rw [hc]
  exact nfU_mem_vStab _ _ _ _

theorem mem_closure_of_mem_r2
    {g : reeFixed ReeTag.F4 K a} (hg : g ∈ r2 K a hK) :
    (g : adjointGroup ReeTag.F4.tag K) ∈ Subgroup.closure
      (((nativeData ReeTag.F4.tag K).B : Set (adjointGroup ReeTag.F4.tag K)) ∪
        weylElement ReeTag.F4.tag K '' {fi 1, ReeTag.F4.perm (fi 1)}) := by
  refine r2_le hK (P := (Subgroup.closure
      (((nativeData ReeTag.F4.tag K).B : Set (adjointGroup ReeTag.F4.tag K)) ∪
        weylElement ReeTag.F4.tag K '' {fi 1, ReeTag.F4.perm (fi 1)})).comap
      (reeFixed ReeTag.F4 K a).subtype) (fun x hx => ?_) (fun u => ?_)
    (nrep_blockElt_mem_closure ReeTag.F4 K (fi 1)) hg
  · exact Subgroup.subset_closure (.inl ((nativeData ReeTag.F4.tag K).U_le_B
      (Uminus_le_U ReeTag.F4.tag K _ hx)))
  · exact Subgroup.subset_closure (.inl ((nativeData ReeTag.F4.tag K).H_le_B
      (ReeTag.F4.reeTorus_mem_H a _ u)))

theorem mem_centralizer_of_mem_r2
    {s : adjointGroup ReeTag.F4.tag K}
    (hs : s ∈ (nativeData ReeTag.F4.tag K).H) (h1 : simpleChar s (fi 1) = 1)
    (h2 : simpleChar s (fi 2) = 1) {g : reeFixed ReeTag.F4 K a} (hg : g ∈ r2 K a hK) :
    (g : adjointGroup ReeTag.F4.tag K) ∈ Subgroup.centralizer {s} := by
  refine r2_le hK (P := (Subgroup.centralizer {s}).comap (reeFixed ReeTag.F4 K a).subtype)
    (fun x hx => ?_) (fun u => ?_) ?_ hg
  · obtain ⟨c₁, c₂, c₃, c₄, hc⟩ := exists_eq_nfU hx
    change (x : adjointGroup ReeTag.F4.tag K) ∈ Subgroup.centralizer {s}
    rw [hc, nfU_eq_evalV]
    exact commute_evalV hs h1 h2 _
  · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_H hs (ReeTag.F4.reeTorus_mem_H a _ u)).eq.symm
  · change nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) ∈ Subgroup.centralizer {s}
    rw [nrep_blockElt_one_eq]
    exact commute_evalV hs h1 h2 _

variable (K a) in
@[expose] noncomputable def r2Rep :
    r2 K a hK →* GL (Fin 4) K :=
  (blockRep vLabel vLabel_injective).comp
    (((reeFixed ReeTag.F4 K a).subtype.comp (r2 K a hK).subtype).codRestrict (vStab K)
      fun g => mem_vStab_of_mem_r2 hK g.2)

theorem coe_r2Rep
    (g : r2 K a hK) :
    ((r2Rep K a hK g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      vMat ((g : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) :=
  rfl

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem det_suzukiW
    [CharP K 2] : (CFSG.Blueprint.suzukiW K).det = 1 := by
  have h := congrArg Matrix.det (CFSG.Blueprint.suzukiW_mul_self K)
  rw [Matrix.det_mul, Matrix.det_one, ← sq] at h
  have h2 : ((CFSG.Blueprint.suzukiW K).det - 1) ^ 2 = 0 := by
    linear_combination h + (1 - (CFSG.Blueprint.suzukiW K).det) * CharTwo.two_eq_zero (R := K)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem det_eq_one_of_mem_suzukiGroup [CharP K 2] {g : GL (Fin 4) K}
    (hg : g ∈ CFSG.Blueprint.suzukiGroup a K) : (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have hle : CFSG.Blueprint.suzukiGroup a K ≤ (Matrix.GeneralLinearGroup.det :
      GL (Fin 4) K →* Kˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (⟨u, v, hg⟩ | ⟨l, hg⟩ | hg) <;> rw [SetLike.mem_coe, MonoidHom.mem_ker] <;>
      refine Units.ext ?_ <;> rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
    · exact CFSG.Blueprint.det_suzukiS a u v
    · exact CFSG.Blueprint.det_suzukiD a l
    · exact det_suzukiW
  have := congrArg Units.val (MonoidHom.mem_ker.1 (hle hg))
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem r2Rep_mem_suzukiGroup
    (g : r2 K a hK) :
    r2Rep K a hK g ∈ CFSG.Blueprint.suzukiGroup a K := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with (hx | ⟨u, rfl⟩) | rfl
    · obtain ⟨u, v, huv⟩ := exists_vMat_eq_suzukiS hx ((mem_reeFixed ReeTag.F4 K a).1 x.2)
      exact Subgroup.subset_closure (.inl ⟨u, v, huv⟩)
    · exact Subgroup.subset_closure (.inr (.inl ⟨_, vMat_reeTorus_one hK u⟩))
    · have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
      exact Subgroup.subset_closure (.inr (.inr vMat_nrep_blockElt_one))
  | one =>
    have e : (⟨1, one_mem _⟩ : r2 K a hK) = 1 := rfl
    rw [e, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, mul_mem hx hy⟩ : r2 K a hK) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ih =>
    have e : (⟨x⁻¹, inv_mem hx⟩ : r2 K a hK) = ⟨x, hx⟩⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem ih

theorem det_vMat_of_mem_r2
    {g : reeFixed ReeTag.F4 K a} (hg : g ∈ r2 K a hK) :
    (vMat (g : adjointGroup ReeTag.F4.tag K)).det = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact det_eq_one_of_mem_suzukiGroup (r2Rep_mem_suzukiGroup hK ⟨g, hg⟩)

include hK in
omit [CharP K ReeTag.F4.prime] in
theorem eq_one_of_zpow_four_mul_sub_two {b : Kˣ} (hb : b ^ (4 * (2 ^ a : ℤ) - 2) = 1) :
    b = 1 := by
  have hq : (Nat.card K : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 := by
    rw [hK, ← natCast_prime_pow]
    exact two_pow_eq_two_mul_sq a
  have h := units_zpow_one_add_mul b (4 * (2 ^ a : ℤ) ^ 2 + 1)
  rw [show 1 + (4 * (2 ^ a : ℤ) ^ 2 + 1) * ((Nat.card K : ℤ) - 1) =
      (4 * (2 ^ a : ℤ) - 2) * ((2 * 2 ^ a + 1) * (2 ^ a) ^ 2) by rw [hq]; ring, zpow_mul, hb,
    one_zpow] at h
  exact h.symm

include hK in
omit [CharP K ReeTag.F4.prime] in
theorem eq_one_of_zpow_one_sub_two_mul {b : Kˣ} (hb : b ^ (1 - 2 * (2 ^ a : ℤ)) = 1) :
    b = 1 := by
  have hq : (Nat.card K : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 := by
    rw [hK, ← natCast_prime_pow]
    exact two_pow_eq_two_mul_sq a
  have h := units_zpow_one_add_mul b 2
  rw [show 1 + 2 * ((Nat.card K : ℤ) - 1) = (1 - 2 * (2 ^ a : ℤ)) * (-1 - 2 * 2 ^ a) by
    rw [hq]; ring, zpow_mul, hb, one_zpow] at h
  exact h.symm

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem suzukiS_zero_zero : CFSG.Blueprint.suzukiS a (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.Blueprint.suzukiS, CFSG.Blueprint.suzukiN]

omit [CharP K ReeTag.F4.prime] in
theorem vMat_zero_three_eq_zero
    {b : adjointGroup ReeTag.F4.tag K}
    (hb : b ∈ (nativeData ReeTag.F4.tag K).B) : vMat b 0 3 = 0 := by
  by_contra h
  have := height_le_of_mem_B hb (a := vLabel 0) (b := vLabel 3) h
  change height (τ := ReeTag.F4.tag) (vRoot 3) ≤ height (τ := ReeTag.F4.tag) (vRoot 0) at this
  revert this
  decide +kernel

end R2

section Cells

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (ha : 1 ≤ a)

include hK ha in
theorem exists_unit_ne_one_sq_ne_one : ∃ t : Kˣ, t ≠ 1 ∧ t ^ 2 ≠ 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hcard : 1 < Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    change 1 < 2 ^ (2 * a + 1) - 1
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (1 : Kˣ)
  refine ⟨t, ht, fun h2 => ht ?_⟩
  have h : ((t : K) - 1) ^ 2 = 0 := by
    have := congrArg Units.val h2
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    linear_combination this + (1 - (t : K)) * CharTwo.two_eq_zero (R := K)
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h))

include hK ha

theorem exists_eq_mul_of_mem_B_of_mem_r2
    {b : reeFixed ReeTag.F4 K a}
    (hb : (b : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).B)
    (hbR : b ∈ r2 K a hK) : ∃ t ∈ blockT a hK 1, ∃ y ∈ blockX (K := K) a 1, b = t * y := by
  obtain ⟨u, hu, huF, h, hh, hhF, hbuh⟩ :=
    exists_mul_of_mem_B_of_mem_reeFixed (t := ReeTag.F4) a hb b.2
  have hcomm : ∀ s ∈ (nativeData ReeTag.F4.tag K).H, simpleChar s (fi 1) = 1 →
      simpleChar s (fi 2) = 1 → s * u * s⁻¹ = u := by
    intro s hs h1 h2
    have hb' := conj_eq_of_mem_centralizer_singleton (mem_centralizer_of_mem_r2 hK hs h1 h2 hbR)
    have hh' : s * h * s⁻¹ = h := by
      rw [(commute_of_mem_H hs hh).eq]
      group
    rw [hbuh] at hb'
    calc s * u * s⁻¹ = s * (u * h) * s⁻¹ * (s * h * s⁻¹)⁻¹ := by group
      _ = u := by rw [hb', hh']; group
  have huz := mem_Uminus_blockElt_one_of_forall_commute (exists_unit_ne_one_sq_ne_one hK ha) hu
    hcomm
  set y₀ : reeFixed ReeTag.F4 K a := ⟨u, huF⟩ with hy₀def
  set h₀ : reeFixed ReeTag.F4 K a := ⟨h, hhF⟩ with hh₀def
  have hy₀ : y₀ ∈ blockX (K := K) a 1 := huz
  have hb₀ : b = y₀ * h₀ := Subtype.ext hbuh
  have hh₀R : h₀ ∈ r2 K a hK := by
    have e : h₀ = y₀⁻¹ * b := by rw [hb₀]; group
    rw [e]
    exact mul_mem (inv_mem (blockX_le_r2 hK hy₀)) hbR
  obtain ⟨b₀, b₁, hh01⟩ := exists_eq_reeTorus_mul hK hh hhF
  have hdet := det_vMat_of_mem_r2 hK hh₀R
  change (vMat h).det = 1 at hdet
  rw [hh01, vMat_mul (mem_vStab_of_mem_H (ReeTag.F4.reeTorus_mem_H a _ b₀))
    (mem_vStab_of_mem_H (ReeTag.F4.reeTorus_mem_H a _ b₁)), Matrix.det_mul,
    det_vMat_reeTorus_zero, vMat_reeTorus_one hK, CFSG.Blueprint.det_suzukiD, mul_one] at hdet
  have hb₀1 : b₀ = 1 := eq_one_of_zpow_four_mul_sub_two hK (Units.val_eq_one.1 hdet)
  rw [hb₀1, reeTorus_one, one_mul] at hh01
  refine ⟨reeTorusHom a hK fi_one_mem_longSet b₁, ⟨b₁, rfl⟩, h₀⁻¹ * y₀ * h₀, ?_, ?_⟩
  · change h⁻¹ * u * h ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))
    have := conj_mem_Uminus_of_mem_H (inv_mem hh) huz
    rwa [inv_inv] at this
  · apply Subtype.ext
    change (b : adjointGroup ReeTag.F4.tag K) = ReeTag.F4.reeTorus a (fi 1) b₁ * (h⁻¹ * u * h)
    rw [hbuh, ← hh01]
    group

theorem r2_cells
    {g : reeFixed ReeTag.F4 K a} (hg : g ∈ r2 K a hK) :
    (∃ t ∈ blockT a hK 1, ∃ y ∈ blockX (K := K) a 1, g = t * y) ∨
      ∃ t ∈ blockT a hK 1, ∃ y ∈ blockX (K := K) a 1, ∃ y' ∈ blockX (K := K) a 1,
        g = t * y * relNrepHom K a (blockGen 1) * y' := by
  obtain ⟨-, hdisj, hexists, hunique⟩ := native_refined_bruhat ReeTag.F4.tag K
  obtain ⟨w, hw, b, hb, hbF, u, hu, huF, hgw⟩ :=
    ReeTag.exists_reeFixed_mul a hdisj hexists hunique ((mem_reeFixed ReeTag.F4 K a).1 g.2)
  obtain ⟨m, hmJ, b₁, hb₁, b₂, hb₂, hgm⟩ :=
    exists_mem_doubleCoset_of_mem_closure _ (mem_closure_of_mem_r2 hK hg)
  have hmw : weylHom ReeTag.F4.tag K m = w := by
    have := nativeData_weylHom_eq_of_mul_eq m
      ⟨nrep ReeTag.F4.tag K w, nrep_mem_monomialGroup _ _ w⟩ hb₁ hb₂ hb
      ((nativeData ReeTag.F4.tag K).U_le_B (Uminus_le_U ReeTag.F4.tag K w hu))
      (hgm.symm.trans hgw)
    rwa [weylHom_nrep] at this
  rw [hmw] at hmJ
  rcases eq_one_or_eq_blockElt hmJ hw with rfl | rfl
  · left
    rw [Uminus_one, Subgroup.mem_bot] at hu
    subst hu
    have hgb : (g : adjointGroup ReeTag.F4.tag K) = b := by
      rw [hgw, CFSG.LieType.Chevalley.nrep_one, mul_one, mul_one]
    exact exists_eq_mul_of_mem_B_of_mem_r2 hK ha (hgb ▸ hb) hg
  · right
    set y' : reeFixed ReeTag.F4 K a := ⟨u, huF⟩ with hy'def
    have hy' : y' ∈ blockX (K := K) a 1 := hu
    set b' : reeFixed ReeTag.F4 K a := ⟨b, hbF⟩ with hb'def
    have hgb : g = b' * relNrepHom K a (blockGen 1) * y' := Subtype.ext hgw
    have hb'R : b' ∈ r2 K a hK := by
      have e : b' = g * y'⁻¹ * (relNrepHom K a (blockGen 1))⁻¹ := by rw [hgb]; group
      rw [e]
      exact mul_mem (mul_mem hg (inv_mem (blockX_le_r2 hK hy'))) (inv_mem (relNrepHom_mem_r2 hK))
    obtain ⟨t, ht, y, hy, hb't⟩ := exists_eq_mul_of_mem_B_of_mem_r2 hK ha hb hb'R
    exact ⟨t, ht, y, hy, y', hy', by rw [hgb, hb't]⟩

theorem r2Rep_injective :
    Function.Injective (r2Rep K a hK) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, hg⟩ hg1
  have hmat : vMat (g : adjointGroup ReeTag.F4.tag K) = 1 := by
    have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hg1
    simpa only [coe_r2Rep, Units.val_one] using this
  apply Subtype.ext
  change g = 1
  rcases r2_cells hK ha hg with ⟨t, ⟨b, rfl⟩, y, hy, rfl⟩ | ⟨t, ht, y, hy, y', hy', rfl⟩
  · obtain ⟨u, v, huv⟩ := exists_vMat_eq_suzukiS (x := (y : adjointGroup ReeTag.F4.tag K)) hy
      ((mem_reeFixed ReeTag.F4 K a).1 y.2)
    have htS := mem_vStab_of_mem_H (K := K) (ReeTag.F4.reeTorus_mem_H a (fi 1) b)
    have hyS := mem_vStab_of_mem_r2 hK (blockX_le_r2 hK hy)
    change vMat (ReeTag.F4.reeTorus a (fi 1) b * (y : adjointGroup ReeTag.F4.tag K)) = 1 at hmat
    rw [vMat_mul htS hyS, vMat_reeTorus_one hK, huv] at hmat
    have h10 : (((b ^ (1 - 2 * (2 ^ a : ℤ))) ^ (2 ^ a : ℤ) : Kˣ) : K) * u = 0 := by
      have := congrFun₂ hmat 1 0
      rw [CFSG.Blueprint.suzukiD, Matrix.diagonal_mul, Matrix.one_apply_ne (by decide)] at this
      exact this
    have h20 : (((b ^ (1 - 2 * (2 ^ a : ℤ))) ^ (-(2 ^ a : ℤ)) : Kˣ) : K) * v = 0 := by
      have := congrFun₂ hmat 2 0
      rw [CFSG.Blueprint.suzukiD, Matrix.diagonal_mul, Matrix.one_apply_ne (by decide)] at this
      exact this
    obtain rfl : u = 0 := (mul_eq_zero.1 h10).resolve_left (Units.ne_zero _)
    obtain rfl : v = 0 := (mul_eq_zero.1 h20).resolve_left (Units.ne_zero _)
    rw [suzukiS_zero_zero, mul_one] at hmat
    have hy1 : y = 1 := Subtype.ext (eq_of_vMat_eq_of_mem_Uminus hy (one_mem _)
      ((huv.trans suzukiS_zero_zero).trans vMat_one.symm))
    have h00 : (((b ^ (1 - 2 * (2 ^ a : ℤ))) ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) = 1 := by
      have := congrFun₂ hmat 0 0
      rw [CFSG.Blueprint.suzukiD, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact this
    have h11 : (((b ^ (1 - 2 * (2 ^ a : ℤ))) ^ (2 ^ a : ℤ) : Kˣ) : K) = 1 := by
      have := congrFun₂ hmat 1 1
      rw [CFSG.Blueprint.suzukiD, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact this
    have hl : b ^ (1 - 2 * (2 ^ a : ℤ)) = 1 := by
      have e := Units.val_eq_one.1 h00
      rw [zpow_add, zpow_one, Units.val_eq_one.1 h11, mul_one] at e
      exact e
    rw [hy1, mul_one, eq_one_of_zpow_one_sub_two_mul hK hl, map_one]
  · exfalso
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    have hn : (relNrepHom K a (blockGen 1) : adjointGroup ReeTag.F4.tag K) =
        (((t * y)⁻¹ : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) *
          ((t * y * relNrepHom K a (blockGen 1) * y' : reeFixed ReeTag.F4 K a) :
            adjointGroup ReeTag.F4.tag K) * ((y'⁻¹ : reeFixed ReeTag.F4 K a) :
              adjointGroup ReeTag.F4.tag K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have htyR : (t * y)⁻¹ ∈ r2 K a hK :=
      inv_mem (mul_mem (blockT_le_r2 hK ht) (blockX_le_r2 hK hy))
    have hy'R : y'⁻¹ ∈ r2 K a hK := inv_mem (blockX_le_r2 hK hy')
    have hW := vMat_nrep_blockElt_one (K := K)
    rw [← coe_relNrepHom_blockGen_one (a := a), hn,
      vMat_mul (mul_mem (mem_vStab_of_mem_r2 hK htyR) (mem_vStab_of_mem_r2 hK hg))
        (mem_vStab_of_mem_r2 hK hy'R),
      vMat_mul (mem_vStab_of_mem_r2 hK htyR) (mem_vStab_of_mem_r2 hK hg), hmat, mul_one,
      ← vMat_mul (mem_vStab_of_mem_r2 hK htyR) (mem_vStab_of_mem_r2 hK hy'R)] at hW
    have hB : (((t * y)⁻¹ : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) *
        ((y'⁻¹ : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) ∈
          (nativeData ReeTag.F4.tag K).B := by
      obtain ⟨c, rfl⟩ := ht
      refine mul_mem (inv_mem (mul_mem ((nativeData ReeTag.F4.tag K).H_le_B
        (ReeTag.F4.reeTorus_mem_H a _ c)) ((nativeData ReeTag.F4.tag K).U_le_B
          (Uminus_le_U ReeTag.F4.tag K _ hy)))) (inv_mem ((nativeData ReeTag.F4.tag K).U_le_B
            (Uminus_le_U ReeTag.F4.tag K _ hy')))
    have h03 := congrFun₂ hW 0 3
    rw [vMat_zero_three_eq_zero hB] at h03
    simp [CFSG.Blueprint.suzukiW] at h03

omit ha in
theorem r2Rep_range :
    (r2Rep K a hK).range = CFSG.Blueprint.suzukiGroup a K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact r2Rep_mem_suzukiGroup hK g
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (⟨u, v, hg⟩ | ⟨l, hg⟩ | hg)
    · obtain ⟨x, hx, hxF, hxv⟩ := exists_reeFixed_vMat_eq_suzukiS hK u v
      exact ⟨⟨⟨x, hxF⟩, blockX_le_r2 hK hx⟩, Units.ext (hxv.trans hg.symm)⟩
    · refine ⟨⟨reeTorusHom a hK fi_one_mem_longSet (l ^ (-(2 * (2 ^ a : ℤ) + 1))),
        blockT_le_r2 hK ⟨_, rfl⟩⟩, Units.ext ?_⟩
      rw [coe_r2Rep, coe_reeTorusHom, vMat_reeTorus_one hK, hg, ← zpow_mul]
      have hq : (Nat.card K : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 := by
        rw [hK, ← natCast_prime_pow]
        exact two_pow_eq_two_mul_sq a
      have e : l ^ (-(2 * (2 ^ a : ℤ) + 1) * (1 - 2 * 2 ^ a)) = l := by
        rw [units_zpow_congr l (y := 1) 2 (by rw [hq]; ring), zpow_one]
      rw [e]
    · have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
      exact ⟨⟨relNrepHom K a (blockGen 1), relNrepHom_mem_r2 hK⟩,
        Units.ext (vMat_nrep_blockElt_one.trans hg.symm)⟩

variable (K a) in
@[expose] noncomputable def r2EquivSuzuki :
    r2 K a hK ≃* CFSG.Blueprint.suzukiGroup a K :=
  (MonoidHom.ofInjective (r2Rep_injective hK ha)).trans
    (MulEquiv.subgroupCongr (r2Rep_range hK))

theorem coe_r2EquivSuzuki
    (g : r2 K a hK) :
    ((r2EquivSuzuki K a hK ha g : CFSG.Blueprint.suzukiGroup a K) : GL (Fin 4) K) =
      r2Rep K a hK g :=
  rfl

end Cells

end CFSG.SectionRank.LargeRee
