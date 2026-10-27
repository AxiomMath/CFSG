module

public import CFSG.LargeExtraspecial.S3Eight
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

theorem isExtraspecialPGroup_two_of_center {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {c : G} (hH : IsPGroup 2 H) (hc : c ∈ H) (hc1 : c ≠ 1)
    (hZ : ∀ x ∈ H, (∀ y ∈ H, x * y = y * x) ↔ x = 1 ∨ x = c)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = c)
    (hsq : ∀ x ∈ H, x ^ 2 = 1 ∨ x ^ 2 = c) (hnc : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) :
    IsExtraspecialPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c' : H := ⟨c, hc⟩
  have hmemZ : ∀ x : H, x ∈ center H ↔ x = 1 ∨ x = c' := by
    intro x
    rw [mem_center_iff]
    have h := hZ x x.2
    constructor
    · intro hx
      rcases h.mp fun y hy => (congrArg Subtype.val (hx ⟨y, hy⟩)).symm with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    · intro hx y
      have h' := h.mpr (by
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)
      exact Subtype.ext (h' y y.2).symm
  have hc'Z : c' ∈ center H := (hmemZ c').mpr (Or.inr rfl)
  have hcommZ : ∀ x y : H, ⁅x, y⁆ ∈ center H := by
    intro x y
    rw [hmemZ]
    rcases hcomm x x.2 y y.2 with h | h
    · left
      exact Subtype.ext (by simpa [commutatorElement_def] using h)
    · right
      exact Subtype.ext (by simpa [commutatorElement_def] using h)
  have hsqZ : ∀ x : H, x ^ 2 ∈ center H := by
    intro x
    rw [hmemZ]
    rcases hsq x x.2 with h | h
    · left
      exact Subtype.ext (by simpa using h)
    · right
      exact Subtype.ext (by simpa using h)
  have hcomm_eq : commutator H = center H := by
    refine le_antisymm ?_ fun x hx => ?_
    · rw [_root_.commutator_def, commutator_le]
      intro x _ y _
      exact hcommZ x y
    · rcases (hmemZ x).mp hx with rfl | rfl
      · exact one_mem _
      · obtain ⟨x, hx, y, hy, hxy⟩ := hnc
        have h1 : x * y * x⁻¹ * y⁻¹ = c := (hcomm x hx y hy).resolve_left fun h => hxy (by
          calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
            _ = y * x := by rw [h, one_mul])
        have : ⁅(⟨x, hx⟩ : H), ⟨y, hy⟩⁆ = c' :=
          Subtype.ext (by simpa [commutatorElement_def] using h1)
        rw [← this, _root_.commutator_def]
        exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hfr_le : frattini H ≤ center H :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) (center H) hcommZ hsqZ
  have hle_fr : center H ≤ frattini H := by
    rw [← hcomm_eq, _root_.commutator_def, commutator_le]
    intro x _ y _
    exact CFSG.SectionRank.Ccomm.commutator_mem_frattini hH x y
  refine ⟨hH, hcomm_eq, le_antisymm hfr_le hle_fr, ?_⟩
  refine (Nat.card_eq_two_iff' (⟨1, one_mem _⟩ : center H)).mpr
    ⟨⟨c', hc'Z⟩, fun h => hc1 (congrArg (fun w : center H => ((w : H) : G)) h), fun y hy => ?_⟩
  rcases (hmemZ y).mp y.2 with h | h
  · exact absurd (Subtype.ext h) hy
  · exact Subtype.ext h

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem QG_inf_Qa_comm {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) {x y : G}
    (hx : x ∈ S.QG ⊓ S.Qa g) (hy : y ∈ S.QG ⊓ S.Qa g) : x * y = y * x := by
  have h1 := S.commutator_eq_one_or_z hx.1 hy.1
  have h2 := (S.conjBy g).commutator_eq_one_or_z hx.2 hy.2
  have h : x * y * x⁻¹ * y⁻¹ = 1 := by
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2).symm hne
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h, one_mul]

theorem QG_inf_Qa_sq {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) {x : G} (hx : x ∈ S.QG ⊓ S.Qa g) :
    x ^ 2 = 1 := by
  rcases S.sq_eq_one_or_z hx.1 with h1 | h1
  · exact h1
  · rcases (S.conjBy g).sq_eq_one_or_z hx.2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2).symm hne

theorem isElementaryAbelian_QG_inf_Qa {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) :
    CFSG.IsElementaryAbelian 2 (S.QG ⊓ S.Qa g : Subgroup G) where
  is_comm := ⟨fun x y => Subtype.ext (S.QG_inf_Qa_comm hne x.2 y.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using S.QG_inf_Qa_sq hne x.2)

theorem card_QG_inf_Qa_le {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ (S.width + 1) :=
  S.card_le_of_commute inf_le_left fun _ hx _ hy => S.QG_inf_Qa_comm hne hx hy

omit [Finite G] in
theorem card_Qa (g : G) : Nat.card (S.Qa g) = Nat.card S.QG := by
  rw [S.Qa_eq_map]
  exact card_map_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem L0_eq (g : G) : S.L0 g = S.Qa g ⊓ centralizer ({S.z} : Set G) := rfl

omit [Finite G] in
theorem L0_le_Qa (g : G) : S.L0 g ≤ S.Qa g := inf_le_left

omit [Finite G] in
theorem L0_le_M (g : G) : S.L0 g ≤ S.M := inf_le_right

theorem relIndex_L0 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    (S.L0 g).relIndex (S.Qa g) = 2 := by
  have hzQa := S.z_mem_Qa_of_mem_QG rfl haQ hne
  exact (S.conjBy g).relIndex_centralizer_eq_two hzQa S.z_ne_one hne.symm

theorem card_L0 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.L0 g) = 2 ^ (2 * S.width) := by
  have h := relIndex_mul_card (S.L0 g) (S.Qa g)
  rw [S.relIndex_L0 haQ hne, inf_eq_left.mpr (S.L0_le_Qa g), S.card_Qa, S.card_QG_eq_card_Q,
    S.card_Q_eq, pow_add, pow_one] at h
  omega

theorem width_conjBy (g : G) : (S.conjBy g).width = S.width := by
  have h1 := (S.conjBy g).card_Q_eq
  rw [← (S.conjBy g).card_QG_eq_card_Q, show (S.conjBy g).QG = S.Qa g from rfl, S.card_Qa,
    S.card_QG_eq_card_Q, S.card_Q_eq] at h1
  have := Nat.pow_right_injective le_rfl h1
  omega

theorem mem_orthogonal_pair_iff {u v x : S.Qt} :
    x ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {u, v}) ↔
      polar S.q u x = 0 ∧ polar S.q v x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h u (Submodule.subset_span (by simp))
      rwa [polarBilin_apply_apply] at this
    · have := h v (Submodule.subset_span (by simp))
      rwa [polarBilin_apply_apply] at this
  · rintro ⟨hu, hv⟩ y hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_smul_left, hu, hv,
      smul_zero, smul_zero, add_zero]

omit [Finite G] in
theorem cl_conj_of_mem {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    S.cl (x * y * x⁻¹) = S.cl y := by
  rcases S.mul_comm_or hx hy with h | h
  · rw [h]
    group
  · rw [h, show S.z * (y * x) * x⁻¹ = y * S.z by rw [S.z_comm_QG hy]; group, S.cl_mul_z hy]

theorem exists_L0_eq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ Q₀ : Subgroup G, Q₀ ≤ S.L0 g ∧ zpowers S.z ⊔ Q₀ = S.L0 g ∧ Disjoint (zpowers S.z) Q₀ ∧
      S.L0 g ≤ normalizer (Q₀ : Set G) ∧ Nat.card Q₀ = 2 ^ (1 + 2 * (S.width - 1)) ∧
      Q₀ ⊓ centralizer (Q₀ : Set G) = zpowers (g * S.z * g⁻¹) ∧
      (2 ≤ S.width → IsExtraspecialPGroup 2 Q₀) := by
  set T := S.conjBy g with hT
  set a := g * S.z * g⁻¹ with ha
  have hTz : T.z = a := rfl
  have hzQa : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl haQ hne
  have ha1 : a ≠ 1 := T.z_ne_one
  obtain ⟨w, hwQ, hwz⟩ := T.exists_conj_eq_mul_z hzQa S.z_ne_one hne.symm
  have hwz' : w * S.z ≠ S.z * w := fun h => by
    have h2 : w * S.z * w⁻¹ = S.z := by rw [h]; group
    rw [h2] at hwz
    have h3 : T.z = 1 := by
      calc T.z = S.z⁻¹ * (S.z * T.z) := by group
        _ = 1 := by rw [← hwz, inv_mul_cancel]
    exact ha1 h3
  have hpwz : polar T.q (T.cl w) (T.cl S.z) = 1 := (T.polar_cl_eq_one_iff hwQ hzQa).mpr hwz'
  set P := Submodule.span (ZMod 2) {T.cl S.z, T.cl w} with hP
  set W := LinearMap.BilinForm.orthogonal T.q.polarBilin P with hW
  set Q₀ := T.clPre W with hQ₀
  have hmem : ∀ x, x ∈ Q₀ ↔ x ∈ T.QG ∧ S.z * x = x * S.z ∧ w * x = x * w := by
    intro x
    rw [T.mem_clPre, T.mem_orthogonal_pair_iff]
    constructor
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, (T.polar_cl_eq_zero_iff hzQa hx).mp h1, (T.polar_cl_eq_zero_iff hwQ hx).mp h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, (T.polar_cl_eq_zero_iff hzQa hx).mpr h1, (T.polar_cl_eq_zero_iff hwQ hx).mpr h2⟩
  have hzL0 : S.z ∈ S.L0 g := ⟨hzQa, S.z_mem_M⟩
  have hQ₀L0 : Q₀ ≤ S.L0 g := fun x hx => by
    obtain ⟨hxQ, hxz, -⟩ := (hmem x).mp hx
    exact ⟨hxQ, S.mem_M_iff.mpr hxz.symm⟩
  have hzQ₀ : S.z ∉ Q₀ := fun h => hwz' ((hmem _).mp h).2.2
  have hdecomp : ∀ x ∈ S.L0 g, x ∈ Q₀ ∨ S.z * x ∈ Q₀ := by
    intro x hx
    have hxQ : x ∈ T.QG := hx.1
    have hxz : S.z * x = x * S.z := (S.mem_M_iff.mp hx.2).symm
    by_cases hxw : w * x = x * w
    · exact Or.inl ((hmem x).mpr ⟨hxQ, hxz, hxw⟩)
    · right
      have hzxQ : S.z * x ∈ T.QG := T.QG.mul_mem hzQa hxQ
      refine (hmem _).mpr ⟨hzxQ, ?_, ?_⟩
      · calc S.z * (S.z * x) = S.z * (x * S.z) := by rw [hxz]
          _ = S.z * x * S.z := by group
      have h1 : polar T.q (T.cl w) (T.cl x) = 1 := (T.polar_cl_eq_one_iff hwQ hxQ).mpr hxw
      have h2 : polar T.q (T.cl w) (T.cl (S.z * x)) = 0 := by
        rw [T.cl_mul hzQa hxQ, polar_add_right, hpwz, h1]
        decide
      exact (T.polar_cl_eq_zero_iff hwQ hzxQ).mp h2
  have hnd := LinearMap.BilinForm.IsAlt.restrict_nondegenerate_orthogonal_span_pair
    T.polarBilin_isAlt (e := T.cl S.z) (f := T.cl w)
    (by rw [polarBilin_apply_apply]; exact hpwz) T.q_nondegenerate
  have hZ : ∀ x ∈ Q₀, (∀ y ∈ Q₀, x * y = y * x) ↔ x = 1 ∨ x = a := by
    intro x hx
    constructor
    · intro h
      have hxW : T.cl x ∈ W := hx.2
      have h0 : (⟨T.cl x, hxW⟩ : W) = 0 := hnd.1 _ fun v => by
        obtain ⟨y, hyQ, hyv⟩ := T.exists_cl (v : T.Qt)
        have hy : y ∈ Q₀ := ⟨hyQ, hyv ▸ v.2⟩
        rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          polarBilin_apply_apply, ← hyv]
        exact (T.polar_cl_eq_zero_iff hx.1 hyQ).mpr (h y hy)
      exact (T.cl_eq_zero_iff hx.1).mp (congrArg Subtype.val h0)
    · rintro (rfl | rfl) y _
      · rw [one_mul, mul_one]
      · exact (T.z_comm_QG ((T.clPre_le_QG W) ‹_›)).symm
  refine ⟨Q₀, hQ₀L0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le (zpowers_le.mpr hzL0) hQ₀L0) fun x hx => ?_
    rcases hdecomp x hx with h | h
    · exact mem_sup_right h
    · have : x = S.z⁻¹ * (S.z * x) := by group
      rw [this]
      exact mul_mem (mem_sup_left (inv_mem (mem_zpowers _))) (mem_sup_right h)
  · rw [disjoint_def]
    intro x hx hxQ
    rcases (mem_zpowers_iff_of_mul_self S.z_mul_z).mp hx with h | h
    · exact h
    · exact absurd (h ▸ hxQ) hzQ₀
  · intro x hx
    rw [mem_normalizer_iff]
    intro y
    have hxQ : x ∈ T.QG := hx.1
    constructor
    · rintro ⟨hyQ, hyW⟩
      refine ⟨T.QG.mul_mem (T.QG.mul_mem hxQ hyQ) (T.QG.inv_mem hxQ), ?_⟩
      rw [T.cl_conj_of_mem hxQ hyQ]
      exact hyW
    · rintro ⟨hyQ, hyW⟩
      have hyQ' : y ∈ T.QG := by
        have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [this]
        exact T.QG.mul_mem (T.QG.mul_mem (T.QG.inv_mem hxQ) hyQ) hxQ
      refine ⟨hyQ', ?_⟩
      rw [T.cl_conj_of_mem hxQ hyQ'] at hyW
      exact hyW
  · have hfin := LinearMap.BilinForm.IsAlt.finrank_orthogonal_span_pair_add_two
      T.polarBilin_isAlt T.q_nondegenerate (e := T.cl S.z) (f := T.cl w)
      (by rw [polarBilin_apply_apply]; exact hpwz)
    rw [T.finrank_Qt_eq_two_mul_width, S.width_conjBy] at hfin
    have hfin' : finrank (ZMod 2) W + 2 = 2 * S.width := hfin
    rw [T.card_clPre, T.card_submodule, show finrank (ZMod 2) W = 2 * (S.width - 1) by omega,
      pow_add, pow_one]
  · ext x
    rw [mem_inf, mem_centralizer_iff, mem_zpowers_iff_of_mul_self (show a * a = 1 from T.z_mul_z)]
    constructor
    · rintro ⟨hx, h⟩
      exact (hZ x hx).mp fun y hy => (h y hy).symm
    · intro h
      have hx : x ∈ Q₀ := by
        rcases h with rfl | rfl
        · exact one_mem _
        · exact T.z_mem_clPre W
      exact ⟨hx, fun y hy => ((hZ x hx).mpr h y hy).symm⟩
  · intro hn
    refine isExtraspecialPGroup_two_of_center (T.isPGroup_QG.to_le (T.clPre_le_QG W))
      (T.z_mem_clPre W) ha1 hZ (fun x hx y hy => T.commutator_eq_one_or_z hx.1 hy.1)
      (fun x hx => T.sq_eq_one_or_z hx.1) ?_
    have hfin := LinearMap.BilinForm.IsAlt.finrank_orthogonal_span_pair_add_two
      T.polarBilin_isAlt T.q_nondegenerate (e := T.cl S.z) (f := T.cl w)
      (by rw [polarBilin_apply_apply]; exact hpwz)
    rw [T.finrank_Qt_eq_two_mul_width, S.width_conjBy] at hfin
    have hfin' : finrank (ZMod 2) W + 2 = 2 * S.width := hfin
    have hWne : W ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hfin'
      omega
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have : ∃ v' : W, polar T.q v v' ≠ 0 := by
      by_contra h
      push Not at h
      apply hv0
      have := hnd.1 ⟨v, hvW⟩ fun v' => by
        rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          polarBilin_apply_apply]
        exact h v'
      exact congrArg Subtype.val this
    obtain ⟨v', hv'⟩ := this
    obtain ⟨x, hxQ, rfl⟩ := T.exists_cl v
    obtain ⟨y, hyQ, hyv⟩ := T.exists_cl (v' : T.Qt)
    refine ⟨x, ⟨hxQ, hvW⟩, y, ⟨hyQ, hyv ▸ v'.2⟩, fun hxy => hv' ?_⟩
    rw [← hyv]
    exact (T.polar_cl_eq_zero_iff hxQ hyQ).mpr hxy

@[expose] noncomputable def Lbar (g : G) : Subgroup S.O := ((S.L0 g).subgroupOf S.M).map S.ρ

theorem Lbar_le_Mbar (g : G) : S.Lbar g ≤ S.Mbar := map_le_range _ _

theorem map_La_eq_Lbar (g : G) : ((S.La g).subgroupOf S.M).map S.ρ = S.Lbar g := by
  refine le_antisymm ?_ (map_mono fun x hx => mem_subgroupOf.mpr
    ((le_sup_right : S.L0 g ≤ S.La g) (mem_subgroupOf.mp hx)))
  set K : Subgroup G := ((S.Lbar g).comap S.ρ).map S.M.subtype
  have hK : S.La g ≤ K := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · refine ⟨⟨x, S.QG_le_M hx⟩, show _ ∈ comap S.ρ (S.Lbar g) from ?_, rfl⟩
      rw [mem_comap, (S.ρ_eq_one_iff _).mpr hx]
      exact one_mem _
    · exact ⟨⟨x, hx.2⟩, ⟨⟨x, hx.2⟩, hx, rfl⟩, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hK hy
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem isElementaryAbelian_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    CFSG.IsElementaryAbelian 2 (S.Lbar g) := by
  set T := S.conjBy g
  have hcomm : ∀ x ∈ S.L0 g, ∀ y ∈ S.L0 g, ∀ (hx : x ∈ S.M) (hy : y ∈ S.M),
      S.ρ ⟨x, hx⟩ * S.ρ ⟨y, hy⟩ = S.ρ ⟨y, hy⟩ * S.ρ ⟨x, hx⟩ := by
    intro x hxL y hyL hx hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ S.QG := by
      rcases T.commutator_eq_one_or_z hxL.1 hyL.1 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact haQ
    have hcM : x * y * x⁻¹ * y⁻¹ ∈ S.M := S.QG_le_M hc
    have h1 := (S.ρ_eq_one_iff ⟨_, hcM⟩).mpr hc
    have h2 : (⟨x, hx⟩ : S.M) * ⟨y, hy⟩ = ⟨_, hcM⟩ * (⟨y, hy⟩ * ⟨x, hx⟩) :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [← map_mul, ← map_mul, h2, map_mul, h1, one_mul]
  have hsq : ∀ x ∈ S.L0 g, ∀ (hx : x ∈ S.M), S.ρ ⟨x, hx⟩ ^ 2 = 1 := by
    intro x hxL hx
    have hc : x ^ 2 ∈ S.QG := by
      rcases T.sq_eq_one_or_z hxL.1 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact haQ
    rw [← map_pow]
    exact (S.ρ_eq_one_iff _).mpr hc
  refine { is_comm := ⟨fun u v => ?_⟩, exponent_dvd_p := ?_ }
  · obtain ⟨⟨x, hx⟩, hxL, hux⟩ := u.2
    obtain ⟨⟨y, hy⟩, hyL, hvy⟩ := v.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hux, ← hvy]
    exact hcomm x hxL y hyL hx hy
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
    obtain ⟨⟨x, hx⟩, hxL, hux⟩ := u.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hux]
    exact hsq x hxL hx

theorem card_Lbar_mul (g : G) :
    Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = Nat.card (S.L0 g) := by
  set f : S.L0 g →* S.O := S.ρ.comp (inclusion (S.L0_le_M g))
  have hrange : f.range = S.Lbar g := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : f.ker = S.QG.subgroupOf (S.L0 g) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have hinf : S.QG ⊓ S.L0 g = S.QG ⊓ S.Qa g := by
    rw [L0, ← inf_assoc, inf_right_comm, inf_eq_left.mpr S.QG_le_M]
  have h := card_ker_mul_card_range f
  rw [hrange, hker, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S.QG ⊓ S.L0 g ≤ S.L0 g)).toEquiv,
    hinf, mul_comm] at h
  exact h

theorem card_Lbar_ge {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    2 ^ (S.width - 1) ≤ Nat.card (S.Lbar g) := by
  have h1 := S.card_Lbar_mul g
  have h2 := S.card_QG_inf_Qa_le hne
  rw [S.card_L0 haQ hne] at h1
  rcases Nat.eq_zero_or_pos S.width with h0 | h0
  · rw [h0]
    refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
    rw [h, zero_mul] at h1
    exact absurd h1.symm (by positivity)
  · have h3 : 2 ^ (S.width - 1) * 2 ^ (S.width + 1) = 2 ^ (2 * S.width) := by
      rw [← pow_add]
      congr 1
      omega
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ (S.width + 1)) ?_ (by positivity)
    rw [h3, ← h1]
    exact Nat.mul_le_mul_left _ h2

theorem mem_of_cl_fixed_by_L0 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {x : G} (hx : x ∈ S.QG ⊓ S.Qa g)
    (hfix : ∀ y ∈ S.L0 g, S.cl (y * x * y⁻¹) = S.cl x) :
    x = 1 ∨ x = g * S.z * g⁻¹ ∨ x = S.z ∨ x = S.z * (g * S.z * g⁻¹) := by
  set T := S.conjBy g
  have hzQa : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl haQ hne
  refine (T.mem_centralizer_centralizer_iff hzQa).mp ⟨hx.2, mem_centralizer_iff.mpr ?_⟩
  intro y hy
  have h1 := hfix y hy
  have hyM : y ∈ S.M := hy.2
  rcases (S.cl_eq_cl_iff hx.1 (S.conj_mem_QG hyM hx.1)).mp h1.symm with h2 | h2
  · calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h2]
  · exfalso
    rcases T.mul_comm_or hy.1 hx.2 with h3 | h3
    · have : y * x * y⁻¹ = x := by rw [h3]; group
      rw [this] at h2
      exact S.z_ne_one (by
        calc S.z = x⁻¹ * (x * S.z) := by group
          _ = 1 := by rw [← h2, inv_mul_cancel])
    · have h4 : y * x * y⁻¹ = T.z * x := by rw [h3]; group
      rw [h4] at h2
      apply hne
      have h5 : T.z * x = S.z * x := by rw [h2, S.z_comm_QG hx.1]
      exact mul_right_cancel h5

theorem conj_L0_of_mem_QG_inf_Qa {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {x : G} (hx : x ∈ S.QG ⊓ S.Qa g)
    (hxa : S.cl x ≠ 0 ∧ S.cl x ≠ S.cl (g * S.z * g⁻¹)) :
    (∀ y ∈ S.L0 g, y * x * y⁻¹ = x ∨ y * x * y⁻¹ = g * S.z * g⁻¹ * x) ∧
      ∃ y ∈ S.L0 g, y * x * y⁻¹ = g * S.z * g⁻¹ * x := by
  set T := S.conjBy g
  have hzQa : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl haQ hne
  have hconj : ∀ y ∈ S.L0 g, y * x * y⁻¹ = x ∨ y * x * y⁻¹ = g * S.z * g⁻¹ * x := by
    intro y hy
    rcases T.mul_comm_or hy.1 hx.2 with h | h
    · left
      rw [h]
      group
    · right
      rw [h]
      change T.z * (x * y) * y⁻¹ = T.z * x
      group
  refine ⟨hconj, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ y ∈ S.L0 g, y * x * y⁻¹ = x := fun y hy =>
    (hconj y hy).resolve_right (hcon y hy)
  have hmem := (T.mem_centralizer_centralizer_iff hzQa).mp ⟨hx.2, mem_centralizer_iff.mpr
    fun y hy => by
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [hcomm y hy]⟩
  have ha : g * S.z * g⁻¹ ∈ S.QG := haQ
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hxa.1 S.cl_one
  · exact hxa.2 rfl
  · exact hxa.1 S.cl_z
  · exact hxa.2 (by
      change S.cl (S.z * (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)
      rw [S.cl_mul S.z_mem_QG ha, S.cl_z, zero_add])

end Setting

end CFSG.LargeExtraspecial
