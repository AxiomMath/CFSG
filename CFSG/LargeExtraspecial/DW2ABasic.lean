module

public import CFSG.LargeExtraspecial.DW2ModBasic
public import CFSG.LargeExtraspecial.S12TriInput
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.DWRed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] noncomputable def Ybar : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.Mbar.map S.O.subtype

theorem ρ_mem_Ybar (m : S.M) : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Ybar S :=
  ⟨S.ρ m, ⟨m, rfl⟩, rfl⟩

theorem mem_Ybar_iff {y : S.Qt ≃ₗ[ZMod 2] S.Qt} :
    y ∈ Ybar S ↔ ∃ m : S.M, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = y := by
  constructor
  · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ρ_mem_Ybar m

theorem Ybar_le_O : Ybar S ≤ S.O := map_subtype_le _

theorem O_le_isometryGroup : S.O ≤ TauCeti.BilinForm.isometryGroup S.q.polarBilin :=
  fun _ hg => TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]

theorem Ybar_le_isometryGroup : Ybar S ≤ TauCeti.BilinForm.isometryGroup S.q.polarBilin :=
  Ybar_le_O.trans O_le_isometryGroup

theorem noNormalTwo_Ybar : S12NoNormalTwo (Ybar S) :=
  S.s12_noNormalTwo_Mbar.map_subtype

theorem isInv_Ybar {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W) :
    IsInv (Ybar S) W := by
  intro y hy w hw
  obtain ⟨m, rfl⟩ := mem_Ybar_iff.mp hy
  exact hW m w hw

theorem eq_bot_of_isUnip_Ybar {K : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt)} (hK : K ≤ Ybar S)
    (hN : Ybar S ≤ normalizer (K : Set (S.Qt ≃ₗ[ZMod 2] S.Qt))) (hu : IsUnip K ⊥ ⊤) : K = ⊥ :=
  noNormalTwo_Ybar K hK (isPGroup_of_isUnip hu) hN

theorem eq_bot_of_isUnip_perp {W : Submodule (ZMod 2) S.Qt}
    {K : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt)} (hK : K ≤ Ybar S)
    (hN : Ybar S ≤ normalizer (K : Set (S.Qt ≃ₗ[ZMod 2] S.Qt))) (h1 : IsUnip K ⊥ W)
    (h2 : IsUnip K W (perp S W)) : K = ⊥ := by
  have hiso : K ≤ TauCeti.BilinForm.isometryGroup S.q.polarBilin :=
    hK.trans Ybar_le_isometryGroup
  have h3 : IsUnip K (perp S W) ⊤ :=
    (isUnip_orth_top_iff S.q_nondegenerate S.polarBilin_isRefl hiso).mpr h1
  exact eq_bot_of_isUnip_Ybar hK hN ((h1.trans h2).trans h3)

@[expose] noncomputable def chainKer (S : Setting G) (W₀ W : Submodule (ZMod 2) S.Qt) :
    Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  Ybar S ⊓ secCent ⊥ W₀ ⊓ secCent W₀ W ⊓ secCent W (perp S W)

theorem chainKer_le_Ybar (W₀ W : Submodule (ZMod 2) S.Qt) : chainKer S W₀ W ≤ Ybar S :=
  inf_le_left.trans (inf_le_left.trans inf_le_left)

theorem le_normalizer_chainKer {W₀ W : Submodule (ZMod 2) S.Qt} (hW₀ : IsMbarInvariant S W₀)
    (hW : IsMbarInvariant S W) :
    Ybar S ≤ normalizer (chainKer S W₀ W : Set (S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have i0 := isInv_Ybar hW₀
  have i1 := isInv_Ybar hW
  have i2 := isInv_Ybar hW.perp
  have ib : IsInv (Ybar S) (⊥ : Submodule (ZMod 2) S.Qt) := isInv_bot
  intro y hy
  rw [mem_normalizer_iff]
  have key : ∀ y ∈ Ybar S, ∀ k ∈ chainKer S W₀ W, y * k * y⁻¹ ∈ chainKer S W₀ W := by
    rintro y hy k ⟨⟨⟨hk, hk1⟩, hk2⟩, hk3⟩
    exact ⟨⟨⟨(Ybar S).mul_mem ((Ybar S).mul_mem hy hk) ((Ybar S).inv_mem hy),
      conj_mem_secCent ib i0 hy hk1⟩, conj_mem_secCent i0 i1 hy hk2⟩,
      conj_mem_secCent i1 i2 hy hk3⟩
  intro k
  refine ⟨key y hy k, fun h => ?_⟩
  have := key y⁻¹ ((Ybar S).inv_mem hy) _ h
  simpa [mul_assoc] using this

theorem chainKer_eq_bot {W₀ W : Submodule (ZMod 2) S.Qt} (hW₀ : IsMbarInvariant S W₀)
    (hW : IsMbarInvariant S W) : chainKer S W₀ W = ⊥ := by
  refine eq_bot_of_isUnip_perp (W := W) (chainKer_le_Ybar W₀ W) (le_normalizer_chainKer hW₀ hW)
    ?_ ?_
  · have a : IsUnip (chainKer S W₀ W) ⊥ W₀ :=
      isUnip_of_commSub_le (commSub_le_of_le_secCent
        (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    have b : IsUnip (chainKer S W₀ W) W₀ W :=
      isUnip_of_commSub_le (commSub_le_of_le_secCent (inf_le_left.trans inf_le_right))
    exact a.trans b
  · exact isUnip_of_commSub_le (commSub_le_of_le_secCent inf_le_right)

theorem eq_one_of_chain {W₀ W : Submodule (ZMod 2) S.Qt} (hW₀ : IsMbarInvariant S W₀)
    (hW : IsMbarInvariant S W) {y : S.Qt ≃ₗ[ZMod 2] S.Qt} (hy : y ∈ Ybar S) (h1 : ∀ w ∈ W₀, y w = w)
    (h2 : ∀ w ∈ W, y w - w ∈ W₀) (h3 : ∀ v ∈ perp S W, y v - v ∈ W) : y = 1 := by
  have hmem : y ∈ chainKer S W₀ W := by
    refine ⟨⟨⟨hy, mem_secCent_of_isInv (isInv_Ybar hW₀) hy fun w hw => ?_⟩,
      mem_secCent_of_isInv (isInv_Ybar hW) hy h2⟩,
      mem_secCent_of_isInv (isInv_Ybar hW.perp) hy h3⟩
    rw [h1 w hw, sub_self]
    exact zero_mem _
  rw [chainKer_eq_bot hW₀ hW, mem_bot] at hmem
  exact hmem

theorem eq_one_of_trivial_perp {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W)
    {y : S.Qt ≃ₗ[ZMod 2] S.Qt} (hy : y ∈ Ybar S)
    (h1 : ∀ w ∈ W, y w = w) (h2 : ∀ v ∈ perp S W, y v - v ∈ W) : y = 1 :=
  eq_one_of_chain hW hW hy h1 (fun w hw => by rw [h1 w hw, sub_self]; exact zero_mem _) h2

theorem exists_polar_eq_one {v : S.Qt} (hv : v ≠ 0) : ∃ w, polar S.q v w = 1 := by
  by_contra h0
  push Not at h0
  apply hv
  refine S.q_nondegenerate.1 v fun w => ?_
  rw [polarBilin_apply_apply]
  exact (zmod2_cases _).resolve_right (h0 w)

theorem perp_perp (W : Submodule (ZMod 2) S.Qt) : perp S (perp S W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W

omit [Finite G] in
theorem finrank_span_pair_of_not_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a b : V} (ha : a ≠ 0) (hb : b ∉ ZMod 2 ∙ a) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {a, b}) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right ha, rfl⟩
    · refine absurd ?_ hb
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      have : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
      rw [← neg_mul, mul_smul, neg_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ ht,
        one_smul]
  have h := finrank_span_eq_card hli
  have hr : Set.range ![a, b] = {a, b} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h) <;> simp [← h]
    · rintro (h | h) <;> simp [h]
  rw [hr] at h
  simpa using h

section Normalizer

variable {W : Submodule (ZMod 2) S.Qt}

omit [Finite G] in
theorem centralizer_clPre_le_M (W : Submodule (ZMod 2) S.Qt) :
    centralizer (S.clPre W : Set G) ≤ S.M := fun _ hc =>
  mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hc) S.z (S.z_mem_clPre W)).symm

theorem QG_inf_centralizer_clPre (W : Submodule (ZMod 2) S.Qt) :
    S.QG ⊓ centralizer (S.clPre W : Set G) = S.clPre (perp S W) := by
  rw [S.centralizer_inf_QG_eq_clPre (S.clPre_le_QG W), S.clSub_clPre]
  rfl

theorem M_le_normalizer_clPre (hW : IsMbarInvariant S W) :
    S.M ≤ normalizer (S.clPre W : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_clPre hW hm ha, fun ha => ?_⟩
  have := conj_mem_clPre hW (S.M.inv_mem hm) ha
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_centralizer {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  have key : ∀ h : G, h ∈ normalizer (A : Set G) → ∀ c ∈ centralizer (A : Set G),
      h * c * h⁻¹ ∈ centralizer (A : Set G) := by
    intro h hh c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : h⁻¹ * a * h ∈ A := by
      have := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hh) a).mp ha
      simpa [mul_assoc] using this
    have e := hc _ ha'
    calc a * (h * c * h⁻¹) = h * ((h⁻¹ * a * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * a * h)) * h⁻¹ := by rw [e]
      _ = h * c * h⁻¹ * a := by group
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ ((normalizer (A : Set G)).inv_mem hg) _ h
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at this

@[expose] noncomputable def core2 (C : Subgroup G) : Subgroup G := (CFSG.pCore 2 C).map C.subtype

omit [Finite G] in
theorem conj_mem_core2 {C : Subgroup G} {g : G} (hg : g ∈ normalizer (C : Set G)) {p : G}
    (hp : p ∈ core2 C) : g * p * g⁻¹ ∈ core2 C := by
  obtain ⟨c, hc, rfl⟩ := hp
  set φ := C.normalizerMonoidHom ⟨g, hg⟩
  have hfix := (CFSG.pCore_characteristic (p := 2) (G := C)).fixed φ.symm
  have hmem : φ c ∈ CFSG.pCore 2 C := by
    rw [← hfix]
    change φ.symm (φ c) ∈ CFSG.pCore 2 C
    simpa using hc
  exact ⟨φ c, hmem, rfl⟩

theorem core2_centralizer_eq (hW : IsMbarInvariant S W) :
    core2 (centralizer (S.clPre W : Set G)) = S.clPre (perp S W) := by
  set C := centralizer (S.clPre W : Set G)
  have hCM : C ≤ S.M := centralizer_clPre_le_M W
  have hMN : ∀ m ∈ S.M, m ∈ normalizer (C : Set G) := fun m hm =>
    mem_normalizer_centralizer (M_le_normalizer_clPre hW hm)
  apply le_antisymm
  ·
    have hle : core2 C ≤ C := map_subtype_le _
    set P : Subgroup S.M := (core2 C).subgroupOf S.M
    have hPn : P.Normal := ⟨fun x hx m => mem_subgroupOf.mpr
      (conj_mem_core2 (hMN m m.2) (mem_subgroupOf.mp hx))⟩
    have hP2 : IsPGroup 2 P := by
      have h1 : IsPGroup 2 (core2 C) := CFSG.pCore_isPGroup.map _
      exact h1.of_equiv (subgroupOfEquivOfLe (hle.trans hCM)).symm
    have hPQ := S.le_of_normal P hPn hP2
    rw [← QG_inf_centralizer_clPre]
    intro p hp
    exact ⟨S.mem_QG_iff.mpr ⟨hCM (hle hp), hPQ (mem_subgroupOf.mpr hp)⟩, hle hp⟩
  ·
    rw [← QG_inf_centralizer_clPre]
    intro b hb
    have hBn : ((S.QG ⊓ C).subgroupOf C).Normal := ⟨fun x hx c => mem_subgroupOf.mpr
      ⟨S.conj_mem_QG (hCM c.2) (mem_subgroupOf.mp hx).1,
        C.mul_mem (C.mul_mem c.2 (mem_subgroupOf.mp hx).2) (C.inv_mem c.2)⟩⟩
    have hB2 : IsPGroup 2 ((S.QG ⊓ C).subgroupOf C) := by
      have h1 : IsPGroup 2 (S.QG ⊓ C : Subgroup G) :=
        (S.extraspecial.1.map S.M.subtype).to_le inf_le_left
      exact h1.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    have hle : (S.QG ⊓ C).subgroupOf C ≤ CFSG.pCore 2 C := le_sSup ⟨hBn, hB2⟩
    exact ⟨⟨b, hb.2⟩, hle (mem_subgroupOf.mpr hb), rfl⟩

theorem normalizer_clPre_le_M (hW : IsMbarInvariant S W) (hne : ¬ perp S W ≤ W) :
    normalizer (S.clPre W : Set G) ≤ S.M := by
  intro g hg
  have hgC := mem_normalizer_centralizer hg
  have hB : ∀ b ∈ S.clPre (perp S W), g * b * g⁻¹ ∈ S.clPre (perp S W) := by
    intro b hb
    rw [← core2_centralizer_eq hW] at hb ⊢
    exact conj_mem_core2 hgC hb
  have hpp : perp S (perp S W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W
  obtain ⟨u, hu, hu'⟩ := Set.not_subset.mp hne
  rw [← hpp] at hu'
  rw [SetLike.mem_coe, mem_perp] at hu'
  push Not at hu'
  obtain ⟨v, hv, huv⟩ := hu'
  obtain ⟨b, hbQ, rfl⟩ := S.exists_cl v
  obtain ⟨b', hb'Q, rfl⟩ := S.exists_cl u
  have hc : b * b' * b⁻¹ * b'⁻¹ = S.z := by
    rcases S.commutator_eq_one_or_z hbQ hb'Q with h | h
    · exfalso
      apply huv
      rw [S.polar_cl_eq_zero_iff hbQ hb'Q]
      calc b * b' = b * b' * b⁻¹ * b'⁻¹ * (b' * b) := by group
        _ = b' * b := by rw [h, one_mul]
    · exact h
  have h1 := hB b ⟨hbQ, hv⟩
  have h2 := hB b' ⟨hb'Q, hu⟩
  have hc' : (g * b * g⁻¹) * (g * b' * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * b' * g⁻¹)⁻¹ =
      g * S.z * g⁻¹ := by
    rw [← hc]
    group
  rw [S.mem_M_iff]
  rcases S.commutator_eq_one_or_z h1.1 h2.1 with h | h
  · rw [h] at hc'
    exfalso
    apply S.z_ne_one
    have := congrArg (fun x => g⁻¹ * x * g) hc'
    simpa [mul_assoc] using this.symm
  · rw [h] at hc'
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [← hc']

end Normalizer

end CFSG.LargeExtraspecial.DW
