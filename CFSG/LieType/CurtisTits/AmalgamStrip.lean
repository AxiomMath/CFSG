module

public import CFSG.LieType.CurtisTits.Amalgam

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u v w

variable {K : Type u} [Group K] {I : Type v} [Fintype I] [DecidableEq I]

structure StripData (𝒮 : Set (Set I)) (P L : Set I → Subgroup K) (T : I → Subgroup K) : Prop where
  small : ∀ C : Set I, C.ncard ≤ 3 → C ∈ 𝒮
  L_mono : ∀ ⦃C C' : Set I⦄, C ⊆ C' → L C ≤ L C'
  L_le : ∀ C ∈ 𝒮, L C ≤ P C
  T_le : ∀ i, T i ≤ L {i}
  T_comm : ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x
  T_indep : iSupIndep T
  norm : ∀ C ∈ 𝒮, ∀ t ∈ ⨆ i, T i, ∀ l ∈ L C, t * l * t⁻¹ ∈ L C
  prod : ∀ C ∈ 𝒮, ∀ x ∈ P C, ∃ t ∈ ⨆ i, T i, ∃ l ∈ L C, x = t * l
  inter : ∀ C ∈ 𝒮, (⨆ i, T i) ⊓ L C ≤ ⨆ i ∈ C, T i
  gen : ∀ C ∈ 𝒮, L C = ⨆ (E : Set I) (_ : E ⊆ C) (_ : E.ncard ≤ 2), L E

namespace StripData

variable {𝒮 : Set (Set I)} {P L : Set I → Subgroup K} {T : I → Subgroup K}

omit [Fintype I] [DecidableEq I] in
private theorem mem_singleton (d : StripData 𝒮 P L T) (i : I) : ({i} : Set I) ∈ 𝒮 :=
  d.small {i} (by rw [Set.ncard_singleton]; norm_num)

omit [Fintype I] [DecidableEq I] in
private theorem t_pairwise (d : StripData 𝒮 P L T) :
    Pairwise fun i j : I => ∀ x y : K, x ∈ T i → y ∈ T j → Commute x y := by
  intro i j hij x y hx hy
  exact d.T_comm i j hij x hx y hy

private noncomputable def torusEquiv (d : StripData 𝒮 P L T) :
    ((i : I) → T i) ≃* ↥(⨆ i, T i) :=
  (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := T)
    (hcomm := d.t_pairwise) d.T_indep)).trans
  (MulEquiv.subgroupCongr (Subgroup.noncommPiCoprod_range (H := T) (hcomm := d.t_pairwise)))

private theorem torusEquiv_mulSingle (d : StripData 𝒮 P L T) (i : I) (x : T i) :
    d.torusEquiv (Pi.mulSingle i x) = Subgroup.inclusion (le_iSup (fun i => T i) i) x := by
  apply Subtype.ext
  simp only [torusEquiv]
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply,
    Subgroup.noncommPiCoprod_mulSingle, Subgroup.coe_inclusion]

private noncomputable def phiT (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    (φ : ∀ C : ↥𝒮, L C.1 →* Y) (i : I) : T i →* Y :=
  (φ ⟨{i}, d.mem_singleton i⟩).comp (Subgroup.inclusion (d.T_le i))

omit [Fintype I] [DecidableEq I] in
private theorem phiT_comm (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ) :
    Pairwise fun i j : I => ∀ (x : T i) (y : T j), Commute (d.phiT φ i x) (d.phiT φ j y) := by
  intro i j hij x y
  have hF : ({i, j} : Set I) ∈ 𝒮 :=
    d.small _ (by rw [Set.ncard_pair hij]; norm_num)
  have hsub_i : ({i} : Set I) ⊆ {i, j} := by
    rw [Set.singleton_subset_iff]; simp
  have hsub_j : ({j} : Set I) ⊆ {i, j} := by
    rw [Set.singleton_subset_iff]; simp
  have hxF : d.phiT φ i x = φ ⟨{i, j}, hF⟩
      ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ :=
    hφ ⟨{i}, d.mem_singleton i⟩ ⟨{i, j}, hF⟩ hsub_i
      (Subgroup.inclusion (d.T_le i) x) ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ rfl
  have hyF : d.phiT φ j y = φ ⟨{i, j}, hF⟩
      ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ :=
    hφ ⟨{j}, d.mem_singleton j⟩ ⟨{i, j}, hF⟩ hsub_j
      (Subgroup.inclusion (d.T_le j) y) ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ rfl
  have hxy : (⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ : L ({i, j} : Set I)) *
      ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ =
      ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ *
      ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ :=
    Subtype.ext (d.T_comm i j hij x x.2 y y.2)
  rw [hxF, hyF]
  calc φ ⟨{i, j}, hF⟩ ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ *
        φ ⟨{i, j}, hF⟩ ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩
      = φ ⟨{i, j}, hF⟩ (⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ *
          ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩) := (map_mul _ _ _).symm
    _ = φ ⟨{i, j}, hF⟩ (⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ *
          ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩) := by rw [hxy]
    _ = φ ⟨{i, j}, hF⟩ ⟨(y : K), d.L_mono hsub_j (d.T_le j y.2)⟩ *
          φ ⟨{i, j}, hF⟩ ⟨(x : K), d.L_mono hsub_i (d.T_le i x.2)⟩ := map_mul _ _ _

private noncomputable def delta (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    (φ : ∀ C : ↥𝒮, L C.1 →* Y) (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ) :
    ↥(⨆ i, T i) →* Y :=
  (MonoidHom.noncommPiCoprod (d.phiT φ) (d.phiT_comm hφ)).comp
    (d.torusEquiv.symm).toMonoidHom

omit [DecidableEq I] in
private theorem delta_torusEquiv (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    (φ : ∀ C : ↥𝒮, L C.1 →* Y) (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (x : (i : I) → T i) :
    d.delta φ hφ (d.torusEquiv x) =
      MonoidHom.noncommPiCoprod (d.phiT φ) (d.phiT_comm hφ) x := by
  simp only [delta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

private theorem delta_inclusion (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    (φ : ∀ C : ↥𝒮, L C.1 →* Y) (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (i : I) (x : T i) :
    d.delta φ hφ (Subgroup.inclusion (le_iSup (fun i => T i) i) x) = d.phiT φ i x := by
  rw [show Subgroup.inclusion (le_iSup (fun i => T i) i) x =
      d.torusEquiv (Pi.mulSingle i x) from (d.torusEquiv_mulSingle i x).symm]
  rw [d.delta_torusEquiv, MonoidHom.noncommPiCoprod_mulSingle]

private theorem delta_eq_phi (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    {C : Set I} (hC : C ∈ 𝒮) {x : K} (hxD : x ∈ ⨆ i, T i) (hxL : x ∈ L C) :
    d.delta φ hφ ⟨x, hxD⟩ = φ ⟨C, hC⟩ ⟨x, hxL⟩ := by
  have hxA : x ∈ ⨆ i ∈ C, T i := d.inter C hC (Subgroup.mem_inf.mpr ⟨hxD, hxL⟩)
  rw [iSup_subtype'] at hxA
  let Q : K → Prop := fun y => y ∈ (⨆ i, T i) ∧ y ∈ L C ∧
    ∀ (hyD : y ∈ ⨆ i, T i) (hyL : y ∈ L C),
      d.delta φ hφ ⟨y, hyD⟩ = φ ⟨C, hC⟩ ⟨y, hyL⟩
  have hgen : ∀ (i : {i : I // i ∈ C}), ∀ y ∈ T (i : I), Q y := by
    rintro ⟨i, hiC⟩ y hy
    refine ⟨Subgroup.mem_iSup_of_mem i hy,
      d.L_mono (Set.singleton_subset_iff.mpr hiC) (d.T_le i hy), fun hyD hyL => ?_⟩
    have h1 : d.delta φ hφ ⟨y, hyD⟩ = d.phiT φ i ⟨y, hy⟩ := by
      rw [show (⟨y, hyD⟩ : ↥(⨆ i, T i)) =
        Subgroup.inclusion (le_iSup (fun i => T i) i) ⟨y, hy⟩ from Subtype.ext rfl,
        d.delta_inclusion φ hφ i ⟨y, hy⟩]
    have h2 : d.phiT φ i ⟨y, hy⟩ = φ ⟨C, hC⟩ ⟨y, hyL⟩ :=
      hφ ⟨{i}, d.mem_singleton i⟩ ⟨C, hC⟩ (Set.singleton_subset_iff.mpr hiC)
        (Subgroup.inclusion (d.T_le i) ⟨y, hy⟩) ⟨y, hyL⟩ rfl
    exact h1.trans h2
  have hone : Q 1 := by
    refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun hyD hyL => ?_⟩
    rw [show (⟨(1 : K), hyD⟩ : ↥(⨆ i, T i)) = 1 from Subtype.ext rfl,
      show (⟨(1 : K), hyL⟩ : L C) = 1 from Subtype.ext rfl, map_one, map_one]
  have hmul : ∀ a b : K, Q a → Q b → Q (a * b) := by
    rintro a b ⟨haD, haL, ha⟩ ⟨hbD, hbL, hb⟩
    refine ⟨Subgroup.mul_mem _ haD hbD, Subgroup.mul_mem _ haL hbL, fun habD habL => ?_⟩
    rw [show (⟨a * b, habD⟩ : ↥(⨆ i, T i)) = ⟨a, haD⟩ * ⟨b, hbD⟩ from Subtype.ext rfl,
      show (⟨a * b, habL⟩ : L C) = ⟨a, haL⟩ * ⟨b, hbL⟩ from Subtype.ext rfl,
      map_mul, map_mul, ha haD haL, hb hbD hbL]
  exact (iSup_induction (fun i : {i : I // i ∈ C} => T (i : I)) (C := Q) hxA hgen hone
    hmul).2.2 hxD hxL

private noncomputable def conjOn (d : StripData 𝒮 P L T) {C : Set I} (hC : C ∈ 𝒮)
    (t : ↥(⨆ i, T i)) : L C →* L C where
  toFun l := ⟨(t : K) * (l : K) * (t : K)⁻¹, d.norm C hC t t.2 l l.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' l m := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

private theorem phi_conj_gen (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    {C : Set I} (hC : C ∈ 𝒮) (i : I) (x : T i) {E : Set I} (hEC : E ⊆ C)
    (hE2 : E.ncard ≤ 2) (l : L E) :
    φ ⟨C, hC⟩ (d.conjOn hC ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩
        (Subgroup.inclusion (d.L_mono hEC) l)) =
      d.delta φ hφ ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩ *
        φ ⟨C, hC⟩ (Subgroup.inclusion (d.L_mono hEC) l) *
        (d.delta φ hφ ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩)⁻¹ := by
  have hE : E ∈ 𝒮 := d.small E (by omega)
  have hF : (E ∪ {i} : Set I) ∈ 𝒮 := d.small _ (by
    have h := Set.ncard_union_le E ({i} : Set I)
    rw [Set.ncard_singleton] at h
    omega)
  have hEF : E ⊆ E ∪ {i} := Set.subset_union_left
  have hiF : i ∈ (E ∪ {i} : Set I) := by simp
  let xD : ↥(⨆ i, T i) := ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩
  let xF : L (E ∪ {i}) := ⟨(x : K), d.L_mono (Set.singleton_subset_iff.mpr hiF) (d.T_le i x.2)⟩
  let lF : L (E ∪ {i}) := Subgroup.inclusion (d.L_mono hEF) l
  have hxlE : (x : K) * (l : K) * (x : K)⁻¹ ∈ L E := d.norm E hE xD xD.2 l l.2
  have hxlF : (x : K) * (l : K) * (x : K)⁻¹ ∈ L (E ∪ {i}) := d.norm _ hF xD xD.2 lF lF.2
  have h1 : φ ⟨C, hC⟩ (d.conjOn hC xD (Subgroup.inclusion (d.L_mono hEC) l)) =
      φ ⟨E, hE⟩ ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlE⟩ :=
    (hφ ⟨E, hE⟩ ⟨C, hC⟩ hEC ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlE⟩
      (d.conjOn hC xD (Subgroup.inclusion (d.L_mono hEC) l)) rfl).symm
  have h2 : φ ⟨E, hE⟩ ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlE⟩ =
      φ ⟨E ∪ {i}, hF⟩ ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlF⟩ :=
    hφ ⟨E, hE⟩ ⟨E ∪ {i}, hF⟩ hEF ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlE⟩
      ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlF⟩ rfl
  have h3 : φ ⟨E ∪ {i}, hF⟩ ⟨(x : K) * (l : K) * (x : K)⁻¹, hxlF⟩ =
      φ ⟨E ∪ {i}, hF⟩ xF * φ ⟨E ∪ {i}, hF⟩ lF * (φ ⟨E ∪ {i}, hF⟩ xF)⁻¹ := by
    rw [show (⟨(x : K) * (l : K) * (x : K)⁻¹, hxlF⟩ : L (E ∪ {i})) =
      xF * lF * xF⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
  have hxF : φ ⟨E ∪ {i}, hF⟩ xF = d.delta φ hφ xD := by
    rw [show xD = Subgroup.inclusion (le_iSup (fun i => T i) i) x from Subtype.ext rfl,
      d.delta_inclusion φ hφ i x]
    exact (hφ ⟨{i}, d.mem_singleton i⟩ ⟨E ∪ {i}, hF⟩
      (Set.singleton_subset_iff.mpr hiF) (Subgroup.inclusion (d.T_le i) x) xF rfl).symm
  have hlF : φ ⟨E ∪ {i}, hF⟩ lF = φ ⟨C, hC⟩ (Subgroup.inclusion (d.L_mono hEC) l) :=
    (hφ ⟨E, hE⟩ ⟨E ∪ {i}, hF⟩ hEF l lF rfl).symm.trans
      (hφ ⟨E, hE⟩ ⟨C, hC⟩ hEC l (Subgroup.inclusion (d.L_mono hEC) l) rfl)
  rw [h1, h2, h3, hxF, hlF]

omit [Fintype I] [DecidableEq I] in
private theorem mem_iSup_gen (d : StripData 𝒮 P L T) {C : Set I} (hC : C ∈ 𝒮) {l : K}
    (hl : l ∈ L C) : l ∈ ⨆ (E : {E : Set I // E ⊆ C ∧ E.ncard ≤ 2}), L E.1 := by
  have h : (⨆ (E : Set I) (_ : E ⊆ C) (_ : E.ncard ≤ 2), L E) ≤
      ⨆ (E : {E : Set I // E ⊆ C ∧ E.ncard ≤ 2}), L E.1 := by
    refine iSup_le fun E => iSup_le fun hE => iSup_le fun hE2 => ?_
    exact le_iSup (fun E : {E : Set I // E ⊆ C ∧ E.ncard ≤ 2} => L E.1) ⟨E, hE, hE2⟩
  rw [d.gen C hC] at hl
  exact h hl

private theorem conj_gen_all (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    {C : Set I} (hC : C ∈ 𝒮) (i : I) (x : T i) (l : L C) :
    φ ⟨C, hC⟩ (d.conjOn hC ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩ l) =
      d.delta φ hφ ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩ * φ ⟨C, hC⟩ l *
        (d.delta φ hφ ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩)⁻¹ := by
  let xD : ↥(⨆ i, T i) := ⟨(x : K), Subgroup.mem_iSup_of_mem i x.2⟩
  let Q : K → Prop := fun y => y ∈ L C ∧ ∀ (hy : y ∈ L C),
    φ ⟨C, hC⟩ (d.conjOn hC xD ⟨y, hy⟩) =
      d.delta φ hφ xD * φ ⟨C, hC⟩ ⟨y, hy⟩ * (d.delta φ hφ xD)⁻¹
  have hgen : ∀ (E : {E : Set I // E ⊆ C ∧ E.ncard ≤ 2}), ∀ y ∈ L E.1, Q y := by
    rintro ⟨E, hEC, hE2⟩ y hy
    refine ⟨d.L_mono hEC hy, fun hyC => ?_⟩
    exact d.phi_conj_gen hφ hC i x hEC hE2 ⟨y, hy⟩
  have hone : Q 1 := by
    refine ⟨Subgroup.one_mem _, fun hy => ?_⟩
    have hc : d.conjOn hC xD (⟨(1 : K), hy⟩ : L C) = 1 := by
      rw [show (⟨(1 : K), hy⟩ : L C) = 1 from Subtype.ext rfl, map_one]
    rw [hc, show (⟨(1 : K), hy⟩ : L C) = 1 from Subtype.ext rfl, map_one]
    group
  have hmul : ∀ a b : K, Q a → Q b → Q (a * b) := by
    rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
    refine ⟨Subgroup.mul_mem _ haC hbC, fun habC => ?_⟩
    rw [show (⟨a * b, habC⟩ : L C) = ⟨a, haC⟩ * ⟨b, hbC⟩ from Subtype.ext rfl,
      map_mul, map_mul, map_mul, ha haC, hb hbC]
    group
  exact (iSup_induction (fun E : {E : Set I // E ⊆ C ∧ E.ncard ≤ 2} => L E.1)
    (C := Q) (d.mem_iSup_gen hC l.2) hgen hone hmul).2 l.2

private theorem conj_rule (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    {C : Set I} (hC : C ∈ 𝒮) (t : ↥(⨆ i, T i)) (l : L C) :
    φ ⟨C, hC⟩ (d.conjOn hC t l) =
      d.delta φ hφ t * φ ⟨C, hC⟩ l * (d.delta φ hφ t)⁻¹ := by
  let Q : K → Prop := fun y => y ∈ (⨆ i, T i) ∧
    ∀ (hy : y ∈ ⨆ i, T i) (l : L C),
      φ ⟨C, hC⟩ (d.conjOn hC ⟨y, hy⟩ l) =
        d.delta φ hφ ⟨y, hy⟩ * φ ⟨C, hC⟩ l * (d.delta φ hφ ⟨y, hy⟩)⁻¹
  have hgen : ∀ i, ∀ y ∈ T i, Q y := by
    intro i y hy
    refine ⟨Subgroup.mem_iSup_of_mem i hy, fun hyD l => ?_⟩
    exact d.conj_gen_all hφ hC i ⟨y, hy⟩ l
  have hone : Q 1 := by
    refine ⟨Subgroup.one_mem _, fun hy l => ?_⟩
    have hc : d.conjOn hC (⟨(1 : K), hy⟩ : ↥(⨆ i, T i)) l = l := by
      apply Subtype.ext
      simp only [conjOn, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
      group
    rw [hc, show (⟨(1 : K), hy⟩ : ↥(⨆ i, T i)) = 1 from Subtype.ext rfl, map_one]
    group
  have hmul : ∀ a b : K, Q a → Q b → Q (a * b) := by
    rintro a b ⟨haD, ha⟩ ⟨hbD, hb⟩
    refine ⟨Subgroup.mul_mem _ haD hbD, fun habD l => ?_⟩
    have e : d.conjOn hC (⟨a * b, habD⟩ : ↥(⨆ i, T i)) l =
        d.conjOn hC (⟨a, haD⟩ : ↥(⨆ i, T i))
          (d.conjOn hC (⟨b, hbD⟩ : ↥(⨆ i, T i)) l) := by
      apply Subtype.ext
      simp only [conjOn, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
      group
    have eδ : d.delta φ hφ (⟨a * b, habD⟩ : ↥(⨆ i, T i)) =
        d.delta φ hφ ⟨a, haD⟩ * d.delta φ hφ ⟨b, hbD⟩ := by
      rw [show (⟨a * b, habD⟩ : ↥(⨆ i, T i)) = ⟨a, haD⟩ * ⟨b, hbD⟩ from Subtype.ext rfl,
        map_mul]
    rw [e, ha haD (d.conjOn hC ⟨b, hbD⟩ l), hb hbD l, eδ]
    group
  exact (iSup_induction (fun i => T i) (C := Q) t.2 hgen hone hmul).2 t.2 l

private noncomputable def hatFun (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (C : ↥𝒮) (x : P C.1) : Y :=
  let w := d.prod C.1 C.2 x.1 x.2
  d.delta φ hφ ⟨w.choose, w.choose_spec.1⟩ *
    φ C ⟨w.choose_spec.2.choose, w.choose_spec.2.choose_spec.1⟩

private theorem hatFun_apply (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (C : ↥𝒮) {x : K} (hx : x ∈ P C.1) (t : ↥(⨆ i, T i)) (l : L C.1)
    (hxt : x = (t : K) * (l : K)) :
    d.hatFun hφ C ⟨x, hx⟩ = d.delta φ hφ t * φ C l := by
  let w := d.prod C.1 C.2 x hx
  let s : K := w.choose
  have hsD : s ∈ ⨆ i, T i := w.choose_spec.1
  let m : K := w.choose_spec.2.choose
  have hmL : m ∈ L C.1 := w.choose_spec.2.choose_spec.1
  have hxm : x = s * m := w.choose_spec.2.choose_spec.2
  change d.delta φ hφ ⟨s, hsD⟩ * φ C ⟨m, hmL⟩ = d.delta φ hφ t * φ C l
  have hsm : s * m = (t : K) * (l : K) := by rw [← hxm, hxt]
  have hz_eq : s⁻¹ * (t : K) = m * (l : K)⁻¹ := by
    calc s⁻¹ * (t : K) = s⁻¹ * ((t : K) * (l : K)) * (l : K)⁻¹ := by group
      _ = s⁻¹ * (s * m) * (l : K)⁻¹ := by rw [← hsm]
      _ = m * (l : K)⁻¹ := by group
  have hzD : s⁻¹ * (t : K) ∈ ⨆ i, T i :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hsD) t.2
  have hzL : s⁻¹ * (t : K) ∈ L C.1 := by
    rw [hz_eq]
    exact Subgroup.mul_mem _ hmL (Subgroup.inv_mem _ l.2)
  have hzδ : d.delta φ hφ ⟨s⁻¹ * (t : K), hzD⟩ = φ C ⟨s⁻¹ * (t : K), hzL⟩ :=
    d.delta_eq_phi hφ C.2 hzD hzL
  have hδ : d.delta φ hφ t =
      d.delta φ hφ ⟨s, hsD⟩ * d.delta φ hφ ⟨s⁻¹ * (t : K), hzD⟩ := by
    conv_lhs => rw [show t = (⟨s, hsD⟩ : ↥(⨆ i, T i)) * ⟨s⁻¹ * (t : K), hzD⟩
      from Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group)]
    rw [map_mul]
  have hφz : φ C ⟨s⁻¹ * (t : K), hzL⟩ = φ C ⟨m, hmL⟩ * (φ C l)⁻¹ := by
    rw [show (⟨s⁻¹ * (t : K), hzL⟩ : L C.1) = ⟨m, hmL⟩ * l⁻¹ from Subtype.ext hz_eq,
      map_mul, map_inv]
  calc d.delta φ hφ ⟨s, hsD⟩ * φ C ⟨m, hmL⟩
      = d.delta φ hφ ⟨s, hsD⟩ * (φ C ⟨m, hmL⟩ * (φ C l)⁻¹) * φ C l := by group
    _ = d.delta φ hφ ⟨s, hsD⟩ * φ C ⟨s⁻¹ * (t : K), hzL⟩ * φ C l := by rw [hφz]
    _ = d.delta φ hφ ⟨s, hsD⟩ * d.delta φ hφ ⟨s⁻¹ * (t : K), hzD⟩ * φ C l := by rw [hzδ]
    _ = d.delta φ hφ t * φ C l := by rw [← hδ]

private noncomputable def hat (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ) (C : ↥𝒮) :
    P C.1 →* Y where
  toFun := d.hatFun hφ C
  map_one' := by
    have h := d.hatFun_apply hφ C (Subgroup.one_mem (P C.1)) 1 1 (by simp)
    rw [show (⟨(1 : K), Subgroup.one_mem (P C.1)⟩ : P C.1) = 1 from Subtype.ext rfl] at h
    simpa using h
  map_mul' x y := by
    change d.hatFun hφ C (x * y) = d.hatFun hφ C x * d.hatFun hφ C y
    obtain ⟨tx, htxD, lx, hlxL, hxl⟩ := d.prod C.1 C.2 x.1 x.2
    obtain ⟨ty, htyD, ly, hlyL, hyl⟩ := d.prod C.1 C.2 y.1 y.2
    set txD : ↥(⨆ i, T i) := ⟨tx, htxD⟩
    set tyD : ↥(⨆ i, T i) := ⟨ty, htyD⟩
    set lxL : L C.1 := ⟨lx, hlxL⟩
    set lyL : L C.1 := ⟨ly, hlyL⟩
    have hx_eq : (x : K) = (txD : K) * (lxL : K) := hxl
    have hy_eq : (y : K) = (tyD : K) * (lyL : K) := hyl
    set l' : L C.1 := d.conjOn C.2 tyD⁻¹ lxL * lyL
    have hl'_eq : (l' : K) = (tyD : K)⁻¹ * (lxL : K) * (tyD : K) * (lyL : K) := by
      simp only [l', Subgroup.coe_mul, Subgroup.coe_inv, conjOn, MonoidHom.coe_mk,
        OneHom.coe_mk]
      group
    have hxy_eq : ((x * y : P C.1) : K) =
        ((txD * tyD : ↥(⨆ i, T i)) : K) * (l' : K) := by
      rw [Subgroup.coe_mul, hx_eq, hy_eq, hl'_eq, Subgroup.coe_mul]
      group
    have h1 := d.hatFun_apply hφ C (x * y).2 (txD * tyD) l' hxy_eq
    have h2 := d.hatFun_apply hφ C x.2 txD lxL hx_eq
    have h3 := d.hatFun_apply hφ C y.2 tyD lyL hy_eq
    rw [h1, h2, h3]
    have hconj : φ C l' = d.delta φ hφ tyD⁻¹ * φ C lxL *
        (d.delta φ hφ tyD⁻¹)⁻¹ * φ C lyL := by
      rw [show l' = d.conjOn C.2 tyD⁻¹ lxL * lyL from rfl, map_mul,
        d.conj_rule hφ C.2 tyD⁻¹ lxL]
    rw [hconj, map_mul, map_inv]
    group

private theorem hat_apply (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (C : ↥𝒮) {x : K} (hx : x ∈ P C.1) (t : ↥(⨆ i, T i)) (l : L C.1)
    (hxt : x = (t : K) * (l : K)) :
    d.hat hφ C ⟨x, hx⟩ = d.delta φ hφ t * φ C l :=
  d.hatFun_apply hφ C hx t l hxt

private theorem hat_compatible (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ) :
    IsCompatible (fun C : ↥𝒮 => P C.1) (fun C => d.hat hφ C) := by
  intro C C' hCC' x y hxy
  obtain ⟨t, htD, l, hlL, hxl⟩ := d.prod C.1 C.2 x.1 x.2
  set tD : ↥(⨆ i, T i) := ⟨t, htD⟩
  set lL : L C.1 := ⟨l, hlL⟩
  have hx_eq : (x : K) = (tD : K) * (lL : K) := hxl
  have hyl : (lL : K) ∈ L C'.1 := d.L_mono hCC' hlL
  have hyl' : (tD : K) * (lL : K) ∈ P C'.1 := by
    rw [← hx_eq, hxy]
    exact y.2
  have h1 := d.hat_apply hφ C x.2 tD lL hx_eq
  have h2 := d.hat_apply hφ C' y.2 tD (Subgroup.inclusion (d.L_mono hCC') lL)
    (by rw [Subgroup.coe_inclusion, ← hxy]; exact hx_eq)
  rw [h1, h2]
  congr 1
  exact hφ C C' hCC' lL (Subgroup.inclusion (d.L_mono hCC') lL) rfl

private theorem hat_extends (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    (C : ↥𝒮) (l : L C.1) :
    d.hat hφ C (Subgroup.inclusion (d.L_le C.1 C.2) l) = φ C l := by
  have h := d.hat_apply hφ C (d.L_le C.1 C.2 l.2) 1 l (by simp)
  have he : (⟨(l : K), d.L_le C.1 C.2 l.2⟩ : P C.1) =
      Subgroup.inclusion (d.L_le C.1 C.2) l := Subtype.ext rfl
  rw [he] at h
  simpa using h

private theorem psi_eq_delta (d : StripData 𝒮 P L T) {Y : Type w} [Group Y]
    {φ : ∀ C : ↥𝒮, L C.1 →* Y} (hφ : IsCompatible (fun C : ↥𝒮 => L C.1) φ)
    {ψ' : K →* Y} (hψ' : ∀ C (x : L C.1), ψ' x = φ C x) (t : ↥(⨆ i, T i)) :
    ψ' (t : K) = d.delta φ hφ t := by
  let Q : K → Prop := fun y => y ∈ (⨆ i, T i) ∧
    ∀ (hy : y ∈ ⨆ i, T i), ψ' y = d.delta φ hφ ⟨y, hy⟩
  have hgen : ∀ i, ∀ y ∈ T i, Q y := by
    intro i y hy
    refine ⟨Subgroup.mem_iSup_of_mem i hy, fun hyD => ?_⟩
    have h1 : ψ' y = d.phiT φ i ⟨y, hy⟩ :=
      hψ' ⟨{i}, d.mem_singleton i⟩ (Subgroup.inclusion (d.T_le i) ⟨y, hy⟩)
    have h2 : d.delta φ hφ ⟨y, hyD⟩ = d.phiT φ i ⟨y, hy⟩ := by
      rw [show (⟨y, hyD⟩ : ↥(⨆ i, T i)) =
        Subgroup.inclusion (le_iSup (fun i => T i) i) ⟨y, hy⟩ from Subtype.ext rfl,
        d.delta_inclusion φ hφ i ⟨y, hy⟩]
    rw [h1, h2]
  have hone : Q 1 := by
    refine ⟨Subgroup.one_mem _, fun hy => ?_⟩
    rw [show (⟨(1 : K), hy⟩ : ↥(⨆ i, T i)) = 1 from Subtype.ext rfl, map_one, map_one]
  have hmul : ∀ a b : K, Q a → Q b → Q (a * b) := by
    rintro a b ⟨haD, ha⟩ ⟨hbD, hb⟩
    refine ⟨Subgroup.mul_mem _ haD hbD, fun habD => ?_⟩
    rw [show (⟨a * b, habD⟩ : ↥(⨆ i, T i)) = ⟨a, haD⟩ * ⟨b, hbD⟩ from Subtype.ext rfl,
      map_mul, map_mul, ha haD, hb hbD]
  exact (iSup_induction (fun i => T i) (C := Q) t.2 hgen hone hmul).2 t.2

theorem isUniversalCompletion (d : StripData 𝒮 P L T)
    (hP : IsUniversalCompletion.{u, v, w} (fun C : ↥𝒮 => P C.1)) :
    IsUniversalCompletion.{u, v, w} (fun C : ↥𝒮 => L C.1) := by
  intro Y _inst φ hφ
  obtain ⟨ψ, hψ, huniq⟩ := hP Y (fun C => d.hat hφ C) (d.hat_compatible hφ)
  refine ⟨ψ, ?_, ?_⟩
  · intro C x
    rw [← d.hat_extends hφ C x]
    exact hψ C (Subgroup.inclusion (d.L_le C.1 C.2) x)
  · intro ψ' hψ'
    refine huniq ψ' ?_
    intro C x
    obtain ⟨t, htD, l, hlL, hxl⟩ := d.prod C.1 C.2 x.1 x.2
    set tD : ↥(⨆ i, T i) := ⟨t, htD⟩
    set lL : L C.1 := ⟨l, hlL⟩
    have hx' : (x : K) = (tD : K) * (lL : K) := hxl
    have hhat : d.hat hφ C x = d.delta φ hφ tD * φ C lL := by
      simpa using d.hat_apply hφ C x.2 tD lL hx'
    rw [hhat]
    have hpsi : ψ' (x : K) = d.delta φ hφ tD * φ C lL := by
      rw [hx', map_mul, d.psi_eq_delta hφ hψ' tD]
      have hl : ψ' (lL : K) = φ C lL := hψ' C lL
      rw [hl]
    rw [hpsi]

end StripData

end CFSG.LieType.CurtisTits
