module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Cover
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped Pointwise

section Geometry

variable {A : Type} [Group A] [Finite A]

theorem cover_sylow_geometry (c : L34Cover A) (T : Sylow 2 A) :
    ∃ H : Fin 2 → Subgroup A, (∀ i, H i ≤ T) ∧
      (∀ i, ∀ x ∈ H i, x ^ 2 = 1) ∧ (∀ i, Nat.card (H i) = 16 * Nat.card c.π.ker) ∧
      (∀ x ∈ (T : Subgroup A), x ^ 2 = 1 → x ∈ H 0 ∨ x ∈ H 1) ∧
      (∀ U : Subgroup A, U ≤ T → (∀ x ∈ U, x ^ 2 = 1) → U ≤ H 0 ∨ U ≤ H 1) ∧
      (∀ i, ∀ x ∈ H i, x ∉ H 0 ⊓ H 1 →
        (T : Subgroup A) ⊓ centralizer ({x} : Set A) = H i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N
  set S : Sylow 2 (A ⧸ N) := T.mapSurjective (QuotientGroup.mk'_surjective N)
  have hS : (S : Subgroup (A ⧸ N)) = (T : Subgroup A).map p := Sylow.coe_mapSurjective _ _
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers
    c.card_k c.π c.surj c.ker_le_center c.elem
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (A ⧸ N) S₀ S
  set π' := c.π.comp (MulAut.conj x⁻¹).toMonoidHom
  have hker' : π'.ker = c.π.ker := by
    ext y
    simp only [π', MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker]
    constructor
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x
      simpa [mul_assoc] using this
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x⁻¹
      simpa [mul_assoc] using this
  have hsurj' : Function.Surjective π' := c.surj.comp (MulAut.conj x⁻¹).surjective
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  have hT' : (projUnip c.k).comap π' = (S : Subgroup (A ⧸ N)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀]
    ext y
    rw [mem_pointwise_smul_iff_inv_smul_mem, mem_comap, mem_comap]
    simp [π', MulAut.smul_def]
  obtain ⟨hH, -, -, -, -, -, -, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ, -, -, hσ, -⟩, -⟩ := hlevi 0
  obtain ⟨⟨-, -, -, hZ, -, -, hmax, hsq, -, hcent, -⟩, -, -⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ hσ
  set H' : Fin 2 → Subgroup (A ⧸ N) := fun i => (projRad c.k i).comap π'
  set H : Fin 2 → Subgroup A := fun i => (T : Subgroup A) ⊓ (H' i).comap p
  have hpT : ∀ y ∈ (T : Subgroup A), p y ∈ (projUnip c.k).comap π' := fun y hy => by
    rw [hT', hS]
    exact ⟨y, hy, rfl⟩
  have hH'T : ∀ i, H' i ≤ (projUnip c.k).comap π' := fun i =>
    Subgroup.comap_mono (projRad_le_projUnip i)
  have hH'S : ∀ i, H' i ≤ (T : Subgroup A).map p := fun i => by
    rw [← hS, ← hT']
    exact hH'T i
  have hHmap : ∀ i, (H i).map p = H' i := fun i => map_inf_comap_eq (hH'S i)
  have hHT : ∀ i, H i ≤ T := fun i => inf_le_left
  refine ⟨H, hHT, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i h hh
    have := (hH i).1
    have h2 : p h ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := H' i) _ hh.2
    rw [← map_pow, ← map_one p] at h2
    exact mk'_injOn T.2 hN (T.pow_mem hh.1 2) (one_mem _) h2
  · intro i
    rw [← card_map_mk'_of_le T.2 hN (hHT i), hHmap, (hH i).2, hker']
  ·
    intro y hy hy2
    have hpy : (p y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    rcases (hsq (p y) (hpT y hy)).mp hpy with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  ·
    intro U hUT hU
    have hUe : CFSG.IsElementaryAbelian 2 (U.map p) := by
      refine isElementaryAbelian_of_sq_eq_one ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, hU u hu, map_one]
    have hUle : U.map p ≤ (projUnip c.k).comap π' := by
      rintro _ ⟨u, hu, rfl⟩
      exact hpT u (hUT hu)
    rcases hmax (U.map p) hUle hUe with h | h
    · exact Or.inl fun u hu => ⟨hUT hu, h ⟨u, hu, rfl⟩⟩
    · exact Or.inr fun u hu => ⟨hUT hu, h ⟨u, hu, rfl⟩⟩
  ·
    intro i y hy hyZ
    have hpy : p y ∉ (projCenterW c.k).comap π' := by
      intro h
      rw [hZ] at h
      exact hyZ ⟨⟨hy.1, h.1⟩, ⟨hy.1, h.2⟩⟩
    have hc := hcent i (p y) hy.2 hpy
    apply le_antisymm
    · rintro t ⟨htT, htc⟩
      refine ⟨htT, ?_⟩
      have : p t ∈ (projUnip c.k).comap π' ⊓ centralizer {p y} := by
        refine ⟨hpT t htT, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp htc]
      rw [hc] at this
      exact this
    · rintro t ⟨htT, htH⟩
      refine ⟨htT, mem_centralizer_singleton_iff.mpr ?_⟩
      have : p t ∈ (projUnip c.k).comap π' ⊓ centralizer {p y} := by
        rw [hc]
        exact htH
      have hcm := mem_centralizer_singleton_iff.mp this.2
      rw [← map_mul, ← map_mul] at hcm
      exact mk'_injOn T.2 hN (T.mul_mem htT hy.1) (T.mul_mem hy.1 htT) hcm

end Geometry

section Frame

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem Frame.sq_eq_one_of_mem_center (hF : Frame G A A R g E F) {z : ↥A}
    (hz : z ∈ center ↥A) (h2 : IsPGroup 2 (zpowers z)) : z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzC : (z : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun a ha =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
  have h2' : IsPGroup 2 (zpowers (z : G)) := by
    have := h2.map A.subtype
    rwa [MonoidHom.map_zpowers] at this
  have hRz : R ≤ normalizer ((zpowers (z : G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [le_centralizer_iff, zpowers_le]
    exact mem_centralizer_iff.mpr fun r hr =>
      ((mem_centralizer_iff.mp (hF.sylowR.le hr)) z z.2).symm
  have hP := hF.sylowR.isPGroup.to_sup_of_normal_right' h2' hRz
  have heq := hF.sylowR.eq_of_le le_sup_left (sup_le hF.sylowR.le (zpowers_le.mpr hzC)) hP
  have hzR : (z : G) ∈ R := heq ▸ mem_sup_right (mem_zpowers _)
  exact Subtype.ext (by simpa using hF.elemR.2 _ hzR)

omit [Finite G] in
theorem map_subtype_centralizer_singleton (x : ↥A) :
    (centralizer ({x} : Set ↥A)).map A.subtype = A ⊓ centralizer ({(x : G)} : Set G) := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hy, hyx⟩
    exact ⟨⟨y, hy⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hyx)), rfl⟩

theorem Frame.l34Cover (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) :
    Nonempty (L34Cover ↥A) :=
  exists_l34Cover hF.quasisimple.1 hL hF.quasisimple.2 fun _ hz h2 =>
    hF.sq_eq_one_of_mem_center hz h2

theorem Frame.sup_inf_center_eq (hF : Frame G A A R g E F) (hRA : R ≤ A) :
    (E ⊔ F) ⊓ (center ↥A).map A.subtype = R := by
  have hRZ : R ≤ (center ↥A).map A.subtype := fun r hr =>
    ⟨⟨r, hRA hr⟩, mem_center_iff.mpr fun a =>
      Subtype.ext ((mem_centralizer_iff.mp (hF.sylowR.le hr)) a a.2), rfl⟩
  have hZC : (center ↥A).map A.subtype ≤ centralizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_centralizer_iff.mpr fun a ha => congrArg Subtype.val ((mem_center_iff.mp hy) ⟨a, ha⟩)
  exact hF.sylowR.eq_of_le (le_inf (hF.R_le_E.trans le_sup_left) hRZ) (inf_le_right.trans hZC)
    (hF.sylow.isPGroup.to_le inf_le_left)

theorem Frame.sylow_geometry (hF : Frame G A A R g E F) (hRA : R ≤ A)
    (hL : TypeL34 (rankTwoQuot A)) :
    (∀ x ∈ E ⊔ F, x ^ 2 = 1 → x ∈ E ∨ x ∈ F) ∧
    (∀ U : Subgroup G, U ≤ E ⊔ F → (∀ x ∈ U, x ^ 2 = 1) → U ≤ E ∨ U ≤ F) ∧
    (∀ x ∈ E, x ∉ F → (E ⊔ F) ⊓ centralizer ({x} : Set G) = E) ∧
    (∀ x ∈ F, x ∉ E → (E ⊔ F) ⊓ centralizer ({x} : Set G) = F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := hF.l34Cover hL
  have hAR : A ⊔ R = A := sup_eq_left.mpr hRA
  have hEA : E ≤ A := hAR ▸ hF.E_le
  have hFA : F ≤ A := hAR ▸ hF.F_le
  have hSA : E ⊔ F ≤ A := sup_le hEA hFA
  obtain ⟨T, hT⟩ : IsSylowOf 2 (E ⊔ F) A := hAR ▸ hF.sylow
  obtain ⟨H, hHT, hH2, hHc, hinv, hel, hcen⟩ := cover_sylow_geometry c T
  have hker : Nat.card c.π.ker = 4 := by
    rw [card_ker_eq c T, ← card_map_of_injective A.subtype_injective,
      map_inf _ _ _ A.subtype_injective, hT, hF.sup_inf_center_eq hRA, hF.cardR]
  have hmapE : (E.subgroupOf A).map A.subtype = E := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hEA]
  have hmapF : (F.subgroupOf A).map A.subtype = F := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hFA]
  have hle : ∀ {U : Subgroup G}, U ≤ E ⊔ F → U.subgroupOf A ≤ T := by
    intro U hU
    rw [← map_le_map_iff_of_injective A.subtype_injective, hT, subgroupOf_map_subtype]
    exact inf_le_left.trans hU
  have hsq : ∀ {U : Subgroup G}, (∀ x ∈ U, x ^ 2 = 1) → ∀ x ∈ U.subgroupOf A, x ^ 2 = 1 :=
    fun hU x hx => Subtype.ext (by simpa using hU _ hx)
  have hEsq : ∀ x ∈ E, x ^ 2 = 1 := hF.elemE.2
  have hFsq : ∀ x ∈ F, x ^ 2 = 1 := hF.elemF.2
  have hcardE : Nat.card (E.subgroupOf A) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv, hF.cardE]
  have hcardF : Nat.card (F.subgroupOf A) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFA).toEquiv, hF.cardF]
  have hHc' : ∀ i, Nat.card (H i) = 64 := fun i => by rw [hHc, hker]
  have heqH : ∀ {U : Subgroup ↥A}, Nat.card U = 64 → U ≤ H 0 ∨ U ≤ H 1 → U = H 0 ∨ U = H 1 := by
    intro U hU h
    rcases h with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hU, hHc']))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hU, hHc']))
  have hE := heqH hcardE (hel _ (hle le_sup_left) (hsq hEsq))
  have hF' := heqH hcardF (hel _ (hle le_sup_right) (hsq hFsq))
  have hne : E.subgroupOf A ≠ F.subgroupOf A := fun h => hF.ne (by rw [← hmapE, h, hmapF])
  have hEF : (H 0 = E.subgroupOf A ∧ H 1 = F.subgroupOf A) ∨
      (H 0 = F.subgroupOf A ∧ H 1 = E.subgroupOf A) := by
    rcases hE with h1 | h1 <;> rcases hF' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
    · exact absurd (h1.trans h2.symm) hne
  have hmem : ∀ {x : G} (hx : x ∈ E ⊔ F), (⟨x, hSA hx⟩ : A) ∈ (T : Subgroup A) := fun hx =>
    hle (U := zpowers _) (zpowers_le.mpr hx) (show (⟨_, hSA hx⟩ : A) ∈ (zpowers _).subgroupOf A
      from mem_zpowers _)
  have hcentG : ∀ {x : G} (hx : x ∈ E ⊔ F) (i : Fin 2), (⟨x, hSA hx⟩ : A) ∈ H i →
      (⟨x, hSA hx⟩ : A) ∉ H 0 ⊓ H 1 →
        (E ⊔ F) ⊓ centralizer ({x} : Set G) = (H i).map A.subtype := by
    intro x hx i hxi hxZ
    rw [← hcen i _ hxi hxZ, map_inf _ _ _ A.subtype_injective, hT,
      map_subtype_centralizer_singleton, ← inf_assoc, inf_eq_left.mpr hSA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx2
    have := hinv _ (hmem hx) (Subtype.ext (by simpa using hx2))
    rcases hEF with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] at this <;>
      rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
  · intro U hU hU2
    have := hel _ (hle hU) (hsq hU2)
    have key : ∀ {X : Subgroup G}, X ≤ A → U.subgroupOf A ≤ X.subgroupOf A → U ≤ X := by
      intro X hX h u hu
      exact h (show (⟨u, hSA (hU hu)⟩ : A) ∈ U.subgroupOf A from hu)
    rcases hEF with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] at this <;> rcases this with h | h
    · exact Or.inl (key hEA h)
    · exact Or.inr (key hFA h)
    · exact Or.inr (key hFA h)
    · exact Or.inl (key hEA h)
  · intro x hx hxF
    have hxS : x ∈ E ⊔ F := mem_sup_left hx
    have hxE' : (⟨x, hSA hxS⟩ : A) ∈ E.subgroupOf A := hx
    have hxF' : (⟨x, hSA hxS⟩ : A) ∉ F.subgroupOf A := hxF
    rcases hEF with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hcentG hxS 0 (h0 ▸ hxE') (fun h => hxF' (h1 ▸ h.2)), h0, hmapE]
    · rw [hcentG hxS 1 (h1 ▸ hxE') (fun h => hxF' (h0 ▸ h.1)), h1, hmapE]
  · intro x hx hxE
    have hxS : x ∈ E ⊔ F := mem_sup_right hx
    have hxF' : (⟨x, hSA hxS⟩ : A) ∈ F.subgroupOf A := hx
    have hxE' : (⟨x, hSA hxS⟩ : A) ∉ E.subgroupOf A := hxE
    rcases hEF with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hcentG hxS 1 (h1 ▸ hxF') (fun h => hxE' (h0 ▸ h.1)), h1, hmapF]
    · rw [hcentG hxS 0 (h0 ▸ hxF') (fun h => hxE' (h1 ▸ h.2)), h0, hmapF]

theorem Frame.le_or_le_of_isElemAbelian (hF : Frame G A A R g E F) (hRA : R ≤ A)
    (hL : TypeL34 (rankTwoQuot A)) {U : Subgroup G} (hU : U ≤ E ⊔ F) (hUe : IsElemAbelian 2 U) :
    U ≤ E ∨ U ≤ F :=
  (hF.sylow_geometry hRA hL).2.1 U hU hUe.2

theorem Frame.eq_or_eq_of_isElemAbelian (hF : Frame G A A R g E F) (hRA : R ≤ A)
    (hL : TypeL34 (rankTwoQuot A)) {U : Subgroup G} (hU : U ≤ E ⊔ F) (hUe : IsElemAbelian 2 U)
    (h64 : Nat.card U = 64) : U = E ∨ U = F := by
  rcases hF.le_or_le_of_isElemAbelian hRA hL hU hUe with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [h64, hF.cardE]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [h64, hF.cardF]))

omit [Finite G] in
theorem map_subtype_centralizer (T : Subgroup ↥A) :
    (centralizer (T : Set ↥A)).map A.subtype = A ⊓ centralizer ((T.map A.subtype : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy t ht)
  · rintro ⟨hy, hyc⟩
    refine ⟨⟨y, hy⟩, mem_centralizer_iff.mpr fun t ht => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.mp hyc _ ⟨t, ht, rfl⟩

theorem Frame.commutator_eq (hF : Frame G A A R g E F) (hRA : R ≤ A)
    (hL : TypeL34 (rankTwoQuot A)) : ⁅E ⊔ F, E ⊔ F⁆ = E ⊓ F := by
  obtain ⟨c⟩ := hF.l34Cover hL
  have hAR : A ⊔ R = A := sup_eq_left.mpr hRA
  have hSA : E ⊔ F ≤ A := sup_le (hAR ▸ hF.E_le) (hAR ▸ hF.F_le)
  obtain ⟨T, hT⟩ : IsSylowOf 2 (E ⊔ F) A := hAR ▸ hF.sylow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcomm⟩ := sylow_structure c T
  have h := congrArg (Subgroup.map A.subtype) (hcomm hF.quasisimple.1)
  rw [map_commutator, hT, centerIn, map_inf _ _ _ A.subtype_injective, hT,
    map_subtype_centralizer, hT, ← inf_assoc, inf_eq_left.mpr hSA] at h
  rw [h, hF.inf_eq_center]
  rfl

end Frame

end CFSG.ComponentClassification.AS81
