module

public import CFSG.ClassicalInvolution.Q3.Q3AM289A02
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
public import CFSG.ClassicalInvolution.Asc77.AscT8V11

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S3A

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Congr

variable {H : Type} [Group H]

@[expose] def inducedAutCongr {L₁ L₂ : Subgroup H} (h : L₁ = L₂) :
    ↥(inducedAutOn L₁) ≃* ↥(inducedAutOn L₂) := by
  subst h
  exact MulEquiv.refl _

theorem inducedAutCongr_apply {L₁ L₂ : Subgroup H} (h : L₁ = L₂) (a : H)
    (ha₁ : a ∈ Subgroup.normalizer (L₁ : Set H)) (ha₂ : a ∈ Subgroup.normalizer (L₂ : Set H)) :
    inducedAutCongr h (toInducedAutOn L₁ ⟨a, ha₁⟩) = toInducedAutOn L₂ ⟨a, ha₂⟩ := by
  subst h
  rfl

theorem mk'_mem_center (N : Subgroup H) [N.Normal] {e : H} (he : e ∈ Subgroup.center H) :
    QuotientGroup.mk' N e ∈ Subgroup.center (H ⧸ N) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective N g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp he g₀]

variable {L N : Subgroup H} [N.Normal]

@[expose] noncomputable def inducedAutQuotEquiv' {L' : Subgroup (H ⧸ N)} (hNL : N ≤ L)
    (hNc : N ≤ Subgroup.center H) [Group.IsPerfect ↥L]
    (hL' : L' = L.map (QuotientGroup.mk' N)) : ↥(inducedAutOn L) ≃* ↥(inducedAutOn L') :=
  (inducedAutQuotEquiv hNL hNc).trans (inducedAutCongr hL'.symm)

theorem inducedAutQuotEquiv'_apply {L' : Subgroup (H ⧸ N)} (hNL : N ≤ L)
    (hNc : N ≤ Subgroup.center H) [Group.IsPerfect ↥L]
    (hL' : L' = L.map (QuotientGroup.mk' N)) (n : H) (hn : n ∈ Subgroup.normalizer (L : Set H))
    (hn' : QuotientGroup.mk' N n ∈ Subgroup.normalizer (L' : Set (H ⧸ N))) :
    inducedAutQuotEquiv' hNL hNc hL' (toInducedAutOn L ⟨n, hn⟩) =
      toInducedAutOn L' ⟨QuotientGroup.mk' N n, hn'⟩ := by
  unfold inducedAutQuotEquiv'
  rw [MulEquiv.trans_apply, inducedAutQuotEquiv_apply hNL hNc n hn]
  exact inducedAutCongr_apply hL'.symm _ _ hn'

theorem alphaOf_eq_bot_of_quotient' {L' : Subgroup (H ⧸ N)} (hNL : N ≤ L)
    (hNc : N ≤ Subgroup.center H) [Group.IsPerfect ↥L]
    (hL' : L' = L.map (QuotientGroup.mk' N)) (A : Subgroup ↥(inducedAutOn L))
    (h : alphaOf (A.map (inducedAutQuotEquiv' hNL hNc hL').toMonoidHom) = ⊥) : alphaOf A = ⊥ := by
  have h1 := ExactLayer.alphaOf_map_equiv (inducedAutQuotEquiv' hNL hNc hL') A
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (inducedAutQuotEquiv' hNL hNc hL').injective).mp h1.symm

end Congr

section Twin

variable {t : StatedLieTag} {M : LieUniversal}

theorem alphaOf_inducedImage_eq_bot_of_twin (hTW : TwinSqAlphaOn t M)
    [hperf : Group.IsPerfect M.K] {H : Type} [Group H] [Finite H] (ψ : M.K →* H)
    (hker : ψ.ker ≤ Subgroup.center M.K) {L : Subgroup H} (hL : L = ψ.range)
    {R R' : Subgroup M.K} (hR : R ∈ fundamentalSubgroups t M.D)
    (hR' : R' ∈ fundamentalSubgroups t M.D) (hne : R ≠ R') (hcomm : Commutes R R')
    {y y' : M.K} (hy : y ∈ R) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hy' : y' ∈ R') (hy'2 : y' * y' = 1) (hy'1 : y' ≠ 1)
    {c : H} (hcc : c ∈ Subgroup.center H) (hc : ψ y * ψ y' = c)
    {k : M.K} (hk : k ∈ R') (hkk : ψ k * ψ k = ψ y')
    {w : H} (hw2 : w * w = 1) (hwN : w ∈ Subgroup.normalizer (L : Set H))
    (hwR : ∀ r ∈ R, w * ψ r * w⁻¹ = ψ r)
    (hwR' : ∀ r ∈ R', w * ψ r * w⁻¹ = ψ k * ψ r * (ψ k)⁻¹)
    {E : Subgroup H} (hyE : ψ y ∈ E) (hwE : w ∈ E)
    (hE : ∀ e ∈ E, ∃ d ∈ ({1, ψ y, w, ψ y * w} : Set H), ∃ e' ∈ Subgroup.center H,
      e = d * e') :
    alphaOf (inducedImage L E) = ⊥ := by
  subst hL
  classical
  set N : Subgroup H := Subgroup.zpowers c with hNdef
  have hNc : N ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hcc
  have hNnorm : N.Normal := Subgroup.normal_of_le_center hNc
  have hcL : c ∈ ψ.range := ⟨y * y', by rw [map_mul, hc]⟩
  have hNL : N ≤ ψ.range := Subgroup.zpowers_le.mpr hcL
  have hLperf : Group.IsPerfect ↥ψ.range :=
    Q3NM.isPerfect_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set ψ' : M.K →* H ⧸ N := π.comp ψ with hψ'
  have hrange : ψ'.range = ψ.range.map π := MonoidHom.range_comp π ψ
  have hψ'y : ψ' y' * ψ' y' = 1 := by rw [← map_mul, hy'2, map_one]
  have hyy : ψ y' * ψ y = c := by
    rw [← hc, ← map_mul, ← map_mul, hcomm y hy y' hy']
  have hker' : ψ'.ker ≤ Subgroup.center M.K := by
    intro s hs
    have h1 : ψ s ∈ N := by
      have : π (ψ s) = 1 := hs
      exact (QuotientGroup.eq_one_iff _).mp this
    exact T8V.mem_center_of_map_mem_center hperf ψ hker (hNc h1)
  have hsame : ψ' y' = ψ' y := by
    have hinv : (ψ y')⁻¹ = ψ y' := inv_eq_of_mul_eq_one_right (by rw [← map_mul, hy'2, map_one])
    have h : (((ψ y' : H) : H ⧸ N)) = (((ψ y : H) : H ⧸ N)) := by
      rw [QuotientGroup.eq, hinv, hyy]
      exact Subgroup.mem_zpowers c
    exact h
  have hpair : TwinPairOn t M ψ' R' R y' y :=
    { ker := hker', mem := hR', mem' := hR, ne := hne.symm,
      comm := fun a ha b hb => (hcomm b hb a ha).symm,
      hx := hy', hx2 := hy'2, hx1 := hy'1, hx' := hy, hx'2 := hy2, hx'1 := hy1, same := hsame }
  have hbN : π w ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) := by
    rw [hrange]
    exact mem_normalizer_map ψ.range N hNL hwN
  have hb2 : π w * π w = 1 := by rw [← map_mul, hw2, map_one]
  have hbR : ∀ r ∈ R, π w * ψ' r * (π w)⁻¹ = ψ' r := by
    intro r hr
    have h := congrArg π (hwR r hr)
    simp only [map_mul, map_inv] at h
    exact h
  have hbR' : ∀ r ∈ R', π w * ψ' r * (π w)⁻¹ = ψ' k * ψ' r * (ψ' k)⁻¹ := by
    intro r hr
    have h := congrArg π (hwR' r hr)
    simp only [map_mul, map_inv] at h
    exact h
  have hba : π w * ψ' k = ψ' k * π w := by
    have h := hbR' k hk
    have h2 : π w * ψ' k * (π w)⁻¹ = ψ' k := by rw [h]; group
    exact (mul_inv_eq_iff_eq_mul.mp h2)
  have hkk' : ψ' k * ψ' k = ψ' y' := by
    show π (ψ k) * π (ψ k) = π (ψ y')
    rw [← map_mul, hkk]
  have hka : ∀ r ∈ R, ψ' k * ψ' r = ψ' r * ψ' k := by
    intro r hr
    have h := hcomm r hr k hk
    calc ψ' k * ψ' r = ψ' (k * r) := (map_mul ψ' k r).symm
      _ = ψ' (r * k) := by rw [← h]
      _ = ψ' r * ψ' k := map_mul ψ' r k
  have hu : (ψ' k)⁻¹ * π w ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) :=
    (Subgroup.normalizer _).mul_mem (Subgroup.inv_mem _ (Subgroup.le_normalizer ⟨k, rfl⟩)) hbN
  set v : ↥(inducedAutOn ψ'.range) := toInducedAutOn ψ'.range ⟨(ψ' k)⁻¹ * π w, hu⟩ with hv
  have hcommute : ∀ r : M.K, (ψ' k)⁻¹ * π w * ψ' r = ψ' r * ((ψ' k)⁻¹ * π w) →
      v * innerHom ψ' r = innerHom ψ' r * v := by
    intro r h
    rw [innerHom_apply, hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have hva : ∀ r ∈ R', v * innerHom ψ' r = innerHom ψ' r * v := by
    intro r hr
    refine hcommute r ?_
    calc (ψ' k)⁻¹ * π w * ψ' r = (ψ' k)⁻¹ * (π w * ψ' r * (π w)⁻¹) * π w := by group
      _ = (ψ' k)⁻¹ * (ψ' k * ψ' r * (ψ' k)⁻¹) * π w := by rw [hbR' r hr]
      _ = ψ' r * ((ψ' k)⁻¹ * π w) := by group
  have hvb : ∀ r ∈ R, v * innerHom ψ' r = innerHom ψ' r * v := by
    intro r hr
    refine hcommute r ?_
    have hka' : (ψ' k)⁻¹ * ψ' r = ψ' r * (ψ' k)⁻¹ := by
      have h := hka r hr
      calc (ψ' k)⁻¹ * ψ' r = (ψ' k)⁻¹ * (ψ' r * ψ' k) * (ψ' k)⁻¹ := by group
        _ = (ψ' k)⁻¹ * (ψ' k * ψ' r) * (ψ' k)⁻¹ := by rw [h]
        _ = ψ' r * (ψ' k)⁻¹ := by group
    calc (ψ' k)⁻¹ * π w * ψ' r = (ψ' k)⁻¹ * (π w * ψ' r * (π w)⁻¹) * π w := by group
      _ = (ψ' k)⁻¹ * ψ' r * π w := by rw [hbR r hr]
      _ = ψ' r * ((ψ' k)⁻¹ * π w) := by rw [hka', mul_assoc]
  have hvv : v * v = innerHom ψ' y' := by
    rw [innerHom_apply, hv, ← map_mul]
    congr 1
    apply Subtype.ext
    show (ψ' k)⁻¹ * π w * ((ψ' k)⁻¹ * π w) = ψ' y'
    have hcom : Commute (π w) (ψ' k) := hba
    calc (ψ' k)⁻¹ * π w * ((ψ' k)⁻¹ * π w) = (ψ' k)⁻¹ * (π w * (ψ' k)⁻¹) * π w := by group
      _ = (ψ' k)⁻¹ * ((ψ' k)⁻¹ * π w) * π w := by rw [hcom.inv_right.eq]
      _ = ((ψ' k)⁻¹ * (ψ' k)⁻¹) * (π w * π w) := by group
      _ = (ψ' k * ψ' k)⁻¹ * 1 := by rw [hb2, ← mul_inv_rev]
      _ = ψ' y' := by rw [hkk', mul_one]; exact inv_eq_of_mul_eq_one_right hψ'y
  have hkv : innerHom ψ' k * v = toInducedAutOn ψ'.range ⟨π w, hbN⟩ := by
    rw [innerHom_apply, hv, ← map_mul]
    congr 1
    apply Subtype.ext
    show ψ' k * ((ψ' k)⁻¹ * π w) = π w
    group
  have hAlpha := hTW (H ⧸ N) ψ' R' R y' y hpair k hk hkk' v hva hvb hvv
  rw [hkv] at hAlpha
  have hmem' : ∀ x : H, x ∈ ψ.range → π x ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) := by
    intro x hx
    rw [hrange]
    exact Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hx)
  have hEq : (inducedImage ψ.range E).map (inducedAutQuotEquiv' hNL hNc hrange).toMonoidHom =
      Subgroup.closure ({toInducedAutOn ψ'.range ⟨π w, hbN⟩, innerHom ψ' y'} :
        Set ↥(inducedAutOn ψ'.range)) := by
    have hyN : ψ y ∈ Subgroup.normalizer (ψ.range : Set H) := mem_normalizer_range ψ y
    have hinn : toInducedAutOn ψ'.range ⟨π (ψ y), hmem' _ ⟨y, rfl⟩⟩ = innerHom ψ' y' := by
      rw [innerHom_apply]
      congr 1
      exact Subtype.ext hsame.symm
    apply le_antisymm
    · rintro _ ⟨x0, hx0, rfl⟩
      obtain ⟨⟨e, he⟩, hemem, rfl⟩ := hx0
      have he' : e ∈ E := Subgroup.mem_subgroupOf.mp hemem
      have hπe_mem : π e ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) := by
        rw [hrange]
        exact mem_normalizer_map ψ.range N hNL he
      show inducedAutQuotEquiv' hNL hNc hrange (toInducedAutOn ψ.range ⟨e, he⟩) ∈ _
      rw [inducedAutQuotEquiv'_apply hNL hNc hrange e he hπe_mem]
      obtain ⟨d, hd, e', he'c, hde⟩ := hE e he'
      have hdN : d ∈ Subgroup.normalizer (ψ.range : Set H) := by
        have hd' : d = e * e'⁻¹ := by rw [hde]; group
        rw [hd']
        exact (Subgroup.normalizer _).mul_mem he
          (Subgroup.inv_mem _ (Subgroup.center_le_normalizer _ he'c))
      have hπd_mem : π d ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) := by
        rw [hrange]
        exact mem_normalizer_map ψ.range N hNL hdN
      have hπe'_mem : π e' ∈ Subgroup.normalizer (ψ'.range : Set (H ⧸ N)) :=
        Subgroup.center_le_normalizer _ (mk'_mem_center N he'c)
      have hcen : toInducedAutOn ψ'.range ⟨π e', hπe'_mem⟩ = 1 :=
        Lemma52Proof.toInducedAutOn_eq_one_of_commute _ hπe'_mem (fun g _ =>
          (Subgroup.mem_center_iff.mp (mk'_mem_center N he'c) g).symm)
      have hsplit : toInducedAutOn ψ'.range ⟨π e, hπe_mem⟩ =
          toInducedAutOn ψ'.range ⟨π d, hπd_mem⟩ := by
        have h1 : (⟨π e, hπe_mem⟩ : Subgroup.normalizer (ψ'.range : Set (H ⧸ N))) =
            ⟨π d, hπd_mem⟩ * ⟨π e', hπe'_mem⟩ := by
          apply Subtype.ext
          show π e = π d * π e'
          rw [hde, map_mul]
        rw [h1, map_mul, hcen, mul_one]
      rw [hsplit]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · have h1 : (⟨π 1, hπd_mem⟩ : Subgroup.normalizer (ψ'.range : Set (H ⧸ N))) = 1 :=
          Subtype.ext (map_one π)
        rw [h1, map_one]
        exact Subgroup.one_mem _
      · rw [hinn]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have h1 : (⟨π (ψ y * w), hπd_mem⟩ : Subgroup.normalizer (ψ'.range : Set (H ⧸ N))) =
            ⟨π (ψ y), hmem' _ ⟨y, rfl⟩⟩ * ⟨π w, hbN⟩ := Subtype.ext (map_mul π _ _)
        rw [h1, map_mul, hinn]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
          (Subgroup.subset_closure (Set.mem_insert _ _))
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · refine ⟨toInducedAutOn ψ.range ⟨w, hwN⟩,
          ⟨⟨w, hwN⟩, Subgroup.mem_subgroupOf.mpr hwE, rfl⟩, ?_⟩
        show inducedAutQuotEquiv' hNL hNc hrange (toInducedAutOn ψ.range ⟨w, hwN⟩) = _
        exact inducedAutQuotEquiv'_apply hNL hNc hrange w hwN hbN
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨toInducedAutOn ψ.range ⟨ψ y, hyN⟩,
          ⟨⟨ψ y, hyN⟩, Subgroup.mem_subgroupOf.mpr hyE, rfl⟩, ?_⟩
        show inducedAutQuotEquiv' hNL hNc hrange (toInducedAutOn ψ.range ⟨ψ y, hyN⟩) = _
        rw [inducedAutQuotEquiv'_apply hNL hNc hrange (ψ y) hyN (hmem' _ ⟨y, rfl⟩)]
        exact hinn
  refine alphaOf_eq_bot_of_quotient' hNL hNc hrange _ ?_
  rw [hEq]
  exact hAlpha

end Twin

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S3A
