module

public import CFSG.ClassicalInvolution.AschTight.S1911P3g
public import CFSG.ClassicalInvolution.AschTight.S1911P3c

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

section Gen

variable {Y₀ : Type} [Group Y₀]

theorem isUniqueInvolution_subgroupOf {M H : Subgroup Y₀} {u : Y₀} (hu : IsUniqueInvolution M u)
    (hMH : M ≤ H) : IsUniqueInvolution (M.subgroupOf H) ⟨u, hMH hu.mem⟩ :=
  ⟨Subgroup.mem_subgroupOf.mpr hu.mem, fun h => hu.ne_one (congrArg Subtype.val h),
    Subtype.ext hu.sq, fun _ hy hy2 => (hu.unique _ (Subgroup.mem_subgroupOf.mp hy)
      (congrArg Subtype.val hy2)).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)⟩

theorem secAct_eq_one_of_mem (Y₁ : Subgroup Y₀) [Y₁.Normal] {v : Y₀}
    (hv : v ∈ oddCoreOf Y₁) : secAct Y₁ v = 1 := by
  obtain ⟨hvY, hvO⟩ := mem_oddCoreOf_iff.mp hv
  rw [secAct_of_mem Y₁ hvY, (QuotientGroup.eq_one_iff _).mpr hvO, map_one]

theorem mem_oddCoreOf_of_secAct {Y₁ : Subgroup Y₀} [Y₁.Normal] {s u : Y₀} (hu : u ∈ Y₁)
    (h : secAct Y₁ s (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩) :
    u⁻¹ * (s * u * s⁻¹) ∈ oddCoreOf Y₁ := by
  rw [secAct_mk] at h
  have h1 := QuotientGroup.eq.mp h.symm
  refine mem_oddCoreOf_iff.mpr ⟨Y₁.mul_mem (Y₁.inv_mem hu) (MulAut.conjNormal s ⟨u, hu⟩).2, ?_⟩
  convert h1 using 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]

end Gen

section Sec

variable {Y₀ : Type} [Group Y₀]

theorem mem_secFamily_iff (L : Subgroup Y₀) (X : Subgroup (↥(conjGen L) ⧸
    classicalInvolutionOddCore ↥(conjGen L))) :
    X ∈ oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)) ↔
      ∃ c : Y₀, X = secImg (conjGen L) (conjSub c L) := by
  constructor
  · rintro ⟨_, ⟨M, ⟨c, rfl⟩, -, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨conjSub c L, ⟨c, rfl⟩, le_conjGen ⟨c, rfl⟩, rfl⟩, rfl⟩

theorem secAct_preserves (L : Subgroup Y₀) (s : Y₀) :
    ∀ X ∈ oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)),
      X.map (@secAct _ _ (conjGen L) (conjGen_normal L) s).toMonoidHom ∈
        oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)) := by
  have := conjGen_normal L
  intro X hX
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff L X).mp hX
  rw [secAct_secImg (conjGen L) s (le_conjGen ⟨c, rfl⟩), ← conjSub_mul]
  exact (mem_secFamily_iff L _).mpr ⟨s * c, rfl⟩

end Sec

section Members2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem isUniqueInvolution_secImg (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)))
      (QuotientGroup.mk' _ ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
        (isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (isUniqueInvolution_subgroupOf (isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c)
      (le_conjGen ⟨c, rfl⟩))

end Members2

section Fusion

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
theorem mem_normalizer_oddCoreOf_conjGen {Y₀ : Type} [Group Y₀] [Finite Y₀] (L : Subgroup Y₀)
    (s : Y₀) : s ∈ Subgroup.normalizer ((oddCoreOf (conjGen L) : Subgroup Y₀) : Set Y₀) := by
  have hN := conjGen_normal L
  refine mem_normalizer_oddCoreOf_of_mem_normalizer ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hN.conj_mem x hx s
  · intro hx
    have := hN.conj_mem _ hx s⁻¹
    simpa [mul_assoc] using this

omit [IsSimpleGroup G] in
theorem exists_conj_comm_of_secAct (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    {s : ↥(Subgroup.centralizer ({a} : Set G))} (hs2 : s * s = 1)
    {c : ↥(Subgroup.centralizer ({a} : Set G))}
    (hc : (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a))).map
      (@secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) s).toMonoidHom =
        secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a))) :
    ∃ v ∈ oddCoreOf (conjGen (perfectCoreIn K a)),
      (v * c)⁻¹ * s * (v * c) * ⟨z, hzA⟩ = ⟨z, hzA⟩ * ((v * c)⁻¹ * s * (v * c)) := by
  have := conjGen_normal (perfectCoreIn K a)
  have hu := isUniqueInvolution_secImg hd hzA hzKa c
  set φ := @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) s with hφ
  set ū := QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))
    ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
      (isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c).mem⟩ with hū
  have hφu : φ ū = ū := by
    have hmem : φ ū ∈ secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)) := by
      rw [← hc]
      exact ⟨ū, hu.mem, rfl⟩
    have hsq : φ ū * φ ū = 1 := by rw [← map_mul, hu.sq, map_one]
    have hne : φ ū ≠ 1 := fun h => hu.ne_one (φ.injective (h.trans (map_one φ).symm))
    exact (hu.unique _ hmem hsq).resolve_left hne
  have hO := mem_oddCoreOf_of_secAct _ hφu
  have hu2 : c * ⟨z, hzA⟩ * c⁻¹ * (c * ⟨z, hzA⟩ * c⁻¹) = 1 :=
    (isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c).sq
  obtain ⟨v, hvO, hv⟩ := exists_conj_commute_of_odd (oddCoreOf_odd_natCard _) hs2 hu2
    (mem_normalizer_oddCoreOf_conjGen _ s) (mem_normalizer_oddCoreOf_conjGen _ _) hO
  refine ⟨v, hvO, ?_⟩
  calc (v * c)⁻¹ * s * (v * c) * ⟨z, hzA⟩
      = (v * c)⁻¹ * (s * (v * (c * ⟨z, hzA⟩ * c⁻¹) * v⁻¹)) * (v * c) := by group
    _ = (v * c)⁻¹ * ((v * (c * ⟨z, hzA⟩ * c⁻¹) * v⁻¹) * s) * (v * c) := by rw [hv]
    _ = ⟨z, hzA⟩ * ((v * c)⁻¹ * s * (v * c)) := by group

omit [IsSimpleGroup G] in
theorem secAct_z_fixes (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :
    ∀ x ∈ secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a),
      @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) ⟨z, hzA⟩ x = x := by
  have := conjGen_normal (perfectCoreIn K a)
  have hu := isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa 1
  simp only [conjSub_one, one_mul, inv_one, mul_one] at hu
  rintro _ ⟨m, hm, rfl⟩
  rw [QuotientGroup.mk'_apply, secAct_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hmL : (m : ↥(Subgroup.centralizer ({a} : Set G))) ∈ perfectCoreIn K a :=
    Subgroup.mem_subgroupOf.mp hm
  generalize (m : ↥(Subgroup.centralizer ({a} : Set G))) = n at hmL ⊢
  have hc : n * ⟨z, hzA⟩ * n⁻¹ ∈ perfectCoreIn K a :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hmL hu.mem) (Subgroup.inv_mem _ hmL)
  have hsq : n * ⟨z, hzA⟩ * n⁻¹ * (n * ⟨z, hzA⟩ * n⁻¹) = 1 := by
    calc n * ⟨z, hzA⟩ * n⁻¹ * (n * ⟨z, hzA⟩ * n⁻¹) = n * (⟨z, hzA⟩ * ⟨z, hzA⟩) * n⁻¹ := by group
      _ = 1 := by rw [hu.sq]; group
  have h1 : n * ⟨z, hzA⟩ * n⁻¹ = ⟨z, hzA⟩ := by
    refine (hu.unique _ hc hsq).resolve_left fun h => hu.ne_one ?_
    calc (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
        n⁻¹ * (n * ⟨z, hzA⟩ * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  calc (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * n * ⟨z, hzA⟩⁻¹ =
      ⟨z, hzA⟩ * (n * ⟨z, hzA⟩ * n⁻¹)⁻¹ * n := by group
    _ = n := by rw [h1]; group

theorem exists_conj_eq_of_secAct_eq (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {t : ↥(Subgroup.centralizer ({a} : Set G))} (ht : ∃ g : G, (t : G) = g * z * g⁻¹)
    (ht2 : t * t = 1) {c' : ↥(Subgroup.centralizer ({a} : Set G))}
    (hφ : @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) t =
      @secAct _ _ (conjGen (perfectCoreIn K a)) (conjGen_normal _) (c' * ⟨z, hzA⟩ * c'⁻¹)) :
    ∃ d : ↥(Subgroup.centralizer ({a} : Set G)), t = d * ⟨z, hzA⟩ * d⁻¹ := by
  have := conjGen_normal (perfectCoreIn K a)
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  have hu := isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c'
  have huY : c' * ⟨z, hzA⟩ * c'⁻¹ ∈ conjGen (perfectCoreIn K a) := le_conjGen ⟨c', rfl⟩ hu.mem
  have hφu : secAct (conjGen (perfectCoreIn K a)) t (QuotientGroup.mk ⟨_, huY⟩) =
      QuotientGroup.mk ⟨_, huY⟩ := by
    rw [hφ, secAct_of_mem _ huY, MulAut.conj_apply, mul_inv_cancel_right]
  obtain ⟨v, hvO, hv⟩ := exists_conj_commute_of_odd (oddCoreOf_odd_natCard _) ht2 hu.sq
    (mem_normalizer_oddCoreOf_conjGen _ t) (mem_normalizer_oddCoreOf_conjGen _ _)
    (mem_oddCoreOf_of_secAct huY hφu)
  set d := v * c' with hd'
  have hvd : v * (c' * ⟨z, hzA⟩ * c'⁻¹) * v⁻¹ = d * ⟨z, hzA⟩ * d⁻¹ := by rw [hd']; group
  rw [hvd] at hv
  have hv1 := secAct_eq_one_of_mem (conjGen (perfectCoreIn K a)) hvO
  have hφ₂ : secAct (conjGen (perfectCoreIn K a)) (d⁻¹ * t * d) =
      secAct (conjGen (perfectCoreIn K a)) ⟨z, hzA⟩ := by
    rw [map_mul, map_mul, hφ, map_inv, hd', map_mul, hv1, one_mul, map_mul, map_mul, map_inv]
    group
  obtain ⟨g, hg⟩ := ht
  have ht₂ : ∃ g : G, ((d⁻¹ * t * d : ↥(Subgroup.centralizer ({a} : Set G))) : G) =
      g * z * g⁻¹ := ⟨(d : G)⁻¹ * g, by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
        group⟩
  have ht₂z : ((d⁻¹ * t * d : ↥(Subgroup.centralizer ({a} : Set G))) : G) * z =
      z * ((d⁻¹ * t * d : ↥(Subgroup.centralizer ({a} : Set G))) : G) := by
    have h1 : d⁻¹ * t * d * ⟨z, hzA⟩ = ⟨z, hzA⟩ * (d⁻¹ * t * d) := by
      calc d⁻¹ * t * d * ⟨z, hzA⟩ = d⁻¹ * (t * (d * ⟨z, hzA⟩ * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * ⟨z, hzA⟩ * d⁻¹) * t) * d := by rw [hv]
        _ = ⟨z, hzA⟩ * (d⁻¹ * t * d) := by group
    exact congrArg Subtype.val h1
  have ht₂2 : d⁻¹ * t * d * (d⁻¹ * t * d) = 1 := by
    calc d⁻¹ * t * d * (d⁻¹ * t * d) = d⁻¹ * (t * t) * d := by group
      _ = 1 := by rw [ht2]; group
  have hfix := secAct_z_fixes hd hzA hzKa
  rw [← hφ₂] at hfix
  have heq := eq_of_secAct_fixes hd h5 hzA hmem ht₂ ht₂z ht₂2 hfix
  refine ⟨d, ?_⟩
  have h2 : d⁻¹ * t * d = ⟨z, hzA⟩ := Subtype.ext heq
  calc t = d * (d⁻¹ * t * d) * d⁻¹ := by group
    _ = d * ⟨z, hzA⟩ * d⁻¹ := by rw [h2]

omit [IsSimpleGroup G] in
theorem exists_noncomm_secImg (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    ∃ x ∈ secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a),
      ∃ y ∈ secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a), x * y ≠ y * x := by
  have hLY : perfectCoreIn K a ≤ conjGen (perfectCoreIn K a) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(perfectCoreIn K a)) := inferInstance
  have hR : (T : Subgroup _).map (perfectCoreIn K a).subtype ∈
      RSet (CoreAssembly.conjClass (perfectCoreIn K a)) :=
    ⟨_, CoreAssembly.mem_conjClass_self _, T, rfl⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := (exists_ne_comm_of_mem_rSet hd.tight.branch.odd h5 hmem hR).1
  have hR2 := isPGroup_of_mem_rSet hR
  have hxL : x ∈ perfectCoreIn K a := Subgroup.map_subtype_le _ hx
  have hyL : y ∈ perfectCoreIn K a := Subgroup.map_subtype_le _ hy
  refine ⟨QuotientGroup.mk' _ ⟨x, hLY hxL⟩, ⟨⟨x, hLY hxL⟩, hxL, rfl⟩,
    QuotientGroup.mk' _ ⟨y, hLY hyL⟩, ⟨⟨y, hLY hyL⟩, hyL, rfl⟩, fun h => hxy ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ↥(conjGen (perfectCoreIn K a)), x' = ⟨x, hLY hxL⟩ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(conjGen (perfectCoreIn K a)), y' = ⟨y, hLY hyL⟩ := ⟨_, rfl⟩
  rw [← hx', ← hy'] at h
  have hc : x' * y' * x'⁻¹ * y'⁻¹ ∈ classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have h' : (QuotientGroup.mk x' : _ ⧸ classicalInvolutionOddCore _) * QuotientGroup.mk y' =
        QuotientGroup.mk y' * QuotientGroup.mk x' := h
    rw [h']
    group
  have hc' : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (conjGen (perfectCoreIn K a)) := by
    refine ⟨x' * y' * x'⁻¹ * y'⁻¹, hc, ?_⟩
    rw [hx', hy']
    rfl
  have hcR : x * y * x⁻¹ * y⁻¹ ∈ (T : Subgroup _).map (perfectCoreIn K a).subtype :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hy)
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc'
    (hR2.to_le (Subgroup.zpowers_le.mpr hcR))
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end Fusion

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
