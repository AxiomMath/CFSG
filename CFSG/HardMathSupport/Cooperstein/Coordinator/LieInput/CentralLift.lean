module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ClassicalRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.Quasithin.SmithC27
  CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

section Central

variable {G : Type*} [Group G]

theorem normal_of_le_center {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) : Z.Normal :=
  ⟨fun z hz g => by
    have := Subgroup.mem_center_iff.mp (hZ hz) g
    rwa [this, mul_inv_cancel_right]⟩

theorem commutatorElement_mul_central_left {a c z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, c⁆ = ⁅a, c⁆ := by
  have h1 : z * c * z⁻¹ = c := by
    rw [← Subgroup.mem_center_iff.mp hz c, mul_inv_cancel_right]
  calc ⁅a * z, c⁆ = a * (z * c * z⁻¹) * a⁻¹ * c⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, c⁆ := by rw [h1]; rfl

theorem commutatorElement_mul_central_right {a c z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a, c * z⁆ = ⁅a, c⁆ := by
  have h1 : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hz a⁻¹, mul_inv_cancel_right]
  calc ⁅a, c * z⁆ = a * c * (z * a⁻¹ * z⁻¹) * c⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, c⁆ := by rw [h1]; rfl

theorem commutatorElement_mul_central {a b z z' : G} (hz : z ∈ Subgroup.center G)
    (hz' : z' ∈ Subgroup.center G) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hz']

theorem commutator_sup_central_le {V Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) :
    ⁅V ⊔ Z, V ⊔ Z⁆ ≤ ⁅V, V⁆ := by
  have : Z.Normal := normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨v, hv, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  obtain ⟨w, hw, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  rw [commutatorElement_mul_central (hZ hz) (hZ hz')]
  exact Subgroup.commutator_mem_commutator hv hw

theorem commute_of_commutator_mem_center {P : Subgroup G} (hP : ⁅P, P⁆ = P) {c : G}
    (h : ∀ d ∈ P, ⁅c, d⁆ ∈ Subgroup.center G) : ∀ d ∈ P, c * d = d * c := by
  let φ : P →* Subgroup.center G :=
    { toFun := fun d => ⟨⁅c, (d : G)⁆, h d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅c, (a : G) * b⁆ = ⁅c, (a : G)⁆ * ⁅c, (b : G)⁆
        have hb := Subgroup.mem_center_iff.1 (h b b.2) a
        have e : ⁅c, (a : G) * b⁆ = ⁅c, (a : G)⁆ * ((a : G) * ⁅c, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hb, mul_inv_cancel_right]) }
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  intro d hd
  have hker : commutator P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have h1 : φ ⟨d, hd⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : ⁅c, d⁆ = 1 := congrArg Subtype.val h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Central

section Transport

theorem isClassicalTwoOrG2_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsClassicalTwoOrG2 Y) : IsClassicalTwoOrG2 Y' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

variable {P Q : Type*} [Group P] [Group Q]

theorem isQuasisimple_of_perfect_central [Group.IsPerfect P] (π : P →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P)
    (hQ : CFSG.IsQuasisimple Q) : CFSG.IsQuasisimple P := by
  have e := quotCenterEquivOfSurjective π hπ hker
  refine ⟨inferInstance, (MulEquiv.isSimpleGroup_congr e).mpr hQ.2.1, ?_⟩
  obtain ⟨a, b, hab⟩ := hQ.2.2
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

end Transport

section Radical

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_two_le_radical {R : Subgroup G}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G))) :
    ∀ z ∈ Subgroup.center G, (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ R := by
  rintro z hz ⟨n, hn⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm := normal_zpowers_of_mem_center hz
  have hle : Subgroup.zpowers z ≤
      pCoreOf 2 ((⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) :=
    le_pCoreOf_of_le_normalizer 2
      (fun x hx => ⟨Subgroup.mem_top _,
        Subgroup.center_le_normalizer (R : Set G) (Subgroup.zpowers_le.mpr hz hx)⟩)
      (by rw [Subgroup.normalizer_eq_top (H := Subgroup.zpowers z)]; exact le_top)
      (isPGroup_zpowers_two hn)
  rw [← hR] at hle
  exact hle (Subgroup.mem_zpowers z)

theorem radical_map_central {R : Subgroup G}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G))) :
    (Subgroup.normalizer (R.map (QuotientGroup.mk' (Subgroup.center G)) :
        Set (G ⧸ Subgroup.center G))).comap (QuotientGroup.mk' (Subgroup.center G)) =
        Subgroup.normalizer (R : Set G) ∧
      R.map (QuotientGroup.mk' (Subgroup.center G)) =
        pCoreOf 2 ((⊤ : Subgroup (G ⧸ Subgroup.center G)) ⊓
          Subgroup.normalizer ((R.map (QuotientGroup.mk' (Subgroup.center G)) :
            Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hR2 : IsPGroup 2 R := by
    rw [hR]; exact pCoreOf_isPGroup 2 _
  have hN : Subgroup.normalizer (R : Set G) =
      (Subgroup.normalizer (R.map π : Set (G ⧸ Subgroup.center G))).comap π :=
    normalizer_eq_comap_normalizer_map_of_two le_rfl hR2 (center_two_le_radical hR)
  refine ⟨hN.symm, le_antisymm ?_ ?_⟩
  · refine le_pCoreOf_of_le_normalizer 2 (fun x hx => ⟨Subgroup.mem_top _,
      Subgroup.le_normalizer hx⟩) inf_le_right (hR2.map π)
  · have h1 := pCoreOf_le_map_pCoreOf_comap_of_two (Subgroup.center G) le_rfl
      ((⊤ : Subgroup (G ⧸ Subgroup.center G)) ⊓
        Subgroup.normalizer (R.map π : Set (G ⧸ Subgroup.center G)))
    have h2 : ((⊤ : Subgroup (G ⧸ Subgroup.center G)) ⊓
        Subgroup.normalizer (R.map π : Set (G ⧸ Subgroup.center G))).comap π =
        (⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.comap_inf, Subgroup.comap_top, ← hN]
    rw [h2, ← hR] at h1
    exact h1

end Radical

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conj_le {S : Subgroup G} {x : G} (h1 : ∀ h ∈ S, x * h * x⁻¹ ∈ S)
    (h2 : ∀ h ∈ S, x⁻¹ * h * x ∈ S) : x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hx => ?_⟩
  simpa [mul_assoc] using h2 _ hx

theorem leviStructure_lift {R : Subgroup G}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)))
    (h : LeviStructure (⊤ : Subgroup (G ⧸ Subgroup.center G))
      (R.map (QuotientGroup.mk' (Subgroup.center G)))) :
    LeviStructure (⊤ : Subgroup G) R := by
  obtain ⟨hN, -⟩ := radical_map_central hR
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center G := QuotientGroup.ker_mk' _
  have hkerz : ∀ x : G, π x = 1 ↔ x ∈ Subgroup.center G := fun x =>
    QuotientGroup.eq_one_iff x
  obtain ⟨n, Cb, Db, hRD, hDY, hDs, hC, hcomm, hY⟩ := h
  have hYpre : ((⊤ : Subgroup (G ⧸ Subgroup.center G)) ⊓
      Subgroup.normalizer (R.map π : Set (G ⧸ Subgroup.center G))).comap π =
      (⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.comap_inf, Subgroup.comap_top, hN]
  have hCperf : ∀ i, ⁅Cb i, Cb i⁆ = Cb i := fun i =>
    Subgroup.isPerfect_iff.mp (hC i).2.1.1
  obtain ⟨C, hCdef⟩ : ∃ C : Fin n → Subgroup G,
      ∀ i, C i = ⁅(Cb i).comap π, (Cb i).comap π⁆ := ⟨_, fun i => rfl⟩
  have mapC : ∀ i, (C i).map π = Cb i := fun i => by
    rw [hCdef, Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπs, hCperf]
  have CleX : ∀ i, C i ≤ (Cb i).comap π := fun i => by
    rw [hCdef]; exact Subgroup.commutator_le_self _
  have Xsup : ∀ i, (Cb i).comap π = C i ⊔ Subgroup.center G := fun i => by
    refine le_antisymm (fun x hx => ?_) (sup_le (CleX i) (fun z hz => ?_))
    · have hx' : π x ∈ (C i).map π := by rw [mapC]; exact hx
      obtain ⟨c, hc, hcx⟩ := hx'
      have hz : c⁻¹ * x ∈ Subgroup.center G := by
        rw [← hkerz, map_mul, map_inv, hcx, inv_mul_cancel]
      have : x = c * (c⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hz)
    · rw [Subgroup.mem_comap, (hkerz z).mpr hz]; exact one_mem _
  have Cperf : ∀ i, ⁅C i, C i⁆ = C i := fun i => by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    calc C i = ⁅(Cb i).comap π, (Cb i).comap π⁆ := hCdef i
      _ = ⁅C i ⊔ Subgroup.center G, C i ⊔ Subgroup.center G⁆ := by rw [Xsup i]
      _ ≤ ⁅C i, C i⁆ := commutator_sup_central_le le_rfl
  have hperf : ∀ i, Group.IsPerfect ↥(C i) := fun i => Subgroup.isPerfect_iff.mpr (Cperf i)
  have hCY : ∀ i, C i ≤ (⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) := fun i => by
    rw [← hYpre]
    exact (CleX i).trans (Subgroup.comap_mono (hC i).1)
  have hDN : ∀ i, Db ≤ Subgroup.normalizer ((Cb i ⊔ R.map π : Subgroup _) : Set _) :=
    fun i => (hC i).2.2.2
  have hZD : Subgroup.center G ≤ Db.comap π := fun z hz => by
    rw [Subgroup.mem_comap, (hkerz z).mpr hz]; exact one_mem _
  have ρC : ∀ i, ∃ ρ : ↥(C i) →* ↥(Cb i), Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center ↥(C i) ∧ ∀ c : ↥(C i), ((ρ c : ↥(Cb i)) : G ⧸ Subgroup.center G) = π c := by
    intro i
    refine ⟨(π.comp (C i).subtype).codRestrict (Cb i) (fun c => by
      rw [← mapC i]; exact ⟨c, c.2, rfl⟩), ?_, ?_, fun c => rfl⟩
    · intro y
      have hy : (y : G ⧸ Subgroup.center G) ∈ (C i).map π := by rw [mapC]; exact y.2
      obtain ⟨c, hc, hcy⟩ := hy
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
    · intro c hc
      have h1 : π (c : G) = 1 := congrArg Subtype.val hc
      have h2 := (hkerz c).mp h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.mp h2 g))
  have hDsub : Db.comap π ≤ (⊤ : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
    le_of_le_of_eq (Subgroup.comap_mono hDY) hYpre
  have hconj : ∀ i, ∀ y ∈ Db.comap π, ∀ h ∈ C i ⊔ R, y * h * y⁻¹ ∈ C i ⊔ R := by
    intro i y hy h hh
    have hyN : y ∈ Subgroup.normalizer (R : Set G) := (hDsub hy).2
    have hyb : π y ∈ Subgroup.normalizer ((Cb i ⊔ R.map π : Subgroup _) : Set _) :=
      hDN i (Subgroup.mem_comap.mp hy)
    have hRc : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr =>
      (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
    set φ : G →* G := (MulAut.conj y).toMonoidHom with hφ
    have hφ' : ∀ g, φ g = y * g * y⁻¹ := fun g => rfl
    have hpre : (C i ⊔ R).map π = Cb i ⊔ R.map π := by rw [Subgroup.map_sup, mapC]
    have hS1 : (C i).map φ ≤ (C i ⊔ R) ⊔ Subgroup.center G := by
      rintro _ ⟨c, hc, rfl⟩
      have hcb : π c ∈ Cb i ⊔ R.map π :=
        Subgroup.mem_sup_left (by rw [← mapC i]; exact Subgroup.mem_map_of_mem π hc)
      have h1 := (Subgroup.mem_normalizer_iff.mp hyb (π c)).mp hcb
      have e : π (φ c) = π y * π c * (π y)⁻¹ := by simp [hφ']
      have h2 : φ c ∈ ((C i ⊔ R).map π).comap π := by
        rw [hpre, Subgroup.mem_comap, e]; exact h1
      rwa [Subgroup.comap_map_eq, hker] at h2
    have hS : (C i).map φ ≤ C i ⊔ R :=
      calc (C i).map φ = ⁅(C i).map φ, (C i).map φ⁆ := by
            rw [← Subgroup.map_commutator, Cperf]
        _ ≤ ⁅(C i ⊔ R) ⊔ Subgroup.center G, (C i ⊔ R) ⊔ Subgroup.center G⁆ :=
            Subgroup.commutator_mono hS1 hS1
        _ ≤ ⁅C i ⊔ R, C i ⊔ R⁆ := commutator_sup_central_le le_rfl
        _ ≤ C i ⊔ R := Subgroup.commutator_le_self _
    have hmapsup : (C i ⊔ R).map φ ≤ C i ⊔ R := by
      rw [Subgroup.map_sup]
      exact sup_le hS (by rintro _ ⟨r, hr, rfl⟩; exact Subgroup.mem_sup_right (hRc r hr))
    exact hmapsup ⟨h, hh, rfl⟩
  refine ⟨n, C, Db.comap π, fun x hx => hRD (Subgroup.mem_map_of_mem π hx), hDsub, ?_, ?_, ?_, ?_⟩
  · have hfm : Subgroup.center G ≤ Db.comap π := hZD
    have : Group.IsSolvable ↥Db := hDs
    have : Group.IsSolvable ↥(Subgroup.center G) := inferInstance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hfm)
      ((π.comp (Db.comap π).subtype).codRestrict Db (fun x => x.2)) ?_
    intro x hx
    have h1 : π (x : G) = 1 := congrArg Subtype.val hx
    exact ⟨⟨x, (hkerz x).mp h1⟩, rfl⟩
  · intro i
    obtain ⟨ρ, hs, hk, -⟩ := ρC i
    have := hperf i
    refine ⟨hCY i, isQuasisimple_of_perfect_central ρ hs hk (hC i).2.1,
      isClassicalTwoOrG2_of_mulEquiv (quotCenterEquivOfSurjective ρ hs hk).symm (hC i).2.2.1, ?_⟩
    intro x hx
    exact mem_normalizer_of_conj_le (hconj i x hx)
      (fun h hh => by simpa using hconj i x⁻¹ (inv_mem hx) h hh)
  · intro i j hij c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hπ : ∀ d ∈ C j, ⁅c, d⁆ ∈ Subgroup.center G := by
      intro d hd
      rw [← hkerz, map_commutatorElement]
      have hc' : π c ∈ Cb i := by rw [← mapC i]; exact Subgroup.mem_map_of_mem π hc
      have hd' : π d ∈ Cb j := by rw [← mapC j]; exact Subgroup.mem_map_of_mem π hd
      have := Subgroup.mem_centralizer_iff.mp (hcomm i j hij hc') (π d) hd'
      exact commutatorElement_eq_one_iff_mul_comm.mpr this.symm
    exact (commute_of_commutator_mem_center (Cperf j) hπ d hd).symm
  · apply le_antisymm
    · intro y hy
      have hy' : π y ∈ Db ⊔ ⨆ i, Cb i := by
        rw [← hY]
        rw [← hYpre] at hy
        exact Subgroup.mem_comap.mp hy
      have hmap : (Db.comap π ⊔ ⨆ i, C i).map π = Db ⊔ ⨆ i, Cb i := by
        rw [Subgroup.map_sup, Subgroup.map_iSup, Subgroup.map_comap_eq_self_of_surjective hπs]
        simp_rw [mapC]
      rw [← hmap] at hy'
      obtain ⟨w, hw, hwy⟩ := hy'
      have hz : w⁻¹ * y ∈ Subgroup.center G := by
        rw [← hkerz, map_mul, map_inv, hwy, inv_mul_cancel]
      have : y = w * (w⁻¹ * y) := by group
      rw [this]
      exact mul_mem hw (Subgroup.mem_sup_left (hZD hz))
    · exact sup_le hDsub (iSup_le hCY)

end Lift

section Map

theorem isQuasisimple_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : CFSG.IsQuasisimple P) : CFSG.IsQuasisimple Q :=
  h.of_mulEquiv e.symm

variable {G Γ : Type} [Group G] [Group Γ]

theorem leviStructure_map (ι : G →* Γ) (hι : Function.Injective ι) {L R : Subgroup G}
    (h : LeviStructure L R) : LeviStructure (L.map ι) (R.map ι) := by
  obtain ⟨n, C, D, hRD, hDY, hDs, hC, hcomm, hY⟩ := h
  have hY' : (L ⊓ Subgroup.normalizer (R : Set G)).map ι =
      L.map ι ⊓ Subgroup.normalizer ((R.map ι : Subgroup Γ) : Set Γ) :=
    map_inf_normalizer_of_injective ι hι L R
  refine ⟨n, fun i => (C i).map ι, D.map ι, Subgroup.map_mono hRD, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hY']; exact Subgroup.map_mono hDY
  · have e := Subgroup.equivMapOfInjective D ι hι
    have : Group.IsSolvable ↥D := hDs
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  · intro i
    obtain ⟨hCY, hq, hcl, hDn⟩ := hC i
    have e := Subgroup.equivMapOfInjective (C i) ι hι
    refine ⟨?_, isQuasisimple_of_mulEquiv e hq,
      isClassicalTwoOrG2_of_mulEquiv (quotCenterCongr e) hcl, ?_⟩
    · rw [← hY']; exact Subgroup.map_mono hCY
    · rw [← Subgroup.map_sup]
      rintro _ ⟨x, hx, rfl⟩
      exact (CFSG.Quasithin.SBd3T.map_mem_normalizer_iff ι hι _ x).2 (hDn hx)
  · intro i j hij
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hcomm i j hij hc) d hd
    rw [← map_mul, ← map_mul, this]
  · rw [← hY', hY, Subgroup.map_sup, Subgroup.map_iSup]

theorem leviStructure_of_subtype {L R : Subgroup Γ} (hRL : R ≤ L)
    (h : LeviStructure (⊤ : Subgroup ↥L) (R.subgroupOf L)) : LeviStructure L R := by
  have := leviStructure_map L.subtype L.subtype_injective h
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hRL] at this

end Map

section Assembly

variable {Γ : Type} [Group Γ] [Finite Γ] {L R : Subgroup Γ}

omit [Finite Γ] in
theorem radical_subgroupOf (hR : R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ))) :
    R ≤ L ∧ R.subgroupOf L =
      pCoreOf 2 ((⊤ : Subgroup ↥L) ⊓ Subgroup.normalizer ((R.subgroupOf L : Subgroup ↥L) :
        Set ↥L)) := by
  have hRL : R ≤ L := by rw [hR]; exact (pCoreOf_le 2 _).trans inf_le_left
  refine ⟨hRL, Subgroup.map_injective L.subtype_injective ?_⟩
  have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.map_subgroupOf_eq_of_le hRL,
    ← pCoreOf_map_of_injective' L.subtype L.subtype_injective,
    map_inf_normalizer_of_injective L.subtype L.subtype_injective, hLtop,
    Subgroup.map_subgroupOf_eq_of_le hRL]
  exact hR

theorem leviStructure_of_simple (hS : LieInputSimple)
    (hc : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hR : R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ))) : LeviStructure L R := by
  obtain ⟨hRL, hRg⟩ := radical_subgroupOf hR
  have hb := (hS _ hc _ (radical_map_central hRg).2).1
  exact leviStructure_of_subtype hRL (leviStructure_lift hRg hb)

theorem centralizerInRadical_of_simple (hS : LieInputSimple)
    (hc : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hR : R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ)))
    (hne : L ⊓ Subgroup.normalizer (R : Set Γ) ≠ L) : CentralizerInRadical L R := by
  obtain ⟨hRL, hRg⟩ := radical_subgroupOf hR
  set Rg := R.subgroupOf L with hRgdef
  set π := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  obtain ⟨hN, hRb⟩ := radical_map_central hRg
  have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h0 : (⊤ : Subgroup ↥L) ⊓ Subgroup.normalizer (Rg : Set ↥L) ≠ ⊤ := by
    intro h
    apply hne
    have := congrArg (Subgroup.map L.subtype) h
    rw [map_inf_normalizer_of_injective L.subtype L.subtype_injective, hLtop,
      Subgroup.map_subgroupOf_eq_of_le hRL] at this
    exact this
  have hprop : (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ⊓
      Subgroup.normalizer ((Rg.map π : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L)) ≠ ⊤ := by
    intro htop
    apply h0
    have := congrArg (Subgroup.comap π) htop
    rw [Subgroup.comap_inf, Subgroup.comap_top, hN] at this
    exact this
  have hb := (hS _ hc _ hRb).2 hprop
  intro x hxL hcomm
  set xg : ↥L := ⟨x, hxL⟩ with hxg
  have hcg : ∀ r ∈ Rg, xg * r = r * xg := fun r hr =>
    Subtype.ext (hcomm r (by simpa [hRgdef, Subgroup.mem_subgroupOf] using hr))
  have hxb : π xg ∈ Rg.map π := hb (π xg) (by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, hcg r hr])
  obtain ⟨r, hr, hrx⟩ := hxb
  have hz : r⁻¹ * xg ∈ Subgroup.center ↥L := by
    have : π (r⁻¹ * xg) = 1 := by rw [map_mul, map_inv, hrx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hxm : xg ∈ Rg ⊔ Subgroup.center ↥L := by
    have e : xg = r * (r⁻¹ * xg) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hz)
  have := Subgroup.mem_map_of_mem L.subtype hxm
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hRL] at this
  exact this

end Assembly

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
