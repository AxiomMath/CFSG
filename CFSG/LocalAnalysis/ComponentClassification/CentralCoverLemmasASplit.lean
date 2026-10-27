module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

variable {E M : Type*} [Group E] [Group M]

private theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hx]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k <;> simp

theorem central_double_cover_splits_over_perfect_factor_from_involution_fusion [Finite E]
    [Finite M] (π : E →* M) (hπ : Function.Surjective π) {t : E} (hker : π.ker = zpowers t)
    (htorder : orderOf t = 2) (htcenter : t ∈ center E) {D : Subgroup M}
    (hD : Group.IsPerfect D) (W : Sylow 2 D) (hW : ∀ w ∈ (W : Subgroup D), w ^ 2 = 1) {r : M}
    (hrD : r ∈ D) (hfusion : ∀ q ∈ D, orderOf q = 2 → ∃ d ∈ D, d * r * d⁻¹ = q) {z : M}
    (hzD : z ∈ Subgroup.centralizer (D : Set M)) (hzorder : orderOf z = 2)
    (hzr : ∃ h : M, h * z * h⁻¹ = z * r) :
    (zpowers t ⊓ ⁅D.comap π, D.comap π⁆ = ⊥ ∧
      zpowers t ⊔ ⁅D.comap π, D.comap π⁆ = D.comap π ∧
      ((zpowers t).subgroupOf (D.comap π)).Normal ∧
      (Subgroup.subgroupOf ⁅D.comap π, D.comap π⁆ (D.comap π)).Normal) ∧
    (∃ e : (⁅D.comap π, D.comap π⁆ : Subgroup E) ≃* D, (∀ a, (e a : M) = π a) ∧
      ∃ σ : D →* D.comap π, (∀ d, (σ d : E) = e.symm d) ∧
        (π.subgroupComap D).comp σ = MonoidHom.id D) ∧
    ∀ x : E, π x ∈ D → orderOf (π x) = 2 → orderOf x = 2 := by
  classical
  set R := D.comap π with hRdef
  set A := ⁅R, R⁆ with hAdef
  have hz2 : z ^ 2 = 1 := by rw [← hzorder]; exact pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := by rw [← htorder]; exact pow_orderOf_eq_one t
  have hπk : ∀ x, π x = 1 → x ∈ zpowers t := fun x hx => hker ▸ hx
  have hkerc : ∀ c ∈ zpowers t, c ∈ center E ∧ c ^ 2 = 1 := by
    intro c hc
    rcases eq_one_or_eq_of_mem_zpowers htorder hc with h | h
    · subst h
      exact ⟨one_mem _, one_pow 2⟩
    · rw [h]
      exact ⟨htcenter, ht2⟩
  have hπt : π t = 1 := by
    have h : t ∈ π.ker := hker ▸ mem_zpowers t
    exact h
  have htR : t ∈ R := by
    change π t ∈ D
    rw [hπt]
    exact one_mem D
  have hmapR : R.map π = D := map_comap_eq_self_of_surjective hπ D
  have hmapA : A.map π = D := by
    rw [hAdef, map_commutator, hmapR]
    exact isPerfect_iff.mp hD
  have hsup : A ⊔ zpowers t = R := by
    have h := comap_map_eq π A
    rw [hmapA, hker] at h
    exact h.symm
  have hAR : A ≤ R := hsup ▸ le_sup_left
  have htA : t ∉ A := by
    intro htA
    have hRA : A = R := le_antisymm hAR (hsup ▸ sup_le le_rfl (zpowers_le.mpr htA))
    have hRperf : Group.IsPerfect R := isPerfect_iff.mpr (hAdef ▸ hRA)
    obtain ⟨v, hv⟩ := hπ z
    obtain ⟨u, hu⟩ := hπ r
    obtain ⟨h, hh⟩ := hzr
    obtain ⟨k, hk⟩ := hπ h
    have huR : u ∈ R := by
      change π u ∈ D
      rw [hu]
      exact hrD
    have hcen : ∀ w : R, v * w * v⁻¹ * (w : E)⁻¹ ∈ center E := by
      intro w
      apply (hkerc _ (hπk _ ?_)).1
      have hwD : π w ∈ D := w.2
      have hcomm := mem_centralizer_iff.mp hzD (π w) hwD
      simp only [map_mul, map_inv, hv]
      rw [← hcomm]
      group
    let f : R →* center E :=
      { toFun := fun w => ⟨v * w * v⁻¹ * (w : E)⁻¹, hcen w⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun w₁ w₂ => by
          apply Subtype.ext
          have hc₂ := mem_center_iff.mp (hcen w₂) (w₁ : E)⁻¹
          change v * ((w₁ : E) * w₂) * v⁻¹ * ((w₁ : E) * w₂)⁻¹ =
            (v * w₁ * v⁻¹ * (w₁ : E)⁻¹) * (v * w₂ * v⁻¹ * (w₂ : E)⁻¹)
          calc v * ((w₁ : E) * w₂) * v⁻¹ * ((w₁ : E) * w₂)⁻¹
              = v * w₁ * v⁻¹ * ((v * w₂ * v⁻¹ * (w₂ : E)⁻¹) * (w₁ : E)⁻¹) := by group
            _ = v * w₁ * v⁻¹ * ((w₁ : E)⁻¹ * (v * w₂ * v⁻¹ * (w₂ : E)⁻¹)) := by rw [← hc₂]
            _ = (v * w₁ * v⁻¹ * (w₁ : E)⁻¹) * (v * w₂ * v⁻¹ * (w₂ : E)⁻¹) := by group }
    have hf : f = 1 := PerfectAutomorphisms.hom_eq_one_of_commutative f
    have hvR : ∀ w ∈ R, v * w = w * v := by
      intro w hw
      have h1 := congrArg (fun φ : R →* center E => ((φ ⟨w, hw⟩ : center E) : E)) hf
      have h2 : v * w * v⁻¹ * w⁻¹ = 1 := h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have hv2 : v ^ 2 ∈ center E := (hkerc _ (hπk _ (by rw [map_pow, hv, hz2]))).1
    have hc : (v * u)⁻¹ * (k * v * k⁻¹) ∈ zpowers t := hπk _ (by
      simp only [map_mul, map_inv, hv, hu, hk, hh]
      group)
    obtain ⟨hcc, hc2⟩ := hkerc _ hc
    set c := (v * u)⁻¹ * (k * v * k⁻¹) with hcdef
    have hkv : k * v * k⁻¹ = v * u * c := by rw [hcdef]; group
    have hu2 : u ^ 2 = 1 := by
      have h1 : k * v ^ 2 * k⁻¹ = v ^ 2 := by
        rw [mem_center_iff.mp hv2 k, mul_inv_cancel_right]
      rw [← conj_pow, hkv, (show Commute (v * u) c from mem_center_iff.mp hcc (v * u)).mul_pow,
        hc2, mul_one, (show Commute v u from hvR u huR).mul_pow] at h1
      exact mul_eq_left.mp h1
    have hlift : ∀ x : E, π x ∈ D → orderOf (π x) = 2 → x ^ 2 = 1 := by
      intro x hxD hxord
      obtain ⟨d, -, hdr⟩ := hfusion (π x) hxD hxord
      obtain ⟨y, hy⟩ := hπ d
      have hc' : (y * u * y⁻¹)⁻¹ * x ∈ zpowers t := hπk _ (by
        simp only [map_mul, map_inv, hy, hu, hdr]
        group)
      obtain ⟨hc'c, hc'2⟩ := hkerc _ hc'
      set c' := (y * u * y⁻¹)⁻¹ * x with hc'def
      have hx : x = y * u * y⁻¹ * c' := by rw [hc'def]; group
      rw [hx, (show Commute (y * u * y⁻¹) c' from mem_center_iff.mp hc'c _).mul_pow, hc'2,
        mul_one, conj_pow, hu2]
      group
    let πR : R →* D := π.subgroupComap D
    let P : Subgroup R := (W : Subgroup D).comap πR
    have hPidx : P.index = (W : Subgroup D).index :=
      index_comap_of_surjective (W : Subgroup D) (π.subgroupComap_surjective D hπ)
    have hP2 : ∀ x ∈ P, x ^ 2 = 1 := by
      intro x hx
      apply Subtype.ext
      change (x : E) ^ 2 = 1
      by_cases h1 : π x = 1
      · exact (hkerc _ (hπk _ h1)).2
      · apply hlift (x : E) x.2
        apply orderOf_eq_prime _ h1
        have hW2 : ((πR x : D) : M) ^ 2 = 1 := by
          simpa using congrArg Subtype.val (hW (πR x) hx)
        exact hW2
    have hPgroup : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by
      rw [pow_one]
      exact hP2 _ x.2)⟩
    have hPcomm : IsMulCommutative P := ⟨⟨fun a b => by
      have hinv : ∀ y ∈ P, y⁻¹ = y := fun y hy =>
        inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hP2 y hy)
      apply Subtype.ext
      change (a : R) * b = b * a
      calc (a : R) * b = ((a : R) * b)⁻¹ := (hinv _ (mul_mem a.2 b.2)).symm
        _ = b * a := by rw [mul_inv_rev, hinv _ a.2, hinv _ b.2]⟩⟩
    let Psyl : Sylow 2 R := hPgroup.toSylow (hPidx ▸ W.not_dvd_index)
    have htP : (⟨t, htR⟩ : R) ∈ (Psyl : Subgroup R) := by
      change πR ⟨t, htR⟩ ∈ (W : Subgroup D)
      have h1 : πR ⟨t, htR⟩ = 1 := Subtype.ext hπt
      rw [h1]
      exact one_mem _
    have htRc : ((⟨⟨t, htR⟩, htP⟩ : (Psyl : Subgroup R)) : R) ∈ center R :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp htcenter g)
    have hmem := CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived Psyl
      ⟨⟨t, htR⟩, htP⟩ htRc
    have : IsMulCommutative (Psyl : Subgroup R) := hPcomm
    rw [commutator_eq_bot, mem_bot] at hmem
    have ht1 : t = 1 := congrArg (fun y : (Psyl : Subgroup R) => ((y : R) : E)) hmem
    rw [ht1, orderOf_one] at htorder
    omega
  have hinf : zpowers t ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxA⟩ := mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers htorder hxt with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ hxA) htA
  have hπA : ∀ a ∈ A, π a = 1 → a = 1 := by
    intro a ha h1
    have h : a ∈ zpowers t ⊓ A := mem_inf.mpr ⟨hπk a h1, ha⟩
    rwa [hinf, mem_bot] at h
  let φ : A →* D := (π.comp A.subtype).codRestrict D fun a => hAR a.2
  have hφ : ∀ a, (φ a : M) = π a := fun a => rfl
  have hφbij : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro a ha
      apply Subtype.ext
      exact hπA a a.2 (by simpa [hφ] using congrArg Subtype.val ha)
    · intro d
      have hd : (d : M) ∈ A.map π := by rw [hmapA]; exact d.2
      obtain ⟨a, ha, had⟩ := hd
      exact ⟨⟨a, ha⟩, Subtype.ext had⟩
  let e : A ≃* D := MulEquiv.ofBijective φ hφbij
  have he : ∀ a, (e a : M) = π a := fun a => rfl
  refine ⟨⟨hinf, by rw [sup_comm]; exact hsup, ?_, ?_⟩, ⟨e, he, ?_⟩, ?_⟩
  · have : (zpowers t).Normal := normal_of_le_center (zpowers_le.mpr htcenter)
    infer_instance
  · constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have h := map_subtype_commutator R
    have hn' : (n : E) ∈ (commutator R).map R.subtype := by rw [h, ← hAdef]; exact hn
    obtain ⟨b₀, hb₀, hb₀n⟩ := hn'
    have hb₀n' : b₀ = n := Subtype.ext hb₀n
    rw [hAdef, ← h]
    refine ⟨g * b₀ * g⁻¹, (inferInstance : (commutator R).Normal).conj_mem b₀ hb₀ g, ?_⟩
    rw [hb₀n']
    rfl
  · refine ⟨(Subgroup.inclusion hAR).comp e.symm.toMonoidHom, fun d => rfl, ?_⟩
    ext d
    change π ((e.symm d : A) : E) = d
    rw [← he, MulEquiv.apply_symm_apply]
  · intro x hxD hxord
    set a := e.symm ⟨π x, hxD⟩ with hadef
    have hπa : π a = π x := by
      rw [← he, hadef, MulEquiv.apply_symm_apply]
    have hc : (a : E)⁻¹ * x ∈ zpowers t := hπk _ (by rw [map_mul, map_inv, hπa, inv_mul_cancel])
    obtain ⟨hcc, hc2⟩ := hkerc _ hc
    have hπx2 : π x ^ 2 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one _
    have ha2 : (a : E) ^ 2 = 1 := hπA _ (pow_mem a.2 2) (by rw [map_pow, hπa, hπx2])
    have hx : x = a * ((a : E)⁻¹ * x) := by group
    apply orderOf_eq_prime
    · rw [hx, (show Commute (a : E) ((a : E)⁻¹ * x) from mem_center_iff.mp hcc _).mul_pow, ha2,
        hc2, one_mul]
    · intro h1
      rw [h1, map_one, orderOf_one] at hxord
      omega

end CFSG.ComponentClassification.CentralCover
