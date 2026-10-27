module

public import CFSG.GH74.GLS.C3.Layer2.L4ZD
public import CFSG.GH74.GLS.C3.Layer2.L4Bender

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.Uniqueness

section Preliminaries

theorem two_le_twoRank {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} (hK : Nat.card K = 4)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    2 ≤ Open.twoRank Y := by
  unfold Open.twoRank Open.pRank
  refine le_csSup ?_ ⟨K, le_top, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩,
    fun x hx => by simpa [sq] using hsq x hx⟩, by rw [hK]; norm_num⟩
  refine ⟨Nat.card Y, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  calc k ≤ 2 ^ k := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card E := hE.symm
    _ ≤ Nat.card Y := Subgroup.card_le_card_group E

theorem card_map_mk_mul_two {C : Type} [Group C] {v : C} [(zpowers v).Normal] (hv : v * v = 1)
    (hv1 : v ≠ 1) (H : Subgroup C) (hH : zpowers v ≤ H) :
    Nat.card (H.map (QuotientGroup.mk' (zpowers v))) * 2 = Nat.card H := by
  let φ : H →* C ⧸ zpowers v := (QuotientGroup.mk' (zpowers v)).comp H.subtype
  have hrange : φ.range = H.map (QuotientGroup.mk' (zpowers v)) := by
    show ((QuotientGroup.mk' (zpowers v)).comp H.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = (zpowers v).subgroupOf H := by
    ext e
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, φ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, Subgroup.subtype_apply]
    exact QuotientGroup.eq_one_iff _
  have hkercard : Nat.card φ.ker = 2 := by
    rw [hker]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hv) hv1
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hkercard, hrange] at h1
  rw [← h1]; ring

theorem exists_pair_of_card_four {Y : Type} [Group Y] {K : Subgroup Y} (hK : Nat.card K = 4) :
    ∃ a ∈ K, ∃ b ∈ K, a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a := by
  have hfin : Finite K := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [Nat.card_eq_zero_of_infinite] at hK
    omega
  have h2 : (K : Set Y).ncard = Nat.card K := (Nat.card_coe_set_eq _).symm
  by_contra hno
  push Not at hno
  by_cases ha : ∃ a ∈ K, a ≠ 1
  · obtain ⟨a, haK, ha1⟩ := ha
    have hsub : (K : Set Y) ⊆ {1, a} := by
      intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (hno a haK y hy ha1 hy1)
    have h1 : (K : Set Y).ncard ≤ ({1, a} : Set Y).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, a} : Set Y).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp
    omega
  · push Not at ha
    have hsub : (K : Set Y) ⊆ {1} := fun y hy => ha y hy
    have h1 : (K : Set Y).ncard ≤ ({1} : Set Y).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at h1
    omega

end Preliminaries

section Main

variable {C : Type} [Group C] [Finite C] {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

theorem normalizer_eq_top
    (hZD : S_ZD) (h : TIData v Zs S E x) (hS : Nat.card S ≤ 128)
    (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v) :
    normalizer (E : Set C) = ⊤ := by
  by_contra hne
  have hVn : (zpowers v).Normal := h.zpowers_normal
  set π : C →* C ⧸ zpowers v := QuotientGroup.mk' (zpowers v) with hπ
  set Zq : Set (C ⧸ zpowers v) := Zt v Zs with hZt
  set Y : Subgroup (C ⧸ zpowers v) := Subgroup.closure Zq with hY
  have hconcl := hZD (C ⧸ zpowers v) Zq (Mt v E) (isInvariantInvolutionSet_Zt h)
    (isProductDisconnected_Zt h hne)
  have hZinvX := (isInvariantInvolutionSet_Zt h).2
  have hYn : Y.Normal := by
    refine ⟨fun y hy g => ?_⟩
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      have := hZinvX y hy g⁻¹
      simpa using this
    | one => simp
    | mul y z _ _ hy hz =>
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this]; exact mul_mem hy hz
    | inv y _ hy =>
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hy
  set Eb : Subgroup (C ⧸ zpowers v) := E.map π with hEq
  have hEbcard : Nat.card Eb = 4 := by
    have h1 : Nat.card (E.map π) * 2 = Nat.card E :=
      card_map_mk_mul_two (v := v) h.v_sq h.v_ne E (zpowers_le.2 h.v_mem)
    rw [h.E_card] at h1
    show Nat.card (E.map π) = 4
    omega
  have hEbcomm : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := by
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
    simp only [← map_mul]
    rw [h.E_comm e₁ he₁ e₂ he₂]
  have hEbsq : ∀ a ∈ Eb, a * a = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h.E_sq e he, map_one]
  have hEbZ : ∀ a ∈ Eb, a ≠ 1 → a ∈ Zq := by
    rintro _ ⟨e, he, rfl⟩ hne1
    have h1 : e ≠ 1 := fun h1 => hne1 (by rw [h1, map_one])
    have h2 : e ≠ v := fun h2 =>
      hne1 (by rw [h2]; exact (QuotientGroup.eq_one_iff v).2 (mem_zpowers v))
    exact ⟨e, h.Zmem_of_mem_E he h1 h2, rfl⟩
  have hEbY : Eb ≤ Y := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]; exact one_mem _
    · exact Subgroup.subset_closure (hEbZ a ha ha1)
  have hZSq : ∀ a ∈ Zq, a ∈ S.map π → a ∈ Eb := by
    rintro _ ⟨z, hz, rfl⟩ hzS
    have hzS' : z ∈ S := mem_S_of_mk_mem_map h hzS
    exact ⟨z, ((h.Z_inter z hzS').1 hz).1, rfl⟩
  set K4 : Subgroup ↥Y := Eb.subgroupOf Y with hK4
  have hK4card : Nat.card K4 = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEbY).toEquiv).trans hEbcard
  have hK4comm : ∀ a ∈ K4, ∀ b ∈ K4, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hEbcomm _ ha _ hb)
  have hK4sq : ∀ a ∈ K4, a * a = 1 := fun a ha => Subtype.ext (hEbsq _ ha)
  set Zset : Set ↥Y := {l | (l : C ⧸ zpowers v) ∈ Zq} with hZset
  have hK4Z : ∀ y ∈ K4, y ≠ 1 → y ∈ Zset :=
    fun y hy hy1 => hEbZ _ hy (fun h1 => hy1 (Subtype.ext h1))
  rcases hconcl with hrank | ⟨u, huM, hu2, hDsup, hDinf, hcomm, hOD, hOM, hBend, hBorel, hZu⟩
  · have h2 : Open.twoRank ↥Y ≤ 1 := hrank
    have := two_le_twoRank hK4card hK4comm hK4sq
    omega
  ·
    obtain ⟨a, haK, b, hbK, ha1, hb1, hba⟩ := exists_pair_of_card_four hK4card
    have hu2' : u * u = 1 := by rw [← sq]; exact hu2
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
    have haZ := hK4Z a haK ha1
    have hbZ := hK4Z b hbK hb1
    have habK : a * b ∈ K4 := K4.mul_mem haK hbK
    have hab1 : a * b ≠ 1 := by
      intro h1
      apply hba
      have := mul_eq_one_iff_eq_inv.1 h1
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (hK4sq b hbK)).symm
    have habZ := hK4Z _ habK hab1
    obtain ⟨⟨d₁, hd₁, hd₁'⟩, -⟩ := hZu a haZ
    obtain ⟨⟨d₂, hd₂, hd₂'⟩, -⟩ := hZu b hbZ
    obtain ⟨⟨d₃, hd₃, hd₃'⟩, -⟩ := hZu _ habZ
    have hmemD : a * b ∈ commutator ↥Y := by
      rw [hd₁', hd₂']
      have : u * d₁ * (u * d₂) = (u * d₁ * u⁻¹) * d₂ := by
        rw [hui]; group
      rw [this]
      exact mul_mem ((inferInstance : (commutator ↥Y).Normal).conj_mem d₁ hd₁ u) hd₂
    have huD : u ∈ commutator ↥Y := by
      have : u = (a * b) * d₃⁻¹ := by rw [hd₃']; group
      rw [this]; exact mul_mem hmemD (inv_mem hd₃)
    have hu1 : u = 1 := by
      have : u ∈ commutator ↥Y ⊓ zpowers u := ⟨huD, mem_zpowers u⟩
      rw [hDinf, Subgroup.mem_bot] at this
      exact this
    subst hu1
    have hperf : commutator ↥Y = ⊤ := by
      have := hDsup
      rwa [Subgroup.zpowers_one_eq_bot, sup_bot_eq] at this
    have hZO : ∀ z ∈ Zset, z ∉ pPrimeCore 2 ↥Y := by
      intro z hz hzO
      exact (hZu z hz).2 z hzO (one_mul z).symm
    have hSyl' : IsSylowOf 2 (S.map π) ⊤ := isSylowOf_map_S h
    have hSylY : IsSylowOf 2 (S.map π ⊓ Y) Y :=
      hSyl'.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 hYn).ge
    set R : Subgroup ↥Y := (S.map π ⊓ Y).subgroupOf Y with hR
    have hmapR : R.map Y.subtype = S.map π ⊓ Y := by
      rw [hR, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 inf_le_right]
    have hmapTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hRSyl : IsSylowOf 2 R ⊤ := by
      rw [← isSylowOf_map_subtype_iff Y, hmapR, hmapTop]
      exact hSylY
    have hZinvY : ∀ z ∈ Zset, ∀ g : ↥Y, g * z * g⁻¹ ∈ Zset := by
      intro z hz g
      have := hZinvX (z : C ⧸ zpowers v) hz ((g : C ⧸ zpowers v)⁻¹)
      simpa [hZset] using this
    have hZ2Y : ∀ z ∈ Zset, z * z = 1 := by
      intro z hz
      have h2 : orderOf (z : C ⧸ zpowers v) = 2 := (isInvariantInvolutionSet_Zt h).1 _ hz
      have : (z : C ⧸ zpowers v) * z = 1 := by
        rw [← sq, ← h2]; exact pow_orderOf_eq_one _
      exact Subtype.ext this
    have hK4R : K4 ≤ R := by
      intro y hy
      show (y : C ⧸ zpowers v) ∈ S.map π ⊓ Y
      exact ⟨Subgroup.map_mono h.E_le hy, y.2⟩
    have hRZ : ∀ y ∈ R, y ∈ Zset → y ∈ K4 := by
      intro y hyR hyZ
      have hyS : (y : C ⧸ zpowers v) ∈ S.map π := (show (y : C ⧸ zpowers v) ∈ S.map π ⊓ Y from hyR).1
      exact hZSq _ hyZ hyS
    obtain ⟨hinvK, hcardR⟩ :=
      bender_sylow_card hZinvY hZ2Y hperf hBend hZO hRSyl hK4R hK4card hK4Z hRZ
    have hR4 : Nat.card R = 4 := by
      rcases hcardR with h4 | h64
      · exact h4
      · exfalso
        have hSqcard : Nat.card (S.map π) ≤ 64 := by
          have h1 : Nat.card (S.map π) * 2 = Nat.card S :=
            card_map_mk_mul_two (v := v) h.v_sq h.v_ne S h.zpowers_le_S
          omega
        have hRcard : Nat.card R = Nat.card ↥(S.map π ⊓ Y) := by
          rw [← hmapR]
          exact (Nat.card_congr (Subgroup.equivMapOfInjective R Y.subtype Y.subtype_injective).toEquiv)
        have hle : S.map π ⊓ Y ≤ S.map π := inf_le_left
        have hcard' : Nat.card (S.map π) ≤ Nat.card ↥(S.map π ⊓ Y) := by omega
        have hSY : S.map π ⊓ Y = S.map π := Subgroup.eq_of_le_of_card_ge hle hcard'
        have hSqY : S.map π ≤ Y := by rw [← hSY]; exact inf_le_right
        obtain ⟨s, hsS, hss, hsE⟩ := hex
        have hπs : π s ∈ S.map π ⊓ Y := ⟨⟨s, hsS, rfl⟩, hSqY ⟨s, hsS, rfl⟩⟩
        have hyR : (⟨π s, hSqY ⟨s, hsS, rfl⟩⟩ : ↥Y) ∈ R := hπs
        have hyK : (⟨π s, hSqY ⟨s, hsS, rfl⟩⟩ : ↥Y) ∈ K4 :=
          hinvK _ hyR (Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, hss, map_one]; rfl))
        obtain ⟨e, he, hes⟩ := (show π s ∈ Eb from hyK)
        have hes' : (QuotientGroup.mk e : C ⧸ zpowers v) = QuotientGroup.mk s := hes
        have h1 : e⁻¹ * s ∈ zpowers v := QuotientGroup.eq.1 hes'
        apply hsE
        have : s = e * (e⁻¹ * s) := by group
        rw [this]
        exact E.mul_mem he (zpowers_le.2 h.v_mem h1)
    have hRK : K4 = R := Subgroup.eq_of_le_of_card_ge hK4R (by rw [hR4, hK4card])
    have hSY : S.map π ⊓ Y = Eb := by
      rw [← hmapR, ← hRK, hK4, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEbY]
    set L : Subgroup C := Y.comap π with hL
    have hLn : L.Normal := Subgroup.normal_comap π
    have hvL : v ∈ L := by
      show π v ∈ Y
      have : π v = 1 := (QuotientGroup.eq_one_iff v).2 (mem_zpowers v)
      rw [this]; exact one_mem _
    have hEL : E = S ⊓ L := by
      apply le_antisymm
      · intro e he
        exact ⟨h.E_le he, hEbY ⟨e, he, rfl⟩⟩
      · rintro y ⟨hyS, hyL⟩
        have hy1 : π y ∈ S.map π ⊓ Y := ⟨⟨y, hyS, rfl⟩, hyL⟩
        rw [hSY] at hy1
        obtain ⟨e, he, hey⟩ := hy1
        have hey' : (QuotientGroup.mk e : C ⧸ zpowers v) = QuotientGroup.mk y := hey
        have h1 : e⁻¹ * y ∈ zpowers v := QuotientGroup.eq.1 hey'
        have : y = e * (e⁻¹ * y) := by group
        rw [this]
        exact E.mul_mem he (zpowers_le.2 h.v_mem h1)
    have hLperf : L ≤ ⁅L, L⁆ ⊔ zpowers v := by
      intro g hg
      have hgY : π g ∈ Y := hg
      have hYY : ⁅Y, Y⁆ = Y := by
        have h1 : (commutator ↥Y).map Y.subtype = ⁅Y, Y⁆ := by
          show Subgroup.map Y.subtype ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = _
          rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
        rw [← h1, hperf, Subgroup.map_top, Subgroup.range_subtype]
      have hLmap : L.map π = Y :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Y
      have hmem : π g ∈ (⁅L, L⁆).map π := by
        rw [Subgroup.map_commutator, hLmap, hYY]; exact hgY
      obtain ⟨k, hk, hkg⟩ := hmem
      have hkg' : (QuotientGroup.mk k : C ⧸ zpowers v) = QuotientGroup.mk g := hkg
      have h1 : k⁻¹ * g ∈ zpowers v := QuotientGroup.eq.1 hkg'
      have : g = k * (k⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hk h1
    exact no_perfect_extension (L := L) h.v_sq h.v_ne h.v_comm hvL h.sylow hZS hEL h.E_card
      h.E_comm h.v_mem hLperf

end Main

end CFSG.GH74.GLS.C3.Layer2.L4
