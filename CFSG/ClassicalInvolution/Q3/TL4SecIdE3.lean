module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdRed
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2
public import CFSG.ClassicalInvolution.Q3.TL3CentStep

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem center_eq_bot_of_muZ2 (hB3 : GoldschmidtB3Tmp) (hm : EdgelessMember3 R S t)
    (hmu : MuZ2Member R) (hnc : t ∉ Subgroup.center Y) : Subgroup.center Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hm.datum
  obtain ⟨hq, hgen, hodd⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) ∧
      TightSelfGen R ∧ TightOddFree Y := hm.cls
  have hodd' : classicalInvolutionOddCore Y = ⊥ := hodd
  obtain ⟨T, hST, hTt⟩ := MFMuZ2.exists_sylow_le_centralizer hd hm.edgeless
  have h16 := MFMuZ2.card_sylow_eq_sixteen hB3 hd hq hgen hodd' hnc hm.edgeless
    (MFMuZ2.allTypeTwo_of_muZ2Member hd hm.edgeless hmu) T hST hTt
  by_contra hne
  obtain ⟨c, hcZ, hc⟩ := exists_central_involution_of_center_ne_bot hodd' hne
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀K : S₀ ≤ tightCore R := hd.sylow_core.1
  have hut := hd.isUniqueInvolution_core
  have hct : c ≠ t := fun h => hnc (h ▸ hcZ)
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc; exact absurd hc (by norm_num)
  have hcc : c * c = 1 := by rw [← pow_two, ← hc, pow_orderOf_eq_one]
  have hCn : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcZ)
  have hC2 : IsPGroup 2 ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hCT : Subgroup.zpowers c ≤ (T : Subgroup Y) := hC2.le_sylow_of_normal T
  have hdisj : Disjoint S₀ (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxc
    rcases mem_zpowers_of_orderOf_two hc hxc with h | h
    · exact h
    · subst h
      rcases hut.unique x (hS₀K hxS) hcc with h' | h'
      · exact absurd h' hc1
      · exact absurd h' hct
  have hS₀8 : Nat.card ↥S₀ = 8 := by
    obtain ⟨e⟩ := hq
    rw [hS₀, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hsup16 : Nat.card ↥(S₀ ⊔ Subgroup.zpowers c) = 16 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S₀ _
      (fun x hx => Subgroup.mem_normalizer_iff.mpr fun y => by
        have hxy : y * x = x * y :=
          Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hcZ hx) y
        rw [show x * y * x⁻¹ = y by rw [← hxy]; group])
      hdisj, hS₀8, Nat.card_zpowers, hc]
  have hTeq : (T : Subgroup Y) = S₀ ⊔ Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (sup_le hST hCT) (by rw [h16, hsup16])).symm
  have htT : t ∈ (T : Subgroup Y) := hST hd.mem
  have htZT : (⟨t, htT⟩ : (T : Subgroup Y)) ∈ Subgroup.center (T : Subgroup Y) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTt s.2)
  obtain ⟨g, hgT₀, hgt₀⟩ := exists_conj_mem_sylow_ne hodd' T ⟨t, htT⟩ htZT
    (by rw [Subgroup.orderOf_mk]; exact hd.order) hnc
  have hgt : g * t * g⁻¹ ≠ t := hgt₀
  have hgT : g * t * g⁻¹ ∈ S₀ ⊔ Subgroup.zpowers c := by
    rw [← hTeq]
    exact hgT₀
  obtain ⟨s, hs, d, hdc, hsd⟩ := Subgroup.mem_sup_of_normal_right.mp hgT
  have hgt2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hut.sq]; group
  have hdZ : d ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr hcZ hdc
  have hss : s * s = 1 := by
    have h1 : (s * d) * (s * d) = (s * s) * (d * d) := by
      rw [show s * d * (s * d) = s * (d * s) * d by group,
        ← Subgroup.mem_center_iff.mp hdZ s]
      group
    have hdd : d * d = 1 := by
      rcases mem_zpowers_of_orderOf_two hc hdc with h | h
      · rw [h, mul_one]
      · rw [h, hcc]
    rw [hsd, hgt2, hdd, mul_one] at h1
    exact h1.symm
  have hEdge := hm.edgeless
  have hd' : d = 1 ∨ d = c := mem_zpowers_of_orderOf_two hc hdc
  rcases hut.unique s (hS₀K hs) hss with hs1 | hs1 <;> rcases hd' with hd1 | hd1 <;>
    rw [hs1, hd1] at hsd
  ·
    rw [mul_one] at hsd
    exact hut.ne_one (by
      have := congrArg (fun x => g⁻¹ * x * g) hsd
      simpa [mul_assoc] using this.symm)
  ·
    rw [one_mul] at hsd
    apply hct
    have h1 : t = g⁻¹ * c * g := by rw [hsd]; group
    rw [h1, Subgroup.mem_center_iff.mp hcZ g⁻¹]
    group
  ·
    rw [mul_one] at hsd
    exact hgt hsd.symm
  ·
    exact TightDatum.not_edgeless_of_twin hd hcZ hc1 hsd.symm hEdge

theorem secIdE3MuZ2_of (hB3 : GoldschmidtB3Tmp) (hT : MuZ2Table) : SecIdE3MuZ2 := by
  intro Y _ _ R S t hm hmu hO2 hx
  have hnc : t ∉ Subgroup.center Y := fun h => by
    refine hO2 ⟨Subgroup.zpowers t, Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h),
      IsPGroup.of_card (n := 1) ?_, Subgroup.mem_zpowers t⟩
    rw [Nat.card_zpowers, hm.datum.order, pow_one]
  have hZ := center_eq_bot_of_muZ2 hB3 hm hmu hnc
  have h32 := MFMuZ2.not_thirtyTwo_dvd_card hB3 hm hmu hnc
  have hZF : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
    have h1 := TightDatum.center_genFittingFStar_le hm.datum hm.cls hO2
    rw [hZ, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar Y).subtype_injective).mp h1
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv hZF
  have hM12 : ¬ NativeSporadic.IsSporadic (FStarQuot Y) .M12 := fun h =>
    h32 ((MFMuZ2.thirtyTwo_dvd_card_m12 h).trans MFMuZ2.card_fstarQuot_dvd)
  rcases hx with ⟨-, hX | hTw⟩ | hE
  · rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl, hi6⟩⟩ | ⟨hm12, -⟩
    · have := (CFSG.LieType.Catalog.lieModel_finite_simple (FStarQuot Y) _ _ _ _ hl).2.2
      exact ⟨eF.isSimpleGroup, hi, Or.inl ⟨p, f, hp, hp2, Or.inl ⟨hf, hl⟩⟩⟩
    · have : IsSimpleGroup (FStarQuot Y) := by
        rcases hl with hl | hl <;>
          exact (CFSG.LieType.Catalog.lieModel_finite_simple (FStarQuot Y) _ _ _ _ hl).2.2
      have hFs : IsSimpleGroup ↥(genFittingFStar Y) := eF.isSimpleGroup
      obtain ⟨hTL3, hTU3, -⟩ := hT Y R S t hm hmu hFs hi6
      have hYs : IsSimpleGroup Y := by
        rcases hl with hl | hl
        · exact (hTL3 p f hl).1
        · exact (hTU3 p f hl).1
      have hi : (genFittingFStar Y).index ≤ 2 := by
        have := genFittingFStar_normal Y
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (genFittingFStar Y) with h | h
        · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hFs.toNontrivial)
        · rw [h, Subgroup.index_top]
          norm_num
      exact ⟨hFs, hi, Or.inl ⟨p, f, hp, hp2, Or.inr hl⟩⟩
    · exact absurd hm12 hM12
  · exfalso
    obtain ⟨L, -, -, -, -, -, hFc, hFL⟩ := hTw
    rw [hZ] at hFc
    exact hFL (hFc.trans bot_le)
  · exfalso
    exact h32 ((MFMuZ2.thirtyTwo_dvd_card_m12 hE).trans (Subgroup.card_quotient_dvd_card _))

end CFSG.ClassicalInvolution.Q3.TL4
