module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28EndgameMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Reduced

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Red (Red pr)

variable {X : Type} [Group X] [Finite X]

namespace EndData

variable {F U M N R : Subgroup X} {x : X}

theorem map_pr (hd : EndData F U M N R x) :
    EndData (F.map (pr X)) (U.map (pr X)) (M.map (pr X)) (N.map (pr X)) (R.map (pr X))
      (pr X x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : IsPGroup 3 F := hd.sylow.isPGroup
  have hU3 : IsPGroup 3 U := elementary_isPGroup 3 U hd.toFData.U_elem
  have hxU : x ∈ U := hd.toFData.x_mem
  refine
    { toFData :=
        { card_F := by rw [GL83P3L28Red.card_map hF3, hd.toFData.card_F]
          nonab := fun hc => hd.toFData.nonab (IsMulCommutative.of_comm fun a b => by
            have h := setLike_mul_comm (s := F.map (pr X)) (Subgroup.mem_map_of_mem _ a.2)
              (Subgroup.mem_map_of_mem _ b.2)
            exact Subtype.ext (GL83P3L28Red.injOn_pr hF3 (F.mul_mem a.2 b.2) (F.mul_mem b.2 a.2)
              (by simpa using h)))
          U_le := Subgroup.map_mono hd.toFData.U_le
          U_elem := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hd.toFData.U_elem
            (pr X)
          U_card := by rw [GL83P3L28Red.card_map hU3, hd.toFData.U_card]
          omega := by
            rintro _ ⟨f, hf, rfl⟩ h3
            have hker : f ^ 3 ∈ (pr X).ker := by
              rw [MonoidHom.mem_ker, map_pow]
              exact h3
            rw [GL83P3L28Red.ker_pr] at hker
            have hbot := GL83P3L28Red.inf_core_eq_bot hF3
            have hf3 : f ^ 3 = 1 := by
              have : f ^ 3 ∈ F ⊓ primeComplementCore (G := X) 3 := ⟨F.pow_mem hf 3, hker⟩
              rwa [hbot, mem_bot] at this
            exact ⟨f, hd.toFData.omega f hf hf3, rfl⟩
          x_mem := ⟨x, hxU, rfl⟩
          x_ne := fun h => hd.toFData.x_ne (GL83P3L28Red.injOn_pr hU3 hxU (U.one_mem)
            (by rw [h, map_one]))
          x_cent := by
            rintro _ ⟨f, hf, rfl⟩
            rw [← map_mul, ← map_mul, hd.toFData.x_cent f hf] }
      catalog := GL83P3L28Red.catalog_red hd.catalog
      sylow := GL83P3L28Red.sylow_map hd.sylow
      F_le := Subgroup.map_mono hd.F_le
      cover := ?_
      N_le := Subgroup.map_mono hd.N_le
      N_norm := ?_
      N_cop := fun h => hd.N_cop (h.trans (Subgroup.card_map_dvd N (pr X)))
      R_le := Subgroup.map_mono hd.R_le
      R_two := hd.R_two.map (pr X)
      R_norm := ?_ }
  · rintro _ ⟨u, hu, rfl⟩ hux y hy
    have hu3 : u ^ 3 ^ 1 = 1 := by simpa using hd.toFData.U_elem.2 u hu
    obtain ⟨c, hc, rfl⟩ := GL83P3L28Red.lift_centralizer hu3
      (mem_centralizer_singleton_iff.mp hy)
    refine ⟨c, hd.cover u hu ?_ (mem_centralizer_singleton_iff.mpr hc), rfl⟩
    rintro ⟨k, hk⟩
    exact hux ⟨k, by simpa [map_zpow] using congrArg (pr X) hk⟩
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨m * n * m⁻¹, hd.N_norm m hm n hn, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨u * r * u⁻¹, ((mem_normalizer_iff.mp (hd.R_norm hu)) r).mp hr, by simp⟩
    · rintro ⟨r', hr', hr'e⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ h
      have hg' : u⁻¹ * r' * u ∈ R := ((mem_normalizer_iff.mp (hd.R_norm hu)) _).mpr
        (by simpa [mul_assoc] using hr')
      refine ⟨u⁻¹ * r' * u, hg', ?_⟩
      rw [map_mul, map_mul, map_inv, hr'e]
      group

theorem R_le_core (hd : EndData F U M N R x) (hCen : KFactCentralOmega)
    (hM27 : KFactSylowM27) (hGen : KFactFieldGeneration) :
    R ≤ primeComplementCore (G := X) 3 := by
  have h := hd.map_pr.R_eq_bot GL83P3L28Red.core_red hCen hM27 hGen
  intro r hr
  have h1 : pr X r ∈ R.map (pr X) := ⟨r, hr, rfl⟩
  rw [h, mem_bot] at h1
  rw [← GL83P3L28Red.ker_pr]
  exact h1

end EndData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem kFactL28Endgame_holds (hCen : KFactCentralOmega) (hM27 : KFactSylowM27)
    (hGen : KFactFieldGeneration) : KFactL28Endgame := by
  intro G _ _ H M F U R₀ x hH hF hnonab hFcard hFM hUF hUe hUc hΩ hxU hx1 hxc hcov hR2 hRH hUR hRM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFH : F ≤ H := hF.le
  have hcard : ∀ {S : Subgroup G}, S ≤ H → Nat.card (S.subgroupOf H) = Nat.card S :=
    fun hS => Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv
  have hUH : U ≤ H := hUF.trans hFH
  have hxH : x ∈ H := hUH hxU
  set xt : H := ⟨x, hxH⟩ with hxt
  have hd : GL83P3L28End.EndData (F.subgroupOf H) (U.subgroupOf H) (M.subgroupOf H)
      ((GLBPrimeCore 3 M).subgroupOf H) (R₀.subgroupOf H) xt :=
    { toFData :=
        { card_F := (hcard hFH).trans hFcard
          nonab := fun hc => hnonab (IsMulCommutative.of_comm fun a b => by
            have := hc
            have h := setLike_mul_comm (s := F.subgroupOf H)
              (a := (⟨a, hFH a.2⟩ : H)) (b := (⟨b, hFH b.2⟩ : H))
              (mem_subgroupOf.mpr a.2) (mem_subgroupOf.mpr b.2)
            exact Subtype.ext (congrArg (fun z : H => (z : G)) h))
          U_le := fun y hy => mem_subgroupOf.mpr (hUF (mem_subgroupOf.mp hy))
          U_elem := ⟨IsMulCommutative.of_comm fun a b => by
              have := hUe.1
              exact Subtype.ext (Subtype.ext (setLike_mul_comm (s := U)
                (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2))),
            fun y hy => Subtype.ext (hUe.2 _ (mem_subgroupOf.mp hy))⟩
          U_card := (hcard hUH).trans hUc
          omega := fun f hf h3 => mem_subgroupOf.mpr (hΩ _ (mem_subgroupOf.mp hf)
            (by simpa using congrArg Subtype.val h3))
          x_mem := mem_subgroupOf.mpr hxU
          x_ne := fun h => hx1 (congrArg Subtype.val h)
          x_cent := fun f hf => Subtype.ext (hxc _ (mem_subgroupOf.mp hf)) }
      catalog := hH
      sylow := by
        rw [← isSylowOf_map_subtype_iff H, subgroupOf_map_subtype, inf_eq_left.mpr hFH,
          ← MonoidHom.range_eq_map, range_subtype]
        exact hF
      F_le := fun y hy => mem_subgroupOf.mpr (hFM (mem_subgroupOf.mp hy))
      cover := by
        intro u hu hux y hy
        have hux' : (u : G) ∉ zpowers x := by
          rintro ⟨k, hk⟩
          exact hux ⟨k, Subtype.ext (by simpa using hk)⟩
        refine mem_subgroupOf.mpr (hcov (u : G) (mem_subgroupOf.mp hu) hux' ⟨?_, y.2⟩)
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      N_le := fun y hy => mem_subgroupOf.mpr (glbPrimeCore_le 3 M (mem_subgroupOf.mp hy))
      N_norm := fun m hm n hn => mem_subgroupOf.mpr
        ((mem_normalizer_iff.mp (le_normalizer_glbPrimeCore 3 M (mem_subgroupOf.mp hm)) _).mp
          (mem_subgroupOf.mp hn))
      N_cop := by
        intro h3
        have h1 : Nat.card ((GLBPrimeCore 3 M).subgroupOf H) =
            Nat.card ↥(GLBPrimeCore 3 M ⊓ H) := by
          rw [← subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]
        rw [h1] at h3
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
          (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
      R_le := fun y hy => mem_subgroupOf.mpr (hRM (mem_subgroupOf.mp hy))
      R_two := hR2.comap_subtype
      R_norm := by
        intro u hu
        rw [mem_normalizer_iff]
        intro h
        exact (mem_normalizer_iff.mp (hUR (mem_subgroupOf.mp hu)) (h : G)) }
  have hle := hd.R_le_core hCen hM27 hGen
  intro r hr
  have hr' : (⟨r, hRH hr⟩ : H) ∈ primeComplementCore (G := H) 3 := hle (mem_subgroupOf.mpr hr)
  rw [← glbPrimeCore_subgroupOf 3 H] at hr'
  exact mem_subgroupOf.mp hr'

end CFSG.LocalAnalysis.RankThreeTheoremC
