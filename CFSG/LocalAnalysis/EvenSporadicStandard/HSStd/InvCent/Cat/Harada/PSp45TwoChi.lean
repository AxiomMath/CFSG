module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45TwoMat
public import Certificates.Certificate27231
public import Certificates.Certificate27232
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGMain

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.EvenSporadicStandard.TwoHS
  CFSG.EvenSporadicStandard.TwoHS.GH312

theorem card_and_simple_of_lieModel {S : Type} [Group S] (hS : LieModel S .PSp 2 5 1) :
    Nat.card S = 4680000 ∧ IsSimpleGroup S := by
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hS.statedClassicalModel_of_ne_zero (by norm_num)
  have e : S ≃* StatedProj (StatedSp 2 (ZMod 5)) :=
    e0.trans (statedProjStatedSpEquivZModFive (by simpa using hK))
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 (ZMod 5))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 5) 2 (by norm_num)
      (Or.inl (Or.inr (by rw [Nat.card_zmod]; norm_num)))
  exact ⟨by rw [Nat.card_congr e.toEquiv, natCard_statedProj_statedSp_zmod_five],
    e.isSimpleGroup⟩

theorem chiPG_surjective :
    Function.Surjective chiPG := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨mkPG pgS1 pgS1_so, chi_s1 Certificates.certificate27232.toMatrix
      Certificates.certificate27231.toMatrix⟩

theorem card_ker_chiPG
    (hX : Nat.card PGSp45 = 9360000) : Nat.card chiPG.ker = 4680000 := by
  have h1 : chiPG.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 chiPG_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h2 := chiPG.ker.card_mul_index
  rw [h1, hX] at h2
  omega

theorem ker_chiPG_le_range
    {G : Type} [Group G] [Finite G] (S : Subgroup G) [S.Normal] (hsimple : IsSimpleGroup ↥S)
    (hS4 : Nat.card S = 4680000) {ψ : G →* PGSp45} (hψ : PGSp45Emb ψ) :
    chiPG.ker ≤ ψ.range := by
  have hK := card_ker_chiPG hψ.card
  have hSK : S.map ψ ≤ chiPG.ker := by
    let φ : ↥S →* ℤˣ := chiPG.comp (ψ.comp S.subtype)
    have hker : φ.ker = ⊤ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exfalso
        have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
        have := Nat.card_le_card_of_injective φ hinj
        rw [hS4, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
        omega
      · exact h
    rintro _ ⟨s, hs, rfl⟩
    have : (⟨s, hs⟩ : ↥S) ∈ φ.ker := by rw [hker]; exact mem_top _
    exact this
  have hmap : Nat.card (S.map ψ) = 4680000 := by
    rw [Subgroup.card_map_of_injective hψ.inj, hS4]
  have heq : S.map ψ = chiPG.ker := Subgroup.eq_of_le_of_card_ge hSK (by rw [hK, hmap])
  rw [← heq]
  exact Subgroup.map_le_range ψ S

namespace PGSp45Emb

variable {G : Type} [Group G] [Finite G] {ψ : G →* PGSp45} (h : PGSp45Emb ψ)

include h

theorem exists_cent_of_mem_range {u : G} {z : PGSp45} (hz : z ∈ ψ.range)
    (hcomm : z * ψ u = ψ u * z) : ∃ w ∈ centralizer ({u} : Set G), ψ w = z := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨w, mem_centralizer_singleton_iff.2 ?_, hw⟩
  apply h.inj
  rw [map_mul, map_mul, hw]
  exact hcomm

end PGSp45Emb

theorem chi_sf :
    chiPG (mkPG pgSf0 pgSf0_so) = 1 := by
  have h0 : mkPG (pgRefl 0) (pgRefl_so (by norm_num)) = mkPG pgSf0 pgSf0_so :=
    pg_ext (by simp [pgRefl])
  have := chi_refl_0 Certificates.certificate27232.toMatrix
    Certificates.certificate27231.toMatrix
  rwa [h0] at this

theorem chi_yy :
    chiPG (mkPG pgR0 pgR0_so * mkPG pgS1 pgS1_so) = 1 := by
  rw [map_mul, chi_R Certificates.certificate27232.toMatrix
    Certificates.certificate27231.toMatrix,
    chi_s1 Certificates.certificate27232.toMatrix
    Certificates.certificate27231.toMatrix]
  exact Int.units_mul_self (-1)

theorem chi_c5 : chiPG (mkPG mC5 mC5_so) = 1 := by
  have h5 : mkPG mC5 mC5_so ^ 5 = 1 := pg_ext (by rw [pg_pow_val, mkPG_val, mC5_pow, pg_one_val])
  have h := congrArg chiPG h5
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (chiPG (mkPG mC5 mC5_so)) with h' | h'
  · exact h'
  · rw [h'] at h
    exact absurd h (by decide)

theorem commute_conj_of_central {G : Type} [Group G] [Finite G] {ψ : G →* PGSp45}
    (hψ : PGSp45Emb ψ) (hker : chiPG.ker ≤ ψ.range) {t v : G}
    (hv : ∀ w ∈ centralizer ({t} : Set G), v * w = w * v) {g : PGSp45}
    (hg : g * ψ t * g⁻¹ = mkPG pgTau1 pgTau1_so) {z : PGSp45} (hz : chiPG z = 1)
    (hzτ : z * mkPG pgTau1 pgTau1_so = mkPG pgTau1 pgTau1_so * z) :
    (g * ψ v * g⁻¹) * z = z * (g * ψ v * g⁻¹) := by
  obtain ⟨z', hz'⟩ : ∃ z' : PGSp45, z' = g⁻¹ * z * g := ⟨_, rfl⟩
  have hz'ker : z' ∈ chiPG.ker := by
    rw [MonoidHom.mem_ker, hz']
    have := chiPG_conj g⁻¹ z
    rwa [inv_inv, hz] at this
  have hzt : z' * ψ t = ψ t * z' := by
    rw [← hg] at hzτ
    calc z' * ψ t = g⁻¹ * (z * (g * ψ t * g⁻¹)) * g := by rw [hz']; group
      _ = g⁻¹ * ((g * ψ t * g⁻¹) * z) * g := by rw [hzτ]
      _ = ψ t * z' := by rw [hz']; group
  obtain ⟨w, hwC, hw⟩ := hψ.exists_cent_of_mem_range (hker hz'ker) hzt
  have hvz : ψ v * z' = z' * ψ v := by
    rw [← hw, ← map_mul, ← map_mul, hv w hwC]
  calc (g * ψ v * g⁻¹) * z = g * (ψ v * z') * g⁻¹ := by rw [hz']; group
    _ = g * (z' * ψ v) * g⁻¹ := by rw [hvz]
    _ = z * (g * ψ v * g⁻¹) := by rw [hz']; group

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
