module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem EndB.isFieldAutPSL2_of_card {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfe : Even f) (h16 : 16 ∣ p ^ f - 1) (hY : Blueprint.LieModel Y .PSL 2 p f)
    {φ : MulAut Y} (hφ2 : φ * φ = 1) (hφ : φ ∉ innAut Y)
    (hcard : p ^ f + 1 < Nat.card ↥(fixedPoints φ)) : IsFieldAutPSL2 φ := by
  obtain ⟨-, hf1, -, hq3, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hY4 : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
    obtain ⟨y, hy4, hy2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
    refine ⟨e.symm y, by rw [← map_pow, hy4, map_one], fun h => hy2 ?_⟩
    rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  rw [isFieldAutPSL2_iff hH.odd e hY4]
  set x := autEquiv e φ with hxd
  have hx2 : x * x = 1 := by rw [hxd, ← map_mul, hφ2, map_one]
  have hφ1 : φ ≠ 1 := fun h => hφ (h ▸ one_mem _)
  have hx1 : x ≠ 1 := fun h => hφ1 ((autEquiv e).injective (h.trans (map_one _).symm))
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  by_cases hr : x.right = 1
  ·
    exfalso
    set g := x.left with hgd
    have hxg : x = SemidirectProduct.inl g := by
      rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one]
    have hgg : g * g = 1 := by
      have h1 := hx2
      rw [hxg, ← map_mul] at h1
      exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
    have hg1 : g ≠ 1 := fun h => hx1 (by rw [hxg, h, map_one])
    have hgr : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rintro ⟨y, hy⟩
      apply hφ
      have hxI : x ∈ pGammaL2PSLRange F := ⟨y, by rw [hxg, ← hy]; rfl⟩
      rw [← map_autEquiv_innAut e] at hxI
      obtain ⟨ψ, hψ, hψx⟩ := hxI
      have : ψ = φ := (autEquiv e).injective hψx
      exact this ▸ hψ
    have h4 : Nat.card F % 4 = 1 := hH.q4
    have h3 : 3 < Nat.card F := by
      have h1 : 3 ≤ p ^ f := le_trans (hp.two_le.lt_of_ne (Ne.symm hp2))
        (Nat.le_self_pow (by omega) p)
      rw [hF]
      omega
    obtain ⟨eD⟩ := psl2_fix_outer_involution hH.odd h4 h3 hgg hg1 hgr
    have hfix : ∀ y : Y, y ∈ fixedPoints φ ↔
        e y ∈ MonoidHom.eqLocus (pglAction F g).toMonoidHom (MonoidHom.id (PSL2 F)) := by
      intro y
      have h1 : (pglAction F g) (e y) = e (φ y) := by
        rw [← semilinearAction_inl, ← hxg, hxd, semilinearAction_autEquiv_apply]
      change φ y = y ↔ (pglAction F g) (e y) = e y
      rw [h1]
      exact ⟨fun h => by rw [h], fun h => e.injective h⟩
    have hcardeq : Nat.card ↥(fixedPoints φ) = Nat.card F + 1 := by
      have h1 : Nat.card ↥(fixedPoints φ) = Nat.card ↥(MonoidHom.eqLocus
          (pglAction F g).toMonoidHom (MonoidHom.id (PSL2 F))) := by
        refine Nat.card_congr ⟨fun y => ⟨e y, (hfix y).mp y.2⟩,
          fun y => ⟨e.symm y, (hfix _).mpr (by rw [e.apply_symm_apply]; exact y.2)⟩,
          fun y => Subtype.ext (e.symm_apply_apply y), fun y => Subtype.ext
            (e.apply_symm_apply y)⟩
      rw [h1, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
      have hodd : Odd (Nat.card F) := by
        obtain ⟨p', n', hp', hpo, -, hq⟩ := hH.odd
        rw [hq]
        exact hpo.pow
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      omega
    rw [hcardeq, hF] at hcard
    omega
  ·
    obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hH.odd x hxo hr
    have hσ2 : x.right * x.right = 1 := by
      have := congrArg SemidirectProduct.right hx2
      rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
    refine ⟨SemidirectProduct.inl C, x.right, orderOf_eq_prime (by rw [sq, hσ2]) hr, ?_⟩
    calc x = SemidirectProduct.inl C *
          ((SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C) *
          (SemidirectProduct.inl C)⁻¹ := by group
      _ = _ := by rw [hC]

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

open HarrisEnd Standing.Setup42 in
theorem Setting46e.isFieldAutPSL2_conjOn (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 2 p
      (2 * (f / 2)))
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    IsFieldAutPSL2 (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (hs.setup.tBar i j)) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set E := layer (MBar β) with hE
  have hp := hs.prime_p
  have hp2 := hs.p_ne_two
  refine EndB.isFieldAutPSL2_of_card hp hp2 ⟨f / 2, by ring⟩ hs.sixteen_dvd hY ?_ hout ?_
  · rw [← map_mul, ← sq, hs.tBar_sq, map_one]
  ·
    have hKle : KBar L β ≤ E ⊓ centralizer {hs.setup.tBar i j} := by
      rw [← h412.layerIn_layer_centralizer]
      exact map_subtype_le _
    have hcE : Nat.card ↥(fixedPoints (conjOn E (hs.setup.tBar i j))) =
        Nat.card ↥(E ⊓ centralizer {hs.setup.tBar i j}) := by
      rw [← map_fixedPoints_conjOn, Subgroup.card_map_of_injective (subtype_injective _)]
    obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel (hs.lieModel_KBar h412)
    have hK : Nat.card ↥(KBar L β) = p ^ (f / 2) * (((p ^ (f / 2)) ^ 2 - 1) / 2) := by
      rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF]
    have hle := Subgroup.card_le_of_le hKle
    rw [hcE]
    refine lt_of_lt_of_le ?_ (hK ▸ hle)
    set r := p ^ (f / 2) with hr
    have hq : p ^ (2 * (f / 2)) = r ^ 2 := by rw [hr, ← pow_mul, mul_comm]
    have h16 := hs.sixteen_dvd
    rw [hq] at h16 ⊢
    have hr3 : 3 ≤ r := le_trans (hp.two_le.lt_of_ne (Ne.symm hp2))
      (Nat.le_self_pow (by have := hs.one_le_half; omega) p)
    have hodd : Odd r := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := hodd
    have h2m : 2 * ((r ^ 2 - 1) / 2) = r ^ 2 - 1 := by
      rw [hk]
      have : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * k + 2 * k) := by ring_nf; omega
      rw [this]
      omega
    have hr17 : 17 ≤ r ^ 2 := by
      obtain ⟨c, hc⟩ := h16
      have h9 : 9 ≤ r ^ 2 := by nlinarith
      omega
    have hr5 : 5 ≤ r := by nlinarith
    set m := (r ^ 2 - 1) / 2 with hm
    have hr2 : r ^ 2 = 2 * m + 1 := by omega
    nlinarith

end CFSG.ComponentClassification.HarrisLit
