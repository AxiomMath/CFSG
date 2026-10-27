module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma conj_inv_conj_mul_inv {Γ : Type} [Group Γ] {a l : Γ} (ha : a ^ 2 = 1) :
    a * ((a * l * a⁻¹) * l⁻¹) * a⁻¹ = ((a * l * a⁻¹) * l⁻¹)⁻¹ := by
  set c : MulAut Γ := MulAut.conj a with hc
  have hc2 : c ^ 2 = 1 := by
    have h : (MulAut.conj : Γ →* MulAut Γ) (a ^ 2) = 1 := by rw [ha, map_one]
    simpa [hc, pow_two, map_mul] using h
  have hcc : c (c l) = l := by
    have h : (c ^ 2) l = l := by rw [hc2]; rfl
    simpa [pow_two, MulAut.mul_apply] using h
  have key : c ((c l) * l⁻¹) = ((c l) * l⁻¹)⁻¹ := by
    rw [map_mul, map_inv, hcc]
    group
  simpa [hc, MulAut.conj_apply] using key

private abbrev Y31PSL : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)

private theorem y31_psl_card : Nat.card Y31PSL = 504 := by
  change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) = 504
  rw [CFSG.Walter.psl2_even_card (f := 3) (by norm_num)]
  norm_num

private theorem y31_psl_mulAut_not_solvable : ¬ Group.IsSolvable (MulAut Y31PSL) := by
  haveI : IsSimpleGroup Y31PSL := by
    change IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))
    refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  refine CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple.not_isSolvable ?_
  by_contra h
  push Not at h
  haveI : IsMulCommutative Y31PSL := IsMulCommutative.of_comm h
  have hprime : (Nat.card Y31PSL).Prime :=
    (Group.is_simple_iff_prime_card (α := Y31PSL)).mp inferInstance
  rw [y31_psl_card] at hprime
  have h504 : ¬ (504 : ℕ).Prime := by
    intro hp
    rcases hp.eq_one_or_self_of_dvd 8 (by norm_num) with h | h <;> omega
  exact h504 hprime

theorem s3_centEl_not_solvable (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    {t'' : G} (ht : ActsAs L t'' s.fr'.σ) (ht2 : t'' ^ 2 = 1) :
    ¬ Group.IsSolvable ↥(centEl L t'') := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have htN : t'' ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L ht
  have hX : centEl L t'' ≤ normalizer (L : Set G) :=
    inf_le_left.trans Subgroup.le_normalizer
  let φ : ↥(centEl L t'') →* MulAut (L ⧸ center L) := jOn L hX
  have hφacts : ∀ x : ↥(centEl L t''), ActsAs L (x : G) (φ x) := fun x =>
    jOn_actsAs L hX x
  have hV_le : centEl L t'' ≤ L ⊔ centralizer (L : Set G) := inf_le_left.trans le_sup_left
  have hφinn : ∀ x : ↥(centEl L t''), φ x ∈ innerAut (L ⧸ center L) := fun x =>
    jSub_le_inner L hV_le ((mem_jSub L).mpr ⟨(x : G), x.2, hφacts x⟩)
  have hφcomm : ∀ x : ↥(centEl L t''), φ x * s.fr'.σ = s.fr'.σ * φ x := by
    intro x
    have hxt : (x : G) * t'' = t'' * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
    have h1 : ActsAs L ((x : G) * t'') (φ x * s.fr'.σ) := actsAs_mul L (hφacts x) ht
    have h2 : ActsAs L (t'' * (x : G)) (s.fr'.σ * φ x) := actsAs_mul L ht (hφacts x)
    rw [← hxt] at h2
    exact actsAs_unique L h1 h2
  let φ' : ↥(centEl L t'') →* ↥(centEl (innerAut (L ⧸ center L)) s.fr'.σ) :=
    { toFun := fun x => ⟨φ x, Subgroup.mem_inf.mpr
        ⟨hφinn x, Subgroup.mem_centralizer_singleton_iff.mpr (hφcomm x)⟩⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y) }
  have hφ'surj : Function.Surjective φ' := by
    rintro ⟨i, hi⟩
    set iA : MulAut (L ⧸ center L) := (i : MulAut (L ⧸ center L)) with hiA
    have hiI : iA ∈ innerAut (L ⧸ center L) := by
      rw [hiA]; exact (Subgroup.mem_inf.mp hi).1
    have hicomm : iA * s.fr'.σ = s.fr'.σ * iA := by
      rw [hiA]
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hi).2
    have hiI' : iA ∈ jSub L L := by rw [jSub_self L]; exact hiI
    obtain ⟨l, hlL, hlacts⟩ := (mem_jSub L).mp hiI'
    set ζ : G := (t'' * l * t''⁻¹) * l⁻¹ with hζdef
    have hζacts : ActsAs L ζ 1 := by
      have h1 : ActsAs L (t'' * l * t''⁻¹) (s.fr'.σ * iA * s.fr'.σ⁻¹) :=
        actsAs_mul L (actsAs_mul L ht hlacts) (actsAs_inv L ht)
      have h2 : s.fr'.σ * iA * s.fr'.σ⁻¹ = iA := by rw [← hicomm]; group
      rw [h2] at h1
      have h3 : ActsAs L l⁻¹ iA⁻¹ := actsAs_inv L hlacts
      have h4 : ActsAs L ((t'' * l * t''⁻¹) * l⁻¹) (iA * iA⁻¹) := actsAs_mul L h1 h3
      simpa [hζdef] using h4
    have hζC : ζ ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hζacts
    have hζL : ζ ∈ L := by
      rw [hζdef]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp htN l).mp hlL) (L.inv_mem hlL)
    have hζcenter : (⟨ζ, hζL⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hζC (g : G) g.2)
    have hm : orderOf ζ ∣ Nat.card ↥(center ↥L) := by
      have h := (center ↥L).orderOf_dvd_natCard hζcenter
      rwa [Subgroup.orderOf_mk ζ hζL] at h
    have hoddζ : Odd (orderOf ζ) := Odd.of_dvd_nat hZ hm
    set m : ℕ := orderOf ζ with hmdef
    set k : ℕ := (m + 1) / 2 with hkdef
    set ξ : G := ζ ^ k with hξdef
    have hξL : ξ ∈ L := by rw [hξdef]; exact L.pow_mem hζL k
    have hξC : ξ ∈ centralizer (L : Set G) := by
      rw [hξdef]; exact (centralizer (L : Set G)).pow_mem hζC k
    have hξ2 : ξ ^ 2 = ζ := by
      rw [hξdef, ← pow_mul]
      have hk2 : k * 2 = m + 1 := by
        obtain ⟨j, hj⟩ := hoddζ
        have hj' : m = 2 * j + 1 := by rw [hmdef]; exact hj
        rw [hkdef, hj']
        omega
      rw [hk2, pow_succ, hmdef, pow_orderOf_eq_one, one_mul]
    have hξinv : t'' * ξ * t''⁻¹ = ξ⁻¹ := by
      have hconj : t'' * ζ * t''⁻¹ = ζ⁻¹ := by
        simpa [hζdef] using conj_inv_conj_mul_inv (a := t'') (l := l) ht2
      have hcp := conj_pow (a := t'') (b := ζ) (i := k)
      rw [hconj, inv_pow] at hcp
      rw [hξdef]
      exact hcp.symm
    set y : G := l * ξ with hydef
    have hyL : y ∈ L := by rw [hydef]; exact L.mul_mem hlL hξL
    have htl : t'' * l * t''⁻¹ = ζ * l := by rw [hζdef]; group
    have hycomm : t'' * y * t''⁻¹ = y := by
      rw [hydef]
      calc t'' * (l * ξ) * t''⁻¹
          = (t'' * l * t''⁻¹) * (t'' * ξ * t''⁻¹) := by group
        _ = (ζ * l) * ξ⁻¹ := by rw [htl, hξinv]
        _ = l * (ζ * ξ⁻¹) := by
              rw [← Subgroup.mem_centralizer_iff.mp hζC l hlL]; group
        _ = l * ξ := by rw [← hξ2]; group
    have hyt : y * t'' = t'' * y := by
      conv_lhs => rw [← hycomm]
      group
    have hyX : y ∈ centEl L t'' :=
      Subgroup.mem_inf.mpr ⟨hyL, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩
    have hyacts : ActsAs L y iA := by
      have h := actsAs_mul L hlacts (actsAs_of_mem_centralizer L hξC)
      simpa [hydef] using h
    have hφy : φ ⟨y, hyX⟩ = iA := actsAs_unique L (jOn_actsAs L hX ⟨y, hyX⟩) hyacts
    exact ⟨⟨y, hyX⟩, Subtype.ext hφy⟩
  intro hsolv
  haveI := hsolv
  have hC : Group.IsSolvable ↥(centEl (innerAut (L ⧸ center L)) s.fr'.σ) :=
    Group.isSolvable_of_surjective (f := φ') hφ'surj
  haveI := hC
  obtain ⟨e⟩ := s.facts.2.2.2.2.2.2.1.1
  have hA : Group.IsSolvable (MulAut Y31PSL) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact y31_psl_mulAut_not_solvable hA

end CFSG.OddStandard.HigherRank.YamadaG23
