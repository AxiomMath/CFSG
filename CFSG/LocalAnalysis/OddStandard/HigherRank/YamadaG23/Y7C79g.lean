module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79a
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.Quasithin.Vol2.Ch12Sec7IdentSL32

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open Matrix CFSG.Quasithin.H13.I1277

private lemma conjSub_sup {Γ : Type} [Group Γ] (c : Γ) (H K : Subgroup Γ) :
    conjSub c (H ⊔ K) = conjSub c H ⊔ conjSub c K := by
  unfold conjSub
  exact Subgroup.map_sup H K _

private lemma conjSub_top {Γ : Type} [Group Γ] (c : Γ) :
    conjSub c (⊤ : Subgroup Γ) = ⊤ := by
  unfold conjSub
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

private lemma conjSub_mul {Γ : Type} [Group Γ] (a b : Γ) (H : Subgroup Γ) :
    conjSub a (conjSub b H) = conjSub (a * b) H := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext h
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
    MulAut.conj_apply]
  group

private lemma map_conjSub {Γ Δ : Type} [Group Γ] [Group Δ] (ψ : Γ →* Δ) (c : Γ)
    (F : Subgroup Γ) : (conjSub c F).map ψ = conjSub (ψ c) (F.map ψ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext f
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
    MulAut.conj_apply, map_mul, map_inv]

private lemma eq_top_of_map_eq_top {Γ Δ : Type} [Group Γ] [Group Δ] {ψ : Γ →* Δ}
    {T : Subgroup Γ} (hker : ψ.ker ≤ T) (h : T.map ψ = ⊤) : T = ⊤ := by
  have h1 : (T.map ψ).comap ψ = T := Subgroup.comap_map_eq_self hker
  rw [h] at h1
  simpa using h1.symm

private def wGL : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩

private theorem dih_gen : ∃ x : GL (Fin 3) (ZMod 2), dih ⊔ conjSub x dih = ⊤ := by
  have hu : dihElt (0, 2) ∈ dih := ⟨(0, 2), rfl⟩
  have hd : dihElt (0, 3) ∈ dih := ⟨(0, 3), rfl⟩
  refine ⟨wGL, ?_⟩
  have hl : MulAut.conj wGL (dihElt (0, 3)) ∈ conjSub wGL dih := by
    unfold conjSub
    exact Subgroup.mem_map_of_mem _ hd
  let H : Subgroup (GL (Fin 3) (ZMod 2)) := dih ⊔ conjSub wGL dih
  have hdihH : dih ≤ H := le_sup_left
  have hconjH : conjSub wGL dih ≤ H := le_sup_right
  have hmem : dihElt (0, 2) * MulAut.conj wGL (dihElt (0, 3)) ∈ H :=
    mul_mem (hdihH hu) (hconjH hl)
  have h2 : 2 ∣ Nat.card H := by
    have h8 := Subgroup.card_dvd_of_le hdihH
    rw [card_dih] at h8
    exact dvd_trans (by norm_num) h8
  have h7 : 7 ∣ Nat.card H := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hord : orderOf (dihElt (0, 2) * MulAut.conj wGL (dihElt (0, 3))) = 7 := by
      apply orderOf_eq_prime
      · decide +kernel
      · decide +kernel
    have hdvd := Subgroup.orderOf_dvd_natCard H hmem
    rwa [hord] at hdvd
  exact CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2 h7

theorem y7c_gl3Two_gen_sylow (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
    (hS : Nat.card S = 8) : ∃ x, S ⊔ conjSub x S = ⊤ := by
  obtain ⟨x0, hx0⟩ := dih_gen
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 3) (by rw [hS]; norm_num)
  have hSidx : ¬ 2 ∣ S.index := by
    have h := S.card_mul_index
    rw [hS, CFSG.ComponentClassification.GHarris.card_GL32_gh] at h
    have : S.index = 21 := by omega
    rw [this]; norm_num
  let PD : Sylow 2 (GL (Fin 3) (ZMod 2)) := dih_isPGroup.toSylow dih_index_not_dvd
  let PS : Sylow 2 (GL (Fin 3) (ZMod 2)) := hSp.toSylow hSidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) PD PS
  have hS_eq : S = conjSub g dih := by
    have hcoe : (PS : Subgroup (GL (Fin 3) (ZMod 2))) = S := IsPGroup.toSylow_coe hSp hSidx
    rw [← hcoe, ← hg, Sylow.coe_subgroup_smul]
    rfl
  have hconj : conjSub (g * x0 * g⁻¹) S = conjSub g (conjSub x0 dih) := by
    rw [hS_eq, conjSub_mul, conjSub_mul]
    congr 1
    group
  refine ⟨g * x0 * g⁻¹, ?_⟩
  rw [hconj, hS_eq]
  calc conjSub g dih ⊔ conjSub g (conjSub x0 dih)
      = conjSub g (dih ⊔ conjSub x0 dih) := (conjSub_sup g dih _).symm
    _ = conjSub g ⊤ := by rw [hx0]
    _ = ⊤ := conjSub_top g

variable {G : Type} [Group G] [Finite G] {E N : Subgroup G}

theorem y7c_gl3_gen_sylow (hE : IsGL3Ext E N) {D : Subgroup G} (hND : N ≤ D) (hDE : D ≤ E)
    (hD : Nat.card D = 8 * Nat.card N) : ∃ x ∈ E, D ⊔ conjSub x D = E := by
  unfold IsGL3Ext SecProp at hE
  obtain ⟨hNE, hNnorm, ⟨e⟩⟩ := hE
  haveI : (N.subgroupOf E).Normal := hNnorm
  let Q := ↥E ⧸ N.subgroupOf E
  let π : E →* Q := QuotientGroup.mk' (N.subgroupOf E)
  let ψ : E →* GL (Fin 3) (ZMod 2) := e.toMonoidHom.comp π
  let A : Subgroup E := D.subgroupOf E
  let φ : ↥A →* GL (Fin 3) (ZMod 2) := ψ.comp A.subtype
  have hψker : ψ.ker = N.subgroupOf E := by
    have h1 : ψ.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
    rw [h1, QuotientGroup.ker_mk']
  have hA : A.map E.subtype = D :=
    Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hrange : φ.range = A.map ψ := by
    change (ψ.comp A.subtype).range = A.map ψ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkercard : Nat.card φ.ker = Nat.card N := by
    have hker : φ.ker = (N.subgroupOf E).subgroupOf A := by
      rw [show φ.ker = ψ.ker.comap A.subtype from
        (MonoidHom.comap_ker ψ A.subtype).symm, hψker]
      rfl
    calc Nat.card φ.ker = Nat.card ((N.subgroupOf E).subgroupOf A) := by rw [hker]
      _ = Nat.card (N.subgroupOf E) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.subgroupOf_mono E hND)).toEquiv
      _ = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE).toEquiv
  have hquot : Nat.card (↥A ⧸ φ.ker) = Nat.card (A.map ψ) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange]
  have hA_D : Nat.card ↥A = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv
  have hAD : Nat.card ↥A = 8 * Nat.card N := hA_D.trans hD
  have hS : Nat.card (A.map ψ) = 8 := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hmain : Nat.card (A.map ψ) * Nat.card N = 8 * Nat.card N := by
      calc Nat.card (A.map ψ) * Nat.card N
          = Nat.card (↥A ⧸ φ.ker) * Nat.card φ.ker := by rw [← hquot, ← hkercard]
        _ = Nat.card ↥A := hcard.symm
        _ = 8 * Nat.card N := hAD
    have hNpos : 0 < Nat.card N := by
      haveI : Nonempty ↥N := ⟨1⟩
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hNpos hmain
  obtain ⟨y0, hy0⟩ := y7c_gl3Two_gen_sylow (A.map ψ) hS
  obtain ⟨xE, hxE⟩ := QuotientGroup.mk'_surjective (N.subgroupOf E) (e.symm y0)
  have hψx : ψ xE = y0 := by
    change e (π xE) = y0
    rw [hxE, e.apply_symm_apply]
  have hker_le : ψ.ker ≤ A ⊔ conjSub xE A := by
    rw [hψker]
    exact (Subgroup.subgroupOf_mono E hND).trans le_sup_left
  have hTE : (A ⊔ conjSub xE A).map ψ = ⊤ := by
    rw [Subgroup.map_sup, map_conjSub, hψx]
    exact hy0
  have hTEtop : A ⊔ conjSub xE A = ⊤ := eq_top_of_map_eq_top hker_le hTE
  have hmap : (A ⊔ conjSub xE A).map E.subtype = D ⊔ conjSub (xE : G) D := by
    rw [Subgroup.map_sup, map_conjSub, hA]
    rfl
  have hGE : D ⊔ conjSub (xE : G) D = E := by
    have h := congrArg (Subgroup.map E.subtype) hTEtop
    rw [hmap] at h
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  exact ⟨(xE : G), xE.2, hGE⟩

end CFSG.OddStandard.HigherRank.YamadaG23
