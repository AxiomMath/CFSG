module

public import CFSG.GroupTheory.InvolutionCentralizerOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.SwapData

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

variable {X : Type*} [Group X]

private lemma dihedralCentralizer_le_centralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    dihedralCentralizer e ≤ centralizer ({u} : Set X) :=
  Subgroup.map_subtype_le _

private lemma conj_mem_dihedralCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {c d : X} (hc : c ∈ centralizer ({u} : Set X)) (hd : d ∈ dihedralCentralizer e) :
    c * d * c⁻¹ ∈ dihedralCentralizer e := by
  obtain ⟨dc, hdc, rfl⟩ := Subgroup.mem_map.mp hd
  refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * dc * ⟨c, hc⟩⁻¹, ?_, ?_⟩
  · exact (inferInstance : (dihedralSubgroup.comap e.toMonoidHom).Normal).conj_mem dc hdc ⟨c, hc⟩
  · simp

private lemma conj_mem_altCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {c k : X} (hc : c ∈ centralizer ({u} : Set X)) (hk : k ∈ altCentralizer e) :
    c * k * c⁻¹ ∈ altCentralizer e := by
  obtain ⟨kc, hkc, rfl⟩ := Subgroup.mem_map.mp hk
  refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * kc * ⟨c, hc⟩⁻¹, ?_, ?_⟩
  · exact (inferInstance : (altSubgroup.comap e.toMonoidHom).Normal).conj_mem kc hkc ⟨c, hc⟩
  · simp

private lemma card_comap_altSubgroup {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    Nat.card ↥(altSubgroup.comap e.toMonoidHom) = 60 := by
  obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
  rw [Nat.card_congr ee.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

private lemma card_dihedralCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    Nat.card ↥(dihedralCentralizer e) = 8 := by
  have hcongr : Nat.card ↥(dihedralCentralizer e) =
      Nat.card ↥(dihedralSubgroup.comap e.toMonoidHom) :=
    Nat.card_congr (Subgroup.equivMapOfInjective
      (dihedralSubgroup.comap e.toMonoidHom) (centralizer ({u} : Set X)).subtype
      (Subgroup.subtype_injective _)).toEquiv.symm
  rw [hcongr, card_comap_dihedralSubgroup e]

private lemma card_map_conj_dihedralCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) (τ : X) :
    Nat.card ↥((dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom) = 8 := by
  have hcongr : Nat.card ↥((dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom) =
      Nat.card ↥(dihedralCentralizer e) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (dihedralCentralizer e)
      (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).toEquiv.symm
  rw [hcongr, card_dihedralCentralizer e]

private lemma isSimpleGroup_altCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    IsSimpleGroup ↥(altCentralizer e) := by
  have h1 : IsSimpleGroup ↥(altSubgroup.comap e.toMonoidHom) := by
    obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
    exact (MulEquiv.isSimpleGroup_congr ee).mpr alternatingGroup.isSimpleGroup_five
  exact (MulEquiv.isSimpleGroup_congr (Subgroup.equivMapOfInjective
    (altSubgroup.comap e.toMonoidHom) (centralizer ({u} : Set X)).subtype
    (Subgroup.subtype_injective _))).mp h1

private lemma map_conj_normal_in_swap {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {B S : Subgroup X} {τ : X} (hsd : SwapData e B S τ)
    {x : X} (hx : x ∈ B)
    {d : X} (hd : d ∈ (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom) :
    x * d * x⁻¹ ∈ (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom := by
  obtain ⟨c, hcD, rfl⟩ := Subgroup.mem_map.mp hd
  have hy : τ⁻¹ * x * τ ∈ B := by
    have h := hsd.normal τ⁻¹ (S.inv_mem hsd.mem_S) x hx
    simpa using h
  have hyC : τ⁻¹ * x * τ ∈ centralizer ({u} : Set X) := hsd.le_centralizer hy
  have hconj : (τ⁻¹ * x * τ) * c * (τ⁻¹ * x * τ)⁻¹ ∈ dihedralCentralizer e :=
    conj_mem_dihedralCentralizer e hyC hcD
  refine Subgroup.mem_map.mpr ⟨(τ⁻¹ * x * τ) * c * (τ⁻¹ * x * τ)⁻¹, hconj, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private lemma card_center_dihedralGroup_four :
    Nat.card ↥(Subgroup.center (DihedralGroup 4)) = 2 := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two (n := 4) (by decide) (by decide)]
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime <;> decide +kernel

private noncomputable def dihedralSubgroupIso :
    ↥(dihedralSubgroup : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5))) ≃* DihedralGroup 4 where
  toFun x := x.1.1
  invFun d := ⟨(d, 1), by
    rw [dihedralSubgroup, Subgroup.mem_prod]
    exact ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩⟩
  left_inv x := by
    have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp x.2).2
    exact Subtype.ext (Prod.ext rfl hx2.symm)
  right_inv d := rfl
  map_mul' x y := rfl

private lemma card_center_congr {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    Nat.card ↥(Subgroup.center G) = Nat.card ↥(Subgroup.center H) :=
  Nat.card_congr ((f.subgroupMap (Subgroup.center G)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_center_eq f))).toEquiv

private lemma card_center_dihedralCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    Nat.card ↥(Subgroup.center ↥(dihedralCentralizer e)) = 2 := by
  let C := ↥(centralizer ({u} : Set X))
  let DC : Subgroup C := dihedralSubgroup.comap e.toMonoidHom
  have hmap : DC.map (e : C →* _) = dihedralSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective dihedralSubgroup
  let f1 : ↥DC ≃* ↥dihedralSubgroup :=
    (e.subgroupMap DC).trans (MulEquiv.subgroupCongr hmap)
  let f2 : ↥(dihedralCentralizer e) ≃* ↥DC :=
    (Subgroup.equivMapOfInjective DC (centralizer ({u} : Set X)).subtype
      (Subgroup.subtype_injective _)).symm
  have h1 : Nat.card ↥(Subgroup.center ↥(dihedralCentralizer e)) =
      Nat.card ↥(Subgroup.center ↥dihedralSubgroup) := card_center_congr (f2.trans f1)
  have h2 : Nat.card ↥(Subgroup.center ↥dihedralSubgroup) =
      Nat.card ↥(Subgroup.center (DihedralGroup 4)) := card_center_congr dihedralSubgroupIso
  rw [h1, h2, card_center_dihedralGroup_four]

private lemma card_inf_altCentralizer_sylow [Finite X] {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {B S : Subgroup X} {τ : X} (hsd : SwapData e B S τ) :
    Nat.card ↥(altCentralizer e ⊓ B) = 4 := by
  let Csub : Subgroup X := centralizer ({u} : Set X)
  let C := ↥Csub
  let KC : Subgroup C := altSubgroup.comap e.toMonoidHom
  let BC : Subgroup C := B.subgroupOf Csub
  haveI : Finite C := (inferInstance : Finite ↥Csub)
  have hCcard : Nat.card C = 960 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm,
      Nat.card_fin]
    norm_num [Nat.factorial]
  have hKCcard : Nat.card ↥KC = 60 := card_comap_altSubgroup e
  have hBCcard : Nat.card ↥BC = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.le_centralizer).toEquiv]
    exact hsd.card_B
  have hKCnormal : KC.Normal := by
    dsimp only [KC]
    infer_instance
  have hprod : Nat.card ↥(KC ⊔ BC) * Nat.card ↥(KC ⊓ BC) = Nat.card ↥KC * Nat.card ↥BC := by
    haveI := hKCnormal
    have h1 := Subgroup.relIndex_mul_card (H := KC) (K := KC ⊔ BC)
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := KC) (K := BC)
    rw [← h1, ← h2]
    ring
  have hle : Nat.card ↥(KC ⊔ BC) ≤ 960 := by
    have := Subgroup.card_le_of_le (le_top : (KC ⊔ BC : Subgroup C) ≤ ⊤)
    rwa [Subgroup.card_top, hCcard] at this
  have hge : 4 ≤ Nat.card ↥(KC ⊓ BC) := by
    have h3840 : 960 * 4 ≤ 960 * Nat.card ↥(KC ⊓ BC) := by
      calc 960 * 4 = 60 * 2 ^ 6 := by norm_num
        _ = Nat.card ↥KC * Nat.card ↥BC := by rw [hKCcard, hBCcard]
        _ = Nat.card ↥(KC ⊔ BC) * Nat.card ↥(KC ⊓ BC) := hprod.symm
        _ ≤ 960 * Nat.card ↥(KC ⊓ BC) := Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left h3840 (by norm_num)
  have hdvd : Nat.card ↥(KC ⊓ BC) ∣ 4 := by
    have h1 : Nat.card ↥(KC ⊓ BC) ∣ Nat.card ↥KC := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(KC ⊓ BC) ∣ Nat.card ↥BC := Subgroup.card_dvd_of_le inf_le_right
    rw [hKCcard] at h1
    rw [hBCcard] at h2
    have := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd 60 (2 ^ 6) = 4 by norm_num] at this
  have hKCBC : Nat.card ↥(KC ⊓ BC) = 4 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hge
  have hmap : (KC ⊓ BC).map (centralizer ({u} : Set X)).subtype = altCentralizer e ⊓ B := by
    dsimp only [KC, BC]
    rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (centralizer ({u} : Set X))),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hsd.le_centralizer]
  rw [← hmap]
  rw [Nat.card_congr (Subgroup.equivMapOfInjective (KC ⊓ BC)
    (centralizer ({u} : Set X)).subtype (Subgroup.subtype_injective _)).toEquiv.symm]
  exact hKCBC

theorem mem_of_altCentralizer_le [Finite X] {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) {T : Subgroup X} (hT : T.Normal)
    (hK : altCentralizer e ≤ T) : u ∈ T := by
  by_contra huT
  obtain ⟨B, S, τ, hsd⟩ := exists_swapData hu1 e P hP
  have hDleC : dihedralCentralizer e ≤ centralizer ({u} : Set X) :=
    dihedralCentralizer_le_centralizer e
  set Dt : Subgroup X := (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom with hDtdef
  have hDT : dihedralCentralizer e ⊓ T = ⊥ := by
    by_contra hne
    let N : Subgroup ↥(centralizer ({u} : Set X)) :=
      (dihedralSubgroup.comap e.toMonoidHom) ⊓ T.subgroupOf (centralizer ({u} : Set X))
    have hNnormal : N.Normal := by
      dsimp only [N]
      exact Subgroup.normal_inf_normal _ _
    have hNne : N ≠ ⊥ := by
      intro hbot
      apply hne
      have hmap : N.map (centralizer ({u} : Set X)).subtype = dihedralCentralizer e ⊓ T := by
        dsimp only [N]
        rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (centralizer ({u} : Set X))),
          Subgroup.subgroupOf_map_subtype]
        rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hDleC)]
      rw [← hmap, hbot, Subgroup.map_bot]
    rcases mem_or_comap_altSubgroup_le_of_normal e N hNnormal hNne with hmem | hle
    · apply huT
      have hmemT : e.symm (DihedralGroup.r 2, 1) ∈
          T.subgroupOf (centralizer ({u} : Set X)) := hmem.2
      have hu_eq : (⟨u, mem_centralizer_singleton_iff.2 rfl⟩ :
          ↥(centralizer ({u} : Set X))) = e.symm (DihedralGroup.r 2, 1) :=
        mk_eq_symm_r_two hu1 e
      rw [← hu_eq] at hmemT
      exact hmemT
    · have hNle : N ≤ dihedralSubgroup.comap e.toMonoidHom := inf_le_left
      have hKle : (altSubgroup.comap e.toMonoidHom) ≤
          dihedralSubgroup.comap e.toMonoidHom := hle.trans hNle
      have hcard := Subgroup.card_le_of_le hKle
      rw [card_comap_altSubgroup e, card_comap_dihedralSubgroup e] at hcard
      norm_num at hcard
  have hDtT : Dt ⊓ T = ⊥ := by
    have hmap : (dihedralCentralizer e ⊓ T).map (MulAut.conj τ).toMonoidHom = Dt ⊓ T := by
      have hTmap : T.map (MulAut.conj τ).toMonoidHom = T :=
        Subgroup.normal_iff_map_conj_eq.mp hT τ
      rw [Subgroup.map_inf _ _ _ (MulAut.conj τ).injective, hTmap]
    rw [← hmap, hDT, Subgroup.map_bot]
  have hZcD : T ⊓ B ≤ Subgroup.centralizer (dihedralCentralizer e : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hzC : z ∈ centralizer ({u} : Set X) := hsd.le_centralizer hz.2
    have hconjD : z * d * z⁻¹ ∈ dihedralCentralizer e := conj_mem_dihedralCentralizer e hzC hd
    have hcommT : z * d * z⁻¹ * d⁻¹ ∈ T := by
      have h1 : d * z⁻¹ * d⁻¹ ∈ T := hT.conj_mem z⁻¹ (T.inv_mem hz.1) d
      have h2 : z * (d * z⁻¹ * d⁻¹) ∈ T := T.mul_mem hz.1 h1
      simpa [mul_assoc] using h2
    have hcommD : z * d * z⁻¹ * d⁻¹ ∈ dihedralCentralizer e :=
      (dihedralCentralizer e).mul_mem hconjD ((dihedralCentralizer e).inv_mem hd)
    have hone : z * d * z⁻¹ * d⁻¹ = 1 := by
      have hmem : z * d * z⁻¹ * d⁻¹ ∈ dihedralCentralizer e ⊓ T := ⟨hcommD, hcommT⟩
      rw [hDT] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : z * d * z⁻¹ = d := mul_inv_eq_one.mp hone
    calc d * z = (z * d * z⁻¹) * z := by rw [hconj]
      _ = z * d := by group
  have hZcDt : T ⊓ B ≤ Subgroup.centralizer (Dt : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hconjDt : z * d * z⁻¹ ∈ Dt := map_conj_normal_in_swap e hsd hz.2 hd
    have hcommT : z * d * z⁻¹ * d⁻¹ ∈ T := by
      have h1 : d * z⁻¹ * d⁻¹ ∈ T := hT.conj_mem z⁻¹ (T.inv_mem hz.1) d
      have h2 : z * (d * z⁻¹ * d⁻¹) ∈ T := T.mul_mem hz.1 h1
      simpa [mul_assoc] using h2
    have hcommDt : z * d * z⁻¹ * d⁻¹ ∈ Dt :=
      Dt.mul_mem hconjDt (Dt.inv_mem hd)
    have hone : z * d * z⁻¹ * d⁻¹ = 1 := by
      have hmem : z * d * z⁻¹ * d⁻¹ ∈ Dt ⊓ T := ⟨hcommDt, hcommT⟩
      rw [hDtT] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : z * d * z⁻¹ = d := mul_inv_eq_one.mp hone
    calc d * z = (z * d * z⁻¹) * z := by rw [hconj]
      _ = z * d := by group
  have hZcent : T ⊓ B ≤ Subgroup.centralizer (B : Set X) := by
    have h1 : dihedralCentralizer e ≤ Subgroup.centralizer ((T ⊓ B : Subgroup X) : Set X) :=
      (Subgroup.le_centralizer_iff).mp hZcD
    have h2 : Dt ≤ Subgroup.centralizer ((T ⊓ B : Subgroup X) : Set X) :=
      (Subgroup.le_centralizer_iff).mp hZcDt
    have hsup : dihedralCentralizer e ⊔ Dt ≤
        Subgroup.centralizer ((T ⊓ B : Subgroup X) : Set X) := sup_le h1 h2
    have h3 : B ≤ Subgroup.centralizer ((T ⊓ B : Subgroup X) : Set X) := by
      have hb := hsup
      rw [hsd.sup_eq] at hb
      exact hb
    exact (Subgroup.le_centralizer_iff).mpr h3
  have hKZ : (altCentralizer e ⊓ B).subgroupOf B ≤ Subgroup.center ↥B := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxKB := Subgroup.mem_subgroupOf.mp hx
    have hxK : (x : X) ∈ altCentralizer e := (Subgroup.mem_inf.mp hxKB).1
    have hxB : (x : X) ∈ B := (Subgroup.mem_inf.mp hxKB).2
    have hxT : (x : X) ∈ T := hK hxK
    have hxcent : (x : X) ∈ Subgroup.centralizer (B : Set X) := hZcent ⟨hxT, hxB⟩
    exact (Subgroup.mem_centralizer_iff.mp hxcent) (y : X) y.2
  have hDtleB : Dt ≤ B := hsd.sup_eq ▸ le_sup_right
  have hinfDDt : dihedralCentralizer e ⊓ Dt = ⊥ := by
    rw [hDtdef, hsd.inf_eq_bot]
  have hcommDDt : ∀ d ∈ dihedralCentralizer e, ∀ d' ∈ Dt, d * d' = d' * d := by
    intro d hd d' hd'
    have hdB : d ∈ B := hsd.dihedral_le hd
    have hd'B : d' ∈ B := hDtleB hd'
    have hcommD : d * d' * d⁻¹ * d'⁻¹ ∈ dihedralCentralizer e := by
      have h1 : d' * d⁻¹ * d'⁻¹ ∈ dihedralCentralizer e :=
        conj_mem_dihedralCentralizer e (hsd.le_centralizer hd'B)
          ((dihedralCentralizer e).inv_mem hd)
      have h2 : d * (d' * d⁻¹ * d'⁻¹) ∈ dihedralCentralizer e :=
        (dihedralCentralizer e).mul_mem hd h1
      simpa [mul_assoc] using h2
    have hcommDt : d * d' * d⁻¹ * d'⁻¹ ∈ Dt :=
      Dt.mul_mem (map_conj_normal_in_swap e hsd hdB hd') (Dt.inv_mem hd')
    have hone : d * d' * d⁻¹ * d'⁻¹ = 1 := by
      have hmem : d * d' * d⁻¹ * d'⁻¹ ∈ dihedralCentralizer e ⊓ Dt := ⟨hcommD, hcommDt⟩
      rw [hinfDDt] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : d * d' * d⁻¹ = d' := mul_inv_eq_one.mp hone
    calc d * d' = (d * d' * d⁻¹) * d := by group
      _ = d' * d := by rw [hconj]
  have hKDt : altCentralizer e ⊓ Dt = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxT : x ∈ T := hK (Subgroup.mem_inf.mp hx).1
    have hxDt : x ∈ Dt := (Subgroup.mem_inf.mp hx).2
    have hmem : x ∈ Dt ⊓ T := ⟨hxDt, hxT⟩
    rw [hDtT] at hmem
    exact Subgroup.mem_bot.mp hmem
  let ψ : ↥(dihedralCentralizer e) × ↥Dt →* X :=
    MonoidHom.noncommCoprod (dihedralCentralizer e).subtype Dt.subtype
      (fun d d' => hcommDDt d d.2 d' d'.2)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hx : (x.1 : X) * (x.2 : X) = (y.1 : X) * (y.2 : X) := hxy
    have hkey : (y.1 : X)⁻¹ * (x.1 : X) = (y.2 : X) * (x.2 : X)⁻¹ := by
      have := congrArg (fun t => (y.1 : X)⁻¹ * t * (x.2 : X)⁻¹) hx
      simpa [mul_assoc] using this
    have hmem : (y.1 : X)⁻¹ * (x.1 : X) ∈ dihedralCentralizer e ⊓ Dt := by
      refine ⟨?_, ?_⟩
      · exact (dihedralCentralizer e).mul_mem ((dihedralCentralizer e).inv_mem y.1.2) x.1.2
      · rw [hkey]; exact Dt.mul_mem y.2.2 (Dt.inv_mem x.2.2)
    rw [hinfDDt] at hmem
    have h1 : (y.1 : X)⁻¹ * (x.1 : X) = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (y.2 : X) * (x.2 : X)⁻¹ = 1 := by rw [← hkey]; exact h1
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (by
        have hx1 := congrArg (fun t => (y.1 : X) * t) h1
        simpa using hx1)
    · exact Subtype.ext (by
        have hx2 := congrArg (fun t => t * (x.2 : X)) h2
        have : (y.2 : X) = (x.2 : X) := by simpa using hx2
        exact this.symm)
  have hψle : ψ.range ≤ B := by
    rintro z ⟨w, rfl⟩
    change (w.1 : X) * (w.2 : X) ∈ B
    exact B.mul_mem (hsd.dihedral_le w.1.2) (hDtleB w.2.2)
  have hψcard : Nat.card (↥(dihedralCentralizer e) × ↥Dt) = Nat.card ↥ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  have hψrange : ψ.range = B := by
    refine Subgroup.eq_of_le_of_card_ge hψle ?_
    rw [← hψcard, Nat.card_prod, card_dihedralCentralizer e,
      card_map_conj_dihedralCentralizer e τ, hsd.card_B]
    norm_num
  let φ : ↥(dihedralCentralizer e) × ↥Dt ≃* ↥B :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)
  have hφapply : ∀ q : ↥(dihedralCentralizer e) × ↥Dt, (φ q : X) = (q.1 : X) * (q.2 : X) := by
    intro q
    rfl
  let π : ↥B →* ↥(dihedralCentralizer e) :=
    (MonoidHom.fst ↥(dihedralCentralizer e) ↥Dt).comp (φ.symm : ↥B →* _)
  have hkerπ : π.ker = Dt.subgroupOf B := by
    ext b
    constructor
    · intro hb
      rw [MonoidHom.mem_ker] at hb
      rw [Subgroup.mem_subgroupOf]
      have hq1 : (φ.symm b).1 = 1 := hb
      have hbval : (b : X) = ((φ.symm b).2 : X) := by
        conv_lhs => rw [← φ.apply_symm_apply b]
        rw [hφapply, hq1]
        simp
      rw [hbval]
      exact (φ.symm b).2.2
    · intro hb
      rw [Subgroup.mem_subgroupOf] at hb
      rw [MonoidHom.mem_ker]
      have hφb : φ (1, ⟨(b : X), hb⟩) = b := by
        apply Subtype.ext
        rw [hφapply]
        simp
      have hsymm : φ.symm b = (1, ⟨(b : X), hb⟩) := by
        apply φ.injective
        rw [φ.apply_symm_apply]
        exact hφb.symm
      show (φ.symm b).1 = 1
      rw [hsymm]
  let f : ↥((altCentralizer e ⊓ B).subgroupOf B) →* ↥(dihedralCentralizer e) :=
    π.comp ((altCentralizer e ⊓ B).subgroupOf B).subtype
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hx
    have hxker : (x : ↥B) ∈ π.ker := hx
    rw [hkerπ, Subgroup.mem_subgroupOf] at hxker
    have hxK : ((x : ↥B) : X) ∈ altCentralizer e := (Subgroup.mem_subgroupOf.mp x.2).1
    have hxKB : ((x : ↥B) : X) ∈ altCentralizer e ⊓ Dt := ⟨hxK, hxker⟩
    rw [hKDt] at hxKB
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hxKB))
  have hfrange : f.range ≤ Subgroup.center ↥(dihedralCentralizer e) := by
    rintro z ⟨y, rfl⟩
    have hycenter : (y : ↥B) ∈ Subgroup.center ↥B := hKZ y.2
    have hmapcenter : (Subgroup.center (↥(dihedralCentralizer e) × ↥Dt)).map φ.toMonoidHom =
        Subgroup.center ↥B := Subgroup.map_center_eq φ
    have hy' : φ.symm (y : ↥B) ∈ Subgroup.center (↥(dihedralCentralizer e) × ↥Dt) :=
      Subgroup.mem_map_equiv.mp (by rw [hmapcenter]; exact hycenter)
    have hy'' := Subgroup.mem_prod.mp (by
      rw [Subgroup.center_prod] at hy'
      exact hy')
    show (φ.symm (y : ↥B)).1 ∈ Subgroup.center ↥(dihedralCentralizer e)
    exact hy''.1
  have hcardK : Nat.card ↥((altCentralizer e ⊓ B).subgroupOf B) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact card_inf_altCentralizer_sylow e hsd
  have hcontr : 4 ≤ 2 := by
    calc 4 = Nat.card ↥((altCentralizer e ⊓ B).subgroupOf B) := hcardK.symm
      _ = Nat.card ↥f.range := Nat.card_congr (MonoidHom.ofInjective
          ((MonoidHom.ker_eq_bot_iff f).mp hfker)).toEquiv
      _ ≤ Nat.card ↥(Subgroup.center ↥(dihedralCentralizer e)) := Subgroup.card_le_of_le hfrange
      _ = 2 := card_center_dihedralCentralizer e
  norm_num at hcontr

theorem altCentralizer_le_of_mem [Finite X] {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) {T : Subgroup X} (hT : T.Normal)
    (huT : u ∈ T) : altCentralizer e ≤ T := by
  by_contra hKT
  obtain ⟨B, S, τ, hsd⟩ := exists_swapData hu1 e P hP
  have hKsimple : IsSimpleGroup ↥(altCentralizer e) := isSimpleGroup_altCentralizer e
  have hNnormal : ((altCentralizer e ⊓ T).subgroupOf (altCentralizer e)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨(altCentralizer e).mul_mem ((altCentralizer e).mul_mem hk hh.1)
        ((altCentralizer e).inv_mem hk), hT.conj_mem h hh.2 k⟩
  have hKTbot : altCentralizer e ⊓ T = ⊥ := by
    haveI := hKsimple
    haveI := hNnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((altCentralizer e ⊓ T).subgroupOf (altCentralizer e))
      with hbot | htop
    · have hd : Disjoint (altCentralizer e ⊓ T) (altCentralizer e) :=
        Subgroup.subgroupOf_eq_bot.mp hbot
      have hd' : (altCentralizer e ⊓ T) ⊓ (altCentralizer e) = ⊥ := disjoint_iff.mp hd
      rwa [inf_eq_left.mpr inf_le_left] at hd'
    · exfalso
      apply hKT
      have hle : altCentralizer e ≤ altCentralizer e ⊓ T := Subgroup.subgroupOf_eq_top.mp htop
      exact hle.trans inf_le_right
  have hTC_centK : T ⊓ centralizer ({u} : Set X) ≤
      Subgroup.centralizer (altCentralizer e : Set X) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hconjK : t * k * t⁻¹ ∈ altCentralizer e := conj_mem_altCentralizer e ht.2 hk
    have hcommT : t * k * t⁻¹ * k⁻¹ ∈ T := by
      have h1 : k * t⁻¹ * k⁻¹ ∈ T := hT.conj_mem t⁻¹ (T.inv_mem ht.1) k
      have h2 : t * (k * t⁻¹ * k⁻¹) ∈ T := T.mul_mem ht.1 h1
      simpa [mul_assoc] using h2
    have hcommK : t * k * t⁻¹ * k⁻¹ ∈ altCentralizer e :=
      (altCentralizer e).mul_mem hconjK ((altCentralizer e).inv_mem hk)
    have hone : t * k * t⁻¹ * k⁻¹ = 1 := by
      have hmem : t * k * t⁻¹ * k⁻¹ ∈ altCentralizer e ⊓ T := ⟨hcommK, hcommT⟩
      rw [hKTbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : t * k * t⁻¹ = k := mul_inv_eq_one.mp hone
    calc k * t = (t * k * t⁻¹) * t := by rw [hconj]
      _ = t * k := by group
  have hTC_le_D : T ⊓ centralizer ({u} : Set X) ≤ dihedralCentralizer e := by
    have hcentKD : Subgroup.centralizer (altCentralizer e : Set X) ⊓
        centralizer ({u} : Set X) ≤ dihedralCentralizer e := by
      intro x hx
      have hxC : x ∈ centralizer ({u} : Set X) := hx.2
      have hxK : x ∈ Subgroup.centralizer (altCentralizer e : Set X) := hx.1
      have hcenter : (⟨x, hxC⟩ : ↥(centralizer ({u} : Set X))) ∈
          Subgroup.centralizer (altSubgroup.comap e.toMonoidHom :
            Set ↥(centralizer ({u} : Set X))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        have hk : (y : X) ∈ altCentralizer e := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
        exact (Subgroup.mem_centralizer_iff.mp hxK) (y : X) hk
      rw [centralizer_comap_altSubgroup] at hcenter
      exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hcenter, rfl⟩
    exact (le_inf hTC_centK inf_le_right).trans hcentKD
  haveI : Finite ↥S := inferInstance
  have hSp : IsPGroup 2 ↥S := IsPGroup.of_card hsd.card_S
  haveI : Group.IsNilpotent ↥S := hSp.isNilpotent
  let H : Subgroup ↥S := (T ⊓ S).subgroupOf S
  have hHnormal : H.Normal := by
    dsimp only [H]
    rw [Subgroup.inf_subgroupOf_right]
    exact hT.subgroupOf S
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hmem : (⟨u, hsd.le_S hsd.mem_B⟩ : ↥S) ∈ H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨huT, hsd.le_S hsd.mem_B⟩
    rw [hbot] at hmem
    exact hu1 (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
  haveI := hHnormal
  obtain ⟨z', hz'ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  have hz'H : (z' : ↥S) ∈ H := z'.2.1
  have hz'cen : (z' : ↥S) ∈ Subgroup.center ↥S := z'.2.2
  have hz'T : ((z' : ↥S) : X) ∈ T := (Subgroup.mem_subgroupOf.mp hz'H).1
  have hzC : ((z' : ↥S) : X) ∈ centralizer ({u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz'cen
      (⟨u, hsd.le_S hsd.mem_B⟩ : ↥S))).symm
  have hzD : ((z' : ↥S) : X) ∈ dihedralCentralizer e :=
    hTC_le_D ⟨hz'T, hzC⟩
  have hzDt : ((z' : ↥S) : X) ∈ (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨((z' : ↥S) : X), hzD, ?_⟩
    have hcomm := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hz'cen
      (⟨τ, hsd.mem_S⟩ : ↥S))
    have hcomm' : τ * ((z' : ↥S) : X) = ((z' : ↥S) : X) * τ := hcomm
    show τ * ((z' : ↥S) : X) * τ⁻¹ = ((z' : ↥S) : X)
    rw [hcomm']
    group
  have hzbot : ((z' : ↥S) : X) ∈ (⊥ : Subgroup X) := by
    rw [← hsd.inf_eq_bot]
    exact ⟨hzD, hzDt⟩
  exact hz'ne (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hzbot)))

theorem mem_and_altCentralizer_le_of_inf_centralizer_ne_bot [Finite X] {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) {T : Subgroup X} (hT : T.Normal)
    (hne : T ⊓ centralizer ({u} : Set X) ≠ ⊥) : u ∈ T ∧ altCentralizer e ≤ T := by
  have hu : u ∈ T := by
    have hN : (T.subgroupOf (centralizer ({u} : Set X))).Normal := hT.subgroupOf _
    have hne' : T.subgroupOf (centralizer ({u} : Set X)) ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : ↥(centralizer ({u} : Set X))) ∈
          T.subgroupOf (centralizer ({u} : Set X)) := hx.1
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
    rcases mem_or_comap_altSubgroup_le_of_normal e _ hN hne' with h | h
    · rw [← mk_eq_symm_r_two hu1 e] at h
      exact h
    · refine mem_of_altCentralizer_le hu1 e P hP hT ?_
      rintro _ ⟨k, hk, rfl⟩
      exact h hk
  exact ⟨hu, altCentralizer_le_of_mem hu1 e P hP hT hu⟩

theorem card_centralizer_eq_of_mulEquiv {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    Nat.card ↥(centralizer ({u} : Set X)) = 960 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem mem_and_altCentralizer_le_and_card_dvd [Finite X] {u : X} (hu : u * u = 1) (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) {T : Subgroup X} (hT : T.Normal)
    (hTe : Even (Nat.card ↥T)) :
    u ∈ T ∧ altCentralizer e ≤ T ∧ Nat.card ↥(T ⊓ centralizer ({u} : Set X)) ∣ 960 := by
  haveI := hT
  have hnorm : u ∈ normalizer (T : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top u
  have hne : T ⊓ centralizer ({u} : Set X) ≠ ⊥ := by
    intro h
    have hev := CFSG.GroupTheory.even_card_inf_centralizer_of_mem_normalizer hu hnorm hTe
    rw [h, Subgroup.card_bot] at hev
    exact Nat.not_even_one hev
  obtain ⟨huT, hK⟩ := mem_and_altCentralizer_le_of_inf_centralizer_ne_bot hu1 e P hP hT hne
  refine ⟨huT, hK, ?_⟩
  rw [← card_centralizer_eq_of_mulEquiv e]
  exact Subgroup.card_dvd_of_le inf_le_right

end CFSG.EvenSporadicStandard.TwoHS.GH312
