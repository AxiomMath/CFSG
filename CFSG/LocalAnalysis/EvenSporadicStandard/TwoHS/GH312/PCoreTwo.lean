module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

private theorem d8_center_mem (x : DihedralGroup 4) :
    x ∈ Subgroup.center (DihedralGroup 4) ↔ x = 1 ∨ x = DihedralGroup.r 2 := by
  revert x; decide +kernel

private theorem prod_center_mem (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    x ∈ Subgroup.center (DihedralGroup 4 × Equiv.Perm (Fin 5)) ↔
      x = 1 ∨ x = (DihedralGroup.r 2, 1) := by
  revert x; decide +kernel

private theorem d8_abelian_bound (S : Finset (DihedralGroup 4))
    (h1 : (1 : DihedralGroup 4) ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : S.card ≤ 4 := by
  revert S; decide +kernel

private theorem s5_involution_conj_order_three (t : Equiv.Perm (Fin 5))
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g h : Equiv.Perm (Fin 5),
      (((g * t * g⁻¹) * (h * t * h⁻¹)) ^ 3 = 1) ∧
      (((g * t * g⁻¹) * (h * t * h⁻¹)) ≠ 1) := by
  revert t; decide +kernel

private theorem s5_normal_two_eq_bot (M : Subgroup (Equiv.Perm (Fin 5)))
    (hM : M.Normal) (h2 : IsPGroup 2 M) : M = ⊥ := by
  by_contra hne
  have hcard : Nat.card ↥M ≠ 1 := fun h1 => hne ((Subgroup.card_eq_one (H := M)).mp h1)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, pow_zero] at hn; exact hcard hn
  have hdvd : 2 ∣ Nat.card ↥M := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (G := ↥M) hdvd
  have htX : orderOf (t : Equiv.Perm (Fin 5)) = 2 := by
    rw [← ht, Subgroup.orderOf_coe]
  have ht2 : (t : Equiv.Perm (Fin 5)) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, htX]
  have ht1 : (t : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h; rw [h, orderOf_one] at htX; norm_num at htX
  obtain ⟨g, h, hg3, hg1⟩ := s5_involution_conj_order_three (t : Equiv.Perm (Fin 5)) ht2 ht1
  have hconj1 : g * (t : Equiv.Perm (Fin 5)) * g⁻¹ ∈ M := hM.conj_mem (t : Equiv.Perm (Fin 5)) t.2 g
  have hconj2 : h * (t : Equiv.Perm (Fin 5)) * h⁻¹ ∈ M := hM.conj_mem (t : Equiv.Perm (Fin 5)) t.2 h
  have hpM : (g * (t : Equiv.Perm (Fin 5)) * g⁻¹) * (h * (t : Equiv.Perm (Fin 5)) * h⁻¹) ∈ M :=
    M.mul_mem hconj1 hconj2
  set p : ↥M := ⟨_, hpM⟩ with hpdef
  have hp3 : p ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hpdef]
    exact hg3
  have hp1 : p ≠ 1 := by
    intro h1
    exact hg1 (by simpa [hpdef] using congrArg (Subtype.val) h1)
  obtain ⟨k, hk⟩ := h2.exists_pow_pow_eq_one p
  have hdvd2 : orderOf p ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have hdvd3 : orderOf p ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hp3
  have hcop : Nat.Coprime (2 ^ k) 3 := (by decide : Nat.Coprime 2 3).pow_left k
  have h1 : orderOf p = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd3
  exact hp1 (orderOf_eq_one_iff.mp h1)

private theorem prod_normal_two_le (M : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)))
    (hM : M.Normal) (h2 : IsPGroup 2 M) :
    M ≤ (⊤ : Subgroup (DihedralGroup 4)).prod ⊥ := by
  have hM2 : (M.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5)))).Normal :=
    hM.map _ Prod.snd_surjective
  have h2' : IsPGroup 2 (M.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5)))) := h2.map _
  have hbot : M.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5))) = ⊥ :=
    s5_normal_two_eq_bot _ hM2 h2'
  have hker : M ≤ (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5))).ker :=
    (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [MonoidHom.ker_snd] at hker

private theorem d8_normal_contains_r2 (M : Subgroup (DihedralGroup 4)) (hM : M.Normal)
    (hne : M ≠ ⊥) : DihedralGroup.r 2 ∈ M := by
  have hcard : Nat.card (DihedralGroup 4) = 2 ^ 3 := by
    rw [DihedralGroup.nat_card]; norm_num
  haveI hnil : Group.IsNilpotent (DihedralGroup 4) := (IsPGroup.of_card hcard).isNilpotent
  have hinf : M ⊓ Subgroup.center (DihedralGroup 4) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  have hxM : (x : DihedralGroup 4) ∈ M := (Subgroup.mem_inf.mp x.2).1
  have hxZ : (x : DihedralGroup 4) ∈ Subgroup.center (DihedralGroup 4) := (Subgroup.mem_inf.mp x.2).2
  rcases (d8_center_mem (x : DihedralGroup 4)).mp hxZ with h | h
  · exact absurd (Subtype.ext h) hx1
  · rwa [h] at hxM

theorem pCore_two_eq_bot_of_centralizer_equiv {X : Type} [Group X] [Finite X]
    (hZ : center X = ⊥) (P : Sylow 2 X) (hP : Nat.card P = 2 ^ 7) {u : X} (hu : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    CFSG.pCore 2 X = ⊥ := by
  classical
  let C : Subgroup X := centralizer ({u} : Set X)
  have huC : u ∈ C := by
    change u ∈ centralizer ({u} : Set X)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let uC : ↥C := ⟨u, huC⟩
  have huZ : uC ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    simpa [uC] using Subgroup.mem_centralizer_singleton_iff.mp c.2
  have heuZ : e uC ∈ Subgroup.center (DihedralGroup 4 × Equiv.Perm (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨c, rfl⟩ := e.surjective y
    rw [← e.map_mul, ← e.map_mul]
    exact congrArg e (Subgroup.mem_center_iff.mp huZ c)
  have heu_ne : e uC ≠ 1 := by
    intro h
    have h1 : uC = 1 := e.injective (by rw [h, map_one])
    exact hu (by simpa [uC] using congrArg (Subtype.val) h1)
  have heu : e uC = (DihedralGroup.r 2, 1) := by
    rcases (prod_center_mem (e uC)).mp heuZ with h | h
    · exact absurd h heu_ne
    · exact h
  have hCenterC : ∀ x : ↥C, x ∈ Subgroup.center ↥C ↔ x = 1 ∨ x = uC := by
    intro x
    constructor
    · intro hx
      have hx' : e x ∈ Subgroup.center (DihedralGroup 4 × Equiv.Perm (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨c, rfl⟩ := e.surjective y
        rw [← e.map_mul, ← e.map_mul]
        exact congrArg e (Subgroup.mem_center_iff.mp hx c)
      rcases (prod_center_mem (e x)).mp hx' with h | h
      · left; exact e.injective (by rw [h, map_one])
      · right; exact e.injective (by rw [h, heu])
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact huZ
  have hCcard : Nat.card ↥C = 960 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm,
      Nat.card_fin]
    norm_num [Nat.factorial]
  have hfac : (960 : ℕ).factorization 2 = 6 := by decide +kernel
  by_contra hQ
  let Q : Subgroup X := CFSG.pCore 2 X
  have hQne : Q ≠ ⊥ := hQ
  haveI hQnormal : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup
  haveI hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  let Z : Subgroup ↥Q := Subgroup.center ↥Q
  have hZnt : Nontrivial ↥Z := hQp.center_nontrivial
  have hZne : Z ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot Z).mp hZnt
  let N : Subgroup X := Z.map Q.subtype
  have hNleQ : N ≤ Q := Subgroup.map_subtype_le Z
  have hNp : IsPGroup 2 N := hQp.to_le hNleQ
  haveI hNnormal : N.Normal := inferInstance
  have hNne : N ≠ ⊥ := by
    intro h
    apply hZne
    apply le_bot_iff.mp
    intro z hz
    have hz' : Q.subtype z ∈ N := Subgroup.mem_map_of_mem Q.subtype hz
    rw [h] at hz'
    exact Subtype.ext (Subgroup.mem_bot.mp hz')
  have hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z1, hz1, hz1x⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z2, hz2, hz2x⟩ := Subgroup.mem_map.mp hy
    rw [← hz1x, ← hz2x, ← map_mul, ← map_mul]
    exact congrArg Q.subtype (Subgroup.mem_center_iff.mp hz1 z2).symm
  let KC : Subgroup ↥C := N.subgroupOf C
  have hKCnormal : KC.Normal := hNnormal.comap C.subtype
  have hKCp : IsPGroup 2 KC := hNp.comap_of_injective C.subtype C.subtype_injective
  have hMle : Subgroup.map e.toMonoidHom KC ≤ (⊤ : Subgroup (DihedralGroup 4)).prod ⊥ :=
    prod_normal_two_le _ (hKCnormal.map e.toMonoidHom e.surjective) (hKCp.map e.toMonoidHom)
  by_cases huN : u ∈ N
  ·
    have hNleC : N ≤ C := by
      intro x hx
      change x ∈ centralizer ({u} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hNab x hx u huN
    have hKCab : ∀ x y : ↥C, x ∈ KC → y ∈ KC → x * y = y * x := by
      intro x y hx hy
      apply Subtype.ext
      exact hNab (x : X) hx (y : X) hy
    let f : ↥KC →* DihedralGroup 4 :=
      { toFun := fun x => (e (x : ↥C)).1
        map_one' := by simp
        map_mul' := by intro x y; simp [map_mul] }
    haveI : Fintype ↥KC := Fintype.ofFinite ↥KC
    have hfinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      have hxM : e (x : ↥C) ∈ (⊤ : Subgroup (DihedralGroup 4)).prod ⊥ := hMle (Subgroup.mem_map_of_mem e.toMonoidHom x.2)
      have hyM : e (y : ↥C) ∈ (⊤ : Subgroup (DihedralGroup 4)).prod ⊥ := hMle (Subgroup.mem_map_of_mem e.toMonoidHom y.2)
      have hx2 : (e (x : ↥C)).2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hxM).2
      have hy2 : (e (y : ↥C)).2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hyM).2
      have hxy' : (e (x : ↥C)).1 = (e (y : ↥C)).1 := hxy
      ext
      · exact hxy'
      · rw [hx2, hy2]
    let S : Finset (DihedralGroup 4) := Finset.univ.image f
    have hScard : S.card = Nat.card ↥KC := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Nat.card_eq_fintype_card]
    have hSle : S.card ≤ 4 := by
      refine d8_abelian_bound S ?_ ?_ ?_
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, map_one f⟩
      · intro x hx y hy
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨a * b, Finset.mem_univ _, map_mul f a b⟩
      · intro x hx y hy
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
        rw [← map_mul, ← map_mul]
        exact congrArg f (Subtype.ext (hKCab (a : ↥C) (b : ↥C) a.2 b.2))
    have hNcard_le : Nat.card N ≤ 4 := by
      calc Nat.card N = Nat.card ↥KC :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleC).toEquiv).symm
        _ = S.card := hScard.symm
        _ ≤ 4 := hSle
    have hclassle : C.index ≤ 3 := by
      have hsub : conjugatesOf u ⊆ (N : Set X) \ {1} := by
        intro x hx
        refine ⟨?_, ?_⟩
        · obtain ⟨c, hc⟩ := isConj_iff.mp hx
          rw [← hc]
          exact hNnormal.conj_mem u huN c
        · intro hx1
          have hconj : IsConj u 1 := hx1 ▸ hx
          exact hu (isConj_one_left.mp hconj)
      have h1mem : (1 : X) ∈ (N : Set X) := Subgroup.one_mem N
      have hcalc : (conjugatesOf u).ncard ≤ ((N : Set X) \ {1}).ncard := Set.ncard_le_ncard hsub
      rw [Set.ncard_sdiff_singleton_of_mem h1mem] at hcalc
      have hNncard : (N : Set X).ncard = Nat.card N := Nat.card_coe_set_eq (N : Set X)
      rw [hNncard] at hcalc
      have : Nat.card N - 1 ≤ 3 := by simpa using Nat.sub_le_sub_right hNcard_le 1
      exact (Subgroup.index_centralizer_eq_ncard u).trans_le (hcalc.trans this)
    have hEven : 2 ∣ C.index := by
      have hXcard : Nat.card X = 2 ^ 7 * P.index := by
        rw [← hP, Subgroup.card_mul_index]
      have hCcardidx : Nat.card ↥C * C.index = Nat.card X := Subgroup.card_mul_index C
      have hm : 2 * P.index = 15 * C.index := by
        have h1 : 2 ^ 6 * (2 * P.index) = Nat.card X := by rw [hXcard]; ring
        have h2 : 2 ^ 6 * (15 * C.index) = Nat.card X := by rw [← hCcardidx, hCcard]; ring
        exact Nat.mul_left_cancel (by norm_num : 0 < 2 ^ 6) (by rw [h1, h2])
      have hdiv : 2 ∣ 15 * C.index := by rw [← hm]; exact dvd_mul_right 2 _
      rcases Nat.prime_two.dvd_mul.mp hdiv with h | h
      · omega
      · exact h
    have hCindex2 : C.index = 2 := by
      have hne1 : C.index ≠ 1 := by
        intro h1
        have htop : C = ⊤ := Subgroup.index_eq_one.mp h1
        have huc : u ∈ center X := by
          rw [Subgroup.mem_center_iff]
          intro g
          have : g ∈ C := by rw [htop]; exact Subgroup.mem_top g
          exact Subgroup.mem_centralizer_singleton_iff.mp this
        rw [hZ] at huc
        exact hu (Subgroup.mem_bot.mp huc)
      have hidx0 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hCnormal : C.Normal := Subgroup.normal_of_index_eq_two hCindex2
    have hcentral : ∀ g : X, g * u * g⁻¹ = u := by
      intro g
      have hmemC : g * u * g⁻¹ ∈ C := hCnormal.conj_mem u huC g
      have hmemZ : (⟨g * u * g⁻¹, hmemC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro c
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_mk]
        have hgc : g⁻¹ * (c : X) * g ∈ C := by
          simpa using hCnormal.conj_mem (c : X) c.2 g⁻¹
        have hcomm : u * (g⁻¹ * (c : X) * g) = (g⁻¹ * (c : X) * g) * u :=
          (Subgroup.mem_centralizer_iff.mp hgc) u (Set.mem_singleton u)
        rw [show (g * u * g⁻¹) * (c : X) = g * (u * (g⁻¹ * (c : X) * g)) * g⁻¹ by group,
          hcomm,
          show g * ((g⁻¹ * (c : X) * g) * u) * g⁻¹ = (c : X) * (g * u * g⁻¹) by group]
      rcases (hCenterC ⟨g * u * g⁻¹, hmemC⟩).mp hmemZ with h | h
      · exfalso
        have h1 : g * u * g⁻¹ = 1 := congrArg (Subtype.val) h
        have h2 : u = 1 := by
          have := congrArg (fun y => g⁻¹ * y * g) h1
          simpa [mul_assoc] using this
        exact hu h2
      · exact congrArg (Subtype.val) h
    have hucenter : u ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hcentral g
      calc g * u = (g * u * g⁻¹) * g := by group
        _ = u * g := by rw [this]
    rw [hZ] at hucenter
    exact hu (Subgroup.mem_bot.mp hucenter)
  ·
    have hKCbot : KC = ⊥ := by
      by_contra hKCne
      have hMapNe : Subgroup.map e.toMonoidHom KC ≠ ⊥ := by
        intro h
        apply hKCne
        apply le_bot_iff.mp
        intro x hx
        have hx' : e (x : ↥C) ∈ Subgroup.map e.toMonoidHom KC :=
          Subgroup.mem_map_of_mem e.toMonoidHom hx
        rw [h] at hx'
        have he1 : e (x : ↥C) = 1 := Subgroup.mem_bot.mp hx'
        have hx1 : x = 1 := by simpa using congrArg e.symm he1
        exact hx1
      let A : Subgroup (DihedralGroup 4) :=
        (Subgroup.map e.toMonoidHom KC).map
          (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5)))
      have hAnormal : A.Normal :=
        (hKCnormal.map e.toMonoidHom e.surjective).map
          (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5))) Prod.fst_surjective
      have hAne : A ≠ ⊥ := by
        intro hA
        apply hMapNe
        have hle : Subgroup.map e.toMonoidHom KC ≤
            (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5))).ker :=
          (Subgroup.map_le_iff_le_comap).mp (le_of_eq hA)
        apply le_bot_iff.mp
        intro x hx
        have hx1 : x ∈ (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5))).ker := hle hx
        rw [MonoidHom.ker_fst] at hx1
        have hx1' : x.1 ∈ (⊥ : Subgroup (DihedralGroup 4)) := (Subgroup.mem_prod.mp hx1).1
        have hx2' : x.2 ∈ (⊥ : Subgroup (Equiv.Perm (Fin 5))) :=
          (Subgroup.mem_prod.mp (hMle hx)).2
        exact Subgroup.mem_bot.mpr
          (Prod.ext (Subgroup.mem_bot.mp hx1') (Subgroup.mem_bot.mp hx2'))
      have hr2 : DihedralGroup.r 2 ∈ A := d8_normal_contains_r2 A hAnormal hAne
      obtain ⟨x, hxK, hx1⟩ := Subgroup.mem_map.mp hr2
      have hx2 : x.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hMle hxK)).2
      have hxeq : x = (DihedralGroup.r 2, 1) := Prod.ext hx1 hx2
      obtain ⟨c, hcKC, hce⟩ := Subgroup.mem_map.mp hxK
      have hcu : c = uC := e.injective (hce.trans (hxeq.trans heu.symm))
      exact huN (Subgroup.mem_subgroupOf.mp (hcu ▸ hcKC))
    have hNCbot : N ⊓ C = ⊥ := by
      have h1 : (N.subgroupOf C).map C.subtype = N ⊓ C := Subgroup.subgroupOf_map_subtype N C
      have h2 : N.subgroupOf C = ⊥ := hKCbot
      rw [h2, Subgroup.map_bot] at h1
      exact h1.symm
    obtain ⟨T, hKCT⟩ := IsPGroup.exists_le_sylow hKCp
    have hTp : IsPGroup 2 (T.map C.subtype) := T.isPGroup'.map C.subtype
    obtain ⟨P1, hTP1⟩ := IsPGroup.exists_le_sylow hTp
    have hP1card : Nat.card (P1 : Subgroup X) = 2 ^ 7 := by
      rw [Sylow.card_eq_multiplicity P1, ← Sylow.card_eq_multiplicity P, hP]
    have hTcard : Nat.card (T : Subgroup ↥C) = 2 ^ 6 := by
      rw [Sylow.card_eq_multiplicity T, hCcard, hfac]
    have hNleP1 : N ≤ P1 := hNp.le_sylow_of_normal P1
    have hTmcard : Nat.card (T.map C.subtype) = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective C.subtype_injective, hTcard]
    have hrel : (T.map C.subtype).relIndex (P1 : Subgroup X) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := T.map C.subtype) (K := P1)
      rw [inf_eq_left.mpr hTP1, hTmcard, hP1card] at h
      omega
    have hIndexLe : (N ⊓ T.map C.subtype).relIndex N ≤ 2 := by
      have h1 : (T.map C.subtype).relIndex N ≤ (T.map C.subtype).relIndex P1 :=
        Subgroup.relIndex_le_of_le_right hNleP1 (by rw [hrel]; norm_num)
      have h2 : (N ⊓ T.map C.subtype).relIndex N = (T.map C.subtype).relIndex N := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      rw [hrel] at h1
      rwa [← h2] at h1
    have hNTbot : N ⊓ T.map C.subtype = ⊥ := by
      refine le_bot_iff.mp ?_
      calc N ⊓ T.map C.subtype ≤ N ⊓ C :=
            inf_le_inf_left _ (Subgroup.map_subtype_le (T : Subgroup ↥C))
        _ = ⊥ := hNCbot
    have hNcard : Nat.card N ≤ 2 := by
      have h2 : (⊥ : Subgroup X).relIndex N ≤ 2 := by
        rw [← hNTbot]; exact hIndexLe
      rwa [Subgroup.relIndex_bot_left] at h2
    have hNcard2 : Nat.card N = 2 := by
      have hne1 : Nat.card N ≠ 1 := fun h => hNne ((Subgroup.card_eq_one (H := N)).mp h)
      have hpos : 0 < Nat.card N := Nat.card_pos
      omega
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNne
    obtain ⟨y0, hy0ne, hy0uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).mp hNcard2
    have hn_eq : (n : ↥N) = y0 := hy0uniq n hn1
    have hcentral_n : ∀ g : X, g * (n : X) * g⁻¹ = (n : X) := by
      intro g
      have hmemN : g * (n : X) * g⁻¹ ∈ N := hNnormal.conj_mem (n : X) n.2 g
      have hne1' : (⟨g * (n : X) * g⁻¹, hmemN⟩ : ↥N) ≠ 1 := by
        intro h
        apply hn1
        have h1 : g * (n : X) * g⁻¹ = 1 := congrArg (Subtype.val) h
        have h2 : (n : X) = 1 := by
          have := congrArg (fun y => g⁻¹ * y * g) h1
          simpa [mul_assoc] using this
        exact Subtype.ext h2
      have heq : (⟨g * (n : X) * g⁻¹, hmemN⟩ : ↥N) = y0 := hy0uniq _ hne1'
      have := congrArg (Subtype.val) (heq.trans hn_eq.symm)
      simpa using this
    have hncenter : (n : X) ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hcentral_n g
      calc g * (n : X) = (g * (n : X) * g⁻¹) * g := by group
        _ = (n : X) * g := by rw [this]
    rw [hZ] at hncenter
    exact hn1 (Subtype.ext (Subgroup.mem_bot.mp hncenter))

end CFSG.EvenSporadicStandard.TwoHS.GH312

end
