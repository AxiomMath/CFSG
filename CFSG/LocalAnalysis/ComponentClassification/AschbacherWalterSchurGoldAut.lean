module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic
public import CFSG.Walter.AStar.N1
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.ComponentClassification.WalterSchur

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {X P E : Subgroup Y}

omit [Finite Y] in
theorem omegaOne_eq_self (hP : ∀ p ∈ P, p * p = 1) : omegaOne P = P :=
  le_antisymm (omegaOne_le P) fun p hp =>
    Subgroup.subset_closure ⟨hp, by rw [sq]; exact hP p hp⟩

omit [Finite Y] in
theorem eq_of_isSylowOf (hP : IsSylowOf 2 P X) {R : Subgroup Y} (hR : IsPGroup 2 R)
    (hRX : R ≤ X) (hPR : P ≤ R) : R = P := by
  obtain ⟨Q, hQ⟩ := hP
  have hR' : IsPGroup 2 (R.subgroupOf X) := hR.comap_subtype
  have hQR : (Q : Subgroup X) ≤ R.subgroupOf X := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hPR (hQ ▸ Subgroup.mem_map_of_mem X.subtype hq)
  have h := Q.is_maximal' hR' hQR
  rw [← hQ, ← h, Subgroup.map_subgroupOf_eq_of_le hRX]

omit [Finite Y] in
theorem exists_sylow_sup (hP : IsSylowOf 2 P X) (hE2 : IsPGroup 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y)) (hEC : E ≤ Subgroup.centralizer (P : Set Y)) :
    ∃ S : Sylow 2 (X ⊔ E : Subgroup Y), (S : Subgroup (X ⊔ E : Subgroup Y)).map
      (X ⊔ E : Subgroup Y).subtype = P ⊔ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP
  have hPX : P ≤ X := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := by rw [← hQ]; exact Q.isPGroup'.map _
  set H := X ⊔ E with hHdef
  have hT2 : IsPGroup 2 (P ⊔ E : Subgroup Y) :=
    hP2.to_sup_of_normal_left' hE2 (hEC.trans (Subgroup.centralizer_le_normalizer _))
  have hTH : P ⊔ E ≤ H := sup_le_sup_right hPX E
  obtain ⟨S, hS⟩ := (hT2.comap_subtype (K := H)).exists_le_sylow
  refine ⟨S, le_antisymm ?_ ?_⟩
  ·
    rintro _ ⟨s, hs, rfl⟩
    have hsH : (s : Y) ∈ (X : Set Y) * (E : Set Y) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X E hEX]
      exact s.2
    obtain ⟨x, hx, e, he, hxe⟩ := Set.mem_mul.mp hsH
    set R := (S : Subgroup H).map H.subtype ⊓ X with hRdef
    have hR2 : IsPGroup 2 R := (S.isPGroup'.map H.subtype).to_le inf_le_left
    have hTS : P ⊔ E ≤ (S : Subgroup H).map H.subtype := by
      intro t ht
      exact ⟨⟨t, hTH ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
    have hPR : P ≤ R := le_inf (le_sup_left.trans hTS) hPX
    have hReq := eq_of_isSylowOf ⟨Q, hQ⟩ hR2 inf_le_right hPR
    have hxR : x ∈ R := by
      refine ⟨?_, hx⟩
      have he' : e ∈ (S : Subgroup H).map H.subtype := hTS (Subgroup.mem_sup_right he)
      have hs' : (s : Y) ∈ (S : Subgroup H).map H.subtype := ⟨s, hs, rfl⟩
      rw [show x = (s : Y) * e⁻¹ by rw [← hxe]; group]
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ he')
    rw [hReq] at hxR
    rw [Subgroup.coe_subtype, ← hxe]
    exact Subgroup.mul_mem_sup hxR he
  · intro t ht
    exact ⟨⟨t, hTH ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

theorem card_le_omegaOne_of_elementary (hX : IsSimpleGroup X)
    (hXnonab : ∃ a b : X, a * b ≠ b * a) (hP : IsSylowOf 2 P X) (hP2 : ∀ p ∈ P, p * p = 1)
    (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) (hE : IsElemAbelian 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e) :
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [omegaOne_eq_self hP2] at hEcent ⊢
  have hP' := hP
  obtain ⟨Q, hQ⟩ := hP'
  have hPX : P ≤ X := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hE2 : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 e e.2)⟩
  have hEC : E ≤ Subgroup.centralizer (P : Set Y) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun p hp => (hEcent e he p hp).symm
  set H := X ⊔ E with hHdef
  obtain ⟨S, hS⟩ := exists_sylow_sup hP hE2 hEX hEC
  have hTab : P ⊔ E ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
    have hPC : P ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro p hp
        exact Subgroup.mem_centralizer_iff.mpr fun q hq => hPc q hq p hp
      · exact hEC
    have hEC' : E ≤ Subgroup.centralizer ((P ⊔ E : Subgroup Y) : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [← Subgroup.le_centralizer_iff]
        exact hEC
      · intro e he
        exact Subgroup.mem_centralizer_iff.mpr fun f hf =>
          congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨e, he⟩)
    exact sup_le hPC hEC'
  have hSab : IsMulCommutative (S : Subgroup H) := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have ha : ((a : H) : Y) ∈ P ⊔ E := hS ▸ ⟨a, a.2, rfl⟩
    have hb : ((b : H) : Y) ∈ P ⊔ E := hS ▸ ⟨b, b.2, rfl⟩
    change ((a : H) : Y) * ((b : H) : Y) = ((b : H) : Y) * ((a : H) : Y)
    exact Subgroup.mem_centralizer_iff.mp (hTab hb) _ ha
  have hHab : Walter.HasAbelianSylowTwo H := Walter.hasAbelianSylowTwo_of_sylow S hSab
  have hXH : X ≤ H := le_sup_left
  set X' : Subgroup H := X.subgroupOf H with hX'def
  let eX : X' ≃* X := Subgroup.subgroupOfEquivOfLe hXH
  have : IsSimpleGroup X := hX
  have hX's : IsSimpleGroup X' := eX.isSimpleGroup
  have hX'nonab : ∃ a b : X', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXnonab
    refine ⟨eX.symm a, eX.symm b, fun h => hab ?_⟩
    simpa using congrArg eX h
  have hX'n : X'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
    (sup_le Subgroup.le_normalizer hEX)
  have hSN : (S : Subgroup H) ≤ Subgroup.normalizer (X' : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hinner := Walter.exists_inner_of_sylow_le_normalizer hHab X' hX'nonab S hSN
  have hEinner : ∀ e ∈ E, ∃ k ∈ X, ∀ x ∈ X, e * x * e⁻¹ = k * x * k⁻¹ := by
    intro e he
    have heS : (⟨e, Subgroup.mem_sup_right he⟩ : H) ∈ (S : Subgroup H) := by
      have hT : e ∈ (S : Subgroup H).map H.subtype := hS ▸ Subgroup.mem_sup_right he
      obtain ⟨s, hs, hse⟩ := hT
      rw [show (⟨e, Subgroup.mem_sup_right he⟩ : H) = s from Subtype.ext hse.symm]
      exact hs
    obtain ⟨k, hk, hkx⟩ := hinner _ heS
    refine ⟨k, Subgroup.mem_subgroupOf.mp hk, fun x hx => ?_⟩
    have h := congrArg Subtype.val (hkx ⟨x, hXH hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
    simpa using h
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hXnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  set ι : X →* MulAut X := MulAut.conj with hιdef
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZX]
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut X => φ x) (MonoidHom.mem_ker.mp hk)
    simp only [hιdef, MulAut.conj_apply, MulAut.one_apply] at h
    calc x * k = k * x * k⁻¹ * k := by rw [h]
      _ = k * x := by group
  set A := (conjAct hEX).range with hAdef
  have hAι : A ≤ ι.range := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hEinner e e.2
    refine ⟨⟨k, hk⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [conjAct_apply, hkx x x.2]
    rfl
  set At := A.comap ι with hAtdef
  have hAt : Nat.card At = Nat.card A := by
    have h := Subgroup.card_map_of_injective (K := At) hιinj
    rw [hAtdef, Subgroup.map_comap_eq, inf_eq_right.mpr hAι] at h
    exact h.symm
  have hAtQ : At ≤ (Q : Subgroup X) := by
    have hAtC : At ≤ Subgroup.centralizer ((Q : Subgroup X) : Set X) := by
      intro k hk
      obtain ⟨e, he⟩ := hk
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqP : (q : Y) ∈ P := hQ ▸ Subgroup.mem_map_of_mem X.subtype hq
      have h := congrArg (fun φ : MulAut X => ((φ q : X) : Y)) he
      simp only [conjAct_apply, hιdef, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      have h2 : ((k : X) : Y) * q * ((k : X) : Y)⁻¹ = q := by
        rw [← h, (hEcent e e.2 q hqP), mul_inv_cancel_right]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (q : Y) * ((k : X) : Y) = ((k : X) : Y) * q * ((k : X) : Y)⁻¹ * ((k : X) : Y) := by
            rw [h2]
        _ = ((k : X) : Y) * q := by group
    have hAt2 : IsPGroup 2 At := by
      intro k
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply hιinj
      obtain ⟨e, he⟩ := Subgroup.mem_comap.mp k.2
      rw [pow_one, Subgroup.coe_pow, map_pow, ← he, ← map_pow, OneMemClass.coe_one, map_one]
      have he2 : e ^ 2 = 1 := Subtype.ext (hE.2 e e.2)
      rw [he2, map_one]
    have hsup := Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_left' hAt2
      (hAtC.trans (Subgroup.centralizer_le_normalizer _))) le_sup_left
    rw [← hsup]
    exact le_sup_right
  have hAcard : Nat.card A ≤ Nat.card P := by
    rw [← hAt, ← hQ, Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_le_of_le hAtQ
  rw [card_eq_mul_card_range hEX, mul_comm]
  exact Nat.mul_le_mul_right _ hAcard

section NormalElementarySquare

private theorem isMulCommutative_sup_zpowers_of_centralizes
    {G : Type*} [Group G] {A : Subgroup G} {x : G} (hA : IsMulCommutative A)
    (hx : x ∈ Subgroup.centralizer (A : Set G)) :
    IsMulCommutative (A ⊔ Subgroup.zpowers x : Subgroup G) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA
  have hZA : Subgroup.zpowers x ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hx
  have hZZ : Subgroup.zpowers x ≤
      Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hAZ : A ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff.mpr hZA
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (sup_le (Subgroup.le_centralizer_iff.mpr (sup_le hAA hZA))
      (Subgroup.le_centralizer_iff.mpr (sup_le hAZ hZZ)))

theorem sq_mem_centralizer_of_isSylowOf
    {G : Type} [Group G] [Finite G] {X P : Subgroup G} {x : G}
    (hX : IsSimpleGroup X) (hXnonab : ∃ a b : X, a * b ≠ b * a)
    (hP : IsSylowOf 2 P X)
    (hP2 : ∀ p ∈ P, p * p = 1) (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hxN : x ∈ Subgroup.normalizer (X : Set G))
    (hxC : x ∈ Subgroup.centralizer (P : Set G)) :
    x ^ 2 ∈ Subgroup.centralizer (X : Set G) := by
  classical
  let E : Subgroup G := Subgroup.zpowers x
  let H : Subgroup G := X ⊔ E
  have hE2 : IsPGroup 2 E := hx2
  have hEX : E ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hxN
  have hEC : E ≤ Subgroup.centralizer (P : Set G) := Subgroup.zpowers_le.mpr hxC
  have hPcomm : IsMulCommutative P :=
    ⟨⟨fun p q => Subtype.ext (hPc p p.2 q q.2)⟩⟩
  have hHcomm : IsMulCommutative (P ⊔ E : Subgroup G) :=
    isMulCommutative_sup_zpowers_of_centralizes (A := P) (x := x) hPcomm hxC
  obtain ⟨S₀, hS₀⟩ := exists_sylow_sup (Y := G) hP hE2 hEX hEC
  let S : Sylow 2 H := S₀
  have hS : (S : Subgroup H).map H.subtype = P ⊔ E := hS₀
  have hScomm : IsMulCommutative (S : Subgroup H) := by
    have hmap : IsMulCommutative ((S : Subgroup H).map H.subtype) := by
      rw [hS]
      exact hHcomm
    let : IsMulCommutative ((S : Subgroup H).map H.subtype) := hmap
    have h := Subgroup.comap_injective_isMulCommutative (H := (S : Subgroup H).map H.subtype)
      H.subtype_injective
    rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h
  have hY : Walter.HasAbelianSylowTwo H :=
    Walter.hasAbelianSylowTwo_of_sylow S hScomm
  have hXH : X ≤ H := le_sup_left
  let X' : Subgroup H := X.subgroupOf H
  let eX : X' ≃* X := Subgroup.subgroupOfEquivOfLe hXH
  have : IsSimpleGroup X' := eX.isSimpleGroup
  have hX'nonab : ∃ a b : X', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXnonab
    refine ⟨eX.symm a, eX.symm b, fun h => hab ?_⟩
    simpa using congrArg eX h
  have hHN : H ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hEX
  have hX'n : X'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHN
  have hSN : (S : Subgroup H) ≤ Subgroup.normalizer (X' : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hxH : x ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxSmap : x ∈ (S : Subgroup H).map H.subtype := by
    rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨s, hsS, hsx⟩ := Subgroup.mem_map.mp hxSmap
  have hs_eq : s = ⟨x, hxH⟩ := Subtype.ext hsx
  have hxS : (⟨x, hxH⟩ : H) ∈ (S : Subgroup H) := hs_eq ▸ hsS
  obtain ⟨k, hk, hkx⟩ :=
    Walter.exists_inner_of_sylow_le_normalizer hY X' hX'nonab S hSN ⟨x, hxH⟩ hxS
  let u : X := ⟨(k : H), Subgroup.mem_subgroupOf.mp hk⟩
  have hu_action : ∀ z ∈ X, x * z * x⁻¹ = (u : G) * z * (u : G)⁻¹ := by
    intro z hz
    let zH : H := ⟨z, hXH hz⟩
    have hzX' : zH ∈ X' := Subgroup.mem_subgroupOf.mpr hz
    have h := hkx zH hzX'
    have hval := congrArg (fun y : H => (y : G)) h
    simpa [zH, u] using hval
  have hPleX : P ≤ X := hP.le
  have hPgrp : IsPGroup 2 P := hP.isPGroup
  have hu_cent_P : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpX : p ∈ X := hPleX hp
    have hact := hu_action p hpX
    have hxp : x * p = p * x :=
      (Subgroup.mem_centralizer_iff.mp hxC p hp).symm
    have huconj : (u : G) * p * (u : G)⁻¹ = p := by
      rw [← hact, hxp]
      group
    calc
      p * (u : G) = ((u : G) * p * (u : G)⁻¹) * (u : G) := by rw [huconj]
      _ = (u : G) * p := by group
  obtain ⟨m, hm⟩ := hx2.exists_pow_pow_eq_one
    (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x)
  have hxm : x ^ (2 ^ m) = 1 := by
    simpa using congrArg Subtype.val hm
  let c : G := (u : G)⁻¹ * x
  have hc_cent : c ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hcz : c * z * c⁻¹ = z := by
      dsimp [c]
      calc
        ((u : G)⁻¹ * x) * z * ((u : G)⁻¹ * x)⁻¹ =
            (u : G)⁻¹ * (x * z * x⁻¹) * (u : G) := by group
        _ = (u : G)⁻¹ * ((u : G) * z * (u : G)⁻¹) * (u : G) := by
          rw [hu_action z hz]
        _ = z := by group
    calc
      z * c = (c * z * c⁻¹) * c := by rw [hcz]
      _ = c * z := by group
  have huc : (u : G) * c = c * (u : G) :=
    Subgroup.mem_centralizer_iff.mp hc_cent (u : G) u.2
  have hx_eq : x = (u : G) * c := by
    dsimp [c]
    group
  have hxpow_exp : (u : G) ^ (2 ^ m) * c ^ (2 ^ m) = 1 := by
    have h := hxm
    rw [hx_eq] at h
    rw [Commute.mul_pow huc (2 ^ m)] at h
    exact h
  have hu_pow_eq : (u : G) ^ (2 ^ m) = (c ^ (2 ^ m))⁻¹ := by
    have hc_eq : c ^ (2 ^ m) = ((u : G) ^ (2 ^ m))⁻¹ :=
      eq_inv_of_mul_eq_one_right hxpow_exp
    rw [hc_eq, inv_inv]
  have hu_pow_cent : (u : G) ^ (2 ^ m) ∈ Subgroup.centralizer (X : Set G) := by
    rw [hu_pow_eq]
    exact (Subgroup.centralizer (X : Set G)).inv_mem
      ((Subgroup.centralizer (X : Set G)).pow_mem hc_cent (2 ^ m))
  have hu_pow_mem : (u : G) ^ (2 ^ m) ∈ X := X.pow_mem u.2 _
  have hu_pow_one : (u : G) ^ (2 ^ m) = 1 := by
    have hcenter : (⟨(u : G) ^ (2 ^ m), hu_pow_mem⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hu_pow_cent (y : G) y.2
    have hXsimple : IsSimpleGroup X := hX
    rw [Walter.center_eq_bot_of_isSimpleGroup (G := X) hXnonab, Subgroup.mem_bot] at hcenter
    exact congrArg Subtype.val hcenter
  have hu2 : IsPGroup 2 (Subgroup.zpowers (u : G)) := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := m) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hu_pow_one
  have huN : Subgroup.zpowers (u : G) ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hu_cent_P).trans (Subgroup.centralizer_le_normalizer _)
  have hPU2 : IsPGroup 2 (P ⊔ Subgroup.zpowers (u : G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (H := P) (K := Subgroup.zpowers (u : G)) hPgrp hu2 huN
  have hPUX : P ⊔ Subgroup.zpowers (u : G) ≤ X :=
    sup_le hPleX (Subgroup.zpowers_le.mpr u.2)
  have hsup_eq : P ⊔ Subgroup.zpowers (u : G) = P :=
    eq_of_isSylowOf hP hPU2 hPUX le_sup_left
  have huP : (u : G) ∈ P := by
    rw [← hsup_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (u : G))
  have hu_sq : (u : G) ^ 2 = 1 := by
    simpa [pow_two] using hP2 (u : G) huP
  have hx2_eq : x ^ 2 = c ^ 2 := by
    rw [hx_eq, Commute.mul_pow huc 2, hu_sq, one_mul]
  rw [hx2_eq]
  exact (Subgroup.centralizer (X : Set G)).pow_mem hc_cent 2

end NormalElementarySquare

end CFSG.ComponentClassification.WalterSchur
