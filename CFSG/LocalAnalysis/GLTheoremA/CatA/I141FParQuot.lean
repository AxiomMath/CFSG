module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.LieType.ChevTwo.Defs
import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FPar

open CFSG.Open
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

noncomputable def conjQ (H : Subgroup Γ) [H.Normal] : Γ →* MulAut (↥H ⧸ Subgroup.center ↥H) :=
  (MulAut.mapQuotient (Subgroup.center ↥H)).comp MulAut.conjNormal

@[expose] def zBar (H A : Subgroup Γ) : Subgroup (↥H ⧸ Subgroup.center ↥H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H))

theorem zBar_mono {H A B : Subgroup Γ} (h : A ≤ B) : zBar H A ≤ zBar H B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H h)

private theorem zBar_inf_centralizer_le_centFix {H E : Subgroup Γ} [H.Normal] :
    zBar H (H ⊓ Subgroup.centralizer (E : Set Γ)) ≤ I142.centFix (E.map (conjQ H)) := by
  intro y hy
  rw [I142.mem_centFix]
  intro e' he'
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 he'
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
  have hhX : (h : Γ) ∈ H ⊓ Subgroup.centralizer (E : Set Γ) :=
    Subgroup.mem_subgroupOf.mp hh
  have hcent : (h : Γ) ∈ Subgroup.centralizer (E : Set Γ) :=
    (Subgroup.mem_inf.mp hhX).2
  have hcomm : e * (h : Γ) = (h : Γ) * e :=
    (Subgroup.mem_centralizer_iff.mp hcent) e he
  change MulAut.mapQuotient (Subgroup.center ↥H) (MulAut.conjNormal e)
    (h : ↥H ⧸ Subgroup.center ↥H) = (h : ↥H ⧸ Subgroup.center ↥H)
  rw [MulAut.mapQuotient_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  calc e * (h : Γ) * e⁻¹ = (h : Γ) * e * e⁻¹ := by rw [hcomm]
    _ = (h : Γ) := by group

private theorem zBar_inf_centralizer_normal {H E : Subgroup Γ} [H.Normal] :
    ((zBar H (H ⊓ Subgroup.centralizer (E : Set Γ))).subgroupOf
        (I142.centFix (E.map (conjQ H)))).Normal := by
  have hle := zBar_inf_centralizer_le_centFix (H := H) (E := E)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro a g ha hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥H) g
  have hxX : (x : Γ) ∈ H ⊓ Subgroup.centralizer (E : Set Γ) :=
    Subgroup.mem_subgroupOf.mp hx
  have hyFix : ∀ e' ∈ E.map (conjQ H),
      e' (y : ↥H ⧸ Subgroup.center ↥H) = (y : ↥H ⧸ Subgroup.center ↥H) :=
    I142.mem_centFix.mp hg
  have hconjX : (y : Γ) * (x : Γ) * (y : Γ)⁻¹ ∈
      H ⊓ Subgroup.centralizer (E : Set Γ) := by
    constructor
    · exact H.mul_mem (H.mul_mem y.2 x.2) (H.inv_mem y.2)
    · change (y : Γ) * (x : Γ) * (y : Γ)⁻¹ ∈ Subgroup.centralizer (E : Set Γ)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hxy : e * (x : Γ) = (x : Γ) * e :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxX).2) e he
      have hqy : (QuotientGroup.mk' (Subgroup.center ↥H)) ((MulAut.conjNormal e) y) =
          (QuotientGroup.mk' (Subgroup.center ↥H)) y := by
        have h := hyFix (conjQ H e) (Subgroup.mem_map_of_mem _ he)
        change MulAut.mapQuotient (Subgroup.center ↥H) (MulAut.conjNormal e)
          (y : ↥H ⧸ Subgroup.center ↥H) = _ at h
        rw [MulAut.mapQuotient_mk] at h
        exact h
      set z : ↥H := ((MulAut.conjNormal e) y)⁻¹ * y with hzdef
      have hz : z ∈ Subgroup.center ↥H :=
        (QuotientGroup.eq (s := Subgroup.center ↥H)).mp hqy
      have hcy : (MulAut.conjNormal e) y = y * z⁻¹ := by
        rw [hzdef]
        group
      have hzx : z⁻¹ * (x : ↥H) * z = (x : ↥H) := by
        have hcommzx : (x : ↥H) * z = z * (x : ↥H) :=
          (Subgroup.mem_center_iff.mp hz) (x : ↥H)
        calc z⁻¹ * (x : ↥H) * z = z⁻¹ * ((x : ↥H) * z) := by group
          _ = z⁻¹ * (z * (x : ↥H)) := by rw [hcommzx]
          _ = (x : ↥H) := by group
      have hfixH : (MulAut.conjNormal e) y * (x : ↥H) * ((MulAut.conjNormal e) y)⁻¹ =
          y * (x : ↥H) * y⁻¹ := by
        rw [hcy]
        calc (y * z⁻¹) * (x : ↥H) * (y * z⁻¹)⁻¹
            = y * (z⁻¹ * (x : ↥H) * z) * y⁻¹ := by group
          _ = y * (x : ↥H) * y⁻¹ := by rw [hzx]
      have hxconj : e * (x : Γ) * e⁻¹ = (x : Γ) := by
        calc e * (x : Γ) * e⁻¹ = (x : Γ) * e * e⁻¹ := by rw [hxy]
          _ = (x : Γ) := by group
      have hfixG : e * ((y : Γ) * (x : Γ) * (y : Γ)⁻¹) * e⁻¹ =
          (y : Γ) * (x : Γ) * (y : Γ)⁻¹ := by
        have h := congrArg (fun t : ↥H => (t : Γ)) hfixH
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h
        calc e * ((y : Γ) * (x : Γ) * (y : Γ)⁻¹) * e⁻¹
            = (e * (y : Γ) * e⁻¹) * (e * (x : Γ) * e⁻¹) *
                (e * (y : Γ) * e⁻¹)⁻¹ := by group
          _ = (e * (y : Γ) * e⁻¹) * (x : Γ) * (e * (y : Γ) * e⁻¹)⁻¹ := by rw [hxconj]
          _ = (y : Γ) * (x : Γ) * (y : Γ)⁻¹ := by simpa only [mul_assoc] using h
      calc e * ((y : Γ) * (x : Γ) * (y : Γ)⁻¹)
            = (e * ((y : Γ) * (x : Γ) * (y : Γ)⁻¹) * e⁻¹) * e := by group
        _ = ((y : Γ) * (x : Γ) * (y : Γ)⁻¹) * e := by rw [hfixG]
  have hmem : (y * x * y⁻¹ : ↥H) ∈
      (H ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr hconjX
  have hmap : (QuotientGroup.mk' (Subgroup.center ↥H)) (y * x * y⁻¹) ∈
      zBar H (H ⊓ Subgroup.centralizer (E : Set Γ)) :=
    Subgroup.mem_map_of_mem _ hmem
  simpa [map_mul, map_inv] using hmap

theorem isSubnormal_zBar_centFix {H E J : Subgroup Γ} [H.Normal]
    (hJ : IsSubnormal J (H ⊓ Subgroup.centralizer (E : Set Γ))) :
    IsSubnormal (zBar H J) (I142.centFix (E.map (conjQ H))) := by
  have h1 : IsSubnormal (zBar H J)
      (zBar H (H ⊓ Subgroup.centralizer (E : Set Γ))) := by
    have h := (hJ.comap H.subtype).map (QuotientGroup.mk' (Subgroup.center ↥H))
    simpa [zBar, Subgroup.comap_subtype] using h
  have h2 : IsSubnormal (zBar H (H ⊓ Subgroup.centralizer (E : Set Γ)))
      (I142.centFix (E.map (conjQ H))) :=
    IsSubnormal.step (zBar_inf_centralizer_le_centFix (H := H) (E := E))
      (zBar_inf_centralizer_normal (H := H) (E := E)) (IsSubnormal.refl _)
  exact h1.trans h2

theorem zBar_perfect {H J : Subgroup Γ} (hJH : J ≤ H) (hperf : ⁅J, J⁆ = J) :
    ⁅zBar H J, zBar H J⁆ = zBar H J := by
  change ⁅(J.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H)),
      (J.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H))⁆ =
    (J.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H))
  rw [← Subgroup.map_commutator]
  have hcomm : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH, hperf]
  rw [hcomm]

theorem zBar_normal {H Q J : Subgroup Γ} (hQJ : Q ≤ J) (hJH : J ≤ H)
    (hQn : (Q.subgroupOf J).Normal) : ((zBar H Q).subgroupOf (zBar H J)).Normal := by
  have hle : zBar H Q ≤ zBar H J := zBar_mono hQJ
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h g hh hg
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hh
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hg
  have hqQ : (q : Γ) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have hjJ : (j : Γ) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hconj : (j : Γ) * (q : Γ) * (j : Γ)⁻¹ ∈ Q :=
    (Subgroup.normal_subgroupOf_iff hQJ).mp hQn (q : Γ) (j : Γ) hqQ hjJ
  have hmem : (j * q * j⁻¹ : ↥H) ∈ Q.subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr hconj
  have hmap : (QuotientGroup.mk' (Subgroup.center ↥H)) (j * q * j⁻¹) ∈ zBar H Q :=
    Subgroup.mem_map_of_mem _ hmem
  simpa [map_mul, map_inv] using hmap

theorem zBar_res [Finite Γ] {p : ℕ} {H J : Subgroup Γ} (hJH : J ≤ H)
    (hres : ∀ N : Subgroup Γ, N ≤ J → (N.subgroupOf J).Normal → Nat.Coprime p (N.relIndex J) →
      N = J) :
    ∀ N : Subgroup (↥H ⧸ Subgroup.center ↥H), N ≤ zBar H J →
      (N.subgroupOf (zBar H J)).Normal →
      Nat.Coprime p (N.relIndex (zBar H J)) → N = zBar H J := by
  intro N hNle hNn hNcop
  let Z : Subgroup ↥H := Subgroup.center ↥H
  let q : ↥H →* ↥H ⧸ Z := QuotientGroup.mk' Z
  let jHom : ↥J →* ↥H ⧸ Z := q.comp (Subgroup.inclusion hJH)
  have hRange : jHom.range = zBar H J := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let jz : ↥J →* ↥(zBar H J) :=
    jHom.codRestrict (zBar H J) fun x => by
      rw [← hRange]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hN₀eq : N.comap jHom = (N.subgroupOf (zBar H J)).comap jz := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    simp [jz]
  have hN₀normal : (N.comap jHom).Normal := by
    rw [hN₀eq]
    exact Subgroup.Normal.comap hNn jz
  have hN'normal : (((N.comap jHom).map J.subtype).subgroupOf J).Normal := by
    change (Subgroup.comap J.subtype ((N.comap jHom).map J.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
    exact hN₀normal
  have hN'le : (N.comap jHom).map J.subtype ≤ J := Subgroup.map_subtype_le _
  have hN'rel₀ : ((N.comap jHom).map J.subtype).relIndex J = (N.comap jHom).index := by
    have h := Subgroup.relIndex_map_map_of_injective (f := J.subtype) (N.comap jHom) ⊤
      J.subtype_injective
    simpa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] using h
  have hN₀index : (N.comap jHom).index = N.relIndex (zBar H J) := by
    rw [Subgroup.index_comap, hRange]
  have hN'rel : ((N.comap jHom).map J.subtype).relIndex J = N.relIndex (zBar H J) := by
    rw [hN'rel₀, hN₀index]
  have hcop' : Nat.Coprime p (((N.comap jHom).map J.subtype).relIndex J) := by
    rw [hN'rel]
    exact hNcop
  have hEqJ : (N.comap jHom).map J.subtype = J :=
    hres _ hN'le hN'normal hcop'
  have hN₀top : N.comap jHom = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [hEqJ, Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm hNle ?_
  intro y hy
  have hy' : y ∈ jHom.range := by rwa [hRange]
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy'
  have hx : x ∈ N.comap jHom := by
    rw [hN₀top]
    exact Subgroup.mem_top x
  exact Subgroup.mem_comap.mp hx

theorem card_zBar [Finite Γ] {p : ℕ} {H Q : Subgroup Γ} (hQH : Q ≤ H)
    (hO : GLAPPrimeCoreOf p H = ⊥) (hQ : Nat.Coprime p (Nat.card Q)) :
    Nat.card (zBar H Q) = Nat.card Q := by
  let Z : Subgroup ↥H := Subgroup.center ↥H
  let q : ↥H →* ↥H ⧸ Z := QuotientGroup.mk' Z
  let QH : Subgroup ↥H := Q.subgroupOf H
  let C : Subgroup ↥H := QH ⊓ Z
  have hCnormal : C.Normal := Subgroup.normal_of_le_center inf_le_right
  have hQHcard : Nat.card QH = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hCcard : Nat.Coprime p (Nat.card C) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hQ
    calc Nat.card C ∣ Nat.card QH := Subgroup.card_dvd_of_le inf_le_left
      _ = Nat.card Q := hQHcard
  have hCcore : C ≤ CFSG.pPrimeCore p ↥H := le_sSup ⟨hCnormal, hCcard⟩
  have hCorebot : CFSG.pPrimeCore p ↥H = ⊥ := by
    have hmap : (CFSG.pPrimeCore p ↥H).map H.subtype = ⊥ := by
      simpa [GLAPPrimeCoreOf, GLAPPrimeCore] using hO
    exact (Subgroup.map_eq_bot_iff_of_injective (f := H.subtype)
      (H := CFSG.pPrimeCore p ↥H) H.subtype_injective).mp hmap
  have hCbot : C = ⊥ := le_bot_iff.mp (hCcore.trans (le_of_eq hCorebot))
  have hinj : Function.Injective fun x : ↥QH => q (x : ↥H) := by
    intro x y hxy
    have hmemZ : ((x : ↥H)⁻¹ * (y : ↥H)) ∈ Z :=
      (QuotientGroup.eq (s := Z)).mp hxy
    have hmemQH : ((x : ↥H)⁻¹ * (y : ↥H)) ∈ QH :=
      QH.mul_mem (QH.inv_mem x.2) y.2
    have hbot : ((x : ↥H)⁻¹ * (y : ↥H)) ∈ (⊥ : Subgroup ↥H) := by
      rw [← hCbot]
      exact Subgroup.mem_inf.mpr ⟨hmemQH, hmemZ⟩
    have hone : (x : ↥H)⁻¹ * (y : ↥H) = 1 := by simpa using hbot
    have hyx : (y : ↥H) = (x : ↥H) := by
      calc (y : ↥H) = (x : ↥H) * ((x : ↥H)⁻¹ * (y : ↥H)) := by group
        _ = (x : ↥H) * 1 := by rw [hone]
        _ = (x : ↥H) := by rw [mul_one]
    exact Subtype.ext hyx.symm
  have hcardmap : Nat.card (zBar H Q) = Nat.card QH := by
    have hmap_eq : (⊤ : Subgroup ↥QH).map (q.comp QH.subtype) = zBar H Q := by
      rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
      rfl
    have hcard := Subgroup.card_map_of_injective (K := ⊤) (f := q.comp QH.subtype) hinj
    rw [hmap_eq] at hcard
    rw [hcard]
    exact Nat.card_congr (Subgroup.topEquiv (G := ↥QH)).toEquiv
  calc Nat.card (zBar H Q) = Nat.card QH := hcardmap
    _ = Nat.card Q := hQHcard

theorem autCentralizer_eq_centFix {S : Type} [Group S] (R : Subgroup (MulAut S)) :
    CFSG.LieType.ChevTwo.autCentralizer R = I142.centFix R := by
  ext s
  rw [I142.mem_centFix]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.I141FPar

end
