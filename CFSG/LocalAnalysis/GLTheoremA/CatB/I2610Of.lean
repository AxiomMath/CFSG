module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Local
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCore
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_zpowers_eq_bot {H : Type} [Group H] [Finite H] {E : Subgroup H} {x : H} (hx3 : orderOf x = 3)
    (hxE : x ∉ E) : E ⊓ Subgroup.zpowers x = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro g ⟨hgE, hgx⟩
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hdvd : orderOf g ∣ 3 := by
    rw [← hx3]
    exact orderOf_dvd_of_mem_zpowers hgx
  have hord : orderOf g = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  apply hxE
  have hle : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hgx
  have hcard : Nat.card ↥(Subgroup.zpowers x) ≤ Nat.card ↥(Subgroup.zpowers g) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hx3]
  have heq : Subgroup.zpowers g = Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard
  have hxg : x ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.2 hgE) hxg

theorem psi_ne_one_of_pow {p : ℕ} (hp : p.Prime) {L : Subgroup G} {y : NL L} (hy : y ^ p = 1)
    (hy1 : y ≠ 1) : psi p L y ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hyN : y ∈ Np p L := (psi_eq_one_iff y).1 h
  have hord : orderOf y = p := orderOf_eq_prime hy hy1
  have hdvd : orderOf (⟨y, hyN⟩ : ↥(Np p L)) ∣ Nat.card ↥(Np p L) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_Np p L) hdvd

theorem isElemAbelian_Ev {p : ℕ} {L E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (Ev L E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact isElemAbelian_commute hE ((mem_Ev (L := L) (a : NL L)).1 a.2)
      ((mem_Ev (L := L) (b : NL L)).1 b.2)
  · apply Subtype.ext
    exact hE.2 _ ((mem_Ev (L := L) a).1 ha)

theorem Ev_map_subtype (L E : Subgroup G) (hE : E ≤ Subgroup.normalizer (L : Set G)) :
    (Ev L E).map (Subgroup.subtype (Subgroup.normalizer (L : Set G))) = E := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_Ev x).1 hx
  · intro hy
    exact ⟨⟨y, hE hy⟩, (mem_Ev _).2 hy, rfl⟩

theorem Ev_mono {L E F : Subgroup G} (h : E ≤ F) : Ev L E ≤ Ev L F := fun x hx =>
  (mem_Ev x).2 (h ((mem_Ev x).1 hx))

theorem isElemAbelian_map_hom {H K : Type} [Group H] [Group K] {p : ℕ} (f : H →* K) {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := (Subgroup.mem_map).1 a.2
    obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_map).1 b.2
    change (a : K) * (b : K) = (b : K) * (a : K)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
  · intro w hw
    obtain ⟨x, hx, hxw⟩ := (Subgroup.mem_map).1 hw
    rw [← hxw, ← map_pow, hE.2 x hx, map_one]

theorem Yv_map_subtype {L : Subgroup G} (E : Subgroup (NL L)) :
    (Lv L ⊓ Subgroup.centralizer (E : Set (NL L))).map
        (Subgroup.subtype (Subgroup.normalizer (L : Set G))) =
      L ⊓ Subgroup.centralizer
        (((E.map (Subgroup.subtype (Subgroup.normalizer (L : Set G)))) : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, hxC⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(mem_Lv x).1 hxL, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
    have h1 : e * x = x * e := Subgroup.mem_centralizer_iff.1 hxC e he
    exact congrArg (fun z : NL L => (z : G)) h1
  · rintro ⟨hyL, hyC⟩
    refine ⟨⟨y, L_le_normalizer L hyL⟩, ⟨(mem_Lv _).2 hyL, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro e he
    have h1 : (e : G) * y = y * (e : G) :=
      Subgroup.mem_centralizer_iff.1 hyC (e : G) (Subgroup.mem_map_of_mem _ he)
    apply Subtype.ext
    exact h1

theorem coprime_inf_ker_subtype (p : ℕ) [Fact p.Prime] (L : Subgroup G) (A : Subgroup (NL L)) :
    Nat.Coprime p (Nat.card ↥(A ⊓ (Subgroup.subtype (Subgroup.normalizer (L : Set G))).ker)) := by
  rw [(MonoidHom.ker_eq_bot_iff (Subgroup.subtype (Subgroup.normalizer (L : Set G)))).2
    (Subgroup.subtype_injective _), inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right _

theorem coprime_inf_ker_psi (p : ℕ) [Fact p.Prime] (L : Subgroup G) (A : Subgroup (NL L)) :
    Nat.Coprime p (Nat.card ↥(A ⊓ (psi p L).ker)) := by
  have h1 : (psi p L).ker = Np p L := QuotientGroup.ker_mk' _
  rw [h1]
  exact (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right)
    (coprime_card_Np p L).symm).symm

theorem exists_comp_of_layer_ne_bot {p : ℕ} {X : Subgroup G} (h : GLAPLayer p X ≠ ⊥) :
    ∃ J : Subgroup G, GLAPComponent p X J := by
  by_contra hno
  push Not at hno
  apply h
  have hempty : {J : Subgroup G | GLAPComponent p X J} = ∅ := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hno J
  show sSup {J : Subgroup G | GLAPComponent p X J} = ⊥
  rw [hempty, sSup_empty]

theorem layer_ne_bot_of_comp {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    GLAPLayer p X ≠ ⊥ := by
  intro hbot
  have hle : J ≤ GLAPLayer p X := le_sSup hJ
  rw [hbot, le_bot_iff] at hle
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  obtain ⟨a, b, hab⟩ := isQuasisimple_nontrivial hq
  apply hab
  subst hle
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  congr 1
  exact Subsingleton.elim x y

theorem layer_ne_bot_of_Gcomp {L : Subgroup G} (hp : Nat.Prime 3) {E : Subgroup (NL L)} (hEp : IsPGroup 3 E)
    {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ((E.map (Subgroup.subtype
      (Subgroup.normalizer (L : Set G))) : Subgroup G) : Set G)) J) :
    GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer ((E.map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L))) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  rw [← Yv_map_subtype E] at hJ
  obtain ⟨Jv, hJv, -⟩ := exists_glaPComponent_map_eq hp (Subgroup.subtype (Subgroup.normalizer (L : Set G)))
    (coprime_inf_ker_subtype 3 L _) hJ
  have hJK := glaPComponent_map hp (psi 3 L) (coprime_inf_ker_psi 3 L _) hJv
  rw [map_inf_centralizer_eq hp E hEp (coprime_card_Np 3 L)] at hJK
  exact layer_ne_bot_of_comp hp hJK

theorem inf_centralizer_K_eq_zpowers {L B : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hBx : B ⊓ centModSubgroup 3 L = Subgroup.zpowers x) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (E : Subgroup (NL L)) (hEB : E ≤ Ev L B) (hxE : (⟨x, hxN⟩ : NL L) ∈ E) :
    E.map (psi 3 L) ⊓ Subgroup.centralizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L)) =
      Subgroup.zpowers (psi 3 L ⟨x, hxN⟩) := by
  have hxB : x ∈ B ⊓ centModSubgroup 3 L := by
    rw [hBx]
    exact Subgroup.mem_zpowers x
  have hxC : (⟨x, hxN⟩ : NL L) ∈ Ev L B := (mem_Ev _).2 hxB.1
  apply le_antisymm
  · rintro w ⟨hwW, hwC⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hwW
    have heC : ((e : NL L) : G) ∈ centModSubgroup 3 L :=
      ⟨e.2, fun l hl => (psi_mem_centralizer_iff e).1 hwC l hl⟩
    have hmem : ((e : NL L) : G) ∈ B ⊓ centModSubgroup 3 L := ⟨(mem_Ev e).1 (hEB he), heC⟩
    rw [hBx] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk
  · intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hxcent : psi 3 L ⟨x, hxN⟩ ∈
        Subgroup.centralizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L)) :=
      (psi_mem_centralizer_iff _).2 (fun l hl => hxB.2.2 l hl)
    exact Subgroup.mem_inf.2 ⟨zpow_mem (Subgroup.mem_map_of_mem _ hxE) k,
      zpow_mem hxcent k⟩

theorem mem_normalizer_of_comm {N : Type} [Group N] {H : Subgroup N} {g : N}
    (hg : ∀ h ∈ H, g * h = h * g) : g ∈ Subgroup.normalizer (H : Set N) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by rw [hg h hh]; group
    rw [e]
    exact hh
  · intro hh
    have hc : g * (g * h * g⁻¹) = (g * h * g⁻¹) * g := hg _ hh
    have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [e]
    have e2 : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
      calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [hc.symm]
        _ = g * h * g⁻¹ := by group
    rw [e2]
    exact hh

theorem map_zpowers_eq {H N : Type} [Group H] [Group N] (f : H →* N) (z : H) :
    (Subgroup.zpowers z).map f = Subgroup.zpowers (f z) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← map_zpow]⟩
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Subgroup.mem_map.2 ⟨z ^ k, Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩, by rw [map_zpow]⟩

theorem inf_centralizer_sup_zpowers {Γ' : Type} [Group Γ'] (K A : Subgroup Γ') (z : Γ')
    (hz : ∀ k ∈ K, z * k = k * z) :
    K ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers z : Subgroup Γ') : Set Γ') =
      K ⊓ Subgroup.centralizer (A : Set Γ') := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgK, hgC⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hgK, Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_iff.1 hgC h (Subgroup.mem_sup_left hh)⟩
  · intro g hg
    obtain ⟨hgK, hgA⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hgK, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hzg : z * g = g * z := hz g hgK
    have hle : A ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({g} : Set Γ') := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact (Subgroup.mem_centralizer_iff.1 hgA a ha).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hzg.symm
    have := Subgroup.mem_centralizer_iff.1 (hle hh) g (Set.mem_singleton g)
    exact this.symm

theorem layer_mono {L : Subgroup G} (hLB : LBalanceAt (Gam 3 L) 3)
    (hK : CFSG.Open.IsKGroup ↥(Kgrp 3 L)) {E D : Subgroup (NL L)} (hDE : D ≤ E)
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 3) :
    GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer ((E.map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L))) ≤
      GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer ((D.map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop := coprime_card_Np 3 L
  refine glaPLayer_inf_centralizer_anti Nat.prime_three hLB hK (Subgroup.map_mono hDE) ?_ ?_ ?_
  · intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hf
    rw [← map_mul, ← map_mul, isElemAbelian_commute hEel (hDE hd) he]
  · exact IsPGroup.iff_card.2 ⟨3, by rw [card_map_psi Nat.prime_three E hEel hcop, hEcard]⟩
  · intro f _
    rw [Subgroup.normalizer_eq_top (Kgrp 3 L)]
    exact Subgroup.mem_top f

theorem comp_of_layer {Q : TauCeti.CFSGIndex → Prop} (hfact : FactShape Q) {L B : Subgroup G} {x : G}
    (hK_qs : CFSG.Open.IsQuasisimple ↥(Kgrp 3 L))
    (hK_cat : catalogIs (↥(Kgrp 3 L) ⧸ Subgroup.center ↥(Kgrp 3 L)) Q)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx : x ≠ 1)
    (hBx : B ⊓ centModSubgroup 3 L = Subgroup.zpowers x) (hB : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (E : Subgroup (NL L)) (hEB : E ≤ Ev L B) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 3)
    (hxE : (⟨x, hxN⟩ : NL L) ∈ E)
    (hlayer : GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer
      ((E.map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L))) ≠ ⊥) :
    ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer
        (((E.map (Subgroup.subtype (Subgroup.normalizer (L : Set G)))) : Subgroup G) : Set G)) J ∧
      ¬ catalogIs (PSimple 3 J) S9.isL2prime := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hcop := coprime_card_Np 3 L
  have hEp : IsPGroup 3 E := IsPGroup.iff_card.2 ⟨3, hEcard⟩
  have hxBC : x ∈ B ⊓ centModSubgroup 3 L := by
    rw [hBx]
    exact Subgroup.mem_zpowers x
  have hxB : x ∈ B := hxBC.1
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hpsi : psi 3 L ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : NL L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hx3)
    rw [this, map_one]
  have hpsi1 : psi 3 L ⟨x, hxN⟩ ≠ 1 := psi_ne_one_of_pow hp
    (show (⟨x, hxN⟩ : NL L) ^ 3 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hx3))
    (fun h => hx (congrArg Subtype.val h))
  have hW_el : IsElemAbelian 3 (E.map (psi 3 L)) := isElemAbelian_map_psi hEel
  have hW_card : Nat.card ↥(E.map (psi 3 L)) = 3 ^ 3 := by
    rw [card_map_psi hp E hEel hcop, hEcard]
  have hK_norm : Subgroup.normalizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L)) = ⊤ :=
    Subgroup.normalizer_eq_top _
  have hW_norm : E.map (psi 3 L) ≤ Subgroup.normalizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L)) := by
    rw [hK_norm]
    exact le_top
  have hker : Nat.card ↥((E.map (psi 3 L)) ⊓ Subgroup.centralizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L))) = 3 := by
    rw [inf_centralizer_K_eq_zpowers hxN hBx hBN E hEB hxE, Nat.card_zpowers,
      orderOf_eq_prime hpsi hpsi1]
  obtain ⟨J', hJ'⟩ := exists_comp_of_layer_ne_bot hlayer
  rw [← map_inf_centralizer_eq hp E hEp hcop] at hJ'
  obtain ⟨Jv, hJv, -⟩ := exists_glaPComponent_map_eq hp (psi 3 L) (coprime_inf_ker_psi 3 L _) hJ'
  have hJG := glaPComponent_map hp (Subgroup.subtype (Subgroup.normalizer (L : Set G)))
    (coprime_inf_ker_subtype 3 L (Lv L ⊓ Subgroup.centralizer (E : Set (NL L)))) hJv
  rw [Yv_map_subtype E] at hJG
  have hJK := glaPComponent_map hp (psi 3 L) (coprime_inf_ker_psi 3 L (Lv L ⊓ Subgroup.centralizer (E : Set (NL L)))) hJv
  rw [map_inf_centralizer_eq hp E hEp hcop] at hJK
  have hnot := hfact (Gam 3 L) (Kgrp 3 L) (E.map (psi 3 L)) hK_qs hK_cat hW_norm hW_el hW_card hker
    (Jv.map (psi 3 L)) hJK
  have e1 : PQuot 3 (Jv.map (Subgroup.subtype (Subgroup.normalizer (L : Set G)))) ≃* PQuot 3 Jv :=
    (lcEquiv hp (Subgroup.subtype (Subgroup.normalizer (L : Set G))) Jv
      (coprime_inf_ker_subtype 3 L Jv)).symm
  have e2 : PQuot 3 Jv ≃* PQuot 3 (Jv.map (psi 3 L)) :=
    lcEquiv hp (psi 3 L) Jv (coprime_inf_ker_psi 3 L Jv)
  have e_ps : PSimple 3 (Jv.map (Subgroup.subtype (Subgroup.normalizer (L : Set G)))) ≃*
      PSimple 3 (Jv.map (psi 3 L)) := quotCenterCongr (e1.trans e2)
  exact ⟨Jv.map (Subgroup.subtype (Subgroup.normalizer (L : Set G))), hJG,
    fun h => hnot (catalogIs_of_mulEquiv e_ps h)⟩

theorem exists_D {H : Type} [Group H] [Finite H] {E₀ : Subgroup H}
    (hcard : Nat.card ↥E₀ = 3 ^ 3) : ∃ D : Subgroup H, D ≤ E₀ ∧ Nat.card ↥D = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₀) 3 (n := 2)
    ⟨3, by rw [hcard]; ring⟩
  refine ⟨K₀.map E₀.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK₀]

theorem core {Q : TauCeti.CFSGIndex → Prop} (hfact : FactShape Q)
    (hLB : ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y 3)
    {X L B : Subgroup G} {x : G} (hX : CFSG.Open.IsKGroup ↥X) (hL : GLAPComponent 3 X L)
    (hQ : catalogIs (PSimple 3 L) Q)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hx : x ≠ 1)
    (hBx : B ⊓ centModSubgroup 3 L = Subgroup.zpowers x) (hGB : IsGB 3 B L) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ B ⊓ centModSubgroup 3 L ≤ E ∧
      ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer (E : Set G)) J ∧
        ¬ catalogIs (PSimple 3 J) S9.isL2prime := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨E₀, hE₀B, hE₀el, hE₀card, hE₀N, hE₀layer⟩ := hGB
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer (E₀ : Set G)) J₀ := by
    by_contra hno
    push Not at hno
    apply hE₀layer
    have hempty : {J : Subgroup G | GLAPComponent 3 (L ⊓ Subgroup.centralizer (E₀ : Set G)) J} = ∅ := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hno J
    show sSup {J : Subgroup G | GLAPComponent 3 (L ⊓ Subgroup.centralizer (E₀ : Set G)) J} = ⊥
    rw [hempty, sSup_empty]
  have hK_qs : CFSG.Open.IsQuasisimple ↥(Kgrp 3 L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (pQuotEquivK 3 L)
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have hK_cat : catalogIs (↥(Kgrp 3 L) ⧸ Subgroup.center ↥(Kgrp 3 L)) Q :=
    catalogIs_of_mulEquiv (quotCenterCongr (pQuotEquivK 3 L)) hQ
  have hLk : CFSG.Open.IsKGroup ↥L :=
    hX.of_injective (Subgroup.inclusion hL.1) (Subgroup.inclusion_injective _)
  have hPQ : CFSG.Open.IsKGroup (↥L ⧸ GLAPPrimeCore 3 ↥L) := hLk.quotient (GLAPPrimeCore 3 ↥L)
  have hKk : CFSG.Open.IsKGroup ↥(Kgrp 3 L) :=
    hPQ.of_injective (pQuotEquivK 3 L).symm.toMonoidHom (pQuotEquivK 3 L).symm.injective
  have hxBC : x ∈ B ⊓ centModSubgroup 3 L := by
    rw [hBx]
    exact Subgroup.mem_zpowers x
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hxBC.2.1
  have hxB : x ∈ B := hxBC.1
  have hEv0el : IsElemAbelian 3 (Ev L E₀) := isElemAbelian_Ev hE₀el
  have hEv0card : Nat.card ↥(Ev L E₀) = 3 ^ 3 := by
    rw [← hE₀card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀N).toEquiv
  have hEv0ne : GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer
      (((Ev L E₀).map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L))) ≠ ⊥ := by
    apply layer_ne_bot_of_Gcomp hp (E := Ev L E₀) (IsPGroup.iff_card.2 ⟨3, hEv0card⟩)
    rw [Ev_map_subtype L E₀ hE₀N]
    exact hJ₀
  by_cases hxE : x ∈ E₀
  ·
    have hx'E : (⟨x, hxN⟩ : NL L) ∈ Ev L E₀ := (mem_Ev _).2 hxE
    obtain ⟨J, hJ, hJn⟩ := comp_of_layer hfact hK_qs hK_cat hxN hx hBx hB hBN (Ev L E₀)
      (Ev_mono hE₀B) hEv0el hEv0card hx'E hEv0ne
    rw [Ev_map_subtype L E₀ hE₀N] at hJ
    refine ⟨E₀, hE₀B, hE₀el, hE₀card, ?_, J, hJ, hJn⟩
    rw [hBx]
    exact Subgroup.zpowers_le.2 hxE
  ·
    obtain ⟨D, hDE₀, hDcard⟩ := exists_D hE₀card
    have hDN : D ≤ Subgroup.normalizer (L : Set G) := hDE₀.trans hE₀N
    have hDvB : Ev L D ≤ Ev L B := Ev_mono (hDE₀.trans hE₀B)
    have hDv_card : Nat.card ↥(Ev L D) = 3 ^ 2 := by
      rw [← hDcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
    have hx'B : (⟨x, hxN⟩ : NL L) ∈ Ev L B := (mem_Ev _).2 hxB
    have hx'ord : orderOf (⟨x, hxN⟩ : NL L) = 3 := by
      apply orderOf_eq_prime
      · exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hB.2 x hxB)
      · exact fun h => hx (congrArg Subtype.val h)
    have hx'notin : (⟨x, hxN⟩ : NL L) ∉ Ev L D := fun h => hxE (hDE₀ ((mem_Ev _).1 h))
    have hinf : Ev L D ⊓ Subgroup.zpowers (⟨x, hxN⟩ : NL L) = ⊥ :=
      inf_zpowers_eq_bot hx'ord hx'notin
    have hcomm : ∀ h ∈ Ev L B, (⟨x, hxN⟩ : NL L) * h = h * (⟨x, hxN⟩ : NL L) := fun h hh =>
      isElemAbelian_commute (isElemAbelian_Ev hB) hx'B hh
    have hnorm : Subgroup.zpowers (⟨x, hxN⟩ : NL L) ≤ Subgroup.normalizer (Ev L D : Set (NL L)) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_comm fun h hh => hcomm h (hDvB hh)
    have hcard_sup : Nat.card ↥(Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)) = 3 ^ 3 := by
      have key := card_sup_mul_card_inf_of_le_normalizer hnorm
      rw [hinf, Subgroup.card_bot, hDv_card, Nat.card_zpowers, hx'ord] at key
      norm_num at key
      omega
    have hE_le : Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L) ≤ Ev L B :=
      sup_le hDvB (Subgroup.zpowers_le.2 hx'B)
    have hE_el : IsElemAbelian 3 (Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)) :=
      isElemAbelian_mono (isElemAbelian_Ev hB) hE_le
    have hxE' : (⟨x, hxN⟩ : NL L) ∈ Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hxcent : psi 3 L ⟨x, hxN⟩ ∈
        Subgroup.centralizer ((Kgrp 3 L : Subgroup (Gam 3 L)) : Set (Gam 3 L)) :=
      (psi_mem_centralizer_iff _).2 (fun l hl => hxBC.2.2 l hl)
    have hz : ∀ k ∈ Kgrp 3 L, psi 3 L ⟨x, hxN⟩ * k = k * psi 3 L ⟨x, hxN⟩ := fun k hk =>
      (Subgroup.mem_centralizer_iff.1 hxcent k hk).symm
    have hmap_sup : (Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)).map (psi 3 L) =
        (Ev L D).map (psi 3 L) ⊔ Subgroup.zpowers (psi 3 L ⟨x, hxN⟩) := by
      rw [Subgroup.map_sup, map_zpowers_eq]
    have hcent_eq : Kgrp 3 L ⊓ Subgroup.centralizer
        ((((Ev L D).map (psi 3 L)) ⊔ Subgroup.zpowers (psi 3 L ⟨x, hxN⟩) : Subgroup (Gam 3 L)) :
          Set (Gam 3 L)) =
        Kgrp 3 L ⊓ Subgroup.centralizer (((Ev L D).map (psi 3 L) : Subgroup (Gam 3 L)) : Set (Gam 3 L)) :=
      inf_centralizer_sup_zpowers _ _ _ hz
    have hmono := layer_mono (hLB (Gam 3 L)) hKk (E := Ev L E₀) (D := Ev L D) (Ev_mono hDE₀)
      hEv0el hEv0card
    have hlayerE : GLAPLayer 3 (Kgrp 3 L ⊓ Subgroup.centralizer
        (((Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)).map (psi 3 L) : Subgroup (Gam 3 L)) :
          Set (Gam 3 L))) ≠ ⊥ := by
      rw [hmap_sup, hcent_eq]
      intro hbot
      apply hEv0ne
      apply le_bot_iff.1
      rw [← hbot]
      exact hmono
    obtain ⟨J, hJ, hJn⟩ := comp_of_layer hfact hK_qs hK_cat hxN hx hBx hB hBN
      (Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)) hE_le hE_el hcard_sup hxE' hlayerE
    refine ⟨(Ev L D ⊔ Subgroup.zpowers (⟨x, hxN⟩ : NL L)).map
      (Subgroup.subtype (Subgroup.normalizer (L : Set G))), ?_, ?_, ?_, ?_, J, hJ, hJn⟩
    · exact (Subgroup.map_mono hE_le).trans (Ev_map_subtype L B hBN).le
    · exact isElemAbelian_map_hom _ hE_el
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact hcard_sup
    · rw [hBx]
      exact Subgroup.zpowers_le.2 (Subgroup.mem_map_of_mem _ hxE')

theorem i2610_of_facts {G : Type} [Group G] [Finite G] (hU : I2610FactU6) (hF : I2610FactF4)
    (hT : I2610FactTE6) (hLB : ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y 3) :
    CFSG.LocalAnalysis.GLTheoremA.I2610At G := by
  unfold CFSG.LocalAnalysis.GLTheoremA.I2610At
  intro X L B x hX hL hcat hB hBN hx hBx hGB
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h | h | h
  · exact core (Q := isU6two) hU hLB hX hL ⟨i, h, ⟨e⟩⟩ hB hBN hx hBx hGB
  · exact core (Q := isF4two) hF hLB hX hL ⟨i, h, ⟨e⟩⟩ hB hBN hx hBx hGB
  · exact core (Q := isTE6two) hT hLB hX hL ⟨i, h, ⟨e⟩⟩ hB hBN hx hBx hGB

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end

