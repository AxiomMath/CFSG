module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Lemma1314b

@[expose] def NotPCentralBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → ¬ IsPCentralIn p M d

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem mem_centerOf_iff_aux (H : Subgroup G) (z : G) :
    z ∈ centerOf H ↔ z ∈ H ∧ ∀ h ∈ H, h * z = z * h := by
  unfold centerOf
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨x.2, fun h hh => ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨h, hh⟩)
    simpa using this
  · rintro ⟨hz, hcomm⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 g.2)

theorem centerOf_le_aux (H : Subgroup G) : centerOf H ≤ H := Subgroup.map_subtype_le _

theorem exists_isSylowIn_above {p : ℕ} {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup p ↥P) :
    ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem isPGroup_gLBConj {p : ℕ} {H : Subgroup G} (hH : IsPGroup p ↥H) (g : G) :
    IsPGroup p ↥(GLBConj g H) :=
  hH.map (MulAut.conj g⁻¹).toMonoidHom

theorem isSylowIn_gLBConj {p : ℕ} {X R : Subgroup G} (hR : IsSylowIn p X R) {x : G} (hx : x ∈ X) :
    IsSylowIn p X (GLBConj x R) := by
  have hXX : ∀ y ∈ X, GLBConj y X = X := fun y hy =>
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)
  refine ⟨?_, isPGroup_gLBConj hR.2.1 x, fun T hTX hTp hle => ?_⟩
  · calc GLBConj x R ≤ GLBConj x X := gLBConj_mono x hR.1
      _ = X := hXX x hx
  · have h1 : R ≤ GLBConj x⁻¹ T := by
      have h := gLBConj_mono x⁻¹ hle
      rwa [gLBConj_inv_gLBConj] at h
    have hT' : GLBConj x⁻¹ T ≤ X := by
      calc GLBConj x⁻¹ T ≤ GLBConj x⁻¹ X := gLBConj_mono _ hTX
        _ = X := hXX _ (X.inv_mem hx)
    have h2 : GLBConj x⁻¹ T = R := hR.2.2 _ hT' (isPGroup_gLBConj hTp x⁻¹) h1
    rw [← h2, gLBConj_gLBConj_inv]

theorem exists_gLBConj_eq {p : ℕ} [Fact p.Prime] {X R P : Subgroup G} (hR : IsSylowIn p X R)
    (hP : IsSylowIn p X P) : ∃ x ∈ X, GLBConj x R = P := by
  obtain ⟨x, hx, S, hSp, hSX, hPS, hRS⟩ :=
    exists_conj_le_pGroup' (p := p) (K := X) (X := P) (Y := R) hP.1 hP.2.1 hR.1 hR.2.1
  have hSP : S = P := hP.2.2 S hSX hSp hPS
  exact ⟨x, hx, ((isSylowIn_gLBConj hR hx).2.2 P hP.1 hP.2.1 (hRS.trans hSP.le)).symm⟩

theorem gLBConj_centerOf_le (x : G) (R : Subgroup G) :
    GLBConj x (centerOf R) ≤ centerOf (GLBConj x R) := by
  intro u hu
  rw [mem_gLBConj] at hu
  obtain ⟨huR, hcomm⟩ := (mem_centerOf_iff_aux R _).1 hu
  rw [mem_centerOf_iff_aux]
  refine ⟨mem_gLBConj.2 huR, fun s hs => ?_⟩
  have hsR : x * s * x⁻¹ ∈ R := mem_gLBConj.1 hs
  have h := hcomm _ hsR
  calc s * u = x⁻¹ * ((x * s * x⁻¹) * (x * u * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * u * x⁻¹) * (x * s * x⁻¹)) * x := by rw [h]
    _ = u * s := by group

theorem mem_centralizer_zpowers_aux {x y : G} (h : x * y = y * x) :
    y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 (fun k hk => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact (show Commute x y from h).zpow_left n

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

theorem ii_core {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (hA3 : CFSG.Open.pRank p A ≤ 3)
    (hU : ∃ U : Subgroup G, U ≤ centerOf R ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2)
    (hNPC : ¬ IsPCentralIn p M d) :
    ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1 := by
  rintro ⟨A1, hA1, hdA1⟩
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hAp : inDp p M A := h.pair.1.2.1
  have hAsc : IsSCp p M A := hAp.1.1
  have hAM : A ≤ M := hAsc.1
  have hAel : IsElemAbelian p A := hAsc.2.1
  have hAmax : ∀ F : Subgroup G, F ≤ M → IsElemAbelian p F → A ≤ F → F = A := hAsc.2.2
  have hdA : d ∈ A := h.hD.1 h.hd.1
  have hdp : d ^ p = 1 := hAel.2 d hdA
  set C : Subgroup G := M ⊓ Cg d with hCdef
  have hCM : C ≤ M := inf_le_left
  have hmemC : ∀ {x : G}, x ∈ C ↔ x ∈ M ∧ x * d = d * x := by
    intro x
    rw [hCdef, Subgroup.mem_inf, Cg, Subgroup.mem_centralizer_singleton_iff]
  have hAC : A ≤ C := fun a ha => hmemC.2 ⟨hAM ha, (elemAbelian_comm hAel hdA ha).symm⟩
  have hAp' : IsPGroup p ↥A := isPGroup_of_isElemAbelian' hAel
  obtain ⟨Pd, hPd, hAPd⟩ := exists_isSylowIn_above hAC hAp'
  obtain ⟨P, hP, hPdP⟩ := exists_isSylowIn_above (hPd.1.trans hCM) hPd.2.1
  have hdPd : d ∈ Pd := hAPd hdA
  have hdP : d ∈ P := hPdP hdPd
  have hZP_Pd : centerOf P ≤ Pd := by
    have hZC : centerOf P ≤ C := by
      intro z hz
      obtain ⟨hzP, hzc⟩ := (mem_centerOf_iff_aux P z).1 hz
      exact hmemC.2 ⟨hP.1 hzP, (hzc d hdP).symm⟩
    have hsupC : Pd ⊔ centerOf P ≤ C := sup_le hPd.1 hZC
    have hsupP : IsPGroup p ↥(Pd ⊔ centerOf P) :=
      hP.2.1.to_le (sup_le hPdP (centerOf_le_aux P))
    have heq := hPd.2.2 (Pd ⊔ centerOf P) hsupC hsupP le_sup_left
    exact le_sup_right.trans heq.le
  have hZP_Z : centerOf P ≤ centerOf Pd := by
    intro z hz
    refine (mem_centerOf_iff_aux Pd z).2 ⟨hZP_Pd hz, fun y hy => ?_⟩
    exact ((mem_centerOf_iff_aux P z).1 hz).2 y (hPdP hy)
  have hdZd : d ∈ centerOf Pd := by
    refine (mem_centerOf_iff_aux Pd d).2 ⟨hdPd, fun y hy => ?_⟩
    exact (hmemC.1 (hPd.1 hy)).2
  have hnotZ : d ∉ centerOf P := fun hdZ => hNPC ⟨P, hP, hdZ⟩
  obtain ⟨U, hUZ, hUel, hUcard⟩ := hU
  obtain ⟨x, -, hxR⟩ := exists_gLBConj_eq h.hR.1 hP
  have hU'Z : GLBConj x U ≤ centerOf P := by
    rw [← hxR]
    exact (gLBConj_mono x hUZ).trans (gLBConj_centerOf_le x R)
  have hU'el : IsElemAbelian p (GLBConj x U) := CFSG.SectionRank.isElemAbelian_map hUel _
  have hU'card : Nat.card (GLBConj x U) = p ^ 2 := by
    rw [GLBConj, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hUcard]
  have hU'Zd : GLBConj x U ≤ centerOf Pd := hU'Z.trans hZP_Z
  have hdU' : d ∉ GLBConj x U := fun hd => hnotZ (hU'Z hd)
  have hcommUd : ∀ u ∈ GLBConj x U, u * d = d * u := fun u hu =>
    (((mem_centerOf_iff_aux P u).1 (hU'Z hu)).2 d hdP).symm
  have hdel : IsElemAbelian p (Subgroup.zpowers d) :=
    isElemAbelian_mono hAel (Subgroup.zpowers_le.2 hdA)
  have hU'cent : GLBConj x U ≤ Subgroup.centralizer (Subgroup.zpowers d : Set G) := fun u hu =>
    mem_centralizer_zpowers_aux (hcommUd u hu).symm
  have hVel : IsElemAbelian p (GLBConj x U ⊔ Subgroup.zpowers d) :=
    isElemAbelian_sup_of_commute hU'el hdel hU'cent
  have hVcard : Nat.card ↥(GLBConj x U ⊔ Subgroup.zpowers d) = p ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (GLBConj x U) hdp hdU' hcommUd,
      hU'card]
    ring
  have hVZ : GLBConj x U ⊔ Subgroup.zpowers d ≤ centerOf Pd :=
    sup_le hU'Zd (Subgroup.zpowers_le.2 hdZd)
  have hVM : GLBConj x U ⊔ Subgroup.zpowers d ≤ M :=
    (hVZ.trans (centerOf_le_aux Pd)).trans (hPd.1.trans hCM)
  have hAV : A ≤ Subgroup.centralizer ((GLBConj x U ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (((mem_centerOf_iff_aux Pd v).1 (hVZ hv)).2 a (hAPd ha)).symm
  have hAsup : IsElemAbelian p (A ⊔ (GLBConj x U ⊔ Subgroup.zpowers d)) :=
    isElemAbelian_sup_of_commute hAel hVel hAV
  have hAeq : A ⊔ (GLBConj x U ⊔ Subgroup.zpowers d) = A :=
    hAmax _ (sup_le hAM hVM) hAsup le_sup_left
  have hVA : GLBConj x U ⊔ Subgroup.zpowers d ≤ A := le_sup_right.trans hAeq.le
  obtain ⟨k, hk⟩ := exists_card_eq_pow hAp'
  have hk3 : k ≤ 3 := (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hAel hk).trans hA3
  have hAcard : Nat.card A ≤ p ^ 3 := by
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk3
  have hVAeq : GLBConj x U ⊔ Subgroup.zpowers d = A :=
    Subgroup.eq_of_le_of_card_ge hVA (by rw [hVcard]; exact hAcard)
  have hAZ : A ≤ centerOf Pd := by
    rw [← hVAeq]
    exact hVZ
  have hA1sc : IsSCp p M A1 := hA1.1.1
  have hA1M : A1 ≤ M := hA1sc.1
  have hA1el : IsElemAbelian p A1 := hA1sc.2.1
  have hA1C : A1 ≤ C := fun a ha => hmemC.2 ⟨hA1M ha, (elemAbelian_comm hA1el hdA1 ha).symm⟩
  obtain ⟨y, hyC, S, hSp, hSC, hPdS, hA1S⟩ :=
    exists_conj_le_pGroup' (p := p) (K := C) (X := Pd) (Y := A1) hPd.1 hPd.2.1 hA1C
      (isPGroup_of_isElemAbelian' hA1el)
  have hSPd : S = Pd := hPd.2.2 S hSC hSp hPdS
  have hA1Pd : GLBConj y A1 ≤ Pd := hA1S.trans hSPd.le
  have hyM : y ∈ M := hCM hyC
  have hA1' : inD p M (GLBConj y A1) :=
    (lemma101_i_holds h.toSec13.toSec11.toSec10Fails hyM hA1 hAp).1
  have hA1'sc : IsSCp p M (GLBConj y A1) := hA1'.1.1
  have hA1'el : IsElemAbelian p (GLBConj y A1) := hA1'sc.2.1
  have hAcent : A ≤ Subgroup.centralizer ((GLBConj y A1 : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((mem_centerOf_iff_aux Pd a).1 (hAZ ha)).2 v (hA1Pd hv)
  have hAsup' : IsElemAbelian p (A ⊔ GLBConj y A1) :=
    isElemAbelian_sup_of_commute hAel hA1'el hAcent
  have hAeq' : A ⊔ GLBConj y A1 = A := hAmax _ (sup_le hAM hA1'sc.1) hAsup' le_sup_left
  have hA1'A : GLBConj y A1 ≤ A := le_sup_right.trans hAeq'.le
  have hAeq'' : A = GLBConj y A1 := hA1'sc.2.2 A hAM hAel hA1'A
  apply hAp.2
  rw [hAeq'']
  exact hA1'.2

theorem ii_of_iv {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hA3 : CFSG.Open.pRank p A = 3) (hL1312 : Lemma1312Statement) (hNPC : NotPCentralBlock) :
    ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1 := by
  obtain ⟨U, hU, hUR⟩ := hL1312 h
  exact ii_core h hA3.le ⟨U, hUR h139a, hU.1.2.1, hU.1.2.2⟩ (hNPC h h139a)

end Main

end Lemma1314b

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
