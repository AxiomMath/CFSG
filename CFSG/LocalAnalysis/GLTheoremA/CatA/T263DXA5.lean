module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXGlue
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.HardMathSupport.Timmesfeld.Proving.ComponentCentralizer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GRed
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem isSubnormal_iSup_of_forall {X : Subgroup Ω} {ι : Type*} (L : ι → Subgroup Ω)
    (hL : ∀ i, L i ≤ X ∧ IsSubnormal (L i) X) : IsSubnormal (⨆ i, L i) X := by
  have hle : (⨆ i, L i) ≤ X := iSup_le fun i => (hL i).1
  rw [CFSG.Open.IsSubnormal.iff_subgroupOf hle]
  have h1 : ∀ A ∈ Set.range fun i => (L i).subgroupOf X, A.IsSubnormal := by
    rintro _ ⟨i, rfl⟩
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf (hL i).1).1 (hL i).2
  have h2 := (CFSG.GroupTheory.subnormal_subgroups_generated_join _ h1).1
  have h3 : Subgroup.closure (⋃ A ∈ Set.range fun i => (L i).subgroupOf X, (A : Set ↥X)) =
      ⨆ i, (L i).subgroupOf X := by
    rw [Set.biUnion_range, ← Subgroup.iSup_eq_closure]
  rw [h3] at h2
  have h4 : (⨆ i, L i).subgroupOf X = ⨆ i, (L i).subgroupOf X := by
    refine le_antisymm ?_ (iSup_le fun i => Subgroup.comap_mono (le_iSup L i))
    have h5 : (⨆ i, L i) ≤ (⨆ i, (L i).subgroupOf X).map X.subtype := by
      refine iSup_le fun i => ?_
      rw [← Subgroup.map_subgroupOf_eq_of_le (hL i).1]
      exact Subgroup.map_mono (le_iSup (fun i => (L i).subgroupOf X) i)
    have h6 := Subgroup.comap_mono (f := X.subtype) h5
    rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at h6
  rwa [h4]

theorem exists_norm_isComponentOf {p : ℕ} (hp : p.Prime) {X J : Subgroup Ω} {e : Ω}
    (hJ : IsComponentOf J X) (hepow : e ^ p = 1) (heX : e ∈ Subgroup.normalizer (X : Set Ω))
    (heJ : e ∉ Subgroup.normalizer (J : Set Ω)) :
    ∃ Δ : Subgroup Ω, IsComponentOf Δ (X ⊓ Subgroup.centralizer ({e} : Set Ω)) ∧
      Nonempty (↥Δ ⧸ Subgroup.center ↥Δ ≃* ↥J ⧸ Subgroup.center ↥J) := by
  let c : ℤ → Subgroup Ω := fun i => J.map (MulAut.conj (e ^ i)).toMonoidHom
  have hci : ∀ i, IsComponentOf (c i) X := fun i =>
    isComponentOf_map_conj_of_mem_normalizer hJ ((Subgroup.normalizer (X : Set Ω)).zpow_mem heX i)
  have hc0 : c 0 = J := by
    ext x
    simp [c, Subgroup.mem_map]
  have hcN : ∀ i, c i ≤ Subgroup.normalizer (J : Set Ω) := by
    intro i
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (hci i) hJ with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (h x hx j hj).symm
  have hconj : ∀ i : ℤ, (c i).map (MulAut.conj e).toMonoidHom = c (i + 1) := by
    intro i
    simp only [c, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [zpow_add_one]
    group
  set Y : Subgroup Ω := ⨆ i, c i with hY
  have hmap : Y.map (MulAut.conj e).toMonoidHom = Y := by
    rw [hY, Subgroup.map_iSup]
    refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
    · rw [hconj]
      exact le_iSup c (i + 1)
    · have h1 : c i = (c (i - 1)).map (MulAut.conj e).toMonoidHom := by
        rw [hconj, sub_add_cancel]
      rw [h1]
      exact le_iSup (fun i => (c i).map (MulAut.conj e).toMonoidHom) (i - 1)
  have hYX : Y ≤ X := iSup_le fun i => (hci i).1
  have hYN : Y ≤ Subgroup.normalizer (J : Set Ω) := iSup_le hcN
  have hYsub : IsSubnormal Y X := isSubnormal_iSup_of_forall c fun i => ⟨(hci i).1, (hci i).2.1⟩
  have heY : e ∈ Subgroup.normalizer (Y : Set Ω) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hJle : J ≤ Y := calc J = c 0 := hc0.symm
    _ ≤ Y := le_iSup c 0
  have hJY : IsComponentOf J Y :=
    ⟨hJle, IsSubnormal.step hJle ((Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 hYN)
      (IsSubnormal.refl Y), hJ.2.2⟩
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ := exists_norm hp hJY hepow heY heJ
  have hNe : ∀ j : J, Commute e (N j) := fun j => (mul_inv_eq_iff_eq_mul.mp (hN2 j))
  have hker : N.rangeRestrict.ker ≤ Subgroup.center J := fun j hj => by
    rw [MonoidHom.ker_rangeRestrict] at hj
    exact Subgroup.mem_center_iff.mpr (hN4 j hj)
  obtain ⟨-, hquasi, ⟨hiso⟩⟩ := central_cover (native_of_open_dx hJ.2.2) N.rangeRestrict
    N.rangeRestrict_surjective hker
  have hΔY : N.range ≤ Y := by
    rintro _ ⟨j, rfl⟩
    exact hN1 j
  have hΔC : N.range ≤ Subgroup.centralizer ({e} : Set Ω) := by
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hNe j).eq.symm
  have hΔle : N.range ≤ Y ⊓ Subgroup.centralizer ({e} : Set Ω) := le_inf hΔY hΔC
  have hnorm : (N.range.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set Ω))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔle]
    rintro _ g ⟨j, rfl⟩ ⟨hgY, hge⟩
    have hge' : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hge
    have hg := Subgroup.mem_normalizer_iff.mp (hYN hgY) j
    exact ⟨⟨g * j * g⁻¹, hg.mp j.2⟩, (hN3 g hge' j _ rfl).symm⟩
  refine ⟨N.range, ⟨le_inf (hΔY.trans hYX) hΔC, ?_, open_of_native_dx hquasi⟩, ⟨hiso⟩⟩
  exact IsSubnormal.step hΔle hnorm (hYsub.inf _)

private theorem card_mulAut_of_card_sixty {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h60 : Nat.card Q = 60) : Nat.card (MulAut Q) = 120 := by
  obtain ⟨e⟩ :=
    CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr (Equiv.ofBijective _ hbij),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_le_three_mul_of_a5 {J B : Subgroup Ω} (hJq : CFSG.Open.IsQuasisimple ↥J)
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) (hB : IsElemAbelian 3 B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set Ω)) :
    Nat.card ↥B ≤ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Ω)) := by
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  set ρ := (CFSG.GH74.GLS.Stage2.Bender.Thm1.actCenterQuot J).comp (Subgroup.inclusion hBJ)
  have hker : ρ.ker ≤ (Subgroup.centralizer (J : Set Ω) ⊓ B).subgroupOf B := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_centralizer_iff.2 fun j hj => ?_, x.2⟩
    exact (CFSG.GH74.GLS.Stage2.Bender.Thm1.commute_of_actCenterQuot_eq_one J
      (Subgroup.inclusion hBJ x) (MonoidHom.mem_ker.1 hx) j hj).symm
  have hrel : (Subgroup.centralizer (J : Set Ω)).relIndex B ≤ Nat.card ρ.range := by
    rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv.symm]
    haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact Subgroup.index_antitone hker
  have hp3 : IsPGroup 3 ρ.range := by
    rintro ⟨y, x, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hx : x ^ 3 = 1 := Subtype.ext (hB.2 x x.2)
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hx, map_one]
  have hcard : Nat.card ρ.range ≤ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hp3.exists_card_eq
    have hdvd : Nat.card ρ.range ∣ 120 :=
      (card_mulAut_of_card_sixty h60) ▸ Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd ⊢
    rcases n with _ | _ | n
    · norm_num
    · norm_num
    · exfalso
      have h9 : 9 ∣ 120 := (pow_dvd_pow 3 (show 2 ≤ n + 2 by omega)).trans hdvd
      omega
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (J : Set Ω)) B
  rw [inf_comm] at h1
  calc Nat.card ↥B = (Subgroup.centralizer (J : Set Ω)).relIndex B *
        Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Ω)) := h1.symm
    _ ≤ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Ω)) :=
        Nat.mul_le_mul_right _ (hrel.trans hcard)

private theorem glaPLayer_ne_bot_of_a5 {X J : Subgroup Ω} (hJ : IsComponentOf J X)
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) : GLAPLayer 3 X ≠ ⊥ := by
  have hcomp : GLAPComponent 3 X J :=
    glaPComponent_of_isComponentOf_of_dvd Nat.prime_three hJ (by rw [h60]; norm_num)
  have hle : J ≤ GLAPLayer 3 X := le_sSup hcomp
  intro hbot
  rw [hbot, le_bot_iff] at hle
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  exact (Subgroup.nontrivial_iff_ne_bot J).1 this hle

private theorem exists_layer_of_extend {S B D J : Subgroup Ω} (hBel : IsElemAbelian 3 B)
    (hB : 3 ^ 4 ≤ Nat.card ↥B) (hDB : D ≤ B) (hD : Nat.card ↥D ∣ 3 ^ 3)
    (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer (D : Set Ω)))
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60)
    (hcase : Nat.card ↥D = 3 ^ 3 ∨ B ≤ Subgroup.normalizer (J : Set Ω)) :
    ∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 ∧
      GLAPLayer 3 (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
  have hJD : J ≤ Subgroup.centralizer (D : Set Ω) := fun x hx => (hJ.1 hx).2
  have hDJ : D ≤ Subgroup.centralizer (J : Set Ω) := Subgroup.le_centralizer_iff.1 hJD
  obtain ⟨E, hE27, hDE, hEBJ⟩ : ∃ E : Subgroup Ω, Nat.card ↥E = 3 ^ 3 ∧ D ≤ E ∧
      E ≤ B ⊓ Subgroup.centralizer (J : Set Ω) := by
    rcases hcase with h27 | hBJ
    · exact ⟨D, h27, le_rfl, le_inf hDB hDJ⟩
    · have hcard := card_le_three_mul_of_a5 hJ.2.2 h60 hBel hBJ
      obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three
        (isElemAbelian_mono hBel (inf_le_left : B ⊓ Subgroup.centralizer (J : Set Ω) ≤ B))
      have h3k : 3 ≤ k := by
        have h1 : 3 ^ 3 ≤ 3 ^ k := by
          rw [← hk]
          omega
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
      obtain ⟨E, h1, h2, h3⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hD
        (by rw [hk]; exact pow_dvd_pow 3 h3k) (le_inf hDB hDJ)
      exact ⟨E, h1, h2, h3⟩
  have hEB : E ≤ B := hEBJ.trans inf_le_left
  have hEJ : E ≤ Subgroup.centralizer (J : Set Ω) := hEBJ.trans inf_le_right
  refine ⟨E, hEB, isElemAbelian_mono hBel hEB, hE27, ?_⟩
  have hJE : J ≤ Subgroup.centralizer (E : Set Ω) := Subgroup.le_centralizer_iff.1 hEJ
  have hCED : Subgroup.centralizer (E : Set Ω) ≤ Subgroup.centralizer (D : Set Ω) :=
    Subgroup.centralizer_le hDE
  have hcomp : IsComponentOf J (S ⊓ Subgroup.centralizer (E : Set Ω)) := by
    have h := CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le hJ hJE
    rwa [inf_assoc, inf_eq_right.2 hCED] at h
  exact glaPLayer_ne_bot_of_a5 hcomp h60

open scoped Pointwise in
private theorem exists_larger_of_a5 {S B D J : Subgroup Ω} (hSn : S.Normal)
    (hBel : IsElemAbelian 3 B) (hDB : D ≤ B) (hD : Nat.card ↥D ∣ 3 ^ 3)
    (hD27 : Nat.card ↥D ≠ 3 ^ 3) (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer (D : Set Ω)))
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) {e : Ω} (heB : e ∈ B)
    (heJ : e ∉ Subgroup.normalizer (J : Set Ω)) :
    ∃ D' J' : Subgroup Ω, D' ≤ B ∧ Nat.card ↥D < Nat.card ↥D' ∧ Nat.card ↥D' ∣ 3 ^ 3 ∧
      IsComponentOf J' (S ⊓ Subgroup.centralizer (D' : Set Ω)) ∧
      Nat.card (↥J' ⧸ Subgroup.center ↥J') = 60 := by
  have hepow : e ^ 3 = 1 := hBel.2 e heB
  have heC : ∀ d ∈ D, d * e = e * d := fun d hd => isElemAbelian_commute hBel (hDB hd) heB
  have heCD : e ∈ Subgroup.centralizer (D : Set Ω) := Subgroup.mem_centralizer_iff.2 heC
  have heX : e ∈ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer (D : Set Ω) : Subgroup Ω) : Set Ω) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer heCD⟩
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top e
  obtain ⟨Δ, hΔ, ⟨hiso⟩⟩ := exists_norm_isComponentOf Nat.prime_three hJ hepow heX heJ
  have hD'B : D ⊔ Subgroup.zpowers e ≤ B := sup_le hDB (Subgroup.zpowers_le.2 heB)
  have hC : Subgroup.centralizer ((D ⊔ Subgroup.zpowers e : Subgroup Ω) : Set Ω) =
      Subgroup.centralizer (D : Set Ω) ⊓ Subgroup.centralizer ({e} : Set Ω) := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hg
      exact ⟨fun h hh => hg h (Subgroup.mem_sup_left hh), fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hg e (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))⟩
    · rintro ⟨hgD, hge⟩ h hh
      have hle : D ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({g} : Set Ω) := by
        refine sup_le (fun d hd => ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hgD d hd)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hge e rfl)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hDJ : D ≤ Subgroup.centralizer (J : Set Ω) :=
    Subgroup.le_centralizer_iff.1 fun x hx => (hJ.1 hx).2
  have heD : e ∉ D := fun h => heJ (Subgroup.centralizer_le_normalizer _ (hDJ h))
  have hlt : Nat.card ↥D < Nat.card ↥(D ⊔ Subgroup.zpowers e) := by
    have hle : D ≤ D ⊔ Subgroup.zpowers e := le_sup_left
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun heq => heD ?_
    rw [Subgroup.eq_of_le_of_card_ge hle heq.ge]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hle3 : Nat.card ↥(D ⊔ Subgroup.zpowers e) ≤ Nat.card ↥D * 3 := by
    have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set Ω) :=
      Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ heCD)
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left D (Subgroup.zpowers e) hN
    have hz : Nat.card ↥(Subgroup.zpowers e) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hepow)
    calc Nat.card ↥(D ⊔ Subgroup.zpowers e)
        = Nat.card ((D ⊔ Subgroup.zpowers e : Subgroup Ω) : Set Ω) := rfl
      _ = Nat.card ((D : Set Ω) * (Subgroup.zpowers e : Set Ω)) := by rw [hcoe]
      _ ≤ Nat.card (D : Set Ω) * Nat.card (Subgroup.zpowers e : Set Ω) := Set.natCard_mul_le
      _ ≤ Nat.card ↥D * 3 := Nat.mul_le_mul_left _ hz
  have hdvd : Nat.card ↥(D ⊔ Subgroup.zpowers e) ∣ 3 ^ 3 := by
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three
      (isElemAbelian_mono hBel hD'B)
    have hD9 : Nat.card ↥D ≤ 9 := by
      obtain ⟨m, hm, hmD⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hD
      have hm2 : m ≤ 2 := by
        by_contra hlt
        exact hD27 (by rw [hmD, show m = 3 by omega])
      rw [hmD]
      calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 9 := by norm_num
    have h1 : 3 ^ k ≤ 3 ^ 3 := by
      rw [← hk]
      omega
    rw [hk]
    exact pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right (by norm_num)).1 h1)
  refine ⟨D ⊔ Subgroup.zpowers e, Δ, hD'B, hlt, hdvd, ?_, ?_⟩
  · rw [hC, ← inf_assoc]
    exact hΔ
  · rw [Nat.card_congr hiso.toEquiv]
    exact h60

theorem exists_layer_of_a5 {S B D J : Subgroup Ω} (hSn : S.Normal) (hBel : IsElemAbelian 3 B)
    (hB : 3 ^ 4 ≤ Nat.card ↥B) (hDB : D ≤ B) (hD : Nat.card ↥D ∣ 3 ^ 3)
    (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer (D : Set Ω)))
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) :
    ∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 ∧
      GLAPLayer 3 (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
  suffices H : ∀ (n : ℕ) (D J : Subgroup Ω), 27 - Nat.card ↥D ≤ n → D ≤ B →
      Nat.card ↥D ∣ 3 ^ 3 → IsComponentOf J (S ⊓ Subgroup.centralizer (D : Set Ω)) →
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 60 →
      ∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 3 ∧
        GLAPLayer 3 (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ from
    H _ D J le_rfl hDB hD hJ h60
  intro n
  induction n with
  | zero =>
    intro D J hn hDB hD hJ h60
    have h27 : Nat.card ↥D = 3 ^ 3 := by
      have := Nat.le_of_dvd (by norm_num) hD
      omega
    exact exists_layer_of_extend hBel hB hDB hD hJ h60 (Or.inl h27)
  | succ n ih =>
    intro D J hn hDB hD hJ h60
    by_cases hBJ : B ≤ Subgroup.normalizer (J : Set Ω)
    · exact exists_layer_of_extend hBel hB hDB hD hJ h60 (Or.inr hBJ)
    by_cases h27 : Nat.card ↥D = 3 ^ 3
    · exact exists_layer_of_extend hBel hB hDB hD hJ h60 (Or.inl h27)
    obtain ⟨e, heB, heJ⟩ := SetLike.not_le_iff_exists.1 hBJ
    obtain ⟨D', J', hD'B, hlt, hD'dvd, hJ', h60'⟩ :=
      exists_larger_of_a5 hSn hBel hDB hD h27 hJ h60 heB heJ
    refine ih D' J' ?_ hD'B hD'dvd hJ' h60'
    have := Nat.le_of_dvd (by norm_num) hD'dvd
    omega

theorem t263GConcl_of_a5 {S B J : Subgroup Ω} (hSn : S.Normal) (hBel : IsElemAbelian 3 B)
    (hB : 3 ^ 4 ≤ Nat.card ↥B) {x : Ω} (hxB : x ∈ B)
    (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)))
    (h60 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) : T263GConcl 3 S B := by
  refine Or.inl (exists_layer_of_a5 hSn hBel hB (D := Subgroup.zpowers x)
    (Subgroup.zpowers_le.2 hxB) ?_ ?_ h60)
  · rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hBel.2 x hxB)).trans (by norm_num)
  · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hJ

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
