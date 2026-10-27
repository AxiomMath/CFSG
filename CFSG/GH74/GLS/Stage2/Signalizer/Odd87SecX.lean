module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SecL2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped Pointwise commutatorElement

theorem isPerfect_map {C D : Type*} [Group C] [Group D] {P : Subgroup C} (hP : Group.IsPerfect ↥P)
    (π : C →* D) : Group.IsPerfect ↥(P.map π) := by
  refine Subgroup.isPerfect_iff.mpr ?_
  have h1 := Subgroup.map_commutator P P π
  rw [Subgroup.commutator_eq_self] at h1
  exact h1.symm

theorem perfect_eq_bot_of_le_solvable {D : Type*} [Group D] {Q P : Subgroup D}
    (hQ : Group.IsSolvable ↥Q) (hP : Group.IsPerfect ↥P) (hPQ : P ≤ Q) : P = ⊥ := by
  have hPsolv : Group.IsSolvable ↥P := by
    have := hQ
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPQ)
      (Subgroup.inclusion_injective hPQ)
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have := hP
  exact (Group.IsPerfect.not_isSolvable (G := ↥P)) hPsolv

theorem perfect_le_of_solvable_quotient {C : Type*} [Group C] {R P : Subgroup C} [R.Normal]
    (hCR : Group.IsSolvable (C ⧸ R)) (hP : Group.IsPerfect ↥P) : P ≤ R := by
  let π : C →* C ⧸ R := QuotientGroup.mk' R
  have hQ : P.map π = ⊥ :=
    perfect_eq_bot_of_le_solvable (Q := ⊤) inferInstance (isPerfect_map hP π) le_top
  intro p hp
  have : π p ∈ P.map π := ⟨p, hp, rfl⟩
  rw [hQ, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff p).mp this

theorem isSection_of_residual_le {C : Type*} [Group C] [Finite C] {N₀ R J T : Subgroup C}
    [N₀.Normal] [R.Normal] [J.Normal]
    (hN₀ : Group.IsSolvable ↥N₀) (hCR : Group.IsSolvable (C ⧸ R))
    (hT : Group.IsSolvable ↥T) (hR : R ≤ N₀ ⊔ J ⊔ T)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y) (h : IsSection Y C) :
    IsSection Y ↥J := by
  classical
  obtain ⟨P, hP, hPs⟩ := exists_perfect_section hns h
  have hPR : P ≤ R := perfect_le_of_solvable_quotient hCR hP
  have hWn : (N₀ ⊔ J).Normal := inferInstance
  have hPW : P ≤ N₀ ⊔ J := by
    let f : C →* C ⧸ (N₀ ⊔ J) := QuotientGroup.mk' (N₀ ⊔ J)
    have hfT : Group.IsSolvable ↥(T.map f) := by
      exact Group.isSolvable_of_surjective (f := f.subgroupMap T) (f.subgroupMap_surjective T)
    have hle : P.map f ≤ T.map f := by
      have h1 : P ≤ N₀ ⊔ J ⊔ T := hPR.trans hR
      have h2 : (N₀ ⊔ J ⊔ T).map f = T.map f := by
        rw [Subgroup.map_sup]
        have : (N₀ ⊔ J).map f = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨w, hw, rfl⟩
          exact (QuotientGroup.eq_one_iff w).mpr hw
        rw [this, bot_sup_eq]
      exact (Subgroup.map_mono h1).trans h2.le
    have hbot : P.map f = ⊥ := perfect_eq_bot_of_le_solvable hfT (isPerfect_map hP f) hle
    intro p hp
    have : f p ∈ P.map f := ⟨p, hp, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff p).mp this
  have hsecW : IsSection Y ↥(N₀ ⊔ J) := IsSection.of_le_le hPW hPs
  have hNn : (N₀.subgroupOf (N₀ ⊔ J)).Normal := inferInstance
  rcases hsecW.dichotomy (N₀.subgroupOf (N₀ ⊔ J)) with h1 | h2
  · exfalso
    have := hN₀
    have : Group.IsSolvable ↥(N₀.subgroupOf (N₀ ⊔ J)) := by
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : N₀ ≤ N₀ ⊔ J)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : N₀ ≤ N₀ ⊔ J)).injective
    exact hns (h1.isSolvable this)
  · refine IsSection.of_surjective ((QuotientGroup.mk' (N₀.subgroupOf (N₀ ⊔ J))).comp
      (Subgroup.inclusion (le_sup_right : J ≤ N₀ ⊔ J))) ?_ h2
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hw : (w : C) ∈ (↑(N₀ ⊔ J) : Set C) := w.2
    rw [Subgroup.mul_normal, Set.mem_mul] at hw
    obtain ⟨n, hn, j, hj, hnj⟩ := hw
    refine ⟨⟨j, hj⟩, ?_⟩
    show (QuotientGroup.mk (⟨j, Subgroup.mem_sup_right hj⟩ : ↥(N₀ ⊔ J)) :
      ↥(N₀ ⊔ J) ⧸ N₀.subgroupOf (N₀ ⊔ J)) = QuotientGroup.mk w
    have hwe : w = (⟨n, Subgroup.mem_sup_left hn⟩ : ↥(N₀ ⊔ J)) * ⟨j, Subgroup.mem_sup_right hj⟩ :=
      Subtype.ext hnj.symm
    rw [hwe, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨n, Subgroup.mem_sup_left hn⟩ : ↥(N₀ ⊔ J)) :
        ↥(N₀ ⊔ J) ⧸ N₀.subgroupOf (N₀ ⊔ J)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    rw [this, one_mul]

section App

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G]

theorem solvable_quot_oPrimeResidual (X : Type*) [Group X] [Finite X]
    [(oPrimeResidual 2 X).Normal] : Group.IsSolvable (X ⧸ oPrimeResidual 2 X) := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hPR : (P : Subgroup X) ≤ oPrimeResidual 2 X := by
    intro x hx
    apply Subgroup.subset_closure
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hdvd : (oPrimeResidual 2 X).index ∣ (P : Subgroup X).index := Subgroup.index_dvd_of_le hPR
  have hodd : Odd (Nat.card (X ⧸ oPrimeResidual 2 X)) := by
    have h1 : ¬ 2 ∣ (P : Subgroup X).index := P.not_dvd_index
    have h2 : ¬ 2 ∣ (oPrimeResidual 2 X).index := fun h => h1 (h.trans hdvd)
    exact Nat.odd_iff.mpr (by
      have : (oPrimeResidual 2 X).index = Nat.card (X ⧸ oPrimeResidual 2 X) := rfl
      omega)
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd

theorem isSection_Jbar_of_residual {x : G} {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hf : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y ↥(centralizer ({x} : Set G))) :
    IsSection Y (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : Jx x ≤ C := sSup_le fun _ hL => hL.1
  have hTC : T ≤ C := hT.le
  have hTp : IsPGroup 2 ↥T := by
    obtain ⟨Q, rfl⟩ := hT
    have := Q.isPGroup'
    exact this.map _
  have hRn : (oPrimeResidual 2 ↥C).Normal := Stage1.Thm6.Prod.oPrimeResidual_normal 2 _
  have hJn : ((Jx x).subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (n : G) ∈ pLayerOf 2 C := hn
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ pLayerOf 2 C
    exact (Subgroup.mem_normalizer_iff.mp (Stage1.Thm2.Recip.mem_normalizer_pLayerOf (X := C) g.2) n).mp hn'

  have hsubA : ∀ A : Subgroup ↥C, A.map C.subtype ≤ C := fun A => Subgroup.map_subtype_le A
  have e1 := congrArg (fun A : Subgroup G => A.subgroupOf C) hf
  have hOle : oPrimeResidualOf 2 C ≤ C := Subgroup.map_subtype_le _
  have hPle : pPrimeCoreOf 2 C ≤ C := Subgroup.map_subtype_le _
  rw [Subgroup.subgroupOf_sup hOle hPle, Subgroup.subgroupOf_sup (sup_le hPle hJC) hTC,
    Subgroup.subgroupOf_sup hPle hJC] at e1
  have hmapsub : ∀ A : Subgroup ↥C, (A.map C.subtype).subgroupOf C = A := fun A =>
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective A
  have hR : oPrimeResidual 2 ↥C ≤ pPrimeCore 2 ↥C ⊔ (Jx x).subgroupOf C ⊔ T.subgroupOf C := by
    have h1 : oPrimeResidual 2 ↥C ≤ oPrimeResidual 2 ↥C ⊔ pPrimeCore 2 ↥C := le_sup_left
    have h2 : (oPrimeResidualOf 2 C).subgroupOf C = oPrimeResidual 2 ↥C := hmapsub _
    have h3 : (pPrimeCoreOf 2 C).subgroupOf C = pPrimeCore 2 ↥C := hmapsub _
    rw [h2, h3] at e1
    rw [e1] at h1
    exact h1
  have hN₀ : Group.IsSolvable ↥(pPrimeCore 2 ↥C) := Stage2.Final.Thm4.pPrimeCore_solvable
  have hCR : Group.IsSolvable (↥C ⧸ oPrimeResidual 2 ↥C) := solvable_quot_oPrimeResidual _
  have hT' : Group.IsSolvable ↥(T.subgroupOf C) := by
    have : IsPGroup 2 ↥(T.subgroupOf C) := hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
    have := this.isNilpotent
    infer_instance
  have hsec := isSection_of_residual_le hN₀ hCR hT' hR hns h
  have h2 : IsSection Y ↥(Jx x) := IsSection.of_equiv (Subgroup.subgroupOfEquivOfLe hJC).symm hsec
  rcases h2.dichotomy (pPrimeCore 2 ↥(Jx x)) with h3 | h3
  · exact absurd (h3.isSolvable Stage2.Final.Thm4.pPrimeCore_solvable) hns
  · exact h3

theorem isL2_odd_of_section {Jb : Type} [Group Jb] {r : ℕ} (hr : Odd r)
    (hJ : IVK.IsL2 Jb (fun s => s = r)) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y Jb) :
    IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  obtain ⟨F₀, iF, fF, hF, ⟨e⟩⟩ := hJ
  have h1 : IsSection Y (IVK.L2 F₀) := IsSection.of_equiv e.symm h
  have hodd : Odd (Nat.card F₀) := by rw [hF]; exact hr
  by_cases h3 : 3 < Nat.card F₀
  · exact simple_sec_L2 ⟨hodd, h3⟩ hns h1
  · exfalso
    apply hns
    have h4 : Group.IsSolvable (GorensteinWalter.PSL2 F₀) :=
      Stage2.Local.P34.psl2_solvable_of_card_le_three (by omega)
    have h5 : Group.IsSolvable (IVK.L2 F₀) :=
      Group.isSolvable_of_isSolvable_injective (f := (IVK.L2.equivPSL F₀).toMonoidHom)
        (IVK.L2.equivPSL F₀).injective
    exact h1.isSolvable h5

theorem exists_conj_mem_cen {z : G} (hcen : IsCentralInvolution z) {u : G} (hu : orderOf u = 2) :
    ∃ g : G, g * u * g⁻¹ ∈ centralizer ({z} : Set G) := by
  obtain ⟨-, S₀, hzS, hSz⟩ := hcen
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hup : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; simp)
  obtain ⟨S₁, hS₁⟩ := hup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S₀
  have hu1 : u ∈ (S₁ : Subgroup G) := hS₁ (Subgroup.mem_zpowers u)
  have h2 : g * u * g⁻¹ ∈ (S₀ : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hu1, by simp [MulAut.smul_def]⟩
  refine ⟨g, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hSz _ h2

omit [Finite G] in
theorem exists_sylow_cen_ge {x z : G} (hz2 : orderOf z = 2) (hxz : x ∈ centralizer ({z} : Set G)) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ z ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hzC : z ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz ⊢
    exact hxz.symm
  let z' : ↥C := ⟨z, hzC⟩
  have hz'2 : orderOf z' = 2 := by rw [← hz2]; exact Subgroup.orderOf_mk z hzC
  have hz' : IsPGroup 2 ↥(Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2]; simp)
  obtain ⟨Q, hQ⟩ := hz'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥C).map C.subtype, ⟨Q, rfl⟩, ?_⟩
  exact ⟨z', hQ (Subgroup.mem_zpowers z'), rfl⟩

end App

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
