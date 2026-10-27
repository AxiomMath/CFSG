module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSylowFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKernelClosure
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUSylow
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_inf_of_normal_sylow {Y : Type*} [Group Y] [Finite Y]
    {Q : Sylow 2 Y} {H : Subgroup Y} [H.Normal] : IsSylowTwoIn ((Q : Subgroup Y) ⊓ H) H := by
  refine ⟨inf_le_right, QuasiDihedralFusion.sylowInfNormal Q H, ?_⟩
  rw [QuasiDihedralFusion.sylowInfNormal_coe]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem exists_sylowTwoIn_normalizer_t {t : G} {W M : Subgroup G}
    (_hM : M = normalizer (W : Set G)) (htM : t ∈ M) (ht2 : orderOf t = 2) :
    ∃ S : Subgroup G, IsSylowTwoIn S M ∧ t ∈ S := by
  have hz : IsPGroup 2 ↥(zpowers (⟨t, htM⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  exact ⟨(Q : Subgroup ↥M).map M.subtype, ⟨map_subtype_le _, Q,
      (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm⟩,
    ⟨⟨t, htM⟩, hQ (mem_zpowers (⟨t, htM⟩ : ↥M)), rfl⟩⟩

theorem suz_zGammaThree_sylow_facts (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : IsComponent L) (hZ : Nat.card (Subgroup.center ↥L) ≤ 2)
    (hLty : IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz) (R : Sylow 2 ↥L) :
    IsElemTwo (zGammaThree (R : Subgroup ↥L)) ∧
      16 ≤ Nat.card (zGammaThree (R : Subgroup ↥L)) := by
  by_cases hcen : Subgroup.center ↥L = ⊥
  · have hspor : IsSporadic ↥L .Suz := by
      obtain ⟨e⟩ := hLty
      exact ⟨((QuotientGroup.quotientBot (G := ↥L)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans e⟩
    obtain ⟨h1, h2, -⟩ := hF1 ↥L hspor R
    exact ⟨h1, by omega⟩
  · have hZbot : 1 < Nat.card (Subgroup.center ↥L) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center ↥L)).mpr hcen
    have hZ2 : Nat.card (Subgroup.center ↥L) = 2 := by omega
    obtain ⟨h1, h2, -⟩ := hF2 ↥L hL.1.1 hZ2 hLty R
    exact ⟨h1, by omega⟩

theorem card_map_of_injOn {H K : Type*} [Group H] [Group K] {f : H →* K} {A : Subgroup H}
    (hf : Set.InjOn f A) : Nat.card ↥(A.map f) = Nat.card ↥A := by
  have hbij : Function.Bijective
      (fun a : ↥A => (⟨f a, Subgroup.mem_map_of_mem f a.2⟩ : ↥(A.map f))) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact Subtype.ext (hf ha hb (Subtype.ext_iff.mp hab))
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem isElemTwo_map_of_injective {H K : Type*} [Group H] [Group K] (f : H →* K)
    {A : Subgroup H} (h : IsElemTwo A) : IsElemTwo (A.map f) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h.2 x hx, map_one]

theorem suz_wGroup_anchor
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {t : G} {P W : Subgroup G}
    (hc : L34WConfigAt (fun X _ => IsSporadic X .Suz) G t P W) :
    ∃ A : Subgroup G, A ≤ centralizer ({t} : Set G) ∧ IsElemTwo A ∧ 16 ≤ Nat.card A ∧
      wGroup A = W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset : L34NormalSettingAt (fun X _ => IsSporadic X .Suz) G t P :=
    ⟨hc.base, hc.order_two, hc.le_centralizer, hc.isPComponent, hc.normal, hc.mirror, hc.type⟩
  have hdata := suzSylowData_of_facts hF1 hF2 hset
  obtain ⟨R₀⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  let R : Subgroup G := (R₀ : Subgroup ↥P).map P.subtype
  have hR : IsSylowTwoIn R P := ⟨map_subtype_le _, R₀, by rw [subgroupOf_map_subtype_eq]⟩
  obtain ⟨hRe, hRcard⟩ := hdata.elem R hR
  have hAle : zGammaThree R ≤ centralizer ({t} : Set G) :=
    ((zGammaThree_le R).trans hR.1).trans hc.le_centralizer
  exact ⟨zGammaThree R, hAle, hRe, hRcard, hc.wGroup_eq _ hAle hRe (by omega)⟩

def SuzPairSeed {G : Type} [Group G] [Finite G] (t : G) (_W M S A₀ : Subgroup G) : Prop :=
  IsSylowTwoIn S M ∧ t ∈ S ∧ A₀ ≤ S ∧ IsElemTwo A₀ ∧ 32 ≤ Nat.card A₀ ∧
    S ≤ normalizer (A₀ : Set G) ∧ IsThreeConnected S

theorem suz_pair_sylow_fusion_of_seed
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {t : G} {P W M : Subgroup G}
    (hc : L34WConfigAt (fun X _ => IsSporadic X .Suz) G t P W)
    (hM : M = normalizer (W : Set G)) {S A₀ : Subgroup G} (hseed : SuzPairSeed t W M S A₀) :
    Odd M.index ∧ ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, htS, hA₀S, hA₀e, hA₀card, hSA₀, h3⟩ := hseed
  obtain ⟨A, hAC, hAe, hAcard, hWA⟩ := suz_wGroup_anchor hF1 hF2 hc
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hc.order_two] at h
    simpa [pow_two] using h
  have hSylA : IsSylowTwoIn S (normalizer (wGroup A : Set G)) := by
    rw [hWA]
    exact hM ▸ hSyl
  have hB : GWTwoBalanced G := hc.gwTwoBalanced
  obtain ⟨Q, hQ⟩ := (sylow_and_fusion_of_threeConnected hB hAe (by omega) hSylA h3).1
  have hrank : ∀ b ∈ S, b * b = 1 → 3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) := by
    intro b hbS hb2
    have hbN : b ∈ normalizer (A₀ : Set G) := hSA₀ hbS
    have hcard := GrSLit.card_le_card_inf_centralizer_sq hA₀e hbN hb2
    have hCe : IsElemTwo (A₀ ⊓ centralizer ({b} : Set G)) := hA₀e.mono inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hCe.isPGroup
    have h32 : 32 ≤ Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) ^ 2 :=
      le_trans hA₀card hcard
    have h32' : 32 ≤ (2 ^ n) ^ 2 := hn ▸ h32
    have hn3 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> norm_num at h32'
    have hC8 : 8 ≤ Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
        _ = Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) := hn.symm
    refine le_trans (hCe.three_le_pRank hC8) (Sol78.pRank_le_of_le ?_)
    exact le_inf (inf_le_left.trans hA₀S) inf_le_right
  refine ⟨CFSG.ComponentClassification.AschbacherStrongEmbedding.Lemma34.odd_index_of_sylow_le
    (S := Q) (H := M) (by rw [hQ]; exact hSyl.1), ?_⟩
  intro g hg
  have hne1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    have h1 : t = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using this
    have h2 := hc.order_two
    rw [h1, orderOf_one] at h2
    omega
  have hb2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [show (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  have hord : orderOf (g⁻¹ * t * g) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hb2) hne1
  have hQgrp : IsPGroup 2 ↥(zpowers (g⁻¹ * t * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hzM : zpowers (g⁻¹ * t * g) ≤ M := zpowers_le.mpr hg
  obtain ⟨c, hcM, hcS⟩ := hSyl.exists_conj_le (H := M) hzM hQgrp
  have hcm : (g * c⁻¹)⁻¹ * t * (g * c⁻¹) ∈ S := by
    have h := hcS (g⁻¹ * t * g) (mem_zpowers (g⁻¹ * t * g))
    simpa [mul_assoc] using h
  have hb2' : ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) * ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) = 1 := by
    rw [show ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) * ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) =
      (g * c⁻¹)⁻¹ * (t * t) * (g * c⁻¹) by group, ht2]
    group
  obtain ⟨m, hm, hmeq⟩ := conj_eq_of_threeConnected hB hAe (by omega) hSylA h3 t htS
    (g * c⁻¹) hcm (hrank t htS ht2) (hrank _ hcm hb2')
  have hmW : m ∈ normalizer (W : Set G) := hWA ▸ hm
  have hmM : m ∈ M := hM.symm ▸ hmW
  refine ⟨m * c, M.mul_mem hmM hcM, ?_⟩
  rw [show (m * c)⁻¹ * t * (m * c) = c⁻¹ * (m⁻¹ * t * m) * c by group, ← hmeq]
  group

theorem suz_component_pair_facts {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom) :
    IsComponent (L.map (MulAut.conj tb).toMonoidHom) ∧
      ⁅L, L.map (MulAut.conj tb).toMonoidHom⁆ = ⊥ ∧
      Nat.card ↥(L ⊓ L.map (MulAut.conj tb).toMonoidHom) ≤
        Nat.card ↥(Subgroup.center ↥L) ∧
      (L ⊔ L.map (MulAut.conj tb).toMonoidHom).Normal ∧
      (∀ x : X, (L ⊔ L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        L ⊔ L.map (MulAut.conj tb).toMonoidHom) := by
  classical
  have hcomp : IsComponent (L.map (MulAut.conj tb).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tb) hL
  have hcomm : ⁅L, L.map (MulAut.conj tb).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL hcomp with h | h
    · exact absurd h.symm hne
    · exact h
  have hcent : L ⊓ L.map (MulAut.conj tb).toMonoidHom ≤
      Subgroup.centralizer (L : Set X) := by
    intro x hx
    have hcomm' : ⁅L.map (MulAut.conj tb).toMonoidHom, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hx.2
  have hcard : Nat.card ↥(L ⊓ L.map (MulAut.conj tb).toMonoidHom) ≤
      Nat.card ↥(Subgroup.center ↥L) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(L ⊓ L.map (MulAut.conj tb).toMonoidHom) =>
        (⟨⟨x.1, x.2.1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext
          (Subgroup.mem_centralizer_iff.mp (hcent x.2) (y : X) y.2)⟩ :
          ↥(Subgroup.center ↥L))) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : X)) hxy)
  have hcomp2 : ∀ x : X, (L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L.map (MulAut.conj (x * tb)).toMonoidHom := by
    intro x
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have himg : ∀ x : X,
      (L.map (MulAut.conj x).toMonoidHom = L ∧
        (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom) ∨
      (L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom ∧
        (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom = L) := by
    intro x
    have himp : ∀ (hx : L.map (MulAut.conj x).toMonoidHom = L)
        (hy : (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom = L),
        False := by
      intro hx hy
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hx, hy]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE.symm)
    have himp2 : ∀ (hx : L.map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom)
        (hy : (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom), False := by
      intro hx hy
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hx, hy]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
    rcases hpair x with hx | hx
    · rcases hpair (x * tb) with hy | hy
      · exact (himp hx (by rw [hcomp2 x]; exact hy)).elim
      · exact Or.inl ⟨hx, by rw [hcomp2 x]; exact hy⟩
    · rcases hpair (x * tb) with hy | hy
      · exact Or.inr ⟨hx, by rw [hcomp2 x]; exact hy⟩
      · exact (himp2 hx (by rw [hcomp2 x]; exact hy)).elim
  have hmap : ∀ x : X, (L ⊔ L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L ⊔ L.map (MulAut.conj tb).toMonoidHom := by
    intro x
    rw [Subgroup.map_sup]
    rcases himg x with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  refine ⟨hcomp, hcomm, hcard, ?_, hmap⟩
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
  intro x _
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap x

theorem suz_pair_component_sylows {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom)
    (Q : Sylow 2 X) :
    IsSylowTwoIn ((Q : Subgroup X) ⊓ (L ⊔ L.map (MulAut.conj tb).toMonoidHom))
        (L ⊔ L.map (MulAut.conj tb).toMonoidHom) ∧
      IsSylowTwoIn ((Q : Subgroup X) ⊓ L) L ∧
      IsSylowTwoIn ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)
        (L.map (MulAut.conj tb).toMonoidHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, -, hHnorm, hHmap⟩ := suz_component_pair_facts hL hne hpair
  let H : Subgroup X := L ⊔ L.map (MulAut.conj tb).toMonoidHom
  have : H.Normal := hHnorm
  have hcent : L.map (MulAut.conj tb).toMonoidHom ≤ Subgroup.centralizer (L : Set X) := by
    have h' : ⁅L.map (MulAut.conj tb).toMonoidHom, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'
  have hcent' : L ≤ Subgroup.centralizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hHnormL : H ≤ Subgroup.normalizer (L : Set X) :=
    sup_le Subgroup.le_normalizer (hcent.trans (Subgroup.centralizer_le_normalizer (L : Set X)))
  have hHnormL₂ : H ≤ Subgroup.normalizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
    sup_le (hcent'.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hHinf : IsSylowTwoIn ((Q : Subgroup X) ⊓ H) H :=
    isSylowTwoIn_inf_of_normal_sylow (Q := Q) (H := H)
  have hLinf : IsSylowTwoIn (((Q : Subgroup X) ⊓ H) ⊓ L) L :=
    CFSG.ComponentClassification.TBLit.L34FU.isSylowTwoIn_inf hHinf le_sup_left hHnormL
  have hL2inf : IsSylowTwoIn (((Q : Subgroup X) ⊓ H) ⊓ L.map (MulAut.conj tb).toMonoidHom)
      (L.map (MulAut.conj tb).toMonoidHom) :=
    CFSG.ComponentClassification.TBLit.L34FU.isSylowTwoIn_inf hHinf le_sup_right hHnormL₂
  have h1 : ((Q : Subgroup X) ⊓ H) ⊓ L = (Q : Subgroup X) ⊓ L := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr (le_sup_left : L ≤ H)
  have h2 : ((Q : Subgroup X) ⊓ H) ⊓ L.map (MulAut.conj tb).toMonoidHom =
      (Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr (le_sup_right : L.map (MulAut.conj tb).toMonoidHom ≤ H)
  exact ⟨hHinf, h1 ▸ hLinf, h2 ▸ hL2inf⟩

theorem suz_pair_zGammaThrees (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L) (hZ : Nat.card (Subgroup.center ↥L) ≤ 2)
    (hLty : IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom)
    (Q : Sylow 2 X) (htbQ : tb ∈ (Q : Subgroup X)) :
    ∃ E₁ E₂ : Subgroup X, E₁ ≤ (Q : Subgroup X) ∧ E₂ ≤ (Q : Subgroup X) ∧
      IsElemTwo (E₁ ⊔ E₂) ∧ 32 ≤ Nat.card ↥(E₁ ⊔ E₂) ∧
      (∀ x ∈ (Q : Subgroup X), (E₁ ⊔ E₂).map (MulAut.conj x).toMonoidHom = E₁ ⊔ E₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, hcardInf, -, -⟩ := suz_component_pair_facts hL hne hpair
  obtain ⟨-, hR₁, -⟩ := suz_pair_component_sylows hL hne hpair Q
  obtain ⟨R₁, hR₁coe⟩ := hR₁.2
  obtain ⟨hE₁e₀, hE₁c₀⟩ := suz_zGammaThree_sylow_facts hF1 hF2 hL hZ hLty R₁
  have hmap₁ : ((R₁ : Subgroup ↥L)).map L.subtype = (Q : Subgroup X) ⊓ L := by
    rw [hR₁coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hz₁ : (zGammaThree (R₁ : Subgroup ↥L)).map L.subtype =
      zGammaThree ((Q : Subgroup X) ⊓ L) := by
    rw [map_zGammaThree_of_injOn L.subtype L.subtype_injective.injOn, hmap₁]
  have hE₁e : IsElemTwo (zGammaThree ((Q : Subgroup X) ⊓ L)) := by
    rw [← hz₁]; exact isElemTwo_map_of_injective L.subtype hE₁e₀
  have hE₁c : 16 ≤ Nat.card ↥(zGammaThree ((Q : Subgroup X) ⊓ L)) := by
    rw [← hz₁, card_map_of_injOn L.subtype_injective.injOn]; exact hE₁c₀
  have hE₁L : zGammaThree ((Q : Subgroup X) ⊓ L) ≤ L :=
    (zGammaThree_le _).trans inf_le_right
  have hE₁Q : zGammaThree ((Q : Subgroup X) ⊓ L) ≤ (Q : Subgroup X) :=
    (zGammaThree_le _).trans inf_le_left
  let E₁ : Subgroup X := zGammaThree ((Q : Subgroup X) ⊓ L)
  let E₂ : Subgroup X := E₁.map (MulAut.conj tb).toMonoidHom
  have hE₂e : IsElemTwo E₂ := isElemTwo_map_of_injective _ hE₁e
  have hE₂c : 16 ≤ Nat.card ↥E₂ := by
    change 16 ≤ Nat.card ↥(E₁.map (MulAut.conj tb).toMonoidHom)
    rw [card_map_of_injOn (MulAut.conj tb).injective.injOn]
    exact hE₁c
  have hQtb : (Q : Subgroup X).map (MulAut.conj tb).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htbQ)
  have hmapQ : ((Q : Subgroup X) ⊓ L).map (MulAut.conj tb).toMonoidHom =
      (Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj tb).injective, hQtb]
  have hE₂L : E₂ ≤ L.map (MulAut.conj tb).toMonoidHom := by
    calc E₂ ≤ ((Q : Subgroup X) ⊓ L).map (MulAut.conj tb).toMonoidHom :=
          Subgroup.map_mono (zGammaThree_le _)
      _ = (Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom := hmapQ
      _ ≤ L.map (MulAut.conj tb).toMonoidHom := inf_le_right
  have hE₂Q : E₂ ≤ (Q : Subgroup X) := by
    calc E₂ ≤ ((Q : Subgroup X) ⊓ L).map (MulAut.conj tb).toMonoidHom :=
          Subgroup.map_mono (zGammaThree_le _)
      _ = (Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom := hmapQ
      _ ≤ (Q : Subgroup X) := inf_le_left
  have hcommE : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
    intro x hx y hy
    have hxL : x ∈ L := hE₁L hx
    have hyL : y ∈ L.map (MulAut.conj tb).toMonoidHom := hE₂L hy
    have hcen : L ≤ Subgroup.centralizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (hcen hxL) y hyL).symm
  have hsupE : IsElemTwo (E₁ ⊔ E₂) := IsElemTwo.sup hE₁e hE₂e hcommE
  have hcard : 32 ≤ Nat.card ↥(E₁ ⊔ E₂) := by
    have h := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hcommE |>.1
    have hin : E₁ ⊓ E₂ ≤ L ⊓ L.map (MulAut.conj tb).toMonoidHom := inf_le_inf hE₁L hE₂L
    have h2 : Nat.card ↥(E₁ ⊓ E₂) ≤ 2 :=
      le_trans (Subgroup.card_le_of_le hin) (le_trans hcardInf hZ)
    have h256 : 256 ≤ Nat.card ↥(E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) := by
      rw [h]; exact Nat.mul_le_mul hE₁c hE₂c
    have hle : Nat.card ↥(E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) ≤
        Nat.card ↥(E₁ ⊔ E₂) * 2 := Nat.mul_le_mul_left _ h2
    have := le_trans h256 hle
    omega
  have hcomp2 : ∀ x : X, (L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L.map (MulAut.conj (x * tb)).toMonoidHom := by
    intro x
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hinv : ∀ x ∈ (Q : Subgroup X),
      (E₁ ⊔ E₂).map (MulAut.conj x).toMonoidHom = E₁ ⊔ E₂ := by
    intro x hxQ
    have hxtQ : x * tb ∈ (Q : Subgroup X) := (Q : Subgroup X).mul_mem hxQ htbQ
    have hE₁conj_gen : ∀ y ∈ (Q : Subgroup X), E₁.map (MulAut.conj y).toMonoidHom =
        zGammaThree ((Q : Subgroup X) ⊓ L.map (MulAut.conj y).toMonoidHom) := by
      intro y hy
      have hQy : (Q : Subgroup X).map (MulAut.conj y).toMonoidHom = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)
      rw [show E₁ = zGammaThree ((Q : Subgroup X) ⊓ L) from rfl,
        ← zGammaThree_map_conj y ((Q : Subgroup X) ⊓ L),
        Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hQy]
    have hx1 : E₁.map (MulAut.conj x).toMonoidHom =
        zGammaThree ((Q : Subgroup X) ⊓ L.map (MulAut.conj x).toMonoidHom) :=
      hE₁conj_gen x hxQ
    have hz₂ : E₂ = zGammaThree ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom) := by
      rw [show E₂ = E₁.map (MulAut.conj tb).toMonoidHom from rfl]
      exact hE₁conj_gen tb htbQ
    have hx2 : E₂.map (MulAut.conj x).toMonoidHom =
        zGammaThree ((Q : Subgroup X) ⊓ L.map (MulAut.conj (x * tb)).toMonoidHom) := by
      rw [show E₂ = E₁.map (MulAut.conj tb).toMonoidHom from rfl, Subgroup.map_map]
      have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj tb).toMonoidHom =
          (MulAut.conj (x * tb)).toMonoidHom := by
        ext y; simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp]
      exact hE₁conj_gen (x * tb) hxtQ
    rw [Subgroup.map_sup, hx1, hx2,
      show E₁ = zGammaThree ((Q : Subgroup X) ⊓ L) from rfl, hz₂]
    rcases hpair x with h1 | h1 <;> rcases hpair (x * tb) with h2 | h2
    · exfalso
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hcomp2 x, h1, h2]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exfalso
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hcomp2 x, h1, h2]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
  exact ⟨E₁, E₂, hE₁Q, hE₂Q, hsupE, hcard, hinv⟩

theorem inf_oddIn_eq_bot_of_isSylowTwoIn {Y : Type} [Group Y] [Finite Y]
    {M S : Subgroup Y} (hSyl : IsSylowTwoIn S M) : S ⊓ oddIn M = ⊥ := by
  have hOodd : Nat.Coprime 2 (Nat.card (oddIn M)) := by
    rw [oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact CFSG.coprime_card_pPrimeCore 2 ↥M
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxO⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn⟩ := hSyl.isPGroup ⟨x, hxS⟩
  have h1 : orderOf x ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hn
  have h2 : orderOf x ∣ Nat.card (oddIn M) := Subgroup.orderOf_dvd_natCard _ hxO
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n hOodd) h1 h2
  simpa using orderOf_eq_one_iff.mp h3

theorem suz_exists_pair_seed (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hZ : Nat.card (Subgroup.center ↥L) ≤ 2)
    (hLty : IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ x : ↥M ⧸ pPrimeCore 2 ↥M,
      L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    ∃ S A₀ : Subgroup G, SuzPairSeed t W M S A₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSyl, htS⟩ := exists_sylowTwoIn_normalizer_t hM htM hc.order_two
  obtain ⟨P_M, hP_M⟩ := hSyl.2
  let π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let Q : Sylow 2 (↥M ⧸ pPrimeCore 2 ↥M) :=
    P_M.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hQcoe : (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) = (S.subgroupOf M).map π := by
    rw [Sylow.coe_mapSurjective]
    exact congrArg (fun K => K.map π) hP_M
  have htbQ : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ ∈
      (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) := by
    rw [hQcoe]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr htS)
  obtain ⟨E₁, E₂, hE₁Q, hE₂Q, hsupE, hcardE, hinv⟩ :=
    suz_pair_zGammaThrees hF1 hF2 hL hZ hLty hne hpair Q htbQ
  have hPbarQ : E₁ ⊔ E₂ ≤ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) := sup_le hE₁Q hE₂Q
  have hS'O : S.subgroupOf M ⊓ pPrimeCore 2 ↥M = ⊥ := by
    have h := inf_oddIn_eq_bot_of_isSylowTwoIn hSyl
    have hmap : (S.subgroupOf M ⊓ pPrimeCore 2 ↥M).map M.subtype = S ⊓ oddIn M := by
      rw [Subgroup.map_inf _ _ _ M.subtype_injective, oddIn,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyl.1]
    exact Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective |>.mp (by rw [hmap, h])
  have hinjS : Function.Injective (π.comp (S.subgroupOf M).subtype) := by
    intro x y hxy
    have hxy' : π (x : ↥M) = π (y : ↥M) := hxy
    have h1 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ pPrimeCore 2 ↥M := by
      have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
        have h3 : π ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
          rw [map_mul, map_inv, hxy', inv_mul_cancel]
        exact h3
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h3 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ S.subgroupOf M :=
      (S.subgroupOf M).mul_mem ((S.subgroupOf M).inv_mem x.2) y.2
    have h4 : ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
      have h5 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ S.subgroupOf M ⊓ pPrimeCore 2 ↥M :=
        Subgroup.mem_inf.mpr ⟨h3, h1⟩
      rwa [hS'O, Subgroup.mem_bot] at h5
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hA₀'e : IsElemTwo ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M) := by
    constructor
    · intro x hx y hy
      have hxP : π x ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
      have hyP : π y ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hy).1
      have hxs : x ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hx).2
      have hys : y ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hy).2
      have hmul : π (x * y) = π (y * x) := by
        rw [map_mul, map_mul, hsupE.1 (π x) hxP (π y) hyP]
      have hxy := hinjS (a₁ := ⟨x * y, (S.subgroupOf M).mul_mem hxs hys⟩)
        (a₂ := ⟨y * x, (S.subgroupOf M).mul_mem hys hxs⟩) hmul
      exact Subtype.ext_iff.mp hxy
    · intro x hx
      have hxP : π x ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
      have hxs : x ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hx).2
      have hmul : π (x * x) = π 1 := by
        simp [map_mul, hsupE.2 (π x) hxP]
      have hxx := hinjS (a₁ := ⟨x * x, (S.subgroupOf M).mul_mem hxs hxs⟩)
        (a₂ := ⟨1, (S.subgroupOf M).one_mem⟩) hmul
      exact Subtype.ext_iff.mp hxx
  have hex : ∀ p : ↥(E₁ ⊔ E₂), ∃ s : ↥M, s ∈ S.subgroupOf M ∧ π s = (p : ↥M ⧸ pPrimeCore 2 ↥M) := by
    intro p
    have hp : (p : ↥M ⧸ pPrimeCore 2 ↥M) ∈ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) :=
      hPbarQ p.2
    rw [hQcoe] at hp
    obtain ⟨s, hs, hπ⟩ := Subgroup.mem_map.mp hp
    exact ⟨s, hs, hπ⟩
  have hcard_le : Nat.card ↥(E₁ ⊔ E₂) ≤
      Nat.card ↥((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M) := by
    have hinj : Function.Injective (fun p : ↥(E₁ ⊔ E₂) =>
        (⟨(hex p).choose, Subgroup.mem_inf.mpr ⟨by
          rw [Subgroup.mem_comap, (hex p).choose_spec.2]; exact p.2,
          (hex p).choose_spec.1⟩⟩ :
          ↥((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M))) := by
      intro p q hpq
      have hp : π ((hex p).choose) = (p : ↥M ⧸ pPrimeCore 2 ↥M) := (hex p).choose_spec.2
      have hq : π ((hex q).choose) = (q : ↥M ⧸ pPrimeCore 2 ↥M) := (hex q).choose_spec.2
      have hval : ((hex p).choose : ↥M) = ((hex q).choose : ↥M) := congrArg Subtype.val hpq
      have h1 : (p : ↥M ⧸ pPrimeCore 2 ↥M) = (q : ↥M ⧸ pPrimeCore 2 ↥M) := by
        rw [← hp, ← hq, congrArg (fun z : ↥M => π z) hval]
      exact Subtype.ext h1
    exact Nat.card_le_card_of_injective _ hinj
  have hA₀le : ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype ≤ S := by
    refine le_trans (Subgroup.map_mono inf_le_right) ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyl.1]
  have hA₀e : IsElemTwo (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype) := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa using congrArg M.subtype (hA₀'e.1 x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg M.subtype (hA₀'e.2 x hx)
  have hA₀card : 32 ≤ Nat.card ↥(((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact le_trans hcardE hcard_le
  have hconjcomap : ∀ (g : ↥M) (K : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)),
      (K.comap π).map (MulAut.conj g).toMonoidHom =
        (K.map (MulAut.conj (π g)).toMonoidHom).comap π := by
    intro g K
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_comap] at hy ⊢
      rw [← hyx]
      have hπ : π ((MulAut.conj g).toMonoidHom y) = (MulAut.conj (π g)).toMonoidHom (π y) := by
        simp [MulAut.conj_apply]
      rw [hπ]
      exact Subgroup.mem_map.mpr ⟨π y, hy, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hπ : π (g⁻¹ * x * g) = (π g)⁻¹ * π x * π g := by
          rw [map_mul, map_mul, map_inv]
        have hconj : (MulAut.conj (π g)).toMonoidHom k = π g * k * (π g)⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hπ, ← hkπ, hconj,
          show (π g)⁻¹ * (π g * k * (π g)⁻¹) * (π g) = k by group]
        exact hk
      · show MulAut.conj g (g⁻¹ * x * g) = x
        rw [MulAut.conj_apply]; group
  have hA₀norm : S ≤ Subgroup.normalizer
      (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype : Set G) := by
    intro s hs
    have hsM : s ∈ M := hSyl.1 hs
    have hstep : ∀ g ∈ S.subgroupOf M,
        ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map (MulAut.conj g).toMonoidHom =
          (E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M := by
      intro g hg
      have hπg : π g ∈ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) := by
        rw [hQcoe]; exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      have hS'inv : (S.subgroupOf M).map (MulAut.conj g).toMonoidHom = S.subgroupOf M :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hconjcomap g (E₁ ⊔ E₂),
        hinv (π g) hπg, hS'inv]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hg : (⟨s, hsM⟩ : ↥M) ∈ S.subgroupOf M := hs
    have hcomp : (MulAut.conj s).toMonoidHom.comp M.subtype =
        M.subtype.comp (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom := by
      ext y
      rfl
    calc (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype).map
          (MulAut.conj s).toMonoidHom
        = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            ((MulAut.conj s).toMonoidHom.comp M.subtype) := by
          rw [Subgroup.map_map]
      _ = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            (M.subtype.comp (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom) := by rw [hcomp]
      _ = (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom).map M.subtype := by
          rw [Subgroup.map_map]
      _ = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype := by
          rw [hstep ⟨s, hsM⟩ hg]
  exact ⟨S, _, hSyl, htS, hA₀le, hA₀e, hA₀card, hA₀norm,
    isThreeConnected_of_normal hSyl.isPGroup hA₀le hA₀norm hA₀e hA₀card⟩

theorem suz_pair_sylow_fusion
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {t : G} {P W M : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hZ : Nat.card (Subgroup.center ↥L) ≤ 2)
    (hLty : IsSporadic (↥L ⧸ Subgroup.center ↥L) .Suz)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ x : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    Odd M.index ∧ ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m := by
  obtain ⟨S, A₀, hseed⟩ := suz_exists_pair_seed hF1 hF2 hc hM htM hL hZ hLty hne hpair
  exact suz_pair_sylow_fusion_of_seed hF1 hF2 hc hM hseed

end CFSG.ComponentClassification.GrSLit.L34Sec5S
