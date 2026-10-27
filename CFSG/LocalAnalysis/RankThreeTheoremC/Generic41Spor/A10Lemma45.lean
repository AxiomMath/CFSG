module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Lemma45
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10l45g_eq_zpowers {X : Type} [Group X] {U₀ : Subgroup X} (hc : Nat.card U₀ = 5) {u : X}
    (hu : u ∈ U₀) (hu1 : u ≠ 1) : U₀ = Subgroup.zpowers u := by
  have hle : Subgroup.zpowers u ≤ U₀ := Subgroup.zpowers_le.mpr hu
  have h1 : orderOf u ∣ 5 := by
    have := orderOf_dvd_natCard (⟨u, hu⟩ : U₀)
    rwa [Subgroup.orderOf_mk, hc] at this
  have h2 : orderOf u = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  haveI : Finite U₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, h2, hc]

theorem a10l45g_lemma45B (X : Type) [Group X] [Finite X] (K : Subgroup X)
    (hK : IsAutOverType IsA10Type 5 K) (R : Sylow 5 X) (U₀ : Subgroup X) (hU₀R : U₀ ≤ (R : Subgroup X))
    (_hU₀e : IsElemAbelian 5 U₀) (hU₀c : Nat.card U₀ = 5) (hsh : A10Shape K (R : Subgroup X) U₀) :
    ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
      ¬ V ≤ ((A10Gamma ↥K (((R : Subgroup X) ⊓ K : Subgroup X).subgroupOf K))).map K.subtype := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hKn, -, hKT⟩ := hK
  haveI : K.Normal := hKn
  obtain ⟨S, hS⟩ := exists_sylow_inf_normal K R
  obtain ⟨e, u, ⟨huU₀, huK⟩, hu, hct⟩ := hsh
  have hu1 : u ≠ 1 := by
    rintro rfl
    have h : (e ⟨1, huK⟩ : alternatingGroup (Fin 10)) = 1 := by
      have : (⟨1, huK⟩ : ↥K) = 1 := rfl
      rw [this, map_one]
    rw [h] at hct
    simp at hct
  have hmem : (⟨u, huK⟩ : ↥K) ∈ (S : Subgroup ↥K) := by
    have : u ∈ (S : Subgroup ↥K).map K.subtype := by rw [hS]; exact ⟨hU₀R huU₀, huK⟩
    obtain ⟨k, hk, hku⟩ := this
    have : k = ⟨u, huK⟩ := Subtype.ext hku
    rwa [this] at hk
  obtain ⟨V₀, hV₀2, hV₀n, hV₀Γ⟩ := a10_lemma45Gamma_holds ↥K hKT S ⟨u, huK⟩ hmem ⟨e, hct⟩
  have hSeq : (S : Subgroup ↥K) = ((R : Subgroup X) ⊓ K : Subgroup X).subgroupOf K := by
    rw [← hS]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  refine ⟨V₀.map K.subtype, Subgroup.map_subtype_le V₀, hV₀2.map K.subtype, ?_, ?_⟩
  · rw [a10l45g_eq_zpowers hU₀c huU₀ hu1, Subgroup.zpowers_le]
    exact Subgroup.le_normalizer_map K.subtype ⟨⟨u, huK⟩, hV₀n, rfl⟩
  · intro hle
    apply hV₀Γ
    rw [hSeq]
    intro v hv
    obtain ⟨w, hw, hwv⟩ := hle ⟨v, hv, rfl⟩
    have : w = v := Subtype.ext hwv
    rwa [this] at hw

theorem a10l45g_exists_iso {J' X Q : Type} [Group J'] [Group X] [Group Q] (π : J' →* X) (ψ : J' →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = π.ker) :
    ∃ e : Q ≃* ↥π.range, ∀ j : J', ((e (ψ j) : ↥π.range) : X) = π j := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange π)), ?_⟩
  intro j
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ j) = (j : J' ⧸ ψ.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  show (((QuotientGroup.quotientKerEquivRange π)
    ((QuotientGroup.quotientMulEquivOfEq hker) ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ j))) :
      ↥π.range) : X) = π j
  rw [h1]
  rfl

theorem a10l45g_shape_core {J' X Q : Type} [Group J'] [Group X] [Group Q] (π : J' →* X) (ψ : J' →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = π.ker) (hQ : IsA10Type 5 Q) (R U₀ : Subgroup X)
    (d : J') (hdU : π d ∈ U₀) (hd5 : π d ^ 5 = 1) (hd1 : π d ≠ 1)
    (hc : Nat.card (Subgroup.centralizer ({ψ d} : Set Q)) = 25) : A10Shape π.range R U₀ := by
  obtain ⟨e, he⟩ := a10l45g_exists_iso π ψ hψ hker
  have hK : IsA10Type 5 ↥π.range := ⟨hQ.1, hQ.2.map fun f => e.symm.trans f⟩
  have huK : π d ∈ π.range := ⟨d, rfl⟩
  refine a10_shape_of_centralizer_card π.range R U₀ hK huK hdU hd5 hd1 ?_
  have hed : e (ψ d) = ⟨π d, huK⟩ := Subtype.ext (he d)
  rw [← hed, ← a10c_card_centralizer_equiv e (ψ d)]
  exact hc

theorem a10l45g_shape
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) {U : Subgroup G} (hU : IIPlane 5 P x J U)
    (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∀ (X : Type) [Group X] (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* X) (K R U₀ : Subgroup X),
      TypeIIRedFactsK 5 P x J U ρ K R U₀ → A10Shape K R U₀ := by
  intro X _ ρ K R U₀ hf
  obtain ⟨d, hd, ⟨hdU, hdT⟩, hψd, hcd⟩ := hγ
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  let π : ↥J →* X := ρ.comp (Subgroup.inclusion hJC)
  have hπK : π.range = K := by
    ext k
    constructor
    · rintro ⟨j, rfl⟩
      exact hf.K_mem ⟨j, hJC j.2⟩ j.2
    · intro hk
      obtain ⟨c, hcJ, rfl⟩ := hf.K_ex k hk
      exact ⟨⟨c, hcJ⟩, rfl⟩
  have hkerπ : ψ.ker = π.ker := by
    rw [hker]
    ext j
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hf.ker_J ⟨j, hJC j.2⟩ j.2).symm
  have hdC : d ∈ Subgroup.centralizer ({x} : Set G) := hJC hd
  have hπd : π ⟨d, hd⟩ = ρ ⟨d, hdC⟩ := rfl
  have hd1 : d ≠ 1 := by
    intro h
    have : (⟨d, hd⟩ : ↥J) = 1 := Subtype.ext h
    exact hψd (by rw [this, map_one])
  rw [← hπK]
  refine a10l45g_shape_core π ψ hψ hkerπ hQ R U₀ ⟨d, hd⟩ ?_ ?_ ?_ hcd
  · rw [hπd]; exact hf.U₀_mem ⟨d, hdC⟩ hdU
  · rw [hπd, ← map_pow]
    have : (⟨d, hdC⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ^ 5 = 1 := Subtype.ext (hU.elem.2 d hdU)
    rw [this, map_one]
  · rw [hπd]
    intro h
    exact hd1 (hf.inj ⟨d, hdC⟩ hdT h)

theorem a10l45g_elemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian p E) :
    IsElemAbelian p F := by
  haveI := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hE.2 y (hFE hy)⟩
  have h := mul_comm' (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩
  apply Subtype.ext
  show (a : G) * b = b * a
  exact congrArg Subtype.val h

theorem a10l45g_zpowers_elemAbelian {x : G} (hx5 : x ^ 5 = 1) :
    IsElemAbelian 5 (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [← zpow_natCast, hx5]

theorem a10l45g_normalizer_le_M
    (hS : Setting G) (hU0 : FullCoreLocal G) (hc : PointConfig IsA10Type G 5 P M x J)
    (hxJ : x ∉ J) (hTe : IsElemAbelian 5 (u3T P x J)) {B : Subgroup ↥J}
    (hB : B ≤ (u3T P x J).subgroupOf J) (hB1 : B ≠ ⊥) {n : ↥J} (hn : n ∈ normalizer (B : Set ↥J)) :
    (n : G) ∈ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set B'' : Subgroup G := B.map J.subtype with hB''
  have hB''T : B'' ≤ u3T P x J := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB hb)
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hx5 : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  have hcomm : ∀ j ∈ J, Commute j x := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJC hj)
  set E : Subgroup G := B'' ⊔ Subgroup.zpowers x with hE
  have hEP : E ≤ (P : Subgroup G) := sup_le (hB''T.trans hTP) (Subgroup.zpowers_le.mpr hxP)
  have hEp : IsPGroup 5 E := P.isPGroup'.to_le hEP
  have hB''e : IsElemAbelian 5 B'' := a10l45g_elemAbelian_of_le hB''T hTe
  have hB''p : IsPGroup 5 B'' := P.isPGroup'.to_le (hB''T.trans hTP)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).mp hB''p
  have hr1 : r ≠ 0 := by
    rintro rfl
    apply hB1
    have h1 : Nat.card B'' = 1 := by simpa using hr
    have h2 : B'' = ⊥ := Subgroup.card_eq_one.mp h1
    rw [eq_bot_iff]
    intro b hb
    have : (b : G) ∈ B'' := ⟨b, hb, rfl⟩
    rw [h2, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hxcard : Nat.card (Subgroup.zpowers x) = 5 ^ 1 := by rw [Nat.card_zpowers, hxo]; norm_num
  have hdisj : B'' ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    have hyJ : y ∈ J := by
      obtain ⟨b, -, rfl⟩ := hy.1
      exact b.2
    have := a10l45g_eq_zpowers (U₀ := Subgroup.zpowers x) (by rw [hxcard]; norm_num) hy.2 hy1
    apply hxJ
    have hxy : x ∈ Subgroup.zpowers y := this ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr hyJ) hxy
  have hcomm' : ∀ a ∈ B'', ∀ y ∈ Subgroup.zpowers x, Commute a y := by
    intro a ha y hy
    obtain ⟨b, -, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hcomm b b.2).zpow_right k
  have hE2 : 2 ≤ CFSG.Open.pRank 5 E := by
    have := plane_add_le_pRank (p := 5) (H := E) (by norm_num) hB''e (a10l45g_zpowers_elemAbelian hx5) hr hxcard
      hcomm' hdisj le_sup_left le_sup_right
    omega
  have hnB'' : (n : G) ∈ normalizer (B'' : Set G) := u3main_mem_normalizer_map hn
  have hzx : (Subgroup.zpowers x).map (MulAut.conj (n : G)) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    have : (MulAut.conj (n : G)) x = x := by
      rw [MulAut.conj_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (hcomm n n.2).eq
    simp [this]
  have hnE : (n : G) ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnB'' ⊢
    rw [hE, Subgroup.map_sup, hnB'', hzx]
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hEp (hEP.trans hPM) hE2 hnE

theorem a10l45g_sylow_image {T : Subgroup G} {X : Type} [Group X] [Finite X] (π : ↥J →* X)
    (hT : IsSylowOf 5 T J) (R : Sylow 5 X) (hTR : (T.subgroupOf J).map π ≤ (R : Subgroup X)) :
    ∃ T' : Sylow 5 ↥π.range, (T' : Subgroup ↥π.range) = (T.subgroupOf J).map π.rangeRestrict ∧
      (T' : Subgroup ↥π.range).map π.range.subtype = (T.subgroupOf J).map π ∧
      (R : Subgroup X) ⊓ π.range = (T.subgroupOf J).map π := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := π.range with hK
  let π' : ↥J →* ↥K := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  obtain ⟨Tsyl, hTsyl⟩ := hT.exists_sylow_eq_subgroupOf
  let T' : Sylow 5 ↥K := Tsyl.mapSurjective hπ'
  have hT'coe : (T' : Subgroup ↥K) = (Tsyl : Subgroup ↥J).map π' := Sylow.coe_mapSurjective hπ' Tsyl
  have hT'map : (T' : Subgroup ↥K).map K.subtype = (T.subgroupOf J).map π := by
    rw [hT'coe, Subgroup.map_map, hTsyl]
    rfl
  have hRK : (R : Subgroup X) ⊓ K = (T.subgroupOf J).map π := by
    have hSyl : IsSylowOf 5 ((T.subgroupOf J).map π) K := ⟨T', hT'map⟩
    refine hSyl.eq_of_le (le_inf hTR ?_) inf_le_right R.isPGroup'.to_inf_left
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  exact ⟨T', by rw [hT'coe, hTsyl], hT'map, hRK⟩

theorem a10l45g_image_le_gamma
    (hS : Setting G) (hU0 : FullCoreLocal G) (hXe : A10Ext) (hc : PointConfig IsA10Type G 5 P M x J)
    (hxJ : x ∉ J) (hTe : IsElemAbelian 5 (u3T P x J))
    {X : Type} [Group X] [Finite X] (π : ↥J →* X) (hKT : IsA10Type 5 ↥π.range)
    (hker : Nat.Coprime 5 (Nat.card π.ker)) (hkerM : ∀ j : ↥J, π j = 1 → (j : G) ∈ M)
    (hT : IsSylowOf 5 (u3T P x J) J) (hJM : ¬ J ≤ M) (R : Sylow 5 X)
    (hTR : ((u3T P x J).subgroupOf J).map π ≤ (R : Subgroup X)) :
    (R : Subgroup X) ⊓ π.range = ((u3T P x J).subgroupOf J).map π ∧
      (M.subgroupOf J).map π ≤
        (A10Gamma ↥π.range (((R : Subgroup X) ⊓ π.range : Subgroup X).subgroupOf π.range)).map
          π.range.subtype := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T', hT'coe, hT'map, hRK⟩ := a10l45g_sylow_image π hT R hTR
  refine ⟨hRK, ?_⟩
  obtain ⟨Tsyl, hTsyl⟩ := hT.exists_sylow_eq_subgroupOf
  let π' : ↥J →* ↥π.range := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  have hπ'ker : π'.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have hSeq : (T' : Subgroup ↥π.range) = ((R : Subgroup X) ⊓ π.range : Subgroup X).subgroupOf π.range := by
    rw [hRK, ← hT'map]
    exact (Subgroup.comap_map_eq_self_of_injective π.range.subtype_injective _).symm
  have hTJp : IsPGroup 5 ((u3T P x J).subgroupOf J) := hTsyl ▸ Tsyl.isPGroup'
  set H : Subgroup ↥π.range := (M.subgroupOf J).map π' with hH
  have hΓH : A10Gamma ↥π.range (T' : Subgroup ↥π.range) ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨B, hBT', hB1, hgB⟩
    obtain ⟨j, rfl⟩ := hπ' g
    set B' : Subgroup ↥J := (u3T P x J).subgroupOf J ⊓ B.comap π' with hB'
    have hB'map : B'.map π' = B := by
      ext b
      constructor
      · rintro ⟨t, ⟨-, ht⟩, rfl⟩
        exact ht
      · intro hb
        have hbT' : b ∈ ((u3T P x J).subgroupOf J).map π' := by
          rw [← hT'coe]
          exact hBT' hb
        obtain ⟨t, ht, rfl⟩ := hbT'
        exact ⟨t, ⟨ht, hb⟩, rfl⟩
    have hB'p : IsPGroup 5 B' := hTJp.to_le inf_le_left
    have hB'1 : B' ≠ ⊥ := by
      intro h
      apply hB1
      rw [← hB'map, h, Subgroup.map_bot]
    have hj : π' j ∈ normalizer ((B'.map π' : Subgroup ↥π.range) : Set ↥π.range) := by
      rw [hB'map]
      exact hgB
    obtain ⟨n, hn, hπn⟩ := typeII_frattini_ker π' (by rw [hπ'ker]; exact hker) hB'p hj
    have hnM : (n : G) ∈ M := a10l45g_normalizer_le_M hS hU0 hc hxJ hTe inf_le_left hB'1 hn
    exact ⟨n, Subgroup.mem_subgroupOf.mpr hnM, hπn⟩
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hJM
    intro g hg
    have hmem : π' ⟨g, hg⟩ ∈ H := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hmem
    have hmg' : π m = π ⟨g, hg⟩ := congrArg Subtype.val hmg
    have hk : m⁻¹ * ⟨g, hg⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg', inv_mul_cancel]
    have h1 : ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) ∈ M := hkerM _ hk
    have h2 : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have : g = (m : G) * ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) := by simp
    rw [this]
    exact M.mul_mem h2 h1
  have hHeq : H = A10Gamma ↥π.range (T' : Subgroup ↥π.range) :=
    ((hXe.gammaMax ↥π.range hKT) T' H hΓH).resolve_right hHtop
  intro v hv
  obtain ⟨j, hj, rfl⟩ := hv
  have h1 : π' j ∈ H := ⟨j, hj, rfl⟩
  rw [hHeq, hSeq] at h1
  exact ⟨π' j, h1, rfl⟩

theorem a10_lemma45_G (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : A10Facts) (hXe : A10Ext) (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q]
    [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J) (hQ : IsA10Type 5 Q)
    {U : Subgroup G} (hU : IIPlane 5 P x J U) (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTe, hxJ⟩ := plane_T_structure hX.sylow hc
  have hT2 : 2 ≤ CFSG.Open.pRank 5 (u3T P x J) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_pRank_of_elemAbelian_card (by norm_num) le_rfl hTe
      hTcard
  have ha : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1 := by
    obtain ⟨d, hd, hdUT, hψd, -⟩ := hγ
    refine ⟨d, hdUT, fun h => hψd ?_⟩
    have : (⟨d, hd⟩ : ↥J) = 1 := Subtype.ext h
    rw [this, map_one]
  exact typeII_lemma45_lift_B (Typ := IsA10Type) (Shape := A10Shape)
    (fun X _ K R => (A10Gamma ↥K ((R ⊓ K : Subgroup X).subgroupOf K)).map K.subtype)
    hS hD1 hU0
    (fun X _ _ K hK R U₀ hU₀R hU₀e hU₀c hsh => a10l45g_lemma45B X K hK R U₀ hU₀R hU₀e hU₀c hsh)
    (fun X _ _ π hKT hker' hkerM hT _ hJM R hTR =>
      a10l45g_image_le_gamma hS hU0 hXe hc hxJ hTe π hKT hker' hkerM hT hJM R hTR)
    (fun A B _ _ e h => ⟨h.1, h.2.map fun f => e.symm.trans f⟩) hc hT2 hU.elem hU.card hU.le hU.mem ha
    (a10l45g_shape hc ψ hψ hker hQ hU hγ)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
