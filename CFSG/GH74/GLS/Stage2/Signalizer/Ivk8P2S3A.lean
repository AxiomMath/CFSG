module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Elementary

variable {G : Type} [Group G]

theorem orderOf_eq_of_elem {p : ℕ} (hp : p.Prime) {V : Subgroup G}
    (hV : IsElementaryAbelian p ↥V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : orderOf v = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hv) hv1

theorem isElementaryAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    (hBA : B ≤ A) : IsElementaryAbelian p ↥B := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    have := congrArg Subtype.val ((hA.toIsMulCommutative.is_comm).comm
      (⟨(a : G), hBA a.2⟩ : A) ⟨(b : G), hBA b.2⟩)
    exact this
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (x : G) (hBA x.2)

theorem exists_plane [Finite G] {p : ℕ} (hp : p.Prime) {V : Subgroup G}
    (hV : IsElementaryAbelian p ↥V) (hnc : ¬ IsCyclic ↥V) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ IsElementaryAbelian p ↥V₀ ∧ Nat.card ↥V₀ = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (IsElementaryAbelian.isPGroup p ↥V)
  have hn2 : 2 ≤ n := by
    by_contra hlt
    apply hnc
    interval_cases n
    · have h1 : Nat.card ↥V = 1 := by rw [hn, pow_zero]
      have : Subsingleton ↥V := (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · exact isCyclic_of_prime_card (p := p) (by rw [hn, pow_one])
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥V) p
    (show p ^ 2 ∣ Nat.card ↥V by rw [hn]; exact pow_dvd_pow p hn2)
  refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · exact isElementaryAbelian_of_le hV (Subgroup.map_subtype_le K)
  · rw [Subgroup.card_map_of_injective V.subtype_injective, hK]

end Elementary

section Steps

variable {G : Type} [Group G] [Finite G]

theorem z_mem_Op_two {z : G} {H : Subgroup G} (hz : z ∈ H) (hz2 : orderOf z = 2)
    (hFs : Fs H ≤ centralizer ({z} : Set G)) : z ∈ Op 2 H := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set zH : ↥H := ⟨z, hz⟩ with hzH
  have hzH2 : orderOf zH = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hcent : zH ∈ centralizer (generalizedFitting ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ Fs H := ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hFs hy')
    exact Subtype.ext this
  have hF : zH ∈ generalizedFitting ↥H := centralizer_generalizedFitting_le ↥H hcent
  have hFn : (generalizedFitting ↥H).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  let N : Subgroup ↥H := generalizedFitting ↥H ⊓ centralizer (generalizedFitting ↥H : Set ↥H)
  have hNn : N.Normal := Subgroup.normal_inf_normal _ _
  have hNc : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp b.2.2) (a : ↥H) a.2.1)⟩⟩
  have hzN : zH ∈ N := ⟨hF, hcent⟩
  let n₀ : ↥N := ⟨zH, hzN⟩
  have hn₀2 : orderOf n₀ = 2 := by rw [Subgroup.orderOf_mk]; exact hzH2
  have hP2 : IsPGroup 2 ↥(zpowers n₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hn₀2]; norm_num)
  obtain ⟨Pn, hPn⟩ := hP2.exists_le_sylow
  have hnil : Group.IsNilpotent ↥N := inferInstance
  have hmap := Sylow.map_le_pCore hNn hnil 2 Pn
  have hzP : zH ∈ Pn.map N.subtype := ⟨n₀, hPn (Subgroup.mem_zpowers n₀), rfl⟩
  exact ⟨zH, hmap hzP, rfl⟩

theorem cent_le_M (h181 : Prop18_1) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hctx : CtxP G z k S M p) {V : Subgroup G} (hVP : V ≤ Op p M)
    (hVel : IsElementaryAbelian p ↥V)
    (hVrk : ∀ v ∈ V, v ≠ 1 → 3 ≤ pRank p ↥(Op p M ⊓ centralizer ({v} : Set G))) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) : centralizer ({v} : Set G) ≤ M :=
  h181 G z k S M hctx.base p hctx.prime hctx.odd hctx.rank v (hVP hv)
    (orderOf_eq_of_elem hctx.prime hVel hv hv1) (hVrk v hv hv1)

theorem Fm_le_M (hAB : IG_11_7) (h1123 : IG_11_23) {z : G} {M H V : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hz2 : orderOf z = 2) (hM : M = centralizer ({z} : Set G))
    (hVP : V ≤ Op p M) (hVel : IsElementaryAbelian p ↥V) (hVnc : ¬ IsCyclic ↥V)
    (hCM : ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ M) (hzH : z ∈ H) (hVH : V ≤ H) :
    Fm H ≤ M := by
  have hVM : V ≤ M := hVP.trans (Op_le p M)
  refine Fm_le_of_forall fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp
    have hVne : V ≠ ⊥ := fun h => hVnc (by rw [h]; infer_instance)
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVne
    have hv : (a : G) ∈ V := a.2
    have hv1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    generalize (a : G) = v at hv hv1
    have hcop : Nat.Coprime q (Nat.card ↥(zpowers z)) := by
      rw [Nat.card_zpowers, hz2]
      exact (Nat.coprime_primes hq Nat.prime_two).mpr hp2
    have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ V, a * b = b * a := by
      intro a ha b hb
      have hzb : Commute z b := (Subgroup.mem_centralizer_singleton_iff.mp (hM ▸ hVM hb)).symm
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (hzb.zpow_left n).eq
    have hcent : zpowers z ≤
        centralizer ((Op q H ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
      have hxv : x ∈ centralizer ({(v : G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
      have hxM : x ∈ M := hCM v hv hv1 hxv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hM ▸ hxM)
    have key := hAB G q hq (zpowers z) V (Op q H) (isPGroup_Op q hq H)
      (IsElementaryAbelian.isPGroup q ↥V) hcop
      (Subgroup.zpowers_le.mpr (le_normalizer_Op q H hzH))
      (fun b hb => le_normalizer_Op q H (hVH hb)) hcomm hcent
    intro x hx
    rw [hM]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (key (Subgroup.mem_zpowers z)) x hx)
  · have : Fact q.Prime := ⟨hq⟩
    obtain ⟨V₀, hV₀V, hV₀el, hV₀card⟩ := exists_plane hp hVel hVnc
    have hcop : Nat.Coprime p (Nat.card ↥(Op q H)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp (isPGroup_Op q hq H)
      rw [hn]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
    have hnorm : V₀ ≤ normalizer (Op q H : Set G) :=
      fun v hv => le_normalizer_Op q H (hVH (hV₀V hv))
    have h := h1123 G p hp V₀ (Op q H) hV₀el hV₀card hcop hnorm
    exact h.trans (iSup_le fun v => iSup_le fun hv =>
      inf_le_right.trans (hCM v (hV₀V hv.1) hv.2))

omit [Finite G] in
theorem exists_comp_not_le {H M : Subgroup G} (hFs : ¬ Fs H ≤ M) (hFm : Fm H ≤ M) :
    ∃ J : Subgroup G, IsCompIn H J ∧ ¬ J ≤ M := by
  by_contra hcon
  push Not at hcon
  apply hFs
  rw [Fs_eq_sup]
  refine sup_le hFm ?_
  rw [Em_def, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hsub : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  exact hcon (K.map H.subtype) ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hK⟩

end Steps

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3
