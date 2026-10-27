module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cA
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump

public section

namespace CFSG.GH74.GLS.Th2.P72c

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Pump

variable {G : Type} [Group G] [Finite G]

theorem layer_le_mul_pPrimeCore {u z : G} {K J : Subgroup G}
    (hpump : PumpUpLT 2 u K z J) (htriv : IsTrivialPumpupAt u K z) :
    ∀ k ∈ pLayerOf 2 (K ⊓ centralizer ({z} : Set G)),
      ∃ j ∈ J, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({z} : Set G)), k = j * o := by
  have hpump' := hpump
  obtain ⟨⟨hxo, -, hKc⟩, ⟨hx'o, -, -⟩, hx'x, hx'K, hK'p⟩ := hpump
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover hx'o hKc hx'K
  have hΛY : Λ ≤ centralizer ({z} : Set G) := hΛX.trans inf_le_right
  have hxY : u ∈ centralizer ({z} : Set G) := mem_centralizer_symm hx'x
  set Y' := centralizer ({z} : Set G) with hY'
  have hso : orderOf (⟨u, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛlay hΛE hK'p
  have himg := (hiff _ hK'2).mp hK'J
  obtain ⟨hJn, ⟨eJK⟩⟩ := htriv J hpump'
  have hsn : (⟨u, hxY⟩ : ↥Y') ∈ normalizer ((J.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') := by
    rw [Subgroup.mem_normalizer_iff]
    intro j
    have h := (Subgroup.mem_normalizer_iff.mp hJn) (j : G)
    simp only [Subgroup.mem_subgroupOf]
    exact h
  have hvert : conjSub (barMk ↥Y' ⟨u, hxY⟩)⁻¹ L = L ∧
      (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L := by
    rcases hcases with h | ⟨hLs, hAB, hAD⟩
    · exact h
    · exfalso
      set s' := barMk ↥Y' ⟨u, hxY⟩ with hs'
      have hs'sq : s' * s' = 1 := by
        rw [hs', ← map_mul]
        have : (⟨u, hxY⟩ : ↥Y') * ⟨u, hxY⟩ = 1 := by
          apply Subtype.ext
          show u * u = 1
          rw [← pow_two]
          have := pow_orderOf_eq_one u
          rwa [hxo] at this
        rw [this, map_one]
      have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'sq
      set M := (J.subgroupOf Y').map (barMk ↥Y') with hM
      have hMinv : ∀ m ∈ M, s' * m * s'⁻¹ ∈ M := by
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (⟨u, hxY⟩ : ↥Y') * j * (⟨u, hxY⟩ : ↥Y')⁻¹ ∈ J.subgroupOf Y' := by
          have := (Subgroup.mem_normalizer_iff.mp hsn) j
          exact this.mp hj
        exact ⟨_, hj', by simp [hs', map_mul]⟩
      have hMc : conjSub s'⁻¹ M = M := by
        ext x
        rw [mem_conjSub_iff', inv_inv]
        constructor
        · intro hx
          have := hMinv _ hx
          have e : s' * (s' * x * s'⁻¹) * s'⁻¹ = x := by
            rw [hs'inv]
            calc s' * (s' * x * s') * s' = (s' * s') * x * (s' * s') := by group
              _ = x := by rw [hs'sq]; simp
          rwa [e] at this
        · intro hx
          exact hMinv x hx
      rcases himg with h | h
      · apply hLs
        rw [← h]
        exact hMc
      · apply hLs
        have e : s'⁻¹⁻¹ = s'⁻¹ := by rw [inv_inv, hs'inv]
        have h2 : conjSub s'⁻¹ (conjSub s'⁻¹ L) = L :=
          calc conjSub s'⁻¹ (conjSub s'⁻¹ L) = conjSub s'⁻¹ (conjSub s'⁻¹⁻¹ L) := by rw [e]
            _ = L := conjSub_conjSub_inv s'⁻¹ L
        calc conjSub s'⁻¹ L = M := h.symm
          _ = conjSub s'⁻¹ M := hMc.symm
          _ = conjSub s'⁻¹ (conjSub s'⁻¹ L) := by rw [← h]
          _ = L := h2
  obtain ⟨hvL, hvΛ⟩ := hvert
  have himgL : (J.subgroupOf Y').map (barMk ↥Y') = L := by
    rcases himg with h | h
    · exact h
    · rw [h, hvL]
  intro k hk
  rw [hΛlay] at hk
  have hkY : k ∈ Y' := hΛY hk
  have hmem : barMk ↥Y' ⟨k, hkY⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
    ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hmemL := hvΛ hmem
  rw [← himgL] at hmemL
  obtain ⟨j, hj, hjπ⟩ := hmemL
  have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hker : j⁻¹ * ⟨k, hkY⟩ ∈ (barMk ↥Y').ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjπ]
    simp
  rw [ker_barMk] at hker
  refine ⟨(j : G), hjJ, ((j⁻¹ * ⟨k, hkY⟩ : ↥Y') : G), ⟨_, hker, rfl⟩, ?_⟩
  simp

end Pump

section Group

variable {G : Type} [Group G]

theorem le_of_perfect_le_mul {J O K : Subgroup G}
    (hJO : ∀ j ∈ J, ∀ o ∈ O, j * o = o * j) (hO : Group.IsSolvable ↥O)
    (hKp : ⁅K, K⁆ = K) (hK : ∀ k ∈ K, ∃ j ∈ J, ∃ o ∈ O, k = j * o) : K ≤ J := by
  classical
  set H : Subgroup G := J ⊔ O with hH
  have hJH : J ≤ H := le_sup_left
  have hOH : O ≤ H := le_sup_right
  have hKH : K ≤ H := by
    intro k hk
    obtain ⟨j, hj, o, ho, rfl⟩ := hK k hk
    exact H.mul_mem (hJH hj) (hOH ho)
  have hfix : ∀ o ∈ O, ∀ w ∈ J, o * w * o⁻¹ = w := by
    intro o ho w hw
    have := hJO w hw o ho
    calc o * w * o⁻¹ = (o * w) * o⁻¹ := rfl
      _ = (w * o) * o⁻¹ := by rw [← this]
      _ = w := by group
  have hfix' : ∀ o ∈ O, ∀ w ∈ J, o⁻¹ * w * o = w := by
    intro o ho w hw
    have := hJO w hw o ho
    calc o⁻¹ * w * o = o⁻¹ * (w * o) := by group
      _ = o⁻¹ * (o * w) := by rw [this]
      _ = w := by group
  have hoN : ∀ o ∈ O, o ∈ normalizer (J : Set G) := by
    intro o ho
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hj => by rw [hfix o ho h hj]; exact hj, fun hj => ?_⟩
    have h1 := hfix' o ho _ hj
    have e : o⁻¹ * (o * h * o⁻¹) * o = h := by group
    rw [e] at h1
    rw [h1]
    exact hj
  have hHN : H ≤ normalizer (J : Set G) := sup_le Subgroup.le_normalizer hoN
  have hN : (J.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr hHN
  let f : ↥H →* ↥H ⧸ J.subgroupOf H := QuotientGroup.mk' _
  let g : ↥O →* ↥H ⧸ J.subgroupOf H := f.comp (Subgroup.inclusion hOH)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j, hj, o, ho, hjo⟩ := exists_mul_of_mem_sup_of_commute hJO h.2
    refine ⟨⟨o, ho⟩, ?_⟩
    show f (Subgroup.inclusion hOH ⟨o, ho⟩) = (QuotientGroup.mk h : ↥H ⧸ J.subgroupOf H)
    have h1 : h = ⟨j, hJH hj⟩ * Subgroup.inclusion hOH ⟨o, ho⟩ := Subtype.ext hjo
    have h2 : f ⟨j, hJH hj⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hj
    show f _ = f h
    rw [h1, map_mul, h2, one_mul]
  have hsolv : Group.IsSolvable (↥H ⧸ J.subgroupOf H) := Group.isSolvable_of_surjective hg
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have hK'p : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le hKH, hKp]
  have key : ∀ n, K'.map f ≤ derivedSeries (↥H ⧸ J.subgroupOf H) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc K'.map f = (⁅K', K'⁆).map f := by rw [hK'p]
        _ = ⁅K'.map f, K'.map f⁆ := Subgroup.map_commutator _ _ _
        _ ≤ ⁅derivedSeries (↥H ⧸ J.subgroupOf H) n, derivedSeries (↥H ⧸ J.subgroupOf H) n⁆ :=
          Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hbot : K'.map f = ⊥ := le_bot_iff.1 (by simpa [hn] using key n)
  intro k hk
  have hkH : k ∈ H := hKH hk
  have h1 : (⟨k, hkH⟩ : ↥H) ∈ K' := hk
  have h2 : f ⟨k, hkH⟩ = 1 := by
    have : f ⟨k, hkH⟩ ∈ K'.map f := ⟨_, h1, rfl⟩
    rw [hbot] at this
    simpa using this
  exact (QuotientGroup.eq_one_iff (⟨k, hkH⟩ : ↥H)).mp h2

theorem not_isSolvable_of_isQuasisimple {J : Subgroup G} (hJ : CFSG.IsQuasisimple ↥J) :
    ¬ Group.IsSolvable ↥J := by
  intro hsolv
  obtain ⟨-, hsimple, a, b, hab⟩ := hJ
  have hsolv' : Group.IsSolvable (↥J ⧸ center ↥J) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (center ↥J))
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv'
  exact hab (hcomm a b)

end Group

section Pump2

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_of_kBar {K J : Subgroup G} (hKJ : K ≤ J)
    (hJq : CFSG.IsQuasisimple ↥J) (e : Nonempty (kBar J ≃* kBar K)) : K = J := by
  classical
  obtain ⟨e⟩ := e
  set N : Subgroup ↥J := pPrimeCore 2 ↥J with hN
  let ψ : ↥K →* ↥J ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hKJ)
  have hkerN : ∀ x : ↥K, x ∈ ψ.ker ↔ Subgroup.inclusion hKJ x ∈ N := by
    intro x
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (Subgroup.inclusion hKJ x)
  have hkerle : ψ.ker ≤ pPrimeCore 2 ↥K := by
    have hcop : Nat.Coprime 2 (Nat.card ↥ψ.ker) := by
      have hmap : ψ.ker.map (Subgroup.inclusion hKJ) ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hkerN x).1 hx
      have h1 : Nat.card ↥(ψ.ker.map (Subgroup.inclusion hKJ)) ∣ Nat.card ↥N :=
        Subgroup.card_dvd_of_le hmap
      have h2 : Nat.card ↥(ψ.ker.map (Subgroup.inclusion hKJ)) = Nat.card ↥ψ.ker :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKJ)
      rw [h2] at h1
      exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
    exact le_sSup ⟨MonoidHom.normal_ker ψ, hcop⟩
  have hK1 : Nat.card ↥K = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hK2 : Nat.card ↥K = Nat.card (kBar K) * Nat.card ↥(pPrimeCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hKbar : Nat.card (↥J ⧸ N) = Nat.card (kBar K) := Nat.card_congr e.toEquiv
  have hle : Nat.card ↥ψ.ker ≤ Nat.card ↥(pPrimeCore 2 ↥K) := Subgroup.card_le_of_le hkerle
  have hkpos : 0 < Nat.card ↥ψ.ker := Nat.card_pos
  have hrange : Nat.card (↥J ⧸ N) ≤ Nat.card ↥ψ.range := by
    rw [hKbar]
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥ψ.range * Nat.card ↥ψ.ker < Nat.card (kBar K) * Nat.card ↥ψ.ker :=
      Nat.mul_lt_mul_of_pos_right hlt hkpos
    have h3 : Nat.card (kBar K) * Nat.card ↥ψ.ker ≤
        Nat.card (kBar K) * Nat.card ↥(pPrimeCore 2 ↥K) :=
      Nat.mul_le_mul_left _ hle
    omega
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_le_card ψ.range hrange
  have hdecomp : ∀ j ∈ J, ∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 J, j = k * o := by
    intro j hj
    have hmem : (QuotientGroup.mk (⟨j, hj⟩ : ↥J) : ↥J ⧸ N) ∈ ψ.range := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := hmem
    have hk' : (QuotientGroup.mk (Subgroup.inclusion hKJ k) : ↥J ⧸ N) =
        QuotientGroup.mk ⟨j, hj⟩ := hk
    have h1 : (Subgroup.inclusion hKJ k)⁻¹ * ⟨j, hj⟩ ∈ N := QuotientGroup.eq.1 hk'
    refine ⟨(k : G), k.2, (k : G)⁻¹ * j, ⟨_, h1, rfl⟩, ?_⟩
    simp
  have hOJ : ∀ k ∈ K, ∀ o ∈ pPrimeCoreOf 2 J, k * o = o * k := fun k hk o ho =>
    (commute_of_mem_pPrimeCoreOf hJq ho (hKJ hk)).symm
  have hsolv : Group.IsSolvable ↥(pPrimeCoreOf 2 J) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (TwoThin.card_pPrimeCoreOf_odd J)
  have hperf : ⁅J, J⁆ = J := commutator_self_of_perfect' J hJq.1
  exact le_antisymm hKJ (le_of_perfect_le_mul hOJ hsolv hperf hdecomp)

omit [Finite G] in
theorem isCompIn_of_isPCompIn_qs {X J : Subgroup G} (hJ : IsPCompIn 2 X J)
    (hq : CFSG.IsQuasisimple ↥J) : IsCompIn X J := by
  have hsub : (J.subgroupOf X).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hJ).2.1 Subgroup.IsSubnormal.top
  exact ⟨hJ.1, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hJ.1).symm hq, hsub⟩

theorem eq_pumpup_of_quasisimple {u z : G} {K J : Subgroup G}
    (hKc : IsPCompIn 2 (centralizer ({u} : Set G)) K) (hKq : CFSG.IsQuasisimple ↥K)
    (hzK : z ∈ centralizerSection K (pPrimeCoreOf 2 K))
    (hpump : PumpUpLT 2 u K z J) (htriv : IsTrivialPumpupAt u K z) (hJq : CFSG.IsQuasisimple ↥J) :
    K = J := by
  have hKz : K ≤ centralizer ({z} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.2 (commute_of_mem_cSec hKq hzK k hk).symm
  have hKK : IsPCompIn 2 K K := C3.Layer1.Bk.isPCompIn_of_le hKc le_rfl hKc.1
  have hKlay : K ≤ pLayerOf 2 (K ⊓ centralizer ({z} : Set G)) := by
    rw [inf_eq_left.2 hKz]
    exact le_sSup hKK
  have hcov := layer_le_mul_pPrimeCore hpump htriv
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hpump.2.1.2.2
  have hJcomp : IsCompIn (centralizer ({z} : Set G)) J := isCompIn_of_isPCompIn_qs hJc hJq
  have hNn : ((pPrimeCoreOf 2 (centralizer ({z} : Set G))).subgroupOf
      (centralizer ({z} : Set G))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := TwoThin.pPrimeCoreOf_normalized (centralizer ({z} : Set G)) g.2 hn
    simpa using this⟩
  have hJO : ∀ j ∈ J, ∀ o ∈ pPrimeCoreOf 2 (centralizer ({z} : Set G)), j * o = o * j := by
    rcases CFSG.LocalCores.component_normal_subgroup hJcomp.2 hNn with hle | hcomm
    · exfalso
      have hJO' : J ≤ pPrimeCoreOf 2 (centralizer ({z} : Set G)) := by
        intro k' hk'
        have : (⟨k', hJc.1 hk'⟩ : ↥(centralizer ({z} : Set G))) ∈
            J.subgroupOf (centralizer ({z} : Set G)) := hk'
        exact hle this
      have hodd : Odd (Nat.card ↥J) :=
        Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({z} : Set G)))
          (Subgroup.card_dvd_of_le hJO')
      exact not_isSolvable_of_isQuasisimple hJq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    · intro j hj o ho
      have hmem : ⁅(⟨j, hJc.1 hj⟩ : ↥(centralizer ({z} : Set G))),
          (⟨o, TwoThin.pPrimeCoreOf_le _ ho⟩ : ↥(centralizer ({z} : Set G)))⁆ ∈
          ⁅J.subgroupOf (centralizer ({z} : Set G)),
            (pPrimeCoreOf 2 (centralizer ({z} : Set G))).subgroupOf
              (centralizer ({z} : Set G))⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.2 hj)
          (Subgroup.mem_subgroupOf.2 ho)
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hmem)
  have hsolv : Group.IsSolvable ↥(pPrimeCoreOf 2 (centralizer ({z} : Set G))) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (TwoThin.card_pPrimeCoreOf_odd _)
  have hKperf : ⁅K, K⁆ = K := commutator_self_of_perfect' K hKq.1
  have hKJ : K ≤ J :=
    le_of_perfect_le_mul hJO hsolv hKperf (fun k hk => hcov k (hKlay hk))
  obtain ⟨-, ⟨e⟩⟩ := htriv J hpump
  exact eq_of_le_of_kBar hKJ hJq ⟨e⟩

end Pump2

end CFSG.GH74.GLS.Th2.P72c

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P72c

section Std

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.exists_nonqs_pumpup (h : Th2Std x y K T S)
    (hnt : ¬ IsTerminalPair 2 x K)
    (hR : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 →
      3 ≤ pRank 2 ↥(centralizer ({u} : Set G))) :
    ∃ t ∈ T ⊓ CxK x K, orderOf t = 2 ∧ ∃ J : Subgroup G, PumpUpLT 2 x K t J ∧
      ¬ CFSG.IsQuasisimple ↥J := by
  by_contra hcon
  push Not at hcon
  apply hnt
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hILo : IsILo 2 x K := hterm.1
  obtain ⟨hpumpx, hKK⟩ := pumpUp_eq_self h.K_le_C h.comp
  have hP0 : PumpUpLT 2 x K x K :=
    ⟨hILo, hILo, mem_centralizer_singleton_iff.2 rfl, h.x_mem_CxK.2, by rw [hpumpx]; exact hKK⟩
  have hKq : CFSG.IsQuasisimple ↥K := hcon x hxQ h.orderOf_x K hP0
  have hev : 2 ∣ Nat.card ↥K := by
    by_contra hne
    have hodd : Odd (Nat.card ↥K) := by
      rcases Nat.even_or_odd (Nat.card ↥K) with he | ho
      · exact absurd (even_iff_two_dvd.1 he) hne
      · exact ho
    exact not_isSolvable_of_isQuasisimple hKq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hcomp : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 → IsCompIn (centralizer ({u} : Set G)) K := by
    intro u hu hu2
    have hrank := hR u hu hu2
    obtain ⟨J, hJ⟩ := TwoThin.exists_pumpup_of_involution h.orderOf_x hu2 h.comp hu.2.1 hu.2.2 hILo hrank
    have hJq := hcon u hu hu2 J hJ
    have htriv : IsTrivialPumpupAt x K u := fun K' hK' => hterm.2.1 u K' hK'
    have hKJ : K = J := eq_pumpup_of_quasisimple h.comp hKq hu.2.2 hJ htriv hJq
    rw [hKJ]
    exact isCompIn_of_isPCompIn_qs hJ.2.1.2.2 hJq
  exact isTerminalPair_of_comp_Q h hev (sylow_Q_centralizer_of_comp hR h hKq hev hcomp)
    hcomp

end Std

end CFSG.GH74.GLS
