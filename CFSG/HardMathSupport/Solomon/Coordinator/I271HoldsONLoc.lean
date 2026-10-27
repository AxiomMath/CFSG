module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsONGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Final

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple CFSG.Open Subgroup
open scoped commutatorElement

section


theorem i271on_conj_zpow_zG (n : GM) (i : ℤ) : n * zG ^ i * n⁻¹ = zG ^ i := by
  have h : zG ^ i * n = n * zG ^ i := ((show Commute zG n from zG_central n).zpow_left i).eq
  rw [← h, mul_inv_cancel_right]

theorem i271on_orderOf_q {S : Type*} [Group S] {q : GM →* S} (hker : q.ker = zpowers zG) {a : GM}
    (ha3 : a ^ 3 = 1) (haz : a ∉ zpowers zG) : orderOf (q a) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ha3, map_one]
  · intro h
    apply haz
    rw [← hker]
    exact h

theorem i271on_local {S : Type} [Group S] [Finite S] (q : GM →* S) (hq : Function.Surjective q)
    (hker : q.ker = zpowers zG) {W : Subgroup S} (hW : IsElemAbelian 3 W) (h81 : 81 ≤ Nat.card W)
    {a : GM} {A₀ : Subgroup GM} (hA₀ : CFSG.RankThree.PartTwo.Late.IsE27 A₀) (ha : a ∈ A₀)
    (haz : a ∉ zpowers zG) (hax : q a ∈ W) :
    ∃ H : Subgroup S, Nonempty (H ≃* alternatingGroup (Fin 6)) ∧
      H ≤ Subgroup.centralizer ({q a} : Set S) ∧
      (∀ c ∈ Subgroup.centralizer ({q a} : Set S), Nat.Coprime 3 (orderOf c) → c ∈ H) ∧
      Nat.card (Subgroup.centralizer ({q a} : Set S)) ≤ 3240 ∧
      ∃ E ≤ W ⊓ H, 9 ≤ Nat.card E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : orderOf zG = 3 := orderOf_eq_prime relG.xcube relG.x1
  have hZ : Nat.card (zpowers zG) = 3 := on25_card_zG
  have hZc : zpowers zG ≤ center GM := by rw [center_GM]
  have hker3 : Nat.card q.ker = 3 := by rw [hker]; exact hZ
  have ha3 : a ^ 3 = 1 := hA₀.1.2 a ha
  have ha1 : a ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have ha3' : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  obtain ⟨n, hC, hdisj⟩ := on25_exists_conj hA₀ ha haz
  set K : Subgroup GM := K0G.map (MulAut.conj n).toMonoidHom with hKdef
  have hKC : K ≤ Subgroup.centralizer ({a} : Set GM) := by rw [hC]; exact le_sup_right
  have hzK : zG ∈ K := on25_z_mem_K n
  have hKcard : Nat.card K = 1080 := on25_card_K n
  have hkerK : q.ker ≤ K := by rw [hker]; exact Subgroup.zpowers_le.2 hzK
  have hconjZ : ∀ g : GM, n * g * n⁻¹ ∈ zpowers zG ↔ g ∈ zpowers zG := by
    intro g
    constructor
    · intro hg
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hg
      have h2 : g = zG ^ i := by
        have : n * g * n⁻¹ = n * zG ^ i * n⁻¹ := by rw [i271on_conj_zpow_zG, hi]
        simpa using this
      rw [h2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zG) i
    · intro hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [i271on_conj_zpow_zG]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zG) i
  let ψ : ↥K0G →* S := (q.comp (MulAut.conj n).toMonoidHom).comp K0G.subtype
  have hψr : ψ.range = K.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hKdef, Subgroup.map_map]
  have hψk : ψ.ker = actK.ker := by
    rw [ker_actK]
    ext k
    rw [MonoidHom.mem_ker]
    show q (n * (k : GM) * n⁻¹) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, hconjZ]
    constructor
    · intro hk
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact Subgroup.mem_zpowers_iff.2 ⟨i, Subtype.ext (by simpa using hi)⟩
    · intro hk
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
  let e : (K.map q) ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hψr.symm).trans
      (((QuotientGroup.quotientKerEquivRange ψ).symm).trans
        ((QuotientGroup.quotientMulEquivOfEq hψk).trans
          ((QuotientGroup.quotientKerEquivRange actK).trans
            (MulEquiv.subgroupCongr range_actK))))
  have hHC : K.map q ≤ Subgroup.centralizer ({q a} : Set S) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
    rw [this]
  have hcomm_ker : ∀ m : GM, q m ∈ Subgroup.centralizer ({q a} : Set S) → ⁅m, a⁆ ∈ zpowers zG := by
    intro m hm
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 hm)
  have hCMa : Nat.card (Subgroup.centralizer ({a} : Set GM)) ≤ 3240 := by
    rw [hC]
    have := i271on_card_sup_le ha3 hKC
    omega
  have hCS : Nat.card (Subgroup.centralizer ({q a} : Set S)) ≤ 3240 := by
    set N : Subgroup GM := (Subgroup.centralizer ({q a} : Set S)).comap q with hN
    have hN1 : Nat.card N = Nat.card (Subgroup.centralizer ({q a} : Set S)) * 3 := by
      rw [hN, on25_card_comap q hq _, hker3]
    have hN2 := i271on_card_le_comm hZc a N (fun m hm => hcomm_ker m hm)
    have hN3 : Nat.card ↥(N ⊓ Subgroup.centralizer ({a} : Set GM)) ≤ 3240 :=
      (Subgroup.card_le_of_le inf_le_right).trans hCMa
    rw [hZ] at hN2
    omega
  have hL2 : ∀ c ∈ Subgroup.centralizer ({q a} : Set S), Nat.Coprime 3 (orderOf c) →
      c ∈ K.map q := by
    intro c hc hcop
    obtain ⟨m, rfl⟩ := hq c
    set s := orderOf (q m) with hs
    set N : Subgroup GM := (Subgroup.centralizer ({q a} : Set S)).comap q with hN
    have hmN : m ∈ N := hc
    let φ := i271onCommHom hZc a N (fun m hm => hcomm_ker m hm)
    have hms : m ^ s ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact pow_orderOf_eq_one _
    have h1 : φ ⟨m, hmN⟩ ^ s = 1 := by
      rw [← map_pow]
      apply Subtype.ext
      rw [i271onCommHom_apply]
      have hcen : m ^ s ∈ center GM := hZc (hker ▸ hms)
      have : (((⟨m, hmN⟩ : ↥N) ^ s : ↥N) : GM) = m ^ s := rfl
      rw [this]
      exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hcen a).symm
    have h2 : φ ⟨m, hmN⟩ ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(zpowers zG)) (x := φ ⟨m, hmN⟩)
      rwa [hZ] at this
    have h3 : φ ⟨m, hmN⟩ = 1 := by
      have := pow_gcd_eq_one.2 ⟨h2, h1⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have h4 : ⁅m, a⁆ = 1 := by
      have := congrArg Subtype.val h3
      rw [i271onCommHom_apply] at this
      simpa using this
    have hmC : m ∈ Subgroup.centralizer ({a} : Set GM) :=
      Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h4)
    rw [hC] at hmC
    obtain ⟨i, k, hk, rfl⟩ := i271on_mem_sup_fin3 ha3 hKC hmC
    have hcommk : Commute (a ^ (i : ℕ)) k := by
      have h : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
      exact ((show Commute k a from h).pow_right (i : ℕ)).symm
    have hpow : (a ^ (i : ℕ) * k) ^ s = a ^ ((i : ℕ) * s) * k ^ s := by
      rw [hcommk.mul_pow, ← pow_mul]
    have hmK : a ^ ((i : ℕ) * s) * k ^ s ∈ K := by
      rw [← hpow]
      exact hkerK hms
    have hak : a ^ ((i : ℕ) * s) ∈ zpowers a ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _, ?_⟩
      have := K.mul_mem hmK (K.inv_mem (K.pow_mem hk s))
      simpa using this
    rw [hdisj, Subgroup.mem_bot] at hak
    have hdvd : 3 ∣ (i : ℕ) * s := by
      have h := orderOf_dvd_of_pow_eq_one hak
      rwa [ha3'] at h
    have hdi : 3 ∣ (i : ℕ) := hcop.dvd_of_dvd_mul_right hdvd
    have hi0 : (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdi i.2
    rw [hi0, pow_zero, one_mul]
    exact ⟨k, hk, rfl⟩
  set P : Subgroup GM := W.comap q with hP
  have haP : a ∈ P := hax
  have hPcard : Nat.card P = Nat.card W * 3 := by
    rw [hP, on25_card_comap q hq W, hker3]
  have hUP : ∀ m ∈ P, ⁅m, a⁆ ∈ zpowers zG := by
    intro m hm
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    have hc := congrArg Subtype.val (hW.1.is_comm.comm (⟨q m, hm⟩ : ↥W) ⟨q a, hax⟩)
    exact commutatorElement_eq_one_iff_mul_comm.2 (by simpa using hc)
  have hP1 := i271on_card_le_comm hZc a P hUP
  rw [hC, hZ] at hP1
  have hP2 := i271on_card_inf_le ha3 hKC haP
  set Y : Subgroup GM := K ⊓ P with hY
  have hkerY : q.ker ≤ Y := by
    refine le_inf hkerK ?_
    intro g hg
    rw [hP, Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
    exact W.one_mem
  have hYcard : Nat.card Y = Nat.card (Y.map q) * 3 := by
    have h := on25_card_comap q hq (Y.map q)
    rw [Subgroup.comap_map_eq, sup_eq_left.2 hkerY, hker3] at h
    exact h
  refine ⟨K.map q, ⟨e⟩, hHC, hL2, hCS, Y.map q, ?_, ?_⟩
  · refine le_inf ?_ (Subgroup.map_mono inf_le_left)
    rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_right
  · omega

theorem i271on_good_lifts {S : Type} [Group S] [Finite S] (q : GM →* S) (hq : Function.Surjective q)
    (hker : q.ker = zpowers zG) {W : Subgroup S} (hW : IsElemAbelian 3 W) (h81 : 81 ≤ Nat.card W) :
    ∃ Ab : Subgroup S, Ab ≤ W ∧ Nat.card Ab = 9 ∧ ∀ x ∈ Ab, x ≠ 1 →
      ∃ (a : GM) (A₀ : Subgroup GM), CFSG.RankThree.PartTwo.Late.IsE27 A₀ ∧ a ∈ A₀ ∧
        a ∉ zpowers zG ∧ q a = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker3 : Nat.card q.ker = 3 := by rw [hker]; exact on25_card_zG
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hW.isPGroup
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : Nat.card W ≤ 3 ^ 3 := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card W := by
    rw [hk]
    exact pow_dvd_pow 3 (by omega)
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W) 3 hdvd
  set W' : Subgroup S := V.map W.subtype with hW'
  have hW'27 : Nat.card W' = 27 := by
    rw [hW', Subgroup.card_map_of_injective W.subtype_injective, hV]
    norm_num
  have hW'W : W' ≤ W := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  set U : Subgroup GM := W'.comap q with hU
  have hU81 : Nat.card U = 81 := by
    rw [hU, on25_card_comap q hq W', hker3, hW'27]
  obtain ⟨A₀, hA₀U, hA₀⟩ := on25_exists_E27 hU81
  have hzA : zG ∈ A₀ := on25_E27_contains_z hA₀
  have hkerA : q.ker ≤ A₀ := by rw [hker]; exact Subgroup.zpowers_le.2 hzA
  have hAcard : Nat.card A₀ = Nat.card (A₀.map q) * 3 := by
    have h := on25_card_comap q hq (A₀.map q)
    rw [Subgroup.comap_map_eq, sup_eq_left.2 hkerA, hker3] at h
    exact h
  refine ⟨A₀.map q, ?_, ?_, ?_⟩
  · refine le_trans ?_ hW'W
    rw [Subgroup.map_le_iff_le_comap]
    exact hA₀U
  · have := hA₀.2
    omega
  · intro x hx hx1
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨a, A₀, hA₀, ha, ?_, rfl⟩
    intro haz
    apply hx1
    rw [← MonoidHom.mem_ker, hker]
    exact haz

end

end CFSG.HardMathSupport.Solomon.Coordinator
