module

public import CFSG.ClassicalInvolution.Q3.Sec13EndHyp
import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTwelve
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.Sec13StarBasic
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem perpP_isPGroup (h : EndHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) : IsPGroup 2 L :=
  IsPGroup.of_card (p := 2) (n := 3) (by norm_num [h.card_eq_eight hL])

theorem perpP_inf_normalizer (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) :
    IsCyclic ↥(J ⊓ Subgroup.normalizer (K : Set G)) ∧
      Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) = 4 := by
  have hΩ := h.thmD.hyp
  obtain ⟨hJΩ, hne, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R, -, J', hJ', hRJ', -, hcU, hcardR, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hR8 : Nat.card ↥R ≤ 8 := by
    have h1 := Subgroup.card_le_of_le hRJ'.1
    rwa [h.card_eq_eight hJ'] at h1
  have hU4 : Nat.card ↥U = 4 := by omega
  have hJ8 : Nat.card ↥J = 8 := h.card_eq_eight hJΩ
  have hUH : U ≤ J ⊓ Subgroup.normalizer (K : Set G) := le_inf hUJ hUN
  rcases CFSG.ClassicalInvolution.Asc77.eq_or_eq_of_natCard_eq_two_mul hUH inf_le_left
    (by omega) with hEq | hEq
  · rw [hEq]
    exact ⟨hcU, hU4⟩
  · exfalso
    apply hJn
    refine (TC.mem_omegaNbr_iff hΩ (fun L hL => perpP_isPGroup h hL)).mpr ⟨hJΩ, hne, ?_⟩
    intro x hx
    have hxJN : x ∈ J ⊓ Subgroup.normalizer (K : Set G) := by
      rw [hEq]
      exact hx
    exact hxJN.2

theorem perpP_inf_bot (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hJn : J ∉ omegaNbr Ω K) : K ⊓ J = ⊥ := by
  have hΩ := h.thmD.hyp
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  by_contra hne
  have hdvd8 : Nat.card ↥(K ⊓ J) ∣ 2 ^ 3 := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : K ⊓ J ≤ K)
    rw [h.card_eq_eight hK] at h1
    norm_num
    exact h1
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd8
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso
      apply hne
      rw [h0, pow_zero] at hi
      exact Subgroup.card_eq_one.mp hi
    · rw [hi]
      exact dvd_pow_self 2 hpos.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hy2 : orderOf (y : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hy
  have hyK : (y : G) ∈ K := (Subgroup.mem_inf.mp y.2).1
  have hyJ : (y : G) ∈ J := (Subgroup.mem_inf.mp y.2).2
  have hsq : (y : G) * (y : G) = 1 := by
    have h1 := pow_orderOf_eq_one (y : G)
    rw [hy2, pow_two] at h1
    exact h1
  have hne1 : (y : G) ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hy2
    norm_num at hy2
  have hzy : (y : G) = z := (hz.unique _ hyK hsq).resolve_left hne1
  have hjy : (y : G) = j := (hj.unique _ hyJ hsq).resolve_left hne1
  have hzj : z = j := hzy.symm.trans hjy
  have hJz : IsUniqueInvolution J z := by
    rw [hzj]
    exact hj
  have hcomm := TC.Thin.twin_comm hΩ (fun L hL => perpP_isPGroup h hL) hK hJ hKJ hz hJz
  have hfix : ∀ g ∈ J, ∀ m ∈ K, g * m * g⁻¹ = m := by
    intro g hg m hm
    calc g * m * g⁻¹ = m * g * g⁻¹ := by rw [hcomm m hm g hg]
      _ = m := by group
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hfix g hg n hn]
      exact hn
    · intro hn
      have e := hfix g⁻¹ (J.inv_mem hg) (g * n * g⁻¹) hn
      have e2 : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [e2] at e
      rw [e]
      exact hn
  exact hJn ((TC.mem_omegaNbr_iff hΩ (fun L hL => perpP_isPGroup h hL)).mpr
    ⟨hJ, hKJ.symm, hJN⟩)

theorem perpP_comm_of_inf_bot {K J : Subgroup G} (hbot : K ⊓ J = ⊥) {u v : G}
    (hu : u ∈ K ⊓ Subgroup.normalizer (J : Set G))
    (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) : u * v = v * u := by
  have hmemK : u * v * u⁻¹ * v⁻¹ ∈ K := by
    have h1 : v * u * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hv.2 u).mp hu.1
    have h2 : u * (v * u * v⁻¹)⁻¹ ∈ K := K.mul_mem hu.1 (K.inv_mem h1)
    have e : u * v * u⁻¹ * v⁻¹ = u * (v * u * v⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  have hmemJ : u * v * u⁻¹ * v⁻¹ ∈ J := by
    have h1 : u * v * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hu.2 v).mp hv.1
    exact J.mul_mem h1 (J.inv_mem hv.1)
  have hc : u * v * u⁻¹ * v⁻¹ = 1 := by
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ K ⊓ J := Subgroup.mem_inf.mpr ⟨hmemK, hmemJ⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    _ = v * u := by rw [hc, one_mul]

theorem perpP_coset {J V : Subgroup G} (hVJ : V ≤ J) (hJ8 : Nat.card ↥J = 8)
    (hV4 : Nat.card ↥V = 4) {x y : G} (hx : x ∈ J) (hxV : x ∉ V) (hy : y ∈ J) (hyV : y ∉ V) :
    x * y⁻¹ ∈ V := by
  have hrel : V.relIndex J = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := J)
    rw [inf_eq_left.mpr hVJ, hV4, hJ8] at h1
    omega
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp hrel
  have hxa : x * a ∈ V := by
    rcases ha x hx with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 hxV
  have hya : y * a ∈ V := by
    rcases ha y hy with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 hyV
  have e : x * y⁻¹ = (x * a) * (y * a)⁻¹ := by group
  rw [e]
  exact V.mul_mem hxa (V.inv_mem hya)

theorem perpP_exists_gen {U : Subgroup G} (hc : IsCyclic ↥U) :
    ∃ u ∈ U, U ≤ Subgroup.zpowers u := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := ↥U)
  refine ⟨g₀, g₀.2, fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨a, ha⟩)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 := congrArg Subtype.val hk
  rw [Subgroup.coe_zpow] at h1
  exact h1

theorem perpP_le_normalizer_sup {J U V : Subgroup G} (hJ8 : Nat.card ↥J = 8)
    (hUN : U ≤ Subgroup.normalizer (J : Set G)) (hcU : IsCyclic ↥U)
    (hVJ : V ≤ J) (hV4 : Nat.card ↥V = 4)
    (hcomm : ∀ a ∈ U, ∀ b ∈ V, a * b = b * a) :
    J ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := by
  have hcos : ∀ x ∈ J, x ∉ V → ∀ y ∈ J, y ∉ V → x * y⁻¹ ∈ V :=
    fun x hx hxV y hy hyV => perpP_coset hVJ hJ8 hV4 hx hxV hy hyV
  have hVn : ∀ g ∈ J, ∀ n ∈ V, g * n * g⁻¹ ∈ V := by
    intro g hg n hn
    by_cases hgV : g ∈ V
    · exact V.mul_mem (V.mul_mem hgV hn) (V.inv_mem hgV)
    · have hgn : g * n ∈ J := J.mul_mem hg (hVJ hn)
      have hgnV : g * n ∉ V := fun h' => hgV (by
        have h2 := V.mul_mem h' (V.inv_mem hn)
        simpa using h2)
      exact hcos (g * n) hgn hgnV g hg hgV
  obtain ⟨u, huU, hUle⟩ := perpP_exists_gen hcU
  have hC2 : ∀ s ∈ J, s ∉ V → s⁻¹ * u * s ∈ U ⊔ V := by
    intro s hs hsV
    have huN' : u⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
      (Subgroup.normalizer (J : Set G)).inv_mem (hUN huU)
    have hs' : u⁻¹ * s * u ∈ J := by
      have h1 := (Subgroup.mem_normalizer_iff.mp huN' s).mp hs
      rwa [inv_inv] at h1
    have hs'V : u⁻¹ * s * u ∉ V := by
      intro h'
      apply hsV
      have hc := hcomm u huU _ h'
      have e1 : u * (u⁻¹ * s * u) * u⁻¹ = s := by group
      have e2 : u * (u⁻¹ * s * u) * u⁻¹ = u⁻¹ * s * u := by
        rw [hc]
        group
      have hss : s = u⁻¹ * s * u := e1.symm.trans e2
      rw [hss]
      exact h'
    have hw : (u⁻¹ * s * u) * s⁻¹ ∈ V := hcos _ hs' hs'V s hs hsV
    obtain ⟨w, hwdef⟩ : ∃ w, w = (u⁻¹ * s * u) * s⁻¹ := ⟨_, rfl⟩
    rw [← hwdef] at hw
    have hws : u⁻¹ * s * u = w * s := by
      rw [hwdef]
      group
    have hsu : s * u = u * (w * s) := by
      rw [← hws]
      group
    have hsus : s * u * s⁻¹ = u * w := by
      rw [hsu]
      group
    have key : s⁻¹ * u * s = u * (s⁻¹ * w⁻¹ * s) := by
      calc s⁻¹ * u * s = s⁻¹ * (u * s) := by group
        _ = s⁻¹ * (s * u * s⁻¹ * w⁻¹ * s) := by
          rw [hsus]
          group
        _ = u * (s⁻¹ * w⁻¹ * s) := by group
    have hw' : s⁻¹ * w⁻¹ * s ∈ V := by
      have h1 := hVn s⁻¹ (J.inv_mem hs) w⁻¹ (V.inv_mem hw)
      rwa [inv_inv] at h1
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huU) (Subgroup.mem_sup_right hw')
  have hQ : ∀ g ∈ J, ∀ n ∈ U ⊔ V, g⁻¹ * n * g ∈ U ⊔ V := by
    intro g hg
    have hgu : g⁻¹ * u * g ∈ U ⊔ V := by
      by_cases hgV : g ∈ V
      · have e : g⁻¹ * u * g = u := by
          have hc := hcomm u huU g hgV
          calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
            _ = g⁻¹ * (g * u) := by rw [hc]
            _ = u := by group
        rw [e]
        exact Subgroup.mem_sup_left huU
      · exact hC2 g hg hgV
    have hUY : U ≤ (U ⊔ V).comap (MulAut.conj g⁻¹).toMonoidHom := by
      intro a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hUle ha)
      have huY : u ∈ (U ⊔ V).comap (MulAut.conj g⁻¹).toMonoidHom := by
        rw [Subgroup.mem_comap]
        simpa [MulAut.conj_apply] using hgu
      rw [← hk]
      exact Subgroup.zpow_mem _ huY k
    have hVY : V ≤ (U ⊔ V).comap (MulAut.conj g⁻¹).toMonoidHom := by
      intro b hb
      rw [Subgroup.mem_comap]
      have h1 := hVn g⁻¹ (J.inv_mem hg) b hb
      rw [inv_inv] at h1
      simpa [MulAut.conj_apply] using Subgroup.mem_sup_right h1
    have hXY : U ⊔ V ≤ (U ⊔ V).comap (MulAut.conj g⁻¹).toMonoidHom := sup_le hUY hVY
    intro n hn
    have h1 := hXY hn
    rw [Subgroup.mem_comap] at h1
    simpa [MulAut.conj_apply] using h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h1 := hQ g⁻¹ (J.inv_mem hg) n hn
    rwa [inv_inv] at h1
  · intro hn
    have h1 := hQ g hg (g * n * g⁻¹) hn
    have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
    rwa [e] at h1

theorem pair_structure (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) :
    IsCyclic ↥(K ⊓ Subgroup.normalizer (J : Set G)) ∧
    Nat.card ↥(K ⊓ Subgroup.normalizer (J : Set G)) = 4 ∧
    IsCyclic ↥(J ⊓ Subgroup.normalizer (K : Set G)) ∧
    Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) = 4 ∧
    (∀ u ∈ K ⊓ Subgroup.normalizer (J : Set G), ∀ v ∈ J ⊓ Subgroup.normalizer (K : Set G),
      u * v = v * u) ∧
    K ⊔ J ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) :
        Subgroup G) : Set G) := by
  have hΩ := h.thmD.hyp
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  have hJ' : K ∈ omegaStarNbr Ω J := Q3T6.Mu.omegaStarNbr_symm hΩ hK hJΩ hJ
  have hJn' : K ∉ omegaNbr Ω J := fun hK' =>
    hJn (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJΩ hK hK')
  obtain ⟨hcU, hU4⟩ := perpP_inf_normalizer h hK hJ hJn
  obtain ⟨hcU', hU4'⟩ := perpP_inf_normalizer h hJΩ hJ' hJn'
  have hbot : K ⊓ J = ⊥ := perpP_inf_bot h hK hJΩ hKJ hJn
  have hJ8 : Nat.card ↥J = 8 := h.card_eq_eight hJΩ
  have hK8 : Nat.card ↥K = 8 := h.card_eq_eight hK
  have hcomm : ∀ a ∈ K ⊓ Subgroup.normalizer (J : Set G),
      ∀ b ∈ J ⊓ Subgroup.normalizer (K : Set G), a * b = b * a :=
    fun a ha b hb => perpP_comm_of_inf_bot hbot ha hb
  have hcomm' : ∀ a ∈ J ⊓ Subgroup.normalizer (K : Set G),
      ∀ b ∈ K ⊓ Subgroup.normalizer (J : Set G), a * b = b * a :=
    fun a ha b hb => (perpP_comm_of_inf_bot hbot hb ha).symm
  have hJle : J ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) :
        Subgroup G) : Set G) :=
    perpP_le_normalizer_sup hJ8 inf_le_right hcU' inf_le_left hU4 hcomm
  have hKle : K ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) :
        Subgroup G) : Set G) := by
    rw [sup_comm]
    exact perpP_le_normalizer_sup hK8 inf_le_right hcU inf_le_left hU4' hcomm'
  exact ⟨hcU', hU4', hcU, hU4, hcomm, sup_le hKle hJle⟩

theorem perpP_gen {U : Subgroup G} (hc : IsCyclic ↥U) (h4 : Nat.card ↥U = 4) :
    ∃ u ∈ U, orderOf u = 4 ∧ U ≤ Subgroup.zpowers u := by
  obtain ⟨u, huU, hle⟩ := perpP_exists_gen hc
  refine ⟨u, huU, ?_, hle⟩
  have h1 : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.mpr huU
  have heq : U = Subgroup.zpowers u := le_antisymm hle h1
  have h2 : Nat.card ↥(Subgroup.zpowers u) = 4 := by
    rw [← heq]
    exact h4
  rw [Nat.card_zpowers] at h2
  exact h2

open scoped Pointwise in
theorem perpP_mem_sup {U V : Subgroup G} (hcomm : ∀ a ∈ U, ∀ b ∈ V, a * b = b * a) {x : G}
    (hx : x ∈ U ⊔ V) : ∃ a ∈ U, ∃ b ∈ V, a * b = x := by
  have hN : U ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have e : a * n * a⁻¹ = n := by
        rw [hcomm a ha n hn]
        group
      rw [e]
      exact hn
    · intro hm
      have hc := hcomm a⁻¹ (U.inv_mem ha) (a * n * a⁻¹) hm
      have e : n = a * n * a⁻¹ := by
        calc n = a⁻¹ * (a * n * a⁻¹) * a := by group
          _ = (a * n * a⁻¹) * a⁻¹ * a := by rw [hc]
          _ = a * n * a⁻¹ := by group
      rw [e]
      exact hm
  have hx' : x ∈ (U : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right U V hN]
    exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, hab⟩

theorem perpP_conj_eq {J : Subgroup G} {j t : G} (hj : IsUniqueInvolution J j) (ht : t ∈ J) :
    t * j * t⁻¹ = j := by
  have hmem : t * j * t⁻¹ ∈ J := J.mul_mem (J.mul_mem ht hj.mem) (J.inv_mem ht)
  have hsq : t * j * t⁻¹ * (t * j * t⁻¹) = 1 := by
    calc t * j * t⁻¹ * (t * j * t⁻¹) = t * (j * j) * t⁻¹ := by group
      _ = 1 := by
        rw [hj.sq]
        group
  have hne : t * j * t⁻¹ ≠ 1 := by
    intro e
    apply hj.ne_one
    calc j = t⁻¹ * (t * j * t⁻¹) * t := by group
      _ = 1 := by
        rw [e]
        group
  exact (hj.unique _ hmem hsq).resolve_left hne

theorem perpP_conj_ne_one {z t : G} (hz : z ≠ 1) : t * z * t⁻¹ ≠ 1 := by
  intro e
  apply hz
  calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
    _ = 1 := by
      rw [e]
      group

theorem conj_involution_eq_mul (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) {z j t : G}
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (ht : t ∈ J)
    (htn : t ∉ Subgroup.normalizer (K : Set G)) :
    t * z * t⁻¹ = z * j := by
  have hΩ := h.thmD.hyp
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  obtain ⟨hcU, hU4, hcV, hV4, hcomm, hsup⟩ := pair_structure h hK hJ hJn
  have hbot : K ⊓ J = ⊥ := perpP_inf_bot h hK hJΩ hKJ hJn
  have hJX : J ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) :
        Subgroup G) : Set G) :=
    le_sup_right.trans hsup
  obtain ⟨u, huU, hu4, -⟩ := perpP_gen hcU hU4
  obtain ⟨v, hvV, hv4, -⟩ := perpP_gen hcV hV4
  have hu2 : u ^ 2 = z := by
    have h1 : u ^ 2 ∈ K := K.pow_mem huU.1 2
    have h4 : u ^ 4 = 1 := by
      rw [← hu4]
      exact pow_orderOf_eq_one u
    have h2 : u ^ 2 * u ^ 2 = 1 := by
      calc u ^ 2 * u ^ 2 = u ^ 4 := by group
        _ = 1 := h4
    have h3 : u ^ 2 ≠ 1 := by
      intro e
      have h5 := orderOf_dvd_of_pow_eq_one e
      rw [hu4] at h5
      norm_num at h5
    exact (hz.unique _ h1 h2).resolve_left h3
  have hv2 : v ^ 2 = j := by
    have h1 : v ^ 2 ∈ J := J.pow_mem hvV.1 2
    have h4 : v ^ 4 = 1 := by
      rw [← hv4]
      exact pow_orderOf_eq_one v
    have h2 : v ^ 2 * v ^ 2 = 1 := by
      calc v ^ 2 * v ^ 2 = v ^ 4 := by group
        _ = 1 := h4
    have h3 : v ^ 2 ≠ 1 := by
      intro e
      have h5 := orderOf_dvd_of_pow_eq_one e
      rw [hv4] at h5
      norm_num at h5
    exact (hj.unique _ h1 h2).resolve_left h3
  have hjN : j ∈ Subgroup.normalizer (K : Set G) := by
    rw [← hv2]
    exact (Subgroup.normalizer (K : Set G)).pow_mem hvV.2 2
  have hzX : z ∈ K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) := by
    rw [← hu2]
    exact Subgroup.mem_sup_left ((K ⊓ Subgroup.normalizer (J : Set G)).pow_mem huU 2)
  have hxX : t * z * t⁻¹ ∈
      K ⊓ Subgroup.normalizer (J : Set G) ⊔ J ⊓ Subgroup.normalizer (K : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (hJX ht) z).mp hzX
  obtain ⟨a, haU, b, hbV, hab⟩ := perpP_mem_sup hcomm hxX
  have hab2 : a * a * (b * b) = 1 := by
    have e1 : a * b * (a * b) = a * a * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm a haU b hbV]
        _ = a * a * (b * b) := by group
    have hsq : t * z * t⁻¹ * (t * z * t⁻¹) = 1 := by
      calc t * z * t⁻¹ * (t * z * t⁻¹) = t * (z * z) * t⁻¹ := by group
        _ = 1 := by
          rw [hz.sq]
          group
    rw [← e1, hab]
    exact hsq
  have haa : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hab2
  have haaK : a * a ∈ K := K.mul_mem haU.1 haU.1
  have haaJ : a * a ∈ J := by
    rw [haa]
    exact J.inv_mem (J.mul_mem hbV.1 hbV.1)
  have haa1 : a * a = 1 := by
    have hmem : a * a ∈ K ⊓ J := Subgroup.mem_inf.mpr ⟨haaK, haaJ⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hbb1 : b * b = 1 := by
    rw [haa1, one_mul] at hab2
    exact hab2
  have ha' : a = 1 ∨ a = z := hz.unique a haU.1 haa1
  have hb' : b = 1 ∨ b = j := hj.unique b hbV.1 hbb1
  have hne1 : t * z * t⁻¹ ≠ 1 := perpP_conj_ne_one hz.ne_one
  have hnez : t * z * t⁻¹ ≠ z := by
    intro e
    have htz : t * z = z * t := by
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [e]
    have htne1 : t ≠ 1 := fun e1 => htn (by
      rw [e1]
      exact Subgroup.one_mem _)
    have htsq : t * t ≠ 1 := by
      intro e2
      rcases hj.unique t ht e2 with h1 | h1
      · exact htne1 h1
      · exact htn (by
          rw [h1]
          exact hjN)
    have hord : 3 ≤ orderOf t := by
      have h0 : 0 < orderOf t := orderOf_pos t
      have h1 : orderOf t ≠ 1 := fun h1 => htne1 (orderOf_eq_one_iff.mp h1)
      have h2 : orderOf t ≠ 2 := fun h2 => htsq (by
        have h3 := pow_orderOf_eq_one t
        rw [h2, pow_two] at h3
        exact h3)
      omega
    have hA : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) := by
      refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJΩ hKJ hz
        (Subgroup.zpowers_le.mpr ht) ?_ ?_ ?_
      · exact (perpP_isPGroup h hJΩ).to_le (Subgroup.zpowers_le.mpr ht)
      · rw [Nat.card_zpowers]
        exact hord
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htz)
    exact htn (hA (Subgroup.mem_zpowers t))
  have hnej : t * z * t⁻¹ ≠ j := by
    intro e
    have hcj := perpP_conj_eq hj ht
    have hjt : t * j = j * t := by
      calc t * j = t * j * t⁻¹ * t := by group
        _ = j * t := by rw [hcj]
    have hzj : z = j := by
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = t⁻¹ * j * t := by rw [e]
        _ = t⁻¹ * (j * t) := by group
        _ = t⁻¹ * (t * j) := by rw [← hjt]
        _ = j := by group
    have hzbot : z ∈ K ⊓ J := Subgroup.mem_inf.mpr ⟨hz.mem, by
      rw [hzj]
      exact hj.mem⟩
    rw [hbot, Subgroup.mem_bot] at hzbot
    exact hz.ne_one hzbot
  rw [← hab]
  rcases ha' with ha1 | ha1 <;> rcases hb' with hb1 | hb1
  · exfalso
    apply hne1
    rw [← hab, ha1, hb1, one_mul]
  · exfalso
    apply hnej
    rw [← hab, ha1, hb1, one_mul]
  · exfalso
    apply hnez
    rw [← hab, ha1, hb1, mul_one]
  · rw [ha1, hb1]

end CFSG.ClassicalInvolution.Q3.Sec13
