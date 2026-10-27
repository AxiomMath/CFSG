module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYEleven
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwelve
import CFSG.Quasithin.Background.A1cTransferVariants
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.Dihedral.DisconnectedInvolutionGraph.SimpleGroupReductions

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

theorem exists_sq_eq_of_mem_closure {G : Type*} [Group G] {A : Subgroup G}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {z : G}
    (hz : z ∈ closure {w | ∃ g ∈ A, w = g ^ 2}) : ∃ g ∈ A, g ^ 2 = z := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨g, hg, rfl⟩ := hw
    exact ⟨g, hg, rfl⟩
  | one => exact ⟨1, one_mem A, one_pow 2⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', rfl⟩ := hy
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    have hc : g * g' = g' * g := hab g hg g' hg'
    rw [sq, sq, sq, mul_assoc, ← mul_assoc g' g g', ← hc, mul_assoc, mul_assoc]
  | inv x _ hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g⁻¹, inv_mem hg, by rw [inv_pow]⟩

theorem exists_pow_sq_eq_of_odd {G : Type*} [Group G] {j : G} (hj : Odd (orderOf j)) :
    ∃ k : ℕ, (j ^ k) ^ 2 = j := by
  obtain ⟨m, hm⟩ := hj
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show (m + 1) * 2 = orderOf j + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem commutator_mem_of_sq_mem {G : Type*} [Group G] {H N : Subgroup G}
    (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hsq : ∀ x ∈ H, x ^ 2 ∈ N) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have e : a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2 * (b⁻¹ * (a⁻¹) ^ 2 * b⁻¹⁻¹) * (b⁻¹) ^ 2 := by
    rw [sq, sq, sq]
    group
  rw [e]
  exact mul_mem (mul_mem (hsq _ (mul_mem ha hb)) (hNn _ (inv_mem hb) _ (hsq _ (inv_mem ha))))
    (hsq _ (inv_mem hb))

namespace G2Data

variable {G : Type*} [Group G]
  {L : Subgroup G} {K : Type} [Field K]

theorem U_le_leviC (d : G2Data L K) : d.U ≤ d.leviC :=
  d.image_mono fun g hg => by
    obtain ⟨x, rfl⟩ := mem_rootSubgroup.1 hg
    exact pinnedX_c_mem_g2LongC x

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem yamadaU₁_sup_le_centralizer_J₁ (h : Setup G L f t) (d : G2Data L K)
    (h8 : 8 ≤ Nat.card K) : yamadaU₁ d t ⊔ zpowers t ≤ centralizer (d.J₁ : Set G) := by
  refine sup_le ?_ ((zpowers_le).2 (mem_centralizer_iff.2 fun j hj => ?_))
  · rw [yamadaU₁_eq d t h8]
    exact inf_le_right
  · exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))

theorem yamadaU₁_le_of_normal (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) {N : Subgroup G}
    (hNn : ∀ g ∈ centralizer (d.J₁ : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hUN : d.U ≤ N)
    (hJN : d.J₃ ≤ N) : yamadaU₁ d t ≤ N := by
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨ν, hνmul, -, hνsurj, hνscal, hκU, hκker⟩ := h.exists_coords_yamadaU₁ d hK h8
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have hU₁H := (le_sup_left.trans (h.yamadaU₁_sup_le_centralizer_J₁ d h8) :
    yamadaU₁ d t ≤ centralizer (d.J₁ : Set G))
  have hV : ∀ {x : G}, x ∈ yamadaU₁ d t → x ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hx =>
    ⟨yamadaC₁_le d t (hU₁C₁ hx), hC₁U (hU₁C₁ hx)⟩
  have hν1 : ν 1 = 0 := by
    have := hνmul (one_mem d.U) (one_mem d.U)
    rwa [mul_one, left_eq_add] at this
  set θ : G → K := fun x => ν (x⁻¹ * t * x * t) with hθdef
  have hθmul : ∀ {x y : G}, x ∈ yamadaU₁ d t → y ∈ yamadaU₁ d t → θ (x * y) = θ x + θ y :=
    fun hx hy => by
      simp only [hθdef]
      rw [hc₁.crossed_mul_of_mem (hV hx) (hV hy), hνmul (hκU hx) (hκU hy)]
  have hθker : ∀ {x : G}, x ∈ yamadaU₁ d t → (θ x = 0 ↔ x ∈ d.U) := fun hx => by
    rw [← hν1]
    exact hκker hx
  have hθinv : ∀ {x : G}, x ∈ yamadaU₁ d t → θ x⁻¹ = -θ x := fun hx => by
    have h1 := hθmul (inv_mem hx) hx
    rw [inv_mul_cancel, (hθker (one_mem _)).2 (one_mem _)] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have hθsurj : ∀ z : K, ∃ y ∈ yamadaU₁ d t, θ y = z := fun z => by
    obtain ⟨u, hu, rfl⟩ := hνsurj z
    obtain ⟨y, hy, hyu⟩ := h.exists_mem_yamadaU₁_crossed d hK h8 hu
    exact ⟨y, hy, by simp only [hθdef]; rw [hyu]⟩
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (hcon x hx)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at h1
    have h2 : ({0, 1} : Set K).ncard ≤ 2 := (Set.ncard_insert_le 0 {1}).trans (by
      rw [Set.ncard_singleton])
    omega
  obtain ⟨j, hj, hjν⟩ := hνscal a ha0
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
    (h.L_le_centralizer (d.J₃_le_inf_normalizer_U hj).1)
  have hjH : j ∈ centralizer (d.J₁ : Set G) :=
    mem_centralizer_iff.2 fun y hy => d.J₁_comm_J₃ hy hj
  intro x hx
  obtain ⟨y, hy, hyθ⟩ := hθsurj (θ x * (a - 1)⁻¹)
  have hjy := h.conj_mem_yamadaU₁ d hK h8 hj hy
  have hθjy : θ (j * y * j⁻¹) = a * θ y := by
    show ν ((j * y * j⁻¹)⁻¹ * t * (j * y * j⁻¹) * t) = a * θ y
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hjt, hjν _ (hκU hy)]
  have hc : j * y * j⁻¹ * y⁻¹ ∈ N := by
    rw [show j * y * j⁻¹ * y⁻¹ = j * (y * j⁻¹ * y⁻¹) by group]
    exact mul_mem (hJN hj) (hNn _ (hU₁H hy) _ (inv_mem (hJN hj)))
  have hw : (j * y * j⁻¹ * y⁻¹)⁻¹ * x ∈ d.U := by
    have hm : j * y * j⁻¹ * y⁻¹ ∈ yamadaU₁ d t := mul_mem hjy (inv_mem hy)
    refine (hθker (mul_mem (inv_mem hm) hx)).1 ?_
    rw [hθmul (inv_mem hm) hx, hθinv hm, hθmul hjy (inv_mem hy), hθinv hy, hθjy, hyθ]
    have hsub : a - 1 ≠ 0 := sub_ne_zero.2 ha1
    field_simp
    ring
  rw [show x = (j * y * j⁻¹ * y⁻¹) * ((j * y * j⁻¹ * y⁻¹)⁻¹ * x) by group]
  exact mul_mem hc (hUN hw)

theorem isPGroup_yamadaU₁_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : IsPGroup 2 (yamadaU₁ d t ⊔ zpowers t : Subgroup G) :=
  IsPGroup.of_card (n := 2 * f + 1) (by
    rw [h.card_yamadaU₁_sup d hK hD, (hD.yamada_5_10_1).2.2, hK, ← pow_mul, pow_succ,
      mul_comm 2 f, mul_comm])

theorem isSylowOf_yamadaU₁_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) :
    IsSylowOf 2 (yamadaU₁ d t ⊔ zpowers t) (centralizer (d.J₁ : Set G)) := by
  have hD := h.doublingFacts_of_eight d hK h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := h.yamadaU₁_sup_le_centralizer_J₁ d h8
  obtain ⟨S, hS⟩ := ((h.isPGroup_yamadaU₁_sup d hK hD).of_equiv
    (subgroupOfEquivOfLe hTH).symm).exists_le_sylow
  exact ⟨S, h.eq_yamadaU₁_sup_of_isPGroup d hK h8 (S.isPGroup'.map _) (map_subtype_le _)
    fun x hx => ⟨⟨x, hTH hx⟩, hS (mem_subgroupOf.2 hx), rfl⟩⟩

theorem conj_t_not_mem_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) (hhc : ∀ x ∈ yamadaU₁ d t, x ^ 2 = 1 ↔ x ∈ d.U) {x : G}
    (hx : x ∈ centralizer (d.J₁ : Set G)) : x⁻¹ * t * x ∉ yamadaU₁ d t := by
  have hD := h.doublingFacts_of_eight d hK h8
  intro hu
  have htt := h.t_mul_t
  have hu2 : (x⁻¹ * t * x) ^ 2 = 1 := by
    rw [sq, show x⁻¹ * t * x * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x by group, htt]
    group
  have huU := (hhc _ hu).1 hu2
  have hTH := h.yamadaU₁_sup_le_centralizer_J₁ d h8
  have hle : yamadaU₁ d t ⊔ zpowers t ≤ centralizer ({x⁻¹ * t * x} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (h.yamadaU₁_mul_comm d hK h8 hy hu))
      ((zpowers_le).2 (mem_centralizer_singleton_iff.2
        (mem_centralizer_singleton_iff.1 (((d.image_le _).trans h.L_le_centralizer) huU)).symm))
  set P := (yamadaU₁ d t ⊔ zpowers t).map (MulAut.conj x).toMonoidHom with hPdef
  have hP : IsPGroup 2 P := (h.isPGroup_yamadaU₁_sup d hK hD).map _
  have hPJ : P ≤ centralizer (d.J₁ : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hx (hTH hy)) (inv_mem hx)
  have hPt : P ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hle hy)
    calc x * y * x⁻¹ * t = x * (y * (x⁻¹ * t * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * t * x) * y) * x⁻¹ := by rw [h1]
      _ = t * (x * y * x⁻¹) := by group
  have hcard := h.card_le_of_isPGroup_of_le_centralizer_J₁ d hK h8 hP hPJ hPt
  rw [hPdef, card_map_of_injective (MulAut.conj x).injective, h.card_yamadaU₁_sup d hK hD,
    (h.yamada_5_10_1 d hK h8).2.2] at hcard
  have : Nat.card K < Nat.card K ^ 2 := by
    rw [sq]
    exact Nat.lt_mul_self_iff.2 (by omega)
  omega

theorem false_of_homocyclic (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K)
    (h4 : ∀ x ∈ yamadaU₁ d t, x ^ 4 = 1) (hhc : ∀ x ∈ yamadaU₁ d t, x ^ 2 = 1 ↔ x ∈ d.U)
    (hcl : closure {z | ∃ g ∈ yamadaU₁ d t, z = g ^ 2} = d.U) : False := by
  have hD := h.doublingFacts_of_eight d hK h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (d.J₁ : Set G) with hHdef
  set T := yamadaU₁ d t ⊔ zpowers t with hTdef
  obtain ⟨-, hUU₁, -⟩ := h.yamadaU₁_spec d h8
  have hab : ∀ x ∈ yamadaU₁ d t, ∀ y ∈ yamadaU₁ d t, x * y = y * x :=
    fun x hx y hy => h.yamadaU₁_mul_comm d hK h8 hx hy
  have hTH := h.yamadaU₁_sup_le_centralizer_J₁ d h8
  have hTsyl := h.isSylowOf_yamadaU₁_sup d hK h8
  obtain ⟨-, hT2, hTidx⟩ := ABGLocalTools.isSylowOf_iff.1 hTsyl
  have hU₁T : yamadaU₁ d t ≤ T := le_sup_left
  have hidx2 : (yamadaU₁ d t).relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := yamadaU₁ d t) (K := T)
    rw [inf_eq_left.2 hU₁T, h.card_yamadaU₁_sup d hK hD] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have htH : t ∈ H := hTH (mem_sup_right (mem_zpowers t))
  obtain ⟨N, hNH, hNn, hsqN, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
    hTH hT2 hTidx hU₁T hidx2 htH h.ht fun x hx => h.conj_t_not_mem_yamadaU₁ d hK h8 hhc hx
  have hNn' : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    hNn.conj_mem ⟨n, hNH hn⟩ hn ⟨g, hg⟩
  have hsqU : ∀ {u : G}, u ∈ d.U → ∃ g ∈ yamadaU₁ d t, g ^ 2 = u := fun {u} hu =>
    exists_sq_eq_of_mem_closure hab (by rw [hcl]; exact hu)
  have hUN : d.U ≤ N := by
    intro u hu
    obtain ⟨g, hg, rfl⟩ := hsqU hu
    exact hsqN g (hTH (hU₁T hg))
  have hJN : d.J₃ ≤ N := by
    intro j hj
    have hjH : j ∈ H := mem_centralizer_iff.2 fun y hy => d.J₁_comm_J₃ hy hj
    have hodd : Odd (orderOf j) := by
      have h1 : orderOf j ∣ Nat.card d.J₃ := by
        rw [← Subgroup.orderOf_mk j hj]
        exact orderOf_dvd_natCard _
      rw [d.card_J₃, hK] at h1
      exact (odd_two_pow_sub_one (by have := three_le_of_card_eq hK h8; omega)).of_dvd_nat h1
    obtain ⟨k, hk⟩ := exists_pow_sq_eq_of_odd hodd
    rw [← hk]
    exact hsqN _ (pow_mem hjH k)
  have hU₁N := h.yamadaU₁_le_of_normal d hK h8 hNn' hUN hJN
  have hTN : T ⊓ N = yamadaU₁ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf hU₁T hU₁N)
    obtain ⟨hxT, hxN⟩ := Subgroup.mem_inf.1 hx
    rcases (h.mem_yamadaU₁_sup_iff d hK hD).1 hxT with h1 | ⟨u, hu, rfl⟩
    · exact h1
    · exfalso
      have := mul_mem (inv_mem (hU₁N hu)) hxN
      rw [inv_mul_cancel_left] at this
      exact htN this
  have hsylN : IsSylowOf 2 (yamadaU₁ d t) N := by
    have := hTsyl.inf_of_le_normalizer hNH ((normal_subgroupOf_iff_le_normalizer hNH).1 hNn)
    rwa [hTN] at this
  obtain ⟨Q, hQ⟩ := hsylN
  have hQmem : ∀ x : N, x ∈ (Q : Subgroup N) ↔ (x : G) ∈ yamadaU₁ d t := by
    intro x
    rw [← hQ]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  obtain ⟨-, hCJ, -, ⟨e⟩⟩ := d.yamada_3_10_J₁_G h8
  have := Fintype.ofFinite K
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    GMSK.sl2_isSimpleGroup CharTwo.two_eq_zero (by rw [Fintype.card_eq_nat_card]; omega)
  have : IsSimpleGroup d.leviC := e.symm.isSimpleGroup
  have hnab : ∃ a b : d.leviC, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := K)
    exact ⟨e x, e y, fun h' => hxy (e.injective (by rw [map_mul, map_mul, h']))⟩
  have hperf : ⁅d.leviC, d.leviC⁆ = d.leviC := by
    have h1 : commutator d.leviC = ⊤ :=
      (CFSG.DisconnectedInvolutionGraph.Helpers.simple_nonabelian_perfect hnab).commutator_eq_top
    have h2 := congrArg (Subgroup.map d.leviC.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hCN : d.leviC ≤ N := by
    rw [← hperf, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact commutator_mem_of_sq_mem hNn' hsqN (hCJ ha) (hCJ hb)
  have : IsSimpleGroup (d.leviC.subgroupOf N) := (subgroupOfEquivOfLe hCN).isSimpleGroup
  have hJnab : ∃ a b : d.leviC.subgroupOf N, a * b ≠ b * a := by
    obtain ⟨a, b, hab'⟩ := hnab
    set φ := subgroupOfEquivOfLe hCN
    exact ⟨φ.symm a, φ.symm b, fun h' => hab' (φ.symm.injective (by rw [map_mul, map_mul, h']))⟩
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ d.U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : d.U = ⊥ := eq_bot_iff.2 fun u hu => (mem_bot).2 (hcon u hu)
    have h2 := d.cards.1
    rw [h1, card_bot] at h2
    omega
  refine false_of_simple_inf_sylow hW (X := N) Q ?_ ?_ ?_ hJnab
    (z := ⟨u₀, hU₁N (hUU₁ hu₀)⟩) (mem_subgroupOf.2 (d.U_le_leviC hu₀))
    ((hQmem _).2 (hUU₁ hu₀)) fun h' => hu₀1 (congrArg Subtype.val h')
  · intro x hx y hy
    exact Subtype.ext (hab _ ((hQmem x).1 hx) _ ((hQmem y).1 hy))
  · intro x hx
    exact Subtype.ext (by rw [Subgroup.coe_pow, h4 _ ((hQmem x).1 hx), Subgroup.coe_one])
  · intro z hz hz2
    have hz2' : (z : G) ^ 2 = 1 := by rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
    obtain ⟨g, hg, hgz⟩ := hsqU ((hhc _ ((hQmem z).1 hz)).1 hz2')
    exact ⟨⟨g, hU₁N hg⟩, (hQmem _).2 hg, Subtype.ext (by rw [Subgroup.coe_pow]; exact hgz)⟩

theorem yamada_5_16 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    CFSG.IsElementaryAbelian 2 (yamadaU₁ d t) := by
  rcases hD.branch with h8 | ⟨-, helem, -⟩
  · exact (h.yamada_5_10_2 d hK h8).resolve_right fun ⟨_, h4, hhc, hcl⟩ =>
      h.false_of_homocyclic hW d hK h8 h4 hhc hcl
  · exact helem

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
