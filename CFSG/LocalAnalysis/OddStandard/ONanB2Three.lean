module

public import CFSG.LocalAnalysis.OddStandard.ONanB2Quot
public import CFSG.LocalAnalysis.OddStandard.ONanB2CM
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34GL32
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.OddStandard.ONanRec.B2

open Subgroup CM CFSG.GorensteinWalter

section General

variable {G : Type} [Group G]

theorem exists_conj_of_card_nine {H : Type*} [Group H] [Finite H] (hH : ¬ 27 ∣ Nat.card H)
    {P Q : Subgroup H} (hP : Nat.card P = 9) (hQ : Nat.card Q = 9) :
    ∃ c : H, ∀ x, x ∈ P ↔ c⁻¹ * x * c ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ {A : Subgroup H}, Nat.card A = 9 → ∃ S : Sylow 3 H, (S : Subgroup H) = A := by
    intro A hA
    have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) (by rw [hA]; norm_num)
    obtain ⟨S, hS⟩ := hAp.exists_le_sylow
    refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 S.isPGroup'
    have h9 : 9 ∣ 3 ^ n := by rw [← hn, ← hA]; exact Subgroup.card_dvd_of_le hS
    have hdvd : 3 ^ n ∣ Nat.card H := by rw [← hn]; exact Subgroup.card_subgroup_dvd_card _
    have hn2 : n ≤ 2 := by
      by_contra hn3
      exact hH ((pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdvd)
    rw [hn, hA]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 9 := by norm_num
  obtain ⟨SP, hSP⟩ := hsyl hP
  obtain ⟨SQ, hSQ⟩ := hsyl hQ
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H SQ SP
  refine ⟨c, fun x => ?_⟩
  rw [← hSP, ← hc, ← hSQ, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem le_normalizer_of_comm {R L : Subgroup G} (hcomm : ∀ r ∈ R, ∀ l ∈ L, r * l = l * r) :
    R ≤ normalizer (L : Set G) := by
  intro r hr
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hcomm r hr h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have e := hcomm r hr _ hh
    have : h = r * h * r⁻¹ := by
      calc h = r⁻¹ * (r * h * r⁻¹) * r := by group
        _ = r⁻¹ * (r * (r * h * r⁻¹)) := by rw [mul_assoc r⁻¹, ← e]
        _ = r * h * r⁻¹ := by group
    rw [this]
    exact hh

theorem exists_mul_of_mem_sup {R L : Subgroup G} (hcomm : ∀ r ∈ R, ∀ l ∈ L, r * l = l * r)
    {x : G} (hx : x ∈ R ⊔ L) : ∃ r ∈ R, ∃ l ∈ L, x = r * l := by
  have hx' : x ∈ ((R ⊔ L : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right R L (le_normalizer_of_comm hcomm)] at hx'
  obtain ⟨r, hr, l, hl, rfl⟩ := hx'
  exact ⟨r, hr, l, hl, rfl⟩

theorem mem_right_of_pow_two {R L : Subgroup G} (hcomm : ∀ r ∈ R, ∀ l ∈ L, r * l = l * r)
    (hRL : R ⊓ L = ⊥) (hRodd : Odd (Nat.card R)) {x : G} (hx : x ∈ R ⊔ L) {n : ℕ}
    (hxn : x ^ (2 ^ n) = 1) : x ∈ L := by
  obtain ⟨r, hr, l, hl, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  have hc : Commute r l := hcomm r hr l hl
  rw [hc.mul_pow] at hxn
  have hr1 : r ^ (2 ^ n) ∈ R ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨pow_mem hr _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hxn]
    exact inv_mem (pow_mem hl _)
  rw [hRL, mem_bot] at hr1
  have hord : orderOf r ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hr1
  have hodd : orderOf r ∣ Nat.card R := by
    rw [← Subgroup.orderOf_mk r hr]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card R) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hRodd)
  rw [orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord hodd), one_mul]
  exact hl

theorem map_mem_normalizer {H : Type*} [Group H] (f : H →* G) {A : Subgroup H} {a : H}
    (ha : a ∈ normalizer (A : Set H)) : f a ∈ normalizer ((A.map f : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a * x * a⁻¹, (mem_normalizer_iff.1 ha x).1 hx, by simp⟩
  · rintro ⟨y, hy, hye⟩
    refine ⟨a⁻¹ * y * a, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem ha) y).1 hy
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hye, map_inv]
      group

end General

section Model

variable {G : Type} [Group G] {i : G} (ψ : centralizer ({i} : Set G) ≃* M480)

@[expose] noncomputable def emb : M480 →* G :=
  (centralizer ({i} : Set G)).subtype.comp ψ.symm.toMonoidHom

theorem emb_injective : Function.Injective (emb ψ) :=
  (centralizer _).subtype_injective.comp ψ.symm.injective

theorem emb_mem (m : M480) : emb ψ m ∈ centralizer ({i} : Set G) := (ψ.symm m).2

theorem emb_psi (g : centralizer ({i} : Set G)) : emb ψ (ψ g) = g := by
  simp [emb]

theorem range_emb : (emb ψ).range = centralizer ({i} : Set G) := by
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    exact emb_mem ψ m
  · intro hg
    exact ⟨ψ ⟨g, hg⟩, emb_psi ψ ⟨g, hg⟩⟩

theorem mem_self_centralizer : i ∈ centralizer ({i} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem psi_i (hi : orderOf i = 2) :
    ψ ⟨i, mem_self_centralizer⟩ = fM := by
  have hc : ∀ m' : M480, m' * ψ ⟨i, mem_self_centralizer⟩ = ψ ⟨i, mem_self_centralizer⟩ * m' := by
    intro m'
    obtain ⟨g, rfl⟩ := ψ.surjective m'
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 g.2))
  rcases center_M480 (ψ ⟨i, mem_self_centralizer⟩) hc with h | h
  · exfalso
    have : (⟨i, mem_self_centralizer⟩ : centralizer ({i} : Set G)) = 1 :=
      ψ.injective (h.trans (map_one ψ).symm)
    have hi1 : i = 1 := congrArg Subtype.val this
    have h12 : orderOf (1 : G) = 2 := hi1 ▸ hi
    simp at h12
  · exact h

theorem emb_fM (hi : orderOf i = 2) :
    emb ψ fM = i := by
  rw [← psi_i ψ hi, emb_psi]

end Model

section Embedded

variable {G : Type} [Group G] {i : G} (ψ : centralizer ({i} : Set G) ≃* M480)

theorem comm_R1M_of {m : M480}
    (h1 : m * r1M = r1M * m) (h2 : m * r2M = r2M * m) : ∀ x ∈ R1M, m * x = x * m := by
  have hle : R1M ≤ centralizer ({m} : Set M480) := by
    rw [R1M, closure_le]
    rintro x (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 h1.symm
    · exact mem_centralizer_singleton_iff.2 h2.symm
  intro x hx
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem mem_R1G_iff (x : G) :
    x ∈ R1M.map (emb ψ) ↔ ∃ a b, a < 3 ∧ b < 3 ∧ x = emb ψ (r1M ^ a * r2M ^ b) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := (mem_R1M_iff m).1 hm
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨_, (mem_R1M_iff _).2 ⟨a, b, ha, hb, rfl⟩, rfl⟩

theorem card_R1G :
    Nat.card (R1M.map (emb ψ)) = 9 := by
  rw [Subgroup.card_map_of_injective (emb_injective ψ), card_R1M]

theorem R1G_le :
    R1M.map (emb ψ) ≤ centralizer ({i} : Set G) := by
  rintro _ ⟨m, -, rfl⟩
  exact emb_mem ψ m

theorem R1M_comm {x y : M480}
    (hx : x ∈ R1M) (hy : y ∈ R1M) : x * y = y * x := by
  obtain ⟨a, b, -, -, rfl⟩ := (mem_R1M_iff x).1 hx
  obtain ⟨a', b', -, -, rfl⟩ := (mem_R1M_iff y).1 hy
  have hc : Commute r1M r2M := rM_comm
  have : Commute (r1M ^ a * r2M ^ b) (r1M ^ a' * r2M ^ b') := by
    apply Commute.mul_left <;> apply Commute.mul_right
    · exact Commute.pow_pow_self r1M a a'
    · exact hc.pow_pow a b'
    · exact (hc.pow_pow a' b).symm
    · exact Commute.pow_pow_self r2M b b'
  exact this.eq

theorem R1G_comm {x y : G}
    (hx : x ∈ R1M.map (emb ψ)) (hy : y ∈ R1M.map (emb ψ)) : x * y = y * x := by
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨n, hn, rfl⟩ := hy
  rw [← map_mul, ← map_mul, R1M_comm hm hn]

theorem R1G_le_centralizer :
    R1M.map (emb ψ) ≤ centralizer ((R1M.map (emb ψ) : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact R1G_comm ψ hy hx

theorem embM_comm_R1G {m : M480}
    (h1 : m * r1M = r1M * m) (h2 : m * r2M = r2M * m) :
    ∀ x ∈ R1M.map (emb ψ), emb ψ m * x = x * emb ψ m := by
  rintro _ ⟨n, hn, rfl⟩
  rw [← map_mul, ← map_mul, comm_R1M_of h1 h2 n hn]

theorem orderOf_zM :
    orderOf zM = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := zM)
    (by rw [pow_one, pow_two]; exact zM_sq_ne) (by norm_num; exact zM_four)
  simpa using h

theorem nonempty_S0G [Finite G] :
    Nonempty (closure ({emb ψ zM, emb ψ dM} : Set G) ≃* DihedralGroup 4) := by
  have hθ := emb_injective ψ
  have hord : orderOf (emb ψ zM) = 4 := by rw [orderOf_injective _ hθ, orderOf_zM]
  rw [← hord]
  refine CFSG.LieType.SteinbergBR.AutGL32.nonempty_closure_pair_mulEquiv_dihedralGroup ?_ ?_ ?_
  · rw [← map_pow, sq, dM_sq, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      show dM⁻¹ = dM from inv_eq_of_mul_eq_one_right dM_sq, dM_zM]
  · classical
    intro hmem
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
    obtain ⟨k, hk, he⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_range] at hk
    rw [← map_pow] at he
    exact dM_ne_zM_pow hk (hθ he).symm

end Embedded

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_centralizer_of_psi {j : G}
    (ψ : centralizer ({j} : Set G) ≃* M480) : Nat.card (centralizer ({j} : Set G)) = 161280 := by
  rw [Nat.card_congr ψ.toEquiv, card_M480 cmBoundCheck_cert cmModelCheck_cert]

omit [Finite G] in
theorem comm_of_card_nine {P : Subgroup G} (hP9 : Nat.card P = 9) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) : x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P)
    (by rw [hP9]; norm_num)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem exists_centralizer_eq_sup
    {j : G} (ψ : centralizer ({j} : Set G) ≃* M480) {P : Subgroup G}
    (hP : P ≤ centralizer ({j} : Set G)) (hP9 : Nat.card P = 9) :
    ∃ S : Subgroup G, S ≤ centralizer ({j} : Set G) ⊓ centralizer (P : Set G) ∧
      Nonempty (S ≃* DihedralGroup 4) ∧
      centralizer ({j} : Set G) ⊓ centralizer (P : Set G) = P ⊔ S := by
  have hθ : Function.Injective (emb ψ) := emb_injective ψ
  have hQC : R1M.map (emb ψ) ≤ centralizer ({j} : Set G) := R1G_le ψ
  obtain ⟨c, hc⟩ := exists_conj_of_card_nine (H := centralizer ({j} : Set G))
    (by rw [card_centralizer_of_psi ψ]; decide)
    (P := P.subgroupOf (centralizer ({j} : Set G)))
    (Q := (R1M.map (emb ψ)).subgroupOf (centralizer ({j} : Set G)))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv, hP9])
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, card_R1G ψ])
  have hcP : ∀ x : G, x ∈ centralizer ({j} : Set G) →
      (x ∈ P ↔ (c : G)⁻¹ * x * c ∈ R1M.map (emb ψ)) := by
    intro x hx
    simpa [mem_subgroupOf] using hc ⟨x, hx⟩
  have hcC : ∀ x : G, x ∈ centralizer ({j} : Set G) →
      (c : G) * x * (c : G)⁻¹ ∈ centralizer ({j} : Set G) := fun x hx =>
    mul_mem (mul_mem c.2 hx) (inv_mem c.2)
  have hconjP : ∀ q ∈ R1M.map (emb ψ), (c : G) * q * (c : G)⁻¹ ∈ P := by
    intro q hq
    rw [hcP _ (hcC q (hQC hq))]
    convert hq using 1
    group
  set S0 : Subgroup G := closure {emb ψ zM, emb ψ dM} with hS0
  have hS0C : S0 ≤ centralizer ({j} : Set G) := by
    rw [hS0, closure_le]
    rintro _ (rfl | rfl)
    · exact emb_mem ψ zM
    · exact emb_mem ψ dM
  have hS0Q : S0 ≤ centralizer ((R1M.map (emb ψ) : Subgroup G) : Set G) := by
    rw [hS0, closure_le]
    obtain ⟨hz1, hz2, hd1, hd2⟩ := zM_r
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro q hq
      exact (embM_comm_R1G ψ hz1 hz2 q hq).symm
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro q hq
      exact (embM_comm_R1G ψ hd1 hd2 q hq).symm
  set S : Subgroup G := S0.map (MulAut.conj (c : G)).toMonoidHom with hS
  have hSC : S ≤ centralizer ({j} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hcC s (hS0C hs)
  have hSP : S ≤ centralizer (P : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hxQ : (c : G)⁻¹ * x * c ∈ R1M.map (emb ψ) := (hcP x (hP hx)).1 hx
    have hcomm := mem_centralizer_iff.1 (hS0Q hs) _ hxQ
    show x * ((c : G) * s * (c : G)⁻¹) = (c : G) * s * (c : G)⁻¹ * x
    calc x * ((c : G) * s * (c : G)⁻¹) = (c : G) * (((c : G)⁻¹ * x * c) * s) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (s * ((c : G)⁻¹ * x * c)) * (c : G)⁻¹ := by rw [hcomm]
      _ = (c : G) * s * (c : G)⁻¹ * x := by group
  have hPcomm : P ≤ centralizer (P : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact comm_of_card_nine hP9 hy hx
  refine ⟨S, le_inf hSC hSP, ?_, le_antisymm ?_ (sup_le (le_inf hP hPcomm) (le_inf hSC hSP))⟩
  · obtain ⟨e⟩ := nonempty_S0G ψ
    exact ⟨(S0.equivMapOfInjective _ (MulAut.conj (c : G)).injective).symm.trans e⟩
  · rintro x ⟨hxj, hxP⟩
    set y := (c : G)⁻¹ * x * c with hy
    have hyC : y ∈ centralizer ({j} : Set G) := by
      have := hcC x hxj
      exact mul_mem (mul_mem (inv_mem c.2) hxj) c.2
    have hyQ : ∀ q ∈ R1M.map (emb ψ), y * q = q * y := by
      intro q hq
      have h1 := mem_centralizer_iff.1 hxP _ (hconjP q hq)
      calc y * q = (c : G)⁻¹ * (x * ((c : G) * q * (c : G)⁻¹)) * c := by rw [hy]; group
        _ = (c : G)⁻¹ * (((c : G) * q * (c : G)⁻¹) * x) * c := by rw [h1]
        _ = q * y := by rw [hy]; group
    obtain ⟨m, hm⟩ : ∃ m : M480, emb ψ m = y := by
      rw [← range_emb ψ] at hyC
      exact hyC
    have hm1 : m * r1M = r1M * m := hθ (by
      rw [map_mul, map_mul, hm]
      exact hyQ _ ⟨r1M, subset_closure (Or.inl rfl), rfl⟩)
    have hm2 : m * r2M = r2M * m := hθ (by
      rw [map_mul, map_mul, hm]
      exact hyQ _ ⟨r2M, subset_closure (Or.inr rfl), rfl⟩)
    obtain ⟨a, b, k, l, ha, hb, -, -, rfl⟩ := centralizer_R1M m hm1 hm2
    have hr : emb ψ (r1M ^ a * r2M ^ b) ∈ R1M.map (emb ψ) :=
      (mem_R1G_iff ψ _).2 ⟨a, b, ha, hb, rfl⟩
    have hs : emb ψ (zM ^ k * dM ^ l) ∈ S0 := by
      rw [map_mul, map_pow, map_pow]
      have hz : emb ψ zM ∈ S0 := Subgroup.subset_closure (Set.mem_insert _ _)
      have hd : emb ψ dM ∈ S0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      exact mul_mem (pow_mem hz k) (pow_mem hd l)
    have hx : x = ((c : G) * emb ψ (r1M ^ a * r2M ^ b) * (c : G)⁻¹) *
        ((c : G) * emb ψ (zM ^ k * dM ^ l) * (c : G)⁻¹) := by
      have : x = (c : G) * y * (c : G)⁻¹ := by rw [hy]; group
      rw [this, ← hm, map_mul]
      group
    rw [hx]
    exact mul_mem_sup (hconjP _ hr) ⟨_, hs, rfl⟩

end Sylow

section Aut

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

theorem nonempty_equiv_GL32 {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (h7 : Nat.card K = 7) (e : X ≃* PSL2 K) :
    Nonempty (X ≃* GL (Fin 3) (ZMod 2)) ∧ Nonempty (X ≃* PSL(2, ZMod 7)) := by
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 7 := by rw [Fintype.card_eq_nat_card, h7]
  let eK : ZMod 7 ≃+* K := ZMod.ringEquivOfPrime K (by norm_num) hK
  let e7 : X ≃* PSL(2, ZMod 7) := e.trans (CFSG.GorensteinWalter.psl2RingEquiv eK).symm
  obtain ⟨g⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨⟨e7.trans g.symm⟩, ⟨e7⟩⟩

theorem card_mulAut_of_seven {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (h7 : Nat.card K = 7) (e : X ≃* PSL2 K) : Nat.card (MulAut X) = 336 := by
  obtain ⟨⟨g⟩, -⟩ := nonempty_equiv_GL32 K h7 e
  rw [Nat.card_congr (MulAut.congr g).toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32

theorem card_of_seven {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (h7 : Nat.card K = 7) (e : X ≃* PSL2 K) : Nat.card X = 168 := by
  obtain ⟨⟨g⟩, -⟩ := nonempty_equiv_GL32 K h7 e
  rw [Nat.card_congr g.toEquiv]
  exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32

theorem not_dvd_card_mulAut {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (hq : Nat.card K = 7 ∨ Nat.card K = 9) (e : X ≃* PSL2 K) : ¬ 64 ∣ Nat.card (MulAut X) := by
  rcases hq with h7 | h9
  · rw [card_mulAut_of_seven K h7 e]
    decide
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨e6⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        K (by rw [Fintype.card_eq_nat_card, h9])
    rw [Nat.card_congr (MulAut.congr (e.trans e6)).toEquiv]
    have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    have h360 : 360 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
      rw [← CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card]
      exact Subgroup.card_subgroup_dvd_card _
    have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := h360
    omega

end Aut

section Split

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev R1G {i : G} (ψ : centralizer ({i} : Set G) ≃* M480) :
    Subgroup G :=
  R1M.map (emb ψ)

noncomputable abbrev CG {i : G} (ψ : centralizer ({i} : Set G) ≃* M480) :
    Subgroup G :=
  centralizer ((R1G ψ : Subgroup G) : Set G)

noncomputable abbrev KG {i : G} (ψ : centralizer ({i} : Set G) ≃* M480) :
    Subgroup G :=
  ⁅CG ψ, CG ψ⁆

omit [Finite G] in
theorem nonempty_psi_of_oneClass (hone : OneClass G) {i : G} (hi : orderOf i = 2)
    (ψ : centralizer ({i} : Set G) ≃* M480) {j : G} (hj : orderOf j = 2) :
    Nonempty (centralizer ({j} : Set G) ≃* M480) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone i j hi hj)
  subst hc
  exact ⟨(centralizerConjEquiv c i).symm.trans ψ⟩

theorem split_R1G
    (hone : OneClass G) {i : G} (hi : orderOf i = 2)
    (ψ : centralizer ({i} : Set G) ≃* M480) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (Nat.card K = 7 ∨ Nat.card K = 9) ∧
      CG ψ = R1G ψ ⊔ KG ψ ∧ R1G ψ ⊓ KG ψ = ⊥ ∧ Nonempty (KG ψ ≃* PSL2 K) := by
  have hR9 : Nat.card (R1G ψ) = 9 := card_R1G ψ
  have hRi : R1G ψ ≤ centralizer ({i} : Set G) := R1G_le ψ
  have hRC : R1G ψ ≤ CG ψ := R1G_le_centralizer ψ
  have hiC : i ∈ CG ψ := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.1 (hRi hr)
  set R' := (R1G ψ).subgroupOf (CG ψ) with hR'
  have hZ : R' ≤ center (CG ψ) := by
    intro r hr
    rw [mem_subgroupOf] at hr
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (mem_centralizer_iff.1 c.2 _ hr).symm
  have hN : R'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.1 (hZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hR'9 : Nat.card R' = 9 := by
    rw [hR', Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv, hR9]
  have hS : ∀ j : CG ψ, orderOf j = 2 → ∃ S : Subgroup (CG ψ),
      Nonempty (S ≃* DihedralGroup 4) ∧ centralizer ({j} : Set (CG ψ)) = R' ⊔ S := by
    intro j hj
    have hjG : orderOf (j : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hj
    obtain ⟨ψj⟩ := nonempty_psi_of_oneClass hone hi ψ hjG
    have hRj : R1G ψ ≤ centralizer ({(j : G)} : Set G) := fun r hr =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 j.2 r hr)
    obtain ⟨SG, hSG, ⟨eS⟩, hSeq⟩ := exists_centralizer_eq_sup ψj hRj hR9
    have hSGC : SG ≤ CG ψ := hSG.trans inf_le_right
    refine ⟨SG.subgroupOf (CG ψ), ⟨(subgroupOfEquivOfLe hSGC).trans eS⟩, ?_⟩
    ext y
    rw [mem_centralizer_singleton_iff, hR', ← subgroupOf_sup hRC hSGC, mem_subgroupOf, ← hSeq]
    constructor
    · intro h
      exact ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val h), y.2⟩
    · rintro ⟨h1, -⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.1 h1)
  have hD8 : CentD8 (CG ψ ⧸ R') := centD8_quotient R' hZ (by rw [hR'9]; decide) hS
  have hinv : ∃ t : CG ψ ⧸ R', orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨QuotientGroup.mk ⟨i, hiC⟩, orderOf_eq_prime ?_ ?_⟩
    · rw [← QuotientGroup.mk_pow]
      have h2 : (⟨i, hiC⟩ : CG ψ) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, ← hi]
        exact pow_orderOf_eq_one i)
      rw [h2, QuotientGroup.mk_one]
    · intro h1
      rw [QuotientGroup.eq_one_iff, hR', mem_subgroupOf] at h1
      have h2 : orderOf i ∣ 9 := by
        rw [← hR9, ← Subgroup.orderOf_mk i h1]
        exact orderOf_dvd_natCard _
      rw [hi] at h2
      norm_num at h2
  obtain ⟨K, hF, hFin, hq, ⟨e⟩⟩ := exists_psl2_of_centD8 hD8 hinv
  have hyN : emb ψ yM ∈ normalizer ((R1G ψ : Subgroup G) : Set G) :=
    map_mem_normalizer (emb ψ) (T0M_le_normalizer yM_mem_T0M)
  have hirr : ∀ A : Subgroup G, A ≤ R1G ψ → Nat.card A = 3 →
      ∃ t ∈ zpowers (emb ψ yM), ∃ a ∈ A, t * a * t⁻¹ ∉ A := by
    intro A hA hA3
    rcases Subgroup.bot_or_exists_ne_one A with hbot | ⟨a, haA, ha1⟩
    · rw [hbot, Subgroup.card_bot] at hA3
      norm_num at hA3
    obtain ⟨p, q, hp, hq', rfl⟩ := (mem_R1G_iff ψ a).1 (hA haA)
    have hpq : ¬ (p = 0 ∧ q = 0) := by
      rintro ⟨rfl, rfl⟩
      exact ha1 (by simp)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ha3 : orderOf (emb ψ (r1M ^ p * r2M ^ q)) = 3 := by
      have hdvd : orderOf (emb ψ (r1M ^ p * r2M ^ q)) ∣ 3 := by
        rw [← hA3, ← Subgroup.orderOf_mk _ haA]
        exact orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) ha1
      · exact h
    have hAz : A = zpowers (emb ψ (r1M ^ p * r2M ^ q)) := by
      symm
      apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 haA)
      rw [hA3, Nat.card_zpowers, ha3]
    refine ⟨emb ψ yM, mem_zpowers _, _, haA, fun hmem => ?_⟩
    rw [hAz] at hmem
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, ha3] at hmem
    obtain ⟨k, hk, he⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_range] at hk
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul] at he
    have he' := emb_injective ψ he
    obtain ⟨h1, h2, h3⟩ := yM_irred hp hq' hpq
    interval_cases k
    · exact h1 (by rw [← he', pow_zero])
    · exact h2 (by rw [← he', pow_one])
    · exact h3 (by rw [← he', pow_two])
  set π : CG ψ →* PSL2 K := e.toMonoidHom.comp (QuotientGroup.mk' R') with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective R')
  have hker : π.ker = R' := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨h1, h2, h3⟩ := exists_complement (R1G ψ) hR9 (zpowers (emb ψ yM)) ((zpowers_le).2 hyN)
    hirr K hq π hπ hker
  exact ⟨K, hF, hFin, hq, h1, h2, h3⟩

end Split

section KFacts

variable {G : Type} [Group G] {i : G} (ψ : centralizer ({i} : Set G) ≃* M480)

theorem comm_R1G_KG {r k : G} (hr : r ∈ R1G ψ) (hk : k ∈ KG ψ) :
    r * k = k * r :=
  mem_centralizer_iff.1 (Subgroup.commutator_le_self (CG ψ) hk) r hr

theorem emb_mem_KG
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥) {m : M480}
    (h1 : m * r1M = r1M * m) (h2 : m * r2M = r2M * m) {n : ℕ} (hn : m ^ (2 ^ n) = 1) :
    emb ψ m ∈ KG ψ := by
  have hmC : emb ψ m ∈ CG ψ := by
    rw [mem_centralizer_iff]
    intro r hr
    exact (embM_comm_R1G ψ h1 h2 r hr).symm
  rw [hdec] at hmC
  refine mem_right_of_pow_two (fun r hr k hk => comm_R1G_KG ψ hr hk) hinf
    (by rw [card_R1G ψ]; decide) hmC (n := n) ?_
  rw [← map_pow, hn, map_one]

theorem zG_mem_KG
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥) : emb ψ zM ∈ KG ψ :=
  emb_mem_KG ψ hdec hinf zM_r.1 zM_r.2.1 (n := 2) (by norm_num; exact zM_four)

theorem dG_mem_KG
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥) : emb ψ dM ∈ KG ψ :=
  emb_mem_KG ψ hdec hinf zM_r.2.2.1 zM_r.2.2.2 (n := 1) (by rw [pow_one, sq]; exact dM_sq)

theorem fG_mem_KG
    (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥) : emb ψ fM ∈ KG ψ := by
  rw [← zM_sq, map_mul]
  exact mul_mem (zG_mem_KG ψ hdec hinf) (zG_mem_KG ψ hdec hinf)

noncomputable abbrev TG : Subgroup G := T0M.map (emb ψ)

theorem card_TG :
    Nat.card (TG ψ) = 64 := by
  rw [Subgroup.card_map_of_injective (emb_injective ψ), card_T0M]

theorem TG_le_normalizer_R1G :
    TG ψ ≤ normalizer ((R1G ψ : Subgroup G) : Set G) := by
  rintro _ ⟨t, ht, rfl⟩
  exact map_mem_normalizer (emb ψ) (T0M_le_normalizer ht)

theorem TG_le_normalizer_KG :
    TG ψ ≤ normalizer ((KG ψ : Subgroup G) : Set G) := by
  intro t ht
  have htN := TG_le_normalizer_R1G ψ ht
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_commutator_centralizer htN hh, fun hh => ?_⟩
  have := conj_mem_commutator_centralizer (inv_mem htN) hh
  rwa [show t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h by group] at this

theorem yfG_mem_TG (l : ℕ) :
    emb ψ (yM * fM ^ l) ∈ TG ψ :=
  ⟨_, mul_mem yM_mem_T0M (pow_mem fM_mem_T0M l), rfl⟩

end KFacts

section Involution

variable {G : Type} [Group G] {i : G} (ψ : centralizer ({i} : Set G) ≃* M480)

@[expose] noncomputable def phiT :
    TG ψ →* MulAut (KG ψ) :=
  (CFSG.GroupTheory.WielandtProduct.normalizerConj (KG ψ)).comp
    (Subgroup.inclusion (TG_le_normalizer_KG ψ))

theorem phiT_apply (t : TG ψ)
    (k : KG ψ) : ((phiT ψ t k : KG ψ) : G) = t * k * (t : G)⁻¹ :=
  rfl

theorem mem_ker_phiT_iff
    (t : TG ψ) : t ∈ (phiT ψ).ker ↔ ∀ k ∈ KG ψ, (t : G) * k = k * t := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h k hk
    have h1 := congrArg (fun α : MulAut (KG ψ) => ((α ⟨k, hk⟩ : KG ψ) : G)) h
    simp only [phiT_apply, MulAut.one_apply] at h1
    calc (t : G) * k = (t : G) * k * (t : G)⁻¹ * t := by group
      _ = k * t := by rw [h1]
  · intro h
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [phiT_apply, MulAut.one_apply, h k k.2, mul_inv_cancel_right]

theorem exists_involution_centralizing
    [Finite G] (K' : Type) [Field K'] [Finite K']
    (hq : Nat.card K' = 7 ∨ Nat.card K' = 9) (eK : KG ψ ≃* PSL2 K') :
    ∃ j : G, orderOf j = 2 ∧ j ∈ TG ψ ∧ ∀ k ∈ KG ψ, j * k = k * j := by
  have hcard := Subgroup.card_ker_mul_card_range (phiT ψ)
  rw [card_TG ψ] at hcard
  have hdvd : Nat.card (phiT ψ).range ∣ Nat.card (MulAut (KG ψ)) :=
    Subgroup.card_subgroup_dvd_card _
  have hnot := not_dvd_card_mulAut K' hq eK
  have hker2 : 2 ∣ Nat.card (phiT ψ).ker := by
    have hk1 : Nat.card (phiT ψ).ker ≠ 1 := by
      intro h1
      rw [h1, one_mul] at hcard
      exact hnot (by rw [← hcard]; exact hdvd)
    have hk64 : Nat.card (phiT ψ).ker ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
      exact Dvd.intro _ hcard
    obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk64
    rw [hm']
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hk1 (by rw [hm', pow_zero])
    exact dvd_pow_self 2 hm0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hker2
  refine ⟨((x : TG ψ) : G), ?_, (x : TG ψ).2, (mem_ker_phiT_iff ψ x).1 x.2⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

theorem exists_yf_centralizing
    (hone : OneClass G) (hi : orderOf i = 2) (hdec : CG ψ = R1G ψ ⊔ KG ψ)
    (hinf : R1G ψ ⊓ KG ψ = ⊥) (hperf : ⁅KG ψ, KG ψ⁆ = KG ψ) {j : G} (hj : orderOf j = 2)
    (hjK : ∀ k ∈ KG ψ, j * k = k * j) :
    ∃ l < 2, ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l) := by
  obtain ⟨ψj⟩ := nonempty_psi_of_oneClass hone hi ψ hj
  set x' := emb ψj zM with hx'
  have hx2 : x' * x' = j := by rw [hx', ← map_mul, zM_sq, emb_fM ψj hj]
  have hjj : j * j = 1 := by rw [← pow_two, ← hj, pow_orderOf_eq_one]
  have hKj : KG ψ ≤ centralizer ({j} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.2 (hjK k hk).symm
  have hKcomm : KG ψ ≤ ⁅centralizer ({j} : Set G), centralizer ({j} : Set G)⁆ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hKj hKj
  have hcomm_map : (commutator M480).map (emb ψj) =
      ⁅centralizer ({j} : Set G), centralizer ({j} : Set G)⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_emb]
  have hx'K : ∀ k ∈ KG ψ, x' * k = k * x' := by
    intro k hk
    have hk' := hKcomm hk
    rw [← hcomm_map] at hk'
    obtain ⟨m, hm, rfl⟩ := hk'
    have hmz := mem_centralizer_singleton_iff.1 (commutator_le_centralizer_zM hm)
    rw [hx', ← map_mul, ← map_mul, hmz]
  have hθ := emb_injective ψ
  have hx'i : x' ∈ centralizer ({i} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← emb_fM ψ hi]
    exact hx'K _ (fG_mem_KG ψ hdec hinf)
  obtain ⟨m, hm⟩ : ∃ m : M480, emb ψ m = x' := by
    rw [← range_emb ψ] at hx'i
    exact hx'i
  have hmz : m * zM = zM * m := hθ (by
    rw [map_mul, map_mul, hm]
    exact hx'K _ (zG_mem_KG ψ hdec hinf))
  have hmd : m * dM = dM * m := hθ (by
    rw [map_mul, map_mul, hm]
    exact hx'K _ (dG_mem_KG ψ hdec hinf))
  have hm4 : m * m * (m * m) = 1 := hθ (by
    rw [map_mul, map_mul, hm, hx2, hjj, map_one])
  have hm2 : m * m ≠ 1 := fun h => by
    have h1 : x' * x' = 1 := by rw [← hm, ← map_mul, h, map_one]
    rw [hx2] at h1
    rw [h1, orderOf_one] at hj
    norm_num at hj
  obtain ⟨a, b, k, l, ha, hb, hk, hl, rfl⟩ := centralizer_S0M m hmz hmd hm4 hm2
  have hr : emb ψ (r1M ^ a * r2M ^ b) ∈ R1G ψ := (mem_R1G_iff ψ _).2 ⟨a, b, ha, hb, rfl⟩
  have hyk : ∀ c ∈ KG ψ, emb ψ (yM ^ k * fM ^ l) * c = c * emb ψ (yM ^ k * fM ^ l) := by
    intro c hc
    have e1 : emb ψ (yM ^ k * fM ^ l) = (emb ψ (r1M ^ a * r2M ^ b))⁻¹ * x' := by
      rw [← hm, ← map_inv, ← map_mul]
      exact congrArg (emb ψ) (by group)
    rw [e1]
    have h1 : Commute (emb ψ (r1M ^ a * r2M ^ b)) c := comm_R1G_KG ψ hr hc
    have h2 := hx'K c hc
    calc (emb ψ (r1M ^ a * r2M ^ b))⁻¹ * x' * c = (emb ψ (r1M ^ a * r2M ^ b))⁻¹ * (x' * c) := by
          group
      _ = (emb ψ (r1M ^ a * r2M ^ b))⁻¹ * (c * x') := by rw [h2]
      _ = ((emb ψ (r1M ^ a * r2M ^ b))⁻¹ * c) * x' := by group
      _ = (c * (emb ψ (r1M ^ a * r2M ^ b))⁻¹) * x' := by rw [h1.inv_left.eq]
      _ = c * ((emb ψ (r1M ^ a * r2M ^ b))⁻¹ * x') := by group
  rcases hk with rfl | rfl
  · exact ⟨l, hl, by simpa using hyk⟩
  · refine ⟨l, hl, fun c hc => ?_⟩
    have e0 : yM * fM ^ l = (yM ^ 3 * fM ^ l)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      have hyf : Commute yM fM := fM_comm yM
      have hfy : Commute (fM ^ l) (yM ^ 3) := hyf.symm.pow_pow l 3
      calc yM * fM ^ l * (yM ^ 3 * fM ^ l) = yM * (fM ^ l * yM ^ 3) * fM ^ l := by group
        _ = yM * (yM ^ 3 * fM ^ l) * fM ^ l := by rw [hfy.eq]
        _ = yM ^ 4 * (fM ^ l * fM ^ l) := by group
        _ = 1 := by rw [yM_four, ← pow_add, ← two_mul, pow_mul, fM_pow_two, one_pow, one_mul]
    have e : emb ψ (yM * fM ^ l) = (emb ψ (yM ^ 3 * fM ^ l))⁻¹ := by
      rw [← map_inv, e0]
    rw [e]
    exact (Commute.inv_left (hyk c hc)).eq

end Involution

section NotSeven

open CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G] {i : G} (ψ : centralizer ({i} : Set G) ≃* M480)

theorem mem_sylow_smul_iff {A : Type*} [Group A] {p : ℕ} (P : Sylow p A) (β x : A) :
    x ∈ ((β • P : Sylow p A) : Subgroup A) ↔ β⁻¹ * x * β ∈ (P : Subgroup A) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem isInner_of_conj {Y : Type} [Group Y] {α β : MulAut Y} (h : IsInner (β * α * β⁻¹)) :
    IsInner α := by
  obtain ⟨k, hk⟩ := h
  refine ⟨β⁻¹ k, fun y => ?_⟩
  have := hk (β y)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at this
  have e := congrArg (fun x => β⁻¹ x) this
  simp only [MulAut.inv_apply_self, map_mul, map_inv] at e
  rw [e]

theorem card_KG_le_of_comm
    (hK : ∀ k ∈ KG ψ, i * k = k * i) : Nat.card (KG ψ) ≤ 72 := by
  have hθ := emb_injective ψ
  have hrep : ∀ x : KG ψ, ∃ p : Fin 3 × Fin 3 × Fin 4 × Fin 2,
      (x : G) = emb ψ (r1M ^ p.1.val * r2M ^ p.2.1.val * (zM ^ p.2.2.1.val * dM ^ p.2.2.2.val)) := by
    intro x
    have hxi : (x : G) ∈ centralizer ({i} : Set G) :=
      mem_centralizer_singleton_iff.2 (hK x x.2).symm
    obtain ⟨m, hm⟩ : ∃ m : M480, emb ψ m = x := by
      rw [← range_emb ψ] at hxi
      exact hxi
    have hxC : (x : G) ∈ CG ψ := Subgroup.commutator_le_self (CG ψ) x.2
    have hm1 : m * r1M = r1M * m := hθ (by
      rw [map_mul, map_mul, hm]
      exact (mem_centralizer_iff.1 hxC _ ⟨r1M, subset_closure (Or.inl rfl), rfl⟩).symm)
    have hm2 : m * r2M = r2M * m := hθ (by
      rw [map_mul, map_mul, hm]
      exact (mem_centralizer_iff.1 hxC _ ⟨r2M, subset_closure (Or.inr rfl), rfl⟩).symm)
    obtain ⟨a, b, k, l, ha, hb, hk, hl, he⟩ := centralizer_R1M m hm1 hm2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨k, hk⟩, ⟨l, hl⟩), by rw [← hm, he]⟩
  choose g hg using hrep
  have hinj : Function.Injective g := fun x y hxy => Subtype.ext (by rw [hg x, hg y, hxy])
  calc Nat.card (KG ψ) ≤ Nat.card (Fin 3 × Fin 3 × Fin 4 × Fin 2) :=
        Nat.card_le_card_of_injective g hinj
    _ = 72 := by simp

theorem not_seven [Finite G]
    (hi : orderOf i = 2) (hdec : CG ψ = R1G ψ ⊔ KG ψ) (hinf : R1G ψ ⊓ KG ψ = ⊥)
    (K' : Type) [Field K'] [Finite K'] (h7 : Nat.card K' = 7) (eK : KG ψ ≃* PSL2 K') {l : ℕ}
    (hl : l < 2) (hw : ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l)) :
    False := by
  have hθ := emb_injective ψ
  have hzK := zG_mem_KG ψ hdec hinf
  have hdK := dG_mem_KG ψ hdec hinf
  have hfK := fG_mem_KG ψ hdec hinf
  set φ := phiT ψ with hφ
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [card_TG ψ] at hcard
  have hAut := card_mulAut_of_seven K' h7 eK
  set wT : TG ψ := ⟨emb ψ (yM * fM ^ l), yfG_mem_TG ψ l⟩ with hwT
  have hwker : wT ∈ φ.ker := (mem_ker_phiT_iff ψ wT).2 hw
  have hw4 : orderOf wT = 4 := by
    rw [← Subgroup.orderOf_coe, orderOf_injective _ hθ]
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := yM * fM ^ l)
      (by rw [pow_one, pow_two]; exact yfM_sq_ne l) (by norm_num; exact yfM_four l)
    simpa using h
  have hzT : emb ψ zM ∈ TG ψ := ⟨zM, zM_mem_T0M, rfl⟩
  have hdT : emb ψ dM ∈ TG ψ := ⟨dM, dM_mem_T0M, rfl⟩
  have hfT : emb ψ fM ∈ TG ψ := ⟨fM, fM_mem_T0M, rfl⟩
  set Q : Subgroup (TG ψ) := centralizer ({⟨emb ψ zM, hzT⟩, ⟨emb ψ dM, hdT⟩} : Set (TG ψ))
    with hQ
  have hkerQ : φ.ker ≤ Q := by
    intro t ht
    rw [hQ, mem_centralizer_iff]
    have h := (mem_ker_phiT_iff ψ t).1 ht
    rintro s (rfl | rfl)
    · exact Subtype.ext (h _ hzK).symm
    · exact Subtype.ext (h _ hdK).symm
  have hfQ : (⟨emb ψ fM, hfT⟩ : TG ψ) ∈ Q := by
    rw [hQ, mem_centralizer_iff]
    rintro s (rfl | rfl)
    · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        fM_comm])
    · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        fM_comm])
  have hfker : (⟨emb ψ fM, hfT⟩ : TG ψ) ∉ φ.ker := by
    intro h
    have hc := (mem_ker_phiT_iff ψ _).1 h
    have hc' : ∀ k ∈ KG ψ, i * k = k * i := fun k hk => by
      rw [← emb_fM ψ hi]
      exact hc k hk
    have h1 := card_KG_le_of_comm ψ hc'
    rw [Nat.card_congr eK.toEquiv, card_of_seven K' h7 (MulEquiv.refl _)] at h1
    norm_num at h1
  have hQ8 : Nat.card Q ≤ 8 := by
    have hrep : ∀ x : Q, ∃ p : Fin 4 × Fin 2,
        ((x : TG ψ) : G) = emb ψ (yM ^ p.1.val * fM ^ p.2.val) := by
      intro x
      obtain ⟨m, hm, hme⟩ := (x : TG ψ).2
      have hxz : ((x : TG ψ) : G) * emb ψ zM = emb ψ zM * (x : TG ψ) :=
        congrArg Subtype.val (mem_centralizer_iff.1 x.2 _ (Or.inl rfl)).symm
      have hxd : ((x : TG ψ) : G) * emb ψ dM = emb ψ dM * (x : TG ψ) :=
        congrArg Subtype.val (mem_centralizer_iff.1 x.2 _ (Or.inr rfl)).symm
      rw [← hme] at hxz hxd
      have hmz : m * zM = zM * m := hθ (by rw [map_mul, map_mul]; exact hxz)
      have hmd : m * dM = dM * m := hθ (by rw [map_mul, map_mul]; exact hxd)
      obtain ⟨k, n, hk, hn, he⟩ := T0M_cent hm hmz hmd
      exact ⟨(⟨k, hk⟩, ⟨n, hn⟩), by rw [← hme, he]⟩
    choose g hg using hrep
    have hinj : Function.Injective g := fun x y hxy =>
      Subtype.ext (Subtype.ext (by rw [hg x, hg y, hxy]))
    calc Nat.card Q ≤ Nat.card (Fin 4 × Fin 2) := Nat.card_le_card_of_injective g hinj
      _ = 8 := by simp
  have hker4 : Nat.card φ.ker ≤ 4 := by
    have hlt : φ.ker < Q := lt_of_le_of_ne hkerQ (fun h => hfker (h ▸ hfQ))
    have h1 := Subgroup.card_lt_of_lt hlt
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hkerQ
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact Nat.card_pos.ne' hc
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hc
      omega
    have : 2 ≤ c := by omega
    nlinarith
  have hzw : zpowers wT ≤ φ.ker := (zpowers_le).2 hwker
  have hzw4 : Nat.card (zpowers wT) = 4 := by rw [Nat.card_zpowers, hw4]
  have hkereq : zpowers wT = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hzw (by rw [hzw4]; exact hker4)
  have hker4' : Nat.card φ.ker = 4 := by rw [← hkereq, hzw4]
  have hrange : Nat.card φ.range = 16 := by
    rw [hker4'] at hcard
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrp : IsPGroup 2 φ.range := IsPGroup.of_card (n := 4) (by rw [hrange]; norm_num)
  obtain ⟨P₁, hP₁⟩ := hrp.exists_le_sylow
  have hP₁eq : φ.range = P₁ := by
    refine Subgroup.eq_of_le_of_card_ge hP₁ ?_
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 P₁.isPGroup'
    have hdvd : 2 ^ n ∣ 336 := by
      rw [← hn, ← hAut]
      exact Subgroup.card_subgroup_dvd_card _
    have hn4 : n ≤ 4 := by
      by_contra hn5
      have : 2 ^ 5 ∣ 336 := (pow_dvd_pow 2 (by omega : 5 ≤ n)).trans hdvd
      norm_num at this
    rw [hn, hrange]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 16 := by norm_num
  obtain ⟨-, hL⟩ := nonempty_equiv_GL32 K' h7 eK
  have hL' := l27AutFact (KG ψ) hL
  set S0K : Subgroup (KG ψ) := (closure ({emb ψ zM, emb ψ dM} : Set G)).subgroupOf (KG ψ)
    with hS0K
  have hS0le : closure ({emb ψ zM, emb ψ dM} : Set G) ≤ KG ψ := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hzK
    · exact hdK
  have hS08 : Nat.card S0K = 8 := by
    obtain ⟨e8⟩ := nonempty_S0G ψ
    rw [hS0K, Nat.card_congr (subgroupOfEquivOfLe hS0le).toEquiv, Nat.card_congr e8.toEquiv,
      DihedralGroup.nat_card]
  obtain ⟨α, hαout, hα2, -⟩ := hL'.exists_outer_inv S0K hS08
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαout IsInner.one
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hαp : IsPGroup 2 (zpowers α) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hαord, pow_one])
  obtain ⟨P₂, hP₂⟩ := hαp.exists_le_sylow
  obtain ⟨β, hβ⟩ := MulAction.exists_smul_eq (MulAut (KG ψ)) P₂ P₁
  have hγ : β * α * β⁻¹ ∈ φ.range := by
    rw [hP₁eq, ← hβ, mem_sylow_smul_iff]
    have : β⁻¹ * (β * α * β⁻¹) * β = α := by group
    rw [this]
    exact hP₂ (mem_zpowers α)
  obtain ⟨t, ht⟩ := hγ
  have hγout : ¬ IsInner (β * α * β⁻¹) := fun h => hαout (isInner_of_conj h)
  have hγ2 : φ (t * t) = 1 := by
    rw [map_mul, ht]
    calc β * α * β⁻¹ * (β * α * β⁻¹) = β * (α * α) * β⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have htt : t * t ∈ zpowers wT := by rw [hkereq]; exact hγ2
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw4] at htt
  obtain ⟨n, hn, hne⟩ := Finset.mem_image.1 htt
  rw [Finset.mem_range] at hn
  obtain ⟨m, hm, hme⟩ := t.2
  have hmm : m * m = (yM * fM ^ l) ^ n := hθ (by
    rw [map_mul, hme, ← Subgroup.coe_mul, ← hne, map_pow]
    rfl)
  obtain ⟨k, e, n', hk, he, hn', hmeq⟩ := T0M_quot hl hm ⟨n, hn, hmm⟩
  have hsK : emb ψ (zM ^ k * dM ^ e) ∈ KG ψ := by
    rw [map_mul, map_pow, map_pow]
    exact mul_mem (pow_mem hzK k) (pow_mem hdK e)
  apply hγout
  rw [← ht]
  refine ⟨⟨emb ψ (zM ^ k * dM ^ e), hsK⟩, fun y => Subtype.ext ?_⟩
  rw [phiT_apply]
  have htw : (t : G) = emb ψ (zM ^ k * dM ^ e) * (emb ψ (yM * fM ^ l)) ^ n' := by
    rw [← hme, hmeq, map_mul, map_pow]
  have hwn : ∀ c ∈ KG ψ, (emb ψ (yM * fM ^ l)) ^ n' * c = c * (emb ψ (yM * fM ^ l)) ^ n' :=
    fun c hc => by
      have hcm : Commute (emb ψ (yM * fM ^ l)) c := hw c hc
      exact (hcm.pow_left n').eq
  rw [htw]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc emb ψ (zM ^ k * dM ^ e) * emb ψ (yM * fM ^ l) ^ n' * (y : G) *
        (emb ψ (zM ^ k * dM ^ e) * emb ψ (yM * fM ^ l) ^ n')⁻¹ =
      emb ψ (zM ^ k * dM ^ e) * (emb ψ (yM * fM ^ l) ^ n' * (y : G)) *
        (emb ψ (yM * fM ^ l) ^ n')⁻¹ * (emb ψ (zM ^ k * dM ^ e))⁻¹ := by group
    _ = emb ψ (zM ^ k * dM ^ e) * ((y : G) * emb ψ (yM * fM ^ l) ^ n') *
        (emb ψ (yM * fM ^ l) ^ n')⁻¹ * (emb ψ (zM ^ k * dM ^ e))⁻¹ := by rw [hwn _ y.2]
    _ = emb ψ (zM ^ k * dM ^ e) * (y : G) * (emb ψ (zM ^ k * dM ^ e))⁻¹ := by group

end NotSeven

section Main

variable {G : Type} [Group G] [Finite G]

theorem threeLocal_R1
    (hone : OneClass G) {i : G} (hi : orderOf i = 2)
    (ψ : centralizer ({i} : Set G) ≃* M480) :
    CG ψ = R1G ψ ⊔ KG ψ ∧ R1G ψ ⊓ KG ψ = ⊥ ∧ Nonempty (KG ψ ≃* alternatingGroup (Fin 6)) ∧
      ∃ l < 2, ∀ k ∈ KG ψ, emb ψ (yM * fM ^ l) * k = k * emb ψ (yM * fM ^ l) := by
  obtain ⟨K', hF, hFin, hq, hdec, hinf, ⟨eK⟩⟩ := split_R1G hone hi ψ
  have hperfX : Group.IsPerfect (PSL2 K') :=
    (isPerfect_card_hopfMultiplier_dvd_six K' hq (MulEquiv.refl _)).1
  have hperfK : Group.IsPerfect (KG ψ) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hperf : ⁅KG ψ, KG ψ⁆ = KG ψ := Subgroup.commutator_eq_self
  obtain ⟨j, hj, -, hjK⟩ := exists_involution_centralizing ψ K' hq eK
  obtain ⟨l, hl, hw⟩ := exists_yf_centralizing ψ hone hi hdec hinf hperf hj hjK
  refine ⟨hdec, hinf, ?_, l, hl, hw⟩
  rcases hq with h7 | h9
  · exact (not_seven ψ hi hdec hinf K' h7 eK hl hw).elim
  · have : Fintype K' := Fintype.ofFinite K'
    obtain ⟨e6⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        K' (by rw [Fintype.card_eq_nat_card, h9])
    exact ⟨eK.trans e6⟩

omit [Finite G] in
theorem centralizer_map_conj (c : G) (H : Subgroup G) :
    centralizer ((H.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, by simp [mul_assoc]⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    have h1 := mem_centralizer_iff.1 hx (c * h * c⁻¹) ⟨h, hh, rfl⟩
    calc h * (c⁻¹ * x * c) = c⁻¹ * ((c * h * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * h * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * x * c * h := by group
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have h1 := mem_centralizer_iff.1 hy h hh
    show c * h * c⁻¹ * (c * y * c⁻¹) = c * y * c⁻¹ * (c * h * c⁻¹)
    calc c * h * c⁻¹ * (c * y * c⁻¹) = c * (h * y) * c⁻¹ := by group
      _ = c * (y * h) * c⁻¹ := by rw [h1]
      _ = c * y * c⁻¹ * (c * h * c⁻¹) := by group

end Main

end CFSG.OddStandard.ONanRec.B2
