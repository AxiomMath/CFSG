module

public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace AscThmA

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

private theorem four_le_card_galoisField (hq : 5 ≤ p ^ f) : 4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  omega

theorem mem_of_uniqueInvolution [Finite G] {K A : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) :
    z ∈ A := by
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

theorem inf_eq_bot_of_uniqueInvolution_not_mem [Finite G] {K V N : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hVK : V ≤ K) (hV2 : IsPGroup 2 V) (hzN : z ∉ N) :
    V ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hxne : x ≠ 1 := fun h => hx1 (by rw [h]; exact one_mem _)
  have hxV : IsPGroup 2 (Subgroup.zpowers x) := hV2.to_le (Subgroup.zpowers_le.mpr hx.1)
  have hcard : 2 ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    have h1 : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.mp h)
    have h2 : 0 < orderOf x := orderOf_pos x
    omega
  have hzx := mem_of_uniqueInvolution hz (Subgroup.zpowers_le.mpr (hVK hx.1)) hxV hcard
  exact hzN ((Subgroup.zpowers_le.mpr hx.2) hzx)

theorem exists_sylow_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ V : Subgroup G, IsSylow2In V K ∧ V ∈ RSet Ω ∧ z ∈ V := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  have h8 : 8 ≤ Nat.card V := hΩ.eight_le_of_mem_RSet hp hVR
  exact ⟨V, hV, hVR, mem_of_uniqueInvolution hz hV.1 hV.2.1 (by omega)⟩

private theorem isPGroup_zpowers_mk [Finite G] {C V : Subgroup G} (hV : IsPGroup 2 V)
    (hVC : V ≤ C) {v : G}
    (hv : v ∈ V) : IsPGroup 2 (Subgroup.zpowers (⟨v, hVC hv⟩ : ↥C)) := by
  obtain ⟨n, hn⟩ := (hV.to_le (Subgroup.zpowers_le.mpr hv)).exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
  exact hn

theorem le_or_commutator_le_oddCoreOf [Finite G] (_hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (N : Subgroup G) [N.Normal] :
    K ≤ N ∨ ⁅K, N ⊓ Subgroup.centralizer ({z} : Set G)⁆ ≤
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hKC : K ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = z := (hz.unique z' hz'.mem hzsq).resolve_left hzne
  have hsubH : (K.subgroupOf C).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      ((CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hKC).mpr hz'.subnormal)
      Subgroup.IsSubnormal.top
  let π : ↥C →* ↥C ⧸ classicalInvolutionOddCore ↥C :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let ψ : ↥K →* ↥((K.subgroupOf C).map π) :=
    (π.comp (Subgroup.inclusion hKC)).codRestrict ((K.subgroupOf C).map π)
      fun x => ⟨Subgroup.inclusion hKC x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : G), ha⟩, rfl⟩
  have hψker : ψ.ker = classicalInvolutionOddCore ↥K := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    have h1 := CFSG.ComponentClassification.OddCore.subnormal_mem_iff hz'.subnormal (x : G) x.2
    have h2 : (π (Subgroup.inclusion hKC x) = 1) ↔
        (Subgroup.inclusion hKC x) ∈ classicalInvolutionOddCore ↥C :=
      QuotientGroup.eq_one_iff _
    constructor
    · intro h
      refine h1.mpr ⟨hKC x.2, ?_⟩
      exact h2.mp h
    · intro h
      obtain ⟨hup, h3⟩ := h1.mp h
      exact h2.mpr h3
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  let e' : ↥((K.subgroupOf C).map π) ≃* SL(2, GaloisField p f) :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hψker)).trans e
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_card_galoisField (p := p) hq
  have hqs : CFSG.IsQuasisimple ↥((K.subgroupOf C).map π) :=
    isQuasisimple_of_mulEquiv e'.symm
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
        (GaloisField p f) le_rfl (Or.inr (by omega)) (Or.inr (by omega)))
  have hcomp : CFSG.IsComponent ((K.subgroupOf C).map π) := ⟨hqs, hsubH.map hπs⟩
  have hNn : ((N.subgroupOf C).map π).Normal :=
    (Subgroup.Normal.subgroupOf (inferInstance : N.Normal) C).map π hπs
  rcases component_normal_subgroup hcomp hNn with h | h
  · left
    have hle : K.subgroupOf C ≤ N.subgroupOf C ⊔ classicalInvolutionOddCore ↥C := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_map_of_mem π hx)
      have h5 : y⁻¹ * x ∈ classicalInvolutionOddCore ↥C := by
        have : π y = π x := hyx
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
        exact this
      have h6 : x = y * (y⁻¹ * x) := by group
      rw [h6]
      exact Subgroup.mul_mem_sup hy h5
    refine hΩ.le_of_forall_isSylow2In hK fun V hV v hv => ?_
    have hv' : (⟨v, hKC (hV.1 hv)⟩ : ↥C) ∈ K.subgroupOf C := hV.1 hv
    exact mem_of_isPGroup_of_mem_sup_of_odd (CFSG.ComponentClassification.OddCore.odd_card ↥C)
      (isPGroup_zpowers_mk hV.2.1 (hV.1.trans hKC) hv) (hle hv')
  · right
    refine Subgroup.commutator_le.mpr fun k hk y hy => ?_
    have h1 : ⁅π ⟨k, hKC hk⟩, π ⟨y, hy.2⟩⁆ ∈
        ⁅(K.subgroupOf C).map π, (N.subgroupOf C).map π⁆ :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_map_of_mem π (show _ ∈ K.subgroupOf C from hk))
        (Subgroup.mem_map_of_mem π (show _ ∈ N.subgroupOf C from hy.1))
    rw [h, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    have hkyC : ⁅k, y⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem (hKC hk) hy.2) (C.inv_mem (hKC hk))) (C.inv_mem hy.2)
    exact mem_oddCoreOf_iff.mpr ⟨hkyC, h1⟩

theorem isComponent_conjSub {L : Subgroup G} (hL : IsComponent L) (k : G) :
    IsComponent (conjSub k L) :=
  isComponent_map_mulEquiv (MulAut.conj k) hL

theorem mul_comm_of_ne [Finite G] {L L' : Subgroup G} (hL : IsComponent L) (hL' : IsComponent L')
    (hne : L ≠ L') {x y : G} (hx : x ∈ L) (hy : y ∈ L') : x * y = y * x := by
  rcases distinct_components_commute hL hL' with h | h
  · exact absurd h hne
  · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx)
      y hy).symm

theorem normal_layer : (layer G).Normal := by
  have := (layer_characteristic (G := G))
  infer_instance

theorem conjSub_eq_of_normal (X : Subgroup G) [hX : X.Normal] (y : G) : conjSub y X = X := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := hX.conj_mem _ h y
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at this
  · intro h
    have := hX.conj_mem _ h y⁻¹
    rwa [inv_inv] at this

theorem commutator_sSup_components {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ B ∈ 𝒮, IsComponent B) :
    ⁅sSup 𝒮, sSup 𝒮⁆ = sSup 𝒮 := by
  refine le_antisymm (Subgroup.commutator_le_self _) (sSup_le fun B hB => ?_)
  calc B = ⁅B, B⁆ := (Subgroup.isPerfect_iff.mp (h𝒮 B hB).1.1).symm
    _ ≤ ⁅sSup 𝒮, sSup 𝒮⁆ := Subgroup.commutator_mono (le_sSup hB) (le_sSup hB)

theorem sSup_le_layer {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ B ∈ 𝒮, IsComponent B) :
    sSup 𝒮 ≤ layer G :=
  sSup_le fun B hB => component_le_layer (h𝒮 B hB)

theorem oddCoreOf_eq_inf [Finite G] (X : Subgroup G) [X.Normal] :
    oddCoreOf X = X ⊓ classicalInvolutionOddCore G :=
  CFSG.ComponentClassification.OddCore.normal_intersection G X

theorem normal_oddCoreOf [Finite G] (X : Subgroup G) [X.Normal] : (oddCoreOf X).Normal := by
  rw [oddCoreOf_eq_inf]
  infer_instance

theorem odd_card_oddCoreOf [Finite G] (X : Subgroup G) [X.Normal] :
    Odd (Nat.card ↥(oddCoreOf X)) := by
  rw [oddCoreOf_eq_inf]
  exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
    (Subgroup.card_dvd_of_le inf_le_right)

theorem commutator_oddCoreOf_eq_bot [Finite G] {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ B ∈ 𝒮, IsComponent B) (hX : (sSup 𝒮).Normal) :
    ⁅oddCoreOf (sSup 𝒮), sSup 𝒮⁆ = ⊥ := by
  have hOn : (oddCoreOf (sSup 𝒮)).Normal := normal_oddCoreOf _
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun B hB => ?_
  have hBc := h𝒮 B hB
  have hOX : oddCoreOf (sSup 𝒮) ≤ sSup 𝒮 := by
    rw [oddCoreOf_eq_inf]
    exact inf_le_left
  have hXn : sSup 𝒮 ≤ Subgroup.normalizer (B : Set G) :=
    (sSup_le_layer h𝒮).trans (layer_le_normalizer hBc)
  have hcomm : ⁅B, oddCoreOf (sSup 𝒮)⁆ ≤ B ⊓ oddCoreOf (sSup 𝒮) := by
    rw [Subgroup.commutator_le]
    intro b hb w hw
    refine ⟨?_, ?_⟩
    · have hw' := (Subgroup.mem_normalizer_iff.mp (hXn (hOX hw)) b⁻¹).mp (B.inv_mem hb)
      have : ⁅b, w⁆ = b * (w * b⁻¹ * w⁻¹) := by group
      rw [this]
      exact B.mul_mem hb hw'
    · have h1 : b * w * b⁻¹ ∈ oddCoreOf (sSup 𝒮) := by
        have := hOn.conj_mem w hw b
        simpa using this
      have : ⁅b, w⁆ = (b * w * b⁻¹) * w⁻¹ := by group
      rw [this]
      exact (oddCoreOf (sSup 𝒮)).mul_mem h1 ((oddCoreOf (sSup 𝒮)).inv_mem hw)
  have hnormB : ((oddCoreOf (sSup 𝒮)).subgroupOf B).Normal := Subgroup.Normal.subgroupOf hOn B
  have hq := hBc.1
  rcases quasisimple_normal_subgroups hq hnormB with htop | hcen
  · exfalso
    have hBO : B ≤ oddCoreOf (sSup 𝒮) := Subgroup.subgroupOf_eq_top.mp htop
    have hodd : Odd (Nat.card B) :=
      (odd_card_oddCoreOf (sSup 𝒮)).of_dvd_nat (Subgroup.card_dvd_of_le hBO)
    have hsolv : Group.IsSolvable B := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial B := isQuasisimple_nontrivial hq
    have : Group.IsPerfect B := hq.1
    exact Group.IsPerfect.not_isSolvable B hsolv
  · have hcB : ⁅⁅B, oddCoreOf (sSup 𝒮)⁆, B⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      obtain ⟨hxB, hxO⟩ := hcomm hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := Subgroup.mem_center_iff.mp (hcen (show (⟨x, hxB⟩ : B) ∈
        (oddCoreOf (sSup 𝒮)).subgroupOf B from hxO)) ⟨b, hb⟩
      exact congrArg Subtype.val this
    have := perfect_double_commutator hq.1 hcB
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact this

theorem commutator_eq_bot_of_le_oddCoreOf [Finite G] {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ B ∈ 𝒮, IsComponent B) (hX : (sSup 𝒮).Normal) {R : Subgroup G}
    (hR : ⁅R, sSup 𝒮⁆ ≤ oddCoreOf (sSup 𝒮)) : ⁅R, sSup 𝒮⁆ = ⊥ := by
  have h1 : ⁅⁅sSup 𝒮, R⁆, sSup 𝒮⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅sSup 𝒮, R⁆, sSup 𝒮⁆ ≤ ⁅oddCoreOf (sSup 𝒮), sSup 𝒮⁆ := by
          rw [Subgroup.commutator_comm (sSup 𝒮) R]
          exact Subgroup.commutator_mono hR le_rfl
      _ = ⊥ := commutator_oddCoreOf_eq_bot h𝒮 hX
  have hP : Group.IsPerfect ↥(sSup 𝒮) :=
    Subgroup.isPerfect_iff.mpr (commutator_sSup_components h𝒮)
  have := perfect_double_commutator hP h1
  rwa [Subgroup.commutator_comm] at this

theorem commutator_eq_bot_of_le_oddCoreOf_component [Finite G] {L : Subgroup G}
    (hL : IsComponent L) (hLn : L.Normal) {R : Subgroup G} (hR : ⁅R, L⁆ ≤ oddCoreOf L) :
    ⁅R, L⁆ = ⊥ := by
  have := commutator_eq_bot_of_le_oddCoreOf (𝒮 := {L}) (fun B hB => hB ▸ hL)
    (by simpa using hLn) (by simpa using hR)
  simpa using this

theorem le_or_commutator_eq_bot_of_normal_component [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {N : Subgroup G} (hN : IsComponent N) (hNn : N.Normal)
    (hNz : N ≤ Subgroup.centralizer ({z} : Set G)) : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  rcases le_or_commutator_le_oddCoreOf hp hq hΩ hK hz N with h | h
  · exact Or.inl h
  · right
    rw [inf_eq_left.mpr hNz] at h
    refine commutator_eq_bot_of_le_oddCoreOf_component hN hNn ?_
    have h1 : ⁅K, N⁆ ≤ N := Subgroup.commutator_le_right K N
    have h2 : N ⊓ oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ oddCoreOf N :=
      inf_le_oddCoreOf_of_le_normalizer
        (fun g hg => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hNz hg)))
        ((oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    exact fun x hx => h2 ⟨h1 hx, h hx⟩

@[expose] def Comm613On (Ω : Set (Subgroup G)) : Prop :=
  ∀ R ∈ RSet Ω, ∀ X : Subgroup G, X.Normal → R ⊓ X = ⊥ → ⁅R, X⁆ ≤ oddCoreOf X

theorem comm613On_of_l6_13 [Finite G] (h : L6_13 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : Comm613On Ω := by
  intro R hR X hX hRX
  exact (h hp hq G Ω hΩ R hR ⊤ X le_top le_top (fun y _ => conjSub_eq_of_normal X y) hRX).2

end AscThmA

end CFSG.ClassicalInvolution.Asc77
