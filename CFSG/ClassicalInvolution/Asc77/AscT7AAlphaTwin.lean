module

public import CFSG.ClassicalInvolution.Asc77.AscT7AAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Group G] in
theorem conjSub_eq_self_of_mem_centralizer [Group G] {E : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (E : Set G)) : conjSub c E = E := by
  ext x
  rw [mem_conjSub_iff]
  have hcomm : ∀ y ∈ E, y * c = c * y := fun y hy => Subgroup.mem_centralizer_iff.mp hc y hy
  constructor
  · intro hx
    have h1 : c * (c⁻¹ * x * c) = (c⁻¹ * x * c) * c := (hcomm _ hx).symm
    have h2 : x = c⁻¹ * x * c := by
      calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
        _ = (c⁻¹ * x * c) * c * c⁻¹ := by rw [h1]
        _ = c⁻¹ * x * c := by group
    rwa [← h2] at hx
  · intro hx
    have h1 : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcomm x hx]
        _ = x := by group
    rwa [h1]

theorem exists_fixed_mul_of_odd [Finite G] {O : Subgroup G} (hO : Odd (Nat.card O)) {t ℓ : G}
    (ht : t * t = 1) (htO : t ∈ Subgroup.normalizer (O : Set G))
    (hℓO : ℓ ∈ Subgroup.normalizer (O : Set G)) (hc : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ O) :
    ∃ o ∈ O, t * (ℓ * o) * t⁻¹ = ℓ * o := by
  have hn : ∀ {x : G}, x ∈ Subgroup.normalizer (O : Set G) → ∀ {y : G}, y ∈ O →
      x * y * x⁻¹ ∈ O := fun {x} hx {y} hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  set o₀ : G := ℓ⁻¹ * t * ℓ * t⁻¹ with ho₀
  have ho₀O : o₀ ∈ O := by
    have h1 := hn (Subgroup.inv_mem _ hℓO) hc
    have e : ℓ⁻¹ * (t * ℓ * t⁻¹ * ℓ⁻¹) * ℓ⁻¹⁻¹ = o₀ := by rw [ho₀]; group
    rwa [e] at h1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hrel : o₀ * (t * o₀ * t⁻¹) = 1 := by
    have e : o₀ * (t * o₀ * t⁻¹) = ℓ⁻¹ * (t * (t * ℓ * t⁻¹) * t⁻¹) := by
      rw [ho₀]; group
    rw [e]
    have : t * (t * ℓ * t⁻¹) * t⁻¹ = ℓ := by
      calc t * (t * ℓ * t⁻¹) * t⁻¹ = (t * t) * ℓ * (t⁻¹ * t⁻¹) := by group
        _ = ℓ := by rw [ht, htinv, ht]; group
    rw [this]
    group
  let φ : ↥O → ↥O := fun o => ⟨o₀ * (t * (o : G) * t⁻¹), O.mul_mem ho₀O (hn htO o.2)⟩
  have hφφ : ∀ o, φ (φ o) = o := by
    intro o
    apply Subtype.ext
    show o₀ * (t * (o₀ * (t * (o : G) * t⁻¹)) * t⁻¹) = (o : G)
    have e : o₀ * (t * (o₀ * (t * (o : G) * t⁻¹)) * t⁻¹) =
        (o₀ * (t * o₀ * t⁻¹)) * ((t * t) * (o : G) * (t⁻¹ * t⁻¹)) := by group
    rw [e, hrel, ht, htinv, ht]
    group
  let σ : Equiv.Perm ↥O := ⟨φ, φ, hφφ, hφφ⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext o
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hφφ o)
  have : Fintype ↥O := Fintype.ofFinite ↥O
  have hodd : ¬ 2 ∣ Fintype.card ↥O := by
    rw [← Nat.card_eq_fintype_card]
    exact hO.not_two_dvd_nat
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  refine ⟨o, o.2, ?_⟩
  have h1 : o₀ * (t * (o : G) * t⁻¹) = (o : G) := congrArg Subtype.val ho
  have e : t * (ℓ * (o : G)) * t⁻¹ = (t * ℓ * t⁻¹) * (t * (o : G) * t⁻¹) := by group
  have e2 : t * ℓ * t⁻¹ = ℓ * o₀ := by rw [ho₀]; group
  rw [e, e2, mul_assoc, h1]

theorem centralizer_le_normalizer_alpha {B E : Subgroup G} {u z : G} (hE : IsElemAbelian2 E 2)
    (hEB : E ≤ B)
    (h3 : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G))) :
    Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  intro c hc
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub c E = E := conjSub_eq_self_of_mem_centralizer hc
  have h2 := alphaOf_conjSub c E
  rw [h1, h3 E hEB hE] at h2
  exact h2.symm

theorem oddCore_le_normalizer_alpha [Finite G] {B : Subgroup G} {u z : G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hBC : B ≤ Subgroup.centralizer ({z} : Set G))
    (h3 : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G))) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({z} : Set G))) hB
    (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => inf_le_right.trans ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact centralizer_le_normalizer_alpha hE2 hE.1 h3

theorem isSubnormal_centralizer (hΩ : HypOmegaMod p f Ω) {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) : IsSubnormal L (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'⟩ := hΩ.classical L hL
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = z := (hz.unique z' hz'.mem hzsq).resolve_left hzne
  exact hz'.subnormal

theorem commutator_twin_mem_oddCoreOf [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    ∀ ℓ ∈ L, ⁅t, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  have hLΩ : L ∈ Ω := hL.1
  have hzL := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hJΩ : J ∈ Ω := h.hJ.1
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 L hL
  have hRsyl : IsSylow2In R J := hΩ.isSylow2In_of_mem_RSet_of_le hp hJΩ hR hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hzL hRN
  have hJnot : J ∉ twinSet Ω L := by
    rintro ⟨-, z₀, hz₀L, hz₀J⟩
    exact h.t_ne_z ((h.ht.eq hz₀J).trans (hzL.eq hz₀L).symm)
  have hV : IsSylow2In R (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hRJ hRC, hRsyl.2.1, fun V' hV' hV'p hRV' =>
      hRsyl.2.2 V' (hV'.trans inf_le_left) hV'p hRV'⟩
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  rcases l6_2 p f hp hq G Ω hΩ L hLΩ z hzL J hJΩ hJnot t h.ht R hV htR with h1 | h1 | h1 | h1
  · exfalso
    have := h8
    rw [h1.1, Nat.card_zpowers, htord] at this
    omega
  · exfalso
    have := h8
    rw [h1.1, Nat.card_zpowers, htord] at this
    omega
  · exfalso
    obtain ⟨R', hR', hle, hcyc, hidx⟩ := h1.1
    obtain ⟨x, hx, y, hy, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_not_commute
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥R)
    have hc : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      rw [← ha, ← hb]
      exact (Commute.zpow_zpow_self g a b).eq
    exact hxy (congrArg Subtype.val hc)
  · intro ℓ hℓ
    have h2 : ⁅t, ℓ⁆ ∈ ⁅R, L⁆ := Subgroup.commutator_mem_commutator htR hℓ
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      (isSubnormal_centralizer hΩ hLΩ hzL) (h1.2 h2)

end T7A

variable (p f) in
theorem twinNormAlpha_of (h3 : C21_3 p f) : TwinNormAlpha p f := by
  intro G _ _ _ Ω K K' z u J t W h L hL
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hfr := h.twinFrameData
  have hB := twinFrame_isElemAbelian hp hΩ hfr
  have hB8 := twinFrame_natCard_eight hp hq hΩ hfr
  have h3' := (h3 G Ω K K' z u J t W h).2
  have hzu : z * u = u * z := hfr.comm_zu
  have hzt : z * t = t * z := hfr.comm_zt hp hΩ
  have hz2 : z * z = 1 := h.std.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have hBC : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hO := T7A.oddCore_le_normalizer_alpha hB hB8 hBC h3'
  intro ℓ hℓ
  have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hcommO := T7A.commutator_twin_mem_oddCoreOf hp hq hΩ hfr hL ℓ hℓ
  have hc' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    rwa [commutatorElement_def] at hcommO
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    ht2 (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hc'
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hoO
  have hcz : ℓ * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hℓC hoC
  have hct : (ℓ * o) * t = t * (ℓ * o) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hE₀ : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 ht2 h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm hzt
  have hE₀B : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hcE₀ : ℓ * o ∈ Subgroup.centralizer ((Subgroup.closure ({z, t} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({ℓ * o} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          hcz).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hcN := T7A.centralizer_le_normalizer_alpha hE₀ hE₀B h3' hcE₀
  have h2 : (ℓ * o) * o⁻¹ ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ (hO hoO))
  rwa [mul_inv_cancel_right] at h2

end CFSG.ClassicalInvolution.Asc77
