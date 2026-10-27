module

public import CFSG.ClassicalInvolution.TwoGroupCase.AmbientEscape
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreSubgroup

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem oddCoreImg_conjSubgroup [Finite G] (R : Subgroup G) (g : G) :
    oddCoreImg (conjSubgroup g R) = conjSubgroup g (oddCoreImg R) := by
  let φ : R ≃* conjSubgroup g R := (MulAut.conj g).subgroupMap R
  have hφ : (oddCore R).map φ.toMonoidHom = oddCore (conjSubgroup g R) :=
    QuaternionStructure.oddCore_map_mulEquiv φ
  rw [oddCoreImg, ← hφ, Subgroup.map_map]
  show _ = (oddCoreImg R).map (MulAut.conj g).toMonoidHom
  rw [oddCoreImg, Subgroup.map_map]
  congr 1

namespace OddByQuat

variable {R S : Subgroup G} {t : G}

theorem conj [Finite G] (d : OddByQuat R S t) (g : G) :
    OddByQuat (conjSubgroup g R) (conjSubgroup g S) (g * t * g⁻¹) where
  sylow := d.sylow.conj g
  t_mem := mem_conjSubgroup_of_mem d.t_mem
  t_ord := d.orderOf_t₁ g
  unique := d.unique_S₁ g
  le_C := by
    rw [← conjSubgroup_centralizer]
    exact conjSubgroup_mono d.le_C
  normal := by
    intro y hy
    rw [← conjSubgroup_centralizer] at hy
    have hy' : g⁻¹ * y * g ∈ Subgroup.centralizer ({t} : Set G) := mem_conjSubgroup_iff.mp hy
    have hN := d.normal hy'
    rw [← conjSubgroup_eq_self_iff] at hN ⊢
    have h1 : conjSubgroup y (conjSubgroup g R) =
        conjSubgroup g (conjSubgroup (g⁻¹ * y * g) R) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [h1, hN]
  two := by
    let φ : R ≃* conjSubgroup g R := (MulAut.conj g).subgroupMap R
    have hφ : (oddCore R).map φ.toMonoidHom = oddCore (conjSubgroup g R) :=
      QuaternionStructure.oddCore_map_mulEquiv φ
    exact d.two.of_equiv (QuotientGroup.congr _ _ φ hφ)

end OddByQuat

theorem exists_mulEquiv_quotient_complement {A K S : Subgroup G} [hn : (K.subgroupOf A).Normal]
    (hKA : K ≤ A) (hSA : S ≤ A) (hKS : K ⊓ S = ⊥) (hfac : ∀ a ∈ A, ∃ k ∈ K, ∃ s ∈ S, a = k * s) :
    ∃ e : (A ⧸ K.subgroupOf A) ≃* S, ∀ k ∈ K, ∀ s ∈ S, ∀ h : k * s ∈ A,
      ((e (QuotientGroup.mk ⟨k * s, h⟩) : S) : G) = s := by
  let f : S →* A ⧸ K.subgroupOf A :=
    (QuotientGroup.mk' (K.subgroupOf A)).comp (Subgroup.inclusion hSA)
  have hmk : ∀ k ∈ K, ∀ s : S, ∀ h : k * (s : G) ∈ A,
      f s = QuotientGroup.mk (⟨k * s, h⟩ : A) := by
    intro k hk s h
    show (QuotientGroup.mk (⟨s, hSA s.2⟩ : A)) = QuotientGroup.mk ⟨k * s, h⟩
    rw [QuotientGroup.eq]
    have := hn.conj_mem ⟨k, hKA hk⟩ (by simpa [Subgroup.mem_subgroupOf] using hk)
      ⟨(s : G)⁻¹, A.inv_mem (hSA s.2)⟩
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : (s : G) ∈ K := by
      have := (QuotientGroup.eq_one_iff (N := K.subgroupOf A) _).mp hs
      simpa [Subgroup.mem_subgroupOf] using this
    have h2 : (s : G) ∈ K ⊓ S := ⟨h1, s.2⟩
    rw [hKS, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, s, hs, rfl⟩ := hfac a ha
    exact ⟨⟨s, hs⟩, hmk k hk ⟨s, hs⟩ ha⟩
  let e' : S ≃* (A ⧸ K.subgroupOf A) := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e'.symm, fun k hk s hs h => ?_⟩
  have hs' : e' ⟨s, hs⟩ = QuotientGroup.mk (⟨k * s, h⟩ : A) := hmk k hk ⟨s, hs⟩ h
  rw [← hs', MulEquiv.symm_apply_apply]

theorem fixed_normal [Finite G] (R : Subgroup G) (t' : G) :
    ((oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)).subgroupOf
      (R ⊓ Subgroup.centralizer ({t'} : Set G))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ (oddCoreImg_le R))).mpr
    (le_normalizer_of_conj_mem fun a ha k hk => ?_)
  refine ⟨conj_mem_oddCoreImg (Subgroup.le_normalizer ha.1) hk.1, ?_⟩
  exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem ha.2 hk.2)
    ((Subgroup.centralizer _).inv_mem ha.2)

namespace OddByQuat

variable [Finite G] {R S : Subgroup G} {t : G}

omit [Finite G] in
theorem fixed_le {R : Subgroup G} (t' : G) :
    (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)) ≤
      R ⊓ Subgroup.centralizer ({t'} : Set G) :=
  inf_le_inf_right _ (oddCoreImg_le R)

omit [Finite G] in
theorem inf_centralizer_mul_eq (d : OddByQuat R S t) (t' : G) :
    R ⊓ Subgroup.centralizer ({t * t'} : Set G) = R ⊓ Subgroup.centralizer ({t'} : Set G) := by
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    have hta : a * t = t * a := (Subgroup.mem_centralizer_singleton_iff.mp (d.le_C ha))
    have : t * (a * t') = t * (t' * a) := by
      calc t * (a * t') = (t * a) * t' := (mul_assoc _ _ _).symm
        _ = (a * t) * t' := by rw [hta]
        _ = a * (t * t') := mul_assoc _ _ _
        _ = (t * t') * a := h
        _ = t * (t' * a) := mul_assoc _ _ _
    exact mul_left_cancel this
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    have hta : a * t = t * a := (Subgroup.mem_centralizer_singleton_iff.mp (d.le_C ha))
    calc a * (t * t') = (a * t) * t' := (mul_assoc _ _ _).symm
      _ = (t * a) * t' := by rw [hta]
      _ = t * (a * t') := mul_assoc _ _ _
      _ = t * (t' * a) := by rw [h]
      _ = (t * t') * a := (mul_assoc _ _ _).symm

theorem exists_mul_fixed (d : OddByQuat R S t) {t' : G} (hcS : ∀ s ∈ S, t' * s = s * t') {a : G}
    (ha : a ∈ R ⊓ Subgroup.centralizer ({t'} : Set G)) :
    ∃ k ∈ oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G), ∃ s ∈ S, a = k * s := by
  obtain ⟨o, ho, s, hs, rfl⟩ := d.exists_mul_O_S a ha.1
  refine ⟨o, ⟨ho, ?_⟩, s, hs, rfl⟩
  have h1 : (o * s) * t' = t' * (o * s) := Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have h2 := hcS s hs
  show o ∈ Subgroup.centralizer ({t'} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc o * t' = o * (t' * s) * s⁻¹ := by group
    _ = o * (s * t') * s⁻¹ := by rw [h2]
    _ = ((o * s) * t') * s⁻¹ := by group
    _ = (t' * (o * s)) * s⁻¹ := by rw [h1]
    _ = t' * o := by group

theorem inf_fixed_S (d : OddByQuat R S t) (t' : G) :
    (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)) ⊓ S = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_right S inf_le_left).trans d.inf_O_S.le)

omit [Finite G] in
theorem S_le_fixed (d : OddByQuat R S t) {t' : G} (hcS : ∀ s ∈ S, t' * s = s * t') :
    S ≤ R ⊓ Subgroup.centralizer ({t'} : Set G) := fun s hs =>
  ⟨d.S_le hs, Subgroup.mem_centralizer_singleton_iff.mpr (hcS s hs).symm⟩

theorem oddCoreImg_fixed (d : OddByQuat R S t) {t' : G}
    (hcS : ∀ s ∈ S, t' * s = s * t') :
    oddCoreImg (R ⊓ Subgroup.centralizer ({t'} : Set G)) =
      oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := R ⊓ Subgroup.centralizer ({t'} : Set G) with hA
  set K : Subgroup G := oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) with hK
  have hn : (K.subgroupOf A).Normal := fixed_normal R t'
  have hKA : K ≤ A := fixed_le t'
  have hSA : S ≤ A := d.S_le_fixed hcS
  obtain ⟨e, he⟩ := exists_mulEquiv_quotient_complement (A := A) (K := K) (S := S) hKA hSA
    (d.inf_fixed_S t') fun a ha => d.exists_mul_fixed hcS ha
  have hKodd : Odd (Nat.card K) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  apply le_antisymm
  ·
    rintro _ ⟨a', ha', rfl⟩
    have hodd : Odd (orderOf a') := by
      have h1 := QuaternionStructure.odd_natCard_oddCore A
      have h2 : Odd (orderOf (⟨a', ha'⟩ : oddCore A)) := h1.of_dvd_nat (orderOf_dvd_natCard _)
      rwa [← Subgroup.orderOf_coe] at h2
    set q : A ⧸ K.subgroupOf A := QuotientGroup.mk a' with hq
    have hdvd : orderOf (e q) ∣ orderOf a' :=
      (orderOf_map_dvd e.toMonoidHom q).trans
        (orderOf_map_dvd (QuotientGroup.mk' (K.subgroupOf A)) a')
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp d.S_two (e q)
    have hm0 : m = 0 := by
      by_contra hm0
      have h2 : 2 ∣ orderOf a' := by
        rw [hm] at hdvd
        exact (dvd_pow_self 2 hm0).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
    have hq1 : q = 1 := e.injective (by rw [hm, map_one])
    have := (QuotientGroup.eq_one_iff (N := K.subgroupOf A) a').mp hq1
    simpa [Subgroup.mem_subgroupOf] using this
  ·
    have hKA' : K.subgroupOf A ≤ oddCore A := by
      refine le_sSup ⟨hn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv]
      exact hKodd
    intro k hk
    exact ⟨⟨k, hKA hk⟩, hKA' (by simpa [Subgroup.mem_subgroupOf] using hk), rfl⟩

omit [Finite G] in
theorem odd_fixed (R : Subgroup G) [Finite G] (t' : G) :
    Odd (Nat.card (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) : Subgroup G)) :=
  (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end OddByQuat

structure FixedStructure (R S : Subgroup G) (t' c : G) : Prop where
  centralizer_eq : R ⊓ Subgroup.centralizer ({c} : Set G) = R ⊓ Subgroup.centralizer ({t'} : Set G)
  factor : ∀ a ∈ R ⊓ Subgroup.centralizer ({c} : Set G),
    ∃ k ∈ oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G), ∃ s ∈ S, a = k * s
  inf_S : (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)) ⊓ S = ⊥
  K_le : oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) ≤ R ⊓ Subgroup.centralizer ({c} : Set G)
  S_le : S ≤ R ⊓ Subgroup.centralizer ({c} : Set G)
  normal : ((oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)).subgroupOf
    (R ⊓ Subgroup.centralizer ({c} : Set G))).Normal
  odd : Odd (Nat.card (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) : Subgroup G))
  oddCoreImg_eq : oddCoreImg (R ⊓ Subgroup.centralizer ({c} : Set G)) =
    oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)
  equiv : ∀ [((oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)).subgroupOf
      (R ⊓ Subgroup.centralizer ({c} : Set G))).Normal],
    ∃ e : ((R ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) ⧸
        (oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G)).subgroupOf
          (R ⊓ Subgroup.centralizer ({c} : Set G))) ≃* S,
      ∀ k ∈ oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G), ∀ s ∈ S,
        ∀ h : k * s ∈ R ⊓ Subgroup.centralizer ({c} : Set G),
          ((e (QuotientGroup.mk ⟨k * s, h⟩) : S) : G) = s

namespace OddByQuat

variable [Finite G] {R S : Subgroup G} {t : G}

theorem fixedStructure (d : OddByQuat R S t) {t' c : G} (hc : c = t * t')
    (hcS : ∀ s ∈ S, t' * s = s * t') : FixedStructure R S t' c := by
  have hA : R ⊓ Subgroup.centralizer ({c} : Set G) = R ⊓ Subgroup.centralizer ({t'} : Set G) := by
    rw [hc]
    exact d.inf_centralizer_mul_eq t'
  have hn := fixed_normal R t'
  rw [← hA] at hn
  have hKA : oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) ≤
      R ⊓ Subgroup.centralizer ({c} : Set G) := hA ▸ fixed_le t'
  have hSA : S ≤ R ⊓ Subgroup.centralizer ({c} : Set G) := hA ▸ d.S_le_fixed hcS
  refine ⟨hA, fun a ha => d.exists_mul_fixed hcS (hA ▸ ha), d.inf_fixed_S t', hKA, hSA, hn,
    odd_fixed R t', hA ▸ d.oddCoreImg_fixed hcS, ?_⟩
  intro hn'
  exact exists_mulEquiv_quotient_complement hKA hSA (d.inf_fixed_S t') fun a ha =>
    d.exists_mul_fixed hcS (hA ▸ ha)

end OddByQuat

theorem mem_normalizer_inf_centralizer {X : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) (hyc : y * c = c * y) :
    y ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_self_iff, conjSubgroup_inf, conjSubgroup_eq_self_iff.mpr hy,
    conjSubgroup_centralizer]
  have : y * c * y⁻¹ = c := by rw [hyc]; group
  rw [this]

theorem le_normalizer_conjSubgroup {T X : Subgroup G} {x : G}
    (hX : T ≤ Subgroup.normalizer (X : Set G)) (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.normalizer ((conjSubgroup x X : Subgroup G) : Set G) := by
  intro y hy
  rw [← conjSubgroup_eq_self_iff]
  have hy' : x⁻¹ * y * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem hx) y).mp hy
    simpa using this
  have h1 : conjSubgroup y (conjSubgroup x X) = conjSubgroup x (conjSubgroup (x⁻¹ * y * x) X) := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [h1, conjSubgroup_eq_self_iff.mpr (hX hy')]

theorem normalizes_fixed [Finite G] {R T : Subgroup G} {t t' : G}
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTt : ∀ y ∈ T, y * t = t * y)
    (hTt' : ∀ y ∈ T, y * t' = t' * y) :
    T ≤ Subgroup.normalizer ((oddCoreImg R : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer ({t * t'} : Set G) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((oddCoreImg R ⊓ Subgroup.centralizer ({t'} : Set G) : Subgroup G) : Set G) := by
  have hO : T ≤ Subgroup.normalizer ((oddCoreImg R : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun y hy _ ho => conj_mem_oddCoreImg (hTR hy) ho
  refine ⟨hO, fun y hy => mem_normalizer_inf_centralizer (hTR hy) ?_,
    fun y hy => mem_normalizer_inf_centralizer (hO hy) (hTt' y hy)⟩
  calc y * (t * t') = (y * t) * t' := (mul_assoc _ _ _).symm
    _ = (t * y) * t' := by rw [hTt y hy]
    _ = t * (y * t') := mul_assoc _ _ _
    _ = t * (t' * y) := by rw [hTt' y hy]
    _ = (t * t') * y := (mul_assoc _ _ _).symm

theorem exists_escape [Finite G] {T U : Subgroup G} (hnot : ¬ IsSylow2Of T ⊤)
    (hU : IsSylow2Of U ⊤) (hTU : T ≤ U) : ∃ x : G, Escape T U x := by
  have hne : T ≠ U := fun h => hnot (h ▸ hU)
  obtain ⟨x, hxU, hxN, hxT, hxx⟩ := exists_mem_normalizer_not_mem_sq_mem hU.2.1 hTU hne
  exact ⟨x, ⟨hU.2.1, hTU, hxU, hxN, hxT, hxx⟩⟩

namespace OddByQuat

section Escape

variable [Finite G] {R S T U : Subgroup G} {t x : G}

omit [Finite G] in
theorem T_le_normalizer_R (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) :
    T ≤ Subgroup.normalizer (R : Set G) := fun _ hy => d.normal (d.T_le_C hT hy)

theorem T_commute_t₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : ∀ y ∈ T, y * (x * t * x⁻¹) = (x * t * x⁻¹) * y := fun y hy =>
  ((d.conj_t_mem hT e.normalizes).2 y hy).symm

theorem t₁_commute (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) :=
  (d.t_central hT _ (d.conj_t_mem hT e.normalizes).1).symm

theorem t₁_centralizes_S (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    ∀ s ∈ S, (x * t * x⁻¹) * s = s * (x * t * x⁻¹) := fun s hs =>
  (d.commute_S_S₁ hT e s hs _ (mem_conjSubgroup_of_mem d.t_mem)).symm

theorem t_centralizes_S₁ (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    ∀ s ∈ conjSubgroup x S, t * s = s * t := fun s hs => d.commute_S_S₁ hT e t d.t_mem s hs

theorem inf_W_R (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) : (T ⊔ Subgroup.zpowers x) ⊓ R = S := by
  have h1 : (T ⊔ Subgroup.zpowers x) ⊓ R =
      ((T ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ R := by
    ext w
    constructor
    · rintro ⟨hw, hR⟩
      exact ⟨⟨hw, d.le_C hR⟩, hR⟩
    · rintro ⟨⟨hw, -⟩, hR⟩
      exact ⟨hw, hR⟩
  rw [h1, d.inf_C_W_t hT e, d.inf_R_eq hT]

theorem inf_W_R₁ (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    (T ⊔ Subgroup.zpowers x) ⊓ conjSubgroup x R = conjSubgroup x S := by
  have hC : conjSubgroup x R ≤ Subgroup.centralizer ({x * t * x⁻¹} : Set G) := (d.conj x).le_C
  have h1 : (T ⊔ Subgroup.zpowers x) ⊓ conjSubgroup x R =
      ((T ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G)) ⊓
        conjSubgroup x R := by
    ext w
    constructor
    · rintro ⟨hw, hR⟩
      exact ⟨⟨hw, hC hR⟩, hR⟩
    · rintro ⟨⟨hw, -⟩, hR⟩
      exact ⟨hw, hR⟩
  rw [h1, d.inf_C_W_t₁ hT e]
  have h2 := conjSubgroup_inf x T R
  rw [conjSubgroup_eq_self_iff.mpr e.normalizes, d.inf_R_eq hT] at h2
  exact h2.symm

theorem fixedStructure_zero (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    FixedStructure R S (x * t * x⁻¹) (t * (x * t * x⁻¹)) :=
  d.fixedStructure rfl (d.t₁_centralizes_S hT e)

theorem fixedStructure_one (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    FixedStructure (conjSubgroup x R) (conjSubgroup x S) t (t * (x * t * x⁻¹)) :=
  (d.conj x).fixedStructure (d.t₁_commute hT e).symm (d.t_centralizes_S₁ hT e)

theorem T_normalizes_zero (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    T ≤ Subgroup.normalizer (R : Set G) ∧
      T ≤ Subgroup.normalizer ((oddCoreImg R : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((oddCoreImg R ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hO, hA, hK⟩ := normalizes_fixed (R := R) (t := t) (t' := x * t * x⁻¹)
    (d.T_le_normalizer_R hT) (fun y hy => (d.t_central hT y hy).symm) (d.T_commute_t₁ hT e)
  exact ⟨d.T_le_normalizer_R hT, hO, hA, hK⟩

theorem T_normalizes_one (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    T ≤ Subgroup.normalizer ((conjSubgroup x R : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((oddCoreImg (conjSubgroup x R) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((conjSubgroup x R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) : Subgroup G) :
          Set G) ∧
      T ≤ Subgroup.normalizer
        ((oddCoreImg (conjSubgroup x R) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G) := by
  have hTR₁ := le_normalizer_conjSubgroup (d.T_le_normalizer_R hT) e.normalizes
  obtain ⟨hO, hA, hK⟩ := normalizes_fixed (R := conjSubgroup x R) (t := x * t * x⁻¹) (t' := t)
    hTR₁ (d.T_commute_t₁ hT e) (fun y hy => (d.t_central hT y hy).symm)
  rw [d.t₁_commute hT e] at hA
  exact ⟨hTR₁, hO, hA, hK⟩

theorem escape_exchange (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    conjSubgroup x (conjSubgroup x R) = R ∧
      conjSubgroup x (conjSubgroup x (oddCoreImg R)) = oddCoreImg R ∧
      conjSubgroup x (R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G)) =
        conjSubgroup x R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) ∧
      conjSubgroup x (conjSubgroup x R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G)) =
        R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) ∧
      conjSubgroup x (oddCoreImg R ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G)) =
        oddCoreImg (conjSubgroup x R) ⊓ Subgroup.centralizer ({t} : Set G) ∧
      conjSubgroup x (oddCoreImg (conjSubgroup x R) ⊓ Subgroup.centralizer ({t} : Set G)) =
        oddCoreImg R ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G) := by
  have hxx : ∀ X : Subgroup G, T ≤ Subgroup.normalizer (X : Set G) →
      conjSubgroup x (conjSubgroup x X) = X := fun X hX => by
    rw [conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_self_iff.mpr (hX e.sq_mem)
  have hR := d.T_le_normalizer_R hT
  have hO := (d.T_normalizes_zero hT e).2.1
  have hx1 := d.conj_t₁ hT e
  have hc : x * (t * (x * t * x⁻¹)) * x⁻¹ = t * (x * t * x⁻¹) := by
    calc x * (t * (x * t * x⁻¹)) * x⁻¹ = (x * t * x⁻¹) * (x * (x * t * x⁻¹) * x⁻¹) := by group
      _ = (x * t * x⁻¹) * t := by rw [hx1]
      _ = t * (x * t * x⁻¹) := d.t₁_commute hT e
  have hoc : oddCoreImg (conjSubgroup x R) = conjSubgroup x (oddCoreImg R) :=
    oddCoreImg_conjSubgroup R x
  refine ⟨hxx R hR, hxx _ hO, ?_, ?_, ?_, ?_⟩
  · rw [conjSubgroup_inf, conjSubgroup_centralizer, hc]
  · rw [conjSubgroup_inf, conjSubgroup_centralizer, hc, hxx R hR]
  · rw [conjSubgroup_inf, conjSubgroup_centralizer, hx1, hoc]
  · rw [conjSubgroup_inf, conjSubgroup_centralizer, hoc, hxx _ hO]

omit [Finite G] in
theorem mem_zpowers_of_orderOf_eq_two {t y : G} (ht : orderOf t = 2) (hy : y ∈ Subgroup.zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h := zpow_mod_orderOf t k
  rw [ht] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    simp [h0]
  · right
    rw [← h]
    simp [h1]

omit [Finite G] in
theorem conj_conj_S (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    conjSubgroup x (conjSubgroup x S) = S := by
  rw [conjSubgroup_conjSubgroup]
  exact conjSubgroup_eq_self_iff.mpr (hT.1 e.sq_mem)

theorem V_card (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers (x * t * x⁻¹) : Subgroup G) = 4 := by
  have ht₁ := d.orderOf_t₁ x
  have hcomm : (x * t * x⁻¹) * t = t * (x * t * x⁻¹) := d.t₁_commute hT e
  have hB : Subgroup.zpowers (x * t * x⁻¹) ≤ Subgroup.normalizer
      ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    refine (Subgroup.zpowers_le).mpr ?_
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute t (x * t * x⁻¹) from hcomm.symm) k)).eq
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers t)
    (Subgroup.zpowers (x * t * x⁻¹)) hB
  have hinf : Subgroup.zpowers t ⊓ Subgroup.zpowers (x * t * x⁻¹) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_of_orderOf_eq_two d.t_ord hy.1 with h | h
    · exact h
    · exfalso
      rcases mem_zpowers_of_orderOf_eq_two ht₁ hy.2 with h' | h'
      · have ht1 : t = 1 := h.symm.trans h'
        have := d.t_ord
        rw [ht1, orderOf_one] at this
        exact absurd this (by norm_num)
      · exact d.t₁_ne hT e (h'.symm.trans h)
  rw [natCard_eq_mul_of_inf_eq_bot le_sup_left le_sup_right hinf (fun m hm => by
    have h1 : m ∈ ((Subgroup.zpowers t ⊔ Subgroup.zpowers (x * t * x⁻¹) : Subgroup G) : Set G) := hm
    rw [hmul] at h1
    obtain ⟨a, ha, b, hb, rfl⟩ := h1
    exact ⟨a, ha, b, hb, rfl⟩), Nat.card_zpowers, Nat.card_zpowers, d.t_ord, ht₁]

theorem V_le_centralizer (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    Subgroup.zpowers t ⊔ Subgroup.zpowers (x * t * x⁻¹) ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  have ht : t ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨d.S_le_T hT d.t_mem, by
      show t ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (d.t_central hT h hh).symm⟩
  have ht₁ : x * t * x⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨(d.conj_t_mem hT e.normalizes).1, by
      show x * t * x⁻¹ ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact d.T_commute_t₁ hT e h hh⟩
  exact sup_le ((Subgroup.zpowers_le).mpr ht) ((Subgroup.zpowers_le).mpr ht₁)

theorem two_mul_card_le (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    2 * Nat.card T ≤
      2 ^ (Nat.card (Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G))).factorization 2 := by
  have h := card_le_of_isPGroup_le (W_two e) (d.c_central hT e)
  rwa [card_W e] at h

theorem escape_odd_structure (d : OddByQuat R S t)
    (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G))) (e : Escape T U x) :
    ((T ⊔ Subgroup.zpowers x) ⊓ R = S ∧
      FixedStructure R S (x * t * x⁻¹) (t * (x * t * x⁻¹)) ∧
      T ≤ Subgroup.normalizer (R : Set G) ∧
      T ≤ Subgroup.normalizer ((oddCoreImg R : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((oddCoreImg R ⊓ Subgroup.centralizer ({x * t * x⁻¹} : Set G) : Subgroup G) : Set G) ∧
      R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) ≤
        Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G)) ∧
    (oddCoreImg (conjSubgroup x R) = conjSubgroup x (oddCoreImg R) ∧
      (T ⊔ Subgroup.zpowers x) ⊓ conjSubgroup x R = conjSubgroup x S ∧
      FixedStructure (conjSubgroup x R) (conjSubgroup x S) t (t * (x * t * x⁻¹)) ∧
      T ≤ Subgroup.normalizer ((conjSubgroup x R : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((oddCoreImg (conjSubgroup x R) : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((conjSubgroup x R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) : Subgroup G) :
          Set G) ∧
      T ≤ Subgroup.normalizer
        ((oddCoreImg (conjSubgroup x R) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G) ∧
      conjSubgroup x R ⊓ Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G) ≤
        Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G)) := by
  obtain ⟨h0R, h0O, h0A, h0K⟩ := d.T_normalizes_zero hT e
  obtain ⟨h1R, h1O, h1A, h1K⟩ := d.T_normalizes_one hT e
  exact ⟨⟨d.inf_W_R hT e, d.fixedStructure_zero hT e, h0R, h0O, h0A, h0K, inf_le_right⟩,
    oddCoreImg_conjSubgroup R x, d.inf_W_R₁ hT e, d.fixedStructure_one hT e, h1R, h1O, h1A, h1K,
    inf_le_right⟩

end Escape

end OddByQuat

end CFSG.ClassicalInvolution
