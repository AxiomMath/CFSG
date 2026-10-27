module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSylow
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Closure
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Suzuki

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.SeitzReduction.RankOne.GMS43 (exists_pow_central_of_ne card_le_four_of_centralizer_le
  card_le_two_of_inf_eq_bot lt_card_commutator_of_mul_lt
  exists_sylow_stronglyClosed_of_commutator_bound)
open CFSG.SeitzReduction.RankOne.GMS28 (exists_mem_normalizer_of_not_isSylowOf)

theorem relIndex_le_two_of_forall_mul_mem {H : Type*} [Group H] [Finite H] {K X : Subgroup H}
    (hmul : ∀ a ∈ X, ∀ b ∈ X, a ∉ K → b ∉ K → a * b ∈ K) : K.relIndex X ≤ 2 := by
  have hc := card_le_two_mul_of_mul_mem hmul
  have h1 := relIndex_mul_card K X
  rw [inf_comm] at hc
  have hpos : 0 < Nat.card (K ⊓ X : Subgroup H) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 3 * Nat.card (K ⊓ X : Subgroup H) ≤ Nat.card X := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hlt
  omega

structure Hyp43 {H : Type*} [Group H] [Finite H] (A : Subgroup H) (t : H)
    (U V D T : Subgroup H) (n : ℕ) : Prop where
  setting : LocalSetting A t U V D n
  sylow : IsSylowOf 2 T (centralizer ({t} : Set H))
  U_le : U ≤ T
  le_normalizer : T ≤ normalizer (V : Set H)

theorem LocalSetting.exists_hyp43 {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H}
    {U V D : Subgroup H} {n : ℕ} (h : LocalSetting A t U V D n) :
    ∃ T : Subgroup H, Hyp43 A t U V D T n := by
  obtain ⟨T, hT, hUT, -, hTV⟩ := h.exists_isSylowOf_le_normalizer
  exact ⟨T, h, hT, hUT, hTV⟩

namespace Hyp43

section Basic

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D T : Subgroup H}
  {n : ℕ} (h : Hyp43 A t U V D T n)
include h

theorem mem_T : t ∈ T := h.setting.mem_T h.sylow

theorem V_inf_T : V ⊓ T = U := h.setting.V_inf_T h.sylow.le h.U_le

theorem isPGroup_sup : IsPGroup 2 (V ⊔ T : Subgroup H) :=
  (h.setting.isSylowOf_sup h.sylow h.U_le h.le_normalizer).isPGroup

theorem sup_le_normalizer : V ⊔ T ≤ normalizer (V : Set H) :=
  sup_le Subgroup.le_normalizer h.le_normalizer

theorem B_le_Vt : U ⊔ zpowers t ≤ V ⊔ zpowers t :=
  sup_le (h.setting.U_le_V.trans le_sup_left) le_sup_right

theorem exists_mul_eq {w : H} (hw : w ∈ V ⊔ T) : ∃ v ∈ V, ∃ p ∈ T, w = v * p := by
  have hw' : w ∈ ((V ⊔ T : Subgroup H) : Set H) := hw
  rw [coe_mul_of_right_le_normalizer_left V T h.le_normalizer] at hw'
  obtain ⟨v, hv, p, hp, hvp⟩ := hw'
  exact ⟨v, hv, p, hp, hvp.symm⟩

theorem exists_mul_eq_of_not_mem {w : H} (hw : w ∈ V ⊔ T) (hwV : w ∉ V ⊔ zpowers t) :
    ∃ v ∈ V, ∃ p ∈ T, w = v * p ∧ p ∉ U ⊔ zpowers t := by
  obtain ⟨v, hv, p, hp, rfl⟩ := h.exists_mul_eq hw
  exact ⟨v, hv, p, hp, rfl, fun hpB => hwV (mul_mem (mem_sup_left hv) (h.B_le_Vt hpB))⟩

theorem mul_self_mem_of_mul_mul_eq_one {v p : H} (hv : v ∈ V) (hp : p ∈ T)
    (h1 : v * p * (v * p) = 1) : p * p ∈ U := by
  have hpv : p * v * p⁻¹ ∈ V := (mem_normalizer_iff.mp (h.le_normalizer hp) v).mp hv
  have h2 : v * (p * v * p⁻¹) * (p * p) = 1 := by rw [← h1]; group
  have h3 : p * p = (v * (p * v * p⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h.V_inf_T]
  exact mem_inf.mpr ⟨by rw [h3]; exact inv_mem (mul_mem hv hpv), mul_mem hp hp⟩

theorem inf_centralizer_le {S : Subgroup H} (hSp : IsPGroup 2 S) (hTS : T ≤ S) :
    S ⊓ centralizer ({t} : Set H) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.sylow.eq_of_le (le_inf hTS h.sylow.le) inf_le_right (hSp.to_le inf_le_left)).le

theorem mem_sup_of_mul_conj_mem {S : Subgroup H} (hSp : IsPGroup 2 S) (hES : V ⊔ T ≤ S)
    {w : H} (hw : w ∈ S) (hwt : t * (w * t * w⁻¹) ∈ V) : w ∈ V ⊔ T := by
  have hs := h.setting
  set e := t * (w * t * w⁻¹) with he_def
  have htt := hs.t_mul_t
  have hte : t * e = w * t * w⁻¹ := by rw [he_def, ← mul_assoc, htt, one_mul]
  have hinv : t * e * (t * e) = 1 := by
    rw [hte]
    calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have het : e * t = t * e := by
    have h1 : t * e * t = e⁻¹ := by
      have : t * e * t * e = 1 := by rw [← hinv]; group
      exact eq_inv_of_mul_eq_one_left this
    rw [inv_eq_of_mul_eq_one_right (hs.V_mul_self e hwt)] at h1
    calc e * t = t * e * t * t := by rw [h1]
      _ = t * e * (t * t) := by group
      _ = t * e := by rw [htt, mul_one]
  have heU : e ∈ U := by
    rw [← hs.V_inf_centralizer]
    exact mem_inf.mpr ⟨hwt, mem_centralizer_singleton_iff.mpr het⟩
  obtain ⟨e₁, he₁, he₁t⟩ := hs.exists_comm_eq e heU
  have hconj : w * t * w⁻¹ = e₁ * t * e₁⁻¹ := by
    calc w * t * w⁻¹ = e * t := by rw [← hte, het]
      _ = e₁ * t * e₁⁻¹ * t * t := by rw [he₁t]
      _ = e₁ * t * e₁⁻¹ * (t * t) := by group
      _ = e₁ * t * e₁⁻¹ := by rw [htt, mul_one]
  have hc : e₁⁻¹ * w ∈ S ⊓ centralizer ({t} : Set H) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hES (mem_sup_left he₁))) hw, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc e₁⁻¹ * w * t = e₁⁻¹ * (w * t * w⁻¹) * w := by group
      _ = e₁⁻¹ * (e₁ * t * e₁⁻¹) * w := by rw [hconj]
      _ = t * (e₁⁻¹ * w) := by group
  have hT := h.inf_centralizer_le hSp (le_sup_right.trans hES) hc
  rw [show w = e₁ * (e₁⁻¹ * w) by group]
  exact mul_mem (mem_sup_left he₁) (mem_sup_right hT)

theorem rightConjugate_mul_self {U' : Subgroup H} (hU' : U' ≤ V) (g : H) :
    ∀ x ∈ rightConjugate U' g, x * x = 1 := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h1 := h.setting.V_mul_self _ (hU' hx)
  calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

theorem not_conj_mem_rightConjugate {U' : Subgroup H} (hU' : U' ≤ V) (g : H) :
    ∀ x ∈ rightConjugate U' g, ∀ k : H, k⁻¹ * t * k ≠ x := by
  intro x hx k hk
  rw [mem_rightConjugate_iff, ← hk] at hx
  exact h.setting.conj_not_mem_V (k * g⁻¹) (by
    rw [show (k * g⁻¹)⁻¹ * t * (k * g⁻¹) = g * (k⁻¹ * t * k) * g⁻¹ by group]
    exact hU' hx)

theorem inf_Vt_le {X : Subgroup H} (hX2 : ∀ x ∈ X, x * x = 1)
    (hXt : ∀ x ∈ X, ∀ k : H, k⁻¹ * t * k ≠ x) : X ⊓ (V ⊔ zpowers t) ≤ V := by
  have hs := h.setting
  intro x hx
  obtain ⟨hxX, hxVt⟩ := mem_inf.mp hx
  rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_V hxVt with
    hV | ⟨v, hv, rfl⟩
  · exact hV
  exfalso
  have hvU := (hs.mul_t_mul_self_iff v hv).mp (hX2 _ hxX)
  obtain ⟨w, -, hw⟩ := hs.exists_conj_V v hvU
  exact hXt _ hxX w (by rw [hw, hs.t_mul_comm v hvU])

theorem card_le_card_inf_mul {K M : Subgroup H} (hK : K ≤ V)
    (hM : ∀ k ∈ K, k * t * k⁻¹ * t ∈ M) :
    Nat.card K ≤ Nat.card (K ⊓ U : Subgroup H) * Nat.card M := by
  classical
  have hs := h.setting
  let φ : K →* M :=
    { toFun := fun k => ⟨k * t * (k : H)⁻¹ * t, hM k k.2⟩
      map_one' := Subtype.ext (by simp [hs.t_mul_t])
      map_mul' := fun a b => Subtype.ext (hs.comm_mul a (hK a.2) b (hK b.2)) }
  have hker : ∀ k : K, k ∈ φ.ker → (k : H) ∈ U := fun k hk =>
    (hs.comm_eq_one_iff k (hK k.2)).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (K ⊓ U : Subgroup H) :=
    Nat.card_le_card_of_injective (fun k => ⟨k.1.1, mem_inf.mpr ⟨k.1.2, hker k.1 k.2⟩⟩)
      (fun a b hab => by
        have h' := congrArg Subtype.val hab
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  have h3 : Nat.card φ.range ≤ Nat.card M := card_le_card_group _
  calc Nat.card K = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ Nat.card M * Nat.card (K ⊓ U : Subgroup H) := Nat.mul_le_mul h3 h2
    _ = _ := mul_comm _ _

theorem card_inf_centralizer_sq_le_of_mem {z : H} (hz : z ∈ V ⊔ T)
    (hzV : z ∉ V ⊔ zpowers t) :
    Nat.card (U ⊓ centralizer ({z} : Set H) : Subgroup H) ^ 2 ≤ 2 ^ n := by
  have hs := h.setting
  obtain ⟨v, hv, p, hp, rfl, hpB⟩ := h.exists_mul_eq_of_not_mem hz hzV
  rw [inf_centralizer_mul_eq fun k hk => hs.V_comm v hv k (hs.U_le_V hk)]
  exact hs.card_inf_centralizer_sq_le h.sylow h.U_le hp hpB

theorem card_inf_centralizer_sq_le_of_not_mem {S : Subgroup H} (hSp : IsPGroup 2 S)
    (hSN : S ≤ normalizer (V : Set H)) (hES : V ⊔ T ≤ S) {w : H} (hw : w ∈ S)
    (hw₀ : w ∉ V ⊔ T) :
    Nat.card (V ⊓ centralizer ({w} : Set H) : Subgroup H) ^ 2 ≤ (2 ^ n) ^ 3 := by
  classical
  have hs := h.setting
  have hVS : V ≤ S := le_sup_left.trans hES
  have : (V.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hVS).mpr hSN
  set N := V.subgroupOf S with hN
  have hQp : IsPGroup 2 (S ⧸ N) := hSp.to_quotient N
  have heq : ∀ a b : S, (a : S ⧸ N) = (b : S ⧸ N) ↔ (a : H)⁻¹ * b ∈ V := fun a b => by
    rw [QuotientGroup.eq, hN, mem_subgroupOf]
    rfl
  have heq1 : ∀ a : S, (a : S ⧸ N) = 1 ↔ (a : H) ∈ V := fun a => by
    rw [QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
  have htS : t ∈ S := hES (mem_sup_right h.mem_T)
  set T' : S := ⟨t, htS⟩ with hT'
  set W' : S := ⟨w, hw⟩ with hW'
  set j : S ⧸ N := (T' : S ⧸ N) with hj
  set j' : S ⧸ N := ((W' * T' * W'⁻¹ : S) : S ⧸ N) with hj'
  have htt' : ((W' * T' * W'⁻¹ : S) : H) = w * t * w⁻¹ := rfl
  have hjj : j * j = 1 := by
    rw [hj, ← QuotientGroup.mk_mul, heq1]
    show t * t ∈ V
    rw [hs.t_mul_t]
    exact one_mem _
  have hj'j' : j' * j' = 1 := by
    rw [hj', ← QuotientGroup.mk_mul, heq1]
    show w * t * w⁻¹ * (w * t * w⁻¹) ∈ V
    rw [show w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, hs.t_mul_t]
    simp
  have hj'1 : j' ≠ 1 := by
    rw [hj', Ne, heq1, htt']
    have := hs.conj_not_mem_V w⁻¹
    rwa [inv_inv] at this
  have hjne : j ≠ j' := by
    intro hjj'
    rw [hj, hj', heq, htt'] at hjj'
    apply hw₀
    refine h.mem_sup_of_mul_conj_mem hSp hES hw ?_
    have := hjj'
    rwa [show (T' : H) = t from rfl, hs.t_inv] at this
  obtain ⟨m, hz1, -, hzj, hzt⟩ := exists_pow_central_of_ne hQp hjj hj'j' hj'1 hjne
  set Z : S := (T' * (W' * T' * W'⁻¹)) ^ m with hZ
  have hZbar : (j * j') ^ m = (Z : S ⧸ N) := by
    rw [hj, hj', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  rw [hZbar] at hz1 hzj hzt
  set z : H := (Z : H) with hz
  have hzdef : z = (t * (w * t * w⁻¹)) ^ m := by
    rw [hz, hZ, Subgroup.coe_pow]
    rfl
  have hzS₀ : z ∈ V ⊔ T := by
    refine h.mem_sup_of_mul_conj_mem hSp hES Z.2 ?_
    have h1 : ((T' * (Z * T' * Z⁻¹) : S) : S ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← hj, ← hzj, mul_assoc j, mul_inv_cancel, mul_one, hjj]
    exact (heq1 _).mp h1
  have hzV : z ∉ V ⊔ zpowers t := by
    intro hzV
    rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_V hzV with
      h1 | ⟨e, he, h1⟩
    · exact hz1 ((heq1 Z).mpr h1)
    · apply hzt
      rw [heq]
      show z⁻¹ * t ∈ V
      rw [h1, show (e * t)⁻¹ * t = t⁻¹ * e⁻¹ * t⁻¹⁻¹ by group]
      exact (mem_normalizer_iff.mp (inv_mem hs.t_mem_normalizer_V) e⁻¹).mp (inv_mem he)
  have hCU : U ⊓ centralizer ({w} : Set H) ≤ U ⊓ centralizer ({z} : Set H) := by
    intro u hu
    obtain ⟨huU, huw⟩ := mem_inf.mp hu
    have hut : Commute u t := hs.t_mul_comm u huU
    have huw' : Commute u w := mem_centralizer_singleton_iff.mp huw
    have hut' : Commute u (w * t * w⁻¹) := (huw'.mul_right hut).mul_right huw'.inv_right
    refine mem_inf.mpr ⟨huU, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hzdef]
    exact ((hut.mul_right hut').pow_right m).eq
  have h1 := h.card_inf_centralizer_sq_le_of_mem hzS₀ hzV
  have h2 := card_le_of_le hCU
  have h3 := h.card_le_card_inf_mul (K := V ⊓ centralizer ({w} : Set H)) (M := U)
    inf_le_left fun k hk => hs.comm_mem k (mem_inf.mp hk).1
  have h4 : Nat.card (V ⊓ centralizer ({w} : Set H) ⊓ U : Subgroup H) ≤
      Nat.card (U ⊓ centralizer ({w} : Set H) : Subgroup H) :=
    card_le_of_le fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  rw [hs.card_U] at h3
  calc Nat.card (V ⊓ centralizer ({w} : Set H) : Subgroup H) ^ 2
      ≤ (Nat.card (U ⊓ centralizer ({w} : Set H) : Subgroup H) * 2 ^ n) ^ 2 :=
        Nat.pow_le_pow_left (h3.trans (Nat.mul_le_mul_right _ h4)) 2
    _ = Nat.card (U ⊓ centralizer ({w} : Set H) : Subgroup H) ^ 2 * (2 ^ n) ^ 2 := by ring
    _ ≤ Nat.card (U ⊓ centralizer ({z} : Set H) : Subgroup H) ^ 2 * (2 ^ n) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 2)
    _ ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_right _ h1
    _ = (2 ^ n) ^ 3 := by ring

theorem exists_isSylowOf_le_normalizer :
    ∃ S : Subgroup H, IsSylowOf 2 S (normalizer (V : Set H)) ∧ V ⊔ T ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_isSylowOf_le h.sup_le_normalizer h.isPGroup_sup

theorem relIndex_sup_eq : V.relIndex (V ⊔ T) = U.relIndex T := by
  have : (V.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer h.le_normalizer
  have : (V.subgroupOf (T ⊔ V)).Normal := normal_subgroupOf_sup_of_le_normalizer h.le_normalizer
  have h1 : V.relIndex T = V.relIndex (T ⊔ V) := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient T V h.le_normalizer).toEquiv
  rw [sup_comm, ← h1, ← inf_relIndex_right, h.V_inf_T]

theorem relIndex_U_B : U.relIndex (U ⊔ zpowers t) = 2 := by
  have hs := h.setting
  apply le_antisymm
  · refine relIndex_le_two_of_forall_mul_mem fun a ha b hb haU hbU => ?_
    rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_U ha with
      ha' | ⟨u, hu, rfl⟩
    · exact absurd ha' haU
    rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_U hb with
      hb' | ⟨u', hu', rfl⟩
    · exact absurd hb' hbU
    rw [show u * t * (u' * t) = u * (t * u') * t by group, ← hs.t_mul_comm u' hu',
      show u * (u' * t) * t = u * u' * (t * t) by group, hs.t_mul_t, mul_one]
    exact mul_mem hu hu'
  · have h1 : U.relIndex (U ⊔ zpowers t) ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      exact fun hle => hs.t_not_mem_U (hle (mem_sup_right (mem_zpowers t)))
    have h2 := relIndex_mul_card U (U ⊔ zpowers t)
    have h3 : 0 < Nat.card (U ⊔ zpowers t : Subgroup H) := Nat.card_pos
    have h4 : U.relIndex (U ⊔ zpowers t) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2
      omega
    omega

theorem relIndex_U_T : U.relIndex T = 2 * (U ⊔ zpowers t).relIndex T := by
  rw [← h.relIndex_U_B, relIndex_mul_relIndex U (U ⊔ zpowers t) T le_sup_left
    (h.setting.B_le_T h.sylow h.U_le)]

theorem relIndex_eq_two_or_four_le (hx : ∃ x ∈ V ⊔ T, x * x = 1 ∧ x ∉ V ⊔ zpowers t) :
    (U ⊔ zpowers t).relIndex T = 2 ∨ 4 ≤ (U ⊔ zpowers t).relIndex T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, -, hxV⟩ := hx
  obtain ⟨-, -, p, hp, -, hpB⟩ := h.exists_mul_eq_of_not_mem hx hxV
  have h1 : (U ⊔ zpowers t).relIndex T ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    exact fun hle => hpB (hle hp)
  obtain ⟨a, ha⟩ := h.sylow.isPGroup.exists_card_eq
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (ha ▸ relIndex_dvd_card (U ⊔ zpowers t) T)
  rw [hb] at h1 ⊢
  rcases b with _ | _ | b
  · exact absurd (pow_zero 2) h1
  · exact Or.inl (pow_one 2)
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mul_self_mem_of_relIndex_eq_two (hTB : (U ⊔ zpowers t).relIndex T = 2)
    (hx : ∃ x ∈ V ⊔ T, x * x = 1 ∧ x ∉ V ⊔ zpowers t) {w : H} (hw : w ∈ V ⊔ T) :
    w * w ∈ V := by
  have hs := h.setting
  obtain ⟨x, hx, hxx, hxV⟩ := hx
  obtain ⟨e₀, he₀, τ, hτ, rfl, hτV⟩ := h.exists_mul_eq_of_not_mem hx hxV
  have hτ2 := h.mul_self_mem_of_mul_mul_eq_one he₀ hτ hxx
  have hTU := hs.T_le_normalizer_U h.sylow h.U_le
  have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.mp (h.sylow.le hτ)
  have hvτ : ∀ v ∈ U ⊔ zpowers t, v * (τ * v * τ⁻¹) ∈ U := by
    intro v hv
    rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_U hv with
      hu | ⟨u, hu, rfl⟩
    · exact mul_mem hu ((mem_normalizer_iff.mp (hTU hτ) v).mp hu)
    · have hu' : τ * u * τ⁻¹ ∈ U := (mem_normalizer_iff.mp (hTU hτ) u).mp hu
      have e1 : u * t * (τ * (u * t) * τ⁻¹) = u * (τ * u * τ⁻¹) * (t * t) := by
        calc u * t * (τ * (u * t) * τ⁻¹) = u * t * (τ * u * τ⁻¹) * (τ * t * τ⁻¹) := by group
          _ = u * t * (τ * u * τ⁻¹) * t := by rw [hτt]; group
          _ = u * (t * (τ * u * τ⁻¹)) * t := by group
          _ = u * ((τ * u * τ⁻¹) * t) * t := by rw [hs.t_mul_comm _ hu']
          _ = u * (τ * u * τ⁻¹) * (t * t) := by group
      rw [e1, hs.t_mul_t, mul_one]
      exact mul_mem hu hu'
  have hpT : ∀ p ∈ T, p * p ∈ U := by
    intro p hp
    by_cases hpB : p ∈ U ⊔ zpowers t
    · rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_U hpB with
        hu | ⟨u, hu, rfl⟩
      · exact mul_mem hu hu
      · rw [show u * t * (u * t) = u * (t * u) * t by group, ← hs.t_mul_comm u hu,
          show u * (u * t) * t = (u * u) * (t * t) by group, hs.U_mul_self u hu, hs.t_mul_t,
          mul_one]
        exact one_mem _
    · have hmem : (⟨p, hp⟩ : T) * (⟨τ, hτ⟩ : T)⁻¹ ∈ (U ⊔ zpowers t).subgroupOf T := by
        rw [mul_mem_iff_of_index_two hTB, mem_subgroupOf, inv_mem_iff, mem_subgroupOf]
        exact iff_of_false hpB hτV
      rw [mem_subgroupOf] at hmem
      set v := p * τ⁻¹ with hv
      have hv' : (v : H) ∈ U ⊔ zpowers t := hmem
      have e1 : p * p = v * (τ * v * τ⁻¹) * (τ * τ) := by rw [hv]; group
      rw [e1]
      exact mul_mem (hvτ v hv') hτ2
  obtain ⟨e, he, p, hp, rfl⟩ := h.exists_mul_eq hw
  have hpe : p * e * p⁻¹ ∈ V := (mem_normalizer_iff.mp (h.le_normalizer hp) e).mp he
  rw [show e * p * (e * p) = e * (p * e * p⁻¹) * (p * p) by group]
  exact mul_mem (mul_mem he hpe) (hs.U_le_V (hpT p hp))

theorem relIndex_le_of_relIndex_eq_two (hx : ∃ x ∈ V ⊔ T, x * x = 1 ∧ x ∉ V ⊔ zpowers t)
    (hTB : (U ⊔ zpowers t).relIndex T = 2) {S : Subgroup H} (hSp : IsPGroup 2 S)
    (hSN : S ≤ normalizer (V : Set H)) (hES : V ⊔ T ≤ S) {X : Subgroup H} (hXS : X ≤ S)
    (hX2 : ∀ x ∈ X, x * x = 1) :
    V.relIndex X ≤ 4 ∧ (X ⊓ (V ⊔ T) ≤ V → V.relIndex X ≤ 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.setting
  have hVS : V ≤ S := le_sup_left.trans hES
  have : (V.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hVS).mpr hSN
  set N := V.subgroupOf S with hN
  set π : S →* S ⧸ N := QuotientGroup.mk' N with hπ
  have hQp : IsPGroup 2 (S ⧸ N) := hSp.to_quotient N
  have heq : ∀ a b : S, π a = π b ↔ (a : H)⁻¹ * b ∈ V := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      mem_subgroupOf]
    rfl
  have heq1 : ∀ a : S, π a = 1 ↔ (a : H) ∈ V := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
  have hcard : ∀ Y : Subgroup H, Y ≤ S → Nat.card ((Y.subgroupOf S).map π) = V.relIndex Y := by
    intro Y hY
    rw [← relIndex_ker, hπ, QuotientGroup.ker_mk', hN, relIndex_subgroupOf hY]
  have hsq : ∀ Y : Subgroup H, (∀ y ∈ Y, y * y ∈ V) →
      ∀ v ∈ (Y.subgroupOf S).map π, v * v = 1 := by
    rintro Y hY _ ⟨a, ha, rfl⟩
    rw [← map_mul, heq1]
    exact hY _ (mem_subgroupOf.mp ha)
  set Vb := ((V ⊔ T).subgroupOf S).map π with hVb
  have htS : t ∈ S := hES (mem_sup_right h.mem_T)
  set j := π ⟨t, htS⟩ with hj
  have hjV : j ∈ Vb := ⟨⟨t, htS⟩, mem_subgroupOf.mpr (mem_sup_right h.mem_T), rfl⟩
  have hV2 : ∀ v ∈ Vb, v * v = 1 :=
    hsq _ fun w hw => h.mul_self_mem_of_relIndex_eq_two hTB hx hw
  have hV4 : Nat.card Vb = 4 := by
    rw [hVb, hcard _ hES, h.relIndex_sup_eq, h.relIndex_U_T, hTB]
  have hC : centralizer ({j} : Set (S ⧸ N)) ≤ Vb := by
    intro c hc
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N c
    have hcomm : π s * j = j * π s := mem_centralizer_singleton_iff.mp hc
    have h1 : π (s * ⟨t, htS⟩ * s⁻¹) = π ⟨t, htS⟩ := by
      rw [map_mul, map_mul, map_inv, ← hj, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := (heq _ _).mp h1.symm
    have h3 : t * ((s : H) * t * (s : H)⁻¹) ∈ V := by
      have h4 : ((⟨t, htS⟩ : S) : H)⁻¹ * ((s * ⟨t, htS⟩ * s⁻¹ : S) : H) =
          t⁻¹ * ((s : H) * t * (s : H)⁻¹) := rfl
      rw [h4, hs.t_inv] at h2
      exact h2
    exact ⟨s, mem_subgroupOf.mpr (h.mem_sup_of_mul_conj_mem hSp hES s.2 h3), rfl⟩
  have hX2' : ∀ v ∈ (X.subgroupOf S).map π, v * v = 1 :=
    hsq X fun x hx => by rw [hX2 x hx]; exact one_mem _
  refine ⟨?_, fun hXE => ?_⟩
  · rw [← hcard X hXS]
    exact card_le_four_of_centralizer_le hQp hV4 hV2 hjV hC hX2'
  · rw [← hcard X hXS]
    refine card_le_two_of_inf_eq_bot hQp hV4 hV2 hjV hC hX2' ?_
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rw [mem_bot, heq1]
    have h1 := (heq b a).mp hab
    have haS₀ : (a : H) ∈ V ⊔ T := by
      rw [show (a : H) = b * ((b : H)⁻¹ * a) by group]
      exact mul_mem (mem_subgroupOf.mp hb) (mem_sup_left h1)
    exact hXE (mem_inf.mpr ⟨mem_subgroupOf.mp ha, haS₀⟩)

end Basic

section Cases

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D T : Subgroup H}
  {n : ℕ} (h : Hyp43 A t U V D T n)
include h

theorem exists_sylow_of_no_involution (hinv : ∀ y ∈ V ⊔ T, y * y = 1 → y ∈ V ⊔ zpowers t) :
    ∃ P : Sylow 2 H, (P : Subgroup H) = V ⊔ T ∧
      ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ V ⊔ T → g⁻¹ * v * g ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.setting
  have hsyl := hs.isSylowOf_sup h.sylow h.U_le h.le_normalizer
  have hinvol : ∀ m ∈ normalizer ((V ⊔ T : Subgroup H) : Set H), ∀ x ∈ V ⊔ T, x * x = 1 →
      m * x * m⁻¹ ∈ V ⊔ zpowers t := fun m hm x hx hxx =>
    hinv _ ((mem_normalizer_iff.mp hm x).mp hx) (by
      calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
        _ = 1 := by rw [hxx]; group)
  have hNS : normalizer ((V ⊔ T : Subgroup H) : Set H) ≤
      normalizer ((V ⊔ zpowers t : Subgroup H) : Set H) := by
    refine le_normalizer_of_conj_mem fun m hm k hk => ?_
    rcases mem_or_exists_mul_of_mem_sup_zpowers hs.t_mul_t hs.t_mem_normalizer_V hk with
      hkV | ⟨v, hv, rfl⟩
    · exact hinvol m hm k (mem_sup_left hkV) (hs.V_mul_self k hkV)
    · rw [show m * (v * t) * m⁻¹ = (m * v * m⁻¹) * (m * t * m⁻¹) by group]
      exact mul_mem (hinvol m hm v (mem_sup_left hv) (hs.V_mul_self v hv))
        (hinvol m hm t (mem_sup_right h.mem_T) hs.t_mul_t)
  have hP : IsPGroup 2 (V ⊔ T : Subgroup H) := hsyl.isPGroup
  have hSyl : IsSylowOf 2 (V ⊔ T) ⊤ := by
    by_contra htop
    obtain ⟨P, hPS, z, hzP, hzN, hzS⟩ := exists_mem_normalizer_of_not_isSylowOf hP htop
    have hzB := hs.normalizer_Vt_le_normalizer_B (hNS hzN)
    have hle : V ⊔ T ⊔ zpowers z ≤ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) :=
      sup_le hsyl.le (zpowers_le.mpr hzB)
    have hp' : IsPGroup 2 (V ⊔ T ⊔ zpowers z : Subgroup H) :=
      P.isPGroup'.to_le (sup_le hPS (zpowers_le.mpr hzP))
    have heq := hsyl.eq_of_le le_sup_left hle hp'
    exact hzS (heq ▸ mem_sup_right (mem_zpowers z))
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp hSyl
  rw [relIndex_top_right] at hidx
  refine ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx, fun v hv g hg => ?_⟩
  have hgg : g⁻¹ * v * g * (g⁻¹ * v * g) = 1 := by
    calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hs.V_mul_self v hv]; group
  have hX : g⁻¹ * v * g ∈ rightConjugate V g := by
    rw [mem_rightConjugate_iff, show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
    exact hv
  exact h.inf_Vt_le (h.rightConjugate_mul_self le_rfl g)
    (h.not_conj_mem_rightConjugate le_rfl g) (mem_inf.mpr ⟨hX, hinv _ hg hgg⟩)

theorem exists_sylow_of_relIndex_eq_two (hn : 3 ≤ n)
    (hx : ∃ x ∈ V ⊔ T, x * x = 1 ∧ x ∉ V ⊔ zpowers t)
    (hTB : (U ⊔ zpowers t).relIndex T = 2) :
    ∃ P : Sylow 2 H, V ≤ P ∧
      ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ (P : Subgroup H) → g⁻¹ * v * g ∈ V := by
  have hs := h.setting
  obtain ⟨S, hsyl, hES⟩ := h.exists_isSylowOf_le_normalizer
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hX : ∀ U' ≤ V, ∀ g : H, rightConjugate U' g ≤ S → ¬ rightConjugate U' g ≤ V →
      ∃ w ∈ rightConjugate U' g,
        V.relIndex (rightConjugate U' g) < Nat.card (⁅V, zpowers w⁆ : Subgroup H) := by
    intro U' hU' g hUS hUE
    have hX2 := h.rightConjugate_mul_self hU' g
    obtain ⟨h4, h2'⟩ := h.relIndex_le_of_relIndex_eq_two hx hTB hsyl.isPGroup hsyl.le hES hUS hX2
    by_cases hX0 : rightConjugate U' g ⊓ (V ⊔ T) ≤ V
    · obtain ⟨w, hwX, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hUE
      have hw0 : w ∉ V ⊔ T := fun hw0 => hwE (hX0 (mem_inf.mpr ⟨hwX, hw0⟩))
      have hC := h.card_inf_centralizer_sq_le_of_not_mem hsyl.isPGroup hsyl.le hES (hUS hwX) hw0
      refine ⟨w, hwX, lt_card_commutator_of_mul_lt hs.V_comm (hsyl.le (hUS hwX)) ?_⟩
      rw [hs.card_V]
      have hr := h2' hX0
      set c := Nat.card (V ⊓ centralizer ({w} : Set H) : Subgroup H)
      set r := V.relIndex (rightConjugate U' g)
      set q := 2 ^ n
      by_contra hle
      push Not at hle
      have h1 : (q ^ 2) ^ 2 ≤ (c * r) ^ 2 := Nat.pow_le_pow_left hle 2
      have hr2 : r ^ 2 ≤ 4 := by nlinarith
      have h3 : (c * r) ^ 2 ≤ q ^ 3 * 4 := by
        rw [mul_pow]
        exact Nat.mul_le_mul hC hr2
      have h5 : q ^ 3 * q ≤ q ^ 3 * 4 := by
        calc q ^ 3 * q = (q ^ 2) ^ 2 := by ring
          _ ≤ _ := h1.trans h3
      have hq3 : 0 < q ^ 3 := by positivity
      have := Nat.le_of_mul_le_mul_left h5 hq3
      omega
    · obtain ⟨w, hw, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hX0
      obtain ⟨hwX, hw0⟩ := mem_inf.mp hw
      have hC := hs.card_inf_centralizer_le h.sylow h.U_le h.le_normalizer hw0 hwE
      refine ⟨w, hwX, lt_card_commutator_of_mul_lt hs.V_comm (hsyl.le (hUS hwX)) ?_⟩
      rw [hs.card_V]
      calc _ ≤ 2 ^ n * 4 := Nat.mul_le_mul hC h4
        _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = (2 ^ n) ^ 2 := (sq _).symm
  obtain ⟨P, hPS, hcl⟩ :=
    exists_sylow_stronglyClosed_of_commutator_bound (le_sup_left.trans hES) hs.V_mul_self hsyl hX
  exact ⟨P, hPS ▸ le_sup_left.trans hES, fun v hv g hg => hcl v hv g (hPS ▸ hg)⟩

theorem exists_sylow_of_relIndex_le_two (hn : 3 ≤ n) (hTB : (U ⊔ zpowers t).relIndex T ≤ 2) :
    ∃ P : Sylow 2 H, V ≤ P ∧
      ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ (P : Subgroup H) → g⁻¹ * v * g ∈ V := by
  by_cases hx : ∃ x ∈ V ⊔ T, x * x = 1 ∧ x ∉ V ⊔ zpowers t
  · rcases h.relIndex_eq_two_or_four_le hx with h2 | h4
    · exact h.exists_sylow_of_relIndex_eq_two hn hx h2
    · omega
  · push Not at hx
    obtain ⟨P, hP, hcl⟩ := h.exists_sylow_of_no_involution hx
    exact ⟨P, hP ▸ le_sup_left, fun v hv g hg => hcl v hv g (hP ▸ hg)⟩

end Cases

end Hyp43

end CFSG.LocalAnalysis.EvenBN.GMS
