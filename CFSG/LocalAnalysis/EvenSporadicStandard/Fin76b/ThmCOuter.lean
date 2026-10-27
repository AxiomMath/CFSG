module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup MulAction CFSG.RankThree.Transfer

structure OuterConfig (G : Type*) [Group G] (A : Subgroup G) (z t : G) (T : Subgroup G) :
    Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_cent : z ∈ centralizer (A : Set G)
  disjoint : Disjoint A (zpowers z)
  cent_le : centralizer ({z} : Set G) ≤ normalizer (A : Set G)
  index_two : (A ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2
  T_le : T ≤ centralizer ({z} : Set G)
  T_pgroup : IsPGroup 2 T
  T_max : ∀ P : Subgroup G, P ≤ centralizer ({z} : Set G) → IsPGroup 2 P → T ≤ P → P ≤ T
  z_mem : z ∈ T
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_mem_A : t ∈ A
  t_mem_T : t ∈ T
  t_central : ∀ y ∈ T, y * t = t * y
  t_fourth : ∃ g ∈ A, g * g * (g * g) = t
  center_T : ∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = z ∨ y = t ∨ y = z * t

namespace OuterConfig

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
theorem z_not_mem_A : z ∉ A := fun hz => h.z_ne (by
  have : z ∈ A ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [h.disjoint.eq_bot, mem_bot] at this
  exact this)

include h in
theorem z_comm_of_mem_A {a : G} (ha : a ∈ A) : a * z = z * a :=
  mem_centralizer_iff.1 h.z_cent a ha

include h in
theorem t_comm_z : t * z = z * t := h.z_comm_of_mem_A h.t_mem_A

include h in
theorem z_ne_t : z ≠ t := fun hzt => h.z_not_mem_A (hzt ▸ h.t_mem_A)

include h in
theorem z_order : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne

include h in
theorem z_central_T : ∀ y ∈ T, y * z = z * y := fun _ hy =>
  mem_centralizer_singleton_iff.1 (h.T_le hy)

include h in
theorem central_zt : ∀ y ∈ T, y * (z * t) = (z * t) * y := by
  intro y hy
  calc y * (z * t) = (y * z) * t := by group
    _ = (z * y) * t := by rw [h.z_central_T y hy]
    _ = z * (y * t) := by group
    _ = z * (t * y) := by rw [h.t_central y hy]
    _ = (z * t) * y := by group

include h in
theorem sq_mem_sup {g : G} (hg : g ∈ centralizer ({z} : Set G)) :
    g * g ∈ A ⊔ zpowers z := by
  have hidx : ((A ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 :=
    h.index_two
  have hN : ((A ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hmem := Subgroup.pow_index_mem
    ((A ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))) (⟨g, hg⟩ : centralizer ({z} : Set G))
  rw [hidx] at hmem
  have := mem_subgroupOf.1 hmem
  simpa [pow_two] using this

include h in
theorem z_not_fourth : ¬ ∃ g : G, g * g * (g * g) = z := by
  rintro ⟨g, hg⟩
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * (g * g * (g * g)) := by rw [hg]
      _ = (g * g * (g * g)) * g := by group
      _ = z * g := by rw [hg]
  obtain ⟨a, ha, c, hc, hac⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.z_cent) (h.sq_mem_sup hgz)
  have hcz : c * a = a * c := by
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
    · simp
    · exact (h.z_comm_of_mem_A ha).symm
  have hcc : c * c = 1 := by
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
    · simp
    · exact h.z_sq
  have h4 : g * g * (g * g) = a * a := by
    rw [hac]
    calc a * c * (a * c) = a * (c * a) * c := by group
      _ = a * (a * c) * c := by rw [hcz]
      _ = a * a * (c * c) := by group
      _ = a * a := by rw [hcc, mul_one]
  rw [h4] at hg
  exact h.z_not_mem_A (hg ▸ mul_mem ha ha)

include h in
theorem conj_t_ne_z (x : G) : x * t * x⁻¹ ≠ z := by
  intro hx
  obtain ⟨g, hgA, hg⟩ := h.t_fourth
  refine h.z_not_fourth ⟨x * g * x⁻¹, ?_⟩
  calc x * g * x⁻¹ * (x * g * x⁻¹) * (x * g * x⁻¹ * (x * g * x⁻¹))
      = x * (g * g * (g * g)) * x⁻¹ := by group
    _ = z := by rw [hg, hx]

include h in
theorem conj_z_ne_t (x : G) : x * z * x⁻¹ ≠ t := by
  intro hx
  obtain ⟨g, hgA, hg⟩ := h.t_fourth
  refine h.z_not_fourth ⟨x⁻¹ * g * x, ?_⟩
  calc x⁻¹ * g * x * (x⁻¹ * g * x) * (x⁻¹ * g * x * (x⁻¹ * g * x))
      = x⁻¹ * (g * g * (g * g)) * x := by group
    _ = z := by rw [hg, ← hx]; group

include h in
theorem normalizer_dichotomy {x : G} (hx : x ∈ normalizer (T : Set G)) :
    (x * z * x⁻¹ = z ∧ x * t * x⁻¹ = t) ∨ (x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t) := by
  obtain ⟨hz1, hz2⟩ := conj_central_of_normalizer hx h.z_mem h.z_central_T
  obtain ⟨ht1, ht2⟩ := conj_central_of_normalizer hx h.t_mem_T h.t_central
  have hz1' := h.center_T _ hz1 hz2
  have ht1' := h.center_T _ ht1 ht2
  have hxz_ne : x * z * x⁻¹ ≠ 1 := fun e => h.z_ne (by
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, e]; group)
  have hxt_ne : x * t * x⁻¹ ≠ 1 := fun e => h.t_ne (by
    have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
    rw [this, e]; group)
  have hxz : x * z * x⁻¹ = z ∨ x * z * x⁻¹ = z * t := by
    rcases hz1' with e | e | e | e
    · exact absurd e hxz_ne
    · exact Or.inl e
    · exact absurd e (h.conj_z_ne_t x)
    · exact Or.inr e
  have hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t := by
    rcases ht1' with e | e | e | e
    · exact absurd e hxt_ne
    · exact absurd e (h.conj_t_ne_z x)
    · exact Or.inl e
    · exact Or.inr e
  rcases hxz with e1 | e1 <;> rcases hxt with e2 | e2
  · exact Or.inl ⟨e1, e2⟩
  · exfalso
    have hxc : x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have : x * z = (x * z * x⁻¹) * x := by group
      rw [this, e1]
    have hat : x * t * x⁻¹ ∈ A := (mem_normalizer_iff.1 (h.cent_le hxc) t).1 h.t_mem_A
    rw [e2] at hat
    exact h.z_not_mem_A (by simpa using mul_mem hat (inv_mem h.t_mem_A))
  · exact Or.inr ⟨e1, e2⟩
  · exfalso
    have h3 : x * z * x⁻¹ = x * t * x⁻¹ := e1.trans e2.symm
    have : z = t := mul_left_cancel (mul_right_cancel h3)
    exact h.z_ne_t this

include h in
theorem mem_T_of_two_group {x : G} (hx : x ∈ centralizer ({z} : Set G)) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) (hxQ : x ∈ Q) : x ∈ T := by
  have hP : IsPGroup 2 (T ⊔ zpowers x : Subgroup G) :=
    hQ.to_le (sup_le hTQ (zpowers_le.2 hxQ))
  have hle : T ⊔ zpowers x ≤ centralizer ({z} : Set G) :=
    sup_le h.T_le (zpowers_le.2 hx)
  exact h.T_max _ hle hP le_sup_left (mem_sup_right (mem_zpowers x))

include h in
theorem normalizer_fixes_of_sylow [Finite G] (hT : ¬ 2 ∣ T.index) {x : G}
    (hx : x ∈ normalizer (T : Set G)) : x * z * x⁻¹ = z ∧ x * t * x⁻¹ = t := by
  rcases h.normalizer_dichotomy hx with h1 | ⟨h1, h2⟩
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ := exists_odd_pow_mem hT hx
    have hsq : x ^ 2 * z * (x ^ 2)⁻¹ = z := by
      have e1 : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      calc x ^ 2 * z * (x ^ 2)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (z * t) * x⁻¹ := by rw [h1]
        _ = (x * z * x⁻¹) * (x * t * x⁻¹) := e1
        _ = (z * t) * t := by rw [h1, h2]
        _ = z * (t * t) := by group
        _ = z := by rw [h.t_sq, mul_one]
    have hc2 : Commute (x ^ 2) z := by
      have : x ^ 2 * z = z * x ^ 2 := by
        calc x ^ 2 * z = (x ^ 2 * z * (x ^ 2)⁻¹) * x ^ 2 := by simp [mul_assoc]
          _ = z * x ^ 2 := by rw [hsq]
      exact this
    have hcm : Commute (x ^ (2 * k + 1)) z := (h.z_central_T _ hk)
    have hx_eq : x = ((x ^ 2) ^ k)⁻¹ * x ^ (2 * k + 1) := by
      have : (x ^ 2) ^ k * x = x ^ (2 * k + 1) := by rw [← pow_mul, ← pow_succ]
      rw [← this]; group
    have hcx : Commute x z := by
      rw [hx_eq]
      exact (hc2.pow_left k).inv_left.mul_left hcm
    have h4 : x * z * x⁻¹ = z := by
      have : x * z = z * x := hcx
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [this]
        _ = z := by group
    rw [h4] at h1
    have : t = 1 := by
      have h3 : z * t = z * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel h3
    exact h.t_ne this

include h in
theorem not_conj_of_sylow [Finite G] (hT : ¬ 2 ∣ T.index) {u w : G}
    (hu : u = z ∨ u = t ∨ u = z * t) (hw : w = z ∨ w = t ∨ w = z * t) {g : G}
    (hg : g * u * g⁻¹ = w) : w = u := by
  have hcen : ∀ v : G, (v = z ∨ v = t ∨ v = z * t) → ∀ y ∈ T, y * v = v * y := by
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact h.z_central_T
    · rw [hv]; exact h.t_central
    · rw [hv]; exact h.central_zt
  obtain ⟨n, hn, hn'⟩ := exists_normalizer_conj h.T_pgroup hT (hcen u hu) (hcen w hw) hg
  obtain ⟨hz, ht⟩ := h.normalizer_fixes_of_sylow hT hn
  have hfix : ∀ v : G, (v = z ∨ v = t ∨ v = z * t) → n * v * n⁻¹ = v := by
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact hz
    · rw [hv]; exact ht
    · rw [hv]
      calc n * (z * t) * n⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) := by group
        _ = z * t := by rw [hz, ht]
  rw [← hn', hfix u hu]

include h in
theorem card_sup [Finite G] : Nat.card (A ⊔ zpowers z : Subgroup G) = 2 * Nat.card A := by
  have e := mulEquivProdSup (zpowers_le.2 h.z_cent) h.disjoint
  rw [Nat.card_congr e.toEquiv.symm, Nat.card_prod, Nat.card_zpowers, h.z_order]
  ring

include h in
theorem A_relIndex_sup [Finite G] : A.relIndex (A ⊔ zpowers z) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ zpowers z)
  rw [inf_eq_left.2 le_sup_left, h.card_sup] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

include h in
theorem exists_fused_centralizing [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ ∀ p ∈ T, p * (g * z * g⁻¹) = (g * z * g⁻¹) * p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hAH : A ≤ centralizer ({z} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A ha)
  have hNn : (A.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).2 h.cent_le
  have hrel : A.relIndex (centralizer ({z} : Set G)) = 2 * 2 := by
    rw [← Subgroup.relIndex_mul_relIndex A (A ⊔ zpowers z) (centralizer ({z} : Set G))
      le_sup_left (sup_le hAH (zpowers_le.2 hzH)), h.A_relIndex_sup, h.index_two]
  have hcard : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
      2 ^ 2 := by
    have : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
        A.relIndex (centralizer ({z} : Set G)) := rfl
    rw [this, hrel]
    norm_num
  let _ : CommGroup (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) :=
    IsPGroup.commGroupOfCardEqPrimeSq hcard
  let ψ : centralizer ({z} : Set G) →*
      (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) :=
    QuotientGroup.mk' (A.subgroupOf (centralizer ({z} : Set G)))
  have hψ : ψ ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1 := by
    intro h1
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact h.z_not_mem_A (mem_subgroupOf.1 h2)
  exact McLStd.exists_conj_ne_centralizing (t := z) hnonab h.z_sq h.T_pgroup h.z_mem
    h.z_central_T ψ hψ

include h in
theorem fused_eq [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, g * z * g⁻¹ = z * t := by
  obtain ⟨g, hne, hcomm⟩ := h.exists_fused_centralizing hnonab
  set z' : G := g * z * g⁻¹ with hz'
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hz'1 : z' ≠ 1 := fun e => h.z_ne (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [← hz', e]; group)
  have hz'H : z' ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (hcomm z h.z_mem).symm
  have hz'order : orderOf z' = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz'2) hz'1
  have hpg : IsPGroup 2 (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'order, pow_one])
  have hTn : T ≤ normalizer (zpowers z' : Set G) := by
    intro y hy
    have hk : ∀ w ∈ T, ∀ k ∈ zpowers z', w * k * w⁻¹ = k := by
      intro w hw k hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
      have hc : w * z' = z' * w := hcomm w hw
      have := ((Commute.zpow_right (show Commute w z' from hc) n).eq)
      rw [this]; group
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hmem => by rw [hk y hy k hmem]; exact hmem, fun hmem => ?_⟩
    have h2 := hk y⁻¹ (inv_mem hy) _ hmem
    have h3 : y⁻¹ * (y * k * y⁻¹) * y⁻¹⁻¹ = k := by group
    rw [h3] at h2
    rw [h2]; exact hmem
  have hQ : IsPGroup 2 (T ⊔ zpowers z' : Subgroup G) := h.T_pgroup.to_sup_of_normal_right' hpg hTn
  have hz'T : z' ∈ T :=
    h.mem_T_of_two_group hz'H hQ le_sup_left (mem_sup_right (mem_zpowers z'))
  rcases h.center_T z' hz'T (fun x hx => hcomm x hx) with e | e | e | e
  · exact absurd e hz'1
  · exact absurd e hne
  · exact absurd e (h.conj_z_ne_t g)
  · exact ⟨g, e⟩

include h in
theorem false_of_sylow [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hT : ¬ 2 ∣ T.index) : False := by
  obtain ⟨g, hg⟩ := h.fused_eq hnonab
  have := h.not_conj_of_sylow hT (Or.inl rfl) (Or.inr (Or.inr rfl)) hg
  exact h.t_ne (mul_left_cancel (this.trans (mul_one z).symm))

include h in
theorem exists_swap [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ (Q : Sylow 2 G) (x : G), T ≤ (Q : Subgroup G) ∧ x ∈ (Q : Subgroup G) ∧ x ∉ T ∧
      x ∈ normalizer (T : Set G) ∧ x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.T_pgroup.exists_le_sylow
  by_cases hTQ : T = Q
  · exfalso
    exact h.false_of_sylow hnonab (by rw [hTQ]; exact Q.not_dvd_index)
  · let TQ : Subgroup (Q : Subgroup G) := T.subgroupOf (Q : Subgroup G)
    have hTQne : TQ < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hTQ ?_
      refine le_antisymm hQ (fun q hq => ?_)
      have : (⟨q, hq⟩ : (Q : Subgroup G)) ∈ TQ := by rw [htop]; trivial
      exact mem_subgroupOf.1 this
    have : Group.IsNilpotent (Q : Subgroup G) := Q.isPGroup'.isNilpotent
    have hnc : NormalizerCondition (Q : Subgroup G) := Group.normalizerCondition_of_isNilpotent
    obtain ⟨y, hyN, hyn⟩ := IsConcreteLE.exists_of_lt (hnc TQ hTQne)
    have hxN : (y : G) ∈ normalizer (T : Set G) := by
      have : y ∈ (normalizer (T : Set G)).subgroupOf (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf_normalizer_eq hQ]; exact hyN
      exact mem_subgroupOf.1 this
    have hxT : (y : G) ∉ T := fun hyT => hyn (mem_subgroupOf.2 hyT)
    rcases h.normalizer_dichotomy hxN with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      refine hxT (h.mem_T_of_two_group ?_ Q.isPGroup' hQ y.2)
      rw [mem_centralizer_singleton_iff]
      calc (y : G) * z = ((y : G) * z * (y : G)⁻¹) * (y : G) := by group
        _ = z * (y : G) := by rw [h1]
    · exact ⟨Q, y, hQ, y.2, hxT, hxN, h1, h2⟩

end OuterConfig

end CFSG.EvenSporadicStandard.Fin76b
