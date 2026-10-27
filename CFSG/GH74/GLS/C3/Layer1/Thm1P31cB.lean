module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cA
public import CFSG.GH74.GLS.C3.Layer1.Thm1A7Two

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1A7 CFSG.GH74.GLS.C3.Layer1.Thm1G33
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section ArgB

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem Env31.hQcapQa (E : Env31 x y K T f z) {a : G} (hxa : a * x * a⁻¹ ≠ x) :
    ∀ w ∈ T ⊓ CxK x K, a⁻¹ * w * a ∈ T ⊓ CxK x K → w = 1 := by
  intro w hw hwa
  by_contra hw1
  have hw2 : ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.hsetup.sylowT.isPGroup ⟨w, hw.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨m, hm⟩ := exists_involution_pow hw2 hw1
  have hwm : w ^ m ∈ T ⊓ CxK x K := Subgroup.pow_mem _ hw m
  have hconj : a⁻¹ * w ^ m * a = (a⁻¹ * w * a) ^ m := by
    have := conj_pow (a := a⁻¹) (b := w) (i := m)
    simpa using this.symm
  have hwma : a⁻¹ * w ^ m * a ∈ T ⊓ CxK x K := by
    rw [hconj]
    exact Subgroup.pow_mem _ hwa m
  have hsq : w ^ m * w ^ m = 1 := by
    have := pow_orderOf_eq_one (w ^ m)
    rwa [hm, sq] at this
  have hne1 : w ^ m ≠ 1 := fun h => by rw [h, orderOf_one] at hm; omega
  have hwx : w ^ m = x := (E.hQ_unique (w ^ m) hwm hsq).resolve_left hne1
  have hsq' : (a⁻¹ * w ^ m * a) * (a⁻¹ * w ^ m * a) = 1 := by
    calc (a⁻¹ * w ^ m * a) * (a⁻¹ * w ^ m * a) = a⁻¹ * (w ^ m * w ^ m) * a := by group
      _ = 1 := by rw [hsq]; group
  rcases E.hQ_unique _ hwma hsq' with h | h
  · apply E.hx1
    rw [hwx] at h
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [hwx] at h
    apply hxa
    have h' : a * x = x * a := by
      calc a * x = a * (a⁻¹ * x * a) := by rw [h]
        _ = x * a := by group
    calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [h']
      _ = x := by group

theorem Env31.hQa_unique (E : Env31 x y K T f z) {a : G} :
    ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → w * w = 1 → w = 1 ∨ w = a * x * a⁻¹ := by
  intro w hw hww
  have hsq' : (a⁻¹ * w * a) * (a⁻¹ * w * a) = 1 := by
    calc (a⁻¹ * w * a) * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
      _ = 1 := by rw [hww]; group
  rcases E.hQ_unique _ hw hsq' with h | h
  · left
    calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [h]

omit [Finite G] in
theorem Env31.hQa_norm (E : Env31 x y K T f z) {a : G} (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) :
    ∀ t ∈ T, ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K →
      a⁻¹ * (t * w * t⁻¹) * a ∈ T ⊓ CxK x K := by
  intro t ht w hw
  have : a⁻¹ * (t * w * t⁻¹) * a = (a⁻¹ * t * a) * (a⁻¹ * w * a) * (a⁻¹ * t * a)⁻¹ := by group
  rw [this]
  exact E.hQnorm _ (haN2 t ht) _ hw

omit [Finite G] in
theorem Env31.hPa_norm (E : Env31 x y K T f z) {a : G} (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) :
    ∀ t ∈ T, ∀ w, a⁻¹ * w * a ∈ T ⊓ K → a⁻¹ * (t * w * t⁻¹) * a ∈ T ⊓ K := by
  intro t ht w hw
  have : a⁻¹ * (t * w * t⁻¹) * a = (a⁻¹ * t * a) * (a⁻¹ * w * a) * (a⁻¹ * t * a)⁻¹ := by group
  rw [this]
  exact E.hPnorm _ (haN2 t ht) _ hw

omit [Finite G] in
theorem Env31.hQa_T {a : G} (_E : Env31 x y K T f z) (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T) {w : G}
    (hw : a⁻¹ * w * a ∈ T ⊓ CxK x K) : w ∈ T := by
  have := haN1 _ hw.1
  have e1 : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
  rwa [e1] at this

omit [Finite G] in
theorem Env31.hPa_T {a : G} (_E : Env31 x y K T f z) (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T) {w : G}
    (hw : a⁻¹ * w * a ∈ T ⊓ K) : w ∈ T := by
  have := haN1 _ hw.1
  have e1 : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
  rwa [e1] at this

theorem Env31.hz_Qa (E : Env31 x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : a⁻¹ * z * a ∈ T ⊓ CxK x K := by
  classical
  by_contra hzQa
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := E.hPK.isPGroup
  have hcap : ∀ w ∈ T ⊓ K, a⁻¹ * w * a ∈ T ⊓ CxK x K → w = 1 := by
    intro w hw hwa
    by_contra hw1
    set N : Subgroup G := (T ⊓ K) ⊓ (T ⊓ CxK x K).map (MulAut.conj a).toMonoidHom with hN
    have hNP : N ≤ T ⊓ K := inf_le_left
    have hNn : ∀ p ∈ T ⊓ K, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
      intro p hp n hn
      have hn' := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨E.hPnorm p hp.1 n hn'.1, ?_⟩
      exact mem_map_conj_iff.2 (E.hQa_norm haN2 p hp.1 n (mem_map_conj_iff.1 hn'.2))
    have hzN : z ∈ N := z_mem_of_normal hP2 E.hzu hNP hNn
      ⟨w, Subgroup.mem_inf.2 ⟨hw, mem_map_conj_iff.2 hwa⟩, hw1⟩
    exact hzQa (mem_map_conj_iff.1 (Subgroup.mem_inf.1 hzN).2)
  have hcomm : ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → ∀ p ∈ T ⊓ K, w * p = p * w := by
    intro w hw p hp
    have hwT : w ∈ T := E.hQa_T haN1 hw
    have hwinv : a⁻¹ * w⁻¹ * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * w⁻¹ * a = (a⁻¹ * w * a)⁻¹ := by group
      rw [this]
      exact (T ⊓ CxK x K).inv_mem hw
    have h1 : a⁻¹ * (p * w⁻¹ * p⁻¹) * a ∈ T ⊓ CxK x K := E.hQa_norm haN2 p hp.1 w⁻¹ hwinv
    have hcQa : a⁻¹ * (w * p * w⁻¹ * p⁻¹) * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * (w * p * w⁻¹ * p⁻¹) * a =
          (a⁻¹ * w * a) * (a⁻¹ * (p * w⁻¹ * p⁻¹) * a) := by group
      rw [this]
      exact (T ⊓ CxK x K).mul_mem hw h1
    have hcP : w * p * w⁻¹ * p⁻¹ ∈ T ⊓ K := by
      have := (T ⊓ K).mul_mem (E.hPnorm w hwT p hp) ((T ⊓ K).inv_mem hp)
      simpa [mul_assoc] using this
    have := hcap _ hcP hcQa
    calc w * p = (w * p * w⁻¹ * p⁻¹) * (p * w) := by group
      _ = p * w := by rw [this, one_mul]
  have hsq : ∀ w, a⁻¹ * w * a ∈ T ⊓ CxK x K → w * w = 1 := by
    intro w hw
    have hwT : w ∈ T := E.hQa_T haN1 hw
    have hsqQ : w * w ∈ T ⊓ CxK x K := E.hsq_CTP w hwT (hcomm w hw)
    have hsqQa : a⁻¹ * (w * w) * a ∈ T ⊓ CxK x K := by
      have : a⁻¹ * (w * w) * a = (a⁻¹ * w * a) * (a⁻¹ * w * a) := by group
      rw [this]
      exact (T ⊓ CxK x K).mul_mem hw hw
    exact E.hQcapQa hxa _ hsqQ hsqQa
  have hQ2 : Nat.card ↥(T ⊓ CxK x K) ≤ 2 := by
    have hle : T ⊓ CxK x K ≤ zpowers x := by
      intro q hq
      have hw : a⁻¹ * (a * q * a⁻¹) * a ∈ T ⊓ CxK x K := by
        have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
        rw [this]
        exact hq
      rcases E.hQa_unique (a := a) _ hw (hsq _ hw) with h | h
      · have : q = 1 := by
          calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
            _ = 1 := by rw [h]; group
        rw [this]
        exact (zpowers x).one_mem
      · have : q = x := by
          calc q = a⁻¹ * (a * q * a⁻¹) * a := by group
            _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [h]
            _ = x := by group
        rw [this]
        exact mem_zpowers x
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, E.hu2.1.1.1] at this
  omega

theorem Env31.hza (E : Env31 x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : a * x * a⁻¹ = z := by
  have hz := E.hz_Qa haN1 haN2 hxa hQ3
  have hsq' : (a⁻¹ * z * a) * (a⁻¹ * z * a) = 1 := by
    calc (a⁻¹ * z * a) * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a := by group
      _ = 1 := by rw [E.hz2']; group
  rcases E.hQ_unique _ hz hsq' with h | h
  · exfalso
    apply E.hz1
    calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc a * x * a⁻¹ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [h]
      _ = z := by group

theorem Env31.haz (E : Env31 x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) (ha2 : a * a ∈ T) : a * z * a⁻¹ = x := by
  rw [← E.hza haN1 haN2 hxa hQ3]
  have h1 : (a * a) * x = x * (a * a) := mem_centralizer_singleton_iff.1 (E.hTC ha2)
  calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
    _ = x * (a * a) * (a * a)⁻¹ := by rw [h1]
    _ = x := by group

theorem Env31.hPPa (E : Env31 x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) :
    ∀ w ∈ T ⊓ K, a⁻¹ * w * a ∈ T ⊓ K → w = 1 := by
  classical
  intro w hw hwa
  by_contra hw1
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := E.hPK.isPGroup
  set N : Subgroup G := (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom with hN
  have hNP : N ≤ T ⊓ K := inf_le_left
  have hNn : ∀ p ∈ T ⊓ K, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
    intro p hp n hn
    have hn' := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨E.hPnorm p hp.1 n hn'.1, ?_⟩
    exact mem_map_conj_iff.2 (E.hPa_norm haN2 p hp.1 n (mem_map_conj_iff.1 hn'.2))
  have hzN : z ∈ N := z_mem_of_normal hP2 E.hzu hNP hNn
    ⟨w, Subgroup.mem_inf.2 ⟨hw, mem_map_conj_iff.2 hwa⟩, hw1⟩
  have hzP : a⁻¹ * z * a ∈ T ⊓ K := mem_map_conj_iff.1 (Subgroup.mem_inf.1 hzN).2
  have hzQ : a⁻¹ * z * a ∈ T ⊓ CxK x K := E.hz_Qa haN1 haN2 hxa hQ3
  have : a⁻¹ * z * a ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hzP, hzQ⟩
  rw [E.hPQ, Subgroup.mem_bot] at this
  apply E.hz1
  calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem Env31.hcommPPa (E : Env31 x y K T f z) {a : G} (haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (hxa : a * x * a⁻¹ ≠ x)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) :
    ∀ p ∈ T ⊓ K, ∀ w, a⁻¹ * w * a ∈ T ⊓ K → p * w = w * p := by
  intro p hp w hw
  have hwT : w ∈ T := E.hPa_T haN1 hw
  have hwinv : a⁻¹ * w⁻¹ * a ∈ T ⊓ K := by
    have : a⁻¹ * w⁻¹ * a = (a⁻¹ * w * a)⁻¹ := by group
    rw [this]
    exact (T ⊓ K).inv_mem hw
  have h1 : a⁻¹ * (p * w⁻¹ * p⁻¹) * a ∈ T ⊓ K := E.hPa_norm haN2 p hp.1 w⁻¹ hwinv
  have hcPa : a⁻¹ * (p * w * p⁻¹ * w⁻¹) * a ∈ T ⊓ K := by
    have : a⁻¹ * (p * w * p⁻¹ * w⁻¹) * a =
        (a⁻¹ * (p * w * p⁻¹) * a) * (a⁻¹ * w * a)⁻¹ := by group
    rw [this]
    exact (T ⊓ K).mul_mem (E.hPa_norm haN2 p hp.1 w hw) ((T ⊓ K).inv_mem hw)
  have hcP : p * w * p⁻¹ * w⁻¹ ∈ T ⊓ K := by
    have h2 := (T ⊓ K).mul_mem hp (E.hPnorm w hwT p⁻¹ ((T ⊓ K).inv_mem hp))
    have e1 : p * (w * p⁻¹ * w⁻¹) = p * w * p⁻¹ * w⁻¹ := by group
    rwa [e1] at h2
  have := E.hPPa haN1 haN2 hxa hQ3 _ hcP hcPa
  calc p * w = (p * w * p⁻¹ * w⁻¹) * (w * p) := by group
    _ = w * p := by rw [this, one_mul]


theorem Env31.exists_a (hG : C3Hyp G) (hS34 : P34.S_prop34) (E : Env31 x y K T f z) :
    ∃ a : G, (∀ t ∈ T, a * t * a⁻¹ ∈ T) ∧ (∀ t ∈ T, a⁻¹ * t * a ∈ T) ∧ a * a ∈ T ∧
      a * x * a⁻¹ ≠ x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hTS'⟩ := EvenSporTransfer.exists_isSylowOf_ge (N := (⊤ : Subgroup G)) (A := T)
    le_top E.hsetup.sylowT.isPGroup
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hTne : T ≠ S := by
    intro hTS
    subst hTS
    have hidx : ¬ 2 ∣ T.index := by
      have := (isSylowOf_iff.1 hS).2.2
      rwa [Subgroup.relIndex_top_right] at this
    have hcen : CFSG.GH74.IsCentralInvolution x := by
      refine ⟨E.hu2.1.1.1, hS2.toSylow hidx, ?_, ?_⟩
      · rw [IsPGroup.toSylow_coe]
        exact E.hxT
      · rw [IsPGroup.toSylow_coe]
        intro s hs
        exact (mem_centralizer_singleton_iff.1 (E.hTC hs))
    exact E.not_central hG hS34 hcen
  have hTS : T < S := lt_of_le_of_ne hTS' hTne
  obtain ⟨b, hbS, hbN, hbT⟩ := exists_mem_normalizer_not_mem hTS.le hTS.ne hS2
  have hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hS2 ⟨b, hbS⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨a, ha, haT, ha2⟩ := exists_pow_not_mem_sq_mem hb2 hbT
  have haS : a ∈ S := (zpowers_le).2 hbS ha
  have haN : a ∈ normalizer (T : Set G) := (zpowers_le).2 hbN ha
  have hxa : a * x * a⁻¹ ≠ x := by
    intro h
    have hac : a ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h]
    have hN₂C : T ⊔ zpowers a ≤ centralizer ({x} : Set G) :=
      sup_le E.hTC ((zpowers_le).2 hac)
    have hN₂S : T ⊔ zpowers a ≤ S := sup_le hTS.le ((zpowers_le).2 haS)
    have hN₂ : IsPGroup 2 ↥(T ⊔ zpowers a) := hS2.to_le hN₂S
    have heq := E.hsetup.sylowT.eq_of_le le_sup_left hN₂C hN₂
    exact haT (heq ▸ Subgroup.mem_sup_right (mem_zpowers a))
  have haN1 : ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 haN t).1 ht
  have haN2 : ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 haN (a⁻¹ * t * a)).2 (by
      have : a * (a⁻¹ * t * a) * a⁻¹ = t := by group
      rw [this]; exact ht)
  exact ⟨a, haN1, haN2, by rw [← sq]; exact ha2, hxa⟩

end ArgB

section Dih

variable {G : Type} [Group G]

theorem exists_dihedral_data {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hP : IsDihedralTwoGroup ↥P n)
    {z : G} (hzP : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ q ∈ P, z * q = q * z) :
    ∃ d ∈ P, ∃ r₀ ∈ P, d * d = 1 ∧ d ≠ 1 ∧ d ≠ z ∧ r₀ * d * r₀⁻¹ = z * d := by
  obtain ⟨-, k, hk, -, ⟨φ⟩⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h8 : (2 : ℕ) ^ (m + 3) = 8 * 2 ^ m := by ring
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨t, rfl⟩ : ∃ t, k = 4 * t := ⟨2 ^ m, by omega⟩
  have ht : 1 ≤ t := by omega
  have : NeZero (4 * t) := ⟨by omega⟩
  have hkeven : Even (4 * t) := ⟨2 * t, by ring⟩
  have hk2' : 4 * t ≠ 2 := by omega
  have hZc : φ ⟨z, hzP⟩ ∈ Subgroup.center (DihedralGroup (4 * t)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc q q.2).symm
  have hZ1 : φ ⟨z, hzP⟩ ≠ 1 := by
    intro h
    apply hz1
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  have hZ := IVK.DihedralAux.eq_r_half_of_central hkeven hk2' hZc hZ1
  have hdiv : (4 * t) / 2 = 2 * t := by omega
  rw [hdiv] at hZ
  refine ⟨((φ.symm (DihedralGroup.sr 0) : ↥P) : G), (φ.symm (DihedralGroup.sr 0)).2,
    ((φ.symm (DihedralGroup.r (t : ZMod (4 * t))) : ↥P) : G),
    (φ.symm (DihedralGroup.r (t : ZMod (4 * t)))).2, ?_, ?_, ?_, ?_⟩
  · have h1 : φ.symm (DihedralGroup.sr 0) * φ.symm (DihedralGroup.sr 0) = 1 := by
      rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
    exact congrArg Subtype.val h1
  · intro h
    have h1 : φ.symm (DihedralGroup.sr 0) = 1 := Subtype.ext h
    have := congrArg φ h1
    rw [MulEquiv.apply_symm_apply, map_one, DihedralGroup.one_def] at this
    cases this
  · intro h
    have h1 : φ.symm (DihedralGroup.sr 0) = ⟨z, hzP⟩ := Subtype.ext h
    have := congrArg φ h1
    rw [MulEquiv.apply_symm_apply, hZ] at this
    cases this
  · have h1 : φ.symm (DihedralGroup.r (t : ZMod (4 * t))) * φ.symm (DihedralGroup.sr 0) *
        (φ.symm (DihedralGroup.r (t : ZMod (4 * t))))⁻¹ =
        (⟨z, hzP⟩ : ↥P) * φ.symm (DihedralGroup.sr 0) := by
      apply φ.injective
      rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hZ, DihedralGroup.r_mul_sr, DihedralGroup.inv_r,
        DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
      congr 1
      push_cast
      ring
    exact congrArg Subtype.val h1

end Dih

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
