module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenAbs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Components

variable {X : Type} [Group X]

theorem component_eq_of_layer [Finite X] {K K' J : Subgroup X} (hK : CFSG.IsComponent K)
    (hK' : CFSG.IsComponent K') (hJ : CFSG.IsComponent J) (hlayer : CFSG.layer X = K ⊔ K') :
    J = K ∨ J = K' := by
  by_contra hcon
  have hcon' := not_or.1 hcon
  have h1 := CFSG.LocalCores.distinct_components_commute hJ hK
  have h2 := CFSG.LocalCores.distinct_components_commute hJ hK'
  have h1' : ⁅J, K⁆ = ⊥ := h1.resolve_left hcon'.1
  have h2' : ⁅J, K'⁆ = ⊥ := h2.resolve_left hcon'.2
  have hKc : K ≤ centralizer (J : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h1'
  have hK'c : K' ≤ centralizer (J : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h2'
  have hJle : J ≤ K ⊔ K' := by
    rw [← hlayer]
    exact le_sSup hJ
  have hJc : J ≤ centralizer (J : Set X) := hJle.trans (sup_le hKc hK'c)
  have hJbot : ⁅J, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJc
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 hJ.1.1
  have hJ0 : J = ⊥ := by rw [← hperf]; exact hJbot
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥J)
  apply hx
  apply Subtype.ext
  have : (x : X) ∈ (⊥ : Subgroup X) := by rw [← hJ0]; exact x.2
  exact this

theorem commute_of_centralizes_layer [Finite X] {t : X} {A K K' : Subgroup X} {m : ℕ}
    (h : ExactShape t A m) (hnormal : (K ⊔ K').Normal) (hA : A ≤ K ⊔ K')
    (ht : ¬ ∀ x ∈ K ⊔ K', t * x = x * t) :
    ∀ a b : X, (∀ k ∈ K, a * k = k * a) → (∀ k ∈ K', a * k = k * a) →
      (∀ k ∈ K, b * k = k * b) → (∀ k ∈ K', b * k = k * b) → a * b = b * a := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order, pow_two] at this
  set V : Subgroup X := centralizer ((K ⊔ K' : Subgroup X) : Set X) with hV
  have hVmem : ∀ v, v ∈ V ↔ ∀ x ∈ K ⊔ K', x * v = v * x := fun v => mem_centralizer_iff
  have : V.Normal := ⟨fun v hv g x hx => by
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ K ⊔ K' := hnormal.conj_mem x hx g⁻¹
    rw [inv_inv] at hx'
    have h1 := (hVmem v).1 hv _ hx'
    calc x * (g * v * g⁻¹) = g * ((g⁻¹ * x * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = (g * v * g⁻¹) * x := by group⟩
  have hmemV : ∀ a : X, (∀ k ∈ K, a * k = k * a) → (∀ k ∈ K', a * k = k * a) → a ∈ V := by
    intro a h1 h2
    have hle : K ⊔ K' ≤ centralizer ({a} : Set X) := sup_le
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (h1 k hk).symm)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (h2 k hk).symm)
    rw [hVmem]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hfpf : ∀ v ∈ V, t * v * t⁻¹ = v → v = 1 := by
    intro v hv htv
    have hvA : v ∈ centralizer (A : Set X) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact (hVmem v).1 hv a (hA ha)
    have hvt : v ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc v * t = (t * v * t⁻¹) * t := by rw [htv]
        _ = t * v := by group
    have hvz : v ∈ zpowers t := by
      rw [← h.cent_cent]
      exact ⟨hvA, hvt⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hvz
    rw [← hj] at hv ⊢
    have hmod : t ^ j = t ^ (j % 2) := by
      simpa [h.order] using (zpow_mod_orderOf t j).symm
    have hj2 : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hj2 with hj2 | hj2
    · rw [hmod, hj2]; simp
    · exfalso
      rw [hmod, hj2, zpow_one] at hv
      exact ht (fun x hx => ((hVmem t).1 hv x hx).symm)
  intro a b ha1 ha2 hb1 hb2
  exact (fpf_inverts_abelian (V := V) ht2 hfpf).2 a (hmemV a ha1 ha2) b (hmemV b hb1 hb2)

end Components

section Absorb

variable {N : Type} [Group N] {O : Subgroup N} [O.Normal]

theorem inf_odd_eq_bot_of_alt (hOodd : Odd (Nat.card O)) {P : Subgroup N} {k : ℕ} (hk : 5 ≤ k)
    (eP : ↥P ≃* alternatingGroup (Fin k)) : P ⊓ O = ⊥ := by
  have hsimple : IsSimpleGroup ↥P := isSimpleGroup_of_alt hk eP
  rcases hsimple.eq_bot_or_eq_top_of_normal (O.subgroupOf P) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥P) ∈ O.subgroupOf P := hx.2
    rw [h] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 this))
  · exfalso
    obtain ⟨t, -, -, -, ht2, -⟩ := exists_two_involutions_of_alt (by omega) eP
    have htO : (t : N) ∈ O := by
      have : t ∈ O.subgroupOf P := by rw [h]; exact Subgroup.mem_top t
      exact this
    have h1 : orderOf (t : N) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O htO
    rw [Subgroup.orderOf_coe, ht2] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)

theorem le_of_map_le (hOodd : Odd (Nat.card O)) {Q P : Subgroup N} {k : ℕ} (hk : 5 ≤ k)
    (eP : ↥P ≃* alternatingGroup (Fin k)) (hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q)
    (hQbot : Q ⊓ O = ⊥)
    (hPQ : P.map (QuotientGroup.mk' O) ≤ Q.map (QuotientGroup.mk' O)) : P ≤ Q := by
  have hsimple : IsSimpleGroup ↥P := isSimpleGroup_of_alt hk eP
  have hdec : ∀ x ∈ P, ∃ q ∈ Q, ∃ o ∈ O, x = q * o := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hPQ ⟨x, hx, rfl⟩
    refine ⟨q, hq, q⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' O) (q⁻¹ * x) = 1
    rw [map_mul, map_inv]
    have : (QuotientGroup.mk' O) q = (QuotientGroup.mk' O) x := hqx
    rw [this]; group
  have hnorm : (Q.subgroupOf P).Normal := ⟨fun y hy g => by
    obtain ⟨q, hq, o, ho, hgo⟩ := hdec (g : N) g.2
    have hyQ : (y : N) ∈ Q := hy
    show ((g * y * g⁻¹ : ↥P) : N) ∈ Q
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hgo]
    have h1 : o * (y : N) = (y : N) * o := (hQO _ hyQ o ho).symm
    have h2 : q * o * (y : N) * (q * o)⁻¹ = q * (y : N) * q⁻¹ := by
      calc q * o * (y : N) * (q * o)⁻¹ = q * (o * (y : N)) * o⁻¹ * q⁻¹ := by group
        _ = q * ((y : N) * o) * o⁻¹ * q⁻¹ := by rw [h1]
        _ = q * (y : N) * q⁻¹ := by group
    rw [h2]
    exact Q.mul_mem (Q.mul_mem hq hyQ) (Q.inv_mem hq)⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal (Q.subgroupOf P) with h | h
  · exfalso
    obtain ⟨t, -, -, -, ht2, -⟩ := exists_two_involutions_of_alt (by omega) eP
    have htsq : (t : N) * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht2, pow_two] at this
      exact congrArg Subtype.val this
    have htne : (t : N) ≠ 1 := by
      intro h1
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht2
      omega
    obtain ⟨q, hq, o, ho, hto⟩ := hdec (t : N) t.2
    have hcomm : q * o = o * q := hQO q hq o ho
    have h1 : q * q * (o * o) = 1 := by
      calc q * q * (o * o) = (q * o) * (q * o) := by
            calc q * q * (o * o) = q * (q * o) * o := by group
              _ = q * (o * q) * o := by rw [hcomm]
              _ = (q * o) * (q * o) := by group
        _ = 1 := by rw [← hto]; exact htsq
    have h2 : q * q ∈ Q ⊓ O := by
      refine ⟨Q.mul_mem hq hq, ?_⟩
      have : q * q = (o * o)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact O.inv_mem (O.mul_mem ho ho)
    rw [hQbot] at h2
    have hq2 : q * q = 1 := h2
    have ho2 : o * o = 1 := by simpa [hq2] using h1
    have hoo : o = 1 := by
      have h3 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
      have h4 : orderOf o ∣ Nat.card O := by
        have := Subgroup.orderOf_dvd_natCard O ho
        simpa using this
      have h5 : orderOf o = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h6 | h6
        · exact h6
        · rw [h6] at h4
          exact absurd (even_iff_two_dvd.2 h4) (Nat.not_even_iff_odd.2 hOodd)
      exact orderOf_eq_one_iff.1 h5
    have htq : (t : N) ∈ Q := by rw [hto, hoo, mul_one]; exact hq
    have : t ∈ Q.subgroupOf P := htq
    rw [h] at this
    exact htne (congrArg Subtype.val (Subgroup.mem_bot.1 this))
  · intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ Q.subgroupOf P := by rw [h]; exact Subgroup.mem_top _
    exact this

variable [Finite N]

theorem absorb_abstract (hOodd : Odd (Nat.card O)) {z : N} (hz : z * z = 1)
    {K A' : Subgroup (N ⧸ O)} {m : ℕ} (hKc : CFSG.IsComponent K)
    (hKne : K.map (MulAut.conj (z : N ⧸ O)).toMonoidHom ≠ K)
    (hlayer : CFSG.layer (N ⧸ O) = K ⊔ K.map (MulAut.conj (z : N ⧸ O)).toMonoidHom)
    (hA' : A' ≤ K ⊔ K.map (MulAut.conj (z : N ⧸ O)).toMonoidHom)
    (hex : ExactShape (z : N ⧸ O) A' m) (eK : ↥K ≃* alternatingGroup (Fin m)) (hm6 : m ≠ 6)
    {Q : Subgroup N} (hQmap : Q.map (QuotientGroup.mk' O) = K)
    (hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q) (hQbot : Q ⊓ O = ⊥) {k : ℕ} (hk6 : 5 ≤ k)
    (hkm : k ≤ m) (hmk : m ≤ k + 3) {P : Subgroup N} (eP : ↥P ≃* alternatingGroup (Fin k))
    (hPP : ∀ a ∈ P, ∀ b ∈ P, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) :
    P ≤ Q ∨ P ≤ Q.map (MulAut.conj z).toMonoidHom := by
  set π : N →* N ⧸ O := QuotientGroup.mk' O with hπ
  set zb : N ⧸ O := (z : N ⧸ O) with hzb
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul, hz]; rfl
  have hzbi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hzb2
  have hπz : π z = zb := rfl
  set K' : Subgroup (N ⧸ O) := K.map (MulAut.conj zb).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj zb) hKc
  have hne : K ≠ K' := fun h => hKne h.symm
  have hPO : P ⊓ O = ⊥ := inf_odd_eq_bot_of_alt hOodd (by omega) eP
  have hinj : Function.Injective (π.comp P.subtype) := by
    intro a b hab
    have h1 : π (a : N) = π (b : N) := hab
    have h2 : (a : N)⁻¹ * (b : N) ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      show π ((a : N)⁻¹ * (b : N)) = 1
      rw [map_mul, map_inv, h1]; group
    have h3 : (a : N)⁻¹ * (b : N) ∈ P ⊓ O := ⟨P.mul_mem (P.inv_mem a.2) b.2, h2⟩
    rw [hPO] at h3
    have h4 : (a : N)⁻¹ * (b : N) = 1 := h3
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hrange : (π.comp P.subtype).range = P.map π := by
    ext x
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  let eP' : ↥(P.map π) ≃* alternatingGroup (Fin k) :=
    (MulEquiv.subgroupCongr hrange.symm).trans ((MonoidHom.ofInjective hinj).symm.trans eP)
  have hperf : ⁅P.map π, P.map π⁆ = P.map π :=
    Subgroup.isPerfect_iff.1 ⟨(isQuasisimple_of_alt (by omega) eP').1⟩
  have hcK : ∀ p : N ⧸ O, K.map (MulAut.conj p).toMonoidHom = K ∨
      K.map (MulAut.conj p).toMonoidHom = K' := fun p =>
    component_eq_of_layer hKc hK'c (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj p) hKc)
      hlayer
  have hcK' : ∀ p : N ⧸ O, K'.map (MulAut.conj p).toMonoidHom = K ∨
      K'.map (MulAut.conj p).toMonoidHom = K' := fun p =>
    component_eq_of_layer hKc hK'c (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj p) hK'c)
      hlayer
  have hNK : ∀ p ∈ P.map π, ∀ x ∈ K, p * x * p⁻¹ ∈ K :=
    perfect_normalizes_of_two hne hperf (fun p _ => hcK p) (fun p _ => hcK' p)
  have hNK' : ∀ p ∈ P.map π, ∀ x ∈ K', p * x * p⁻¹ ∈ K' :=
    perfect_normalizes_of_two hne.symm hperf (fun p _ => (hcK' p).symm) (fun p _ => (hcK p).symm)
  have hKz : ∀ x ∈ K, zb * x * zb⁻¹ ∈ K' := fun x hx => ⟨x, hx, by simp⟩
  have hK'z : ∀ x ∈ K', zb * x * zb⁻¹ ∈ K := by
    rintro _ ⟨y, hy, rfl⟩
    have : zb * (zb * y * zb⁻¹) * zb⁻¹ = (zb * zb) * y * (zb * zb)⁻¹ := by group
    show zb * (zb * y * zb⁻¹) * zb⁻¹ ∈ K
    rw [this, hzb2]; simpa using hy
  have hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h1 | h1
    · exact absurd h1 hne
    · intro a ha b hb
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ ⁅K, K'⁆ := by
        have := Subgroup.commutator_mem_commutator ha hb
        simpa [commutatorElement_def] using this
      rw [h1] at h2
      have h3 : a * b * a⁻¹ * b⁻¹ = 1 := h2
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h3, one_mul]
  have hnormal : (K ⊔ K').Normal := by
    have : (CFSG.layer (N ⧸ O)).Characteristic := CFSG.LocalCores.layer_characteristic
    have h2 : (CFSG.layer (N ⧸ O)).Normal := inferInstance
    rw [hlayer] at h2
    exact h2
  have hnc : ¬ ∀ x ∈ K ⊔ K', zb * x = x * zb := by
    intro hcen
    apply hKne
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hcen x ((le_sup_left : K ≤ K ⊔ K') hx)
      show zb * x * zb⁻¹ ∈ K
      have h2 : zb * x * zb⁻¹ = x := by rw [this]; group
      rw [h2]; exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      have := hcen y ((le_sup_left : K ≤ K ⊔ K') hy)
      show zb * y * zb⁻¹ = y
      rw [this]; group
  have hZ := commute_of_centralizes_layer hex hnormal hA' hnc
  let eK' : ↥K' ≃* alternatingGroup (Fin m) :=
    (K.equivMapOfInjective (MulAut.conj zb).toMonoidHom (MulAut.conj zb).injective).symm.trans eK
  have hPPb : ∀ a ∈ P.map π, ∀ b ∈ P.map π, a * (zb * b * zb⁻¹) = (zb * b * zb⁻¹) * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := congrArg π (hPP a ha b hb)
    simpa [map_mul, map_inv, hπz] using this
  have hsplit := perfect_le_or_le hm6 hk6 hkm hmk eK eK' eP' hzb2 hKz hK'z hKK' hZ hNK hNK' hPPb
  rcases hsplit with h | h
  · left
    exact le_of_map_le hOodd (by omega) eP hQO hQbot (by rw [hQmap]; exact h)
  · right
    have hQ'map : (Q.map (MulAut.conj z).toMonoidHom).map π = K' := by
      rw [hK', ← hQmap, Subgroup.map_map, Subgroup.map_map]
      congr 1
    refine le_of_map_le hOodd (by omega) eP ?_ ?_ (by rw [hQ'map]; exact h)
    · rintro _ ⟨q, hq, rfl⟩ u hu
      have hu' : z⁻¹ * u * z ∈ O := by
        have := (inferInstance : O.Normal).conj_mem u hu z⁻¹
        simpa using this
      have h1 := hQO q hq _ hu'
      show z * q * z⁻¹ * u = u * (z * q * z⁻¹)
      calc z * q * z⁻¹ * u = z * (q * (z⁻¹ * u * z)) * z⁻¹ := by group
        _ = z * ((z⁻¹ * u * z) * q) * z⁻¹ := by rw [h1]
        _ = u * (z * q * z⁻¹) := by group
    · rw [eq_bot_iff]
      rintro x ⟨⟨q, hq, rfl⟩, hxO⟩
      have hqO : q ∈ O := by
        have := (inferInstance : O.Normal).conj_mem _ hxO z⁻¹
        simpa [MulAut.conj_apply, mul_assoc] using this
      have : q ∈ Q ⊓ O := ⟨hq, hqO⟩
      rw [hQbot] at this
      have hq1 : q = 1 := this
      simp [hq1]

end Absorb

end CFSG.OddStandard.AltStdSec
