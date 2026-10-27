module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_zpowers_cases_of_orderOf_two {t b : G} (ht : orderOf t = 2) (hb : b ∈ zpowers t) :
    b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left; simp [h0]
  · right; simp [h0]

omit [Finite G] in
theorem exists_eq_of_mem_sup_zpowers {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) {x : G} (hx : x ∈ L ⊔ zpowers t) : (x ∈ L) ∨ ∃ l ∈ L, x = l * t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (A := L) (B := zpowers t) (zpowers_le.2 ht) hx
  rcases mem_zpowers_cases_of_orderOf_two ht2 hb with hb1 | hb1
  · left; rw [hb1, mul_one]; exact ha
  · right; exact ⟨a, ha, by rw [hb1]⟩

omit [Finite G] in
theorem isPGroup_sup_of_le_centralizer {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hAB : B ≤ centralizer (A : Set G)) : IsPGroup 2 (A ⊔ B : Subgroup G) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hx
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨a, ha⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hB) ⟨b, hb⟩
  rw [Subgroup.orderOf_mk] at hi hj
  have hcomm : Commute a b := (mem_centralizer_iff.mp (hAB hb) a ha)
  have hdvd := hcomm.orderOf_mul_dvd_lcm
  rw [hi, hj] at hdvd
  have hl : Nat.lcm (2 ^ i) (2 ^ j) = 2 ^ (max i j : ℕ) := by
    rcases le_total i j with hij | hij
    · rw [max_eq_right hij]; exact Nat.lcm_eq_right (pow_dvd_pow 2 hij)
    · rw [max_eq_left hij]; exact Nat.lcm_eq_left (pow_dvd_pow 2 hij)
  rw [hl] at hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨k, ?_⟩
  rw [Subgroup.orderOf_mk]
  exact hk'

omit [Finite G] in
theorem t_not_mem_of_center_eq_bot (hZ : center L = ⊥) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) : t ∉ L := fun htL => by
  have := eq_one_of_mem_of_mem_centralizer hZ htL ht
  rw [this, orderOf_one] at ht2
  omega

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.comm_mem_of_relIndex_dvd_two
    (h : StdHyp G L) {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hZ : center L = ⊥)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2) {a b : G}
    (ha : a * t = t * a) (hb : b * t = t * b) : ⁅a, b⁆ ∈ L := by
  have htL := t_not_mem_of_center_eq_bot hZ ht ht2
  have claim1 : ∀ m : G, m * t = t * m → ∀ n ∈ L ⊔ zpowers t, ⁅m, n⁆ ∈ L := by
    intro m hm n hn
    obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := L) (B := zpowers t) (zpowers_le.2 ht) hn
    have hmz : m * z = z * m := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      exact ((Commute.zpow_right (show Commute m t from hm) k)).eq
    have hml : m * l * m⁻¹ ∈ L :=
      (mem_normalizer_iff.1 (h.centralizer_le_normalizer ht ht2
        (mem_centralizer_singleton_iff.2 hm)) l).1 hl
    have hz' : m * z * m⁻¹ = z := by rw [hmz]; group
    rw [commutatorElement_def]
    have : m * (l * z) * m⁻¹ * (l * z)⁻¹ = (m * l * m⁻¹) * l⁻¹ := by
      calc m * (l * z) * m⁻¹ * (l * z)⁻¹ = (m * l * m⁻¹) * (m * z * m⁻¹) * z⁻¹ * l⁻¹ := by group
        _ = (m * l * m⁻¹) * z * z⁻¹ * l⁻¹ := by rw [hz']
        _ = (m * l * m⁻¹) * l⁻¹ := by group
    rw [this]
    exact L.mul_mem hml (L.inv_mem hl)
  set N : Subgroup G := L ⊔ zpowers t with hN
  by_cases haN : a ∈ N
  · have := claim1 b hb a haN
    have h2 : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := (commutatorElement_inv b a).symm
    rw [h2]
    exact L.inv_mem this
  by_cases hbN : b ∈ N
  · exact claim1 a ha b hbN
  have haM : a ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 ha
  have hbM : b ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hb
  have hidx2 : (N.subgroupOf (centralizer ({t} : Set G))).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · exfalso
      apply haN
      have h1' : N.subgroupOf (centralizer ({t} : Set G)) = ⊤ :=
        Subgroup.index_eq_one.1 (by rw [Subgroup.relIndex] at h1; exact h1)
      have : (⟨a, haM⟩ : centralizer ({t} : Set G)) ∈
          N.subgroupOf (centralizer ({t} : Set G)) := by rw [h1']; exact mem_top _
      exact this
    · rw [Subgroup.relIndex] at h2; exact h2
  have hmem : a * b⁻¹ ∈ N := by
    have hx' : (⟨a, haM⟩ : centralizer ({t} : Set G)) ∉
        N.subgroupOf (centralizer ({t} : Set G)) := haN
    have hy' : (⟨b⁻¹, (centralizer ({t} : Set G)).inv_mem hbM⟩ : centralizer ({t} : Set G)) ∉
        N.subgroupOf (centralizer ({t} : Set G)) := fun h => hbN (by simpa using N.inv_mem h)
    exact (Subgroup.mul_mem_iff_of_index_two hidx2
      (a := ⟨a, haM⟩) (b := ⟨b⁻¹, (centralizer ({t} : Set G)).inv_mem hbM⟩)).2
        (iff_of_false hx' hy')
  have h3 := claim1 b hb (a * b⁻¹) hmem
  have h4 : ⁅a, b⁆ = ⁅b, a * b⁻¹⁆⁻¹ := by
    rw [← commutatorElement_inv]
    simp only [commutatorElement_def]
    group
  rw [h4]
  exact L.inv_mem h3

@[expose] def FusionData (L : Type*) [Group L] [Finite L] : Prop :=
  (∀ β : MulAut L, (∃ R : Sylow 2 L, ∀ x ∈ (R : Subgroup L), β x = x) →
      ∃ l : L, β = MulAut.conj l) ∧
    ∀ R : Sylow 2 L, ∃ z : L, orderOf z = 2 ∧ centralizer ((R : Subgroup L) : Set L) = zpowers z ∧
      ∃ P : Subgroup L, P ≤ centralizer ({z} : Set L) ∧ ⁅P, P⁆ = P ∧ z ∈ P

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_conj_eq_mul_of_fusionData_sylow
    (h : StdHyp G L) (hZ : center L = ⊥)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    (hFD : FusionData L) (R : Sylow 2 L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    ∃ z : L, orderOf z = 2 ∧ centralizer ((R : Subgroup L) : Set L) = zpowers z ∧
      ∃ g : G, g * t * g⁻¹ = (z : G) * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := h.simple
  set M := centralizer ({t} : Set G) with hMdef
  have hidx : (L ⊔ zpowers t).relIndex M ∣ 2 :=
    (h.relIndex_sup_zpowers_dvd hS ht ht2).trans hout
  have htL : t ∉ L := t_not_mem_of_center_eq_bot hZ ht ht2
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have hMN : M ≤ normalizer (L : Set G) := h.centralizer_le_normalizer ht ht2
  have hLM : L ≤ M := fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  let ψ : M →* Abelianization M := Abelianization.of
  have hψ : ψ ⟨t, htM⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨t, htM⟩ : M) ∈ commutator M := (QuotientGroup.eq_one_iff _).mp h1
    have hle : commutator M ≤ L.subgroupOf M := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact h.comm_mem_of_relIndex_dvd_two ht ht2 hZ hidx
        (mem_centralizer_singleton_iff.1 x.2) (mem_centralizer_singleton_iff.1 y.2)
    exact htL (hle h2)
  set A : Subgroup G := (R : Subgroup L).map L.subtype with hAdef
  have hA : IsPGroup 2 A :=
    (R.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  have hB : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hAL : A ≤ L := Subgroup.map_subtype_le _
  have hBA : zpowers t ≤ centralizer (A : Set G) := fun b hb => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    rw [mem_centralizer_iff]
    intro a ha
    exact (Commute.zpow_right (show Commute a t from mem_centralizer_iff.1 ht a (hAL ha))
      k).eq
  have hP := isPGroup_sup_of_le_centralizer hA hB hBA
  have htP : t ∈ A ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hPM : A ⊔ zpowers t ≤ M := sup_le (hAL.trans hLM)
    (zpowers_le.2 htM)
  have hPt : ∀ p ∈ A ⊔ zpowers t, p * t = t * p := fun p hp =>
    mem_centralizer_singleton_iff.mp (hPM hp)
  obtain ⟨g, hgne, hgcomm⟩ := McLStd.exists_conj_ne_centralizing h.nonabelian htt hP htP hPt ψ hψ
  set t' : G := g * t * g⁻¹ with ht'def
  have ht'2 : t' * t' = 1 := by
    rw [ht'def]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have ht'M : t' ∈ M := by
    rw [mem_centralizer_singleton_iff]
    exact (hgcomm t htP).symm
  have ht'A : ∀ a ∈ A, a * t' = t' * a := fun a ha => hgcomm a (mem_sup_left ha)
  set β : MulAut L := L.normalizerMonoidHom ⟨t', hMN ht'M⟩ with hβdef
  have hβ : ∀ x : L, ((β x : L) : G) = t' * x * t'⁻¹ := fun x => rfl
  have hβR : ∀ x ∈ (R : Subgroup L), β x = x := by
    intro x hx
    apply Subtype.ext
    rw [hβ]
    have := ht'A x ⟨x, hx, rfl⟩
    calc t' * (x : G) * t'⁻¹ = (x : G) * t' * t'⁻¹ := by rw [← this]
      _ = x := by group
  obtain ⟨l, hl⟩ := hFD.1 β ⟨R, hβR⟩
  have hcC : (l : G)⁻¹ * t' ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut L => ((φ ⟨x, hx⟩ : L) : G)) hl
    have h1' : t' * x * t'⁻¹ = l * x * (l : G)⁻¹ := by
      have := h1
      simpa [hβ, MulAut.conj_apply] using this
    calc x * ((l : G)⁻¹ * t') = (l : G)⁻¹ * (l * x * (l : G)⁻¹) * t' := by group
      _ = (l : G)⁻¹ * (t' * x * t'⁻¹) * t' := by rw [h1']
      _ = (l : G)⁻¹ * t' * x := by group
  have ht'sup : t' ∈ L ⊔ zpowers t := by
    have h1 : t' ∈ M ⊓ (L ⊔ centralizer (L : Set G)) := by
      refine ⟨ht'M, ?_⟩
      have : t' = (l : G) * ((l : G)⁻¹ * t') := by group
      rw [this]
      exact mul_mem_sup l.2 hcC
    rwa [h.centralizer_inf_sup_centralizer_eq hS ht ht2] at h1
  obtain ⟨z, hz2, hCz, P, hPle, hPP, hzP⟩ := hFD.2 R
  have hcentR : ∀ a : L, (∀ x ∈ A, (x : G) * a = a * x) → a = 1 ∨ a = z := by
    intro a ha
    have : a ∈ centralizer ((R : Subgroup L) : Set L) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (ha x ⟨x, hx, rfl⟩)
    rw [hCz] at this
    exact mem_zpowers_cases_of_orderOf_two hz2 this
  have ht'1 : t' ≠ 1 := by
    intro h1
    have : t = 1 := by
      calc t = g⁻¹ * t' * g := by rw [ht'def]; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at ht2
    omega
  rcases exists_eq_of_mem_sup_zpowers ht ht2 ht'sup with hL' | ⟨a, ha, hat⟩
  ·
    exfalso
    have hcomm : ∀ x ∈ A, (x : G) * ((⟨t', hL'⟩ : L) : G) = ((⟨t', hL'⟩ : L) : G) * x :=
      fun x hx => ht'A x hx
    rcases hcentR ⟨t', hL'⟩ hcomm with h1 | h1
    · exact ht'1 (congrArg Subtype.val h1)
    · have hzt' : (z : G) = t' := (congrArg Subtype.val h1).symm
      have htz : t = g⁻¹ * z * g := by rw [hzt', ht'def]; group
      set PG : Subgroup G := P.map L.subtype with hPG
      have hPGc : ⁅PG, PG⁆ = PG := by rw [hPG, ← Subgroup.map_commutator, hPP]
      set P₀ : Subgroup G := PG.map (MulAut.conj g⁻¹).toMonoidHom with hP₀
      have hP₀c : ⁅P₀, P₀⁆ = P₀ := by rw [hP₀, ← Subgroup.map_commutator, hPGc]
      have hP₀le : P₀ ≤ centralizer ({t} : Set G) := by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
        have hpz := mem_centralizer_singleton_iff.mp (hPle hp)
        have hpz' : (p : G) * z = z * (p : G) := congrArg Subtype.val hpz
        have e : (MulAut.conj g⁻¹).toMonoidHom (L.subtype p) = g⁻¹ * (p : G) * g := by simp
        rw [e, mem_centralizer_singleton_iff, htz]
        calc g⁻¹ * (p : G) * g * (g⁻¹ * z * g) = g⁻¹ * ((p : G) * z) * g := by group
          _ = g⁻¹ * (z * (p : G)) * g := by rw [hpz']
          _ = g⁻¹ * z * g * (g⁻¹ * (p : G) * g) := by group
      have htP₀ : t ∈ P₀ := ⟨(z : G), ⟨z, hzP, rfl⟩, by simp [htz]⟩
      exact htL ((h.le_of_perfect_of_le_centralizer hout ht ht2 hP₀c hP₀le) htP₀)
  ·
    have hcomm : ∀ x ∈ A, (x : G) * ((⟨a, ha⟩ : L) : G) = ((⟨a, ha⟩ : L) : G) * x := by
      intro x hx
      have h1 := ht'A x hx
      have hxt : (x : G) * t = t * x := mem_centralizer_iff.1 ht x (hAL hx)
      rw [hat] at h1
      calc (x : G) * a = (x * (a * t)) * t⁻¹ := by group
        _ = ((a * t) * x) * t⁻¹ := by rw [h1]
        _ = a * (t * x) * t⁻¹ := by group
        _ = a * (x * t) * t⁻¹ := by rw [hxt]
        _ = a * x := by group
    rcases hcentR ⟨a, ha⟩ hcomm with h1 | h1
    · exfalso
      have : a = 1 := congrArg Subtype.val h1
      rw [this, one_mul] at hat
      exact hgne hat
    · have hza : (z : G) = a := (congrArg Subtype.val h1).symm
      exact ⟨z, hz2, hCz, g, by rw [hza]; exact hat⟩

end CFSG.EvenSporadicStandard.HSStd
