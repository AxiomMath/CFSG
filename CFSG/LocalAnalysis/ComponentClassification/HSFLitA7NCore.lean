module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NSyl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

private theorem odd_card_oddCore'' (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

namespace Inst

variable (I : S.Inst)

theorem oddCoreIn_le_centralizerE :
    oddCoreIn (normalizer (I.E : Set X)) ≤ centralizer (I.E : Set X) := by
  set N := normalizer (I.E : Set X)
  rintro _ ⟨o, ho, rfl⟩
  rw [mem_centralizer_iff]
  intro e he
  have heN : e ∈ N := Subgroup.le_normalizer he
  set e' : N := ⟨e, heN⟩ with he'
  set c : N := o * e' * o⁻¹ * e'⁻¹ with hc
  have hcO : c ∈ CFSG.oddCore N := by
    have h1 : e' * o⁻¹ * e'⁻¹ ∈ CFSG.oddCore N :=
      (CFSG.oddCore_normal N).conj_mem _ (inv_mem ho) e'
    have := mul_mem ho h1
    rwa [show o * (e' * o⁻¹ * e'⁻¹) = c by rw [hc]; group] at this
  have hcX : (c : X) = (o : X) * e * (o : X)⁻¹ * e⁻¹ := by rw [hc]; rfl
  have hcE : (c : X) ∈ I.E := by
    have h1 : (o : X) * e * (o : X)⁻¹ ∈ I.E := (mem_normalizer_iff.mp o.2 e).mp he
    rw [hcX]; exact mul_mem h1 (inv_mem he)
  have hc2 : c ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact I.sq_eq_one hcE)
  have hodd : Odd (orderOf c) := by
    have h1 := orderOf_dvd_natCard (⟨c, hcO⟩ : CFSG.oddCore N)
    rw [Subgroup.orderOf_mk] at h1
    exact (odd_card_oddCore'' N).of_dvd_nat h1
  have h1 : orderOf c = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hc2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hc1 : (c : X) = 1 := by rw [orderOf_eq_one_iff.mp h1]; rfl
  rw [hcX] at hc1
  have := mul_inv_eq_one.mp hc1
  calc e * (o : X) = (o : X) * e * (o : X)⁻¹ * (o : X) := by rw [this]
    _ = (o : X) * e := by group

omit [Finite X] in
theorem exists_pow_mem_oddCoreIn' {N : Subgroup X} {κ : X} (hκ : κ ∈ oddTwoCoreIn N) :
    ∃ a : ℕ, κ ^ (2 ^ a) ∈ oddCoreIn N := by
  obtain ⟨n, hn, rfl⟩ := hκ
  have hn' : QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N) := hn
  have hp : IsPGroup 2 (CFSG.pCore 2 (N ⧸ CFSG.oddCore N)) := CFSG.pCore_isPGroup
  obtain ⟨a, ha⟩ := hp ⟨_, hn'⟩
  refine ⟨a, ⟨n ^ (2 ^ a), ?_, by simp⟩⟩
  show n ^ (2 ^ a) ∈ CFSG.oddCore N
  rw [← QuotientGroup.eq_one_iff]
  have := congrArg Subtype.val ha
  simpa using this

omit [Finite X] in
theorem conj_mem_oddTwoCoreIn' {N : Subgroup X} {m κ : X} (hm : m ∈ N)
    (hκ : κ ∈ oddTwoCoreIn N) : m * κ * m⁻¹ ∈ oddTwoCoreIn N := by
  obtain ⟨n, hn, rfl⟩ := hκ
  have hn' : QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N) := hn
  refine ⟨⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹, ?_, by simp⟩
  show QuotientGroup.mk' (CFSG.oddCore N) (⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹) ∈
    CFSG.pCore 2 (N ⧸ CFSG.oddCore N)
  rw [map_mul, map_mul, map_inv]
  exact (CFSG.pCore_normal (p := 2) (G := N ⧸ CFSG.oddCore N)).conj_mem _ hn' _

theorem conj_mem_centralizerE {n c : X} (hn : n ∈ normalizer (I.E : Set X))
    (hc : c ∈ centralizer (I.E : Set X)) : n * c * n⁻¹ ∈ centralizer (I.E : Set X) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro e he
  have he' : n⁻¹ * e * n ∈ I.E := by
    have := (mem_normalizer_iff.mp (inv_mem hn) e).mp he
    simpa using this
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n)) * n⁻¹ := by rw [hc _ he']
    _ = n * c * n⁻¹ * e := by group

theorem exists_complement : ∃ K : Subgroup X, K ≤ centralizer (I.E : Set X) ∧
    K ≤ oddCoreIn (normalizer (I.E : Set X)) ∧
    ∀ c ∈ centralizer (I.E : Set X), ∃ e ∈ I.E, ∃ k ∈ K, c = e * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (I.E : Set X) with hC
  set N := normalizer (I.E : Set X) with hN
  have hEC := I.E_le_centralizer
  have hcardE : Nat.card (I.E.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B, I.factorization_centralizer]
    rfl
  set P : Sylow 2 C := Sylow.ofCard _ hcardE with hP
  have hPeq : (P : Subgroup C) = I.E.subgroupOf C := Sylow.coe_ofCard _ _
  have hPc : normalizer ((P : Subgroup C) : Set C) ≤ centralizer ((P : Subgroup C) : Set C) := by
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, hPeq, mem_subgroupOf] at hh
    apply Subtype.ext
    exact ((mem_centralizer_iff.mp g.2) _ hh)
  obtain ⟨K, hKn, hKp, -, -, -, hcomp, -, hKP, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPc
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact hKp
  have hdec : ∀ c : C, ∃ e ∈ I.E, ∃ k ∈ K, (c : X) = e * k := by
    intro c
    obtain ⟨⟨k, p⟩, hkp⟩ := hcomp.2 c
    have hp : ((p : C) : X) ∈ I.E := by
      have h1 : (p : C) ∈ (P : Subgroup C) := p.2
      have h2 : (p : C) ∈ I.E.subgroupOf C := by rw [← hPeq]; exact h1
      exact h2
    refine ⟨((p : C) : X), hp, (k : C), k.2, ?_⟩
    have h1 : (c : X) = ((k : C) : X) * ((p : C) : X) := by
      rw [← hkp]; rfl
    rw [h1]
    exact ((mem_centralizer_iff.mp (k : C).2) _ hp).symm
  have hKodd' : ∀ c : C, Odd (orderOf c) → c ∈ K := by
    intro c hc
    obtain ⟨e, he, k', hk', hck⟩ := hdec c
    set m := orderOf c
    have hcm : c ^ m = 1 := pow_orderOf_eq_one c
    have hek : e * (k' : X) = (k' : X) * e := (mem_centralizer_iff.mp k'.2) _ he
    have hpow : (c : X) ^ m = e ^ m * (k' : X) ^ m := by
      rw [hck]; exact (Commute.mul_pow hek m)
    have hem : e ^ m = 1 := by
      have h1 : e ^ m = ((k' : X) ^ m)⁻¹ := by
        have : (c : X) ^ m = 1 := by rw [← Subgroup.coe_pow, hcm]; rfl
        rw [hpow] at this
        exact eq_inv_of_mul_eq_one_left this
      have hgX : (((k' ^ m)⁻¹ : C) : X) = e ^ m := by
        rw [h1]; simp
      have hmemK : ((k' ^ m)⁻¹ : C) ∈ K ⊓ (P : Subgroup C) := by
        refine mem_inf.mpr ⟨inv_mem (pow_mem hk' m), ?_⟩
        show _ ∈ (P : Subgroup C)
        rw [hPeq, mem_subgroupOf, hgX]
        exact pow_mem he m
      rw [hKP, mem_bot] at hmemK
      rw [← hgX, hmemK]
      rfl
    have he1 : e = 1 := by
      have h2 : e ^ 2 = 1 := I.sq_eq_one he
      obtain ⟨j, hj⟩ := hc
      rw [hj, pow_succ, pow_mul, h2, one_pow, one_mul] at hem
      exact hem
    have : c = k' := Subtype.ext (by rw [hck, he1, one_mul])
    rw [this]
    exact hk'
  refine ⟨K.map C.subtype, map_subtype_le _, ?_, ?_⟩
  · have hCN : C ≤ N := I.centralizer_le_normalizer
    set K' : Subgroup N := (K.map C.subtype).subgroupOf N with hK'
    have hK'card : Nat.card K' = Nat.card K := by
      rw [hK', Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le K).trans hCN)).toEquiv,
        card_map_of_injective (subtype_injective _)]
    have hK'n : K'.Normal := by
      refine ⟨fun a ha n => ?_⟩
      rw [hK', mem_subgroupOf] at ha ⊢
      obtain ⟨k, hk, hka⟩ := ha
      have hcC : (n : X) * (a : X) * (n : X)⁻¹ ∈ C := by
        rw [← hka]
        exact I.conj_mem_centralizerE n.2 k.2
      refine ⟨⟨_, hcC⟩, hKodd' _ ?_, rfl⟩
      have hord : orderOf (⟨_, hcC⟩ : C) = orderOf k := by
        rw [Subgroup.orderOf_mk, ← hka]
        simp only [Subgroup.coe_subtype]
        rw [show (n : X) * (k : X) * (n : X)⁻¹ = (MulAut.conj (n : X)).toMonoidHom (k : X) from rfl,
          orderOf_injective _ (MulAut.conj (n : X)).injective, Subgroup.orderOf_coe]
      rw [hord]
      have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
      rw [Subgroup.orderOf_mk] at this
      exact hKodd.of_dvd_nat this
    have hle : K' ≤ CFSG.oddCore N := le_sSup ⟨hK'n, hK'card ▸ hKodd⟩
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨(k : X), hCN k.2⟩, hle ?_, rfl⟩
    rw [hK', mem_subgroupOf]
    exact ⟨k, hk, rfl⟩
  · intro c hc
    obtain ⟨e, he, k, hk, h⟩ := hdec ⟨c, hc⟩
    exact ⟨e, he, (k : X), ⟨k, hk, rfl⟩, h⟩

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
