module

public import CFSG.Holt.H78.AltModelSylow

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv Equiv.Perm CFSG.Holt.H78

theorem false_of_index_three_of_isSimpleGroup {W : Type*} [Group W] [Finite W] [IsSimpleGroup W]
    (hW : 6 < Nat.card W) (K : Subgroup W) (hK : K.index = 3) : False := by
  have hfin : Finite (W ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (W ⧸ K) = 3 := by rw [← Subgroup.index, hK]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom W (W ⧸ K)).ker with h | h
  · have hinj : Function.Injective (MulAction.toPermHom W (W ⧸ K)) :=
      (MonoidHom.ker_eq_bot_iff _).1 h
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, hcard] at this
    have h6 : (3 : ℕ).factorial = 6 := by decide
    omega
  · have hK1 : K = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      have ha : a ∈ (MulAction.toPermHom W (W ⧸ K)).ker := by rw [h]; trivial
      have := (MonoidHom.mem_ker).1 ha
      have h1 : a • ((1 : W) : W ⧸ K) = ((1 : W) : W ⧸ K) := by
        have := congrArg (fun p : Equiv.Perm (W ⧸ K) => p ((1 : W) : W ⧸ K)) this
        simpa using this
      change ((a * 1 : W) : W ⧸ K) = _ at h1
      rw [mul_one, QuotientGroup.eq] at h1
      simpa using h1
    rw [hK1, Subgroup.index_top] at hK
    omega

theorem card_support_eq_five {c : Perm (Fin 6)} (hc : orderOf c = 5) : c.support.card = 5 := by
  have hne : c ≠ 1 := by rintro rfl; simp at hc
  have hmem : ∀ n ∈ c.cycleType, n = 5 := fun n hn => by
    have h1 := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rw [hc] at h1
    rcases (Nat.dvd_prime Nat.prime_five).1 h1 with h | h <;> omega
  have hsum := Equiv.Perm.sum_cycleType c
  have hle := Equiv.Perm.sum_cycleType_le c
  have hrep := Multiset.eq_replicate_card.2 hmem
  have hpos : 0 < Multiset.card c.cycleType := by
    rw [Multiset.card_pos]
    exact fun h => hne (Equiv.Perm.cycleType_eq_zero.1 h)
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hle
  simp only [Fintype.card_fin] at hle
  have : Multiset.card c.cycleType = 1 := by omega
  rw [← hsum, this]

theorem exists_le_stabilizer_of_card (K : Subgroup (Perm (Fin 6))) (h20 : 20 ∣ Nat.card K)
    (h40 : Nat.card K ∣ 40) : ∃ f : Fin 6, K ≤ MulAction.stabilizer (Perm (Fin 6)) f := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card K := dvd_trans (by norm_num) h20
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5
  have hS : IsPGroup 5 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc]; simp)
  obtain ⟨P, hPS⟩ := hS.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup K) = 5 := by
    have h1 := P.card_eq_multiplicity
    have h2 : Nat.card (P : Subgroup K) ∣ 40 :=
      (Subgroup.card_subgroup_dvd_card _).trans h40
    have h3 : 5 ∣ Nat.card (P : Subgroup K) := by
      have := Subgroup.card_dvd_of_le hPS
      rwa [Nat.card_zpowers, hc] at this
    set e := (Nat.card K).factorization 5
    rcases Nat.lt_or_ge e 2 with he | he
    · interval_cases e
      · rw [pow_zero] at h1; omega
      · simpa using h1
    · exfalso
      have : 25 ∣ 40 := by
        refine dvd_trans ?_ (h1 ▸ h2)
        rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
        exact pow_dvd_pow 5 he
      omega
  have hPeq : (P : Subgroup K) = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge hPS ?_).symm
    rw [hPcard, Nat.card_zpowers, hc]
  have hn : Nat.card (Sylow 5 K) = 1 := by
    have hmod := card_sylow_modEq_one 5 K
    have hdvd := P.card_dvd_index
    have hidx := Subgroup.card_mul_index (P : Subgroup K)
    rw [hPcard] at hidx
    set i := (P : Subgroup K).index
    set n := Nat.card (Sylow 5 K)
    have hi : i ≤ 8 := by
      have : 5 * i ∣ 40 := hidx ▸ h40
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hipos : 0 < i := by omega
    have hn' : n ≤ 8 := (Nat.le_of_dvd hipos hdvd).trans hi
    have hmod' : n % 5 = 1 := hmod
    have hn0 : 0 < n := Nat.card_pos
    have h20' : 20 ∣ 5 * i := hidx ▸ h20
    interval_cases n <;> omega
  have : Subsingleton (Sylow 5 K) := by
    exact (Nat.card_eq_one_iff_unique.1 hn).1
  have : (P : Subgroup K).Normal := Sylow.normal_of_subsingleton P
  set σ : Perm (Fin 6) := (c : Perm (Fin 6)) with hσ
  have hσ5 : orderOf σ = 5 := by rw [hσ, Subgroup.orderOf_coe, hc]
  have hsupp := card_support_eq_five hσ5
  have hcompl : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hsupp]; simp
  obtain ⟨f, hf⟩ := Finset.card_eq_one.1 hcompl
  refine ⟨f, fun g hg => ?_⟩
  have hgc : (⟨g, hg⟩ : K) * c * (⟨g, hg⟩ : K)⁻¹ ∈ Subgroup.zpowers c := by
    rw [← hPeq]
    exact Subgroup.Normal.conj_mem inferInstance c (hPeq ▸ Subgroup.mem_zpowers c) _
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hgc
  obtain ⟨m, hm, hgm⟩ := hgc
  rw [hc, Finset.mem_range] at hm
  have hgm' : g * σ * g⁻¹ = σ ^ m := by
    have := congrArg (fun x : K => (x : Perm (Fin 6))) hgm
    simpa [hσ] using this.symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : σ = 1 := by
      simpa [mul_inv_eq_one] using hgm'
    rw [this] at hσ5; simp at hσ5
  have hcop : Nat.Coprime m (orderOf σ) := by
    rw [hσ5]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (by intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))))
  have hsm : (g * σ * g⁻¹).support = σ.support := by
    rw [hgm']; exact Equiv.Perm.support_pow_coprime hcop
  rw [Equiv.Perm.support_conj] at hsm
  have hiff : ∀ x, g x ∈ σ.support ↔ x ∈ σ.support := fun x => by
    have := Finset.mem_map' (s := σ.support) g.toEmbedding (a := x)
    rwa [hsm] at this
  have hfn : f ∉ σ.support := by
    have : f ∈ σ.supportᶜ := by rw [hf]; simp
    simpa using this
  have : g f ∈ σ.supportᶜ := by
    simpa [hiff] using hfn
  rw [hf, Finset.mem_singleton] at this
  simpa [MulAction.mem_stabilizer_iff] using this

theorem card_alternatingGroup_inf_stabilizer_six (f : Fin 6) :
    Nat.card (alternatingGroup (Fin 6) ⊓ MulAction.stabilizer (Perm (Fin 6)) f :
      Subgroup (Perm (Fin 6))) = 60 := by
  rw [← Nat.card_congr (alternatingGroupStabilizerEquiv f).toEquiv]
  have h5 : Nat.card {x : Fin 6 // x ≠ f} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  have : Nontrivial {x : Fin 6 // x ≠ f} :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [h5]; norm_num)
  have h := two_mul_nat_card_alternatingGroup (α := {x : Fin 6 // x ≠ f})
  rw [Nat.card_perm, h5] at h
  have : (5 : ℕ).factorial = 120 := by decide
  omega

theorem card_le_of_not_three_dvd_alt_six (H : Subgroup (alternatingGroup (Fin 6)))
    (h : ¬ 3 ∣ Nat.card H) : Nat.card H ≤ 10 := by
  by_contra hlt
  rw [not_le] at hlt
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at this
    have h6 : (6 : ℕ).factorial = 720 := by decide
    omega
  have hd360 : Nat.card H ∣ 40 * 9 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [hA] at this
  have hcop : Nat.Coprime (Nat.card H) 9 := by
    have : Nat.Coprime (Nat.card H) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
    simpa using Nat.Coprime.pow_right 2 this
  have hd40 : Nat.card H ∣ 40 := hcop.dvd_of_dvd_mul_right hd360
  have h20 : 20 ∣ Nat.card H := by
    have hle := Nat.le_of_dvd (by norm_num) hd40
    generalize Nat.card H = n at *
    interval_cases n <;> omega
  set K : Subgroup (Perm (Fin 6)) := H.map (alternatingGroup (Fin 6)).subtype with hKdef
  have hK : Nat.card K = Nat.card H :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective
  obtain ⟨f, hf⟩ := exists_le_stabilizer_of_card K (hK ▸ h20) (hK ▸ hd40)
  have hKW : K ≤ alternatingGroup (Fin 6) ⊓ MulAction.stabilizer (Perm (Fin 6)) f :=
    le_inf (Subgroup.map_subtype_le H) hf
  set W := (alternatingGroup (Fin 6) ⊓ MulAction.stabilizer (Perm (Fin 6)) f :
    Subgroup (Perm (Fin 6))) with hWdef
  have hW : Nat.card W = 60 := card_alternatingGroup_inf_stabilizer_six f
  have hsimple : IsSimpleGroup W :=
    isSimpleGroup_alternatingGroup_inf_stabilizer (by simp) f
  have hK' : Nat.card (K.subgroupOf W) = Nat.card H := by
    rw [← hK]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv
  have hmul := Subgroup.card_mul_index (K.subgroupOf W)
  rw [hK', hW] at hmul
  have hd60 : Nat.card H ∣ 60 := ⟨_, hmul.symm⟩
  have h20' : Nat.card H = 20 := by
    have hle := Nat.le_of_dvd (by norm_num) hd60
    have hle40 := Nat.le_of_dvd (by norm_num) hd40
    generalize Nat.card H = n at *
    interval_cases n <;> omega
  rw [h20'] at hmul
  exact false_of_index_three_of_isSimpleGroup (W := W) (by omega) (K.subgroupOf W) (by omega)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
