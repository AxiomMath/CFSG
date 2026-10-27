module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Bur

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.S16A

open Subgroup CFSG.Open

theorem subgroupOf_zpowers_eq {Γ : Type*} [Group Γ] {K : Subgroup Γ} {g : Γ} (hg : g ∈ K) :
    (zpowers g).subgroupOf K = zpowers (⟨g, hg⟩ : K) := by
  ext x
  rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩

theorem oddCore_sup_eq_top_of_cyclic {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    (hVc : ∀ v ∈ V, ∀ k : H, v * k = k * v) (hV2 : IsPGroup 2 V) (Q : Sylow 2 H) {g : H}
    (hQ : (Q : Subgroup H) = zpowers g ⊔ V) :
    standardComponentOddCore H ⊔ (Q : Subgroup H) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVn : V.Normal :=
    ⟨fun v hv k => by rw [← hVc v hv k, mul_assoc, mul_inv_cancel, mul_one]; exact hv⟩
  have hVQ : V ≤ (Q : Subgroup H) := by rw [hQ]; exact le_sup_right
  let π : H →* H ⧸ V := QuotientGroup.mk' V
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective V
  have hker : ∀ c : H, π c = 1 ↔ c ∈ V := fun c => QuotientGroup.eq_one_iff c
  let S₁ : Sylow 2 (H ⧸ V) := Q.mapSurjective hπs
  have hS₁ : (S₁ : Subgroup (H ⧸ V)) = (Q : Subgroup H).map π := rfl
  have hcyc : IsCyclic S₁ := by
    have hle : (S₁ : Subgroup (H ⧸ V)) ≤ zpowers (π g) := by
      rw [hS₁, Subgroup.map_le_iff_le_comap, hQ]
      refine sup_le (zpowers_le.2 (Subgroup.mem_comap.2 (mem_zpowers _))) fun v hv => ?_
      rw [Subgroup.mem_comap, (hker v).2 hv]
      exact one_mem _
    exact Subgroup.isCyclic_of_le hle
  obtain ⟨-, hmul, -, -, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S₁ hcyc
  have hOc : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 (H ⧸ V))) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := H ⧸ V)
  let K₂ : Subgroup H := (CFSG.pPrimeCore 2 (H ⧸ V)).comap π
  have hK₂n : K₂.Normal := Subgroup.Normal.comap inferInstance π
  have hK₂V : ∀ c ∈ K₂, ∀ a : ℕ, c ^ 2 ^ a = 1 → c ∈ V := by
    intro c hc a hca
    have h1 : orderOf (π c) ∣ 2 ^ a :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hca, map_one])
    have h2 : orderOf (π c) ∣ Nat.card (CFSG.pPrimeCore 2 (H ⧸ V)) :=
      Subgroup.orderOf_dvd_natCard _ hc
    exact (hker c).1 (orderOf_eq_one_iff.1
      (Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left a hOc).coprime_dvd_left h1) h2))
  have hW : fusionIsSylowIn 2 V K₂ := by
    refine ⟨fun v hv => ?_, hV2, fun P hPK hP hVP => le_antisymm (fun p hp => ?_) hVP⟩
    · show π v ∈ CFSG.pPrimeCore 2 (H ⧸ V)
      rw [(hker v).2 hv]
      exact one_mem _
    · obtain ⟨a, ha⟩ := hP ⟨p, hp⟩
      exact hK₂V p (hPK hp) a (congrArg Subtype.val ha)
  obtain ⟨N, -, hNodd, hNn, hNo⟩ := P6.exists_normal_odd_subgroup (Hh := ⊤) (C := K₂) (Wst := V)
    le_top (fun h _ c hc => hK₂n.conj_mem c hc h) hW (fun c _ w hw => (hVc w hw c).symm)
  have hNle : N ≤ standardComponentOddCore H :=
    le_sSup ⟨⟨fun n hn h => hNn h trivial n hn⟩, hNodd⟩
  have hdec : ∀ c ∈ K₂, c ∈ N ⊔ V := by
    intro c hc
    obtain ⟨a, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine P6.mem_of_pow_mem_of_coprime (a := 2 ^ a) (b := b)
      (Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hb)) ?_ ?_
    · have hord : orderOf (c ^ 2 ^ a) ∣ b :=
        orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hn]; exact pow_orderOf_eq_one c)
      exact Subgroup.mem_sup_left (hNo _ (pow_mem hc _) (hb.of_dvd_nat hord))
    · exact Subgroup.mem_sup_right (hK₂V _ (pow_mem hc _) a
        (by rw [← pow_mul, mul_comm, ← hn]; exact pow_orderOf_eq_one c))
  refine top_le_iff.1 fun k _ => ?_
  obtain ⟨o, ho, s₁, hs₁, hos⟩ := Set.mem_mul.1 (hmul ▸ Set.mem_univ (π k))
  obtain ⟨s, hsQ, rfl⟩ := hs₁
  have hks : k * s⁻¹ ∈ K₂ := by
    show π (k * s⁻¹) ∈ CFSG.pPrimeCore 2 (H ⧸ V)
    rw [map_mul, map_inv, ← hos]
    simpa using ho
  have hk : k = k * s⁻¹ * s := by group
  rw [hk]
  exact mul_mem (sup_le_sup hNle hVQ (hdec _ hks)) (Subgroup.mem_sup_right hsQ)

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_oddCoreSub_sup_of_cyclic {K V S : Subgroup Γ} (hVK : V ≤ K)
    (hVc : ∀ v ∈ V, ∀ k ∈ K, v * k = k * v) (hV2 : IsPGroup 2 V) (hS : fusionIsSylowIn 2 S K)
    {g : Γ} (hgS : g ∈ S) (hSg : S = zpowers g ⊔ V) : K = oddCoreSub K ⊔ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : S ≤ K := hS.1
  have hgK : g ∈ K := hSK hgS
  obtain ⟨Q, hQ⟩ := (P6.isSylowOf_of_fusionIsSylowIn hS).exists_sylow_eq_subgroupOf
  have hQg : (Q : Subgroup K) = zpowers (⟨g, hgK⟩ : K) ⊔ V.subgroupOf K := by
    rw [hQ, hSg, subgroupOf_sup (zpowers_le.2 hgK) hVK, subgroupOf_zpowers_eq hgK]
  have hVc' : ∀ v ∈ V.subgroupOf K, ∀ k : K, v * k = k * v := fun v hv k =>
    Subtype.ext (hVc v (mem_subgroupOf.1 hv) k k.2)
  have key := oddCore_sup_eq_top_of_cyclic hVc' hV2.comap_subtype Q hQg
  have := congrArg (Subgroup.map K.subtype) key
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQ,
    subgroupOf_map_subtype, inf_eq_left.2 hSK] at this
  exact this.symm

end CFSG.LocalAnalysis.EvenBN.Tits.N.S16A
