module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem z4j_isPGroup_of_sq {A : Subgroup X} (h : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa [pow_two] using h g.1 g.2)

theorem z4j_isPGroup_pair {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 (closure ({a, b} : Set X)) := by
  refine z4j_isPGroup_of_sq fun x hx => ?_
  rw [mem_closure_pair_of_invol ha hb hab] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact ha
  · exact hb
  · calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]

theorem z4j_eq_of_odd_relIndex {A P K : Subgroup X} (hAP : A ≤ P) (hPK : P ≤ K)
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ A.relIndex K) : P = A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex A P K hAP hPK
  have hoddP : ¬ 2 ∣ A.relIndex P := by
    intro h2
    apply hodd
    rw [← hmul]
    exact dvd_mul_of_dvd_left h2 _
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : A.relIndex P ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card A P
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      apply hoddP
      rw [hk]
      exact pow_dvd_pow 2 (Nat.succ_le_of_lt h)
  have hone : A.relIndex P = 1 := by rw [hk, hk0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hAP

variable {N Q Y : Subgroup X} {ρ t τ l : X} [N.Normal]

theorem z4j_K_triv_of (hN : Odd (Nat.card N)) (hY : IsPGroup 2 Y)
    (hK : ∀ k ∈ ⁅centralizer (Y : Set X), zpowers ρ⁆ ⊔ (Q ⊔ N),
      t * k * t⁻¹ * k⁻¹ ∈ Q ⊔ N → k ∈ Q ⊔ N) :
    ∀ k ∈ ⁅centralizer ((Y.map (z4iπ N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)),
        zpowers (z4iπ N ρ)⁆ ⊔ Q.map (z4iπ N),
      z4iπ N t * k * (z4iπ N t)⁻¹ * k⁻¹ ∈ Q.map (z4iπ N) → k ∈ Q.map (z4iπ N) := by
  intro k hk hkt
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker]; exact hN
  have hsup : (⁅centralizer (Y : Set X), zpowers ρ⁆ ⊔ (Q ⊔ N)).map (z4iπ N)
      = ⁅centralizer ((Y.map (z4iπ N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)),
          zpowers (z4iπ N ρ)⁆ ⊔ Q.map (z4iπ N) := by
    rw [← sup_assoc, z4i_map_sup_N, Subgroup.map_sup, Subgroup.map_commutator,
      MonoidHom.map_zpowers,
      ← z4i_centralizer_map_eq (z4iπ N) (z4iπ_surjective N) hker hY]
  have hk' : k ∈ (⁅centralizer (Y : Set X), zpowers ρ⁆ ⊔ (Q ⊔ N)).map (z4iπ N) := by
    rw [hsup]
    exact hk
  obtain ⟨k0, hk0, hk0k⟩ := hk'
  have hmem : t * k0 * t⁻¹ * k0⁻¹ ∈ Q ⊔ N := by
    refine (z4iπ_mem_map_iff N).1 ?_
    have h : z4iπ N (t * k0 * t⁻¹ * k0⁻¹)
        = z4iπ N t * k * (z4iπ N t)⁻¹ * k⁻¹ := by
      rw [← hk0k]
      simp only [map_mul, map_inv]
    rwa [h]
  have hk0QN : k0 ∈ Q ⊔ N := hK k0 hk0 hmem
  have hkQ : z4iπ N k0 ∈ Q.map (z4iπ N) := (z4iπ_mem_map_iff N).2 hk0QN
  rwa [hk0k] at hkQ

theorem z4j_tt_sylow_of (hN : Odd (Nat.card N)) (hCN : ∀ n ∈ N, t * n = n * t → n = 1)
    (ht : t * ρ = ρ * t) (hτ : τ * ρ = ρ * τ) (ht2 : t * t = 1) (hτ2 : τ * τ = 1)
    (htτ : t * τ = τ * t)
    (hodd : ¬ 2 ∣ (closure ({t, τ} : Set X)).relIndex (centralizer ({ρ} : Set X))) :
    ∀ P : Subgroup (X ⧸ N), P ≤ centralizer ({z4iπ N ρ} : Set (X ⧸ N)) → IsPGroup 2 P →
      ∃ c ∈ centralizer ({z4iπ N ρ} : Set (X ⧸ N)),
        ∀ p ∈ P, c * p * c⁻¹ ∈ closure ({z4iπ N t, z4iπ N τ} : Set (X ⧸ N)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (X ⧸ N) := inferInstance
  have hπ : Function.Surjective (z4iπ N) := z4iπ_surjective N
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker]; exact hN
  set A : Subgroup X := closure ({t, τ} : Set X) with hAdef
  set S0 : Subgroup (X ⧸ N) := closure ({z4iπ N t, z4iπ N τ} : Set (X ⧸ N)) with hS0def
  set Kb : Subgroup (X ⧸ N) := centralizer ({z4iπ N ρ} : Set (X ⧸ N)) with hKbdef
  have hA2 : IsPGroup 2 A := by
    rw [hAdef]
    exact z4j_isPGroup_pair ht2 hτ2 htτ
  have hAcent : A ≤ centralizer ({ρ} : Set X) := by
    rw [hAdef, Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_centralizer_singleton_iff.2 ht
    · exact mem_centralizer_singleton_iff.2 hτ
  have hS0eq : A.map (z4iπ N) = S0 := by
    rw [hAdef, hS0def, MonoidHom.map_closure, Set.image_pair]
  have hS02 : IsPGroup 2 S0 := by
    rw [← hS0eq]
    exact hA2.map (z4iπ N)
  have hS0K : S0 ≤ Kb := by
    rw [hKbdef, ← hS0eq]
    rintro _ ⟨a, ha, rfl⟩
    apply mem_centralizer_singleton_iff.2
    rw [← map_mul, ← map_mul]
    exact congrArg (z4iπ N) (mem_centralizer_singleton_iff.1 (hAcent ha))
  have hmax : ∀ T : Subgroup (X ⧸ N), IsPGroup 2 T → T ≤ Kb → S0 ≤ T → T ≤ S0 := by
    intro T hT hTK hS0T
    rw [hKbdef] at hTK
    obtain ⟨P, hP, hAP, hPT, -⟩ :=
      z4i_lift_two_ge (z4iπ N) hπ hker hA2 hT (hS0eq.le.trans hS0T)
    have hπρ : z4iπ N ρ ∈ centralizer ((P.map (z4iπ N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨p, hp, rfl⟩
      exact (mem_centralizer_iff.1 (hTK (hPT ▸ Subgroup.mem_map_of_mem (z4iπ N) hp))
        (z4iπ N ρ) (by simp)).symm
    rw [z4i_centralizer_map_eq (z4iπ N) hπ hker hP] at hπρ
    obtain ⟨x, hx, hxρ⟩ := hπρ
    have hnN : ρ⁻¹ * x ∈ N := (z4iπ_eq_iff N).1 hxρ.symm
    have htA : t ∈ A := by
      rw [hAdef]
      exact Subgroup.subset_closure (by simp)
    have htx : t * x = x * t := (mem_centralizer_iff.1 hx) t (hAP htA)
    have hρinv : t * ρ⁻¹ = ρ⁻¹ * t := by
      have hρ : t * ρ * t⁻¹ = ρ := by rw [ht]; group
      have h1 : t * ρ⁻¹ * t⁻¹ = ρ⁻¹ := by
        rw [show t * ρ⁻¹ * t⁻¹ = (t * ρ * t⁻¹)⁻¹ by group, hρ]
      calc t * ρ⁻¹ = (t * ρ⁻¹ * t⁻¹) * t := by group
        _ = ρ⁻¹ * t := by rw [h1]
    have hcom : t * (ρ⁻¹ * x) = (ρ⁻¹ * x) * t := by
      calc t * (ρ⁻¹ * x) = (t * ρ⁻¹) * x := by group
        _ = (ρ⁻¹ * t) * x := by rw [hρinv]
        _ = ρ⁻¹ * (t * x) := by group
        _ = ρ⁻¹ * (x * t) := by rw [htx]
        _ = (ρ⁻¹ * x) * t := by group
    have hxeq : x = ρ := by
      have h1 : ρ⁻¹ * x = 1 := hCN (ρ⁻¹ * x) hnN hcom
      exact (inv_mul_eq_one.1 h1).symm
    have hxmemρ : ρ ∈ centralizer (P : Set X) := hxeq ▸ hx
    have hPcent : P ≤ centralizer ({ρ} : Set X) := by
      intro p hp
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxmemρ p hp)
    have hPA : P ≤ A := (z4j_eq_of_odd_relIndex hAP hPcent hP hodd).le
    intro t' ht'
    have ht'map : t' ∈ P.map (z4iπ N) := hPT.symm ▸ ht'
    obtain ⟨p, hp, hpp⟩ := ht'map
    rw [← hS0eq, ← hpp]
    exact Subgroup.mem_map_of_mem (z4iπ N) (hPA hp)
  have hSylow : IsSylowIn 2 S0 Kb := by
    refine ⟨hS0K, hS02, ?_⟩
    obtain ⟨S, hS, hS0S⟩ := exists_isSylowIn_of_le hS0K hS02
    have hSeq : S = S0 := le_antisymm (hmax S hS.2.1 hS.1 hS0S) hS0S
    rw [← hSeq]
    exact hS.2.2
  intro P hPK hP
  obtain ⟨T, hTsyl, hPT⟩ := exists_isSylowIn_of_le hPK hP
  obtain ⟨c, hcK, hcj⟩ := exists_cj_of_isSylowIn hTsyl hSylow
  refine ⟨c, ?_, ?_⟩
  · simpa [hKbdef] using hcK
  · intro p hp
    have hmem : c * p * c⁻¹ ∈ cj c T := conj_mem_cj (hPT hp)
    rw [hcj] at hmem
    simpa [hS0def] using hmem

theorem z4j_two_pow_of (hN : Odd (Nat.card N)) (h : 2 ^ 10 ∣ Nat.card X) :
    2 ^ 10 ∣ Nat.card (X ⧸ N) := by
  have hcop : Nat.Coprime (2 ^ 10) (Nat.card N) :=
    (Nat.coprime_two_left.2 hN).pow_left 10
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at h
  exact hcop.dvd_of_dvd_mul_right h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
