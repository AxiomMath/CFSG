module

public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.CGT.Stroth77.Section1Structure

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)

namespace S223

variable {G : Type} [Group G]

theorem isSylowIn_of_le {N Q P : Subgroup G} (hQ : IsSylowIn 2 N Q) (hQP : Q ≤ P)
    (hPN : P ≤ N) (hP : IsPGroup 2 P) : IsSylowIn 2 N P := by
  refine ⟨hPN, hP, fun h => hQ.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex Q P N hQP hPN]
  exact Dvd.dvd.mul_left h _

theorem exists_isSylowIn_ge [Finite G] {N P : Subgroup G} (hPN : P ≤ N) (hP : IsPGroup 2 P) :
    ∃ Q : Subgroup G, IsSylowIn 2 N Q ∧ P ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf N) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup N).map N.subtype, ⟨Subgroup.map_subtype_le _, Q.2.map _, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact Q.not_dvd_index
  · intro x hx
    exact ⟨⟨x, hPN hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem exists_sylow_isSylowIn_inf [Finite G] {N P : Subgroup G} (hPN : P ≤ N)
    (hP : IsPGroup 2 P) : ∃ S : Sylow 2 G, P ≤ S ∧ IsSylowIn 2 N ((S : Subgroup G) ⊓ N) := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowIn_ge hPN hP
  obtain ⟨S, hQS⟩ := hQ.2.1.exists_le_sylow
  exact ⟨S, hPQ.trans hQS,
    isSylowIn_of_le hQ (le_inf hQS hQ.1) inf_le_right (S.2.to_le inf_le_left)⟩

theorem inf_centralizer_eq_of_isSylowIn [Finite G] {D S : Subgroup G}
    (hD : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) (hS : IsPGroup 2 S) (hDS : D ≤ S) :
    S ⊓ Subgroup.centralizer (D : Set G) = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : D ≤ S ⊓ Subgroup.centralizer (D : Set G) := le_inf hDS hD.1
  have hP : IsPGroup 2 (S ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :=
    hS.to_le inf_le_left
  refine le_antisymm ?_ hle
  rw [← Subgroup.relIndex_eq_one]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : D.relIndex (S ⊓ Subgroup.centralizer (D : Set G)) ∣ 2 ^ n :=
    hn ▸ Subgroup.relIndex_dvd_card D _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rcases k with _ | k
  · simpa using hk
  · exfalso
    apply hD.2.2
    rw [← Subgroup.relIndex_mul_relIndex D _ _ hle inf_le_right, hk, pow_succ]
    exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

end S223

namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

@[expose] def mulRho (D : StrothWeakTypeData B τ) (o : S)
    (hoB : o ∈ Subgroup.centralizer (B : Set S)) (huv : o * D.uv = D.uv * o)
    (ht : o * D.t = D.t * o) (hodd : Odd (orderOf (D.ρ * o)))
    (hu : D.u * (D.ρ * o) * D.u * (D.ρ * o) = 1) : StrothWeakTypeData B τ where
  e := D.e
  uv := D.uv
  t := D.t
  u := D.u
  ρ := D.ρ * o
  uv_sq := D.uv_sq
  t_sq := D.t_sq
  uv_comm_t := D.uv_comm_t
  rho_odd := hodd
  u_sq := D.u_sq
  u_rho := hu
  uv_rho := by
    calc D.uv * (D.ρ * o) = (D.uv * D.ρ) * o := (mul_assoc _ _ _).symm
      _ = (D.ρ * D.t) * o := by rw [D.uv_rho]
      _ = D.ρ * (D.t * o) := mul_assoc _ _ _
      _ = D.ρ * (o * D.t) := by rw [ht]
      _ = D.ρ * o * D.t := (mul_assoc _ _ _).symm
  t_rho := by
    calc D.t * (D.ρ * o) = (D.t * D.ρ) * o := (mul_assoc _ _ _).symm
      _ = (D.ρ * D.uv * D.t) * o := by rw [D.t_rho]
      _ = D.ρ * D.uv * (D.t * o) := mul_assoc _ _ _
      _ = D.ρ * D.uv * (o * D.t) := by rw [ht]
      _ = D.ρ * (D.uv * o) * D.t := by group
      _ = D.ρ * (o * D.uv) * D.t := by rw [huv]
      _ = D.ρ * o * D.uv * D.t := by group
  uv_comm_u := D.uv_comm_u
  t_u := D.t_u
  uv_mem := D.uv_mem
  t_mem := D.t_mem
  u_mem := D.u_mem
  ρ_mem := mul_mem D.ρ_mem (Subgroup.centralizer_le_normalizer _ hoB)
  uv_conj := D.uv_conj
  t_conj := D.t_conj
  u_conj := D.u_conj
  ρ_conj := fun x => by
    have hx : conjBy (mul_mem D.ρ_mem (Subgroup.centralizer_le_normalizer _ hoB)) x =
        conjBy D.ρ_mem x := by
      apply Subtype.ext
      have hy : D.ρ⁻¹ * (x : S) * D.ρ ∈ B := (conjBy D.ρ_mem x).2
      have hc := (Subgroup.mem_centralizer_iff.mp hoB) _ hy
      change (D.ρ * o)⁻¹ * (x : S) * (D.ρ * o) = D.ρ⁻¹ * (x : S) * D.ρ
      calc (D.ρ * o)⁻¹ * (x : S) * (D.ρ * o) = o⁻¹ * ((D.ρ⁻¹ * (x : S) * D.ρ) * o) := by group
        _ = o⁻¹ * (o * (D.ρ⁻¹ * (x : S) * D.ρ)) := by rw [hc]
        _ = D.ρ⁻¹ * (x : S) * D.ρ := by group
    rw [hx]
    exact D.ρ_conj x

variable (D : StrothWeakTypeData B τ) (o : S) (hoB : o ∈ Subgroup.centralizer (B : Set S))
  (huv : o * D.uv = D.uv * o) (ht : o * D.t = D.t * o) (hodd : Odd (orderOf (D.ρ * o)))
  (hu : D.u * (D.ρ * o) * D.u * (D.ρ * o) = 1)

@[simp] theorem mulRho_e : (D.mulRho o hoB huv ht hodd hu).e = D.e := rfl

@[simp] theorem mulRho_uv : (D.mulRho o hoB huv ht hodd hu).uv = D.uv := rfl

@[simp] theorem mulRho_t : (D.mulRho o hoB huv ht hodd hu).t = D.t := rfl

@[simp] theorem mulRho_u : (D.mulRho o hoB huv ht hodd hu).u = D.u := rfl

@[simp] theorem mulRho_ρ : (D.mulRho o hoB huv ht hodd hu).ρ = D.ρ * o := rfl

@[simp] theorem mulRho_c : (D.mulRho o hoB huv ht hodd hu).c = D.c := rfl

@[simp] theorem mulRho_a : (D.mulRho o hoB huv ht hodd hu).a = D.a := rfl

@[simp] theorem mulRho_b : (D.mulRho o hoB huv ht hodd hu).b = D.b := rfl

theorem mulRho_L_le {X : Subgroup S} (hL : D.L ≤ Subgroup.normalizer (X : Set S))
    (hoX : o ∈ Subgroup.normalizer (X : Set S)) :
    (D.mulRho o hoB huv ht hodd hu).L ≤ Subgroup.normalizer (X : Set S) := by
  rw [StrothWeakTypeData.L, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hL D.uv_mem_L
  · exact hL D.t_mem_L
  · exact hL D.u_mem_L
  · exact mul_mem (hL D.ρ_mem_L) hoX

end StrothWeakTypeData

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

@[expose] def withSylow (S' : Sylow 2 G) (hA : F.A ≤ (S' : Subgroup G))
    (huv : F.dA.uv ∈ (S' : Subgroup G)) (ht : F.dA.t ∈ (S' : Subgroup G))
    (hu : F.dA.u ∈ (S' : Subgroup G))
    (hns : IsSylowIn 2 (Subgroup.normalizer (F.A : Set G))
      ((S' : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G))) : StrothFrame G where
  simple := F.simple
  S := S'
  A := F.A
  dA := F.dA
  E := F.E
  E_eq := F.E_eq
  E_isE := F.E_isE
  E_quot := F.E_quot
  E_syl := F.E_syl
  A_le_S := hA
  uv_mem_S := huv
  t_mem_S := ht
  u_mem_S := hu
  nsylowA := hns
  L_le := F.L_le
  A_le := F.A_le
  model := F.model

section WithSylow

variable (S' : Sylow 2 G) (hA : F.A ≤ (S' : Subgroup G)) (huv : F.dA.uv ∈ (S' : Subgroup G))
  (ht : F.dA.t ∈ (S' : Subgroup G)) (hu : F.dA.u ∈ (S' : Subgroup G))
  (hns : IsSylowIn 2 (Subgroup.normalizer (F.A : Set G))
    ((S' : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G)))

@[simp] theorem withSylow_S : (F.withSylow S' hA huv ht hu hns).S = S' := rfl

@[simp] theorem withSylow_A : (F.withSylow S' hA huv ht hu hns).A = F.A := rfl

@[simp] theorem withSylow_dA : (F.withSylow S' hA huv ht hu hns).dA = F.dA := rfl

@[simp] theorem withSylow_E : (F.withSylow S' hA huv ht hu hns).E = F.E := rfl

end WithSylow

theorem exists_withSylow_of_le {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (F.A : Set G)) (hA : F.A ≤ P) (huv : F.dA.uv ∈ P)
    (ht : F.dA.t ∈ P) (hu : F.dA.u ∈ P) :
    ∃ S' : Sylow 2 G, F.A ≤ (S' : Subgroup G) ∧ F.dA.uv ∈ (S' : Subgroup G) ∧
      F.dA.t ∈ (S' : Subgroup G) ∧ F.dA.u ∈ (S' : Subgroup G) ∧
      IsSylowIn 2 (Subgroup.normalizer (F.A : Set G))
        ((S' : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G)) ∧ P ≤ (S' : Subgroup G) := by
  obtain ⟨S', hPS, hns⟩ := S223.exists_sylow_isSylowIn_inf hPN hP
  exact ⟨S', hA.trans hPS, hPS huv, hPS ht, hPS hu, hns, hPS⟩

theorem IsD.withSylow {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} (h : F.IsD D dD) (S' : Sylow 2 G) (hA : F.A ≤ (S' : Subgroup G))
    (huv : F.dA.uv ∈ (S' : Subgroup G)) (ht : F.dA.t ∈ (S' : Subgroup G))
    (hu : F.dA.u ∈ (S' : Subgroup G))
    (hns : IsSylowIn 2 (Subgroup.normalizer (F.A : Set G))
      ((S' : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G)))
    (hDS : D ≤ (S' : Subgroup G))
    (hcent : (S' : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) = D) :
    (F.withSylow S' hA huv ht hu hns).IsD D dD where
  A_le := h.A_le
  le_S := hDS
  uv_eq := h.uv_eq
  t_eq := h.t_eq
  u_eq := h.u_eq
  ρ_eq := h.ρ_eq
  cent := hcent

theorem mem_oddCore_of_mem_centralizer_E {o : G} (hoE : o ∈ Subgroup.centralizer (F.E : Set G))
    (hodd : Odd (orderOf o)) :
    (⟨o, centralizer_le_normalizer_set hoE⟩ : ↥(Subgroup.normalizer (F.E : Set G))) ∈
      CFSG.oddCore ↥(Subgroup.normalizer (F.E : Set G)) := by
  obtain ⟨K, hKC, hKodd, hKiff, -, -⟩ := exists_odd_complement_centralizer F.E_isE F.E_syl
  rw [oddCore_normalizer_eq F.E_isE hKC hKodd hKiff, Subgroup.mem_subgroupOf]
  exact (hKiff o).2 ⟨hoE, hodd⟩

variable {o : G} (hoA : o ∈ Subgroup.centralizer (F.A : Set G))
  (hoE : o ∈ Subgroup.centralizer (F.E : Set G)) (hodd : Odd (orderOf o))
  (hρodd : Odd (orderOf (F.dA.ρ * o)))
  (hu : F.dA.u * (F.dA.ρ * o) * F.dA.u * (F.dA.ρ * o) = 1)

include hoE in
theorem comm_uv_of_mem_centralizer_E : o * F.dA.uv = F.dA.uv * o :=
  ((Subgroup.mem_centralizer_iff.mp hoE) _ F.uv_mem_E).symm

include hoE in
theorem comm_t_of_mem_centralizer_E : o * F.dA.t = F.dA.t * o :=
  ((Subgroup.mem_centralizer_iff.mp hoE) _ F.t_mem_E).symm

@[expose] def dAMulRho : StrothWeakTypeData F.A (StrothTypeIndex.t100 1) :=
  F.dA.mulRho o hoA (F.comm_uv_of_mem_centralizer_E hoE) (F.comm_t_of_mem_centralizer_E hoE)
    hρodd hu

theorem dAMulRho_L_le : (F.dAMulRho hoA hoE hρodd hu).L ≤ Subgroup.normalizer (F.E : Set G) :=
  StrothWeakTypeData.mulRho_L_le F.dA o hoA (F.comm_uv_of_mem_centralizer_E hoE)
    (F.comm_t_of_mem_centralizer_E hoE) hρodd hu F.L_le (centralizer_le_normalizer_set hoE)

@[expose] def withRho : StrothFrame G where
  simple := F.simple
  S := F.S
  A := F.A
  dA := F.dAMulRho hoA hoE hρodd hu
  E := F.E
  E_eq := F.E_eq
  E_isE := F.E_isE
  E_quot := F.E_quot
  E_syl := F.E_syl
  A_le_S := F.A_le_S
  uv_mem_S := F.uv_mem_S
  t_mem_S := F.t_mem_S
  u_mem_S := F.u_mem_S
  nsylowA := F.nsylowA
  L_le := F.dAMulRho_L_le hoA hoE hρodd hu
  A_le := F.A_le
  model := by
    obtain ⟨φ, hφs, hφk, h1, h2, h3, h4, h5, h6, h7⟩ := F.model
    have ho1 : φ ⟨o, centralizer_le_normalizer_set hoE⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hφk]
      exact F.mem_oddCore_of_mem_centralizer_E hoE hodd
    refine ⟨φ, hφs, hφk, h1, h2, h3, ?_, h5, h6, h7⟩
    have hsplit : (⟨(F.dAMulRho hoA hoE hρodd hu).ρ, F.dAMulRho_L_le hoA hoE hρodd hu
        (StrothWeakTypeData.ρ_mem_L _)⟩ : ↥(Subgroup.normalizer (F.E : Set G))) =
        ⟨F.dA.ρ, F.L_le F.dA.ρ_mem_L⟩ * ⟨o, centralizer_le_normalizer_set hoE⟩ := rfl
    rw [hsplit, map_mul, h4, ho1, mul_one]

section WithRho

@[simp] theorem withRho_S : (F.withRho hoA hoE hodd hρodd hu).S = F.S := rfl

@[simp] theorem withRho_A : (F.withRho hoA hoE hodd hρodd hu).A = F.A := rfl

@[simp] theorem withRho_E : (F.withRho hoA hoE hodd hρodd hu).E = F.E := rfl

@[simp] theorem withRho_uv : (F.withRho hoA hoE hodd hρodd hu).dA.uv = F.dA.uv := rfl

@[simp] theorem withRho_t : (F.withRho hoA hoE hodd hρodd hu).dA.t = F.dA.t := rfl

@[simp] theorem withRho_u : (F.withRho hoA hoE hodd hρodd hu).dA.u = F.dA.u := rfl

@[simp] theorem withRho_ρ : (F.withRho hoA hoE hodd hρodd hu).dA.ρ = F.dA.ρ * o := rfl

end WithRho

end StrothFrame

end CFSG.CGT.Stroth77
