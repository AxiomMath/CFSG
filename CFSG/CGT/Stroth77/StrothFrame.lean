module

public import CFSG.CGT.Stroth77.WeakType
public import CFSG.CGT.Stroth77.NonSplit.StrothTInputs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)

structure StrothFrame (G : Type) [Group G] [Finite G] where
  simple : IsSimpleGroup G
  S : Sylow 2 G
  A : Subgroup G
  dA : StrothWeakTypeData A (StrothTypeIndex.t100 1)
  E : Subgroup G
  E_eq : E = Subgroup.closure {((dA.a : A) : G) ^ 2, ((dA.b : A) : G) ^ 2, dA.uv, dA.t}
  E_isE : IsE 4 ↥E
  E_quot : ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6),
    Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G))
  E_syl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E
  A_le_S : A ≤ (S : Subgroup G)
  uv_mem_S : dA.uv ∈ (S : Subgroup G)
  t_mem_S : dA.t ∈ (S : Subgroup G)
  u_mem_S : dA.u ∈ (S : Subgroup G)
  nsylowA : IsSylowIn 2 (Subgroup.normalizer (A : Set G))
    ((S : Subgroup G) ⊓ Subgroup.normalizer (A : Set G))
  L_le : dA.L ≤ Subgroup.normalizer (E : Set G)
  A_le : A ≤ Subgroup.normalizer (E : Set G)
  model : ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* Mns, Function.Surjective φ ∧
    φ.ker = CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)) ∧
    φ ⟨dA.uv, L_le dA.uv_mem_L⟩ = mnsUV ∧ φ ⟨dA.t, L_le dA.t_mem_L⟩ = mnsT ∧
    φ ⟨dA.u, L_le dA.u_mem_L⟩ = mnsU ∧ φ ⟨dA.ρ, L_le dA.ρ_mem_L⟩ = mnsRho ∧
    φ ⟨(dA.c : G), A_le dA.c.2⟩ = mnsW ∧ φ ⟨(dA.a : G), A_le dA.a.2⟩ = mnsX1 * mnsX ∧
    φ ⟨(dA.b : G), A_le dA.b.2⟩ = mnsY1 * mnsY

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem E_comm {x y : G} (hx : x ∈ F.E) (hy : y ∈ F.E) : x * y = y * x := by
  have h := F.E_isE.1.1.is_comm.comm ⟨⟨x, hx⟩, Subgroup.mem_top _⟩ ⟨⟨y, hy⟩, Subgroup.mem_top _⟩
  exact congrArg (fun z : ↥(⊤ : Subgroup ↥F.E) => ((z : ↥F.E) : G)) h

theorem E_sq {x : G} (hx : x ∈ F.E) : x * x = 1 := by
  have h := F.E_isE.1.2 ⟨x, hx⟩ (Subgroup.mem_top _)
  have h' := congrArg (fun z : ↥F.E => (z : G)) h
  simpa [pow_two] using h'

theorem a_sq_mem_E : ((F.dA.a : F.A) : G) ^ 2 ∈ F.E := by
  rw [F.E_eq]; exact Subgroup.subset_closure (by simp)

theorem b_sq_mem_E : ((F.dA.b : F.A) : G) ^ 2 ∈ F.E := by
  rw [F.E_eq]; exact Subgroup.subset_closure (by simp)

theorem uv_mem_E : F.dA.uv ∈ F.E := by
  rw [F.E_eq]; exact Subgroup.subset_closure (by simp)

theorem t_mem_E : F.dA.t ∈ F.E := by
  rw [F.E_eq]; exact Subgroup.subset_closure (by simp)

theorem uv_not_mem_centralizer_A : F.dA.uv ∉ Subgroup.centralizer (F.A : Set G) := by
  intro h
  have h1 : conjBy F.dA.uv_mem F.dA.a = F.dA.a := by
    apply Subtype.ext
    have := (Subgroup.mem_centralizer_iff.mp h) _ F.dA.a.2
    simp only [conjBy]
    rw [mul_assoc, this]; group
  have h2 := F.dA.conj_apply F.dA.uv_mem F.dA.uv_conj Torus.a
  rw [show Additive.toMul (F.dA.e.symm Torus.a) = F.dA.a from rfl, h1] at h2
  have h3 : F.dA.e (Additive.ofMul F.dA.a) = Torus.a := by
    simp [StrothWeakTypeData.a]
  rw [h3] at h2
  exact (show (Type100.action 1).φuv Torus.a ≠ (Torus.a : Torus (Type100.k 1)) by decide) h2.symm

theorem t_not_mem_centralizer_A : F.dA.t ∉ Subgroup.centralizer (F.A : Set G) := by
  intro h
  have h1 : conjBy F.dA.t_mem F.dA.a = F.dA.a := by
    apply Subtype.ext
    have := (Subgroup.mem_centralizer_iff.mp h) _ F.dA.a.2
    simp only [conjBy]
    rw [mul_assoc, this]; group
  have h2 := F.dA.conj_apply F.dA.t_mem F.dA.t_conj Torus.a
  rw [show Additive.toMul (F.dA.e.symm Torus.a) = F.dA.a from rfl, h1] at h2
  have h3 : F.dA.e (Additive.ofMul F.dA.a) = Torus.a := by
    simp [StrothWeakTypeData.a]
  rw [h3] at h2
  exact (show (Type100.action 1).φt Torus.a ≠ (Torus.a : Torus (Type100.k 1)) by decide) h2.symm

theorem uv_t_not_mem_centralizer_A : F.dA.uv * F.dA.t ∉ Subgroup.centralizer (F.A : Set G) := by
  intro h
  have h1 : conjBy F.dA.t_mem (conjBy F.dA.uv_mem F.dA.a) = F.dA.a := by
    apply Subtype.ext
    have := (Subgroup.mem_centralizer_iff.mp h) _ F.dA.a.2
    simp only [conjBy]
    calc F.dA.t⁻¹ * (F.dA.uv⁻¹ * (F.dA.a : G) * F.dA.uv) * F.dA.t
        = (F.dA.uv * F.dA.t)⁻¹ * ((F.dA.a : G) * (F.dA.uv * F.dA.t)) := by group
      _ = (F.dA.uv * F.dA.t)⁻¹ * ((F.dA.uv * F.dA.t) * (F.dA.a : G)) := by rw [this]
      _ = F.dA.a := by group
  have h3 : F.dA.e (Additive.ofMul F.dA.a) = Torus.a := by
    simp [StrothWeakTypeData.a]
  have h2 : F.dA.e (Additive.ofMul (conjBy F.dA.t_mem (conjBy F.dA.uv_mem F.dA.a))) =
      (Type100.action 1).φt ((Type100.action 1).φuv Torus.a) := by
    rw [F.dA.t_conj, F.dA.uv_conj, h3]
    rfl
  rw [h1, h3] at h2
  exact (show (Type100.action 1).φt ((Type100.action 1).φuv Torus.a) ≠
    (Torus.a : Torus (Type100.k 1)) by decide) h2.symm

theorem inf_E {D : Subgroup G} (hD : IsMulCommutative D) (hAD : F.A ≤ D) :
    D ⊓ F.E = Subgroup.closure {((F.dA.a : F.A) : G) ^ 2, ((F.dA.b : F.A) : G) ^ 2} := by
  set K := Subgroup.closure {((F.dA.a : F.A) : G) ^ 2, ((F.dA.b : F.A) : G) ^ 2} with hK
  have hKA : K ≤ F.A := by
    rw [hK, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact pow_mem F.dA.a.2 2
    · exact pow_mem F.dA.b.2 2
  have hKE : K ≤ F.E := by
    rw [hK, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact F.a_sq_mem_E
    · exact F.b_sq_mem_E
  apply le_antisymm
  · rintro x ⟨hxD, hxE⟩
    have hnf : ∀ y ∈ F.E, ∃ s ∈ K, ∃ k l : ℕ, y = s * F.dA.uv ^ k * F.dA.t ^ l := by
      intro y hy
      rw [F.E_eq] at hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact ⟨((F.dA.a : F.A) : G) ^ 2, Subgroup.subset_closure (by simp), 0, 0, by simp⟩
        · exact ⟨((F.dA.b : F.A) : G) ^ 2, Subgroup.subset_closure (by simp), 0, 0, by simp⟩
        · exact ⟨1, one_mem _, 1, 0, by simp⟩
        · exact ⟨1, one_mem _, 0, 1, by simp⟩
      | one => exact ⟨1, one_mem _, 0, 0, by simp⟩
      | mul y z hy' hz' hy hz =>
        obtain ⟨s, hs, k, l, rfl⟩ := hy
        obtain ⟨s', hs', k', l', rfl⟩ := hz
        refine ⟨s * s', mul_mem hs hs', k + k', l + l', ?_⟩
        have hsE := hKE hs
        have hs'E := hKE hs'
        have huvk : F.dA.uv ^ k ∈ F.E := pow_mem F.uv_mem_E k
        have huvk' : F.dA.uv ^ k' ∈ F.E := pow_mem F.uv_mem_E k'
        have htl : F.dA.t ^ l ∈ F.E := pow_mem F.t_mem_E l
        have htl' : F.dA.t ^ l' ∈ F.E := pow_mem F.t_mem_E l'
        have hc1 : F.dA.uv ^ k * F.dA.t ^ l * s' = s' * (F.dA.uv ^ k * F.dA.t ^ l) :=
          F.E_comm (mul_mem huvk htl) hs'E
        rw [pow_add, pow_add]
        calc s * F.dA.uv ^ k * F.dA.t ^ l * (s' * F.dA.uv ^ k' * F.dA.t ^ l')
            = s * (F.dA.uv ^ k * F.dA.t ^ l * s') * F.dA.uv ^ k' * F.dA.t ^ l' := by
              simp only [mul_assoc]
          _ = s * (s' * (F.dA.uv ^ k * F.dA.t ^ l)) * F.dA.uv ^ k' * F.dA.t ^ l' := by rw [hc1]
          _ = s * s' * F.dA.uv ^ k * (F.dA.t ^ l * F.dA.uv ^ k') * F.dA.t ^ l' := by
              simp only [mul_assoc]
          _ = s * s' * F.dA.uv ^ k * (F.dA.uv ^ k' * F.dA.t ^ l) * F.dA.t ^ l' := by
              rw [F.E_comm htl huvk']
          _ = s * s' * (F.dA.uv ^ k * F.dA.uv ^ k') * (F.dA.t ^ l * F.dA.t ^ l') := by
              simp only [mul_assoc]
      | inv y hy' hy =>
        obtain ⟨s, hs, k, l, rfl⟩ := hy
        refine ⟨s⁻¹, inv_mem hs, k, l, ?_⟩
        have hsE := hKE hs
        have hsym : ∀ {z : G}, z ∈ F.E → z⁻¹ = z := fun hz =>
          inv_eq_of_mul_eq_one_right (F.E_sq hz)
        rw [hsym (mul_mem (mul_mem hsE (pow_mem F.uv_mem_E k)) (pow_mem F.t_mem_E l)),
          hsym hsE]
    obtain ⟨s, hs, k, l, rfl⟩ := hnf x hxE
    have hcent : ∀ y ∈ F.A, y * (F.dA.uv ^ k * F.dA.t ^ l) = (F.dA.uv ^ k * F.dA.t ^ l) * y := by
      intro y hy
      have h1 : y * (s * F.dA.uv ^ k * F.dA.t ^ l) = (s * F.dA.uv ^ k * F.dA.t ^ l) * y :=
        hD.is_comm.comm ⟨y, hAD hy⟩ ⟨_, hxD⟩ |> congrArg Subtype.val
      have h2 : y * s = s * y := hD.is_comm.comm ⟨y, hAD hy⟩ ⟨s, hAD (hKA hs)⟩ |>
        congrArg Subtype.val
      calc y * (F.dA.uv ^ k * F.dA.t ^ l) = s⁻¹ * (s * y) * (F.dA.uv ^ k * F.dA.t ^ l) := by
            group
        _ = s⁻¹ * (y * s) * (F.dA.uv ^ k * F.dA.t ^ l) := by rw [h2]
        _ = s⁻¹ * (y * (s * F.dA.uv ^ k * F.dA.t ^ l)) := by simp only [mul_assoc]
        _ = s⁻¹ * ((s * F.dA.uv ^ k * F.dA.t ^ l) * y) := by rw [h1]
        _ = (F.dA.uv ^ k * F.dA.t ^ l) * y := by group
    have hmod : ∀ (z : G) (n : ℕ), z ∈ F.E → z ^ n = z ^ (n % 2) := fun z n hz => by
      conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq, F.E_sq hz, one_pow, one_mul]
    rw [hmod _ k F.uv_mem_E, hmod _ l F.t_mem_E] at hcent ⊢
    have hk : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
    have hl : l % 2 = 0 ∨ l % 2 = 1 := Nat.mod_two_eq_zero_or_one l
    rcases hk with hk | hk <;> rcases hl with hl | hl <;> rw [hk, hl] at hcent ⊢
    · simpa using hs
    · exact absurd (Subgroup.mem_centralizer_iff.mpr fun y hy => by simpa using hcent y hy)
        F.t_not_mem_centralizer_A
    · exact absurd (Subgroup.mem_centralizer_iff.mpr fun y hy => by simpa using hcent y hy)
        F.uv_not_mem_centralizer_A
    · exact absurd (Subgroup.mem_centralizer_iff.mpr fun y hy => by simpa using hcent y hy)
        F.uv_t_not_mem_centralizer_A
  · exact le_inf (hKA.trans hAD) hKE

end StrothFrame

end CFSG.CGT.Stroth77
