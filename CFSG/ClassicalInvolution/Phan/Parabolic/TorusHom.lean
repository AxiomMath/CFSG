module

public import CFSG.ClassicalInvolution.Phan.Torus
public import CFSG.ClassicalInvolution.Phan.TorusAgree

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {Y : Type} [Group Y] {n : ℕ}

theorem blockEmb2_two_zero_eq (h : 0 < 2) :
    blockEmb2 K p f 2 ⟨0, h⟩ = embSUid (unitaryInvolution K p f) 2 :=
  embSUid_two_eq_blockEmb.symm

theorem blockEmb2_two_one_eq (h : 1 < 2) :
    blockEmb2 K p f 2 ⟨1, h⟩ = embSUid (unitaryInvolution K p f) 0 :=
  embSUid_zero_eq_blockEmb.symm

theorem blockEmb2_zero_eq : blockEmb2 K p f 2 0 = embSUid (unitaryInvolution K p f) 2 :=
  embSUid_two_eq_blockEmb.symm

theorem blockEmb2_one_eq : blockEmb2 K p f 2 1 = embSUid (unitaryInvolution K p f) 0 :=
  embSUid_zero_eq_blockEmb.symm

theorem PhanFamily.θ_embSUid_two (F : PhanFamily K p f Y n) (i : Fin n) (h : (i : ℕ) + 1 < n)
    (B : Su K p f 2) : F.θ i (embSUid (unitaryInvolution K p f) 2 B) = F.ι i B :=
  DFunLike.congr_fun (F.left i h) B

theorem PhanFamily.θ_embSUid_zero (F : PhanFamily K p f Y n) (i : Fin n) (h : (i : ℕ) + 1 < n)
    (B : Su K p f 2) : F.θ i (embSUid (unitaryInvolution K p f) 0 B) = F.ι ⟨i + 1, h⟩ B :=
  DFunLike.congr_fun (F.right i h) B

@[expose] noncomputable def PhanFamily.torusFactor (F : PhanFamily K p f Y n) (k : Fin n) :
    normOne (unitaryInvolution K p f) →* Y :=
  (F.ι k).comp (torusTwo (unitaryInvolution K p f))

theorem PhanFamily.torusFactor_apply (F : PhanFamily K p f Y n) (k : Fin n)
    (u : normOne (unitaryInvolution K p f)) :
    F.torusFactor k u = F.ι k (torusTwo (unitaryInvolution K p f) u) :=
  rfl

theorem PhanFamily.torusFactor_commute_succ (F : PhanFamily K p f Y n) (i : Fin n)
    (h : (i : ℕ) + 1 < n) (u v : normOne (unitaryInvolution K p f)) :
    Commute (F.torusFactor i u) (F.torusFactor ⟨i + 1, h⟩ v) := by
  rw [PhanFamily.torusFactor_apply, PhanFamily.torusFactor_apply, ← F.θ_embSUid_two i h,
    ← F.θ_embSUid_zero i h, Commute, SemiconjBy, ← map_mul, ← map_mul, embSUid_two_torus_comm]

theorem PhanFamily.torusFactor_commute (F : PhanFamily K p f Y n) {k l : Fin n} (hkl : k ≠ l)
    (u v : normOne (unitaryInvolution K p f)) :
    Commute (F.torusFactor k u) (F.torusFactor l v) := by
  have hkl' : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
  rcases (by omega : (k : ℕ) + 1 < l ∨ (l : ℕ) + 1 < k ∨ (l : ℕ) = k + 1 ∨ (k : ℕ) = l + 1) with
    h | h | h | h
  · exact F.comm k l h _ _
  · exact (F.comm l k h _ _).symm
  · have := F.torusFactor_commute_succ k (by omega) u v
    convert this using 3
    exact Fin.ext h
  · have := F.torusFactor_commute_succ l (by omega) v u
    convert this.symm using 3
    exact Fin.ext h

@[expose] noncomputable def PhanFamily.torusHom (F : PhanFamily K p f Y n) :
    torus (unitaryInvolution K p f) (n + 1) →* Y :=
  (MonoidHom.noncommPiCoprod F.torusFactor (fun _ _ hkl u v => F.torusFactor_commute hkl u v)).comp
    (torusEquiv (unitaryInvolution K p f) n).symm.toMonoidHom

theorem PhanFamily.torusHom_torusEquiv_mulSingle (F : PhanFamily K p f Y n) (k : Fin n)
    (u : normOne (unitaryInvolution K p f)) :
    F.torusHom (torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u)) = F.torusFactor k u := by
  simp only [PhanFamily.torusHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem PhanFamily.torusHom_blockEmb2 (F : PhanFamily K p f Y n) (k : Fin n)
    (u : normOne (unitaryInvolution K p f))
    (h : blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) ∈
      torus (unitaryInvolution K p f) (n + 1)) :
    F.torusHom ⟨blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u), h⟩ =
      F.ι k (torusTwo (unitaryInvolution K p f) u) := by
  have : (⟨blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u), h⟩ :
      torus (unitaryInvolution K p f) (n + 1)) =
        torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u) :=
    Subtype.ext (coe_torusEquiv_mulSingle k u).symm
  rw [this, F.torusHom_torusEquiv_mulSingle]
  rfl

theorem blockEmb2_torusTwo_mem_torus (k : Fin n) (u : normOne (unitaryInvolution K p f)) :
    blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) ∈
      torus (unitaryInvolution K p f) (n + 1) := by
  rw [← coe_torusEquiv_mulSingle]
  exact (torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u)).2

@[expose] noncomputable def blockTuple (k j : Fin n) (u : normOne (unitaryInvolution K p f)) :
    Fin 2 → normOne (unitaryInvolution K p f) :=
  fun x => if (j : ℕ) + x = k then u else if (j : ℕ) + x = k + 1 then u⁻¹ else 1

theorem blockTuple_self (k : Fin n) (u : normOne (unitaryInvolution K p f)) :
    blockTuple k k u = ![u, u⁻¹] := by
  funext x
  fin_cases x <;> simp [blockTuple]

theorem blockTuple_succ {k j : Fin n} (h : (j : ℕ) = k + 1)
    (u : normOne (unitaryInvolution K p f)) : blockTuple k j u = ![u⁻¹, 1] := by
  funext x
  fin_cases x
  · simp [blockTuple, h]
  · simp only [blockTuple, Fin.mk_one, ite_eq_right (by omega : ¬ (j : ℕ) + 1 = k),
      ite_eq_right (by omega : ¬ (j : ℕ) + 1 = k + 1)]
    rfl

theorem blockTuple_pred {k j : Fin n} (h : (k : ℕ) = j + 1)
    (u : normOne (unitaryInvolution K p f)) : blockTuple k j u = ![1, u] := by
  funext x
  fin_cases x
  · simp only [blockTuple, Fin.zero_eta, add_zero, ite_eq_right (by omega : ¬ (j : ℕ) = k),
      ite_eq_right (by omega : ¬ (j : ℕ) = k + 1)]
    rfl
  · simp [blockTuple, h]

theorem PhanFamily.conj_torusFactor (hK : Nat.card K = (p ^ f) ^ 2) (F : PhanFamily K p f Y n)
    (k j : Fin n) (u : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    F.torusFactor k u * F.ι j A * (F.torusFactor k u)⁻¹ =
      F.ι j (conjDiag hK (blockTuple k j u) A) := by
  have hmain := blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK k j u A
  change blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u) * blockEmb2 K p f n j A *
      (blockEmb2 K p f n k (torusTwo (unitaryInvolution K p f) u))⁻¹ =
    blockEmb2 K p f n j (conjDiag hK (blockTuple k j u) A) at hmain
  rcases (by omega : (k : ℕ) + 1 < j ∨ (j : ℕ) + 1 < k ∨ (j : ℕ) = k ∨ (j : ℕ) = k + 1 ∨
    (k : ℕ) = j + 1) with hfar | hfar | hjk | hjk | hjk
  ·
    have hc : conjDiag hK (blockTuple k j u) A = A := by
      refine blockEmb2_injective n j ?_
      rw [← hmain, blockEmb2_comm n k j hfar, mul_inv_cancel_right]
    rw [hc, torusFactor_apply]
    exact mul_inv_eq_iff_eq_mul.2 (F.comm k j hfar _ _)
  · have hc : conjDiag hK (blockTuple k j u) A = A := by
      refine blockEmb2_injective n j ?_
      rw [← hmain, ← blockEmb2_comm n j k hfar, mul_inv_cancel_right]
    rw [hc, torusFactor_apply]
    exact mul_inv_eq_iff_eq_mul.2 (F.comm j k hfar _ _).symm
  · have hjk' : j = k := Fin.ext hjk
    subst hjk'
    have hc : conjDiag hK (blockTuple j j u) A =
        torusTwo (unitaryInvolution K p f) u * A * (torusTwo (unitaryInvolution K p f) u)⁻¹ := by
      refine blockEmb2_injective n j ?_
      rw [← hmain]
      simp only [map_mul, map_inv]
    rw [hc, torusFactor_apply]
    simp only [map_mul, map_inv]
  · have hk : (k : ℕ) + 1 < n := by omega
    obtain rfl : j = ⟨k + 1, hk⟩ := Fin.ext hjk
    have h2 := blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK (n := 2) ⟨0, by omega⟩ ⟨1, by omega⟩ u A
    change blockEmb2 K p f 2 ⟨0, by omega⟩ (torusTwo (unitaryInvolution K p f) u) *
        blockEmb2 K p f 2 ⟨1, by omega⟩ A *
        (blockEmb2 K p f 2 ⟨0, by omega⟩ (torusTwo (unitaryInvolution K p f) u))⁻¹ =
      blockEmb2 K p f 2 ⟨1, by omega⟩
        (conjDiag hK (blockTuple (n := 2) ⟨0, by omega⟩ ⟨1, by omega⟩ u) A) at h2
    rw [blockTuple_succ (by rfl), blockEmb2_two_zero_eq, blockEmb2_two_one_eq] at h2
    have h3 := congrArg (F.θ k) h2
    simp only [map_mul, map_inv, F.θ_embSUid_two k hk, F.θ_embSUid_zero k hk] at h3
    rw [blockTuple_succ (by rfl), torusFactor_apply]
    exact h3
  · have hj : (j : ℕ) + 1 < n := by omega
    obtain rfl : k = ⟨j + 1, hj⟩ := Fin.ext hjk
    have h2 := blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK (n := 2) ⟨1, by omega⟩ ⟨0, by omega⟩ u A
    change blockEmb2 K p f 2 ⟨1, by omega⟩ (torusTwo (unitaryInvolution K p f) u) *
        blockEmb2 K p f 2 ⟨0, by omega⟩ A *
        (blockEmb2 K p f 2 ⟨1, by omega⟩ (torusTwo (unitaryInvolution K p f) u))⁻¹ =
      blockEmb2 K p f 2 ⟨0, by omega⟩
        (conjDiag hK (blockTuple (n := 2) ⟨1, by omega⟩ ⟨0, by omega⟩ u) A) at h2
    rw [blockTuple_pred (by rfl), blockEmb2_two_zero_eq, blockEmb2_two_one_eq] at h2
    have h3 := congrArg (F.θ j) h2
    simp only [map_mul, map_inv, F.θ_embSUid_two j hj, F.θ_embSUid_zero j hj] at h3
    rw [blockTuple_pred (by rfl), torusFactor_apply]
    exact h3

end CFSG.ClassicalInvolution.Phan
