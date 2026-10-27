module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NO2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Syl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def eCols5 (a b : Fin 2) (i : Fin 3) (j : Fin 2) : Fin 4 → V4 :=
  comp (transCols a b) (comp (pw3 dCols i) (pw xCols j))

theorem eCols5_injective : ∀ a b a' b' : Fin 2, ∀ i i' : Fin 3, ∀ j j' : Fin 2,
    ¬ (∀ k, blk (lin (eCols5 a b i j) (pt k)) = blk (lin (eCols5 a' b' i' j') (pt k))) ∨
      (a = a' ∧ b = b' ∧ i = i' ∧ j = j') := by decide

theorem cls5_eq_bas : ∀ a b : Fin 2, ∀ σ₁ ∈ three, ∀ σ₂ ∈ three, σ₁ = σ₂ ∨
    ¬ (∀ j, blk (lin (cls5 a b σ₁ σ₂) (pt j)) = j) ∨ ∀ i, cls5 a b σ₁ σ₂ i = bas i := by decide

theorem transl_cls5 : ∀ a b : Fin 2, ∀ σ₁ ∈ three, ∀ σ₂ ∈ three, σ₁ = σ₂ ∨
    ((∀ j, blk (lin (cls5 a b σ₁ σ₂) (pt j)) = j + blk (lin (cls5 a b σ₁ σ₂) (pt 0))) ↔
      (σ₁ = (1, 0, 0, 0) ∧ σ₂ = (0, 1, 0, 0))) := by decide

theorem cls5_id : ∀ a b : Fin 2, ∀ i, cls5 a b (1, 0, 0, 0) (0, 1, 0, 0) i = transCols a b i := by
  decide

theorem transCols_transl : ∀ a b : Fin 2, ∀ j,
    blk (lin (transCols a b) (pt j)) = j + blk (lin (transCols a b) (pt 0)) := by decide

theorem blk_dCols : ∀ j, blk (lin dCols (pt j)) = πd j := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem μ_pt (I : S.Inst) (n : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) :
    I.μ n (pt j) = pt (blk (I.μ n (pt j))) := by
  have h1 : I.wV (pt j) ∈ I.orbitN := (H.mem_orbitN_iff I (pt j)).mpr ⟨rfl, rfl⟩
  have h2 : I.wV (I.μ n (pt j)) ∈ I.orbitN := by
    rw [← I.conj_wV]
    exact I.conj_mem_orbitN n.2 h1
  obtain ⟨h3, h4⟩ := (H.mem_orbitN_iff I _).mp h2
  generalize I.μ n (pt j) = P at h3 h4 ⊢
  obtain ⟨p, q, r, s⟩ := P
  simp only at h3 h4
  subst h3 h4
  rfl

theorem βf_mul5 (I : S.Inst) (n m : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) :
    I.βf (n * m) j = I.βf n (I.βf m j) := by
  show blk (I.μ (n * m) (pt j)) = blk (I.μ n (pt (blk (I.μ m (pt j)))))
  rw [I.μ_mul, ← H.μ_pt I m j]

@[expose] noncomputable def blockHom5 (I : S.Inst) :
    normalizer (I.E : Set X) →* Perm (Fin 2 × Fin 2) where
  toFun n :=
    { toFun := I.βf n
      invFun := I.βf n⁻¹
      left_inv := fun j => by rw [← H.βf_mul5 I, inv_mul_cancel, I.βf_one]
      right_inv := fun j => by rw [← H.βf_mul5 I, mul_inv_cancel, I.βf_one] }
  map_one' := Equiv.ext fun j => I.βf_one j
  map_mul' n m := Equiv.ext fun j => H.βf_mul5 I n m j

theorem blockHom5_apply (I : S.Inst) (n : normalizer (I.E : Set X)) (j : Fin 2 × Fin 2) :
    H.blockHom5 I n j = blk (I.μ n (pt j)) := rfl

theorem blockHom5_of_mat (I : S.Inst) {n : X} {c : Fin 4 → V4} (h : I.Mat n c)
    (j : Fin 2 × Fin 2) : H.blockHom5 I ⟨n, h.1⟩ j = blk (lin c (pt j)) := by
  rw [blockHom5_apply, I.μ_eq_lin, show (fun i => I.μ ⟨n, h.1⟩ (bas i)) = c from funext h.2]

theorem blockHom5_eq_one_of_mem (I : S.Inst) {n : normalizer (I.E : Set X)}
    (hn : (n : X) ∈ centralizer (I.E : Set X)) : H.blockHom5 I n = 1 := by
  have hcols : (fun i => I.μ n (bas i)) = bas := funext ((I.μ_eq_id_iff n).mpr hn)
  refine Equiv.ext fun j => ?_
  rw [blockHom5_apply, I.μ_eq_lin, hcols, Inst.lin_bas_self]
  rfl

theorem ker_blockHom5 (I : S.Inst) :
    (H.blockHom5 I).ker = (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h1
    obtain ⟨a, b, σ₁, h₁, σ₂, h₂, h12, hM⟩ := H.classify I n.2
    have hb : ∀ j, blk (lin (cls5 a b σ₁ σ₂) (pt j)) = j := fun j => by
      have := congrArg (fun e : Perm (Fin 2 × Fin 2) => e j) h1
      simp only [Perm.coe_one, id_eq] at this
      rw [← H.blockHom5_of_mat I hM j]
      exact this
    have := ((cls5_eq_bas a b σ₁ h₁ σ₂ h₂).resolve_left h12).resolve_left (not_not.mpr hb)
    exact (I.μ_eq_id_iff n).mp fun i => (hM.2 i).trans (this i)
  · exact fun hn => H.blockHom5_eq_one_of_mem I hn

theorem blockHom5_surjective (I : S.Inst) : Function.Surjective (H.blockHom5 I) := by
  obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
  have hdM : I.Mat d dCols := ⟨hd.1, hdc⟩
  have hxN : S.x ∈ normalizer (I.E : Set X) := S.T_le_normalizer_E I.yi_mem S.x_mem.1
  have hxM : I.Mat S.x xCols := ⟨hxN, I.x_cols hxN⟩
  have hτ : ∀ a b : Fin 2, ∃ τ, I.Mat τ (transCols a b) := H.exists_transl I
  choose τ hτM using hτ
  let g : Fin 2 × Fin 2 × Fin 3 × Fin 2 → normalizer (I.E : Set X) := fun p =>
    ⟨τ p.1 p.2.1 * (d ^ (p.2.2.1 : ℕ) * S.x ^ (p.2.2.2 : ℕ)),
      ((hτM p.1 p.2.1).mul ((hdM.pw3 p.2.2.1).mul (hxM.pw p.2.2.2))).1⟩
  have hgM : ∀ p, I.Mat (g p : X) (eCols5 p.1 p.2.1 p.2.2.1 p.2.2.2) := fun p =>
    (hτM p.1 p.2.1).mul ((hdM.pw3 p.2.2.1).mul (hxM.pw p.2.2.2))
  have hinj : Function.Injective (fun p => H.blockHom5 I (g p)) := by
    intro p p' h
    have hb : ∀ k, blk (lin (eCols5 p.1 p.2.1 p.2.2.1 p.2.2.2) (pt k)) =
        blk (lin (eCols5 p'.1 p'.2.1 p'.2.2.1 p'.2.2.2) (pt k)) := fun k => by
      have h3 : H.blockHom5 I (g p) k = H.blockHom5 I (g p') k := by
        simp only at h
        rw [h]
      rwa [show g p = ⟨_, (hgM p).1⟩ from rfl, show g p' = ⟨_, (hgM p').1⟩ from rfl,
        H.blockHom5_of_mat I (hgM p), H.blockHom5_of_mat I (hgM p')] at h3
    obtain ⟨h₁, h₂, h₃, h₄⟩ := (eCols5_injective _ _ _ _ _ _ _ _).resolve_left (not_not.mpr hb)
    obtain ⟨a, b, i, j⟩ := p
    obtain ⟨a', b', i', j'⟩ := p'
    simp only at h₁ h₂ h₃ h₄
    subst h₁ h₂ h₃ h₄
    rfl
  have hcard : Fintype.card (Fin 2 × Fin 2 × Fin 3 × Fin 2) =
      Fintype.card (Perm (Fin 2 × Fin 2)) := by
    simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial]
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  intro y
  obtain ⟨p, hp⟩ := hbij.2 y
  exact ⟨g p, hp⟩

theorem automizer (I : S.Inst) :
    Nonempty (normalizer (I.E : Set X) ⧸
      (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X)) ≃* Equiv.Perm (Fin 4)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (H.ker_blockHom5 I).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ (H.blockHom5_surjective I)).trans
      (finProdFinEquiv.permCongrHom))⟩

@[expose] noncomputable def Pre5 (I : S.Inst) : Subgroup (normalizer (I.E : Set X)) :=
  transl.comap (H.blockHom5 I)

theorem Pre5_normal (I : S.Inst) : (H.Pre5 I).Normal :=
  @Subgroup.Normal.comap _ _ _ _ _ transl_normal (H.blockHom5 I)

theorem cols_of_mem_Pre5 (I : S.Inst) {n : normalizer (I.E : Set X)} (hn : n ∈ H.Pre5 I) :
    ∃ a b : Fin 2, I.Mat (n : X) (transCols a b) := by
  obtain ⟨a, b, σ₁, h₁, σ₂, h₂, h12, hM⟩ := H.classify I n.2
  have htr : ∀ j, blk (lin (cls5 a b σ₁ σ₂) (pt j)) = j + blk (lin (cls5 a b σ₁ σ₂) (pt 0)) := by
    intro j
    rw [← H.blockHom5_of_mat I hM, ← H.blockHom5_of_mat I hM]
    exact hn j
  obtain ⟨rfl, rfl⟩ := ((transl_cls5 a b σ₁ h₁ σ₂ h₂).resolve_left h12).mp htr
  exact ⟨a, b, hM.1, fun i => (hM.2 i).trans (cls5_id a b i)⟩

theorem mem_Pre5_of_mat (I : S.Inst) {n : X} {a b : Fin 2} (h : I.Mat n (transCols a b)) :
    (⟨n, h.1⟩ : normalizer (I.E : Set X)) ∈ H.Pre5 I := by
  show ∀ j, H.blockHom5 I ⟨n, h.1⟩ j = j + H.blockHom5 I ⟨n, h.1⟩ 0
  intro j
  rw [H.blockHom5_of_mat I h, H.blockHom5_of_mat I h]
  exact transCols_transl a b j

theorem oddTwoCoreIn_eq (I : S.Inst) :
    oddTwoCoreIn (normalizer (I.E : Set X)) =
      (H.Pre5 I).map (normalizer (I.E : Set X)).subtype := by
  set N := normalizer (I.E : Set X) with hN
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    have hnK : (n : X) ∈ oddTwoCoreIn N := ⟨n, hn, rfl⟩
    have h8 : ∀ g : N, (g : X) ∈ oddTwoCoreIn N → H.blockHom5 I g ^ 8 = 1 := by
      intro g hg
      obtain ⟨a, ha⟩ := Inst.exists_pow_mem_oddCoreIn' hg
      have hgC : ((g ^ (2 ^ a) : N) : X) ∈ centralizer (I.E : Set X) := by
        have := I.oddCoreIn_le_centralizerE ha
        simpa using this
      exact pow8_of_pow (by rw [← map_pow]; exact H.blockHom5_eq_one_of_mem I hgC)
    obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
    have hdM : I.Mat d dCols := ⟨hd.1, hdc⟩
    set D : N := ⟨d, hd.1⟩
    have hβd : H.blockHom5 I D = πd := Equiv.ext fun j => by
      rw [show D = ⟨d, hdM.1⟩ from rfl, H.blockHom5_of_mat I hdM, blk_dCols]
    have hgK : ((n * D * n⁻¹ * D⁻¹ : N) : X) ∈ oddTwoCoreIn N := by
      have h1 : (D : X) * (n : X)⁻¹ * (D : X)⁻¹ ∈ oddTwoCoreIn N :=
        Inst.conj_mem_oddTwoCoreIn' D.2 (inv_mem hnK)
      have := mul_mem hnK h1
      simpa [mul_assoc] using this
    have hc := h8 _ hgK
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hβd] at hc
    rcases transl_of_comm (H.blockHom5 I n) with h | h | h
    · exact h
    · exact absurd (h8 n hnK) h
    · exact absurd hc h
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N)
    obtain ⟨K, hKC, hKO, hdec⟩ := I.exists_complement
    have hnormal : ((H.Pre5 I).map (QuotientGroup.mk' (CFSG.oddCore N))).Normal :=
      @Subgroup.Normal.map _ _ _ _ _ (H.Pre5_normal I) _ (QuotientGroup.mk'_surjective _)
    have hp : IsPGroup 2 ((H.Pre5 I).map (QuotientGroup.mk' (CFSG.oddCore N))) := by
      rintro ⟨_, ⟨p, hp, rfl⟩⟩
      refine ⟨2, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨a, b, hpM⟩ := H.cols_of_mem_Pre5 I hp
      have hp2 : ((p ^ 2 : N) : X) ∈ centralizer (I.E : Set X) := by
        have := hpM.mul hpM
        rw [show comp (transCols a b) (transCols a b) = bas from funext (transCols_sq a b),
          ← pow_two] at this
        exact this.mem_centralizer
      obtain ⟨e, he, k, hk, hek⟩ := hdec _ hp2
      have hk' : (((p ^ 2) ^ 2 : N) : X) = k ^ 2 := by
        rw [Subgroup.coe_pow, hek, pow_two, pow_two]
        have hc : e * k = k * e := (mem_centralizer_iff.mp (hKC hk)) e he
        calc e * k * (e * k) = (e * e) * (k * k) := by
              rw [mul_assoc, ← mul_assoc k e k, ← hc, mul_assoc, mul_assoc]
          _ = k * k := by rw [← pow_two e, I.sq_eq_one he, one_mul]
      have hkO : k ^ 2 ∈ oddCoreIn N := pow_mem (hKO hk) 2
      obtain ⟨o, ho, hoe⟩ := hkO
      have : (p ^ 2) ^ 2 = o := Subtype.ext (by rw [hk', ← hoe]; rfl)
      rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, this]
      exact ho
    exact (le_sSup (s := {K : Subgroup (N ⧸ CFSG.oddCore N) | K.Normal ∧ IsPGroup 2 K})
      ⟨hnormal, hp⟩ : _ ≤ CFSG.pCore 2 (N ⧸ CFSG.oddCore N)) (Subgroup.mem_map_of_mem _ hn)

theorem index_Pre5 (I : S.Inst) : (H.Pre5 I).index = 6 := by
  rw [Pre5, index_comap_of_surjective _ (H.blockHom5_surjective I)]
  have h1 := transl.card_mul_index
  have hcard : Nat.card transl = 4 := by
    have key : (transl : Set (Perm (Fin 2 × Fin 2))) =
        {σ : Perm (Fin 2 × Fin 2) | ∀ j, σ j = j + σ 0} := rfl
    rw [← SetLike.coe_sort_coe, key, Nat.card_eq_fintype_card]
    rfl
  rw [hcard, Nat.card_perm] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Nat.factorial] at h1
  omega

theorem factorization_Pre5 (I : S.Inst) : (Nat.card (H.Pre5 I)).factorization 2 = 6 := by
  have h1 := (H.Pre5 I).card_mul_index
  rw [H.index_Pre5 I] at h1
  have h2 := H.factorization_normalizer I
  rw [← h1, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
    show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h2
  have h3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  omega

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
