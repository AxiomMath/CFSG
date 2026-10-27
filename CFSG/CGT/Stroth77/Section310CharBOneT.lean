module

public import CFSG.CGT.Stroth77.Section310CharBOne
public import CFSG.CGT.Stroth77.Section310CharBT200
public import CFSG.CGT.Stroth77.Section310CharBT201

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

namespace Stroth310One

theorem actsBy_of_rel34i {e : G} {N : ℕ} (hN : N = 4) (he : Rel34i dD e N)
    (hinv : ∀ v, diag4 τ.k 1 (diag4 τ.k 1 v) = v) : ActsBy dD e 1 := by
  subst hN
  refine actsBy_of_conj dD (d := ![1, 5, 5]) rfl hinv ?_ ?_ ?_
  · rw [he.c_conj]; show _ = (dD.c : G) ^ (1 : ℤ); simp
  · rw [he.a_conj]; show _ = (dD.a : G) ^ (5 : ℤ); group
  · rw [he.b_conj]; show _ = (dD.b : G) ^ (5 : ℤ); group

theorem actsBy_of_rel34inv_zero {e s : G} {p : ℕ} (he : Rel34inv dD e 0 s p)
    (hinv : ∀ v, diag4 τ.k 2 (diag4 τ.k 2 v) = v) : ActsBy dD e 2 := by
  refine actsBy_of_conj dD (d := ![-1, -1, -1]) rfl hinv ?_ ?_ ?_
  · rw [he.c_conj]; show _ = (dD.c : G) ^ (-1 : ℤ); simp
  · rw [he.a_conj]; show _ = (dD.a : G) ^ (-1 : ℤ); simp
  · rw [he.b_conj]; show _ = (dD.b : G) ^ (-1 : ℤ); simp

theorem actsBy_of_rel34inv_four {e s : G} {j p : ℕ} (hj : j = 4) (he : Rel34inv dD e j s p)
    (hinv : ∀ v, diag4 τ.k 3 (diag4 τ.k 3 v) = v) : ActsBy dD e 3 := by
  subst hj
  refine actsBy_of_conj dD (d := ![-1, 3, 3]) rfl hinv ?_ ?_ ?_
  · rw [he.c_conj]; show _ = (dD.c : G) ^ (-1 : ℤ); simp
  · rw [he.a_conj]; show _ = (dD.a : G) ^ (3 : ℤ); group
  · rw [he.b_conj]; show _ = (dD.b : G) ^ (3 : ℤ); group

theorem actsBy_of_mem_sup_zpowers {e x : G} {b : Fin 4} (he : ActsBy dD e b)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D)
    (hx : x ∈ D ⊔ Subgroup.zpowers e) : ActsBy dD x 0 ∨ ActsBy dD x b := by
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 hx with hxD | hxD
  · exact Or.inl (actsBy_of_mem dD hxD)
  · right
    have h := he.mul_mem hxD
    rwa [mul_inv_cancel_left] at h

theorem hQ_of_sup_zpowers {e : G} {b : Fin 4} (hb : b ≠ 0) (he : ActsBy dD e b)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D) {Q : Subgroup G}
    (hQR : Q ≤ D ⊔ Subgroup.zpowers e) (hQD : ¬ Q ≤ D) :
    ∃ q ∈ Q, ∃ b' : Fin 4, ActsBy dD q b' ∧
      ((b' = 1 ∧ D.relIndex Q ≤ 2) ∨ ((b' = 2 ∨ b' = 3) ∧ D.relIndex Q ≤ 4)) := by
  obtain ⟨q, hqQ, hqD⟩ := SetLike.not_le_iff_exists.mp hQD
  have hq := (mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 (hQR hqQ)).resolve_left hqD
  have hqb : ActsBy dD q b := by
    have h := he.mul_mem hq
    rwa [mul_inv_cancel_left] at h
  have hi := relIndex_le_two_of_le_sup_zpowers heN he2 hQR
  refine ⟨q, hqQ, b, hqb, ?_⟩
  fin_cases b
  · exact absurd rfl hb
  · exact Or.inl ⟨rfl, hi⟩
  · exact Or.inr ⟨Or.inl rfl, hi.trans (by norm_num)⟩
  · exact Or.inr ⟨Or.inr rfl, hi.trans (by norm_num)⟩

theorem actsBy_of_mem_tower {e f x : G} (he : ActsBy dD e 1) (hf : ActsBy dD f 2)
    (h21 : ∀ v, diag4 τ.k 2 (diag4 τ.k 1 v) = diag4 τ.k 3 v)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D)
    (hfN : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers e : Subgroup G) : Set G))
    (hf2 : f * f ∈ D ⊔ Subgroup.zpowers e)
    (hx : x ∈ (D ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f) : ∃ a, ActsBy dD x a := by
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers hfN hf2 hx with hx' | hx'
  · rcases actsBy_of_mem_sup_zpowers he heN he2 hx' with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  · rcases mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 hx' with hd | hd
    · refine ⟨2, ?_⟩
      have h := hf.mul_mem hd
      rwa [mul_inv_cancel_left] at h
    · refine ⟨3, ?_⟩
      have h := (hf.mul he h21).mul_mem hd
      have e1 : f * e * (e⁻¹ * (f⁻¹ * x)) = x := by group
      rwa [e1] at h

theorem hQ_of_tower {e f : G} (he : ActsBy dD e 1) (hf : ActsBy dD f 2)
    (h21 : ∀ v, diag4 τ.k 2 (diag4 τ.k 1 v) = diag4 τ.k 3 v)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D)
    (hfN : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers e : Subgroup G) : Set G))
    (hf2 : f * f ∈ D ⊔ Subgroup.zpowers e) {Q : Subgroup G}
    (hQR : Q ≤ (D ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f) (hQD : ¬ Q ≤ D) :
    ∃ q ∈ Q, ∃ b' : Fin 4, ActsBy dD q b' ∧
      ((b' = 1 ∧ D.relIndex Q ≤ 2) ∨ ((b' = 2 ∨ b' = 3) ∧ D.relIndex Q ≤ 4)) := by
  by_cases hQe : Q ≤ D ⊔ Subgroup.zpowers e
  · exact hQ_of_sup_zpowers (b := 1) (by decide) he heN he2 hQe hQD
  obtain ⟨q, hqQ, hqe⟩ := SetLike.not_le_iff_exists.mp hQe
  have hq' := (mem_or_inv_mul_mem_of_mem_sup_zpowers hfN hf2 (hQR hqQ)).resolve_left hqe
  have hidx1 := relIndex_le_two_of_le_sup_zpowers hfN hf2 hQR
  have hidx2 := relIndex_le_two_of_le_sup_zpowers heN he2
    (inf_le_left : (D ⊔ Subgroup.zpowers e) ⊓ Q ≤ D ⊔ Subgroup.zpowers e)
  have htower : D.relIndex Q =
      D.relIndex ((D ⊔ Subgroup.zpowers e) ⊓ Q) * (D ⊔ Subgroup.zpowers e).relIndex Q := by
    rw [Subgroup.relIndex_inf_mul_relIndex D (D ⊔ Subgroup.zpowers e) Q,
      inf_eq_left.mpr le_sup_left]
  have hi : D.relIndex Q ≤ 4 := by
    rw [htower]
    calc D.relIndex ((D ⊔ Subgroup.zpowers e) ⊓ Q) * (D ⊔ Subgroup.zpowers e).relIndex Q
        ≤ 2 * 2 := Nat.mul_le_mul hidx2 hidx1
      _ = 4 := by norm_num
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 hq' with hd | hd
  · refine ⟨q, hqQ, 2, ?_, Or.inr ⟨Or.inl rfl, hi⟩⟩
    have h := hf.mul_mem hd
    rwa [mul_inv_cancel_left] at h
  · refine ⟨q, hqQ, 3, ?_, Or.inr ⟨Or.inr rfl, hi⟩⟩
    have h := (hf.mul he h21).mul_mem hd
    have e1 : f * e * (e⁻¹ * (f⁻¹ * q)) = q := by group
    rwa [e1] at h

end Stroth310One

open Stroth310One

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t200_one {m : ℕ} (hm : m = 1)
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t200 m).m = (StrothTypeIndex.t200 m).n)
    (h34 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨
          Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)))
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  subst hm
  have hD : Nat.card D = 128 := by rw [Stroth310T200.card_D dD]; norm_num
  have hinv : ∀ b : Fin 4, ∀ v, diag4 (StrothTypeIndex.t200 1).k b
      (diag4 (StrothTypeIndex.t200 1).k b v) = v := by decide +kernel
  have h21 : ∀ v, diag4 (StrothTypeIndex.t200 1).k 2 (diag4 (StrothTypeIndex.t200 1).k 1 v) =
      diag4 (StrothTypeIndex.t200 1).k 3 v := by decide +kernel
  have hRN : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      x ∈ Subgroup.normalizer (D : Set G) := fun x hx => (Subgroup.mem_inf.mp hx).1.2
  have key : (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∃ a, ActsBy dD x a) ∧
      (∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
        ∃ q ∈ Q, ∃ b : Fin 4, ActsBy dD q b ∧
          ((b = 1 ∧ D.relIndex Q ≤ 2) ∨ ((b = 2 ∨ b = 3) ∧ D.relIndex Q ≤ 4))) := by
    rcases h34 with hRD | ⟨e, heR, hRe, hshape⟩ | ⟨e, heR, f, hfR, hRef, he, hf, hfe⟩ |
      ⟨hm2, -⟩
    · exact ⟨fun x hx => ⟨0, actsBy_of_mem dD (hRD ▸ hx)⟩,
        fun Q hQR hQD => absurd (hRD ▸ hQR) hQD⟩
    · have heN := hRN e heR
      obtain ⟨b, hb0, heb, he2⟩ : ∃ b : Fin 4, b ≠ 0 ∧ ActsBy dD e b ∧ e * e ∈ D := by
        rcases hshape with he | he | he | he | he | he | he
        · exact ⟨1, by decide, actsBy_of_rel34i rfl he (hinv 1), he.e_sq ▸ inv_mem dD.c.2⟩
        · exact ⟨2, by decide, actsBy_of_rel34inv_zero he (hinv 2),
            by rw [he.e_sq]; exact one_mem D⟩
        · exact ⟨2, by decide, actsBy_of_rel34inv_zero he (hinv 2),
            by rw [he.e_sq]; exact one_mem D⟩
        · exact ⟨2, by decide, actsBy_of_rel34inv_zero he (hinv 2),
            by rw [he.e_sq]; exact one_mem D⟩
        · exact ⟨3, by decide, actsBy_of_rel34inv_four rfl he (hinv 3),
            by rw [he.e_sq]; exact one_mem D⟩
        · exact ⟨3, by decide, actsBy_of_rel34inv_four rfl he (hinv 3),
            by rw [he.e_sq]; exact pow_mem dD.c.2 _⟩
        · exact ⟨3, by decide, actsBy_of_rel34inv_four rfl he (hinv 3),
            by rw [he.e_sq]; exact pow_mem dD.c.2 _⟩
      refine ⟨fun x hx => ?_, fun Q hQR hQD => hQ_of_sup_zpowers hb0 heb heN he2 (hRe ▸ hQR) hQD⟩
      rcases actsBy_of_mem_sup_zpowers heb heN he2 (hRe ▸ hx) with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨b, h1⟩
    · have heN := hRN e heR
      have hfN := hRN f hfR
      have he2 : e * e ∈ D := he.e_sq ▸ inv_mem dD.c.2
      have hff : f * f = 1 := by rcases hf with hf | hf <;> exact hf.e_sq
      have hf' : ActsBy dD f 2 := by
        rcases hf with hf | hf
        · exact actsBy_of_rel34inv_zero hf (hinv 2)
        · exact actsBy_of_rel34inv_zero hf (hinv 2)
      have he' : ActsBy dD e 1 := actsBy_of_rel34i rfl he (hinv 1)
      have hRrs : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) =
            (D ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f := by
        rw [hRef, sup_assoc, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union, Set.insert_eq]
      have hsN : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers e : Subgroup G) : Set G) :=
        mem_normalizer_sup_zpowers hfN (by
          rw [hfe]
          exact mul_mem (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers e)))
            (Subgroup.mem_sup_left (pow_mem dD.c.2 _)))
      have hs2 : f * f ∈ D ⊔ Subgroup.zpowers e := by rw [hff]; exact one_mem _
      exact ⟨fun x hx => actsBy_of_mem_tower he' hf' h21 heN he2 hsN hs2 (hRrs ▸ hx),
        fun Q hQR hQD => hQ_of_tower he' hf' h21 heN he2 hsN hs2 (hRrs ▸ hQR) hQD⟩
    · omega
  exact h.mem_normalizer_omegaIn_one (by decide) (Stroth47Core.t200_one_le_k le_rfl)
    (Stroth310T200.uv_not_mem dD le_rfl) h226 hD (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) key.1 key.2 hgN

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t201_one {m : ℕ} (hm : m = 1)
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t201 m).m = (StrothTypeIndex.t201 m).n)
    (h34 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨ Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2))
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  subst hm
  have hD : Nat.card D = 128 := by rw [Stroth310T201.card_D dD]; norm_num
  have hinv : ∀ b : Fin 4, ∀ v, diag4 (StrothTypeIndex.t201 1).k b
      (diag4 (StrothTypeIndex.t201 1).k b v) = v := by decide +kernel
  have hRN : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      x ∈ Subgroup.normalizer (D : Set G) := fun x hx => (Subgroup.mem_inf.mp hx).1.2
  have key : (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∃ a, ActsBy dD x a) ∧
      (∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
        ∃ q ∈ Q, ∃ b : Fin 4, ActsBy dD q b ∧
          ((b = 1 ∧ D.relIndex Q ≤ 2) ∨ ((b = 2 ∨ b = 3) ∧ D.relIndex Q ≤ 4))) := by
    rcases h34 with hRD | ⟨e, heR, hRe, hshape⟩
    · exact ⟨fun x hx => ⟨0, actsBy_of_mem dD (hRD ▸ hx)⟩,
        fun Q hQR hQD => absurd (hRD ▸ hQR) hQD⟩
    · have heN := hRN e heR
      obtain ⟨b, hb0, heb, he2⟩ : ∃ b : Fin 4, b ≠ 0 ∧ ActsBy dD e b ∧ e * e ∈ D := by
        rcases hshape with he | he | he
        · exact ⟨1, by decide, actsBy_of_rel34i rfl he (hinv 1), he.e_sq ▸ inv_mem dD.c.2⟩
        · exact ⟨2, by decide, actsBy_of_rel34inv_zero he (hinv 2),
            by rw [he.e_sq]; exact one_mem D⟩
        · exact ⟨3, by decide, actsBy_of_rel34inv_four rfl he (hinv 3),
            by rw [he.e_sq]; exact one_mem D⟩
      refine ⟨fun x hx => ?_, fun Q hQR hQD => hQ_of_sup_zpowers hb0 heb heN he2 (hRe ▸ hQR) hQD⟩
      rcases actsBy_of_mem_sup_zpowers heb heN he2 (hRe ▸ hx) with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨b, h1⟩
  exact h.mem_normalizer_omegaIn_one (by decide) (Stroth44Core.t201_one_le_k le_rfl)
    (Stroth310T201.uv_not_mem dD le_rfl) h226 hD (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) key.1 key.2 hgN

end CFSG.CGT.Stroth77
