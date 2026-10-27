module

public import CFSG.Quasithin.H13.L32AL2k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2i

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem exists_model_F4 (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (π : TensorG2 F →* ↥(X.img (conjClosure K T)))
      (β : Hat V (A6.g1 T V) W ≃* TensorE2 F), X.IsModel π β := by
  obtain ⟨F, fF, finF, hF, π, β, hπ, hd⟩ :=
    exists_tensorData2 (X.omega4_F4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334)
  exact ⟨F, fF, finF, π, β, hπ, hd, by rw [hF]; norm_num⟩

variable {X}

section Ident

variable {F : Type} [Field F] [Finite F] {π : TensorG2 F →* ↥(X.img (conjClosure K T))}
  {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}

theorem img_K_inf_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    X.img K ⊓ X.img (K.map (MulAut.conj t₀ : G →* G)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have h1 := (Subgroup.mem_inf.mp hy).1
  have h2 := (Subgroup.mem_inf.mp hy).2
  rw [img_eq_map] at h1 h2
  obtain ⟨k, hk, rfl⟩ := h1
  obtain ⟨k', hk', hkk'⟩ := h2
  rw [hinj hkk'] at hk'
  rw [X.C.eq_one_of_mem_kb_kt hA37 hk hk', map_one]
  exact one_mem _

theorem nonempty_equiv_img_Kt_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Nonempty (↥(X.img (K.map (MulAut.conj t₀ : G →* G))) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  rw [img_Kt_eq]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulEquiv.injective _)).symm.trans φ⟩

theorem IsModel.factors_F4 (Y : X.IsModel π β) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    (X.img K = leftImg π ∧ X.img (K.map (MulAut.conj t₀ : G →* G)) = rightImg π) ∨
      (X.img K = rightImg π ∧ X.img (K.map (MulAut.conj t₀ : G →* G)) = leftImg π) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨φ'⟩ := X.nonempty_equiv_img_Kt_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨hs, hc, hnc⟩ := props_of_equiv φ
  obtain ⟨hs', hc', hnc'⟩ := props_of_equiv φ'
  have hinf := X.img_K_inf_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure X.C.ht₀ hk
  have hle : X.img K ≤ X.img (conjClosure K T) :=
    Subgroup.map_mono fun x hx => le_conjClosure K T hx
  have hle' : X.img (K.map (MulAut.conj t₀ : G →* G)) ≤ X.img (conjClosure K T) :=
    Subgroup.map_mono fun x hx => hKt hx
  have hnormL : X.img (conjClosure K T) ≤
      Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
    rw [img_K₀_eq]
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← X.img_K_comm hA37 ha hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have h2 := X.img_K_comm hA37 ha (inv_mem hb)
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← h2]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  have hnormLt : X.img (conjClosure K T) ≤ Subgroup.normalizer
      (X.img (K.map (MulAut.conj t₀ : G →* G)) : Set (MulAut (Hat V (A6.g1 T V) W))) := by
    rw [img_K₀_eq]
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [X.img_K_comm hA37 ha hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h2 := X.img_K_comm hA37 (inv_mem ha) hb
      have e : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h2]
          _ = a * b * a⁻¹ := by group
      rw [e]
      exact hb
  have hn1 : ∀ m ∈ X.img (conjClosure K T), ∀ n ∈ X.img K, m * n * m⁻¹ ∈ X.img K :=
    fun m hm n hn => (Subgroup.mem_normalizer_iff.mp (hnormL hm) n).mp hn
  have hn2 : ∀ m ∈ X.img (conjClosure K T), ∀ n ∈ X.img (K.map (MulAut.conj t₀ : G →* G)),
      m * n * m⁻¹ ∈ X.img (K.map (MulAut.conj t₀ : G →* G)) :=
    fun m hm n hn => (Subgroup.mem_normalizer_iff.mp (hnormLt hm) n).mp hn
  have hne : X.img K ≠ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
    intro h
    rw [← h, inf_idem] at hinf
    have : Nat.card (X.img K) = 1 := by rw [hinf]; exact Subgroup.card_bot
    omega
  rcases Y.eq_left_or_right hle hn1 hnc hc with h1 | h1 <;>
    rcases Y.eq_left_or_right hle' hn2 hnc' hc' with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Ident

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
