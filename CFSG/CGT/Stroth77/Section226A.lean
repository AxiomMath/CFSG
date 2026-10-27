module

public import CFSG.CGT.Stroth76.FrameLemma7
public import CFSG.CGT.Stroth77.Section224A
public import CFSG.CGT.Stroth77.Section310CharBA
public import CFSG.CGT.Stroth77.Section41

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem false_of_relIndex_mul_card_lt {D B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcard : Nat.card B = Nat.card D) {x : G} (hx : x ∈ B) {k : ℕ} (hk : D.relIndex B ≤ k)
    (hlt : k * Nat.card ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) < Nat.card D) : False := by
  have hle : D ⊓ B ≤ D ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr (hB y hy.2 x hx)⟩
  have h1 := Subgroup.relIndex_mul_card D B
  have h2 := Subgroup.card_le_of_le hle
  have h3 : D.relIndex B * Nat.card ↥(D ⊓ B) ≤ k * Nat.card ↥(D ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.mul_le_mul hk h2
  omega

namespace StrothFrame

variable {F : StrothFrame G}

theorem sup_closure_le_normalizer_E (F : StrothFrame G) :
    F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤ Subgroup.normalizer (F.E : Set G) := by
  refine sup_le F.A_le ((Subgroup.closure_le _).mpr ?_)
  rintro x (rfl | rfl | rfl)
  · exact F.L_le F.dA.uv_mem_L
  · exact F.L_le F.dA.t_mem_L
  · exact F.L_le F.dA.u_mem_L

theorem conj_eq_inv_of_inverts (F : StrothFrame G) {s : G}
    (hsc : s⁻¹ * (F.dA.c : G) * s = F.dA.c) (hsa : s⁻¹ * (F.dA.a : G) * s = (F.dA.a : G)⁻¹)
    (hsb : s⁻¹ * (F.dA.b : G) * s = (F.dA.b : G)⁻¹) {d : G} (hd : d ∈ F.A) :
    s⁻¹ * d * s = d⁻¹ := by
  have hcomm : ∀ x ∈ F.A, ∀ y ∈ F.A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (F.dA.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc2 : (F.dA.c : G) * F.dA.c = 1 := by rw [← pow_two]; exact F.dA.pow_two_c
  rw [← F.dA.closure_c_a_b_of_zpow] at hd
  induction hd using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hsc]; exact (inv_eq_of_mul_eq_one_right hc2).symm
    · exact hsa
    · exact hsb
  | one => simp
  | mul y z hy hz ihy ihz =>
    rw [F.dA.closure_c_a_b_of_zpow] at hy hz
    calc s⁻¹ * (y * z) * s = (s⁻¹ * y * s) * (s⁻¹ * z * s) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by rw [hcomm y hy z hz, mul_inv_rev]
  | inv y hy ihy =>
    calc s⁻¹ * y⁻¹ * s = (s⁻¹ * y * s)⁻¹ := by group
      _ = y⁻¹⁻¹ := by rw [ihy]

namespace IsD

variable {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem false_of_le_R_of_card_le (h : F.IsD D dD) (hD : Nat.card D ≤ 32) {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : Nat.card B = Nat.card D) (hne : B ≠ D) :
    False := by
  have hDA : F.A = D :=
    Subgroup.eq_of_le_of_card_ge h.A_le (by rw [F.dA.card_eq_32]; exact hD)
  have hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A := by
    rw [inf_comm, hDA]
    exact h.cent
  have hBS : ∀ x ∈ B, x ∈ (F.S : Subgroup G) := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hBR hx)).1).1
  have hBC : ∀ x ∈ B, x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (hBR hx)).2
  have hBD : ¬ B ≤ D := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  obtain ⟨x, hxB, hxD⟩ := SetLike.not_le_iff_exists.mp hBD
  have hT := F.sup_closure_le_normalizer_E
  rcases F.arch76Lemma2 hCA with hS | ⟨s, hsS, hSeq, hs2, hsc, hsa, hsb, hrel⟩
  ·
    exact hxD (h.mem_of_mem_normalizer_E (hBS x hxB) (hBC x hxB)
      (hT (hS ▸ hBS x hxB)))
  ·
    set T : Subgroup G := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hTdef
    have hinv : ∀ d ∈ F.A, s⁻¹ * d * s = d⁻¹ := fun d hd =>
      F.conj_eq_inv_of_inverts hsc hsa hsb hd
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hsNA : s ∈ Subgroup.normalizer (F.A : Set G) := F.le_normalizer_A hCA hsS
    have hsT : ∀ y ∈ T, s * y * s⁻¹ ∈ T := by
      have hle : T ≤ T.comap (MulAut.conj s).toMonoidHom := by
        refine sup_le (fun y hy => ?_) ((Subgroup.closure_le _).mpr ?_)
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hsNA y).mp hy)
        · have hA : ∀ a ∈ F.A, ∀ l ∈ Subgroup.closure ({F.dA.uv, F.dA.t, F.dA.u} : Set G),
              a * l ∈ T := fun a ha l hl =>
            T.mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hl)
          have hl : ∀ l ∈ ({F.dA.uv, F.dA.t, F.dA.u} : Set G),
              l ∈ Subgroup.closure ({F.dA.uv, F.dA.t, F.dA.u} : Set G) :=
            fun l hl => Subgroup.subset_closure hl
          rintro y (rfl | rfl | rfl) <;>
            simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
              MulAut.conj_apply, SetLike.mem_coe] <;> rw [← hs1, inv_inv]
          · rcases hrel with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> rw [h1]
            · exact hA _ (mul_mem (inv_mem F.dA.a.2) (inv_mem F.dA.b.2)) _ (hl _ (by simp))
            · exact hA _ (mul_mem F.dA.a.2 (inv_mem F.dA.b.2)) _ (hl _ (by simp))
          · rcases hrel with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> rw [h1]
            · exact hA _ F.dA.a.2 _ (hl _ (by simp))
            · exact hA _ (mul_mem F.dA.a.2 (pow_mem F.dA.b.2 2)) _ (hl _ (by simp))
          · rcases hrel with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1]
            · exact Subgroup.mem_sup_right (hl _ (by simp))
            · exact hA _ F.dA.c.2 _ (hl _ (by simp))
      exact fun y hy => hle hy
    have hsNT : s ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hsT y hy, fun hy => ?_⟩
      have := hsT _ hy
      rwa [show s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s * s)⁻¹ by group, hs2, one_mul,
        inv_one, mul_one] at this
    have hST : (F.S : Subgroup G) = T ⊔ Subgroup.zpowers s := by
      rw [hSeq, Stroth76.closure_insert_four_eq, ← Subgroup.zpowers_eq_closure, hTdef, sup_assoc]
    have hcommD : IsMulCommutative D := dD.isMulCommutative
    have hsΩ : s⁻¹ ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hwD, hw2⟩ := (mem_omegaIn_one_iff hcommD).mp hw
      have h3 := hinv w (hDA ▸ hwD)
      rw [hs1] at h3 ⊢
      calc w * s = s * (s * w * s) := by rw [← mul_assoc, ← mul_assoc, hs2, one_mul]
        _ = s * w := by rw [h3, inv_eq_of_mul_eq_one_right hw2]
    have hBsplit : ∀ y ∈ B, y ∈ D ∨ s⁻¹ * y ∈ D := by
      intro y hy
      have hyS := hBS y hy
      rw [hST] at hyS
      rcases mem_or_inv_mul_mem_of_mem_sup_zpowers hsNT (by rw [hs2]; exact one_mem _) hyS with
        hyT | hyT
      · exact Or.inl (h.mem_of_mem_normalizer_E (hBS y hy) (hBC y hy) (hT hyT))
      · exact Or.inr (h.mem_of_mem_normalizer_E (mul_mem (inv_mem hsS) (hBS y hy))
          (mul_mem hsΩ (hBC y hy)) (hT hyT))
    have hBle : B ≤ D ⊔ Subgroup.zpowers s := by
      intro y hy
      rcases hBsplit y hy with h1 | h1
      · exact Subgroup.mem_sup_left h1
      · rw [show y = s * (s⁻¹ * y) by group]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)) (Subgroup.mem_sup_left h1)
    have hsND : s ∈ Subgroup.normalizer (D : Set G) := hDA ▸ hsNA
    have hidx : D.relIndex B ≤ 2 :=
      relIndex_le_two_of_le_sup_zpowers hsND (by rw [hs2]; exact one_mem _) hBle
    have hx0 : s⁻¹ * x ∈ D := (hBsplit x hxB).resolve_left hxD
    have hCx : D ⊓ Subgroup.centralizer ({x} : Set G) ≤ omegaIn 1 D := by
      rintro d ⟨hdD, hdx⟩
      have hdx' : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.mp hdx
      have ha0 : (s⁻¹ * x) * d = d * (s⁻¹ * x) :=
        congrArg Subtype.val (hcommD.is_comm.comm ⟨_, hx0⟩ ⟨d, hdD⟩)
      have hsd : s * d = d * s := by
        refine mul_right_cancel (b := s⁻¹ * x) ?_
        calc s * d * (s⁻¹ * x) = s * ((s⁻¹ * x) * d) := by rw [ha0]; group
          _ = x * d := by group
          _ = d * x := hdx'.symm
          _ = d * s * (s⁻¹ * x) := by group
      have hdinv := hinv d (hDA ▸ hdD)
      have hdd : d * d = 1 := by
        have e1 : s⁻¹ * d * s = d := by rw [mul_assoc, ← hsd]; group
        rw [e1] at hdinv
        calc d * d = d * d⁻¹ := by rw [← hdinv]
          _ = 1 := mul_inv_cancel d
      exact (mem_omegaIn_one_iff hcommD).mpr ⟨hdD, hdd⟩
    have hΩ8 : Nat.card ↥(omegaIn 1 D) = 8 := by rw [← hDA]; exact F.card_omegaIn_one_A
    have hD32 : Nat.card D = 32 := by rw [← hDA]; exact F.dA.card_eq_32
    have hle8 := Subgroup.card_le_of_le hCx
    exact false_of_relIndex_mul_card_lt hB hcard hxB hidx (by omega)

end IsD

end StrothFrame

end CFSG.CGT.Stroth77
