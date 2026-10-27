module

public import CFSG.GH74.GLS.IVK.Proofs2.SylowCommute
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.Prod.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma31iSylow

open Subgroup CFSG.GH74.GLS.IVK

theorem inf_le_of_card_eq {G : Type*} [Group G] [Finite G] {A B S : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : Nat.card ↥(A ⊓ B) = 2)
    (hSA : S ≤ A) (hS : Nat.card S = 2 ^ (Nat.card A).factorization 2) : A ⊓ B ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSc : Nat.card (S.subgroupOf A) = 2 ^ (Nat.card A).factorization 2 := by
    rw [← hS]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv
  let P : Sylow 2 A := Sylow.ofCard (S.subgroupOf A) hSc
  have hN : ((A ⊓ B).subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnB : (n : G) ∈ B := (Subgroup.mem_inf.1 hn).2
    have hc : (g : G) * n = n * g := hcomm g g.2 n hnB
    show (g : G) * n * (g : G)⁻¹ ∈ A ⊓ B
    have : (g : G) * n * (g : G)⁻¹ = n := by rw [hc]; group
    rw [this]
    exact hn
  have hNp : IsPGroup 2 ((A ⊓ B).subgroupOf A) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv, hAB]
    norm_num
  intro w hw
  have hwA : w ∈ A := (Subgroup.mem_inf.1 hw).1
  have h1 : (⟨w, hwA⟩ : A) ∈ (P : Subgroup A) := hNp.le_sylow_of_normal P hw
  exact h1

theorem factorization_card_sup_two {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : Nat.card ↥(A ⊓ B) = 2) :
    (Nat.card ↥(A ⊔ B)).factorization 2 + 1 =
      (Nat.card A).factorization 2 + (Nat.card B).factorization 2 := by
  have h := (SylowCommute.card_sup_mul_card_inf A B hcomm).1
  have h2 := congrArg (fun n => n.factorization 2) h
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', hAB] at h2
  simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h2
  omega

theorem sylow_inf_decomp_two {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : Nat.card ↥(A ⊓ B) = 2)
    {X : Subgroup G} (hXK : X ≤ A ⊔ B)
    (hX : Nat.card X = 2 ^ (Nat.card ↥(A ⊔ B)).factorization 2) :
    Nat.card ↥(X ⊓ A) = 2 ^ (Nat.card A).factorization 2 ∧
    Nat.card ↥(X ⊓ B) = 2 ^ (Nat.card B).factorization 2 ∧ A ⊓ B ≤ X ∧
    ∀ x ∈ X, ∃ a ∈ X ⊓ A, ∃ b ∈ X ⊓ B, x = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨SA, hSA, hSAc⟩ := SylowCommute.exists_le_card_eq (p := 2) A
  obtain ⟨SB, hSB, hSBc⟩ := SylowCommute.exists_le_card_eq (p := 2) B
  have hcSAB : ∀ x ∈ SA, ∀ y ∈ SB, x * y = y * x := fun x hx y hy =>
    hcomm x (hSA hx) y (hSB hy)
  have hNA : A ⊓ B ≤ SA := inf_le_of_card_eq hcomm hAB hSA hSAc
  have hNB : A ⊓ B ≤ SB := by
    have := inf_le_of_card_eq (A := B) (B := A) (fun b hb a ha => (hcomm a ha b hb).symm)
      (by rw [inf_comm]; exact hAB) hSB hSBc
    rwa [inf_comm]
  have hSS : SA ⊓ SB = A ⊓ B := le_antisymm (inf_le_inf hSA hSB) (le_inf hNA hNB)
  have hone : Nat.card ↥(SA ⊓ SB) = 2 := by rw [hSS]; exact hAB
  obtain ⟨hTcard, hTmem⟩ := SylowCommute.card_sup_mul_card_inf SA SB hcSAB
  have hfac := factorization_card_sup_two hcomm hAB
  have hTc : Nat.card ↥(SA ⊔ SB) = 2 ^ (Nat.card ↥(A ⊔ B)).factorization 2 := by
    rw [hone, hSAc, hSBc, ← pow_add, ← hfac, pow_succ] at hTcard
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hTcard
  obtain ⟨g, hgK, hg⟩ :=
    SylowCommute.exists_conj_of_card_eq (p := 2) (sup_le_sup hSA hSB) hXK hTc hX
  obtain ⟨a₀, ha₀, b₀, hb₀, hg0⟩ :=
    ((SylowCommute.card_sup_mul_card_inf A B hcomm).2 g).1 hgK
  have hconjA : ∀ s ∈ SA, g * s * g⁻¹ = a₀ * s * a₀⁻¹ := by
    intro s hs
    have hc : b₀ * s = s * b₀ := (hcomm s (hSA hs) b₀ hb₀).symm
    rw [hg0]
    calc a₀ * b₀ * s * (a₀ * b₀)⁻¹ = a₀ * (b₀ * s) * b₀⁻¹ * a₀⁻¹ := by group
      _ = a₀ * (s * b₀) * b₀⁻¹ * a₀⁻¹ := by rw [hc]
      _ = a₀ * s * a₀⁻¹ := by group
  have hA : ∀ s ∈ SA, g * s * g⁻¹ ∈ X ⊓ A := by
    intro s hs
    have hmemA : g * s * g⁻¹ ∈ A := by
      rw [hconjA s hs]
      exact mul_mem (mul_mem ha₀ (hSA hs)) (inv_mem ha₀)
    exact Subgroup.mem_inf.2 ⟨(hg _).2 ⟨s, Subgroup.mem_sup_left hs, rfl⟩, hmemA⟩
  have hB : ∀ s ∈ SB, g * s * g⁻¹ ∈ X ⊓ B := by
    intro s hs
    have hmem : b₀ * s * b₀⁻¹ ∈ B := mul_mem (mul_mem hb₀ (hSB hs)) (inv_mem hb₀)
    have hc : a₀ * (b₀ * s * b₀⁻¹) = (b₀ * s * b₀⁻¹) * a₀ := hcomm a₀ ha₀ _ hmem
    have hconj : g * s * g⁻¹ = b₀ * s * b₀⁻¹ := by
      rw [hg0]
      calc a₀ * b₀ * s * (a₀ * b₀)⁻¹ = a₀ * (b₀ * s * b₀⁻¹) * a₀⁻¹ := by group
        _ = (b₀ * s * b₀⁻¹) * a₀ * a₀⁻¹ := by rw [hc]
        _ = b₀ * s * b₀⁻¹ := by group
    have hmemB : g * s * g⁻¹ ∈ B := by
      rw [hconj]
      exact hmem
    exact Subgroup.mem_inf.2 ⟨(hg _).2 ⟨s, Subgroup.mem_sup_right hs, rfl⟩, hmemB⟩
  have hcm : ∀ S : Subgroup G, Nat.card ↥(S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
    fun S => Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hAle : SA.map (MulAut.conj g).toMonoidHom ≤ X ⊓ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hA s hs
  have hBle : SB.map (MulAut.conj g).toMonoidHom ≤ X ⊓ B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hB s hs
  refine ⟨SylowCommute.card_inf_eq hp hX hAle (by rw [hcm, hSAc]),
    SylowCommute.card_inf_eq hp hX hBle (by rw [hcm, hSBc]), ?_, ?_⟩
  · intro w hw
    have hwSA : w ∈ SA := hNA hw
    have hwB : w ∈ B := (Subgroup.mem_inf.1 hw).2
    have hfix : g * w * g⁻¹ = w := by
      rw [hconjA w hwSA, hcomm a₀ ha₀ w hwB]
      group
    have := (Subgroup.mem_inf.1 (hA w hwSA)).1
    rwa [hfix] at this
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := (hg x).1 hx
    obtain ⟨sa, hsa, sb, hsb, rfl⟩ := (hTmem t).1 ht
    exact ⟨g * sa * g⁻¹, hA sa hsa, g * sb * g⁻¹, hB sb hsb, by group⟩

theorem exists_quat_of_sylow {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card F)) {P : Subgroup X}
    (hP : Nat.card P = 2 ^ (Nat.card X).factorization 2) :
    ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (m - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := Sylow.ofCard P hP
  let S' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨m, hm, ⟨φ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd S'
  exact ⟨m, hm, ⟨(e.subgroupMap P).trans φ⟩⟩

theorem sylow_side {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    (T : Sylow 2 H) {t : H} (ht : t ∈ (T : Subgroup H)) (htt : t * t = 1)
    (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) {n : ℕ}
    (hn : Nat.card ↥((T : Subgroup H) ⊓ K₁) * 2 = 2 ^ (n + 1)) :
    3 ≤ n ∧ z ∈ (T : Subgroup H) ∧
      Nonempty (↥((T : Subgroup H) ⊓ K₁) ≃* QuaternionGroup (2 ^ (n - 2))) ∧
      Nat.card ↥((T : Subgroup H) ⊓ (K₁ ⊔ K₂)) = 2 ^ (2 * n - 1) ∧
      ∀ x ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂),
        ∃ a ∈ (T : Subgroup H) ⊓ K₁, ∃ b ∈ (T : Subgroup H) ⊓ K₂, x = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF₁ : Finite F₁ := h.finite₁
  have hnorm : (K₁ ⊔ K₂).Normal := h.fstar_normal
  have hXcard : Nat.card ↥((T : Subgroup H) ⊓ (K₁ ⊔ K₂)) =
      2 ^ (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 := card_sylow_inf_normal 2 T (K₁ ⊔ K₂)
  obtain ⟨hc1, hc2, hzX, hdec⟩ := sylow_inf_decomp_two h.comm h.card_inter
    (inf_le_right : (T : Subgroup H) ⊓ (K₁ ⊔ K₂) ≤ K₁ ⊔ K₂) hXcard
  have e1 : (T : Subgroup H) ⊓ (K₁ ⊔ K₂) ⊓ K₁ = (T : Subgroup H) ⊓ K₁ := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, Subgroup.mem_sup_left hx.2⟩, hx.2⟩⟩
  have e2 : (T : Subgroup H) ⊓ (K₁ ⊔ K₂) ⊓ K₂ = (T : Subgroup H) ⊓ K₂ := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, Subgroup.mem_sup_right hx.2⟩, hx.2⟩⟩
  rw [e1] at hc1
  rw [e2] at hc2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcard12 : Nat.card ↥((T : Subgroup H) ⊓ K₂) = Nat.card ↥((T : Subgroup H) ⊓ K₁) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨t * x * t⁻¹, ?_⟩
        invFun := fun y => ⟨t * y * t⁻¹, ?_⟩
        left_inv := fun x => ?_
        right_inv := fun y => ?_ }
    · exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht (Subgroup.mem_inf.1 x.2).1) (inv_mem ht),
        ProdSL2.swap_mem₂ htt hK (Subgroup.mem_inf.1 x.2).2⟩
    · exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht (Subgroup.mem_inf.1 y.2).1) (inv_mem ht),
        ProdSL2.swap_mem₁ hK (Subgroup.mem_inf.1 y.2).2⟩
    · apply Subtype.ext
      show t * (t * (x : H) * t⁻¹) * t⁻¹ = x
      rw [hti]
      calc t * (t * (x : H) * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [htt]; group
    · apply Subtype.ext
      show t * (t * (y : H) * t⁻¹) * t⁻¹ = y
      rw [hti]
      calc t * (t * (y : H) * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt]; group
  have hfac := factorization_card_sup_two h.comm h.card_inter
  have hpow : ∀ a b : ℕ, 2 ^ a = 2 ^ b → a = b := fun a b hab => Nat.pow_right_injective le_rfl hab
  have hn1 : (Nat.card ↥K₁).factorization 2 = n := by
    have h1 : 2 ^ ((Nat.card ↥K₁).factorization 2 + 1) = 2 ^ (n + 1) := by
      rw [pow_succ, ← hc1]; exact hn
    have := hpow _ _ h1
    omega
  have hn2 : (Nat.card ↥K₂).factorization 2 = n := by
    have h1 : 2 ^ (Nat.card ↥K₂).factorization 2 = 2 ^ n := by
      rw [← hc2, hcard12, hc1, hn1]
    exact hpow _ _ h1
  have hK2 : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 = 2 * n - 1 := by omega
  have hzT : z ∈ (T : Subgroup H) := (Subgroup.mem_inf.1 (hzX hz)).1
  have hodd : Odd (Nat.card F₁) := by
    obtain ⟨h2, -⟩ := h.z_data₁ hz hz1
    have hF : ringChar F₁ ≠ 2 := by
      intro hc
      apply h2
      have := CharP.cast_eq_zero F₁ (ringChar F₁)
      rw [hc] at this
      exact_mod_cast this
    have : Fintype F₁ := Fintype.ofFinite F₁
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hF)
  have hle : (T : Subgroup H) ⊓ K₁ ≤ K₁ := inf_le_right
  have hPc : Nat.card ↥(((T : Subgroup H) ⊓ K₁).subgroupOf K₁) =
      2 ^ (Nat.card ↥K₁).factorization 2 := by
    rw [← hc1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  obtain ⟨m, hm3, ⟨φ⟩⟩ :=
    exists_quat_of_sylow h.slEquiv₁ hodd (P := ((T : Subgroup H) ⊓ K₁).subgroupOf K₁) hPc
  have e3 : ↥((T : Subgroup H) ⊓ K₁) ≃* QuaternionGroup (2 ^ (m - 2)) :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans φ
  have hmn : m = n := by
    have h1 : Nat.card ↥((T : Subgroup H) ⊓ K₁) = 4 * 2 ^ (m - 2) := by
      rw [Nat.card_congr e3.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h2 : 2 ^ n = 2 ^ m := by
      have h3 : 4 * 2 ^ (m - 2) = 2 ^ m := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        rw [Nat.add_sub_cancel, pow_add]
        ring
      rw [← h3, ← h1, hc1, hn1]
    exact (hpow _ _ h2).symm
  subst hmn
  refine ⟨hm3, hzT, ⟨e3⟩, ?_, ?_⟩
  · rw [hXcard, hK2]
  · intro x hx
    have := hdec x hx
    rwa [e1, e2] at this

end CFSG.GH74.GLS.IVK.Proofs2.Lemma31iSylow
