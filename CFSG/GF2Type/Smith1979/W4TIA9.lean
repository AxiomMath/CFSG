module

public import CFSG.GF2Type.Smith1979.W4AsTI
public import CFSG.GF2Type.Smith1979.W4TIA9Perm
public import CFSG.LargeExtraspecial.GLRFusInj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
  CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] def NormTrans {A : Type*} [Group A] (L : Subgroup A) : Prop :=
  ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ normalizer (L : Set A), k * x * k⁻¹ = y

theorem NormTrans.of_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {L : Subgroup A}
    {T : Subgroup B} (hψ : L.map ψ.toMonoidHom = T)
    (hT : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ k ∈ normalizer (T : Set B), k * x * k⁻¹ = y) :
    NormTrans L := by
  intro x hx hx1 y hy hy1
  have hψx : ψ x ∈ T := hψ ▸ ⟨x, hx, rfl⟩
  have hψy : ψ y ∈ T := hψ ▸ ⟨y, hy, rfl⟩
  obtain ⟨k', hk', hk'e⟩ := hT (ψ x) hψx (fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm)))
    (ψ y) hψy (fun h => hy1 (ψ.injective (h.trans (map_one ψ).symm)))
  refine ⟨ψ.symm k', ?_, ?_⟩
  · have hN := Subgroup.map_equiv_normalizer_eq L ψ
    rw [hψ] at hN
    rw [← hN] at hk'
    obtain ⟨k, hk, hkk⟩ := hk'
    have : ψ.symm k' = k := by
      rw [← hkk]
      exact ψ.symm_apply_apply k
    rw [this]
    exact hk
  · apply ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hk'e

theorem normTrans_LM0 (hF2 : Form2StrongStmt) (H : Hyp4 S g) (C : Cons311 S g)
    (hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g)
    (hirr : ¬ S.IsReducible) : NormTrans (LM0 S g) := by
  refine (hF2 S.Mbar (LM S g) (isWC_Lbar H C hTI)).elim (fun h => absurd h.1 ?_) fun h => ?_
  · have h2n := two_mul_width_le_card_Lbar H
    have hn4 := four_le_width H C
    rw [card_Form2L (S := S) (g := g)]
    omega
  · have hz : Subgroup.center (Form2Q S.Mbar (LM S g)) = ⊥ := by
      by_contra hz
      exact hirr (isReducible_of_center_Form2Q_ne_bot H hz)
    obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Form2Q hz
    exact NormTrans.of_mulEquiv ψ hψ h.2.2.2.2.2.1

theorem mem_normalizer_LM_iff (x : S.Mbar) :
    x ∈ normalizer (LM S g : Set S.Mbar) ↔ (x : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
  have hL := S.Lbar_le_Mbar g
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      have h1 := (h ⟨y, hL hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
    · intro hy
      have hyM : y ∈ S.Mbar := by
        have h2 : (x : S.O) * y * (x : S.O)⁻¹ ∈ S.Mbar := hL hy
        have h3 : (x : S.O)⁻¹ * ((x : S.O) * y * (x : S.O)⁻¹) * (x : S.O) ∈ S.Mbar :=
          S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem x.2) h2) x.2
        simpa [mul_assoc] using h3
      exact mem_subgroupOf.mp ((h ⟨y, hyM⟩).mpr (mem_subgroupOf.mpr hy))
  · intro h y
    rw [mem_subgroupOf, mem_subgroupOf]
    exact h y

theorem index_normalizer_LM_le (H : Hyp4 S g) (hw : S.width = 4) :
    (normalizer (LM S g : Set S.Mbar)).index ≤ 255 := by
  classical
  set a : S.Qt := S.cl (g * S.z * g⁻¹) with ha
  have hsmul : ∀ (x : S.Mbar) (v : S.Qt), x • v = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
    fun _ _ => rfl
  have hstab : normalizer (LM S g : Set S.Mbar) = MulAction.stabilizer S.Mbar a := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_normalizer_LM_iff]
    obtain ⟨m, hm⟩ := x.2
    rw [← hm]
    exact S.timmesfeld_12_4_1 H.conj_mem H.conj_ne (by omega) m
  rw [hstab, MulAction.index_stabilizer]
  have ha0 : a ≠ 0 := S4.cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hne : ∀ v : MulAction.orbit S.Mbar a, (v : S.Qt) ≠ 0 := by
    rintro ⟨_, x, rfl⟩ h
    exact ha0 ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hinj : Function.Injective
      (fun o : Option (MulAction.orbit S.Mbar a) => o.elim (0 : S.Qt) (fun x => (x : S.Qt))) := by
    intro o₁ o₂ h
    rcases o₁ with _ | x₁ <;> rcases o₂ with _ | x₂
    · rfl
    · exact absurd h.symm (hne x₂)
    · exact absurd h (hne x₁)
    · exact congrArg some (Subtype.ext h)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option, S.card_Qt, S.finrank_Qt_eq_two_mul_width, hw] at hle
  rw [← Nat.card_coe_set_eq]
  omega

@[expose] noncomputable def autPerm9 {K₀ : Type*} [Group K₀] (e : K₀ ≃* alternatingGroup (Fin 9)) :
    MulAut K₀ ≃* Equiv.Perm (Fin 9) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num))).symm

theorem autPerm9_conj {K₀ : Type*} [Group K₀] (e : K₀ ≃* alternatingGroup (Fin 9)) (k : K₀) :
    autPerm9 e (MulAut.conj k) = ((e k : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) := by
  unfold autPerm9
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  ext a i
  simp [MulAut.congr_apply, MulAut.conjNormal_apply]

theorem card_fixedBy_conj (σ x : Equiv.Perm (Fin 9)) :
    Fintype.card (MulAction.fixedBy (Fin 9) (σ * x * σ⁻¹)) =
      Fintype.card (MulAction.fixedBy (Fin 9) x) := by
  classical
  refine Fintype.card_congr
    { toFun := fun p => ⟨σ⁻¹ p, ?_⟩
      invFun := fun q => ⟨σ q, ?_⟩
      left_inv := fun p => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp) }
  · have hp : (σ * x * σ⁻¹) p = p := p.2
    change x (σ⁻¹ p) = σ⁻¹ p
    have h := congrArg (fun q => σ⁻¹ q) hp
    simpa [Equiv.Perm.mul_apply] using h
  · have hq : x q = q := q.2
    change (σ * x * σ⁻¹) (σ q) = σ q
    simp [Equiv.Perm.mul_apply, hq]

theorem conj_of_normTrans_subgroupOf {M : Type*} [Group M] {K L : Subgroup M} (hLK : L ≤ K)
    (h : NormTrans (L.subgroupOf K)) :
    ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k : M, k * x * k⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨k, -, hk⟩ := h ⟨x, hLK hx⟩ (mem_subgroupOf.mpr hx)
    (fun e => hx1 (congrArg Subtype.val e)) ⟨y, hLK hy⟩ (mem_subgroupOf.mpr hy)
    (fun e => hy1 (congrArg Subtype.val e))
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem le_index_normalizer_map {M : Type*} [Group M] (κ : M →* Equiv.Perm (Fin 9))
    (hκ : Function.Injective κ) {L : Subgroup M} (hL8 : Nat.card L = 8)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) (hsq : ∀ t ∈ L, t * t = 1)
    (hconj : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k : M, k * x * k⁻¹ = y) :
    270 ≤ (normalizer ((L.map κ : Subgroup (Equiv.Perm (Fin 9))) : Set (Equiv.Perm (Fin 9)))).index := by
  classical
  have hT8 : Nat.card (L.map κ) = 8 := by rw [Subgroup.card_map_of_injective hκ, hL8]
  have hTc : ∀ a ∈ L.map κ, ∀ b ∈ L.map κ, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hTs : ∀ t ∈ L.map κ, t * t = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  have hTconj : ∀ x ∈ L.map κ, x ≠ 1 → ∀ y ∈ L.map κ, y ≠ 1 →
      ∃ σ : Equiv.Perm (Fin 9), σ * x * σ⁻¹ = y := by
    rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨y, hy, rfl⟩ hy1
    obtain ⟨k, hk⟩ := hconj x hx (fun e => hx1 (by rw [e, map_one])) y hy
      (fun e => hy1 (by rw [e, map_one]))
    exact ⟨κ k, by rw [← map_inv, ← map_mul, ← map_mul, hk]⟩
  obtain ⟨t₀, ht₀T, ht₀⟩ : ∃ t ∈ L.map κ, t ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : L.map κ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hT8
    omega
  have hf : ∀ t ∈ L.map κ, t ≠ 1 →
      Fintype.card (MulAction.fixedBy (Fin 9) t) = Fintype.card (MulAction.fixedBy (Fin 9) t₀) := by
    intro t htT ht1
    obtain ⟨σ, hσ⟩ := hTconj t₀ ht₀T ht₀ t htT ht1
    rw [← hσ, card_fixedBy_conj]
  exact le_index_normalizer hT8 hTc hTs hf

theorem card_eq_of_le_range {M : Type*} [Group M] (κ : M →* Equiv.Perm (Fin 9))
    (hκ : Function.Injective κ) {L : Subgroup M} (hL8 : Nat.card L = 8)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a) (hsq : ∀ t ∈ L, t * t = 1)
    (hconj : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k : M, k * x * k⁻¹ = y)
    (hidx : (normalizer (L : Set M)).index ≤ 255) (hA9 : alternatingGroup (Fin 9) ≤ κ.range) :
    Nat.card M = 181440 := by
  classical
  have h270 := le_index_normalizer_map κ hκ hL8 hcomm hsq hconj
  have hns : κ.range ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective κ := MonoidHom.range_eq_top.mp htop
    let κe : M ≃* Equiv.Perm (Fin 9) := MulEquiv.ofBijective κ ⟨hκ, hsurj⟩
    have hN := Subgroup.map_equiv_normalizer_eq L κe
    have hidx' : (normalizer ((L.map κe.toMonoidHom : Subgroup _) : Set (Equiv.Perm (Fin 9)))).index =
        (normalizer (L : Set M)).index := by
      rw [← hN]
      exact Subgroup.index_map_equiv _ κe
    have hmap : L.map κe.toMonoidHom = L.map κ := rfl
    rw [hmap] at hidx'
    omega
  have hA9card : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hS9card : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h1 : 181440 ∣ Nat.card κ.range := hA9card ▸ Subgroup.card_dvd_of_le hA9
  have h2 : Nat.card κ.range ∣ 362880 := hS9card ▸ Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card κ.range ≠ 362880 := fun h =>
    hns ((Subgroup.card_eq_iff_eq_top _).mp (h.trans hS9card.symm))
  have hrange : Nat.card κ.range = 181440 := by
    obtain ⟨c, hc⟩ := h1
    have hpos : 0 < Nat.card κ.range := Nat.card_pos
    rw [hc] at h2 h3 hpos
    have hc2 : c ∣ 2 := by
      have : 181440 * c ∣ 181440 * 2 := by simpa using h2
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with rfl | rfl
    · rw [hc]
    · exact absurd rfl h3
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hκ).toEquiv

theorem eq_top_of_A9 {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (e : K ≃* alternatingGroup (Fin 9))
    (hinj : Function.Injective (MulAut.conjNormal : X →* MulAut K)) {L : Subgroup X}
    (hLK : L ≤ K) (hL8 : Nat.card L = 8) (hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hsq : ∀ t ∈ L, t * t = 1) (htr : NormTrans (L.subgroupOf K))
    (hidx : (normalizer (L : Set X)).index ≤ 255) : K = ⊤ := by
  have hκi : Function.Injective ((autPerm9 e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)) :=
    (autPerm9 e).injective.comp hinj
  have hA9 : alternatingGroup (Fin 9) ≤
      ((autPerm9 e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)).range := by
    intro σ hσ
    refine ⟨((e.symm ⟨σ, hσ⟩ : K) : X), ?_⟩
    change autPerm9 e (MulAut.conjNormal ((e.symm ⟨σ, hσ⟩ : K) : X)) = σ
    rw [MulAut.conjNormal_val, autPerm9_conj, MulEquiv.apply_symm_apply]
  have hcard := card_eq_of_le_range _ hκi hL8 hcomm hsq (conj_of_normTrans_subgroupOf hLK htr)
    hidx hA9
  have hA9card : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  haveI : Finite K := Finite.of_equiv _ e.symm.toEquiv
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [hcard, Nat.card_congr e.toEquiv, hA9card]

theorem M0_eq_top_of_A9 (H : Hyp4 S g) (C : Cons311 S g) (hirr : ¬ S.IsReducible)
    (hw : S.width = 4) (htr : NormTrans (LM0 S g)) (e : M0 S g ≃* alternatingGroup (Fin 9)) :
    M0 S g = ⊤ := by
  have haQ := H.conj_mem
  have hL8 : Nat.card (LM S g) = 8 := by
    have h1 : Nat.card (LM S g) = Nat.card (S.Lbar g) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv
    rw [h1, C.card_Lbar, hw]
    norm_num
  exact eq_top_of_A9 e (injective_conjNormal_M0 H hirr) LM_le_M0 hL8
    (fun a ha b hb => Subtype.ext (GLR.Lbar_comm haQ (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb)))
    (fun t ht => Subtype.ext (GLR.Lbar_mul_self haQ (mem_subgroupOf.mp ht))) htr
    (index_normalizer_LM_le H hw)

end CFSG.GF2Type.Smith1979.W4As
