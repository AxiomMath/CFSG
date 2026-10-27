module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup Matrix CFSG.Open
open scoped commutatorElement

theorem u3_center_SL2_eq_bot (F : Type*) [Field F] [CharP F 2] :
    center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  rw [mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

noncomputable def u3SL2EquivPSL2 (F : Type*) [Field F] [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (u3_center_SL2_eq_bot F).symm)

theorem u3_isSimpleGroup_SL2 (F : Type*) [Field F] [CharP F 2] (h4 : ∃ s : Finset F, s.card = 4) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4)).2.1
  exact (u3SL2EquivPSL2 F).isSimpleGroup

theorem u3_even_card_SL2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Even (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  set x := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F)
    with hx
  have hx2 : x ^ 2 = 1 := by
    rw [hx, sq, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hx1 : x ≠ 1 := by
    intro h
    have h' := congrArg
      (fun y : Matrix.SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [hx, Matrix.SpecialLinearGroup.transvection_coe] at h'
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) F) := inferInstance
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have h := _root_.orderOf_dvd_natCard x
  rw [hord] at h
  exact even_iff_two_dvd.mpr h

theorem nonempty_SL2_equiv_galois (F : Type*) [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : f ≠ 0) (hF : Nat.card F = 2 ^ f) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 f)) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hc : Fintype.card F = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 f hf]
  let e : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hc
  let s : Matrix.SpecialLinearGroup (Fin 2) F ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
      (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
      (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
      (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
  exact ⟨s.trans (u3SL2EquivPSL2 (GaloisField 2 f))⟩

noncomputable def quotCenterEquivOfSurjective {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center X) (hY : center Y = ⊥) :
    X ⧸ center X ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (le_antisymm (fun z hz => by
      rw [MonoidHom.mem_ker, ← mem_bot, ← hY, mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) x]) hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem nonempty_quotCenter_map_equiv {H : Type*} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] (hN : Odd (Nat.card N)) {X : Subgroup H} (hX : IsSimpleGroup (X ⧸ center X))
    (hXZ : center (X ⧸ center X) = ⊥) (heven : Even (Nat.card (X ⧸ center X))) :
    Nonempty (X ⧸ center X ≃*
      ↥(X.map (QuotientGroup.mk' N)) ⧸ center ↥(X.map (QuotientGroup.mk' N))) := by
  set π := QuotientGroup.mk' N
  set Y := X.map π
  set φ : X →* Y := π.subgroupMap X
  have hφ : Function.Surjective φ := π.subgroupMap_surjective X
  set ψ := (QuotientGroup.mk' (center Y)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hkerφ : φ.ker ≤ center X := by
    set ρ := QuotientGroup.mk' (center X)
    have hn : (φ.ker.map ρ).Normal := (φ.normal_ker).map ρ (QuotientGroup.mk'_surjective _)
    have : IsSimpleGroup (X ⧸ center X) := hX
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map ρ) with hb | ht
    · intro x hx
      have : ρ x ∈ φ.ker.map ρ := ⟨x, hx, rfl⟩
      rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      have hmemN : ∀ x : φ.ker, ((x : X) : H) ∈ N := fun x => by
        have h' : π ((x : X) : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
      let ι : φ.ker →* N :=
        { toFun := fun x => ⟨((x : X) : H), hmemN x⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hinj : Function.Injective ι := fun a b hab => by
        have h : ((a : X) : H) = ((b : X) : H) := congrArg (fun x : N => (x : H)) hab
        exact Subtype.ext (Subtype.ext h)
      have h1 : Nat.card φ.ker ∣ Nat.card N := Subgroup.card_dvd_of_injective ι hinj
      have h2 : Nat.card (φ.ker.map ρ) ∣ Nat.card φ.ker := card_map_dvd _ _
      rw [ht, card_top] at h2
      have hodd := hN.of_dvd_nat (h2.trans h1)
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hker : ψ.ker = center X := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      rw [← QuotientGroup.eq_one_iff, ← mem_bot, ← hXZ, mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center X) y
      have hc : y * x * y⁻¹ * x⁻¹ ∈ center X := by
        apply hkerφ
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          (mem_center_iff.mp hx) (φ y)]
        group
      rw [← QuotientGroup.eq_one_iff] at hc
      change QuotientGroup.mk' (center X) y * QuotientGroup.mk' (center X) x =
        QuotientGroup.mk' (center X) x * QuotientGroup.mk' (center X) y
      have hc' : QuotientGroup.mk' (center X) (y * x * y⁻¹ * x⁻¹) = 1 := hc
      simp only [map_mul, map_inv] at hc'
      calc QuotientGroup.mk' (center X) y * QuotientGroup.mk' (center X) x =
            QuotientGroup.mk' (center X) y * QuotientGroup.mk' (center X) x *
              (QuotientGroup.mk' (center X) y)⁻¹ * (QuotientGroup.mk' (center X) x)⁻¹ *
              (QuotientGroup.mk' (center X) x * QuotientGroup.mk' (center X) y) := by group
        _ = QuotientGroup.mk' (center X) x * QuotientGroup.mk' (center X) y := by
          rw [hc', one_mul]
    · intro z hz
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) x]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

noncomputable def quotCenterCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      change e x * e a = e a * e x
      rw [← map_mul, ← map_mul, (mem_center_iff.mp ha) x]
    · intro hb
      refine ⟨e.symm b, mem_center_iff.mpr fun x => e.injective ?_, by simp⟩
      rw [map_mul, map_mul, e.apply_symm_apply, (mem_center_iff.mp hb) (e x)])

theorem card_comap_of_surjective' {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (H : Subgroup B) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  have : Finite B := Finite.of_surjective f hf
  have h1 := (H.comap f).card_mul_index
  have h2 := H.card_mul_index
  have h3 : (H.comap f).index = H.index := H.index_comap_of_surjective hf
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h5 : Nat.card (A ⧸ f.ker) = Nat.card B :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hpos : 0 < (H.comap f).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (H.comap f) * (H.comap f).index = Nat.card A := h1
    _ = Nat.card B * Nat.card f.ker := by rw [h4, h5]
    _ = Nat.card H * H.index * Nat.card f.ker := by rw [h2]
    _ = Nat.card H * Nat.card f.ker * (H.comap f).index := by rw [h3]; ring

theorem nonempty_quotCenter_commutator_equiv {M P : Type*} [Group M] [Group P] (ρ : M →* P)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center M) {A J : Subgroup P}
    (hC : centralizer (A : Set P) = J ⊔ A) (hJA : ∀ x ∈ J, ∀ y ∈ A, x * y = y * x)
    (hJ : ⁅J, J⁆ = J) (hJZ : center J = ⊥) :
    Nonempty (↥⁅centralizer ((A.comap ρ : Subgroup M) : Set M),
        centralizer ((A.comap ρ : Subgroup M) : Set M)⁆ ⧸
      center ↥⁅centralizer ((A.comap ρ : Subgroup M) : Set M),
        centralizer ((A.comap ρ : Subgroup M) : Set M)⁆ ≃* J) := by
  set K := A.comap ρ
  set C := centralizer (K : Set M)
  set Q := (centralizer (A : Set P)).comap ρ
  have hAJ : A ≤ normalizer (J : Set P) := fun a ha => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun j hj => ?_)
    exact hJA j hj a ha
  have hJC : J ≤ centralizer (A : Set P) := hC ▸ le_sup_left
  have hAC : A ≤ centralizer (A : Set P) := hC ▸ le_sup_right
  have hCQ : C ≤ Q := by
    intro x hx
    rw [mem_comap, mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := hρ a
    have hk : k ∈ K := ha
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hx) k hk]
  have hcen : ∀ x ∈ Q, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ center M := by
    intro x hx k hk
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [(mem_centralizer_iff.mp hx) (ρ k) hk]
    group
  have hQQ : ⁅Q, Q⁆ ≤ C := by
    rw [commutator_le]
    intro x hx y hy
    rw [mem_centralizer_iff]
    intro k hk
    set e₁ := k * x * k⁻¹ * x⁻¹ with he₁
    set e₂ := k * y * k⁻¹ * y⁻¹ with he₂
    have hc₁ : ∀ g : M, g * e₁ = e₁ * g := mem_center_iff.mp (hcen x hx k hk)
    have hc₂ : ∀ g : M, g * e₂ = e₂ * g := mem_center_iff.mp (hcen y hy k hk)
    have hkx : k * x * k⁻¹ = x * e₁ := by
      rw [hc₁ x, he₁]
      group
    have hky : k * y * k⁻¹ = y * e₂ := by
      rw [hc₂ y, he₂]
      group
    rw [commutatorElement_def]
    calc k * (x * y * x⁻¹ * y⁻¹) =
          (k * x * k⁻¹) * (k * y * k⁻¹) * (k * x * k⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹ * k := by group
      _ = x * e₁ * (y * e₂) * (x * e₁)⁻¹ * (y * e₂)⁻¹ * k := by rw [hkx, hky]
      _ = x * (e₁ * y) * e₂ * e₁⁻¹ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * (y * e₁) * e₂ * e₁⁻¹ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by rw [hc₁ y]
      _ = x * y * (e₁ * e₂ * e₁⁻¹) * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * y * e₂ * x⁻¹ * e₂⁻¹ * y⁻¹ * k := by
          rw [show e₁ * e₂ * e₁⁻¹ = e₂ by rw [← hc₁ e₂]; group]
      _ = x * y * (e₂ * x⁻¹) * e₂⁻¹ * y⁻¹ * k := by group
      _ = x * y * (x⁻¹ * e₂) * e₂⁻¹ * y⁻¹ * k := by rw [hc₂ x⁻¹]
      _ = x * y * x⁻¹ * y⁻¹ * k := by group
  have hJAJ : ⁅J ⊔ A, J ⊔ A⁆ ≤ J := by
    rw [commutator_le]
    intro u hu v hv
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left J A hAJ,
      Set.mem_mul] at hu hv
    obtain ⟨j, hj, a, ha, rfl⟩ := hu
    obtain ⟨j', hj', a', ha', rfl⟩ := hv
    have h1 : a * j' = j' * a := (hJA j' hj' a ha).symm
    have h2 : a * a' = a' * a := (mem_centralizer_iff.mp (hAC ha')) a ha
    have h3 : a' * j = j * a' := (hJA j hj a' ha').symm
    have h4 : a' * j' = j' * a' := (hJA j' hj' a' ha').symm
    have h5 : a * j = j * a := (hJA j hj a ha).symm
    have e : ⁅j * a, j' * a'⁆ = j * j' * j⁻¹ * j'⁻¹ := by
      rw [commutatorElement_def]
      calc j * a * (j' * a') * (j * a)⁻¹ * (j' * a')⁻¹ =
            j * (a * j') * a' * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by group
        _ = j * (j' * a) * a' * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by rw [h1]
        _ = j * j' * (a * a') * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by group
        _ = j * j' * (a' * a) * a⁻¹ * j⁻¹ * a'⁻¹ * j'⁻¹ := by rw [h2]
        _ = j * j' * (a' * j⁻¹) * a'⁻¹ * j'⁻¹ := by group
        _ = j * j' * (j⁻¹ * a') * a'⁻¹ * j'⁻¹ := by
          rw [show a' * j⁻¹ = j⁻¹ * a' by
            calc a' * j⁻¹ = j⁻¹ * (j * a') * j⁻¹ := by group
              _ = j⁻¹ * (a' * j) * j⁻¹ := by rw [h3]
              _ = j⁻¹ * a' := by group]
        _ = j * j' * j⁻¹ * j'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hj hj') (inv_mem hj)) (inv_mem hj')
  have hQmap : Q.map ρ = centralizer (A : Set P) := map_comap_eq_self_of_surjective hρ _
  have hle : ⁅C, C⁆.map ρ ≤ J := by
    rw [map_commutator]
    refine le_trans (commutator_mono (map_mono hCQ) (map_mono hCQ)) ?_
    rw [hQmap, hC]
    exact hJAJ
  have hge : J ≤ ⁅C, C⁆.map ρ := by
    have h1 : ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ ≤ ⁅C, C⁆ := commutator_mono hQQ hQQ
    have h2 := map_mono (f := ρ) h1
    rw [map_commutator, map_commutator, hQmap] at h2
    refine le_trans ?_ h2
    have h3 : ⁅J, J⁆ ≤ ⁅centralizer (A : Set P), centralizer (A : Set P)⁆ :=
      commutator_mono hJC hJC
    calc J = ⁅⁅J, J⁆, ⁅J, J⁆⁆ := by rw [hJ, hJ]
      _ ≤ _ := commutator_mono h3 h3
  have hmem : ∀ x : ↥⁅C, C⁆, ρ x ∈ J := fun x => hle ⟨x, x.2, rfl⟩
  let ψ : ↥⁅C, C⁆ →* J := (ρ.comp (⁅C, C⁆).subtype).codRestrict J hmem
  have hψ : Function.Surjective ψ := by
    intro j
    obtain ⟨x, hx, hxj⟩ := hge j.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxj⟩
  have hψker : ψ.ker ≤ center ↥⁅C, C⁆ := by
    intro x hx
    have hx' : ρ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hz := mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx'))
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hz y)
  exact ⟨quotCenterEquivOfSurjective ψ hψ hψker hJZ⟩

instance u3_standardComponentOddCore_normal (H : Type*) [Group H] :
    (standardComponentOddCore H).Normal :=
  sSup_normal _ fun _ hN => hN.1

theorem le_standardComponentOddCore' {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ standardComponentOddCore H :=
  le_sSup ⟨hN, hodd⟩

theorem u3_odd_card_sup_of_normal {H : Type*} [Group H] [Finite H] {A B : Subgroup H}
    (hA : A.Normal) (hB : B.Normal) (hAo : Odd (Nat.card A)) (hBo : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup H)) := by
  have : A.Normal := hA
  have : B.Normal := hB
  have hindexOdd : Odd (A.relIndex (A ⊔ B)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hBo.of_dvd_nat (A.relIndex_dvd_card B)
  have hwithin : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toEquiv
  have hproduct := (A.subgroupOf (A ⊔ B)).index_mul_card
  have hindex : (A.subgroupOf (A ⊔ B)).index = A.relIndex (A ⊔ B) := rfl
  rw [hindex, hwithin] at hproduct
  rw [← hproduct]
  exact hindexOdd.mul hAo

theorem odd_card_standardComponentOddCore' {H : Type*} [Group H] [Finite H] :
    Odd (Nat.card (standardComponentOddCore H)) := by
  classical
  have hbot : (⊥ : Subgroup H).Normal ∧ Odd (Nat.card (⊥ : Subgroup H)) :=
    ⟨inferInstance, by rw [card_bot]; decide⟩
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal (α := Subgroup H)
    (p := fun N => N.Normal ∧ Odd (Nat.card N)) hbot
  have hle : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N ≤ M := by
    intro N hN hNo
    have : M.Normal := hM.prop.1
    have : N.Normal := hN
    have hsup := u3_odd_card_sup_of_normal hM.prop.1 hN hM.prop.2 hNo
    have heq := hM.eq_of_le ⟨inferInstance, hsup⟩ le_sup_left
    exact heq ▸ le_sup_right
  have hEq : standardComponentOddCore H = M :=
    le_antisymm (sSup_le fun N hN => hle N hN.1 hN.2)
      (le_standardComponentOddCore' hM.prop.1 hM.prop.2)
  rw [hEq]
  exact hM.prop.2

theorem standardComponentOddCore_quot_eq_bot {H : Type*} [Group H] [Finite H] :
    standardComponentOddCore (H ⧸ standardComponentOddCore H) = ⊥ := by
  set O := standardComponentOddCore H
  refine le_bot_iff.mp (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hNo⟩ := hN
  set M := N.comap (QuotientGroup.mk' O)
  have hMn : M.Normal := hNn.comap _
  have hOM : O ≤ M := fun x hx => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hMo : Odd (Nat.card M) := by
    have h1 := M.card_mul_index
    have h2 := N.card_mul_index
    have h3 : M.index = N.index := N.index_comap_of_surjective (QuotientGroup.mk'_surjective O)
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
    have hpos : 0 < M.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hM : Nat.card M = Nat.card N * Nat.card O := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc Nat.card M * M.index = Nat.card H := h1
        _ = Nat.card (H ⧸ O) * Nat.card O := h4
        _ = Nat.card N * N.index * Nat.card O := by rw [h2]
        _ = Nat.card N * Nat.card O * M.index := by rw [h3]; ring
    rw [hM]
    exact hNo.mul odd_card_standardComponentOddCore'
  have hMO : M ≤ O := le_standardComponentOddCore' hMn hMo
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hy : y ∈ M := hx
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hMO hy

end CFSG.ComponentClassification.GMS78
