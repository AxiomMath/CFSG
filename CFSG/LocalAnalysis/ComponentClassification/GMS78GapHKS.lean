module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSCoord
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSAffine
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSField

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G} {q : ℕ}

namespace IsTorus

variable {y : G}

omit [Finite G] in
theorem inv_aut_pow_apply (hy : IsTorus L T y) (m : ℕ) (b : gmsA L T) :
    (((hy.aut⁻¹) ^ m) b : G) = (y ^ m)⁻¹ * b * y ^ m := by
  rw [inv_pow, ← zpow_natCast, ← zpow_neg, hy.aut_zpow_apply]
  simp [zpow_neg, zpow_natCast]

theorem existsUnique_zpow_perm (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) {β γ : gmsDelta L T} (hβ : β ≠ deltaT₀ L T) (hγ : γ ≠ deltaT₀ L T) :
    ∃! c, c ∈ zpowers hy.perm ∧ c β = γ := by
  obtain ⟨k, hk⟩ := hy.exists_zpow_perm_apply h313 hX h hβ hγ
  refine ⟨hy.perm ^ k, ⟨zpow_mem (mem_zpowers _) k, hk⟩, ?_⟩
  rintro c ⟨hc, hcβ⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
  have h1 : (hy.perm ^ (-j + k)) β = β := by
    rw [zpow_add, zpow_neg, Equiv.Perm.mul_apply, hk, ← hcβ]
    exact (hy.perm ^ j).symm_apply_apply β
  have h2 := hy.zpow_perm_eq_one h313 h hβ h1
  rw [zpow_add, zpow_neg, inv_mul_eq_one] at h2
  exact h2

theorem exists_translation_of_affine
    (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) (hHKS : HKSRegularNormalAffine) : ∀ Q ∈ gmsDelta L T,
      ∃ u ∈ gmsTrans L T, rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q := by
  classical
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.T₀_ne_bot
  have ht₁1' : t₁ ≠ 1 := fun h1 => ht₁1 (Subtype.ext h1)
  have hAcomm : ∀ a b : gmsA L T, a * b = b * a := fun a b => Subtype.ext (by
    have := congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, mem_sup_left a.2⟩ ⟨b, mem_sup_left b.2⟩)
    simpa using this)
  let instA : CommGroup (gmsA L T) := { (inferInstance : Group (gmsA L T)) with mul_comm := hAcomm }
  have hq4 := hX.four_le
  have hAc := (hX.sylow h).1
  have hnt : Nontrivial (gmsA L T) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hAc]
    omega
  set s : MulAut (gmsA L T) := hy.aut⁻¹ with hsdef
  have hs : ∀ a b : gmsA L T, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (s ^ m) a = b := by
    intro a b ha hb
    obtain ⟨m, hm⟩ := hy.trans a a.2 b b.2 (fun h1 => ha (Subtype.ext h1))
      (fun h1 => hb (Subtype.ext h1))
    exact ⟨m, Subtype.ext (by rw [hy.inv_aut_pow_apply, hm])⟩
  set E : Set ℕ := {m | ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∀ Q ∈ gmsDelta L T,
    deltaCoord L T t Q = (y ^ m)⁻¹ * deltaCoord L T t₁ Q * y ^ m} with hEdef
  let fA : ∀ n : G, n ∈ gmsN₁ L T → MulAut (gmsA L T) := fun n hn =>
    (gmsA L T).normalizerMonoidHom ⟨n, (GMS78.mem_gmsN₁.mp hn).2.1⟩
  have hfA : ∀ n (hn : n ∈ gmsN₁ L T) (b : gmsA L T), ((fA n hn b : gmsA L T) : G) = n * b * n⁻¹ :=
    fun n hn b => normalizerMonoidHom_apply_apply_coe _ _ _
  have hcomm : ∀ n (hn : n ∈ gmsN₁ L T), ∀ m ∈ E, fA n hn * s ^ m = s ^ m * fA n hn := by
    rintro n hn m ⟨t, ht, -, hm⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp only [MulAut.mul_apply]
    rw [hfA n hn, hy.inv_aut_pow_apply, hy.inv_aut_pow_apply, hfA n hn]
    exact conj_comm_of_mem_gmsN₁ h313 hX h hF ht₁ ht₁1' ht hm hn b.2
  have : Finite (Additive (gmsA L T)) := inferInstanceAs (Finite (gmsA L T))
  have : Finite (AddMonoid.End (Additive (gmsA L T))) := DFunLike.finite _
  let R := Singer.ring s E
  let instR : Field R := (Singer.isField E hs).toField
  let lin : ∀ n (hn : n ∈ gmsN₁ L T), Additive (gmsA L T) ≃ₗ[R] Additive (gmsA L T) :=
    fun n hn => Singer.linEquiv s E (hcomm n hn)
  have hlin : ∀ n (hn : n ∈ gmsN₁ L T) (b : gmsA L T),
      lin n hn (Additive.ofMul b) = Additive.ofMul (fA n hn b) := fun _ _ _ => rfl
  have hR4 : 4 ≤ Nat.card R := by
    obtain ⟨Q₁, hQ₁⟩ := exists_ne_deltaT₀ h313 hX
    have hQ₁T : (Q₁ : Subgroup G) ≠ T ⊓ centralizer (L : Set G) := fun h1 => hQ₁ (Subtype.ext h1)
    have hpick : ∀ t : (T ⊓ centralizer (L : Set G) : Subgroup G), ∃ r : R,
        (r : AddMonoid.End (Additive (gmsA L T)))
          (Additive.ofMul ⟨deltaCoord L T t₁ Q₁, (deltaCoord_spec h313 hX h hF Q₁.2 ht₁).1⟩) =
        Additive.ofMul ⟨deltaCoord L T t Q₁, (deltaCoord_spec h313 hX h hF Q₁.2 t.2).1⟩ := by
      intro t
      by_cases ht1 : (t : G) = 1
      · refine ⟨0, ?_⟩
        have : deltaCoord L T (t : G) Q₁ = 1 := by rw [ht1]; exact deltaCoord_one h313 Q₁.2
        simp only [ZeroMemClass.coe_zero]
        rw [eq_comm]
        exact congrArg Additive.ofMul (Subtype.ext this)
      · obtain ⟨m, hm⟩ := exists_pow_deltaCoord hy h313 hX h hF ht₁ ht₁1' t.2 ht1
        refine ⟨⟨_, Singer.pow_mem_ring s E (show m ∈ E from ⟨t, t.2, ht1, hm⟩)⟩, ?_⟩
        rw [Singer.toEnd_apply]
        congr 1
        apply Subtype.ext
        rw [hy.inv_aut_pow_apply]
        exact (hm Q₁ Q₁.2).symm
    choose r hr using hpick
    have hinj : Function.Injective r := by
      intro t t' htt'
      have h1 := (hr t).symm.trans ((congrArg (fun r : R =>
        (r : AddMonoid.End (Additive (gmsA L T)))
          (Additive.ofMul ⟨deltaCoord L T t₁ Q₁, (deltaCoord_spec h313 hX h hF Q₁.2 ht₁).1⟩))
        htt').trans (hr t'))
      have h2 : deltaCoord L T t Q₁ = deltaCoord L T t' Q₁ :=
        congrArg Subtype.val (Additive.ofMul.injective h1)
      obtain ⟨hcA, hcQ⟩ := deltaCoord_spec h313 hX h hF Q₁.2 t.2
      obtain ⟨-, hcQ'⟩ := deltaCoord_spec h313 hX h hF Q₁.2 t'.2
      rw [← h2] at hcQ'
      have hct : ∀ s ∈ T ⊓ centralizer (L : Set G), deltaCoord L T t Q₁ * s =
          s * deltaCoord L T t Q₁ := fun s hs =>
        mem_centralizer_iff.mp (mem_inf.mp hs).2 _ (mem_inf.mp (mem_inf.mp hcA).1).2
      have h3 : (t : G) * (t' : G)⁻¹ ∈ (Q₁ : Subgroup G) ⊓ (T ⊓ centralizer (L : Set G)) := by
        refine mem_inf.mpr ⟨?_, mul_mem t.2 (inv_mem t'.2)⟩
        have h4 := mul_mem hcQ (inv_mem hcQ')
        have h5 : deltaCoord L T t Q₁ * t * (deltaCoord L T t Q₁ * t')⁻¹ =
            (t : G) * (t' : G)⁻¹ := by
          calc deltaCoord L T t Q₁ * t * (deltaCoord L T t Q₁ * t')⁻¹
              = deltaCoord L T t Q₁ * (t * (t' : G)⁻¹) * (deltaCoord L T t Q₁)⁻¹ := by group
            _ = (t * (t' : G)⁻¹) * deltaCoord L T t Q₁ * (deltaCoord L T t Q₁)⁻¹ := by
                rw [hct _ (mul_mem t.2 (inv_mem t'.2))]
            _ = (t : G) * (t' : G)⁻¹ := by group
        rwa [h5] at h4
      rw [h313.inf_eq_bot _ Q₁.2 _ mem_delta_T₀ hQ₁T, mem_bot, mul_inv_eq_one] at h3
      exact Subtype.ext h3
    have h1 := Nat.card_le_card_of_injective r hinj
    obtain ⟨F, hF4, -, hF4c⟩ := h.exists_four_le
    have h2 := card_le_of_le hF4
    omega
  have hbij := deltaCoord_bijective h313 hX h hF ht₁ ht₁1'
  let ι : gmsDelta L T ≃ Additive (gmsA L T) := (Equiv.ofBijective _ hbij).trans Additive.ofMul
  have hι : ∀ Q : gmsDelta L T,
      ((Additive.toMul (ι Q) : gmsA L T) : G) = deltaCoord L T t₁ Q := fun _ => rfl
  have hιT : ι (deltaT₀ L T) = 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hι]
    exact deltaCoord_T₀ h313 ht₁
  let Φ : Equiv.Perm (gmsDelta L T) →* Equiv.Perm (Additive (gmsA L T)) :=
    (Equiv.permCongrHom ι).toMonoidHom
  have hΦ : ∀ σ m, Φ σ m = ι (σ (ι.symm m)) := fun _ _ => rfl
  have hη : ∀ n : G, n ∈ gmsN₁ L T → n * t₁ * n⁻¹ * t₁⁻¹ ∈ gmsA L T :=
    fun n hn => (GMS78.mem_gmsN₁.mp hn).2.2 t₁ (mem_sup_right ht₁)
  have hform : ∀ (n : normalizer (gmsV L T : Set G)) (hn : (n : G) ∈ gmsN₁ L T)
      (m : Additive (gmsA L T)), Φ (deltaPerm L T n) m =
        lin n hn m + Additive.ofMul ⟨n * t₁ * (n : G)⁻¹ * t₁⁻¹, hη n hn⟩ := by
    intro n hn m
    obtain ⟨Q, rfl⟩ := ι.surjective m
    rw [hΦ, Equiv.symm_apply_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    have hl : lin n hn (ι Q) = Additive.ofMul (fA n hn (Additive.toMul (ι Q))) := rfl
    rw [hι, deltaPerm_apply, deltaCoord_conj h313 hX h hF Q.2 ht₁ hn, toMul_add,
      Subgroup.coe_mul, hl, toMul_ofMul, toMul_ofMul, hfA _ hn, hι]
  set X := (deltaN₁ L T).map Φ with hXdef
  have haff : ∀ x ∈ X, ∃ φ : Additive (gmsA L T) ≃ₗ[R] Additive (gmsA L T),
      ∃ b, ∀ m, x m = φ m + b := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := mem_map.mp hx
    obtain ⟨n, hn, rfl⟩ := mem_map.mp hσ
    have hn' : (n : G) ∈ gmsN₁ L T := mem_subgroupOf.mp hn
    exact ⟨lin n hn', _, hform n hn'⟩
  have h2 : ∀ a b c d : Additive (gmsA L T), a ≠ b → c ≠ d → ∃ x ∈ X, x a = c ∧ x b = d := by
    intro a b c d hab hcd
    obtain ⟨σ, hσ, h1, h2⟩ := hy.twoTransitive_deltaN₁ h313 hX h (ι.symm a) (ι.symm b)
      (ι.symm c) (ι.symm d) (ι.symm.injective.ne hab) (ι.symm.injective.ne hcd)
    exact ⟨Φ σ, mem_map_of_mem _ hσ, by rw [hΦ, h1, Equiv.apply_symm_apply],
      by rw [hΦ, h2, Equiv.apply_symm_apply]⟩
  set C := (zpowers hy.perm).map Φ with hCdef
  have hCX : C ≤ X := map_mono (zpowers_le.mpr hy.perm_mem_deltaN₁)
  have hzT : ∀ c ∈ zpowers hy.perm, c (deltaT₀ L T) = deltaT₀ L T := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hy.perm_apply_T₀ k
  have hC0 : ∀ c ∈ C, c 0 = 0 := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_map.mp hc
    rw [hΦ, ← hιT, Equiv.symm_apply_apply, hzT c' hc']
  have hcyc : IsCyclic C := by
    rw [hCdef, MonoidHom.map_zpowers]
    infer_instance
  have hnorm : ∀ x ∈ X, x 0 = 0 → ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx hx0 c hc
    obtain ⟨σ, hσ, rfl⟩ := mem_map.mp hx
    obtain ⟨c', hc', rfl⟩ := mem_map.mp hc
    have hσT : σ (deltaT₀ L T) = deltaT₀ L T := by
      rw [hΦ, ← hιT, Equiv.symm_apply_apply] at hx0
      exact ι.injective hx0
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc'
    have h1 := hy.conj_mem_zpowers h (map_le_range _ _ hσ) hσT
    rw [← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem _ ?_
    have h3 : σ * hy.perm ^ k * σ⁻¹ = (σ * hy.perm * σ⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [h3]
    exact zpow_mem h1 k
  have hreg : ∀ β γ : Additive (gmsA L T), β ≠ 0 → γ ≠ 0 → ∃! c, c ∈ C ∧ c β = γ := by
    intro β γ hβ hγ
    have hβ' : ι.symm β ≠ deltaT₀ L T := fun h1 => hβ (by rw [← hιT, ← h1, Equiv.apply_symm_apply])
    have hγ' : ι.symm γ ≠ deltaT₀ L T := fun h1 => hγ (by rw [← hιT, ← h1, Equiv.apply_symm_apply])
    obtain ⟨c', ⟨hc', hc'β⟩, huniq⟩ := hy.existsUnique_zpow_perm h313 hX h hβ' hγ'
    refine ⟨Φ c', ⟨mem_map_of_mem _ hc', by rw [hΦ, hc'β, Equiv.apply_symm_apply]⟩, ?_⟩
    rintro c ⟨hc, hcβ⟩
    obtain ⟨c'', hc'', rfl⟩ := mem_map.mp hc
    rw [hΦ] at hcβ
    rw [huniq c'' ⟨hc'', (Equiv.eq_symm_apply ι).mpr hcβ⟩]
  have : Nontrivial (Additive (gmsA L T)) := inferInstanceAs (Nontrivial (gmsA L T))
  obtain ⟨x, hxX, b, hb, hxb⟩ :=
    Affine.exists_translation hHKS hR4 haff h2 hCX hC0 hcyc hnorm hreg
  intro Q hQ
  by_cases hQT : Q = T ⊓ centralizer (L : Set G)
  · exact ⟨1, one_mem _, by rw [inv_one, rightConjugate_one, hQT]⟩
  set Q' : gmsDelta L T := ⟨Q, hQ⟩ with hQ'def
  have hQ'0 : ι Q' ≠ 0 := fun h1 =>
    hQT (congrArg Subtype.val (ι.injective (h1.trans hιT.symm)))
  obtain ⟨c, ⟨hc, hcb⟩, -⟩ := hreg b (ι Q') hb hQ'0
  obtain ⟨φc, bc, hφc⟩ := haff c (hCX hc)
  have hbc : bc = 0 := by
    have := hφc 0
    rwa [hC0 c hc, map_zero, zero_add, eq_comm] at this
  have hcadd : ∀ m, c m = φc m := fun m => by rw [hφc, hbc, add_zero]
  have hx'X : c * x * c⁻¹ ∈ X := mul_mem (mul_mem (hCX hc) hxX) (inv_mem (hCX hc))
  have hx' : ∀ m, (c * x * c⁻¹) m = m + ι Q' := by
    intro m
    simp only [Equiv.Perm.mul_apply]
    rw [hxb, hcadd, map_add, ← hcadd, ← hcadd, Equiv.Perm.inv_def, Equiv.apply_symm_apply, hcb]
  obtain ⟨σ, hσ, hσx⟩ := mem_map.mp hx'X
  obtain ⟨n, hn, rfl⟩ := mem_map.mp hσ
  have hn' : (n : G) ∈ gmsN₁ L T := mem_subgroupOf.mp hn
  have hf := hform n hn'
  have h0 := hf 0
  rw [hσx, hx', map_zero, zero_add, zero_add] at h0
  have hlin1 : ∀ m, lin n hn' m = m := by
    intro m
    have h1 := hf m
    rw [hσx, hx', ← h0] at h1
    exact (add_right_cancel h1).symm
  have hnC : (n : G) ∈ centralizer (gmsA L T : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := congrArg (fun m => ((Additive.toMul m : gmsA L T) : G))
      (hlin1 (Additive.ofMul ⟨a, ha⟩))
    simp only [hlin, toMul_ofMul, hfA] at h1
    calc a * n = n * a * (n : G)⁻¹ * n := by rw [h1]
      _ = n * a := by group
  refine ⟨n, mem_inf.mpr ⟨hn', hnC⟩, ?_⟩
  have hσT : deltaPerm L T n (deltaT₀ L T) = Q' := by
    apply ι.injective
    have h1 := hx' (ι (deltaT₀ L T))
    rw [← hσx, hΦ, Equiv.symm_apply_apply, hιT, zero_add] at h1
    exact h1
  have := congrArg Subtype.val hσT
  rw [deltaPerm_apply] at this
  exact this

end IsTorus

end Sec3

end CFSG.ComponentClassification.GMS78
