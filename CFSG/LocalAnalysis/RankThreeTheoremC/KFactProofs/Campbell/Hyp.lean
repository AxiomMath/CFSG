module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Generic
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.pCore_X_le_R (h : CampbellHyp X K R P) : pCoreOf 2 X ≤ R :=
  pCoreOf_le_of_odd_index h.R_two h.R_le h.R_sylow

theorem CampbellHyp.R_sylow_P (h : CampbellHyp X K R P) : ¬ 2 ∣ (R.subgroupOf P).index := by
  intro h2
  apply h.R_sylow
  have hmul := Subgroup.relIndex_mul_relIndex R P X h.R_le_P h.P_le
  show 2 ∣ R.relIndex X
  rw [← hmul]
  exact Dvd.dvd.mul_right h2 _

theorem CampbellHyp.pCore_P_le_R (h : CampbellHyp X K R P) : pCoreOf 2 P ≤ R :=
  pCoreOf_le_of_odd_index h.R_two h.R_le_P h.R_sylow_P

theorem CampbellHyp.pCore_X_le_pCore_P (h : CampbellHyp X K R P) :
    pCoreOf 2 X ≤ pCoreOf 2 P :=
  le_pCoreOf_of_normalizes (isPGroup_pCoreOf X) (h.pCore_X_le_R.trans h.R_le_P)
    (h.P_le.trans (normalizer_pCoreOf X))

theorem CampbellHyp.P_lt_X (h : CampbellHyp X K R P) : P < X := by
  refine lt_of_le_of_ne h.P_le ?_
  rintro rfl
  have h7 := h.P_index
  rw [Subgroup.subgroupOf_self, Subgroup.index_top] at h7
  omega

theorem hypPCore_conj_pCoreOf {x : A} (hx : x ∈ normalizer (K : Set A)) {n : A}
    (hn : n ∈ pCoreOf 2 K) : x * n * x⁻¹ ∈ pCoreOf 2 K := by
  have hxK : ∀ k : A, k ∈ K ↔ x * k * x⁻¹ ∈ K := mem_normalizer_iff.1 hx
  have hxK' : ∀ k : A, k ∈ K ↔ x⁻¹ * k * x ∈ K := mem_normalizer_iff''.1 hx
  let φ : ↥K ≃* ↥K :=
    { toFun := fun k => ⟨x * k * x⁻¹, (hxK k).1 k.2⟩
      invFun := fun k => ⟨x⁻¹ * k * x, (hxK' k).1 k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
  have hmap := CFSG.pCore_map_iso 2 φ
  have hφ : φ n' ∈ CFSG.pCore 2 ↥K := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hn'
  exact Subgroup.mem_map.2 ⟨φ n', hφ, rfl⟩

theorem hypPCore_normalizer_pCoreOf {Y : Subgroup A} (hY : Y ≤ normalizer (K : Set A)) :
    Y ≤ normalizer (pCoreOf 2 K : Set A) := by
  intro x hx
  refine mem_normalizer_iff.2 fun n => ⟨hypPCore_conj_pCoreOf (hY hx), fun hn => ?_⟩
  have := hypPCore_conj_pCoreOf (hY (Y.inv_mem hx)) hn
  simpa [mul_assoc] using this

theorem CampbellHyp.pCoreOf_K (h : CampbellHyp X K R P) : pCoreOf 2 K = K ⊓ pCoreOf 2 X := by
  apply le_antisymm
  · refine le_inf (pCoreOf_le_self K) ?_
    exact le_pCoreOf_of_normalizes (isPGroup_pCoreOf K) ((pCoreOf_le_self K).trans h.K_le)
      (hypPCore_normalizer_pCoreOf h.K_normal)
  · refine le_pCoreOf_of_normalizes ((isPGroup_pCoreOf X).to_le inf_le_right) inf_le_left ?_
    exact le_trans (le_inf Subgroup.le_normalizer (h.K_le.trans (normalizer_pCoreOf X)))
      Subgroup.inf_normalizer_le_normalizer_inf

theorem CampbellHyp.pCore_K_eq (h : CampbellHyp X K R P) :
    CFSG.pCore 2 ↥K = (pCoreOf 2 X).comap K.subtype := by
  ext k
  have hK := h.pCoreOf_K
  constructor
  · intro hk
    have hk' : (k : A) ∈ pCoreOf 2 K := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    rw [hK] at hk'
    exact Subgroup.mem_comap.2 (Subgroup.mem_inf.1 hk').2
  · intro hk
    have hk' : (k : A) ∈ K ⊓ pCoreOf 2 X := Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_comap.1 hk⟩
    rw [← hK] at hk'
    obtain ⟨k', hk'', hkk⟩ := Subgroup.mem_map.1 hk'
    have hkk' : k' = k := Subtype.ext hkk
    rwa [hkk'] at hk''

theorem CampbellHyp.mem_X_iff (h : CampbellHyp X K R P) {g : A} :
    g ∈ X ↔ ∃ k ∈ K, ∃ o ∈ pCoreOf 2 X, g = k * o := by
  constructor
  · intro hg
    have hset : ((K ⊔ pCoreOf 2 X : Subgroup A) : Set A) = (K : Set A) * (pCoreOf 2 X : Set A) :=
      Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 X)
        (h.K_le.trans (normalizer_pCoreOf X))
    have hg' : g ∈ ((K ⊔ pCoreOf 2 X : Subgroup A) : Set A) := h.X_eq.le hg
    rw [hset] at hg'
    obtain ⟨k, hk, o, ho, rfl⟩ := hg'
    exact ⟨k, hk, o, ho, rfl⟩
  · rintro ⟨k, hk, o, ho, rfl⟩
    exact X.mul_mem (h.K_le hk) (pCoreOf_le_self X ho)

theorem CampbellHyp.X_eq_mul (h : CampbellHyp X K R P) :
    (X : Set A) = (K : Set A) * (pCoreOf 2 P : Set A) := by
  ext g
  rw [Set.mem_mul]
  constructor
  · intro hg
    obtain ⟨k, hk, o, ho, rfl⟩ := h.mem_X_iff.1 hg
    exact ⟨k, hk, o, h.pCore_X_le_pCore_P ho, rfl⟩
  · rintro ⟨k, hk, o, ho, rfl⟩
    exact X.mul_mem (h.K_le hk) (h.P_le (pCoreOf_le_self P ho))
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.card_quot (h : CampbellHyp X K R P) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 := by
  obtain ⟨f, hf, hker⟩ := h.quot
  have hker' : f.ker = CFSG.pCore 2 ↥K := by
    rw [h.pCore_K_eq]
    ext k
    rw [MonoidHom.mem_ker, hker k]
    rfl
  rw [← hker', Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact CFSG.ComponentClassification.GHarris.card_GL32_gh

theorem CampbellHyp.exists_psi (h : CampbellHyp X K R P) :
    ∃ ψ : ↥X →* GL32, Function.Surjective ψ ∧ ψ.ker = (pCoreOf 2 X).subgroupOf X := by
  obtain ⟨f, hf, hker⟩ := h.quot
  have hle : pCoreOf 2 X ≤ X := pCoreOf_le_self X
  haveI hN : ((pCoreOf 2 X).subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).2 (normalizer_pCoreOf X)
  let g : ↥K →* ↥X ⧸ (pCoreOf 2 X).subgroupOf X :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion h.K_le)
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk, o, ho, hxko⟩ := h.mem_X_iff.1 x.2
    refine ⟨⟨k, hk⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion h.K_le ⟨k, hk⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hxko] using ho
  have hg_ker : g.ker = f.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker k]
    show QuotientGroup.mk (Subgroup.inclusion h.K_le k) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  let e : (↥X ⧸ (pCoreOf 2 X).subgroupOf X) ≃* GL32 :=
    (QuotientGroup.quotientKerEquivOfSurjective g hg_surj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hg_ker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    simp

theorem CampbellHyp.card_X (h : CampbellHyp X K R P) :
    Nat.card ↥X = Nat.card ↥(pCoreOf 2 X) * 168 := by
  obtain ⟨ψ, hψ, hψker⟩ := h.exists_psi
  have h1 := Subgroup.card_ker_mul_card_of_surjective hψ
  rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le_self X)).toEquiv,
    CFSG.ComponentClassification.GHarris.card_GL32_gh] at h1
  exact h1.symm
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
