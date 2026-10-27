module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutLoc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516COdd
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapNarrow

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem eq_or_eq_of_isPComponent_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {K : Subgroup X} (hKH : K ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hKpc : IsPComponent 2 (K.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X)))) :
    K = M ∨ K = M.map (MulAut.conj t).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  by_contra hK
  push Not at hK
  obtain ⟨hKM, hKMt⟩ := hK
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have htt : ∀ L : Subgroup X, (L.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t).toMonoidHom = L := by
    intro L
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      change t * (t * w * t⁻¹) * t⁻¹ ∈ L
      have h1 : t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ := by group
      rw [h1, ht2, one_mul, inv_one, mul_one]
      exact hw
    · intro hz
      refine ⟨t * z * t⁻¹, ⟨z, hz, rfl⟩, ?_⟩
      change t * (t * z * t⁻¹) * t⁻¹ = z
      have h1 : t * (t * z * t⁻¹) * t⁻¹ = (t * t) * z * (t * t)⁻¹ := by group
      rw [h1, ht2, one_mul, inv_one, mul_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  set Kt := K.map (MulAut.conj t).toMonoidHom with hKtdef
  obtain ⟨hKtH, hKtpc⟩ := isPComponent_conj hKH hKpc htH
  have hKtt : Kt.map (MulAut.conj t).toMonoidHom = K := htt K
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := htt M
  have hKtM : M ≠ Kt := by
    intro h
    apply hKMt
    rw [← hKtt, ← h]
  have hKtMt : Mt ≠ Kt := by
    intro h
    apply hKM
    rw [← hKtt, ← h, hMtt]
  have hKKM : K ⊔ Kt ≤ UnbalancedLayer.coreActionKernel M :=
    sup_le (GSThmB.B5a.le_coreActionKernel_of_ne hMH hKH hMpc hKpc (Ne.symm hKM))
      (GSThmB.B5a.le_coreActionKernel_of_ne hMH hKtH hMpc hKtpc hKtM)
  have hKKMt : K ⊔ Kt ≤ UnbalancedLayer.coreActionKernel Mt :=
    sup_le (GSThmB.B5a.le_coreActionKernel_of_ne hMtH hKH hMtpc hKpc (Ne.symm hKMt))
      (GSThmB.B5a.le_coreActionKernel_of_ne hMtH hKtH hMtpc hKtpc hKtMt)
  have htKK : t ∉ K ⊔ Kt := by
    intro h
    exact hne (mem_normalizer_iff_map_conj_eq.mp (hKKM h).1)
  have htN : zpowers t ≤ normalizer ((K ⊔ Kt : Subgroup X) : Set X) := by
    rw [zpowers_le, mem_normalizer_iff_map_conj_eq]
    change (K ⊔ Kt).map (MulAut.conj t).toMonoidHom = K ⊔ Kt
    rw [Subgroup.map_sup, hKtt]
    exact sup_comm _ _
  set K₀ := zpowers t ⊔ (K ⊔ Kt) with hK₀def
  have htK : t ∈ UnbalancedLayer.coreActionKernel J := S.t_mem_coreActionKernel
  have hcent : centralizer ({t} : Set X) ⊓ K₀ ≤ UnbalancedLayer.coreActionKernel J := by
    intro x hx
    obtain ⟨hxt, hxK₀⟩ := mem_inf.mp hx
    rw [← SetLike.mem_coe, hK₀def, coe_mul_of_left_le_normalizer_right _ _ htN] at hxK₀
    obtain ⟨a, ha, k, hk, rfl⟩ := hxK₀
    have hat : a ∈ centralizer ({t} : Set X) := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      exact zpow_mem (mem_centralizer_singleton_iff.mpr rfl) m
    have hkt : k ∈ centralizer ({t} : Set X) := by
      have h1 := mul_mem (inv_mem hat) hxt
      rwa [inv_mul_cancel_left] at h1
    have haK : a ∈ UnbalancedLayer.coreActionKernel J :=
      (zpowers_le.mpr htK) ha
    exact mul_mem haK (S.mem_coreActionKernel_of_centralizer_swap hCH hMH hMpc hJM hkt
      (hKKM hk) (hKKMt hk))
  have h4 : 4 ∣ Nat.card K := GSThmB.Cent516.four_dvd_card_of_perfect
    (UnbalancedCorr.commutator_eq_of_isPComponent hKH hKpc)
    (two_dvd_card_of_isPComponent_in hKH hKpc)
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := ↥K)
    (by norm_num; exact h4)
  set P := P₀.map K.subtype with hPdef
  have hPcard : Nat.card P = 4 := by
    rw [hPdef, card_map_of_injective K.subtype_injective, hP₀]
    norm_num
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hPK₀ : P ≤ K₀ := (map_subtype_le _).trans (le_sup_left.trans le_sup_right)
  have h1 := card_le_two_of_centralizer_inf (mem_sup_left (mem_zpowers t)) S.pair.1.1
    (fun Q hQ hQ2 => hsmall Q (hQ.trans hcent) hQ2) hPK₀ hP2
  omega

theorem le_or_le_of_isPComponent_swap
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {y : X} (hyJ : y ∈ J) (hy : orderOf y = 2) {T : Subgroup X}
    (hTH : T ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hTC : T ≤ centralizer ({y} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({y} : Set X)))) :
    T ≤ M ∨ T ≤ M.map (MulAut.conj t).toMonoidHom := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hJH : J ≤ H := hJM.trans (sup_le hMH hMtH)
  have hTpc' : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer ({y} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le (le_inf hTH hTC) inf_le_right hTpc
  obtain ⟨M₁, hM₁H, hM₁pc, hTM₁, -⟩ := pump_location_in (hJH hyJ) hy (le_inf hTH hTC) hTpc'
  have hyM : M.map (MulAut.conj y).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (hJN hyJ)
  have hyMt : (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      M.map (MulAut.conj t).toMonoidHom := by
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (S.pair.1.2.1 hyJ)
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨y * w * y⁻¹, (mem_normalizer_iff.mp (hJN hyJ) w).mp hw, ?_⟩
      change t * (y * w * y⁻¹) * t⁻¹ = y * (t * w * t⁻¹) * y⁻¹
      calc t * (y * w * y⁻¹) * t⁻¹ = (t * y) * w * (t * y)⁻¹ := by group
        _ = (y * t) * w * (y * t)⁻¹ := by rw [hyt]
        _ = y * (t * w * t⁻¹) * y⁻¹ := by group
    · rintro ⟨w, hw, rfl⟩
      refine ⟨t * (y⁻¹ * w * y) * t⁻¹, ⟨y⁻¹ * w * y, ?_, rfl⟩, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem (hJN hyJ)) w).mp hw
        rwa [inv_inv] at h1
      · change y * (t * (y⁻¹ * w * y) * t⁻¹) * y⁻¹ = t * w * t⁻¹
        calc y * (t * (y⁻¹ * w * y) * t⁻¹) * y⁻¹ =
            (y * t) * (y⁻¹ * w * y) * (y * t)⁻¹ := by group
          _ = (t * y) * (y⁻¹ * w * y) * (t * y)⁻¹ := by rw [hyt]
          _ = t * w * t⁻¹ := by group
  rcases S.eq_or_eq_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall hM₁H hM₁pc with h | h
  · left
    rw [h, hyM, sup_idem] at hTM₁
    exact hTM₁
  · right
    rw [h, hyMt, sup_idem] at hTM₁
    exact hTM₁

end Sig36

end CFSG.ComponentClassification.SolMax
