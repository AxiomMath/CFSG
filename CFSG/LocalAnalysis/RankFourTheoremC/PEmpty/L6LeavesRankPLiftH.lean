module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG CFSG.LocalCores Subgroup CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

theorem exists_lift_in_H (hI : GL83I66Two) {f : ℕ} (hf : f.Prime) (hf5 : 5 ≤ f)
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) (R : Subgroup X) [R.Normal]
    (H T Z0 : Subgroup X) (hTR : T ≤ R) (hTH : T ≤ H) (hZ0H : Z0 ≤ H)
    (hTn : ∀ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ ∈ T) (hTf : ¬ f ∣ Nat.card T)
    (hdec : ∀ n ∈ H ⊓ R, ∃ t ∈ T, ∃ z ∈ Z0, n = t * z)
    (hZ0c : ∀ z ∈ Z0, ∀ h ∈ H, h * z = z * h)
    (hC : ∀ C : ComponentIndex (X ⧸ R), IsSimpleGroup C.1)
    (hZ : ∀ C : ComponentIndex (X ⧸ R), center C.1 = ⊥)
    (hΛ : layer (X ⧸ R) ≤ H.map (QuotientGroup.mk' R)) {z : X ⧸ R}
    (hzΛ : z ∈ layer (X ⧸ R)) (hzf : z ^ f = 1)
    (hcen : ∀ C : ComponentIndex (X ⧸ R), ∃ S : Sylow f C.1,
      coord hZ C ⟨z, hzΛ⟩ ∈ (S : Subgroup C.1) ∧
        ∀ s ∈ (S : Subgroup C.1), coord hZ C ⟨z, hzΛ⟩ * s = s * coord hZ C ⟨z, hzΛ⟩) :
    ∃ h ∈ H, h ^ f = 1 ∧ QuotientGroup.mk' R h = z := by
  classical
  haveI := Fact.mk hf
  haveI hTnorm : (T.subgroupOf H).Normal := ⟨fun n hn g => hTn g g.2 n hn⟩
  let ψ : H →* X ⧸ R := (QuotientGroup.mk' R).comp H.subtype
  have hψ : T.subgroupOf H ≤ ψ.ker := fun t ht =>
    MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr (hTR ht))
  let φ : H ⧸ T.subgroupOf H →* X ⧸ R := QuotientGroup.lift (T.subgroupOf H) ψ hψ
  have hφ : ∀ h : H, φ (QuotientGroup.mk h) = QuotientGroup.mk' R (h : X) := fun h => rfl
  have hker : φ.ker ≤ center (H ⧸ T.subgroupOf H) := by
    intro x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hh : (h : X) ∈ R := by
      have := MonoidHom.mem_ker.mp hx
      rw [hφ] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨t, ht, z', hz', htz⟩ := hdec (h : X) ⟨h.2, hh⟩
    have htH : t ∈ H := hTH ht
    have hdecH : h = ⟨t, htH⟩ * ⟨z', hZ0H hz'⟩ := Subtype.ext htz
    have hmk_t : (QuotientGroup.mk (⟨t, htH⟩ : H) : H ⧸ T.subgroupOf H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (show t ∈ T from ht)
    rw [hdecH, QuotientGroup.mk_mul, hmk_t, one_mul]
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hZ0c z' hz' k k.2)
  have hΛ' : layer (X ⧸ R) ≤ φ.range := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := hΛ hx
    exact ⟨QuotientGroup.mk ⟨h, hh⟩, rfl⟩
  have hΓ : CFSG.Open.IsKGroup (H ⧸ T.subgroupOf H) :=
    CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup'
      (CFSG.KCore.KGroupNonab.subgroup isoInvariant_isCatalogGroup' hX H) (T.subgroupOf H)
  obtain ⟨w, hwf, hwz⟩ := lift_layer hI hf hf5 hΓ φ hker hC hZ hΛ' hzΛ hzf hcen
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective w
  have hh₀f : ((h₀ : X) ^ f) ∈ T := by
    have h1 : (QuotientGroup.mk (h₀ ^ f) : H ⧸ T.subgroupOf H) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hwf
    have h2 : h₀ ^ f ∈ T.subgroupOf H := (QuotientGroup.eq_one_iff (h₀ ^ f)).mp h1
    exact h2
  have hh₀z : QuotientGroup.mk' R (h₀ : X) = z := hwz
  have hTpow : ((h₀ : X) ^ f) ^ Nat.card T = 1 := by
    have h1 : (⟨(h₀ : X) ^ f, hh₀f⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hcop : Nat.Coprime (Nat.card T) f := ((Nat.Prime.coprime_iff_not_dvd hf).mpr hTf).symm
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hf.one_lt
  refine ⟨(h₀ : X) ^ (Nat.card T * a), H.pow_mem h₀.2 _, ?_, ?_⟩
  · calc (((h₀ : X) ^ (Nat.card T * a)) ^ f) = (((h₀ : X) ^ f) ^ Nat.card T) ^ a := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hTpow, one_pow]
  · rw [map_pow, hh₀z]
    generalize Nat.card T * a = u at ha ⊢
    have hmod : u = f * (u / f) + 1 := by
      have := Nat.div_add_mod u f
      omega
    rw [hmod, pow_add, pow_mul, hzf, one_pow, one_mul, pow_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
