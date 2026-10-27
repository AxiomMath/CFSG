module

public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type*} [Group X]

theorem isComponentOf_top_map_conj {L : Subgroup X} (hL : IsComponentOf L ⊤) (c : X) :
    IsComponentOf (L.map (MulAut.conj c).toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h := CFSG.ComponentClassification.Components.chain_map (MulAut.conj c).toMonoidHom hL.2.1
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.equivMapOfInjective L _ (MulAut.conj c).injective).symm hL.2.2

variable [Finite X]

theorem mem_centralizer_of_centralizes_moving_components (hX : CFSG.pCore 2 X = ⊥)
    {T : Subgroup X} (hT : IsPGroup 2 T)
    (hnorm : ∀ L : Subgroup X, IsComponentOf L ⊤ → T ≤ Subgroup.normalizer (L : Set X))
    (hO : CFSG.pPrimeCore 2 X ≤ Subgroup.centralizer (T : Set X)) {c : X}
    (hc : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ Subgroup.normalizer (T : Set X) →
      c ∈ Subgroup.centralizer (L : Set X)) :
    c ∈ Subgroup.centralizer (T : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 X
  have hOn : O.Normal := CFSG.pPrimeCore_normal
  set Fs := CFSG.ComponentClassification.GeneralizedFitting.subgroup X
  set d : X → X := fun t => t⁻¹ * c⁻¹ * t * c with hd
  have hcrit : ∀ t y : X, t * y = y * t → t * (c * y * c⁻¹) = (c * y * c⁻¹) * t →
      d t * y = y * d t := by
    intro t y h1 h2
    have h3 : c⁻¹ * t * c * y = y * (c⁻¹ * t * c) := by
      calc c⁻¹ * t * c * y = c⁻¹ * (t * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * t) * c := by rw [h2]
        _ = y * (c⁻¹ * t * c) := by group
    have h4 : t⁻¹ * y = y * t⁻¹ := by
      calc t⁻¹ * y = t⁻¹ * (y * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * y) * t⁻¹ := by rw [h1]
        _ = y * t⁻¹ := by group
    calc d t * y = t⁻¹ * (c⁻¹ * t * c * y) := by simp only [hd]; group
      _ = t⁻¹ * (y * (c⁻¹ * t * c)) := by rw [h3]
      _ = (t⁻¹ * y) * (c⁻¹ * t * c) := by group
      _ = (y * t⁻¹) * (c⁻¹ * t * c) := by rw [h4]
      _ = y * d t := by simp only [hd]; group
  have hTO : ∀ t ∈ T, ∀ y ∈ O, t * y = y * t := fun t ht y hy =>
    (Subgroup.mem_centralizer_iff.mp (hO hy) t ht)
  have hTL : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ Subgroup.normalizer (T : Set X) →
      ∀ t ∈ T, ∀ y ∈ L, t * y = y * t := by
    intro L hL hLT t ht y hy
    have h := commutator_eq_bot_of_le_normalizer hL hT hLT
    have hLC : L ≤ Subgroup.centralizer (T : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h
    exact Subgroup.mem_centralizer_iff.mp (hLC hy) t ht
  have hdC : ∀ t ∈ T, d t ∈ Subgroup.centralizer (Fs : Set X) := by
    intro t ht
    have hFs : Fs ≤ Subgroup.centralizer ({d t} : Set X) := by
      refine sup_le ?_ (sSup_le fun L hL => ?_)
      · intro y hy
        have hyO : y ∈ O := fitting_le_pPrimeCore_two hX hy
        have hcy : c * y * c⁻¹ ∈ O := hOn.conj_mem y hyO c
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (hcrit t y (hTO t ht y hyO) (hTO t ht _ hcy)).symm
      · intro y hy
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        by_cases hLT : L ≤ Subgroup.normalizer (T : Set X)
        ·
          set L' := L.map (MulAut.conj c).toMonoidHom
          have hL' : IsComponentOf L' ⊤ := isComponentOf_top_map_conj hL c
          have hL'T : L' ≤ Subgroup.normalizer (T : Set X) := by
            by_contra hcon
            have hcL' := hc L' hL' hcon
            apply hcon
            intro z hz
            obtain ⟨w, hw, rfl⟩ := hz
            have e : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by simp [MulAut.conj_apply]
            have hmem : c * w * c⁻¹ ∈ L' := ⟨w, hw, e⟩
            have hwz : c * w * c⁻¹ = w := by
              have hcw : c * (c * w * c⁻¹) = (c * w * c⁻¹) * c :=
                (Subgroup.mem_centralizer_iff.mp hcL' _ hmem).symm
              have e2 : c * w * c⁻¹ * c = c * w := by group
              rw [e2] at hcw
              exact mul_left_cancel hcw
            rw [e, hwz]
            exact hLT hw
          have hcy : c * y * c⁻¹ ∈ L' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
          exact (hcrit t y (hTL L hL hLT t ht y hy) (hTL L' hL' hL'T t ht _ hcy)).symm
        ·
          have hcL := hc L hL hLT
          have hty : t * y * t⁻¹ ∈ L := by
            have := (Subgroup.mem_normalizer_iff.mp (hnorm L hL ht) y).mp hy
            exact this
          have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hcL y hy).symm
          have hcty : c⁻¹ * (t * y * t⁻¹) = (t * y * t⁻¹) * c⁻¹ := by
            have h1 : c * (t * y * t⁻¹) = (t * y * t⁻¹) * c :=
              (Subgroup.mem_centralizer_iff.mp hcL _ hty).symm
            calc c⁻¹ * (t * y * t⁻¹) = c⁻¹ * ((t * y * t⁻¹) * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * (t * y * t⁻¹)) * c⁻¹ := by rw [h1]
              _ = (t * y * t⁻¹) * c⁻¹ := by group
          symm
          calc d t * y = t⁻¹ * c⁻¹ * t * (c * y) := by simp only [hd]; group
            _ = t⁻¹ * c⁻¹ * t * (y * c) := by rw [hcy]
            _ = t⁻¹ * (c⁻¹ * (t * y * t⁻¹)) * t * c := by group
            _ = t⁻¹ * ((t * y * t⁻¹) * c⁻¹) * t * c := by rw [hcty]
            _ = y * d t := by simp only [hd]; group
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hFs hy)
  set Z := Fs ⊓ Subgroup.centralizer (Fs : Set X)
  have : Fs.Normal := CFSG.ComponentClassification.GeneralizedFitting.normal X
  have hZn : Z.Normal := Subgroup.normal_inf_normal _ _
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  have hZodd : Nat.Coprime 2 (Nat.card Z) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hxp : IsPGroup 2 ((Subgroup.zpowers x).map Z.subtype) :=
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])).map _
    have hle := le_pCore_of_isPGroup_of_le_commutative_normal hZn hZc
      (Subgroup.map_le_iff_le_comap.mpr fun _ _ => by simp) hxp
    rw [hX] at hle
    have hx1 : (x : X) = 1 :=
      Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers x)))
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hZO : Z ≤ O := le_sSup ⟨hZn, hZodd⟩
  have hdZ : ∀ t ∈ T, d t ∈ Z := fun t ht =>
    ⟨CFSG.ComponentClassification.GeneralizedFitting.centralizer_le X (hdC t ht), hdC t ht⟩
  have hmul : ∀ t ∈ T, ∀ t' ∈ T, d (t * t') = d t * d t' := by
    intro t ht t' ht'
    have h1 : t'⁻¹ * d t * t' = d t := by
      have := hTO t' ht' (d t) (hZO (hdZ t ht))
      calc t'⁻¹ * d t * t' = t'⁻¹ * (t' * d t) := by rw [this]; group
        _ = d t := by group
    calc d (t * t') = (t'⁻¹ * d t * t') * (t'⁻¹ * c⁻¹ * t' * c) := by simp only [hd]; group
      _ = d t * d t' := by rw [h1]
  have hpow : ∀ t ∈ T, ∀ n : ℕ, d (t ^ n) = d t ^ n := by
    intro t ht n
    induction n with
    | zero => simp [hd]
    | succ n ih => rw [pow_succ, hmul _ (T.pow_mem ht n) _ ht, ih, pow_succ]
  have hd1 : ∀ t ∈ T, d t = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : d t ^ 2 ^ k = 1 := by rw [← hpow t ht, htk]; simp [hd]
    have h2 : orderOf (d t) ∣ Nat.card Z := Z.orderOf_dvd_natCard (hdZ t ht)
    have h3 : orderOf (d t) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hZodd.pow_left k) h3 h2)
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  have h : t⁻¹ * c⁻¹ * t * c = 1 := hd1 t ht
  have h' : c⁻¹ * t * c = t := by
    calc c⁻¹ * t * c = t * (t⁻¹ * c⁻¹ * t * c) := by group
      _ = t := by rw [h, mul_one]
  calc t * c = c * (c⁻¹ * t * c) := by group
    _ = c * t := by rw [h']

end CFSG.AGLEmbedding
