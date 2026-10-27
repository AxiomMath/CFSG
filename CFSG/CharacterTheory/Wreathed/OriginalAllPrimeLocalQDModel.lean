module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDGroup
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDTorus
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolution
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.QuasiDihedralFusion CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.Wreathed.CentralSL2Abelianization

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem eq_one_of_pow_two_pow_of_odd {X : Type*} [Group X] [Finite X] (hX : Odd (Nat.card X))
    {x : X} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
  have h3 : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hX)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

theorem eq_one_of_noIndexTwo {K : Type*} [Group K] [Finite K] (hK : ∀ X : Subgroup K, X.index ≠ 2)
    {n m : ℕ} (hmn : m = 2 ^ n) (θ : K →* Multiplicative (ZMod m)) (x : K) : θ x = 1 := by
  have : NeZero m := ⟨by rw [hmn]; positivity⟩
  have hp : IsPGroup 2 θ.range := by
    have h : IsPGroup 2 (Multiplicative (ZMod m)) := IsPGroup.of_card (n := n) (by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hmn])
    exact h.to_subgroup θ.range
  by_contra hne
  have h2 : 2 ∣ Nat.card θ.range := by
    rcases hp.card_eq_or_dvd with h | h
    · exfalso
      have hbot := (Subgroup.eq_bot_iff_card θ.range).mpr h
      exact hne (by
        have hx : θ x ∈ θ.range := ⟨x, rfl⟩
        rw [hbot] at hx
        exact hx)
    · exact h
  obtain ⟨X, hX⟩ := exists_index_two_of_isPGroup hp h2
  apply hK (X.comap θ.rangeRestrict)
  rw [Subgroup.index_comap_of_surjective X θ.rangeRestrict_surjective, hX]

variable [Finite F]

theorem torus_hyps_of_isQGroup {n : ℕ} (hmn : m = 2 ^ n)
    (h4m : ¬ 4 * m ∣ Nat.card F * (Nat.card F ^ 2 - 1)) (hd : Odd (Nat.card Sigma))
    {A : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hA : IsQGroup A)
    {P : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hPA : P ≤ A)
    (hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPcard : Nat.card P = m ^ 2) :
    2 * m ∣ Nat.card (A.comap (matrixInclusion F b m hm heven Sigma hSigma)) ∧
      ∀ C : Subgroup (A.comap (matrixInclusion F b m hm heven Sigma hSigma)),
        C.Characteristic → C.index ≠ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set j := matrixInclusion F b m hm heven Sigma hSigma with hj
  set ψ := psi F b m hm heven Sigma hSigma with hψ
  have hjinj : Function.Injective j := matrixInclusion_injective F b m hm heven Sigma hSigma
  have hψker : ψ.ker = j.range := psi_ker F b m hm heven Sigma hSigma
  have hjnormal : j.range.Normal := matrixLayer_normal F b m hm heven Sigma hSigma
  set P' : Subgroup A := P.subgroupOf A with hP'
  have hP'card : Nat.card P' = 2 ^ (2 * n) := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, hPcard, hmn, ← pow_mul,
      mul_comm]
  have hP'p : IsPGroup 2 P' := IsPGroup.of_card hP'card
  obtain ⟨R, hPR⟩ := hP'p.exists_le_sylow
  obtain ⟨K, hK⟩ := hA.exists_data R
  set Y : Subgroup A := K ⊓ (R : Subgroup A) with hYdef
  obtain ⟨k, hk, ⟨eY⟩⟩ := hK.quaternion.exists_quaternion_equiv
  have hYnc : ¬ ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ * y₂ = y₂ * y₁ := by
    intro hcomm
    have : NeZero (2 ^ k) := ⟨by positivity⟩
    have h1 := hcomm (eY.symm (QuaternionGroup.a 1)) (eY.symm _).2
      (eY.symm (QuaternionGroup.xa 0)) (eY.symm _).2
    have h2 : eY.symm (QuaternionGroup.a 1) * eY.symm (QuaternionGroup.xa 0) =
        eY.symm (QuaternionGroup.xa 0) * eY.symm (QuaternionGroup.a 1) := Subtype.ext h1
    rw [← map_mul, ← map_mul] at h2
    have h3 := eY.symm.injective h2
    simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h3
    have h4 : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
      push_cast
      linear_combination -h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
    omega
  have hR2 : 2 ^ (2 * n + 1) ≤ Nat.card (R : Subgroup A) := by
    obtain ⟨e, he⟩ := R.isPGroup'.exists_card_eq
    have hdvd : 2 ^ (2 * n) ∣ 2 ^ e := by
      rw [← hP'card, ← he]
      exact Subgroup.card_dvd_of_le hPR
    have hle : 2 * n ≤ e := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    rcases hle.lt_or_eq with hlt | heq
    · rw [he]
      exact Nat.pow_le_pow_right (by norm_num) hlt
    · exfalso
      have hRP : (R : Subgroup A) = P' :=
        (Subgroup.eq_of_le_of_card_ge hPR (by rw [he, hP'card, heq])).symm
      apply hYnc
      intro y₁ hy₁ y₂ hy₂
      have h1 : y₁ ∈ P' := hRP ▸ (Subgroup.mem_inf.mp hy₁).2
      have h2 : y₂ ∈ P' := hRP ▸ (Subgroup.mem_inf.mp hy₂).2
      exact Subtype.ext (hPcomm _ (Subgroup.mem_subgroupOf.mp h1) _ (Subgroup.mem_subgroupOf.mp h2))
  have hYcard : 2 ^ (n + 1) ≤ Nat.card Y := pow_le_card_of_isMaximalQuaternionIn hK.quaternion hR2
  have hYp : IsPGroup 2 Y := R.isPGroup'.to_le inf_le_right
  have hYdvd : 2 * m ∣ Nat.card Y := by
    obtain ⟨e, he⟩ := hYp.exists_card_eq
    rw [he] at hYcard ⊢
    rw [hmn, ← pow_succ']
    exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hYcard)
  have hθ : ∀ x : K, (ψ ((x : A) : SemilinearExtension F b m hm heven Sigma hSigma)).1 = 1 :=
    eq_one_of_noIndexTwo hK.noIndexTwo hmn
      ((MonoidHom.fst _ _).comp (ψ.comp (A.subtype.comp K.subtype)))
  let κ : K →* Sigma := (MonoidHom.snd _ _).comp (ψ.comp (A.subtype.comp K.subtype))
  have hκ : ∀ x : K, κ x = 1 ↔
      ((x : A) : SemilinearExtension F b m hm heven Sigma hSigma) ∈ j.range := by
    intro x
    rw [← hψker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact Prod.ext (hθ x) h
    · intro h
      exact congrArg Prod.snd h
  set N : Subgroup A := j.range.subgroupOf A with hN
  have hNnormal : N.Normal := by
    rw [hN]
    exact Subgroup.Normal.subgroupOf hjnormal A
  set B : Subgroup A := K ⊓ N with hB
  have hBK : B.subgroupOf K = κ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hκ, hB, Subgroup.mem_inf, hN,
      Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hBodd : Odd (B.relIndex K) := by
    rw [Subgroup.relIndex, hBK, Subgroup.index_ker]
    refine Odd.of_dvd_nat hd ?_
    rw [← Subgroup.card_top (G := Sigma)]
    exact Subgroup.card_dvd_of_le le_top
  have hYN : Y ≤ N := by
    intro y hy
    obtain ⟨e, he⟩ := hYp (⟨y, hy⟩ : Y)
    have hyK : y ∈ K := (Subgroup.mem_inf.mp hy).1
    have h1 : κ ⟨y, hyK⟩ ^ 2 ^ e = 1 := by
      rw [← map_pow]
      have h2 : (⟨y, hyK⟩ : K) ^ 2 ^ e = 1 := by
        apply Subtype.ext
        have h3 := congrArg Subtype.val he
        simpa using h3
      rw [h2, map_one]
    have h4 := eq_one_of_pow_two_pow_of_odd hd h1
    rw [hN, Subgroup.mem_subgroupOf]
    exact (hκ ⟨y, hyK⟩).mp h4
  let f : A.comap j →* N :=
    ((j.comp (A.comap j).subtype).codRestrict A (fun x => x.2)).codRestrict N
      (fun x => Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hjinj
      have h := congrArg (fun z : N => ((z : A) : SemilinearExtension F b m hm heven Sigma hSigma))
        hxy
      exact h
    · rintro ⟨⟨z, hzA⟩, hzN⟩
      obtain ⟨x, rfl⟩ := Subgroup.mem_subgroupOf.mp hzN
      exact ⟨⟨x, hzA⟩, rfl⟩
  let e : A.comap j ≃* N := MulEquiv.ofBijective f hf
  have hcardN : Nat.card (A.comap j) = Nat.card N := Nat.card_congr e.toEquiv
  have hSL : Nat.card (A.comap j) ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.GorensteinWalter.sl2_card_formula F]
    rw [← Subgroup.card_top (G := Matrix.SpecialLinearGroup (Fin 2) F)]
    exact Subgroup.card_dvd_of_le le_top
  refine ⟨?_, ?_⟩
  · rw [hcardN]
    exact hYdvd.trans (Subgroup.card_dvd_of_le hYN)
  · intro C hC hC2
    have hCN : (C.map e.toMonoidHom).Characteristic := characteristic_map_mulEquiv e hC
    set CA : Subgroup A := (C.map e.toMonoidHom).map N.subtype with hCA
    have hCAnormal : CA.Normal := by
      rw [hCA]
      exact ConjAct.normal_of_characteristic_of_normal
    have hCAN : CA ≤ N := Subgroup.map_subtype_le _
    have hCAcard : Nat.card CA = Nat.card C := by
      rw [hCA, Subgroup.card_map_of_injective N.subtype_injective]
      exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    have hCidx : Nat.card C * 2 = Nat.card (A.comap j) := by
      have h := Subgroup.card_mul_index C
      rw [hC2] at h
      exact h
    by_cases hle : B ≤ CA
    · apply h4m
      have hYC : Y ≤ CA := (le_inf inf_le_left hYN).trans hle
      have h1 : 2 * m ∣ Nat.card C := by
        rw [← hCAcard]
        exact hYdvd.trans (Subgroup.card_dvd_of_le hYC)
      have h2 : 4 * m ∣ Nat.card (A.comap j) := by
        rw [← hCidx]
        obtain ⟨c, hc⟩ := h1
        exact ⟨c, by rw [hc]; ring⟩
      exact h2.trans hSL
    · have hrelN : CA.relIndex N = 2 := by
        have h1 := Subgroup.relIndex_mul_card CA N
        rw [inf_eq_left.mpr hCAN, hCAcard] at h1
        have h2 : Nat.card N = 2 * Nat.card C := by rw [← hcardN, ← hCidx, mul_comm]
        rw [h2] at h1
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
      have hrel : (K ⊓ CA).relIndex B = 2 := by
        have h1 : (K ⊓ CA).relIndex B = CA.relIndex B := by
          rw [← Subgroup.inf_relIndex_right (K ⊓ CA) B, ← Subgroup.inf_relIndex_right CA B]
          congr 1
          apply le_antisymm
          · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
          · exact le_inf (le_inf ((inf_le_right).trans inf_le_left) inf_le_left) inf_le_right
        rw [h1]
        have h2 : CA.relIndex B ≤ CA.relIndex N :=
          Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hrelN]; norm_num)
        rw [hrelN] at h2
        have h3 : CA.relIndex B ≠ 1 := fun h => hle (Subgroup.relIndex_eq_one.mp h)
        have h4 : CA.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hKn : K ≤ Subgroup.normalizer (K : Set A) := Subgroup.le_normalizer
      have hNn : K ≤ Subgroup.normalizer (N : Set A) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hNnormal]
        exact le_top
      have hCAn : K ≤ Subgroup.normalizer (CA : Set A) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hCAnormal]
        exact le_top
      obtain ⟨X, hX⟩ := exists_index_two_of_relIndex_two' inf_le_left
        (inf_le_inf_left K hCAN)
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKn hk, hNn hk⟩)
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKn hk, hCAn hk⟩)
        hrel hBodd
      exact hK.noIndexTwo X hX

theorem modelLayer_le_of_isQGroup
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hb : ¬ IsSquare b)
    {A : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hA : IsQGroup A)
    (hD : ModelSignalizers.modelC b m hm heven Sigma hSigma ⊓
      ModelSignalizers.modelBase b m hm heven Sigma hSigma ≤ A) :
    ModelSignalizers.modelLayer b m hm heven Sigma hSigma ≤ A := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, hDcomm, -, -, hPcard, -, hcyc, hTcard, -⟩ := hred
  set j := matrixInclusion F b m hm heven Sigma hSigma with hj
  have hiFinj : Function.Injective (specialInclusion F b m hm heven) :=
    specialInclusion_injective F b m hm heven
  have hinl : Function.Injective (SemidirectProduct.inl : CentralExtension F b m hm heven →*
      SemilinearExtension F b m hm heven Sigma hSigma) := SemidirectProduct.inl_injective
  let Dv : Subgroup (CentralExtension F b m hm heven) :=
    Subgroup.centralizer {CentralSL2.involutionY F b m hm heven}
  have hmemA : ∀ v ∈ Dv,
      (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma) ∈ A := by
    intro v hv
    apply hD
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨v, rfl⟩⟩
    rw [ModelSignalizers.inl_mem_modelC_iff]
    exact hv
  set T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := Subgroup.centralizer {weyl F} with hT
  have hTcyc : IsCyclic T :=
    isCyclic_of_surjective (T.equivMapOfInjective _ hiFinj).symm.toMonoidHom
      (T.equivMapOfInjective _ hiFinj).symm.surjective
  have hTcard' : (Nat.card T : ℤ) = (p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
    rw [← Subgroup.card_map_of_injective (K := T) hiFinj]
    exact hTcard
  have hTA : T ≤ A.comap j := fun t ht =>
    hD (Subgroup.mem_inf.mpr ⟨(ModelSignalizers.inl_specialInclusion_mem_modelC_iff t).mpr ht,
      ⟨_, rfl⟩⟩)
  obtain ⟨P⟩ : Nonempty (Sylow 2 Dv) := inferInstance
  set PH : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
    ((P : Subgroup Dv).map Dv.subtype).map SemidirectProduct.inl with hPH
  have hPA : PH ≤ A := by
    rintro _ ⟨_, ⟨d, -, rfl⟩, rfl⟩
    exact hmemA _ d.2
  have hPcomm : ∀ x ∈ PH, ∀ y ∈ PH, x * y = y * x := by
    rintro _ ⟨_, ⟨d, -, rfl⟩, rfl⟩ _ ⟨_, ⟨d', -, rfl⟩, rfl⟩
    have h := hDcomm _ d.2 _ d'.2
    simp only [Subgroup.subtype_apply]
    rw [← map_mul, h, map_mul]
  have hPHcard : Nat.card PH = m ^ 2 := by
    rw [hPH, Subgroup.card_map_of_injective hinl,
      Subgroup.card_map_of_injective Dv.subtype_injective]
    exact (hPcard P).1
  have h3 : 3 ≤ p ^ f := by omega
  have h4m : ¬ 4 * m ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [hcard]
    exact not_four_mul_dvd hpodd.pow h3 rfl hm2
  obtain ⟨h2m, hchar⟩ := torus_hyps_of_isQGroup hm2 h4m hd hA hPA hPcomm hPHcard
  have htop := eq_top_of_torus_le hp hpodd hf hcard hq _ rfl m hm2 hTA hTcyc hTcard' h2m hchar
  rw [ModelSignalizers.modelLayer_eq_matrixLayer]
  rintro _ ⟨X, rfl⟩
  have hX : X ∈ A.comap j := by
    rw [htop]
    exact Subgroup.mem_top X
  exact hX

end CFSG.Wreathed.OriginalAllPrime.LocalQD
