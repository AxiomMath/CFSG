module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
  (onQuotient fixedImage fixedImageProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed (restrictAutomorphism)

section General

theorem exists_isComponent_fixed_onQuotient {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    {M : Subgroup (fixedSubgroup ψ)} (hM : CFSG.IsComponent M) :
    ∃ K : Subgroup (fixedSubgroup (onQuotient Z ψ hinv)), CFSG.IsComponent K ∧
      Nonempty (↥K ⧸ center ↥K ≃* ↥M ⧸ center ↥M) := by
  haveI : (fixedImage Z ψ hinv).Normal :=
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedImage_normal Z ψ hinv hcentral
  set P := fixedImageProjection Z ψ hinv
  have hPs : Function.Surjective P :=
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedImageProjection_surjective
      Z ψ hinv
  have hPk : P.ker ≤ center (fixedSubgroup ψ) :=
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central
      Z ψ hinv hcentral
  let f : ↥M →* ↥(M.map P) := P.subgroupMap M
  have hf : Function.Surjective f := P.subgroupMap_surjective M
  have hfk : f.ker ≤ center ↥M := by
    intro x hx
    have h1 : P (x : fixedSubgroup ψ) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := hPk (MonoidHom.mem_ker.2 h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    exact Subtype.ext (h2 (g : fixedSubgroup ψ))
  have hM₁ : CFSG.IsComponent (M.map P) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_surjective hM.1 f hf hfk, hM.2.map hPs⟩
  refine ⟨(M.map P).map (fixedImage Z ψ hinv).subtype,
    CFSG.ComponentClassification.CatLeafProof.isComponent_map_subtype_of_normal hM₁, ?_⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hM.1 f hf
    hfk
  let e₂ := (M.map P).equivMapOfInjective (fixedImage Z ψ hinv).subtype
    (fixedImage Z ψ hinv).subtype_injective
  exact ⟨(e.trans (QuotientGroup.congr _ _ e₂ (Subgroup.map_center_eq e₂))).symm⟩

theorem mulAut_eq_one_of_forall_inv_mul_mem_center {Y : Type*} [Group Y] (hY : Group.IsPerfect Y)
    (α : MulAut Y) (h : ∀ x : Y, x⁻¹ * α x ∈ center Y) : α = 1 := by
  let c : Y →* center Y :=
    { toFun := fun x => ⟨x⁻¹ * α x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by
              rw [map_mul, mul_inv_rev]; group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hz]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hker : commutator Y ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [Group.isPerfect_def.1 hY] at hker
  ext x
  have hx : c x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  have h2 : α x = x := by
    calc α x = x * (x⁻¹ * α x) := by group
      _ = x := by rw [h1, mul_one]
  simpa using h2

theorem isCompIn_fixedSubgroup_restrict_conj {H : Type} [Group H] {A B D : Subgroup H} (s : H)
    (hA : A.map (MulAut.conj s).toMonoidHom = A) (hAD : ∀ x ∈ A, x ∈ D ↔ s * x = x * s)
    (hD : IsCompIn B D) (hBA : B ≤ A) :
    IsCompIn (B.subgroupOf A) (fixedSubgroup (restrictAutomorphism A (MulAut.conj s) hA)) := by
  have hBD : B ≤ D ⊓ A := le_inf hD.1 hBA
  have h1 := isCompIn_subgroupOf (isCompIn_of_le hD hBD inf_le_left) (inf_le_right : D ⊓ A ≤ A)
  have h2 : (D ⊓ A).subgroupOf A =
      fixedSubgroup (restrictAutomorphism A (MulAut.conj s) hA) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change _ ↔ restrictAutomorphism A (MulAut.conj s) hA x = x
    rw [Subtype.ext_iff,
      CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed.restrictAutomorphism_apply,
      MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact ⟨fun hx => (hAD x x.2).1 hx.1, fun hx => ⟨(hAD x x.2).2 hx, x.2⟩⟩
  rwa [h2] at h1

end General

section Link

variable {H : Type} [Group H] [Finite H] {a : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}

private theorem mem_centralizer_sup_zpowers_iff {T : Subgroup H} {s x : H}
    (hx : x ∈ centralizer (T : Set H)) :
    x ∈ centralizer ((T ⊔ zpowers s : Subgroup H) : Set H) ↔ s * x = x * s := by
  constructor
  · intro h
    exact Subgroup.mem_centralizer_iff.1 h s
      ((le_sup_right : zpowers s ≤ T ⊔ zpowers s) (Subgroup.mem_zpowers s))
  · intro h
    have hle : T ⊔ zpowers s ≤ centralizer ({x} : Set H) := by
      refine sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2 ?_) ?_
      · exact Subgroup.mem_centralizer_iff.1 hx t ht
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact h
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

private theorem conj_conj_eq_of_sq_comm {s x : H} (hc : s ^ 2 * x = x * s ^ 2) :
    s * (s * x * s⁻¹) * s⁻¹ = x := by
  rw [pow_two] at hc
  calc s * (s * x * s⁻¹) * s⁻¹ = (s * s * x) * (s⁻¹ * s⁻¹) := by simp only [mul_assoc]
    _ = (x * (s * s)) * (s⁻¹ * s⁻¹) := by rw [hc]
    _ = x := by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem TLinks.not_le_centralizer_of_inv (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i)
    (hia : i ≤ a) (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom)
    (hne : L (i - 1) ≠ L i) : ¬ L i ≤ centralizer ({s i} : Set H) := by
  intro hc
  obtain ⟨-, hLc⟩ := h.comp i hia
  obtain ⟨-, -, -, hBc⟩ := h.elem i hi hia
  have hle : L (i - 1) ≤ L i := h.le_of_inv hi hia hinv
  have hAC : L i ≤ centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H) := by
    intro x hx
    rw [mem_centralizer_sup_zpowers_iff (hLc.1 hx)]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hc hx)).symm
  have hCT : centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H) ≤
      centralizer (T i : Set H) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hA : IsCompIn (L i) (centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H)) :=
    isCompIn_of_le hLc hAC hCT
  have hcomm := IsCompIn.commute_of_ne hBc hA hne
  exact not_forall_commute_of_isQuasisimple (h.comp (i - 1) (by omega)).2.isQuasisimple
    fun x hx y hy => hcomm x hx y (hle hy)

theorem link_fixedComponent (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom) (hne : L (i - 1) ≠ L i) :
    ∃ σ : MulAut (↥(L i) ⧸ center ↥(L i)), orderOf σ = 2 ∧
      ∃ K : Subgroup (fixedSubgroup σ), CFSG.IsComponent K ∧
        Nonempty (↥K ⧸ center ↥K ≃* ↥(L (i - 1)) ⧸ center ↥(L (i - 1))) ∧
        cqOrd (L (i - 1)) ∣ Nat.card K := by
  obtain ⟨-, hLc⟩ := h.comp i hia
  obtain ⟨-, -, hs2, hBc⟩ := h.elem i hi hia
  have hle : L (i - 1) ≤ L i := h.le_of_inv hi hia hinv
  have hinv' : (L i).map (MulAut.conj (s i)).toMonoidHom = L i := hinv.symm
  let ψ : MulAut ↥(L i) := restrictAutomorphism (L i) (MulAut.conj (s i)) hinv'
  have hψ : ∀ x : ↥(L i), ((ψ x : ↥(L i)) : H) = s i * x * (s i)⁻¹ := fun x => by
    rw [CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed.restrictAutomorphism_apply,
      MulAut.conj_apply]
  have hZ : (center ↥(L i)).map ψ.toMonoidHom = center ↥(L i) := Subgroup.map_center_eq ψ
  let σ : MulAut (↥(L i) ⧸ center ↥(L i)) := onQuotient (center ↥(L i)) ψ hZ
  have hσmk : ∀ x : ↥(L i), σ (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := fun x =>
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk _ ψ hZ x
  have hψ2 : ∀ x : ↥(L i), ψ (ψ x) = x := by
    intro x
    apply Subtype.ext
    rw [hψ, hψ]
    have hx : (x : H) ∈ centralizer (T i : Set H) := hLc.1 x.2
    exact conj_conj_eq_of_sq_comm (Subgroup.mem_centralizer_iff.1 hx _ hs2)
  have hσ2 : σ ^ 2 = 1 := by
    rw [pow_two]
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.mul_apply, hσmk, hσmk, hψ2]
    rfl
  have hσne : σ ≠ 1 := by
    intro h1
    have hall : ∀ x : ↥(L i), x⁻¹ * ψ x ∈ center ↥(L i) := by
      intro x
      have h2 : σ (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [h1]; rfl
      rw [hσmk] at h2
      exact QuotientGroup.eq.1 h2.symm
    have hψ1 : ψ = 1 :=
      mulAut_eq_one_of_forall_inv_mul_mem_center (hLc.isQuasisimple.1) ψ hall
    refine h.not_le_centralizer_of_inv hi hia hinv hne fun x hx => ?_
    have h3 := congrArg (fun f : MulAut ↥(L i) => ((f ⟨x, hx⟩ : ↥(L i)) : H)) hψ1
    simp only [hψ] at h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hAD : ∀ x ∈ L i,
      x ∈ centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H) ↔ s i * x = x * s i :=
    fun x hx => mem_centralizer_sup_zpowers_iff (hLc.1 hx)
  have hM := isCompIn_fixedSubgroup_restrict_conj (s i) hinv' hAD hBc hle
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_isComponent_fixed_onQuotient (center ↥(L i)) le_rfl ψ hZ hM.2
  let e₃ := (Subgroup.subgroupOfEquivOfLe hM.1).trans (Subgroup.subgroupOfEquivOfLe hle)
  let eM := QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)
  refine ⟨σ, orderOf_eq_prime hσ2 hσne, K, hK, ⟨e.trans eM⟩, ?_⟩
  have hcard : cqOrd (L (i - 1)) = Nat.card (↥K ⧸ center ↥K) :=
    Nat.card_congr (e.trans eM).symm.toEquiv
  rw [hcard]
  exact Subgroup.card_quotient_dvd_card _

theorem TLinks.cqOrd_dvd_of_inv (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom) (hne : L (i - 1) ≠ L i) :
    cqOrd (L (i - 1)) ∣ cqOrd (L i) := by
  obtain ⟨σ, -, K, -, -, hdvd⟩ := link_fixedComponent h hi hia hinv hne
  exact hdvd.trans ((Subgroup.card_subgroup_dvd_card K).trans
    (Subgroup.card_subgroup_dvd_card (fixedSubgroup σ)))

theorem five_dvd_step (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom) (hne : L (i - 1) ≠ L i)
    (h5 : 5 ∣ cqOrd (L (i - 1))) : 5 ∣ cqOrd (L i) :=
  h5.trans (h.cqOrd_dvd_of_inv hi hia hinv hne)

end Link

section BaseArithmetic

open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)

private theorem factorization_sixty_three : (60 : ℕ).factorization 3 = 1 := by
  have h : (60 : ℕ) = 3 ^ 1 * 20 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd]

private theorem lieSylowExponent_mul_ne_one {τ : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible τ n 3 f) : lieSylowExponent τ n * f ≠ 1 := by
  intro h
  have hf : f = 1 := Nat.eq_one_of_mul_eq_one_left h
  have he : lieSylowExponent τ n = 1 := Nat.eq_one_of_mul_eq_one_right h
  subst hf
  obtain ⟨-, -, hτ⟩ := hadm
  cases τ <;> simp only [lieSylowExponent] at he hτ
  · obtain ⟨hn, -, h3⟩ := hτ
    have hn2 : n = 2 := by
      by_contra hne
      have := Nat.mul_le_mul (show 3 ≤ n by omega) (show 2 ≤ n - 1 by omega)
      omega
    subst hn2
    exact h3 (by norm_num)
  · obtain ⟨hn, -⟩ := hτ
    have := Nat.mul_le_mul hn (show 2 ≤ n - 1 by omega)
    omega
  · obtain ⟨hn, -⟩ := hτ
    have := Nat.pow_le_pow_left hn 2
    omega
  · obtain ⟨hn, -⟩ := hτ
    have := Nat.pow_le_pow_left hn 2
    omega
  · have := Nat.mul_le_mul hτ (show 3 ≤ n - 1 by omega)
    omega
  · have := Nat.mul_le_mul hτ (show 3 ≤ n - 1 by omega)
    omega
  all_goals omega

end BaseArithmetic

section Base


theorem not_charThreeLie_of_card_sixty {Q : Type} [Group Q] (h : Nat.card Q = 60) :
    ¬ CharThreeLie Q := by
  rintro ⟨τ, n, f, hL⟩
  have hadm := hL.admissible
  obtain ⟨-, -, hfac⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput Q τ n 3 f hadm hL
  rw [h, factorization_sixty_three] at hfac
  exact lieSylowExponent_mul_ne_one hadm hfac.symm

theorem notF3Five_of_card_sixty {H : Type} [Group H] [Finite H] {X : Subgroup H}
    (h : cqOrd X = 60) : NotF3Five X :=
  ⟨not_charThreeLie_of_card_sixty h, by rw [h]; norm_num⟩

end Base

section Step

variable {H : Type} [Group H] [Finite H] {a : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}


theorem charThreeLie_step {Q : Type} [Group Q] (hQ : CharThreeLie Q) {σ : MulAut Q}
    (hσ : orderOf σ = 2) {K : Subgroup (fixedSubgroup σ)} (hK : CFSG.IsComponent K) :
    CharThreeLie (↥K ⧸ center ↥K) ∨ Nat.card K = 504 := by
  obtain ⟨τ, n, f, hL⟩ := hQ
  rcases CFSG.SeitzReduction.gls3OddLieAutComponentsInput Q τ n 3 f Nat.prime_three (by norm_num)
      hL.admissible hL σ hσ K hK with ⟨τ', n', f', -, hK'⟩ | ⟨-, -, -, hK'⟩
  · exact Or.inl ⟨τ', n', f', hK'⟩
  · right
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hK']
    decide

theorem TLinks.notF3Five_step (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hne : L (i - 1) ≠ L i) (h0 : NotF3Five (L (i - 1))) : NotF3Five (L i) := by
  rcases h.link i hi hia with h5a | hinv
  · obtain ⟨e⟩ := h5a.2
    exact ⟨fun hc => h0.1 ((charThreeLie_congr e).1 hc),
      (h.cqOrd_eq_of_swap hi hia h5a) ▸ h0.2⟩
  · refine ⟨fun hc => ?_, five_dvd_step h hi hia hinv hne h0.2⟩
    obtain ⟨σ, hσ, K, hK, ⟨e⟩, hdvd⟩ := link_fixedComponent h hi hia hinv hne
    rcases charThreeLie_step hc hσ hK with hc' | h504
    · exact h0.1 ((charThreeLie_congr e).1 hc')
    · have h5 : 5 ∣ 504 := by
        rw [← h504]
        exact h0.2.trans hdvd
      omega

theorem TLinks.notF3Five (h : TLinks H a L T s) (hne : ∀ i, 1 ≤ i → i ≤ a → L (i - 1) ≠ L i)
    (h0 : NotF3Five (L 0)) : ∀ i ≤ a, NotF3Five (L i) := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ k ih =>
    intro hk
    have h1 : k + 1 - 1 = k := by omega
    have := h.notF3Five_step (i := k + 1) (by omega) hk (hne (k + 1) (by omega) hk)
    rw [h1] at this
    exact this (ih (by omega))

theorem InCGb.notF3Five_top {G : Type} [Group G] [Finite G] {n : ℕ} {L T : ℕ → Subgroup G}
    {s : ℕ → G} (h : InCGb G n L T s) : NotF3Five (L (n - 1)) := by
  have hn := h.1.one_le
  refine (h.1.links.mono (Nat.sub_le n 1)).notF3Five (fun i hi hin => ?_) h.2 (n - 1) le_rfl
  intro heq
  have := h.1.inj (i - 1) (by omega) i (by omega) heq
  omega

end Step

end CFSG.EvenSporadicStandard.M12Std.Rbc
