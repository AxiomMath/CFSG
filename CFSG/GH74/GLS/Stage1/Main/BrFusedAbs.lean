module

public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement Pointwise

theorem ivkIsPGL2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {P : ℕ → Prop}
    (h : IVK.IsPGL2 X P) : IVK.IsPGL2 Y P := by
  obtain ⟨F₀, iF, fF, hP, ⟨φ⟩⟩ := h
  exact ⟨F₀, iF, fF, hP, ⟨e.symm.trans φ⟩⟩

theorem inducedPGL2_map_iff {A X : Type} [Group A] [Group X] (f : A →* X)
    (hf : Function.Injective f) (L T : Subgroup A) (r : ℕ) :
    InducedPGL2 (L.map f) (T.map f) r ↔ InducedPGL2 L T r := by
  have hB : (L ⊔ T).map f = L.map f ⊔ T.map f := Subgroup.map_sup _ _ _
  let e : ↥(L ⊔ T) ≃* ↥(L.map f ⊔ T.map f) :=
    (Subgroup.equivMapOfInjective (L ⊔ T) f hf).trans (MulEquiv.subgroupCongr hB)
  have he : ∀ x, ((e x : ↥(L.map f ⊔ T.map f)) : X) = f x := fun x => rfl
  have hN : ((centralizer (L : Set A)).subgroupOf (L ⊔ T)).map e.toMonoidHom =
      (centralizer ((L.map f : Subgroup X) : Set X)).subgroupOf (L.map f ⊔ T.map f) := by
    ext x
    obtain ⟨h, rfl⟩ := e.surjective x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, he, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh
      rintro _ ⟨l, hl, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg f (hh l hl)
    · intro hh l hl
      apply hf
      rw [map_mul, map_mul]
      exact hh _ (Subgroup.mem_map_of_mem _ hl)
  constructor
  · rintro ⟨hn', hP⟩
    have hn : ((centralizer (L : Set A)).subgroupOf (L ⊔ T)).Normal := by
      have h1 := hn'.comap e.toMonoidHom
      rw [← hN, Subgroup.comap_map_eq_self_of_injective e.injective] at h1
      exact h1
    refine ⟨hn, ?_⟩
    have := hn
    have := hn'
    exact ivkIsPGL2_of_mulEquiv (QuotientGroup.congr _ _ e hN).symm hP
  · rintro ⟨hn, hP⟩
    have hn' : ((centralizer ((L.map f : Subgroup X) : Set X)).subgroupOf
        (L.map f ⊔ T.map f)).Normal := by
      rw [← hN]
      exact hn.map e.toMonoidHom e.surjective
    refine ⟨hn', ?_⟩
    have := hn
    have := hn'
    exact ivkIsPGL2_of_mulEquiv (QuotientGroup.congr _ _ e hN) hP

theorem centralizer_le_of_sylow_inf {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥)
    {L : Subgroup H} (hL : L.Normal) {T : Subgroup H}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {ζ : H} (hζL : ζ ∈ L) (hζ : ζ * ζ = 1)
    (hcT : ∀ x ∈ T, (∀ l ∈ L, l * x = x * l) → x = 1 ∨ x = ζ) :
    ∀ γ : H, (∀ l ∈ L, l * γ = γ * l) → γ ∈ L := by
  classical
  have _ := hζ
  set D : Subgroup H := centralizer (L : Set H) with hD
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hTD : T ⊓ D ≤ zpowers ζ := by
    intro x hx
    rcases hcT x hx.1 (Subgroup.mem_centralizer_iff.1 hx.2) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers ζ
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ D) D :=
    hT.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top D).ge
  obtain ⟨Q, hQ⟩ := hS
  have hQmem : ∀ x : ↥D, x ∈ (Q : Subgroup ↥D) → (x : H) ∈ T ⊓ D := fun x hx => by
    rw [← hQ]
    exact ⟨x, hx, rfl⟩
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥D) := by
    let f : ↥(Q : Subgroup ↥D) →* ↥(zpowers ζ) :=
      ((D.subtype).comp (Q : Subgroup ↥D).subtype).codRestrict (zpowers ζ)
        (fun x => hTD (hQmem x x.2))
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t => ((t : ↥(zpowers ζ)) : H)) hab
    exact isCyclic_of_injective f hf
  have hcyc := CFSG.cyclic_sylow_normal_odd_complement Q hQcyc
  have hK : pPrimeCore 2 ↥D = ⊥ := by
    have hnorm := CFSG.GH74.GLS.Stage1.Thm6.Prod.pPrimeCore_map_normal D 2
    have hle : (pPrimeCore 2 ↥D).map D.subtype ≤ pPrimeCore 2 H := by
      apply CFSG.le_pPrimeCore_of_normal_coprime hnorm
      rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    rw [hO] at hle
    rw [eq_bot_iff]
    intro k hk
    have := hle ⟨k, hk, rfl⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  intro γ hγ
  have hγD : γ ∈ D := Subgroup.mem_centralizer_iff.2 hγ
  have huniv := hcyc.2.1
  have hmem : (⟨γ, hγD⟩ : ↥D) ∈ ((pPrimeCore 2 ↥D : Set ↥D) * (Q : Set ↥D)) := by
    rw [huniv]; trivial
  obtain ⟨k, hk, q, hq, hkq⟩ := Set.mem_mul.1 hmem
  rw [hK] at hk
  have hk1 : k = 1 := Subgroup.mem_bot.1 hk
  rw [hk1, one_mul] at hkq
  have hγQ : γ ∈ T ⊓ D := by
    have := hQmem q hq
    rw [hkq] at this
    exact this
  rcases hcT γ hγQ.1 hγ with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact hζL

theorem oResidual_two_eq {Y : Type} [Group Y] [Finite Y] {E₁ E₂ T : Subgroup Y}
    (hP₁ : Group.IsPerfect ↥E₁) (hP₂ : Group.IsPerfect ↥E₂) (hN : (E₁ ⊔ E₂).Normal)
    (hT : IsPGroup 2 ↥T) (hY : E₁ ⊔ E₂ ⊔ T = ⊤) : oResidual 2 Y = E₁ ⊔ E₂ :=
  oResidual_sup_eq hN (sup_le (perfect_le_oResidual E₁ hP₁) (perfect_le_oResidual E₂ hP₂)) hT hY

theorem comps_of_sup_pgroup {Y : Type} [Group Y] [Finite Y] {E₁ E₂ T : Subgroup Y}
    (hQ₁ : IsQuasisimple ↥E₁) (hQ₂ : IsQuasisimple ↥E₂) (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hN : (E₁ ⊔ E₂).Normal) (hT : IsPGroup 2 ↥T) (hY : E₁ ⊔ E₂ ⊔ T = ⊤) :
    {K : Subgroup Y | IsComponent K} = {E₁, E₂} := by
  have hO : oResidual 2 Y = E₁ ⊔ E₂ := oResidual_two_eq hQ₁.1 hQ₂.1 hN hT hY
  have hle₁ : E₁ ≤ E₁ ⊔ E₂ := le_sup_left
  have hle₂ : E₂ ≤ E₁ ⊔ E₂ := le_sup_right
  have hc₁ : IsComponent E₁ := ⟨hQ₁, isSubnormal_of_comm_normal hcomm hN⟩
  have hcomm' : ∀ b ∈ E₂, ∀ a ∈ E₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hN' : (E₂ ⊔ E₁).Normal := by rw [sup_comm]; exact hN
  have hc₂ : IsComponent E₂ := ⟨hQ₂, isSubnormal_of_comm_normal hcomm' hN'⟩
  have hA₁ : IsQuasisimple ↥(E₁.subgroupOf (E₁ ⊔ E₂)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle₁).symm hQ₁
  have hA₂ : IsQuasisimple ↥(E₂.subgroupOf (E₁ ⊔ E₂)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle₂).symm hQ₂
  have hAtop : E₁.subgroupOf (E₁ ⊔ E₂) ⊔ E₂.subgroupOf (E₁ ⊔ E₂) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle₁ hle₂]
    exact Subgroup.subgroupOf_self _
  have hAcomm : ∀ a ∈ E₁.subgroupOf (E₁ ⊔ E₂), ∀ b ∈ E₂.subgroupOf (E₁ ⊔ E₂), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hcomm a ha b hb)
  have hpair := comps_of_pair hA₁ hA₂ hAcomm (by rw [hAtop]; infer_instance)
    (fun γ _ => by rw [hAtop]; trivial)
  ext K
  constructor
  · intro hK
    have hKle : K ≤ E₁ ⊔ E₂ := hO ▸ perfect_le_oResidual K hK.1.1
    have hKc : IsComponent (K.subgroupOf (E₁ ⊔ E₂)) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle).symm hK.1,
        hK.2.subgroupOf⟩
    have hmem : K.subgroupOf (E₁ ⊔ E₂) ∈ ({E₁.subgroupOf (E₁ ⊔ E₂), E₂.subgroupOf (E₁ ⊔ E₂)} :
        Set (Subgroup ↥(E₁ ⊔ E₂))) := by
      rw [← hpair]
      exact hKc
    rcases hmem with h | h
    · left
      rw [← Subgroup.map_subgroupOf_eq_of_le hKle, h, Subgroup.map_subgroupOf_eq_of_le hle₁]
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hKle, Set.mem_singleton_iff.1 h,
        Subgroup.map_subgroupOf_eq_of_le hle₂]
      exact Set.mem_singleton _
  · rintro (rfl | rfl)
    · exact hc₁
    · exact hc₂

open CFSG.GorensteinWalter in
theorem inf_centralizer_le_Z' {Γ : Type} [Group Γ] [Finite Γ] {L B Z : Subgroup Γ} (hLB : L ≤ B)
    (hZB : Z ≤ B) (hLperf : Group.IsPerfect ↥L) (hidx : (L ⊔ Z).relIndex B ≤ 2)
    [hZn : (Z.subgroupOf B).Normal] {Fq : Type} [Field Fq] [Finite Fq]
    (hodd : IsOddPrimePower (Nat.card Fq)) (h3 : 3 < Nat.card Fq)
    (φ : ↥B ⧸ Z.subgroupOf B ≃* PGL2 Fq) : B ⊓ centralizer (L : Set Γ) ≤ Z := by
  classical
  have : Finite (PGL2 Fq) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let ψ : ↥B →* PGL2 Fq := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf B))
  have hψsurj : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk b) = 1 ↔ b ∈ Z.subgroupOf B
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  set L' : Subgroup ↥B := L.subgroupOf B with hL'
  set R : Subgroup (PGL2 Fq) := L'.map ψ with hR
  have hL'perf : ⁅L', L'⁆ = L' := by
    have hperf' : Group.IsPerfect ↥L' :=
      Group.IsPerfect.ofSurjective (G := ↥L) (G' := ↥L')
        (f := (Subgroup.subgroupOfEquivOfLe hLB).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLB).symm.surjective
    exact Subgroup.isPerfect_iff.1 hperf'
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hL'perf]
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three Fq hodd h3
  have hRle : R ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Fq)).range := by
    rw [← hcomm, ← hRperf, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  set P₀ : Subgroup (PGL2 Fq) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Fq)).range with hP₀
  have hP₀idx : P₀.index = 2 := pgl2_psl2Range_index_eq_two Fq hodd
  have hRidx : R.index ≤ 2 := by
    rw [hR, Subgroup.index_map, MonoidHom.range_eq_top.2 hψsurj, Subgroup.index_top, mul_one,
      hψker, hL', ← Subgroup.subgroupOf_sup hLB hZB]
    exact hidx
  have hRidx2 : R.index = 2 := by
    have h1 : P₀.index ∣ R.index := Subgroup.index_dvd_of_le hRle
    rw [hP₀idx] at h1
    have h2 : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  have hReq : R = P₀ := by
    have e1 := Subgroup.index_mul_card R
    have e2 := Subgroup.index_mul_card P₀
    rw [hRidx2] at e1
    rw [hP₀idx] at e2
    exact Subgroup.eq_of_le_of_card_ge hRle (by
      have : 2 * Nat.card P₀ ≤ 2 * Nat.card R := by rw [e2, ← e1]
      omega)
  intro b hb
  have hbB : b ∈ B := hb.1
  have hbC : b ∈ centralizer (L : Set Γ) := hb.2
  have hψb : ψ ⟨b, hbB⟩ ∈ centralizer (P₀ : Set (PGL2 Fq)) := by
    rw [← hReq, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l', hl', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hbC (l' : Γ) (Subgroup.mem_subgroupOf.1 hl'))
  rw [pgl2_psl2Range_centralizer_eq_bot Fq hodd, Subgroup.mem_bot] at hψb
  have : (⟨b, hbB⟩ : ↥B) ∈ ψ.ker := hψb
  rw [hψker, Subgroup.mem_subgroupOf] at this
  exact this

end CFSG.GH74.GLS.Stage1.Main
