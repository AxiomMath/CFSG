module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

variable {K : Type} [Field K]

section Witness

variable {n : ℕ}

theorem shortBlock_sl2Upper_mem_centralizer_siegDiag [CharP K 2] {p q : Fin n} (hpq : p ≠ q)
    (c : K) :
    shortBlock K hpq (sl2Upper c) ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) := by
  rw [mem_centralizer_siegDiag_iff]
  intro r
  rw [mat_shortBlock]
  rcases r with r | r
  · rw [fromBlocks_apply₁₁, Matrix.one_apply]
    simp only [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply, sl2Upper, Sum.inl.injEq]
    by_cases hrp : r = p
    · subst hrp
      simp
    · by_cases hrq : r = q
      · subst hrq
        simp [Ne.symm hpq]
      · simp [hrp, hrq]
  · rw [fromBlocks_apply₂₁, Matrix.one_apply_ne (by simp)]
    rfl

theorem twoCentralElt_one_one_eq (i j : Fin n) :
    twoCentralElt n i j (1 : K) 1 = siegDiag K i 1 * twoCentralElt n i j 0 1 := by
  rw [twoCentralElt_eq_siegDiag_mul_siegPair, twoCentralElt_eq_siegDiag_mul_siegPair,
    siegDiag_zero, one_mul]

theorem shortBlock_sl2Upper_mem_centralizer_twoCentralElt [CharP K 2] {a : K}
    (ha : a = 0 ∨ a = 1) :
    shortBlock K (one_ne_two_fin (n := n)) (sl2Upper (1 : K)) ∈
      centralizer ({twoCentralElt (n + 3) 1 2 a 1} : Set (StatedSp (n + 3) K)) := by
  have h12 := one_ne_two_fin (n := n)
  rcases ha with rfl | rfl
  · exact shortBlock_mem_centralizer h12 _ 1
  · rw [twoCentralElt_one_one_eq]
    have h1 := mem_centralizer_singleton_iff.1
      (shortBlock_sl2Upper_mem_centralizer_siegDiag (K := K) h12 1)
    have h2 := mem_centralizer_singleton_iff.1 (shortBlock_mem_centralizer (K := K) h12
      (sl2Upper (1 : K)) 1)
    rw [mem_centralizer_singleton_iff, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem mat_shortBlock_sl2Upper_one_two :
    mat (n + 3) K (shortBlock K (one_ne_two_fin (n := n)) (sl2Upper (1 : K))) (Sum.inl 1)
      (Sum.inl 2) = 1 := by
  have h := congrFun (congrFun (wBlock_shortBlock (n := n + 3) (K := K) one_ne_two_fin
    (sl2Upper (1 : K))) 0) 1
  simpa [wBlock, sl2Upper] using h

theorem commutator_centralizer_twoCentralElt_ne_two [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {a : K} (ha : a = 0 ∨ a = 1) :
    ⁅centralizer ({twoCentralElt (n + 3) 1 2 a 1} : Set (StatedSp (n + 3) K)),
      centralizer ({twoCentralElt (n + 3) 1 2 a 1} : Set (StatedSp (n + 3) K))⁆ ≠
      centralizer ({twoCentralElt (n + 3) 1 2 a 1} : Set (StatedSp (n + 3) K)) := by
  intro hperf
  have : Finite (StatedSp (n + 3) K) := by
    have : Finite (GL (Fin (n + 3) ⊕ Fin (n + 3)) K) := inferInstance
    exact Subtype.finite
  have h12 := one_ne_two_fin (n := n)
  have hcore := CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf
  have hmem := shortBlock_sl2Upper_mem_centralizer_twoCentralElt (n := n) (K := K) ha
  have hent := mat_shortBlock_sl2Upper_one_two (n := n) (K := K)
  rcases ha with rfl | rfl
  · have := isSolvable_SL2_of_natCard_two hK
    have hle := perfectCore_le_map_ker_of_isSolvable _ (a2Coord h12 (one_ne_zero (α := K)))
    rw [hcore] at hle
    obtain ⟨g', hg', hgg'⟩ := hle hmem
    have hg'v : (g' : StatedSp (n + 3) K) = shortBlock K h12 (sl2Upper (1 : K)) := hgg'
    have h2 : wBlock 1 2 (mat (n + 3) K (g' : StatedSp (n + 3) K)) = 1 :=
      congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) (MonoidHom.mem_ker.1 hg')
    have h4 : mat (n + 3) K (g' : StatedSp (n + 3) K) (Sum.inl 1) (Sum.inl 2) = 0 := by
      have := congrFun (congrFun h2 0) 1
      simpa [wBlock] using this
    rw [hg'v, hent] at h4
    exact one_ne_zero h4
  · have hle := perfectCore_le_map_ker_of_isSolvable _ (c2Coord (n := n) (K := K))
    rw [hcore] at hle
    obtain ⟨g', hg', hgg'⟩ := hle hmem
    have h1 := MonoidHom.mem_ker.1 hg'
    have hg'v : (g' : StatedSp (n + 3) K) = shortBlock K h12 (sl2Upper (1 : K)) := hgg'
    simp only [c2Coord, MonoidHom.coe_mk, OneHom.coe_mk, hg'v, hent] at h1
    exact one_ne_zero (congrArg Multiplicative.toAdd h1)

end Witness

section Class

variable [Finite K] [CharP K 2]

theorem exists_conj_eq_siegDiag_two (hK : Nat.card K = 2) {n : ℕ} {X : Type*} [Group X]
    [Finite X] (e : X ≃* StatedSp (n + 3) K) {x : X} (hx : x ≠ 1)
    (hperf : ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆ = centralizer ({x} : Set X))
    {p : Fin (n + 3)}
    (hcard : Nat.card (centralizer ({x} : Set X)) =
      Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (n + 3) K))))
    (p' : Fin (n + 3)) :
    ∃ c : X, c * x * c⁻¹ = e.symm (siegDiag K p' 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : (Nat.card (centralizer ({x} : Set X))).factorization 2 =
      (Nat.card X).factorization 2 := by
    rw [hcard, factorization_card_centralizer_siegDiag (n + 1) p, Nat.card_congr e.toEquiv]
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 (centralizer ({x} : Set X))) := inferInstance
  set U : Subgroup X := (U₀ : Subgroup (centralizer ({x} : Set X))).map
    (centralizer ({x} : Set X)).subtype with hU
  have hUc : Nat.card U = 2 ^ (Nat.card X).factorization 2 := by
    rw [hU, Subgroup.card_map_of_injective (subtype_injective _), U₀.card_eq_multiplicity, hv]
  let U' : Sylow 2 X := Sylow.ofCard U hUc
  have hxU : ∀ u ∈ (U' : Subgroup X), u * x = x * u := by
    rintro _ ⟨u, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 u.2
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep_of_mulEquiv e hx hxU
  have hperfκ : ⁅centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K)),
      centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K))⁆ =
      centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K)) := by
    have hmap := map_centralizer_singleton_mulEquiv ((MulAut.conj c).trans e) x
    have hφx : ((MulAut.conj c).trans e) x = spRep (K := K) n κ := by
      rw [MulEquiv.trans_apply, MulAut.conj_apply, hc, MulEquiv.apply_symm_apply]
    rw [hφx] at hmap
    rw [← hmap, ← Subgroup.map_commutator, hperf]
  cases κ with
  | b1 =>
    rw [spRep_b1_eq_siegDiag] at hc
    set π : Equiv.Perm (Fin (n + 3)) := Equiv.swap p' 1 with hπ
    have hz := conj_permSp_siegDiag (K := K) π p' 1
    rw [hπ, Equiv.swap_apply_left] at hz
    refine ⟨(e.symm (permSp K π))⁻¹ * c, ?_⟩
    rw [_root_.mul_inv_rev, inv_inv]
    calc (e.symm (permSp K π))⁻¹ * c * x * (c⁻¹ * e.symm (permSp K π)) =
        (e.symm (permSp K π))⁻¹ * (c * x * c⁻¹) * e.symm (permSp K π) := by group
      _ = (e.symm (permSp K π))⁻¹ * e.symm (permSp K π * siegDiag K p' 1 *
          (permSp K π)⁻¹) * e.symm (permSp K π) := by rw [hc, ← hz, hπ]
      _ = e.symm (siegDiag K p' 1) := by
          rw [map_mul, map_mul, map_inv]
          group
  | a2 =>
    rw [spRep_a2_eq] at hperfκ
    exact absurd hperfκ (commutator_centralizer_twoCentralElt_ne_two hK (Or.inl rfl))
  | c2 =>
    rw [spRep_c2_eq] at hperfκ
    exact absurd hperfκ (commutator_centralizer_twoCentralElt_ne_two hK (Or.inr rfl))

end Class

section Aut

variable [Finite K] [CharP K 2] {m : ℕ}

omit [Finite K] in
theorem mem_transvRadical_of_normal_of_isPGroup (hK : Nat.card K = 2) (hm : 3 ≤ m)
    {p : Fin (m + 1)}
    {R : Subgroup (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)))} (hR : R.Normal)
    (h2 : IsPGroup 2 R) {r : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))}
    (hr : r ∈ R) : (r : StatedSp (m + 1) K) ∈ transvRadical K p := by
  set π := comprHom K p (n := m + 1) with hπ
  set N : Subgroup (complSp K p) := (R.map π).subgroupOf (complSp K p) with hNdef
  have hN : N.Normal := by
    constructor
    intro a ha d
    obtain ⟨r', hr', hr'a⟩ := ha
    set d' : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
      ⟨d, complSp_le_centralizer_siegDiag d.2⟩ with hd'
    have hπd : π d' = d := comprHom_of_mem_complSp (g := d') d.2
    refine ⟨d' * r' * d'⁻¹, hR.conj_mem r' hr' d', ?_⟩
    rw [map_mul, map_mul, map_inv, hπd, hr'a]
    rfl
  have hN2 : IsPGroup 2 N := (h2.map π).comap_subtype
  have hNbot := eq_bot_of_normal_of_isPGroup_of_mulEquiv_two hK hm (complSpEquiv (K := K) p).symm
    N hN hN2
  have hmem : (⟨π r, comprHom_mem_complSp r⟩ : complSp K p) ∈ N := ⟨r, hr, rfl⟩
  rw [hNbot, mem_bot] at hmem
  exact (mem_transvRadical_iff_comprHom_eq_one (g := r)).2 (congrArg Subtype.val hmem)

omit [Finite K] in
theorem mul_inv_comprHom_mem_transvRadical {n : ℕ} {p : Fin n}
    (g : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
    (g : StatedSp n K) * (comprHom K p g)⁻¹ ∈ transvRadical K p := by
  set m' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
    ⟨comprHom K p g, complSp_le_centralizer_siegDiag (comprHom_mem_complSp g)⟩ with hm'
  have h1 : comprHom K p m' = comprHom K p g := comprHom_of_mem_complSp (comprHom_mem_complSp g)
  have h2 : ((g * m'⁻¹ : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) : StatedSp n K) ∈
      transvRadical K p := by
    rw [mem_transvRadical_iff_comprHom_eq_one, map_mul, map_inv, h1, mul_inv_cancel]
  simpa [m'] using h2

theorem exists_mem_complSp_conj_of_mulEquiv (hK : Nat.card K = 2) (hm : 3 ≤ m)
    {p : Fin (m + 1)}
    (φ : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) ≃*
      centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) :
    ∃ δ ∈ complSp K p, ∀ (d : StatedSp (m + 1) K) (hd : d ∈ complSp K p),
      (φ ⟨d, complSp_le_centralizer_siegDiag hd⟩ : StatedSp (m + 1) K) * (δ * d * δ⁻¹)⁻¹ ∈
        transvRadical K p := by
  set Q' : Subgroup (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) :=
    (transvRadical K p).subgroupOf (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)))
    with hQ'
  have hQ'2 : IsPGroup 2 Q' := isPGroup_transvRadical.comap_subtype
  have hback : ∀ y : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      (φ y : StatedSp (m + 1) K) ∈ transvRadical K p →
      (y : StatedSp (m + 1) K) ∈ transvRadical K p := by
    intro y hy
    have hR : (Q'.map φ.symm.toMonoidHom).Normal := by
      have hQn : Q'.Normal := by
        constructor
        intro a ha c
        have h1 : (c : StatedSp (m + 1) K) ∈ normalizer (transvRadical K p : Set _) :=
          sup_le le_normalizer complSp_le_normalizer_transvRadical
            ((centralizer_siegDiag_eq_sup (K := K) (p := p)).le c.2)
        exact (mem_normalizer_iff.1 h1 a).1 ha
      exact hQn.map _ φ.symm.surjective
    have h2 : IsPGroup 2 (Q'.map φ.symm.toMonoidHom) := hQ'2.map _
    have hyR : y ∈ Q'.map φ.symm.toMonoidHom := ⟨φ y, hy, by simp⟩
    exact mem_transvRadical_of_normal_of_isPGroup hK hm hR h2 hyR
  set ι : complSp K p →* centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
    Subgroup.inclusion complSp_le_centralizer_siegDiag with hι
  set α : complSp K p →* complSp K p :=
    ((comprHom K p).comp (φ.toMonoidHom.comp ι)).codRestrict (complSp K p)
      (fun y => comprHom_mem_complSp _) with hα
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : comprHom K p (φ (ι d)) = 1 := congrArg Subtype.val hd
    have h2 := hback (ι d) ((mem_transvRadical_iff_comprHom_eq_one (g := φ (ι d))).2 h1)
    have h3 : (d : StatedSp (m + 1) K) = 1 :=
      (Subgroup.disjoint_def.1 disjoint_transvRadical_complSp) h2 d.2
    exact Subtype.ext h3
  set αE : complSp K p ≃* complSp K p := MulEquiv.ofBijective α hαinj.bijective_of_finite
  set β : MulAut (StatedSp m K) :=
    ((complSpEquiv (K := K) p).trans αE).trans (complSpEquiv (K := K) p).symm with hβ
  obtain ⟨s, σ, hs⟩ := exists_eq_conj_mul_fieldSp hm β
  have hσ : σ = 1 := by
    ext c
    rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl <;> simp
  rw [hσ, map_one, mul_one] at hs
  refine ⟨((complSpEquiv (K := K) p s : complSp K p) : StatedSp (m + 1) K),
    (complSpEquiv (K := K) p s).2, fun d hd => ?_⟩
  have hαd : ((α ⟨d, hd⟩ : complSp K p) : StatedSp (m + 1) K) =
      ((complSpEquiv (K := K) p s : complSp K p) : StatedSp (m + 1) K) * d *
        ((complSpEquiv (K := K) p s : complSp K p) : StatedSp (m + 1) K)⁻¹ := by
    have h1 : αE ⟨d, hd⟩ = complSpEquiv (K := K) p
        (β ((complSpEquiv (K := K) p).symm ⟨d, hd⟩)) := by
      rw [hβ]
      simp
    rw [hs, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    have h3 : αE ⟨d, hd⟩ = α ⟨d, hd⟩ := rfl
    rw [h3] at h2
    simpa using h2
  have h3 := mul_inv_comprHom_mem_transvRadical (φ ⟨d, complSp_le_centralizer_siegDiag hd⟩)
  rw [← hαd]
  exact h3

theorem exists_conj_map_nsTorusSp_eq (hK : Nat.card K = 2) (hm : 3 ≤ m) {p k : Fin (m + 1)}
    (hkp : k ≠ p) {H : Type*} [Group H] {ψ₁ ψ₂ : StatedSp (m + 1) K →* H}
    (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂)
    (hC : (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).map ψ₁ =
      (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).map ψ₂) :
    ∃ c ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      (nsTorusSp K k).map ψ₁ = ((nsTorusSp K k).map (MulAut.conj c).toMonoidHom).map ψ₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSp (m + 1) K) := by
    have : Finite (GL (Fin (m + 1) ⊕ Fin (m + 1)) K) := inferInstance
    exact Subtype.finite
  let e₁ := Subgroup.equivMapOfInjective
    (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) ψ₁ h₁
  let e₂ := Subgroup.equivMapOfInjective
    (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) ψ₂ h₂
  let φ := e₁.trans ((MulEquiv.subgroupCongr hC).trans e₂.symm)
  have hφ : ∀ y : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      ψ₂ (φ y : StatedSp (m + 1) K) = ψ₁ (y : StatedSp (m + 1) K) := by
    intro y
    have h1 : ((e₂ (φ y) : _) : H) = ψ₂ (φ y : StatedSp (m + 1) K) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ _
    have h2 : e₂ (φ y) = MulEquiv.subgroupCongr hC (e₁ y) := e₂.apply_symm_apply _
    rw [← h1, h2]
    rfl
  obtain ⟨δ, hδD, hδ⟩ := exists_mem_complSp_conj_of_mulEquiv hK hm φ
  have hXD : nsTorusSp K k ≤ complSp K p := nsTorusSp_le_complSp hkp
  have hXC : nsTorusSp K k ≤ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
    hXD.trans complSp_le_centralizer_siegDiag
  set T : Subgroup (StatedSp (m + 1) K) := (nsTorusSp K k).map (MulAut.conj δ).toMonoidHom
    with hT
  set Tφ : Subgroup (StatedSp (m + 1) K) :=
    ((nsTorusSp K k).subgroupOf (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)))).map
      ((centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype.comp
        φ.toMonoidHom) with hTφ
  have hTD : T ≤ complSp K p := by
    rintro _ ⟨x, hx, rfl⟩
    exact (complSp K p).mul_mem ((complSp K p).mul_mem hδD (hXD hx)) ((complSp K p).inv_mem hδD)
  have hTN : T ≤ normalizer (transvRadical K p : Set (StatedSp (m + 1) K)) :=
    hTD.trans complSp_le_normalizer_transvRadical
  have hQT : transvRadical K p ⊓ T = ⊥ :=
    disjoint_iff.1 (disjoint_transvRadical_complSp.mono_right hTD)
  have hS : Tφ ≤ T ⊔ transvRadical K p := by
    rintro _ ⟨⟨x, hxC⟩, hx, rfl⟩
    have hxX : x ∈ nsTorusSp K k := hx
    have h1 := hδ x (hXD hxX)
    change (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) ∈ T ⊔ transvRadical K p
    have e : (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) =
        ((φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * (δ * x * δ⁻¹)⁻¹) * (δ * x * δ⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_right h1) (mem_sup_left ⟨x, hxX, rfl⟩)
  have hcardX : Nat.card (nsTorusSp K k) = 3 := card_nsTorusSp k
  have hinjφ : Function.Injective
      ((centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype.comp
        φ.toMonoidHom) := fun a b hab => φ.injective (Subtype.ext hab)
  have hcardTφ : Nat.card Tφ = 3 := by
    rw [hTφ, Subgroup.card_map_of_injective hinjφ,
      CFSG.LieType.Chevalley.card_subgroupOf_of_le hXC, hcardX]
  have hcardT : Nat.card T = 3 := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj δ).injective, hcardX]
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup isPGroup_transvRadical hTN hQT
    hS (by rw [hcardTφ]; decide)
  have heqT : Tφ.map (MulAut.conj u).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardT, Subgroup.card_map_of_injective (MulAut.conj u).injective, hcardTφ])
  have huC := transvRadical_le_centralizer (K := K) (p := p) hu
  have hδC := complSp_le_centralizer_siegDiag (K := K) (p := p) hδD
  refine ⟨u⁻¹ * δ, mul_mem (inv_mem huC) hδC, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxC := hXC hx
    have hmem : (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) ∈ Tφ := ⟨⟨x, hxC⟩, hx, rfl⟩
    have h2 : u * (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * u⁻¹ ∈ T := by
      rw [← heqT]
      exact ⟨_, hmem, rfl⟩
    obtain ⟨x₂, hx₂, hx₂eq⟩ := h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx₂eq
    refine ⟨(u⁻¹ * δ) * x₂ * (u⁻¹ * δ)⁻¹, ⟨x₂, hx₂, rfl⟩, ?_⟩
    rw [← hφ ⟨x, hxC⟩]
    congr 1
    calc (u⁻¹ * δ) * x₂ * (u⁻¹ * δ)⁻¹ = u⁻¹ * (δ * x₂ * δ⁻¹) * u := by group
      _ = u⁻¹ * (u * (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * u⁻¹) * u := by rw [hx₂eq]
      _ = (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) := by group
  · rintro _ ⟨_, ⟨x₂, hx₂, rfl⟩, rfl⟩
    have h2 : δ * x₂ * δ⁻¹ ∈ Tφ.map (MulAut.conj u).toMonoidHom := by
      rw [heqT]
      exact ⟨x₂, hx₂, rfl⟩
    obtain ⟨_, ⟨⟨x, hxC⟩, hx, rfl⟩, hy⟩ := h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype] at hy
    refine ⟨x, hx, ?_⟩
    change ψ₁ x = ψ₂ ((MulAut.conj (u⁻¹ * δ)).toMonoidHom x₂)
    rw [← hφ ⟨x, hxC⟩]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) =
        u⁻¹ * (u * (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * u⁻¹) * u := by group
      _ = u⁻¹ * (δ * x₂ * δ⁻¹) * u := by rw [hy]
      _ = (u⁻¹ * δ) * x₂ * (u⁻¹ * δ)⁻¹ := by group

end Aut

end CFSG.SeitzReduction.SymplecticPilot
