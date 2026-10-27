module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE6Four
public import CFSG.RankThree.PartOne.KE.E7FourPerX

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups commutatorElement Pointwise

section Abstract

theorem map_mem_centralizer_of_pElem {C G : Type*} [Group C] [Finite C] [Group G] {p : ℕ}
    (hp : p.Prime) (S : Sylow p C) (ψ : C →* G) (X : Subgroup G)
    (hN : ∀ u : C, ψ u ∈ Subgroup.normalizer (X : Set G))
    (hS : ∀ s ∈ (S : Subgroup C), ψ s ∈ Subgroup.centralizer (X : Set G)) {y : C}
    (hy : ∃ k : ℕ, y ^ p ^ k = 1) : ψ y ∈ Subgroup.centralizer (X : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hy
  have hpg : IsPGroup p (Subgroup.zpowers y) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S Q
  have hyQ : y ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply] at hyQ
  have hs : g⁻¹ * y * g ∈ (S : Subgroup C) := by simpa using hyQ
  have hψs := hS _ hs
  have hyeq : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [Subgroup.mem_centralizer_iff] at hψs ⊢
  intro x hx
  have hx' : (ψ g)⁻¹ * x * ψ g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.1 (hN g⁻¹) x).1 hx
    simpa [map_inv] using this
  have h1 := hψs _ hx'
  rw [hyeq, map_mul, map_mul, map_inv]
  calc x * (ψ g * ψ (g⁻¹ * y * g) * (ψ g)⁻¹)
      = ψ g * (((ψ g)⁻¹ * x * ψ g) * ψ (g⁻¹ * y * g)) * (ψ g)⁻¹ := by group
    _ = ψ g * (ψ (g⁻¹ * y * g) * ((ψ g)⁻¹ * x * ψ g)) * (ψ g)⁻¹ := by rw [h1]
    _ = ψ g * ψ (g⁻¹ * y * g) * (ψ g)⁻¹ * x := by group

theorem oddPCoreInClosure_of_closure {C G : Type*} [Group C] [Finite C] [Group G] {p : ℕ}
    (F : C →* G) (hF : Function.Injective F) (X : Subgroup G)
    (hX : ∀ y : C, (∃ k : ℕ, y ^ p ^ k = 1) → F y ∈ X) (W : Subgroup G)
    (hW : ∀ c : C, F c ∈ X → F c ∈ W) (hWodd : Odd (Nat.card W)) : OddPCoreInClosure p C := by
  intro K hK hKle hKcop
  have hcl : pElemClosure p C ≤ X.comap F := by
    rw [pElemClosure, Subgroup.closure_le]
    intro y hy
    exact hX y hy
  have hle : ∀ k ∈ K, F k ∈ W := fun k hk => hW k (hcl (hKle hk))
  let ψ : K →* W :=
    { toFun := fun k => ⟨F k, hle k k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hF (congrArg Subtype.val h))
  exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)

theorem oddPCoreInClosure_of_closure_quasisimple {C G : Type*} [Group C] [Finite C] [Group G]
    {p : ℕ} (hp : p.Prime) (F : C →* G) (hF : Function.Injective F) (Q : Subgroup G)
    (hQD : Q ≤ F.range) (hQn : ∀ c : C, ∀ q ∈ Q, F c * q * (F c)⁻¹ ∈ Q)
    (hQq : CFSG.IsQuasisimple Q) (hpQ : p ∣ Nat.card Q) (X : Subgroup G)
    (hX : ∀ y : C, (∃ k : ℕ, y ^ p ^ k = 1) → F y ∈ X) (W : Subgroup G)
    (hW : ∀ c : C, (∀ q ∈ Q, F c * q = q * F c) → F c ∈ X → F c ∈ W)
    (hWodd : Odd (Nat.card W)) : OddPCoreInClosure p C := by
  classical
  set Q' : Subgroup C := Q.comap F with hQ'
  haveI hQ'n : Q'.Normal := ⟨fun q hq c => by
    rw [hQ', Subgroup.mem_comap] at hq ⊢
    rw [map_mul, map_mul, map_inv]
    exact hQn c _ hq⟩
  have hmap : Q'.map F = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hQD
  let e : Q' ≃* Q := (Subgroup.equivMapOfInjective Q' F hF).trans (MulEquiv.subgroupCongr hmap)
  have hq : CFSG.IsQuasisimple Q' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQq
  have hpQ' : p ∣ Nat.card Q' := by rw [Nat.card_congr e.toEquiv]; exact hpQ
  intro K hK hKle hKcop
  haveI : K.Normal := hK
  have hcomm : ⁅K, Q'⁆ = ⊥ :=
    commutator_eq_bot_of_normal_pPrime_of_quasisimple hp Q' hq hpQ' K hKcop
  have hKc : K ≤ Subgroup.centralizer (Q' : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hcl : pElemClosure p C ≤ X.comap F := by
    rw [pElemClosure, Subgroup.closure_le]
    intro y hy
    exact hX y hy
  have hle : ∀ k ∈ K, F k ∈ W := fun k hk => by
    refine hW k (fun q hqQ => ?_) (hcl (hKle hk))
    obtain ⟨q', rfl⟩ : q ∈ F.range := hQD hqQ
    have hq' : q' ∈ Q' := hqQ
    have h1 : q' * k = k * q' := Subgroup.mem_centralizer_iff.1 (hKc hk) q' hq'
    rw [← map_mul, ← map_mul, h1]
  let ψ : K →* W :=
    { toFun := fun k => ⟨F k, hle k k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hF (congrArg Subtype.val h))
  exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)

end Abstract

section Torus

variable {τ : Tag} {L : Type} [Field L]


theorem odd_card_range_inf_torus {C : Type*} [Group C] [Finite C] [CharP L 2]
    (ψ : C →* ModGL τ L) :
    Odd (Nat.card (ψ.range ⊓ torusGroup τ L : Subgroup (ModGL τ L))) := by
  classical
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  haveI : Finite (ψ.range ⊓ torusGroup τ L : Subgroup (ModGL τ L)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : ψ.range ⊓ torusGroup τ L ≤ ψ.range))
      (Subgroup.inclusion_injective _)
  by_contra hnodd
  have h2 : 2 ∣ Nat.card (ψ.range ⊓ torusGroup τ L : Subgroup (ModGL τ L)) :=
    (Nat.not_odd_iff_even.1 hnodd).two_dvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := (ψ.range ⊓ torusGroup τ L : Subgroup (ModGL τ L))) 2 h2
  have hw2 : (w : ModGL τ L) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hw, pow_orderOf_eq_one, Subgroup.coe_one]
  have h1 := eq_one_of_sq_eq_one_of_mem_torusGroup w.2.2 hw2
  have hw1 : w = 1 := Subtype.ext h1
  rw [hw1, orderOf_one] at hw
  omega

end Torus

section RootChar

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_eq_one_of_fixed_root {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    {q m : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : 0 < q) {b : Fin τ.rank → Lˣ}
    (hb : b ∈ fixedCharTuples M Fr) {r : Fin τ.rank → ℤ} (hr : M *ᵥ r = r)
    (hbm : ∀ i, b i ^ m = 1) (hcop : Nat.Coprime m (q - 1)) : rootChar b r = 1 := by
  have h1 : rootChar b r ^ m = 1 := CTTorus.rootChar_pow_eq_one hbm r
  have h2 : rootChar b r = rootChar b r ^ q := by
    have := (mem_fixedCharTuples_iff.1 hb) r
    rw [hr, CTTorus.map_units_eq_pow hFr] at this
    exact this
  have h3 : rootChar b r ^ (q - 1) = 1 := by
    have h4 : rootChar b r ^ q = rootChar b r ^ (q - 1) * rootChar b r := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [h4] at h2
    exact (mul_eq_right.1 h2.symm)
  have h5 : rootChar b r ^ Nat.gcd m (q - 1) = 1 := pow_gcd_eq_one.2 ⟨h1, h3⟩
  rwa [hcop, pow_one] at h5

end RootChar

section CentTorus

variable {L : Type} [Field L]

section Def


@[expose] def CentTorus (L : Type) [Field L] (S : Set (Fin Tag.E7.rank → ℤ)) : Prop :=
  ∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L S,
    y ∈ Subgroup.centralizer (rootSpan .E7 L S : Set (ModGL .E7 L)) → y ∈ torusGroup .E7 L

end Def


theorem centTorus_pair {r : Fin Tag.E7.rank → ℤ} (hr : IsRoot .E7 r) : CentTorus L {r, -r} := by
  intro y hy hc
  have hroots : ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), IsRoot .E7 α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have hrange : rootSpan .E7 L {r, -r} = (rootSL2 .E7 L r).range := by
    rw [rootSpan, iSup_insert, iSup_singleton, ← range_rootSL2_of_isRoot hr]
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup .E7 L)
    (rootSpan .E7 L {r, -r}) (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hroots)
  have hy' : y ∈ ((torusGroup .E7 L ⊔ rootSpan .E7 L {r, -r} : Subgroup (ModGL .E7 L)) :
    Set (ModGL .E7 L)) := hy
  rw [e] at hy'
  have hy2 : y ∈ (torusGroup .E7 L : Set (ModGL .E7 L)) *
      (rootRankOneGroup .E7 L r : Set (ModGL .E7 L)) := by
    obtain ⟨t, ht, q, hq', rfl⟩ := hy'
    rw [SetLike.mem_coe, hrange] at hq'
    exact ⟨t, ht, q, hq', rfl⟩
  have hall : ∀ A : SL2 L, y * rootSL2 .E7 L r A = rootSL2 .E7 L r A * y := fun A =>
    (Subgroup.mem_centralizer_iff.1 hc (rootSL2 .E7 L r A)
      (by rw [SetLike.mem_coe, hrange]; exact ⟨A, rfl⟩)).symm
  exact mem_torusGroup_of_centralizes_rootSL2 hr hy2 hall

theorem centTorus_union {S₁ S₂ : Set (Fin Tag.E7.rank → ℤ)} (hS₁ : ∀ r ∈ S₁, IsRoot .E7 r)
    (hS₂ : ∀ r ∈ S₂, IsRoot .E7 r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0)
    (h₁ : CentTorus L S₁) (h₂ : CentTorus L S₂) : CentTorus L (S₁ ∪ S₂) := by
  intro y hy hc
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨h, hh, z₁, hz₁, z₂, hz₂, rfl⟩ := exists_decomp_union hτ hS₁ hS₂ horth hy
  have hcomm := rootSpan_commute_of_orth (L := L) hτ hS₁ hS₂ horth
  have hcu : ∀ u ∈ rootSpan .E7 L S₁, u * (h * z₁ * z₂) = (h * z₁ * z₂) * u := fun u hu =>
    Subgroup.mem_centralizer_iff.1 hc u (by
      rw [SetLike.mem_coe, rootSpan_union_eq]
      exact Subgroup.mem_sup_left hu)
  have hy₁ : h * z₁ ∈ torusGroup .E7 L := by
    refine h₁ _ (mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz₁))
      (Subgroup.mem_centralizer_iff.2 fun u hu => ?_)
    have h2 : u * z₂ = z₂ * u := hcomm u hu z₂ hz₂
    have h3 := hcu u hu
    have h4 : (u * (h * z₁)) * z₂ = ((h * z₁) * u) * z₂ :=
      calc (u * (h * z₁)) * z₂ = u * (h * z₁ * z₂) := by group
        _ = (h * z₁ * z₂) * u := h3
        _ = (h * z₁) * (z₂ * u) := by group
        _ = (h * z₁) * (u * z₂) := by rw [h2]
        _ = ((h * z₁) * u) * z₂ := by group
    exact mul_right_cancel h4
  exact h₂ _ (mul_mem (Subgroup.mem_sup_left hy₁) (Subgroup.mem_sup_right hz₂))
    (Subgroup.mem_centralizer_iff.2 fun u hu => Subgroup.mem_centralizer_iff.1 hc u (by
      rw [SetLike.mem_coe, rootSpan_union_eq]
      exact Subgroup.mem_sup_right hu))

theorem centTorus_S0 : CentTorus L e7F4S0Set := by
  obtain ⟨hα₀, hβ₀, hγ₀⟩ := e7F4_S0_isRoot
  obtain ⟨o12, o13, o23⟩ := e7F4_S0_orth
  have hr : ∀ (r : Fin Tag.E7.rank → ℤ), IsRoot .E7 r →
      ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), IsRoot .E7 α := by
    intro r hr' α hα
    rcases hα with rfl | rfl
    exacts [hr', IsRoot.neg hr']
  have hneg : ∀ (r r' : Fin Tag.E7.rank → ℤ),
      r ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r') = 0 →
        ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), ∀ β ∈ ({r', -r'} : Set (Fin Tag.E7.rank → ℤ)),
          α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro r r' h α hα β hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, h]
  have o13' := hneg _ _ o13
  have o23' := hneg _ _ o23
  have hS12 : ∀ α ∈ ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} : Set (Fin Tag.E7.rank → ℤ)),
      IsRoot .E7 α := fun α hα => hα.elim (hr _ hα₀ α) (hr _ hβ₀ α)
  have o123 : ∀ α ∈ ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} : Set (Fin Tag.E7.rank → ℤ)),
      ∀ β ∈ ({e7F4γ, -e7F4γ} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 :=
    fun α hα β hβ => hα.elim (fun h => o13' α h β hβ) (fun h => o23' α h β hβ)
  have e : e7F4S0Set = ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} ∪ {e7F4γ, -e7F4γ} :
      Set (Fin Tag.E7.rank → ℤ)) := e7F4_S0_eq
  rw [e]
  exact centTorus_union hS12 (hr _ hγ₀) o123
    (centTorus_union (hr _ hα₀) (hr _ hβ₀) (hneg _ _ o12) (centTorus_pair hα₀)
      (centTorus_pair hβ₀))
    (centTorus_pair hγ₀)

end CentTorus

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
