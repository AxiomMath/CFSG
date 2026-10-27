module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIReeSocleSteps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeOuterInvolutions

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_socle_component {A : Type} [Group A] [Finite A] {W : Subgroup A} {a : A}
    (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (2 * m + 1)) (φ : W ≃* ReeTag.G2.reeGamma K m)
    {ρ : A →* MulAut (ReeTag.G2.reeGamma K m)} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) (hZ : center (ReeTag.G2.reeGamma K m) = ⊥)
    {t : ReeTag.G2.reeGamma K m} (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH m K (-1))
    {B : Subgroup (ReeTag.G2.reeGamma K m)}
    (hIDP : CFSG.Walter.JT.IsInternalDirectProduct (zpowers t) B (centralizer {t}))
    (hBs : IsSimpleGroup B) (hBnab : ∃ x y : B, x * y ≠ y * x) :
    ∃ g : ReeTag.G2.reeGamma K m,
      ρ a = MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹ ∧
      (centralizer {a}).map ρ = ρ.range ⊓
        (centralizer {MulAut.conj t}).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      (W ⊓ centralizer {a}).map ρ =
        ((centralizer {t}).map MulAut.conj).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      L.map ρ = (B.map MulAut.conj).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
      (∃ θ : L ≃* B, ∀ l : L,
        MulAut.conj (θ l : ReeTag.G2.reeGamma K m) = (MulAut.conj g)⁻¹ * ρ l * MulAut.conj g) ∧
      ((centralizer {a}).map ρ).map
          (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m))) =
        ρ.range.map (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m))) ∧
      (centralizer {a}).map ρ ⊓
          (QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m))).ker =
        (W ⊓ centralizer {a}).map ρ := by
  have htt : t = ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩ := Subtype.ext ht
  have hfus : ∀ x : ReeTag.G2.reeGamma K m, orderOf x = 2 →
      ∃ y : ReeTag.G2.reeGamma K m, y * x * y⁻¹ = t := by
    rw [htt]
    exact ree_involution_fusion hK
  have hρa2 : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
  obtain ⟨-, hinv⟩ := CatalogueBSmallRee.small_Ree_automorphism_involutions_inner m hm K hK
  obtain ⟨z, ⟨hz2, hρz⟩, -⟩ := hinv (ρ a) hρa2
  obtain ⟨y, hy⟩ := hfus z hz2
  obtain ⟨g, hg⟩ : ∃ g : ReeTag.G2.reeGamma K m, g = y⁻¹ := ⟨_, rfl⟩
  have hz : z = g * t * g⁻¹ := by
    rw [hg, ← hy]
    group
  have hρa : ρ a = MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹ := by
    rw [hρz, hz, map_mul, map_mul, map_inv]
  have hfusz : ∀ x : ReeTag.G2.reeGamma K m, orderOf x = 2 →
      ∃ y' : ReeTag.G2.reeGamma K m, y' * x * y'⁻¹ = z := by
    intro x hx
    obtain ⟨y₁, hy₁⟩ := hfus x hx
    refine ⟨g * y₁, ?_⟩
    rw [hz, ← hy₁]
    group
  have hW : W.map ρ = OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m) :=
    map_eq_range_conj φ hρW
  have : Finite (ReeTag.G2.reeGamma K m) := Finite.of_equiv _ φ.toEquiv
  obtain ⟨hCA, hCW, hLimg, hθ⟩ := socle_conj_component hLCW hinj hW hZ hIDP hBs hBnab hρa
  exact ⟨g, hρa, hCA, hCW, hLimg, hθ, socle_outer_restrict hinj hW hZ hz2 hfusz hρz⟩

theorem faithful_small_Ree_socle_small_source_involution_selector_explicit
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hm : 1 ≤ m) (hK : Nat.card K = 3 ^ (2 * m + 1)) (φ : W ≃* ReeTag.G2.reeGamma K m) :
    ∃ ρ : A →* MulAut (ReeTag.G2.reeGamma K m), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (ReeTag.G2.reeGamma K m), (∀ w : W, ρ' w = MulAut.conj (φ w)) →
        ρ' = ρ) ∧
      p = 3 ∧ f = 2 * m + 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 ∧
      IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      ∃ (t : ReeTag.G2.reeGamma K m) (ψ : SL2 K →* ReeTag.G2.reeGamma K m),
        (t : ModGL ReeTag.G2.tag K) = smallReeH m K (-1) ∧
        (∀ b : K, (ψ (uSL b) : ModGL ReeTag.G2.tag K) = smallReeU m K 0 b 0) ∧
        (∀ w₀ : WeylGroup ReeTag.G2.tag, (∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
            (coxeterSystem ReeTag.G2.tag).length w₀) →
          (ψ WSL : ModGL ReeTag.G2.tag K) = canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀) ∧
        (∀ r : Kˣ, (ψ (HSL r) : ModGL ReeTag.G2.tag K) = smallReeH m K (r ^ (3 + 3 * 3 ^ m))) ∧
        (∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) ∧ ψ.ker = center (SL2 K) ∧
        CFSG.Walter.JT.IsInternalDirectProduct (zpowers t) ψ.range (centralizer {t}) ∧
        Nat.card (zpowers t) = 2 ∧
        (∃ eB : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* ψ.range,
          ∀ g, (eB (QuotientGroup.mk g) : ReeTag.G2.reeGamma K m) = ψ g) ∧
        IsSimpleGroup ψ.range ∧ (∃ x y : ψ.range, x * y ≠ y * x) ∧
        (let π := QuotientGroup.mk' (OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m))
         let Mt := centralizer {MulAut.conj t}
         let Nt := (centralizer {t}).map MulAut.conj
         let Fld := ReeTag.G2.reeGammaFld K m
         CFSG.Walter.JT.IsInternalDirectProduct ((zpowers t).map MulAut.conj)
             (ψ.range.map MulAut.conj) Nt ∧
           (∀ β : MulAut (ReeTag.G2.reeGamma K m), β ∈ Mt ↔ β t = t) ∧
           Mt ⊓ OuterAutomorphisms.inner (ReeTag.G2.reeGamma K m) = Nt ∧
           Mt.map π = ⊤ ∧ Mt ⊓ π.ker = Nt ∧
           (∀ (σ : K ≃+* K) (g : ReeTag.G2.reeGamma K m),
             ((ReeTag.G2.reeGammaFieldAut K m σ g : ReeTag.G2.reeGamma K m) :
               ModGL ReeTag.G2.tag K) = Units.map (entrywiseHom σ.toRingHom) (g : ModGL _ K)) ∧
           Nat.card Fld = 2 * m + 1 ∧ Nat.card (Fld.map π) = 2 * m + 1 ∧ Fld ≤ Mt ∧
           (∃ (R : Subgroup (Outer (ReeTag.G2.reeGamma K m)))
             (χ : Outer (ReeTag.G2.reeGamma K m) →* (K ≃+* K)), χ.ker = R ∧
             (∀ σ : K ≃+* K, χ (QuotientGroup.mk (ReeTag.G2.reeGammaFieldAut K m σ)) = σ) ∧
             R.Normal ∧ IsPGroup 3 R ∧ R.IsComplement' (Fld.map π)) ∧
           (∀ R : Subgroup (Outer (ReeTag.G2.reeGamma K m)), R.Normal →
             R.IsComplement' (Fld.map π) →
             let Tt := Mt ⊓ R.comap π
             Nt ≤ Tt ∧ (Nt.subgroupOf Tt).Normal ∧ (Tt.subgroupOf Mt).Normal ∧
               Tt.map π = R ∧ Tt ⊓ π.ker = Nt ∧ Tt ⊓ Fld = ⊥ ∧
               (∃ _ : (Nt.subgroupOf Tt).Normal, ∃ e : Tt ⧸ Nt.subgroupOf Tt ≃* R,
                 ∀ v : Tt, (e (QuotientGroup.mk v) : Outer (ReeTag.G2.reeGamma K m)) = π v) ∧
               ∀ β ∈ Mt, ∃! vτ : Tt × Fld,
                 (vτ.1 : MulAut (ReeTag.G2.reeGamma K m)) * vτ.2 = β) ∧
           ∃ g : ReeTag.G2.reeGamma K m,
             ρ a = MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹ ∧
             (centralizer {a}).map ρ = ρ.range ⊓
               Mt.map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
             (W ⊓ centralizer {a}).map ρ = Nt.map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
             L.map ρ = (ψ.range.map MulAut.conj).map (MulAut.conj (MulAut.conj g)).toMonoidHom ∧
             (∃ θ : L ≃* ψ.range, ∀ l : L, MulAut.conj (θ l : ReeTag.G2.reeGamma K m) =
               (MulAut.conj g)⁻¹ * ρ l * MulAut.conj g) ∧
             ((centralizer {a}).map ρ).map π = ρ.range.map π ∧
             (centralizer {a}).map ρ ⊓ π.ker = (W ⊓ centralizer {a}).map ρ) := by
  classical
  have : IsSimpleGroup (ReeTag.G2.reeGamma K m) := φ.symm.isSimpleGroup
  have hnabP : ∃ x y : ReeTag.G2.reeGamma K m, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnonab
    refine ⟨φ x, φ y, fun hc => hxy (φ.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  have hZ := center_eq_bot_of_isSimpleGroup hnabP
  obtain ⟨ρ, hinj, hρW, huniq, -⟩ := socle_extension hCW φ hZ
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hLnab := exists_ne_commute_of_isQuasisimple hL.2.2
  obtain ⟨ψ, hψu, hψW, hψH, hψ1, hψker, hIDP, ⟨eB, heB⟩, hBs, hBnab⟩ :=
    ree_socle_psi_structure hm hK
  obtain ⟨g, hρa, hCA, hCWa, hLimg, ⟨θ, hθ⟩, hπs, hπk⟩ :=
    ree_socle_component ha hLCW hm hK φ hinj hρW hZ (t := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩)
      rfl hIDP hBs hBnab
  have : IsSimpleGroup ψ.range := hBs
  have hLs : IsSimpleGroup L := θ.isSimpleGroup
  have eL : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := θ.trans eB.symm
  have hS := ree_socle_source (L := L) hm hK eL hp2 hsrc
  have hO := ree_socle_outer hm hK (t := ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩) rfl hIDP hZ
  have ht2 := orderOf_smallReeH_neg_one (a := m) hK
  exact ⟨ρ, hinj, hρW, huniq, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2, hLs, hLnab,
    ⟨_, smallReeH_neg_one_mem_reeGamma hK⟩, ψ, rfl, hψu, hψW, hψH, hψ1, hψker, hIDP,
    by rw [Nat.card_zpowers, ht2], ⟨eB, heB⟩, hBs, hBnab, hO.1, hO.2.1, hO.2.2.1, hO.2.2.2.1,
    hO.2.2.2.2.1, hO.2.2.2.2.2.1, hO.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2.2.1,
    hO.2.2.2.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2.2.2.2, g, hρa, hCA, hCWa, hLimg, ⟨θ, hθ⟩, hπs, hπk⟩

end CFSG.ComponentClassification.OutcomeLocal
