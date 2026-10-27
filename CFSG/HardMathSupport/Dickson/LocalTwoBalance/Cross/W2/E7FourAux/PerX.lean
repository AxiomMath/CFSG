module

public import CFSG.RankThree.PartOne.KE.E7FourPerX

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Special

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem e7_four_perx_special_def (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    (cert : D4A1Cert) (hcert : cert ∈ e7F4Certs)
    (hker : rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b)) ∧
      (∀ y, F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup .E7 L) ∧
      ∃ PD : Subgroup (ModGL .E7 L), PD = rootSpan .E7 L (e7D4Set cert) ⊓
        twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
        PD ≤ ψ.range ∧ Finite PD ∧ CFSG.IsQuasisimple PD ∧
        (∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)), ∀ u ∈ PD,
          ψ d * u * (ψ d)⁻¹ ∈ PD) ∧
        (∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b),
          (∀ u ∈ PD, y * u = u * y) →
            y ∈ Subgroup.centralizer (rootSpan .E7 L (e7D4Set cert) : Set (ModGL .E7 L))) ∧
        (∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b),
          (∀ u ∈ PD, y * u = u * y) →
            ∃ h ∈ torusGroup .E7 L,
              h ∈ Subgroup.centralizer (rootSpan .E7 L (e7D4Set cert) : Set (ModGL .E7 L)) ∧
              ∃ z ∈ rootSpan .E7 L {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r},
                y = h * z) ∧
        ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} ⊆ e7F4S0Set) ∧
        ∀ m : Fin Tag.E7.rank, m.val = 3 → ∃ h₀ : ModGL .E7 L, ∀ Y : SL(2, K),
          h₀ * simpleRootSL2 .E7 L m (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹ ∈ PD := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hgood := e7F4_certs_good cert hcert
  obtain ⟨hr, hrS, hSigma, horth, hfix, u, hu, hcertw⟩ := D4A1Cert.sound hgood
  obtain ⟨-, -, -, -, -, -, -, hab, ha, hbl, -⟩ := hgood
  have hnC : F.n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  have hnr : weylQuotientHom .E7 L ⟨F.n, F.hnm⟩ • toVec Tag.E7.rank cert.r =
      toVec Tag.E7.rank cert.r := by
    rw [F.hnW]
    exact hfix
  obtain ⟨PD, hPD, hfac, hsl⟩ := e7_d4_swap_factor hD4 hf hK
    ((coxeterSystem Tag.E7).wordProd cert.w) F.n F.hnm hnC cert.a cert.b hab
    (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
    (by rw [F.hnW]; exact ⟨u, hu, hcertw⟩)
  have hkerS : rootCharKernel b = e7D4Set cert ∪ {toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} := hker.trans hSigma
  have hroots : ∀ α ∈ e7D4Set cert, IsRoot Tag.E7 α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 _
  have hrootsA : ∀ α ∈ ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} :
      Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have horth' : ∀ α ∈ e7D4Set cert, ∀ β ∈ ({toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro α hα β hβ
    rcases hβ with rfl | rfl
    · exact horth α hα
    · rw [Matrix.mulVec_neg, dotProduct_neg, horth α hα, neg_zero]
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hHN := torus_sup_union_le_normalizers (L := L) hτ hroots hrootsA horth'
  have hPQ : PD ≤ rootSpan .E7 L (rootCharKernel b) := by
    rw [hkerS, rootSpan_union_eq]
    exact (hfac.le_root ()).trans le_sup_left
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψnorm⟩ := e7_perx_core_of_stab Fr hFr F.n F.g0
    F.hg0C F.hg0 F.hperf hp hstab hx c hbh hh rfl hS hSn (P := fun _ : Unit => PD)
    (fun _ => hfac.finite ()) (fun _ => hfac.quasi ()) (fun _ => hPQ) (fun _ => hfac.le_fix ())
    (fun _ => hfac.le_adj ()) (fun _ y hy hyR u hu => by
      rw [hkerS] at hy
      exact hfac.norm () y (hHN hy).1 hyR u hu)
  refine ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, PD, hPD, hPψ (), hfac.finite (), hfac.quasi (),
    hψnorm (), ?_, ?_, ?_, hsl⟩
  · intro y hy hc
    rw [hkerS] at hy
    exact (ThetaFree.one_sided hτ hroots hrootsA horth' hfac.thetaFree hfac.le_root hy
      fun i u hu => hc u hu).2
  · intro y hy hc
    rw [hkerS] at hy
    exact (ThetaFree.one_sided hτ hroots hrootsA horth' hfac.thetaFree hfac.le_root hy
      fun i u hu => hc u hu).1
  · intro α hα
    rcases hα with rfl | rfl
    · exact hrS
    · exact e7F4_S0_neg _ hrS

end Special

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
