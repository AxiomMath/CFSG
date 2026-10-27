module

public import CFSG.CGT.PushingUpLit.LIT.A4.L35Alpha
public import CFSG.CGT.PushingUpLit.LIT.A4.SECProof

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4
open CFSG.Open (fusionStronglyEmbedded)


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {M : Subgroup G}
  {𝒳 : Set (Subgroup G)}

theorem Fam.stronglyEmbedded (F : Fam M 𝒳) (hr : 3 ≤ Nat.card ↥𝒳) (hM : M ≠ ⊤) :
    fusionStronglyEmbedded M := by
  obtain ⟨Y₁, hY₁, -⟩ := F.two
  obtain ⟨a₁, ha₁⟩ := F.blk Y₁ hY₁
  let D : Set G := {z | ∃ g : G, ∃ w ∈ pCoreOf 2 Y₁, w ≠ 1 ∧ z = g⁻¹ * w * g}
  have hDsq : ∀ z ∈ D, z * z = 1 := by
    rintro _ ⟨g, w, hw, hw1, rfl⟩
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [ha₁.sq w hw]; group
  have hD1 : ∀ z ∈ D, z ≠ 1 := by
    rintro _ ⟨g, w, hw, hw1, rfl⟩ h
    exact hw1 (conj_eq_one_iff.1 (show g⁻¹ * w * g⁻¹⁻¹ = 1 by simpa using h))
  have hD2 : ∀ d ∈ D, orderOf d = 2 := fun d hd => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hDsq d hd) (hD1 d hd)
  have hDn : ∀ d ∈ D, ∀ g : G, g⁻¹ * d * g ∈ D := by
    rintro _ ⟨g', w, hw, hw1, rfl⟩ g
    exact ⟨g' * g, w, hw, hw1, by group⟩
  have hDM : ∀ z ∈ D, z ∈ M → ∃ Y ∈ 𝒳, z ∈ pCoreOf 2 Y ∧ z ≠ 1 := by
    intro z hz hzM
    obtain ⟨g, w, hw, hw1, rfl⟩ := hz
    have hgM : g⁻¹ ∈ M := by
      by_contra hg
      have hvW : g⁻¹ * w * g ∈ conjSub g⁻¹ (pCoreOf 2 Y₁ ⊔ pCoreOf 2 Y₁) := by
        have : g⁻¹ * w * g⁻¹⁻¹ ∈ conjSub g⁻¹ (pCoreOf 2 Y₁ ⊔ pCoreOf 2 Y₁) :=
          conj_mem_conjSub (Subgroup.mem_sup_left hw)
        simpa using this
      have hz1 := F.alpha hr (x := g⁻¹) hg hY₁ hY₁ hvW hzM
      exact hw1 (conj_eq_one_iff.1 (show g⁻¹ * w * g⁻¹⁻¹ = 1 by simpa using hz1))
    refine ⟨conjSub g⁻¹ Y₁, F.perm g⁻¹ hgM Y₁ hY₁, ?_, hD1 _ ⟨g, w, hw, hw1, rfl⟩⟩
    rw [pCoreOf_conjSub]
    simpa using conj_mem_conjSub (g := g⁻¹) hw
  have h1 : ∀ x ∈ D, x ∈ M → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M := by
    intro x hxD hxM g hgM
    by_contra hg
    obtain ⟨Y, hY, hxY, hx1⟩ := hDM x hxD hxM
    have hyD : g⁻¹ * x * g ∈ D := hDn x hxD g
    obtain ⟨Y', hY', hyY', hy1⟩ := hDM _ hyD hgM
    obtain ⟨Y₂, hY₂, hY₂Y, -⟩ := exists_third hr Y Y
    obtain ⟨Y₃, hY₃, hY₃Y', -⟩ := exists_third hr Y' Y'
    have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := hDsq _ hyD
    have hCy : Subgroup.centralizer ({g⁻¹ * x * g} : Set G) ≤ M :=
      F.cent _ hy1 hy2 ⟨Y₃, hY₃, fun t ht =>
        F.comm Y' hY' Y₃ hY₃ hY₃Y'.symm _ ((pCoreOf_le_self Y') hyY') t ht⟩
    have hle : conjSub g⁻¹ Y₂ ≤ M := by
      intro z hz
      apply hCy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' : g * z * g⁻¹ ∈ Y₂ := by simpa using mem_conjSub_iff.1 hz
      have hc := F.comm Y hY Y₂ hY₂ hY₂Y.symm x ((pCoreOf_le_self Y) hxY) _ hz'
      calc z * (g⁻¹ * x * g) = g⁻¹ * ((g * z * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [← hc]
        _ = (g⁻¹ * x * g) * z := by group
    have := F.conj_le Y₂ hY₂ g⁻¹ hle
    exact hg (by simpa using M.inv_mem this)
  have h2 : ∀ x ∈ D, x ∈ M → ∀ y ∈ D, y ∈ M → x * y = y * x → ∀ g : G,
      g⁻¹ * (x * y) * g ≠ 1 → g⁻¹ * (x * y) * g ∈ M → g ∈ M := by
    intro x hxD hxM y hyD hyM _ g hne hmem
    by_contra hg
    obtain ⟨Y, hY, hxY, -⟩ := hDM x hxD hxM
    obtain ⟨Y', hY', hyY', -⟩ := hDM y hyD hyM
    have hxyW : x * y ∈ pCoreOf 2 Y ⊔ pCoreOf 2 Y' :=
      mul_mem (Subgroup.mem_sup_left hxY) (Subgroup.mem_sup_right hyY')
    have hv : g⁻¹ * (x * y) * g ∈ conjSub g⁻¹ (pCoreOf 2 Y ⊔ pCoreOf 2 Y') := by
      have := conj_mem_conjSub (g := g⁻¹) hxyW
      simpa using this
    exact hne (F.alpha hr (x := g⁻¹) (fun h => hg (by simpa using M.inv_mem h)) hY hY' hv hmem)
  obtain ⟨w, hw, hw1⟩ := ha₁.exists_ne_one
  have hwD : w ∈ D := ⟨1, w, hw, hw1, by simp⟩
  have hwM : w ∈ M := F.le Y₁ hY₁ ((pCoreOf_le_self Y₁) hw)
  exact SEC.fusionStronglyEmbedded_of_isSimpleGroup hM hD2 hDn h1 h2 hwD hwM

end CFSG.CGT.PushingUpLit.A4.L34
