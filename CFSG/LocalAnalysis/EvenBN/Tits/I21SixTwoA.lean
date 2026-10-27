module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixC
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Quot
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixOne
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoB
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoC

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_six_two_a_two (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P)
    (hno : ∀ W : Subgroup G, W ≤ P → (∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W) →
      IsElemAbelian 2 W → Nat.card W = 4 → ∀ w ∈ W, ∀ g : G, g * t * g⁻¹ ≠ w)
    (hV : ∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
      Nat.card V = 4) :
    ∃ (T : Subgroup G) (n : ℕ) (x u₀ : G), TwoGroupShape P t (u ^ 2) n x u₀ T := by
  obtain ⟨V, hVP, hVn, hVe, hV4⟩ := hV
  have C0 : SixACtx t u P V := ⟨h, hP, hRP, hno, hVP, hVn, hVe, hV4⟩
  obtain ⟨v, hv, hv1, hvz⟩ := C0.exists_v
  have C1 : SixAV t u P V v := { toSixACtx := C0, v_mem := hv, v_ne_one := hv1, v_ne_z := hvz }
  obtain ⟨w, hw, hw2, hvw⟩ := C1.exists_w
  have C2 : SixAW t u P V v w := { toSixAV := C1, hu₀ := hw, u₀_sq := hw2, v_u₀ := hvw }
  obtain ⟨y₀, C3⟩ := C2.exists_y₀
  obtain ⟨T, n, x, hT⟩ := exists_shape C3 (fun hU => quot_shape C3 hU)
  exact ⟨T, n, x, w, hT⟩

theorem sec622_six_two_a (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P) :
    ((∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
        Nat.card V = 4 ∧ ∃ v ∈ V, ∃ g : G, g * t * g⁻¹ = v) ∧ Nat.card P ≤ 16) ∨
    ∃ (T : Subgroup G) (n : ℕ) (x u₀ : G), TwoGroupShape P t (u ^ 2) n x u₀ T := by
  rcases sec622_six_two_a_one h hP hRP with h1 | ⟨hno, hV⟩
  · exact Or.inl h1
  · exact Or.inr (sec622_six_two_a_two h hP hRP hno hV)

theorem sec622_six_two (h : SecTwoHyp G t u)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) {L M : Subgroup G}
    (hLn : L.Normal) (htL : t ∉ L) (hM2 : IsPGroup 2 M) (hML : M ≤ L)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) {w : G} (hw : w = u ∨ w = t * u)
    (hCM : M ⊓ centralizer ({t} : Set G) = zpowers w) :
    Sec622UniqueInv M ∨ IsMulCommutative M ∨ Nonempty (M ≃* SemidihedralGroup 4) ∨
      Nonempty (M ≃* DihedralGroup 4) ∨ Sec622Order16 M ∨ Sec622CentralInv M ∨
      Sec622ProdDihedral M 3 :=
  sec622_six_two_of h hexp hLn htL hM2 hML hMt hw hCM (sec622_six_two_a h)
    (sec622_six_two_c h)

end CFSG.LocalAnalysis.EvenBN.Tits
