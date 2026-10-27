module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKM24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem examExcludes_sporadic_of_strongCard (s : TauCeti.SporadicName) {k : ℕ} (hk : ¬ 4 ∣ k)
    (hS : StrongCardEx (NativeSporadic.Carrier s) k) : ExamExcludes (FamSporadic s) := by
  rintro G _ _ K B B' P R m h ⟨e⟩
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  have habs := h.toAbs
  let θ : ↥K →* NativeSporadic.Carrier s :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU, hS'⟩ := hS
  obtain ⟨R₀, A₀, hR₀U, hnorm, hcardR, -, -, -, -, hstrong⟩ :=
    habs.exists_Rprime θ hθsurj hθker.le U hU
  have hne : R₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardR
    have hm := h.two_le
    have : 1 < 2 ^ (4 * m) := Nat.one_lt_two_pow (by omega)
    omega
  have hcard := hS' R₀ hR₀U hne
    (fun u hu r hr => hnorm u (Subgroup.le_normalizer hu) r hr) hstrong
  rw [hcardR] at hcard
  have h4 := Nat.pow_right_injective (le_refl 2) hcard
  exact hk ⟨m, by omega⟩

theorem examExcludes_sporadic_fusion
    (s : TauCeti.SporadicName)
    (hs : s = .M24 ∨ s = .He ∨ s = .Ru ∨ s = .J4) : ExamExcludes (FamSporadic s) := by
  rcases hs with rfl | rfl | rfl | rfl
  · have : Finite (NativeSporadic.Carrier .M24) := by
      dsimp only [NativeSporadic.Carrier]
      infer_instance
    exact examExcludes_sporadic_of_strongCard .M24 (k := 10) (by norm_num) m24_strongCard.toEx
  · have : Finite (NativeSporadic.Carrier .He) := by
      dsimp only [NativeSporadic.Carrier]
      infer_instance
    exact examExcludes_sporadic_of_strongCard .He (k := 10) (by norm_num) he_native_strongCard.toEx
  · have : Finite (NativeSporadic.Carrier .Ru) := by
      dsimp only [NativeSporadic.Carrier]
      infer_instance
    exact examExcludes_sporadic_of_strongCard .Ru (k := 14) (by norm_num) ru_native_strongCard.toEx
  · exact examExcludes_sporadic_of_strongCard .J4 (k := 21) (by norm_num) j4_native_strongCardEx

end CFSG.QuasithinUnique.Lin2
