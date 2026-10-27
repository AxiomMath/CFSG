module

public import CFSG.Sporadic.Bridge.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.Sporadic.Bridge

theorem identify_of_gpl {N H : Type} [Group N] [Group H] [Nontrivial H]
    (hSimple : IsSimpleGroup N)
    (hBridge : Nonempty (N ≃* TauCeti.Sporadic.onanPresentation.Group))
    (x : ℕ → H)
    (hx : ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters, wordProd x v = 1)
    (hgen : Subgroup.closure (Set.range fun i : Fin 7 => x i) = ⊤) :
    Nonempty (H ≃* N) := by
  obtain ⟨e⟩ := hBridge
  set φ := presHom TauCeti.Sporadic.onanPresentation x hx with hφ
  have hP : IsSimpleGroup TauCeti.Sporadic.onanPresentation.Group :=
    @MulEquiv.isSimpleGroup TauCeti.Sporadic.onanPresentation.Group _ N _ hSimple e.symm
  have hcount : TauCeti.Sporadic.onanPresentation.generatorCount = 7 := by
    simp [TauCeti.GroupPresentation.generatorCount]
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨presGen TauCeti.Sporadic.onanPresentation i,
      presHom_presGen _ _ hx (by rw [hcount]; exact i.2)⟩
  have hker : φ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have : ∀ g : H, g = 1 := by
        intro g
        obtain ⟨p, rfl⟩ := hsurj g
        exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top p)
      obtain ⟨g, hg⟩ := exists_ne (1 : H)
      exact hg (this g)
  have hbij : Function.Bijective φ := ⟨(MonoidHom.ker_eq_bot_iff φ).1 hker, hsurj⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans e.symm⟩

end CFSG.OddStandard.ONanRec
