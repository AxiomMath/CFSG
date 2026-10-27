module

public import CFSG.CGT.PushingUpLit.BHS6.SymLocalGrp
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] {n : ℕ}

theorem card_eq_img_mul_ker {G A : Subgroup Γ} (φ : ↥G →* Equiv.Perm (Fin n)) (hAG : A ≤ G) :
    Nat.card ↥A = Nat.card ↥(imgG G φ A) * Nat.card ↥(A ⊓ kerG G φ) := by
  classical
  let f : ↥A →* Equiv.Perm (Fin n) := φ.comp (Subgroup.inclusion hAG)
  have hrange : f.range = imgG G φ A := by
    ext σ
    rw [MonoidHom.mem_range, mem_imgG]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, hAG a.2, a.2, rfl⟩
    · rintro ⟨g, hg, hgA, rfl⟩
      exact ⟨⟨g, hgA⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ kerG G φ) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : Γ), a.1.2, mem_kerG.2 ⟨hAG a.1.2, a.2⟩⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
          obtain ⟨hg, h1⟩ := mem_kerG.1 x.2.2
          exact h1⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at this
  rw [← this, mul_comm]

end CFSG.CGT.PushingUpLit.SYMB
