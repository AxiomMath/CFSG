module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModData

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

inductive F4 : Type
  | z | o | w | w2
  deriving DecidableEq

namespace F4

instance : Fintype F4 :=
  ⟨⟨{z, o, w, w2}, by decide⟩, fun x => by cases x <;> decide⟩

def add : F4 → F4 → F4
  | z, y => y
  | x, z => x
  | o, o => z
  | w, w => z
  | w2, w2 => z
  | o, w => w2
  | w, o => w2
  | o, w2 => w
  | w2, o => w
  | w, w2 => o
  | w2, w => o

def mul : F4 → F4 → F4
  | z, _ => z
  | _, z => z
  | o, y => y
  | x, o => x
  | w, w => w2
  | w, w2 => o
  | w2, w => o
  | w2, w2 => w

def inv : F4 → F4
  | z => z
  | o => o
  | w => w2
  | w2 => w

instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Inv F4 := ⟨inv⟩
instance : Zero F4 := ⟨z⟩
instance : One F4 := ⟨o⟩

instance : Field F4 :=
  Field.ofMinimalAxioms F4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem card_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

end F4

section Mod

variable {W : Type} [AddCommGroup W]

def smulW (ω : W →+ W) : F4 → W → W
  | F4.z, _ => 0
  | F4.o, v => v
  | F4.w, v => ω v
  | F4.w2, v => ω v + v

theorem add_def (x y : F4) : x + y = F4.add x y := rfl
theorem mul_def (x y : F4) : x * y = F4.mul x y := rfl

def modF4 (ω : W →+ W) (h2 : ∀ w : W, w + w = 0) (hω : ∀ w, ω (ω w) + ω w + w = 0) :
    Module F4 W :=
  have hω' : ∀ v, ω (ω v) = ω v + v := fun v => by
    have := hω v
    rw [add_assoc] at this
    exact eq_neg_of_add_eq_zero_left this |>.trans (neg_eq_of_add_eq_zero_right (h2 _))
  have h3 : ∀ a b : W, a + (a + b) = b := fun a b => by rw [← add_assoc, h2, zero_add]
  have h4 : ∀ a b : W, a + (b + a) = b := fun a b => by rw [add_comm b a, h3]
  { smul := smulW ω
    one_smul := fun _ => rfl
    zero_smul := fun _ => rfl
    smul_zero := fun x => by cases x <;> simp [HSMul.hSMul, SMul.smul, smulW]
    smul_add := fun x v v' => by
      cases x <;> simp [HSMul.hSMul, SMul.smul, smulW] <;> abel
    add_smul := fun x y v => by
      cases x <;> cases y <;>
        simp only [HSMul.hSMul, SMul.smul, add_def, F4.add, smulW, h2, h3, h4, add_zero, zero_add,
          add_comm] <;>
        first | abel | skip
    mul_smul := fun x y v => by
      cases x <;> cases y <;>
        simp only [HSMul.hSMul, SMul.smul, mul_def, F4.mul, smulW, map_zero, map_add, hω', h3, h4,
          add_zero, zero_add, add_comm] <;>
        first | abel | skip }

end Mod

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
