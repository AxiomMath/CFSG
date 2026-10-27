module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.AltSplit

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS6

theorem emb_two_two (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) (n : ℕ) (hn3 : 3 ≤ n) (hodd : Odd n)
    (hind : ∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (A B : Subgroup V) (hAB : A ≤ B) (_hA : GInv G A) (hB : GInv G B)
    (hAt : ∀ g ∈ G, ∀ a ∈ A, g a = a) (hVB : ∀ g ∈ G, ∀ v : V, g v * v⁻¹ ∈ B)
    (hnat : IsNatSectionBy (fun (s : alternatingGroup (Fin n)) (v : ↥(coreMod n)) =>
      coreAct n (s : Equiv.Perm (Fin n)) v) G B A) :
    A = ⊥ ∧ B = ⊤ := by
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  exact alt_chain hV G hn3 hodd hind A B hAB hB hAt hVB θ β hβs hβk hβe

end CFSG.CGT.PushingUpLit.CGT6
