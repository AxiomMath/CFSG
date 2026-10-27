module

public import Certificates.Data.Kernel.F4Syl3Rel
public import CFSG.Certificates.Kernel.F4SaltSound
public import CFSG.Certificates.Kernel.F4Syl3.Model

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.KC.F4Salt CFSG.KC.Loop
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree

variable {K : Type} [Field K]
  [CharP K 2]

theorem hasBitsS_powS {g : adjointGroup ReeTag.F4.tag K} {A : ℕ} (h : HasBitsS K g A) :
    ∀ n, HasBitsS K (g ^ n) (powS A n)
  | 0 => by
    rw [pow_zero]
    exact hasBitsS_one
  | n + 1 => by
    rw [pow_succ]
    exact (hasBitsS_powS h n).mul h

theorem hasBitsS_fSS {s : Fin 4 → adjointGroup ReeTag.F4.tag K} {S : List ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (s i) (S.getD i 0)) (a : ℕ) :
    HasBitsS K (fS s a) (fSS S a) :=
  (((hasBitsS_powS (hs 0) _).mul (hasBitsS_powS (hs 1) _)).mul (hasBitsS_powS (hs 2) _)).mul
    (hasBitsS_powS (hs 3) _)

theorem pres_of_relB {s : Fin 4 → adjointGroup ReeTag.F4.tag K}
    {g4 g5 : adjointGroup ReeTag.F4.tag K} {S : List ℕ} {G4 G5 : ℕ}
    (hs : ∀ i : Fin 4, HasBitsS K (s i) (S.getD i 0)) (h4 : HasBitsS K g4 G4)
    (h5 : HasBitsS K g5 G5) (h : relB S G4 G5 = true) : Pres s g4 g5 := by
  simp only [relB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hcu⟩, h43⟩, h53⟩, h45⟩, ha4⟩, ha5⟩, hz⟩ := h
  have c3 : ∀ x : adjointGroup ReeTag.F4.tag K, x ^ 3 = x * x * x := fun x => by
    rw [pow_succ, pow_two]
  refine ⟨fun i j => ?_, fun i => ?_, ?_, ?_, ?_, fun i => ?_, fun i => ?_, ?_⟩
  · exact (((hs i).mul (hs j)).eq_iff ((hs j).mul (hs i))).2
      (allB_spec (allB_spec hc i i.2) j j.2)
  · rw [c3]
    exact ((((hs i).mul (hs i)).mul (hs i)).eq_iff hasBitsS_one).2 (allB_spec hcu i i.2)
  · rw [c3]
    exact (((h4.mul h4).mul h4).eq_iff hasBitsS_one).2 h43
  · rw [c3]
    exact (((h5.mul h5).mul h5).eq_iff hasBitsS_one).2 h53
  · exact ((h4.mul h5).eq_iff (h5.mul h4)).2 h45
  · exact ((h4.mul (hs i)).eq_iff ((hasBitsS_fSS hs _).mul h4)).2 (allB_spec ha4 i i.2)
  · exact ((h5.mul (hs i)).eq_iff ((hasBitsS_fSS hs _).mul h5)).2 (allB_spec ha5 i i.2)
  · intro e
    have := ((hasBitsS_fSS hs 26).eq_iff hasBitsS_one).1 e
    rw [this] at hz
    exact Bool.noConfusion hz

theorem relN_spec (W4 L4 W5 L5 : ℕ) : relN W4 L4 W5 L5 =
    (relB [saltOf (sBits 0), saltOf (sBits 1), saltOf (sBits 2), saltOf (sBits 3)]
      (wordS W4 L4) (wordS W5 L5)).toNat := by
  simp only [relN, strictN_eq]

theorem relB_of_relN {W4 L4 W5 L5 : ℕ} (h : relN W4 L4 W5 L5 = 1) :
    relB [saltOf (sBits 0), saltOf (sBits 1), saltOf (sBits 2), saltOf (sBits 3)]
      (wordS W4 L4) (wordS W5 L5) = true := by
  rw [relN_spec] at h
  revert h
  cases relB [saltOf (sBits 0), saltOf (sBits 1), saltOf (sBits 2), saltOf (sBits 3)]
    (wordS W4 L4) (wordS W5 L5) <;> simp

end CFSG.KC.F4Syl3

end
