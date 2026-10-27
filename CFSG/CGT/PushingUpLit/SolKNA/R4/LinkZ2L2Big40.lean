module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W9
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2B4A

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ}

theorem z2BigProp6a4_of_parts (hChoice : Z2BigChoiceB r n) (hT1 : Z2BigT1 r n)
    (hT2 : Z2BigT2 r n) (hw : Z2BigHweak r n) : Z2BigProp6a4 r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 hall hno
  obtain ⟨b, hbP, hbA, hab⟩ := hChoice hr Y R S t J u R₀ T₀ P hs hall hno
  have hbt := hs.swap_of_not_mem hbP hbA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine false_of_transfer_1515 (p := 2) (P := (P : Subgroup Y))
    (Q := edgeCent (P : Subgroup Y) t u) (R₀ := R₀) (u := b)
    (fun _ _ f hf => LinkZ2B.hom_eq_one_of_sylow_tight hs.large.cls.2.1 hs.hR₀ f hf)
    P.isPGroup' P.not_dvd_index (fun x hx q hq => hs.conj_mem_edgeCent hx hq)
    ⟨b, hbP, fun x hx => ?_⟩ hbP hbA
    (fun g k hg => hT2 hr Y R S t J u R₀ T₀ P hs h1 hall hno b hbP hbA hab g k hg)
    (fun g hg _ => hs.mem_or_mem_of_swap hbP hbt hg)
    (fun g => hT1 hr Y R S t J u R₀ T₀ P hs h1 hall hno b hbP hbA hab g)
    (hw hr Y R S t J u R₀ T₀ P hs h1)
  rcases hs.mem_or_mem_of_swap hbP hbt hx with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
