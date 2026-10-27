module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Spec
public import Certificates.Certificate117041

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0

open Subgroup CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus

theorem model_PA0 :
    Nonempty (PA0 hs100P (1 : Equiv.Perm (Fin 100)) E0 Zp) := by
  have h := Certificates.certificate117041
  obtain ⟨hb, hcl, hy, hk, ha, ht⟩ := s0_parts h
  obtain ⟨hgs, hvz, hZP, hZ2', hZ1, hvy, hYP, hU1, hX, hR, hvp, hPP⟩ := basic_spec hb
  obtain ⟨hcZ, hcU, hcY, hfZ, hfU⟩ := classes_spec hb hcl
  obtain ⟨hY3, hY1, hYZ, hYN, hZE, hEY⟩ := y_spec hy hvy hvz
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYo : orderOf Yp = 3 := orderOf_eq_prime hY3 hY1
  obtain ⟨hK0card, hKP, hKY, hKdisj, hUK, ⟨eK, heK⟩, hcyenum, hCy⟩ := k_spec hb hk hcl hYo
  obtain ⟨hAcard, hAle, hAsup, hAdisj, hJA, hYJ, hJcard, hnormal, hCJ, hder, ⟨eJ⟩⟩ :=
    a_spec hb hcl hk ha hcyenum hCy
  have hUP : Up ∈ hs100P := (hX 0 (by norm_num)).2
  have hC : ∀ a ∈ Ab, (∀ j ∈ Jm, a * j = j * a) → a = 1 := by
    intro a ha hcomm
    have : a ∈ hs100P ⊓ centralizer (Jm : Set (Equiv.Perm (Fin 100))) :=
      Subgroup.mem_inf.2 ⟨(hAle ha).1, mem_centralizer_iff.2 fun j hj => (hcomm j hj).symm⟩
    rw [hCJ] at this
    exact Subgroup.disjoint_def.1 hAdisj this ha
  obtain ⟨f, hf⟩ := exists_eAbar hnormal eJ hAcard hC
  have tab := table_spec hb hcl hk ha ht hAle hAdisj
  have hCDer : hs100P ⊓ centralizer ((derivedIn Ab : Subgroup (Equiv.Perm (Fin 100))) :
      Set (Equiv.Perm (Fin 100))) = zpowers Up := by
    apply le_antisymm
    · intro g hg
      rw [← hCJ]
      exact Subgroup.mem_inf.2 ⟨hg.1, mem_centralizer_iff.2 fun j hj =>
        mem_centralizer_iff.1 hg.2 j (hder hj)⟩
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hUP, mem_centralizer_iff.2 fun j hj => ?_⟩)
      have hjA : j ∈ Ab := derivedIn_le Ab hj
      exact mem_centralizer_singleton_iff.1 (hAle hjA).2
  exact ⟨{ y := Yp
           u := Up
           K₀ := K0
           Abar := Ab
           eK₀ := eK
           eAbar := f
           y_mem := Subgroup.mem_inf.2 ⟨hYN, hYP⟩
           y_ord := hYo
           zy := hYZ
           card_Ey := hEY
           K₀_le := hKP
           K₀_y := hKY
           K₀_disj := hKdisj
           u_mem := hUK
           u_swap := heK hUK
           card_Lu := hcU
           Abar_le := hAle
           Abar_comp := hAsup
           Abar_disj := hAdisj
           y_J := hder hYJ
           C_L_J := hCDer
           tab_inner := fun x hx hx2 hx1 hinn =>
             (tab x hx hx2 hx1).1
               ((eAbar_inner_iff (e := eJ) hC hJA f hf ⟨x, hx⟩).1 hinn)
           tab_S6 := fun x hx hx2 hx1 hnot hfix =>
             (tab x hx hx2 hx1).2.1
               (fun hxJ => hnot ((eAbar_inner_iff (e := eJ) hC hJA f hf ⟨x, hx⟩).2 hxJ))
               ((eAbar_fix_iff (e := eJ) (f := f) hf ⟨x, hx⟩).1 hfix)
           tab_PGL := fun x hx hx2 hx1 hnot hfix =>
             (tab x hx hx2 hx1).2.2
               (fun hxJ => hnot ((eAbar_inner_iff (e := eJ) hC hJA f hf ⟨x, hx⟩).2 hxJ))
               (fun j hj hj3 hcomm => by
                 obtain ⟨b, hb3, hfb⟩ :=
                   (eAbar_fix_iff (e := eJ) (f := f) hf ⟨x, hx⟩).2 ⟨j, hj, hj3, hcomm⟩
                 exact hfix b hb3 hfb) }⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0
