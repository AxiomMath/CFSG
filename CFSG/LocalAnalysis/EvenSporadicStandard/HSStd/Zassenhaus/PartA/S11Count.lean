module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

section Odd

theorem s11_odd_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (Open.fusionOddCore X)) := by
  have h : Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem s11_card_centralizer_odd {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) {u : H} (hu : u * u = 1) (hNu : ∀ n ∈ N, n * u = u * n) :
    Nat.card (centralizer ({u} : Set H)) =
      Nat.card N * Nat.card (centralizer ({QuotientGroup.mk' N u} : Set (H ⧸ N))) := by
  set K : Subgroup H := centralizer ({u} : Set H) with hK
  let g : K →* H ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have h1 : Nat.card g.ker * Nat.card g.range = Nat.card K := Subgroup.card_ker_mul_card_range g
  have h2 : g.range = centralizer ({QuotientGroup.mk' N u} : Set (H ⧸ N)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hK, map_centralizer_eq_of_odd N hN hu]
  have hNK : N ≤ K := fun n hn => mem_centralizer_singleton_iff.2 (hNu n hn)
  have h3 : g.ker = N.subgroupOf K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have h4 : Nat.card g.ker = Nat.card N := by
    rw [h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  rw [← h1, h2, h4]

end Odd

section S5

theorem s11_card_centralizer_swap (σ : Equiv.Perm (Fin 5)) (h : σ.IsSwap) :
    Nat.card (centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) = 12 := by
  obtain ⟨i, j, hij, rfl⟩ := h
  have key : ∀ i j : Fin 5, i ≠ j →
      Fintype.card {g : Equiv.Perm (Fin 5) // g * Equiv.swap i j = Equiv.swap i j * g} = 12 := by
    decide +kernel
  rw [← key i j hij, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_centralizer_singleton_iff)

end S5

section Sylow

variable {B : Type*} [Group B]

theorem s11_le_of_card (N T : Subgroup B) [N.Normal] (hB : Nat.card B = 2592)
    (hN : Nat.card N = 9) (hT : Nat.card T = 81) : N ≤ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 4) (by rw [hT]; norm_num)
  have hidx : ¬ 3 ∣ T.index := by
    have := Subgroup.card_mul_index T
    rw [hB, hT] at this
    have : T.index = 32 := by omega
    omega
  have hNp : IsPGroup 3 N := IsPGroup.of_card (n := 2) (by rw [hN]; norm_num)
  exact hNp.le_sylow_of_normal (hTp.toSylow hidx)

end Sylow

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
