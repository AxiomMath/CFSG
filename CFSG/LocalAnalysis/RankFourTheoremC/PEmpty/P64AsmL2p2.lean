module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.AGLEmbedding Subgroup

namespace P64Asm

theorem conjNormal_injective {Z : Type} [Group Z] {K : Subgroup Z} [K.Normal]
    (hcen : centralizer (K : Set Z) = ⊥) : Function.Injective (MulAut.conjNormal (H := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ centralizer (K : Set Z) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : Z)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * g = (g * k * g⁻¹) * g := by rw [h1]
      _ = g * k := by group
  rw [hcen, Subgroup.mem_bot] at hgc
  exact hgc

theorem isMulCommutative_of_card_dvd_sq {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime)
    (hQ : Nat.card Q ∣ p ^ 2) : IsMulCommutative Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow hp).mp hQ
  interval_cases k
  · haveI : IsCyclic Q := isCyclic_of_card_dvd_prime (p := p) (by rw [hkQ]; simp)
    infer_instance
  · haveI : IsCyclic Q := isCyclic_of_card_dvd_prime (p := p) (by rw [hkQ]; simp)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hkQ

end P64Asm

theorem kdI278L2p2_holds : KDI278L2p2 := by
  intro p hp hp5 Z _ _ K hKn hK hcen Q
  obtain ⟨hfact, ⟨e⟩⟩ := hK
  have hinj : Function.Injective
      (((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))) :
        Z →* MulAut (PSL2GF p 2)) :=
    (MulAut.congr e).injective.comp (P64Asm.conjNormal_injective hcen)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hA := kFactL2AutPCard p 2 (by omega) (by omega)
    ((Q : Subgroup Z).map ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))))
    (Q.isPGroup'.map _)
  rw [Subgroup.card_map_of_injective hinj, hk] at hA
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have hdvd : Nat.card (Q : Subgroup Z) ∣ p ^ 2 := by
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right hA
  exact P64Asm.isMulCommutative_of_card_dvd_sq hp hdvd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
