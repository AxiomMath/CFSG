module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem card_piSub_W
    (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) :
    Nat.card (piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_barOf hW).inf_of_le_normalizer
    (le_top : layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ ⊤)
    (by intro x _; rw [Subgroup.normalizer_eq_top]; exact mem_top x)
  have h2 := isSylowOf_piSub π h1 le_rfl
  have hpiE : piSub π (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = P := by
    rw [piSub, subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hJ.surj,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [h2.card_eq, hpiE]
  exact twoPart_P

theorem mem_piSub_oP
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W)
    {ζ : Equiv.Perm (Fin 315)} (hζP : ζ ∈ P)
    (hζR : ∀ r ∈ R, (∀ s ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), r * s = s * r) → r = 1 ∨ r = ζ)
    {o : Equiv.Perm (Fin 315)} (ho : o ∈ centralizerIn P ζ) (hodd : Odd (orderOf o)) :
    o ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (oP W)) := by
  obtain ⟨z', hz'Z, hz'2, hPP⟩ := hs.exists_zprime hKC hW hUW
  have hz'M : z' ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hW.le (mem_inf.mp hz'Z).1
  have hzbc : ∀ a ∈ barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      (QuotientGroup.mk ⟨z', hz'M⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * a =
        a * QuotientGroup.mk ⟨z', hz'M⟩ := by
    rintro _ ⟨⟨x, hxW, rfl⟩, -⟩
    have h1 : (x : X) * z' = z' * x := mem_centralizer_iff.mp (mem_inf.mp hz'Z).2 _ hxW
    change (QuotientGroup.mk (⟨z', hz'M⟩ * x) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk (x * ⟨z', hz'M⟩)
    rw [show (⟨z', hz'M⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) * x =
      x * ⟨z', hz'M⟩ from Subtype.ext h1.symm]
  have hθ := hJ.theta_eq_of_comm hζP hζR hzbc
  have hinn : hJ.theta (QuotientGroup.mk ⟨z', hz'M⟩) ∈ innAut P := by
    rcases hθ with h | h <;> rw [h]
    · exact one_mem _
    · exact ⟨_, rfl⟩
  have hc : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ n ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), k * n = n * k := by
    intro k hk n hn
    rw [← hs.centralizer_layer_eq hJ.h412] at hn
    exact mem_centralizer_iff.mp hn k hk
  obtain ⟨e', he', q', hq', hzeq⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc
    ((hJ.theta_mem_inner_iff _).mp hinn)
  have hθe : hJ.theta (QuotientGroup.mk ⟨z', hz'M⟩) = MulAut.conj (π ⟨e', he'⟩) := by
    rw [hzeq, map_mul, (hJ.theta_eq_one_iff q').mpr hq', mul_one]
    exact hJ.theta_conj ⟨e', he'⟩
  have hoP : o ∈ P := (mem_centralizerIn.mp ho).1
  have hcomm : (⟨o, hoP⟩ : P) * π ⟨e', he'⟩ = π ⟨e', he'⟩ * ⟨o, hoP⟩ := by
    rcases hθ with h | h
    · rw [h] at hθe
      have : π ⟨e', he'⟩ = 1 := conj_injective_P (by rw [← hθe, map_one])
      rw [this, one_mul, mul_one]
    · rw [h] at hθe
      have : π ⟨e', he'⟩ = ⟨ζ, hζP⟩ := (conj_injective_P hθe).symm
      rw [this]
      exact Subtype.ext (mem_centralizerIn.mp ho).2
  have hoddP : Odd (orderOf (⟨o, hoP⟩ : P)) := by rw [Subgroup.orderOf_mk]; exact hodd
  obtain ⟨y, hπy, hy, hye⟩ :=
    exists_odd_lift π hJ.surj (le_of_eq hJ.ker) hJ.isPGroup_ker hoddP hcomm
  have hyC : (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      centralizer {(QuotientGroup.mk ⟨z', hz'M⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} := by
    rw [hzeq]
    exact hJ.mem_centralizer_of_comm hq' hye
  have hz'' : (⟨z', hz'M⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) *
      ⟨z', hz'M⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hz'2, Subgroup.coe_one])
  have hCmap := GSThmB.OddQuot.centralizer_singleton_map_eq hz''
  have hyC' : (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      (centralizer {(⟨z', hz'M⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))}).map
        (QuotientGroup.mk' (pPrimeCore 2
          ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) := by
    rw [← hCmap]
    exact hyC
  obtain ⟨m, hm, hmy⟩ := hyC'
  have hmodd : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) m)) := by
    rw [hmy, Subgroup.orderOf_coe]
    exact hy
  obtain ⟨k, hk, hmk⟩ := exists_odd_pow_map_eq _ m hmodd
  have hmkC := pow_mem hm k
  have hmkX : ((m ^ k : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) : X) ∈
      oP W := by
    apply Subgroup.subset_closure
    refine ⟨(hPP _).mpr ⟨(m ^ k).2, ?_⟩, ?_⟩
    · exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hmkC)
    · rw [Subgroup.orderOf_coe]
      exact hk
  refine mem_piSub.mpr ⟨y, ⟨m ^ k, hmkX, ?_⟩, by rw [hπy]⟩
  rw [hmk, hmy]

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
