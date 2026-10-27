module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapNorm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSwap
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracLu
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracMod
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneTrans

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Cover

variable {X : Type} [Group X]

private theorem bcdLu_cover_form {E K : Subgroup X} (hEK : E ≤ K)
    (hcov : E.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) :
    ∀ c ∈ K, ∃ a ∈ E, ∃ o ∈ oddCoreOf K, c = a * o := by
  have h1 : E ⊔ pPrimeCoreOf 2 K = K := (covers_subgroupOf_iff hEK).1 hcov
  exact cover_form_of_eq_sup hEK (by rw [sup_comm]; exact h1.symm)

end Cover

section Lu

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem exists_Lu_model (h : Sec5Data X n z Z S) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {u : X} (huZ : u ∈ Z) (hu1 : u ≠ 1)
    (hAu : IsIntrinsicIn X (normalizer (Z : Set X)) A u) {t : X} (htA : t ∈ normalizer (A : Set X))
    (htu : t * u = u * t) (M : AhatModel X n A) :
    ∃ (L E : Subgroup X) (_ : Sec5Comp X n (centralizer ({u} : Set X)) L)
      (htL : t ∈ normalizer (L : Set X)) (M' : AhatModel X n L),
      u ∈ E ∧ E ≤ A ⊓ L ∧ (∀ c ∈ L, ∃ a ∈ E, ∃ o ∈ oddCoreOf L, c = a * o) ∧
      t ∈ normalizer (E : Set X) ∧ M'.perm t htL = M.perm t htA := by
  classical
  have hn : 8 ≤ n := h.maxdeg.1
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  set N : Subgroup X := normalizer (Z : Set X) with hN
  have hAK : A ≤ K0 X n N := le_sSup hA
  have hAu' : A ≤ centralizer ({u} : Set X) :=
    hAK.trans (h.K0_le_centralizer_Z.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huZ)))
  have hAH : A ≤ N ⊓ centralizer ({u} : Set X) := le_inf hA.isPCompIn.1 hAu'
  have huH : IsIntrinsicIn X (N ⊓ centralizer ({u} : Set X)) A u :=
    ⟨hAu.1, hAu.2.1, ⟨hAH, isPComponent_subgroupOf_mono hAH inf_le_left hAu.2.2.1.2⟩, hAu.2.2.2⟩
  obtain ⟨L, hL, hLn, hEL⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := u) hAu.1
    (inf_le_right : N ⊓ centralizer ({u} : Set X) ≤ centralizer ({u} : Set X)) huH hA.2
  have hLc : Sec5Comp X n (centralizer ({u} : Set X)) L := ⟨⟨u, hL⟩, hLn⟩
  set E : Subgroup X := oTwoPrimeOf (A ⊓ centralizer ({u} : Set X)) with hE
  obtain ⟨hEA, hcovA', hEq⟩ := hAu.cover_oTwoPrimeOf
  have hcovA : ∀ c ∈ A, ∃ a ∈ E, ∃ o ∈ oddCoreOf A, c = a * o := bcdLu_cover_form hEA hcovA'
  have hEn : IsDoubleCoverOfAlt (↥E ⧸ pPrimeCore 2 ↥E) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hEA hcovA' n).2 hA.2
  have hcovL' : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    covers_of_card_le hEL (by
      rw [natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hLn,
        natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hEn])
  have hcovL : ∀ c ∈ L, ∃ a ∈ E, ∃ o ∈ oddCoreOf L, c = a * o := bcdLu_cover_form hEL hcovL'
  have huE : u ∈ E := mem_oTwoPrimeOf_inf_centralizer hAu.2.1 hu2
  have htE : t ∈ normalizer (E : Set X) := normalizer_oTwoPrimeOf_inf htA htu
  have htL : t ∈ normalizer (L : Set X) :=
    mem_normalizer_of_covers_of_normalizes htu hLc.isPCompIn hEL htE hEq
  let ME : AhatModel X n E := M.transport hEA hcovA
  let ML : AhatModel X n L := ME.transportUp hEL hcovL
  refine ⟨L, E, hLc, htL, ML, huE, le_inf hEA hEL, hcovL, htE, ?_⟩
  rw [ME.perm_transportUp hn hEL hcovL htE htL, M.perm_transport hn hEA hcovA htE htA]

end Lu

section Swap

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem Z_le_centralizer_of_swap (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) :
    Z ≤ centralizer ({s} : Set X) := by
  classical
  refine h.pair.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨huZ, L, hL, hLn⟩
  obtain ⟨h1, h2, -⟩ := h.pair.isIntrinsicIn_normalizer huZ hL hLn
  set E : Subgroup X := oTwoPrimeOf (L ⊓ centralizer (Z : Set X)) with hE
  have hEc : Sec5Comp X n (normalizer (Z : Set X)) E := ⟨⟨u, h1⟩, h2⟩
  have huE : u ∈ E := h1.2.1
  have hu1 : u ≠ 1 := by
    intro hu
    have := h1.1
    rw [hu, orderOf_one] at this
    omega
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  by_cases hsE : s ∈ normalizer (E : Set X)
  · exact comm_of_mem_Z_of_norm h hs hEc hsE huZ huE hu1
  set E' : Subgroup X := E.map (MulAut.conj s).toMonoidHom with hE'
  have hE'c : Sec5Comp X n (normalizer (Z : Set X)) E' :=
    hEc.map_conj (Subgroup.le_normalizer hs.mem)
  have hne : E ≠ E' := fun heq => hsE (mem_normalizer_of_map_conj_eq heq.symm)
  have hzs := zStar_sup_eq_of_swap h hs hEc hE'c hne rfl
  set D : Subgroup X := K0 X n (normalizer (Z : Set X)) with hD
  have hEK : E ≤ D := le_sSup hEc
  have hE'K : E' ≤ D := le_sSup hE'c
  have hZD : Z ≤ D := h.Z_le_K0
  have hodd : Odd (Nat.card (oddCoreOf D)) := odd_card_oddCoreOf D
  have hZ1 : ∀ x ∈ Z, x ∈ oddCoreOf D → x = 1 := fun x hx hxO =>
    eq_one_of_mem_of_mem_odd (oddCoreOf D) Z hodd h.isPGroup_Z hx hxO
  have huzE : u ∈ zStar E := mem_zStar_of_mem_of_le_centralizer huE fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.Z_le_center_K0 huZ (hEK hk)).symm
  have hu' : u ∈ zStar E' ⊔ oddCoreOf D := hzs ▸ Subgroup.mem_sup_left huzE
  set u' : X := s * u * s⁻¹ with hu'def
  have hu'Z : u' ∈ Z := (Subgroup.mem_normalizer_iff.1 hs.mem u).1 huZ
  have hu'E' : u' ∈ E' := ⟨u, huE, rfl⟩
  have hu'1 : u' ≠ 1 := by
    intro h1'
    apply hu1
    have := congrArg (fun t => s⁻¹ * t * s) h1'
    simpa [hu'def, mul_assoc] using this
  have hu'zE' : u' ∈ zStar E' := mem_zStar_of_mem_of_le_centralizer hu'E' fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.Z_le_center_K0 hu'Z (hE'K hk)).symm
  obtain ⟨⟨w', hw'⟩, hE'n⟩ := hE'c
  have hzw : zStar E' ≤ pPrimeCoreOf 2 E' ⊔ Subgroup.zpowers w' := hw'.zStar_le_sup_zpowers hE'n
  have hOE' : pPrimeCoreOf 2 E' ≤ oddCoreOf D :=
    oddCoreOf_le_of_isPCompIn ⟨hE'K, isPComponent_subgroupOf_mono hE'K (K0_le n _) hw'.2.2.1.2⟩
  have hw'D : w' ∈ D := hE'K hw'.2.1
  have hP : ∀ x ∈ zStar E', x ∈ oddCoreOf D ⊔ Subgroup.zpowers w' := fun x hx =>
    (sup_le_sup_right hOE' _) (hzw hx)
  have hnormD : Subgroup.zpowers w' ≤ normalizer (oddCoreOf D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_pPrimeCoreOf_of_mem hw'D
  have hform : ∀ x ∈ Z, x ≠ 1 → x ∈ oddCoreOf D ⊔ Subgroup.zpowers w' →
      ∃ o ∈ oddCoreOf D, x = o * w' := by
    intro x hxZ hx1 hxP
    obtain ⟨o, ho, t, ht, rfl⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing (oddCoreOf D) (Subgroup.zpowers w')
        hnormD x).1 hxP
    rcases zpowers_eq_of_orderOf_two hw'.1 t ht with h1 | h1
    · exfalso
      rw [h1, mul_one] at hxZ hx1
      exact hx1 (hZ1 o hxZ ho)
    · exact ⟨o, ho, by rw [h1]⟩
  have hu_in : u ∈ oddCoreOf D ⊔ Subgroup.zpowers w' := by
    have hle : zStar E' ⊔ oddCoreOf D ≤ oddCoreOf D ⊔ Subgroup.zpowers w' :=
      sup_le (fun x hx => hP x hx) le_sup_left
    exact hle hu'
  obtain ⟨o₁, ho₁, hu_eq⟩ := hform u huZ hu1 hu_in
  obtain ⟨o₂, ho₂, hu'_eq⟩ := hform u' hu'Z hu'1 (hP u' hu'zE')
  have hdiff : u * u'⁻¹ ∈ oddCoreOf D := by
    have : u * u'⁻¹ = o₁ * o₂⁻¹ := by
      rw [hu_eq, hu'_eq]; group
    rw [this]
    exact (oddCoreOf D).mul_mem ho₁ ((oddCoreOf D).inv_mem ho₂)
  have hu_eq' : u * u'⁻¹ = 1 :=
    hZ1 _ (Z.mul_mem huZ (Z.inv_mem hu'Z)) hdiff
  have : u' = u := by
    have := mul_inv_eq_one.1 hu_eq'
    exact this.symm
  have hsu : s * u * s⁻¹ = u := by rw [← hu'def]; exact this
  have : s * u = u * s := by
    have := congrArg (fun t => t * s) hsu
    simpa [mul_assoc] using this
  exact this.symm

end Swap

end CFSG.OddStandard.Solomon75
