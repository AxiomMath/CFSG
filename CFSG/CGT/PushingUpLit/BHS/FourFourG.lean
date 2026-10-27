module

public import CFSG.CGT.PushingUpLit.BHS.FourFourD
public import CFSG.CGT.PushingUpLit.BHS.FourFourE

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_hyp413Comm {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    {B : Subgroup (MulAut V)} (hB : B ∈ D) (hLB : ∃ l ∈ L, ∃ b ∈ B, l * b ≠ b * l)
    (hBL : ¬ B ≤ L) :
    ∃ (A : Subgroup (MulAut V)) (n : ℕ), Hyp413Comm P D M L A B n ∧
      ∀ A' ∈ D, A' ≤ L → (∀ a ∈ A', ∀ b ∈ B, a * b = b * a) → A' = A := by
  obtain ⟨A, hA, hAL, hcomm⟩ := exists_comm_sylow h hV hL hB
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  refine ⟨A, n, ⟨h.toHyp41, hL, hn1, hSL, hA, hAL, hB, hBL, hcomm, hLB⟩, ?_⟩
  intro A' hA' hA'L hcomm'
  by_contra hne
  have hS : IsSylowOf 2 A L := (hΛ2 A).1 ⟨hA, hAL⟩
  have hS' : IsSylowOf 2 A' L := (hΛ2 A').1 ⟨hA', hA'L⟩
  have hsup : A' ⊔ A = L := hSL.sylow_sup_eq hn1 hS' hS hne
  obtain ⟨l, hl, b, hb, hne2⟩ := hLB
  rw [← hsup] at hl
  have hle : A' ⊔ A ≤ Subgroup.centralizer (B : Set (MulAut V)) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm' a ha b hb).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  exact hne2 ((Subgroup.mem_centralizer_iff.1 (hle hl) b hb).symm)

theorem four_thirteen {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    {B : Subgroup (MulAut V)} (hB : B ∈ D) (hLB : ∃ l ∈ L, ∃ b ∈ B, l * b ≠ b * l)
    (hBL : ¬ B ≤ L) :
    ∃ A ∈ D, A ≤ L ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧
      (∀ A' ∈ D, A' ≤ L → (∀ a ∈ A', ∀ b ∈ B, a * b = b * a) → A' = A) ∧
      ∃ n : ℕ, 1 ≤ n ∧ IsSLNatSection L ⊤ (fixV L) n ∧ Nat.card A = 2 ^ n ∧
        (commV A ⊔ fixV (L ⊔ B) = fixV (A ⊔ B) ∧ commV B ⊔ fixV (L ⊔ B) = fixV (A ⊔ B)) ∧
        Nat.card ↥(commV A ⊔ fixV (L ⊔ B)) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) ∧
        Nat.card V = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) ∧
        Nat.card ↥(fixV L) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) ∧
        commV (L ⊔ B) ⊔ fixV (L ⊔ B) = commV L ⊔ fixV (L ⊔ B) ∧
        (∀ g ∈ L ⊔ B, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), g w ∈ commV L ⊔ fixV (L ⊔ B)) ∧
        IsSLNatSection L (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B)) n := by
  obtain ⟨A, n, d, huniq⟩ := exists_hyp413Comm h hV hL hB hLB hBL
  obtain ⟨hcard, -, hb, hc, hd, he, he2, he3, he4⟩ :=
    four_thirteen_comm d.hyp d.lam d.one_le d.sl d.memA d.leA d.memB d.not_le d.comm d.noncomm
  exact ⟨A, d.memA, d.leA, d.comm, huniq, n, d.one_le, d.sl, hcard, hb, hc, hd, he, he2, he3,
    he4⟩

end CFSG.CGT.PushingUpLit.BHS
