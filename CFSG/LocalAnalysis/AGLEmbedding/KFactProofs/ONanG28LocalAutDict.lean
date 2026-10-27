module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalFrob

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28

section Dict


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] def IsEl (x : MulAut (adjointGroup .G2 K)) (p : Array ℕ × ℕ) : Prop :=
  ∃ g : adjointGroup .G2 K, M.rho g = decode p.1 ∧ x = mk g p.2

theorem mk_mod (hK : Nat.card K = 8) (g : adjointGroup .G2 K) (n : ℕ) :
    (mk g n : MulAut (adjointGroup .G2 K)) = mk g (n % 3) := by
  unfold mk
  rw [pow_eq_pow_mod n (phi_pow_three hK)]

variable {M}

theorem valid_semi {p q : Array ℕ × ℕ} (hp : Valid p.1) (hq : Valid q.1) :
    Valid (semi p q).1 :=
  valid_mulCode hp (valid_frobk hq p.2)

theorem IsEl.mul (hK : Nat.card K = 8) {x y : MulAut (adjointGroup .G2 K)} {p q : Array ℕ × ℕ}
    (hp : Valid p.1) (hq : Valid q.1) (hx : IsEl M x p) (hy : IsEl M y q) :
    IsEl M (x * y) (semi p q) := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  refine ⟨g * (phi ^ p.2 : MulAut (adjointGroup .G2 K)) h, ?_, ?_⟩
  · rw [map_mul, hg, rho_phi_pow M p.2 h hq hh]
    exact (decode_mulCode hp (valid_frobk hq p.2)).symm
  · rw [mk_mul, mk_mod hK]
    rfl

theorem IsEl.inj (hK : Nat.card K = 8) {x y : MulAut (adjointGroup .G2 K)} {p q : Array ℕ × ℕ}
    (hp : Valid p.1) (hq : Valid q.1) (hp2 : p.2 < 3) (hq2 : q.2 < 3) (hx : IsEl M x p)
    (hy : IsEl M y q) : x = y ↔ p = q := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  constructor
  · intro e
    obtain ⟨hgh, hpq⟩ := mk_inj hK hp2 hq2 e
    have := (G28Model.eq_iff_codes M hp hq hg hh).1 hgh
    exact Prod.ext this hpq
  · intro e
    obtain ⟨hA, hs⟩ : p.1 = q.1 ∧ p.2 = q.2 := ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    have : g = h := (G28Model.eq_iff_codes M hp hq hg hh).2 hA
    rw [this, hs]

theorem isEl_conj {g : adjointGroup .G2 K} {A : Array ℕ} (hg : M.rho g = decode A) :
    IsEl M (MulAut.conj g) (A, 0) := ⟨g, hg, by simp [mk]⟩

theorem isEl_phi : IsEl M (phi : MulAut (adjointGroup .G2 K)) (idCode, 1) :=
  ⟨1, by rw [map_one, decode_idCode], by simp [mk]⟩

end Dict

end CFSG.AGLEmbedding.KFactProofs.G28
