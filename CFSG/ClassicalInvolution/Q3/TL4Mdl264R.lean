module

public import CFSG.ClassicalInvolution.Q3.TL4C264OmDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RD
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame (CentOmega3)
open CFSG.Blueprint

@[expose] def ThreeOver2Om3 (S : Type) [Group S] : Prop :=
  ∀ (A B : Subgroup S) (r : S), QuatTwinDatum A r →
    (∃ q ∈ Subgroup.centralizer ({r} : Set S), conjSub q A = B) → B ≠ A →
      ∃ C₁ ∈ CoreAssembly.conjClass A, ∃ C₂ ∈ CoreAssembly.conjClass A,
        ∃ C₃ ∈ CoreAssembly.conjClass A, C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₂ ≠ C₃ ∧
          ∃ P : Subgroup S, IsPGroup 2 ↥P ∧ 2 < Nat.card ↥(C₁ ⊓ P) ∧
            2 < Nat.card ↥(C₂ ⊓ P) ∧ 2 < Nat.card ↥(C₃ ⊓ P)

@[expose] def OrthBad3 (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨ (t = .POmegaMinus ∧ 4 ≤ n)

section Pull

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {Q : Type} [Group Q]

theorem exists_member_of_mem_conjClass_map (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) {C : Subgroup Q} (hC : C ∈ CoreAssembly.conjClass (K.map f))
    (P : Subgroup Q) :
    ∃ M ∈ Φ, M.map f = C ∧ Nat.card ↥(C ⊓ P) ≤ Nat.card ↥(M ⊓ P.comap f) := by
  obtain ⟨s, rfl⟩ := hC
  obtain ⟨w, rfl⟩ := hf s
  have hM : (conjSub w K).map f = conjSub (f w) (K.map f) := AscQuot.map_conjSub f w K
  refine ⟨conjSub w K, h.fam.hyp.conjInvariant w K h.memK, hM, ?_⟩
  have hle : conjSub (f w) (K.map f) ⊓ P ≤ (conjSub w K ⊓ P.comap f).map f := by
    rintro y ⟨hyC, hyP⟩
    rw [← hM] at hyC
    obtain ⟨x, hx, rfl⟩ := hyC
    exact ⟨x, ⟨hx, hyP⟩, rfl⟩
  have : Finite ↥((conjSub w K ⊓ P.comap f).map f) := Finite.of_surjective _
    (MonoidHom.subgroupMap_surjective f _)
  exact (Subgroup.card_le_of_le hle).trans
    (Nat.le_of_dvd Nat.card_pos ((conjSub w K ⊓ P.comap f).card_map_dvd f))

theorem false_of_three_map (h : TwinBase3 Φ K K' k k') (hNo : NoThreeOver2 Φ) (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) {C₁ C₂ C₃ : Subgroup Q}
    (hC₁ : C₁ ∈ CoreAssembly.conjClass (K.map f)) (hC₂ : C₂ ∈ CoreAssembly.conjClass (K.map f))
    (hC₃ : C₃ ∈ CoreAssembly.conjClass (K.map f)) (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃)
    (h23 : C₂ ≠ C₃) {P : Subgroup Q} (hP : IsPGroup 2 ↥P) (h1 : 2 < Nat.card ↥(C₁ ⊓ P))
    (h2 : 2 < Nat.card ↥(C₂ ⊓ P)) (h3 : 2 < Nat.card ↥(C₃ ⊓ P)) : False := by
  obtain ⟨M₁, hM₁, rfl, hc₁⟩ := exists_member_of_mem_conjClass_map h f hf hC₁ P
  obtain ⟨M₂, hM₂, rfl, hc₂⟩ := exists_member_of_mem_conjClass_map h f hf hC₂ P
  obtain ⟨M₃, hM₃, rfl, hc₃⟩ := exists_member_of_mem_conjClass_map h f hf hC₃ P
  have hle := hNo M₁ hM₁ M₂ hM₂ M₃ hM₃ (fun e => h12 (by rw [e]))
    (fun e => h13 (by rw [e])) (fun e => h23 (by rw [e])) (P.comap f)
    (hP.comap_of_ker_isPGroup f hf2) (h1.trans_le hc₁) (h2.trans_le hc₂)
  omega

end Pull

section Cit3


variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}

theorem false_of_threeOver2Om3 (h : TwinBase3 Φ K K' k k') (hNo : NoThreeOver2 Φ)
    (N : Subgroup W) [N.Normal] (hN : N = Subgroup.zpowers (k * k'))
    {t : Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (ht : E3S3O.ClassicalTag3 t)
    (hS : LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) t n 3 1)
    (h3 : ThreeOver2Om3 ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N))) : False := by
  obtain ⟨hf, hf2, hs, hOS⟩ := E3S3O.quotCenter_reduction h N hN ht hS
  set f := (QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N) with hfdef
  have hd := E3S3O.quatTwinDatum_map_of_simple h f hf hf2 hs hOS
  obtain ⟨-, ⟨c, -, hcr, hK'⟩, hne⟩ := E3S3O.twin_map_of_simple h f hf hf2 hs hOS
  obtain ⟨C₁, hC₁, C₂, hC₂, C₃, hC₃, h12, h13, h23, P, hP, h1, h2, h3'⟩ :=
    h3 (K.map f) (K'.map f) (f k) hd ⟨f c, hcr, hK'.symm⟩ hne
  exact false_of_three_map h hNo f hf hf2 hC₁ hC₂ hC₃ h12 h13 h23 hP h1 h2 h3'

theorem model264Rank3_of
    (hU : ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 → ThreeOver2Om3 S)
    (hO : ∀ (S : Type) [Group S] [Finite S] (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      OrthBad3 t n → LieModel S t n 3 1 → ThreeOver2Om3 S) : Model264Rank3 := by
  intro W _ _ Φ K K' k k' h hNo N _ hN hC
  have : Finite ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) :=
    Finite.of_surjective ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp
      (QuotientGroup.mk' N)) ((QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective N))
  rcases hC with hS | hS | hS | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
  · exact Or.inl hS
  · exact Or.inr hS
  · exact (false_of_threeOver2Om3 h hNo N hN (Or.inr (Or.inr (Or.inl rfl))) hS
      (hU _ hS)).elim
  · exact (false_of_threeOver2Om3 h hNo N hN (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hS
      (hO _ _ _ (Or.inl ⟨rfl, hm⟩) hS)).elim
  · exact (false_of_threeOver2Om3 h hNo N hN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      hS (hO _ _ _ (Or.inr (Or.inl ⟨rfl, hm⟩)) hS)).elim
  · exact (false_of_threeOver2Om3 h hNo N hN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      hS (hO _ _ _ (Or.inr (Or.inr ⟨rfl, hm⟩)) hS)).elim

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
