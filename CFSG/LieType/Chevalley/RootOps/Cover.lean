module

public import CFSG.LieType.Chevalley.RootOps.Poly
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

@[expose] def walkPair (τ : Tag) (w : List (Fin τ.rank)) (p : ℕ × ℕ) : ℕ × ℕ :=
  w.foldr (fun s x => (imgPar τ s x.1 / 2, imgPar τ s x.2 / 2)) p

theorem walkPair_spec (htab : tabCheck τ = true) (w : List (Fin τ.rank)) {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) :
    (walkPair τ w (a, b)).1 < τ.rootCertificate.roots.length ∧
      (walkPair τ w (a, b)).2 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (walkPair τ w (a, b)).1 =
        (w.map (simple τ)).prod • τ.rootCertificate.root a ∧
      τ.rootCertificate.root (walkPair τ w (a, b)).2 =
        (w.map (simple τ)).prod • τ.rootCertificate.root b := by
  induction w with
  | nil => simpa [walkPair] using ⟨ha, hb⟩
  | cons s w ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [walkPair, List.foldr_cons] at h1 h2 h3 h4 ⊢
    rw [imgPar_div_two htab h1, imgPar_div_two htab h2]
    refine ⟨rootCertificate_image_lt h1 s, rootCertificate_image_lt h2 s, ?_, ?_⟩
    · rw [rootCertificate_root_image h1, h3, List.map_cons, List.prod_cons, mul_smul,
        simple_smul]
    · rw [rootCertificate_root_image h2, h4, List.map_cons, List.prod_cons, mul_smul,
        simple_smul]

@[expose] def decodeWord (τ : Tag) : ℕ → ℕ → List (Fin τ.rank)
  | 0, _ => []
  | fuel + 1, code =>
    if code = 0 then []
    else if h : code % 16 - 1 < τ.rank then ⟨code % 16 - 1, h⟩ :: decodeWord τ fuel (code / 16)
    else decodeWord τ fuel (code / 16)

@[expose] def neededPairs (τ : Tag) : List (ℕ × ℕ) :=
  (List.finRange τ.rank).flatMap fun (i : Fin τ.rank) =>
    (List.range τ.rootCertificate.roots.length).filterMap fun m =>
      if decide (0 < height (τ.rootCertificate.root m)) && !(m == (i : ℕ)) then some ((i : ℕ), m)
      else none

@[expose] def coverPair (e : ℕ) : ℕ × ℕ := (e % 16, e / 16 % 256)

@[expose] def coverRep (e : ℕ) : ℕ := e / 4096 % 16

@[expose] def coverWord (e : ℕ) : ℕ := e / 65536

@[expose] def repPair (reps : List (ℕ × ℕ × List Factor)) (r : ℕ) : ℕ × ℕ :=
  ((reps.getD r (0, 0, [])).1, (reps.getD r (0, 0, [])).2.1)

@[expose] def coverCheck (τ : Tag) (reps : List (ℕ × ℕ × List Factor)) (cover : List ℕ) : Bool :=
  cover.map coverPair == neededPairs τ &&
    cover.all fun e => Nat.blt (coverRep e) reps.length &&
      walkPair τ (decodeWord τ 64 (coverWord e)) (repPair reps (coverRep e)) == coverPair e

@[expose] def repsCheck (τ : Tag) (reps : List (ℕ × ℕ × List Factor)) : Bool :=
  reps.all fun x => repCheck τ x.1 x.2.1 x.2.2

theorem mem_neededPairs (i : Fin τ.rank) (β : Root τ) (hβ : 0 < height β.1)
    (hne : β ≠ simpleRoot τ i) : ((i : ℕ), rootPos β) ∈ neededPairs τ := by
  have hm : rootPos β ≠ (i : ℕ) := by
    intro h
    apply hne
    have := root_rootPos β
    rw [h] at this
    obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
    exact Subtype.ext (this.symm.trans (hb i))
  refine List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_filterMap.2
    ⟨rootPos β, List.mem_range.2 (rootPos_lt β), ?_⟩⟩
  rw [root_rootPos]
  simp [hβ, hm]

variable (K : Type) [Field K]

theorem commContained_of_checks (hv : allValid τ = true) (htab : tabCheck τ = true)
    {reps : List (ℕ × ℕ × List Factor)} {cover : List ℕ} (hreps : repsCheck τ reps = true)
    (hcover : coverCheck τ reps cover = true) (i : Fin τ.rank) (β : Root τ)
    (hβ : 0 < height β.1) (hne : β ≠ simpleRoot τ i) :
    (rootOperatorFamily τ).CommContained K (simpleRoot τ i) β := by
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hcover
  obtain ⟨hpairs, hwalk⟩ := hcover
  have hmem := mem_neededPairs i β hβ hne
  rw [← hpairs, List.mem_map] at hmem
  obtain ⟨e, he, hpe⟩ := hmem
  obtain ⟨hr, hw⟩ := hwalk e he
  set x := reps.getD (coverRep e) (0, 0, []) with hx
  have hxmem : x ∈ reps := by
    rw [hx, List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hrep : repCheck τ x.1 x.2.1 x.2.2 = true := by
    simp only [repsCheck, List.all_eq_true] at hreps
    exact hreps x hxmem
  have hab : x.1 < τ.rootCertificate.roots.length ∧ x.2.1 < τ.rootCertificate.roots.length := by
    simp only [repCheck, Bool.and_eq_true, Nat.blt_eq] at hrep
    exact ⟨hrep.1.1.1, hrep.1.1.2⟩
  have hcomm := commContained_of_repCheck K hv hrep (rootAt τ x.1 hab.1) (rootAt τ x.2.1 hab.2)
    (rootPos_rootAt _) (rootPos_rootAt _)
  set w := decodeWord τ 64 (coverWord e)
  have ht := (rootOperatorFamily τ).comm_transport_list w hcomm
  obtain ⟨-, -, h3, h4⟩ := walkPair_spec htab w hab.1 hab.2
  have hw' : walkPair τ w (x.1, x.2.1) = ((i : ℕ), rootPos β) := by
    rw [← hpe]
    exact hw
  rw [hw'] at h3 h4
  obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have e1 : (w.map (simple τ)).prod • rootAt τ x.1 hab.1 = simpleRoot τ i := by
    apply Subtype.ext
    rw [coe_smul_root]
    exact h3.symm.trans (hb i)
  have e2 : (w.map (simple τ)).prod • rootAt τ x.2.1 hab.2 = β := by
    apply Subtype.ext
    rw [coe_smul_root]
    exact h4.symm.trans (root_rootPos β)
  rwa [e1, e2] at ht

end CFSG.LieType.Chevalley.RootOps
