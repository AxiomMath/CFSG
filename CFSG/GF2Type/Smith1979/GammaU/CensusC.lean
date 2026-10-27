module

public import CFSG.GF2Type.Smith1979.GammaU.FrameEnum
public import CFSG.GF2Type.Smith1979.GammaU.Enum
public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
public import Certificates.Certificate16966
import Certificates.Kernel.GammaU.BaseBridge
public import CFSG.GF2Type.Smith1979.GammaU.NativeBridge
public import CFSG.GF2Type.Smith1979.GammaU.StepA2

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

theorem mem_bfsClosure {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ)) :
    ∀ (fuel : ℕ) (frontier : List σ) (seen : Std.HashSet κ) (visited : List σ),
      ∀ x ∈ frontier ++ visited, x ∈ bfsClosure key fs fuel frontier seen visited
  | 0, _, _, _, _, hx => hx
  | fuel + 1, frontier, seen, visited, x, hx => by
    simp only [bfsClosure]
    split_ifs
    · exact hx
    · exact mem_bfsClosure key fs fuel _ _ _ x (List.mem_append_right _ hx)

@[expose] def InSub (H : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (x : Array ℕ) : Prop :=
  Canon x ∧ ∃ l ∈ H, ∀ y, l y = linOfRows x y

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    match l with
    | [] => exact List.nodup_nil
    | a :: as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨?_, ih _ ?_ _ rfl⟩
      · rw [List.mem_eraseDups, List.mem_filter]
        simp
      · rw [← h, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem card_toFinset_eraseDups {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List α) :
    l.toFinset.card = l.eraseDups.length := by
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups l)]
  congr 1
  ext a
  simp [List.mem_eraseDups]

@[expose] def Realizable (g : Array ℕ) : Prop :=
  Canon g ∧ ∃ l : V12 ≃ₗ[ZMod 2] V12, ∀ y, l y = linOfRows g y

theorem inSub_genGrp {gens : List (Array ℕ)} (hg : ∀ g ∈ gens, Realizable g) :
    ∀ g ∈ gens, InSub (Viol.genGrp gens) g := fun g hgm =>
  ⟨(hg g hgm).1, (hg g hgm).2.choose,
    Subgroup.subset_closure ⟨g, hgm, (hg g hgm).2.choose_spec⟩, (hg g hgm).2.choose_spec⟩

theorem compOf_eq (c : ℕ) : compOf c = subsetProducts (ResPair.compGens c) := rfl

theorem mem_foldl_subsetProducts (gens : List (Array ℕ)) :
    ∀ acc : List (Array ℕ), ∀ x ∈ acc,
      x ∈ gens.foldl (fun acc g => acc ++ acc.map (mulR g)) acc := by
  induction gens with
  | nil => exact fun acc x hx => hx
  | cons g gs ih => exact fun acc x hx => ih _ x (List.mem_append_left _ hx)

theorem mulR_idR_mem_subsetProducts {gens : List (Array ℕ)} {g : Array ℕ} (hg : g ∈ gens) :
    mulR g idR ∈ subsetProducts gens := by
  unfold subsetProducts
  suffices h : ∀ (gens : List (Array ℕ)) (acc : List (Array ℕ)), idR ∈ acc → g ∈ gens →
      mulR g idR ∈ gens.foldl (fun acc g => acc ++ acc.map (mulR g)) acc from
    h gens [idR] (List.mem_singleton_self _) hg
  intro gens
  induction gens with
  | nil => exact fun _ _ hg => by simp at hg
  | cons g' gs ih =>
    intro acc hacc hg
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hg with rfl | hg
    · exact mem_foldl_subsetProducts gs _ _
        (List.mem_append_right _ (List.mem_map.2 ⟨idR, hacc, rfl⟩))
    · exact ih _ (List.mem_append_left _ hacc) hg

theorem rowsSet_subsetProducts {gens : List (Array ℕ)} {g : Array ℕ} (hg : g ∈ gens)
    {l : V12 ≃ₗ[ZMod 2] V12} (hl : ∀ y, l y = linOfRows g y) : RowsSet (subsetProducts gens) l :=
  ⟨mulR g idR, mulR_idR_mem_subsetProducts hg, fun y => by rw [hl, linOfRows_mulR, linOfRows_idR]⟩

theorem self_mem_orbitOf (gens : List (Array ℕ)) (p : ℕ) : p ∈ orbitOf gens p :=
  mem_bfsClosure id _ 4096 [p] _ [] p (by simp)

theorem orbitOf_inv {H : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {gens : List (Array ℕ)}
    (hg : ∀ g ∈ gens, InSub H g) {p : ℕ} (hp : p < 4096) :
    ∀ x ∈ orbitOf gens p, x < 4096 ∧ ∃ l ∈ H, vecOf x = l (vecOf p) := by
  unfold orbitOf
  refine bfsClosure_inv id _ ?_ 4096 [p] _ [] ?_ (by simp)
  · intro f hf x ⟨hx, l, hl, hlx⟩
    obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hgc, m, hm, hmx⟩ := hg g hgm
    refine ⟨appN_lt hgc.2 x, m * l, mul_mem hm hl, ?_⟩
    rw [vecOf_appN, LinearEquiv.mul_apply, ← hlx, hmx]
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨hp, 1, one_mem _, rfl⟩

theorem closedOrbit_spec {O : List ℕ} {gens : List (Array ℕ)}
    (h : CFSG.GammaU.Native.closedOrbit O gens = true) : ∀ x ∈ O, ∀ g ∈ gens, appN g x ∈ O := by
  simpa only [CFSG.GammaU.Native.closedOrbit, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, native_appN] using h

theorem orbit_eq {gens : List (Array ℕ)} (hg : ∀ g ∈ gens, Realizable g) {p : ℕ} (hp : p < 4096)
    (hcl : ∀ x ∈ orbitOf gens p, ∀ g ∈ gens, appN g x ∈ orbitOf gens p) :
    MulAction.orbit (Viol.genGrp gens) (vecOf p) = vecOf '' {x | x ∈ orbitOf gens p} := by
  ext y
  constructor
  · rintro ⟨⟨l, hl⟩, rfl⟩
    change l (vecOf p) ∈ _
    have hl' : l ∈ (Viol.genGrp gens).toSubmonoid := hl
    clear hl
    rw [Viol.genGrp, Subgroup.closure_toSubmonoid_of_finite] at hl'
    induction hl' using Submonoid.closure_induction_left with
    | one => exact ⟨p, self_mem_orbitOf gens p, rfl⟩
    | mul_left s hs t _ ih =>
      obtain ⟨x, hx, hxt⟩ := ih
      obtain ⟨g, hgm, hgs⟩ := hs
      refine ⟨appN g x, hcl x hx g hgm, ?_⟩
      rw [vecOf_appN, LinearEquiv.mul_apply, ← hxt, hgs]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, l, hl, hlx⟩ := orbitOf_inv (inSub_genGrp hg) hp x hx
    exact ⟨⟨l, hl⟩, hlx.symm⟩

theorem canon_of_mem_compOf (h16964 : StepATFacts) {c : ℕ} (hc : c < 32) {r : Array ℕ}
    (hr : r ∈ compOf c) : Canon r :=
  h16964.t3 c hc r hr

end CFSG.GF2Type.Smith1979.GammaU.StepA
