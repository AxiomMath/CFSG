
module

public import CFSG.Fischer.Polar.LinesBase
public import CFSG.Fischer.Polar.Search
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

@[expose] public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab lamTab gWords hypEnum

local notation "PT" => perpTab ()
local notation "PL" => perpLists (perpTab ())
local notation "LT" => lineTab (perpTab ())
local notation "LAM" => lamTab ()
local notation "WS" => gWords ()
local notation "CT" => mkCtx (perpTab ()) (gWords ()) (lamTab ())
local notation "HU" => Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2) ++ Prod.fst (hypEnum 3)
local notation "IX" =>
  famIndex (Prod.fst (hypEnum 1) ++ Prod.fst (hypEnum 2) ++ Prod.fst (hypEnum 3))

structure HypFacts : Prop where
  lam : lamOK PT LT LAM = true
  words : wordsOK WS (CT).gI = true
  root₁ : rootOK PT LT (rootFlags 1) = true
  root₂ : rootOK PT LT (rootFlags 2) = true
  root₃ : rootOK PT LT (rootFlags 3) = true
  orbit₁ : hypOrbitOK (rootFlags 1) (hypGens ()) (hypGensInv ()) (hypEnum 1) IX 0 = true
  orbit₂ : hypOrbitOK (rootFlags 2) (hypGens ()) (hypGensInv ()) (hypEnum 2) IX 1408 = true
  orbit₃ : hypOrbitOK (rootFlags 3) (hypGens ()) (hypGensInv ()) (hypEnum 3) IX 2816 = true
  fam : famOK HU IX = true
  search : searchOK CT HU IX 40 = true

theorem hypCtx_P : (CT).P = PT := by unfold mkCtx; rfl

theorem hypCtx_pl : (CT).pl = PL := by unfold mkCtx; rfl

theorem hypCtx_lam : (CT).lam = LAM := by unfold mkCtx; rfl

theorem hypCtx_lamIdx {a : ℕ} (ha : a < 693) :
    (CT).lamIdx[a]! = filterRange (fun j => (LAM[j]!)[a]!) 1024 [] := by
  unfold mkCtx
  rw [getElem!_pos _ a (by simpa using ha), Array.getElem_ofFn]

theorem hypCtx_gI {x : ℕ} (hx : x < 693) : (CT).gI[x]! = invT 693 (tvWordTab WS[x]!) := by
  unfold mkCtx wordInvs
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

noncomputable def gx (x : Fin 693) : Equiv.Perm (Fin 693) := wordP WS[x.val]!

theorem gx_mem (x : Fin 693) : gx x ∈ T46 := wordP_mem _

theorem foldl_set_true' {α : Type*} {l : List α} {f : α → ℕ} {a : Flags} {p : ℕ}
    (h : (l.foldl (fun a v => a.set! (f v) true) a)[p]! = true) :
    a[p]! = true ∨ ∃ v ∈ l, f v = p := by
  induction l generalizing a with
  | nil => exact Or.inl h
  | cons v l ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h1 | ⟨w, hw, hwp⟩
    · rcases getElem!_set!_true h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨v, List.mem_cons_self .., h2⟩
    · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hwp⟩

theorem clStep_sound {O : Set (Fin 693)} (hO : ∀ x ∈ O, tvP x '' O = O) {F : Flags}
    (hF : ∀ p : Fin 693, F[p.val]! = true → p ∈ O) :
    ∀ p : Fin 693, (clStep F)[p.val]! = true → p ∈ O := by
  intro p hp
  unfold clStep at hp
  have key : ∀ (l : List ℕ) (a : Flags), (∀ u ∈ l, u ∈ members F) →
      (l.foldl (fun a u => (members F).foldl (fun a v => a.set! (ap tvTabs[u]! v) true) a)
        a)[p.val]!
        = true → a[p.val]! = true ∨ p ∈ O := by
    intro l
    induction l with
    | nil => intro a _ h; exact Or.inl h
    | cons u l ih =>
      intro a hl h
      rw [List.foldl_cons] at h
      rcases ih _ (fun u' hu' => hl u' (List.mem_cons_of_mem _ hu')) h with h1 | h1
      · rcases foldl_set_true' h1 with h2 | ⟨v, hv, hvp⟩
        · exact Or.inl h2
        · right
          obtain ⟨hu, hFu⟩ := mem_members.1 (hl u (List.mem_cons_self ..))
          obtain ⟨hv', hFv⟩ := mem_members.1 hv
          have hr := rep_tvP ⟨u, hu⟩ v hv'
          rw [idx_of_lt _ hv'] at hr
          have hpe : p = tvP ⟨u, hu⟩ ⟨v, hv'⟩ := Fin.ext (by rw [← hvp, hr]; rfl)
          rw [hpe, ← hO ⟨u, hu⟩ (hF ⟨u, hu⟩ hFu)]
          exact ⟨⟨v, hv'⟩, hF ⟨v, hv'⟩ hFv, rfl⟩
      · exact Or.inr h1
  rcases key (members F) F (fun u hu => hu) hp with h | h
  · exact hF p h
  · exact h

theorem clIter_sound {O : Set (Fin 693)} (hO : ∀ x ∈ O, tvP x '' O = O) (k : ℕ) :
    ∀ F : Flags, (∀ p : Fin 693, F[p.val]! = true → p ∈ O) →
      ∀ p : Fin 693, (clIter k F)[p.val]! = true → p ∈ O := by
  induction k with
  | zero => intro F hF; exact hF
  | succ k ih => intro F hF; exact ih (clStep F) (clStep_sound hO hF)

theorem lam_get {j : ℕ} (hj : j < 1024) :
    LAM[j]! = clIter 3 (lamStart ((lamSel ()).map (lineC 0)) j) := by
  unfold lamTab lamOf
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem lineC_zero_get (y : Fin 693) : (lineC 0 y.val)[0]! = 0 := by
  have := lineC_eq 0 y
  rw [Fin.val_zero] at this
  rw [this]
  rfl

theorem lamSel_size : (lamSel ()).size = 5 := rfl

theorem lamSel_map_get {i : ℕ} (hi : i < 5) :
    ((lamSel ()).map (lineC 0))[i]! = lineC 0 (lamSel ())[i]! := by
  rw [getElem!_pos _ i (by rw [Array.size_map, lamSel_size]; exact hi), Array.getElem_map,
    getElem!_pos _ i (by rw [lamSel_size]; exact hi)]

end CFSG.Fischer
