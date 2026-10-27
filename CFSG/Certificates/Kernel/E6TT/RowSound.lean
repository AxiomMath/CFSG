module

public import Certificates.Data.Kernel.E6TT.Row
public import CFSG.Certificates.Kernel.E6TT.WeylSound
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTRank
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTCoset

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec dot iform cartan roots reps classes kerRoots kerRootsOf act
  followOrbit)
open Certificates.Data.E6TableTTwo (cosetW orbitLen inOrbit rankOf)
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (twistInner compRank componentOrbitLength)
open CFSG.StandardType.TablePThreeKG (classSet E6Admissible repZ vecZ bList act_bList_ofFn
  e6Two_classes_facts)

local notation "ip" => CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6)

theorem rho_sum (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (x : Fin Tag.E6.rank → ℤ) : ρ x = ∑ i, x i • ρ (Pi.single i 1) := by
  let ρA : (Fin Tag.E6.rank → ℤ) ≃+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := ρ, invFun := ρ.symm, left_inv := ρ.left_inv, right_inv := ρ.right_inv,
      map_add' := hadd }
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_eq_of_ne (Ne.symm hbj)]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [hx]
  change ρA (∑ i, x i • (Pi.single i 1)) = ∑ i, x i • ρA (Pi.single i 1)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_zsmul ρA (x i) (Pi.single i 1)

theorem ip_sum_sum (a c : Fin Tag.E6.rank → ℤ) (u w : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)) :
    ip (∑ i, a i • u i) (∑ j, c j • w j) = ∑ i, ∑ j, a i * c j * ip (u i) (w j) := by
  have hl : ∀ (f : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)) y, ip (∑ i, f i) y = ∑ i, ip (f i) y :=
    fun f y => map_sum (AddMonoidHom.mk' (fun x => ip x y)
      (fun x x' => CFSG.LieType.Steinberg.Adjoint.iform_add_left x x' y)) f Finset.univ
  have hr : ∀ x (f : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)), ip x (∑ j, f j) = ∑ j, ip x (f j) :=
    fun x f => map_sum (AddMonoidHom.mk' (fun y => ip x y)
      (fun y y' => CFSG.LieType.Steinberg.Adjoint.iform_add_right x y y')) f Finset.univ
  rw [hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CFSG.LieType.Steinberg.Adjoint.iform_smul_left, hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CFSG.LieType.Steinberg.Adjoint.iform_smul_right]
  ring

theorem ip_rho (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hg : ∀ i j, ip (ρ (Pi.single i 1)) (ρ (Pi.single j 1)) =
      ip (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1)) (x y : Fin Tag.E6.rank → ℤ) :
    ip (ρ x) (ρ y) = ip x y := by
  have e : ∀ z : Fin Tag.E6.rank → ℤ, z = ∑ i, z i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) :=
    rho_sum (Equiv.refl _) (fun _ _ => rfl)
  rw [rho_sum ρ hadd x, rho_sum ρ hadd y, ip_sum_sum]
  conv_rhs => rw [e x, e y, ip_sum_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hg]

@[expose] def chiK (k : Fin 5) (x : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ m, ((x m : ℤ) : ZMod 3) * repZ k m

theorem chi_rho (k : Fin 5) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hc : ∀ i, ∑ m, ((ρ (Pi.single i 1) m : ℤ) : ZMod 3) * repZ k m = 2 * repZ k i)
    (x : Fin Tag.E6.rank → ℤ) : chiK k (ρ x) = 2 * chiK k x := by
  unfold chiK
  rw [rho_sum ρ hadd x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := hc i
  calc ∑ m, ((x i : ℤ) : ZMod 3) * ((ρ (Pi.single i 1) m : ℤ) : ZMod 3) * repZ k m
      = ((x i : ℤ) : ZMod 3) * ∑ m, ((ρ (Pi.single i 1) m : ℤ) : ZMod 3) * repZ k m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = 2 * (((x i : ℤ) : ZMod 3) * repZ k i) := by rw [h]; ring

theorem emod3_iff (z : ℤ) : (z % 3 == 0) = true ↔ ((z : ZMod 3) = 0) := by
  rw [beq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  norm_num

theorem ofFn_mem_ker (k : Fin 5) (γ : Fin Tag.E6.rank → ℤ) :
    List.ofFn γ ∈ kerRoots (reps.getD k []) ↔ IsRoot Tag.E6 γ ∧ chiK k γ = 0 := by
  rw [kerRoots, kerRootsOf, List.mem_filter, ← CFSG.StandardType.TablePThreeKG.isRoot_iff_mem_roots, emod3_iff, dot_ofFnE]
  refine and_congr_right fun _ => ?_
  have hrep : ∀ m : Fin Tag.E6.rank,
      (repZ k) m = (((reps.getD k []).getD m.val 0 : ℤ) : ZMod 3) := fun m => by
    simp [repZ, vecZ]
  unfold chiK
  push_cast
  simp only [hrep]

theorem ker_rho (k : Fin 5) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ))
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) (repZ k) 2) {γ : Fin Tag.E6.rank → ℤ}
    (h : List.ofFn γ ∈ kerRoots (reps.getD k [])) : List.ofFn (ρ γ) ∈ kerRoots (reps.getD k []) := by
  obtain ⟨hr, hc⟩ := (ofFn_mem_ker k γ).1 h
  refine (ofFn_mem_ker k _).2 ⟨hroot γ hr, ?_⟩
  rw [chi_rho k ρ hadd hadm.2.2, hc, mul_zero]

theorem exists_ip_ne {S : Set (Fin Tag.E6.rank → ℤ)} {z y : Fin Tag.E6.rank → ℤ}
    (hy : y ∈ AddSubgroup.closure S) (hne : ip z y ≠ 0) : ∃ s ∈ S, ip z s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine AddSubgroup.closure_induction (p := fun y _ => ip z y = 0) (fun s hs => hcon s hs) ?_ ?_ ?_ hy
  · simp [CFSG.LieType.Steinberg.Adjoint.iform]
  · intro a b _ _ ha hb
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_right, ha, hb, add_zero]
  · intro a _ ha
    have e : ip z (-a) = ip z ((-1 : ℤ) • a) := by rw [neg_one_smul]
    rw [e, CFSG.LieType.Steinberg.Adjoint.iform_smul_right, ha, mul_zero]

theorem ip_self_root {γ : Fin Tag.E6.rank → ℤ} (h : IsRoot Tag.E6 γ) : ip γ γ = 2 := by
  obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot h
  rw [hj]
  simp [CFSG.Blueprint.Chevalley.Tag.symmetrizer]

theorem meet_of_mem {l : List Vec} (hroot : ∀ x ∈ l, x ∈ roots ()) {H : List Nat}
    {O : List (List Nat)} (hc : classK l H O = true) {x : Vec} (hx : x ∈ l) (h6 : x.length = 6) :
    meetK H x = true := by
  obtain ⟨-, hlin, -, -⟩ := classK_spec hc
  have hΔ6 : ∀ δ ∈ dK H, δ.length = 6 := length_of_mem_vecs _ _
  obtain ⟨cs, hcs⟩ := hlin x hx
  have hmem := (lin_mem (toV '' {δ | δ ∈ dK H}) cs (dK H) hΔ6 (fun δ hδ => ⟨δ, hδ, rfl⟩)).2
  change toV (lin cs (vecs (H.getD 2 0) (H.getD 0 0))) ∈ _ at hmem
  rw [← hcs] at hmem
  have hr : IsRoot Tag.E6 (toV x) := by
    rw [CFSG.StandardType.TablePThreeKG.isRoot_iff_mem_roots, ofFn_toV h6]
    exact hroot x hx
  obtain ⟨_, ⟨δ, hδ, rfl⟩, hne⟩ := exists_ip_ne hmem (by rw [ip_self_root hr]; decide)
  unfold meetK
  refine List.any_eq_true.2 ⟨δ, hδ, ?_⟩
  rw [iform_eq_ip h6 (hΔ6 δ hδ)]
  exact bne_iff_ne.2 hne

theorem mem_of_meet (k : Fin 5) {l : List Vec} (hl : l ∈ classes (reps.getD k [])) {H : List Nat}
    {O : List (List Nat)} (hc : classK l H O = true) {x : Vec}
    (hx : x ∈ kerRoots (reps.getD k [])) (h : meetK H x = true) : x ∈ l := by
  obtain ⟨hΔl, -, -, -⟩ := classK_spec hc
  obtain ⟨-, hlen, -, -, hclos⟩ := (e6Two_classes_facts k).1 l hl
  obtain ⟨δ, hδ, hne⟩ := List.any_eq_true.1 h
  have hδl := hΔl δ hδ
  have hx6 : x.length = 6 := by
    obtain ⟨l', hl', hxl'⟩ := (e6Two_classes_facts k).2 x hx
    exact ((e6Two_classes_facts k).1 l' hl').2.1 x hxl'
  refine hclos δ hδl x hx ?_
  rw [iform_eq_ip (hlen δ hδl) hx6, CFSG.LieType.Steinberg.Adjoint.iform_comm,
    ← iform_eq_ip hx6 (hlen δ hδl)]
  exact bne_iff_ne.1 hne

theorem idxK_spec (x : Vec) : ∀ (Hs : List (List Nat)) (i : Nat),
    i ≤ idxK x Hs i ∧ (idxK x Hs i < i + Hs.length → meetK (Hs.getD (idxK x Hs i - i) []) x = true)
  | [], i => by
    have e : idxK x [] i = i := rfl
    rw [e]
    exact ⟨le_rfl, fun h => absurd h (by simp)⟩
  | H :: Hs, i => by
    have e : idxK x (H :: Hs) i = if meetK H x = true then i else idxK x Hs (i + 1) :=
      nIf_eqE _ _ _
    rw [e]
    by_cases hm : meetK H x = true
    · rw [if_pos hm]
      exact ⟨le_rfl, fun _ => by rw [Nat.sub_self, List.getD_cons_zero]; exact hm⟩
    · rw [if_neg hm]
      obtain ⟨h1, h2⟩ := idxK_spec x Hs (i + 1)
      refine ⟨by omega, fun hlt => ?_⟩
      have e2 : idxK x Hs (i + 1) - i = (idxK x Hs (i + 1) - (i + 1)) + 1 := by omega
      rw [e2, List.getD_cons_succ]
      exact h2 (by simp only [List.length_cons] at hlt; omega)

theorem act_toV (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    {x : Vec} (hx : x.length = 6) :
    act (bList fun i => ρ (Pi.single i 1)) x = List.ofFn (ρ (toV x)) := by
  conv_lhs => rw [← ofFn_toV hx]
  exact act_bList_ofFn ρ hadd _

theorem class_ker (k : Fin 5) {l : List Vec} (hl : l ∈ classes (reps.getD k [])) {x : Vec}
    (hx : x ∈ l) : x ∈ kerRoots (reps.getD k []) ∧ x.length = 6 :=
  ⟨((e6Two_classes_facts k).1 l hl).2.2.2.1 x hx, ((e6Two_classes_facts k).1 l hl).2.1 x hx⟩

theorem classSub (k : Fin 5) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ))
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) (repZ k) 2)
    {l l' : List Vec} (hl : l ∈ classes (reps.getD k [])) (hl' : l' ∈ classes (reps.getD k []))
    {H H' : List Nat} {O O' : List (List Nat)} (hc : classK l H O = true)
    (hc' : classK l' H' O' = true) (hconn : connK H = true)
    (hm : meetK H' (act (bList fun i => ρ (Pi.single i 1)) (hdK H)) = true) :
    ∀ x ∈ l, act (bList fun i => ρ (Pi.single i 1)) x ∈ l' := by
  set b := bList fun i => ρ (Pi.single i 1) with hb
  obtain ⟨hΔl, hlin, -, -⟩ := classK_spec hc
  obtain ⟨-, -, -, -, hclos'⟩ := (e6Two_classes_facts k).1 l' hl'
  have hΔ6 : ∀ δ ∈ dK H, δ.length = 6 := length_of_mem_vecs _ _
  have hiso := ip_rho ρ hadd (fun i j => hadm.2.1 i j)
  have hkerI : ∀ x ∈ l, act b x ∈ kerRoots (reps.getD k []) := by
    intro x hx
    obtain ⟨hxK, hx6⟩ := class_ker k hl hx
    rw [act_toV ρ hadd hx6]
    rw [← ofFn_toV hx6] at hxK
    exact ker_rho k ρ hadd hroot hadm hxK
  have hform : ∀ x ∈ l, ∀ y ∈ l, iform (act b x) (act b y) = iform x y := by
    intro x hx y hy
    have hx6 := (class_ker k hl hx).2
    have hy6 := (class_ker k hl hy).2
    rw [act_toV ρ hadd hx6, act_toV ρ hadd hy6, iform_eq_ip (length_ofFn6 _) (length_ofFn6 _),
      toV_ofFn, toV_ofFn, hiso, ← iform_eq_ip hx6 hy6]
  have hstep : ∀ x ∈ l, ∀ y ∈ l, act b x ∈ l' → iform x y ≠ 0 → act b y ∈ l' := by
    intro x hx y hy hxl' hne
    exact hclos' _ hxl' _ (hkerI y hy) (by rw [hform x hx y hy]; exact hne)
  have hsimple : ∀ t, t < (dK H).length → act b ((dK H).getD t []) ∈ l' := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro ht
    have hmemt : (dK H).getD t [] ∈ dK H := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact mem_of_meet k hl' hc' (hkerI _ (hΔl _ hmemt)) hm
    · have hct : bIf(Nat.beq (0 + t) 0, true, ((dK H).take (0 + t)).any fun δ' =>
          iform ((dK H).getD t []) δ' != 0) = true := allIdx_spec _ (dK H) 0 hconn t ht
      have hne0 : Nat.beq t 0 = false := by
        cases t with
        | zero => omega
        | succ n => rfl
      rw [Nat.zero_add, hne0] at hct
      change (((dK H).take t).any fun δ' => iform ((dK H).getD t []) δ' != 0) = true at hct
      obtain ⟨δ', hδ', hne⟩ := List.any_eq_true.1 hct
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hδ'
      rw [List.length_take] at hs
      have hst : s < t := lt_of_lt_of_le hs (min_le_left _ _)
      have hsl : s < (dK H).length := lt_trans hst ht
      have e : (List.take t (dK H))[s] = (dK H).getD s [] := by
        rw [List.getElem_take, List.getD_eq_getElem _ _ hsl]
      rw [e] at hne
      have hmems : (dK H).getD s [] ∈ dK H := by
        rw [List.getD_eq_getElem _ _ hsl]
        exact List.getElem_mem hsl
      refine hstep _ (hΔl _ hmems) _ (hΔl _ hmemt) (ih s hst hsl) ?_
      have hs6 := hΔ6 _ hmems
      have ht6 := hΔ6 _ hmemt
      rw [iform_eq_ip hs6 ht6, CFSG.LieType.Steinberg.Adjoint.iform_comm, ← iform_eq_ip ht6 hs6]
      exact bne_iff_ne.1 hne
  intro x hx
  obtain ⟨hxK, hx6⟩ := class_ker k hl hx
  obtain ⟨cs, hcs⟩ := hlin x hx
  have hmem := (lin_mem (toV '' {δ | δ ∈ dK H}) cs (dK H) hΔ6 (fun δ hδ => ⟨δ, hδ, rfl⟩)).2
  change toV (lin cs (vecs (H.getD 2 0) (H.getD 0 0))) ∈ _ at hmem
  rw [← hcs] at hmem
  let ρA : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) := AddMonoidHom.mk' ρ hadd
  have hmemρ : ρ (toV x) ∈ AddSubgroup.closure (ρA '' (toV '' {δ | δ ∈ dK H})) := by
    rw [← AddMonoidHom.map_closure]
    exact AddSubgroup.mem_map_of_mem ρA hmem
  have hrx : IsRoot Tag.E6 (ρ (toV x)) :=
    hroot _ ((ofFn_mem_ker k _).1 (by rw [ofFn_toV hx6]; exact hxK)).1
  obtain ⟨_, ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩, hne⟩ :=
    exists_ip_ne hmemρ (by rw [ip_self_root hrx]; decide)
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem (hδ : δ ∈ dK H)
  have hδl' := hsimple t ht
  rw [List.getD_eq_getElem _ _ ht] at hδl'
  have hδ6 := hΔ6 _ (List.getElem_mem ht)
  refine hclos' _ hδl' _ (hkerI x hx) ?_
  rw [act_toV ρ hadd hδ6, act_toV ρ hadd hx6, iform_eq_ip (length_ofFn6 _) (length_ofFn6 _),
    toV_ofFn, toV_ofFn, CFSG.LieType.Steinberg.Adjoint.iform_comm]
  exact hne

def listOfPermK {n : ℕ} (p : Fin n → Fin n) : List ℕ := List.ofFn fun i => (p i).val

def ordK {n : ℕ} (p : Fin n → Fin n) (j : Fin n) : ℕ :=
  ((Finset.range n).image (fun m => (p^[m]) j)).card

theorem ordK_le {n : ℕ} (p : Fin n → Fin n) (j : Fin n) : ordK p j ≤ n := by
  unfold ordK
  calc ((Finset.range n).image (fun m => (p^[m]) j)).card
      ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

theorem ordK_pos {n : ℕ} (p : Fin n → Fin n) (j : Fin n) : 0 < ordK p j := by
  unfold ordK
  refine Finset.card_pos.mpr ⟨j, Finset.mem_image.mpr ⟨0, ?_, ?_⟩⟩
  · rw [Finset.mem_range]; exact Nat.zero_lt_of_lt j.isLt
  · simp

def OrbFacts (n : ℕ) : Prop := ∀ (p : Fin n → Fin n), Function.Bijective p →
    (∀ j : Fin n, (followOrbit (listOfPermK p) 6 j.val []).length = ordK p j) ∧
    (∀ j j' : Fin n, ((followOrbit (listOfPermK p) 6 j.val []).contains j'.val = true ↔
      j' ∈ (Finset.range n).image (fun m => (p^[m]) j))) ∧
    (∀ j : Fin n, (p^[ordK p j]) j = j) ∧
    (∀ j : Fin n, ∀ s : Fin n, 0 < s.val → s.val < ordK p j → (p^[s.val]) j ≠ j) ∧
    (∀ i : Fin n, (p^[6]) i = i)

theorem orbFacts0 : OrbFacts 0 := by unfold OrbFacts ordK listOfPermK; decide +kernel
theorem orbFacts1 : OrbFacts 1 := by unfold OrbFacts ordK listOfPermK; decide +kernel
theorem orbFacts2 : OrbFacts 2 := by unfold OrbFacts ordK listOfPermK; decide +kernel
theorem orbFacts3 : OrbFacts 3 := by unfold OrbFacts ordK listOfPermK; decide +kernel

theorem orbFacts {n : ℕ} (hn : n ≤ 3) : OrbFacts n := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl
  · exact orbFacts0
  · exact orbFacts1
  · exact orbFacts2
  · exact orbFacts3

theorem iterate_modK {n : ℕ} (p : Fin n → Fin n) (j : Fin n) {ord : ℕ}
    (hpos : 0 < ord) (hfix : (p^[ord]) j = j) (m : ℕ) :
    ∃ r < ord, (p^[r]) j = (p^[m]) j := by
  refine ⟨m % ord, Nat.mod_lt m hpos, ?_⟩
  have hfix' : ∀ k, ((p^[ord])^[k]) j = j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
  conv_rhs => rw [← Nat.mod_add_div m ord]
  rw [Function.iterate_add_apply, Function.iterate_mul, hfix']

theorem sInf_eqK {n : ℕ} (p : Fin n → Fin n) (j : Fin n)
    (hfix : (p^[ordK p j]) j = j)
    (hmin : ∀ s : ℕ, 0 < s → s < ordK p j → (p^[s]) j ≠ j) :
    sInf {s : ℕ | 0 < s ∧ (p^[s]) j = j} = ordK p j := by
  set S : Set ℕ := {s : ℕ | 0 < s ∧ (p^[s]) j = j}
  have hmem : ordK p j ∈ S := ⟨ordK_pos p j, hfix⟩
  have hSne : S.Nonempty := ⟨_, hmem⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  exact (hmin (sInf S) (Nat.sInf_mem hSne).1 (Nat.lt_of_not_le hlt)) (Nat.sInf_mem hSne).2

theorem eq_of_le_permK {n : ℕ} (p : Fin n → Fin n) (a : Fin n → ℕ)
    (h6 : ∀ i, (p^[6]) i = i) (hle : ∀ i, a i ≤ a (p i)) : ∀ i, a i = a (p i) := by
  intro i
  have hmono : ∀ m : ℕ, a ((p^[m]) i) ≤ a ((p^[m+1]) i) := by
    intro m
    rw [Function.iterate_succ_apply']
    exact hle _
  have h16 : a ((p^[1]) i) ≤ a ((p^[6]) i) :=
    le_trans (hmono 1) (le_trans (hmono 2) (le_trans (hmono 3) (le_trans (hmono 4) (hmono 5))))
  have h60 : a ((p^[6]) i) = a ((p^[0]) i) := by rw [h6 i]; rfl
  have hAeq : a ((p^[0]) i) = a ((p^[1]) i) := le_antisymm (hmono 0) (h16.trans_eq h60)
  simpa using hAeq

theorem classSet_finiteK (l : List Vec) : (classSet l).Finite :=
  (List.finite_toSet l).preimage (List.ofFn_injective.injOn)

theorem classes_len_leK (k : Fin 5) : (classes (reps.getD k [])).length ≤ 3 := by
  have hmem : (classes (reps.getD k [])).map List.length ∈
      (List.range 5).map (fun k => (classes (reps.getD k [])).map List.length) :=
    List.mem_map_of_mem (List.mem_range.mpr k.isLt)
  rw [CFSG.StandardType.TablePThreeKG.classes_lengths] at hmem
  have hlen : ∀ l ∈ ([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List ℕ)), l.length ≤ 3 := by
    decide
  have := hlen _ hmem
  rwa [List.length_map] at this

theorem classPermK (k : Fin 5) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (π : List ℕ)
    (hπlen : π.length = (classes (reps.getD k [])).length)
    (hlt : ∀ i < (classes (reps.getD k [])).length, π.getD i 0 < (classes (reps.getD k [])).length)
    (hsurj : ∀ i < (classes (reps.getD k [])).length,
      ∃ i' < (classes (reps.getD k [])).length, π.getD i' 0 = i)
    (hsub : ∀ i < (classes (reps.getD k [])).length, ∀ x ∈ (classes (reps.getD k [])).getD i [],
      List.ofFn (ρ (toV x)) ∈ (classes (reps.getD k [])).getD (π.getD i 0) [])
    (hinj : ∀ i i', i < (classes (reps.getD k [])).length → i' < (classes (reps.getD k [])).length →
      classSet ((classes (reps.getD k [])).getD i []) =
        classSet ((classes (reps.getD k [])).getD i' []) → i = i')
    (j : ℕ) (hj : j < (classes (reps.getD k [])).length) :
    componentOrbitLength ρ (classSet ((classes (reps.getD k [])).getD j [])) = orbitLen π j ∧
      ∀ j' < (classes (reps.getD k [])).length,
        ((∃ m : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[m] ''
            classSet ((classes (reps.getD k [])).getD j []) =
              classSet ((classes (reps.getD k [])).getD j' [])) ↔ inOrbit π j j' = true) := by
  set cl : List (List Vec) := classes (reps.getD k []) with hcl
  have hn : cl.length ≤ 3 := classes_len_leK k
  clear_value cl
  let p : Fin cl.length → Fin cl.length := fun i => ⟨π.getD i.val 0, hlt i.val i.isLt⟩
  have hp_surj : Function.Surjective p := by
    intro i
    obtain ⟨i', hi', he⟩ := hsurj i.val i.isLt
    exact ⟨⟨i', hi'⟩, Fin.ext he⟩
  have hp_inj : Function.Injective p := Finite.injective_iff_surjective.mpr hp_surj
  have hp_bij : Function.Bijective p := ⟨hp_inj, hp_surj⟩
  obtain ⟨hF1, hF2, hF3, hF4, hF6⟩ := orbFacts (n := cl.length) hn p hp_bij
  have hπ_eq : π = listOfPermK p := by
    apply List.ext_getElem
    · rw [listOfPermK, List.length_ofFn]; exact hπlen
    · intro i h1 h2
      rw [List.getElem_eq_getD (h := h1) (0 : ℕ)]
      simp only [listOfPermK, List.getElem_ofFn]
      rfl
  have hsub_image : ∀ i : Fin cl.length, ρ '' classSet (cl.getD i.val []) ⊆
      classSet (cl.getD (p i).val []) := by
    intro i γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    have h := hsub i.val i.isLt (List.ofFn δ) hδ
    rw [toV_ofFn] at h
    exact h
  have hcard_all : ∀ i : Fin cl.length, (classSet (cl.getD i.val [])).ncard =
      (classSet (cl.getD (p i).val [])).ncard :=
    eq_of_le_permK p (fun i => (classSet (cl.getD i.val [])).ncard) (hF6) (fun i => by
      calc (classSet (cl.getD i.val [])).ncard
          = (ρ '' classSet (cl.getD i.val [])).ncard :=
            (Set.ncard_image_of_injective _ ρ.injective).symm
        _ ≤ (classSet (cl.getD (p i).val [])).ncard :=
            Set.ncard_le_ncard (hsub_image i) (classSet_finiteK _))
  have himage : ∀ i : Fin cl.length, ρ '' classSet (cl.getD i.val []) =
      classSet (cl.getD (p i).val []) := by
    intro i
    refine Set.eq_of_subset_of_ncard_le (hsub_image i) ?_ (classSet_finiteK _)
    rw [← hcard_all i, Set.ncard_image_of_injective _ ρ.injective]
  let jj : Fin cl.length := ⟨j, hj⟩
  have hiter : ∀ m : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[m] ''
      classSet (cl.getD jj.val []) = classSet (cl.getD ((p^[m]) jj).val []) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ', Set.image_comp, ih, himage ((p^[m]) jj),
        Function.iterate_succ_apply']
  have hS_eq : {s : ℕ | 0 < s ∧ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
      classSet (cl.getD jj.val []) = classSet (cl.getD jj.val [])} =
      {s : ℕ | 0 < s ∧ (p^[s]) jj = jj} := by
    ext s
    simp only [Set.mem_setOf_eq]
    rw [hiter s]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Fin.ext (hinj _ _ ((p^[s]) jj).isLt jj.isLt h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]⟩
  have hcomp : componentOrbitLength ρ (classSet (cl.getD jj.val [])) = ordK p jj := by
    unfold componentOrbitLength
    rw [hS_eq]
    exact sInf_eqK p jj (hF3 jj)
      (fun s hs hlt' => hF4 jj ⟨s, lt_of_lt_of_le hlt' (ordK_le p jj)⟩ hs hlt')
  have hlen : orbitLen π j = ordK p jj := by
    rw [orbitLen, hπ_eq]
    exact hF1 jj
  refine ⟨by rw [hcomp, hlen], fun j' hj'' => ⟨?_, ?_⟩⟩
  · rintro ⟨m, hm⟩
    have heq : classSet (cl.getD ((p^[m]) jj).val []) = classSet (cl.getD j' []) := by
      rw [← hiter m, hm]
    have hpj : (p^[m]) jj = (⟨j', hj''⟩ : Fin cl.length) :=
      Fin.ext (hinj _ _ ((p^[m]) jj).isLt hj'' heq)
    obtain ⟨r, hr_lt, hr_eq⟩ := iterate_modK p jj (ordK_pos p jj) (hF3 jj) m
    have hmem : (⟨j', hj''⟩ : Fin cl.length) ∈
        (Finset.range cl.length).image (fun m => (p^[m]) jj) :=
      Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr
        (lt_of_lt_of_le hr_lt (ordK_le p jj)), hr_eq.trans hpj⟩
    rw [inOrbit, hπ_eq]
    exact (hF2 jj ⟨j', hj''⟩).mpr hmem
  · intro hmem
    rw [inOrbit, hπ_eq] at hmem
    obtain ⟨m, -, hm_eq⟩ := Finset.mem_image.mp ((hF2 jj ⟨j', hj''⟩).mp hmem)
    exact ⟨m, by rw [hiter m, hm_eq]⟩

end CFSG.KC.E6TT

end
