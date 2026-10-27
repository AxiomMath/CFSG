module

public import CFSG.Certificates.Kernel.E6TT.NegSound
public import CFSG.Certificates.Kernel.E6TT.RowKSound
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTClasses
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRank

public section

namespace CFSG.KC.E6TT

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (twistInner compRank componentOrbitLength)
open Certificates.Data.E6TableT (Vec roots reps classes)
open CFSG.StandardType.TablePThreeKG (E6Admissible E6KerComponent E6TableTAt E6TableTTwoStmt
  E6SolvTwo E6CosetW repZ classSet classes_lengths classSet_ncard classes_compRank
  e6KerComponent_iff_classes)

local notation "V6" => Fin Tag.E6.rank → ℤ

local notation "ip" => CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6)

theorem sum_single_eqA2 (x : Fin Tag.E6.rank → ℤ) : (∑ i, x i • Pi.single i 1) = x := by
  ext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sum_mul_repZ0 (f : Fin Tag.E6.rank → ZMod 3) : (∑ k, f k * repZ 0 k) = f 3 := by
  rw [Finset.sum_eq_single (3 : Fin Tag.E6.rank)]
  · have h : repZ 0 (3 : Fin Tag.E6.rank) = 1 := by decide
    rw [h, mul_one]
  · intro b _ hb
    have h : repZ 0 b = 0 := by
      fin_cases b
      · decide
      · decide
      · decide
      · exact absurd rfl hb
      · decide
      · decide
    rw [h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem repZ0_eigenvalue (ρ : Equiv.Perm V6) (r : ZMod 3) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) (repZ 0) r) : r = 1 ∨ r = 2 := by
  have hr0 : r ≠ 0 := by
    intro hr
    have hcoeff : ∀ i, (((ρ (Pi.single i 1)) 3 : ℤ) : ZMod 3) = 0 := by
      intro i
      have hi := hadm.2.2 i
      rw [hr] at hi
      rw [sum_mul_repZ0 (fun k => (((ρ (Pi.single i 1)) k : ℤ) : ZMod 3))] at hi
      simpa using hi
    let φ : V6 →+ V6 := AddMonoidHom.mk' ρ hadd
    have hmap : ∀ x, φ x = ∑ i, x i • ρ (Pi.single i 1) := by
      intro x
      conv_lhs => rw [← sum_single_eqA2 x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul]
      rfl
    have hcoord : ∀ x, (((φ x) (3 : Fin Tag.E6.rank) : ℤ) : ZMod 3) = 0 := by
      intro x
      rw [hmap x, Finset.sum_apply, Int.cast_sum]
      apply Finset.sum_eq_zero
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hcoeff i, zero_mul, mul_zero]
    have hsing : ((((φ (ρ.symm (Pi.single (3 : Fin Tag.E6.rank) 1))) 3 : ℤ)) : ZMod 3) = 0 :=
      hcoord (ρ.symm (Pi.single (3 : Fin Tag.E6.rank) 1))
    change ((((ρ (ρ.symm (Pi.single (3 : Fin Tag.E6.rank) 1))) 3 : ℤ)) : ZMod 3) = 0 at hsing
    rw [Equiv.apply_symm_apply] at hsing
    simp only [Pi.single_eq_same, Int.cast_one] at hsing
    exact one_ne_zero hsing
  fin_cases r
  · exact absurd rfl hr0
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem length_of_mem_classes_repA2 {l : List Vec} (hl : l ∈ classes (reps.getD (0 : Fin 5) [])) :
    l.length = 6 := by
  have h := classes_lengths
  have h0 := congrArg (fun l : List (List Nat) => l.getD 0 []) h
  have hlens : (classes (reps.getD (0 : Fin 5) [])).map List.length = [6, 6, 6] := by
    simpa using h0
  have hmem : l.length ∈ [6, 6, 6] := by
    rw [← hlens]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  omega

theorem classSet_injK (k : Fin 5)
    {Hs : List (List Nat)} {Os : List (List (List Nat))}
    (hw : wOKK (classes (reps.getD k [])) Hs Os = true) (hs : hsK Hs = true) :
    ∀ i i', i < (classes (reps.getD k [])).length → i' < (classes (reps.getD k [])).length →
      classSet ((classes (reps.getD k [])).getD i []) =
        classSet ((classes (reps.getD k [])).getD i' []) → i = i' := by
  obtain ⟨hHlen, -, hc⟩ := wOKK_spec hw
  obtain ⟨-, hsep⟩ := bAnd_true hs
  intro i i' hi hi' heq
  by_contra hne
  have hx := hdK_mem k (getD_mem_classes k hi) (hc i hi)
  have hx6 := (class_ker k (getD_mem_classes k hi) hx).2
  have h1 : toV (hdK (Hs.getD i [])) ∈ classSet ((classes (reps.getD k [])).getD i []) := by
    change List.ofFn (toV (hdK (Hs.getD i []))) ∈ (classes (reps.getD k [])).getD i []
    rw [ofFn_toV hx6]
    exact hx
  rw [heq] at h1
  have h2 : List.ofFn (toV (hdK (Hs.getD i []))) ∈ (classes (reps.getD k [])).getD i' [] := h1
  rw [ofFn_toV hx6] at h2
  have hm := meet_of_mem (class_roots k (getD_mem_classes k hi')) (hc i' hi') h2 hx6
  unfold sepK at hsep
  have hs1 := List.all_eq_true.1 hsep i (List.mem_range.2 (by omega))
  have hs2 := List.all_eq_true.1 hs1 i' (List.mem_range.2 (by omega))
  have hb : Nat.beq i i' = false := by
    cases h : Nat.beq i i'
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne
  rw [hb] at hs2
  have hs3 : (!meetK (Hs.getD i' []) (hdK (Hs.getD i []))) = true := hs2
  rw [hm] at hs3
  exact absurd hs3 (by decide)

theorem ip_iterate (ρ : Equiv.Perm V6)
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hg : ∀ i j, ip (ρ (Pi.single i 1)) (ρ (Pi.single j 1)) =
      ip (Pi.single i 1 : V6) (Pi.single j 1)) :
    ∀ (n : ℕ) (x y : V6), ip ((ρ : V6 → V6)^[n] x) ((ρ : V6 → V6)^[n] y) = ip x y
  | 0, _, _ => rfl
  | n + 1, x, y => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ip_rho ρ hadd hg,
      ip_iterate ρ hadd hg n]

theorem e6TableTAt_repA2_of_two
    (h2 : E6TableTTwoStmt) {Hs : List (List Nat)} {Os : List (List (List Nat))}
    (hw : wOKK (classes (reps.getD 0 [])) Hs Os = true) (hs : hsK Hs = true)
    (hpm : ∀ l ∈ classes (reps.getD 0 []), ∀ σ : V6 → V6, (∀ a b, σ (a + b) = σ a + σ b) →
      (∀ γ ∈ classSet l, σ γ ∈ classSet l) → (∀ x y, ip (σ x) (σ y) = ip x y) →
      twistInner (classSet l) σ ∨ twistInner (classSet l) (fun x => -σ x)) :
    E6TableTAt (repZ 0) := by
  intro ρ r hadd hroot hadm hv0 Ψ hΨ hsingle
  have hr : r = 1 ∨ r = 2 := repZ0_eigenvalue ρ r hadd hadm
  obtain ⟨l, hl, rfl⟩ := (e6KerComponent_iff_classes 0 Ψ).mp hΨ
  have hncard : (classSet l).ncard = 6 := by
    rw [classSet_ncard 0 l hl]
    exact length_of_mem_classes_repA2 hl
  have hrank : compRank (classSet l) = 2 := (classes_compRank 0 l hl).1 rfl
  have hlen3 : (classes (reps.getD (0 : Fin 5) [])).length = 3 := cls_count 0
  have hinj := classSet_injK 0 hw hs
  have hcomp : ∀ j < 3,
      E6KerComponent (repZ 0) (classSet ((classes (reps.getD (0 : Fin 5) [])).getD j [])) :=
    fun j hj => (e6KerComponent_iff_classes 0 _).mpr ⟨_, getD_mem_classes 0 (by omega), rfl⟩
  have hd : ∀ i i', i < 3 → i' < 3 → i ≠ i' →
      classSet ((classes (reps.getD (0 : Fin 5) [])).getD i []) ≠
        classSet ((classes (reps.getD (0 : Fin 5) [])).getD i' []) :=
    fun i i' hi hi' hne heq => hne (hinj i i' (by omega) (by omega) heq)
  have horb : ∀ τ : Equiv.Perm V6, (∀ Ψ', E6KerComponent (repZ 0) Ψ' →
      ∃ k : ℕ, (τ : V6 → V6)^[k] '' classSet l = Ψ') →
      componentOrbitLength τ (classSet l) ≠ 1 ∧ componentOrbitLength τ (classSet l) ≠ 2 :=
    fun τ hτ => orbitLength_ne (hτ _ (hcomp 0 (by omega))) (hτ _ (hcomp 1 (by omega)))
      (hτ _ (hcomp 2 (by omega))) (hd 0 1 (by omega) (by omega) (by omega))
      (hd 0 2 (by omega) (by omega) (by omega)) (hd 1 2 (by omega) (by omega) (by omega))
  have htwo : ∀ τ : Equiv.Perm V6, (∀ x y, τ (x + y) = τ x + τ y) →
      (∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (τ γ)) →
      E6Admissible (fun i => τ (Pi.single i 1)) (repZ 0) 2 →
      (∀ Ψ', E6KerComponent (repZ 0) Ψ' → ∃ k : ℕ, (τ : V6 → V6)^[k] '' classSet l = Ψ') →
      componentOrbitLength τ (classSet l) = 3 ∧
        ¬ twistInner (classSet l) ((τ : V6 → V6)^[3]) := by
    intro τ htadd htroot htadm htsingle
    obtain ⟨hne1, hne2⟩ := horb τ htsingle
    have hnot : ¬ E6SolvTwo τ (classSet l) := by
      rintro (⟨h1, -⟩ | ⟨-, -, h1, -⟩)
      · rw [hrank] at h1
        exact absurd h1 (by decide)
      · exact hne1 h1
    have hall : ∀ Ψ', E6KerComponent (repZ 0) Ψ' →
        (∀ k : ℕ, (τ : V6 → V6)^[k] '' classSet l ≠ Ψ') → E6SolvTwo τ Ψ' := by
      intro Ψ' hΨ' hk
      obtain ⟨k, hk'⟩ := htsingle Ψ' hΨ'
      exact absurd hk' (hk k)
    obtain ⟨hW, hT⟩ := h2 τ (repZ 0) htadd htroot htadm hv0 (classSet l) hΨ hnot hall
    by_cases hc : E6CosetW τ
    · exfalso
      rcases hW hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h, -⟩
      · rw [hrank] at h
        exact absurd h (by decide)
      · rw [hrank] at h
        exact absurd h (by decide)
      · exact hne2 h
    · rcases hT hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h3, hn⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · rw [hrank] at h
        exact absurd h (by decide)
      · rw [hrank] at h
        exact absurd h (by decide)
      · rw [hrank] at h
        exact absurd h (by decide)
      · exact ⟨h3, hn⟩
      · rw [hrank] at h
        exact absurd h (by decide)
      · rw [hrank] at h
        exact absurd h (by decide)
  rcases hr with rfl | rfl
  ·
    have hneg : ∀ Ψ', E6KerComponent (repZ 0) Ψ' → ∀ x ∈ Ψ', -x ∈ Ψ' := by
      rintro Ψ' ⟨i, rfl⟩ x hx
      exact (isRootComponent_componentRoots i).neg_mem x hx
    have hσsingle : ∀ Ψ', E6KerComponent (repZ 0) Ψ' →
        ∃ k : ℕ, (negRho ρ : V6 → V6)^[k] '' classSet l = Ψ' := by
      intro Ψ' hΨ'
      obtain ⟨k, hk⟩ := hsingle Ψ' hΨ'
      refine ⟨k, ?_⟩
      rw [negRho_image ρ hadd k (by rw [hk]; exact hneg Ψ' hΨ'), hk]
    obtain ⟨hL, hout⟩ := htwo (negRho ρ) (negRho_add ρ hadd) (negRho_root ρ hroot)
      (negRho_adm ρ _ hadm) hσsingle
    rw [negRho_orbitLength ρ hadd (hneg _ hΨ)] at hL
    have hstab : (ρ : V6 → V6)^[3] '' classSet l = classSet l :=
      iterate_image_of_orbitLength hL (by decide)
    have hpm' := hpm l hl ((ρ : V6 → V6)^[3]) (iterate_add_hom ρ hadd 3)
      (fun γ hγ => by
        rw [← hstab]
        exact Set.mem_image_of_mem _ hγ)
      (ip_iterate ρ hadd hadm.2.1 3)
    have e3 : (negRho ρ : V6 → V6)^[3] = fun x => -(ρ : V6 → V6)^[3] x :=
      funext (negRho_iterate_three ρ hadd)
    rw [e3] at hout
    exact Or.inr (Or.inr (Or.inr ⟨hrank, hncard, hL, fun _ => hpm'.resolve_right hout,
      fun h => absurd h (by decide)⟩))
  ·
    obtain ⟨hL, hout⟩ := htwo ρ hadd hroot hadm hsingle
    exact Or.inr (Or.inr (Or.inr ⟨hrank, hncard, hL, fun h => absurd h (by decide), fun _ => hout⟩))

end CFSG.KC.E6TT

end
