module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxDescentBase
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxDescentCore
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxFrob
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false

theorem sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (N : ℕ) (h : f N = f 0) :
    ∑ j ∈ Finset.range N, f (j + 1) = ∑ j ∈ Finset.range N, f j := by
  have h1 := Finset.sum_range_succ' f N
  have h2 := Finset.sum_range_succ f N
  rw [h2, h] at h1
  exact (add_right_cancel h1).symm

section ArtinSchreier

open Polynomial in
theorem exists_artin_schreier {L : Type} [Field L] [IsAlgClosed L] (q : ℕ) (hq : 1 < q) (ε κ : L)
    (hε : ε ≠ 0) : ∃ z : L, ε * z ^ q - z + κ = 0 := by
  set p : L[X] := C ε * X ^ q - X + C κ with hp
  have hdeg : p.natDegree = q := by
    rw [hp, natDegree_add_C]
    have h1 : (C ε * X ^ q : L[X]).natDegree = q := natDegree_C_mul_X_pow q ε hε
    have h2 : (X : L[X]).natDegree = 1 := natDegree_X
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [h1, h2]; exact hq), h1]
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hd : p.degree ≠ 0 := by
    rw [degree_eq_natDegree hp0, hdeg]
    exact_mod_cast (by omega : q ≠ 0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd
  refine ⟨z, ?_⟩
  have := hz
  simpa [hp, IsRoot.def] using this

end ArtinSchreier


section Seq

variable {τ : Tag} {L : Type} [Field L]

@[expose] def Yprod (β : ℕ → Fin τ.rank → ℤ) (s : ℕ → L) (N : ℕ) : ModGL τ L :=
  ((List.range N).map fun j => pinnedX τ L (β j) (s j)).prod

theorem Yprod_zero (β : ℕ → Fin τ.rank → ℤ) (s : ℕ → L) : Yprod β s 0 = 1 := by
  simp [Yprod]

theorem Yprod_succ (β : ℕ → Fin τ.rank → ℤ) (s : ℕ → L) (N : ℕ) :
    Yprod β s (N + 1) = Yprod β s N * pinnedX τ L (β N) (s N) := by
  simp [Yprod, List.range_succ]

theorem Yprod_spec {β : ℕ → Fin τ.rank → ℤ} (hβ : ∀ j, β j ∈ Deg1 τ) (s : ℕ → L) (N : ℕ) :
    Yprod β s N ∈ Qθ τ L ∧ heisCoord τ L (Yprod β s N) =
      ∑ j ∈ Finset.range N, (Pi.single (β j) (s j) : (Fin τ.rank → ℤ) → L) := by
  induction N with
  | zero => rw [Yprod_zero, Finset.sum_range_zero]; exact ⟨one_mem _, heisCoord_one⟩
  | succ N ih =>
    obtain ⟨hQ, hc⟩ := ih
    have hQa := pinnedX_mem_Qθ_of_mem_Deg1 (K := L) (hβ N) (s N)
    refine ⟨by rw [Yprod_succ]; exact mul_mem hQ hQa, ?_⟩
    rw [Yprod_succ, (heisCoord_spec τ L).mul _ hQ _ hQa, hc,
      (heisCoord_spec τ L).pinnedX_deg1 _ (hβ N), Finset.sum_range_succ]

theorem Yprod_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {β : ℕ → Fin τ.rank → ℤ}
    (hβ : ∀ j, β j ∈ S) (s : ℕ → L) (N : ℕ) : Yprod β s N ∈ rootSpan τ L S := by
  induction N with
  | zero => rw [Yprod_zero]; exact one_mem _
  | succ N ih => rw [Yprod_succ]; exact mul_mem ih (pinnedX_mem_rootSpan (hβ N) _)

end Seq

section Twist

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

@[expose] def nw : ModGL τ D.L := canonicalRep (coxeterSystem τ) D.L w

@[expose] def twF : ModGL τ D.L →* ModGL τ D.L := (MulAut.conj (nw D)).toMonoidHom.comp (Fm D.Fr)

theorem twF_apply (y : ModGL τ D.L) : twF D y = nw D * Fm D.Fr y * (nw D)⁻¹ := rfl

theorem Fm_conj_g (y : ModGL τ D.L) :
    Fm D.Fr (D.g * y * D.g⁻¹) = D.g * twF D y * D.g⁻¹ := by
  have h : Fm D.Fr D.g = D.g * nw D := D.lang
  rw [map_mul, map_mul, map_inv, h, twF_apply]
  group

theorem twF_pinnedX {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : D.L, ε * ε = 1 ∧ ∀ c : D.L,
      twF D (pinnedX τ D.L β c) = pinnedX τ D.L (w • β) (ε * D.Fr c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L w hβ
  exact ⟨ε, hε, fun c => by rw [twF_apply, Fm_pinnedX]; exact h (D.Fr c)⟩

theorem twF_Yprod {β : ℕ → Fin τ.rank → ℤ} {ε : ℕ → D.L}
    (hε : ∀ j c, twF D (pinnedX τ D.L (β j) c) = pinnedX τ D.L (w • β j) (ε j * D.Fr c))
    (s : ℕ → D.L) (N : ℕ) :
    twF D (Yprod β s N) = Yprod (fun j => w • β j) (fun j => ε j * D.Fr (s j)) N := by
  induction N with
  | zero => rw [Yprod_zero, Yprod_zero, map_one]
  | succ N ih => rw [Yprod_succ, Yprod_succ, map_mul, ih, hε]

theorem exists_fixed_lift (N : ℕ) (β : ℕ → Fin τ.rank → ℤ) (hβ : ∀ j, β j ∈ Deg1 τ)
    (hβw : ∀ j, w • β j = β (j + 1)) (hβN : β N = β 0) {ε : ℕ → D.L}
    (hε : ∀ j c, twF D (pinnedX τ D.L (β j) c) = pinnedX τ D.L (w • β j) (ε j * D.Fr c))
    {εθ : D.L} (hεθ0 : εθ ≠ 0)
    (hεθ : ∀ c, twF D (pinnedX τ D.L (highRoot τ) c) =
      pinnedX τ D.L (highRoot τ) (εθ * D.Fr c))
    (s : ℕ → D.L) (hs : ∀ j, s (j + 1) = ε j * D.Fr (s j)) (hsN : s N = s 0) :
    ∃ z : D.L, twF D (Yprod β s N * pinnedX τ D.L (highRoot τ) z) =
      Yprod β s N * pinnedX τ D.L (highRoot τ) z := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hspec := heisCoord_spec τ D.L
  obtain ⟨hYQ, hYc⟩ := Yprod_spec hβ s N
  have hβ' : ∀ j, β (j + 1) ∈ Deg1 τ := fun j => hβ (j + 1)
  have e1 : (fun j => w • β j) = fun j => β (j + 1) := funext hβw
  have e2 : (fun j => ε j * D.Fr (s j)) = fun j => s (j + 1) := funext fun j => (hs j).symm
  have htw : twF D (Yprod β s N) = Yprod (fun j => β (j + 1)) (fun j => s (j + 1)) N := by
    rw [twF_Yprod D hε, e1, e2]
  obtain ⟨hZQ, hZc⟩ := Yprod_spec hβ' (fun j => s (j + 1)) N
  have hcoords : heisCoord τ D.L (Yprod (fun j => β (j + 1)) (fun j => s (j + 1)) N) =
      heisCoord τ D.L (Yprod β s N) := by
    rw [hZc, hYc]
    exact sum_range_shift (fun j => (Pi.single (β j) (s j) : (Fin τ.rank → ℤ) → D.L)) N
      (by simp only [hβN, hsN])
  have hu : (Yprod β s N)⁻¹ * Yprod (fun j => β (j + 1)) (fun j => s (j + 1)) N ∈ Uθ τ D.L := by
    refine (hspec.eq_zero_iff _ (mul_mem (inv_mem hYQ) hZQ)).1 ?_
    rw [hspec.mul _ (inv_mem hYQ) _ hZQ, heisCoord_inv hYQ, hcoords]
    exact neg_add_cancel _
  obtain ⟨κ, hκ⟩ := mem_rootSubgroup.1 hu
  have hZ : Yprod (fun j => β (j + 1)) (fun j => s (j + 1)) N =
      Yprod β s N * pinnedX τ D.L (highRoot τ) κ := by
    rw [hκ]; group
  obtain ⟨z, hz⟩ := exists_artin_schreier (Nat.card K) Finite.one_lt_card εθ κ hεθ0
  refine ⟨z, ?_⟩
  have hzz : κ + εθ * D.Fr z = z := by
    rw [D.hFr]
    linear_combination hz
  rw [map_mul, htw, hεθ, hZ, mul_assoc, ← pinnedX_add, hzz]

end Twist

section Frame

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}

theorem mem_frame_iff' (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

@[expose] def hat (D : LangLevi τ K w) (x : ModGL τ K) : ModGL τ D.L :=
  D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g

end Frame

section Orbit

variable {τ : Tag} {w : WeylGroup τ}

theorem smul_mem_Deg1 (hwθ : w • highRoot τ = highRoot τ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ Deg1 τ) : w • β ∈ Deg1 τ := by
  refine ⟨IsRoot.smul hβ.1 w, ?_⟩
  have h1 : CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) (w • β) =
      CFSG.LieType.Steinberg.Adjoint.iform (highRoot τ) β := by
    conv_lhs => rw [← hwθ]
    exact iform_smul w _ _
  rw [iform_highRoot_apply, iform_highRoot_apply] at h1
  have := mul_left_cancel₀ (cθ_ne_zero τ) h1
  show (w • β) (iθ τ) = 1
  rw [this]
  exact hβ.2

theorem orbit_mem {S : Set (Fin τ.rank → ℤ)} (hwθ : w • highRoot τ = highRoot τ)
    (hwS : ∀ β ∈ S, w • β ∈ S) {β₀ : Fin τ.rank → ℤ} (hβS : β₀ ∈ S) (hβ1 : β₀ ∈ Deg1 τ) :
    ∀ j : ℕ, (w ^ j) • β₀ ∈ S ∧ (w ^ j) • β₀ ∈ Deg1 τ := by
  intro j
  induction j with
  | zero => simpa using And.intro hβS hβ1
  | succ j ih =>
    rw [pow_succ', mul_smul]
    exact ⟨hwS _ ih.1, smul_mem_Deg1 hwθ ih.2⟩

end Orbit

theorem centralizes_deg1 {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)} (hθS : highRoot τ ∈ S)
    (hwθ : w • highRoot τ = highRoot τ) (hwS : ∀ β ∈ S, w • β ∈ S)
    {x : ModGL τ K} (hxS : ∀ y ∈ D.frame S, x * y = y * x)
    (hθ : ∀ u ∈ Uθ τ D.L, hat D x * u = u * hat D x)
    (hn : ∀ u ∈ Heis.Uneg τ D.L, hat D x * u = u * hat D x)
    {β₀ : Fin τ.rank → ℤ} (hβS : β₀ ∈ S) (hβ1 : β₀ ∈ Deg1 τ) (cc : D.L) :
    hat D x * pinnedX τ D.L β₀ cc = pinnedX τ D.L β₀ cc * hat D x := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set q := Nat.card K with hqdef
  have hq1 : 1 < q := Finite.one_lt_card
  have hq0 : (q : D.L) = 0 := by
    haveI := Fintype.ofFinite K
    rw [hqdef, Nat.card_eq_fintype_card, ← map_natCast (algebraMap K D.L),
      Nat.cast_card_eq_zero, map_zero]
  set N := orderOf w with hNdef
  have hN : 0 < N := orderOf_pos w
  obtain ⟨β, hβdef⟩ : ∃ β : ℕ → Fin τ.rank → ℤ, β = fun j => (w ^ j) • β₀ := ⟨_, rfl⟩
  have hβmem : ∀ j, β j ∈ S ∧ β j ∈ Deg1 τ := fun j => by
    rw [hβdef]
    exact orbit_mem hwθ hwS hβS hβ1 j
  have hβw : ∀ j, w • β j = β (j + 1) := fun j => by
    simp only [hβdef]
    rw [pow_succ', mul_smul]
  have hβN : β N = β 0 := by
    simp only [hβdef]
    rw [hNdef, pow_orderOf_eq_one, pow_zero]
  have hβ0 : β 0 = β₀ := by simp [hβdef]
  choose ε hε1 hε2 using fun j => twF_pinnedX D (hβmem j).2.1
  obtain ⟨εθ, hεθ1, hεθ2⟩ := twF_pinnedX D (isRoot_highRoot τ)
  rw [hwθ] at hεθ2
  have hεθ0 : εθ ≠ 0 := fun h => by
    rw [h, zero_mul] at hεθ1
    exact zero_ne_one hεθ1
  have hε0 : ∀ j, ε j ≠ 0 := fun j h => by
    have := hε1 j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hcore := descent_core (Wsub (hat D x) hθ hn) q hq1 hq0 N hN ε hε0
    (fun j => (Pi.single (β j) 1 : (Fin τ.rank → ℤ) → D.L)) ?_
  · have h0 := hcore 0 hN
    rw [hβ0] at h0
    have h1 : (Pi.single β₀ cc : (Fin τ.rank → ℤ) → D.L) ∈ Wsub (hat D x) hθ hn := by
      have := Submodule.smul_mem _ cc h0
      have e : cc • (Pi.single β₀ 1 : (Fin τ.rank → ℤ) → D.L) = Pi.single β₀ cc := by
        funext ν
        by_cases h : ν = β₀ <;> simp [Pi.single_apply, h]
      rwa [e] at this
    exact (mem_CQ.1 (pinnedX_mem_CQ hθ hn hβ1 cc h1)).2
  · intro a ha
    set s : ℕ → D.L := fun j => Cseq ε q j * a ^ (q ^ j) with hsdef
    have hs : ∀ j, s (j + 1) = ε j * D.Fr (s j) := by
      intro j
      simp only [hsdef]
      rw [D.hFr, Cseq, mul_pow, ← pow_mul, pow_succ]
      ring
    have hs0 : s 0 = a := by simp [hsdef, Cseq]
    have hsN : s N = s 0 := by rw [hs0]; exact ha
    obtain ⟨z, hz⟩ := exists_fixed_lift D N β (fun j => (hβmem j).2) hβw hβN hε2 hεθ0 hεθ2 s hs hsN
    set ŷ := Yprod β s N * pinnedX τ D.L (highRoot τ) z with hŷ
    have hθQ : pinnedX τ D.L (highRoot τ) z ∈ Qθ τ D.L :=
      Uθ_le_Qθ (mem_rootSubgroup.2 ⟨z, rfl⟩)
    obtain ⟨hYQ, hYc⟩ := Yprod_spec (fun j => (hβmem j).2) s N
    have hŷQ : ŷ ∈ Qθ τ D.L := mul_mem hYQ hθQ
    have hŷS : ŷ ∈ rootSpan τ D.L S :=
      mul_mem (Yprod_mem_rootSpan (fun j => (hβmem j).1) s N) (pinnedX_mem_rootSpan hθS z)
    have hŷcoord : heisCoord τ D.L ŷ =
        ∑ j ∈ Finset.range N, (s j) • (Pi.single (β j) 1 : (Fin τ.rank → ℤ) → D.L) := by
      rw [hŷ, (heisCoord_spec τ D.L).mul _ hYQ _ hθQ, hYc,
        (heisCoord_spec τ D.L).pinnedX_highRoot, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      funext ν
      by_cases h : ν = β j <;> simp [Pi.single_apply, h]
    have hyQ : D.g * ŷ * D.g⁻¹ ∈ Qθ τ D.L :=
      (Subgroup.mem_normalizer_iff.1
        (Pθ_le_normalizer_Qθ τ D.L (Lθ_le_Pθ τ D.L D.g_mem)) ŷ).1 hŷQ
    have hyF : Fm D.Fr (D.g * ŷ * D.g⁻¹) = D.g * ŷ * D.g⁻¹ := by
      rw [Fm_conj_g, hz]
    obtain ⟨y₀, hy₀Q, hy₀⟩ := exists_rational_of_fixed D.Fr D.hFr hyQ hyF
    have hy₀S : y₀ ∈ D.frame S := by
      rw [mem_frame_iff']
      refine ⟨Qθ_le_adjointGroup τ K hy₀Q, ?_⟩
      rw [hy₀]
      have e : D.g⁻¹ * (D.g * ŷ * D.g⁻¹) * D.g = ŷ := by group
      rw [e]
      exact hŷS
    have hcomm := hxS y₀ hy₀S
    have hcomm' : baseChangeGL (algebraMap K D.L) x * (D.g * ŷ * D.g⁻¹) =
        (D.g * ŷ * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
      rw [← hy₀, ← map_mul, ← map_mul, hcomm]
    have hxŷ : hat D x * ŷ = ŷ * hat D x := by
      unfold hat
      calc D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g * ŷ
          = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) x * (D.g * ŷ * D.g⁻¹)) * D.g := by group
        _ = D.g⁻¹ * ((D.g * ŷ * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x) * D.g := by
          rw [hcomm']
        _ = ŷ * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) := by group
    rw [← hŷcoord]
    exact coord_mem_Wsub hθ hn (mem_CQ.2 ⟨hŷQ, hxŷ⟩)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
