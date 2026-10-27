module

public import CFSG.CGT.Foote82.T66.CaseIEnd
public import CFSG.CGT.Foote82.T66.CaseIS8Perm
import CFSG.GH74.Uniqueness.SU.SU10Fusion

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart

@[expose] def DeltaB (m : ℕ) : Set (Fin (m + 6)) := {i | 4 ≤ (i : ℕ)}

theorem ncard_DeltaB (m : ℕ) : (DeltaB m).ncard = m + 2 := by
  have e : Fin (m + 2) ≃ DeltaB m :=
    { toFun := fun j => ⟨⟨j.val + 4, by omega⟩, show 4 ≤ j.val + 4 by omega⟩
      invFun := fun i => ⟨i.1.val - 4, by have := i.1.2; omega⟩
      left_inv := fun j => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by
        have : 4 ≤ (i.1 : ℕ) := i.2
        simp only
        omega)) }
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ne_of_mem_DeltaB {m : ℕ} {x : Fin (m + 6)} (hx : x ∈ DeltaB m) :
    x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 := by
  have hx' : 4 ≤ (x : ℕ) := hx
  have h0 : ((0 : Fin (m + 6)) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin (m + 6)) : ℕ) = 1 := rfl
  have h2 : ((2 : Fin (m + 6)) : ℕ) = 2 := rfl
  have h3 : ((3 : Fin (m + 6)) : ℕ) = 3 := rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg Fin.val h; omega

theorem comm_dt {m : ℕ} {σ : Perm (Fin (m + 6))} (hσ : σ ∈ altOn (DeltaB m)) :
    σ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * σ := by
  refine (Equiv.Perm.Disjoint.commute ?_).eq
  intro x
  by_cases hx : x ∈ DeltaB m
  · right
    obtain ⟨h0, h1, h2, h3⟩ := ne_of_mem_DeltaB hx
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3, swap_apply_of_ne_of_ne h0 h1]
  · left; exact (mem_altOn_iff.1 hσ).2 x hx

theorem comm_dt_swap {m : ℕ} {a b : Fin (m + 6)} (ha : a ∈ DeltaB m) (hb : b ∈ DeltaB m) :
    swap a b * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * swap a b := by
  refine (Equiv.Perm.Disjoint.commute ?_).eq
  intro x
  by_cases hx : x ∈ DeltaB m
  · right
    obtain ⟨h0, h1, h2, h3⟩ := ne_of_mem_DeltaB hx
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3, swap_apply_of_ne_of_ne h0 h1]
  · left
    exact swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

theorem altOn_le_alt {m : ℕ} : altOn (DeltaB m) ≤ alternatingGroup (Fin (m + 6)) :=
  fun _ hσ => (mem_altOn_iff.1 hσ).1

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

@[expose] noncomputable def jB (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) :
    ↥(altOn (DeltaB m)) →* GLV V :=
  (jL ψ).comp (Subgroup.inclusion altOn_le_alt)

theorem jB_apply (σ : ↥(altOn (DeltaB m))) :
    jB ψ σ = pe ψ (iota2 (m + 6) (σ : Perm (Fin (m + 6)))) := rfl

theorem Hyp.jB_mem_L (h : Hyp G L z v H₁ m ψ) (σ : ↥(altOn (DeltaB m))) : jB ψ σ ∈ L :=
  h.jL_mem _

theorem jB_comm_tt (σ : ↥(altOn (DeltaB m))) : jB ψ σ * tt ψ = tt ψ * jB ψ σ := by
  rw [jB_apply, tt, ← map_mul, ← map_mul, ← map_mul, ← map_mul, comm_dt σ.2]

theorem Hyp.conjB_comm_z (h : Hyp G L z v H₁ m ψ) {hh : GLV V}
    (hht : hh * z * hh⁻¹ = tt ψ) (σ : ↥(altOn (DeltaB m))) :
    hh⁻¹ * jB ψ σ * hh * z = z * (hh⁻¹ * jB ψ σ * hh) := by
  have hz : z = hh⁻¹ * tt ψ * hh := by rw [← hht]; group
  rw [hz]
  calc hh⁻¹ * jB ψ σ * hh * (hh⁻¹ * tt ψ * hh) = hh⁻¹ * (jB ψ σ * tt ψ) * hh := by group
    _ = hh⁻¹ * (tt ψ * jB ψ σ) * hh := by rw [jB_comm_tt]
    _ = hh⁻¹ * tt ψ * hh * (hh⁻¹ * jB ψ σ * hh) := by group

theorem Hyp.conjB_mem_N (h : Hyp G L z v H₁ m ψ) {hh : GLV V} (hhG : hh ∈ G)
    (hht : hh * z * hh⁻¹ = tt ψ) (σ : ↥(altOn (DeltaB m))) :
    hh⁻¹ * jB ψ σ * hh ∈ NN G L :=
  h.centralizer_z_le (G.mul_mem (G.mul_mem (G.inv_mem hhG) (h.H₁_le_G (pe_mem _))) hhG)
    (h.conjB_comm_z hht σ)

theorem Hyp.exists_phiB (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m)
    {θ : ↥(NN G L) →* Perm (Fin (m + 6))}
    (hθ : ∀ (x : ↥(NN G L)) a,
      (x : GLV V) * jL ψ a * (x : GLV V)⁻¹ = jL ψ (CaseIAut.conjA (θ x) a))
    (hθ1 : ∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x)
    {hh : GLV V} (hhG : hh ∈ G) (hht : hh * z * hh⁻¹ = tt ψ) :
    ∃ φB : ↥(altOn (DeltaB m)) →* Perm (Fin (m + 6)),
      (∀ σ, φB σ = θ ⟨hh⁻¹ * jB ψ σ * hh, h.conjB_mem_N hhG hht σ⟩) ∧
      Function.Injective φB ∧
      ∀ σ : ↥(altOn (DeltaB m)), (σ : Perm (Fin (m + 6))).IsThreeCycle → (φB σ).IsThreeCycle := by
  classical
  let f : ↥(altOn (DeltaB m)) →* ↥(NN G L) :=
    { toFun := fun σ => ⟨hh⁻¹ * jB ψ σ * hh, h.conjB_mem_N hhG hht σ⟩
      map_one' := Subtype.ext (by
        show hh⁻¹ * jB ψ 1 * hh = 1
        rw [map_one]; group)
      map_mul' := fun a b => Subtype.ext (by
        show hh⁻¹ * jB ψ (a * b) * hh = (hh⁻¹ * jB ψ a * hh) * (hh⁻¹ * jB ψ b * hh)
        rw [map_mul]; group) }
  set φB := θ.comp f with hφB
  have hφB' : ∀ σ, φB σ = θ ⟨hh⁻¹ * jB ψ σ * hh, h.conjB_mem_N hhG hht σ⟩ := fun _ => rfl
  have hinj : Function.Injective φB := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    by_contra hσ1
    set M : Subgroup (Perm (Fin (m + 6))) := φB.ker.map (altOn (DeltaB m)).subtype with hM
    have hMmem : ∀ τ ∈ M, ∃ hτ : τ ∈ altOn (DeltaB m),
        hh⁻¹ * jB ψ ⟨τ, hτ⟩ * hh ∈ KK G L := by
      rintro _ ⟨τ, hτ, rfl⟩
      exact ⟨τ.2, h.mem_K_of_theta hθ1 (f τ) hτ⟩
    have hsupp : ∀ τ ∈ M, ∀ x, x ∉ (DeltaB m).toFinset → τ x = x := by
      intro τ hτ x hx
      obtain ⟨hτA, -⟩ := hMmem τ hτ
      exact (mem_altOn_iff.1 hτA).2 x (by simpa using hx)
    have hconj : ∀ τ ∈ M, ∀ a ∈ (DeltaB m).toFinset, ∀ b ∈ (DeltaB m).toFinset,
        swap a b * τ * swap a b ∈ M := by
      intro τ hτ a ha b hb
      obtain ⟨hτA, hτK⟩ := hMmem τ hτ
      have ha' : a ∈ DeltaB m := by simpa using ha
      have hb' : b ∈ DeltaB m := by simpa using hb
      have hmem : swap a b * τ * swap a b ∈ altOn (DeltaB m) := by
        refine mem_altOn_iff.2 ⟨?_, fun x hx => ?_⟩
        · rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul,
            Equiv.Perm.mem_alternatingGroup.1 (mem_altOn_iff.1 hτA).1, mul_one,
            ← map_mul, swap_mul_self, map_one]
        · have hxa : x ≠ a := fun e => hx (e ▸ ha')
          have hxb : x ≠ b := fun e => hx (e ▸ hb')
          rw [Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb,
            (mem_altOn_iff.1 hτA).2 x hx, swap_apply_of_ne_of_ne hxa hxb]
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      show θ (f ⟨_, hmem⟩) = 1
      set g : GLV V := hh⁻¹ * pe ψ (iota2 (m + 6) (swap a b)) * hh with hg
      have hgN : g ∈ NN G L := by
        refine h.centralizer_z_le (G.mul_mem (G.mul_mem (G.inv_mem hhG)
          (h.H₁_le_G (pe_mem _))) hhG) ?_
        have hz : z = hh⁻¹ * tt ψ * hh := by rw [← hht]; group
        have hc : pe ψ (iota2 (m + 6) (swap a b)) * tt ψ =
            tt ψ * pe ψ (iota2 (m + 6) (swap a b)) := by
          rw [tt, ← map_mul, ← map_mul, ← map_mul, ← map_mul, comm_dt_swap ha' hb']
        rw [hg, hz]
        calc hh⁻¹ * pe ψ (iota2 (m + 6) (swap a b)) * hh * (hh⁻¹ * tt ψ * hh)
            = hh⁻¹ * (pe ψ (iota2 (m + 6) (swap a b)) * tt ψ) * hh := by group
          _ = hh⁻¹ * (tt ψ * pe ψ (iota2 (m + 6) (swap a b))) * hh := by rw [hc]
          _ = hh⁻¹ * tt ψ * hh * (hh⁻¹ * pe ψ (iota2 (m + 6) (swap a b)) * hh) := by group
      have hPP : pe ψ (iota2 (m + 6) (swap a b)) * pe ψ (iota2 (m + 6) (swap a b)) = 1 := by
        rw [← map_mul, ← map_mul, swap_mul_self, map_one, map_one]
      have hPinv : (pe ψ (iota2 (m + 6) (swap a b)))⁻¹ = pe ψ (iota2 (m + 6) (swap a b)) :=
        inv_eq_of_mul_eq_one_right hPP
      have hginv : g⁻¹ = g := by
        rw [hg, mul_inv_rev, mul_inv_rev, inv_inv, hPinv, mul_assoc]
      have heq : hh⁻¹ * jB ψ ⟨_, hmem⟩ * hh = g * (hh⁻¹ * jB ψ ⟨τ, hτA⟩ * hh) * g⁻¹ := by
        rw [hginv, jB_apply, jB_apply, hg]
        show hh⁻¹ * pe ψ (iota2 (m + 6) (swap a b * τ * swap a b)) * hh = _
        rw [map_mul, map_mul, map_mul, map_mul]
        group
      have hK : hh⁻¹ * jB ψ ⟨_, hmem⟩ * hh ∈ KK G L := by
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.1 (h.N_le_normalizer_K hgN) _).1 hτK
      exact h.theta_of_mem_K hθ1 _ hK
    have hσM : (σ : Perm (Fin (m + 6))) ∈ M := ⟨σ, hσ, rfl⟩
    have hσ1' : (σ : Perm (Fin (m + 6))) ≠ 1 := fun e => hσ1 (Subtype.ext e)
    have hcard : 4 ≤ (DeltaB m).toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card', ncard_DeltaB]; omega
    obtain ⟨u, huM, huu, hu1⟩ := CaseIS8Perm.exists_involution_of_conj_closed _ hcard M hsupp hconj
      hσM hσ1'
    obtain ⟨huA, huK⟩ := hMmem u huM
    set u' := hh⁻¹ * jB ψ ⟨u, huA⟩ * hh with hu'
    have hu'u' : u' * u' = 1 := by
      rw [hu']
      have : jB ψ ⟨u, huA⟩ * jB ψ ⟨u, huA⟩ = 1 := by
        rw [← map_mul]
        have : (⟨u, huA⟩ : ↥(altOn (DeltaB m))) * ⟨u, huA⟩ = 1 := Subtype.ext huu
        rw [this, map_one]
      calc hh⁻¹ * jB ψ ⟨u, huA⟩ * hh * (hh⁻¹ * jB ψ ⟨u, huA⟩ * hh)
          = hh⁻¹ * (jB ψ ⟨u, huA⟩ * jB ψ ⟨u, huA⟩) * hh := by group
        _ = 1 := by rw [this]; group
    have hu'1 : u' ≠ 1 := by
      intro e
      apply hu1
      have h1 : jB ψ ⟨u, huA⟩ = 1 := by
        have : jB ψ ⟨u, huA⟩ = hh * u' * hh⁻¹ := by rw [hu']; group
        rw [this, e]; group
      rw [jB_apply] at h1
      exact iota2_injective _ (pe_injective (h1.trans (map_one _).symm) |>.trans
        (map_one _).symm)
    have hu'z : u' ≠ z := by
      intro e
      have h1 : jB ψ ⟨u, huA⟩ = tt ψ := by
        have : jB ψ ⟨u, huA⟩ = hh * u' * hh⁻¹ := by rw [hu']; group
        rw [this, e, hht]
      rw [jB_apply, tt] at h1
      have h2 := iota2_injective _ (pe_injective h1)
      have h3 := congrArg (fun π : Perm (Fin (m + 6)) => π 0) h2
      simp only at h3
      rw [(mem_altOn_iff.1 huA).2 0 (by
        show ¬ (4 ≤ ((0 : Fin (m + 6)) : ℕ))
        show ¬ (4 ≤ 0); omega), Perm.mul_apply, swap_apply_of_ne_of_ne ne02' ne03',
        swap_apply_left] at h3
      exact ne01' h3
    have hu'2 : orderOf u' = 2 := orderOf_eq_prime (by rw [sq]; exact hu'u') hu'1
    have hcomm : u' * z = z * u' := h.conjB_comm_z hht ⟨u, huA⟩
    have := CFSG.GH74.Uniqueness.SU.SU10.two_le_pRank_of_commuting_involutions huK h.z_mem_K
      hu'2 h.std.orderOf_s hu'z hcomm
    rw [h.rank] at this
    omega
  refine ⟨φB, hφB', hinj, fun σ hσ3 => ?_⟩
  by_contra hn
  have hord : orderOf (φB σ) = 3 := by
    rw [orderOf_injective φB hinj, ← Subgroup.orderOf_coe, hσ3.orderOf]
  have h4 := h.four_le_finrank_N hθ ⟨_, h.conjB_mem_N hhG hht σ⟩ (by rw [← hφB']; exact hord)
    (by rw [← hφB']; exact hn)
  have h2 := h.finrank_jL_le_two (a := ⟨σ, altOn_le_alt σ.2⟩) hσ3
  have e := finrank_conj hh⁻¹ (jL ψ ⟨σ, altOn_le_alt σ.2⟩)
  rw [inv_inv] at e
  have h4' : 4 ≤ Module.finrank (ZMod 2)
      ↥(commSpace (Subgroup.zpowers (hh⁻¹ * jL ψ ⟨σ, altOn_le_alt σ.2⟩ * hh)) ⊤) := h4
  rw [e] at h4'
  omega

theorem ncard_compl_le_four {m : ℕ} (hm : 1 ≤ m)
    (φB : ↥(altOn (DeltaB m)) →* Perm (Fin (m + 6))) (hinj : Function.Injective φB) :
    ({p | ∃ σ : ↥(altOn (DeltaB m)), (σ : Perm (Fin (m + 6))).IsThreeCycle ∧ φB σ p ≠ p} :
      Set (Fin (m + 6)))ᶜ.ncard ≤ 4 := by
  classical
  set D : Set (Fin (m + 6)) :=
    {p | ∃ σ : ↥(altOn (DeltaB m)), (σ : Perm (Fin (m + 6))).IsThreeCycle ∧ φB σ p ≠ p} with hD
  have hcl : Subgroup.closure {σ | σ ∈ altOn (DeltaB m) ∧ σ.IsThreeCycle} ≤ altOn (DeltaB m) :=
    (Subgroup.closure_le _).2 fun σ hσ => hσ.1
  have hfix0 : ∀ τ (hτ : τ ∈ Subgroup.closure {σ | σ ∈ altOn (DeltaB m) ∧ σ.IsThreeCycle}),
      ∀ p ∉ D, φB ⟨τ, hcl hτ⟩ p = p := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      intro p hp
      by_contra hne
      exact hp ⟨⟨x, hx.1⟩, hx.2, hne⟩
    | one =>
      intro p _
      rw [show (⟨1, hcl (Subgroup.one_mem _)⟩ : ↥(altOn (DeltaB m))) = 1 from rfl, map_one]
      rfl
    | mul x y hx hy ihx ihy =>
      intro p hp
      rw [show (⟨x * y, hcl (Subgroup.mul_mem _ hx hy)⟩ : ↥(altOn (DeltaB m))) =
        ⟨x, hcl hx⟩ * ⟨y, hcl hy⟩ from rfl, map_mul, Perm.mul_apply, ihy p hp, ihx p hp]
    | inv x hx ihx =>
      intro p hp
      rw [show (⟨x⁻¹, hcl (Subgroup.inv_mem _ hx)⟩ : ↥(altOn (DeltaB m))) =
        (⟨x, hcl hx⟩)⁻¹ from rfl, map_inv, Perm.inv_eq_iff_eq]
      exact (ihx p hp).symm
  have hfix : ∀ σ : ↥(altOn (DeltaB m)), ∀ p ∉ D, φB σ p = p := fun σ p hp =>
    hfix0 σ (CaseIS8Perm.altOn_le_closure_threeCycles _ σ.2) p hp
  have hpres : ∀ σ : ↥(altOn (DeltaB m)), ∀ x, φB σ x ∈ D ↔ x ∈ D := by
    intro σ x
    constructor
    · intro h
      by_contra hx
      rw [hfix σ x hx] at h
      exact hx h
    · intro hx
      by_contra h
      exact h (by rw [(φB σ).injective (hfix σ _ h)]; exact hx)
  have hemb : Function.Injective
      (fun σ : ↥(altOn (DeltaB m)) => (φB σ).subtypePerm (hpres σ)) := by
    intro σ₁ σ₂ he
    apply hinj
    refine Perm.ext fun x => ?_
    by_cases hx : x ∈ D
    · have := congrArg (fun π : Perm {x // x ∈ D} => (π ⟨x, hx⟩ : Fin (m + 6))) he
      simpa using this
    · rw [hfix σ₁ x hx, hfix σ₂ x hx]
  have hcard := Nat.card_le_card_of_injective _ hemb
  rw [Nat.card_eq_fintype_card (α := Perm {x // x ∈ D}), Fintype.card_perm,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hcard
  have h2 := two_mul_card_altOn (DeltaB m) (by rw [Nat.card_coe_set_eq, ncard_DeltaB]; omega)
  rw [Nat.card_coe_set_eq, ncard_DeltaB] at h2
  have hDm : m + 2 ≤ D.ncard := by
    by_contra hlt
    push Not at hlt
    have h4 := Nat.factorial_le (show D.ncard ≤ m + 1 by omega)
    have h5 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ _
    have h6 := Nat.factorial_pos (m + 1)
    nlinarith
  have hsum := Set.ncard_add_ncard_compl D
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  omega

variable {S : Subgroup (GLV V)}

theorem SBad.false_of_ge (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (hm : 2 ≤ m) : False := by
  classical
  obtain ⟨θ, hθ, hθ1, hθ3⟩ := h.exists_thetaL
  obtain ⟨hh, hhG, hht⟩ := hS.exists_hh h
  obtain ⟨φB, hφB, hinj, h3⟩ := h.exists_phiB hm hθ hθ1 hhG hht
  obtain ⟨φ, hφ, hφdef⟩ := hS.embed h hhG hht θ hθ1
  obtain ⟨hQ2, hz2, huniq⟩ := hS.image_uniq h hφ
  set D : Set (Fin (m + 6)) :=
    {p | ∃ σ : ↥(altOn (DeltaB m)), (σ : Perm (Fin (m + 6))).IsThreeCycle ∧ φB σ p ≠ p} with hD
  have hD4 : Dᶜ.ncard ≤ 4 := ncard_compl_le_four (by omega) φB hinj
  have hcommB : ∀ (s : ↥S) σ, φ s * φB σ = φB σ * φ s := by
    intro s σ
    rw [hφdef, hφB, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show hh⁻¹ * s * hh * (hh⁻¹ * jB ψ σ * hh) = hh⁻¹ * jB ψ σ * hh * (hh⁻¹ * s * hh)
    have hc : (s : GLV V) * jB ψ σ = jB ψ σ * s :=
      (Subgroup.mem_centralizer_iff.1 (hS.le s.2).2 _ (h.jB_mem_L σ)).symm
    calc hh⁻¹ * s * hh * (hh⁻¹ * jB ψ σ * hh) = hh⁻¹ * ((s : GLV V) * jB ψ σ) * hh := by group
      _ = hh⁻¹ * (jB ψ σ * s) * hh := by rw [hc]
      _ = hh⁻¹ * jB ψ σ * hh * (hh⁻¹ * s * hh) := by group
  have hfixD : ∀ (s : ↥S), ∀ p ∈ D, φ s p = p := by
    intro s p hp
    obtain ⟨σ, hσ3, hσp⟩ := hp
    obtain ⟨k, hk⟩ := hS.isP s
    have hk' : φ s ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    exact fixes_support_of_commute_isThreeCycle (h3 σ hσ3) (hcommB s σ) hk'
      (Perm.mem_support.2 hσp)
  obtain ⟨p₀, hp₀⟩ := exists_regular_of_unique_involution hQ2 hz2 huniq
  have hp₀D : p₀ ∉ D := by
    intro hp
    have hall : ∀ s : ↥S, s = 1 := fun s =>
      hφ (by rw [map_one]; exact hp₀ _ ⟨s, rfl⟩ (hfixD s p₀ hp))
    have h1 : Nat.card S ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => by rw [hall a, hall b]⟩
    have := hS.four
    omega
  have hcardS : Nat.card S ≤ 4 := by
    have hmapsto : ∀ s : ↥S, φ s p₀ ∈ Dᶜ := by
      intro s hs
      apply hp₀D
      have h1 := hfixD s _ hs
      rw [(φ s).injective h1] at hs
      exact hs
    have hinj' : Function.Injective (fun s : ↥S => (⟨φ s p₀, hmapsto s⟩ : ↥Dᶜ)) := by
      intro s₁ s₂ he
      have he' : φ s₁ p₀ = φ s₂ p₀ := congrArg Subtype.val he
      have h1 : φ (s₂⁻¹ * s₁) p₀ = p₀ := by
        rw [map_mul, map_inv, Perm.mul_apply, he', perm_inv_apply]
      have h2 := hp₀ _ ⟨_, rfl⟩ h1
      have h3 : s₂⁻¹ * s₁ = 1 := hφ (h2.trans (map_one φ).symm)
      exact (inv_mul_eq_one.1 h3).symm
    have := Nat.card_le_card_of_injective _ hinj'
    rw [Nat.card_coe_set_eq] at this
    omega
  have h4 : Nat.card S = 4 := le_antisymm hcardS hS.four
  obtain ⟨s, hsS, hs4, hss, hgen⟩ := hS.exists_gen h h4
  have hsign : sign (φ ⟨s, hsS⟩) = -1 := by
    apply sign_eq_neg_one_of_orderOf_eq_four
    · rw [orderOf_injective φ hφ, Subgroup.orderOf_mk, hs4]
    · have hsub : (φ ⟨s, hsS⟩).support ⊆ Dᶜ.toFinset := by
        intro x hx
        rw [Set.mem_toFinset]
        intro hxD
        exact (Perm.mem_support.1 hx) (hfixD _ x hxD)
      calc (φ ⟨s, hsS⟩).support.card ≤ Dᶜ.toFinset.card := Finset.card_le_card hsub
        _ = Dᶜ.ncard := (Set.ncard_eq_toFinset_card' _).symm
        _ ≤ 4 := hD4
  obtain ⟨c, hcK, hct, hcomm⟩ := hS.exists_comm_conj h h4 hθ hθ1 hθ3 hhG hht
  have h'G : hh * c ∈ G := G.mul_mem hhG hcK.1
  have hxN := hS.conj_mem_N h h'G hct hsS
  have hs4' : s ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hs4]; exact pow_orderOf_eq_one s
  have hsg := hS.sign_eq_one h h4 hθ1 hθ3 ⟨_, hxN⟩ (fun s' hs' => hcomm s hsS s' hs') (k := 2) (by
    show ((hh * c)⁻¹ * s * (hh * c)) ^ (2 ^ 2) = 1
    have e := conj_pow (a := (hh * c)⁻¹) (b := s) (i := 2 ^ 2)
    rw [inv_inv] at e
    rw [e, hs4', mul_one, inv_mul_cancel])
  have hcN : c ∈ NN G L := h.K_le_N hcK
  have heq : θ ⟨_, hxN⟩ = φ ⟨s, hsS⟩ := by
    rw [hφdef]
    have e : (⟨(hh * c)⁻¹ * s * (hh * c), hxN⟩ : ↥(NN G L)) =
        ⟨c, hcN⟩⁻¹ * ⟨hh⁻¹ * s * hh, hS.conj_mem_N h hhG hht hsS⟩ * ⟨c, hcN⟩ :=
      Subtype.ext (by
        show (hh * c)⁻¹ * s * (hh * c) = c⁻¹ * (hh⁻¹ * s * hh) * c
        group)
    rw [e, map_mul, map_mul, map_inv, h.theta_of_mem_K hθ1 ⟨c, hcN⟩ hcK, inv_one, one_mul, mul_one]
  rw [heq, hsign] at hsg
  exact absurd hsg (by decide)

theorem Hyp.smallK_of_ge (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) :
    ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2 := by
  intro Q hQK hQ
  by_contra hc
  push Not at hc
  obtain ⟨S, hS⟩ := h.exists_sBad ⟨Q, hQK, hQ, hc⟩
  exact hS.false_of_ge h hm

end CaseIAux

end CFSG.CGT.Foote82
