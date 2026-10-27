module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem isPGroup_of_forall_prime_orderOf {A : Type*} [Group A] [Finite A]
    (h : ∀ a : A, ∀ ℓ : ℕ, ℓ.Prime → orderOf a = ℓ → ℓ = p) : IsPGroup p A := by
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdvd
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' d hdvd
  exact h a d hd ha

section AutQuotient

variable {G : Type*} [Group G]

@[expose] def autQuotient (N : Subgroup G) [hN : N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun α := QuotientGroup.congr N N α (characteristic_iff_map_eq.1 hN α)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem autQuotient_mk (N : Subgroup G) [N.Characteristic] (α : MulAut G) (x : G) :
    autQuotient N α (x : G ⧸ N) = (α x : G ⧸ N) :=
  rfl

theorem mem_ker_autQuotient (N : Subgroup G) [N.Characteristic] {α : MulAut G} :
    α ∈ (autQuotient N).ker ↔ ∀ x : G, x⁻¹ * α x ∈ N := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    have h1 := congrArg (fun β : MulAut (G ⧸ N) => β (x : G ⧸ N)) h
    simp only [autQuotient_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [autQuotient_mk, MulAut.one_apply, QuotientGroup.eq]
    have := inv_mem (h x)
    simpa using this

@[expose] noncomputable def frattiniAction (D : Subgroup G) [D.Characteristic] :
    MulAut G →* MulAut (D ⧸ frattini D) :=
  (autQuotient (frattini D)).comp (MulAut.characteristic D)

theorem frattiniAction_mk (D : Subgroup G) [D.Characteristic] (α : MulAut G) (d : D) :
    frattiniAction D α (d : D ⧸ frattini D) =
      ((⟨α d, (MulAut.characteristic D α d).2⟩ : D) : D ⧸ frattini D) :=
  rfl

theorem mem_ker_frattiniAction (D : Subgroup G) [D.Characteristic] {α : MulAut G} :
    α ∈ (frattiniAction D).ker ↔ ∀ d : D, d⁻¹ * MulAut.characteristic D α d ∈ frattini D := by
  rw [frattiniAction, ← MonoidHom.comap_ker, Subgroup.mem_comap, mem_ker_autQuotient]

end AutQuotient

variable {P : Type*} [Group P] [Finite P]

theorem isPGroup_ker_autQuotient_frattini (hP : IsPGroup p P) :
    IsPGroup p (autQuotient (frattini P)).ker := by
  classical
  set K := (autQuotient (frattini P)).ker with hKdef
  have hKfix : ∀ a ∈ K, ∀ x : P, ((a x : P) : P ⧸ frattini P) = x := fun a ha x =>
    (QuotientGroup.eq.2 ((mem_ker_autQuotient _).1 ha x)).symm
  let T := {s : P ⧸ frattini P → P // ∀ y, ((s y : P) : P ⧸ frattini P) = y}
  let act : MulAction K T :=
    { smul := fun a s => ⟨fun y => (a : MulAut P) (s.1 y), fun y => by rw [hKfix a a.2, s.2 y]⟩
      one_smul := fun s => rfl
      mul_smul := fun a b s => rfl }
  have hTcard : ∃ N : ℕ, Nat.card T = p ^ N := by
    obtain ⟨j, hj⟩ := (hP.to_subgroup (frattini P)).exists_card_eq
    let := Fintype.ofFinite (P ⧸ frattini P)
    refine ⟨j * Fintype.card (P ⧸ frattini P), ?_⟩
    have e : T ≃ ∀ y : P ⧸ frattini P, {x : P // ((x : P) : P ⧸ frattini P) = y} :=
      @Equiv.subtypePiEquivPi (P ⧸ frattini P) (fun _ => P)
        (fun y x => ((x : P) : P ⧸ frattini P) = y)
    rw [Nat.card_congr e, Nat.card_pi]
    have hfib : ∀ y : P ⧸ frattini P,
        Nat.card {x : P // ((x : P) : P ⧸ frattini P) = y} = p ^ j := by
      intro y
      have h := QuotientGroup.card_preimage_mk (frattini P) {y}
      rw [show Nat.card ({y} : Set (P ⧸ frattini P)) = 1 from Nat.card_unique, mul_one,
        hj] at h
      exact h
    simp only [hfib, Finset.prod_const, Finset.card_univ, ← pow_mul]
  apply isPGroup_of_forall_prime_orderOf
  intro a ℓ hℓ hord
  by_contra hne
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hZ : IsPGroup ℓ (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hmod := hZ.card_modEq_card_fixedPoints T
  obtain ⟨N, hN⟩ := hTcard
  have hnd : ¬ ℓ ∣ Nat.card T := by
    rw [hN]
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp.out).1 (hℓ.dvd_of_dvd_pow h))
  have hfixne : Nat.card (MulAction.fixedPoints (zpowers a) T) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hnd (Nat.modEq_zero_iff_dvd.1 hmod)
  obtain ⟨s, hs⟩ := (Nat.card_ne_zero.1 hfixne).1
  have hsa : ∀ y, (a : MulAut P) (s.1 y) = s.1 y := fun y =>
    congrArg (fun t : T => t.1 y) (hs ⟨a, mem_zpowers a⟩)
  have hgen : closure (Set.range s.1) = ⊤ := by
    apply frattini_nongenerating
    rw [eq_top_iff]
    intro x _
    have hx : (s.1 (x : P ⧸ frattini P))⁻¹ * x ∈ frattini P :=
      QuotientGroup.eq.1 (s.2 (x : P ⧸ frattini P))
    have e : x = s.1 (x : P ⧸ frattini P) * ((s.1 (x : P ⧸ frattini P))⁻¹ * x) := by group
    rw [e]
    exact mul_mem_sup (subset_closure ⟨_, rfl⟩) hx
  have ha1 : (a : MulAut P) = 1 := by
    ext x
    have hx : x ∈ closure (Set.range s.1) := hgen ▸ mem_top x
    rw [MulAut.one_apply]
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact hsa y
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, hx]
  have : a = 1 := Subtype.ext ha1
  rw [this, orderOf_one] at hord
  exact hℓ.one_lt.ne hord

end CFSG.SectionRank.Ccomm
