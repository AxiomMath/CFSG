module

public import CFSG.LocalAnalysis.ComponentInitial.GroupBinaryPolar
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionAlternating
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverComplement
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverPrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open Matrix
open scoped commutatorElement

section Polar

variable {r : ℕ}

@[expose] def polarMat (w w' : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    Matrix (Fin r) (Fin r) (ZMod 2) :=
  vecMulVec w.1 w'.2 + vecMulVec w'.2 w.1 + vecMulVec w.2 w'.1 + vecMulVec w'.1 w.2

theorem zmod_two_mul_add_mul (a b : ZMod 2) : a * b + b * a = 0 := by
  rw [mul_comm b a, ← two_mul]
  exact mul_eq_zero_of_left (by decide) _

theorem polarMat_mem (w w' : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    polarMat w w' ∈ binaryAltMatrices r := by
  refine ⟨?_, fun i => ?_⟩
  · simp only [polarMat, transpose_add, transpose_vecMulVec]
    abel
  · simp only [polarMat, Matrix.add_apply, vecMulVec_apply]
    rw [zmod_two_mul_add_mul, zero_add, zmod_two_mul_add_mul]

@[expose] def polarAlt (w w' : (Fin r → ZMod 2) × (Fin r → ZMod 2)) : binaryAltMatrices r :=
  ⟨polarMat w w', polarMat_mem w w'⟩

theorem coe_polarAlt (w w' : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    (polarAlt w w' : Matrix (Fin r) (Fin r) (ZMod 2)) = polarMat w w' :=
  rfl

theorem polarAlt_zero_left (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) : polarAlt 0 w = 0 := by
  apply Subtype.ext
  simp [coe_polarAlt, polarMat]

theorem zmod_two_prod_neg (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) : -w = w :=
  Prod.ext (funext fun _ => ZMod.neg_eq_self_mod_two _) (funext fun _ => ZMod.neg_eq_self_mod_two _)

theorem polarAlt_neg_neg (w w' : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    polarAlt (-w) (-w') = polarAlt w w' := by
  rw [zmod_two_prod_neg, zmod_two_prod_neg]

theorem polarAlt_single (i j : Fin r) :
    ((polarAlt (Pi.single i 1, 0) (0, Pi.single j 1) : binaryAltMatrices r) :
      Matrix (Fin r) (Fin r) (ZMod 2)) = MatrixExtension.binaryOff i j := by
  rw [coe_polarAlt, polarMat, MatrixExtension.binaryOff_eq_vecMulVec]
  simp

@[expose] def omegaMul (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    (Fin r → ZMod 2) × (Fin r → ZMod 2) :=
  (w.2, w.1 + w.2)

theorem add_omegaMul_add_omegaMul (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    w + omegaMul w + omegaMul (omegaMul w) = 0 := by
  have h2 : ∀ v : Fin r → ZMod 2, v + v = 0 := fun v => funext fun i => by
    rw [Pi.add_apply, ← two_mul]
    exact mul_eq_zero_of_left (by decide) _
  refine Prod.ext ?_ ?_
  · change w.1 + w.2 + (w.1 + w.2) = 0
    exact h2 _
  · change w.2 + (w.1 + w.2) + (w.2 + (w.1 + w.2)) = 0
    exact h2 _

end Polar

section Generic

theorem mem_commutator_of_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {v : G}
    (hv : v ∈ ⁅H, H⁆) : ∃ hvH : v ∈ H, (⟨v, hvH⟩ : H) ∈ commutator H := by
  have heq : ⁅H, H⁆ = (commutator H).map H.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [heq] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨y.2, hy⟩

theorem coe_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {y : H}
    (hy : y ∈ commutator H) : (y : G) ∈ ⁅H, H⁆ := by
  have heq : ⁅H, H⁆ = (commutator H).map H.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [heq]
  exact ⟨y, hy, rfl⟩

end Generic

structure Shape (X : Type*) [Group X] (r : ℕ) where
  ρ : GL (Fin r) (ZMod 2) →* X
  ρ_injective : Function.Injective ρ
  N : Subgroup X
  π : X → (Fin r → ZMod 2) × (Fin r → ZMod 2)
  π_mul : ∀ m ∈ N, ∀ n ∈ N, π (m * n) = π m + π n
  exists_π : ∀ w, ∃ n ∈ N, π n = w
  τ : Multiplicative (binaryAltMatrices r) →* X
  τ_injective : Function.Injective τ
  τ_mem : ∀ B, τ B ∈ N
  π_eq_zero_iff : ∀ n ∈ N, π n = 0 ↔ n ∈ τ.range
  commutator_eq : ∀ m ∈ N, ∀ n ∈ N, ⁅m, n⁆ = τ (Multiplicative.ofAdd (polarAlt (π m) (π n)))
  ρ_conj_mem : ∀ g, ∀ n ∈ N, ρ g * n * (ρ g)⁻¹ ∈ N
  π_ρ_conj : ∀ g, ∀ n ∈ N, π (ρ g * n * (ρ g)⁻¹) =
    ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π n).1,
      (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (π n).2)
  h : X
  h_conj_mem : ∀ n ∈ N, h * n * h⁻¹ ∈ N
  π_h_conj : ∀ n ∈ N, π (h * n * h⁻¹) = omegaMul (π n)
  h_τ : ∀ B, h * τ B = τ B * h
  h_ρ : ∀ g, h * ρ g = ρ g * h
  sylow : ∃ S : Sylow 2 X, ∀ s ∈ (S : Subgroup X),
    ∃ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL),
      ∃ b ∈ N, s = a * b
  inf_eq_bot : (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL) ⊓ N = ⊥

namespace Shape

variable {X : Type*} [Group X] {r : ℕ} (S : Shape X r)

theorem π_one : S.π 1 = 0 := by
  have h := S.π_mul 1 S.N.one_mem 1 S.N.one_mem
  rw [one_mul] at h
  exact (add_eq_left.mp h.symm)

theorem π_inv {n : X} (hn : n ∈ S.N) : S.π n⁻¹ = -S.π n := by
  have h := S.π_mul n hn n⁻¹ (S.N.inv_mem hn)
  rw [mul_inv_cancel, S.π_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem π_τ (B : Multiplicative (binaryAltMatrices r)) : S.π (S.τ B) = 0 :=
  (S.π_eq_zero_iff _ (S.τ_mem B)).mpr ⟨B, rfl⟩

theorem τ_range_le : S.τ.range ≤ S.N := by
  rintro _ ⟨B, rfl⟩
  exact S.τ_mem B

theorem commutatorElement_τ (B : Multiplicative (binaryAltMatrices r)) {n : X} (hn : n ∈ S.N) :
    ⁅S.τ B, n⁆ = 1 := by
  rw [S.commutator_eq _ (S.τ_mem B) _ hn, S.π_τ, polarAlt_zero_left, ofAdd_zero, map_one]

theorem τ_mul_comm (B : Multiplicative (binaryAltMatrices r)) {n : X} (hn : n ∈ S.N) :
    S.τ B * n = n * S.τ B :=
  commutatorElement_eq_one_iff_mul_comm.mp (S.commutatorElement_τ B hn)

theorem commutatorElement_mem_τ_range {m n : X} (hm : m ∈ S.N) (hn : n ∈ S.N) :
    ⁅m, n⁆ ∈ S.τ.range :=
  ⟨_, (S.commutator_eq m hm n hn).symm⟩

theorem norm_mem_τ_range {m : X} (hm : m ∈ S.N) :
    m * (S.h * m * S.h⁻¹) * (S.h * (S.h * m * S.h⁻¹) * S.h⁻¹) ∈ S.τ.range := by
  have hm1 := S.h_conj_mem m hm
  have hm2 := S.h_conj_mem _ hm1
  refine (S.π_eq_zero_iff _ (S.N.mul_mem (S.N.mul_mem hm hm1) hm2)).mp ?_
  rw [S.π_mul _ (S.N.mul_mem hm hm1) _ hm2, S.π_mul _ hm _ hm1, S.π_h_conj _ hm1,
    S.π_h_conj _ hm]
  exact add_omegaMul_add_omegaMul _

variable {E : Type*} [Group E] (θ : E →* X)

@[expose] def preN : Subgroup E :=
  S.N.comap θ

@[expose] def preV : Subgroup E :=
  S.τ.range.comap θ

variable {S θ}

theorem mem_preN {m : E} : m ∈ S.preN θ ↔ θ m ∈ S.N :=
  Iff.rfl

theorem mem_preV {t : E} : t ∈ S.preV θ ↔ θ t ∈ S.τ.range :=
  Iff.rfl

theorem preV_le_preN : S.preV θ ≤ S.preN θ := fun _ ht => S.τ_range_le ht

theorem ker_le_preV : θ.ker ≤ S.preV θ := fun c hc => ⟨1, by rw [map_one]; exact hc.symm⟩

theorem commutatorElement_mem_preV {m n : E} (hm : m ∈ S.preN θ) (hn : n ∈ S.preN θ) :
    ⁅m, n⁆ ∈ S.preV θ := by
  rw [mem_preV, map_commutatorElement]
  exact S.commutatorElement_mem_τ_range hm hn

theorem commutator_le_preV : ⁅S.preN θ, S.preN θ⁆ ≤ S.preV θ := by
  rw [Subgroup.commutator_le]
  intro m hm n hn
  exact commutatorElement_mem_preV hm hn

theorem map_commutatorElement_preV_eq_one {t m : E} (ht : t ∈ S.preV θ) (hm : m ∈ S.preN θ) :
    θ ⁅t, m⁆ = 1 := by
  obtain ⟨B, hB⟩ := ht
  rw [map_commutatorElement, ← hB]
  exact S.commutatorElement_τ B hm

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
include hθ

theorem map_preN : (S.preN θ).map θ = S.N :=
  Subgroup.map_comap_eq_self_of_surjective hθ _

theorem preV_le_commutator_sup : S.preV θ ≤ ⁅S.preN θ, S.preN θ⁆ ⊔ θ.ker := by
  set Ksub : AddSubgroup (binaryAltMatrices r) :=
    { carrier := {B | ∃ v ∈ ⁅S.preN θ, S.preN θ⁆, θ v = S.τ (Multiplicative.ofAdd B)}
      add_mem' := by
        rintro B B' ⟨v, hv, hvB⟩ ⟨v', hv', hvB'⟩
        exact ⟨v * v', mul_mem hv hv', by rw [map_mul, hvB, hvB', ← map_mul, ofAdd_add]⟩
      zero_mem' := ⟨1, one_mem _, by rw [map_one, ofAdd_zero, map_one]⟩
      neg_mem' := by
        rintro B ⟨v, hv, hvB⟩
        exact ⟨v⁻¹, inv_mem hv, by rw [map_inv, hvB, ← map_inv, ofAdd_neg]⟩ }
  have hsingle : ∀ i j : Fin r, (⟨MatrixExtension.binaryOff i j,
      MatrixExtension.binaryOff_mem_binaryAltMatrices i j⟩ : binaryAltMatrices r) ∈ Ksub := by
    intro i j
    obtain ⟨m, hm, hmw⟩ := S.exists_π (Pi.single i 1, 0)
    obtain ⟨n, hn, hnw⟩ := S.exists_π (0, Pi.single j 1)
    obtain ⟨m', rfl⟩ := hθ m
    obtain ⟨n', rfl⟩ := hθ n
    refine ⟨⁅m', n'⁆, Subgroup.commutator_mem_commutator hm hn, ?_⟩
    rw [map_commutatorElement, S.commutator_eq _ hm _ hn, hmw, hnw]
    congr 2
    exact Subtype.ext (polarAlt_single i j)
  have htop : ∀ B : binaryAltMatrices r, B ∈ Ksub := by
    intro B
    rw [MatrixExtension.binaryAlt_eq_sum B]
    exact Finset.sum_induction _ (· ∈ Ksub) (fun _ _ ha hb => Ksub.add_mem ha hb) Ksub.zero_mem
      fun p _ => Ksub.nsmul_mem (hsingle p.1 p.2) _
  intro t ht
  obtain ⟨B, hB⟩ := ht
  obtain ⟨v, hv, hvB⟩ := htop B.toAdd
  rw [ofAdd_toAdd] at hvB
  have hk : v⁻¹ * t ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvB, hB, inv_mul_cancel]
  have := Subgroup.mul_mem_sup hv hk
  rwa [mul_inv_cancel_left] at this

omit hθ in
include hC in
theorem mul_comm_of_mem_preV (hθ : Function.Surjective θ) (hsq : ∀ c, θ c = 1 → c ^ 2 = 1)
    {t m : E} (ht : t ∈ S.preV θ) (hm : m ∈ S.preN θ) : t * m = m * t := by
  have hcen : ∀ n ∈ S.preN θ, ⁅t, n⁆ ∈ Subgroup.center E := fun n hn =>
    hC (map_commutatorElement_preV_eq_one ht hn)
  have hMM : ⁅S.preN θ, S.preN θ⁆ ≤ Subgroup.centralizer {t} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hta : t * a * t⁻¹ = ⁅t, a⁆ * a := by rw [commutatorElement_def]; group
    have htb : t * b * t⁻¹ = ⁅t, b⁆ * b := by rw [commutatorElement_def]; group
    have h := LinearCover.conj_commutatorElement_eq t a b
    rw [hta, htb, UnitaryOddCover.commutatorElement_central_mul (hcen a ha) (hcen b hb)] at h
    nth_rewrite 1 [← h]
    group
  have hTc : ∀ t' ∈ S.preV θ, t' * t = t * t' := fun t' ht' =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (sup_le hMM (hC.trans (Subgroup.center_le_centralizer _))
        (preV_le_commutator_sup hθ ht'))
  obtain ⟨hh, hhh⟩ := hθ S.h
  have hconjM : ∀ n ∈ S.preN θ, hh * n * hh⁻¹ ∈ S.preN θ := fun n hn => by
    rw [mem_preN, map_mul, map_mul, map_inv, hhh]
    exact S.h_conj_mem _ hn
  have htc : ⁅hh⁻¹, t⁆ ∈ Subgroup.center E := hC (by
    obtain ⟨B, hB⟩ := ht
    rw [MonoidHom.mem_ker, map_commutatorElement, map_inv, hhh, ← hB, commutatorElement_def,
      inv_inv, mul_assoc S.h⁻¹, ← S.h_τ B, inv_mul_cancel_left, mul_inv_cancel])
  have hinv : ∀ n ∈ S.preN θ, ⁅t, hh * n * hh⁻¹⁆ = ⁅t, n⁆ := by
    intro n hn
    have h1 : hh⁻¹ * t * hh = ⁅hh⁻¹, t⁆ * t := by rw [commutatorElement_def]; group
    have h2 := LinearCover.conj_commutatorElement_eq hh (hh⁻¹ * t * hh) n
    rw [show hh * (hh⁻¹ * t * hh) * hh⁻¹ = t by group, h1,
      show ⁅⁅hh⁻¹, t⁆ * t, n⁆ = ⁅⁅hh⁻¹, t⁆ * t, 1 * n⁆ by rw [one_mul],
      UnitaryOddCover.commutatorElement_central_mul htc (Subgroup.one_mem _),
      UnitaryOddCover.conj_central (hcen n hn)] at h2
    exact h2.symm
  have hmul : ∀ a ∈ S.preN θ, ∀ b ∈ S.preN θ, ⁅t, a * b⁆ = ⁅t, a⁆ * ⁅t, b⁆ := by
    intro a ha b hb
    rw [LinearCover.commutatorElement_mul_right_eq, UnitaryOddCover.conj_central (hcen b hb)]
  have hm1 := hconjM m hm
  have hm2 := hconjM _ hm1
  have hy : m * (hh * m * hh⁻¹) * (hh * (hh * m * hh⁻¹) * hh⁻¹) ∈ S.preV θ := by
    rw [mem_preV]
    have h := S.norm_mem_τ_range hm
    simpa only [map_mul, map_inv, hhh] using h
  have h3 : ⁅t, m⁆ ^ 3 = 1 := by
    have h := commutatorElement_eq_one_iff_mul_comm.mpr (hTc _ hy).symm
    rwa [hmul _ (mul_mem hm hm1) _ hm2, hmul _ hm _ hm1, hinv _ hm1, hinv _ hm, ← pow_three']
      at h
  have h2 : ⁅t, m⁆ ^ 2 = 1 := hsq _ (map_commutatorElement_preV_eq_one ht hm)
  have h1 : ⁅t, m⁆ = 1 := by
    rw [pow_succ, h2, one_mul] at h3
    exact h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

include hC in
theorem commutator_preN_spec (hr : 3 ≤ r) (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) :
    θ.ker ⊓ ⁅S.preN θ, S.preN θ⁆ = ⊥ ∧ ∀ v ∈ ⁅S.preN θ, S.preN θ⁆, v ^ 2 = 1 := by
  set M := S.preN θ with hMdef
  let πM : M →* Multiplicative ((Fin r → ZMod 2) × (Fin r → ZMod 2)) :=
    { toFun := fun m => Multiplicative.ofAdd (S.π (θ m))
      map_one' := by
        change Multiplicative.ofAdd (S.π (θ 1)) = 1
        rw [map_one, S.π_one, ofAdd_zero]
      map_mul' := fun m n => by
        change Multiplicative.ofAdd (S.π (θ ((m : E) * n))) = _
        rw [map_mul, S.π_mul _ m.2 _ n.2, ofAdd_add] }
  have hπM : ∀ m, πM m = Multiplicative.ofAdd (S.π (θ m)) := fun _ => rfl
  have hπMsurj : Function.Surjective πM := by
    intro w
    obtain ⟨n, hn, hnw⟩ := S.exists_π w.toAdd
    obtain ⟨m, rfl⟩ := hθ n
    exact ⟨⟨m, hn⟩, by rw [hπM, hnw, ofAdd_toAdd]⟩
  set T' := (S.preV θ).subgroupOf M with hT'def
  set C' := θ.ker.subgroupOf M with hC'def
  have hπT : πM.ker = T' := by
    ext m
    rw [MonoidHom.mem_ker, hπM, Subgroup.mem_subgroupOf, mem_preV,
      ← S.π_eq_zero_iff _ m.2]
    exact ⟨fun h => by rw [← ofAdd_zero] at h; exact Multiplicative.ofAdd.injective h,
      fun h => by rw [h, ofAdd_zero]⟩
  let ι := MonoidHom.ofInjective S.τ_injective
  let θT : T' →* S.τ.range :=
    (θ.comp (M.subtype.comp T'.subtype)).codRestrict S.τ.range fun t =>
      Subgroup.mem_subgroupOf.mp t.2
  let τM : T' →* Multiplicative (binaryAltMatrices r) := ι.symm.toMonoidHom.comp θT
  have hτM : ∀ t : T', S.τ (τM t) = θ ((t : M) : E) := fun t =>
    congrArg Subtype.val (ι.apply_symm_apply (θT t))
  have hτC : τM.ker = C'.subgroupOf T' := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker,
      ← hτM]
    exact ⟨fun h => by rw [h, map_one], fun h => S.τ_injective (by rw [h, map_one])⟩
  set α : GL (Fin r) (ZMod 2) →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp S.ρ
  have hαM : ∀ g, ∀ x ∈ M, α g x ∈ M := fun g x hx => by
    rw [hMdef, mem_preN, MonoidHom.comp_apply, BinarySymplecticSix.map_liftConj_apply]
    exact S.ρ_conj_mem g _ hx
  set act := BinarySymplecticSix.restrictAct α M hαM
  have hactC : ∀ g, ∀ c ∈ C', act g c = c := fun g c hc => Subtype.ext
    (BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ (Subgroup.mem_subgroupOf.mp hc))
  have hπact : ∀ g m, πM (act g m) = Multiplicative.ofAdd
      ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (πM m).toAdd.1,
        (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (πM m).toAdd.2) := by
    intro g m
    rw [hπM, hπM, toAdd_ofAdd]
    change Multiplicative.ofAdd (S.π (θ (α g m))) = _
    rw [MonoidHom.comp_apply, BinarySymplecticSix.map_liftConj_apply, S.π_ρ_conj _ _ m.2]
  have hτcomm : ∀ (m n : M) (h : m⁻¹ * n⁻¹ * m * n ∈ T'),
      ((τM ⟨m⁻¹ * n⁻¹ * m * n, h⟩).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) =
        vecMulVec (πM m).toAdd.1 (πM n).toAdd.2 + vecMulVec (πM n).toAdd.2 (πM m).toAdd.1 +
          vecMulVec (πM m).toAdd.2 (πM n).toAdd.1 +
            vecMulVec (πM n).toAdd.1 (πM m).toAdd.2 := by
    intro m n h
    have h1 : S.τ (τM ⟨m⁻¹ * n⁻¹ * m * n, h⟩) =
        S.τ (Multiplicative.ofAdd (polarAlt (S.π (θ m)) (S.π (θ n)))) := by
      rw [hτM]
      have he : ((m⁻¹ * n⁻¹ * m * n : M) : E) = ⁅((m : E))⁻¹, ((n : E))⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv]
        rfl
      rw [he, map_commutatorElement, map_inv, map_inv,
        S.commutator_eq _ (S.N.inv_mem m.2) _ (S.N.inv_mem n.2), S.π_inv m.2, S.π_inv n.2,
        polarAlt_neg_neg]
    rw [S.τ_injective h1, toAdd_ofAdd, coe_polarAlt, hπM, hπM, toAdd_ofAdd, toAdd_ofAdd]
    rfl
  have hCT : C' ≤ T' := fun c hc => Subgroup.mem_subgroupOf.mpr
    (ker_le_preV (Subgroup.mem_subgroupOf.mp hc))
  have hTZ : T' ≤ Subgroup.center M := fun t ht => Subgroup.mem_center_iff.mpr fun m =>
    Subtype.ext (mul_comm_of_mem_preV hC hθ hsq (Subgroup.mem_subgroupOf.mp ht) m.2).symm
  obtain ⟨hel, -, hinf, -, -⟩ := binaryPolar_commutator_complement hr hCT hTZ πM hπMsurj hπT
    τM hτC act hactC hπact hτcomm
  refine ⟨eq_bot_iff.mpr fun x hx => ?_, fun v hv => ?_⟩
  · obtain ⟨hxM, hxc⟩ := mem_commutator_of_mem_commutator hx.2
    have hxC : (⟨x, hxM⟩ : M) ∈ C' ⊓ commutator M :=
      ⟨Subgroup.mem_subgroupOf.mpr hx.1, hxc⟩
    rw [hinf, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxC)
  · obtain ⟨hvM, hvc⟩ := mem_commutator_of_mem_commutator hv
    exact congrArg Subtype.val (hel.2 _ hvc)

include hC in
theorem sq_eq_one_of_mem_preV (hr : 3 ≤ r) (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) {t : E}
    (ht : t ∈ S.preV θ) : t ^ 2 = 1 := by
  have h := preV_le_commutator_sup hθ ht
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at h
  obtain ⟨v, hv, c, hc, rfl⟩ := h
  have hvc : Commute v c := Subgroup.mem_center_iff.mp (hC hc) v
  rw [hvc.mul_pow, (commutator_preN_spec hθ hC hr hsq).2 v hv, hsq c hc, one_mul]

include hC in
theorem mul_comm_of_mem_preV_of_mem_preV (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) {t t' : E}
    (ht : t ∈ S.preV θ) (ht' : t' ∈ S.preV θ) : t * t' = t' * t :=
  mul_comm_of_mem_preV hC hθ hsq ht (preV_le_preN ht')

omit hθ

variable (S θ) in
@[expose] def conjPreN (hh : E) (hhh : θ hh = S.h) : S.preN θ →* S.preN θ :=
  ((MulAut.conj hh).toMonoidHom.comp (S.preN θ).subtype).codRestrict (S.preN θ) fun m => by
    change θ (hh * m * hh⁻¹) ∈ S.N
    rw [map_mul, map_mul, map_inv, hhh]
    exact S.h_conj_mem _ m.2

theorem coe_conjPreN (hh : E) (hhh : θ hh = S.h) (m : S.preN θ) :
    (conjPreN S θ hh hhh m : E) = hh * m * hh⁻¹ :=
  rfl

variable (S θ) in
@[expose] noncomputable def normPreN (hh : E) (hhh : θ hh = S.h) :
    S.preN θ →* Abelianization (S.preN θ) :=
  Abelianization.of * Abelianization.of.comp (conjPreN S θ hh hhh) *
    Abelianization.of.comp ((conjPreN S θ hh hhh).comp (conjPreN S θ hh hhh))

variable (S θ) in
@[expose] noncomputable def radComplement (hh : E) (hhh : θ hh = S.h) : Subgroup E :=
  (normPreN S θ hh hhh).ker.map (S.preN θ).subtype

theorem mem_radComplement {hh : E} {hhh : θ hh = S.h} {y : E} :
    y ∈ radComplement S θ hh hhh ↔ y ∈ S.preN θ ∧
      y * (hh * y * hh⁻¹) * (hh * (hh * y * hh⁻¹) * hh⁻¹) ∈ ⁅S.preN θ, S.preN θ⁆ := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, ?_⟩
    have h : y' * conjPreN S θ hh hhh y' * conjPreN S θ hh hhh (conjPreN S θ hh hhh y') ∈
        commutator (S.preN θ) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_mul]
      exact hy'
    exact coe_mem_commutator h
  · rintro ⟨hy, hn⟩
    obtain ⟨hnM, hnc⟩ := mem_commutator_of_mem_commutator hn
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    change Abelianization.of _ * Abelianization.of _ * Abelianization.of _ = 1
    rw [← map_mul, ← map_mul, ← MonoidHom.mem_ker, Abelianization.ker_of]
    convert hnc using 1
    exact Subtype.ext rfl

include hθ hC in
theorem eq_one_of_mem_radComplement (hr : 3 ≤ r) (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) (hh : E)
    (hhh : θ hh = S.h) {c : E} (hc : c ∈ radComplement S θ hh hhh) (hc1 : θ c = 1) : c = 1 := by
  obtain ⟨-, hn⟩ := mem_radComplement.mp hc
  have hconj : hh * c * hh⁻¹ = c := UnitaryOddCover.conj_central (hC hc1) hh
  rw [hconj, hconj, show c * c * c = c ^ 2 * c by rw [sq], hsq c hc1, one_mul] at hn
  have hmem : c ∈ θ.ker ⊓ ⁅S.preN θ, S.preN θ⁆ := ⟨hc1, hn⟩
  rw [(commutator_preN_spec hθ hC hr hsq).1] at hmem
  exact hmem

include hθ hC in
theorem exists_mem_radComplement (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) (hh : E) (hhh : θ hh = S.h)
    {n : X} (hn : n ∈ S.N) : ∃ y ∈ radComplement S θ hh hhh, θ y = n := by
  obtain ⟨y, rfl⟩ := hθ n
  have hy : y ∈ S.preN θ := hn
  have hconjM : ∀ m ∈ S.preN θ, hh * m * hh⁻¹ ∈ S.preN θ := fun m hm => by
    rw [mem_preN, map_mul, map_mul, map_inv, hhh]
    exact S.h_conj_mem _ hm
  have hY : y * (hh * y * hh⁻¹) * (hh * (hh * y * hh⁻¹) * hh⁻¹) ∈ S.preV θ := by
    rw [mem_preV]
    have h := S.norm_mem_τ_range hn
    simpa only [map_mul, map_inv, hhh] using h
  have hY' := preV_le_commutator_sup hθ hY
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hY'
  obtain ⟨v, hv, c, hc, hvc⟩ := hY'
  have hcen : c ∈ Subgroup.center E := hC hc
  refine ⟨y * c, mem_radComplement.mpr ⟨mul_mem hy (preV_le_preN (ker_le_preV hc)), ?_⟩, ?_⟩
  · have hcc : ∀ z : E, hh * (z * c) * hh⁻¹ = hh * z * hh⁻¹ * c := fun z => by
      rw [show hh * (z * c) * hh⁻¹ = hh * z * hh⁻¹ * (hh * c * hh⁻¹) by group,
        UnitaryOddCover.conj_central hcen]
    rw [hcc, hcc, UnitaryOddCover.mul_central_three hcen, ← hvc, mul_assoc, ← pow_succ',
      show c ^ (3 + 1) = (c ^ 2) ^ 2 by rw [← pow_mul], hsq c hc, one_pow, mul_one]
    exact hv
  · rw [map_mul, show θ c = 1 from hc, mul_one]

include hC in
theorem conj_mem_radComplement (hh : E) (hhh : θ hh = S.h) {g : GL (Fin r) (ZMod 2)} {u : E}
    (hu : θ u = S.ρ g) {y : E} (hy : y ∈ radComplement S θ hh hhh) :
    u * y * u⁻¹ ∈ radComplement S θ hh hhh := by
  obtain ⟨hyM, hn⟩ := mem_radComplement.mp hy
  have hconjM : ∀ m ∈ S.preN θ, u * m * u⁻¹ ∈ S.preN θ := fun m hm => by
    rw [mem_preN, map_mul, map_mul, map_inv, hu]
    exact S.ρ_conj_mem g _ hm
  have hcomm : MulAut.conj (hh * u) = MulAut.conj (u * hh) :=
    BinarySymplecticSix.conj_eq_of_map_eq hC (by rw [map_mul, map_mul, hhh, hu, S.h_ρ])
  have hswap : ∀ z, hh * (u * z * u⁻¹) * hh⁻¹ = u * (hh * z * hh⁻¹) * u⁻¹ := fun z => by
    have h := congrArg (fun φ : MulAut E => φ z) hcomm
    simp only [MulAut.conj_apply] at h
    calc hh * (u * z * u⁻¹) * hh⁻¹ = hh * u * z * (hh * u)⁻¹ := by group
      _ = u * hh * z * (u * hh)⁻¹ := h
      _ = u * (hh * z * hh⁻¹) * u⁻¹ := by group
  refine mem_radComplement.mpr ⟨hconjM y hyM, ?_⟩
  rw [hswap, hswap, show u * y * u⁻¹ * (u * (hh * y * hh⁻¹) * u⁻¹) *
      (u * (hh * (hh * y * hh⁻¹) * hh⁻¹) * u⁻¹) =
      u * (y * (hh * y * hh⁻¹) * (hh * (hh * y * hh⁻¹) * hh⁻¹)) * u⁻¹ by group]
  have hM : (S.preN θ).map (MulAut.conj u).toMonoidHom ≤ S.preN θ := by
    rintro _ ⟨m, hm, rfl⟩
    exact hconjM m hm
  have hcM : ⁅S.preN θ, S.preN θ⁆.map (MulAut.conj u).toMonoidHom ≤ ⁅S.preN θ, S.preN θ⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hM hM
  exact hcM ⟨_, hn, rfl⟩

include hθ hC in
theorem ker_eq_bot_of_lift [Finite E] [Group.IsPerfect E] (hr : 3 ≤ r)
    (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) (U : Subgroup E)
    (hU : ∀ u ∈ U, θ u ∈ (LinearFlag.unitriangular r (ZMod 2)).map
      (S.ρ.comp SpecialLinearGroup.toGL))
    (hUsurj : ∀ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (S.ρ.comp SpecialLinearGroup.toGL),
      ∃ u ∈ U, θ u = a)
    (hUinj : ∀ u ∈ U, θ u = 1 → u = 1) : θ.ker = ⊥ := by
  have h2 : IsPGroup 2 θ.ker := fun k => ⟨1, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact hsq _ k.2)⟩
  obtain ⟨hh, hhh⟩ := hθ S.h
  obtain ⟨Syl, hSyl⟩ := S.sylow
  have hUN : U ≤ Subgroup.normalizer (radComplement S θ hh hhh : Set E) := by
    intro u hu
    obtain ⟨A, -, hA⟩ := hU u hu
    have hu' : θ u = S.ρ (SpecialLinearGroup.toGL A) := hA.symm
    have hui : θ u⁻¹ = S.ρ (SpecialLinearGroup.toGL A)⁻¹ := by rw [map_inv, hu', map_inv]
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => conj_mem_radComplement hC hh hhh hu' hn, fun hn => ?_⟩
    have := conj_mem_radComplement hC hh hhh hui hn
    rwa [show u⁻¹ * (u * n * u⁻¹) * u⁻¹⁻¹ = n by group] at this
  have hker := OrthogonalSplit.ker_le_of_lifts hθ hC h2 ⊥ S.N _ Syl hSyl S.inf_eq_bot
    (radComplement S θ hh hhh) U hUN (fun v hv => (mem_radComplement.mp hv).1) hU
    (fun b hb => exists_mem_radComplement hθ hC hsq hh hhh hb) hUsurj
    (fun v hv hθv => Subgroup.mem_bot.mpr (eq_one_of_mem_radComplement hθ hC hr hsq hh hhh hv hθv))
    (fun u hu hθu => Subgroup.mem_bot.mpr (hUinj u hu hθu))
  exact le_bot_iff.mp hker

include hθ hC in
theorem exists_lift_of_five_le [Finite E] (hr : 5 ≤ r) (h2 : IsPGroup 2 θ.ker) :
    ∃ U : Subgroup E,
      (∀ u ∈ U, θ u ∈ (LinearFlag.unitriangular r (ZMod 2)).map
        (S.ρ.comp SpecialLinearGroup.toGL)) ∧
      (∀ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (S.ρ.comp SpecialLinearGroup.toGL),
        ∃ u ∈ U, θ u = a) ∧ ∀ u ∈ U, θ u = 1 → u = 1 := by
  set ρ' : SpecialLinearGroup (Fin r) (ZMod 2) →* X := S.ρ.comp SpecialLinearGroup.toGL
    with hρ'
  have hρ'inj : Function.Injective ρ' :=
    S.ρ_injective.comp fun A B h => Subtype.ext (congrArg Units.val h)
  set R := ρ'.range with hR
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set F₀ := OrthogonalSplit.leviLift θ R with hF₀
  have : Group.IsPerfect F₀ := OrthogonalSplit.isPerfect_leviLift θ R hθ hC
  set η : F₀ →* LinearFlag.projectiveSL r (ZMod 2) := (LinearFlag.proj r (ZMod 2)).comp
    ((MonoidHom.ofInjective hρ'inj).symm.toMonoidHom.comp (OrthogonalSplit.leviLiftHom θ R))
    with hη
  have hηeq : ∀ u : F₀, η u = 1 ↔ θ u = 1 := by
    intro u
    rw [hη, MonoidHom.comp_apply, LinearFlag.proj_eq_one_iff,
      OrthogonalSplit.scalars_zmod_two_eq_bot, Subgroup.mem_bot, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, map_one,
      ← OrthogonalSplit.leviLiftHom_eq_one_iff θ R u]
  have hηsurj : Function.Surjective η :=
    (LinearFlag.proj_surjective r (ZMod 2)).comp
      ((MonoidHom.ofInjective hρ'inj).symm.surjective.comp
        (OrthogonalSplit.leviLiftHom_surjective θ R hθ))
  have hηC : η.ker ≤ Subgroup.center F₀ := fun u hu => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hηeq u).mp hu)) g)
  have hη2 : IsPGroup 2 η.ker := fun k => by
    obtain ⟨n, hn⟩ := h2 ⟨((k : F₀) : E), (hηeq k).mp k.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hηbot := LinearCover.ker_eq_bot_of_projectiveSL (K := ZMod 2) (by rw [Nat.card_zmod]) hr
    η hηsurj hηC hη2
  have hF₀inj : ∀ u ∈ F₀, θ u = 1 → u = 1 := by
    intro u hu hθu
    have hk : (⟨u, hu⟩ : F₀) ∈ η.ker := (hηeq _).mpr hθu
    rw [hηbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  refine ⟨((LinearFlag.unitriangular r (ZMod 2)).map ρ').comap θ ⊓ F₀, fun u hu => hu.1,
    fun a ha => ?_, fun u hu hθu => hF₀inj u hu.2 hθu⟩
  have haR : a ∈ F₀.map θ := by
    rw [hF₀, OrthogonalSplit.map_leviLift θ R hθ]
    exact Subgroup.map_le_range ρ' _ ha
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp haR
  exact ⟨u, ⟨ha, hu⟩, rfl⟩

omit hθ hC in
theorem map_unitriangular_eq_closure :
    (LinearFlag.unitriangular r (ZMod 2)).map (S.ρ.comp SpecialLinearGroup.toGL) =
      Subgroup.closure {g | ∃ i j : Fin r, i < j ∧
        S.ρ (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j)) = g} := by
  have hU : LinearFlag.unitriangular r (ZMod 2) =
      Subgroup.closure {g | ∃ i j : Fin r, i < j ∧ LinearCover.rootSL i j = g} := by
    refine le_antisymm (LinearCover.unitriangular_le_closure_rootSL (by rw [Nat.card_zmod])) ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, rfl⟩
    exact LinearCover.rootSL_mem_unitriangular hij
  rw [hU, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩

omit hθ hC in
theorem card_map_unitriangular :
    Nat.card ((LinearFlag.unitriangular r (ZMod 2)).map (S.ρ.comp SpecialLinearGroup.toGL)) =
      2 ^ (r * (r - 1) / 2) := by
  have hinj : Function.Injective (S.ρ.comp SpecialLinearGroup.toGL) :=
    S.ρ_injective.comp fun A B h => Subtype.ext (congrArg Units.val h)
  have hcard := LinearFlag.card_unitriangular (K := ZMod 2) r
  rw [Nat.card_zmod] at hcard
  rw [← hcard]
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨fun u v huv => Subtype.ext (hinj (congrArg Subtype.val huv)),
      (S.ρ.comp SpecialLinearGroup.toGL).subgroupMap_surjective _⟩)).symm

end Shape

namespace Shape

section Three

variable {X : Type*} [Group X] (S : Shape X 3)

abbrev rootX (i j : Fin 3) : X :=
  S.ρ (SpecialLinearGroup.toGL (LinearCover.rootSL (K := ZMod 2) i j))

theorem pos_cases : ∀ i j : Fin 3, i < j → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
  decide

variable {S} {E : Type*} [Group E] {θ : E →* X} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)
include hθ hC

theorem sq_eq_one_and_commute_of_conj (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) {w g g' : X}
    (hg : w * g * w⁻¹ ∈ S.τ.range) (hg' : w * g' * w⁻¹ ∈ S.τ.range) {e e' : E} (he : θ e = g)
    (he' : θ e' = g') : e ^ 2 = 1 ∧ e * e' = e' * e := by
  obtain ⟨ŵ, hŵ⟩ := hθ w
  have h1 : ŵ * e * ŵ⁻¹ ∈ S.preV θ := by
    rw [mem_preV, map_mul, map_mul, map_inv, hŵ, he]
    exact hg
  have h2 : ŵ * e' * ŵ⁻¹ ∈ S.preV θ := by
    rw [mem_preV, map_mul, map_mul, map_inv, hŵ, he']
    exact hg'
  constructor
  · have h := sq_eq_one_of_mem_preV hθ hC le_rfl hsq h1
    rw [conj_pow] at h
    have h' : e ^ 2 = ŵ⁻¹ * (ŵ * e ^ 2 * ŵ⁻¹) * ŵ := by group
    rw [h', h]
    group
  · have h := mul_comm_of_mem_preV_of_mem_preV hθ hC hsq h1 h2
    have h' : ŵ * (e * e') * ŵ⁻¹ = ŵ * (e' * e) * ŵ⁻¹ := by
      rw [show ŵ * (e * e') * ŵ⁻¹ = ŵ * e * ŵ⁻¹ * (ŵ * e' * ŵ⁻¹) by group, h]
      group
    exact mul_left_cancel (mul_right_cancel h')

theorem exists_lift_of_three [Finite E] (hsq : ∀ c, θ c = 1 → c ^ 2 = 1)
    (hw₁ : ∃ w : X, w * S.rootX 0 1 * w⁻¹ ∈ S.τ.range ∧ w * S.rootX 0 2 * w⁻¹ ∈ S.τ.range)
    (hw₂ : ∃ w : X, w * S.rootX 1 2 * w⁻¹ ∈ S.τ.range ∧ w * S.rootX 0 2 * w⁻¹ ∈ S.τ.range) :
    ∃ U : Subgroup E,
      (∀ u ∈ U, θ u ∈ (LinearFlag.unitriangular 3 (ZMod 2)).map
        (S.ρ.comp SpecialLinearGroup.toGL)) ∧
      (∀ a ∈ (LinearFlag.unitriangular 3 (ZMod 2)).map (S.ρ.comp SpecialLinearGroup.toGL),
        ∃ u ∈ U, θ u = a) ∧ ∀ u ∈ U, θ u = 1 → u = 1 := by
  obtain ⟨w₁, h11, h12⟩ := hw₁
  obtain ⟨w₂, h21, h22⟩ := hw₂
  obtain ⟨a, ha⟩ := hθ (S.rootX 0 1)
  obtain ⟨b, hb⟩ := hθ (S.rootX 1 2)
  have hc : θ ⁅a, b⁆ = S.rootX 0 2 := by
    rw [map_commutatorElement, ha, hb, ← map_commutatorElement, ← map_commutatorElement,
      LinearCover.commutatorElement_rootSL (by decide) (by decide) (by decide)]
  obtain ⟨ha2, hac⟩ := sq_eq_one_and_commute_of_conj hθ hC hsq h11 h12 ha hc
  obtain ⟨hb2, hbc⟩ := sq_eq_one_and_commute_of_conj hθ hC hsq h21 h22 hb hc
  obtain ⟨hc2, -⟩ := sq_eq_one_and_commute_of_conj hθ hC hsq h12 h12 hc hc
  set y : Fin 3 → Fin 3 → E := ![![1, a, ⁅a, b⁆], ![1, 1, b], ![1, 1, 1]] with hy
  have hθy : ∀ i j, i < j → θ (y i j) = S.rootX i j := by
    intro i j hij
    rcases pos_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha
    · exact hc
    · exact hb
  have hy2 : ∀ i j, i < j → y i j * y i j = 1 := by
    intro i j hij
    rcases pos_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← sq]; exact ha2
    · rw [← sq]; exact hc2
    · rw [← sq]; exact hb2
  have hyc : ∀ i j k l, i < j → k < l → j ≠ k → i ≠ l → y i j * y k l = y k l * y i j := by
    intro i j k l hij hkl hjk hil
    rcases pos_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pos_cases k l hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | rfl
      | exact absurd rfl hjk
      | exact absurd rfl hil
      | exact hac
      | exact hac.symm
      | exact hbc
      | exact hbc.symm
  have hy3 : ∀ i j l, i < j → j < l → ⁅y i j, y j l⁆ = y i l := by
    intro i j l hij hjl
    rcases pos_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases pos_cases 1 l hjl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · rfl
    · exact absurd hjl (by revert l; decide)
    · exact absurd hjl (by revert l; decide)
  set U := Subgroup.closure {g | ∃ i j, i < j ∧ y i j = g} with hUdef
  have hcard : Nat.card U ≤ 2 ^ (3 * (3 - 1) / 2) :=
    LinearCover.card_closure_le_of_roots y hy2 hyc hy3
  have hmap : U.map θ = (LinearFlag.unitriangular 3 (ZMod 2)).map
      (S.ρ.comp SpecialLinearGroup.toGL) := by
    rw [map_unitriangular_eq_closure, hUdef, MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, (hθy i j hij).symm⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨y i j, ⟨i, j, hij, rfl⟩, hθy i j hij⟩
  have : Finite (U.map θ) := Finite.of_surjective _ (θ.subgroupMap_surjective U)
  have hbij : Function.Bijective (θ.subgroupMap U) := by
    refine (θ.subgroupMap_surjective U).bijective_of_nat_card_le ?_
    rw [hmap, card_map_unitriangular]
    exact hcard
  refine ⟨U, fun u hu => hmap ▸ Subgroup.mem_map_of_mem θ hu, fun g hg => ?_,
    fun u hu hθu => ?_⟩
  · rw [← hmap] at hg
    obtain ⟨u, hu, rfl⟩ := hg
    exact ⟨u, hu, rfl⟩
  · have h : θ.subgroupMap U ⟨u, hu⟩ = θ.subgroupMap U 1 :=
      Subtype.ext (by rw [map_one]; exact hθu)
    exact congrArg Subtype.val (hbij.1 h)

end Three

end Shape

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
