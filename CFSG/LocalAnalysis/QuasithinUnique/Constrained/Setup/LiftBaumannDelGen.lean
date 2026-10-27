module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannGen

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization
open Projectivization

universe v

section Perm

variable {Ω : Type*} [DecidableEq Ω]

theorem closure_path_swaps [Fintype Ω] (h5 : Fintype.card Ω = 5)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (haω : a ≠ ω) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbω : b ≠ ω) (hcd : c ≠ d) (hcω : c ≠ ω) (hdω : d ≠ ω) :
    Subgroup.closure ({Equiv.swap a b, Equiv.swap b c, Equiv.swap c d, Equiv.swap d ω} :
      Set (Equiv.Perm Ω)) = ⊤ := by
  set H := Subgroup.closure ({Equiv.swap a b, Equiv.swap b c, Equiv.swap c d, Equiv.swap d ω} :
    Set (Equiv.Perm Ω)) with hH
  have h1 : Equiv.swap a b ∈ H := Subgroup.subset_closure (by simp)
  have h2 : Equiv.swap b c ∈ H := Subgroup.subset_closure (by simp)
  have h3 : Equiv.swap c d ∈ H := Subgroup.subset_closure (by simp)
  have h4 : Equiv.swap d ω ∈ H := Subgroup.subset_closure (by simp)
  have key : ∀ x y z : Ω, x ≠ y → x ≠ z → y ≠ z → Equiv.swap x y ∈ H → Equiv.swap y z ∈ H →
      Equiv.swap x z ∈ H := by
    intro x y z hxy hxz hyz hxy' hyz'
    have : Equiv.swap y z * Equiv.swap x y * Equiv.swap y z = Equiv.swap z x :=
      Equiv.swap_mul_swap_mul_swap hxy hxz
    rw [Equiv.swap_comm z x] at this
    rw [← this]
    exact H.mul_mem (H.mul_mem hyz' hxy') hyz'
  have h5' : Equiv.swap a c ∈ H := key a b c hab hac hbc h1 h2
  have h6 : Equiv.swap b d ∈ H := key b c d hbc hbd hcd h2 h3
  have h7 : Equiv.swap c ω ∈ H := key c d ω hcd hcω hdω h3 h4
  have h8 : Equiv.swap a d ∈ H := key a c d hac had hcd h5' h3
  have h9 : Equiv.swap b ω ∈ H := key b d ω hbd hbω hdω h6 h4
  have h10 : Equiv.swap a ω ∈ H := key a d ω had haω hdω h8 h4
  have hcover : ∀ x : Ω, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = ω := by
    intro x
    have hcard : ({a, b, c, d, ω} : Finset Ω).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair hdω] <;> simp [*]
    have : ({a, b, c, d, ω} : Finset Ω) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, h5])
    have hx : x ∈ ({a, b, c, d, ω} : Finset Ω) := by rw [this]; exact Finset.mem_univ x
    simpa using hx
  have hall : ∀ x y : Ω, x ≠ y → Equiv.swap x y ∈ H := by
    intro x y hxy
    rcases hcover x with rfl | rfl | rfl | rfl | rfl <;>
      rcases hcover y with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | (rwa [Equiv.swap_comm])
  refine eq_top_iff.2 ?_
  rw [← Equiv.Perm.closure_isSwap]
  rw [Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  exact hall x y hxy

@[expose] def fiveCycle (a b c d ω : Ω) : Equiv.Perm Ω :=
  Equiv.swap a b * Equiv.swap b c * Equiv.swap c d * Equiv.swap d ω

theorem fiveCycle_apply {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (haω : a ≠ ω)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbω : b ≠ ω) (hcd : c ≠ d) (hcω : c ≠ ω) (hdω : d ≠ ω) :
    fiveCycle a b c d ω a = b ∧ fiveCycle a b c d ω b = c ∧ fiveCycle a b c d ω c = d ∧
      fiveCycle a b c d ω d = ω ∧ fiveCycle a b c d ω ω = a := by
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hωa := haω.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have hωb := hbω.symm
  have hdc := hcd.symm
  have hωc := hcω.symm
  have hωd := hdω.symm
  simp [fiveCycle, Equiv.swap_apply_def, *]

theorem fiveCycle_even [Fintype Ω] {a b c d ω : Ω} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d)
    (hdω : d ≠ ω) : fiveCycle a b c d ω ∈ alternatingGroup Ω := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [fiveCycle, hab, hbc, hcd, hdω]

theorem sym5_sup_conj_eq_top [Fintype Ω] (h5 : Fintype.card Ω = 5)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (haω : a ≠ ω) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbω : b ≠ ω) (hcd : c ≠ d) (hcω : c ≠ ω) (hdω : d ≠ ω) :
    Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) ⊔
      (Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω))).map
        (MulAut.conj (fiveCycle a b c d ω)).toMonoidHom = ⊤ := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := fiveCycle_apply hab hac had haω hbc hbd hbω hcd hcω hdω
  set σ := fiveCycle a b c d ω with hσ
  set C := Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) with hC
  set K := C ⊔ C.map (MulAut.conj σ).toMonoidHom with hK
  have hconj : ∀ x y : Ω, Equiv.swap x y ∈ C → Equiv.swap (σ x) (σ y) ∈ K := by
    intro x y hxy
    refine Subgroup.mem_sup_right ⟨Equiv.swap x y, hxy, ?_⟩
    rw [Equiv.swap_apply_apply]
    simp [MulAut.conj_apply]
  have h1 : Equiv.swap a b ∈ K := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have h3 : Equiv.swap c d ∈ K := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have h2 : Equiv.swap b c ∈ K := by
    have := hconj a b (Subgroup.subset_closure (by simp))
    rwa [e1, e2] at this
  have h4 : Equiv.swap d ω ∈ K := by
    have := hconj c d (Subgroup.subset_closure (by simp))
    rwa [e3, e4] at this
  rw [eq_top_iff, ← closure_path_swaps h5 hab hac had haω hbc hbd hbω hcd hcω hdω,
    Subgroup.closure_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

end Perm

section Gen

variable {𝔊 : Type*} [Group 𝔊] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem deleted_exists_conj_gen (h5 : Fintype.card Ω = 5) {B Li A : Subgroup 𝔊}
    (ψ : ↥B ≃* Equiv.Perm Ω) (hLiB : Li ≤ B) (hAB : A ≤ B)
    (halt : (Li.subgroupOf B).map ψ.toMonoidHom = alternatingGroup Ω)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (haω : a ≠ ω) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbω : b ≠ ω) (hcd : c ≠ d) (hcω : c ≠ ω) (hdω : d ≠ ω)
    (hA : (A.subgroupOf B).map ψ.toMonoidHom =
      Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω))) :
    ∃ g ∈ Li, Li ≤ A ⊔ conjSub g A := by
  classical
  set σ := fiveCycle a b c d ω with hσ
  have hσalt : σ ∈ alternatingGroup Ω := fiveCycle_even hab hbc hcd hdω
  have hσmem : σ ∈ (Li.subgroupOf B).map ψ.toMonoidHom := by
    rw [halt]
    exact hσalt
  obtain ⟨x, hxLi, hxσ⟩ := hσmem
  have hxLi' : (x : 𝔊) ∈ Li := hxLi
  have hxσ' : ψ x = σ := hxσ
  refine ⟨(x : 𝔊), hxLi', ?_⟩
  set Cl := A ⊔ conjSub (x : 𝔊) A with hCl
  have hClB : Cl ≤ B := by
    refine sup_le hAB ?_
    intro y hy
    rw [mem_conjSub] at hy
    have h1 : (x : 𝔊) * ((x : 𝔊)⁻¹ * y * (x : 𝔊)) * (x : 𝔊)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem x.2 (hAB hy)) (B.inv_mem x.2)
    simpa [mul_assoc] using h1
  set K := (Cl.subgroupOf B).map ψ.toMonoidHom with hK
  set C := Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) with hC
  have hCK : C ≤ K := by
    rw [← hA]
    refine Subgroup.map_mono fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hy))
  have hCK' : C.map (MulAut.conj σ).toMonoidHom ≤ K := by
    rintro _ ⟨τ, hτ, rfl⟩
    have hτ' : τ ∈ (A.subgroupOf B).map ψ.toMonoidHom := by
      rw [hA]
      exact hτ
    obtain ⟨y, hy, rfl⟩ := hτ'
    have hyA : (y : 𝔊) ∈ A := hy
    refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have hmem : (x : 𝔊) * (y : 𝔊) * (x : 𝔊)⁻¹ ∈ conjSub (x : 𝔊) A := by
        rw [mem_conjSub]
        simpa [mul_assoc] using hyA
      exact Subgroup.mem_sup_right hmem
    · show ψ (x * y * x⁻¹) = _
      rw [map_mul, map_mul, map_inv, hxσ']
      simp [MulAut.conj_apply]
  have hKtop : K = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← sym5_sup_conj_eq_top h5 hab hac had haω hbc hbd hbω hcd hcω hdω]
    exact sup_le hCK hCK'
  intro l hl
  have hlB : l ∈ B := hLiB hl
  have hψl : ψ ⟨l, hlB⟩ ∈ K := by
    rw [hKtop]
    trivial
  obtain ⟨c', hc', hcl⟩ := hψl
  have hcl' : c' = ⟨l, hlB⟩ := ψ.injective hcl
  rw [hcl'] at hc'
  exact Subgroup.mem_subgroupOf.1 hc'

end Gen

section Deleted

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem deleted_exists_gen_element (ctx : FamilyCtx H T n F r Lc)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) (common : EvenSL2FamilyCommon H T r Lc)
    (ψ : ∀ i, ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
    (A : Fin r → Subgroup (V ≃ₗ[ZMod 2] V))
    (halt : ∀ i, ((Lc i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
      alternatingGroup (ℙ F (Fin 2 → F)))
    (hAB : ∀ i, A i ≤ blockB H (Lc i))
    (hAs : ∀ i, ∃ a b c d ω : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
      ((A i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
        Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm (ℙ F (Fin 2 → F))))) :
    ∃ g ∈ ⨆ i, Lc i, (⨆ i, Lc i) ≤ (⨆ i, A i) ⊔ conjSub g (⨆ i, A i) := by
  refine exists_gen_element_of_local ctx A (fun i j hij x hx y hy => ?_) (fun i => ?_)
  · exact common.B_comm i j hij x (common.L_le_B i hx) y (hAB j hy)
  · obtain ⟨a, b, c, d, ω, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hA⟩ := hAs i
    exact deleted_exists_conj_gen h5 (ψ i) (common.L_le_B i) (hAB i) (halt i) hab hac had hωa.symm
      hbc hbd hωb.symm hcd hωc.symm hωd.symm hA

omit [Finite V] in
theorem natCard_W_deleted (hdel : DeletedFamily H n r Lc) (i : Fin r) :
    Nat.card (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) = 16 := by
  obtain ⟨Ω, _, _, h5, ψ, β, -⟩ := hdel.model i
  have hZ : fixIn (Lc i) (commGL (Lc i) ⊤) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : (w : V) ∈ commGL (Lc i) ⊤ ⊓ fixGL (Lc i) := ⟨w.2, hw⟩
    rw [hdel.Z_bot] at h1
    exact Subtype.ext (Submodule.mem_bot _ |>.1 h1)
  rw [Nat.card_congr (Submodule.quotEquivOfEqBot _ hZ).toEquiv, Nat.card_congr β.toEquiv]
  exact natCard_evenWeight h5

theorem card_V_deleted (ctx : FamilyCtx H T n F r Lc) (hdel : DeletedFamily H n r Lc) :
    Nat.card V = Nat.card ↥(fixGL (oddGen H)) * 2 ^ (4 * r) := by
  rw [card_V_eq_prod ctx, Finset.prod_congr rfl fun i _ => natCard_W_deleted hdel i,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
  norm_num

end Deleted

end CFSG.QuasithinUnique.Setup.Lift
