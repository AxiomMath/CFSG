module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
public import CFSG.GH74.Generic.S3.V1InnerLib

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.Assembly.LowTwoRank
open CFSG.GH74.KGroups.L3Eps (tInv tInv_mul_self tInv_ne_one exists_projectiveSL_equiv blockSub
  isQuasisimple_blockSub tInv_mem_blockSub blockSub_le_centralizer conj_mem_blockSub
  commutator_mem_blockSub)
open scoped MatrixGroups commutatorElement

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem exists_invCore_lin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {X : Type}
    [Group X] [Finite X] (hX : StatedClassicalModel X .PSL 3 p f) :
    ∀ x : X, x * x = 1 → x ≠ 1 → ∃ S : Subgroup X, CFSG.IsQuasisimple ↥S ∧ x ∈ S ∧
      S ≤ Subgroup.centralizer ({x} : Set X) ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set X), ∀ s ∈ S, c * s * c⁻¹ ∈ S) ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set X), ∀ d ∈ Subgroup.centralizer ({x} : Set X),
        ⁅c, d⁆ ∈ S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := Generic.S3.two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  intro x hx2 hx1
  have hex2 : e x * e x = 1 := by rw [← map_mul, hx2, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := Generic.S3.singleInv_projectiveSL h2 (e x) tInv hex2 hex1 tInv_mul_self
    (tInv_ne_one h2)
  let e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.trans (MulAut.conj g)
  have he' : e' x = tInv := by
    show MulAut.conj g (e x) = tInv
    rw [MulAut.conj_apply]
    exact hg
  have hcen : ∀ y : X, y ∈ Subgroup.centralizer ({x} : Set X) ↔
      e' y ∈ Subgroup.centralizer ({tInv} : Set
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← he',
      ← map_mul, ← map_mul]
    exact ⟨fun h => by rw [h], fun h => e'.injective h⟩
  have hmem : ∀ y : X, y ∈ blockSub.map e'.symm.toMonoidHom ↔ e' y ∈ blockSub := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro h
      exact ⟨e' y, h, by simp⟩
  refine ⟨blockSub.map e'.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e'.symm blockSub)
      (isQuasisimple_blockSub h4)
  · rw [hmem, he']
    exact tInv_mem_blockSub
  · intro s hs
    rw [hmem] at hs
    rw [hcen]
    exact blockSub_le_centralizer hs
  · intro c hc s hs
    rw [hcen] at hc
    rw [hmem] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_blockSub h2 hc hs
  · intro c hc d hd
    rw [hcen] at hc hd
    rw [hmem, map_commutatorElement]
    exact commutator_mem_blockSub h2 hc hd

theorem comp_mem_lin_all {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {X : Type}
    [Group X] [Finite X] (hX : StatedClassicalModel X .PSL 3 p f) :
    ∀ y : X, y * y = 1 → y ≠ 1 → ∀ B : Subgroup X,
      IsCompIn (Subgroup.centralizer ({y} : Set X)) B → y ∈ B := by
  intro y hy2 hy1 B hB
  obtain ⟨S, hS, hyS, hSc, hSn, hSd⟩ := exists_invCore_lin hp hp2 h5 hX y hy2 hy1
  exact GHInv.mem_of_isCompIn_of_normal_quasisimple hS hyS hSc hSn hSd hB

theorem Ivk73Cfg.false_of_comp_mem_of_inv
    (h : Ivk73Cfg N L K Q) (hu : ∃ u : N, u ∈ Q ∧ orderOf u = 2 ∧ u ∈ L)
    (hcomp : ∀ y : ↥L, y * y = 1 → y ≠ 1 → ∀ B : Subgroup ↥L,
      IsCompIn (centralizer ({y} : Set ↥L)) B → y ∈ B) : False := by
  obtain ⟨u, huQ, hu2, huL⟩ := hu
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  let y : ↥L := ⟨u, huL⟩
  have hy2 : y * y = 1 := Subtype.ext huu
  have hy1 : y ≠ 1 := by
    intro h1
    have : u = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hu2
    omega
  have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
  have hterm := h.terminal u hu2 huC
  have hKM : K ≤ centralizer ({u} : Set N) ⊓ L := le_inf hterm.1 h.K_le
  have hM : IsCompIn (centralizer ({u} : Set N) ⊓ L) K :=
    LU.Local.isCompIn_mono' hterm hKM inf_le_left
  have hB : IsCompIn (centralizer ({y} : Set ↥L)) (K.subgroupOf L) := by
    rw [← subgroupOf_centralizer_inf_eq u huL]
    exact ⟨Subgroup.subgroupOf_mono L hKM,
      (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({u} : Set N) ⊓ L) (H := L)
        inf_le_right).2 hM.2⟩
  have hyB : y ∈ K.subgroupOf L := hcomp y hy2 hy1 _ hB
  have huK : u ∈ K := hyB
  have hodd := odd_center_K h.kbar_cases
  let c : ↥(center ↥K) := ⟨⟨u, huK⟩, Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 huC g g.2)⟩
  have hc2 : orderOf c = 2 := by
    have h1 : orderOf (⟨u, huK⟩ : ↥K) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu2
    rw [← Subgroup.orderOf_coe c]
    exact h1
  have hdvd : orderOf c ∣ Nat.card (center ↥K) := orderOf_dvd_natCard c
  rw [hc2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end CFSG.GH74.GLS.IVK
