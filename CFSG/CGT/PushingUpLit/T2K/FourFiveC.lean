module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveB
public import CFSG.CGT.PushingUpLit.T2K.Cohomology

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

theorem card_fixed_le {F : Type} [Field F] [Finite F] {r : Matrix.SpecialLinearGroup (Fin 2) F}
    (hr : r ≠ 1) :
    Nat.card {w : Fin 2 → F | (r : Matrix (Fin 2) (Fin 2) F).mulVec w = w} ≤ Nat.card F := by
  classical
  set N : Matrix (Fin 2) (Fin 2) F := (r : Matrix (Fin 2) (Fin 2) F) - 1 with hNdef
  have hN : N ≠ 0 := by
    intro h0
    apply hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.1 h0
  let f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) := Matrix.mulVecLin N
  have hf : f ≠ 0 := by
    intro h0
    apply hN
    ext i j
    have := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
    simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank F (LinearMap.range f) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    exact hf h0
  have h3 : Module.finrank F (LinearMap.ker f) ≤ 1 := by
    have : Module.finrank F (Fin 2 → F) = 2 := by simp
    omega
  have h4 : Nat.card (LinearMap.ker f) = Nat.card F ^ Module.finrank F (LinearMap.ker f) :=
    Module.natCard_eq_pow_finrank
  have h5 : {w : Fin 2 → F | (r : Matrix (Fin 2) (Fin 2) F).mulVec w = w} =
      (LinearMap.ker f : Set (Fin 2 → F)) := by
    ext w
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, f, Matrix.mulVecLin_apply,
      hNdef, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [h5]
  calc Nat.card (LinearMap.ker f : Set (Fin 2 → F)) = Nat.card (LinearMap.ker f) := rfl
    _ = Nat.card F ^ Module.finrank F (LinearMap.ker f) := h4
    _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right Nat.card_pos h3
    _ = Nat.card F := pow_one _

namespace NatBlock

theorem card_blockU (h : NatBlock L n) :
    Nat.card ↥(blockU L) = (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := by
  classical
  let D := h.natData
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup D.ψ.ker
  have e : (↥(blockU L) ⧸ D.ψ.ker) ≃* Multiplicative (Fin 2 → GaloisField 2 n) :=
    QuotientGroup.quotientKerEquivOfSurjective D.ψ D.ψ_surj
  have hker : Nat.card ↥D.ψ.ker = Nat.card ↥(blockZ L) := by
    have hk : D.ψ.ker = (blockZ L).subgroupOf (blockU L) := by
      ext v
      rw [MonoidHom.mem_ker, D.ψ_ker, Subgroup.mem_subgroupOf]
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockZ_le_blockU L)).toEquiv
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by have := h.two_le; omega)
  have hF : Nat.card (Multiplicative (Fin 2 → GaloisField 2 n)) = (2 ^ n) ^ 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → GaloisField 2 n) ≃ _),
      Nat.card_fun, hq]
    simp
  rw [h1, Nat.card_congr e.toEquiv, hF, hker]

end NatBlock

omit [Finite G] in
theorem conj_mem_centralizer_of_normalizer {x y : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.centralizer (L : Set G)) : x * y * x⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
  (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer hx) y).1 hy

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem A_le_normalizer {a : G} (ha : a ∈ A) : a ∈ Subgroup.normalizer (L : Set G) :=
  H.normal (H.A_le_M ha)

theorem delta_mem_blockZ {a b l : G} (ha : a ∈ A)
    (hb : b ∈ A ⊓ Subgroup.centralizer (blockU L : Set G)) (hl : l ∈ L) (hact : ActsAs L a l) :
    delta b l ∈ blockZ L := by
  have hbU : b ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨H.A_le_M hb.1, hb.2⟩
  have hu : l⁻¹ * a ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
    H.inv_mul_mem_centralizer ha hl hact
  have hc : ⁅(l⁻¹ * a)⁻¹, b⁆ ∈ Subgroup.centralizer (L : Set G) :=
    H.block.comm_mem_centralizer H.normal (inv_mem hu) hbU
  have hab : a * b = b * a := H.A_comm ha hb.1
  have hab' : a⁻¹ * b = b * a⁻¹ := (Commute.inv_left (show Commute a b from hab)).eq
  have hdelta : delta b l = b⁻¹ * (a * ⁅(l⁻¹ * a)⁻¹, b⁆ * a⁻¹) * b := by
    calc delta b l = b⁻¹ * a * (l⁻¹ * a)⁻¹ * b * (l⁻¹ * a) * a⁻¹ := by
          simp only [delta]; group
      _ = b⁻¹ * a * ((l⁻¹ * a)⁻¹ * b * (l⁻¹ * a) * b⁻¹) * (b * a⁻¹) := by group
      _ = b⁻¹ * a * ((l⁻¹ * a)⁻¹ * b * (l⁻¹ * a) * b⁻¹) * (a⁻¹ * b) := by rw [hab']
      _ = b⁻¹ * (a * ⁅(l⁻¹ * a)⁻¹, b⁆ * a⁻¹) * b := by
          simp only [commutatorElement_def]; group
  refine Subgroup.mem_inf.2 ⟨H.block.delta_mem H.normal hbU hl, ?_⟩
  rw [hdelta]
  have h1 := conj_mem_centralizer_of_normalizer (H.A_le_normalizer ha) hc
  have h2 := conj_mem_centralizer_of_normalizer (H.A_le_normalizer ((A.inv_mem hb.1))) h1
  simpa using h2

theorem κ_eq_zero_of_mem_range {b : G} (hb : b ∈ A ⊓ Subgroup.centralizer (blockU L : Set G))
    {g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)} (hg : g ∈ H.rho.range) :
    H.block.natData.κ b g = 0 := by
  obtain ⟨a, rfl⟩ := hg
  have hbU : b ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨H.A_le_M hb.1, hb.2⟩
  have h1 := H.rho_apply_eq (a := a) (H.lOf_mem a) (H.actsAs_lOf a)
  rw [h1, H.block.κ_apply H.le H.normal hbU (H.lOf_mem a)]
  exact (H.block.natData.ψe_eq_zero_iff (H.block.delta_mem H.normal hbU (H.lOf_mem a))).2
    (H.delta_mem_blockZ a.2 hb (H.lOf_mem a) (H.actsAs_lOf a))

theorem mem_centralizer_of_fixed_one {a₀ : G} (ha₀ : a₀ ∈ A)
    (ha₀V : a₀ ∉ Subgroup.centralizer (blockU L : Set G)) {v : G} (hv : v ∈ blockU L)
    (hfix : ((H.rho ⟨a₀, ha₀⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (H.block.natData.ψe v) =
        H.block.natData.ψe v) :
    v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) := by
  classical
  let D := H.block.natData
  set a₀' : ↥A := ⟨a₀, ha₀⟩ with ha₀'
  set r₀ := H.rho a₀' with hr₀
  have hr₀1 : r₀ ≠ 1 := fun h1 => ha₀V ((H.rho_eq_one_iff a₀').1 h1)
  have hr₀φ : r₀ = D.φ ⟨H.lOf a₀', H.lOf_mem a₀'⟩ := H.rho_apply_eq _ (H.actsAs_lOf a₀')
  let K₀ : Subgroup (Multiplicative (Fin 2 → GaloisField 2 n)) :=
    { carrier := {w | (r₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd w) = Multiplicative.toAdd w}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, toAdd_mul, Matrix.mulVec_add] at hx hy ⊢
        rw [hx, hy]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, toAdd_inv, Matrix.mulVec_neg] at hx ⊢
        rw [hx] }
  have hK₀card : Nat.card ↥K₀ ≤ 2 ^ n := by
    have hq : Nat.card (GaloisField 2 n) = 2 ^ n :=
      GaloisField.card 2 n (by have := H.block.two_le; omega)
    have e : ↥K₀ ≃ {w : Fin 2 → GaloisField 2 n |
        (r₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w = w} :=
      (Multiplicative.toAdd.subtypeEquiv fun w => Iff.rfl)
    rw [Nat.card_congr e, ← hq]
    exact card_fixed_le hr₀1
  have hK₀idx : K₀.index * Nat.card ↥K₀ = (2 ^ n) ^ 2 := by
    have hq : Nat.card (GaloisField 2 n) = 2 ^ n :=
      GaloisField.card 2 n (by have := H.block.two_le; omega)
    rw [Subgroup.index_mul_card, Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (Fin 2 → GaloisField 2 n) ≃ _), Nat.card_fun, hq]
    simp
  let E₀ : Subgroup ↥(blockU L) := K₀.comap D.ψ
  let C₀ : Subgroup ↥(blockU L) := (blockU L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
    (blockU L)
  have hC₀E₀ : C₀ ≤ E₀ := by
    intro x hx
    have hxV : (x : G) ∈ blockU L := x.2
    have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) := hx.2
    show D.ψ x ∈ K₀
    show (r₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (Multiplicative.toAdd (D.ψ x)) = Multiplicative.toAdd (D.ψ x)
    have h1 : Multiplicative.toAdd (D.ψ x) = D.ψe (x : G) := (D.ψe_of_mem hxV).symm
    rw [h1, hr₀φ, ← D.ψe_conj (H.lOf_mem a₀') hxV]
    have h2 := H.actsAs_lOf a₀' (x : G) hxV
    have h3 : (a₀ : G) * x * a₀⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.1 hxC a₀ ha₀
      rw [this, mul_inv_cancel_right]
    rw [← h2]
    exact congrArg D.ψe h3
  have hC₀idx : C₀.index = 2 ^ n := H.offender_data.2.1
  have hE₀idx : E₀.index = K₀.index := Subgroup.index_comap_of_surjective K₀ D.ψ_surj
  have hq0 : 0 < 2 ^ n := by positivity
  have hK₀pos : 0 < Nat.card ↥K₀ := Nat.card_pos
  have hge : 2 ^ n ≤ E₀.index := by
    have : (2 ^ n) * (2 ^ n) ≤ E₀.index * (2 ^ n) := by
      calc (2 ^ n) * (2 ^ n) = (2 ^ n) ^ 2 := by ring
        _ = K₀.index * Nat.card ↥K₀ := hK₀idx.symm
        _ ≤ K₀.index * (2 ^ n) := Nat.mul_le_mul_left _ hK₀card
        _ = E₀.index * (2 ^ n) := by rw [hE₀idx]
    exact Nat.le_of_mul_le_mul_right this hq0
  have hle : E₀.index ≤ C₀.index := by
    have := Subgroup.index_dvd_of_le hC₀E₀
    exact Nat.le_of_dvd (by rw [hC₀idx]; exact hq0) this
  have hEC : E₀.index = C₀.index := le_antisymm hle (by rw [hC₀idx]; exact hge)
  have hrel : C₀.relIndex E₀ = 1 := by
    have := Subgroup.relIndex_mul_index hC₀E₀
    rw [← hEC] at this
    have hpos : 0 < E₀.index := by rw [hEC, hC₀idx]; exact hq0
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [this, one_mul])
  have hEle : E₀ ≤ C₀ := Subgroup.relIndex_eq_one.1 hrel
  have hvE : (⟨v, hv⟩ : ↥(blockU L)) ∈ E₀ := by
    show D.ψ ⟨v, hv⟩ ∈ K₀
    show (r₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (Multiplicative.toAdd (D.ψ ⟨v, hv⟩)) = Multiplicative.toAdd (D.ψ ⟨v, hv⟩)
    rw [← D.ψe_of_mem hv]
    exact hfix
  exact hEle hvE

theorem mem_centralizer_of_fixed {v : G} (hv : v ∈ blockU L)
    (hfix : ∀ g ∈ H.rho.range, (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (H.block.natData.ψe v) = H.block.natData.ψe v) :
    v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) := by
  obtain ⟨a₀, ha₀, ha₀V⟩ : ∃ a₀ ∈ A, a₀ ∉ Subgroup.centralizer (blockU L : Set G) := by
    by_contra hcon
    push Not at hcon
    exact H.nontriv fun a ha => hcon a ha
  exact H.mem_centralizer_of_fixed_one ha₀ ha₀V hv (hfix _ ⟨⟨a₀, ha₀⟩, rfl⟩)

theorem inf_centralizer_le :
    A ⊓ Subgroup.centralizer (blockU L : Set G) ≤
      (A ⊓ Subgroup.centralizer (L : Set G)) ⊔ (blockU L ⊓ A) := by
  intro b hb
  let D := H.block.natData
  have hbU : b ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨H.A_le_M hb.1, hb.2⟩
  have hκ : D.κ b ∈ Z1A (mu2 (F := GaloisField 2 n)) := H.block.κ_mem_Z1A H.le H.normal hbU
  have hvan : ∀ g ∈ H.rho.range, D.κ b g = 0 := fun g hg => H.κ_eq_zero_of_mem_range hb hg
  have h2 : ∀ m : Fin 2 → GaloisField 2 n, m + m = 0 := fun m => by
    funext j
    exact CharTwo.add_self_eq_zero (m j)
  have hB1 : D.κ b ∈ B1A (mu2 (F := GaloisField 2 n)) :=
    mem_B1A_of_vanish h2 H.odd_index_range_rho hκ hvan
  obtain ⟨w, hw⟩ := hB1
  obtain ⟨v, hvV, hvw⟩ := D.exists_ψe w
  have hvinv : v⁻¹ ∈ blockU L := (blockU L).inv_mem hvV
  have hvU : v⁻¹ ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨H.le (blockU_le L hvinv), H.blockU_le_centralizer hvinv⟩
  have hcU : b * v⁻¹ ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := mul_mem hbU hvU
  have hκc : D.κ (b * v⁻¹) = 0 := by
    funext g
    rw [H.block.κ_mul_left H.normal hbU hvU g, H.block.κ_blockU hvinv g, D.ψe_inv hvV, hvw,
      ← hw]
    simp
  have hcC : b * v⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    (H.block.κ_eq_zero_iff H.le H.normal hcU).1 hκc
  have hfix : ∀ g ∈ H.rho.range, (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (D.ψe v) = D.ψe v := by
    intro g hg
    have h1 := hvan g hg
    rw [← hw, coboundaryA_apply, mu2_apply] at h1
    rw [hvw]
    exact sub_eq_zero.1 h1
  have hvCA := H.mem_centralizer_of_fixed hvV hfix
  rw [H.centralizer_blockU_eq] at hvCA
  have hcA : b * v⁻¹ ∈ A := A.mul_mem hb.1 (A.inv_mem hvCA.2)
  have e : b = (b * v⁻¹) * v := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨hcA, hcC⟩ hvCA

theorem inf_centralizer_eq :
    A ⊓ Subgroup.centralizer (blockU L : Set G) =
      (A ⊓ Subgroup.centralizer (L : Set G)) ⊔ (blockU L ⊓ A) := by
  refine le_antisymm H.inf_centralizer_le (sup_le ?_ ?_)
  · exact inf_le_inf_left A (Subgroup.centralizer_le (blockU_le L))
  · exact fun x hx => ⟨hx.2, H.blockU_le_centralizer hx.1⟩

theorem inf_centralizer_L_eq
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    A ⊓ Subgroup.centralizer (L : Set G) = T ⊓ Subgroup.centralizer (L : Set G) := by
  set S : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) with hSdef
  have hAS : A ⊓ Subgroup.centralizer (L : Set G) ≤ S := inf_le_inf_right _ H.A_le_T
  have hBeq : bGrp L A = (A ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
    unfold bGrp
    rw [H.inf_centralizer_eq]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right)
  have hcommVS : ∀ s ∈ S, ∀ v ∈ blockU L, s * v = v * s := fun s hs v hv =>
    (Subgroup.mem_centralizer_iff.1 hs.2 v (blockU_le L hv)).symm
  have hSV : IsElemAbelian 2 (S ⊔ blockU L) :=
    isElemAbelian_sup' hS H.block.isElemAbelian_blockU hcommVS
  have hSVT : S ⊔ blockU L ≤ T := sup_le inf_le_left H.V_le_T
  have hBle : bGrp L A ≤ S ⊔ blockU L := by
    rw [hBeq]
    exact sup_le_sup_right hAS _
  have hcard := H.isMaxElemAbelian_B.2.2 _ hSVT hSV
  have hBS : bGrp L A = S ⊔ blockU L := Subgroup.eq_of_le_of_card_ge hBle hcard
  refine le_antisymm hAS (fun s hs => ?_)
  have hsB : s ∈ bGrp L A := by
    rw [hBS]
    exact Subgroup.mem_sup_left hs
  rw [hBeq] at hsB
  have hcomm' : ∀ x ∈ A ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.1 hx.2 y (blockU_le L hy)).symm
  obtain ⟨c, hc, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm' hsB
  have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : v = c⁻¹ * (c * v) := by group
    rw [h1]
    exact (Subgroup.centralizer (L : Set G)).mul_mem
      ((Subgroup.centralizer (L : Set G)).inv_mem hc.2) hs.2
  have hvA : v ∈ A := H.blockZ_le_A ⟨hv, hvC⟩
  exact ⟨A.mul_mem hc.1 hvA, hs.2⟩

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
