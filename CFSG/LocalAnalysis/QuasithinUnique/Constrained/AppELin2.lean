module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalLin2

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

theorem lin2_commutator_inf_Z {L T : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT : IsSylowTwoOf T L) :
    ∀ t ∈ T, t ∉ blockQ L → ∀ u ∈ blockU L, ⁅u, t⁆ ∈ blockZ L → ⁅u, t⁆ = 1 := by
  classical
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hq
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hLN : L ≤ normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  let conjL : ↥L →* MulAut ↥(blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hconjL : ∀ (l : L) (u : blockU L), ((conjL l u : blockU L) : G) = l * u * l⁻¹ :=
    fun l u => rfl
  have hkerle : α.ker ≤ conjL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rw [hconjL, MulAut.one_apply]
    have hlQ : (l : G) ∈ blockQ L := (C56.mem_blockQ_iff l).mpr (hαk ▸ hl)
    have := C1.blockU_comm hL u u.2 l hlQ
    rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    exact this.symm
  let act : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut ↥(blockU L) :=
    MonoidHom.liftOfRightInverse α (Function.surjInv hαs) (Function.rightInverse_surjInv hαs)
      ⟨conjL, hkerle⟩
  have hact : ∀ l : L, act (α l) = conjL l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨conjL, hkerle⟩ l
  have hactc : ∀ (l : L) (u : blockU L), ((act (α l) u : blockU L) : G) = l * u * l⁻¹ := by
    intro l u
    rw [hact, hconjL]
  let hCG : CommGroup ↥(blockU L) :=
    { (inferInstance : Group ↥(blockU L)) with
      mul_comm := fun a b => Subtype.ext (hUab _ a.2 _ b.2) }
  have hIs : IsNatPlane act β := by
    refine ⟨?_, hβs, ?_, ?_⟩
    · intro e
      apply Subtype.ext
      have := C1.blockU_sq hL e e.2
      simpa [pow_two] using this
    · intro g e
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact hβe l e (conjL l e) (hconjL l e)
    · intro g e he
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      have heZ : (e : G) ∈ blockZ L := by
        have : e ∈ (blockZ L).subgroupOf (blockU L) := hβk ▸ he
        exact this
      apply Subtype.ext
      rw [hconjL]
      have := Subgroup.mem_centralizer_iff.mp heZ.2 (l : G) l.2
      rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      exact this
  have hEL : commSub act Set.univ ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro e _
    have hUK : blockU L ≤ (commSub act Set.univ ⊤).map (blockU L).subtype := by
      refine (C1.commutator_blockU hL).symm.le.trans ?_
      rw [Subgroup.commutator_le]
      intro u hu l hl
      have hgen : act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹ ∈ commSub act Set.univ ⊤ :=
        Subgroup.subset_closure ⟨α ⟨l, hl⟩, Set.mem_univ _, ⟨u, hu⟩, Subgroup.mem_top _, rfl⟩
      refine ⟨(act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹)⁻¹, inv_mem hgen, ?_⟩
      show (((act (α ⟨l, hl⟩) ⟨u, hu⟩ * (⟨u, hu⟩ : blockU L)⁻¹)⁻¹ : blockU L) : G) = ⁅u, l⁆
      rw [commutatorElement_def]
      simp [hactc]
      group
    obtain ⟨k, hk, hke⟩ := hUK e.2
    have : k = e := Subtype.ext hke
    rwa [this] at hk
  obtain ⟨-, hpall⟩ := saturated_natural_plane_root_fixed_space (k := F) (E := ↥(blockU L)) hn hq
    hIs hEL
  obtain ⟨p, hTp, hT2⟩ := C56.lin2_exists_point hn hT hq α hαs hαk
  intro t ht htQ u hu hZ
  have htL : t ∈ L := hT.le ht
  have hα1 : α ⟨t, htL⟩ ≠ 1 := fun h => htQ ((C56.mem_blockQ_iff ⟨t, htL⟩).2
    (by rw [← hαk]; exact h))
  have hαp : α ⟨t, htL⟩ ∈ rootGrp p := (hT2 _).mpr ht
  obtain ⟨-, -, -, hts, -, -⟩ := hpall p
  have hinf := (hts _ hαp hα1).2.2.2
  set e : ↥(blockU L) := ⟨u, hu⟩ with he
  have hd : ((e * (act (α ⟨t, htL⟩) e)⁻¹ : blockU L) : G) = ⁅u, t⁆ := by
    show (e : G) * ((act (α ⟨t, htL⟩) e : blockU L) : G)⁻¹ = _
    rw [hactc, commutatorElement_def]
    simp [he, mul_assoc]
  have hmem : e * (act (α ⟨t, htL⟩) e)⁻¹ ∈ (actDiff act (α ⟨t, htL⟩)).range := by
    have : e * (act (α ⟨t, htL⟩) e)⁻¹ = (actDiff act (α ⟨t, htL⟩) e)⁻¹ := by
      show _ = (act (α ⟨t, htL⟩) e * e⁻¹)⁻¹
      rw [mul_inv_rev, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ ⟨e, rfl⟩
  have hker : e * (act (α ⟨t, htL⟩) e)⁻¹ ∈ β.ker := by
    rw [hβk]
    show ((e * (act (α ⟨t, htL⟩) e)⁻¹ : blockU L) : G) ∈ blockZ L
    rw [hd]
    exact hZ
  have hbot : e * (act (α ⟨t, htL⟩) e)⁻¹ ∈ (⊥ : Subgroup ↥(blockU L)) := by
    rw [← hinf]
    exact ⟨hmem, hker⟩
  rw [Subgroup.mem_bot] at hbot
  rw [← hd, hbot]
  rfl

theorem lin2_B_commutator_inf_Z {L B Q : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hTsyl : IsSylowTwoOf (B ⊓ L) L) (hQ : Q = B ⊓ centralizer (blockU L : Set G))
    (hBTQ : B ≤ (B ⊓ L) ⊔ Q) (hLQ : L ≤ normalizer (Q : Set G)) :
    ∀ y ∈ B, y ∉ Q → ∀ u ∈ blockU L, ⁅u, y⁆ ∈ blockZ L → ⁅u, y⁆ = 1 := by
  intro y hy hyQ u hu hZ
  have hTQ : B ⊓ L ≤ normalizer (Q : Set G) := fun g hg => hLQ hg.2
  obtain ⟨t₀, ht₀, c, hc, rfl⟩ := C5.mem_sup_of_le_normalizer hTQ (hBTQ hy)
  have hcU : c ∈ centralizer (blockU L : Set G) := by
    rw [hQ] at hc; exact hc.2
  have hcomm : ⁅u, t₀ * c⁆ = ⁅u, t₀⁆ := by
    have hcu : c * u⁻¹ = u⁻¹ * c := by
      have := Subgroup.mem_centralizer_iff.mp hcU u⁻¹ ((blockU L).inv_mem hu)
      exact this.symm
    simp only [commutatorElement_def]
    calc u * (t₀ * c) * u⁻¹ * (t₀ * c)⁻¹ = u * t₀ * (c * u⁻¹) * c⁻¹ * t₀⁻¹ := by group
      _ = u * t₀ * (u⁻¹ * c) * c⁻¹ * t₀⁻¹ := by rw [hcu]
      _ = u * t₀ * u⁻¹ * t₀⁻¹ := by group
  rw [hcomm] at hZ ⊢
  have ht₀Q : t₀ ∉ blockQ L := by
    intro h
    apply hyQ
    have h1 : t₀ ∈ Q := by
      rw [hQ]
      exact ⟨ht₀.1, Subgroup.mem_centralizer_iff.mpr fun v hv => (C1.blockU_comm hL v hv t₀ h)⟩
    exact Q.mul_mem h1 hc
  exact lin2_commutator_inf_Z hL hn hlin hTsyl t₀ ht₀ ht₀Q u hu hZ

end CFSG.QuasithinUnique.AppE
