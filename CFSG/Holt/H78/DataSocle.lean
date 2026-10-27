module

public import CFSG.Holt.H78.DataTransport

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise commutatorElement

section General

variable {X : Type*} [Group X]

private theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup X] (h : ¬ IsMulCommutative X) :
    Subgroup.center X = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right fun h' =>
    h (isMulCommutative_iff.mpr fun a b => ?_)
  exact (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b) a)

private theorem le_normalizer_inf {K A B : Subgroup X} (hA : K ≤ Subgroup.normalizer (A : Set X))
    (hB : K ≤ Subgroup.normalizer (B : Set X)) : K ≤ Subgroup.normalizer ((A ⊓ B : Subgroup X) :
      Set X) := fun x hx => Subgroup.mem_normalizer_iff.mpr fun y => by
  simp only [Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hA hx) y)
    (Subgroup.mem_normalizer_iff.mp (hB hx) y)

end General

section Quotient

variable {G : Type*} [Group G] {O L : Subgroup G} [O.Normal]

theorem eq_or_eq_of_isSimpleGroup_quotient [IsSimpleGroup (L ⧸ O.subgroupOf L)]
    {N : Subgroup G} (hON : O ≤ N) (hNL : N ≤ L) (hN : L ≤ Subgroup.normalizer (N : Set G)) :
    N = O ∨ N = L := by
  have hNn : (N.subgroupOf L).Normal :=
    ⟨fun n hn l => (Subgroup.mem_normalizer_iff.mp (hN l.2) n).mp hn⟩
  set π := QuotientGroup.mk' (O.subgroupOf L)
  have := hNn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map π) with h | h
  · refine Or.inl (le_antisymm (fun n hn => ?_) hON)
    have hm : π ⟨n, hNL hn⟩ ∈ (N.subgroupOf L).map π := ⟨⟨n, hNL hn⟩, hn, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
    exact hm
  · refine Or.inr (le_antisymm hNL fun l hl => ?_)
    obtain ⟨n, hn, hnl⟩ := h.ge (Subgroup.mem_top (π ⟨l, hl⟩))
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have hmem : ((n⁻¹ * ⟨l, hl⟩ : L) : G) ∈ N := hON hnl
    have hl' : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : L) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hl']
    exact N.mul_mem hn hmem

theorem isMulCommutative_quotient_of_commutator_le (h : ⁅L, L⁆ ≤ O) :
    IsMulCommutative (L ⧸ O.subgroupOf L) := by
  refine isMulCommutative_iff.mpr fun a b => ?_
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hc := Subgroup.commutator_le.mp h _ (y⁻¹).2 _ (x⁻¹).2
  rw [commutatorElement_def] at hc
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc] using hc

private theorem commutator_self_le (L : Subgroup G) : ⁅L, L⁆ ≤ L :=
  Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)

theorem not_le_of_isSimpleGroup_quotient [IsSimpleGroup (L ⧸ O.subgroupOf L)] : ¬ L ≤ O := by
  intro hLO
  obtain ⟨a, ha⟩ := exists_ne (1 : L ⧸ O.subgroupOf L)
  induction a using QuotientGroup.induction_on with | H x => ?_
  exact ha ((QuotientGroup.eq_one_iff x).mpr (hLO x.2))

end Quotient

section Component

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

structure IsJComponent (L : Subgroup G) : Prop where
  oddCore_le : jOddCore G Ω ≤ L
  le_jHull : L ≤ jHull G Ω
  le_normalizer : jHull G Ω ≤ Subgroup.normalizer (L : Set G)
  isSimpleGroup : IsSimpleGroup (L ⧸ (jOddCore G Ω).subgroupOf L)
  not_isMulCommutative : ¬ IsMulCommutative (L ⧸ (jOddCore G Ω).subgroupOf L)

variable {G Ω} {L : Subgroup G}

theorem IsJComponent.eq_or_eq (hL : IsJComponent G Ω L) {N : Subgroup G}
    (hON : jOddCore G Ω ≤ N) (hNL : N ≤ L) (hN : L ≤ Subgroup.normalizer (N : Set G)) :
    N = jOddCore G Ω ∨ N = L := by
  have := hL.isSimpleGroup
  exact eq_or_eq_of_isSimpleGroup_quotient hON hNL hN

theorem IsJComponent.not_commutator_le (hL : IsJComponent G Ω L) :
    ¬ ⁅L, L⁆ ≤ jOddCore G Ω :=
  fun h => hL.not_isMulCommutative (isMulCommutative_quotient_of_commutator_le h)

end Component

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem ker_rho_comp_inclusion (i : D.ι) :
    ((D.ρ i).comp (Subgroup.inclusion (D.L_le i))).ker = (jOddCore G Ω).subgroupOf (D.L i) := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  exact ⟨fun h => mem_jOddCore_of_mem_L (h := Subgroup.inclusion (D.L_le i) x) x.2 h,
    fun h => rho_eq_one_of_mem_jOddCore (h := Subgroup.inclusion (D.L_le i) x) h i⟩

theorem range_rho_comp_inclusion (i : D.ι) :
    ((D.ρ i).comp (Subgroup.inclusion (D.L_le i))).range = D.M i := by
  ext x
  rw [MonoidHom.mem_range, mem_M]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion (D.L_le i) l, l.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

@[expose] noncomputable def quotientEquivM (i : D.ι) :
    D.L i ⧸ (jOddCore G Ω).subgroupOf (D.L i) ≃* D.M i :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_rho_comp_inclusion i).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (D.range_rho_comp_inclusion i)))

@[simp] theorem coe_quotientEquivM_mk (i : D.ι) (l : D.L i) :
    (D.quotientEquivM i (QuotientGroup.mk l) : Equiv.Perm (D.Ψc i)) =
      D.ρ i (Subgroup.inclusion (D.L_le i) l) :=
  rfl

theorem isJComponent_L (i : D.ι) : IsJComponent G Ω (D.L i) where
  oddCore_le := D.oddCore_le i
  le_jHull := D.L_le i
  le_normalizer := D.le_normalizer i
  isSimpleGroup := by
    have := D.isSimpleGroup_M i
    exact (D.quotientEquivM i).isSimpleGroup
  not_isMulCommutative h := D.not_isMulCommutative_M i (isMulCommutative_iff.mpr fun a b =>
    (D.quotientEquivM i).symm.injective (by rw [map_mul, map_mul, mul_comm']))

theorem eq_jOddCore_or_eq_L (i : D.ι) {N : Subgroup G} (hON : jOddCore G Ω ≤ N)
    (hNL : N ≤ D.L i) (hN : D.L i ≤ Subgroup.normalizer (N : Set G)) :
    N = jOddCore G Ω ∨ N = D.L i :=
  (D.isJComponent_L i).eq_or_eq hON hNL hN

theorem commutator_jHull_le_socPre : ⁅jHull G Ω, jHull G Ω⁆ ≤ D.socPre := by
  have := D.normal_socPre_subgroupOf
  have hcard : Nat.card (jHull G Ω ⧸ D.socPre.subgroupOf (jHull G Ω)) ∣ 2 :=
    D.relIndex_socPre_jHull_dvd_two
  have hcomm : ∀ a b : jHull G Ω ⧸ D.socPre.subgroupOf (jHull G Ω), a * b = b * a := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h2
    · have := (Nat.card_eq_one_iff_unique.mp h1).1
      exact fun a b => Subsingleton.elim _ _
    · have := isCyclic_of_prime_card (hp := ⟨Nat.prime_two⟩) h2
      exact fun a b => (IsCyclic.commGroup).mul_comm a b
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  have h := (QuotientGroup.eq_one_iff (N := D.socPre.subgroupOf (jHull G Ω))
    (⁅(⟨x, hx⟩ : jHull G Ω), ⟨y, hy⟩⁆)).mp (by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _)
  rw [Subgroup.mem_subgroupOf] at h
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h

end HoltData

section Identify

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {L : Subgroup G}

theorem IsJComponent.le_socPre (hL : IsJComponent G Ω L) (D : HoltData G Ω) :
    L ≤ D.socPre := by
  have := hL.isSimpleGroup
  rcases eq_or_eq_of_isSimpleGroup_quotient (O := jOddCore G Ω) (L := L)
      (le_inf hL.oddCore_le D.jOddCore_le_socPre) inf_le_left
      (le_normalizer_inf (hL.le_jHull.trans hL.le_normalizer)
        (hL.le_jHull.trans D.le_normalizer_socPre)) with h | h
  · refine absurd (isMulCommutative_quotient_of_commutator_le ?_) hL.not_isMulCommutative
    rw [← h]
    exact le_inf (commutator_self_le L)
      ((Subgroup.commutator_mono hL.le_jHull hL.le_jHull).trans D.commutator_jHull_le_socPre)
  · rw [← h]
    exact inf_le_right

namespace HoltData

variable (D : HoltData G Ω)

theorem exists_eq_L_of_isJComponent (hL : IsJComponent G Ω L) : ∃ i, L = D.L i := by
  have := hL.isSimpleGroup
  by_contra! hne
  have hLs := hL.le_socPre D
  have hinf : ∀ i, L ⊓ D.L i ≤ jOddCore G Ω := fun i => by
    rcases eq_or_eq_of_isSimpleGroup_quotient (O := jOddCore G Ω) (L := L)
        (le_inf hL.oddCore_le (D.oddCore_le i)) inf_le_left
        (le_normalizer_inf (hL.le_jHull.trans hL.le_normalizer)
          (hL.le_jHull.trans (D.le_normalizer i))) with h | h
    · exact h.le
    · have hLi : L ≤ D.L i := by
        rw [← h]
        exact inf_le_right
      rcases D.eq_jOddCore_or_eq_L i hL.oddCore_le hLi
          ((D.L_le i).trans hL.le_normalizer) with h' | h'
      · exact absurd h'.le not_le_of_isSimpleGroup_quotient
      · exact absurd h' (hne i)
  have hrho : ∀ x (hx : x ∈ L) i, D.ρ i ⟨x, hL.le_jHull hx⟩ = 1 := by
    intro x hx i
    have hxM := rho_mem_M_of_mem_socPre (D := D) (h := ⟨x, hL.le_jHull hx⟩) (hLs hx) i
    have hcen : (⟨_, hxM⟩ : D.M i) ∈ Subgroup.center (D.M i) := by
      refine Subgroup.mem_center_iff.mpr fun ⟨m, hm⟩ => Subtype.ext ?_
      obtain ⟨y, hy, rfl⟩ := mem_M.mp hm
      have hyL : (y : G) * x⁻¹ * (y : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hL.le_normalizer y.2) x⁻¹).mp (L.inv_mem hx)
      have hxy : x * y * x⁻¹ ∈ D.L i :=
        (Subgroup.mem_normalizer_iff.mp (D.le_normalizer i (hL.le_jHull hx)) y).mp hy
      have hxyL : x * y * x⁻¹ * (y : G)⁻¹ ∈ L := by
        simpa only [mul_assoc] using L.mul_mem hx hyL
      have hc : x * y * x⁻¹ * (y : G)⁻¹ ∈ jOddCore G Ω :=
        hinf i (Subgroup.mem_inf.mpr ⟨hxyL, (D.L i).mul_mem hxy ((D.L i).inv_mem hy)⟩)
      have h1 := rho_eq_one_of_mem_jOddCore (D := D)
        (h := ⟨x, hL.le_jHull hx⟩ * y * ⟨x, hL.le_jHull hx⟩⁻¹ * y⁻¹) hc i
      simp only [map_mul, map_inv] at h1
      simp only [Subgroup.coe_mul]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have := D.isSimpleGroup_M i
    rw [center_eq_bot_of_isSimpleGroup (D.not_isMulCommutative_M i)] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcen)
  refine not_le_of_isSimpleGroup_quotient (O := jOddCore G Ω) (L := L) fun x hx => ?_
  rw [← D.socPre_inf_jOrbitKernel]
  exact ⟨hLs hx, (mem_jOrbitKernel_iff_rho (D := D) (h := ⟨x, hL.le_jHull hx⟩)).mpr
    (hrho x hx)⟩

end HoltData

end Identify

namespace HoltData

section Unique

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem L_injective : Function.Injective D.L := by
  intro i j hij
  by_contra hne
  have := D.isSimpleGroup_M j
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : D.M j)
  obtain ⟨h, hh, rfl⟩ := mem_M.mp hx
  exact hx1 (Subtype.ext (rho_eq_one_of_mem_L hne (hij ▸ hh)))

theorem exists_equiv_L_eq (D D' : HoltData G Ω) : ∃ σ : D.ι ≃ D'.ι, ∀ i, D'.L (σ i) = D.L i := by
  choose f hf using fun i => D'.exists_eq_L_of_isJComponent (D.isJComponent_L i)
  refine ⟨Equiv.ofBijective f ⟨fun i j hij => D.L_injective ?_, fun j => ?_⟩,
    fun i => (hf i).symm⟩
  · rw [hf i, hf j, hij]
  · obtain ⟨i, hi⟩ := D.exists_eq_L_of_isJComponent (D'.isJComponent_L j)
    exact ⟨i, D'.L_injective ((hf i).symm.trans hi.symm)⟩

end Unique

section Conj

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
  {G' : Type*} [Group G'] {Ω' : Type*} [MulAction G' Ω']

theorem congr_L (D : HoltData G Ω) (φ : G ≃* G') (e : Ω ≃ Ω')
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = φ g • e ω) (i : D.ι) :
    (D.congr φ e he).L i = (D.L i).map φ.toMonoidHom := by
  ext g'
  rw [Subgroup.mem_map]
  change g' ∈ hullMap _ (D.L i) ↔ _
  rw [mem_hullMap]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, D.L_le i hx⟩, hx, rfl⟩

theorem exists_equiv_L_map (D : HoltData G Ω) (D' : HoltData G' Ω') (φ : G ≃* G') (e : Ω ≃ Ω')
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = φ g • e ω) :
    ∃ σ : D.ι ≃ D'.ι, ∀ i, D'.L (σ i) = (D.L i).map φ.toMonoidHom := by
  obtain ⟨σ, hσ⟩ := exists_equiv_L_eq (D.congr φ e he) D'
  exact ⟨σ, fun i => (hσ i).trans (D.congr_L φ e he i)⟩

theorem conj_L (D : HoltData G Ω) (g : G) :
    ∃ σ : D.ι ≃ D.ι, ∀ i, D.L (σ i) = (D.L i).map (MulAut.conj g).toMonoidHom :=
  exists_equiv_L_map D D (MulAut.conj g) (MulAction.toPerm g) fun x ω => by
    rw [MulAut.conj_apply, MulAction.toPerm_apply, MulAction.toPerm_apply, mul_smul, mul_smul,
      inv_smul_smul]

end Conj

end HoltData

end CFSG.Holt.H78
