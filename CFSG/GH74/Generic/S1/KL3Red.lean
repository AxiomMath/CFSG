module

public import CFSG.GH74.Generic.S1.TQ3BarVert
public import CFSG.GH74.Generic.S1.TQ3BarGeom

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1


theorem kl3_inf_center_eq_bot {M : Type} [Group M] {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) {P : Subgroup M} (e : P ≃* SL(3, F)) : P ⊓ center M = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxZ⟩
  have hc : e ⟨x, hxP⟩ ∈ center SL(3, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hxZ (e.symm g : M)
    have h2 : (e.symm g) * (⟨x, hxP⟩ : P) = (⟨x, hxP⟩ : P) * (e.symm g) := Subtype.ext h1
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3
  rw [center_sl3_three hF3, Subgroup.mem_bot] at hc
  have : (⟨x, hxP⟩ : P) = 1 := e.injective (by rw [hc, map_one])
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)



theorem kl3_solvable_bar {M : Type} [Group M] [Finite M] {y : M}
    (h : Group.IsSolvable ↥(centralizer ({y} : Set M))) :
    Group.IsSolvable ↥(centralizer ({(QuotientGroup.mk y : M ⧸ center M)} : Set (M ⧸ center M))) := by
  classical
  let π : M →* M ⧸ center M := QuotientGroup.mk' (center M)
  let Ct : Subgroup M := (centralizer ({π y} : Set (M ⧸ center M))).comap π
  have hCt : ∀ g : M, g ∈ Ct ↔ π g ∈ centralizer ({π y} : Set (M ⧸ center M)) := fun g => Iff.rfl
  have hmem : ∀ g : Ct, (g : M) * y * (g : M)⁻¹ * y⁻¹ ∈ center M := by
    intro g
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 ((hCt g).1 g.2)
    rw [← QuotientGroup.eq_one_iff (N := center M)]
    have h2 : π g * π y = π y * π g := h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change π g * π y * (π g)⁻¹ * (π y)⁻¹ = 1
    rw [h2]
    group
  let θ : Ct →* center M := MonoidHom.mk' (fun g => ⟨(g : M) * y * (g : M)⁻¹ * y⁻¹, hmem g⟩) (by
    intro a b
    apply Subtype.ext
    have hb := Subgroup.mem_center_iff.1 (hmem b) (a : M)
    show (a : M) * (b : M) * y * ((a : M) * (b : M))⁻¹ * y⁻¹ =
      ((a : M) * y * (a : M)⁻¹ * y⁻¹) * ((b : M) * y * (b : M)⁻¹ * y⁻¹)
    have hb' : (a : M) * ((b : M) * y * (b : M)⁻¹ * y⁻¹) =
        ((b : M) * y * (b : M)⁻¹ * y⁻¹) * (a : M) := hb
    have hb2 := Subgroup.mem_center_iff.1 (hmem b) ((a : M) * y * (a : M)⁻¹ * y⁻¹)
    calc (a : M) * (b : M) * y * ((a : M) * (b : M))⁻¹ * y⁻¹
        = (a : M) * ((b : M) * y * (b : M)⁻¹ * y⁻¹) * (y * (a : M)⁻¹ * y⁻¹) := by group
      _ = ((b : M) * y * (b : M)⁻¹ * y⁻¹) * (a : M) * (y * (a : M)⁻¹ * y⁻¹) := by rw [hb']
      _ = ((b : M) * y * (b : M)⁻¹ * y⁻¹) * ((a : M) * y * (a : M)⁻¹ * y⁻¹) := by group
      _ = ((a : M) * y * (a : M)⁻¹ * y⁻¹) * ((b : M) * y * (b : M)⁻¹ * y⁻¹) := hb2.symm)
  have hle : centralizer ({y} : Set M) ≤ Ct := by
    intro g hg
    rw [hCt, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 hg
    change π g * π y = π y * π g
    rw [← map_mul, ← map_mul, this]
  have hsolvCt : Group.IsSolvable Ct := by
    have : Group.IsSolvable ↥(center M) := inferInstance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) θ ?_
    intro g hg
    have hg1 : (g : M) * y * (g : M)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
    refine ⟨⟨g, ?_⟩, Subtype.ext rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g : M) * y = (g * y * (g : M)⁻¹ * y⁻¹) * y * g := by group
      _ = y * g := by rw [hg1]; group
  let ρ : Ct →* ↥(centralizer ({π y} : Set (M ⧸ center M))) :=
    ((π.comp Ct.subtype).codRestrict _ (fun g => (hCt g).1 g.2))
  have hρ : Function.Surjective ρ := by
    rintro ⟨s, hs⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨⟨m, (hCt m).2 hs⟩, Subtype.ext rfl⟩
  exact Group.isSolvable_of_surjective hρ



@[expose] noncomputable def kl3BarAut (M : Type) [Group M] : MulAut M →* MulAut (M ⧸ center M) where
  toFun α := QuotientGroup.congr (center M) (center M) α (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem kl3BarAut_mk {M : Type} [Group M] (α : MulAut M) (m : M) :
    kl3BarAut M α (QuotientGroup.mk m) = QuotientGroup.mk (α m) := rfl

theorem kl3_eq_one_of_bar {M : Type} [Group M] (hM : Group.IsPerfect M) {α : MulAut M}
    (h : kl3BarAut M α = 1) : α = 1 := by
  have hmem : ∀ m : M, m⁻¹ * α m ∈ center M := by
    intro m
    rw [← QuotientGroup.eq_one_iff (N := center M)]
    have h1 := kl3BarAut_mk α m
    rw [h] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h1]
    simp
  let ζ : M →* center M := MonoidHom.mk' (fun m => ⟨m⁻¹ * α m, hmem m⟩) (by
    intro a b
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.1 (hmem a) (b⁻¹)
    show (a * b)⁻¹ * α (a * b) = (a⁻¹ * α a) * (b⁻¹ * α b)
    calc (a * b)⁻¹ * α (a * b) = b⁻¹ * (a⁻¹ * α a) * α b := by rw [map_mul]; group
      _ = (a⁻¹ * α a) * b⁻¹ * α b := by rw [h1]
      _ = (a⁻¹ * α a) * (b⁻¹ * α b) := by group)
  have hker : commutator M ≤ ζ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (ζ a).2 (ζ b : M)).symm)
  rw [hM.commutator_eq_top, top_le_iff] at hker
  ext m
  have h1 : ζ m = 1 := by
    have : m ∈ ζ.ker := by rw [hker]; trivial
    exact this
  have h2 : m⁻¹ * α m = 1 := congrArg Subtype.val h1
  have : α m = m := by
    calc α m = m * (m⁻¹ * α m) := by group
      _ = m := by rw [h2, mul_one]
  simpa using this

theorem kl3_comm_mul_central_left {M : Type} [Group M] {g h z : M} (hz : z ∈ center M) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have h1 := Subgroup.mem_center_iff.1 hz h
  simp only [commutatorElement_def]
  calc g * z * h * (g * z)⁻¹ * h⁻¹ = g * (z * h) * z⁻¹ * g⁻¹ * h⁻¹ := by group
    _ = g * (h * z) * z⁻¹ * g⁻¹ * h⁻¹ := by rw [h1]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem kl3_comm_mul_central_right {M : Type} [Group M] {g h z : M} (hz : z ∈ center M) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have h1 := Subgroup.mem_center_iff.1 hz g⁻¹
  simp only [commutatorElement_def]
  calc g * (h * z) * g⁻¹ * (h * z)⁻¹ = g * h * (z * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * z) * z⁻¹ * h⁻¹ := by rw [← h1]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem kl3_eq_top_of_map_eq_top {M : Type} [Group M] (hM : Group.IsPerfect M) {P : Subgroup M}
    (hP : P.map (QuotientGroup.mk' (center M)) = ⊤) : P = ⊤ := by
  have hdec : ∀ m : M, ∃ p ∈ P, ∃ z ∈ center M, m = p * z := by
    intro m
    have : QuotientGroup.mk' (center M) m ∈ P.map (QuotientGroup.mk' (center M)) := by
      rw [hP]; trivial
    obtain ⟨p, hp, hpm⟩ := Subgroup.mem_map.1 this
    refine ⟨p, hp, p⁻¹ * m, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff (N := center M)]
    have : (QuotientGroup.mk p : M ⧸ center M) = QuotientGroup.mk m := hpm
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, this]
    simp
  have hle : commutator M ≤ P := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨p, hp, z, hz, rfl⟩ := hdec a
    obtain ⟨q, hq, w, hw, rfl⟩ := hdec b
    rw [kl3_comm_mul_central_left hz, kl3_comm_mul_central_right hw, commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp)) (P.inv_mem hq)
  rw [hM.commutator_eq_top, top_le_iff] at hle
  exact hle


@[expose] def KL3Classify : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → GHList S →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 →
      ∀ Pb : Subgroup S, Nonempty (↥Pb ≃* SL(3, F)) → ∀ yb ∈ Pb, orderOf yb = 2 →
        Group.IsSolvable ↥(centralizer ({yb} : Set S)) →
          Nat.card S = 5616 ∨ LieModel S .PSL 4 3 1 ∨ LieModel S .G2 0 3 1

@[expose] def KL3Surv : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (LieModel S .PSL 4 3 1 ∨ LieModel S .G2 0 3 1) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 →
      ∀ Pb : Subgroup S, Nonempty (↥Pb ≃* SL(3, F)) →
        (∀ α : MulAut S, Odd (orderOf α) → (∀ p ∈ Pb, α p = p) → α = 1) ∧
          ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 2 E ∧ 4 < Nat.card E

theorem kl3Table_of_parts (hC : KL3Classify) (hS : KL3Surv) : KL3Table := by
  classical
  intro M _ _ hMq hGH F _ _ hF3 P hPe y hyP hy2 hsolv
  obtain ⟨e⟩ := hPe
  let π : M →* M ⧸ center M := QuotientGroup.mk' (center M)
  have hinf := kl3_inf_center_eq_bot hF3 e
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : M) ∈ center M := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : M) ∈ P ⊓ center M := ⟨x.2, hx1⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  let Pb : Subgroup (M ⧸ center M) := (π.comp P.subtype).range
  have hPb : Pb = P.map π := by
    simp [Pb, MonoidHom.range_comp, Subgroup.range_subtype]
  let eb : ↥Pb ≃* SL(3, F) := (MonoidHom.ofInjective hinj).symm.trans e
  have hyb : (π y) ∈ Pb := ⟨⟨y, hyP⟩, rfl⟩
  have hyb2 : orderOf (π y) = 2 := by
    have h1 : orderOf ((π.comp P.subtype) ⟨y, hyP⟩) = orderOf (⟨y, hyP⟩ : P) :=
      orderOf_injective _ hinj _
    rw [← hy2]
    simpa [Subgroup.orderOf_mk] using h1
  have hsolvb := kl3_solvable_bar hsolv
  have hsimple : IsSimpleGroup (M ⧸ center M) := hMq.2.1
  have hperf : Group.IsPerfect M := hMq.1
  have hcls := hC (M ⧸ center M) hsimple hGH F hF3 Pb ⟨eb⟩ (π y) hyb hyb2 hsolvb
  rcases hcls with hcard | hsurv
  · left
    apply kl3_eq_top_of_map_eq_top hperf
    rw [← hPb]
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, Nat.card_congr eb.toEquiv, card_sl3_three hF3]
  · right
    obtain ⟨hAut, E, hE, hEc⟩ := hS (M ⧸ center M) hsurv F hF3 Pb ⟨eb⟩
    refine ⟨?_, E, hE, hEc⟩
    intro α hαodd hαfix
    apply kl3_eq_one_of_bar hperf
    apply hAut
    · exact Odd.of_dvd_nat hαodd (orderOf_map_dvd _ _)
    · rintro _ ⟨⟨p, hp⟩, rfl⟩
      show kl3BarAut M α (QuotientGroup.mk p) = QuotientGroup.mk p
      rw [kl3BarAut_mk, hαfix p hp]


end CFSG.GH74.Generic.S1
