
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModelBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem card_Z0_le :
    Nat.card Z0 ≤ 4 := by
  have hf : ∀ k : Fin 4, wordPerm (tg ([0, 4, 8, 12].get ⟨k.val, by simp⟩)) ∈ Z0 :=
    fun k => mem_Z0.2 ⟨_, List.get_mem _ _, rfl⟩
  have hs : Function.Surjective (fun k : Fin 4 => (⟨_, hf k⟩ : Z0)) := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hk
    exact ⟨⟨i.val, i.2⟩, rfl⟩
  have := Nat.card_le_card_of_surjective _ hs
  have h4 : Nat.card (Fin 4) = 4 := by simp
  rwa [h4] at this

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

namespace IsQSetting

theorem exists_psi
    (h : IsQSetting q l) {z : E} (hz : z ∈ q.ker) :
    ∃ d, psi l d = z := by
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 hz
  exact ⟨_, psi_ofAdd l i j⟩

theorem card_omega_ker_le
    [Finite E] (h : IsQSetting q l) :
    Nat.card {e : E // e ∈ q.ker ∧ e * e = 1} ≤ 4 := by
  have hcomm : ∀ x y : q.ker, x * y = y * x := fun x y => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_center_iff.mp (h.ker_le y.2) x)
  let sq : q.ker →* q.ker := MonoidHom.mk' (fun x => x * x) fun x y => by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y x]
      _ = x * x * (y * y) := by group
  have hker : Nat.card sq.ker = Nat.card {e : E // e ∈ q.ker ∧ e * e = 1} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun e => ⟨⟨e.1, e.2.1⟩, Subtype.ext e.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := Subgroup.card_ker_mul_card_range sq
  have hpsi : ∀ d, psi l d ∈ q.ker := h.psi_mem_ker
  have hsurj : Function.Surjective (fun x : (Fin 2 × Fin 2) × sq.range =>
      (⟨psi l (Multiplicative.ofAdd (x.1.1.val : ZMod 4),
        Multiplicative.ofAdd (x.1.2.val : ZMod 4)), hpsi _⟩ : q.ker) * x.2) := by
    rintro ⟨y, hy⟩
    obtain ⟨d, rfl⟩ := h.exists_psi hy
    obtain ⟨i, j, f, hf⟩ := decomp_D4 d
    refine ⟨((i, j), ⟨⟨psi l f, hpsi f⟩ * ⟨psi l f, hpsi f⟩, ⟨_, rfl⟩⟩), Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul]
    rw [hf, map_mul, map_mul]
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h2
  rw [← hker]
  have hpos : 0 < Nat.card sq.range := Nat.card_pos
  nlinarith

end IsQSetting

variable {G : Type} [Group G] {J P : Subgroup G} {q' : Jhat J →* Equiv.Perm (Fin 42)}

theorem card_le_sixteen
    [Finite G] {l : Cover →* Jhat J} (hQ : IsQSetting q' l) (hP : IsSylowTwoIn P J)
    {D : Subgroup G} (hDP : D ≤ P) (hDe : IsElemTwo D)
    (hDZ : ∀ {d : G} (hd : d ∈ D), q' (jq J ⟨d, hP.1 (hDP hd)⟩) ∈ Z0) : Nat.card D ≤ 16 := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  set φ : D →* Equiv.Perm (Fin 42) := (q'.comp (jq J)).comp (Subgroup.inclusion (hDP.trans hP.1))
    with hφ
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hr : Nat.card φ.range ≤ 4 := by
    refine (Subgroup.card_le_of_le ?_).trans card_Z0_le
    rintro _ ⟨d, rfl⟩
    exact hDZ d.2
  have hk : Nat.card φ.ker ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun d => (⟨jq J ⟨d.1.1, hP.1 (hDP d.1.2)⟩, d.2, ?_⟩ :
        {e : Jhat J // e ∈ q'.ker ∧ e * e = 1})) fun a b hab => ?_) hQ.card_omega_ker_le
    · rw [← map_mul]
      have : (⟨d.1.1, hP.1 (hDP d.1.2)⟩ : J) * ⟨d.1.1, hP.1 (hDP d.1.2)⟩ = 1 :=
        Subtype.ext (hDe.2 _ d.1.2)
      rw [this, map_one]
    · have h2 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (eq_of_jq_eq hP.1 hP2 (hDP a.1.2) (hDP b.1.2) h2))
  rw [← h1]
  exact (Nat.mul_le_mul hk hr).trans (by norm_num)

end CFSG.ComponentClassification.GrSLit.L34Facts
