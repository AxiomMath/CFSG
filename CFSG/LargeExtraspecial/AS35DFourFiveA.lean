module

public import CFSG.LargeExtraspecial.AS35DFourNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def rhoL {x : G} (hxM : x ∈ S.M) : S.Qt ≃ₗ[ZMod 2] S.Qt :=
  ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)

theorem rhoL_cl {x : G} (hxM : x ∈ S.M) {y : G} (hy : y ∈ S.QG) :
    S.rhoL hxM (S.cl y) = S.cl (x * y * x⁻¹) :=
  S.ρ_cl ⟨x, hxM⟩ hy

theorem rhoL_mem {x : G} (hxM : x ∈ S.M) :
    S.rhoL hxM ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨x, hxM⟩).2

theorem rhoL_mul_self {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) :
    S.rhoL hxM * S.rhoL hxM = 1 :=
  S.ρ_mul_self hxM (by rw [pow_two]; exact hxx)

theorem rhoL_ne_one {x : G} (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) : S.rhoL hxM ≠ 1 := by
  intro h
  apply hxQ
  exact (S.ρ_eq_one_iff ⟨x, hxM⟩).mp (Subtype.ext h)

theorem conj_eq_inv_of_cl_mem_commSpace {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1) {u : G}
    (hu : u ∈ S.QG) (hcu : S.cl u ∈ commSpace (S.rhoL hxM)) : x * u * x⁻¹ = u⁻¹ := by
  obtain ⟨v, hv⟩ := mem_commSpace.mp hcu
  obtain ⟨w, hw, rfl⟩ := S.exists_cl v
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  set c := x * w * x⁻¹ * w⁻¹ with hc
  have hcQ : c ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG hxM hw) (S.QG.inv_mem hw)
  have hcl : S.cl c = S.cl u := by
    rw [← hv, S.rhoL_cl hxM hw, hc, S.cl_mul (S.conj_mem_QG hxM hw) (S.QG.inv_mem hw),
      S.cl_inv hw, sub_eq_add_vec (ZMod 2)]
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hc, hxinv]
    calc x * (x * w * x * w⁻¹) * x = (x * x) * w * x * w⁻¹ * x := by group
      _ = w * x * w⁻¹ * x := by rw [hxx]; group
      _ = (x * w * x * w⁻¹)⁻¹ := by
          rw [show (x * w * x * w⁻¹)⁻¹ = w * x⁻¹ * w⁻¹ * x⁻¹ by group, hxinv]
  rcases (S.cl_eq_cl_iff hcQ hu).mp hcl with rfl | rfl
  · exact hxc
  · have hxz : x * S.z * x⁻¹ = S.z := by rw [S.z_comm hxM]; group
    have hinv : (c * S.z)⁻¹ = c⁻¹ * S.z := by
      rw [mul_inv_rev, S.z_inv]
      exact (S.z_comm_QG (S.QG.inv_mem hcQ)).symm
    calc x * (c * S.z) * x⁻¹ = (x * c * x⁻¹) * (x * S.z * x⁻¹) := by group
      _ = c⁻¹ * S.z := by rw [hxc, hxz]
      _ = (c * S.z)⁻¹ := hinv.symm

theorem commute_iff_q_eq_zero_of_cl_mem_commSpace {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
    {u : G} (hu : u ∈ S.QG) (hcu : S.cl u ∈ commSpace (S.rhoL hxM)) :
    x * u = u * x ↔ S.q (S.cl u) = 0 := by
  have hinv := S.conj_eq_inv_of_cl_mem_commSpace hxM hxx hu hcu
  rw [S.q_cl_eq_zero_iff hu, pow_two]
  constructor
  · intro h
    have : x * u * x⁻¹ = u := by rw [h]; group
    rw [hinv] at this
    calc u * u = u * u⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel u
  · intro h
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right h
    rw [hu'] at hinv
    calc x * u = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [hinv]

@[expose] noncomputable def cqxSub (x : G) : Submodule (ZMod 2) S.Qt :=
  S.clSub (S.QG ⊓ centralizer ({x} : Set G))

omit [Finite G] in
theorem z_mem_cqx {x : G} (hxM : x ∈ S.M) : S.z ∈ S.QG ⊓ centralizer ({x} : Set G) :=
  mem_inf.mpr ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩

omit [Finite G] in
theorem clPre_cqxSub {x : G} (hxM : x ∈ S.M) :
    S.clPre (S.cqxSub x) = S.QG ⊓ centralizer ({x} : Set G) :=
  S.clPre_clSub inf_le_left (S.z_mem_cqx hxM)

theorem cqxSub_le_fixSpace {x : G} (hxM : x ∈ S.M) : S.cqxSub x ≤ fixSpace (S.rhoL hxM) := by
  intro v hv
  obtain ⟨y, hyX, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [mem_fixSpace, S.rhoL_cl hxM hyQ, (S.mem_inf_centralizer_iff_conj.mp hyX).2]

theorem finrank_fixSpace_le {x : G} (hxM : x ∈ S.M) :
    finrank (ZMod 2) (fixSpace (S.rhoL hxM)) ≤ finrank (ZMod 2) (S.cqxSub x) + 1 := by
  have h1 := S.card_clPre_fixSpace_le hxM
  rw [← S.clPre_cqxSub hxM, S.card_clPre, S.card_clPre, S.card_submodule,
    S.card_submodule] at h1
  change 2 * 2 ^ finrank (ZMod 2) (fixSpace (S.rhoL hxM)) ≤
    2 * (2 * 2 ^ finrank (ZMod 2) (S.cqxSub x)) at h1
  have h2 : 2 ^ finrank (ZMod 2) (fixSpace (S.rhoL hxM)) ≤
      2 ^ (finrank (ZMod 2) (S.cqxSub x) + 1) := by
    rw [pow_succ]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2

theorem card_QG_eq_mul {x : G} (hxM : x ∈ S.M) :
    Nat.card S.QG = 2 ^ (2 * S.width - finrank (ZMod 2) (S.cqxSub x)) *
      Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hle : finrank (ZMod 2) (S.cqxSub x) ≤ 2 * S.width := by
    rw [← S.finrank_Qt_eq_two_mul_width]
    exact Submodule.finrank_le _
  rw [← S.clPre_cqxSub hxM, S.card_clPre, S.card_submodule, S.card_QG_eq, S.card_Qt,
    S.finrank_Qt_eq_two_mul_width]
  rw [show 2 ^ (2 * S.width - finrank (ZMod 2) (S.cqxSub x)) *
      (2 * 2 ^ finrank (ZMod 2) (S.cqxSub x)) =
      2 * (2 ^ (2 * S.width - finrank (ZMod 2) (S.cqxSub x)) *
        2 ^ finrank (ZMod 2) (S.cqxSub x)) by ring, ← pow_add, Nat.sub_add_cancel hle]

theorem center_cqx_eq {x : G} (hxM : x ∈ S.M) :
    S.QG ⊓ centralizer ({x} : Set G) ⊓
        centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) =
      S.clPre (S.cqxSub x ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub x)) := by
  have h1 := S.centralizer_inf_QG_eq_clPre (X := S.QG ⊓ centralizer ({x} : Set G)) inf_le_left
  change _ = S.clPre (LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub x)) at h1
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hyZ⟩ := mem_inf.mp hy
    have hy1 : y ∈ S.clPre (S.cqxSub x) := by rw [S.clPre_cqxSub hxM]; exact hyC
    have hy2 : y ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) :
        Set G) := mem_inf.mpr ⟨(mem_inf.mp hyC).1, hyZ⟩
    rw [h1] at hy2
    exact ⟨(S.mem_clPre.mp hy1).1, Submodule.mem_inf.mpr ⟨(S.mem_clPre.mp hy1).2,
      (S.mem_clPre.mp hy2).2⟩⟩
  · intro hy
    obtain ⟨hyQ, hyK⟩ := S.mem_clPre.mp hy
    obtain ⟨hyK1, hyK2⟩ := Submodule.mem_inf.mp hyK
    have hy1 : y ∈ S.clPre (S.cqxSub x) := S.mem_clPre.mpr ⟨hyQ, hyK1⟩
    rw [S.clPre_cqxSub hxM] at hy1
    have hy2 : y ∈ S.clPre (LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub x)) :=
      S.mem_clPre.mpr ⟨hyQ, hyK2⟩
    rw [← h1] at hy2
    exact mem_inf.mpr ⟨hy1, (mem_inf.mp hy2).2⟩

@[expose] noncomputable def singSub (W : Submodule (ZMod 2) S.Qt)
    (hW : ∀ a ∈ W, ∀ b ∈ W, polar S.q a b = 0) : Submodule (ZMod 2) S.Qt where
  carrier := {v | v ∈ W ∧ S.q v = 0}
  add_mem' := by
    rintro a b ⟨ha, hqa⟩ ⟨hb, hqb⟩
    refine ⟨W.add_mem ha hb, ?_⟩
    rw [QuadraticMap.map_add S.q a b, hqa, hqb, hW a ha b hb, add_zero, add_zero]
  zero_mem' := ⟨W.zero_mem, QuadraticMap.map_zero _⟩
  smul_mem' := by
    rintro c v ⟨hv, hqv⟩
    refine ⟨W.smul_mem c hv, ?_⟩
    rw [QuadraticMap.map_smul, hqv, smul_zero]

theorem singSub_le (W : Submodule (ZMod 2) S.Qt) (hW : ∀ a ∈ W, ∀ b ∈ W, polar S.q a b = 0) :
    S.singSub W hW ≤ W := fun _ hv => hv.1

theorem mem_singSub {W : Submodule (ZMod 2) S.Qt} {hW : ∀ a ∈ W, ∀ b ∈ W, polar S.q a b = 0}
    {v : S.Qt} : v ∈ S.singSub W hW ↔ v ∈ W ∧ S.q v = 0 := Iff.rfl

theorem mem_clPre_singSub_iff {W : Submodule (ZMod 2) S.Qt}
    {hW : ∀ a ∈ W, ∀ b ∈ W, polar S.q a b = 0} {y : G} :
    y ∈ S.clPre (S.singSub W hW) ↔ y ∈ S.clPre W ∧ y * y = 1 := by
  rw [S.mem_clPre, S.mem_clPre, mem_singSub]
  constructor
  · rintro ⟨hy, hyW, hq⟩
    exact ⟨⟨hy, hyW⟩, by rw [← pow_two]; exact (S.q_cl_eq_zero_iff hy).mp hq⟩
  · rintro ⟨⟨hy, hyW⟩, hyy⟩
    exact ⟨hy, hyW, (S.q_cl_eq_zero_iff hy).mpr (by rw [pow_two]; exact hyy)⟩

end Setting

end CFSG.LargeExtraspecial
