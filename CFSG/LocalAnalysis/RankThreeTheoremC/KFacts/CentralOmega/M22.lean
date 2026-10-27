module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Tools
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

open CFSG.Sporadic.Bridge

@[expose] def m22U : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 20, 12] * List.formPerm [1, 7, 17] * List.formPerm [2, 15, 19] *
    List.formPerm [3, 16, 21] * List.formPerm [5, 6, 11] * List.formPerm [8, 9, 18]

@[expose] def m22V : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 7, 17] * List.formPerm [2, 21, 11] * List.formPerm [3, 5, 15] *
    List.formPerm [6, 19, 16] * List.formPerm [8, 18, 9] * List.formPerm [10, 13, 14]

theorem m22U_eq : m22U = wordProd M22.gen [(0, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, false)] := by
  decide +kernel

theorem m22V_eq : m22V = wordProd M22.gen [(0, true), (1, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, true)] := by
  decide +kernel

theorem m22U_cube : m22U ^ 3 = 1 := by decide +kernel

theorem m22V_cube : m22V ^ 3 = 1 := by decide +kernel

theorem m22U_comm : m22U * m22V = m22V * m22U := by decide +kernel

theorem m22A_conj_U : M22.gen 0 * m22U * (M22.gen 0)⁻¹ = m22U⁻¹ := by decide +kernel

theorem m22A_conj_V : M22.gen 0 * m22V * (M22.gen 0)⁻¹ = m22V⁻¹ := by decide +kernel

theorem m22Param_injective :
    Function.Injective (fun ij : Fin 3 × Fin 3 => m22U ^ ij.1.val * m22V ^ ij.2.val) := by
  decide +kernel

@[expose] def m22u : Blueprint.NativeSporadic.M22 :=
  ⟨m22U, by rw [m22U_eq]; exact M22.nativeWord_mem _⟩

@[expose] def m22v : Blueprint.NativeSporadic.M22 :=
  ⟨m22V, by rw [m22V_eq]; exact M22.nativeWord_mem _⟩

@[expose] def m22a : Blueprint.NativeSporadic.M22 := ⟨M22.gen 0, M22.gen_mem 0⟩

theorem m22u_cube : m22u ^ 3 = 1 := Subtype.ext m22U_cube

theorem m22v_cube : m22v ^ 3 = 1 := Subtype.ext m22V_cube

theorem m22uv_comm : m22u * m22v = m22v * m22u := Subtype.ext m22U_comm

theorem m22a_conj_u : m22a * m22u * m22a⁻¹ = m22u⁻¹ := Subtype.ext m22A_conj_U

theorem m22a_conj_v : m22a * m22v * m22a⁻¹ = m22v⁻¹ := Subtype.ext m22A_conj_V

theorem card_m22 : Nat.card Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨e⟩ := M22.nonempty_mulEquiv
  obtain ⟨-, hle⟩ := M22.tauCeti_finite_card_le
  have hge := M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at hge ⊢
  omega

theorem isPGroup_closure_m22 :
    IsPGroup 3 (Subgroup.closure ({m22u, m22v} : Set Blueprint.NativeSporadic.M22)) :=
  isPGroup_closure_of_conj_eq_mul (Subgroup.one_mem _) (one_pow 3) m22u_cube m22v_cube
    (by rw [← m22uv_comm, mul_inv_cancel_right, one_mul])

theorem m22_pow_mem (ij : Fin 3 × Fin 3) : m22u ^ ij.1.val * m22v ^ ij.2.val ∈
    Subgroup.closure ({m22u, m22v} : Set Blueprint.NativeSporadic.M22) :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert m22u {m22v})) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure
      (Set.mem_insert_of_mem m22u (Set.mem_singleton m22v))) _)

theorem nine_le_card_closure_m22 :
    9 ≤ Nat.card (Subgroup.closure ({m22u, m22v} : Set Blueprint.NativeSporadic.M22)) := by
  let f : Fin 3 × Fin 3 → Subgroup.closure ({m22u, m22v} : Set Blueprint.NativeSporadic.M22) :=
    fun ij => ⟨_, m22_pow_mem ij⟩
  have hf : Function.Injective f := by
    intro ij kl h
    have h1 : m22u ^ ij.1.val * m22v ^ ij.2.val = m22u ^ kl.1.val * m22v ^ kl.2.val :=
      congrArg Subtype.val h
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_pow] at h2
    exact m22Param_injective h2
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at h

theorem not_dvd_card_m22 : ¬ 27 ∣ Nat.card Blueprint.NativeSporadic.M22 := by
  rw [card_m22]
  norm_num

theorem exists_sylow_m22 : ∃ Q : Sylow 3 Blueprint.NativeSporadic.M22,
    (Q : Subgroup Blueprint.NativeSporadic.M22) = Subgroup.closure {m22u, m22v} :=
  exists_sylow_eq_of_nine_le isPGroup_closure_m22 nine_le_card_closure_m22 not_dvd_card_m22

theorem not_forall_commute_m22 {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hc : Nat.card (Subgroup.center L) = 3)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  obtain ⟨b⟩ := M22.nonempty_mulEquiv
  obtain ⟨Q, hQ⟩ := exists_sylow_m22
  exact not_forall_commute_of_cover hq hc (e.trans b.symm) m22u_cube m22v_cube
    ⟨m22a, m22a_conj_u⟩ ⟨m22a, m22a_conj_v⟩ Q hQ S

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
