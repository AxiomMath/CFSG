module

public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Ck
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallU33
public import CFSG.GH74.KGroups.Generic6
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import Certificates.Certificate55111

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.GH74.KGroups.U33
open scoped commutatorElement

theorem concl163Syl_u3_three {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hD : TightDatum R S z) (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    (hgen : TightSelfGen R) (h3 : ¬ TightActs3 R z) {N : Subgroup X} [N.Normal]
    [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hL : CFSG.Blueprint.LieModel ↥N .PSU 3 3 1) : TL4.Concl163Syl R S z := by
  classical
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, QP_closure, u33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  set ψ := M.actHom N with hψ
  have hψi : Function.Injective ψ := M.actHom_injective N hC
  have hψN : ∀ n (hn : n ∈ N), ψ n = (M.e ⟨n, hn⟩ : Equiv.Perm (Fin 28)) := by
    intro n hn
    show (M.Φ (MulAut.conjNormal n) : Equiv.Perm (Fin 28)) = _
    rw [show (MulAut.conjNormal n : MulAut N) = MulAut.conj ⟨n, hn⟩ from
      MulAut.conjNormal_val (h := ⟨n, hn⟩)]
    exact autModel_Φ_conj_eq M hPA ⟨n, hn⟩
  have hle1 : QP.originalSubgroup ≤ ψ.range := by
    intro m hm
    rw [← hMP] at hm
    refine ⟨((M.e.symm ⟨m, hm⟩ : N) : X), ?_⟩
    rw [hψN _ (M.e.symm ⟨m, hm⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hle2 : ψ.range ≤ QA.originalSubgroup := by
    rintro _ ⟨x, rfl⟩
    rw [← hMA]
    exact M.actHom_mem N x
  have hP : Nat.card QP.originalSubgroup = 6048 := by rw [card_group QP QP_ok, QP_valid.2]
  have hA : Nat.card QA.originalSubgroup = 12096 := by rw [card_group QA QA_ok, QA_valid.2]
  obtain ⟨k, hk⟩ : 6048 ∣ Nat.card ψ.range := hP ▸ Subgroup.card_dvd_of_le hle1
  have h2 : Nat.card ψ.range ∣ 12096 := hA ▸ Subgroup.card_dvd_of_le hle2
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6048) (by simpa using h2)
  have hLN : ∀ y, ψ y ∈ elemsT QP ↔ y ∈ N := by
    intro y
    rw [mem_elemsT QP QP_ok]
    constructor
    · intro hy
      rw [← hMP] at hy
      have h1 : ψ ((M.e.symm ⟨ψ y, hy⟩ : N) : X) = ψ y := by
        rw [hψN _ (M.e.symm ⟨ψ y, hy⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      rw [← hψi h1]
      exact (M.e.symm ⟨ψ y, hy⟩).2
    · intro hy
      rw [hψN y hy, ← hMP]
      exact (M.e ⟨y, hy⟩).2
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  ·
    exfalso
    have hR : ψ.range = QP.originalSubgroup :=
      (Subgroup.eq_of_le_of_card_ge hle1 (by rw [hk, hP])).symm
    have hLP : ∀ m, m ∈ elemsT QP ↔ ∃ y, ψ y = m := fun m => by
      rw [mem_elemsT QP QP_ok, ← hR]
      rfl
    obtain ⟨x, k', hx, hxk, hxr, -⟩ := good_of_goodCheck (ι := ψ) hψi hLP u33_check_9743 hD hq8
    exact h3 ⟨x, k', hx, hxk, hxr⟩
  have hR : ψ.range = QA.originalSubgroup :=
    Subgroup.eq_of_le_of_card_ge hle2 (by rw [hk, hA])
  have hLA : ∀ m, m ∈ elemsT QA ↔ ∃ y, ψ y = m := fun m => by
    rw [mem_elemsT QA QA_ok, ← hR]
    rfl
  have hNtop : N ≠ ⊤ := by
    intro hN
    have hle : ψ.range ≤ QP.originalSubgroup := by
      rintro _ ⟨y, rfl⟩
      rw [← mem_elemsT QP QP_ok, hLN, hN]
      trivial
    have := Subgroup.card_le_of_le hle
    rw [hR, hA, hP] at this
    omega
  have hck := u33_check_9744
  have hcov := (Bool.and_eq_true_iff.1 hck).1
  have h55 : Certificates.TL4MF163U3Inv.centInvCheck (elemsT QP) (elemsT QA)
      (pickReps (elemsT QA)) = true := Certificates.certificate55111
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hψi hLA hcov hD.order
  have hVP := verdictPred_of_check hψi hLA (by norm_num : 100 < 243) hLN hck hr
  have hNO : NoOddNormalAt3 z := noOddNormalAt3_of_conj g (hg ▸ hVP.1)
  have hO : oddCoreImg R = ⊥ := oddCoreImg_eq_bot_3 hNO hD.cent hD.le_normalizer
  obtain ⟨-, hR2, u, v, hu, hv, huu, hvv, hvu, hlist⟩ := datum_shape_of_odd hD hq8 hO
  have hnorm : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      c * u * c⁻¹ ∈ q8List z u v ∧ c * v * c⁻¹ ∈ q8List z u v := fun c hc =>
    ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hc) u).mp hu),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hc) v).mp hv)⟩
  have hNuv : ¬ (u ∈ N ∧ v ∈ N) := fun huv =>
    not_selfGen_of_le inferInstance hNtop (fun x hx => mem_of_mem_q8List huv.1 huv.2 huu
      (hlist x hx)) hgen
  have h3uv : ∀ x ∈ Subgroup.centralizer ({z} : Set X), x ^ 3 = 1 →
      x * u = u * x ∧ x * v = v * x := by
    intro x hx hx3
    by_contra hne
    apply h3
    have hx3' : x ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hx3
    rw [not_and_or] at hne
    rcases hne with hne | hne
    · refine ⟨x, 1, hx, hx3', u, hu, fun hm => hne ?_⟩
      rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · refine ⟨x, 1, hx, hx3', v, hv, fun hm => hne ?_⟩
      rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
  have hK0 : tightCore R = R := tightCore_eq_of_pGroup hR2
  have hRS : tightCore R ≤ (S : Subgroup R).map R.subtype := by
    rw [hK0]
    intro x hx
    have hS : (S : Subgroup R) = ⊤ := (S.is_maximal' (hR2.to_subgroup ⊤) le_top).symm
    exact ⟨⟨x, hx⟩, by rw [hS]; exact Subgroup.mem_top _, rfl⟩
  refine MF163.concl163Syl_of_aut hC (MulEquiv.refl N) fun b hb2 hbK => ?_
  have hcongr : ∀ φ : MulAut N, MulAut.congr (MulEquiv.refl N) φ = φ := fun φ => by
    ext
    rfl
  simp only [hcongr] at hbK ⊢
  have hΦk : ∀ x : X, (M.Φ (MulAut.conjNormal x) : Equiv.Perm (Fin 28)) = ψ x := fun _ => rfl
  obtain ⟨c, hc⟩ : (M.Φ b : Equiv.Perm (Fin 28)) ∈ ψ.range := hR ▸ (hMA ▸ (M.Φ b).2)
  have hc2 : c * c = 1 := hψi (by
    rw [map_mul, hc, map_one, ← Subgroup.coe_mul, ← map_mul, hb2, map_one]
    rfl)
  have hcK : ∀ x ∈ tightCore R, c * x = x * c := fun x hx => hψi (by
    rw [map_mul, map_mul, hc, ← hΦk, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
      ← map_mul, hbK x (hRS hx)])
  have hcz : c * z = z * c := hcK z (by rw [hK0]; exact hD.mem_right)
  rcases eq_of_pair_of_check hψi hLA inferInstance hLN hcov h55 hD.order huu hvv hvu hnorm hNuv
    h3uv hcz hc2 (hcK u (by rw [hK0]; exact hu)) (hcK v (by rw [hK0]; exact hv)) with h0 | h0
  · left
    rw [h0, map_one] at hc
    exact (M.Φ_eq_one).mp hc.symm
  · right
    apply M.Φ.injective
    apply Subtype.ext
    rw [← hc, h0, ← hΦk]

theorem concl163_u3_three {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hD : TightDatum R S z) (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    (hgen : TightSelfGen R) (h3 : ¬ TightActs3 R z) {N : Subgroup X} [N.Normal]
    [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hL : CFSG.Blueprint.LieModel ↥N .PSU 3 3 1) : TL4.Concl163 R z :=
  MF163.Concl163Syl.concl163 (concl163Syl_u3_three hD hq8 hgen h3 hC hL)

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
