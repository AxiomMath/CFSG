module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Good
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import Certificates.Certificate55109

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4C


theorem ngWit_mem {y : Equiv.Perm (Fin 36)} (hy : y ∈ ngWit ()) :
    y ∈ sp6CentQ2.originalSubgroup := by
  simp only [ngWit, List.mem_map] at hy
  obtain ⟨w, -, rfl⟩ := hy
  rw [tab_eq]
  refine evalCodes_mem _ (fun g hg => ?_) w
  rw [sp6CentQ2, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem validT : ValidSchreier sp6CentQ2 :=
  (cover_of_centCheck (by rw [sp6CentQ2, certificate_originalSubgroup])
    exists_word_of_mem_map sp6_cent_check₂).1


theorem cent_eq : centralizerIn co3X36 sp6Rep2 = sp6CentQ2.originalSubgroup := by
  rw [← sp6Q_originalSubgroup]
  exact sp6_cent_spec₂.1

theorem chain_le :
    sp6CentQ2.originalSubgroup ≤ co3X36 := by
  rw [← cent_eq]
  exact inf_le_left

theorem pow_nine {x : Equiv.Perm (Fin 36)} (hx : x ∈ sp6CentQ2.originalSubgroup) {k : ℕ}
    (hx3 : x ^ 3 ^ k = 1) : x ^ 9 = 1 := by
  obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx3)
  have hT : orderOf x ∣ 4608 := by
    rw [← sp6_cent_spec₂.2.1]
    exact Subgroup.orderOf_dvd_natCard _ hx
  have hj2 : j ≤ 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have h27 : 3 ^ 3 ∣ 4608 := (Nat.pow_dvd_pow 3 hlt).trans (hjx ▸ hT)
    norm_num at h27
  rw [← orderOf_dvd_iff_pow_eq_one, hjx]
  exact (Nat.pow_dvd_pow 3 hj2).trans (by norm_num)


theorem ng_parts : (∀ y ∈ ngWit (), y ^ 3 = 1 ∧ y * rho () = rho () * y ∧
      y * jay () = jay () * y) ∧
    ∀ c ∈ enumeration sp6CentQ2, ngBad (L0 ()) (rho ()) (jay ()) (ngWit ()) c = false := by
  have h : ngCheck () = true := Certificates.certificate55109
  unfold ngCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hy, hc⟩ := h
  refine ⟨fun y hyw => ?_, fun c hce => ?_⟩
  · have h1 := List.all_eq_true.mp hy y hyw
    rw [Bool.and_eq_true, Bool.and_eq_true] at h1
    exact ⟨of_decide_eq_true h1.1.1, of_decide_eq_true h1.1.2, of_decide_eq_true h1.2⟩
  · have h1 := List.all_eq_true.mp hc c hce
    rw [Bool.not_eq_true'] at h1
    exact h1

theorem commute_of_gens {y : Equiv.Perm (Fin 36)} (hr : y * rho () = rho () * y)
    (hj : y * jay () = jay () * y) {c : Equiv.Perm (Fin 36)} (hc : c ∈ K0) : y * c = c * y := by
  have hle : K0 ≤ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 36))) := by
    rw [K0, Subgroup.closure_le]
    rintro z (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact hr.symm
    · exact hj.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

theorem noGood_model {sc : Equiv.Perm (Fin 36)} (hsc : IsUniqueInvolution K0 sc)
    {x : Equiv.Perm (Fin 36)} (hx : x ∈ co3X36) (k : ℕ) (hx3 : x ^ 3 ^ k = 1)
    (hxK : conjSub x K0 = K0) (hact : ∃ c ∈ K0, x * c ≠ c * x) :
    ∃ y ∈ co3X36, y ^ 3 = 1 ∧ (∀ c ∈ K0, y * c = c * y) ∧ x * y ≠ y * x := by
  have hsc2 := eq_rep_of_isUniqueInvolution hsc
  have hxr : x * sp6Rep2 = sp6Rep2 * x := by
    have h := hsc.conj_eq hxK
    rw [hsc2] at h
    calc x * sp6Rep2 = x * sp6Rep2 * x⁻¹ * x := by group
      _ = sp6Rep2 * x := by rw [h]
  have hxT : x ∈ sp6CentQ2.originalSubgroup := cent_eq ▸ mem_centralizerIn.2 ⟨hx, hxr⟩
  have hxe : x ∈ enumeration sp6CentQ2 := (mem_enumeration_iff sp6CentQ2 validT x).2 hxT
  have hbad := ng_parts.2 x hxe
  have hn : norms (L0 ()) (rho ()) (jay ()) x = true := norms_of_conjSub_eq mem_K0_iff hxK
  have hnc : (decide (x * rho () = rho () * x) && decide (x * jay () = jay () * x)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨c, hc, hxc⟩ := hact
    exact hxc (commute_of_gens h.1 h.2 hc)
  have h9 : decide (x ^ 9 = 1) = true := decide_eq_true (pow_nine hxT hx3)
  unfold ngBad at hbad
  rw [hn, hnc, h9] at hbad
  simp only [Bool.not_false, Bool.true_and, Bool.and_true, List.all_eq_false] at hbad
  obtain ⟨y, hyw, hxy⟩ := hbad
  rw [decide_eq_true_eq] at hxy
  obtain ⟨hy3, hyr, hyj⟩ := ng_parts.1 y hyw
  exact ⟨y, chain_le (ngWit_mem hyw), hy3, fun c hc => commute_of_gens hyr hyj hc, hxy⟩

theorem e4QuatNoGood_PSp {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4QuatNoGood M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  exact Vtx.e4QuatNoGood_of_model co3X36 K0 (fun K s hd => exists_emb e hd)
    (fun sc hsc x hx k hx3 hxK hact => noGood_model hsc hx k hx3 hxK hact)

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
