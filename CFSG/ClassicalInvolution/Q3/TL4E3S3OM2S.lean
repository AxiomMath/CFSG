module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2C
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4Sp6
public import Certificates.Certificate55117

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data
open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

namespace E3S3O

theorem center_eq_bot_of_quat {M : Type} [Group M] [IsSimpleGroup M] {A : Subgroup M} {r : M}
    (hd : QuatTwinDatum A r) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · exfalso
    obtain ⟨e⟩ := hd.q8
    have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top
      ((e.symm (QuaternionGroup.a 1) : ↥A) : M)) ((e.symm (QuaternionGroup.xa 0) : ↥A) : M)
    have h1 : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) =
        e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) := Subtype.ext hc
    rw [← map_mul, ← map_mul] at h1
    exact absurd (e.symm.injective h1) (by decide)

theorem mem_twin_iff (z : Equiv.Perm (Fin 36)) :
    z ∈ conjSub (twin ()) K0 ↔ z ∈ L1 () := by
  rw [mem_conjSub_iff, mem_K0_iff, L1, List.mem_map]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [show (twin ())⁻¹ * (twin () * y * (twin ())⁻¹) * twin () = y by group]


theorem sig_parts : ∀ g ∈ enumeration sp6CentQ2, sigStep (rho ()) (jay ())
    (twin () * rho () * (twin ())⁻¹) (twin () * jay () * (twin ())⁻¹) (L1 ()) g = false := by
  have h := Certificates.certificate55117
  have htab : (L1 ()).map tab = L1 () := tabs_eq _
  simp only [sigCheck, tab_eq, List.all_eq_true, Bool.not_eq_true'] at h
  rw [htab] at h
  exact h

theorem e4SigmaFix_PSp {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4SigmaFix M := by
  intro A B r x hd hB hBA hx2 hfixA hact
  exfalso
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hAφ⟩ := E4Sp6.exists_emb e hd
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  have : IsSimpleGroup M := Vtx.isSimpleGroup_of_exLie (Or.inl hM)
  have hZ := center_eq_bot_of_quat hd
  obtain ⟨g, rfl⟩ := Q3NM.mem_innSubgroup_iff.mp (ExitTwo.E4.aut_inner_of_lieModel_PSp hM x)
  have hcomm : ∀ a ∈ A, g * a = a * g := fun a ha => by
    have h1 := hfixA a ha
    rw [MulAut.conj_apply] at h1
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h1]
  have hg2 : g * g = 1 := by
    have h1 : g * g ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun τ : MulAut M => τ y) hx2
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * (g * g) = g * (g * y * g⁻¹) * g⁻¹ * (g * g) := by rw [h2]
        _ = g * g * y := by group
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hr : φ r = sp6Rep2 :=
    E4Sp6.eq_rep_of_isUniqueInvolution (hAφ ▸ Vtx.isUniqueInvolution_map φ hφ hd.inv)
  obtain ⟨q, hq, rfl⟩ := hB
  have hBφ : (conjSub q A).map φ = conjSub (φ q) K0 := by rw [AscQuot.map_conjSub, hAφ]
  have hBK : conjSub (φ q) K0 = conjSub (twin ()) K0 := by
    refine E4Sp6.eq_twin_of_le_normalizer (hmem q) (fun h1 => hBA ?_) ?_
    · apply Subgroup.map_injective hφ
      rw [hBφ, h1, hAφ]
    · rcases hd.twins q hq with h1 | h1
      · exact absurd h1 hBA
      · rw [← hBφ]
        rintro _ ⟨y, hy, rfl⟩
        rw [mem_normalizer_iff_conjSub_eq, ← hAφ, ← AscQuot.map_conjSub,
          Vtx.conjSub_eq_of_forall_commute fun a ha => (h1 a ha y hy).symm]
  obtain ⟨w, hwB, hw4, hwact⟩ := hact
  have hTB : ∀ z ∈ conjSub (twin ()) K0, ∃ b ∈ conjSub q A, φ b = z := fun z hz => by
    rw [← hBK, ← hBφ] at hz
    exact hz
  have hact' : ∀ z ∈ conjSub (twin ()) K0, φ g * z * φ g * φ w = φ w * z := fun z hz => by
    obtain ⟨b, hb, rfl⟩ := hTB z hz
    have h1 := hwact b hb
    rw [MulAut.conj_apply] at h1
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    calc g * b * g * w = g * b * g⁻¹ * w := by rw [hgi]
      _ = w * b * w⁻¹ * w := by rw [h1]
      _ = w * b := by group
  have hgr : g * r = r * g := hcomm r hd.inv.mem
  have hQv := (E4Sp6.cover_of_centCheck (by rw [sp6CentQ2, certificate_originalSubgroup])
    exists_word_of_mem_map sp6_cent_check₂).1
  have hgQ : φ g ∈ enumeration sp6CentQ2 := by
    rw [mem_enumeration_iff _ hQv, ← sp6_cent_spec₂.1, sp6Q_originalSubgroup]
    exact mem_centralizerIn.2 ⟨hmem g, by rw [← hr, ← map_mul, hgr, map_mul]⟩
  have hρ : rho () ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : jay () ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hK0 : ∀ z ∈ K0, φ g * z = z * φ g := fun z hz => by
    rw [← hAφ] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hcomm a ha]
  have hwL : φ w ∈ L1 () := by
    rw [← mem_twin_iff, ← hBK, ← hBφ]
    exact Subgroup.mem_map_of_mem φ hwB
  have hw2 : ¬ φ w * φ w = 1 := by
    intro h1
    rw [← map_mul, ← map_one φ] at h1
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hφ h1)
    rw [hw4] at h2
    norm_num at h2
  have h1 : decide (φ g * φ g = 1) = true := decide_eq_true (by rw [← map_mul, hg2, map_one])
  have h2 : decide (φ g * rho () = rho () * φ g) = true := decide_eq_true (hK0 _ hρ)
  have h3 : decide (φ g * jay () = jay () * φ g) = true := decide_eq_true (hK0 _ hj)
  have h4 : ((L1 ()).any fun w' => !decide (w' * w' = 1) &&
      decide (φ g * (twin () * rho () * (twin ())⁻¹) * φ g * w' =
        w' * (twin () * rho () * (twin ())⁻¹)) &&
      decide (φ g * (twin () * jay () * (twin ())⁻¹) * φ g * w' =
        w' * (twin () * jay () * (twin ())⁻¹))) = true := by
    refine List.any_eq_true.2 ⟨φ w, hwL, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨⟨hw2, hact' _ (conj_mem_conjSub hρ)⟩, hact' _ (conj_mem_conjSub hj)⟩
  have hstep : sigStep (rho ()) (jay ()) (twin () * rho () * (twin ())⁻¹)
      (twin () * jay () * (twin ())⁻¹) (L1 ()) (φ g) = true := by
    unfold sigStep
    rw [h1, h2, h3, h4]
    rfl
  rw [sig_parts _ hgQ] at hstep
  exact Bool.false_ne_true hstep

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
