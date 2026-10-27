module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut

namespace AutA6Invol

@[expose] def invCodes : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && c != Core.cid

theorem centralizer_check : invCodes.all (fun a =>
    decide ((Core.autL.filter fun c => Core.cmul a c == Core.cmul c a).length ≤ 48)) = true := by
  rw [List.all_eq_true]
  intro a ha
  unfold invCodes at ha
  rw [List.mem_filter] at ha
  obtain ⟨hmem, hinv⟩ := ha
  obtain ⟨x, rfl⟩ := exists_of_mem_autL hmem
  rw [decide_eq_true_eq,
    AutA6K.length_filter_autL (fun c => Core.cmul (cd x) c == Core.cmul c (cd x))
    (CFSG.Permutation.FinPack.commLaneK 10 (CFSG.Permutation.FinPack.enc (x : P10)))
    (fun y => AutA6K.comm_eq x y)]
  have hx : AutA6K.invTK (CFSG.Permutation.FinPack.enc (x : P10)) = true := by
    rw [AutA6K.invTK_eq]
    exact hinv
  have h := CFSG.Permutation.FinPack.allK_iff.1 AutA6K.cent48K _ (AutA6K.enc_mem_invK hx)
  rw [Nat.ble_eq] at h
  exact h

theorem psl_involution_check :
    Core.pslLit.any (fun c => Core.cmul c c == Core.cid && c != Core.cid) = true := by
  decide +kernel

@[expose] def xCode : List ℕ := [0, 1, 2, 6, 7, 8, 3, 4, 5, 9]

@[expose] def yCode : List ℕ := [9, 7, 5, 8, 6, 2, 4, 1, 3, 0]

theorem xCode_mem : xCode ∈ Core.autL := by decide +kernel

theorem yCode_mem : yCode ∈ Core.autL := by decide +kernel

theorem xCode_sq : Core.cmul xCode xCode = Core.cid := by decide +kernel

theorem yCode_sq : Core.cmul yCode yCode = Core.cid := by decide +kernel

theorem coset_cover_check : Core.autL.all (fun c =>
    Core.pslLit.contains c || Core.pslLit.contains (Core.cmul xCode c) ||
      Core.pslLit.contains (Core.cmul yCode c) ||
      Core.pslLit.contains (Core.cmul (Core.cmul xCode yCode) c)) = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨r, hr, h0, hrw⟩ := AutA6K.exists_rep hc
  rw [h0, hrw _ xCode_mem, hrw _ yCode_mem, hrw _ (AutA6K.cmul_mem_autL xCode_mem yCode_mem)]
  exact List.all_eq_true.1 (AutA6K.reps_cover xCode yCode rfl rfl) r hr

theorem cd_involution {x : AutA6} (h2 : x * x = 1) (h1 : x ≠ 1) : cd x ∈ invCodes := by
  unfold invCodes
  rw [List.mem_filter]
  refine ⟨cd_mem_autL x, ?_⟩
  rw [← cd_mul, h2, cd_one]
  simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
  rw [← cd_one]
  exact fun h => h1 (cd_injective h)

theorem card_centralizer_aut_le (a : MulAut (alternatingGroup (Fin 6))) (h2 : a * a = 1)
    (h1 : a ≠ 1) :
    Nat.card (Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) ≤ 48 := by
  set x : AutA6 := thetaEquiv.symm a with hx
  have hxx : x * x = 1 := by
    apply thetaEquiv.injective
    rw [map_mul, map_one, hx, MulEquiv.apply_symm_apply, h2]
  have hx1 : x ≠ 1 := by
    intro h
    apply h1
    rw [← MulEquiv.apply_symm_apply thetaEquiv a, ← hx, h, map_one]
  have hmem := cd_involution hxx hx1
  have hcheck := List.all_eq_true.mp centralizer_check _ hmem
  rw [decide_eq_true_eq] at hcheck
  set L := Core.autL.filter fun c => Core.cmul (cd x) c == Core.cmul c (cd x) with hL
  let f : ↥(Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) →
      ↥L.toFinset := fun g => ⟨cd (thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6)))), by
    have hg := (Subgroup.mem_centralizer_iff.mp g.2) a (Set.mem_singleton a)
    have hc : x * thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) =
        thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) * x := by
      rw [hx, ← map_mul, ← map_mul, hg]
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨cd_mem_autL _, ?_⟩
    rw [← cd_mul, ← cd_mul, hc]
    simp⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h1 := cd_injective (congrArg Subtype.val h)
    exact Subtype.ext (thetaEquiv.symm.injective h1)
  calc Nat.card (Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6)))))
      ≤ Nat.card ↥L.toFinset := Nat.card_le_card_of_injective f hf
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le L
    _ ≤ 48 := hcheck

theorem mem_PslSub_of_contains {w : AutA6} (h : Core.pslLit.contains (cd w) = true) :
    w ∈ PslSub := by
  rw [mem_PslSub, mem_psl29_iff]
  show cd w ∈ Core.pslLit
  simpa [List.contains_eq_any_beq] using h

theorem exists_aut_of_mem {c : List ℕ} (hc : c ∈ Core.autL) (hsq : Core.cmul c c = Core.cid) :
    ∃ u : AutA6, cd u = c ∧ u * u = 1 := by
  obtain ⟨u, hu⟩ := exists_of_mem_autL hc
  refine ⟨u, hu, ?_⟩
  apply cd_injective
  rw [cd_mul, hu, cd_one, hsq]

theorem closure_involutions_aut :
    Subgroup.closure {x : AutA6 | x * x = 1} = ⊤ := by
  set K : Subgroup AutA6 := Subgroup.closure {x : AutA6 | x * x = 1} with hK
  have hS : ∀ u : AutA6, u * u = 1 → u ∈ K := fun u hu => Subgroup.subset_closure hu
  have hpsl : PslSub ≤ K := by
    obtain ⟨c, hcmem, hc⟩ := List.any_eq_true.mp psl_involution_check
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨y, hy, hyc⟩ := exists_psl29_of_code hcmem
    set a : AutA6 := ⟨y, psl29_le_autA6 hy⟩ with ha
    have hca : cd a = c := hyc
    have haP : a ∈ PslSub := hy
    have haa : a * a = 1 := by
      apply cd_injective
      rw [cd_mul, hca, cd_one, hc.1]
    have ha1 : a ≠ 1 := by
      intro h
      apply hc.2
      rw [← hca, h, cd_one]
    obtain ⟨g, -, hle⟩ := d3_model haP ha1 haa
    refine hle.trans ((Subgroup.closure_le K).mpr ?_)
    rintro _ ⟨i, rfl⟩
    apply hS
    have : g i * a * (g i)⁻¹ * (g i * a * (g i)⁻¹) = g i * (a * a) * (g i)⁻¹ := by group
    rw [this, haa]
    simp
  obtain ⟨u, hu, huu⟩ := exists_aut_of_mem xCode_mem xCode_sq
  obtain ⟨v, hv, hvv⟩ := exists_aut_of_mem yCode_mem yCode_sq
  have hcover := List.all_eq_true.mp coset_cover_check
  rw [eq_top_iff]
  intro z _
  have key : ∀ w : AutA6, w ∈ K → w * z ∈ PslSub → z ∈ K := by
    intro w hw hwz
    have : z = w⁻¹ * (w * z) := by group
    rw [this]
    exact K.mul_mem (K.inv_mem hw) (hpsl hwz)
  have hz := hcover (cd z) (cd_mem_autL z)
  simp only [Bool.or_eq_true] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · exact hpsl (mem_PslSub_of_contains hz)
  · refine key u (hS u huu) (mem_PslSub_of_contains ?_)
    rw [cd_mul, hu]
    exact hz
  · refine key v (hS v hvv) (mem_PslSub_of_contains ?_)
    rw [cd_mul, hv]
    exact hz
  · refine key (u * v) (K.mul_mem (hS u huu) (hS v hvv)) (mem_PslSub_of_contains ?_)
    rw [cd_mul, cd_mul, hu, hv]
    exact hz

end AutA6Invol

open AutA6Invol

theorem card_centralizer_le_of_involution (a : MulAut (alternatingGroup (Fin 6)))
    (h2 : a * a = 1) (h1 : a ≠ 1) :
    Nat.card (Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) ≤ 48 :=
  card_centralizer_aut_le a h2 h1

theorem closure_involutions_eq_top :
    Subgroup.closure {a : MulAut (alternatingGroup (Fin 6)) | a * a = 1} = ⊤ := by
  have himg : (thetaEquiv : AutA6 → MulAut (alternatingGroup (Fin 6))) ''
      {x : AutA6 | x * x = 1} = {a : MulAut (alternatingGroup (Fin 6)) | a * a = 1} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      show thetaEquiv x * thetaEquiv x = 1
      rw [← map_mul, show x * x = 1 from hx, map_one]
    · intro ha
      refine ⟨thetaEquiv.symm a, ?_, MulEquiv.apply_symm_apply _ _⟩
      show thetaEquiv.symm a * thetaEquiv.symm a = 1
      rw [← map_mul, show a * a = 1 from ha, map_one]
  rw [← himg]
  exact closure_map_equiv thetaEquiv closure_involutions_aut

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
