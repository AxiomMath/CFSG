module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZStarCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowFacts
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHe36Check
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSLayer

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.ComponentClassification.GrSLit.HeldFix Certificates.GrSLitHeZStar

section Outer


theorem exists_twoA_comm_heAutU :
    ∃ v ∈ heP, v * heAutU = heAutU * v ∧ v ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  obtain ⟨h2, h1, hf, -⟩ := heZStar_check
  have hT : TabRep heZOuterTab (heOuterC1 * heOuterC1) := tabRep_comp_of_rep rep_heC1 rep_heC1
  have hmem : heOuterC1 * heOuterC1 ∈ heP := mul_mem heOuterC1_mem heOuterC1_mem
  refine ⟨_, hmem, ?_, mem_conjClass_t0_of_tab hT hmem h2 h1 hf⟩
  rw [mul_assoc, heOuterC1_comm, ← mul_assoc, heOuterC1_comm, mul_assoc]

theorem exists_four_heOuterD :
    ∃ x₁ ∈ heOuterD, ∃ x₂ ∈ heOuterD, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
      x₁ ≠ x₂ ∧ x₁ * x₂ = x₂ * x₁ := by
  obtain ⟨-, -, -, h11, h22, h1, h2, h12, hc, -⟩ := heZStar_check
  have r0 := rep_heD (j := 0) (by norm_num)
  have r2 := rep_heD (j := 2) (by norm_num)
  have m0 := heOuterDGen_mem_D 0 (by norm_num)
  have m2 := heOuterDGen_mem_D 2 (by norm_num)
  have T1 : TabRep heZD1Tab (heOuterDGen 0 * heOuterDGen 0) := tabRep_comp_of_rep r0 r0
  have TY : TabRep heZDYTab (heOuterDGen 0 * heOuterDGen 0 * heOuterDGen 2 * heOuterDGen 2) :=
    tabRep_comp_of_rep (rep_comp T1.2 r2) r2
  set y := heOuterDGen 0 * heOuterDGen 0 * heOuterDGen 2 * heOuterDGen 2 with hy
  have T2 : TabRep heZD2Tab (y * (y * y)) := tabRep_comp_of_rep TY.2 (rep_comp TY.2 TY.2)
  have hym : y ∈ heOuterD := mul_mem (mul_mem (mul_mem m0 m0) m2) m2
  refine ⟨_, mul_mem m0 m0, _, mul_mem hym (mul_mem hym hym), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((T1.comp T1).eq_iff TabRep.idTab).1 h11
  · exact ((T2.comp T2).eq_iff TabRep.idTab).1 h22
  · exact fun h => h1 ((T1.eq_iff TabRep.idTab).2 h)
  · exact fun h => h2 ((T2.eq_iff TabRep.idTab).2 h)
  · exact fun h => h12 ((T1.eq_iff T2).2 h)
  · exact ((T1.comp T2).eq_iff (T2.comp T1)).1 hc

end Outer

section Sylow


theorem sq_eq_one_of_comm_mod {x : Equiv.Perm (Fin 8330)} (hx : x ∈ hfT)
    (hc : ∀ j < 5, x * hfTL j = hfTL j * x ∨ x * hfTL j = heT1P * (hfTL j * x)) :
    x * x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hS, -⟩ := heZStar_check
  set σ := hfPhiT ⟨x, hx⟩ with hσdef
  have hσ : σ ∈ genGroup 32 hfTTabs32 hfTGen32 := range_hfPhiT ▸ ⟨_, rfl⟩
  obtain ⟨t, ht, hrep⟩ := enumerates_genT32.complete σ hσ
  have hsz : hfTTabs32.size = 5 := by simp [hfTTabs32, hfTTabs_size]
  have hgen : ∀ (j : ℕ) (hj : j < 5), TabRep hfTTabs32[j]! (hfPhiT ⟨hfTL j, hfTL_mem_hfT hj⟩) :=
    fun j hj => hfTGen32_eq hj ▸ tabRep_hfTTabs32 j (by rw [hsz]; exact hj)
  have hz := hgen 0 (by norm_num)
  have e0 : hfTL 0 = heT1P := by simp [hfTL]
  have hall : allBelow 5 (heZCommMod t) = true := by
    simp only [allBelow, List.all_eq_true, List.mem_range]
    intro j hj
    have hs := hgen j hj
    simp only [heZCommMod, Bool.or_eq_true, beq_iff_eq]
    rcases hc j hj with h | h
    · left
      rw [(hrep.comp hs).eq_iff (hs.comp hrep), hσdef, ← map_mul, ← map_mul]
      exact congrArg hfPhiT (Subtype.ext h)
    · right
      have h' : x * hfTL j = hfTL 0 * (hfTL j * x) := by rw [e0]; exact h
      rw [(hrep.comp hs).eq_iff (hz.comp (hs.comp hrep)), hσdef, ← map_mul, ← map_mul,
        ← map_mul]
      exact congrArg hfPhiT (Subtype.ext h')
  have hmem : t ∈ hfTEnum32.tabs := Array.mem_def.mpr ht
  have h1 := Array.all_eq_true_iff_forall_mem.mp hS t hmem
  simp only [hall, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  have h2 : σ * σ = 1 := ((hrep.comp hrep).eq_iff TabRep.idTab).1 h1
  rw [hσdef, ← map_mul, ← map_one hfPhiT] at h2
  exact congrArg Subtype.val (hfPhiT_injective h2)

end Sylow

section Layer

theorem heZWords_lt : ∀ x < 105, ∀ j ∈ heZWords.getD x [], j < heDGens.size := by
  simp only [heDGens, Array.size_ofFn]
  decide

@[expose] def heZUPerm (x : ℕ) : Equiv.Perm (Fin 105) := ((heZWords.getD x []).map heDPerm).prod

theorem tabRep_heZU {x : ℕ} (hx : x < 105) :
    TabRep (heZU x) (heZUPerm x) :=
  tabRep_wordTabS tabRep_heDGens _ (heZWords_lt x hx)

theorem heZUPerm_mem {x : ℕ} (hx : x < 105) : heZUPerm x ∈ genGroup 105 heDGens heDPerm := by
  refine Subgroup.list_prod_mem _ fun d hd => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
  have := heZWords_lt x hx j hj
  exact heDPerm_mem_D (by simpa [heDGens] using this)

theorem perm_apply_comm_of_comm {α : Type*} {S : Subgroup (Equiv.Perm α)} {z : Equiv.Perm α}
    (hz : ∀ d ∈ S, z * d = d * z) : ∀ d ∈ S, ∀ p, z (d p) = d (z p) := fun d hd p => by
  have := congrArg (fun f : Equiv.Perm α => f p) (hz d hd)
  simpa [Equiv.Perm.mul_apply] using this


theorem eq_one_of_comm_heD {z : Equiv.Perm (Fin 105)}
    (hz : ∀ d ∈ genGroup 105 heDGens heDPerm, z * d = d * z) : z = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hT, hF, -⟩ := heZStar_check
  have hzc : ∀ d ∈ genGroup 105 heDGens heDPerm, ∀ p, z (d p) = d (z p) :=
    perm_apply_comm_of_comm hz
  have hT' : ∀ x < 105, (heZU x)[0]! = x := by
    simpa only [heZTransOK, allBelow, List.all_eq_true, List.mem_range, beq_iff_eq] using hT
  have hU : ∀ (x : ℕ) (hx : x < 105), heZUPerm x 0 = ⟨x, hx⟩ := fun x hx =>
    Fin.ext (by rw [← (tabRep_heZU hx).apply 0]; exact hT' x hx)
  have he2 : TabRep heDGens[2]! (heDPerm 2) := tabRep_heDGens 2 (by simp [heDGens])
  have he2m : heDPerm 2 ∈ genGroup 105 heDGens heDPerm := heDPerm_mem_D (by norm_num)
  simp only [heZFixOK, Bool.and_eq_true, beq_iff_eq, allBelow, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne] at hF
  obtain ⟨⟨h79, h94⟩, hfix⟩ := hF
  have hpt : ∀ (p q : ℕ) (hp : p < 105) (hq : q < 105), (heDGens[2]!)[p]! = q →
      (heDGens[2]!)[(heZU p)[(z 0 : ℕ)]!]! = (heZU q)[(z 0 : ℕ)]! := by
    intro p q hp hq hpq
    have e1 : heDPerm 2 (heZUPerm p 0) = heZUPerm q 0 := by
      rw [hU p hp, hU q hq]
      exact Fin.ext (by rw [← he2.apply ⟨p, hp⟩]; exact hpq)
    have key : heDPerm 2 (heZUPerm p (z 0)) = heZUPerm q (z 0) :=
      calc heDPerm 2 (heZUPerm p (z 0)) = heDPerm 2 (z (heZUPerm p 0)) := by
            rw [hzc _ (heZUPerm_mem hp)]
        _ = z (heDPerm 2 (heZUPerm p 0)) := (hzc _ he2m _).symm
        _ = z (heZUPerm q 0) := by rw [e1]
        _ = heZUPerm q (z 0) := hzc _ (heZUPerm_mem hq) 0
    rewrite [(tabRep_heZU hp).apply, he2.apply, (tabRep_heZU hq).apply]
    exact congrArg Fin.val key
  have hω : (z 0 : ℕ) = 0 := by
    rcases hfix (z 0) (z 0).2 with h | h | h
    · exact h
    · exact absurd (hpt 79 63 (by norm_num) (by norm_num) h79) h
    · exact absurd (hpt 94 86 (by norm_num) (by norm_num) h94) h
  have hz0 : z 0 = 0 := Fin.ext hω
  refine Equiv.ext fun x => ?_
  have hx : heZUPerm x 0 = x := (hU x.val x.2).trans (Fin.eta x x.2)
  rw [Equiv.Perm.one_apply]
  calc z x = z (heZUPerm x 0) := by rw [hx]
    _ = heZUPerm x (z 0) := hzc _ (heZUPerm_mem x.2) 0
    _ = x := by rw [hz0, hx]


theorem eq_of_comm_heK0 {c : Equiv.Perm (Fin 8330)} (hc : c ∈ heP)
    (hK : ∀ k ∈ heK0, c * k = k * c) :
    c = 1 ∨ c = heGenPerm 0 ∨ c = (heGSU : Equiv.Perm (Fin 8330)) ∨
      c = heGenPerm 0 * (heGSU : Equiv.Perm (Fin 8330)) := by
  have ht0 : heGenPerm 0 ∈ heK0 := mem_map_of_mem _ heGST0_mem_layer
  have hcC : c ∈ centralizerIn heP (heGenPerm 0) := mem_centralizerIn.mpr ⟨hc, hK _ ht0⟩
  set c' : ↥(centralizerIn heP (heGenPerm 0)) := ⟨c, hcC⟩
  have hρ : HeLay.rho0 c' = 1 := by
    apply eq_one_of_comm_heD
    intro d hd
    rw [← layer_facts.2.2] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    rw [← map_mul, ← map_mul]
    exact congrArg HeLay.rho0 (Subtype.ext (hK _ (mem_map_of_mem _ hn)))
  rcases mem_ker_rho0 hρ with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end Layer

section Pure

theorem tabRep_heZUTab :
    TabRep heZUTab (heGSU : Equiv.Perm (Fin 8330)) := by
  rw [coe_heGSU]
  exact tabRep_heGSKTab (heGSComm2_lt _)


theorem heGSU_mem_conjClass :
    (heGSU : Equiv.Perm (Fin 8330)) ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  obtain ⟨-, -, -, -, hu1, -⟩ := heGS_layer_check
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hf, -⟩ := heZStar_check
  exact mem_conjClass_t0_of_tab tabRep_heZUTab (mem_centralizerIn.mp heGSU.2).1
    heGS36_check.2.2.2.2 hu1 hf

theorem heGST0U_mem_conjClass :
    heGenPerm 0 * (heGSU : Equiv.Perm (Fin 8330)) ∈
      Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hf, h2, h1⟩ := heZStar_check
  have hT : TabRep heZT0UTab (heGenPerm 0 * (heGSU : Equiv.Perm (Fin 8330))) :=
    tabRep_comp_of_rep (rep_heGen (by norm_num)) tabRep_heZUTab.2
  exact mem_conjClass_t0_of_tab hT
    (mul_mem (heGenPerm_mem (by norm_num)) (mem_centralizerIn.mp heGSU.2).1) h2 h1 hf

end Pure

end CFSG.ComponentClassification.GrSLit.HeGS
