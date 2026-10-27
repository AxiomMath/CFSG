module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Assembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheck
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAmbient
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiSimple
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.Certificates.Native
open scoped Pointwise

namespace McLProof

open McLProof

variable {n : ℕ}

theorem lbOK_spec (hn : n < 2 ^ 32) {cap m : ℕ} {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (h : lbOK n cap m gs = true) :
    m ≤ Nat.card (genOf n gs) := by
  simp only [lbOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨htree, hdist⟩, hsize⟩ := h
  set E := (mulClosureH n gs.toArray cap).1
  have hGg : ∀ l < gs.toArray.size,
      Rep n gs.toArray[l]! (tp n gs.toArray[l]!) ∧ tp n gs.toArray[l]! ∈ genOf n gs := by
    intro l hl
    have hmem : gs.toArray[l]! ∈ gs := by simpa using getElem!_mem_array hl
    exact ⟨rep_tp (hg _ hmem), tp_mem_genOf hmem⟩
  have hspec := mulTreeOK_spec hn (genOf n gs) hGg htree
  have hrep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hspec k hk
    rw [tablePerm_eq hc]
    exact hc
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hrep) hdist
  have := length_le_card_of_nodup hnodup (K := genOf n gs) fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hrep hx
    obtain ⟨c, hc, hcrep⟩ := hspec k hk
    rw [tablePerm_eq hcrep]
    exact hc
  rwa [List.length_map, Array.length_toList, hsize] at this

theorem hn : (275 : ℕ) < 2 ^ 32 := by norm_num

noncomputable abbrev P : Subgroup (Equiv.Perm (Fin 275)) := genOf 275 abT

noncomputable abbrev pa : Equiv.Perm (Fin 275) := tp 275 Ta

noncomputable abbrev pb : Equiv.Perm (Fin 275) := tp 275 Tb

noncomputable abbrev K : Subgroup (Equiv.Perm (Fin 275)) := genOf 275 kgens

noncomputable abbrev S : Subgroup (Equiv.Perm (Fin 275)) := genOf 275 sgens

theorem permOK_abT : ∀ g ∈ abT, permOK 275 g = true := by
  intro g hg
  simp only [abT, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact tables_check.1
  · exact tables_check.2.1

theorem rep_pa : Rep 275 Ta pa := rep_tp tables_check.1

theorem rep_pb : Rep 275 Tb pb := rep_tp tables_check.2.1

theorem pa_mem : pa ∈ P := tp_mem_genOf (by simp [abT])

theorem pb_mem : pb ∈ P := tp_mem_genOf (by simp [abT])

theorem orderOf_pa : orderOf pa = 2 := orderOf_eq_two_of_involOK hn rep_pa tables_check.2.2.1

theorem pa_mul_self : pa * pa = 1 := by
  rw [← sq, ← orderOf_pa]
  exact pow_orderOf_eq_one pa

theorem pa_ne_one : pa ≠ 1 := by
  intro h
  have := orderOf_pa
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem kgens_perm : ∀ g ∈ kgens, permOK 275 g = true := fun g hg =>
  List.all_eq_true.1 kgens_check.2.1 g hg

theorem kgens_inv : ∀ g ∈ kgens, invOK 275 g (invT 275 g) = true := fun g hg =>
  List.all_eq_true.1 kgens_check.2.2.1 g hg

theorem sgens_perm : ∀ g ∈ sgens, permOK 275 g = true := fun g hg =>
  List.all_eq_true.1 words_check.2.2.2.2.1 g hg

theorem kgens_comm : ∀ g ∈ kgens, commTT 275 g Ta = true := fun g hg =>
  List.all_eq_true.1 kgens_check.2.2.2.1 g hg

theorem wordTbl_mem {gs : List Table} (hg : ∀ g ∈ gs, permOK 275 g = true) {w : List ℕ}
    (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ gs.length) (hp : permOK 275 (wordTbl 275 gs w) = true) :
    tp 275 (wordTbl 275 gs w) ∈ genOf 275 gs :=
  tp_wordTbl_mem hn hg hw hp

theorem K_le_P : K ≤ P := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ kgens := by simpa using hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (show g ∈ kWords.map (wordTbl 275 abT) from hg')
  exact wordTbl_mem permOK_abT (fun l hl => by
    have := words_check.1 w hw l hl
    simpa [abT] using this) (kgens_perm _ hg')

theorem K_le_cent : K ≤ centralizerIn P pa := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ kgens := by simpa using hg
  rw [SetLike.mem_coe, mem_centralizerIn]
  exact ⟨K_le_P (tp_mem_genOf hg'),
    (commTT_iff (rep_tp (kgens_perm g hg')) rep_pa).1 (kgens_comm g hg')⟩

theorem card_K_ge : 40320 ≤ Nat.card K := kgens_check.1.ge

noncomputable def gsAB (k : ℕ) : Equiv.Perm (Fin 275) := if k = 0 then pa else pb

theorem abArr_size : abArr.size = 2 := rfl

theorem rep_abArr : ∀ k < abArr.size, CFSG.Monster.B.Co2.Rep 275 abArr[k]! (gsAB k) := by
  intro k hk
  rw [abArr_size] at hk
  interval_cases k
  · exact co2Rep_natArr_iff.2 rep_pa
  · exact co2Rep_natArr_iff.2 rep_pb

theorem mem_abArr : ∀ k < abArr.size, gsAB k ∈ P := by
  intro k hk
  rw [abArr_size] at hk
  interval_cases k
  · exact pa_mem
  · exact pb_mem

theorem rep_zArr : CFSG.Monster.B.Co2.Rep 275 zArr pa := co2Rep_natArr_iff.2 rep_pa

theorem fix_orbit : 22275 ≤ (Set.range fun g : P => g • {p : Fin 275 | pa p = p}).ncard := by
  have h := ncard_orbit_fixed_ge P abArr gsAB rep_abArr mem_abArr rep_zArr
    orbit_check.1 orbit_check.2.1
  rwa [orbit_check.2.2] at h

theorem card_P_ge_index (hP : Nat.card P = 898128000) :
    (K.subgroupOf P).index ≤ (Set.range fun g : P => g • {p : Fin 275 | pa p = p}).ncard := by
  have hKP := K_le_P
  have h := (K.subgroupOf P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, hP] at h
  have := card_K_ge
  have hpos : 0 < (K.subgroupOf P).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0, mul_zero] at h
    omega)
  have hle : (K.subgroupOf P).index ≤ 22275 := by
    by_contra hlt
    push Not at hlt
    have : 40320 * 22276 ≤ Nat.card K * (K.subgroupOf P).index :=
      Nat.mul_le_mul this hlt
    omega
  exact hle.trans fix_orbit

theorem centralizerIn_P (hP : Nat.card P = 898128000) : centralizerIn P pa = K :=
  centralizerIn_eq_of_orbit P pa_mem K K_le_cent (card_P_ge_index hP)

theorem card_K (hP : Nat.card P = 898128000) : Nat.card K = 40320 := by
  have hKP := K_le_P
  have hidx := index_eq_ncard_orbit P pa_mem K K_le_cent (card_P_ge_index hP)
  have h := (K.subgroupOf P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, hP] at h
  have h22 : 22275 ≤ (K.subgroupOf P).index := hidx ▸ fix_orbit
  have := card_K_ge
  have hle : Nat.card K ≤ 40320 := by
    by_contra hlt
    push Not at hlt
    have : 40321 * 22275 ≤ Nat.card K * (K.subgroupOf P).index := Nat.mul_le_mul hlt h22
    omega
  omega

theorem kgens_length : kgens.length = 2 := kgens_check.2.2.2.2.1

theorem kRange {w : List ℕ} (h : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) : ∀ l ∈ w, 1 ≤ l ∧ l ≤ kgens.length :=
  fun l hl => by
    have := h l hl
    rw [kgens_length]
    exact this

theorem pa_mem_K : pa ∈ K := by
  obtain ⟨heq, hperm⟩ := kgens_check.2.2.2.2.2
  have hmem := wordTbl_mem kgens_perm (kRange fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    omega) hperm
  rwa [(tblEq_iff_eq rep_pa (rep_tp hperm)).1 heq]

theorem hKg : ∀ l < kgens.toArray.size,
    Rep 275 kgens.toArray[l]! (tp 275 kgens.toArray[l]!) ∧
      Rep 275 (kgens.toArray.map (invT 275))[l]! (tp 275 kgens.toArray[l]!)⁻¹ ∧
      tp 275 kgens.toArray[l]! ∈ K := by
  intro l hl
  have hmem : kgens.toArray[l]! ∈ kgens := by simpa using getElem!_mem_array hl
  have hrep := rep_tp (kgens_perm _ hmem)
  refine ⟨hrep, ?_, tp_mem_genOf hmem⟩
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l hl]
  exact rep_invT hrep (kgens_inv _ hmem)

theorem repTbl_perm : ∀ T ∈ repTbls, permOK 275 T = true := fun T hT =>
  List.all_eq_true.1 words_check.2.2.2.2.2.1 T hT

theorem repTbl_mem_K : ∀ T ∈ repTbls, tp 275 T ∈ K := by
  intro T hT
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
  exact wordTbl_mem kgens_perm (kRange (words_check.2.2.2.1 p hp).1) (repTbl_perm _ hT)

theorem cover :
    ∀ x ∈ K, x = 1 ∨ x = pa ∨ ∃ r ∈ repTbls.map (tp 275), ∃ c ∈ K, x = c * r * c⁻¹ :=
  cover_check

theorem gen :
    ∀ r ∈ repTbls.map (tp 275), K ≤ Subgroup.closure (CFSG.Sporadic.Schreier.conjClass K r) := by
  intro r hr
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
  set R := wordTbl 275 kgens p.1 with hR
  have hRrep : Rep 275 R (tp 275 R) := rep_tp (repTbl_perm _ hT)
  set gs : List Table := R :: p.2.map fun cw =>
    (let c := wordTbl 275 kgens cw; conjT 275 c (invT 275 c) R) with hgs
  have hgsmem : gs ∈ repGens := List.mem_map.2 ⟨p, hp, rfl⟩
  have hperm : ∀ g ∈ gs, permOK 275 g = true := fun g hg =>
    List.all_eq_true.1 (List.all_eq_true.1 words_check.2.2.2.2.2.2.2.2 gs hgsmem) g hg
  have hle1 : genOf 275 gs ≤ Subgroup.closure (CFSG.Sporadic.Schreier.conjClass K (tp 275 R)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ gs := by simpa using hg
    have hgp := hperm g hg'
    rw [hgs, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact Subgroup.subset_closure ⟨1, K.one_mem, by simp⟩
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hg'
      have hcwp := List.all_eq_true.1 (List.all_eq_true.1 words_check.2.2.2.2.2.2.2.1 p hp) cw hcw
      simp only [Bool.and_eq_true] at hcwp
      have hc := rep_tp hcwp.1
      have hci := rep_invT hc hcwp.2
      have hcK : tp 275 (wordTbl 275 kgens cw) ∈ K :=
        wordTbl_mem kgens_perm (kRange ((words_check.2.2.2.1 p hp).2 cw hcw)) hcwp.1
      have hrep := rep_conjT hc hci hRrep
      rw [rep_unique (rep_tp hgp) hrep]
      exact Subgroup.subset_closure ⟨_, hcK, rfl⟩
  exact (gen_check gs hgsmem).trans hle1

theorem commutator_ne :
    tp 275 kx * tp 275 ky * (tp 275 kx)⁻¹ * (tp 275 ky)⁻¹ ≠ 1 ∧
      tp 275 kx * tp 275 ky * (tp 275 kx)⁻¹ * (tp 275 ky)⁻¹ ≠ pa := by
  obtain ⟨hc, h0, h1⟩ := comm_check
  have hx := rep_tp (kgens_perm _ h0)
  have hy := rep_tp (kgens_perm _ h1)
  have hrep := Rep.compT (Rep.compT hx hy)
    (Rep.compT (rep_invT hx (kgens_inv _ h0)) (rep_invT hy (kgens_inv _ h1)))
  simp only [commOK, Bool.and_eq_true, Bool.not_eq_true'] at hc
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (tblEq_idT_iff hn hrep).2 (by simpa [mul_assoc] using h)
    rw [hc.1] at this
    exact Bool.noConfusion this
  · have := (tblEq_iff_eq hrep rep_pa).2 (by simpa [mul_assoc] using h)
    rw [hc.2] at this
    exact Bool.noConfusion this

theorem K_quasisimple :
    CFSG.Open.IsQuasisimple ↥K ∧
      Subgroup.center ↥K = Subgroup.zpowers (⟨pa, pa_mem_K⟩ : K) := by
  obtain ⟨-, h0, h1⟩ := comm_check
  exact isQuasisimple_of_cover pa_mem_K
    (fun k hk => (mem_centralizerIn.1 (K_le_cent hk)).2) (repTbls.map (tp 275)) cover
    gen (tp_mem_genOf h0) (tp_mem_genOf h1) commutator_ne.1 commutator_ne.2

theorem card_center_K : Nat.card (Subgroup.center ↥K) = 2 := by
  rw [K_quasisimple.2, Nat.card_zpowers]
  exact (Subgroup.orderOf_coe (⟨pa, pa_mem_K⟩ : K)).symm.trans orderOf_pa

theorem sWords_range : ∀ w ∈ sWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ kgens.length := fun w hw =>
  kRange (words_check.2.1 w hw)

theorem S_le_K : S ≤ K := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ sgens := by simpa using hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (show g ∈ sWords.map (wordTbl 275 kgens) from hg')
  exact wordTbl_mem kgens_perm (sWords_range w hw) (sgens_perm _ hg')

theorem card_S : Nat.card S = 128 := (enumOK_spec hn sgens_perm sylow_check.1).1

theorem cover_S : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ P, s = c * pa * c⁻¹ := by
  obtain ⟨-, -, hcovE, -⟩ := enumOK_spec hn sgens_perm sylow_check.1
  have hcov := sylow_check.2
  simp only [sylowCoverOK, Array.all_eq_true] at hcov
  intro s hs ho
  obtain ⟨k, hk, hrep⟩ := hcovE s hs
  have h1 := hcov k hk
  rw [← getElem!_pos _ k hk, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · exact absurd (involOK_of_orderOf hn hrep ho) (by rw [h1]; exact Bool.false_ne_true)
  · obtain ⟨ct, hct, hteq⟩ := List.any_eq_true.1 h1
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hct
    have hcp := List.all_eq_true.1 words_check.2.2.2.2.2.2.1
      (wordTbl 275 abT w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp only [Bool.and_eq_true] at hcp
    obtain ⟨c', hc', hc⟩ := rep_wordTbl hn permOK_abT w (fun l hl => by
      have := words_check.2.2.1 w hw l hl
      simpa [abT] using this)
    have hci := rep_invT hc hcp.2
    have hct' := rep_conjT hc hci rep_pa
    exact ⟨c', hc', (tblEq_iff_eq hrep hct').1 hteq⟩

theorem S_index_odd (hP : Nat.card P = 898128000) : ¬ 2 ∣ (S.subgroupOf P).index := by
  have hSP : S ≤ P := S_le_K.trans K_le_P
  have h := (S.subgroupOf P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv, card_S, hP] at h
  omega

theorem noNonsolvableClassical_P (hP : Nat.card P = 898128000) : NoNonsolvableClassical P := by
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [card_S]; norm_num)
  refine noNonsolvableClassical_of_sylow_cover_at P S hS2 (S_index_odd hP) pa_mem cover_S ?_
  exact NoNonsolvableClassicalAt.of_ambient_quasisimple P ⟨pa, pa_mem⟩ K (centralizerIn_P hP)
    K_quasisimple.1 card_center_K (Or.inl (card_K hP))

section Model

noncomputable def actionHom : CFSG.Sporadic.McL.J →* Equiv.Perm (Fin 275) :=
  MulAction.toPermHom CFSG.Sporadic.McL.J (Fin 275)

theorem actionHom_a : actionHom CFSG.Sporadic.McL.a = pa := by
  ext x
  have h1 := rep_pa x.val x.isLt
  have h2 := CFSG.Sporadic.McL.rep_alpha x.val x.isLt
  rw [idx_of_lt pa x.isLt] at h1
  rw [idx_of_lt CFSG.Sporadic.McL.a x.isLt] at h2
  exact h2.symm.trans h1

theorem actionHom_b : actionHom CFSG.Sporadic.McL.b = pb := by
  ext x
  have h1 := rep_pb x.val x.isLt
  have h2 := CFSG.Sporadic.McL.rep_beta x.val x.isLt
  rw [idx_of_lt pb x.isLt] at h1
  rw [idx_of_lt CFSG.Sporadic.McL.b x.isLt] at h2
  exact h2.symm.trans h1

theorem actionHom_injective : Function.Injective actionHom := MulAction.toPerm_injective

theorem actionHom_range : actionHom.range = P := by
  rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.McL.closure_ab, MonoidHom.map_closure,
    Set.image_pair, actionHom_a, actionHom_b]
  show Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext g
  simp [abT, eq_comm]

noncomputable def jEquivP : CFSG.Sporadic.McL.J ≃* P :=
  (MonoidHom.ofInjective actionHom_injective).trans (MulEquiv.subgroupCongr actionHom_range)

noncomputable def mclEquivP : CFSG.Blueprint.NativeSporadic.McL ≃* P :=
  CFSG.Sporadic.McL.mclEquivJ.trans jEquivP

theorem card_P : Nat.card P = 898128000 := by
  rw [← Nat.card_congr mclEquivP.toEquiv]
  exact CFSG.Sporadic.McL.card_McL

end Model

end McLProof

theorem noNonsolvableClassical_McL :
    NoNonsolvableClassical CFSG.Blueprint.NativeSporadic.McL :=
  NoNonsolvableClassical.of_mulEquiv McLProof.mclEquivP
    (McLProof.noNonsolvableClassical_P McLProof.card_P)

end CFSG.ClassicalInvolution
