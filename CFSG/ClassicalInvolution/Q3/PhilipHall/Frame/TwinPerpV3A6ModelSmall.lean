module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelQ8Lib
public import Certificates.Certificate517503

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin Certificates.S5Rows
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

set_option quotPrecheck false in
local notation "CZ" => Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)

set_option quotPrecheck false in
local notation "kx" => (k0Gens ()).getD 0 1

set_option quotPrecheck false in
local notation "ky" => (k0Gens ()).getD 1 1

theorem sQ_valid : ValidSchreier (sQ ()) := Certificates.certificate517503.1.1

theorem czQ_valid : ValidSchreier (czQ ()) := Certificates.certificate517503.1.2

theorem sm_comm : (∀ g ∈ czGens (), g * z0 () = z0 () * g ∧ g * g = 1) ∧
    (∀ g ∈ sGens (), g * z0 () = z0 () * g) ∧ cutPerm () * z0 () = z0 () * cutPerm () ∧
    ∀ c ∈ conjPerms (), c * z0 () = z0 () * c :=
  Certificates.certificate517503.2.2.2.1

theorem sm_k0 : Q8Rel kx ky ∧ kx * kx = z0 () ∧ (twinPairs ()).length = 4 :=
  Certificates.certificate517503.2.2.2.2.2.1

theorem sm_twins : ∀ g ∈ czGens (), ∀ p ∈ twinPairs (), ∃ q ∈ twinPairs (),
    g * p.1 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} ∧ g * p.2 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} :=
  Certificates.certificate517503.2.2.2.2.2.2.1

theorem sm_pairs : ∀ x ∈ Subgroup.closure {g | g ∈ sGens ()},
    ∀ y ∈ Subgroup.closure {g | g ∈ sGens ()}, x * x = z0 () → y * y = z0 () →
      (cutPerm ())⁻¹ * x * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} →
      (cutPerm ())⁻¹ * y * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} → x * y * x = y →
      (∃ p ∈ twinPairs (), x ∈ Subgroup.closure {p.1, p.2} ∧ y ∈ Subgroup.closure {p.1, p.2}) ∨
        5 ≤ Set.ncard {J | ∃ c ∈ conjPerms (),
          J = (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom} :=
  Certificates.certificate517503.2.2.2.2.2.2.2

theorem curtis_getD_mem (i : ℕ) : (curtisPerms ()).getD i 1 ∈ omegaT := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (curtisPerms ())[i]? with
  | none => exact omegaT.one_mem
  | some g => exact curtisPerms_mem g (List.mem_of_getElem? h)

theorem sGens_mem : ∀ g ∈ sGens (), g ∈ omegaT := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact curtis_getD_mem i

theorem czGens_mem : ∀ g ∈ czGens (), g ∈ omegaT := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact curtis_getD_mem i

theorem conjPerms_mem : ∀ c ∈ conjPerms (), c ∈ omegaT := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hc
  exact aeWord_mem_omegaT w

theorem cutPerm_mem : cutPerm () ∈ omegaT := aeWord_mem_omegaT _

theorem mem_CZ {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) (hz : g * z0 () = z0 () * g) :
    (⟨g, hg⟩ : AE6Om) ∈ CZ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_ae6ModelZ]
  exact hz

theorem sQ_le : (sQ ()).originalSubgroup ≤ omegaT := by
  rw [sQ, certificate_originalSubgroup, Subgroup.closure_le]
  exact fun g hg => sGens_mem g hg

theorem card_sylow : Nat.card ((sQ ()).originalSubgroup.subgroupOf omegaT) = 4096 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sQ_le).toEquiv, sQ,
    certificate_originalSubgroup]
  exact Certificates.certificate517503.2.1

theorem isPGroup_sylow : IsPGroup 2 ((sQ ()).originalSubgroup.subgroupOf omegaT) :=
  IsPGroup.of_card (n := 12) (by rw [card_sylow]; norm_num)

theorem index_sylow : ¬ 2 ∣ ((sQ ()).originalSubgroup.subgroupOf omegaT).index := by
  have h := ((sQ ()).originalSubgroup.subgroupOf omegaT).card_mul_index
  rw [card_sylow, card_omegaT] at h
  have : ((sQ ()).originalSubgroup.subgroupOf omegaT).index = 42525 := by omega
  rw [this]
  decide

theorem sylow_le_CZ : (sQ ()).originalSubgroup.subgroupOf omegaT ≤ CZ := by
  have hle : (sQ ()).originalSubgroup ≤
      Subgroup.centralizer ({z0 ()} : Set (Equiv.Perm (Fin 360))) := by
    rw [sQ, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact sm_comm.2.1 g hg
  intro x hx
  have hx' := hle (Subgroup.mem_subgroupOf.mp hx)
  rw [Subgroup.mem_centralizer_singleton_iff] at hx'
  exact mem_CZ x.2 hx'

theorem pCore_le_sylow : pCoreOf 2 CZ ≤ (sQ ()).originalSubgroup.subgroupOf omegaT :=
  pCoreOf_le_of_odd_index sylow_le_CZ isPGroup_sylow index_sylow

theorem czQ_le : (czQ ()).originalSubgroup ≤ centralizerIn omegaT (z0 ()) := by
  rw [czQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, mem_centralizerIn]
  exact ⟨czGens_mem g hg, (sm_comm.1 g hg).1⟩

theorem class_ge : 1575 ≤ (CFSG.Sporadic.Schreier.conjClass omegaT (z0 ())).ncard :=
  Certificates.certificate517503.2.2.2.2.1

theorem centralizerIn_z0 : centralizerIn omegaT (z0 ()) = (czQ ()).originalSubgroup := by
  refine centralizerIn_eq_of_le omegaT (z0 ()) czQ_le class_ge ?_
  rw [czQ, certificate_originalSubgroup, Certificates.certificate517503.2.2.1, card_omegaT]

theorem mem_czQ_of_mem_CZ {c : AE6Om} (hc : c ∈ CZ) :
    (c : Equiv.Perm (Fin 360)) ∈ (czQ ()).originalSubgroup := by
  rw [← centralizerIn_z0, mem_centralizerIn]
  refine ⟨c.2, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have := congrArg Subtype.val hc
  simpa [coe_ae6ModelZ] using this

theorem mem_twinPairs {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)} :
    p ∈ twinPairs () ↔ ∃ c ∈ cPerms (), (c * kx * c⁻¹, c * ky * c⁻¹) = p :=
  List.mem_map

theorem q8Rel_twinPair {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)} (hp : p ∈ twinPairs ()) :
    Q8Rel p.1 p.2 := by
  obtain ⟨c, -, rfl⟩ := mem_twinPairs.mp hp
  exact q8Rel_conj sm_k0.1 c

theorem cPerms_mem_czQ : ∀ c ∈ cPerms (), c ∈ (czQ ()).originalSubgroup := by
  intro c hc
  rw [← centralizerIn_z0, mem_centralizerIn]
  exact ⟨cPerms_mem c hc, cPerms_comm c hc⟩

theorem twin_gen {g : Equiv.Perm (Fin 360)} (hg : g ∈ czGens ())
    {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)} (hp : p ∈ twinPairs ()) :
    ∃ p' ∈ twinPairs (), conjSub g (Subgroup.closure ({p.1, p.2} : Set _)) =
      Subgroup.closure ({p'.1, p'.2} : Set _) := by
  obtain ⟨p', hp', h1, h2⟩ := sm_twins g hg p hp
  refine ⟨p', hp', ?_⟩
  rw [CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair]
  exact closure_pair_eq_of_mem (q8Rel_conj (q8Rel_twinPair hp) g) (q8Rel_twinPair hp') h1 h2

theorem twin_conj {c : Equiv.Perm (Fin 360)} (hc : c ∈ (czQ ()).originalSubgroup) :
    ∀ p ∈ twinPairs (), ∃ p' ∈ twinPairs (),
      conjSub c (Subgroup.closure ({p.1, p.2} : Set _)) =
        Subgroup.closure ({p'.1, p'.2} : Set _) := by
  rw [czQ, certificate_originalSubgroup] at hc
  induction hc using Subgroup.closure_induction_left with
  | one => exact fun p hp => ⟨p, hp, conjSub_one _⟩
  | mul_left x hx y _ ih =>
    intro p hp
    obtain ⟨p', hp', h1⟩ := ih p hp
    obtain ⟨p'', hp'', h2⟩ := twin_gen hx hp'
    exact ⟨p'', hp'', by rw [conjSub_mul, h1, h2]⟩
  | inv_mul_cancel x hx y _ ih =>
    have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (sm_comm.1 x hx).2
    intro p hp
    obtain ⟨p', hp', h1⟩ := ih p hp
    obtain ⟨p'', hp'', h2⟩ := twin_gen hx hp'
    exact ⟨p'', hp'', by rw [hxx, conjSub_mul, h1, h2]⟩

theorem coe_k1 : ((ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om) :
    Equiv.Perm (Fin 360)) = kx := by
  rw [coe_ae6Word]
  rfl

theorem coe_k2 : ((ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : AE6Om) :
    Equiv.Perm (Fin 360)) = ky := by
  rw [coe_ae6Word]
  rfl

theorem mem_conjSub_K0_iff {g x : AE6Om} : x ∈ conjSub g ae6ModelK ↔
    (x : Equiv.Perm (Fin 360)) ∈ Subgroup.closure
      ({(g : Equiv.Perm (Fin 360)) * kx * (g : Equiv.Perm (Fin 360))⁻¹,
        (g : Equiv.Perm (Fin 360)) * ky * (g : Equiv.Perm (Fin 360))⁻¹} : Set _) := by
  rw [ae6ModelK, mem_conjSub_closure_pair_coe, coe_k1, coe_k2]

theorem twin_eq {g : AE6Om} (hg : g ∈ CZ) : ∃ p ∈ twinPairs (), ∀ x : AE6Om,
    x ∈ conjSub g ae6ModelK ↔
      (x : Equiv.Perm (Fin 360)) ∈ Subgroup.closure ({p.1, p.2} : Set _) := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ ∈ twinPairs () :=
    List.exists_mem_of_length_pos (by rw [sm_k0.2.2]; norm_num)
  obtain ⟨c₀, hc₀, rfl⟩ := mem_twinPairs.mp hp₀
  have hgc : (g : Equiv.Perm (Fin 360)) * c₀⁻¹ ∈ (czQ ()).originalSubgroup :=
    (czQ ()).originalSubgroup.mul_mem (mem_czQ_of_mem_CZ hg)
      ((czQ ()).originalSubgroup.inv_mem (cPerms_mem_czQ c₀ hc₀))
  obtain ⟨p, hp, hpe⟩ := twin_conj hgc _ hp₀
  refine ⟨p, hp, fun x => ?_⟩
  rw [mem_conjSub_K0_iff, ← hpe, conjSub_mul, CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair,
    CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair]
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev, inv_inv]

theorem ncard_twins_le :
    Set.ncard {J' | ∃ c ∈ CZ, conjSub c ae6ModelK = J'} ≤ 4 := by
  classical
  set f : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360) → Subgroup AE6Om :=
    fun p => (Subgroup.closure ({p.1, p.2} : Set _)).subgroupOf omegaT with hf
  have hsub : {J' | ∃ c ∈ CZ, conjSub c ae6ModelK = J'} ⊆
      (((twinPairs ()).map f).toFinset : Set (Subgroup AE6Om)) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨p, hp, hpe⟩ := twin_eq hg
    rw [Finset.mem_coe, List.mem_toFinset]
    refine List.mem_map.mpr ⟨p, hp, ?_⟩
    ext x
    exact Subgroup.mem_subgroupOf.trans (hpe x).symm
  calc _ ≤ (((twinPairs ()).map f).toFinset : Set (Subgroup AE6Om)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((twinPairs ()).map f).toFinset.card := Set.ncard_coe_finset _
    _ ≤ ((twinPairs ()).map f).length := List.toFinset_card_le _
    _ = 4 := by rw [List.length_map, sm_k0.2.2]

theorem K0_le_CZ : ae6ModelK ≤ CZ := by
  have hz : kx * kx = z0 () := sm_k0.2.1
  have hz' : ky * ky = z0 () := by
    rw [← hz, ← sq, ← sq]
    exact sm_k0.1.2.2.1.symm
  rw [ae6ModelK, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_ae6ModelZ, coe_k1]
    rw [← hz, mul_assoc]
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_ae6ModelZ, coe_k2]
    rw [← hz', mul_assoc]

theorem twin_le_CZ {g : AE6Om} (hg : g ∈ CZ) : conjSub g ae6ModelK ≤ CZ := by
  intro x hx
  have h := K0_le_CZ (mem_conjSub_iff.mp hx)
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h) (Subgroup.inv_mem _ hg)
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

theorem P0_le_CZ : ae6ModelP ≤ CZ :=
  sSup_le fun _ ⟨_, hg, hJ⟩ => hJ ▸ twin_le_CZ hg

theorem conj_mem_P0 {c : AE6Om} (hc : c ∈ CZ) {t : AE6Om} (ht : t ∈ ae6ModelP) :
    c * t * c⁻¹ ∈ ae6ModelP := by
  have hle : ae6ModelP ≤ ae6ModelP.comap (MulAut.conj c).toMonoidHom := by
    refine sSup_le fun J hJ => ?_
    obtain ⟨g, hg, rfl⟩ := hJ
    intro x hx
    rw [Subgroup.mem_comap]
    have htw : conjSub (c * g) ae6ModelK ∈ ae6ModelTwins := ⟨c * g, Subgroup.mul_mem _ hc hg, rfl⟩
    refine le_sSup htw ?_
    rw [conjSub_mul]
    exact conj_mem_conjSub hx
  exact hle ht

theorem CZ_le_normalizer : CZ ≤ Subgroup.normalizer (ae6ModelP : Set AE6Om) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨conj_mem_P0 hc, fun h => ?_⟩
  have := conj_mem_P0 (Subgroup.inv_mem _ hc) h
  rwa [inv_inv, show c⁻¹ * (c * t * c⁻¹) * c = t by group] at this

theorem plQ_le : (plQ ()).originalSubgroup ≤ omegaT := by
  rw [plQ, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ (cPerms ()).flatMap fun c => (k0Gens ()).map fun x => c * x * c⁻¹ := hg
  obtain ⟨c, hc, hgc⟩ := List.mem_flatMap.mp hg'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgc
  obtain ⟨x', -, rfl⟩ := k0Gens_mem x hx
  exact omegaT.mul_mem (omegaT.mul_mem (cPerms_mem c hc) x'.2) (omegaT.inv_mem (cPerms_mem c hc))

theorem kx_mem : kx ∈ k0Gens () := by
  have h : (k0Gens ()).length = 2 := by simp [k0Gens, kWords]
  rw [List.getD_eq_getElem _ _ (by rw [h]; norm_num)]
  exact List.getElem_mem _

theorem ky_mem : ky ∈ k0Gens () := by
  have h : (k0Gens ()).length = 2 := by simp [k0Gens, kWords]
  rw [List.getD_eq_getElem _ _ (by rw [h]; norm_num)]
  exact List.getElem_mem _

theorem P0_le_plQ : ae6ModelP ≤ (plQ ()).originalSubgroup.subgroupOf omegaT := by
  refine sSup_le fun J hJ => ?_
  obtain ⟨g, hg, rfl⟩ := hJ
  obtain ⟨p, hp, hpe⟩ := twin_eq hg
  obtain ⟨c, hc, rfl⟩ := mem_twinPairs.mp hp
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hx' := (hpe x).mp hx
  refine (Subgroup.closure_le _).mpr ?_ hx'
  rintro y (rfl | rfl)
  · rw [plQ, certificate_originalSubgroup]
    exact Subgroup.subset_closure (List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨_, kx_mem, rfl⟩⟩)
  · rw [plQ, certificate_originalSubgroup]
    exact Subgroup.subset_closure (List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨_, ky_mem, rfl⟩⟩)

theorem isPGroup_P0 : IsPGroup 2 ae6ModelP := by
  have hc : Nat.card ((plQ ()).originalSubgroup.subgroupOf omegaT) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe plQ_le).toEquiv,
      ← (plQ ()).orderCertificate_eq_card plQ_valid, chains_parts.2.1]
  exact (IsPGroup.of_card (n := 9) (by rw [hc]; norm_num)).to_le P0_le_plQ

theorem P0_le_pCore : ae6ModelP ≤ pCoreOf 2 CZ :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 P0_le_CZ CZ_le_normalizer isPGroup_P0

theorem smallQ8_K0 : AE6SmallQ8 ae6ModelZ ae6ModelK := by
  have hq : Q8Rel (ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om)
      (ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]) :=
    q8Rel_of_coe (by rw [coe_k1, coe_k2]; exact sm_k0.1)
  have hzz : (ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om) *
      ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] = ae6ModelZ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_k1, coe_ae6ModelZ]
    exact sm_k0.2.1
  refine ⟨nonempty_closure_pair_mulEquiv hq, ?_, ?_, ncard_twins_le⟩
  · rw [← hzz]
    exact isUniqueInvolution_closure_pair hq
  · have hK : ae6ModelK ∈ ae6ModelTwins := ⟨1, Subgroup.one_mem _, conjSub_one _⟩
    exact (le_sSup hK).trans P0_le_pCore

theorem smallQ8_twin (J : Subgroup AE6Om) (hJ : AE6SmallQ8 ae6ModelZ J) : J ∈ ae6ModelTwins := by
  obtain ⟨i, j, hij, hii, hJeq⟩ := exists_pair_of_smallQ8 hJ
  have hiJ : i ∈ J := hJeq ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hjJ : j ∈ J := hJeq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hjj : j * j = ae6ModelZ := by
    rw [← hii, ← sq, ← sq]
    exact hij.2.2.1.symm
  set h' : AE6Om := ⟨cutPerm (), cutPerm_mem⟩ with hh'def
  have hh' : h' ∈ CZ := mem_CZ cutPerm_mem sm_comm.2.2.1
  have hS : ∀ t ∈ J, (t : Equiv.Perm (Fin 360)) ∈ (sQ ()).originalSubgroup ∧
      (cutPerm ())⁻¹ * t * cutPerm () ∈ (sQ ()).originalSubgroup := by
    intro t ht
    have ht' := hJ.2.2.1 ht
    refine ⟨Subgroup.mem_subgroupOf.mp (pCore_le_sylow ht'), ?_⟩
    have h2 := conj_mem_pCoreOf (Subgroup.inv_mem _ hh') ht'
    rw [inv_inv] at h2
    have h3 := Subgroup.mem_subgroupOf.mp (pCore_le_sylow h2)
    simpa [hh'def] using h3
  have hsq : ∀ t : AE6Om, t * t = ae6ModelZ →
      ((t : Equiv.Perm (Fin 360)) * t = z0 ()) := fun t ht => by
    have := congrArg Subtype.val ht
    simpa [coe_ae6ModelZ] using this
  have hij' : Q8Rel (i : Equiv.Perm (Fin 360)) j := q8Rel_coe hij
  have hiji : (i : Equiv.Perm (Fin 360)) * j * i = j := by
    have h1 := q8Rel_mul_j hij'
    calc (i : Equiv.Perm (Fin 360)) * j * i = j * (i : Equiv.Perm (Fin 360))⁻¹ * i := by rw [h1]
      _ = j := by group
  have eS : (sQ ()).originalSubgroup = Subgroup.closure {g | g ∈ sGens ()} := by
    rw [sQ, certificate_originalSubgroup]
  rw [eS] at hS
  rcases sm_pairs _ (hS i hiJ).1 _ (hS j hjJ).1 (hsq i hii) (hsq j hjj) (hS i hiJ).2 (hS j hjJ).2
    hiji with ⟨p, hp, h1, h2⟩ | h5
  ·
    have hq := q8Rel_twinPair hp
    have hcl := closure_pair_eq_of_mem hij' hq h1 h2
    obtain ⟨c, hc, rfl⟩ := mem_twinPairs.mp hp
    refine ⟨⟨c, cPerms_mem c hc⟩, mem_CZ (cPerms_mem c hc) (cPerms_comm c hc), ?_⟩
    ext x
    rw [mem_conjSub_K0_iff, hJeq, mem_closure_pair_coe, hcl]
  ·
    exfalso
    set f : Subgroup AE6Om → Subgroup (Equiv.Perm (Fin 360)) := fun K => K.map omegaT.subtype
      with hf
    have hinj : Function.Injective f := Subgroup.map_injective omegaT.subtype_injective
    have hsub : {K | ∃ c ∈ conjPerms (), K = (Subgroup.closure
        {(i : Equiv.Perm (Fin 360)), (j : Equiv.Perm (Fin 360))}).map (MulAut.conj c).toMonoidHom} ⊆
        f '' {J' | ∃ c ∈ CZ, conjSub c J = J'} := by
      rintro _ ⟨c, hc, rfl⟩
      have hcm := conjPerms_mem c hc
      refine ⟨conjSub ⟨c, hcm⟩ J, ⟨_, mem_CZ hcm (sm_comm.2.2.2 c hc), rfl⟩, ?_⟩
      rw [MonoidHom.map_closure, Set.image_pair]
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        rw [hJeq, mem_conjSub_closure_pair_coe] at hy
        exact hy
      · intro hx
        have hxo : x ∈ omegaT := by
          refine (Subgroup.closure_le _).2 ?_ hx
          rintro _ (rfl | rfl)
          · exact omegaT.mul_mem (omegaT.mul_mem hcm i.2) (omegaT.inv_mem hcm)
          · exact omegaT.mul_mem (omegaT.mul_mem hcm j.2) (omegaT.inv_mem hcm)
        refine Subgroup.mem_map.2 ⟨⟨x, hxo⟩, ?_, rfl⟩
        rw [hJeq, mem_conjSub_closure_pair_coe]
        exact hx
    have hle := Set.ncard_le_ncard hsub ((conjSet_finite CZ J).image f)
    rw [Set.ncard_image_of_injective _ hinj] at hle
    have := hJ.2.2.2
    omega

theorem ae6ModelSmall_proved : AE6ModelSmall :=
  ⟨smallQ8_K0, smallQ8_twin⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
