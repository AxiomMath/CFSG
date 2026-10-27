module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ElemAbelianGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSTransport
public import Certificates.Certificate117001
public import Certificates.Certificate117002
public import Certificates.Certificate117003

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd
open scoped Pointwise

@[expose] noncomputable def zasT0 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 zasTGens)

@[expose] noncomputable def zasZ0 : Equiv.Perm (Fin 100) := permOfArr 100 s5Z

theorem zas_sylow_spec :
    zasT0 ≤ hs100P ∧ Nat.card zasT0 = 512 ∧ zasZ0 ∈ zasT0 ∧ zasZ0 * zasZ0 = 1 ∧ zasZ0 ≠ 1 ∧
      ∀ x ∈ zasT0, zasZ0 * x = x * zasZ0 := by
  classical
  have h : zasSylowOK = true := Certificates.certificate117001
  simp only [zasSylowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨henum, hsize⟩, hsift⟩, hvz⟩, hinz⟩, hnez⟩, hz2⟩, hcen⟩, hany⟩ := h
  have hps : ∀ p ∈ zasTKeys, p < 100 := by
    intro p hp
    simp only [zasTKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hrz : Rep 100 s5Z zasZ0 := rep_of_validA hvz
  have hne1 : zasZ0 ≠ 1 := by
    intro h
    have h1 : eqA 100 s5Z (idA 100) = true := (eqA_iff hrz rep_idA).2 h
    rw [h1] at hnez
    exact absurd hnez (by simp)
  refine ⟨?_, hcard.trans hsize, ?_, (eqA_iff (rep_compA hrz hrz) rep_idA).1 hz2, hne1, ?_⟩
  · rw [zasT0, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hkv := enumOK_gens_valid henum hk
    exact (s5InP_iff hkv).1 (allLt_spec hsift hk)
  · exact enumOK_mem_of_any hps henum hrz hany
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    have hrx := rep_of_validA (hval i hi)
    have hmemL : zasTCert.pts[i]! ∈ zasTCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    exact (eqA_iff (rep_compA hrz hrx) (rep_compA hrx hrz)).1 (List.all_eq_true.1 hcen _ hmemL)

theorem rep_zasConj {a x : Array ℕ} {h : Equiv.Perm (Fin 100)} (ha : validA 100 a = true)
    (hx : Rep 100 x h) :
    Rep 100 (zasConj a x) (permOfArr 100 a * h * (permOfArr 100 a)⁻¹) :=
  rep_compA (rep_compA (rep_of_validA ha) hx) (rep_inv_of_validA ha)

theorem rep_zasConjInv {a x : Array ℕ} {h : Equiv.Perm (Fin 100)} (ha : validA 100 a = true)
    (hx : Rep 100 x h) :
    Rep 100 (zasConjInv a x) ((permOfArr 100 a)⁻¹ * h * permOfArr 100 a) :=
  rep_compA (rep_compA (rep_inv_of_validA ha) hx) (rep_of_validA ha)

@[expose] def zasDec (a : Array ℕ) : Set (Fin 100) := {i | a[i.1]! = 1}

@[expose] noncomputable def zasPGen (k : ℕ) : Equiv.Perm (Fin 100) := permOfArr 100 (hs100Arr k)

theorem zasDec_act {k : ℕ} (hk : k < 2) (hv : validA 100 (hs100Arr k) = true) (a : Array ℕ) :
    zasDec (zasSetAct k a) = zasPGen k • zasDec a := by
  have hginv : zasGInv[k]! = invCand 100 (hs100Arr k) := by
    rw [getElem!_pos zasGInv k (by simp [zasGInv]; omega)]
    simp [zasGInv]
  have hr := rep_inv_of_validA hv
  have hz : zasPGen k = permOfArr 100 (hs100Arr k) := rfl
  rw [hz]
  ext j
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [zasDec, zasSetAct, Set.mem_ofPred_eq, hginv]
  rw [getElem!_ofFn_nat _ j.2, hr j]
  rw [Equiv.Perm.smul_def]



theorem closure_zasPGen : Subgroup.closure (zasPGen '' {k | k < 2}) = hs100P := by
  have : zasPGen '' {k | k < 2} = {hs100A, hs100B} := by
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  rw [this]
  rfl

theorem zasSetKey_eq {a b : Array ℕ} (ha : zasSetValid a = true) (hb : zasSetValid b = true)
    (h : zasDec a = zasDec b) : zasSetKey a = zasSetKey b := by
  simp only [zasSetValid, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at ha hb
  unfold zasSetKey keyA
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' : p < 100 := List.mem_range.1 hp
  have h1 := ha.2 p hp'
  have h2 := hb.2 p hp'
  have h3 : (⟨p, hp'⟩ : Fin 100) ∈ zasDec a ↔ (⟨p, hp'⟩ : Fin 100) ∈ zasDec b := by rw [h]
  simp only [zasDec, Set.mem_ofPred_eq] at h3
  omega

theorem zasDec_act' (hv : ∀ k < 2, validA 100 (hs100Arr k) = true) :
    ∀ k < 2, ∀ a, zasSetValid a = true →
      zasDec (zasSetAct k a) = zasPGen k • zasDec a := by
  intro k hk a _
  exact zasDec_act hk (hv k hk) a

theorem zas_stab_card
    (hv : ∀ k < 2, validA 100 (hs100Arr k) = true)
    (hcert : arrCertOK zasSetAct 2 zasSetValid zasSetKey zasFixVec zasFCert = true)
    (hsize : zasFCert.pts.size = 3850) :
    Nat.card (MulAction.stabilizer (Subgroup.closure (zasPGen '' {k | k < 2}))
      (zasDec zasFixVec)) = 11520 := by
  have horb := ncard_orbit_of_arrCertOK (G := Equiv.Perm (Fin 100)) (X := Set (Fin 100))
    (dec := zasDec) («gens» := zasPGen) hcert (zasDec_act' hv) (fun a b ha hb h => zasSetKey_eq ha hb h)
  rw [hsize] at horb
  have hidx := MulAction.index_stabilizer (Subgroup.closure (zasPGen '' {k | k < 2}))
    (zasDec zasFixVec)
  have hmul := Subgroup.index_mul_card
    (MulAction.stabilizer (Subgroup.closure (zasPGen '' {k | k < 2})) (zasDec zasFixVec))
  have hcardP : Nat.card (Subgroup.closure (zasPGen '' {k | k < 2})) = 44352000 := by
    rw [closure_zasPGen]
    exact card_hs100P
  rw [hidx, horb, hcardP] at hmul
  omega


theorem zasPts_mem {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) : c.pts[i]! ∈ c.pts.toList := by
  rw [getElem!_pos _ i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem zas_special_spec_ext :
    ∃ E : Subgroup (Equiv.Perm (Fin 100)), E = Subgroup.closure (permsA 100 zasE0Gens) ∧
      Subgroup.closure (permsA 100 zasNGens) = normalizer (E : Set (Equiv.Perm (Fin 100))) ⊓ hs100P ∧
      IsSpecialIn hs100P zasZ0 E := by
  classical
  have h : zasSpecialOK = true := Certificates.certificate117002
  simp only [zasSpecialOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hvz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  set E : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (permsA 100 zasE0Gens) with hEdef
  set Nn : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (permsA 100 zasNGens) with hNdef
  have hpsE : ∀ p ∈ zasEKeys, p < 100 := fun p hp => List.mem_range.1 hp
  have hpsN : ∀ p ∈ zasNKeys, p < 100 := by
    intro p hp
    simp only [zasNKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmemE, hcardE, hvalE⟩ := enumOK_spec hpsE h1
  obtain ⟨hmemN, hcardN, hvalN⟩ := enumOK_spec hpsN h7
  have hz : Rep 100 s5Z zasZ0 := rep_of_validA hvz
  have hEpts : ∀ x ∈ E, ∃ i < zasE0Cert.pts.size, Rep 100 zasE0Cert.pts[i]! x :=
    fun x hx => enumOK_exists_rep hpsE h1 hx
  have hNpts : ∀ x ∈ Nn, ∃ i < zasNCert.pts.size, Rep 100 zasNCert.pts[i]! x :=
    fun x hx => enumOK_exists_rep hpsN h7 hx
  have hzE : zasZ0 ∈ E := enumOK_mem_of_any hpsE h1 hz h6
  have hEP : E ≤ hs100P := by
    rw [hEdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (s5InP_iff (enumOK_gens_valid h1 hk)).1 (allLt_spec h3 hk)
  have hNP : Nn ≤ hs100P := by
    rw [hNdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (s5InP_iff (enumOK_gens_valid h7 hk)).1 (allLt_spec h9 hk)
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    obtain ⟨i, hi, hr⟩ := hEpts x hx
    exact (eqA_iff (rep_compA hr hr) rep_idA).1 (List.all_eq_true.1 h4 _ (zasPts_mem hi))
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, hi, hr⟩ := hEpts x hx
    obtain ⟨j, hj, hs⟩ := hEpts y hy
    have := List.all_eq_true.1 (List.all_eq_true.1 h5 _ (zasPts_mem hi)) _ (zasPts_mem hj)
    exact (eqA_iff (rep_compA hr hs) (rep_compA hs hr)).1 this
  have habel : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff_of_setLike.2 hcomm, fun x hx => ?_⟩
    rw [pow_two]
    exact hsq x hx
  have hcard16 : Nat.card E = 16 := hcardE.trans h2
  have hgen_norm : ∀ k < zasNGens.size, permOfArr 100 zasNGens[k]! ∈ normalizer (E : Set _) := by
    intro k hk
    have hkv := enumOK_gens_valid h7 hk
    have hk10 := List.all_eq_true.1 (allLt_spec h10 hk)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hr⟩ := hEpts x hx
      have := hk10 _ (zasPts_mem hi)
      simp only [Bool.and_eq_true] at this
      exact enumOK_mem_of_any hpsE h1 (rep_zasConj hkv hr) this.1
    · intro hx
      obtain ⟨i, hi, hr⟩ := hEpts _ hx
      have := hk10 _ (zasPts_mem hi)
      simp only [Bool.and_eq_true] at this
      have h' := enumOK_mem_of_any hpsE h1 (rep_zasConjInv hkv hr) this.2
      have e : (permOfArr 100 zasNGens[k]!)⁻¹ *
          (permOfArr 100 zasNGens[k]! * x * (permOfArr 100 zasNGens[k]!)⁻¹) *
          permOfArr 100 zasNGens[k]! = x := by group
      rwa [e] at h'
  have hNnorm : Nn ≤ normalizer (E : Set _) ⊓ hs100P := by
    refine le_inf ?_ hNP
    rw [hNdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hgen_norm k hk
  have hv : ∀ k < 2, validA 100 (hs100Arr k) = true := fun k hk => allLt_spec h12 hk
  have hstab := zas_stab_card hv h13 h14
  have hptsE : ∀ x ∈ zasE0Cert.pts.toList, ∃ g ∈ E, Rep 100 x g := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hx)
    have hjx' : zasE0Cert.pts[j]! = x := by rw [getElem!_pos _ j hj]; exact hjx
    have hr : Rep 100 x (permOfArr 100 x) := rep_of_validA (hjx' ▸ hvalE j hj)
    exact ⟨permOfArr 100 x, enumOK_mem hpsE h1 hj (hjx' ▸ hr), hr⟩
  have hFix : ∀ i : Fin 100, i ∈ zasDec zasFixVec ↔ ∀ e ∈ E, e i = i := by
    intro i
    simp only [zasDec, Set.mem_ofPred_eq, zasFixVec]
    rw [getElem!_ofFn_nat _ i.2]
    constructor
    · intro hi e he
      by_cases hall : zasE0Cert.pts.toList.all (fun x => x[i.1]! == i.1) = true
      · obtain ⟨j, hj, hr⟩ := hEpts e he
        have := List.all_eq_true.1 hall _ (zasPts_mem hj)
        rw [beq_iff_eq, hr i] at this
        exact Fin.ext this
      · simp [hall] at hi
    · intro hall
      have hall' : zasE0Cert.pts.toList.all (fun x => x[i.1]! == i.1) = true := by
        rw [List.all_eq_true]
        intro x hx
        obtain ⟨g, hg, hr⟩ := hptsE x hx
        rw [beq_iff_eq, hr i, hall g hg]
      simp [hall']
  have hS : ∀ g ∈ normalizer (E : Set (Equiv.Perm (Fin 100))), ∀ i,
      i ∈ zasDec zasFixVec → g i ∈ zasDec zasFixVec := by
    intro g hg i hi
    rw [hFix] at hi ⊢
    intro e he
    have hmem := mem_normalizer_iff.1 hg (g⁻¹ * e * g)
    have hconj : g⁻¹ * e * g ∈ E := by
      rw [hmem]
      have e' : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
      rw [e']
      exact he
    have h3 : g⁻¹ (e (g i)) = i := hi _ hconj
    calc e (g i) = g (g⁻¹ (e (g i))) := by simp
      _ = g i := by rw [h3]
  have hSstab : ∀ g ∈ normalizer (E : Set (Equiv.Perm (Fin 100))),
      g • zasDec zasFixVec = zasDec zasFixVec := by
    intro g hg
    ext j
    rw [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def]
    constructor
    · intro h
      have := hS g hg _ h
      simpa using this
    · intro h
      exact hS g⁻¹ (inv_mem hg) j h
  have hHP : Subgroup.closure (zasPGen '' {k | k < 2}) = hs100P := closure_zasPGen
  set Nrm : Subgroup (Equiv.Perm (Fin 100)) := normalizer (E : Set _) ⊓ hs100P with hNrm
  have hNrmH : Nrm ≤ Subgroup.closure (zasPGen '' {k | k < 2}) := hHP ▸ inf_le_right
  have hQle : Nrm.subgroupOf (Subgroup.closure (zasPGen '' {k | k < 2})) ≤
      MulAction.stabilizer (Subgroup.closure (zasPGen '' {k | k < 2})) (zasDec zasFixVec) := by
    intro q hq
    rw [MulAction.mem_stabilizer_iff]
    have hq' : (q : Equiv.Perm (Fin 100)) ∈ Nrm := hq
    exact hSstab _ hq'.1
  have hNcard : Nat.card Nrm ≤ 11520 := by
    have := Subgroup.card_le_of_le hQle
    rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNrmH).toEquiv] at this
    exact this
  have hNeq : Nn = Nrm :=
    Subgroup.eq_of_le_of_card_ge hNnorm (by rw [hcardN, h8]; exact hNcard)
  set Ωs : Set (Fin 100) := {i | zasOmVec[i.1]! = 1} with hΩs
  have hΩgen : ∀ k < zasNGens.size, permOfArr 100 zasNGens[k]! ∈
      MulAction.stabilizer (Equiv.Perm (Fin 100)) Ωs := by
    intro k hk
    have hkv := enumOK_gens_valid h7 hk
    have hr := rep_of_validA hkv
    have hk16 := allLt_spec h16 hk
    have hiff : ∀ i : Fin 100, permOfArr 100 zasNGens[k]! i ∈ Ωs ↔ i ∈ Ωs := by
      intro i
      have := allLt_spec hk16 i.2
      rw [beq_iff_eq] at this
      simp only [hΩs, Set.mem_ofPred_eq]
      rw [← hr i]
      rw [this]
    rw [MulAction.mem_stabilizer_iff]
    ext j
    rw [Set.mem_smul_set_iff_inv_smul_mem, Equiv.Perm.smul_def]
    have := hiff ((permOfArr 100 zasNGens[k]!)⁻¹ j)
    simpa using this.symm
  have hΩst : ∀ g ∈ Nrm, ∀ i, g i ∈ Ωs ↔ i ∈ Ωs := by
    intro g hg i
    have hg' : g ∈ Nn := hNeq ▸ hg
    have hle : Nn ≤ MulAction.stabilizer (Equiv.Perm (Fin 100)) Ωs := by
      rw [hNdef, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact hΩgen k hk
    have h1' := MulAction.mem_stabilizer_iff.1 (hle hg')
    have : g i ∈ g • Ωs ↔ i ∈ Ωs := Set.smul_mem_smul_set_iff
    rwa [h1'] at this
  have hΩcard : Nat.card Ωs = 6 := by
    rw [Nat.card_eq_fintype_card]
    simpa [hΩs, Fintype.card_subtype] using h15
  let e6 : Ωs ≃ Fin 6 := Finite.equivFinOfCardEq hΩcard
  let φ₀ : ↥Nrm →* Equiv.Perm Ωs :=
    { toFun := fun g => (g : Equiv.Perm (Fin 100)).subtypePerm (hΩst g.1 g.2)
      map_one' := Equiv.ext fun x => Subtype.ext rfl
      map_mul' := fun g h => Equiv.ext fun x => Subtype.ext rfl }
  let φ : ↥Nrm →* Equiv.Perm (Fin 6) := e6.permCongrHom.toMonoidHom.comp φ₀
  have hφ1 : ∀ g : ↥Nrm, φ g = 1 ↔ ∀ i : Fin 100, i ∈ Ωs → (g : Equiv.Perm (Fin 100)) i = i := by
    intro g
    have h1 : φ g = 1 ↔ φ₀ g = 1 := by
      constructor
      · intro h
        have : e6.permCongrHom (φ₀ g) = e6.permCongrHom 1 := by
          rw [map_one]; exact h
        exact e6.permCongrHom.injective this
      · intro h
        show e6.permCongrHom (φ₀ g) = 1
        rw [h, map_one]
    rw [h1]
    constructor
    · intro h i hi
      have := congrArg (fun p : Equiv.Perm Ωs => (p ⟨i, hi⟩ : Fin 100)) h
      have h2 : ((φ₀ g ⟨i, hi⟩ : Ωs) : Fin 100) = i := by simpa using this
      exact h2
    · intro h
      refine Equiv.ext fun x => Subtype.ext ?_
      exact h x.1 x.2
  have hEN : E ≤ Nrm := by
    refine le_inf (fun x hx => mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩) hEP
    · exact mul_mem (mul_mem hx hh) (inv_mem hx)
    · have := mul_mem (mul_mem (inv_mem hx) hh) hx
      simpa [mul_assoc] using this
  have hker : φ.ker = E.subgroupOf Nrm := by
    ext g
    rw [MonoidHom.mem_ker, hφ1, mem_subgroupOf]
    constructor
    · intro h
      have hg' : (g : Equiv.Perm (Fin 100)) ∈ Nn := by rw [hNeq]; exact g.2
      obtain ⟨j, hj, hr⟩ := hNpts _ hg'
      have hfix : zasFixesOm zasNCert.pts[j]! = true := by
        rw [zasFixesOm, allLt_iff]
        intro i hi
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        by_cases hOm : zasOmVec[i]! = 1
        · right
          have := h ⟨i, hi⟩ hOm
          rw [hr ⟨i, hi⟩, this]
        · left
          exact hOm
      have hk18 := List.all_eq_true.1 h18 _ (zasPts_mem hj)
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk18
      rcases hk18 with h' | h'
      · rw [hfix] at h'
        exact absurd h' (by simp)
      · exact enumOK_mem_of_any hpsE h1 hr h'
    · intro hgE i hi
      obtain ⟨j, hj, hr⟩ := hEpts _ hgE
      have hfix := allLt_iff.1 (List.all_eq_true.1 h17 _ (zasPts_mem hj)) i.1 i.2
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfix
      rcases hfix with h' | h'
      · exact absurd hi h'
      · exact Fin.ext (by rw [← hr i]; exact h')
  have hcardN' : Nat.card Nrm = 11520 := by rw [← hNeq, hcardN, h8]
  have hkercard : Nat.card φ.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hcard16]
  have hrange : Nat.card φ.range = 720 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hkercard, hcardN'] at h1
    omega
  have hsurj : Function.Surjective φ := by
    have : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [hrange, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl)
    exact MonoidHom.range_eq_top.1 this
  have htrans : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ Nrm, a * zasZ0 * a⁻¹ = e := by
    intro e he hne
    obtain ⟨i, hi, hr⟩ := hEpts e he
    have hid : ¬ eqA 100 zasE0Cert.pts[i]! (idA 100) = true := fun h' =>
      hne ((eqA_iff hr rep_idA).1 h')
    have := List.all_eq_true.1 h11 _ (zasPts_mem hi)
    simp only [Bool.or_eq_true] at this
    rcases this with h' | h'
    · exact absurd h' hid
    · obtain ⟨a, ha, hea⟩ := List.any_eq_true.1 h'
      obtain ⟨j, hj, hja⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 ha)
      have hja' : zasNCert.pts[j]! = a := by rw [getElem!_pos _ j hj]; exact hja
      have hva : validA 100 a = true := by
        rw [← hja']
        exact hvalN j hj
      have hra := rep_zasConj hva hz
      have hr' : Rep 100 zasNCert.pts[j]! (permOfArr 100 a) := by
        rw [hja']
        exact rep_of_validA hva
      have hmemNn : permOfArr 100 a ∈ Nn := enumOK_mem hpsN h7 hj hr'
      refine ⟨permOfArr 100 a, by rw [← hNeq]; exact hmemNn, ?_⟩
      exact (eqA_iff hra hr).1 hea
  exact ⟨E, hEdef, hNeq, hEP, hzE, habel, hcard16, ⟨φ, hsurj, hker⟩, htrans⟩

theorem zas_special_spec :
    ∃ E : Subgroup (Equiv.Perm (Fin 100)), IsSpecialIn hs100P zasZ0 E := by
  obtain ⟨E, -, -, h⟩ := zas_special_spec_ext
  exact ⟨E, h⟩

theorem zasMemL_iff {l : List (Array ℕ)} {w : Array ℕ} :
    zasMemL l w = true ↔ ∃ u ∈ l, eqA 100 w u = true := by
  simp [zasMemL, List.any_eq_true]

theorem zasFp_rep {w : Array ℕ} {g : Equiv.Perm (Fin 100)} (h : Rep 100 w g) :
    zasFp w = (Finset.univ.filter fun i : Fin 100 => g i = i).card := by
  unfold zasFp
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  rw [h i]
  exact Fin.ext_iff.symm

theorem card_fix_conj (a z : Equiv.Perm (Fin 100)) :
    (Finset.univ.filter fun i : Fin 100 => (a * z * a⁻¹) i = i).card =
      (Finset.univ.filter fun i : Fin 100 => z i = i).card := by
  refine Finset.card_bij (fun i _ => a⁻¹ i) ?_ ?_ ?_
  · intro i hi
    have hi' : a (z (a⁻¹ i)) = i := (Finset.mem_filter.1 hi).2
    have h2 : z (a⁻¹ i) = a⁻¹ i := by
      have := congrArg (fun x => a⁻¹ x) hi'
      simpa using this
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
  · intro i _ j _ hij
    exact a⁻¹.injective hij
  · intro j hj
    have hj' : z j = j := (Finset.mem_filter.1 hj).2
    refine ⟨a j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    show a (z (a⁻¹ (a j))) = a j
    simp [hj']

theorem zas_uniq_spec :
    ∀ F₁ F₂ : Subgroup (Equiv.Perm (Fin 100)), F₁ ≤ zasT0 → F₂ ≤ zasT0 →
      IsElemAbelian 2 F₁ → IsElemAbelian 2 F₂ → Nat.card F₁ = 16 → Nat.card F₂ = 16 →
      zasZ0 ∈ F₁ → zasZ0 ∈ F₂ →
      (∀ e ∈ F₁, e ≠ 1 → ∃ a : Equiv.Perm (Fin 100), a * zasZ0 * a⁻¹ = e) →
      (∀ e ∈ F₂, e ≠ 1 → ∃ a : Equiv.Perm (Fin 100), a * zasZ0 * a⁻¹ = e) →
      ∃ t ∈ zasT0, F₁.map (MulAut.conj t).toMonoidHom = F₂ := by
  classical
  have h : zasUniqOK = true := Certificates.certificate117003
  simp only [zasUniqOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hvz, hz1, hT, hTsize, hE, hcomp, hnon, hconj⟩ := h
  have hpsT : ∀ p ∈ zasTKeys, p < 100 := by
    intro p hp
    simp only [zasTKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have hpsE : ∀ p ∈ zasEKeys, p < 100 := fun p hp => List.mem_range.1 hp
  have hz : Rep 100 s5Z zasZ0 := rep_of_validA hvz
  have hz1' : zasZ0 ≠ 1 := by
    intro h'
    have := (eqA_iff hz rep_idA).2 h'
    rw [this] at hz1
    simp at hz1
  set Ej : ℕ → Subgroup (Equiv.Perm (Fin 100)) := fun j =>
    Subgroup.closure (permsA 100 (zasEGens j)) with hEj
  have hEfacts : ∀ j < 8, enumOK 100 (zasEGens j) zasEKeys (zasEC j) = true ∧
      (zasEC j).pts.size = 16 ∧ zasMem (zasEC j) s5Z = true := by
    intro j hj
    have := List.all_eq_true.1 hE j (List.mem_range.2 hj)
    simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using this
  have hEcard : ∀ j < 8, Nat.card (Ej j) = 16 := by
    intro j hj
    obtain ⟨h1, h2, -⟩ := hEfacts j hj
    exact (enumOK_spec hpsE h1).2.1.trans h2
  have hzEj : ∀ j < 8, zasZ0 ∈ Ej j := by
    intro j hj
    obtain ⟨h1, -, h3⟩ := hEfacts j hj
    exact enumOK_mem_of_any hpsE h1 hz h3
  have hclass : ∀ F : Subgroup (Equiv.Perm (Fin 100)), F ≤ zasT0 → IsElemAbelian 2 F →
      Nat.card F = 16 → zasZ0 ∈ F →
      (∀ e ∈ F, e ≠ 1 → ∃ a : Equiv.Perm (Fin 100), a * zasZ0 * a⁻¹ = e) →
      ∃ j, (j = 0 ∨ j = 5) ∧ F = Ej j := by
    intro F hFT hab hFc hzF hconjF
    have hFT' : F ≤ Subgroup.closure (permsA 100 zasTGens) := hFT
    have hinv : ∀ x ∈ F, x ≠ 1 → ∃ xx ∈ zasInvs, Rep 100 xx x := by
      intro x hx hx1
      obtain ⟨i, hi, hr⟩ := enumOK_exists_rep hpsT hT (hFT' hx)
      refine ⟨zasTCert.pts[i]!, ?_, hr⟩
      unfold zasInvs
      rw [List.mem_filter]
      refine ⟨zasPts_mem hi, ?_⟩
      have hsq : x * x = 1 := by
        have := hab.2 x hx
        rwa [pow_two] at this
      simp only [zasIsInv, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨(eqA_iff (rep_compA hr hr) rep_idA).2 hsq, ?_⟩
      exact Bool.eq_false_of_ne_true (mt (eqA_iff hr rep_idA).1 hx1)
    obtain ⟨a, haF, b, hbF, c, hcF, ha, hb, hc, hFeq⟩ := exists_gen_card_sixteen hab hFc hzF hz1'
    have ha1 : a ≠ 1 := fun h' => ha (h' ▸ one_mem _)
    have hb1 : b ≠ 1 := fun h' => hb (h' ▸ one_mem _)
    have hc1 : c ≠ 1 := fun h' => hc (h' ▸ one_mem _)
    obtain ⟨aa, haaI, hra⟩ := hinv a haF ha1
    obtain ⟨bb, hbbI, hrb⟩ := hinv b hbF hb1
    obtain ⟨cc, hccI, hrc⟩ := hinv c hcF hc1
    have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
      have := hab.1
      rw [isMulCommutative_iff_of_setLike] at this
      exact this
    have hK2 : ∀ u ∈ zasK2 aa, ∃ g ∈ zpowers zasZ0 ⊔ zpowers a, Rep 100 u g := by
      intro u hu
      simp only [zasK2, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, rep_idA⟩
      · exact ⟨zasZ0, mem_sup_left (mem_zpowers _), hz⟩
      · exact ⟨a, mem_sup_right (mem_zpowers _), hra⟩
      · exact ⟨zasZ0 * a, mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)),
          rep_compA hz hra⟩
    have hK3 : ∀ u ∈ zasK3 aa bb, ∃ g ∈ zpowers zasZ0 ⊔ zpowers a ⊔ zpowers b, Rep 100 u g := by
      intro u hu
      simp only [zasK3, List.mem_append, List.mem_map] at hu
      rcases hu with hu | ⟨u', hu', rfl⟩
      · obtain ⟨g, hg, hr⟩ := hK2 u hu
        exact ⟨g, mem_sup_left hg, hr⟩
      · obtain ⟨g, hg, hr⟩ := hK2 u' hu'
        exact ⟨b * g, mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hg), rep_compA hrb hr⟩
    have hmemF : ∀ x ∈ F, ∀ y ∈ F, ∀ (u v : Array ℕ), Rep 100 u x → Rep 100 v y → True := by
      intros; trivial
    have h1 := List.all_eq_true.1 hcomp aa haaI
    simp only [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exfalso
      obtain ⟨u, hu, hue⟩ := zasMemL_iff.1 h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ha1 ((eqA_iff hra rep_idA).1 hue)
      · exact ha (((eqA_iff hra hz).1 hue) ▸ mem_zpowers _)
    have h2 := List.all_eq_true.1 h1 bb hbbI
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
    rcases h2 with (h2 | h2) | h2
    · exfalso
      have : zasComm aa bb = true := by
        unfold zasComm
        exact (eqA_iff (rep_compA hra hrb) (rep_compA hrb hra)).2 (hcomm a haF b hbF)
      rw [this] at h2
      exact absurd h2 (by simp)
    · exfalso
      obtain ⟨u, hu, hue⟩ := zasMemL_iff.1 h2
      obtain ⟨g, hg, hr⟩ := hK2 u hu
      exact hb ((eqA_iff hrb hr).1 hue ▸ hg)
    have h3 := List.all_eq_true.1 h2 cc hccI
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h3
    rcases h3 with ((h3 | h3) | h3) | h3
    · exfalso
      have : zasComm aa cc = true := by
        unfold zasComm
        exact (eqA_iff (rep_compA hra hrc) (rep_compA hrc hra)).2 (hcomm a haF c hcF)
      rw [this] at h3
      exact absurd h3 (by simp)
    · exfalso
      have : zasComm bb cc = true := by
        unfold zasComm
        exact (eqA_iff (rep_compA hrb hrc) (rep_compA hrc hrb)).2 (hcomm b hbF c hcF)
      rw [this] at h3
      exact absurd h3 (by simp)
    · exfalso
      obtain ⟨u, hu, hue⟩ := zasMemL_iff.1 h3
      obtain ⟨g, hg, hr⟩ := hK3 u hu
      exact hc ((eqA_iff hrc hr).1 hue ▸ hg)
    obtain ⟨j, hj, hjabc⟩ : ∃ j, j < 8 ∧ zasMem (zasEC j) aa = true ∧ zasMem (zasEC j) bb = true ∧
        zasMem (zasEC j) cc = true := by
      unfold zasInSome at h3
      obtain ⟨j, hj, hj'⟩ := List.any_eq_true.1 h3
      refine ⟨j, List.mem_range.1 hj, ?_⟩
      simpa only [Bool.and_eq_true, and_assoc] using hj'
    obtain ⟨hjaa, hjbb, hjcc⟩ := hjabc
    obtain ⟨hEj1, -, -⟩ := hEfacts j hj
    have haE : a ∈ Ej j := enumOK_mem_of_any hpsE hEj1 hra hjaa
    have hbE : b ∈ Ej j := enumOK_mem_of_any hpsE hEj1 hrb hjbb
    have hcE : c ∈ Ej j := enumOK_mem_of_any hpsE hEj1 hrc hjcc
    have hzE : zasZ0 ∈ Ej j := hzEj j hj
    have hFle : F ≤ Ej j := by
      rw [hFeq]
      exact sup_le (sup_le (sup_le (zpowers_le.2 hzE) (zpowers_le.2 haE)) (zpowers_le.2 hbE))
        (zpowers_le.2 hcE)
    have hFE : F = Ej j := Subgroup.eq_of_le_of_card_ge hFle (by rw [hEcard j hj, hFc])
    refine ⟨j, ?_, hFE⟩
    by_contra hjne
    push Not at hjne
    have hn := List.all_eq_true.1 hnon j (List.mem_range.2 hj)
    simp only [Bool.or_eq_true, beq_iff_eq] at hn
    rcases hn with (hn | hn) | hn
    · exact hjne.1 (by simpa [zasSpecIdx] using hn)
    · exact hjne.2 (by simpa [zasSpecIdx] using hn)
    · obtain ⟨w, hw, hwp⟩ := List.any_eq_true.1 hn
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hwp
      obtain ⟨hw1, hw2⟩ := hwp
      obtain ⟨hEj1, -, -⟩ := hEfacts j hj
      obtain ⟨hmemj, -, hvalj⟩ := enumOK_spec hpsE hEj1
      obtain ⟨i, hi, hiw⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hw)
      have hiw' : (zasEC j).pts[i]! = w := by rw [getElem!_pos _ i hi]; exact hiw
      have hvw : validA 100 w = true := by rw [← hiw']; exact hvalj i hi
      have hrw := rep_of_validA hvw
      have hxF : permOfArr 100 w ∈ F := by
        rw [hFE]
        refine enumOK_mem hpsE hEj1 hi ?_
        rw [hiw']
        exact hrw
      have hx1 : permOfArr 100 w ≠ 1 := by
        intro h'
        have := (eqA_iff hrw rep_idA).2 h'
        rw [this] at hw1
        exact absurd hw1 (by simp)
      obtain ⟨a', ha'⟩ := hconjF _ hxF hx1
      apply hw2
      rw [zasFp_rep hrw, zasFp_rep hz, ← ha', card_fix_conj]
  obtain ⟨tt, htT, htconj⟩ : ∃ t ∈ zasT0, (Ej 0).map (MulAut.conj t).toMonoidHom = Ej 5 := by
    obtain ⟨t, ht, ht'⟩ := List.any_eq_true.1 hconj
    obtain ⟨i, hi, hiw⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 ht)
    have hit : zasTCert.pts[i]! = t := by rw [getElem!_pos _ i hi]; exact hiw
    obtain ⟨-, -, hvalT⟩ := enumOK_spec hpsT hT
    have hvt : validA 100 t = true := by rw [← hit]; exact hvalT i hi
    have hrt : Rep 100 zasTCert.pts[i]! (permOfArr 100 t) := by
      rw [hit]
      exact rep_of_validA hvt
    refine ⟨permOfArr 100 t, enumOK_mem hpsT hT hi hrt, ?_⟩
    obtain ⟨hE5, -, -⟩ := hEfacts 5 (by norm_num)
    have hle : (Ej 0).map (MulAut.conj (permOfArr 100 t)).toMonoidHom ≤ Ej 5 := by
      rw [Subgroup.map_le_iff_le_comap]
      show Subgroup.closure (permsA 100 (zasEGens 0)) ≤ _
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      have hk4 : k < 4 := hk
      have hgen := List.all_eq_true.1 ht' k (List.mem_range.2 hk4)
      have hgv : validA 100 (zasEGens 0)[k]! = true := by
        obtain ⟨hE0, -, -⟩ := hEfacts 0 (by norm_num)
        exact enumOK_gens_valid hE0 (by simpa [zasEGens] using hk4)
      have hr := rep_zasConj hvt (rep_of_validA hgv)
      have := enumOK_mem_of_any hpsE hE5 hr hgen
      simpa [MulAut.conj_apply] using this
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (permOfArr 100 t)).injective, hEcard 0 (by norm_num),
      hEcard 5 (by norm_num)]
  intro F₁ F₂ hF₁ hF₂ hab₁ hab₂ hc₁ hc₂ hz₁ hz₂ hcj₁ hcj₂
  obtain ⟨j₁, hj₁, hE₁⟩ := hclass F₁ hF₁ hab₁ hc₁ hz₁ hcj₁
  obtain ⟨j₂, hj₂, hE₂⟩ := hclass F₂ hF₂ hab₂ hc₂ hz₂ hcj₂
  have hid : ∀ E : Subgroup (Equiv.Perm (Fin 100)),
      E.map (MulAut.conj (1 : Equiv.Perm (Fin 100))).toMonoidHom = E := by
    intro E
    ext x
    simp [Subgroup.mem_map]
  rcases hj₁ with rfl | rfl <;> rcases hj₂ with rfl | rfl
  · exact ⟨1, one_mem _, by rw [hE₁, hE₂]; exact hid _⟩
  · exact ⟨tt, htT, by rw [hE₁, hE₂]; exact htconj⟩
  · refine ⟨tt⁻¹, inv_mem htT, ?_⟩
    rw [hE₁, hE₂, ← htconj]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨z', hz', rfl⟩, rfl⟩
      simpa [mul_assoc] using hz'
    · intro hx
      exact ⟨tt * x * tt⁻¹, ⟨x, hx, rfl⟩, by group⟩
  · exact ⟨1, one_mem _, by rw [hE₁, hE₂]; exact hid _⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
