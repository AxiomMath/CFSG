
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvBase

public import Certificates.Certificate3961
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem checkFacts : CheckFacts := by
  have h := Certificates.certificate3961
  simp only [u43InvCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨fun j hj => by simpa [Bool.and_eq_true] using h3 j hj, h4, h5, h6, h7,
    fun j hj => h8 j hj, h9, h10, h11, fun k hk => h12 k hk, fun k hk => h13 k hk, h14⟩

theorem rep_hTab (k : ℕ) :
    Rep 820 (hTab k) (psi (hElt k)) := by
  have hf := checkFacts
  have hlen := hGens_length
  have hnl : 0 < 2 * hGensG.length := by have := hf.hpos; omega
  unfold hTab hElt
  rw [hlen]
  exact rep_treeG rep_one hnl (fun t g l hl h => rep_mulStep hGens_length rep_hGens
    (fun j hj => (hf.gens j (by omega)).1) t g l hl h) hPar hLab fuel k

theorem hEnum :
    (∀ k, hElt k ∈ hSub) ∧ (∀ h ∈ hSub, ∃ k < 1152, hElt k = h) ∧
      (∀ i < 1152, ∀ j < 1152, hElt i = hElt j → i = j) := by
  have hf := checkFacts
  exact enum_spec hGens_length rep_hGens (fun j hj => (hf.gens j (by rw [hGens_length]; exact hj)).1)
    (by have := hf.hpos; rw [hGens_length] at this; exact this) (by norm_num) hf.hclosed hf.hdist

theorem card_hSub :
    Nat.card hSub = 1152 := by
  obtain ⟨hmem, hsurj, hinj⟩ := hEnum
  have : Function.Bijective (fun k : Fin 1152 => (⟨hElt k, hmem k⟩ : hSub)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
    · intro h
      obtain ⟨k, hk, hkh⟩ := hsurj h h.2
      exact ⟨⟨k, hk⟩, Subtype.ext hkh⟩
  rw [← Nat.card_eq_of_bijective _ this]
  simp

theorem rep_pGens :
    ∀ j < pGensG.length, Rep 820 pGens[j]! (psi (pGensG.getD j 1)) := by
  intro j hj
  have hj' : j < pGenIdx.length := by simpa [pGensG] using hj
  rw [pGens, getElem!_map_lt _ _ hj', pGensG, getD_map_lt _ _ hj']
  exact rep_hTab _

theorem pEnum :
    (∀ k, pElt k ∈ pSub) ∧ (∀ h ∈ pSub, ∃ k < 128, pElt k = h) ∧
      (∀ i < 128, ∀ j < 128, pElt i = pElt j → i = j) := by
  have hf := checkFacts
  exact enum_spec pGens_length rep_pGens
    (fun j hj => hf.pinv j (by rw [pGens_length]; exact hj))
    (by have := hf.ppos; rw [pGens_length] at this; exact this) (by norm_num) hf.pclosed hf.pdist

theorem card_pSub :
    Nat.card pSub = 128 := by
  obtain ⟨hmem, hsurj, hinj⟩ := pEnum
  have : Function.Bijective (fun k : Fin 128 => (⟨pElt k, hmem k⟩ : pSub)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
    · intro h
      obtain ⟨k, hk, hkh⟩ := hsurj h h.2
      exact ⟨⟨k, hk⟩, Subtype.ext hkh⟩
  rw [← Nat.card_eq_of_bijective _ this]
  simp

theorem rep_pTab (k : ℕ) :
    Rep 820 (pTab k) (psi (pElt k)) := by
  have hf := checkFacts
  have hnl : 0 < 2 * pGensG.length := by have := hf.ppos; rw [pGens_length] at this; omega
  unfold pTab pElt
  rw [pGens_length]
  exact rep_treeG rep_one hnl (fun t g l hl h => rep_mulStep pGens_length rep_pGens
    (fun j hj => hf.pinv j (by rw [pGens_length]; exact hj)) t g l hl h) pPar pLab fuel k

theorem cElt_inj :
    ∀ i < 2835, ∀ j < 2835, cElt i = cElt j → i = j := by
  intro i hi j hj hij
  apply distinctOK_spec checkFacts.cdist i hi j hj
  have key : ∀ (x : ℕ) (hx : x < 820), (cTab i)[x]! = (cTab j)[x]! := fun x hx => by
    rw [(rep_cTab i).apply hx, (rep_cTab j).apply hx, hij]
  simp [fpKey, key 0 (by norm_num), key 1 (by norm_num), key 9 (by norm_num)]

theorem card_centralizer_le :
    Nat.card (Subgroup.centralizer ({xElt} : Set X₀)) ≤ 1152 := by
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({xElt} : Set X₀))
  rw [Subgroup.index_centralizer_eq_ncard, card_X₀] at h1
  have hsub : (cElt '' ((Finset.range 2835 : Finset ℕ) : Set ℕ)) ⊆ conjugatesOf xElt := by
    rintro _ ⟨k, -, rfl⟩
    obtain ⟨d, hd⟩ := cElt_conj k
    show IsConj xElt (cElt k)
    rw [isConj_iff]
    exact ⟨d, hd.symm⟩
  have h2 : 2835 ≤ (conjugatesOf xElt).ncard := by
    have hinj : Set.InjOn cElt ((Finset.range 2835 : Finset ℕ) : Set ℕ) := by
      intro i hi j hj hij
      exact cElt_inj i (by simpa using hi) j (by simpa using hj) hij
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range] at this
  nlinarith

theorem hSub_le_centralizer :
    hSub ≤ Subgroup.centralizer ({xElt} : Set X₀) := by
  have hf := checkFacts
  unfold hSub
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hj' : j < hGens.length := by rw [hGens_length]; exact hj
  have hr := rep_hGens j hj
  rw [List.getD_eq_getElem _ _ hj] at hr
  have heq := (eqA_iff (rep_compA hr rep_tabA) (rep_compA rep_tabA hr)).1 (hf.gens j hj').2
  rw [← map_mul, ← map_mul] at heq
  exact (psi_injective heq).symm

theorem hSub_eq_centralizer :
    hSub = Subgroup.centralizer ({xElt} : Set X₀) :=
  Subgroup.eq_of_le_of_card_ge hSub_le_centralizer (by rw [card_hSub]; exact card_centralizer_le)

theorem fuse_xElt :
    ∀ u ∈ pSub, u * u = 1 → u ≠ 1 → ∃ d : X₀, u = d * xElt * d⁻¹ := by
  intro u hu h2 hne
  obtain ⟨k, hk, rfl⟩ := pEnum.2.1 u hu
  have hfk := checkFacts.fuse k hk
  have hin := (isInvol_iff (rep_pTab k)).2 ⟨h2, hne⟩
  unfold fuseOK at hfk
  rw [hin] at hfk
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range] at hfk
  obtain ⟨j, -, hj⟩ := hfk
  have := (eqA_iff (rep_pTab k) (rep_cTab j)).1 hj
  obtain ⟨d, hd⟩ := cElt_conj j
  exact ⟨d, by rw [psi_injective this, hd]⟩

theorem u43_isConj_xElt {u : X₀}
    (hu : orderOf u = 2) : IsConj xElt u := by
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hu2 : u * u = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hne : u ≠ 1 := by
    rintro rfl
    simp at hu
  have hidx : ¬ 2 ∣ pSub.index := by
    have h := Subgroup.card_mul_index pSub
    rw [card_pSub, card_X₀] at h
    have : pSub.index = 25515 := by omega
    rw [this]
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨g, hg⟩ := CFSG.ShultStronglyClosedTI.OddPrimeInverters.exists_conj_mem_of_not_dvd_index
    pSub hidx hz
  have hv2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    have : (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    rw [this, hu2]
    group
  have hvne : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hne
    have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [this, h]
    group
  obtain ⟨d, hd⟩ := fuse_xElt _ hg hv2 hvne
  rw [isConj_iff]
  refine ⟨g⁻¹ * d, ?_⟩
  have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
  rw [this, hd]
  group

theorem five_lt_orderOf_z0 :
    5 < orderOf (xElt * (g0Elt * xElt * g0Elt⁻¹)) := by
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hg0 := checkFacts.g0
  simp only [g0OK, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hg0
  obtain ⟨hginv, h1, h2, h3, h4, h5⟩ := hg0
  have hg : Rep 820 (wordTab g0Word) (psi g0Elt) := rep_wordTab _
  have hc : Rep 820 (conjTab (wordTab g0Word) tabA) (psi (g0Elt * xElt * g0Elt⁻¹)) := by
    unfold conjTab
    rw [map_mul, map_mul]
    exact rep_compA (rep_compA hg rep_tabA) (rep_inv' hg hginv)
  have hz : Rep 820 (compA 820 tabA (conjTab (wordTab g0Word) tabA))
      (psi (xElt * (g0Elt * xElt * g0Elt⁻¹))) := by
    rw [map_mul]
    exact rep_compA rep_tabA hc
  have hne : ∀ k : ℕ, (!eqA 820 (powTab (compA 820 tabA (conjTab (wordTab g0Word) tabA)) k)
      (idA 820)) = true → (xElt * (g0Elt * xElt * g0Elt⁻¹)) ^ k ≠ 1 := by
    intro k hk hpow
    have := (eqA_one_iff (rep_powTab hz k)).2 hpow
    rw [this] at hk
    simp at hk
  by_contra hlt
  push Not at hlt
  have hpos : 0 < orderOf (xElt * (g0Elt * xElt * g0Elt⁻¹)) := orderOf_pos _
  have hp := pow_orderOf_eq_one (xElt * (g0Elt * xElt * g0Elt⁻¹))
  interval_cases h : orderOf (xElt * (g0Elt * xElt * g0Elt⁻¹))
  · exact hne 1 h1 hp
  · exact hne 2 h2 hp
  · exact hne 3 h3 hp
  · exact hne 4 h4 hp
  · exact hne 5 h5 hp

theorem u43_exists_conj_orderOf
    {u : X₀} (hu : orderOf u = 2) : ∃ g : X₀, 5 < orderOf (u * (g * u * g⁻¹)) := by
  obtain ⟨d, rfl⟩ := isConj_iff.1 (u43_isConj_xElt hu)
  refine ⟨d * g0Elt * d⁻¹, ?_⟩
  have : d * xElt * d⁻¹ * (d * g0Elt * d⁻¹ * (d * xElt * d⁻¹) * (d * g0Elt * d⁻¹)⁻¹) =
      d * (xElt * (g0Elt * xElt * g0Elt⁻¹)) * d⁻¹ := by group
  rw [this, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact five_lt_orderOf_z0

theorem u43_F2_xElt {b : X₀}
    (hb : orderOf b = 2) (hbx : b ≠ xElt) (hcomm : b * xElt = xElt * b) :
    ∃ c : X₀, c * xElt = xElt * c ∧ b * (c * b * c⁻¹) ≠ (c * b * c⁻¹) * b := by
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hb2 : b * b = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one b
    rwa [hb] at this
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb
  have hbH : b ∈ hSub := by
    rw [hSub_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm.symm
  obtain ⟨k, hk, rfl⟩ := hEnum.2.1 b hbH
  have hf := checkFacts.f2 k hk
  have hin := (isInvol_iff (rep_hTab k)).2 ⟨hb2, hb1⟩
  have hxk : eqA 820 (hTab k) tabA = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hbx (psi_injective ((eqA_iff (rep_hTab k) rep_tabA).1 h))
  unfold f2OK at hf
  rw [hin, hxk] at hf
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at hf
  obtain ⟨⟨hw, hwinv⟩, hne⟩ := hf
  have hrw := rep_hTab f2Wit[k]!
  have hcc : Rep 820 (conjTab (hTab f2Wit[k]!) (hTab k))
      (psi (hElt f2Wit[k]! * hElt k * (hElt f2Wit[k]!)⁻¹)) := by
    unfold conjTab
    rw [map_mul, map_mul]
    exact rep_compA (rep_compA hrw (rep_hTab k)) (rep_inv' hrw hwinv)
  refine ⟨hElt f2Wit[k]!, ?_, ?_⟩
  · have hcH : hElt f2Wit[k]! ∈ hSub := hEnum.1 _
    rw [hSub_eq_centralizer, Subgroup.mem_centralizer_iff] at hcH
    exact (hcH xElt rfl).symm
  · intro heq
    have h1 := rep_compA (rep_hTab k) hcc
    have h2 := rep_compA hcc (rep_hTab k)
    rw [← map_mul] at h1 h2
    rw [heq] at h1
    have := (eqA_iff h1 h2).2 rfl
    rw [this] at hne
    simp at hne

theorem u43_F2 {a b : X₀}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hba : b ≠ a) (hcomm : b * a = a * b) :
    ∃ c : X₀, c * a = a * c ∧ b * (c * b * c⁻¹) ≠ (c * b * c⁻¹) * b := by
  obtain ⟨d, rfl⟩ := isConj_iff.1 (u43_isConj_xElt ha)
  obtain ⟨b', rfl⟩ : ∃ b', b = d * b' * d⁻¹ := ⟨d⁻¹ * b * d, by group⟩
  rw [orderOf_conj'] at hb
  have hbx : b' ≠ xElt := fun h => hba (by rw [h])
  have hc := (conj_comm_iff d b' xElt).1 hcomm
  obtain ⟨c', hc', hne'⟩ := u43_F2_xElt hb hbx hc
  refine ⟨d * c' * d⁻¹, (conj_comm_iff d c' xElt).2 hc', ?_⟩
  have e : d * c' * d⁻¹ * (d * b' * d⁻¹) * (d * c' * d⁻¹)⁻¹ = d * (c' * b' * c'⁻¹) * d⁻¹ := by
    group
  rw [e]
  intro h
  exact hne' ((conj_comm_iff d b' (c' * b' * c'⁻¹)).1 h)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
