
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutCheck
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvBase

@[expose] public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

structure AutFacts : Prop where
  dinv : isInvA 820 dTab (invCand 820 dTab) = true
  sinv : isInvA 820 sTab (invCand 820 sTab) = true
  conjN : ∀ g ∈ [dTab, invCand 820 dTab, sTab, invCand 820 sTab], ∀ h ∈ [tabA, tabB],
    siftA 820 (rawLevels 820 chainS baseArr) baseArr 0 (conjTab g h) = true
  cos : ∀ i < 4, ∀ j < 2, isInvA 820 (dsElt i j) (invCand 820 (dsElt i j)) = true ∧
    ∀ k < 4, ∀ l < 2, (i = k ∧ j = l) ∨
      siftA 820 (rawLevels 820 chainS baseArr) baseArr 0
        (compA 820 (invCand 820 (dsElt i j)) (dsElt k l)) = false
  cen : ∀ bp ∈ cenGens, cenOK bp = true
  bases : cenGens.map (·.1) = [0, 4]
  trans : ∀ r < 820, transOK r = true

abbrev Gp : Type := Equiv.Perm (Fin 820)

noncomputable def Nsub : Subgroup Gp := psi.range

noncomputable abbrev Nrm : Subgroup Gp := Subgroup.normalizer (Nsub : Set Gp)

noncomputable def dPerm : Gp := permOfArr 820 dTab

noncomputable def sPerm : Gp := permOfArr 820 sTab

theorem rep_dTab (hf : AutFacts) : Rep 820 dTab dPerm := (rep_permOfArr hf.dinv).1
theorem rep_dTab_inv (hf : AutFacts) : Rep 820 (invCand 820 dTab) dPerm⁻¹ :=
  (rep_permOfArr hf.dinv).2
theorem rep_sTab (hf : AutFacts) : Rep 820 sTab sPerm := (rep_permOfArr hf.sinv).1
theorem rep_sTab_inv (hf : AutFacts) : Rep 820 (invCand 820 sTab) sPerm⁻¹ :=
  (rep_permOfArr hf.sinv).2

theorem closure_range :
    Subgroup.closure ({psi xElt, psi yElt} : Set Gp) = Nsub := by
  have hmap : (Subgroup.closure ({xElt, yElt} : Set X₀)).map psi =
      Subgroup.closure {psi xElt, psi yElt} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [← hmap, closure_xy]
  simp [Nsub, MonoidHom.range_eq_map]

noncomputable def chainQ' : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

theorem chainQ'_eq :
    chainQ'.originalSubgroup = Subgroup.closure {psi xElt, psi yElt} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [chainQ', Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have e0 : permOfArr 820 chainS[0]! = psi xElt := Rep.unique h0 rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt := Rep.unique h1 rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem sift_iff {t : Array ℕ} {g : Gp} (hg : Rep 820 t g) :
    siftA 820 (rawLevels 820 chainS baseArr) baseArr 0 t = true ↔ g ∈ Nsub := by
  have h := siftA_iff_mem_originalSubgroup (Q := chainQ')
    (chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv) (by norm_num) chain_check hg
  rw [chainQ'_eq, closure_range] at h
  exact h

theorem conj_mem_N {g : Gp} (hx : g * psi xElt * g⁻¹ ∈ Nsub)
    (hy : g * psi yElt * g⁻¹ ∈ Nsub) : ∀ n ∈ Nsub, g * n * g⁻¹ ∈ Nsub := by
  intro n hn
  obtain ⟨u, rfl⟩ := hn
  have hu : u ∈ Subgroup.closure ({xElt, yElt} : Set X₀) := by rw [closure_xy]; trivial
  induction hu using Subgroup.closure_induction with
  | mem u hu => rcases hu with rfl | rfl <;> assumption
  | one => simp
  | mul u v _ _ hu hv =>
    have : g * psi (u * v) * g⁻¹ = (g * psi u * g⁻¹) * (g * psi v * g⁻¹) := by
      rw [map_mul]; group
    rw [this]
    exact Nsub.mul_mem hu hv
  | inv u _ hu =>
    have : g * psi u⁻¹ * g⁻¹ = (g * psi u * g⁻¹)⁻¹ := by
      rw [map_inv]; group
    rw [this]
    exact Nsub.inv_mem hu

theorem mem_Nrm_of_gens {g : Gp}
    (h1 : g * psi xElt * g⁻¹ ∈ Nsub) (h2 : g * psi yElt * g⁻¹ ∈ Nsub) : g ∈ Nrm := by
  have hfin : Finite Nsub := inferInstance
  have hle : Nsub.map (MulAut.conj g).toMonoidHom ≤ Nsub := by
    rintro _ ⟨n, hn, rfl⟩
    exact conj_mem_N h1 h2 n hn
  have hcard : Nat.card (Nsub.map (MulAut.conj g).toMonoidHom) = Nat.card Nsub :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : Nsub.map (MulAut.conj g).toMonoidHom = Nsub :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem rep_conjTab {c b : Array ℕ} {g h : Gp} (hc : Rep 820 c g) (hb : Rep 820 b h)
    (hi : Rep 820 (invCand 820 c) g⁻¹) : Rep 820 (conjTab c b) (g * h * g⁻¹) :=
  rep_compA (rep_compA hc hb) hi

theorem rep_psi_x : Rep 820 tabA (psi xElt) := rep_tabA
theorem rep_psi_y : Rep 820 tabB (psi yElt) := rep_tabB

theorem dPerm_mem (hf : AutFacts) : dPerm ∈ Nrm := by
  have hx := (sift_iff (rep_conjTab (rep_dTab hf) rep_tabA (rep_dTab_inv hf))).1
    (hf.conjN dTab (by simp) tabA (by simp))
  have hy := (sift_iff (rep_conjTab (rep_dTab hf) rep_tabB (rep_dTab_inv hf))).1
    (hf.conjN dTab (by simp) tabB (by simp))
  exact mem_Nrm_of_gens hx hy

theorem sPerm_mem (hf : AutFacts) : sPerm ∈ Nrm := by
  have hx := (sift_iff (rep_conjTab (rep_sTab hf) rep_tabA (rep_sTab_inv hf))).1
    (hf.conjN sTab (by simp) tabA (by simp))
  have hy := (sift_iff (rep_conjTab (rep_sTab hf) rep_tabB (rep_sTab_inv hf))).1
    (hf.conjN sTab (by simp) tabB (by simp))
  exact mem_Nrm_of_gens hx hy

theorem Nsub_le_Nrm : Nsub ≤ Nrm := by
  intro n hn
  rw [Nrm, Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Nsub.mul_mem (Nsub.mul_mem hn hh) (Nsub.inv_mem hn)
  · intro hh
    have := Nsub.mul_mem (Nsub.mul_mem (Nsub.inv_mem hn) hh) hn
    simpa [mul_assoc] using this

theorem rep_powTab_perm {t : Array ℕ} {g : Gp} (h : Rep 820 t g) :
    ∀ k, Rep 820 (powTab t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (rep_powTab_perm h k)

noncomputable def dsPerm (i j : ℕ) : Gp := dPerm ^ i * sPerm ^ j

theorem rep_dsElt (hf : AutFacts) (i j : ℕ) : Rep 820 (dsElt i j) (dsPerm i j) :=
  rep_compA (rep_powTab_perm (rep_dTab hf) i) (rep_powTab_perm (rep_sTab hf) j)

theorem dsPerm_mem (hf : AutFacts) (i j : ℕ) :
    dsPerm i j ∈ Nrm :=
  Nrm.mul_mem (Nrm.pow_mem (dPerm_mem hf) i) (Nrm.pow_mem (sPerm_mem hf) j)

theorem eight_le_index (hf : AutFacts) :
    8 ≤ (Nsub.subgroupOf Nrm).index := by
  let f : Fin 4 × Fin 2 → Nrm ⧸ Nsub.subgroupOf Nrm := fun p =>
    QuotientGroup.mk ⟨dsPerm p.1 p.2, dsPerm_mem hf p.1 p.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h' := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h'
    obtain ⟨hinv, hkl⟩ := hf.cos i i.2 j j.2
    rcases hkl k k.2 l l.2 with ⟨hik, hjl⟩ | hfalse
    · exact Prod.ext (Fin.ext hik) (Fin.ext hjl)
    · exfalso
      have hrep := rep_compA (rep_inv_of_isInvA (rep_dsElt hf i j) hinv) (rep_dsElt hf k l)
      have h3 := (sift_iff hrep).2 (by simpa using h')
      rw [hfalse] at h3
      exact Bool.false_ne_true h3
  have := Nat.card_le_card_of_injective f hinj
  simpa [Subgroup.index] using this

theorem card_Nsub :
    Nat.card Nsub = 3265920 := by
  rw [← card_X₀]
  exact (Nat.card_congr (MonoidHom.ofInjective psi_injective).toEquiv).symm

theorem le_card_Nrm (hf : AutFacts) : 8 * 3265920 ≤ Nat.card Nrm := by
  have h1 := Subgroup.card_mul_index (Nsub.subgroupOf Nrm)
  have h2 : Nat.card (Nsub.subgroupOf Nrm) = Nat.card Nsub :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Nsub_le_Nrm).toEquiv
  have h3 := eight_le_index hf
  rw [h2, card_Nsub] at h1
  nlinarith

theorem rep_wordPsi (w : List ℕ) :
    Rep 820 (wordTab w) (psi (wordElt w)) := rep_wordTab w

theorem centralizer_trivial (hf : AutFacts) (z : Gp)
    (hz : ∀ n ∈ Nsub, z * n = n * z) : z = 1 := by
  have hfix : ∀ b ∈ cenGens.map (·.1), ∀ hb : b < 820, z ⟨b, hb⟩ = ⟨b, hb⟩ := by
    intro b hb hb820
    obtain ⟨bp, hbp, rfl⟩ := List.mem_map.1 hb
    have hcen := hf.cen bp hbp
    unfold cenOK at hcen
    rw [Bool.and_eq_true] at hcen
    obtain ⟨hc1, hc2⟩ := hcen
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hc1
    have hc2 := List.all_eq_true.1 hc2
    set q : Fin 820 := z ⟨bp.1, hb820⟩ with hq
    have hstab : ∀ gt ∈ bp.2, ∃ s ∈ Nsub, Rep 820 (stabElt gt) s := by
      intro gt hgt
      refine ⟨(psi (wordElt gt.2))⁻¹ * psi (wordElt gt.1), ?_, ?_⟩
      · exact Nsub.mul_mem (Nsub.inv_mem ⟨_, rfl⟩) ⟨_, rfl⟩
      · exact rep_compA (rep_inv_of_isInvA (rep_wordPsi gt.2) (hc1 gt hgt).1) (rep_wordPsi gt.1)
    have hall : ∀ gt ∈ bp.2, (stabElt gt)[(q : ℕ)]! = (q : ℕ) := by
      intro gt hgt
      obtain ⟨s, hsN, hrep⟩ := hstab gt hgt
      have hsb : s ⟨bp.1, hb820⟩ = ⟨bp.1, hb820⟩ := by
        apply Fin.ext
        rw [← hrep.apply hb820]
        exact (hc1 gt hgt).2
      have hsq : s q = q := by
        rw [hq]
        calc s (z ⟨bp.1, hb820⟩) = (s * z) ⟨bp.1, hb820⟩ := rfl
          _ = (z * s) ⟨bp.1, hb820⟩ := by rw [(hz s hsN).symm]
          _ = z (s ⟨bp.1, hb820⟩) := rfl
          _ = z ⟨bp.1, hb820⟩ := by rw [hsb]
      have := hrep.apply q.2
      rw [hsq] at this
      simpa using this
    have hq' : (q : ℕ) = bp.1 := by
      have h := hc2 (q : ℕ) (List.mem_range.2 q.2)
      rw [Bool.or_eq_true] at h
      rcases h with h1 | h1
      · exfalso
        have : (bp.2.all fun gt => (stabElt gt)[(q : ℕ)]! == (q : ℕ)) = true :=
          List.all_eq_true.2 (fun gt hgt => beq_iff_eq.2 (hall gt hgt))
        rw [this] at h1
        exact Bool.false_ne_true h1
      · exact beq_iff_eq.1 h1
    exact Fin.ext hq'
  have h0 : z ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
    hfix 0 (by rw [hf.bases]; simp) (by norm_num)
  have h4 : z ⟨4, by norm_num⟩ = ⟨4, by norm_num⟩ :=
    hfix 4 (by rw [hf.bases]; simp) (by norm_num)
  have key : ∀ (r : Fin 820) (bp : ℕ) (hbp : bp < 820), z ⟨bp, hbp⟩ = ⟨bp, hbp⟩ →
      ∀ w : List ℕ, (wordTab w)[bp]! = (r : ℕ) → z r = r := by
    intro r bp hbp hz0 w hw
    have hn : psi (wordElt w) ⟨bp, hbp⟩ = r := by
      apply Fin.ext
      rw [← (rep_wordPsi w).apply hbp]
      exact hw
    have hmem : psi (wordElt w) ∈ Nsub := ⟨_, rfl⟩
    calc z r = z (psi (wordElt w) ⟨bp, hbp⟩) := by rw [hn]
      _ = (z * psi (wordElt w)) ⟨bp, hbp⟩ := rfl
      _ = (psi (wordElt w) * z) ⟨bp, hbp⟩ := by rw [hz _ hmem]
      _ = psi (wordElt w) (z ⟨bp, hbp⟩) := rfl
      _ = r := by rw [hz0, hn]
  refine Equiv.ext fun r => ?_
  have hr := hf.trans r r.2
  unfold transOK at hr
  simp only at hr
  split_ifs at hr with hb
  · exact key r 0 (by norm_num) h0 _ (beq_iff_eq.1 hr)
  · exact key r 4 (by norm_num) h4 _ (beq_iff_eq.1 hr)

noncomputable def e0 : X₀ ≃* Nsub :=
  MonoidHom.ofInjective psi_injective

theorem card_mulAut_Nsub_le :
    Nat.card (MulAut Nsub) ≤ 26127360 := by
  have h1 : Nat.card (MulAut Nsub) = Nat.card (MulAut X₀) :=
    Nat.card_congr (MulAut.congr e0).toEquiv.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card F9 = (3 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F9.card_eq]
    norm_num
  have h := card_mulAut_psu_le (p := 3) (e := 1) (n := 4) (K := F9) (by norm_num) hK
    (by norm_num)
  have hU := unitaryFieldData_of_card (p := 3) (e := 1) (K := F9) hK
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
  have hSU : Nat.card (StatedSU 4 (3 ^ 1) F9) = 13063680 := by
    have h2 : ((Nat.card (StatedSU 4 (3 ^ 1) F9) : ℕ) : ℤ) = 13063680 := by
      rw [hint]
      decide
    exact_mod_cast h2
  rw [hSU] at h
  rw [h1]
  exact h

theorem kappa_injective (hf : AutFacts) :
    Function.Injective (Nsub.normalizerMonoidHom : (Nrm : Subgroup Gp) →* MulAut Nsub) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply centralizer_trivial hf
  intro n hn
  exact (ha n hn).symm

theorem kappa_bijective (hf : AutFacts) :
    Function.Bijective (Nsub.normalizerMonoidHom : (Nrm : Subgroup Gp) →* MulAut Nsub) := by
  have : Finite (MulAut Nsub) :=
    Finite.of_injective (fun f : MulAut Nsub => (f : Nsub → Nsub))
      (fun a b h => MulEquiv.ext (fun x => congrFun h x))
  refine (kappa_injective hf).bijective_of_nat_card_le ?_
  exact (card_mulAut_Nsub_le).trans (le_card_Nrm hf)

noncomputable def autEquiv (hf : AutFacts) :
    (Nrm : Subgroup Gp) ≃* MulAut X₀ :=
  (MulEquiv.ofBijective _ (kappa_bijective hf)).trans (MulAut.congr e0).symm

theorem psi_autEquiv (hf : AutFacts) (a : (Nrm : Subgroup Gp))
    (x : X₀) : psi (autEquiv hf a x) = (a : Gp) * psi x * (a : Gp)⁻¹ := by
  set β : MulAut Nsub := Nsub.normalizerMonoidHom a with hβ
  set α : MulAut X₀ := autEquiv hf a with hα
  have hαβ : MulAut.congr e0 α = β := by
    have hα' : α = (MulAut.congr e0).symm β := rfl
    rw [hα']
    exact MulEquiv.apply_symm_apply _ _
  have h1 : (MulAut.congr e0 α) (e0 x) = e0 (α x) := by
    simp [MulAut.congr_apply]
  have h2 : psi (α x) = ((e0 (α x) : Nsub) : Gp) := rfl
  rw [h2, ← h1, hαβ, hβ]
  rfl

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
