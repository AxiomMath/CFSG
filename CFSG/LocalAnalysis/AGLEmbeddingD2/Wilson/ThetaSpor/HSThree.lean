module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.ConjSylow
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import Certificates.Certificate12612
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PreprimitiveSolvableBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PreprimitiveSolvableSmall

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Certificates

section Stage1

theorem hsThree_parts :
    hsCentOK () = true ∧ hsSylowOK () = true ∧ hsBlockOK () = true := by
  have h := Certificates.certificate12612
  simp only [hsThreeOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem hsCent_parts :
    validA 100 hsX = true ∧ siftA 100 hs100PLevels hs100BaseArr 0 hsX = true ∧
      eqA 100 (powArr 100 hsX 3) (idA 100) = true ∧ eqA 100 hsX (idA 100) = false ∧
      centOK 100 hs100StrongArrs hs100BaseArr hsX hsRels hsGs hsKeys (hsCCert ()) 360 = true := by
  have h := hsThree_parts.1
  simp only [hsCentOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩ := h
  exact ⟨ha, hb, hc, hd, he⟩

@[expose] noncomputable def hsXperm : Equiv.Perm (Fin 100) := permOfArr 100 hsX

theorem rep_hsX : Rep 100 hsX hsXperm := rep_of_validA hsCent_parts.1

theorem hsXperm_mem : hsXperm ∈ hs100P :=
  mem_hs100P_of_sift rep_hsX hsCent_parts.2.1

@[expose] noncomputable def hsXp : hs100P := ⟨hsXperm, hsXperm_mem⟩

theorem closure_hsGs_eq :
    Subgroup.closure (permsA 100 hsGs) = Subgroup.centralizer {hsXperm} ⊓ hs100P := by
  obtain ⟨-, -, -, -, hcent⟩ := hsCent_parts
  simp only [centOK, Bool.and_eq_true] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hps : ∀ p ∈ hsKeys, p < 100 := by decide
  rw [hs100P_eq_original]
  exact centralizer_eq_of_ptailOK hs100ChainArrays hs100_chain_check.1 rep_hsX hrels hps hC hcomm
    hsift htail

theorem hsCent_enum :
    (∀ x, x ∈ Subgroup.closure (permsA 100 hsGs) ↔
        ∃ i < (hsCCert ()).pts.size, permOfArr 100 (hsCCert ()).pts[i]! = x) ∧
      Nat.card (Subgroup.closure (permsA 100 hsGs)) = 360 ∧
      ∀ i < (hsCCert ()).pts.size, validA 100 (hsCCert ()).pts[i]! = true := by
  obtain ⟨-, -, -, -, hcent⟩ := hsCent_parts
  simp only [centOK, Bool.and_eq_true, beq_iff_eq] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  have hps : ∀ p ∈ hsKeys, p < 100 := by decide
  obtain ⟨h1, h2, h3⟩ := enumOK_spec hps hC
  exact ⟨h1, h2.trans hsize, h3⟩

end Stage1

section Stage2

theorem hsSylow_parts :
    enumOK 100 #[hsX, hsC3] hsKeys (hsPCert ()) = true ∧ (hsPCert ()).pts.size = 9 ∧
      siftA 100 hs100PLevels hs100BaseArr 0 hsC3 = true ∧
      ∀ k < (hsPCert ()).pts.size, eqA 100 (hsPCert ()).pts[k]! (idA 100) = true ∨
        ∃ g ∈ hsConjs, validA 100 g = true ∧ siftA 100 hs100PLevels hs100BaseArr 0 g = true ∧
          eqA 100 (conjA 100 g (hsPCert ()).pts[k]!) hsX = true := by
  have h := hsThree_parts.2.1
  simp only [hsSylowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨he, hsz⟩, hs⟩, hall⟩ := h
  refine ⟨he, hsz, hs, fun k hk => ?_⟩
  have := allLt_spec hall hk
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at this
  rcases this with h | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx, h1, h2, h3⟩

theorem hsC3_valid : validA 100 hsC3 = true := by
  have := hsSylow_parts.1
  simp only [enumOK, Bool.and_eq_true] at this
  have h1 := allLt_spec this.1 (i := 1) (by simp)
  simpa using h1

theorem rep_hsC3 : Rep 100 hsC3 (permOfArr 100 hsC3) := rep_of_validA hsC3_valid

theorem hsC3perm_mem : permOfArr 100 hsC3 ∈ hs100P :=
  mem_hs100P_of_sift rep_hsC3 hsSylow_parts.2.2.1

@[expose] noncomputable def hsSylowSub : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 #[hsX, hsC3])

theorem hsSylowSub_le : hsSylowSub ≤ hs100P := by
  rw [hsSylowSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by simpa using hk
  interval_cases k
  · exact hsXperm_mem
  · exact hsC3perm_mem

theorem card_hsSylowSub : Nat.card hsSylowSub = 9 := by
  obtain ⟨he, hsz, -, -⟩ := hsSylow_parts
  have hps : ∀ p ∈ hsKeys, p < 100 := by decide
  rw [hsSylowSub, (enumOK_spec hps he).2.1, hsz]

theorem exists_conj_hsXp (b : hs100P) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ g : hs100P, g * b * g⁻¹ = hsXp := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hQ : Nat.card (hsSylowSub.subgroupOf hs100P) = 3 ^ 2 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsSylowSub_le).toEquiv
    rw [e, card_hsSylowSub]
    norm_num
  have hfin : Finite hs100P := Nat.finite_of_card_ne_zero (by rw [card_hs100P]; norm_num)
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf_prime_sylow 3 2 (hsSylowSub.subgroupOf hs100P) hQ
    (by rw [card_hs100P]; norm_num) hord
  rw [Subgroup.mem_subgroupOf] at hh
  have hq1 : h⁻¹ * b * h ≠ 1 := by
    intro h1
    apply hb1
    have : b = h * (h⁻¹ * b * h) * h⁻¹ := by group
    rw [this, h1]; group
  have hps : ∀ p ∈ hsKeys, p < 100 := by decide
  obtain ⟨he, hsz, -, hall⟩ := hsSylow_parts
  obtain ⟨i, hi, hiq⟩ := ((enumOK_spec hps he).1 _).1 hh
  have hvalid := (enumOK_spec hps he).2.2 i hi
  have hrep : Rep 100 (hsPCert ()).pts[i]! (permOfArr 100 (hsPCert ()).pts[i]!) :=
    rep_of_validA hvalid
  rcases hall i hi with hid | ⟨g, hg, hgv, hgs, hgc⟩
  · exfalso
    apply hq1
    apply Subtype.ext
    have := (eqA_iff hrep rep_idA).1 hid
    rw [← hiq] at *
    simpa using this
  · have hgrep := rep_of_validA hgv
    have hc := eq_of_eqA (rep_conjA hgv hrep) rep_hsX hgc
    have hgmem : permOfArr 100 g ∈ hs100P := mem_hs100P_of_sift hgrep hgs
    refine ⟨⟨permOfArr 100 g, hgmem⟩ * h⁻¹, ?_⟩
    apply Subtype.ext
    have e : (⟨permOfArr 100 g, hgmem⟩ * h⁻¹ * b * (⟨permOfArr 100 g, hgmem⟩ * h⁻¹)⁻¹ : hs100P) =
        ⟨permOfArr 100 g, hgmem⟩ * (h⁻¹ * b * h) * (⟨permOfArr 100 g, hgmem⟩)⁻¹ := by group
    rw [e]
    change permOfArr 100 g * (h⁻¹ * b * h : hs100P).1 * (permOfArr 100 g)⁻¹ = hsXperm
    rw [← hiq, ← hc]

end Stage2

section Stage3

@[expose] def cAct (σ : Equiv.Perm (Fin 100)) (n : ℕ) : ℕ :=
  if h : n < 100 then (σ ⟨n, h⟩ : ℕ) else n

theorem cAct_eq (σ : Equiv.Perm (Fin 100)) {n : ℕ} (hn : n < 100) :
    cAct σ n = (σ ⟨n, hn⟩ : ℕ) := by
  simp [cAct, hn]

theorem rep_cAct {t : Array ℕ} {σ : Equiv.Perm (Fin 100)} (h : Rep 100 t σ) {n : ℕ} (hn : n < 100) :
    t[n]! = cAct σ n := by
  rw [h.apply hn, cAct_eq σ hn]

theorem cAct_lt (σ : Equiv.Perm (Fin 100)) {n : ℕ} (hn : n < 100) : cAct σ n < 100 := by
  rw [cAct_eq σ hn]
  exact (σ _).2

theorem cAct_mul (σ τ : Equiv.Perm (Fin 100)) {n : ℕ} (hn : n < 100) :
    cAct (σ * τ) n = cAct σ (cAct τ n) := by
  have h2 := cAct_lt τ hn
  rw [cAct_eq (σ * τ) hn, cAct_eq τ hn, cAct_eq σ (by rwa [cAct_eq τ hn] at h2)]
  rfl

theorem cAct_one (n : ℕ) : cAct 1 n = n := by
  unfold cAct
  split_ifs <;> rfl

theorem hsF_lt : ∀ x ∈ hsF, x < 100 := by decide

theorem lt_of_contains {x : ℕ} (h : hsF.contains x = true) : x < 100 :=
  hsF_lt x (List.contains_iff_mem.1 h)

@[expose] def BI (σ : Equiv.Perm (Fin 100)) : Prop :=
  ∀ p : ℕ, p < 100 → hsF.contains p = true →
    hsF.contains (cAct σ p) = true ∧
      hsBlk[cAct σ p]! = hsBlk[cAct σ hsRep[hsBlk[p]!]!]!

theorem hsBlock_parts :
    (∀ i < 100, ((hsX[i]! == i) == hsF.contains i) = true) ∧
    (∀ i < 100, (if hsF.contains i then decide (hsBlk[i]! < 5) else hsBlk[i]! == 5) = true) ∧
    (∀ b < 5, (hsF.contains hsRep[b]! && hsBlk[hsRep[b]!]! == b) = true) ∧
    (∀ k < (hsCCert ()).pts.size,
      (allLt 100 (fun p => !(hsF.contains p) ||
        (hsF.contains (hsEl k)[p]! &&
          hsBlk[(hsEl k)[p]!]! == hsBlk[(hsEl k)[hsRep[hsBlk[p]!]!]!]!)) &&
      (!(allLt 100 (fun p => !(hsF.contains p) || hsBlk[(hsEl k)[p]!]! == hsBlk[p]!)) ||
        eqA 100 (powArr 100 (hsEl k) 3) (idA 100))) = true) ∧
    (∀ b < 5, (hsBlk[(hsGs[0]!)[hsRep[b]!]!]! == hsR0[b]!) = true) ∧
    (∀ b < 5, (hsBlk[(hsGs[1]!)[hsRep[b]!]!]! == hsR1[b]!) = true) ∧
    enumOK 5 #[hsR0, hsR1] [0, 1, 2, 3, 4] (hsFiveCert ()) = true ∧
    (hsFiveCert ()).pts.size = 120 := by
  have h := hsThree_parts.2.2
  simp only [hsBlockOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨allLt_iff.1 h1, allLt_iff.1 h2, allLt_iff.1 h3, allLt_iff.1 h4, allLt_iff.1 h5,
    allLt_iff.1 h6, h7, h8⟩

end Stage3

section Stage4

theorem BI_and_cube_of_rep {i : ℕ} (hi : i < (hsCCert ()).pts.size) {σ : Equiv.Perm (Fin 100)}
    (h : Rep 100 (hsEl i) σ) :
    BI σ ∧ ((∀ p : ℕ, p < 100 → hsF.contains p = true → hsBlk[cAct σ p]! = hsBlk[p]!) →
      σ ^ 3 = 1) := by
  obtain ⟨-, hB2, hB3, hB4, -⟩ := hsBlock_parts
  have h4 := hB4 i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h4
  obtain ⟨hA, hB⟩ := h4
  have hrep_lt : ∀ p : ℕ, p < 100 → hsF.contains p = true → hsRep[hsBlk[p]!]! < 100 := by
    intro p hp hpF
    have h2 := hB2 p hp
    simp only [hpF, ↓reduceIte, decide_eq_true_eq] at h2
    have hb : hsBlk[p]! < 5 := by simpa using h2
    have h3 := hB3 _ hb
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    exact lt_of_contains h3.1
  refine ⟨?_, ?_⟩
  · intro p hp hpF
    have := allLt_iff.1 hA p hp
    simp only [hpF, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨hc1, hc2⟩ := this
    have hr := hrep_lt p hp hpF
    rw [rep_cAct h hp] at hc1 hc2
    rw [rep_cAct h hr] at hc2
    exact ⟨hc1, hc2⟩
  · intro hfix
    have hall : allLt 100 (fun p => !(hsF.contains p) ||
        hsBlk[(hsEl i)[p]!]! == hsBlk[p]!) = true := by
      rw [allLt_iff]
      intro p hp
      by_cases hpF : hsF.contains p = true
      · simp only [hpF, Bool.not_true, Bool.false_or, beq_iff_eq]
        rw [rep_cAct h hp]
        exact hfix p hp hpF
      · have hf : hsF.contains p = false := Bool.eq_false_iff.2 hpF
        simp only [hf, Bool.not_false, Bool.true_or]
    rcases hB with hB | hB
    · rw [hall] at hB
      exact absurd hB (by simp)
    · exact (eqA_iff (rep_powArr h 3) rep_idA).1 hB

end Stage4

section Stage5

abbrev HSC : Type := ↥(Subgroup.centralizer ({hsXp} : Set hs100P))

theorem mem_closure_of_mem_HSC {c : hs100P}
    (hc : c ∈ Subgroup.centralizer ({hsXp} : Set hs100P)) :
    c.1 ∈ Subgroup.closure (permsA 100 hsGs) := by
  rw [closure_hsGs_eq]
  refine ⟨?_, c.2⟩
  have hc' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
  exact Subgroup.mem_centralizer_singleton_iff.2 hc'

theorem mem_HSC_of_mem_closure {c : hs100P} (hc : c.1 ∈ Subgroup.closure (permsA 100 hsGs)) :
    c ∈ Subgroup.centralizer ({hsXp} : Set hs100P) := by
  rw [closure_hsGs_eq] at hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.1 hc.1

theorem BI_and_cube_of_mem {c : hs100P} (hc : c ∈ Subgroup.centralizer ({hsXp} : Set hs100P)) :
    BI c.1 ∧ ((∀ p : ℕ, p < 100 → hsF.contains p = true → hsBlk[cAct c.1 p]! = hsBlk[p]!) →
      c.1 ^ 3 = 1) := by
  obtain ⟨i, hi, hiq⟩ := (hsCent_enum.1 c.1).1 (mem_closure_of_mem_HSC hc)
  have hrep : Rep 100 (hsEl i) c.1 := by
    have := rep_of_validA (hsCent_enum.2.2 i hi)
    rw [hiq] at this
    exact this
  exact BI_and_cube_of_rep hi hrep

theorem hsRep_facts {b : ℕ} (hb : b < 5) :
    hsRep[b]! < 100 ∧ hsF.contains hsRep[b]! = true ∧ hsBlk[hsRep[b]!]! = b := by
  have h3 := hsBlock_parts.2.2.1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h3
  exact ⟨lt_of_contains h3.1, h3.1, h3.2⟩

theorem hsBlk_lt {p : ℕ} (hp : p < 100) (hpF : hsF.contains p = true) : hsBlk[p]! < 5 := by
  have h2 := hsBlock_parts.2.1 p hp
  simp only [hpF, ↓reduceIte, decide_eq_true_eq] at h2
  simpa using h2

@[expose] def actNat (σ : Equiv.Perm (Fin 100)) (k : ℕ) : ℕ := hsBlk[cAct σ hsRep[k]!]!

theorem actNat_lt {σ : Equiv.Perm (Fin 100)} (hσ : BI σ) {k : ℕ} (hk : k < 5) : actNat σ k < 5 := by
  obtain ⟨h1, h2, -⟩ := hsRep_facts hk
  obtain ⟨hF, -⟩ := hσ _ h1 h2
  exact hsBlk_lt (cAct_lt σ h1) hF

theorem actNat_mul {σ τ : Equiv.Perm (Fin 100)} (hσ : BI σ) (hτ : BI τ) {k : ℕ} (hk : k < 5) :
    actNat (σ * τ) k = actNat σ (actNat τ k) := by
  obtain ⟨h1, h2, -⟩ := hsRep_facts hk
  obtain ⟨hF, -⟩ := hτ _ h1 h2
  have hlt := cAct_lt τ h1
  obtain ⟨-, hE⟩ := hσ _ hlt hF
  unfold actNat
  rw [cAct_mul σ τ h1]
  exact hE

theorem actNat_one {k : ℕ} (hk : k < 5) : actNat 1 k = k := by
  obtain ⟨-, -, h3⟩ := hsRep_facts hk
  unfold actNat
  rw [cAct_one, h3]

theorem BI_HSC (c : HSC) : BI c.1.1 := (BI_and_cube_of_mem c.2).1

set_option warn.classDefReducibility false in
@[expose] noncomputable def hsMulAction : MulAction HSC (Fin 5) where
  smul c k := ⟨actNat c.1.1 k.1, actNat_lt (BI_HSC c) k.2⟩
  one_smul k := Fin.ext (actNat_one k.2)
  mul_smul c d k := Fin.ext (actNat_mul (BI_HSC c) (BI_HSC d) k.2)

@[expose] noncomputable def hsPhi : HSC →* Equiv.Perm (Fin 5) :=
  @MulAction.toPermHom HSC (Fin 5) _ hsMulAction

theorem hsPhi_apply (c : HSC) (k : Fin 5) : ((hsPhi c k : Fin 5) : ℕ) = actNat c.1.1 k.1 := rfl

end Stage5

section Stage6

theorem hsGs_valid {k : ℕ} (hk : k < 2) : validA 100 hsGs[k]! = true := by
  obtain ⟨-, -, -, -, hcent⟩ := hsCent_parts
  simp only [centOK, Bool.and_eq_true] at hcent
  obtain ⟨⟨⟨⟨⟨hrels, hC⟩, hsize⟩, hcomm⟩, hsift⟩, htail⟩ := hcent
  simp only [enumOK, Bool.and_eq_true] at hC
  exact allLt_spec hC.1 (by simpa [hsGs] using hk)

theorem hsGs_mem_closure {k : ℕ} (hk : k < 2) :
    permOfArr 100 hsGs[k]! ∈ Subgroup.closure (permsA 100 hsGs) :=
  Subgroup.subset_closure (mem_permsA (by simpa [hsGs] using hk))

theorem hsGs_mem_hs100P {k : ℕ} (hk : k < 2) : permOfArr 100 hsGs[k]! ∈ hs100P := by
  have h := hsGs_mem_closure hk
  rw [closure_hsGs_eq] at h
  exact h.2

@[expose] noncomputable def gHSC (k : ℕ) (hk : k < 2) : HSC :=
  ⟨⟨permOfArr 100 hsGs[k]!, hsGs_mem_hs100P hk⟩, mem_HSC_of_mem_closure (hsGs_mem_closure hk)⟩

theorem hsFive_spec :
    validA 5 hsR0 = true ∧ validA 5 hsR1 = true ∧
      Nat.card (Subgroup.closure (permsA 5 #[hsR0, hsR1])) = 120 := by
  obtain ⟨-, -, -, -, -, -, he, hsz⟩ := hsBlock_parts
  have hps : ∀ p ∈ ([0, 1, 2, 3, 4] : List ℕ), p < 5 := by decide
  obtain ⟨-, h2, -⟩ := enumOK_spec hps he
  refine ⟨enumOK_gens_valid he (k := 0) (by simp), enumOK_gens_valid he (k := 1) (by simp), ?_⟩
  rw [h2, hsz]

theorem hsPhi_gHSC_zero : hsPhi (gHSC 0 (by norm_num)) = permOfArr 5 hsR0 := by
  have hv := hsFive_spec.1
  have hrep := rep_of_validA hv
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [hsPhi_apply, ← hrep j]
  have hj := j.2
  have h5 := hsBlock_parts.2.2.2.2.1 j hj
  simp only [beq_iff_eq] at h5
  have hrl := (hsRep_facts hj).1
  rw [← h5]
  change hsBlk[cAct (permOfArr 100 hsGs[0]!) hsRep[(j : ℕ)]!]! = hsBlk[(hsGs[0]!)[hsRep[(j : ℕ)]!]!]!
  rw [← rep_cAct (rep_of_validA (hsGs_valid (k := 0) (by norm_num))) hrl]

theorem hsPhi_gHSC_one : hsPhi (gHSC 1 (by norm_num)) = permOfArr 5 hsR1 := by
  have hv := hsFive_spec.2.1
  have hrep := rep_of_validA hv
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [hsPhi_apply, ← hrep j]
  have hj := j.2
  have h5 := hsBlock_parts.2.2.2.2.2.1 j hj
  simp only [beq_iff_eq] at h5
  have hrl := (hsRep_facts hj).1
  rw [← h5]
  change hsBlk[cAct (permOfArr 100 hsGs[1]!) hsRep[(j : ℕ)]!]! = hsBlk[(hsGs[1]!)[hsRep[(j : ℕ)]!]!]!
  rw [← rep_cAct (rep_of_validA (hsGs_valid (k := 1) (by norm_num))) hrl]

theorem closure_le_range : Subgroup.closure (permsA 5 #[hsR0, hsR1]) ≤ hsPhi.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by simpa using hk
  interval_cases k
  · exact ⟨gHSC 0 (by norm_num), hsPhi_gHSC_zero⟩
  · exact ⟨gHSC 1 (by norm_num), hsPhi_gHSC_one⟩

theorem card_range_hsPhi : Nat.card hsPhi.range = 120 := by
  have h1 : 120 ≤ Nat.card hsPhi.range := by
    rw [← hsFive_spec.2.2]
    exact Subgroup.card_le_of_le closure_le_range
  have h2 : Nat.card hsPhi.range ≤ Nat.card (Equiv.Perm (Fin 5)) := Subgroup.card_le_card_group _
  have h3 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  omega

theorem range_hsPhi_eq_top : hsPhi.range = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [card_range_hsPhi]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem isPGroup_ker_hsPhi : IsPGroup 3 hsPhi.ker := by
  intro g
  have hg3 : g ^ 3 = 1 := by
    have hker : hsPhi g.1 = 1 := g.2
    have hfix : ∀ p : ℕ, p < 100 → hsF.contains p = true →
        hsBlk[cAct g.1.1.1 p]! = hsBlk[p]! := by
      intro p hp hpF
      have hb := hsBlk_lt hp hpF
      have hBI := (BI_HSC g.1) p hp hpF
      rw [hBI.2]
      have hk := congrArg (fun f : Equiv.Perm (Fin 5) => ((f ⟨hsBlk[p]!, hb⟩ : Fin 5) : ℕ)) hker
      simp only [hsPhi_apply] at hk
      have h3 := (hsRep_facts hb).2.2
      change actNat g.1.1.1 hsBlk[p]! = hsBlk[p]! at hk
      exact hk
    have hc := (BI_and_cube_of_mem g.1.2).2 hfix
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using hc
  exact ⟨1, by simpa using hg3⟩

theorem aschbacherSolvableCore_hsXp : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 HSC = ⊥ := by
  have hfin : Finite hs100P := Nat.finite_of_card_ne_zero (by rw [card_hs100P]; norm_num)
  have : Finite HSC := inferInstance
  have hpre : MulAction.IsPretransitive hsPhi.range (Fin 5) := by
    refine ⟨fun x y => ?_⟩
    refine ⟨⟨Equiv.swap y x, ?_⟩, ?_⟩
    · rw [range_hsPhi_eq_top]; exact Subgroup.mem_top _
    · change Equiv.swap y x x = y
      exact Equiv.swap_apply_right y x
  have : MulAction.IsPreprimitive hsPhi.range (Fin 5) :=
    MulAction.IsPreprimitive.of_prime_card (by simp; norm_num)
  refine CFSG.AGLEmbeddingD2.Wilson.Proving.aschbacherSolvableCore_eq_bot_of_hom hsPhi ?_
    isPGroup_ker_hsPhi
  intro A hcomm htrans
  rw [CFSG.AGLEmbeddingD2.Wilson.Proving.card_mul_card_mulAut_eq_twenty_of_abelian_transitive_five
    A hcomm htrans, card_range_hsPhi]
  norm_num

end Stage6

section Final

theorem thetaCent_hs (b : hs100P) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b} : Set hs100P)) = ⊥ := by
  have : Finite hs100P := Nat.finite_of_card_ne_zero (by rw [card_hs100P]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_hsXp b hb hb1
  exact aschbacherSolvableCore_three_centralizer_eq_bot_of_conj g b hsXp hg
    aschbacherSolvableCore_hsXp

end Final

section Transport

open CFSG.Blueprint

theorem thetaCent_of_hs
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .HS) (b : X)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b} : Set X)) = ⊥ := by
  let e' : X ≃* hs100P := e.trans hs100Equiv
  rw [ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  refine thetaCent_hs (e' b) (by rw [← map_pow, hb3, map_one]) fun h => hb1 ?_
  exact e'.injective (by rw [h, map_one])

end Transport

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
