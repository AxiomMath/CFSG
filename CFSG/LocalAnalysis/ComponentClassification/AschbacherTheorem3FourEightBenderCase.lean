module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Assembly
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTorus

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_normalizer_of_map_le {A K : Subgroup X}
    (h : ∀ x ∈ A, K.map (MulAut.conj x).toMonoidHom ≤ K) :
    A ≤ Subgroup.normalizer (K : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm (h x hx)
  have h2 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) (h x⁻¹ (A.inv_mem hx))
  rw [Subgroup.map_map] at h2
  have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
      MonoidHom.id X := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hid, Subgroup.map_id] at h2
  exact h2

omit [Finite X] in
theorem sup_le_normalizer_commutator {G T : Subgroup X} (hF : Frame G T) :
    G ⊔ T ≤ Subgroup.normalizer ((⁅T, G⁆ : Subgroup X) : Set X) := by
  refine sup_le (le_normalizer_of_map_le fun x hx => ?_)
    (CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer T T G
      Subgroup.le_normalizer hF.le_normalizer)
  rw [Subgroup.map_le_iff_le_comap, Subgroup.commutator_le]
  intro t ht c hc
  rw [Subgroup.mem_comap]
  change x * ⁅t, c⁆ * x⁻¹ ∈ ⁅T, G⁆
  have h1 := Subgroup.commutator_mem_commutator ht hx
  have h2 := Subgroup.commutator_mem_commutator ht (G.mul_mem hx hc)
  have heq : x * ⁅t, c⁆ * x⁻¹ = ⁅t, x⁆⁻¹ * ⁅t, x * c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2

omit [Finite X] in
theorem le_conjugateClosure (G T : Subgroup X) : T ≤ conjugateClosure G T := by
  intro t ht
  unfold conjugateClosure
  refine Subgroup.mem_iSup_of_mem (1 : G) ?_
  change t ∈ rightConjugate T 1
  rw [rightConjugate_one]
  exact ht

omit [Finite X] in
theorem conjugateClosure_eq {G T : Subgroup X} : conjugateClosure G T = T ⊔ ⁅T, G⁆ := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have hy' : y = ((x : X) * y * (x : X)⁻¹) * ⁅((x : X) * y * (x : X)⁻¹)⁻¹, (x : X)⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator (T.inv_mem hy) (G.inv_mem x.2)))
  · refine sup_le (le_conjugateClosure G T) ?_
    rw [Subgroup.commutator_le]
    intro t ht c hc
    have h1 : t ∈ conjugateClosure G T := le_conjugateClosure G T ht
    have h2 : c * t⁻¹ * c⁻¹ ∈ conjugateClosure G T := by
      unfold conjugateClosure
      refine Subgroup.mem_iSup_of_mem (⟨c⁻¹, G.inv_mem hc⟩ : G) ?_
      change c * t⁻¹ * c⁻¹ ∈ rightConjugate T c⁻¹
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using T.inv_mem ht
    have heq : ⁅t, c⁆ = t * (c * t⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact Subgroup.mul_mem _ h1 h2

omit [Finite X] in
theorem sup_le_normalizer_conjugateClosure {G T : Subgroup X} (hF : Frame G T) :
    G ⊔ T ≤ Subgroup.normalizer ((conjugateClosure G T : Subgroup X) : Set X) := by
  rw [conjugateClosure_eq]
  have hL := sup_le_normalizer_commutator hF
  have hLmap : ∀ x ∈ G ⊔ T, (⁅T, G⁆ : Subgroup X).map (MulAut.conj x).toMonoidHom = ⁅T, G⁆ :=
    fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL hx)
  refine sup_le (le_normalizer_of_map_le fun x hx => ?_) (le_normalizer_of_map_le fun x hx => ?_)
  · rw [Subgroup.map_sup, hLmap x (Subgroup.mem_sup_left hx)]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨t, ht, rfl⟩
    change x * t * x⁻¹ ∈ T ⊔ ⁅T, G⁆
    have heq : x * t * x⁻¹ = t * ⁅t⁻¹, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht)
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (T.inv_mem ht) hx))
  · have hT : T.map (MulAut.conj x).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
    rw [Subgroup.map_sup, hLmap x (Subgroup.mem_sup_right hx), hT]

theorem le_of_isSylowOf_of_normal {E S K : Subgroup X} (hS : IsSylowOf 2 S K) (hE : IsPGroup 2 E)
    (hEK : E ≤ K) (hN : K ≤ Subgroup.normalizer (E : Set X)) : E ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (S ⊔ E : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hS.isPGroup hE (hS.le.trans hN)
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le hEK) hsup
  exact le_sup_right.trans heq.le

omit [Finite X] in
theorem mem_sup_iff_of_le_centralizer {E L : Subgroup X}
    (hEC : E ≤ Subgroup.centralizer (L : Set X)) {x : X} (hx : x ∈ E ⊔ L) :
    ∃ e ∈ E, ∃ ℓ ∈ L, x = e * ℓ ∧ e * ℓ = ℓ * e := by
  have hEN : E ≤ Subgroup.normalizer (L : Set X) :=
    hEC.trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ (E : Set X) * (L : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E L hEN]
    exact hx
  obtain ⟨e, he, ℓ, hℓ, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨e, he, ℓ, hℓ, rfl, (Subgroup.mem_centralizer_iff.mp (hEC he) ℓ hℓ).symm⟩

theorem bender_case {G T S Q H : Subgroup X} {g : X} {n : ℕ} (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (h45 : Hyp45 G T S Q H g) (hHS : H ⊓ S = T ⊔ rightConjugate T g)
    (hW : relativeWeakClosure G T S = T ⊔ rightConjugate T g)
    (hK : conjugateClosure G T = pCoreOf 2 (conjugateClosure G T) ⊔ ⁅T, G⁆)
    (hEL : pCoreOf 2 (conjugateClosure G T) ⊓ ⁅T, G⁆ = ⊥)
    (hcomm : ⁅pCoreOf 2 (conjugateClosure G T), ⁅T, G⁆⁆ = ⊥)
    (hel : IsElemAbelian 2 (pCoreOf 2 (conjugateClosure G T)))
    (hcard : Nat.card (pCoreOf 2 (conjugateClosure G T)) = 2 ^ n)
    (hB : IsBenderType ⁅T, G⁆ n) :
    ∃ n : ℕ, 2 ≤ n ∧
      oTwoPrime (G ⊔ T) = pCoreOf 2 (G ⊔ T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (G ⊔ T) ⊓ ⁅T, G⁆ = ⊥ ∧ ⁅pCoreOf 2 (G ⊔ T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (G ⊔ T)) ∧ Nat.card (pCoreOf 2 (G ⊔ T)) = 2 ^ n ∧
      Nonempty ((⁅T, G⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := h.toFrame
  set K := conjugateClosure G T with hKdef
  set E := pCoreOf 2 K with hEdef
  set L := ⁅T, G⁆ with hLdef
  set M := T ⊔ rightConjugate T g with hMdef
  have hTS : T ≤ S := h.le
  have hSGT : S ≤ G ⊔ T := h.sylow.le
  have hS2 : IsPGroup 2 S := h.sylow.isPGroup
  have hT2 : IsPGroup 2 T := hF.isPGroup
  have hab : IsMulCommutative T := h45.isMulCommutative
  have hT : T ≠ ⊥ := h45.ne_bot
  have hLG : L ≤ G := by
    rw [hLdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hTL : T ⊓ L = ⊥ := le_bot_iff.mp ((inf_le_inf_left T hLG).trans hF.inf_eq_bot.le)
  have hKeq : K = T ⊔ L := conjugateClosure_eq
  have hTK : T ≤ K := le_conjugateClosure G T
  have hLK : L ≤ K := hKeq ▸ le_sup_right
  have hKN : G ⊔ T ≤ Subgroup.normalizer (K : Set X) := sup_le_normalizer_conjugateClosure hF
  have hLN : G ⊔ T ≤ Subgroup.normalizer (L : Set X) := sup_le_normalizer_commutator hF
  have hEN : G ⊔ T ≤ Subgroup.normalizer (E : Set X) :=
    hKN.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hE2 : IsPGroup 2 E := LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hEK : E ≤ K := LieType.BorelTits.pCoreOf_le 2 K
  have hKGT : K ≤ G ⊔ T := hKeq ▸ sup_le le_sup_right (hLG.trans le_sup_left)
  have hEGT : E ≤ G ⊔ T := hEK.trans hKGT
  have hES : E ≤ S := le_of_isSylowOf_of_normal h.sylow hE2 hEGT hEN
  have hEC : E ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hLC : L ≤ Subgroup.centralizer (E : Set X) := Subgroup.le_centralizer_iff.mp hEC
  have hEab : IsMulCommutative E := hel.1
  have hE1 : ∀ e ∈ E, e ^ 2 = 1 := hel.2
  have hdecomp : ∀ x ∈ K, ∃ e ∈ E, ∃ ℓ ∈ L, x = e * ℓ ∧ e * ℓ = ℓ * e := fun x hx =>
    mem_sup_iff_of_le_centralizer hEC (hK ▸ hx)
  have hTel : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨e, he, ℓ, hℓ, rfl, hcm⟩ := hdecomp t (hTK ht)
    have h2 : (e * ℓ) ^ 2 = ℓ ^ 2 := by
      rw [(Commute.mul_pow hcm 2), hE1 e he, one_mul]
    have hmem : (e * ℓ) ^ 2 ∈ T ⊓ L := ⟨T.pow_mem ht 2, h2 ▸ L.pow_mem hℓ 2⟩
    rwa [hTL, Subgroup.mem_bot] at hmem
  have hTN : T ≤ Subgroup.normalizer (L : Set X) := le_sup_right.trans hLN
  have hEN' : E ≤ Subgroup.normalizer (L : Set X) := hEGT.trans hLN
  have hcardLT : Nat.card (L ⊔ T : Subgroup X) = Nat.card L * Nat.card T :=
    card_sup_of_le_normalizer hTN (by rw [inf_comm]; exact hTL)
  have hcardLE : Nat.card (L ⊔ E : Subgroup X) = Nat.card L * Nat.card E :=
    card_sup_of_le_normalizer hEN' (by rw [inf_comm]; exact hEL)
  have hTE : Nat.card T ≤ Nat.card E := by
    have hle : L ⊔ T ≤ L ⊔ E := sup_le le_sup_left (hTK.trans (hK ▸ (sup_comm E L ▸ le_rfl)))
    have := Subgroup.card_le_of_le hle
    rw [hcardLT, hcardLE] at this
    exact Nat.le_of_mul_le_mul_left this Nat.card_pos
  set P := S ⊓ L with hPdef
  have hPL : P ≤ L := inf_le_right
  have hPS : P ≤ S := inf_le_left
  have hP : IsSylowOf 2 P L := h.sylow.inf_of_le_normalizer (hLG.trans le_sup_left) hLN
  obtain ⟨hcentral, hL2⟩ := bender_sylow hB hP
  have hgN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X) :=
    h45.conj_le_normalizer
  obtain ⟨-, hinf, -, -⟩ := h45.facts
  have hcardM : Nat.card M = Nat.card T * Nat.card T := by
    rw [hMdef, card_sup_of_le_normalizer hgN hinf, rightConjugate_card]
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT
  have ht1' : (t : X) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  obtain ⟨e, he, ℓ, hℓ, hteq, hcm⟩ := hdecomp t (hTK t.2)
  have hℓS : ℓ ∈ S := by
    have := S.mul_mem (S.inv_mem (hES he)) (hTS t.2)
    rwa [hteq, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have hℓ2 : ℓ ^ 2 = 1 := by
    have h1 := hTel t t.2
    rw [hteq, Commute.mul_pow hcm 2, hE1 e he, one_mul] at h1
    exact h1
  have hEPC : E ⊔ P ≤ S ⊓ Subgroup.centralizer {(t : X)} := by
    refine sup_le (le_inf hES fun e' he' => ?_) (le_inf hPS fun p hp => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff, hteq]
      have h1 : e' * e = e * e' := hEab.is_comm.comm ⟨e', he'⟩ ⟨e, he⟩ |> congrArg Subtype.val
      have h2 : e' * ℓ = ℓ * e' := (Subgroup.mem_centralizer_iff.mp (hEC he') ℓ hℓ).symm
      calc e' * (e * ℓ) = e * (e' * ℓ) := by rw [← mul_assoc, h1, mul_assoc]
        _ = e * ℓ * e' := by rw [h2, mul_assoc]
    · rw [Subgroup.mem_centralizer_singleton_iff, hteq]
      have h1 : p * e = e * p := (Subgroup.mem_centralizer_iff.mp (hLC (hPL hp)) e he).symm
      have h2 : ℓ * p = p * ℓ := hcentral ℓ ⟨hℓS, hℓ⟩ hℓ2 p hp
      calc p * (e * ℓ) = e * (p * ℓ) := by rw [← mul_assoc, h1, mul_assoc]
        _ = e * ℓ * p := by rw [← h2, mul_assoc]
  have hEPM : E ⊔ P ≤ M := by
    rw [← hHS, lemma_4_5_one h45 t.2 ht1']
    exact hEPC
  have hEP : E ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left E hPL).trans hEL.le)
  have hPN : P ≤ Subgroup.normalizer (E : Set X) :=
    (hPL.trans hLC).trans (Subgroup.centralizer_le_normalizer _)
  have hcardEP : Nat.card (E ⊔ P : Subgroup X) = Nat.card E * Nat.card P :=
    card_sup_of_le_normalizer hPN hEP
  have hPle : Nat.card P ≤ 2 ^ n := by
    have h1 := Subgroup.card_le_of_le hEPM
    rw [hcardEP, hcardM] at h1
    have h2 : Nat.card E * Nat.card P ≤ Nat.card E * Nat.card E :=
      h1.trans (Nat.mul_le_mul hTE hTE)
    rw [← hcard]
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  obtain ⟨hn, ⟨eL⟩⟩ := hL2 hPle
  obtain ⟨-, hcardP, D, hDL, hDP, hcardD, hfree⟩ := exists_torus hn eL hP
  have hcardT : Nat.card T = 2 ^ n := by
    have h1 := Subgroup.card_le_of_le hEPM
    rw [hcardEP, hcardM, hcard, hcardP] at h1
    have h2 : Nat.card T ≤ 2 ^ n := hcard ▸ hTE
    nlinarith
  have hMEP : E ⊔ P = M := by
    apply Subgroup.eq_of_le_of_card_ge hEPM
    rw [hcardEP, hcardM, hcard, hcardP, hcardT]
  have hMS : M ≤ S := h45.W_le.trans inf_le_right
  have hDG : D ≤ G := hDL.trans hLG
  have hDE : D ≤ Subgroup.centralizer (E : Set X) := hDL.trans hLC
  have hEC' : E ≤ Subgroup.centralizer (P : Set X) :=
    hEC.trans (Subgroup.centralizer_le (by exact_mod_cast hPL))
  have hTP : T ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left T hPL).trans hTL.le)
  have hTM : T ≤ E ⊔ P := hMEP ▸ (le_sup_left : T ≤ M)
  have hDM : ∀ d ∈ D, rightConjugate T d ≤ M := by
    intro d hd
    rw [← hMEP]
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hx' := hTM hx
    have hdE : d⁻¹ ∈ Subgroup.normalizer (E : Set X) :=
      Subgroup.centralizer_le_normalizer _ (hDE (D.inv_mem hd))
    have hdP : d⁻¹ ∈ Subgroup.normalizer (P : Set X) := hDP (D.inv_mem hd)
    have hdN : d⁻¹ ∈ Subgroup.normalizer ((E ⊔ P : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hdE,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hdP]
    have := (Subgroup.mem_normalizer_iff.mp hdN _).mp hx'
    simpa [mul_assoc] using this
  have hTE' : T ⊓ E = ⊥ := by
    by_contra hne
    obtain ⟨⟨x, hxT, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hDT : ∀ d ∈ D, rightConjugate T d = T := by
      intro d hd
      have hdx : d⁻¹ * x * d = x := by
        have := Subgroup.mem_centralizer_iff.mp (hDE hd) x hxE
        calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
          _ = d⁻¹ * (d * x) := by rw [this]
          _ = x := by group
      have hne' : rightConjugate T 1 ⊓ rightConjugate T d ≠ ⊥ := by
        rw [rightConjugate_one]
        intro hbot
        have hmem : x ∈ T ⊓ rightConjugate T d := by
          refine ⟨hxT, ?_⟩
          rw [← hdx]
          exact conj_mem_rightConjugate hxT d
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hx1' hmem
      have := rightConjugate_eq_of_inf_ne_bot h h43 hab G.one_mem (hDG hd)
        (by rw [rightConjugate_one]; exact hTS) ((hDM d hd).trans hMS) hne'
      rw [rightConjugate_one] at this
      exact this.symm
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hD1 : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr hcon
      rw [hD1, Subgroup.card_bot] at hcardD
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hTE2 : T ≤ E := by
      intro t' ht'
      obtain ⟨e', he', ℓ', hℓ', hteq', hcm'⟩ := hdecomp t' (hTK ht')
      have hℓ'S : ℓ' ∈ S := by
        have := S.mul_mem (S.inv_mem (hES he')) (hTS ht')
        rwa [hteq', ← mul_assoc, inv_mul_cancel, one_mul] at this
      have hconj : d⁻¹ * t' * d ∈ T := by
        have h1 : d⁻¹ * t' * d ∈ rightConjugate T d := conj_mem_rightConjugate ht' d
        rwa [hDT d hdD] at h1
      have hde' : d⁻¹ * e' * d = e' := by
        have := Subgroup.mem_centralizer_iff.mp (hDE hdD) e' he'
        calc d⁻¹ * e' * d = d⁻¹ * (e' * d) := by group
          _ = d⁻¹ * (d * e') := by rw [this]
          _ = e' := by group
      have hmem : t'⁻¹ * (d⁻¹ * t' * d) ∈ T ⊓ L := by
        refine ⟨T.mul_mem (T.inv_mem ht') hconj, ?_⟩
        have heq : t'⁻¹ * (d⁻¹ * t' * d) = ℓ'⁻¹ * (d⁻¹ * ℓ' * d) := by
          rw [hteq']
          calc (e' * ℓ')⁻¹ * (d⁻¹ * (e' * ℓ') * d)
              = ℓ'⁻¹ * e'⁻¹ * ((d⁻¹ * e' * d) * (d⁻¹ * ℓ' * d)) := by group
            _ = ℓ'⁻¹ * (d⁻¹ * ℓ' * d) := by rw [hde']; group
        rw [heq]
        exact L.mul_mem (L.inv_mem hℓ') (L.mul_mem (L.mul_mem (L.inv_mem (hDL hdD)) hℓ')
          (hDL hdD))
      rw [hTL, Subgroup.mem_bot] at hmem
      have hfix : d⁻¹ * ℓ' * d = ℓ' := by
        have h1 : t'⁻¹ * (d⁻¹ * t' * d) = ℓ'⁻¹ * (d⁻¹ * ℓ' * d) := by
          rw [hteq']
          calc (e' * ℓ')⁻¹ * (d⁻¹ * (e' * ℓ') * d)
              = ℓ'⁻¹ * e'⁻¹ * ((d⁻¹ * e' * d) * (d⁻¹ * ℓ' * d)) := by group
            _ = ℓ'⁻¹ * (d⁻¹ * ℓ' * d) := by rw [hde']; group
        rw [h1] at hmem
        calc d⁻¹ * ℓ' * d = ℓ' * (ℓ'⁻¹ * (d⁻¹ * ℓ' * d)) := by group
          _ = ℓ' := by rw [hmem, mul_one]
      have hℓ'1 : ℓ' = 1 := by
        by_contra hℓ'1
        exact hd1 (hfree d hdD ℓ' ⟨hℓ'S, hℓ'⟩ hℓ'1 hfix)
      rw [hteq', hℓ'1, mul_one]
      exact he'
    have hTEeq : T = E := Subgroup.eq_of_le_of_card_ge hTE2 (by rw [hcardT, hcard])
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff, hLdef, Subgroup.commutator_le]
      intro a ha c hc
      have hmem : ⁅a, c⁆ ∈ T ⊓ G := by
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have h1 : c * a⁻¹ * c⁻¹ ∈ T := by
            have hcN : c ∈ Subgroup.normalizer (T : Set X) :=
              hTEeq ▸ hEN (Subgroup.mem_sup_left hc)
            exact (Subgroup.mem_normalizer_iff.mp hcN _).mp (T.inv_mem ha)
          simpa [mul_assoc] using T.mul_mem ha h1
        · rw [commutatorElement_def]
          have h1 : a * c * a⁻¹ ∈ G :=
            (Subgroup.mem_normalizer_iff.mp (hF.le_normalizer ha) _).mp hc
          exact G.mul_mem h1 (G.inv_mem hc)
      rwa [hF.inf_eq_bot] at hmem
    have hPbot : P = ⊥ := le_bot_iff.mp (hLbot ▸ hPL)
    rw [hPbot, Subgroup.card_bot] at hcardP
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  set 𝒞 : Set (Subgroup X) := {K' | ∃ x ∈ G, K' = rightConjugate T x ∧ rightConjugate T x ≤ M}
    with h𝒞def
  have hconjD : ∀ x ∈ G, rightConjugate T x ≤ M →
      ∃ d ∈ D, rightConjugate T x = rightConjugate T d := by
    intro x hx hxM
    have hFx := hF.rightConjugate_frame hx
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (fun hbot => hT (rightConjugate_eq_bot_iff.mp hbot))
    have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    have hyE : y ∉ E := by
      intro hyE
      have hmem : y ∈ rightConjugate T x ⊓ E := ⟨hy, hyE⟩
      have hEx : rightConjugate E x = E :=
        (rightConjugate_eq_self_iff E x).mpr (hEN (Subgroup.mem_sup_left hx))
      rw [← hEx, ← rightConjugate_inf, hTE', rightConjugate_bot, Subgroup.mem_bot] at hmem
      exact hy1' hmem
    have hyP : y ∉ P := by
      intro hyP
      have hmem : y ∈ rightConjugate T x ⊓ G := ⟨hy, hLG (hPL hyP)⟩
      rw [hFx.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hy1' hmem
    obtain ⟨d, hd, hyd⟩ := exists_mem_rightConjugate hEP hEC' hTM hTP hTE' (by rw [hcard, hcardT])
      hDE hDP (by rw [hcardP, hcardD]) hfree (hMEP ▸ hxM hy) hyE hyP
    refine ⟨d, hd, rightConjugate_eq_of_inf_ne_bot h h43 hab hx (hDG hd) (hxM.trans hMS)
      ((hDM d hd).trans hMS) ?_⟩
    intro hbot
    have hmem : y ∈ rightConjugate T x ⊓ rightConjugate T d := ⟨hy, hyd⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy1' hmem
  have hcard𝒞 : Nat.card 𝒞 = Nat.card D := by
    let ψ : D → 𝒞 := fun d => ⟨rightConjugate T d, d, hDG d.2, rfl, hDM d d.2⟩
    have hψ : Function.Bijective ψ := by
      refine ⟨fun d d' hdd => Subtype.ext ?_, fun K' => ?_⟩
      · exact rightConjugate_injOn hEC' hTM hTP hTE' hT hDE hDP hfree d.2 d'.2
          (congrArg Subtype.val hdd)
      · obtain ⟨x, hx, hK', hxM⟩ := K'.2
        obtain ⟨d, hd, hxd⟩ := hconjD x hx hxM
        exact ⟨⟨d, hd⟩, Subtype.ext (by rw [hK', hxd])⟩
    exact (Nat.card_congr (Equiv.ofBijective ψ hψ)).symm
  have hodd : Odd (Nat.card 𝒞) := by
    rw [hcard𝒞, hcardD]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  have hSW : S ≤ Subgroup.normalizer (M : Set X) :=
    hW ▸ le_normalizer_relativeWeakClosure hF hSGT hTS
  have hinv : ∀ K' ∈ 𝒞, ∀ s ∈ S, rightConjugate K' s ∈ 𝒞 := by
    rintro K' ⟨x, hx, rfl, hxM⟩ s hs
    have hxs : x * s ∈ G ⊔ T := Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (hSGT hs)
    obtain ⟨t₀, -, g₀, hg₀, -, hrc⟩ := hF.exists_rightConjugate_eq hxs
    refine ⟨g₀, hg₀, by rw [rightConjugate_mul, hrc], ?_⟩
    rw [← hrc, ← rightConjugate_mul]
    calc rightConjugate (rightConjugate T x) s ≤ rightConjugate M s :=
          rightConjugate_le_rightConjugate hxM s
      _ = M := (rightConjugate_eq_self_iff M s).mpr (hSW hs)
  obtain ⟨K', ⟨x, hx, rfl, hxM⟩, hSN⟩ := exists_mem_normalizer_of_odd hS2 𝒞 hinv hodd
  have hSx : rightConjugate S x⁻¹ ≤ (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X) := by
    refine le_inf ?_ ?_
    · rw [← rightConjugate_eq_of_mem (Subgroup.mem_sup_left (G.inv_mem hx) : x⁻¹ ∈ G ⊔ T)]
      exact rightConjugate_le_rightConjugate hSGT _
    · have h1 := rightConjugate_le_rightConjugate hSN x⁻¹
      rw [rightConjugate_normalizer, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
        at h1
      exact h1
  have hcardS : Nat.card S ≤ Nat.card M := by
    have h1 := card_le_of_isSylowOf h.sylow_normalizer (isPGroup_rightConjugate hS2 _) hSx
    rw [rightConjugate_card] at h1
    have h2 : S ⊓ Subgroup.normalizer (T : Set X) ≤ M := by
      rw [← hHS]
      exact le_inf ((inf_le_inf_right _ hSGT).trans (h43.normalizer_le hF hT)) inf_le_left
    exact h1.trans (Subgroup.card_le_of_le h2)
  have hSM : S = M := (Subgroup.eq_of_le_of_card_ge hMS hcardS).symm
  have hSK : S ≤ K := by
    rw [hSM, ← hMEP]
    exact sup_le hEK (hPL.trans hLK)
  have hOK : oTwoPrime (G ⊔ T) = K := by
    apply le_antisymm
    · rw [oTwoPrime, Subgroup.closure_le]
      rintro z ⟨hz, k, hzk⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hzk)
      have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
        IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      obtain ⟨c, hc, hcle⟩ := exists_rightConjugate_le_of_isSylowOf h.sylow hZ2
        ((Subgroup.zpowers_le).mpr hz)
      have hzc : c⁻¹ * z * c ∈ K := hSK (hcle (conj_mem_rightConjugate (Subgroup.mem_zpowers z) c))
      have hcK : c ∈ Subgroup.normalizer (K : Set X) := hKN hc
      have := (Subgroup.mem_normalizer_iff.mp hcK _).mp hzc
      simpa [mul_assoc] using this
    · rw [hKeq]
      refine sup_le ?_ ?_
      · intro t ht
        refine Subgroup.subset_closure ⟨Subgroup.mem_sup_right ht, ?_⟩
        obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      · rw [hLdef, Subgroup.commutator_le]
        intro a ha c hc
        have h1 : a ∈ oTwoPrime (G ⊔ T) := by
          refine Subgroup.subset_closure ⟨Subgroup.mem_sup_right ha, ?_⟩
          obtain ⟨k, hk⟩ := hT2 ⟨a, ha⟩
          exact ⟨k, congrArg Subtype.val hk⟩
        have h2 : c * a⁻¹ * c⁻¹ ∈ oTwoPrime (G ⊔ T) := by
          refine Subgroup.subset_closure ⟨?_, ?_⟩
          · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
              (Subgroup.mem_sup_right (T.inv_mem ha))) (Subgroup.mem_sup_left (G.inv_mem hc))
          · obtain ⟨k, hk⟩ := hT2 ⟨a⁻¹, T.inv_mem ha⟩
            refine ⟨k, ?_⟩
            have hk' : a⁻¹ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
            rw [conj_pow, hk']
            group
        rw [commutatorElement_def, show a * c * a⁻¹ * c⁻¹ = a * (c * a⁻¹ * c⁻¹) by group]
        exact Subgroup.mul_mem _ h1 h2
  have hO2 : pCoreOf 2 (G ⊔ T) = E := by
    apply le_antisymm
    · have hO2S : pCoreOf 2 (G ⊔ T) ≤ S := pCoreOf_le_of_isSylowOf h.sylow
      exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2S.trans hSK)
        (hKGT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 (G ⊔ T)))
        (LieType.BorelTits.pCoreOf_isPGroup 2 (G ⊔ T))
    · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEGT hEN hE2
  refine ⟨n, hn, ?_, ?_, ?_, ?_, ?_, ⟨eL⟩⟩
  · rw [hOK, hO2]
    exact hK
  · rw [hO2]
    exact hEL
  · rw [hO2]
    exact hcomm
  · rw [hO2]
    exact hel
  · rw [hO2]
    exact hcard





end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
