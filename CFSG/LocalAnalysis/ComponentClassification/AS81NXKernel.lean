module

public import CFSG.LocalAnalysis.ComponentClassification.AS81NXKernelCover
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4NXAct

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace NXKernel

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_oddCoreIn_of_frame (h4 : AS76b.Asc75Theorem4)
    (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hEA : E ≤ A) :
    normalizer (E : Set G) ≤
      normalizer (AS76b.oddCoreIn (centralizer (A : Set G)) : Set G) := by
  set O := AS76b.oddCoreIn (centralizer (A : Set G)) with hO
  by_cases hO1 : O = ⊥
  · rw [hO1, normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn _
  have hEO : E ≤ normalizer (O : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (AS76b.oddCoreIn_le _ ho) e (hEA he)).symm)
  obtain ⟨X₀, hOX₀, hX₀⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) ⟨hOodd, hEO⟩
  have hX₀ne : X₀ ≠ ⊥ := fun h => hO1 (le_bot_iff.mp (h ▸ hOX₀))
  obtain ⟨hconj, -, -, -⟩ := step17a_of_frame h4 h34 hE16 hF hL X₀ hX₀ hX₀ne
  have hX₀O : X₀ = O := by
    have h1 := hconj 1 (one_mem _)
    rwa [rightConjugate_one] at h1
  intro h hh
  have h1 := hconj h hh
  rw [hX₀O, AS76b.centralizer_rightConjugate, Asc75T4.oddCoreIn_rightConjugate] at h1
  exact (rightConjugate_eq_self_iff O h).mp h1.symm

omit [Finite G] in
theorem le_of_normal_of_ne_one {N M C K L : Subgroup G} {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (hΩ : 5 ≤ Nat.card Ω) (ρ : ↥N →* Equiv.Perm Ω)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hCM : C ≤ M)
    (hCn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C)
    (hK : ∀ n : ↥N, ρ n = 1 ↔ (n : G) ∈ K) (hKN : K ≤ N) (hK3 : C.relIndex K = 3)
    (hL : ∀ n : ↥N, (n : G) ∈ L ↔ ρ n ∈ alternatingGroup Ω) (hLN : L ≤ N)
    (halt : alternatingGroup Ω ≤ ρ.range) (hperf : ⁅L, L⁆ ⊔ C = L)
    {x : G} (hxM : x ∈ M) (hxL : x ∈ L) (hx : ρ ⟨x, hLN hxL⟩ ≠ 1) : L ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρL : ↥L →* alternatingGroup Ω :=
    (ρ.comp (inclusion hLN)).codRestrict (alternatingGroup Ω) fun l => (hL (inclusion hLN l)).mp l.2
  have hρL : ∀ l : ↥L, ((ρL l : alternatingGroup Ω) : Equiv.Perm Ω) = ρ (inclusion hLN l) :=
    fun l => rfl
  have hρLs : Function.Surjective ρL := by
    intro σ
    obtain ⟨n, hn⟩ := halt σ.2
    have hnL : (n : G) ∈ L := (hL n).mpr (by rw [hn]; exact σ.2)
    exact ⟨⟨n, hnL⟩, Subtype.ext (by rw [hρL]; exact hn)⟩
  have hMLn : ((M ⊓ L).subgroupOf L).Normal := ⟨fun m hm l => by
    rw [mem_subgroupOf] at hm ⊢
    exact ⟨hMn l (hLN l.2) m hm.1, L.mul_mem (L.mul_mem l.2 hm.2) (L.inv_mem l.2)⟩⟩
  have hIn : (((M ⊓ L).subgroupOf L).map ρL).Normal := hMLn.map ρL hρLs
  have : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup hΩ
  have hItop : ((M ⊓ L).subgroupOf L).map ρL = ⊤ := by
    rcases hIn.eq_bot_or_eq_top with h | h
    · exfalso
      have hmem : ρL ⟨x, hxL⟩ ∈ ((M ⊓ L).subgroupOf L).map ρL :=
        ⟨⟨x, hxL⟩, mem_subgroupOf.mpr ⟨hxM, hxL⟩, rfl⟩
      rw [h, mem_bot] at hmem
      exact hx (congrArg Subtype.val hmem)
    · exact h
  have hLsup : L ≤ K ⊔ (M ⊓ L) := by
    intro l hl
    have hmem : ρL ⟨l, hl⟩ ∈ ((M ⊓ L).subgroupOf L).map ρL := by
      rw [hItop]
      exact mem_top _
    obtain ⟨m, hm, hml⟩ := hmem
    have hk : (m : G)⁻¹ * l ∈ K := by
      have e1 : (⟨(m : G)⁻¹ * l, N.mul_mem (N.inv_mem (hLN m.2)) (hLN hl)⟩ : ↥N) =
          (inclusion hLN m)⁻¹ * inclusion hLN ⟨l, hl⟩ := rfl
      refine (hK ⟨(m : G)⁻¹ * l, N.mul_mem (N.inv_mem (hLN m.2)) (hLN hl)⟩).mp ?_
      rw [e1, map_mul, map_inv, ← hρL, ← hρL, hml, inv_mul_cancel]
    have e2 : l = (m : G) * ((m : G)⁻¹ * l) := by group
    rw [e2, sup_comm]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hm)) (mem_sup_right hk)
  have hKC : ⁅K, K⁆ ≤ C := by
    have hCKn : (C.subgroupOf K).Normal := ⟨fun c hc k => by
      rw [mem_subgroupOf] at hc ⊢
      exact hCn k (hKN k.2) c hc⟩
    have hcard : Nat.card (↥K ⧸ C.subgroupOf K) = 3 := by
      rw [← hK3, relIndex, index]
    have hcyc : IsCyclic (↥K ⧸ C.subgroupOf K) := isCyclic_of_prime_card hcard
    rw [commutator_le]
    intro k₁ hk₁ k₂ hk₂
    have h1 := hcyc.commGroup.mul_comm (QuotientGroup.mk (⟨k₁, hk₁⟩ : ↥K))
      (QuotientGroup.mk (⟨k₂, hk₂⟩ : ↥K))
    have h2 : (⟨k₁, hk₁⟩ : ↥K) * ⟨k₂, hk₂⟩ * (⟨k₁, hk₁⟩ : ↥K)⁻¹ * (⟨k₂, hk₂⟩ : ↥K)⁻¹ ∈
        C.subgroupOf K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      rw [h1]
      group
    rw [commutatorElement_def]
    exact mem_subgroupOf.mp h2
  have hKn : K ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro y
    have hkN := hKN hk
    have hkL : k ∈ L := (hL ⟨k, hkN⟩).mpr (by rw [(hK _).mpr hk]; exact one_mem _)
    constructor
    · intro hy
      exact ⟨hMn k hkN y hy.1, L.mul_mem (L.mul_mem hkL hy.2) (L.inv_mem hkL)⟩
    · intro hy
      have h1 := hMn k⁻¹ (N.inv_mem hkN) _ hy.1
      have h2 := L.mul_mem (L.mul_mem (L.inv_mem hkL) hy.2) (L.inv_mem (L.inv_mem hkL))
      rw [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at h1 h2
      exact ⟨h1, h2⟩
  have hLL : ⁅L, L⁆ ≤ M := by
    have h1 : ⁅L, L⁆ ≤ ⁅K ⊔ (M ⊓ L), K ⊔ (M ⊓ L)⁆ := commutator_mono hLsup hLsup
    refine (h1.trans (commutator_sup_le hKn)).trans (sup_le (hKC.trans hCM) inf_le_left)
  rw [← hperf]
  exact sup_le hLL hCM

theorem oUpper_inf_eq_bot_of_planeData
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {A R : Subgroup G}
    {g : G} {E F : Subgroup G} (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) :
    AS76b.oUpperTwoPrime (normalizer (F : Set G)) ⊓
      AS76b.oddCoreIn (centralizer (A : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨O, hO⟩ : ∃ O, AS76b.oddCoreIn (centralizer (A : Set G)) = O := ⟨_, rfl⟩
  rw [hO]
  have hOodd : Odd (Nat.card O) := by rw [← hO]; exact AS76b.odd_card_oddCoreIn _
  have hOA : O ≤ centralizer (A : Set G) := by rw [← hO]; exact AS76b.oddCoreIn_le _
  have hXO : ∀ {X : Subgroup G}, X ≤ A → X ≤ centralizer (O : Set G) := fun hXA x hx =>
    mem_centralizer_iff.mpr fun o ho => (mem_centralizer_iff.mp (hOA ho) x (hXA hx)).symm
  have hOC : ∀ {X : Subgroup G}, X ≤ A → O ≤ centralizer (X : Set G) := fun hXA o ho =>
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp (hOA ho) x (hXA hx)
  have hCE : centralizer (E : Set G) = E ⊔ O := by rw [← hO]; exact hD.centralizer_eq
  have hCF : centralizer (F : Set G) = F ⊔ O := by rw [← hO]; exact hD.centralizer_eq'
  have hNE : normalizer (E : Set G) ≤ normalizer (O : Set G) := by
    rw [← hO]
    exact normalizer_le_normalizer_oddCoreIn_of_frame h4 h34 hE16 hD.frame hD.type hD.E_le_A
  have hNF : normalizer (F : Set G) ≤ normalizer (O : Set G) := by
    rw [← hO]
    exact normalizer_le_normalizer_oddCoreIn_of_frame h4 h34 hE16 hD'.frame hD'.type hD'.E_le_A
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  have : Fintype ↥(pointsIn R F) := Fintype.ofFinite _
  obtain ⟨LE, -, hLEN, hperfE, -, hK3E, hevenE, haltE⟩ := hD.exists_even
  obtain ⟨LF, -, hLFN, hperfF, -, hK3F, hevenF, haltF⟩ := hD'.exists_even
  have h6E : 5 ≤ Nat.card ↥(pointsIn R E) := by rw [hD.six]; norm_num
  have h6F : 5 ≤ Nat.card ↥(pointsIn R F) := by rw [hD'.six]; norm_num
  have hKiff : ∀ {X : Subgroup G} (n : ↥(normalizer (X : Set G))),
      pointsAction R X n = 1 ↔ (n : G) ∈ ptsKer R X := fun n =>
    ⟨fun h => mem_ptsKer.mpr ⟨n.2, h⟩, fun h => by
      obtain ⟨_, h'⟩ := mem_ptsKer.mp h
      exact h'⟩
  have hMconj : ∀ {X : Subgroup G}, normalizer (X : Set G) ≤ normalizer (O : Set G) →
      ∀ n ∈ normalizer (X : Set G), ∀ m ∈ (normalizer (X : Set G) ⊓ centralizer (O : Set G)) ⊔
        centralizer (X : Set G), n * m * n⁻¹ ∈ (normalizer (X : Set G) ⊓
          centralizer (O : Set G)) ⊔ centralizer (X : Set G) := by
    intro X hNX n hn m hm
    have hle : normalizer (X : Set G) ≤ normalizer (((normalizer (X : Set G) ⊓
        centralizer (O : Set G)) ⊔ centralizer (X : Set G) : Subgroup G) : Set G) :=
      le_normalizer_sup
        (le_normalizer_of_conj_mem fun n hn x hx => mem_inf.mpr
          ⟨(normalizer (X : Set G)).mul_mem ((normalizer (X : Set G)).mul_mem hn hx.1)
            ((normalizer (X : Set G)).inv_mem hn),
            conj_mem_centralizer_of_mem_normalizer (hNX hn) hx.2⟩)
        (le_normalizer_of_conj_mem fun n hn c hc => conj_mem_centralizer hn hc)
    exact (mem_normalizer_iff.mp (hle hn) m).mp hm
  have hFout : ∃ f ∈ F, f ∉ E ⊓ F := by
    by_contra hcon
    push Not at hcon
    have heq : E ⊓ F = F := le_antisymm inf_le_right fun f hf => hcon f hf
    have h2 := hD.two
    rw [heq, hD'.six] at h2
    norm_num at h2
  have hEout : ∃ e ∈ E, e ∉ F ⊓ E := by
    by_contra hcon
    push Not at hcon
    have heq : F ⊓ E = E := le_antisymm inf_le_right fun e he => hcon e he
    have h2 := hD'.two
    rw [heq, hD.six] at h2
    norm_num at h2
  obtain ⟨f, hfF, hfEF⟩ := hFout
  have hfNE : f ∈ normalizer (E : Set G) := hD.F_le_normalizer hfF
  have hfLE : f ∈ LE := (hevenE f hfNE).mpr
    (pointsAction_mem_alternatingGroup (M := A ⊓ normalizer (E : Set G)) inf_le_right hD.radical
      ⟨hD.F_le_A hfF, hfNE⟩)
  have hLE := le_of_normal_of_ne_one h6E (pointsAction R E) (hMconj hNE) le_sup_right
    (fun n hn c hc => conj_mem_centralizer hn hc) hKiff ptsKer_le_normalizer hK3E
    (fun n => hevenE n n.2) hLEN haltE hperfE (x := f)
    (mem_sup_left ⟨hfNE, hXO hD.F_le_A hfF⟩) hfLE (hD.pointsAction_ne_one hfF hfEF)
  obtain ⟨e, heE, heFE⟩ := hEout
  have heNF : e ∈ normalizer (F : Set G) := hD'.F_le_normalizer heE
  have heLF : e ∈ LF := (hevenF e heNF).mpr
    (pointsAction_mem_alternatingGroup (M := A ⊓ normalizer (F : Set G)) inf_le_right hD'.radical
      ⟨hD'.F_le_A heE, heNF⟩)
  have hLF := le_of_normal_of_ne_one h6F (pointsAction R F) (hMconj hNF) le_sup_right
    (fun n hn c hc => conj_mem_centralizer hn hc) hKiff ptsKer_le_normalizer hK3F
    (fun n => hevenF n n.2) hLFN haltF hperfF (x := e)
    (mem_sup_left ⟨heNF, hXO hD'.F_le_A heE⟩) heLF (hD'.pointsAction_ne_one heE heFE)
  obtain ⟨t, htE, htF, htev, hsign⟩ := hD.exists_odd hD'
  have htLE : t ∈ LE := (hevenE t htE).mpr (Equiv.Perm.mem_alternatingGroup.mpr htev)
  have hEDE : E ≤ normalizer (E : Set G) ⊓ centralizer (O : Set G) := fun x hx =>
    ⟨le_normalizer hx, hXO hD.E_le_A hx⟩
  have ht' : t ∈ (normalizer (E : Set G) ⊓ centralizer (O : Set G)) ⊔ O := by
    have h1 := hLE htLE
    rwa [hCE, ← sup_assoc, sup_eq_left.mpr hEDE] at h1
  have hDEO : normalizer (E : Set G) ⊓ centralizer (O : Set G) ≤ normalizer (O : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have ht'' : t ∈ (((normalizer (E : Set G) ⊓ centralizer (O : Set G)) ⊔ O : Subgroup G) :
      Set G) := ht'
  rw [coe_mul_of_left_le_normalizer_right _ O hDEO] at ht''
  obtain ⟨d, hd, o, ho, hdo⟩ := ht''
  have hoCF : o ∈ centralizer (F : Set G) := hOC hD.F_le_A ho
  have hoNF : o ∈ normalizer (F : Set G) := Subgroup.centralizer_le_normalizer _ hoCF
  have hdt : d = t * o⁻¹ := by rw [← hdo, mul_inv_cancel_right]
  have hdF : d ∈ normalizer (F : Set G) := by
    rw [hdt]
    exact mul_mem htF (inv_mem hoNF)
  have hdsign : Equiv.Perm.sign (pointsAction R F ⟨d, hdF⟩) = -1 := by
    have e1 : (⟨d, hdF⟩ : ↥(normalizer (F : Set G))) = ⟨t, htF⟩ * (⟨o, hoNF⟩)⁻¹ :=
      Subtype.ext hdt
    rw [e1, map_mul, map_inv, pointsAction_eq_one_of_mem_centralizer (c := ⟨o, hoNF⟩) hoCF,
      inv_one, mul_one, hsign]
  have hFO : F ≤ centralizer (O : Set G) := hXO hD.F_le_A
  have hT2 : IsPGroup 2 F := isPGroup_two_of_isElemAbelian hD.frame.elemF
  have hcentF := (centralizes_of_relIndex_three centralizer_le_ptsKer ptsKer_le_normalizer
    (fun n hn c hc => conj_mem_centralizer hn hc) (fun n hn k hk => conj_mem_ptsKer hn hk)
    hK3F hLFN hperfF).2
  have hCK : F ⊔ O ≤ ptsKer R F := hCF ▸ centralizer_le_ptsKer
  rw [hCF] at hcentF hK3F hperfF hLF
  exact oUpper_inf_eq_bot (N := normalizer (F : Set G)) hD'.six (pointsAction R F) hT2 hOodd
    le_rfl hNF hFO hKiff ptsKer_le_normalizer hCK hK3F (fun n => hevenF n n.2) hLFN haltF hperfF
    hcentF hLF hdF hd.2 hdsign

end NXKernel

theorem sec4NXKernel_of
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) : Sec4NXKernel := by
  intro G _ _ A R g E F hset X hX
  have hD := planeData_of hE16 h11 hset.frame hset.even
  have hD' := planeData_of hE16 h11 hset.frame.swap hset.even
  rcases hX with rfl | rfl
  · exact NXKernel.oUpper_inf_eq_bot_of_planeData h4 h34 hE16 hD' hD
  · exact NXKernel.oUpper_inf_eq_bot_of_planeData h4 h34 hE16 hD hD'

end CFSG.ComponentClassification.AS81
