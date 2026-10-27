module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpStar
public import CFSG.ClassicalInvolution.Q3.Sec13EndMin
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E8Sec
public import CFSG.ClassicalInvolution.Q3.TL3T12_6Dual
public import CFSG.ClassicalInvolution.Q3.TL3T20
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1
public import CFSG.ClassicalInvolution.Q3.TL3T26
public import CFSG.ClassicalInvolution.Q3.TL3C6
public import CFSG.ClassicalInvolution.Q3.TL3T39
public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15Ker
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinComm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Thin
public import CFSG.ClassicalInvolution.Q3.Sec13PerpD
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T47
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T51
public import CFSG.ClassicalInvolution.Q3.TL3T53
public import CFSG.ClassicalInvolution.Q3.TL3T54
public import CFSG.ClassicalInvolution.Q3.TL3T55
public import CFSG.ClassicalInvolution.Q3.TL4AECoverH
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AET

public section


namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitO2
  (fam_mem_omegaStarNbr_of_phi Q8Fam)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15 (memBar_inj)
open CFSG.ClassicalInvolution.Q3.TL4.SecIdE2 (exists_normalizing_memBar comm_memBar_twin
  card_of_mem_e64Sets adj4_of_mem_e64Sets card_of_mem_e29Sets)

open CFSG.ClassicalInvolution.Q3.AE Wr in
private theorem perpB_range_or_compl {n : ℕ} {ι κ : Fin 4 ↪ Fin n}
    (h : mkQ n (zOf ι) = mkQ n (zOf κ)) :
    Set.range ι = Set.range κ ∨ ∀ x, x ∈ Set.range ι ↔ x ∉ Set.range κ := by
  classical
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact Or.inl (range_eq_of_zOf_eq (inv_mul_eq_one.mp h1))
  · right
    have hv : ∀ x, (zOf ι).vec x + (zOf κ).vec x = 1 := by
      intro x
      have h2 := congrFun (congrArg Wr.vec h1) x
      rw [mul_vec, zOf_inv, zOf_perm] at h2
      exact h2
    intro x
    have h3 := hv x
    rw [zOf_vec_apply, zOf_vec_apply] at h3
    by_cases h4 : x ∈ Set.range ι <;> by_cases h5 : x ∈ Set.range κ <;>
      simp only [h4, h5, ite_true, ite_false] at h3 <;> first
        | exact absurd h3 (by decide) | simp [h4, h5]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private def PerpBClique (Q : Set (Subgroup G)) : Prop :=
  ∀ L ∈ Q, ∀ L' ∈ Q, L ≠ L' → Commutes L L'

private def perpBOrb (P : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ x ∈ pSpan P, conjSub x M = L}

private theorem perpB_dComp_eq {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dComp Ω K) :
    dComp Ω L = dComp Ω K := by
  ext J
  constructor
  · intro hJ
    exact Relation.ReflTransGen.trans hL hJ
  · intro hJ
    exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK hL) hJ

private theorem perpB_omegaNbr_mem_dComp {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    J ∈ dComp Ω K :=
  Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩

private theorem perpB_star_comm (h : EndHyp Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hL' : L' ∈ dComp Ω L) (hs : L' ∈ omegaStarNbr Ω L) : Commutes L L' := by
  have hn : L' ∈ omegaNbr Ω L := by
    by_contra hn
    exact not_mem_dComp_of_omegaStar h hL hs hn hL'
  exact comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two hL hn

private theorem perpB_conjSub_eq_of_comm {K : Subgroup G} {y : G}
    (hc : ∀ x ∈ K, x * y = y * x) : conjSub y K = K := by
  have h1 : ∀ x ∈ K, y⁻¹ * x * y = x := fun x hx => by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hc x hx]
      _ = x := by group
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have hk := hc _ hx
    have e : x = y⁻¹ * x * y := by
      calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
        _ = y⁻¹ * x * y := by rw [← hk]; group
    rw [e]
    exact hx
  · intro hx
    rw [h1 x hx]
    exact hx

private theorem perpB_mem_omegaNbr_of_comm {K J : Subgroup G} (h : EndHyp Ω) (hK : K ∈ Ω)
    (hJ : J ∈ Ω)
    (hne : J ≠ K) (hc : Commutes K J) : J ∈ omegaNbr Ω K := by
  rw [TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two]
  refine ⟨hJ, hne, fun y hy => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  exact perpB_conjSub_eq_of_comm fun x hx => hc x hx y hy

private theorem perpBOrb_self (P : Set (Subgroup G)) (M : Subgroup G) : M ∈ perpBOrb P M :=
  ⟨1, one_mem _, conjSub_one M⟩

private theorem perpBOrb_conj {P : Set (Subgroup G)} {M L : Subgroup G} {x : G} (hx : x ∈ pSpan P)
    (hL : L ∈ perpBOrb P M) : conjSub x L ∈ perpBOrb P M := by
  obtain ⟨y, hy, rfl⟩ := hL
  exact ⟨x * y, mul_mem hx hy, by rw [conjSub_mul]⟩

private theorem perpBOrb_eq {P : Set (Subgroup G)} {M L : Subgroup G} (hL : L ∈ perpBOrb P M) :
    perpBOrb P L = perpBOrb P M := by
  obtain ⟨x, hx, rfl⟩ := hL
  ext N
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y * x, mul_mem hy hx, ?_⟩
    rw [conjSub_mul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y * x⁻¹, mul_mem hy (inv_mem hx), ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]

private theorem perpBOrb_trans {P : Set (Subgroup G)} {M L L' : Subgroup G} (hL : L ∈ perpBOrb P M)
    (hL' : L' ∈ perpBOrb P M) : ∃ x ∈ pSpan P, conjSub x L = L' := by
  obtain ⟨a, ha, rfl⟩ := hL
  obtain ⟨b, hb, rfl⟩ := hL'
  refine ⟨b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
  rw [conjSub_mul, conjSub_inv_conjSub]

private theorem perpB_conjSub_commutes {g : G} {L L' : Subgroup G} (hc : Commutes L L') :
    Commutes (conjSub g L) (conjSub g L') := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have := hc x hx y hy
  show g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹)
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

private def PerpBNorm (g : G) (P : Set (Subgroup G)) : Prop :=
  ∀ L : Subgroup G, L ∈ P ↔ conjSub g L ∈ P

private theorem perpB_conj_conj_inv (g : G) (L : Subgroup G) : conjSub g (conjSub g⁻¹ L) = L := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

private theorem PerpBNorm.inv {g : G} {P : Set (Subgroup G)} (hg : PerpBNorm g P) :
    PerpBNorm g⁻¹ P := by
  intro L
  constructor
  · intro hL
    exact (hg (conjSub g⁻¹ L)).2 (by rw [perpB_conj_conj_inv]; exact hL)
  · intro hL
    have := (hg (conjSub g⁻¹ L)).1 hL
    rwa [perpB_conj_conj_inv] at this

private theorem perpB_conj_pSpan {P : Set (Subgroup G)} {g : G} (hg : PerpBNorm g P) {x : G}
    (hx : x ∈ pSpan P) : g * x * g⁻¹ ∈ pSpan P := by
  let S : Subgroup G := (pSpan P).comap (MulAut.conj g).toMonoidHom
  have hS : pSpan P ≤ S := pSpan_le fun L hL y hy => le_pSpan ((hg L).1 hL) ⟨y, hy, rfl⟩
  exact hS hx

private theorem perpB_conj_mem_orb {P : Set (Subgroup G)} {g : G} (hg : PerpBNorm g P)
    {M L : Subgroup G} (hL : L ∈ perpBOrb P M) : conjSub g L ∈ perpBOrb P (conjSub g M) := by
  obtain ⟨x, hx, rfl⟩ := hL
  refine ⟨g * x * g⁻¹, perpB_conj_pSpan hg hx, ?_⟩
  calc conjSub (g * x * g⁻¹) (conjSub g M) = conjSub (g * x) (conjSub g⁻¹ (conjSub g M)) := by
        rw [conjSub_mul]
    _ = conjSub (g * x) M := by rw [conjSub_inv_conjSub]
    _ = conjSub g (conjSub x M) := by rw [conjSub_mul]


private theorem perpB_mem_dComp_conj_iff (hΩ : ConjInvariant Ω) (g : G) {K L : Subgroup G} :
    L ∈ dComp Ω K ↔ conjSub g L ∈ dComp Ω (conjSub g K) := by
  constructor
  · intro hL
    exact Thompson.mem_dComp_conjSub hΩ hL g
  · intro hL
    have h1 := Thompson.mem_dComp_conjSub hΩ hL g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1

private theorem perpB_norm_dComp (h : EndHyp Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K) :
    ∃ g : G, conjSub g K = M ∧ PerpBNorm g (dComp Ω K) := by
  obtain ⟨g, hg⟩ := h.thmD.trans K hK M (dComp_subset_of_mem hK hM)
  refine ⟨g, hg, fun L => ?_⟩
  exact (perpB_mem_dComp_conj_iff h.thmD.hyp.conjInvariant g).trans
    (by rw [hg, perpB_dComp_eq hK hM])

private theorem perpB_trans_of_cross {S P₁ : Set (Subgroup G)}
    (hA : ∀ L ∈ P₁, ∀ x ∈ pSpan P₁, conjSub x L ∈ P₁)
    (hcross : ∀ A ∈ P₁, ∀ B ∈ S, B ∉ P₁ → Commutes A B)
    {L : Subgroup G} (hL : L ∈ P₁) {L' : Subgroup G} (h : ∃ x ∈ pSpan S, conjSub x L = L') :
    ∃ x ∈ pSpan P₁, conjSub x L = L' := by
  obtain ⟨h₀, hh₀, hcL⟩ := h
  let CcS : Subgroup G := ⨅ A ∈ P₁, Subgroup.centralizer (A : Set G)
  have hc_mem : ∀ c : G, c ∈ CcS ↔ ∀ A ∈ P₁, ∀ y ∈ A, y * c = c * y := by
    intro c
    constructor
    · intro hc A hA' y hy
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hc A) hA')
        y hy
    · intro hc
      refine Subgroup.mem_iInf.mpr fun A => Subgroup.mem_iInf.mpr fun hA' =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => hc A hA' y hy
  have hnorm : ∀ a ∈ pSpan P₁, ∀ c ∈ CcS, a * c * a⁻¹ ∈ CcS := by
    intro a ha c hc
    rw [hc_mem] at hc ⊢
    intro A hA' y hy
    have hA'' : conjSub a⁻¹ A ∈ P₁ := hA A hA' a⁻¹ (inv_mem ha)
    have hz : a⁻¹ * y * a ∈ conjSub a⁻¹ A := ⟨y, hy, by simp⟩
    have hcz := hc (conjSub a⁻¹ A) hA'' (a⁻¹ * y * a) hz
    calc y * (a * c * a⁻¹) = a * ((a⁻¹ * y * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * y * a)) * a⁻¹ := by rw [hcz]
      _ = a * c * a⁻¹ * y := by group
  let M : Subgroup G :=
    { carrier := {g | ∃ a ∈ pSpan P₁, ∃ c ∈ CcS, g = a * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        refine ⟨a * a', mul_mem ha ha', a'⁻¹ * c * a'⁻¹⁻¹ * c', mul_mem
          (hnorm a'⁻¹ (inv_mem ha') c hc) hc', ?_⟩
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        exact ⟨a⁻¹, inv_mem ha, a * c⁻¹ * a⁻¹, hnorm a ha c⁻¹ (CcS.inv_mem hc), by group⟩ }
  have hSM : pSpan S ≤ M := by
    refine pSpan_le fun N hN y hy => ?_
    by_cases hNP : N ∈ P₁
    · exact ⟨y, le_pSpan hNP hy, 1, one_mem _, by group⟩
    · have hyC : y ∈ CcS := (hc_mem y).mpr fun A hA' z hz => hcross A hA' N hN hNP z hz y hy
      exact ⟨1, one_mem _, y, hyC, by group⟩
  obtain ⟨a, ha, c, hc, hh⟩ := hSM hh₀
  refine ⟨a, ha, ?_⟩
  rw [← hcL, hh, conjSub_mul, perpB_conjSub_eq_of_comm ((hc_mem c).mp hc L hL)]


private theorem perpB_secHyp (h : EndHyp Ω) {Q : Set (Subgroup G)} (hQΩ : Q ⊆ Ω)
    (hinv : ∀ L ∈ Q, ∀ x ∈ pSpan Q, conjSub x L ∈ Q)
    (htr : ∀ L ∈ Q, ∀ L' ∈ Q, ∃ x ∈ pSpan Q, conjSub x L = L')
    (hodd : classicalInvolutionOddCore ↥(pSpan Q) = ⊥) : SecHyp 3 Ω Q := by
  refine ⟨h.thmD.hyp, h.thmD.two, h.thmD.card, h.thmD.aEmpty, hQΩ, hinv, htr, hodd, ?_⟩
  intro L hL u hu
  obtain ⟨N, hN, hN2, huN⟩ := h.thmD.inO2 L (hQΩ hL) u hu
  refine ⟨N ⊓ pSpan Q, inf_le_right, fun x hx q hq => ⟨hN.conj_mem q hq.1 x,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hq.2) (Subgroup.inv_mem _ hx)⟩,
    hN2.to_le inf_le_left, ⟨huN, le_pSpan hL hu.mem⟩⟩

private theorem perpB_sigma_clique_false (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) (hne : KPerp Ω J ≠ KPerp Ω K)
    (hcl : PerpBClique (dComp Ω K)) : False := by
  have hJS : J ∈ dComp Ω K := perpB_omegaNbr_mem_dComp hJ
  have hJΩ : J ∈ Ω := hJ.1
  have hKS : K ∈ dComp Ω K := Relation.ReflTransGen.refl
  have hdJ : dComp Ω J = dComp Ω K := perpB_dComp_eq hK hJS
  have hKP : KPerp Ω K = dComp Ω K := by
    ext L
    simp only [KPerp, Set.mem_insert_iff]
    constructor
    · rintro (rfl | hL)
      · exact hKS
      · exact perpB_omegaNbr_mem_dComp hL
    · intro hL
      by_cases hLK : L = K
      · exact Or.inl hLK
      · exact Or.inr (perpB_mem_omegaNbr_of_comm h hK (dComp_subset_of_mem hK hL) hLK
          (hcl K hKS L hL (Ne.symm hLK)))
  have hJP : KPerp Ω J = dComp Ω K := by
    ext L
    simp only [KPerp, Set.mem_insert_iff]
    constructor
    · rintro (rfl | hL)
      · exact hJS
      · have := perpB_omegaNbr_mem_dComp hL
        rwa [hdJ] at this
    · intro hL
      by_cases hLJ : L = J
      · exact Or.inl hLJ
      · exact Or.inr (perpB_mem_omegaNbr_of_comm h hJΩ (dComp_subset_of_mem hK hL) hLJ
          (hcl J hJS L hL (Ne.symm hLJ)))
  exact hne (hJP.trans hKP.symm)

private theorem perpB_sigma_clique_of_orb (h : EndHyp Ω) {K M : Subgroup G} (hK : K ∈ Ω)
    (hM : M ∈ dComp Ω K)
    (hcross : ∀ A ∈ dComp Ω K, ∀ B ∈ dComp Ω K,
      (¬ ∃ x ∈ pSpan (dComp Ω K), conjSub x A = B) → Commutes A B)
    (hMcl : PerpBClique (perpBOrb (dComp Ω K) M)) : PerpBClique (dComp Ω K) := by
  intro L1 hL1 L2 hL2 hne
  by_cases hor : ∃ x ∈ pSpan (dComp Ω K), conjSub x L1 = L2
  · have hMΩ : M ∈ Ω := dComp_subset_of_mem hK hM
    have hL1M : L1 ∈ dComp Ω M := by rw [perpB_dComp_eq hK hM]; exact hL1
    obtain ⟨g1, hg1, hN⟩ := perpB_norm_dComp h hMΩ hL1M
    have hN' : PerpBNorm g1 (dComp Ω K) := by rw [← perpB_dComp_eq hK hM]; exact hN
    have hL2orb : L2 ∈ perpBOrb (dComp Ω K) L1 := hor
    have hB := perpB_conj_mem_orb hN'.inv hL2orb
    rw [← hg1, conjSub_inv_conjSub] at hB
    have hBne : conjSub g1⁻¹ L2 ≠ M := by
      intro hBM
      exact hne (by rw [← hg1, ← hBM, perpB_conj_conj_inv])
    have hMB : Commutes M (conjSub g1⁻¹ L2) := hMcl M (perpBOrb_self _ _) _ hB hBne.symm
    have := perpB_conjSub_commutes (g := g1) hMB
    rwa [hg1, perpB_conj_conj_inv] at this
  · exact hcross L1 hL1 L2 hL2 hor

private theorem perpB_dSet_conj (h : EndHyp Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W) (g : G) :
    conjSub g R ∈ DSet Ω (conjSub g W) := by
  rw [h.mem_dSet_iff] at hR ⊢
  refine ⟨h.thmD.hyp.conjInvariant g R hR.1, fun y hy => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  have hr : g⁻¹ * y * g ∈ R := (mem_conjSub_iff).mp hy
  have hrW : conjSub (g⁻¹ * y * g) W = W := mem_normalizer_iff_conjSub_eq.mp (hR.2 hr)
  have hy' : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  calc conjSub y (conjSub g W)
      = conjSub (g * (g⁻¹ * y * g) * g⁻¹) (conjSub g W) := by rw [← hy']
    _ = conjSub g (conjSub (g⁻¹ * y * g) (conjSub g⁻¹ (conjSub g W))) := by
        rw [conjSub_mul, conjSub_mul]
    _ = conjSub g (conjSub (g⁻¹ * y * g) W) := by rw [conjSub_inv_conjSub]
    _ = conjSub g W := by rw [hrW]

private theorem perpB_card_le_four (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcl : PerpBClique C) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : C.ncard ≤ 4 := by
  have hb := clique_ncard_le h hC hcl hW hR
  rcases h.mu W hW with h3 | h4 | h5
  · have := (dSet_class_ncard h hW hR).1 h3
    omega
  · have := (dSet_class_ncard h hW hR).2.1 h4
    omega
  · have := (dSet_class_ncard h hW hR).2.2 h5
    omega

private theorem perpB_wylD4_of_card (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcl : PerpBClique C) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) (hcard : 4 ≤ C.ncard) : MuIsoWylD4 Ω W := by
  have hb := clique_ncard_le h hC hcl hW hR
  rcases h.mu W hW with h3 | h4 | h5
  · have := (dSet_class_ncard h hW hR).1 h3
    omega
  · have := (dSet_class_ncard h hW hR).2.1 h4
    omega
  · exact h5


private theorem perpB_pSpan_mono {P S : Set (Subgroup G)} (hPS : P ⊆ S) : pSpan P ≤ pSpan S :=
  pSpan_le fun L hL => le_pSpan (hPS hL)

private theorem perpB_orb_sub (h : EndHyp Ω) {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dComp Ω K)
    {L : Subgroup G} (hL : L ∈ perpBOrb (dComp Ω K) M) : L ∈ dComp Ω K := by
  obtain ⟨x, hx, rfl⟩ := hL
  exact h.conjSub_mem_dComp hK hM hx

private theorem perpB_norm_orb {S : Set (Subgroup G)} {M : Subgroup G} {g : G} (hg : g ∈ pSpan S) :
    PerpBNorm g (perpBOrb S M) := by
  intro L
  constructor
  · intro hL
    exact perpBOrb_conj hg hL
  · intro hL
    have := perpBOrb_conj (inv_mem hg) hL
    rwa [conjSub_inv_conjSub] at this

private theorem perpB_odd_sub {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : ∀ y ∈ H, ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    (hOH : classicalInvolutionOddCore ↥H = ⊥) : classicalInvolutionOddCore ↥X = ⊥ := by
  set TG : Subgroup G := (classicalInvolutionOddCore ↥X).map X.subtype with hTG
  have hTGH : TG ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact hXH x.2
  have hstabG : ∀ y ∈ H, ∀ t ∈ TG, y * t * y⁻¹ ∈ TG := by
    intro y hy t ht
    obtain ⟨x, hx, rfl⟩ := ht
    let f : ↥X ≃* ↥X :=
      { toFun := fun z => ⟨y * z * y⁻¹, hXn y hy z z.2⟩
        invFun := fun z => ⟨y⁻¹ * z * y, by simpa using hXn y⁻¹ (inv_mem hy) z z.2⟩
        left_inv := fun z => by ext; simp [mul_assoc]
        right_inv := fun z => by ext; simp [mul_assoc]
        map_mul' := fun a b => by ext; simp [mul_assoc] }
    have hfN : (classicalInvolutionOddCore ↥X).map f.toMonoidHom ≤
        classicalInvolutionOddCore ↥X := by
      apply le_sSup
      refine ⟨Subgroup.Normal.map (classicalInvolutionOddCore_normal ↥X) f.toMonoidHom
        f.surjective, ?_⟩
      rw [Nat.card_congr (Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).symm.toEquiv]
      exact QuaternionStructure.odd_natCard_oddCore ↥X
    exact ⟨f x, hfN ⟨x, hx, rfl⟩, rfl⟩
  have hNH : (TG.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hstabG (g : G) g.2 _ hn
    simpa using this⟩
  have hodd : Odd (Nat.card ↥(TG.subgroupOf H)) := by
    have e1 : Nat.card ↥TG = Nat.card ↥(classicalInvolutionOddCore ↥X) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective).symm.toEquiv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTGH).toEquiv, e1]
    exact QuaternionStructure.odd_natCard_oddCore ↥X
  have hle : TG.subgroupOf H ≤ classicalInvolutionOddCore ↥H := le_sSup ⟨hNH, hodd⟩
  rw [hOH] at hle
  ext x
  constructor
  · intro hx
    have hxT : (x : G) ∈ TG := ⟨x, hx, rfl⟩
    have h1 : (⟨(x : G), hTGH hxT⟩ : ↥H) ∈ TG.subgroupOf H := Subgroup.mem_subgroupOf.mpr hxT
    have h2 := hle h1
    rw [Subgroup.mem_bot] at h2
    have h3 : (x : G) = 1 := congrArg Subtype.val h2
    exact (Subgroup.mem_bot).mpr (Subtype.ext h3)
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _


private theorem perpB_exists_W (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ W ∈ WSet Ω, K ∈ DSet Ω W := by
  obtain ⟨S, hKS⟩ := (h.thmD.two K hK).exists_le_sylow
  obtain ⟨η, hη, -, hinv, -⟩ := h.exists_wSet_of_le hK S hKS
  refine ⟨⨆ V ∈ η, V, ⟨η, hη, rfl⟩, ?_⟩
  rw [h.mem_dSet_iff]
  refine ⟨hK, fun k hk => ?_⟩
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  exact TC.conjSub_etaSpan_eq (fun V hV => hinv k (hKS hk) V hV)
    (fun V hV => hinv k⁻¹ ((S : Subgroup G).inv_mem (hKS hk)) V hV)

private theorem perpB_comm_symm {X Y : Subgroup G} (c : Commutes X Y) : Commutes Y X :=
  fun y hy x hx => (c x hx y hy).symm

private theorem perpB_six_false (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hcross : ∀ A ∈ dComp Ω K, ∀ B ∈ dComp Ω K,
      (¬ ∃ x ∈ pSpan (dComp Ω K), conjSub x A = B) → Commutes A B)
    {A B : Subgroup G} (hA : A ∈ perpBOrb (dComp Ω K) K) (hB : B ∈ perpBOrb (dComp Ω K) K)
    (hAB : A ≠ B) (hcAB : Commutes A B)
    {M N : Subgroup G} (hM : M ∈ dComp Ω K) (hN : N ∈ dComp Ω K)
    (hMK : M ∉ perpBOrb (dComp Ω K) K) (hNK : N ∉ perpBOrb (dComp Ω K) K)
    (hMN : N ∉ perpBOrb (dComp Ω K) M)
    {W₀ R₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω) (hR₀ : R₀ ∈ DSet Ω W₀) : False := by
  obtain ⟨gM, hgM, hgMN⟩ := perpB_norm_dComp h hK hM
  obtain ⟨gN, hgN, hgNN⟩ := perpB_norm_dComp h hK hN
  have hKS : K ∈ dComp Ω K := Relation.ReflTransGen.refl
  have hA1 : conjSub gM A ∈ perpBOrb (dComp Ω K) M := by
    have := perpB_conj_mem_orb hgMN hA
    rwa [hgM] at this
  have hB1 : conjSub gM B ∈ perpBOrb (dComp Ω K) M := by
    have := perpB_conj_mem_orb hgMN hB
    rwa [hgM] at this
  have hA2 : conjSub gN A ∈ perpBOrb (dComp Ω K) N := by
    have := perpB_conj_mem_orb hgNN hA
    rwa [hgN] at this
  have hB2 : conjSub gN B ∈ perpBOrb (dComp Ω K) N := by
    have := perpB_conj_mem_orb hgNN hB
    rwa [hgN] at this
  have hnotP1 : ∀ {X : Subgroup G}, X ∈ perpBOrb (dComp Ω K) M → X ∉ perpBOrb (dComp Ω K) K := by
    intro X hX hXK
    apply hMK
    have e1 := perpBOrb_eq hX
    have e2 := perpBOrb_eq hXK
    have : M ∈ perpBOrb (dComp Ω K) K := by
      rw [← e2, e1]
      exact perpBOrb_self _ _
    exact this
  have hnotP2 : ∀ {X : Subgroup G}, X ∈ perpBOrb (dComp Ω K) N → X ∉ perpBOrb (dComp Ω K) K := by
    intro X hX hXK
    apply hNK
    have e1 := perpBOrb_eq hX
    have e2 := perpBOrb_eq hXK
    have : N ∈ perpBOrb (dComp Ω K) K := by
      rw [← e2, e1]
      exact perpBOrb_self _ _
    exact this
  have hMN' : ∀ {X Y : Subgroup G}, X ∈ perpBOrb (dComp Ω K) M →
      Y ∈ perpBOrb (dComp Ω K) N → X ≠ Y := by
    intro X Y hX hY hXY
    apply hMN
    have e1 := perpBOrb_eq hX
    have e2 := perpBOrb_eq hY
    rw [hXY] at e1
    have : N ∈ perpBOrb (dComp Ω K) Y := by
      rw [e2]
      exact perpBOrb_self _ _
    rw [e1] at this
    exact this
  have hconjinj : ∀ {X Y : Subgroup G} (g : G), conjSub g X = conjSub g Y → X = Y := by
    intro X Y g e
    have := congrArg (conjSub g⁻¹) e
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hAS : A ∈ dComp Ω K := perpB_orb_sub h hK hKS hA
  have hBS : B ∈ dComp Ω K := perpB_orb_sub h hK hKS hB
  have hA1S : conjSub gM A ∈ dComp Ω K := perpB_orb_sub h hK hM hA1
  have hB1S : conjSub gM B ∈ dComp Ω K := perpB_orb_sub h hK hM hB1
  have hA2S : conjSub gN A ∈ dComp Ω K := perpB_orb_sub h hK hN hA2
  have hB2S : conjSub gN B ∈ dComp Ω K := perpB_orb_sub h hK hN hB2
  have cAB := hcAB
  have cAA1 : Commutes A (conjSub gM A) := hcross A hAS _ hA1S
    (fun ⟨x, hx, hxe⟩ => hnotP1 hA1 (hxe ▸ perpBOrb_conj hx hA))
  have cBB1 : Commutes B (conjSub gM B) := hcross B hBS _ hB1S
    (fun ⟨x, hx, hxe⟩ => hnotP1 hB1 (hxe ▸ perpBOrb_conj hx hB))
  have cAB1 : Commutes A (conjSub gM B) := hcross A hAS _ hB1S
    (fun ⟨x, hx, hxe⟩ => hnotP1 hB1 (hxe ▸ perpBOrb_conj hx hA))
  have cBA1 : Commutes B (conjSub gM A) := hcross B hBS _ hA1S
    (fun ⟨x, hx, hxe⟩ => hnotP1 hA1 (hxe ▸ perpBOrb_conj hx hB))
  have cAA2 : Commutes A (conjSub gN A) := hcross A hAS _ hA2S
    (fun ⟨x, hx, hxe⟩ => hnotP2 hA2 (hxe ▸ perpBOrb_conj hx hA))
  have cBB2 : Commutes B (conjSub gN B) := hcross B hBS _ hB2S
    (fun ⟨x, hx, hxe⟩ => hnotP2 hB2 (hxe ▸ perpBOrb_conj hx hB))
  have cAB2 : Commutes A (conjSub gN B) := hcross A hAS _ hB2S
    (fun ⟨x, hx, hxe⟩ => hnotP2 hB2 (hxe ▸ perpBOrb_conj hx hA))
  have cBA2 : Commutes B (conjSub gN A) := hcross B hBS _ hA2S
    (fun ⟨x, hx, hxe⟩ => hnotP2 hA2 (hxe ▸ perpBOrb_conj hx hB))
  have cA1B1 : Commutes (conjSub gM A) (conjSub gM B) := perpB_conjSub_commutes hcAB
  have cA2B2 : Commutes (conjSub gN A) (conjSub gN B) := perpB_conjSub_commutes hcAB
  have cA1A2 : Commutes (conjSub gM A) (conjSub gN A) := hcross _ hA1S _ hA2S
    (fun ⟨x, hx, hxe⟩ => hMN' (perpBOrb_conj hx hA1) hA2 (hxe ▸ rfl))
  have cA1B2 : Commutes (conjSub gM A) (conjSub gN B) := hcross _ hA1S _ hB2S
    (fun ⟨x, hx, hxe⟩ => hMN' (hxe ▸ perpBOrb_conj hx hA1) hB2 rfl)
  have cB1A2 : Commutes (conjSub gM B) (conjSub gN A) := hcross _ hB1S _ hA2S
    (fun ⟨x, hx, hxe⟩ => hMN' (hxe ▸ perpBOrb_conj hx hB1) hA2 rfl)
  have cB1B2 : Commutes (conjSub gM B) (conjSub gN B) := hcross _ hB1S _ hB2S
    (fun ⟨x, hx, hxe⟩ => hMN' (hxe ▸ perpBOrb_conj hx hB1) hB2 rfl)
  have dA_A1 : A ≠ conjSub gM A := fun e => hnotP1 hA1 (e ▸ hA)
  have dA_B1 : A ≠ conjSub gM B := fun e => hnotP1 hB1 (e ▸ hA)
  have dA_A2 : A ≠ conjSub gN A := fun e => hnotP2 hA2 (e ▸ hA)
  have dA_B2 : A ≠ conjSub gN B := fun e => hnotP2 hB2 (e ▸ hA)
  have dB_A1 : B ≠ conjSub gM A := fun e => hnotP1 hA1 (e ▸ hB)
  have dB_B1 : B ≠ conjSub gM B := fun e => hnotP1 hB1 (e ▸ hB)
  have dB_A2 : B ≠ conjSub gN A := fun e => hnotP2 hA2 (e ▸ hB)
  have dB_B2 : B ≠ conjSub gN B := fun e => hnotP2 hB2 (e ▸ hB)
  have dA1_B1 : conjSub gM A ≠ conjSub gM B := fun e => hAB (hconjinj gM e)
  have dA1_A2 : conjSub gM A ≠ conjSub gN A := hMN' hA1 hA2
  have dA1_B2 : conjSub gM A ≠ conjSub gN B := hMN' hA1 hB2
  have dB1_A2 : conjSub gM B ≠ conjSub gN A := hMN' hB1 hA2
  have dB1_B2 : conjSub gM B ≠ conjSub gN B := hMN' hB1 hB2
  have dA2_B2 : conjSub gN A ≠ conjSub gN B := fun e => hAB (hconjinj gN e)
  have hmem6 : ∀ X ∈ ({A, B, conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)), X ∈ dComp Ω K := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hAS, hBS, hA1S, hB1S, hA2S, hB2S]
  have hCS : ({A, B, conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)) ⊆ Ω := fun X hX => dComp_subset_of_mem hK (hmem6 X hX)
  have hcl : PerpBClique ({A, B, conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)) := by
    intro X hX Y hY hXY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hY with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hXY
      | assumption
      | exact perpB_comm_symm (by assumption)
  have n1 : A ∉ ({B, conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hAB, dA_A1, dA_B1, dA_A2, dA_B2⟩
  have n2 : B ∉ ({conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨dB_A1, dB_B1, dB_A2, dB_B2⟩
  have n3 : conjSub gM A ∉ ({conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨dA1_B1, dA1_A2, dA1_B2⟩
  have n4 : conjSub gM B ∉ ({conjSub gN A, conjSub gN B} : Set (Subgroup G)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨dB1_A2, dB1_B2⟩
  have hcard : ({A, B, conjSub gM A, conjSub gM B, conjSub gN A, conjSub gN B} :
      Set (Subgroup G)).ncard = 6 := by
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_pair dA2_B2]
  have hle := perpB_card_le_four h hCS hcl hW₀ hR₀
  rw [hcard] at hle
  omega


private theorem perpB_omegaStar_of_restrict {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hcard : ∀ J ∈ Ω, Nat.card J = 8) {L M : Subgroup G}
    (hL : L ∈ P) (hM : M ∈ P)
    (h : M.subgroupOf (pSpan P) ∈ omegaStarNbr (restrictFamily P (pSpan P))
      (L.subgroupOf (pSpan P))) : M ∈ omegaStarNbr Ω L := by
  obtain ⟨-, hne', U, hU, hUM, hUN⟩ := h
  have hMX : M ≤ pSpan P := le_pSpan hM
  have hML : M ≠ L := fun e => hne' (by rw [e])
  refine ⟨hPΩ hM, hML, ?_⟩
  obtain ⟨R, hR, hUR, hcyc, hrel⟩ := hU
  obtain ⟨J₁, hJ₁, -, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet_restrict hR
  have hJ₁Ω : J₁ ∈ Ω := hPΩ hJ₁
  have hRJ : R.map (pSpan P).subtype = J₁ :=
    (hRJ₁.2.2 J₁ le_rfl (h2 J₁ hJ₁Ω) hRJ₁.1).symm
  have hRcard : Nat.card R = 8 := by
    rw [← hcard J₁ hJ₁Ω, ← hRJ]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective R _ (pSpan P).subtype_injective).toEquiv)
  have hUcard : Nat.card U = 4 := by
    have := Subgroup.relIndex_mul_card (H := U) (K := R)
    rw [inf_eq_left.mpr hUR, hrel, hRcard] at this
    omega
  set V : Subgroup G := U.map (pSpan P).subtype with hVdef
  have hVcard : Nat.card V = 4 := by
    rw [← hUcard]
    exact (Nat.card_congr
    (Subgroup.equivMapOfInjective U _ (pSpan P).subtype_injective).toEquiv).symm
  haveI : IsCyclic U := hcyc
  have hVcyc : IsCyclic ↥V :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective U _ (pSpan P).subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective U _ (pSpan P).subtype_injective).surjective
  have hVJ : V ≤ J₁ := by
    rw [← hRJ]
    exact Subgroup.map_mono hUR
  have hsyl : IsSylow2In J₁ J₁ := ⟨le_rfl, h2 J₁ hJ₁Ω, fun V' hV' _ hJV' => le_antisymm hV' hJV'⟩
  have hVUSet : V ∈ USet Ω := by
    refine mem_USet_of_natCard (R := J₁) hJ₁Ω hsyl hVJ hVcyc ?_
    rw [hcard J₁ hJ₁Ω, hVcard]
  refine ⟨V, hVUSet, ?_, ?_⟩
  · rw [hVdef]
    exact (Subgroup.map_mono hUM).trans (Subgroup.map_subgroupOf_eq_of_le hMX).le
  · intro v hv
    rw [hVdef, Subgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have hun : ∀ x : pSpan P, x ∈ L.subgroupOf (pSpan P) ↔
        u * x * u⁻¹ ∈ L.subgroupOf (pSpan P) :=
      fun x => Subgroup.mem_normalizer_iff.mp (hUN hu) x
    have hun' : ∀ x : pSpan P, x ∈ L.subgroupOf (pSpan P) ↔
        u⁻¹ * x * u⁻¹⁻¹ ∈ L.subgroupOf (pSpan P) :=
      fun x => Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hUN hu)) x
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyX : y ∈ pSpan P := le_pSpan hL hy
      exact Subgroup.mem_subgroupOf.mp ((hun ⟨y, hyX⟩).mp (Subgroup.mem_subgroupOf.mpr hy))
    · intro hy
      have hyX : (pSpan P).subtype u * y * ((pSpan P).subtype u)⁻¹ ∈ pSpan P := le_pSpan hL hy
      set x : pSpan P := ⟨(pSpan P).subtype u * y * ((pSpan P).subtype u)⁻¹, hyX⟩ with hxdef
      have hx : x ∈ L.subgroupOf (pSpan P) := Subgroup.mem_subgroupOf.mpr hy
      have h2' := Subgroup.mem_subgroupOf.mp ((hun' x).mp hx)
      have e : ((u⁻¹ * x * u⁻¹⁻¹ : pSpan P) : G) = y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hxdef, Subgroup.subtype_apply]
        group
      rw [e] at h2'
      exact h2'

private theorem perpB_q8_iso {L : Subgroup G} (hq : IsQuatSub L) (hL : Nat.card L = 8) :
    Nonempty (↥L ≃* QuaternionGroup 2) := by
  obtain ⟨k, -, ⟨e⟩⟩ := hq
  have hc : Nat.card (QuaternionGroup (2 ^ k)) = 8 := by
    rw [← Nat.card_congr e.toEquiv, hL]
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
  have hk : k = 1 := by
    have h2k : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2k
  subst hk
  exact ⟨e⟩

private theorem perpB_q8fam (h : EndHyp Ω) {Q : Set (Subgroup G)} (hP : SecHyp 3 Ω Q) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitO2.Q8Fam ↥(pSpan Q)
      (restrictFamily Q (pSpan Q)) := by
  have hT := hP.thmDHyp
  refine ⟨hT.hyp, hT.two, ?_, hT.aEmpty, hT.gen, hT.trans, hT.odd, hT.inO2⟩
  rintro _ ⟨L, hL, hLX, rfl⟩
  have hq : IsQuatSub L := Sec6Gen.isQuatSub_of_mem_RSet hP.hyp
    (TC.mem_RSet_of_isPGroup (hP.sub hL) (hP.two L (hP.sub hL)))
  obtain ⟨e⟩ := perpB_q8_iso hq (hP.card L (hP.sub hL))
  exact ⟨(Subgroup.subgroupOfEquivOfLe hLX).trans e⟩

private theorem perpB_transport_map {P : Set (Subgroup G)} {H : Type} [Group H]
    (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤) (φ : ↥(pSpan P) →* H) (L : Subgroup G) :
    ((L.subgroupOf (pSpan P)).subgroupOf (pSpan (restrictFamily P (pSpan P)))).map
      (φ.comp (spanEquiv hgen).symm.toMonoidHom) = (L.subgroupOf (pSpan P)).map φ := by
  have h1 : ((L.subgroupOf (pSpan P)).subgroupOf (pSpan (restrictFamily P (pSpan P)))).map
      (spanEquiv hgen).symm.toMonoidHom = L.subgroupOf (pSpan P) := by
    rw [← map_spanEquiv hgen L, Subgroup.map_map]
    have hcomp : (spanEquiv hgen).symm.toMonoidHom.comp (spanEquiv hgen).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rw [← Subgroup.map_map, h1]

private noncomputable def perpB_aeIdent_restrict {P : Set (Subgroup G)} {n : ℕ}
    (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤) (I : AEIdent P n) :
    AEIdent (restrictFamily P (pSpan P)) n where
  φ := I.φ.comp (spanEquiv hgen).symm.toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (spanEquiv hgen).symm.surjective,
      ← MonoidHom.range_eq_map]
    exact I.range_eq
  ker_le := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : (spanEquiv hgen).symm x ∈ Subgroup.center ↥(pSpan P) :=
      I.ker_le (MonoidHom.mem_ker.mpr hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro z
    apply (spanEquiv hgen).symm.injective
    rw [map_mul, map_mul]
    exact hc ((spanEquiv hgen).symm z)
  label := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, (perpB_transport_map hgen I.φ L).trans hlab⟩
  label_surj := by
    intro α h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α h b
    exact ⟨L.subgroupOf (pSpan P), ⟨L, hL, le_pSpan hL, rfl⟩,
      (perpB_transport_map hgen I.φ L).trans hlab⟩

private noncomputable def perpB_aeIdentOn_restrict {P : Set (Subgroup G)} {n : ℕ}
    {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤) (I : AEIdentOn P n 𝒜 H) :
    AEIdentOn (restrictFamily P (pSpan P)) n 𝒜 H where
  φ := I.φ.comp (spanEquiv hgen).symm.toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (spanEquiv hgen).symm.surjective,
      ← MonoidHom.range_eq_map]
    exact I.range_eq
  ker_le := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : (spanEquiv hgen).symm x ∈ Subgroup.center ↥(pSpan P) :=
      I.ker_le (MonoidHom.mem_ker.mpr hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro z
    apply (spanEquiv hgen).symm.injective
    rw [map_mul, map_mul]
    exact hc ((spanEquiv hgen).symm z)
  label := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨α, hα, h, b, hlab⟩ := I.label L hL
    exact ⟨α, hα, h, b, (perpB_transport_map hgen I.φ L).trans hlab⟩
  label_surj := by
    intro α hα h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj α hα h b
    exact ⟨L.subgroupOf (pSpan P), ⟨L, hL, le_pSpan hL, rfl⟩,
      (perpB_transport_map hgen I.φ L).trans hlab⟩

private theorem perpB_omegaStar_aeIdent (h : EndHyp Ω) {Q : Set (Subgroup G)} (hP : SecHyp 3 Ω Q)
    {m : ℕ} (hm : 5 ≤ m) (I : AEIdent Q m) {L M : Subgroup G} (hL : L ∈ Q) (hM : M ∈ Q)
    (hne : L ≠ M) {α β : Finset (Fin m)} {hα : α.card = 4} {hβ : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan Q)).map I.φ = AE.memBar α hα b)
    (hlab' : (M.subgroupOf (pSpan Q)).map I.φ = AE.memBar β hβ c)
    (hv : ∃ v ∈ AE.memBar β hβ c, v * v ≠ 1 ∧
      ∀ a ∈ AE.memBar α hα b, v * a * v⁻¹ ∈ AE.memBar α hα b) :
    M ∈ omegaStarNbr Ω L := by
  have hgen := pSpan_restrictFamily_eq_top Q
  have hne' : L.subgroupOf (pSpan Q) ≠ M.subgroupOf (pSpan Q) := by
    intro e
    apply hne
    have := Subgroup.subgroupOf_inj.mp e
    rwa [inf_eq_left.mpr (le_pSpan hL), inf_eq_left.mpr (le_pSpan hM)] at this
  have key := fam_mem_omegaStarNbr_of_phi
    (perpB_aeIdent_restrict hgen I).φ (perpB_q8fam h hP) hm (perpB_aeIdent_restrict hgen I).ker_le
    (perpB_aeIdent_restrict hgen I).label ⟨L, hL, le_pSpan hL, rfl⟩
    ⟨M, hM, le_pSpan hM, rfl⟩ hne' ((perpB_transport_map hgen I.φ L).trans hlab)
    ((perpB_transport_map hgen I.φ M).trans hlab') hv
  exact perpB_omegaStar_of_restrict hP.sub (fun J hJ => h.thmD.two J hJ)
    (fun J hJ => (h.thmD.card J hJ).trans (by norm_num)) hL hM key

private theorem perpB_omegaStar_aeIdentOn (h : EndHyp Ω) {Q : Set (Subgroup G)} (hP : SecHyp 3 Ω Q)
    {m : ℕ} (hm : 5 ≤ m) {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AE.AEQ m)}
    (I : AEIdentOn Q m 𝒜 H) {L M : Subgroup G} (hL : L ∈ Q) (hM : M ∈ Q)
    (hne : L ≠ M) {α β : Finset (Fin m)} {hα : α.card = 4} {hβ : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan Q)).map I.φ = AE.memBar α hα b)
    (hlab' : (M.subgroupOf (pSpan Q)).map I.φ = AE.memBar β hβ c)
    (hv : ∃ v ∈ AE.memBar β hβ c, v * v ≠ 1 ∧
      ∀ a ∈ AE.memBar α hα b, v * a * v⁻¹ ∈ AE.memBar α hα b) :
    M ∈ omegaStarNbr Ω L := by
  have hgen := pSpan_restrictFamily_eq_top Q
  have hne' : L.subgroupOf (pSpan Q) ≠ M.subgroupOf (pSpan Q) := by
    intro e
    apply hne
    have := Subgroup.subgroupOf_inj.mp e
    rwa [inf_eq_left.mpr (le_pSpan hL), inf_eq_left.mpr (le_pSpan hM)] at this
  have hlabel : ∀ N ∈ restrictFamily Q (pSpan Q), ∃ (α' : Finset (Fin m))
      (h' : α'.card = 4) (b' : Bool), (N.subgroupOf (pSpan (restrictFamily Q (pSpan Q)))).map
        (I.φ.comp (spanEquiv hgen).symm.toMonoidHom) = AE.memBar α' h' b' := by
    intro N hN
    obtain ⟨α', -, h', b', hlab''⟩ := (perpB_aeIdentOn_restrict hgen I).label N hN
    exact ⟨α', h', b', hlab''⟩
  have key := fam_mem_omegaStarNbr_of_phi
    (perpB_aeIdentOn_restrict hgen I).φ (perpB_q8fam h hP) hm
    (perpB_aeIdentOn_restrict hgen I).ker_le hlabel
    ⟨L, hL, le_pSpan hL, rfl⟩ ⟨M, hM, le_pSpan hM, rfl⟩ hne'
    ((perpB_transport_map hgen I.φ L).trans hlab)
    ((perpB_transport_map hgen I.φ M).trans hlab') hv
  exact perpB_omegaStar_of_restrict hP.sub (fun J hJ => h.thmD.two J hJ)
    (fun J hJ => (h.thmD.card J hJ).trans (by norm_num)) hL hM key

private theorem perpB_label_of_commutes {Q : Set (Subgroup G)} (h : EndHyp Ω) (hP : SecHyp 3 Ω Q)
    {n : ℕ} (hn : 5 ≤ n) (φ : ↥(pSpan Q) →* AE.AEQ n) {L M : Subgroup G} (hL : L ∈ Q)
    (hM : M ∈ Q) (hcomm : Commutes L M) {α β : Finset (Fin n)} {hα : α.card = 4}
    {hβ : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan Q)).map φ = AE.memBar α hα b)
    (hlab' : (M.subgroupOf (pSpan Q)).map φ = AE.memBar β hβ c) :
    α = β ∨ Disjoint α β := by
  by_cases hab : α = β
  · exact Or.inl hab
  right
  obtain ⟨u, hu⟩ := (h.thmD.hyp.omega1 L (hP.sub hL)).1
  have h8L : Nat.card L = 8 := (hP.card L (hP.sub hL)).trans (by norm_num)
  have hzu := TC.Thin.phi_map_eq_zBar φ hn hL h8L hlab hu
  apply AE.disjoint_of_zBar_comm hab (c := c)
  intro y hy
  rw [← hlab'] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← hzu, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact hcomm u hu.mem x (Subgroup.mem_subgroupOf.mp hx)

private theorem perpB_not_disjoint_fin5 {α β : Finset (Fin 5)} (hα : α.card = 4) (hβ : β.card = 4) :
    ¬ Disjoint α β := by
  intro hd
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_univ (α ∪ β)
  rw [Fintype.card_fin] at h2
  omega

private theorem perpB_fibre (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) (I : AEIdent Q 5) :
    ∃ A ∈ Q, ∃ B ∈ Q, A ≠ B ∧ Commutes A B := by
  have hα : (({0, 1, 2, 3} : Finset (Fin 5))).card = 4 := by decide
  obtain ⟨A, hA, hlabA⟩ := I.label_surj _ hα true
  obtain ⟨B, hB, hlabB⟩ := I.label_surj _ hα false
  have hAB : A ≠ B := by
    intro e
    rw [e] at hlabA
    have := memBar_inj (by norm_num) (by norm_num) (hlabA.symm.trans hlabB)
    exact Bool.noConfusion this.2
  have hBΩ : B ∈ Ω := hP.sub hB
  have h8B : Nat.card B = 8 := (hP.card B hBΩ).trans (by norm_num)
  obtain ⟨x, hxB, hxx⟩ := (perpB_q8fam h hP).exists_mul_self_ne_one (B.subgroupOf (pSpan Q))
    ⟨B, hB, le_pSpan hB, rfl⟩
  have hxB' : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hxB
  have hv : ∃ v ∈ AE.memBar ({0, 1, 2, 3} : Finset (Fin 5)) hα false, v * v ≠ 1 ∧
      ∀ a ∈ AE.memBar ({0, 1, 2, 3} : Finset (Fin 5)) hα true,
        v * a * v⁻¹ ∈ AE.memBar ({0, 1, 2, 3} : Finset (Fin 5)) hα true := by
    refine ⟨I.φ x, ?_, ?_, ?_⟩
    · rw [← hlabB]
      exact Subgroup.mem_map_of_mem _ hxB
    · rw [← map_mul]
      intro he
      apply hxx
      have hmem : (x : G) * x ∈ B := B.mul_mem hxB' hxB'
      have he' : I.φ (x * x) = I.φ 1 := by rw [map_one]; exact he
      have := TC.Thin.phi_injOn I.φ (le_refl 5) hB h8B hlabB hmem (B.one_mem) he'
      exact Subtype.ext (by simpa using this)
    · intro a ha
      have hc := comm_memBar_twin _ hα a ha (I.φ x)
        (by rw [← hlabB]; exact Subgroup.mem_map_of_mem _ hxB)
      have hconj : I.φ x * a * (I.φ x)⁻¹ = a := by
        rw [← hc]
        group
      rw [hconj]
      exact ha
  exact ⟨A, hA, B, hB, hAB,
    perpB_star_comm h (dComp_subset_of_mem hK (hQS hA))
      (by rw [perpB_dComp_eq hK (hQS hA)]; exact hQS hB)
      (perpB_omegaStar_aeIdent h hP (le_refl 5) I hA hB hAB hlabA hlabB hv)⟩

private theorem perpB_ae5_sigma_false (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hP : SecHyp 3 Ω (dComp Ω K)) (I : AEIdent (dComp Ω K) 5) : False := by
  have hKS : K ∈ dComp Ω K := Relation.ReflTransGen.refl
  obtain ⟨α₀, hα₀, b₀, hlab₀⟩ := I.label K hKS
  obtain ⟨β, hβ, hβne⟩ : ∃ β : Finset (Fin 5), β.card = 4 ∧ β ≠ α₀ := by
    by_cases h1 : α₀ = {0, 1, 2, 3}
    · exact ⟨{0, 1, 2, 4}, by decide, fun e => by
        rw [h1] at e
        exact absurd e (by decide)⟩
    · exact ⟨{0, 1, 2, 3}, by decide, fun e => h1 e.symm⟩
  obtain ⟨B, hB, hlabB⟩ := I.label_surj β hβ true
  have hall : ∀ L, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L →
      Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L ∧
        ∃ (hc : α₀.card = 4) (b : Bool),
          (L.subgroupOf (pSpan (dComp Ω K))).map I.φ = AE.memBar α₀ hc b := by
    intro L hL
    induction hL with
    | refl => exact ⟨Relation.ReflTransGen.refl, hα₀, b₀, hlab₀⟩
    | @tail c d hcR hstep ih =>
      obtain ⟨-, hc, bc, hlabc⟩ := ih
      have hdR : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N)
          K d := Relation.ReflTransGen.tail hcR hstep
      refine ⟨hdR, ?_⟩
      have hcS : c ∈ dComp Ω K := hcR
      have hdS : d ∈ dComp Ω K := hdR
      obtain ⟨α_d, hα_d, b_d, hlab_d⟩ := I.label d hdS
      have hcomm : Commutes c d := by
        rcases hstep.2 with hd1 | hd2
        · exact comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two (dComp_subset_of_mem hK hcS) hd1
        · exact perpB_comm_symm
            (comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two (dComp_subset_of_mem hK hdS) hd2)
      rcases perpB_label_of_commutes h hP (le_refl 5) I.φ hcS hdS hcomm hlabc hlab_d with e | e
      · subst e
        exact ⟨hα_d, b_d, hlab_d⟩
      · exact absurd e (perpB_not_disjoint_fin5 hα₀ hα_d)
  obtain ⟨-, hc, b', hlab'⟩ := hall B hB
  have := memBar_inj
    (by norm_num) (by norm_num) (hlabB.symm.trans hlab')
  exact hβne this.1

private theorem perpB_exists_pair_fin {m : ℕ} (hm : 6 ≤ m) :
    ∃ α β : Finset (Fin m), α.card = 4 ∧ β.card = 4 ∧ (α ∩ β).card = 2 := by
  let f : Fin 6 ↪ Fin m := ⟨fun i => ⟨i.val, by omega⟩, fun i j hij => Fin.ext (by
    have := congrArg Fin.val hij
    simpa using this)⟩
  refine ⟨({0, 1, 2, 3} : Finset (Fin 6)).map f, ({0, 1, 4, 5} : Finset (Fin 6)).map f, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    decide
  · rw [Finset.card_map]
    decide
  · rw [← Finset.map_inter, Finset.card_map]
    decide

private theorem perpB_false_of_inter_two {Q : Set (Subgroup G)} (h : EndHyp Ω) (hP : SecHyp 3 Ω Q)
    {K : Subgroup G} (hK : K ∈ Ω) (hQS : Q ⊆ dComp Ω K) {m : ℕ} (hm : 5 ≤ m)
    (I : AEIdent Q m) {α β : Finset (Fin m)} (hα : α.card = 4) (hβ : β.card = 4)
    (hint : (α ∩ β).card = 2)
    (hdist : ∀ b c : Bool, AE.memBar α hα b ≠ AE.memBar β hβ c) : False := by
  obtain ⟨A, hA, hlabA⟩ := I.label_surj α hα true
  obtain ⟨B, hB, hlabB⟩ := I.label_surj β hβ true
  have hαβ : α ≠ β := by
    intro e
    rw [e, Finset.inter_self, hβ] at hint
    norm_num at hint
  have hAB : A ≠ B := by
    intro e
    rw [e] at hlabA
    exact hdist true true (hlabA.symm.trans hlabB)
  obtain ⟨v, hv, hvv, hvn⟩ := exists_normalizing_memBar
    hm hα hβ hint
  have hBA := perpB_omegaStar_aeIdent h hP hm I hA hB hAB hlabA hlabB ⟨v, hv, hvv, hvn⟩
  have hcomm := perpB_star_comm h (dComp_subset_of_mem hK (hQS hA))
    (by rw [perpB_dComp_eq hK (hQS hA)]; exact hQS hB) hBA
  rcases perpB_label_of_commutes h hP hm I.φ hA hB hcomm hlabA hlabB with e | e
  · exact hαβ e
  · have h0 := Finset.disjoint_iff_inter_eq_empty.mp e
    rw [h0] at hint
    norm_num at hint

private theorem perpB_false_of_inter_two_on {Q : Set (Subgroup G)} (h : EndHyp Ω)
    (hP : SecHyp 3 Ω Q)
    {K : Subgroup G} (hK : K ∈ Ω) (hQS : Q ⊆ dComp Ω K) {m : ℕ} (hm : 5 ≤ m)
    {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AE.AEQ m)} (I : AEIdentOn Q m 𝒜 H)
    {α β : Finset (Fin m)} (hα𝒜 : α ∈ 𝒜) (hβ𝒜 : β ∈ 𝒜) (hα : α.card = 4) (hβ : β.card = 4)
    (hint : (α ∩ β).card = 2)
    (hdist : ∀ b c : Bool, AE.memBar α hα b ≠ AE.memBar β hβ c) : False := by
  obtain ⟨A, hA, hlabA⟩ := I.label_surj α hα𝒜 hα true
  obtain ⟨B, hB, hlabB⟩ := I.label_surj β hβ𝒜 hβ true
  have hαβ : α ≠ β := by
    intro e
    rw [e, Finset.inter_self, hβ] at hint
    norm_num at hint
  have hAB : A ≠ B := by
    intro e
    rw [e] at hlabA
    exact hdist true true (hlabA.symm.trans hlabB)
  obtain ⟨v, hv, hvv, hvn⟩ := exists_normalizing_memBar
    hm hα hβ hint
  have hBA := perpB_omegaStar_aeIdentOn h hP hm I hA hB hAB hlabA hlabB ⟨v, hv, hvv, hvn⟩
  have hcomm := perpB_star_comm h (dComp_subset_of_mem hK (hQS hA))
    (by rw [perpB_dComp_eq hK (hQS hA)]; exact hQS hB) hBA
  rcases perpB_label_of_commutes h hP hm I.φ hA hB hcomm hlabA hlabB with e | e
  · exact hαβ e
  · have h0 := Finset.disjoint_iff_inter_eq_empty.mp e
    rw [h0] at hint
    norm_num at hint

private theorem perpB_memBar_ne_fin8 {α β : Finset (Fin 8)} (hα : α.card = 4) (hβ : β.card = 4)
    (hint : (α ∩ β).card = 2) (b c : Bool) : AE.memBar α hα b ≠ AE.memBar β hβ c := by
  intro he
  have hz : AE.zBar β hβ ∈ AE.memBar α hα b := he ▸ AE.zBar_mem_memBar β hβ c
  rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hz (AE.zBar_mul_self β hβ) with h1 | h1
  · exact AE.zBar_ne_one (by norm_num) β hβ h1
  · have hmk : AE.mkQ 8 (AE.zOf (AE.emb β hβ)) = AE.mkQ 8 (AE.zOf (AE.emb α hα)) := h1
    rcases perpB_range_or_compl hmk with hr | hc
    · rw [AE.range_emb, AE.range_emb] at hr
      have hab : α = β := Finset.coe_inj.mp hr.symm
      subst hab
      rw [Finset.inter_self, hα] at hint
      norm_num at hint
    · have hempty : α ∩ β = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter] at hx
        have hxb : x ∈ Set.range (AE.emb β hβ) := by
          rw [AE.range_emb]
          exact hx.2
        have hxa := (hc x).mp hxb
        rw [AE.range_emb] at hxa
        exact hxa hx.1
      rw [hempty, Finset.card_empty] at hint
      norm_num at hint

private theorem perpB_false_e64 (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) (I : AEIdentOn Q 7 AE.e64Sets AE.e64Sub) :
    False := by
  have hα : (({0, 1, 3} : Finset (Fin 7))ᶜ) ∈ AE.e64Sets := ⟨{0, 1, 3}, by decide, rfl⟩
  have hβ : (({1, 2, 4} : Finset (Fin 7))ᶜ) ∈ AE.e64Sets := ⟨{1, 2, 4}, by decide, rfl⟩
  have hne : (({0, 1, 3} : Finset (Fin 7))ᶜ) ≠ (({1, 2, 4} : Finset (Fin 7))ᶜ) := by decide
  have hcα := card_of_mem_e64Sets hα
  have hcβ := card_of_mem_e64Sets hβ
  have hadj := adj4_of_mem_e64Sets hα hβ hne
  have hint : ((({0, 1, 3} : Finset (Fin 7))ᶜ) ∩ (({1, 2, 4} : Finset (Fin 7))ᶜ)).card = 2 := by
    rcases hadj with h2 | hd
    · exact h2
    · have h1 := Finset.card_union_of_disjoint hd
      have h2 := Finset.card_le_univ (((({0, 1, 3} : Finset (Fin 7))ᶜ) ∪
        (({1, 2, 4} : Finset (Fin 7))ᶜ)))
      rw [Fintype.card_fin] at h2
      omega
  refine perpB_false_of_inter_two_on h hP hK hQS (by norm_num) I hα hβ hcα hcβ hint ?_
  intro b c he
  have := memBar_inj (by norm_num)
    (by norm_num) he.symm
  exact hne this.1.symm

private theorem perpB_false_e29 (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) (I : AEIdentOn Q 8 AE.e29Sets AE.e29Sub) :
    False := by
  have hα : (({0, 2, 4, 6} : Finset (Fin 8))) ∈ AE.e29Sets :=
    (show (({0, 2, 4, 6} : Finset (Fin 8))) ∈ AE.affinePlanes by decide)
  have hβ : (({0, 1, 4, 5} : Finset (Fin 8))) ∈ AE.e29Sets :=
    (show (({0, 1, 4, 5} : Finset (Fin 8))) ∈ AE.affinePlanes by decide)
  have hcα := card_of_mem_e29Sets hα
  have hcβ := card_of_mem_e29Sets hβ
  have hint : (({0, 2, 4, 6} : Finset (Fin 8)) ∩ ({0, 1, 4, 5} : Finset (Fin 8))).card = 2 := by
    decide
  exact perpB_false_of_inter_two_on h hP hK hQS (by norm_num) I hα hβ hcα hcβ hint
    (fun b c => perpB_memBar_ne_fin8 hcα hcβ hint b c)

private theorem perpB_false_aeIdent_ge6 (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {Q : Set (Subgroup G)} (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) {m : ℕ} (hm : 6 ≤ m)
    (I : AEIdent Q m) : False := by
  obtain ⟨α, β, hα, hβ, hint⟩ := perpB_exists_pair_fin hm
  by_cases hm8 : m = 8
  · subst hm8
    exact perpB_false_of_inter_two h hP hK hQS (by norm_num) I hα hβ hint
      (fun b c => perpB_memBar_ne_fin8 hα hβ hint b c)
  · refine perpB_false_of_inter_two h hP hK hQS (by omega) I hα hβ hint ?_
    intro b c he
    have hh := memBar_inj (by omega) hm8
      he.symm
    obtain ⟨e1, -⟩ := hh
    subst e1
    rw [Finset.inter_self, hα] at hint
    norm_num at hint

private theorem perpB_clique_of_wIn (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) {W : Subgroup G}
    (hW : WIn Q (pSpan Q) = {W}) : PerpBClique Q := by
  have hΔ : ConjInvariant (restrictFamily Q (pSpan Q)) :=
    conjInvariant_restrictFamily (fun L hL x hx => hP.inv L hL x hx)
  have hWmem : W ∈ WIn Q (pSpan Q) := by
    rw [hW]
    exact Set.mem_singleton W
  obtain ⟨W', hW'S, hW'eq⟩ := hWmem
  have hW'map : Subgroup.map (pSpan Q).subtype W' = W := hW'eq
  have huniq : ∀ W'' ∈ WSet (restrictFamily Q (pSpan Q)),
      Subgroup.map (pSpan Q).subtype W'' = W := by
    intro W'' hW''
    have hmem : Subgroup.map (pSpan Q).subtype W'' ∈ WIn Q (pSpan Q) := ⟨W'', hW'', rfl⟩
    rw [hW] at hmem
    exact hmem
  have hnorm : ∀ x : pSpan Q, x ∈ Subgroup.normalizer (W' : Set (pSpan Q)) := by
    intro x
    rw [mem_normalizer_iff_conjSub_eq]
    apply Subgroup.map_injective (f := (pSpan Q).subtype) (pSpan Q).subtype_injective
    rw [huniq _ (WSet.conj hΔ hW'S x), hW'map]
  have h2 : ∀ N ∈ Q, IsPGroup 2 ↥(N.subgroupOf (pSpan Q)) := fun N hN =>
    (hP.two N (hP.sub hN)).comap_subtype
  have hsyl : ∀ N ∈ Q, IsSylow2In (N.subgroupOf (pSpan Q)) (N.subgroupOf (pSpan Q)) :=
    fun N hN => ⟨le_rfl, h2 N hN, fun V' hV' _ hV'' => le_antisymm hV' hV''⟩
  have hDS : ∀ N ∈ Q, N.subgroupOf (pSpan Q) ∈ DSet (restrictFamily Q (pSpan Q)) W' :=
    fun N hN => ⟨TC.mem_RSet_of_isPGroup ⟨N, hN, le_pSpan hN, rfl⟩ (h2 N hN),
      fun x _ => hnorm x⟩
  intro L hL L' hL' hne
  have hne' : L.subgroupOf (pSpan Q) ≠ L'.subgroupOf (pSpan Q) := by
    intro e
    apply hne
    have := Subgroup.subgroupOf_inj.mp e
    rwa [inf_eq_left.mpr (le_pSpan hL), inf_eq_left.mpr (le_pSpan hL')] at this
  have hOS := Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hP.thmDHyp.hyp hW'S
    (⟨L, hL, le_pSpan hL, rfl⟩ : L.subgroupOf (pSpan Q) ∈ restrictFamily Q (pSpan Q))
    (⟨L', hL', le_pSpan hL', rfl⟩ : L'.subgroupOf (pSpan Q) ∈ restrictFamily Q (pSpan Q))
    hne' (hDS L hL) (hDS L' hL') (hsyl L hL) (hsyl L' hL')
  have hLL' := perpB_omegaStar_of_restrict hP.sub (fun J hJ => h.thmD.two J hJ)
    (fun J hJ => (h.thmD.card J hJ).trans (by norm_num)) hL hL' hOS.1
  exact perpB_star_comm h (dComp_subset_of_mem hK (hQS hL))
    (by rw [perpB_dComp_eq hK (hQS hL)]; exact hQS hL') hLL'

private theorem perpB_clique_of_e8 (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) {E : Subgroup G} (hE : E8Struct (pSpan Q) E) :
    PerpBClique Q := by
  have key : ∀ L₀ ∈ Q, ∀ M ∈ Q, L₀ ≠ M → Commutes L₀ M := by
    intro L₀ hL₀ M hM hne
    have hL₀Ω := hP.sub hL₀
    have hMΩ := hP.sub hM
    obtain ⟨u, hu⟩ := (h.thmD.hyp.omega1 L₀ hL₀Ω).1
    obtain ⟨w, hw⟩ := (h.thmD.hyp.omega1 M hMΩ).1
    by_cases huw : u = w
    · subst huw
      exact CFSG.ClassicalInvolution.Q3.TC.Thin.twin_comm h.thmD.hyp h.thmD.two hL₀Ω hMΩ hne hu hw
    have hwE : w ∈ E := SecHyp.e8_inv_mem hP hE hM hw
    have hq : IsQuatSub L₀ := Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp
      (TC.mem_RSet_of_isPGroup hL₀Ω (h.thmD.two L₀ hL₀Ω))
    have hcard8 : Nat.card ↥L₀ = 8 := (hP.card L₀ hL₀Ω).trans (by norm_num)
    obtain ⟨e⟩ := perpB_q8_iso hq hcard8
    set X : ↥L₀ := e.symm (QuaternionGroup.a 1) with hXdef
    set Y : ↥L₀ := e.symm (QuaternionGroup.xa 0) with hYdef
    have hi4 : orderOf (X : G) = 4 := by
      rw [Subgroup.orderOf_coe, hXdef, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
    have hj4 : orderOf (Y : G) = 4 := by
      rw [Subgroup.orderOf_coe, hYdef, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
    have hXY : X * Y = e.symm (QuaternionGroup.xa 3) := by
      rw [hXdef, hYdef, ← MulEquiv.map_mul]
      congr 1
    have hij4 : orderOf ((X * Y : ↥L₀) : G) = 4 := by
      rw [Subgroup.orderOf_coe, hXY, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
    have hnc1 : (X : G) * (Y : G) ≠ (Y : G) * (X : G) := by
      intro hc
      have h1 : X * Y = Y * X := Subtype.ext hc
      have h2 := congrArg e h1
      simp only [map_mul, hXdef, hYdef, MulEquiv.apply_symm_apply] at h2
      exact (show (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2) ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide) h2
    have hnc2 : ((X * Y : ↥L₀) : G) * (X : G) ≠ (X : G) * ((X * Y : ↥L₀) : G) := by
      intro hc
      have h1 : (X * Y) * X = X * (X * Y) := Subtype.ext hc
      have h2 := congrArg e h1
      simp only [map_mul, hXdef, hYdef, MulEquiv.apply_symm_apply] at h2
      exact (show (QuaternionGroup.a 1 * QuaternionGroup.xa 0 * QuaternionGroup.a 1 :
        QuaternionGroup 2) ≠ QuaternionGroup.a 1 * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) by
          decide) h2
    have hXX : (X : G) * (X : G) = u := by
      have hsq : ((X : G) * X) * ((X : G) * X) = 1 := by
        have h4 := pow_orderOf_eq_one (X : G)
        rw [hi4] at h4
        calc (X : G) * X * ((X : G) * X) = (X : G) ^ 4 := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = 1 := h4
      have hne1 : (X : G) * X ≠ 1 := by
        intro h1
        have hd := orderOf_dvd_of_pow_eq_one
          (show (X : G) ^ 2 = 1 by rw [pow_two]; exact h1)
        rw [hi4] at hd
        norm_num at hd
      exact (hu.unique _ (L₀.mul_mem X.2 X.2) hsq).resolve_left hne1
    have hconj : ∀ k ∈ L₀, ∀ x ∈ E, k * x * k⁻¹ = x ∨ k * x * k⁻¹ = u * x :=
      fun k hk x hx => SecHyp.e8_conj_mem_or hP hE hL₀ hu hk hx
    have hcov : ∃ v : G, v ∈ L₀ ∧ orderOf v = 4 ∧ v * w = w * v ∧
        ¬ (∀ x ∈ L₀, v * x = x * v) := by
      by_cases h1 : (X : G) * w = w * (X : G)
      · exact ⟨X, X.2, hi4, h1, fun hc => hnc1 (hc Y Y.2)⟩
      by_cases h2 : (Y : G) * w = w * (Y : G)
      · exact ⟨Y, Y.2, hj4, h2, fun hc => hnc1 (hc X X.2).symm⟩
      have hiw : (X : G) * w * (X : G)⁻¹ = u * w := by
        rcases hconj X X.2 w hwE with hh | hh
        · exact absurd (by
            calc (X : G) * w = (X : G) * w * (X : G)⁻¹ * (X : G) := by group
              _ = w * (X : G) := by rw [hh]) h1
        · exact hh
      have hjw : (Y : G) * w * (Y : G)⁻¹ = u * w := by
        rcases hconj Y Y.2 w hwE with hh | hh
        · exact absurd (by
            calc (Y : G) * w = (Y : G) * w * (Y : G)⁻¹ * (Y : G) := by group
              _ = w * (Y : G) := by rw [hh]) h2
        · exact hh
      have hiu : (X : G) * u * (X : G)⁻¹ = u := by
        rw [← hXX]
        group
      refine ⟨(X : G) * (Y : G), L₀.mul_mem X.2 Y.2, hij4, ?_, ?_⟩
      · have hc : ((X : G) * Y) * w * ((X : G) * Y)⁻¹ = w := by
          calc ((X : G) * Y) * w * ((X : G) * Y)⁻¹
              = (X : G) * ((Y : G) * w * (Y : G)⁻¹) * (X : G)⁻¹ := by group
            _ = (X : G) * (u * w) * (X : G)⁻¹ := by rw [hjw]
            _ = ((X : G) * u * (X : G)⁻¹) * ((X : G) * w * (X : G)⁻¹) := by group
            _ = u * (u * w) := by rw [hiu, hiw]
            _ = w := by rw [← mul_assoc, hu.sq, one_mul]
        calc ((X : G) * Y) * w = (((X : G) * Y) * w * ((X : G) * Y)⁻¹) * ((X : G) * Y) := by
              group
          _ = w * ((X : G) * Y) := by rw [hc]
      · intro hall
        exact hnc2 (hall X X.2)
    obtain ⟨v, hvL, hv4, hvw, hvnc⟩ := hcov
    have h2v : IsPGroup 2 (Subgroup.zpowers v) :=
      (h.thmD.two L₀ hL₀Ω).to_le (Subgroup.zpowers_le.mpr hvL)
    have hvN : v ∈ Subgroup.normalizer (M : Set G) :=
      h.thmD.hyp.omega5 M hMΩ L₀ hL₀Ω hne.symm w hw v hvL hvnc h2v hvw
    have hU : Subgroup.zpowers v ∈ USet Ω :=
      mem_USet_of_natCard hL₀Ω
        ⟨le_rfl, h.thmD.two L₀ hL₀Ω, fun V' hV' _ hV'' => le_antisymm hV' hV''⟩
        (Subgroup.zpowers_le.mpr hvL) inferInstance
        (by rw [hcard8, Nat.card_zpowers, hv4])
    have hLM : L₀ ∈ omegaStarNbr Ω M :=
      ⟨hL₀Ω, hne, Subgroup.zpowers v, hU, Subgroup.zpowers_le.mpr hvL,
        Subgroup.zpowers_le.mpr hvN⟩
    exact perpB_comm_symm (perpB_star_comm h hMΩ
      (by rw [perpB_dComp_eq hK (hQS hM)]; exact hQS hL₀) hLM)
  intro L hL L' hL' hne
  exact key L hL L' hL' hne

private theorem perpB_outcome (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {Q : Set (Subgroup G)}
    (hQS : Q ⊆ dComp Ω K) (hP : SecHyp 3 Ω Q) (hO : SectionOutcome Q) :
    Nonempty (AEIdent Q 5) ∨ PerpBClique Q := by
  rcases hO with hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm, hIm⟩ | hI29
  · exact Or.inr fun L hL L' hL' hne => absurd (hsing L hL L' hL') hne
  · exact Or.inr (perpB_clique_of_wIn h hK hQS hP hW)
  · exact Or.inr (perpB_clique_of_e8 h hK hQS hP hE)
  · obtain ⟨I⟩ := hI64
    exact (perpB_false_e64 h hK hQS hP I).elim
  · obtain ⟨I⟩ := hIm
    rcases Nat.lt_or_ge m 6 with hm6 | hm6
    · have hm5 : m = 5 := by omega
      subst hm5
      exact Or.inl ⟨I⟩
    · exact (perpB_false_aeIdent_ge6 h hK hQS hP hm6 I).elim
  · obtain ⟨I⟩ := hI29
    exact (perpB_false_e29 h hK hQS hP I).elim

theorem caseB_structure (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) (hne : KPerp Ω J ≠ KPerp Ω K) :
    (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) ∧
    ∃ P₁ P₂ : Set (Subgroup G), K ∈ P₁ ∧ dComp Ω K = P₁ ∪ P₂ ∧ Disjoint P₁ P₂ ∧
      (∀ L ∈ P₁, ∀ L' ∈ P₂, ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∃ g : G, conjSub g K ∈ P₂ ∧ ∀ L : Subgroup G, L ∈ P₂ ↔ conjSub g⁻¹ L ∈ P₁) ∧
      (∀ L ∈ P₁, ∀ x ∈ pSpan P₁, conjSub x L ∈ P₁) ∧
      (∀ L ∈ P₁, ∀ L' ∈ P₁, ∃ x ∈ pSpan P₁, conjSub x L = L') ∧
      classicalInvolutionOddCore ↥(pSpan P₁) = ⊥ ∧
      Nonempty (AEIdent P₁ 5) := by
  have hdisc : ¬ Disconnected.DConnected Ω := h.disc
  have hKS : K ∈ dComp Ω K := Relation.ReflTransGen.refl
  by_cases hT : ∀ L ∈ dComp Ω K, ∀ L' ∈ dComp Ω K, ∃ x ∈ pSpan (dComp Ω K), conjSub x L = L'
  ·
    exfalso
    have hSC := h.sectionConcl_dComp hdisc hK
    unfold SectionConcl at hSC
    have hO : SectionOutcome (dComp Ω K) := by
      rcases hSC with ⟨⟨L, hL, L', hL', hnc⟩, _⟩ | ⟨_, _, hO⟩
      · exact absurd (hT L hL L' hL') hnc
      · exact hO
    have hP := perpB_secHyp h (dComp_subset_of_mem hK)
      (fun L hL x hx => h.conjSub_mem_dComp hK hL hx) hT (oddCore_pSpan_dComp h hK)
    rcases perpB_outcome h hK (subset_refl _) hP hO with hAE | hcl
    · obtain ⟨I⟩ := hAE
      exact perpB_ae5_sigma_false h hK hP I
    · exact perpB_sigma_clique_false h hK hJ hne hcl
  have hSC := h.sectionConcl_dComp hdisc hK
  unfold SectionConcl at hSC
  have hcross : ∀ A ∈ dComp Ω K, ∀ B ∈ dComp Ω K,
      (¬ ∃ x ∈ pSpan (dComp Ω K), conjSub x A = B) → Commutes A B := by
    rcases hSC with ⟨_, hc⟩ | ⟨ht, _⟩
    · exact hc
    · exact absurd ht hT
  have hP₁S : perpBOrb (dComp Ω K) K ⊆ dComp Ω K := fun L hL => perpB_orb_sub h hK hKS hL
  have hP₁inv : ∀ L ∈ perpBOrb (dComp Ω K) K, ∀ x ∈ pSpan (perpBOrb (dComp Ω K) K),
      conjSub x L ∈ perpBOrb (dComp Ω K) K := fun L hL x hx =>
    perpBOrb_conj (perpB_pSpan_mono hP₁S hx) hL
  have hcrossP : ∀ A ∈ perpBOrb (dComp Ω K) K, ∀ B ∈ dComp Ω K,
      B ∉ perpBOrb (dComp Ω K) K → Commutes A B := by
    intro A hA B hB hBn
    apply hcross A (hP₁S hA) B hB
    rintro ⟨x, hx, hxe⟩
    exact hBn (hxe ▸ perpBOrb_conj hx hA)
  have hP₁tr : ∀ L ∈ perpBOrb (dComp Ω K) K, ∀ L' ∈ perpBOrb (dComp Ω K) K,
      ∃ x ∈ pSpan (perpBOrb (dComp Ω K) K), conjSub x L = L' :=
    fun L hL L' hL' => perpB_trans_of_cross hP₁inv hcrossP hL (perpBOrb_trans hL hL')
  have hP₁Ω : perpBOrb (dComp Ω K) K ⊆ Ω := fun L hL => dComp_subset_of_mem hK (hP₁S hL)
  have hodd₁ : classicalInvolutionOddCore ↥(pSpan (perpBOrb (dComp Ω K) K)) = ⊥ :=
    perpB_odd_sub (perpB_pSpan_mono hP₁S)
      (fun y hy x hx => perpB_conj_pSpan (perpB_norm_orb hy) hx)
      (oddCore_pSpan_dComp h hK)
  have hlt : Nat.card ↥(pSpan (perpBOrb (dComp Ω K) K)) < Nat.card G :=
    lt_of_le_of_lt (Subgroup.card_le_of_le (perpB_pSpan_mono hP₁S))
      (h.card_pSpan_dComp_lt hdisc hK)
  have hSO₁ : SectionOutcome (perpBOrb (dComp Ω K) K) := by
    have hSC₁ := h.sectionConcl hP₁Ω hP₁inv hlt
    unfold SectionConcl at hSC₁
    rcases hSC₁ with ⟨⟨L, hL, L', hL', hnc⟩, _⟩ | ⟨_, _, hO⟩
    · exact absurd (hP₁tr L hL L' hL') hnc
    · exact hO
  have hP₁sec : SecHyp 3 Ω (perpBOrb (dComp Ω K) K) :=
    perpB_secHyp h hP₁Ω hP₁inv hP₁tr hodd₁
  have hAE₁ : Nonempty (AEIdent (perpBOrb (dComp Ω K) K) 5) := by
    rcases perpB_outcome h hK hP₁S hP₁sec hSO₁ with hAE | hcl
    · exact hAE
    · exact (perpB_sigma_clique_false h hK hJ hne
        (perpB_sigma_clique_of_orb h hK hKS hcross hcl)).elim
  obtain ⟨I⟩ := hAE₁
  obtain ⟨A, hA, B, hB, hAB, hcAB⟩ := perpB_fibre h hK hP₁S hP₁sec I
  obtain ⟨W₀, hW₀, hR₀⟩ := perpB_exists_W h hK
  set P₁ := perpBOrb (dComp Ω K) K with hP₁def
  set P₂ : Set (Subgroup G) := {L | L ∈ dComp Ω K ∧ L ∉ P₁} with hP₂def
  have hP₂ne : ∃ M, M ∈ P₂ := by
    by_contra hcon
    apply hT
    intro L hL L' hL'
    have hL1 : L ∈ P₁ := by
      by_contra hn
      exact hcon ⟨L, hL, hn⟩
    have hL1' : L' ∈ P₁ := by
      by_contra hn
      exact hcon ⟨L', hL', hn⟩
    exact perpBOrb_trans hL1 hL1'
  obtain ⟨M₀, hM₀⟩ := hP₂ne
  have hP₂orb : ∀ M ∈ P₂, ∀ N ∈ P₂, N ∈ perpBOrb (dComp Ω K) M := by
    intro M hM N hN
    by_contra hNM
    exact perpB_six_false h hK hcross hA hB hAB hcAB hM.1 hN.1 hM.2 hN.2 hNM hW₀ hR₀
  have hP₂sub : ∀ X ∈ perpBOrb (dComp Ω K) M₀, X ∈ P₂ := by
    intro X hX
    refine ⟨perpB_orb_sub h hK hM₀.1 hX, ?_⟩
    intro hXP
    apply hM₀.2
    have e1 := perpBOrb_eq hX
    have e2 := perpBOrb_eq hXP
    have : M₀ ∈ perpBOrb (dComp Ω K) K := by
      rw [← e2, e1]
      exact perpBOrb_self _ _
    exact this
  obtain ⟨g₀, hg₀, hg₀N⟩ := perpB_norm_dComp h hK hM₀.1
  have hiff : ∀ L : Subgroup G, L ∈ P₂ ↔ conjSub g₀⁻¹ L ∈ P₁ := by
    intro L
    constructor
    · intro hL
      have hLo := hP₂orb M₀ hM₀ L hL
      have := perpB_conj_mem_orb hg₀N.inv hLo
      rw [← hg₀, conjSub_inv_conjSub] at this
      exact this
    · intro hL
      have := perpB_conj_mem_orb hg₀N hL
      rw [perpB_conj_conj_inv, hg₀] at this
      exact hP₂sub L this
  have hcross12 : ∀ L ∈ P₁, ∀ L' ∈ P₂, Commutes L L' := by
    intro L hL L' hL'
    apply hcross L (hP₁S hL) L' hL'.1
    rintro ⟨x, hx, hxe⟩
    exact hL'.2 (hxe ▸ perpBOrb_conj hx hL)
  have hconjP₂ : ∀ L ∈ P₁, conjSub g₀ L ∈ P₂ := fun L hL =>
    (hiff (conjSub g₀ L)).mpr (by rw [conjSub_inv_conjSub]; exact hL)
  have hdisj : ∀ X ∈ P₁, ∀ Y ∈ P₂, X ≠ Y := fun X hX Y hY e => hY.2 (e ▸ hX)
  have hconjinj : ∀ {X Y : Subgroup G}, conjSub g₀ X = conjSub g₀ Y → X = Y := by
    intro X Y e
    have := congrArg (conjSub g₀⁻¹) e
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W := by
    intro W hW
    obtain ⟨g, hg⟩ := wSet_conj h hW₀ hW
    have hRW : conjSub g K ∈ DSet Ω W := by
      rw [← hg]
      exact perpB_dSet_conj h hR₀ g
    have hA' := hconjP₂ A hA
    have hB' := hconjP₂ B hB
    have d2 : A ≠ conjSub g₀ A := hdisj A hA _ hA'
    have d3 : A ≠ conjSub g₀ B := hdisj A hA _ hB'
    have d4 : B ≠ conjSub g₀ A := hdisj B hB _ hA'
    have d5 : B ≠ conjSub g₀ B := hdisj B hB _ hB'
    have d6 : conjSub g₀ A ≠ conjSub g₀ B := fun e => hAB (hconjinj e)
    have hC4 : ({A, B, conjSub g₀ A, conjSub g₀ B} : Set (Subgroup G)) ⊆ Ω := by
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl
      · exact hP₁Ω hA
      · exact hP₁Ω hB
      · exact (dComp_subset_of_mem hK hA'.1)
      · exact (dComp_subset_of_mem hK hB'.1)
    have hclq : PerpBClique ({A, B, conjSub g₀ A, conjSub g₀ B} : Set (Subgroup G)) := by
      intro X hX Y hY hXY
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
      have c1 : Commutes A (conjSub g₀ A) := hcross12 A hA _ hA'
      have c2 : Commutes A (conjSub g₀ B) := hcross12 A hA _ hB'
      have c3 : Commutes B (conjSub g₀ A) := hcross12 B hB _ hA'
      have c4 : Commutes B (conjSub g₀ B) := hcross12 B hB _ hB'
      have c5 : Commutes (conjSub g₀ A) (conjSub g₀ B) := perpB_conjSub_commutes hcAB
      rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl hXY
        | assumption
        | exact perpB_comm_symm (by assumption)
    have n1 : A ∉ ({B, conjSub g₀ A, conjSub g₀ B} : Set (Subgroup G)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hAB, d2, d3⟩
    have n2 : B ∉ ({conjSub g₀ A, conjSub g₀ B} : Set (Subgroup G)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨d4, d5⟩
    have hcard4 : ({A, B, conjSub g₀ A, conjSub g₀ B} : Set (Subgroup G)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair d6]
    exact perpB_wylD4_of_card h hC4 hclq hW hRW (le_of_eq hcard4.symm)
  have hKP₁ : K ∈ P₁ := perpBOrb_self _ _
  have hunion : dComp Ω K = P₁ ∪ P₂ := by
    ext L
    constructor
    · intro hL
      by_cases hLP : L ∈ P₁
      · exact Or.inl hLP
      · exact Or.inr ⟨hL, hLP⟩
    · rintro (hL | hL)
      · exact hP₁S hL
      · exact hL.1
  refine ⟨hμ, P₁, P₂, hKP₁, hunion, Set.disjoint_left.mpr (fun L hL1 hL2 => hL2.2 hL1),
    hcross12, ⟨g₀, by rw [hg₀]; exact hM₀, hiff⟩, hP₁inv, hP₁tr, hodd₁, ⟨I⟩⟩

end CFSG.ClassicalInvolution.Q3.Sec13
end
