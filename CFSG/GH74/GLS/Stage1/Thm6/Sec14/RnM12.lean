module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnCfg
public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.RFacts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Asc03
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnFinal

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.M12Facts CFSG.GH74.GLS.Stage1.Thm6.Sec14
open scoped commutatorElement

section M12

variable {G : Type} [Group G] {S : Subgroup G} {a b y x : G} (h : Sec13.M12Data S a b y x)

abbrev Cz (a b : G) : Subgroup G := Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set G)

include h in
theorem S_le_Cz : S ≤ Cz a b := by
  intro s hs
  rw [mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  rw [ht]
  exact (z_central h hs).symm

@[expose] def νC (p : NF) : ↥(Cz a b) := ⟨nu a b y x p, S_le_Cz h (nu_mem h p)⟩

theorem νC_val (p : NF) : ((νC h p : ↥(Cz a b)) : G) = nu a b y x p := rfl

theorem νC_mul (p q : NF) : νC h p * νC h q = νC h (nfMul p q) :=
  Subtype.ext (nu_mul h p q)

theorem νC_inv (p : NF) : (νC h p)⁻¹ = νC h (nfInv p) := Subtype.ext (nu_inv h p)

theorem νC_zero : νC h (0, 0, 0, 0) = 1 := Subtype.ext nu_zero

theorem νC_inj : Function.Injective (νC h) := fun _ _ e => nu_injective h (congrArg Subtype.val e)

theorem exists_νC {r : ↥(Cz a b)} (hr : (r : G) ∈ S) : ∃ p, r = νC h p := by
  obtain ⟨p, hp⟩ := exists_nf h hr
  exact ⟨p, Subtype.ext hp⟩

theorem mem_sub_iff {P : NF → Prop} (hP : NFClosed P) {r : ↥(Cz a b)} :
    r ∈ (nfSub h P hP).subgroupOf (Cz a b) ↔ ∃ p, P p ∧ r = νC h p := by
  constructor
  · intro hr
    obtain ⟨p, hp, hpr⟩ := hr
    exact ⟨p, hp, Subtype.ext hpr⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem νC_mem_sub {P : NF → Prop} (hP : NFClosed P) (p : NF) :
    νC h p ∈ (nfSub h P hP).subgroupOf (Cz a b) ↔ P p := by
  rw [mem_subgroupOf]
  exact nu_mem_nfSub h hP p

include h in
theorem card_filter_R (P : NF → Prop) (Q : ↥(Cz a b) → Prop)
    (hPQ : ∀ q : NF, pR q → (Q (νC h q) ↔ P q)) :
    Nat.card {r : ↥(Cz a b) // r ∈ (nfSub h pR closed_pR).subgroupOf (Cz a b) ∧ Q r} =
      Nat.card {q : NF // pR q ∧ P q} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : {q : NF // pR q ∧ P q} =>
      (⟨νC h q.1, (νC_mem_sub h closed_pR q.1).2 q.2.1, (hPQ q.1 q.2.1).2 q.2.2⟩ :
        {r : ↥(Cz a b) // r ∈ (nfSub h pR closed_pR).subgroupOf (Cz a b) ∧ Q r})) ⟨?_, ?_⟩)
  · intro q q' e
    exact Subtype.ext (νC_inj h (congrArg Subtype.val e))
  · rintro ⟨r, hr, hQ⟩
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hr
    exact ⟨⟨p, hp, (hPQ p hp).1 hQ⟩, rfl⟩

theorem mem_normalizer_of_conj_mem {C' : Type} [Group C'] {K : Subgroup C'} {g : C'}
    (h1 : ∀ r ∈ K, g * r * g⁻¹ ∈ K) (h2 : ∀ r ∈ K, g⁻¹ * r * g ∈ K) :
    g ∈ Subgroup.normalizer (K : Set C') := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h1 r, fun hr => ?_⟩
  have := h2 _ hr
  simpa [mul_assoc] using this

include h in
theorem norm_of_conj {P : NF → Prop} (hP : NFClosed P)
    (hc : ∀ p q, P q → P (nfMul (nfMul p q) (nfInv p))) {s : ↥(Cz a b)} (hs : (s : G) ∈ S) :
    s ∈ Subgroup.normalizer (((nfSub h P hP).subgroupOf (Cz a b) : Subgroup ↥(Cz a b)) :
      Set ↥(Cz a b)) := by
  have hsi : ((s⁻¹ : ↥(Cz a b)) : G) ∈ S := S.inv_mem hs
  refine mem_normalizer_of_conj_mem (fun r hr => ?_) (fun r hr => ?_)
  · exact conj_mem_nfSub h hP hc (s : G) hs (r : G) hr
  · have := conj_mem_nfSub h hP hc ((s⁻¹ : ↥(Cz a b)) : G) hsi (r : G) hr
    simpa [Subgroup.mem_subgroupOf] using this

include h in
theorem rcfg (hS : Sec13.Sylow2In S ⊤) :
    RCfg (νC h zNF) (S.subgroupOf (Cz a b)) ((nfSub h pR closed_pR).subgroupOf (Cz a b))
      ((nfSub h pR1 closed_pR1).subgroupOf (Cz a b))
      ((nfSub h pR2 closed_pR2).subgroupOf (Cz a b)) := by
  have hSC : S ≤ Cz a b := S_le_Cz h
  have hRC : nfSub h pR closed_pR ≤ Cz a b := (nfSub_le_S h closed_pR).trans hSC
  have hR1C : nfSub h pR1 closed_pR1 ≤ Cz a b := (nfSub_le_S h closed_pR1).trans hSC
  have hR2C : nfSub h pR2 closed_pR2 ≤ Cz a b := (nfSub_le_S h closed_pR2).trans hSC
  have hSyl := sylow2In_centralizer_z h hS
  have hmemR1 := νC_mem_sub h closed_pR1
  have hmemR2 := νC_mem_sub h closed_pR2
  have hmemR := νC_mem_sub h closed_pR
  refine
    { z_central := fun g => ?_
      z_sq := by rw [νC_mul, zNF_sq, νC_zero]
      z_ne := fun e => zNF_ne_zero (νC_inj h (e.trans (νC_zero h).symm))
      sylow := ?_
      card_S := ?_
      R_le := fun r hr => nfSub_le_S h closed_pR hr
      card_R := ?_
      R₁_le := fun r hr => R1_le_R h hr
      R₂_le := fun r hr => nfSub_le_nfSub h closed_pR2 closed_pR pR_of_pR2 hr
      card_R₁ := ?_
      card_R₂ := ?_
      z₁ := (hmemR1 zNF).2 pR1_zNF
      z₂ := (hmemR2 zNF).2 pR2_zNF
      ex₁ := ⟨νC h (r1rep 0), (hmemR1 _).2 (r1rep_mem 0), by rw [νC_mul, r1rep_sq]⟩
      ex₂ := ⟨νC h (r2rep 0), (hmemR2 _).2 (r2rep_mem 0), by rw [νC_mul, r2rep_sq]⟩
      inter := ?_
      comm₁₂ := ?_
      prod := ?_
      sq := ?_
      comm := ?_
      nn := ?_
      sq₁ := ?_
      sq₂ := ?_
      nc₁ := ?_
      nc₂ := ?_
      cent8 := ?_
      norm₁ := fun s hs => norm_of_conj h closed_pR1 conj_pR1 hs
      norm₂ := fun s hs => norm_of_conj h closed_pR2 conj_pR2 hs }
  · apply Subtype.ext
    have hg := mem_centralizer_iff.1 g.2 (a ^ 2 * b ^ 2) (Set.mem_singleton _)
    show (g : G) * nu a b y x zNF = nu a b y x zNF * g
    rw [← zG_eq (y := y) (x := x)]
    exact hg.symm
  · obtain ⟨_, hS2, hSidx⟩ := hSyl
    refine ⟨le_top, ?_, ?_⟩
    · exact hS2.of_surjective (Subgroup.subgroupOfEquivOfLe hSC).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hSC).symm.surjective
    · rw [Subgroup.relIndex_top_right]
      exact hSidx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact h.card
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv]
    exact card_R h
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR1C).toEquiv, card_nfSub h]
    exact card_pR1
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR2C).toEquiv, card_nfSub h]
    exact card_pR2
  · intro r hr1 hr2
    obtain ⟨p, hp1, rfl⟩ := (mem_sub_iff h closed_pR1).1 hr1
    have hp2 := (hmemR2 p).1 hr2
    rcases R1R2_inter p hp1 hp2 with rfl | rfl
    · left; exact νC_zero h
    · right; rfl
  · intro r hr r' hr'
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hr
    obtain ⟨q, hq, rfl⟩ := (mem_sub_iff h closed_pR2).1 hr'
    rw [νC_mul, νC_mul, R1R2_comm p q hp hq]
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hr
    obtain ⟨q, hq, q', hq', e⟩ := R_decomp p hp
    refine ⟨νC h q, (hmemR1 _).2 hq, νC h q', (hmemR2 _).2 hq', ?_⟩
    rw [νC_mul, e]
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hr
    rw [νC_mul]
    rcases pR_sq_cases p hp with e | e
    · left; rw [e, νC_zero]
    · right; rw [e]
  · intro r hr r' hr'
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hr
    obtain ⟨q, hq, rfl⟩ := (mem_sub_iff h closed_pR).1 hr'
    simp only [νC_mul]
    rcases R_comm p q hp hq with e | e
    · left; rw [e]
    · right; rw [e]
  · intro r hr hsq
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hr
    rw [νC_mul] at hsq
    rcases R_sq_z p hp (νC_inj h hsq) with h1 | h2
    · left; exact (hmemR1 p).2 h1
    · right; exact (hmemR2 p).2 h2
  · intro r hr h1 h2
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hr
    rw [νC_mul]
    exact congrArg (νC h) (R1_order4 p hp (fun e => h1 (by rw [e]; exact νC_zero h))
      (fun e => h2 (by rw [e])))
  · intro r hr h1 h2
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR2).1 hr
    rw [νC_mul]
    exact congrArg (νC h) (R2_order4 p hp (fun e => h1 (by rw [e]; exact νC_zero h))
      (fun e => h2 (by rw [e])))
  · intro r hr r' hr' hpp hqq hne1 hne2
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hr
    obtain ⟨q, hq, rfl⟩ := (mem_sub_iff h closed_pR1).1 hr'
    rw [νC_mul] at hpp hqq
    rw [νC_mul, νC_mul]
    intro e
    exact R1_noncomm p q hp hq (νC_inj h hpp) (νC_inj h hqq) (fun e' => hne1 (by rw [e']))
      (fun e' => hne2 (by rw [νC_mul, e'])) (νC_inj h e)
  · intro r hr r' hr' hpp hqq hne1 hne2
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR2).1 hr
    obtain ⟨q, hq, rfl⟩ := (mem_sub_iff h closed_pR2).1 hr'
    rw [νC_mul] at hpp hqq
    rw [νC_mul, νC_mul]
    intro e
    exact R2_noncomm p q hp hq (νC_inj h hpp) (νC_inj h hqq) (fun e' => hne1 (by rw [e']))
      (fun e' => hne2 (by rw [νC_mul, e'])) (νC_inj h e)
  · intro s hs hsR
    obtain ⟨p, rfl⟩ := exists_νC h hs
    have hp : ¬ pR p := fun hp => hsR ((hmemR p).2 hp)
    rw [card_filter_R h (fun q => nfMul q p = nfMul p q ∨ nfMul q p = nfMul (nfMul p q) zNF)
      (fun r => r * νC h p = νC h p * r ∨ r * νC h p = νC h p * r * νC h zNF) (fun q _ => by
        simp only [νC_mul]
        exact or_congr (νC_inj h).eq_iff (νC_inj h).eq_iff),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact cent_card p hp

theorem normal_zpowers_of_central {C' : Type} [Group C'] {z : C'} (hz : ∀ g : C', g * z = z * g) :
    (Subgroup.zpowers z).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := hn
    have h1 : g * z ^ k = z ^ k * g := (Commute.zpow_right (show Commute g z from hz g) k).eq
    have : g * z ^ k * g⁻¹ = z ^ k := by rw [h1]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k⟩

include h in
theorem νC_central (g : ↥(Cz a b)) : g * νC h zNF = νC h zNF * g := by
  apply Subtype.ext
  have hg := mem_centralizer_iff.1 g.2 (a ^ 2 * b ^ 2) (Set.mem_singleton _)
  show (g : G) * nu a b y x zNF = nu a b y x zNF * g
  rw [← zG_eq (y := y) (x := x)]
  exact hg.symm

instance zNormal : (Subgroup.zpowers (νC h zNF)).Normal :=
  normal_zpowers_of_central (νC_central h)

include h in
theorem νC_sq_z : νC h zNF * νC h zNF = 1 := by rw [νC_mul, zNF_sq, νC_zero]

include h in
theorem π_eq_iff (p q : NF) :
    piZ (νC h zNF) (νC h p) = piZ (νC h zNF) (νC h q) ↔ q = p ∨ q = nfMul p zNF := by
  rw [piZ_eq_iff_sq (νC_sq_z h)]
  constructor
  · rintro (e | e)
    · exact Or.inl (νC_inj h e)
    · right; rw [νC_mul] at e; exact νC_inj h e
  · rintro (e | e)
    · left; rw [e]
    · right; rw [e, νC_mul]

include h in
theorem π_eq_one_iff (p : NF) :
    piZ (νC h zNF) (νC h p) = 1 ↔ p = (0, 0, 0, 0) ∨ p = zNF := by
  have := π_eq_iff h (0, 0, 0, 0) p
  rw [νC_zero, map_one] at this
  have e : nfMul (0, 0, 0, 0) zNF = zNF := by decide +kernel
  rw [e] at this
  rw [eq_comm]
  exact this

abbrev Aq (P : NF → Prop) (hP : NFClosed P) :
    Subgroup (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) :=
  ((nfSub h P hP).subgroupOf (Cz a b)).map (piZ (νC h zNF))

section F

variable (hF1 : ∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
    ∃ g ∈ Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G) ∧
      (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2)

include h hF1 in
theorem conj_pt {p : NF} (hpp : nfMul p p = zNF) :
    ∃ g : ↥(Cz a b), ∃ q : NF, (q = r1rep 0 ∨ q = nfMul (r1rep 0) zNF ∨ q = r2rep 0 ∨
      q = nfMul (r2rep 0) zNF) ∧ g * νC h p * g⁻¹ = νC h q := by
  have hc : nu a b y x p ∈ S := nu_mem h p
  have hcc : nu a b y x p * nu a b y x p = a ^ 2 * b ^ 2 := by
    rw [nu_mul h, hpp, zG_eq (y := y) (x := x)]
  obtain ⟨g, hg, hgc, hgcc⟩ := hF1 _ hc hcc
  rw [H0_eq h] at hgc
  obtain ⟨q, hq, hqe⟩ := hgc
  have hqq : nfMul q q = zNF := by
    apply nu_injective h
    rw [← nu_mul h, ← hqe, hgcc, zG_eq (y := y) (x := x)]
  exact ⟨⟨g, hg⟩, q, H0_sq_z q hq hqq, Subtype.ext hqe⟩

include h hF1 in
theorem hconj_A : ∀ v ∈ Aq h pR closed_pR, v ≠ 1 →
    (v ∈ Aq h pR1 closed_pR1 ∨ v ∈ Aq h pR2 closed_pR2) →
    ∃ g : ↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF),
      g * v * g⁻¹ = piZ (νC h zNF) (νC h (r1rep 0)) ∨
        g * v * g⁻¹ = piZ (νC h zNF) (νC h (r2rep 0)) := by
  intro v _ hv1 hv12
  have hz1 : piZ (νC h zNF) (νC h zNF) = 1 := (π_eq_one_iff h zNF).2 (Or.inr rfl)
  have hz0 : piZ (νC h zNF) (νC h (0, 0, 0, 0)) = 1 := by rw [νC_zero, map_one]
  have key : ∃ p : NF, v = piZ (νC h zNF) (νC h p) ∧ nfMul p p = zNF := by
    rcases hv12 with hv | hv
    · obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hv
      obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hc
      exact ⟨p, rfl, R1_order4 p hp (fun e => hv1 (by rw [e]; exact hz0))
        (fun e => hv1 (by rw [e]; exact hz1))⟩
    · obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hv
      obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR2).1 hc
      exact ⟨p, rfl, R2_order4 p hp (fun e => hv1 (by rw [e]; exact hz0))
        (fun e => hv1 (by rw [e]; exact hz1))⟩
  obtain ⟨p, rfl, hpp⟩ := key
  obtain ⟨g, q, hq, hgq⟩ := conj_pt h hF1 hpp
  refine ⟨piZ (νC h zNF) g, ?_⟩
  have hc : piZ (νC h zNF) g * piZ (νC h zNF) (νC h p) * (piZ (νC h zNF) g)⁻¹ =
      piZ (νC h zNF) (νC h q) := by
    rw [← map_inv, ← map_mul, ← map_mul, hgq]
  rw [hc]
  rcases hq with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl ((π_eq_iff h (r1rep 0) _).2 (Or.inr rfl)).symm
  · exact Or.inr rfl
  · exact Or.inr ((π_eq_iff h (r2rep 0) _).2 (Or.inr rfl)).symm

include h in
theorem w1_mem : piZ (νC h zNF) (νC h (r1rep 0)) ∈
    commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) := by
  have e : r1rep 0 = nfComm yNF aNF := by
    have : r1rep 0 = (3, 1, 0, 0) := by decide +kernel
    rw [this, w1_comm]
  have e2 : νC h (nfComm yNF aNF) = ⁅νC h yNF, νC h aNF⁆ := by
    simp only [commutatorElement_def, νC_inv, νC_mul, nfComm]
  rw [e, e2, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

include h in
theorem w2_mem : piZ (νC h zNF) (νC h (r2rep 0)) ∈
    commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) := by
  have e : r2rep 0 = nfMul (nfComm yNF bNF) (nfInv (nfComm xNF bNF)) := by
    have : r2rep 0 = (1, 1, 0, 0) := by decide +kernel
    rw [this, w2_comm]
  have c1 : (⁅νC h yNF, νC h bNF⁆ : ↥(Cz a b)) = νC h (nfComm yNF bNF) := by
    simp only [commutatorElement_def, νC_inv, νC_mul, nfComm]
  have c2 : (⁅νC h xNF, νC h bNF⁆ : ↥(Cz a b)) = νC h (nfComm xNF bNF) := by
    simp only [commutatorElement_def, νC_inv, νC_mul, nfComm]
  have e2 : νC h (r2rep 0) = ⁅νC h yNF, νC h bNF⁆ * (⁅νC h xNF, νC h bNF⁆)⁻¹ := by
    rw [c1, c2, νC_inv, νC_mul, e]
  rw [e2, map_mul, map_inv, map_commutatorElement, map_commutatorElement]
  exact mul_mem (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (inv_mem (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)))

include h hF1 in
theorem A_le_comm : Aq h pR closed_pR ≤ commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro r hrR
  obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR).1 hrR
  rw [Subgroup.mem_comap]
  have hN : (commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF))).Normal := inferInstance
  have hroot : ∀ q : NF, nfMul q q = zNF →
      piZ (νC h zNF) (νC h q) ∈ commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) := by
    intro q hqq
    obtain ⟨g, q', hq', hgq⟩ := conj_pt h hF1 hqq
    have hw : piZ (νC h zNF) (νC h q') ∈
        commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) := by
      rcases hq' with rfl | rfl | rfl | rfl
      · exact w1_mem h
      · rw [← (π_eq_iff h (r1rep 0) _).2 (Or.inr rfl)]; exact w1_mem h
      · exact w2_mem h
      · rw [← (π_eq_iff h (r2rep 0) _).2 (Or.inr rfl)]; exact w2_mem h
    have hc : piZ (νC h zNF) (νC h q) =
        (piZ (νC h zNF) g)⁻¹ * piZ (νC h zNF) (νC h q') * ((piZ (νC h zNF) g)⁻¹)⁻¹ := by
      rw [← hgq]
      simp only [map_mul, map_inv]
      group
    rw [hc]
    exact hN.conj_mem _ hw _
  rcases pR_gen p hp with rfl | hr | ⟨q, hq, r, hr, rfl⟩
  · rw [νC_zero, map_one]; exact one_mem _
  · exact hroot p ((sq_eq_z_iff p).2 hr)
  · rw [← νC_mul, map_mul]
    exact mul_mem (hroot q ((sq_eq_z_iff q).2 hq)) (hroot r ((sq_eq_z_iff r).2 hr))

end F

omit h in
theorem x_eq : nu a b y x xNF = x := by simp [nu, xNF]

include h in
theorem hsing_A (hF2 : ∀ g ∈ Cz a b, g * x * g⁻¹ ∉ Subgroup.closure ({a * a, b * b} : Set G)) :
    ∃ α ∈ Aq h pR closed_pR, ∃ β ∈ Aq h pR closed_pR, α ≠ 1 ∧ α ∉ Aq h pR1 closed_pR1 ∧
      α ∉ Aq h pR2 closed_pR2 ∧ β ≠ 1 ∧ β ∉ Aq h pR1 closed_pR1 ∧ β ∉ Aq h pR2 closed_pR2 ∧
      ∀ n ∈ commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) ⊓
        Subgroup.normalizer ((Aq h pR closed_pR : Subgroup (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF))) :
          Set (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF))),
        n * α * n⁻¹ ≠ β := by
  have hπ1 := π_eq_one_iff h
  refine ⟨piZ (νC h zNF) (νC h xNF), ⟨νC h xNF, (νC_mem_sub h closed_pR _).2 pR_xNF, rfl⟩,
    piZ (νC h zNF) (νC h (2, 0, 0, 0)),
    ⟨νC h (2, 0, 0, 0), (νC_mem_sub h closed_pR _).2 pR_a2, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, hπ1]
    rintro (e | e)
    · exact xNF_ne_zero e
    · exact xNF_ne_zNF e
  · intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hc
    rcases (π_eq_iff h p xNF).1 hce with e | e
    · exact (x_not_R1 p hp).1 e
    · exact (x_not_R1 p hp).2 e
  · intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR2).1 hc
    rcases (π_eq_iff h p xNF).1 hce with e | e
    · exact (x_not_R2 p hp).1 e
    · exact (x_not_R2 p hp).2 e
  · rw [Ne, hπ1]
    rintro (e | e)
    · exact a2_ne_zero e
    · exact a2_ne_zNF e
  · intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR1).1 hc
    rcases (π_eq_iff h p (2, 0, 0, 0)).1 hce with e | e
    · exact (a2_not_R1 p hp).1 e
    · exact (a2_not_R1 p hp).2 e
  · intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨p, hp, rfl⟩ := (mem_sub_iff h closed_pR2).1 hc
    rcases (π_eq_iff h p (2, 0, 0, 0)).1 hce with e | e
    · exact (a2_not_R2 p hp).1 e
    · exact (a2_not_R2 p hp).2 e
  · have hbad : ∀ (g : ↥(Cz a b)) (q : NF), pU q → g * νC h xNF * g⁻¹ = νC h q → False := by
      intro g q hq e
      apply hF2 g.1 g.2
      have h1 : g.1 * x * g.1⁻¹ = nu a b y x q := by
        have := congrArg Subtype.val e
        simpa [νC_val h, x_eq] using this
      rw [h1, U_eq h]
      exact ⟨q, hq, rfl⟩
    rintro n ⟨_, _⟩ he
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ n
    have he' : piZ (νC h zNF) (g * νC h xNF * g⁻¹) = piZ (νC h zNF) (νC h (2, 0, 0, 0)) := by
      rw [map_mul, map_mul, map_inv]; exact he
    rcases (piZ_eq_iff_sq (νC_sq_z h)).1 he' with e | e
    · exact hbad g (2, 0, 0, 0) pU_two_zero e.symm
    · apply hbad g (0, 2, 0, 0) pU_zero_two
      have e1 : g * νC h xNF * g⁻¹ = νC h (2, 0, 0, 0) * νC h zNF := by
        calc g * νC h xNF * g⁻¹ = g * νC h xNF * g⁻¹ * νC h zNF * νC h zNF := by
              rw [mul_assoc _ (νC h zNF) (νC h zNF), νC_sq_z h, mul_one]
          _ = νC h (2, 0, 0, 0) * νC h zNF := by rw [← e]
      rw [e1, νC_mul, a2_mul_z]

variable [Finite G]

theorem oddCore_eq_pPrimeCore_two' (X : Type*) [Group X] : CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  simp only [CFSG.oddCore, CFSG.pPrimeCore, Nat.coprime_two_left]

include h in
theorem Cz_ne_top (hK : IsKProperSimple G) : Cz a b ≠ ⊤ := by
  obtain ⟨hs, hn, -⟩ := isKProperSimple_iff.1 hK
  intro htop
  have hz : (a ^ 2 * b ^ 2 : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Cz a b := htop ▸ Subgroup.mem_top g
    exact (mem_centralizer_iff.1 this (a ^ 2 * b ^ 2) (Set.mem_singleton _)).symm
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact z_ne_one h (by simpa [hb] using hz)
  · obtain ⟨u, v, huv⟩ := hn
    have : u ∈ Subgroup.center G := ht ▸ Subgroup.mem_top u
    exact huv ((Subgroup.mem_center_iff.1 this v).symm)

include h in
theorem normal_of_m12 (h91 : IVK_9_1) (hKC : IsKGroupNative ↥(Cz a b)) (hS : Sec13.Sylow2In S ⊤)
    (hO : CFSG.oddCore ↥(Cz a b) = ⊥)
    (hF1 : ∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
      ∃ g ∈ Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ Subgroup.closure ({a, b} : Set G) ∧
        (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2)
    (hF2 : ∀ g ∈ Cz a b, g * x * g⁻¹ ∉ Subgroup.closure ({a * a, b * b} : Set G)) :
    ((nfSub h pR closed_pR).subgroupOf (Cz a b)).Normal := by
  classical
  have c := rcfg h hS
  have hctx := c.ctx16
  have hKY : IsKGroupNative (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF)) :=
    SectionRank.IsKGroupCat.quotient hKC _
  have hodd0 : CFSG.pPrimeCore 2 ↥(Cz a b) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two']; exact hO
  have hoddY := pPrimeCore_quot_eq_bot c.z_sq c.z_ne c.z_central hodd0
  have hodd := pPrimeCoreOf_normal_eq_bot
    (N := commutator (↥(Cz a b) ⧸ Subgroup.zpowers (νC h zNF))) hoddY
  have hw₁ : piZ (νC h zNF) (νC h (r1rep 0)) ∈ Aq h pR1 closed_pR1 :=
    ⟨νC h (r1rep 0), (νC_mem_sub h closed_pR1 _).2 (r1rep_mem 0), rfl⟩
  have hw₂ : piZ (νC h zNF) (νC h (r2rep 0)) ∈ Aq h pR2 closed_pR2 :=
    ⟨νC h (r2rep 0), (νC_mem_sub h closed_pR2 _).2 (r2rep_mem 0), rfl⟩
  have hw₁1 : piZ (νC h zNF) (νC h (r1rep 0)) ≠ 1 := by
    rw [Ne, π_eq_one_iff h]; decide +kernel
  have hw₂1 : piZ (νC h zNF) (νC h (r2rep 0)) ≠ 1 := by
    rw [Ne, π_eq_one_iff h]; decide +kernel
  have hA := normal_of_ctx h91 Sec12.ig_15_15 Sec12.ig_16_2 hKY hodd hctx (A_le_comm h hF1)
    hw₁ hw₂ hw₁1 hw₂1 (hconj_A h hF1) (hsing_A h hF2)
  have hRz : Subgroup.zpowers (νC h zNF) ≤ (nfSub h pR closed_pR).subgroupOf (Cz a b) :=
    Subgroup.zpowers_le.2 (c.R₁_le c.z₁)
  have := hA.comap (piZ (νC h zNF))
  rwa [comap_map_piZ hRz] at this

end M12

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
