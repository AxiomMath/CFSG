module

public import CFSG.Certificates.Kernel.DELKHKSound
public import CFSG.LocalAnalysis.StandardType.GGDepELLowCheck2
public import Certificates.Data.Kernel.DELKWF
import CFSG.Certificates.Kernel.TWLK6Sound

public section

namespace CFSG.StandardType.DELK

open CFSG.StandardType Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
  Certificates.TwoDepSmallLow Certificates.DELK
open Certificates.TWLK (kAll2)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem dk_isRefl_of_valid {q : GGDepANPair} (hq : GGDepELNValid q) :
    GGDepELIsRefl (ggDepELNRflOf q) :=
  ⟨ggDepELToZ q.1, ggDepELToZ q.2, ggDepELNValid_dot hq, rfl⟩

theorem dk_refl_mul_self_of_isRefl (r : Module.End (ZMod 3) (GGDepAE 3 6))
    (hr : GGDepELIsRefl r) : r * r = 1 := by
  rcases hr with ⟨c, f, h, rfl⟩
  exact l05nL6_refl_invol c f h

private lemma dkPB_fix_refl {q : GGDepANPair} {z : List ℕ} (hq : GGDepELNValid q)
    (hz : z.length = 6) (h : ggDepANDot 3 q.2 z = 0) :
    ggDepELNRflOf q (ggDepELToZ z) = ggDepELToZ z := by
  have hdot : ggDepAdot (ggDepELToZ q.2) (ggDepELToZ z) = 0 := by
    have hcast := ggDepELDot_cast (a := q.2) (b := z) hq.2.1 hz
    rw [h] at hcast
    exact hcast.symm
  change ggDepARefl (ggDepELToZ q.1) (ggDepELToZ q.2) (ggDepELToZ z) = ggDepELToZ z
  rw [l05nNC_refl_apply, hdot, zero_smul, sub_zero]

private lemma dkPB_conj_fold (C : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6)))
    (q : GGDepANPair) (hq : GGDepELNValid q) :
    ∀ fixes : List GGDepANPair,
      (∀ g ∈ fixes, GGDepELNValid g) →
      (∀ g ∈ fixes, ggDepELNRflOf g ∈ C) →
      ∃ G ∈ C, ∃ G' ∈ C, G * G' = 1 ∧
        GGDepELNValid (fixes.foldr (fun g acc => ggDepANConj 3 acc g) q) ∧
        ggDepELNRflOf (fixes.foldr (fun g acc => ggDepANConj 3 acc g) q) =
          G * ggDepELNRflOf q * G' := by
  intro fixes
  induction fixes with
  | nil =>
      intro _ _
      exact ⟨1, C.one_mem, 1, C.one_mem, by simp, by simpa using hq, by simp⟩
  | cons g gs ih =>
      intro hfixv hfixmem
      have hgv : GGDepELNValid g := hfixv g (by simp)
      have hgsv : ∀ g' ∈ gs, GGDepELNValid g' := fun g' hg' => hfixv g' (by simp [hg'])
      have hgmem : ggDepELNRflOf g ∈ C := hfixmem g (by simp)
      have hgsmem : ∀ g' ∈ gs, ggDepELNRflOf g' ∈ C := fun g' hg' => hfixmem g' (by simp [hg'])
      obtain ⟨G, hG, G', hG', hGG', hvrest, hEq⟩ := ih hgsv hgsmem
      refine ⟨ggDepELNRflOf g * G, Submonoid.mul_mem _ hgmem hG,
        G' * ggDepELNRflOf g, Submonoid.mul_mem _ hG' hgmem, ?_, ?_, ?_⟩
      · calc (ggDepELNRflOf g * G) * (G' * ggDepELNRflOf g)
            = ggDepELNRflOf g * (G * G') * ggDepELNRflOf g := by simp only [mul_assoc]
          _ = ggDepELNRflOf g * 1 * ggDepELNRflOf g := by rw [hGG']
          _ = ggDepELNRflOf g * ggDepELNRflOf g := by rw [mul_one]
          _ = 1 := dk_refl_mul_self_of_isRefl _ (dk_isRefl_of_valid hgv)
      · rw [List.foldr_cons]
        exact (ggDepELNConj_rfl hvrest hgv).1
      · rw [List.foldr_cons, (ggDepELNConj_rfl hvrest hgv).2, hEq]
        simp only [mul_assoc]

private lemma dkPB_word_cons (news : List GGDepANPair) (q : GGDepANPair) (g : ℕ)
    (w : List ℕ) :
    ggDepELNWord news q (g :: w) =
      ggDepANConj 3 (ggDepELNWord news q w) (ggDepELNGen news g) := by
  simp [ggDepELNWord]

private lemma dkPB_word_J {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (S : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6)))
    (w : List ℕ) (hw : ∀ g ∈ w, g < 6 + news.length)
    (hmem : ∀ g ∈ w, ggDepELNRflOf (ggDepELNGen news g) ∈ S)
    (q : GGDepANPair) (hq : GGDepELNValid q) (hqm : ggDepELNRflOf q ∈ S) :
    GGDepELNValid (ggDepELNWord news q w) ∧ ggDepELNRflOf (ggDepELNWord news q w) ∈ S := by
  induction w generalizing q with
  | nil => simpa [ggDepELNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      rw [dkPB_word_cons]
      have hg : g < 6 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < 6 + news.length := fun g' hg' => hw g' (by simp [hg'])
      have hmem' : ∀ g' ∈ w, ggDepELNRflOf (ggDepELNGen news g') ∈ S :=
        fun g' hg' => hmem g' (by simp [hg'])
      obtain ⟨ihV, ihM⟩ := ih hw' hmem' q hq hqm
      have hG : GGDepELNValid (ggDepELNGen news g) := ggDepELNGen_valid hnews hg
      refine ⟨(ggDepELNConj_rfl ihV hG).1, ?_⟩
      rw [(ggDepELNConj_rfl ihV hG).2]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g (by simp)) ihM) (hmem g (by simp))

theorem dk_orbit_involution (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (z : GGDepAE 3 6) : ∀ t ∈ ggDepELPZOrbit gens z, t * t = 1 := by
  intro t ht
  rcases ht with ⟨r, hrJ, g, hg, g', hg', hgg', rfl⟩
  have hrr : r * r = 1 := dk_refl_mul_self_of_isRefl r hrJ.2
  have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
  calc (g * r * g') * (g * r * g') = g * (r * (g' * g) * r) * g' := by simp only [mul_assoc]
    _ = g * (r * 1 * r) * g' := by rw [hg'g]
    _ = g * (r * r) * g' := by rw [mul_one]
    _ = g * 1 * g' := by rw [hrr]
    _ = 1 := by rw [mul_one, hgg']

instance dk_end_finite : Finite (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  Finite.of_injective (fun f : Module.End (ZMod 3) (GGDepAE 3 6) => (f : GGDepAE 3 6 → GGDepAE 3 6))
    LinearMap.coe_injective

private theorem dk_submonoid_inv_mem {P : Type*} [Group P] [Finite P] (T : Submonoid P)
    {g : P} (hg : g ∈ T) : g⁻¹ ∈ T := by
  have h1 : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  have h2 : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left h1).symm
  rw [h2]
  exact T.pow_mem hg _

private lemma dk_card_subgroup {M : Type*} [Monoid M] {S : Set M}
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1)
    (H : Subgroup Mˣ)
    (hH : ∀ u : Mˣ, u ∈ H ↔ (u : M) ∈ Submonoid.closure S) :
    Nat.card ↥H = Nat.card ↥(Submonoid.closure S) := by
  apply Nat.card_eq_of_bijective
    (fun u : ↥H => (⟨(u.1 : M), (hH u.1).mp u.2⟩ : ↥(Submonoid.closure S)))
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    simpa using congrArg Subtype.val hab
  · intro g
    obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv (g : M) g.2
    refine ⟨⟨(⟨(g : M), g', hg'1, hg'2⟩ : Mˣ), ?_⟩, ?_⟩
    · exact (hH _).mpr g.2
    · apply Subtype.ext
      rfl

private lemma dk_sub_inv {S S' : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (hS : ∀ s ∈ S, s * s = 1) (hsub : S' ⊆ Submonoid.closure S) :
    ∀ g ∈ Submonoid.closure S', ∃ g' ∈ Submonoid.closure S', g * g' = 1 ∧ g' * g = 1 := by
  let M := Module.End (ZMod 3) (GGDepAE 3 6)
  have hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1 :=
    l05nDA_inv_mem (T := S) (fun t ht =>
      ⟨t, Submonoid.subset_closure ht, hS t ht, hS t ht⟩)
  intro g hg'
  have hg : g ∈ Submonoid.closure S := Submonoid.closure_le.mpr hsub hg'
  obtain ⟨g', hg'mem, hgg', hg'g⟩ := hinv g hg
  let P : Submonoid Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S'}
      one_mem' := by
        change ((1 : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        change ((u * v : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv }
  let u : Mˣ := ⟨g, g', hgg', hg'g⟩
  have hu : u ∈ P := by
    change (u : M) ∈ Submonoid.closure S'
    exact hg'
  have huinv : ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S' :=
    dk_submonoid_inv_mem P hu
  have hval : ((u⁻¹ : Mˣ) : M) = g' := rfl
  exact ⟨g', hval ▸ huinv, hgg', hg'g⟩

noncomputable def kT (Q : List GGDepANPair) : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  {g | ∃ q ∈ Q, g = ggTWLMatLin 3 6 (ggTWLMatOfPair 3 6 q)}

def KFacts (T : Set (Module.End (ZMod 3) (GGDepAE 3 6))) : Prop :=
  ∃ (K : ℕ) (hasCen : Bool), K ∣ Nat.card ↥(Submonoid.closure T) ∧
    ggTWLPZArith 7 K hasCen = true ∧
    (hasCen = true → ∃ a ∈ Submonoid.closure T, a ≠ 1 ∧ ∀ t ∈ T, a * t = t * a)

theorem delk_pz_bad (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6))) (z : GGDepAE 3 6)
    (T : Set (Module.End (ZMod 3) (GGDepAE 3 6))) (hT : T ⊆ ggDepELPZOrbit gens z)
    (hF : KFacts T) : GGDepELPZBad gens z := by
  obtain ⟨K, hasCen, hKT, harith, hcen⟩ := hF
  set O := ggDepELPZOrbit gens z with hO
  have hOi := dk_orbit_involution gens z
  have hTO : T ⊆ Submonoid.closure O := fun t ht => Submonoid.subset_closure (hT ht)
  have hTdvd : Nat.card ↥(Submonoid.closure T) ∣ Nat.card ↥(Submonoid.closure O) :=
    ggDepEL_card_dvd hOi hTO
  intro r n c ht hlo hhi ⟨hdvd, himp⟩
  obtain ⟨rfl, rfl, hc⟩ := ggTWLPZArith_sound harith ht hlo hhi ((hKT.trans hTdvd).trans hdvd)
  have hOK := Nat.dvd_antisymm hdvd (hKT.trans hTdvd)
  have hcen1 := himp hOK
  obtain ⟨a, ha, hne, hcomm⟩ := hcen hc
  have hTK : Nat.card ↥(Submonoid.closure T) = Nat.card ↥(Submonoid.closure O) :=
    Nat.dvd_antisymm hTdvd (by rw [hOK]; exact hKT)
  have heq : ((Submonoid.closure T : Submonoid _) : Set (Module.End (ZMod 3) (GGDepAE 3 6))) =
      Submonoid.closure O := by
    apply Set.eq_of_subset_of_ncard_le (Submonoid.closure_le.mpr hTO)
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hTK.ge
  have hcommT : ∀ g ∈ Submonoid.closure T, a * g = g * a := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem x hx => exact hcomm x hx
    | one => rw [mul_one, one_mul]
    | mul x y _ _ ihx ihy => rw [← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]
  have haO : a ∈ Submonoid.closure O := by
    have : a ∈ ((Submonoid.closure T : Submonoid _) :
        Set (Module.End (ZMod 3) (GGDepAE 3 6))) := ha
    rwa [heq] at this
  unfold ggDepELCentreCard at hcen1
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hcen1
  let x : {g : ↥(Submonoid.closure O) // ∀ h : ↥(Submonoid.closure O), g * h = h * g} :=
    ⟨⟨a, haO⟩, fun h => by
      have hT' : (h : Module.End (ZMod 3) (GGDepAE 3 6)) ∈
          ((Submonoid.closure T : Submonoid _) : Set (Module.End (ZMod 3) (GGDepAE 3 6))) := by
        rw [heq]; exact h.2
      exact Subtype.ext (hcommT h.1 hT')⟩
  let y : {g : ↥(Submonoid.closure O) // ∀ h : ↥(Submonoid.closure O), g * h = h * g} :=
    ⟨1, fun h => by rw [one_mul, mul_one]⟩
  exact hne (congrArg (fun u => (u.1 : Module.End (ZMod 3) (GGDepAE 3 6))) (hsub.elim x y))

theorem kAll2_mem_right {α β : Type} (t : α → β → Bool) :
    ∀ (cs : List α) (is : List β), kAll2 t cs is = true → ∀ i ∈ is, ∃ c ∈ cs, t c i = true
  | [], [], _, i, hi => by simp at hi
  | [], _ :: _, h, _, _ => by simp [kAll2] at h
  | _ :: _, [], h, _, _ => by simp [kAll2] at h
  | c :: cs, j :: is, h, i, hi => by
      simp only [kAll2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨c, List.mem_cons_self .., h.1⟩
      · obtain ⟨c', hc', ht⟩ := kAll2_mem_right t cs is h.2 i hi
        exact ⟨c', List.mem_cons_of_mem _ hc', ht⟩

theorem kAll2_mem_left {α β : Type} (t : α → β → Bool) :
    ∀ (cs : List α) (is : List β), kAll2 t cs is = true → ∀ c ∈ cs, ∃ i ∈ is, t c i = true
  | [], _, _, c, hc => by simp at hc
  | _ :: _, [], h, _, _ => by simp [kAll2] at h
  | c :: cs, j :: is, h, c', hc' => by
      simp only [kAll2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨j, List.mem_cons_self .., h.1⟩
      · obtain ⟨i, hi, ht⟩ := kAll2_mem_left t cs is h.2 c' hc'
        exact ⟨i, List.mem_cons_of_mem _ hi, ht⟩

theorem dk_length_of_veceq {a b : List ℕ} (h : ggTWLVecEq 3 a b = true) :
    a.length = b.length := by
  rw [ggTWLVecEq, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp h.1

theorem dk_matOfPair {q : GGDepANPair} (hq : GGDepELNValid q) :
    ggTWLMatWF 6 (ggTWLMatOfPair 3 6 q) ∧
      ggTWLMatLin 3 6 (ggTWLMatOfPair 3 6 q) = ggDepELNRflOf q :=
  ggTWLMatOfPair_lin (p := 3) (N := 7) hq

theorem kPZRef_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (y : List ℕ) (hy : y.length = 6) (Ps : List (List GGDepANPair)) (e : KPZ)
    (h : kPZRef Ps news y e = true) :
    (e.1.1 : ZMod 3) ≠ 0 ∧ e.2 < Ps.length ∧
      ∀ q' ∈ Ps.getD e.2 [], ∃ q, GGDepELNValid q ∧
        ggDepELNRflOf q ∈ ggDepELPZOrbit (ggDepELGens (ggDepELNNews news))
          (ggDepELx + (e.1.1 : ZMod 3) • ggDepELToZ y) ∧
        ggTWLVecEq 3 q.1 q'.1 = true ∧ ggTWLVecEq 3 q.2 q'.2 = true := by
  obtain ⟨⟨c0, fixs, orbs⟩, gi⟩ := e
  simp only [kPZRef, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  set fixP : List GGDepANPair :=
    fixs.map (fun e => ggDepELNWord news (ggDepELNGen news e.1) e.2) with hfixP
  set orbP : List GGDepANPair := orbs.map (fun e =>
      e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], [])))
        (ggDepELNWord news (ggDepELNGen news e.1) e.2.1)) with horbP
  set A : Set (Module.End (ZMod 3) (GGDepAE 3 6)) := ggDepELGens (ggDepELNNews news) with hA
  set zvec : GGDepAE 3 6 := ggDepELx + (c0 : ZMod 3) • ggDepELToZ y with hzvec
  obtain ⟨⟨⟨⟨⟨⟨hc0, hc0p⟩, hfixs⟩, horbs⟩, hfixdot⟩, hlt⟩, hpairs⟩ := h
  have hztest : ggDepELToZ (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 c0 y)) = zvec := by
    rw [hzvec, ggDepELToZ_add ggDepELNX_length (ggDepELSmul_length c0 hy), ggDepELNX_toZ,
      ggDepELToZ_smul hy c0]
  refine ⟨?_, hlt, ?_⟩
  · intro hz
    have hdvd : 3 ∣ c0 := (ZMod.natCast_eq_zero_iff c0 3).mp hz
    have hle : 3 ≤ c0 := Nat.le_of_dvd hc0 hdvd
    omega
  have hfix_all : ∀ s ∈ fixP, GGDepELNValid s ∧
      ggDepELNRflOf s ∈ ggDepELPZFixRefl A zvec := by
    intro s hs
    have hdotmod : ggDepANDot 3 s.2 (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 c0 y)) = 0 :=
      beq_iff_eq.mp (hfixdot s hs)
    rw [hfixP] at hs
    rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := hfixs e he
    have hvg : GGDepELNValid (ggDepELNGen news e.1) := ggDepELNGen_valid hnews he1
    have hmg : ggDepELNRflOf (ggDepELNGen news e.1) ∈ Submonoid.closure A :=
      ggDepELNGen_mem he1
    obtain ⟨hv, hm⟩ := ggDepELNWord_valid_mem hnews hvg hmg he2
    have hzl : (ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 c0 y)).length = 6 :=
      ggDepELAdd_length ggDepELNX_length (ggDepELSmul_length c0 hy)
    have hfixz : ggDepELNRflOf (ggDepELNWord news (ggDepELNGen news e.1) e.2) zvec = zvec := by
      rw [← hztest]
      exact dkPB_fix_refl hv hzl hdotmod
    exact ⟨hv, hm, dk_isRefl_of_valid hv, hfixz⟩
  have horbit : ∀ q ∈ orbP, GGDepELNValid q ∧
      ggDepELNRflOf q ∈ ggDepELPZOrbit A zvec := by
    intro q hq
    rw [horbP] at hq
    rcases List.mem_map.mp hq with ⟨e, he, rfl⟩
    obtain ⟨⟨heJ, heJw⟩, hefix⟩ := horbs e he
    have he1lt : e.1 < 6 := ggDepELNInJ_lt heJ
    let qin : GGDepANPair := ggDepELNWord news (ggDepELNGen news e.1) e.2.1
    have hJmem : ggDepELNRflOf (ggDepELNGen news e.1) ∈
        Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
          Set.univ) := by
      have hgen : ggDepELNGen news e.1 = (ggDepELNH e.1, ggDepELNA e.1) := by
        rw [ggDepELNGen, if_pos he1lt]
      rw [hgen]
      refine Submonoid.subset_closure ⟨⟨⟨e.1, he1lt⟩, (ggDepELNInJ_iff ⟨e.1, he1lt⟩).mp heJ⟩,
        Set.mem_univ _, ?_⟩
      change ggDepELrefl ⟨e.1, he1lt⟩ =
        ggDepARefl (ggDepELToZ (ggDepELNH e.1)) (ggDepELToZ (ggDepELNA e.1))
      rw [ggDepELNH_toZ ⟨e.1, he1lt⟩, ggDepELNA_toZ ⟨e.1, he1lt⟩]
      rfl
    have hmemJ : ∀ g ∈ e.2.1, ggDepELNRflOf (ggDepELNGen news g) ∈
        Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
          Set.univ) := by
      intro g hg
      have hgJ : ggDepELNInJ g = true := heJw g hg
      have hglt : g < 6 := ggDepELNInJ_lt hgJ
      have hgen : ggDepELNGen news g = (ggDepELNH g, ggDepELNA g) := by
        rw [ggDepELNGen, if_pos hglt]
      rw [hgen]
      refine Submonoid.subset_closure ⟨⟨⟨g, hglt⟩, (ggDepELNInJ_iff ⟨g, hglt⟩).mp hgJ⟩,
        Set.mem_univ _, ?_⟩
      change ggDepELrefl ⟨g, hglt⟩ =
        ggDepARefl (ggDepELToZ (ggDepELNH g)) (ggDepELToZ (ggDepELNA g))
      rw [ggDepELNH_toZ ⟨g, hglt⟩, ggDepELNA_toZ ⟨g, hglt⟩]
      rfl
    have hwlt : ∀ g ∈ e.2.1, g < 6 + news.length := by
      intro g hg
      have := ggDepELNInJ_lt (heJw g hg)
      omega
    obtain ⟨hqinV, hqinM⟩ := dkPB_word_J hnews
      (Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
        Set.univ)) e.2.1 hwlt hmemJ (ggDepELNGen news e.1)
      (ggDepELNGen_valid hnews (by omega)) hJmem
    have hqinJ : ggDepELNRflOf qin ∈ ggDepELPZJRefl := by
      rw [ggDepELPZJRefl]
      exact ⟨hqinM, dk_isRefl_of_valid hqinV⟩
    set fixes : List GGDepANPair := e.2.2.map (fun k => fixP.getD k ([], [])) with hfixes
    have hgetmem : ∀ k ∈ e.2.2, fixP.getD k ([], []) ∈ fixP := by
      intro k hk
      have hklt : k < fixP.length := hefix k hk
      rw [List.getD_eq_getElem (l := fixP) (d := ([], [])) (n := k) hklt]
      exact List.getElem_mem hklt
    have hfixe_v : ∀ g ∈ fixes, GGDepELNValid g := by
      intro g hg
      rw [hfixes] at hg
      rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
      exact (hfix_all _ (hgetmem k hk)).1
    have hfixe_m : ∀ g ∈ fixes,
        ggDepELNRflOf g ∈ Submonoid.closure (ggDepELPZFixRefl A zvec) := by
      intro g hg
      rw [hfixes] at hg
      rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
      exact Submonoid.subset_closure (hfix_all _ (hgetmem k hk)).2
    obtain ⟨G, hG, G', hG', hGG', hvfold, hfold⟩ :=
      dkPB_conj_fold (Submonoid.closure (ggDepELPZFixRefl A zvec)) qin hqinV
        fixes hfixe_v hfixe_m
    have hfoldmap : fixes.foldr (fun g acc => ggDepANConj 3 acc g) qin =
        e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], []))) qin :=
      List.foldr_map
    rw [hfoldmap] at hvfold hfold
    exact ⟨hvfold, ⟨ggDepELNRflOf qin, hqinJ, G, hG, G', hG', hGG', hfold⟩⟩
  intro q' hq'
  obtain ⟨q, hq, hqq⟩ := kAll2_mem_right _ orbP _ hpairs q' hq'
  rw [Bool.and_eq_true] at hqq
  exact ⟨q, (horbit q hq).1, (horbit q hq).2, hqq.1, hqq.2⟩

theorem kT_sub_orbit {Q : List GGDepANPair} (hQ : ∀ q ∈ Q, GGDepELNValid q)
    {O : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (h : ∀ q' ∈ Q, ∃ q, GGDepELNValid q ∧ ggDepELNRflOf q ∈ O ∧
      ggTWLVecEq 3 q.1 q'.1 = true ∧ ggTWLVecEq 3 q.2 q'.2 = true) : kT Q ⊆ O := by
  rintro g ⟨q', hq', rfl⟩
  obtain ⟨q, -, hqO, h1, h2⟩ := h q' hq'
  rw [(dk_matOfPair (hQ q' hq')).2]
  change ggDepARefl (ggDepELToZ q'.1) (ggDepELToZ q'.2) ∈ O
  rw [← dk_toZ_of_veceq h1, ← dk_toZ_of_veceq h2]
  exact hqO

noncomputable def kLinSet (G : List (List (List ℕ))) : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  {f | ∃ g ∈ G, f = ggTWLMatLin 3 6 g}

theorem kAll2_get {α β : Type} (t : α → β → Bool) :
    ∀ (cs : List α) (is : List β), kAll2 t cs is = true →
      cs.length = is.length ∧ ∀ k (h1 : k < cs.length) (h2 : k < is.length), t cs[k] is[k] = true
  | [], [], _ => ⟨rfl, fun k h1 => absurd h1 (Nat.not_lt_zero k)⟩
  | [], _ :: _, h => by simp [kAll2] at h
  | _ :: _, [], h => by simp [kAll2] at h
  | c :: cs, i :: is, h => by
    simp only [kAll2, Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := kAll2_get t cs is h.2
    refine ⟨by simp [hl], fun k h1 h2 => ?_⟩
    cases k with
    | zero => exact h.1
    | succ k => exact hk k (by simpa using h1) (by simpa using h2)

theorem dk_lin_single (A : List (List ℕ)) (k : Fin 6) :
    ggTWLMatLin 3 6 A (Pi.single k 1) = ggDepELToZ (A.getD k.val []) := by
  unfold ggTWLMatLin
  rw [LinearMap.sum_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem dk_apply_lin {g : List (List ℕ)} (hg : ggTWLMatWF 6 g) {v : List ℕ} (hv : v.length = 6) :
    (ggTWLMatApply 3 6 g v).length = 6 ∧
      ggDepELToZ (ggTWLMatApply 3 6 g v) = ggTWLMatLin 3 6 g (ggDepELToZ v) := by
  have hB : ggTWLMatWF 6 (List.replicate 6 v) :=
    ⟨List.length_replicate, fun c hc => by rw [List.eq_of_mem_replicate hc]; exact hv⟩
  obtain ⟨hW, hL⟩ := ggTWLMatMul_lin (p := 3) hg hB
  have hcol : (ggTWLMatMul 3 6 g (List.replicate 6 v)).getD 0 [] = ggTWLMatApply 3 6 g v := by
    simp [ggTWLMatMul]
  refine ⟨hW.2 _ (by simp [ggTWLMatMul]), ?_⟩
  have h1 := congrArg (fun f => f (Pi.single (0 : Fin 6) 1)) hL
  have h0 : ((0 : Fin 6) : ℕ) = 0 := rfl
  simp only [Module.End.mul_apply] at h1
  rw [dk_lin_single, dk_lin_single, h0, hcol] at h1
  rw [h1]
  simp

def kOrbPt (G : List (List (List ℕ))) (B t : List (List ℕ)) : Prop :=
  t.length = B.length ∧ (∀ v ∈ t, v.length = 6) ∧ ∃ m ∈ Submonoid.closure (kLinSet G),
    ∀ k : Fin B.length, ggDepELToZ (t.getD k.val []) = m (ggDepELToZ (B.get k))

theorem kOrbPt_apply {G : List (List (List ℕ))} (hG : ∀ g ∈ G, ggTWLMatWF 6 g)
    {B t : List (List ℕ)} (ht : kOrbPt G B t) {g : List (List ℕ)} (hg : g ∈ G) :
    kOrbPt G B (kTupApply g t) := by
  obtain ⟨hl, hv, m, hm, hk⟩ := ht
  refine ⟨by simp [kTupApply, hl], ?_, ggTWLMatLin 3 6 g * m,
    Submonoid.mul_mem _ (Submonoid.subset_closure ⟨g, hg, rfl⟩) hm, fun k => ?_⟩
  · intro v hv'
    simp only [kTupApply, List.mem_map] at hv'
    obtain ⟨w, hw, rfl⟩ := hv'
    exact (dk_apply_lin (hG g hg) (hv w hw)).1
  · have hkt : k.val < t.length := by
      rw [hl]
      exact k.isLt
    have e : (kTupApply g t).getD k.val [] = ggTWLMatApply 3 6 g (t.getD k.val []) := by
      rw [kTupApply, List.getD_eq_getElem _ _ (by simpa using hkt), List.getElem_map,
        List.getD_eq_getElem _ _ hkt]
    have hvk : (t.getD k.val []).length = 6 := by
      rw [List.getD_eq_getElem _ _ hkt]
      exact hv _ (List.getElem_mem hkt)
    rw [e, (dk_apply_lin (hG g hg) hvk).2, hk k, Module.End.mul_apply]

theorem kOrbReplay_facts {G : List (List (List ℕ))} (hG : ∀ g ∈ G, ggTWLMatWF 6 g)
    (B : List (List ℕ)) : ∀ (l : List (ℕ × ℕ)) (V0 : List (List (List ℕ))),
      (∀ t ∈ V0, kOrbPt G B t) →
      (∀ k < l.length, (l.getD k (0, 0)).1 < V0.length + k ∧ (l.getD k (0, 0)).2 < G.length) →
      (∀ t ∈ l.foldl (fun V e => V ++ [kTupApply (G.getD e.2 []) (V.getD e.1 [])]) V0,
        kOrbPt G B t) ∧
      (l.foldl (fun V e => V ++ [kTupApply (G.getD e.2 []) (V.getD e.1 [])]) V0).length =
        V0.length + l.length
  | [], V0, h0, _ => ⟨h0, by simp⟩
  | e :: l, V0, h0, hl => by
    rw [List.foldl_cons]
    have he := hl 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at he
    have ht : V0.getD e.1 [] ∈ V0 := by
      rw [List.getD_eq_getElem _ _ he.1]
      exact List.getElem_mem _
    have hg : G.getD e.2 [] ∈ G := by
      rw [List.getD_eq_getElem _ _ he.2]
      exact List.getElem_mem _
    have hnew := kOrbPt_apply hG (h0 _ ht) hg
    obtain ⟨ih1, ih2⟩ := kOrbReplay_facts hG B l _
      (by
        intro t ht'
        rcases List.mem_append.mp ht' with h | h
        · exact h0 t h
        · rw [List.mem_singleton.mp h]
          exact hnew)
      (by
        intro k hk
        obtain ⟨h1, h2⟩ := hl (k + 1) (by simp; omega)
        simp only [List.getD_cons_succ] at h1 h2
        simp only [List.length_append, List.length_singleton]
        exact ⟨by omega, h2⟩)
    refine ⟨ih1, ?_⟩
    rw [ih2]
    simp
    omega

theorem prefix_foldl_append {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (V0 : List α), V0 <+: l.foldl (fun V e => V ++ [f V e]) V0
  | [], V0 => List.prefix_refl V0
  | e :: l, V0 => (List.prefix_append V0 [f V0 e]).trans (prefix_foldl_append f l _)

def kMdl (B t : List (List ℕ)) : Fin B.length → GGDepAE 3 6 := fun i => ggDepELToZ (t.getD i.val [])

theorem kOrbOK_facts {G : List (List (List ℕ))} (hG : ∀ g ∈ G, ggTWLMatWF 6 g)
    {B : List (List ℕ)} {par : List (ℕ × ℕ)} {cl : List (List ℕ)} {ord : List ℕ}
    (h : kOrbOK G B par cl ord = true) :
    ∃ L : List (Fin B.length → GGDepAE 3 6), L.Nodup ∧ L.length = par.length + 1 ∧
      (fun i => ggDepELToZ (B.get i)) ∈ L ∧
      (∀ v ∈ L, ∀ g ∈ G, (fun i => ggTWLMatLin 3 6 g (v i)) ∈ L) ∧
      (∀ v ∈ L, ∃ m ∈ Submonoid.closure (kLinSet G),
        v = fun i => m (ggDepELToZ (B.get i))) := by
  simp only [kOrbOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hBl, hpar⟩, hcl⟩, hordl⟩, hordr⟩, hinc⟩ := h
  set V := kOrbReplay G B par with hV
  have hbase : kOrbPt G B B :=
    ⟨rfl, hBl, 1, Submonoid.one_mem _, fun k => by
      rw [List.getD_eq_getElem _ _ k.isLt, Module.End.one_apply]
      rfl⟩
  obtain ⟨hVpt, hVlen⟩ := kOrbReplay_facts hG B par [B] (by simpa using hbase)
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hpar k hk
      simp only [List.length_singleton]
      exact ⟨by omega, h2⟩)
  have hVpt' : ∀ t ∈ V, kOrbPt G B t := hVpt
  have hVlen' : V.length = 1 + par.length := hVlen
  have hBV : B ∈ V := (prefix_foldl_append
    (fun (V : List (List (List ℕ))) (e : ℕ × ℕ) => kTupApply (G.getD e.2 []) (V.getD e.1 [])) par
      [B]).subset (List.mem_singleton_self B)
  have hmemV : ∀ i < V.length, V.getD i [] ∈ V := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  refine ⟨V.map (kMdl B), ?_, by rw [List.length_map, hVlen']; omega, ?_, ?_, ?_⟩
  ·
    have hpw := TWLK.kIncr_pairwise _ hinc
    have hordnd : ord.Nodup := List.Pairwise.of_map _
      (fun a b hab e => by subst e; exact lt_irrefl _ hab) hpw
    have hsurj : ∀ i < V.length, i ∈ ord := by
      have hsub : ord.toFinset ⊆ Finset.range V.length := fun x hx =>
        Finset.mem_range.mpr (hordr x (List.mem_toFinset.mp hx))
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_range, List.toFinset_card_of_nodup hordnd, hordl])
      intro i hi
      rw [← List.mem_toFinset, heq]
      exact Finset.mem_range.mpr hi
    have hkey : ∀ t ∈ V, ∀ t' ∈ V, kMdl B t = kMdl B t' →
        Certificates.TWLK.kVKey 3 t = Certificates.TWLK.kVKey 3 t' := by
      intro t ht t' ht' he
      obtain ⟨hli, hvi, -⟩ := hVpt' t ht
      obtain ⟨hlj, hvj, -⟩ := hVpt' t' ht'
      rw [TWLK.kVKey_mod, TWLK.kVKey_mod 3 t']
      congr 1
      apply List.ext_getElem (by rw [List.length_map, List.length_map, hli, hlj])
      intro k h1 h2
      simp only [List.getElem_map]
      rw [List.length_map, hli] at h1
      have hc := congrFun he ⟨k, h1⟩
      simp only [kMdl] at hc
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hc
      exact TWLK.k6_mod_of_toZ (hvi _ (List.getElem_mem _)) (hvj _ (List.getElem_mem _)) hc
    have hkeq : ∀ i < V.length, ∀ j < V.length, kMdl B (V.getD i []) = kMdl B (V.getD j []) →
        Certificates.TWLK.kVKey 3 (V.getD i []) = Certificates.TWLK.kVKey 3 (V.getD j []) :=
      fun i hi j hj => hkey _ (hmemV i hi) _ (hmemV j hj)
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro a b ha hb hab heq
    simp only [List.length_map] at ha hb
    simp only [List.getElem_map] at heq
    obtain ⟨x, hx, hxa⟩ := List.mem_iff_getElem.mp (hsurj a ha)
    obtain ⟨y, hy, hyb⟩ := List.mem_iff_getElem.mp (hsurj b hb)
    have hk := hkeq a ha b hb (by rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]; exact heq)
    rcases lt_trichotomy x y with hlt | rfl | hlt
    · have := List.pairwise_iff_getElem.mp hpw x y (by simpa using hx) (by simpa using hy) hlt
      simp only [List.getElem_map, hxa, hyb] at this
      omega
    · have := hxa.symm.trans hyb
      omega
    · have := List.pairwise_iff_getElem.mp hpw y x (by simpa using hy) (by simpa using hx) hlt
      simp only [List.getElem_map, hxa, hyb] at this
      omega
  ·
    refine List.mem_map.mpr ⟨B, hBV, funext fun i => ?_⟩
    change ggDepELToZ (B.getD i.val []) = _
    rw [List.getD_eq_getElem _ _ i.isLt]
    rfl
  ·
    intro v hv g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hc := kAll2_get _ V cl hcl
    have hr := kAll2_get _ G _ (hc.2 i hi (by rw [← hc.1]; exact hi))
    have hw := kAll2_get _ _ _ (hr.2 j hj (by rw [← hr.1]; exact hj))
    obtain ⟨hl, hvec, -⟩ := hVpt' _ (List.getElem_mem hi)
    by_cases hcV : cl[i][j] < V.length
    · rw [List.getD_eq_getElem _ _ hcV] at hw
      refine List.mem_map.mpr ⟨V[cl[i][j]], List.getElem_mem hcV, funext fun k => ?_⟩
      have hkt : k.val < (kTupApply G[j] V[i]).length := by
        rw [kTupApply, List.length_map, hl]
        exact k.isLt
      have hkc : k.val < V[cl[i][j]].length := by
        rw [hw.1]
        exact hkt
      have hq := hw.2 k.val hkc hkt
      simp only [kTupApply, List.getElem_map] at hq
      have hki : k.val < V[i].length := by
        rw [hl]
        exact k.isLt
      simp only [kMdl]
      rw [List.getD_eq_getElem _ _ hkc, List.getD_eq_getElem _ _ hki, dk_toZ_of_veceq hq,
        (dk_apply_lin (hG _ (List.getElem_mem hj)) (hvec _ (List.getElem_mem hki))).2]
    · have e0 : V.getD cl[i][j] [] = [] := List.getD_eq_default _ _ (by omega)
      have hB0 : B.length = 0 := by
        have h1 := hw.1
        rw [e0, kTupApply, List.length_map, hl] at h1
        simp at h1
        omega
      exact List.mem_map.mpr ⟨B, hBV, funext fun k => absurd k.isLt (by omega)⟩
  ·
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    obtain ⟨-, -, m, hm, hk⟩ := hVpt' t ht
    exact ⟨m, hm, funext hk⟩

theorem kOrb_dvd {G : List (List (List ℕ))} (hG : ∀ g ∈ G, ggTWLMatWF 6 g)
    (hinv : ∀ g ∈ Submonoid.closure (kLinSet G),
      ∃ g' ∈ Submonoid.closure (kLinSet G), g * g' = 1 ∧ g' * g = 1)
    {B : List (List ℕ)} {par : List (ℕ × ℕ)} {cl : List (List ℕ)} {ord : List ℕ}
    (h : kOrbOK G B par cl ord = true) :
    par.length + 1 ∣ Nat.card ↥(Submonoid.closure (kLinSet G)) := by
  obtain ⟨L, hnd, hlen, hb, hcl, hrep⟩ := kOrbOK_facts hG h
  let M := Module.End (ZMod 3) (GGDepAE 3 6)
  let S' := kLinSet G
  let H : Subgroup Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S'}
      one_mem' := by
        change ((1 : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        change ((u * v : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv
      inv_mem' := by
        intro u hu
        obtain ⟨g', hg'mem, hg'1, -⟩ := hinv (u : M) hu
        have hcalc : ((u⁻¹ : Mˣ) : M) = g' := by
          calc ((u⁻¹ : Mˣ) : M) = ((u⁻¹ : Mˣ) : M) * ((u : M) * g') := by rw [hg'1, mul_one]
            _ = g' := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        change ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S'
        rw [hcalc]
        exact hg'mem }
  have hcard : Nat.card ↥H = Nat.card ↥(Submonoid.closure S') :=
    dk_card_subgroup hinv H (fun u => Iff.rfl)
  let b : Fin B.length → GGDepAE 3 6 := fun i => ggDepELToZ (B.get i)
  have hsmul : ∀ (u : ↥H) (v : Fin B.length → GGDepAE 3 6),
      u • v = fun i => ((u : Mˣ) : M) (v i) := fun _ _ => rfl
  have hpres : ∀ m ∈ Submonoid.closure S', ∀ v ∈ L, (fun i => m (v i)) ∈ L := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        exact fun v hv => hcl v hv g hg
    | one => exact fun v hv => hv
    | mul x y _ _ ihx ihy => exact fun v hv => ihx _ (ihy v hv)
  have horb : MulAction.orbit (↥H) b = {v | v ∈ L} := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      change u • b ∈ L
      rw [hsmul]
      exact hpres _ u.2 b hb
    · intro hv
      obtain ⟨m, hm, rfl⟩ := hrep v hv
      obtain ⟨m', -, hmm', hm'm⟩ := hinv m hm
      exact ⟨⟨⟨m, m', hmm', hm'm⟩, hm⟩, rfl⟩
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype (MulAction.orbit (↥H) b) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer (↥H) b) := Fintype.ofFinite _
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥H) b
  have h2 : Fintype.card (MulAction.orbit (↥H) b) = L.length := by
    rw [← Nat.card_eq_fintype_card, horb, Nat.card_coe_set_eq, ← List.coe_toFinset, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  rw [← hcard, ← hlen, Nat.card_eq_fintype_card, ← h1, h2]
  exact Dvd.intro _ rfl

theorem kT_inv {Q : List GGDepANPair} (hQ : ∀ q ∈ Q, GGDepELNValid q) :
    ∀ t ∈ kT Q, t * t = 1 := by
  rintro t ⟨q, hq, rfl⟩
  rw [(dk_matOfPair (hQ q hq)).2]
  exact dk_refl_mul_self_of_isRefl _ (dk_isRefl_of_valid (hQ q hq))

theorem dk_om_wf {Q : List GGDepANPair} (hQ : ∀ q ∈ Q, GGDepELNValid q) :
    ∀ t ∈ Q.map (ggTWLMatOfPair 3 6), ggTWLMatWF 6 t := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact (dk_matOfPair (hQ q hq)).1

theorem dk_word_mem {Q : List GGDepANPair} (hQ : ∀ q ∈ Q, GGDepELNValid q) {u : List ℕ}
    (hu : ∀ j ∈ u, j < Q.length) :
    ggTWLMatWF 6 (ggTWLWordMat 3 6 (Q.map (ggTWLMatOfPair 3 6)) u) ∧
      ggTWLMatLin 3 6 (ggTWLWordMat 3 6 (Q.map (ggTWLMatOfPair 3 6)) u) ∈
        Submonoid.closure (kT Q) := by
  have hu' : ∀ k ∈ u, k < (Q.map (ggTWLMatOfPair 3 6)).length := by
    simpa only [List.length_map] using hu
  obtain ⟨hwf, hlin⟩ := ggTWLWordMat_lin (p := 3) (d := 6) (dk_om_wf hQ) hu'
  refine ⟨hwf, ?_⟩
  rw [hlin]
  refine Submonoid.list_prod_mem _ (fun g hg => ?_)
  rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
  have hklt : k < Q.length := hu k hk
  rw [List.getD_eq_getElem _ _ (by simpa using hklt), List.getElem_map]
  exact Submonoid.subset_closure ⟨Q[k], List.getElem_mem hklt, rfl⟩

theorem dk_foldl_lcm_dvd {α : Type} (f : α → ℕ) {n : ℕ} :
    ∀ (l : List α) (a : ℕ), a ∣ n → (∀ s ∈ l, f s ∣ n) →
      l.foldl (fun k s => Nat.lcm k (f s)) a ∣ n
  | [], _, ha, _ => ha
  | s :: l, a, ha, hs => dk_foldl_lcm_dvd f l (Nat.lcm a (f s)) (Nat.lcm_dvd ha (hs s (by simp)))
      (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))

theorem kPZBase_facts {Q : List GGDepANPair} (hQ : ∀ q ∈ Q, GGDepELNValid q)
    {subs : List KSub} {cen : List ℕ} (h : kPZBase Q subs cen = true) : KFacts (kT Q) := by
  unfold kPZBase at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsubs, hcen⟩, harith⟩ := h
  refine ⟨_, _, ?_, harith, ?_⟩
  · refine dk_foldl_lcm_dvd (fun s : KSub => s.2.2.1.length + 1) subs 1 (one_dvd _) ?_
    intro s hs
    have hs' := List.all_eq_true.mp hsubs s hs
    unfold kSubOK at hs'
    rw [Bool.and_eq_true] at hs'
    obtain ⟨hw, horb⟩ := hs'
    have hw' : ∀ u ∈ s.1, ∀ j ∈ u, j < Q.length := by
      intro u hu j hj
      have := List.all_eq_true.mp (List.all_eq_true.mp hw u hu) j hj
      simpa using this
    have hGwf : ∀ g ∈ s.1.map (ggTWLWordMat 3 6 (Q.map (ggTWLMatOfPair 3 6))),
        ggTWLMatWF 6 g := by
      intro g hg
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact (dk_word_mem hQ (hw' u hu)).1
    have hsub : kLinSet (s.1.map (ggTWLWordMat 3 6 (Q.map (ggTWLMatOfPair 3 6)))) ⊆
        Submonoid.closure (kT Q) := by
      rintro f ⟨g, hg, rfl⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact (dk_word_mem hQ (hw' u hu)).2
    exact (kOrb_dvd hGwf (dk_sub_inv (kT_inv hQ) hsub) horb).trans
      (ggDepEL_card_dvd (kT_inv hQ) hsub)
  · intro hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨hcl, hk⟩ := hc
    have hcl' : ∀ j ∈ cen, j < Q.length := by
      intro j hj
      have := List.all_eq_true.mp hcl j hj
      simpa using this
    obtain ⟨haWF, haM⟩ := dk_word_mem hQ hcl'
    set a := ggTWLWordMat 3 6 (Q.map (ggTWLMatOfPair 3 6)) cen with ha
    unfold kCen at hk
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨hne, hcomm⟩ := hk
    have honeWF : ggTWLMatWF 6 (ggTWLMatOne 6) := (ggTWLMatOne_lin (p := 3) (d := 6)).1
    refine ⟨ggTWLMatLin 3 6 a, haM, ?_, ?_⟩
    · intro heq
      have htrue : ggTWLMatEq 3 a (ggTWLMatOne 6) = true :=
        (ggTWLMatEq_iff haWF honeWF).mpr (by rw [heq, (ggTWLMatOne_lin (p := 3) (d := 6)).2])
      rw [htrue] at hne
      exact Bool.false_ne_true hne.symm
    · rintro t ⟨q, hq, rfl⟩
      have htm : ggTWLMatOfPair 3 6 q ∈ Q.map (ggTWLMatOfPair 3 6) := List.mem_map_of_mem hq
      have hc := List.all_eq_true.mp hcomm _ htm
      have htWF : ggTWLMatWF 6 (ggTWLMatOfPair 3 6 q) := (dk_matOfPair (hQ q hq)).1
      rw [← (ggTWLMatMul_lin (p := 3) (d := 6) haWF htWF).2,
        ← (ggTWLMatMul_lin (p := 3) (d := 6) htWF haWF).2]
      exact (ggTWLMatEq_iff (ggTWLMatMul_lin haWF htWF).1 (ggTWLMatMul_lin htWF haWF).1).mp hc

def dkConj {M : Type*} [Monoid M] (A B : M) (hAB : A * B = 1) (hBA : B * A = 1) : M →* M where
  toFun x := A * x * B
  map_one' := by rw [mul_one, hAB]
  map_mul' x y := by
    calc A * (x * y) * B = A * x * (B * A) * y * B := by rw [hBA, mul_one]; simp only [mul_assoc]
      _ = A * x * B * (A * y * B) := by simp only [mul_assoc]

theorem dkConj_injective {M : Type*} [Monoid M] (A B : M) (hAB : A * B = 1) (hBA : B * A = 1) :
    Function.Injective (dkConj A B hAB hBA) := by
  intro x y hxy
  have hx : x = B * (A * x * B) * A := by
    simp only [← mul_assoc, hBA, one_mul]; rw [mul_assoc, hBA, mul_one]
  have hy : y = B * (A * y * B) * A := by
    simp only [← mul_assoc, hBA, one_mul]; rw [mul_assoc, hBA, mul_one]
  change A * x * B = A * y * B at hxy
  rw [hx, hy, hxy]

theorem kPZConj_facts {P Q : List GGDepANPair} (hP : ∀ q ∈ P, GGDepELNValid q)
    (hQ : ∀ q ∈ Q, GGDepELNValid q) {m mi : List (List ℕ)} (hm : kMat6 m = true)
    (hmi : kMat6 mi = true) (h : kPZConj P Q m mi = true) (hF : KFacts (kT P)) :
    KFacts (kT Q) := by
  have hwf : ∀ {x : List (List ℕ)}, kMat6 x = true → ggTWLMatWF 6 x := by
    intro x hx
    simp only [kMat6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
    exact hx
  have hmWF := hwf hm
  have hmiWF := hwf hmi
  unfold kPZConj at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩, hall⟩ := h
  have honeWF : ggTWLMatWF 6 (ggTWLMatOne 6) := (ggTWLMatOne_lin (p := 3) (d := 6)).1
  have hAB : ggTWLMatLin 3 6 m * ggTWLMatLin 3 6 mi = 1 := by
    rw [← (ggTWLMatMul_lin (p := 3) (d := 6) hmWF hmiWF).2,
      ← (ggTWLMatOne_lin (p := 3) (d := 6)).2]
    exact (ggTWLMatEq_iff (ggTWLMatMul_lin hmWF hmiWF).1 honeWF).mp h1
  have hBA : ggTWLMatLin 3 6 mi * ggTWLMatLin 3 6 m = 1 := by
    rw [← (ggTWLMatMul_lin (p := 3) (d := 6) hmiWF hmWF).2,
      ← (ggTWLMatOne_lin (p := 3) (d := 6)).2]
    exact (ggTWLMatEq_iff (ggTWLMatMul_lin hmiWF hmWF).1 honeWF).mp h2
  set φ := dkConj (ggTWLMatLin 3 6 m) (ggTWLMatLin 3 6 mi) hAB hBA with hφ
  have hpair : ∀ a b : GGDepANPair, a ∈ P → b ∈ Q →
      ggTWLMatEq 3 (ggTWLMatMul 3 6 (ggTWLMatMul 3 6 m (ggTWLMatOfPair 3 6 a)) mi)
        (ggTWLMatOfPair 3 6 b) = true →
      φ (ggTWLMatLin 3 6 (ggTWLMatOfPair 3 6 a)) = ggTWLMatLin 3 6 (ggTWLMatOfPair 3 6 b) := by
    intro a b ha hb hab
    have haWF := (dk_matOfPair (hP a ha)).1
    have hbWF := (dk_matOfPair (hQ b hb)).1
    have hmaWF := (ggTWLMatMul_lin (p := 3) (d := 6) hmWF haWF).1
    have hmamWF := (ggTWLMatMul_lin (p := 3) (d := 6) hmaWF hmiWF).1
    have heq := (ggTWLMatEq_iff hmamWF hbWF).mp hab
    rw [(ggTWLMatMul_lin (p := 3) (d := 6) hmaWF hmiWF).2,
      (ggTWLMatMul_lin (p := 3) (d := 6) hmWF haWF).2] at heq
    exact heq
  have himg : kT Q = φ '' kT P := by
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, hab⟩ := kAll2_mem_right _ P Q hall b hb
      exact ⟨_, ⟨a, ha, rfl⟩, hpair a b ha hb hab⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      obtain ⟨b, hb, hab⟩ := kAll2_mem_left _ P Q hall a ha
      exact ⟨b, hb, hpair a b ha hb hab⟩
  have hinj := dkConj_injective (ggTWLMatLin 3 6 m) (ggTWLMatLin 3 6 mi) hAB hBA
  have hcl : Submonoid.closure (kT Q) = (Submonoid.closure (kT P)).map φ := by
    rw [himg, MonoidHom.map_mclosure]
  obtain ⟨K, hasCen, hK, harith, hcen⟩ := hF
  refine ⟨K, hasCen, ?_, harith, ?_⟩
  · rw [hcl, Nat.card_congr (Submonoid.equivMapOfInjective _ φ hinj).toEquiv.symm]
    exact hK
  · intro hc
    obtain ⟨a, haM, hne, hcomm⟩ := hcen hc
    refine ⟨φ a, ?_, ?_, ?_⟩
    · rw [hcl]
      exact Submonoid.mem_map_of_mem _ haM
    · intro h1'
      apply hne
      apply hinj
      rw [h1', map_one]
    · rw [himg]
      rintro _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul, hcomm t ht]

theorem groups_facts (Ps : List (List GGDepANPair)) (S : List KBase) (C : List KConj)
    (hv : kPairsOK Ps = true) (hsh : kConjShapes C = true)
    (hS : ∀ i < S.length, kBaseAt Ps S i = true) (hC : ∀ i < C.length, kConjAt Ps S C i = true)
    (hcov : kGroupsCover Ps S C = true) :
    (∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q) ∧
      ∀ g < Ps.length, KFacts (kT (Ps.getD g [])) := by
  have hval : ∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q := by
    intro g hg q hq
    rw [List.getD_eq_getElem _ _ hg] at hq
    have h := List.all_eq_true.mp (List.all_eq_true.mp hv _ (List.getElem_mem hg)) q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hbase : ∀ e ∈ S, e.1 < Ps.length ∧ KFacts (kT (Ps.getD e.1 [])) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have h := hS i hi
    simp only [kBaseAt, List.getElem?_eq_getElem hi, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, kPZBase_facts (hval _ h.1) h.2⟩
  refine ⟨hval, fun g hg => ?_⟩
  have hc := List.all_eq_true.mp hcov g (List.mem_range.mpr hg)
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · obtain ⟨e, he, rfl⟩ : ∃ e ∈ S, e.1 = g := by simpa using hc
    exact (hbase e he).2
  · obtain ⟨c, hcC, rfl⟩ : ∃ c ∈ C, c.1 = g := by simpa using hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcC
    have h := hC i hi
    simp only [kConjAt, List.getElem?_eq_getElem hi, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, hsrc⟩, hconj⟩ := h
    obtain ⟨e, he, hesrc⟩ : ∃ e ∈ S, e.1 = C[i].2.1 := by simpa using hsrc
    have hsh' := List.all_eq_true.mp hsh _ (List.getElem_mem hi)
    rw [Bool.and_eq_true] at hsh'
    obtain ⟨hlt, hF⟩ := hbase e he
    rw [hesrc] at hlt hF
    exact kPZConj_facts (hval _ hlt) (hval _ hg) hsh'.1 hsh'.2 hconj hF

theorem kPZRef_line_sound {Ps : List (List GGDepANPair)}
    (hPv : ∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q)
    (hgroups : ∀ g < Ps.length, KFacts (kT (Ps.getD g [])))
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q) (lam mu : ZMod 3)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0)
    (hx : ∃ q ∈ news, ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0) (e : KPZ)
    (h : kPZRef Ps news (ggDepELY0 news) e = true) :
    ∃ c : ZMod 3, c ≠ 0 ∧ GGDepELPZBad (ggDepELGens (ggDepELNNews news))
      (ggDepELx + c • (lam • ggDepELx + mu • ggDepELz)) := by
  obtain ⟨hY0len, t, ht, heq⟩ := ggDepELY0_line hnews lam mu hlm hfix hx
  obtain ⟨hc0, hlt, hq⟩ := kPZRef_sound hnews (ggDepELY0 news) hY0len Ps _ h
  refine ⟨(e.1.1 : ZMod 3) * t⁻¹, mul_ne_zero hc0 (inv_ne_zero ht), ?_⟩
  have htoz : ggDepELToZ (ggDepELY0 news) = t⁻¹ • (lam • ggDepELx + mu • ggDepELz) := by
    rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hT := kT_sub_orbit (hPv _ hlt) hq
  rw [htoz, smul_smul] at hT
  exact delk_pz_bad _ _ _ hT (hgroups _ hlt)

theorem kRT_sound {H : List KHK} {Z : List KPZ} {Ps : List (List GGDepANPair)}
    (hPv : ∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q)
    (hgroups : ∀ g < Ps.length, KFacts (kT (Ps.getD g [])))
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q) (lam mu : ZMod 3)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0)
    (hx : ∃ q ∈ news, ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0) (r : ℕ × ℕ)
    (h : kRT H Z Ps news r = true) :
    GGDepELKill .other (ggDepELNNews news) (lam • ggDepELx + mu • ggDepELz) ∨
      ∃ c : ZMod 3, c ≠ 0 ∧ GGDepELPZBad (ggDepELGens (ggDepELNNews news))
        (ggDepELx + c • (lam • ggDepELx + mu • ggDepELz)) := by
  obtain ⟨hY0len, t, ht, heq⟩ := ggDepELY0_line hnews lam mu hlm hfix hx
  unfold kRT at h
  split_ifs at h with h1 h2
  · left
    have hkill0 := kHKTest_sound hnews (ggDepELY0 news) hY0len _ h
    have hs := (ggDepELKill_other_smul (ggDepELNNews news)
      (ggDepELToZ (ggDepELY0 news)) t ht).mpr hkill0
    rw [← heq] at hs
    exact hs
  · exact Or.inr (kPZRef_line_sound hPv hgroups hnews lam mu hlm hfix hx _ h)

private theorem dk_cases1_extract (rt : List GGDepANPair → ℕ × ℕ → Bool) (c0 : ℕ)
    (wits : List KWit) (exc : List ((List ℕ × List ℕ) × (ℕ × ℕ)))
    (h : kCases1 rt c0 wits exc = true) {lh la : List ℕ}
    (hlh : lh ∈ ggDepELSolH (fun c => if c = c0 then 2 else 0))
    (hla : la ∈ ggDepELSolA (fun c => if c = c0 then 2 else 0))
    (hd : ggDepANDot 3 la lh = 2) (hz : ggDepANDot 3 la ggDepELNX ≠ 0) :
    (∃ w ∈ wits, ggDepELTvTest [(lh, la)] (kWit w) = true) ∨
      (∃ e ∈ exc, rt [(lh, la)] e.2 = true) := by
  simp only [kCases1] at h
  have h1 := List.all_eq_true.mp h lh hlh
  have h2 := List.all_eq_true.mp h1 la hla
  have hc : (ggDepANDot 3 la lh == 2 && ggDepANDot 3 la ggDepELNX != 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hd, bne_iff_ne.mpr hz⟩
  rw [if_pos hc] at h2
  cases hfind : exc.find?
      (fun e => ggTWLVecEq 3 e.1.1 lh && ggTWLVecEq 3 e.1.2 la) with
  | none =>
      rw [hfind] at h2
      exact Or.inl (List.any_eq_true.mp h2)
  | some e =>
      rw [hfind] at h2
      exact Or.inr ⟨e, List.mem_of_find?_eq_some hfind, h2⟩

theorem dk_notSurv1 {H : List KHK} {Z : List KPZ} {Ps : List (List GGDepANPair)}
    {O : List KPat1} {T : List KPat2}
    (hPv : ∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q)
    (hgroups : ∀ g < Ps.length, KFacts (kT (Ps.getD g [])))
    (hcover : kCover O T = true) (hO : ∀ i < O.length, kPat1At H Z Ps O i = true) :
    ¬ GGDepED4LowSurv1 := by
  rintro ⟨c0, ha, αa, lam, mu, hleaf, hpair, hdot, hx, hlm, hfix, hkf, hko, hpz⟩
  have hc0 : c0.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c0).mpr hleaf
  have hcov1 := (Bool.and_eq_true_iff.mp hcover).1
  obtain ⟨e, he, hec⟩ : ∃ e ∈ O, e.1 = c0.val := by
    simpa using List.all_eq_true.mp hcov1 c0.val hc0
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hpat := hO i hi
  simp only [kPat1At, List.getElem?_eq_getElem hi, Bool.and_eq_true] at hpat
  obtain ⟨hwv, hcases⟩ := hpat
  rw [hec] at hcases
  obtain ⟨lh, la, hlh, hla, hd, hz, hvalid_pair, hnews_eq⟩ :=
    ggDepELEnc1 c0 hleaf ha αa hpair hdot hx
  have hvalid : ∀ q ∈ [(lh, la)], GGDepELNValid q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hvalid_pair
  have hla_eq : ggDepELToZ la = αa := by
    have hmem : (ggDepELToZ lh, ggDepELToZ la) ∈ ggDepELNNews [(lh, la)] :=
      ⟨(lh, la), by simp, rfl⟩
    rw [hnews_eq] at hmem
    rw [Set.mem_singleton_iff] at hmem
    exact congrArg Prod.snd hmem
  have hfix' : ∀ q ∈ [(lh, la)],
      ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hla_eq]
    exact hfix
  have hx' : ∃ q ∈ [(lh, la)], ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0 :=
    ⟨(lh, la), by simp, by rw [hla_eq]; exact hx⟩
  obtain hwit | hexc := dk_cases1_extract _ c0.val _ _ hcases hlh hla hd hz
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hv : ggDepELTvValid (6 + [(lh, la)].length) (kWit w) = true :=
      List.all_eq_true.mp hwv w hwmem
    have hkill := ggDepELTv_sound hvalid (kWit w) hv hwtest
    rw [hnews_eq] at hkill
    exact hkf (Or.inl hkill)
  · obtain ⟨e', -, hrt⟩ := hexc
    rcases kRT_sound hPv hgroups hvalid lam mu hlm hfix' hx' e'.2 hrt with hk | ⟨c, hc, hbad⟩
    · rw [hnews_eq] at hk
      exact hko hk
    · rw [hnews_eq] at hbad
      exact hpz c hc hbad

private theorem dk_cases2_extract (rt : List GGDepANPair → ℕ × ℕ → Bool) (c c' : ℕ)
    (wits : List KWit)
    (exc : List ((List ℕ × List ℕ × List ℕ × List ℕ) × (ℕ × ℕ)))
    (h : kCases2 rt c c' wits exc = true)
    {lh1 la1 lh2 la2 : List ℕ}
    (hlh1 : lh1 ∈ ggDepELSolH (fun d => if d = c then 2 else 0))
    (hla1 : la1 ∈ ggDepELSolA (fun d => if d = c then 2 else 0))
    (hlh2 : lh2 ∈ ggDepELSolH (fun d => if d = c' then 2 else 0))
    (hla2 : la2 ∈ ggDepELSolA (fun d => if d = c' then 2 else 0))
    (hd1 : ggDepANDot 3 la1 lh1 = 2)
    (hd2 : ggDepANDot 3 la1 lh2 = 0)
    (hd3 : ggDepANDot 3 la2 lh2 = 2)
    (hd4 : ggDepANDot 3 la2 lh1 = 0)
    (hx : ggDepANDot 3 la1 ggDepELNX ≠ 0 ∨ ggDepANDot 3 la2 ggDepELNX ≠ 0)
    (hdet : (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 =
      (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3) :
    (∃ w ∈ wits, ggDepELTvTest [(lh1, la1), (lh2, la2)] (kWit w) = true) ∨
      (∃ e ∈ exc, rt [(lh1, la1), (lh2, la2)] e.2 = true) := by
  simp only [kCases2] at h
  have e1 := List.all_eq_true.mp h lh1 hlh1
  have e2 := List.all_eq_true.mp e1 la1 hla1
  rw [if_pos (beq_iff_eq.mpr hd1)] at e2
  have e3 := List.all_eq_true.mp e2 lh2 hlh2
  rw [if_pos (beq_iff_eq.mpr hd2)] at e3
  have e4 := List.all_eq_true.mp e3 la2 hla2
  have hor : (ggDepANDot 3 la1 ggDepELNX != 0 || ggDepANDot 3 la2 ggDepELNX != 0) = true := by
    rw [Bool.or_eq_true_iff]
    exact hx.imp (fun h => bne_iff_ne.mpr h) (fun h => bne_iff_ne.mpr h)
  have hcond : (ggDepANDot 3 la2 lh2 == 2 && ggDepANDot 3 la2 lh1 == 0 &&
      (ggDepANDot 3 la1 ggDepELNX != 0 || ggDepANDot 3 la2 ggDepELNX != 0) &&
      (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 ==
        (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨beq_iff_eq.mpr hd3, beq_iff_eq.mpr hd4⟩, hor⟩, beq_iff_eq.mpr hdet⟩
  rw [if_pos hcond] at e4
  cases hfind : exc.find? (fun e => ggTWLVecEq 3 e.1.1 lh1 && ggTWLVecEq 3 e.1.2.1 la1 &&
      ggTWLVecEq 3 e.1.2.2.1 lh2 && ggTWLVecEq 3 e.1.2.2.2 la2) with
  | none => rw [hfind] at e4; exact Or.inl (List.any_eq_true.mp e4)
  | some e =>
      rw [hfind] at e4
      exact Or.inr ⟨e, List.mem_of_find?_eq_some hfind, e4⟩

theorem dk_notSurv2 {H : List KHK} {Z : List KPZ} {Ps : List (List GGDepANPair)}
    {O : List KPat1} {T : List KPat2}
    (hPv : ∀ g < Ps.length, ∀ q ∈ Ps.getD g [], GGDepELNValid q)
    (hgroups : ∀ g < Ps.length, KFacts (kT (Ps.getD g [])))
    (hcover : kCover O T = true) (hT : ∀ i < T.length, kPat2At H Z Ps T i = true)
    (hTpz : T.all (fun e => e.2.2.all fun c => c.2.1 == 2) = true) :
    ¬ GGDepED4LowSurv2 := by
  rintro ⟨c, c', ha1, αa1, ha2, αa2, lam, mu, hc, hc', hne, hP, hx, hlm, h1, h2, htv, hpz⟩
  have hcov2 := (Bool.and_eq_true_iff.mp hcover).2
  have hc_mem : c.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c).mpr hc
  have hc'_mem : c'.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c').mpr hc'
  have hpairc := List.all_eq_true.mp (List.all_eq_true.mp hcov2 c.val hc_mem) c'.val hc'_mem
  have hne' : c.val ≠ c'.val := fun hh => hne (Fin.ext hh)
  rw [Bool.or_eq_true, beq_iff_eq] at hpairc
  obtain ⟨e, he, hec⟩ : ∃ e ∈ T, e.1 = (c.val, c'.val) := by
    rcases hpairc with h | h
    · exact absurd h hne'
    · simpa using h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hpat := hT i hi
  simp only [kPat2At, List.getElem?_eq_getElem hi, Bool.and_eq_true] at hpat
  obtain ⟨hwv, hcases⟩ := hpat
  rw [hec] at hcases
  obtain ⟨lh1, la1, lh2, la2, hlh1, hla1, hlh2, hla2, hd1, hd2, hd3, hd4, hx_list, hdet,
    hvalid_pair1, hvalid_pair2, hnews_eq⟩ :=
    ggDepELEnc2 c c' hc hc' ha1 αa1 ha2 αa2 hP hx lam mu hlm h1 h2
  have hvalid : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGDepELNValid q := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact hvalid_pair1
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact hvalid_pair2
      · simp at hq
  have hla1mem : (ggDepELToZ lh1, ggDepELToZ la1) ∈
      ggDepELNNews [(lh1, la1), (lh2, la2)] :=
    ⟨(lh1, la1), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla1mem
  have hla2mem : (ggDepELToZ lh2, ggDepELToZ la2) ∈
      ggDepELNNews [(lh1, la1), (lh2, la2)] :=
    ⟨(lh2, la2), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla2mem
  have hfix' : ∀ q ∈ [(lh1, la1), (lh2, la2)],
      ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0 := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      change ggDepAdot (ggDepELToZ la1) (lam • ggDepELx + mu • ggDepELz) = 0
      rcases hla1mem with he | he
      · have hla : ggDepELToZ la1 = αa1 := by simpa using congrArg Prod.snd he
        rw [hla]; exact h1
      · have hla : ggDepELToZ la1 = αa2 := by simpa using congrArg Prod.snd he
        rw [hla]; exact h2
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        change ggDepAdot (ggDepELToZ la2) (lam • ggDepELx + mu • ggDepELz) = 0
        rcases hla2mem with he | he
        · have hla : ggDepELToZ la2 = αa1 := by simpa using congrArg Prod.snd he
          rw [hla]; exact h1
        · have hla : ggDepELToZ la2 = αa2 := by simpa using congrArg Prod.snd he
          rw [hla]; exact h2
      · simp at hq
  have hx' : ∃ q ∈ [(lh1, la1), (lh2, la2)],
      ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0 := by
    rcases hx with hx1 | hx2
    · have hmem : (ha1, αa1) ∈ ggDepELNNews [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggDepELToZ q.2 = αa1 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx1⟩
    · have hmem : (ha2, αa2) ∈ ggDepELNNews [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggDepELToZ q.2 = αa2 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx2⟩
  obtain hwit | hexc := dk_cases2_extract _ c.val c'.val _ _ hcases
    hlh1 hla1 hlh2 hla2 hd1 hd2 hd3 hd4 hx_list hdet
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hv : ggDepELTvValid (6 + [(lh1, la1), (lh2, la2)].length) (kWit w) = true :=
      List.all_eq_true.mp hwv w hwmem
    have hkill := ggDepELTv_sound hvalid (kWit w) hv hwtest
    rw [hnews_eq] at hkill
    exact htv hkill
  · obtain ⟨e', he', hrt⟩ := hexc
    have hkind : e'.2.1 = 2 := by
      have hall := List.all_eq_true.mp (List.all_eq_true.mp hTpz _ (List.getElem_mem hi)) e' he'
      simpa using hall
    have hrt' : kPZRef Ps [(lh1, la1), (lh2, la2)] (ggDepELY0 [(lh1, la1), (lh2, la2)])
        (Z.getD e'.2.2 kZ0) = true := by
      simpa [kRT, hkind] using hrt
    obtain ⟨c'', hc'', hbad⟩ := kPZRef_line_sound hPv hgroups hvalid lam mu hlm hfix' hx' _ hrt'
    rw [hnews_eq] at hbad
    exact hpz c'' hc'' hbad

theorem delk_sound (H : List KHK) (Z : List KPZ) (Ps : List (List GGDepANPair))
    (O : List KPat1) (T : List KPat2) (S : List KBase) (C : List KConj)
    (hv : kPairsOK Ps = true) (hsh : kConjShapes C = true)
    (hS : ∀ i < S.length, kBaseAt Ps S i = true) (hC : ∀ i < C.length, kConjAt Ps S C i = true)
    (hcov : kGroupsCover Ps S C = true) (hcover : kCover O T = true)
    (hO : ∀ i < O.length, kPat1At H Z Ps O i = true)
    (hT : ∀ i < T.length, kPat2At H Z Ps T i = true)
    (hTpz : T.all (fun e => e.2.2.all fun c => c.2.1 == 2) = true) :
    GGDepED4LowCells := by
  obtain ⟨hPv, hgroups⟩ := groups_facts Ps S C hv hsh hS hC hcov
  exact ⟨dk_notSurv1 hPv hgroups hcover hO, dk_notSurv2 hPv hgroups hcover hT hTpz⟩

end CFSG.StandardType.DELK

end
