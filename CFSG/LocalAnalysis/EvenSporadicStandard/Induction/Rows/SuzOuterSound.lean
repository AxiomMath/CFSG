module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow
public import CFSG.Sporadic.SuzOddCore.CTIBase
public import Certificates.Certificate27215
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.ConjClassCount

public noncomputable section

namespace CFSG.EvenSporadicStandard.SuzOuter

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.Induction.AutBound

@[expose] def gen (j : ℕ) : Equiv.Perm (Fin 1782) := CFSG.Sporadic.SuzOddCore.invInnerGen 3 j

@[expose] def letterElt (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j < 5 then gen j else (gen (j - 5))⁻¹

@[expose] def wordElt (ls : ℕ → Equiv.Perm (Fin 1782)) (w : List ℕ) : Equiv.Perm (Fin 1782) :=
  (w.map ls).prod

theorem size_gensC : gensC.size = 5 := by
  simp [gensC, CFSG.Sporadic.SuzOddCore.invInnerGenArrs,
    CFSG.Sporadic.SuzOddCore.invInnerGenCounts]

theorem tabRep_wordTab {gs : ℕ → Tab} {ls : ℕ → Equiv.Perm (Fin 1782)} (w : List ℕ)
    (h : ∀ j ∈ w, TabRep (gs j) (ls j)) : TabRep (wordTab gs w) (wordElt ls w) := by
  induction w with
  | nil =>
    simp only [wordTab, wordElt, List.foldr_nil, List.map_nil, List.prod_nil]
    exact TabRep.idTab
  | cons j w ih =>
    have ih' := ih fun k hk => h k (List.mem_cons_of_mem _ hk)
    simp only [wordTab, wordElt, List.foldr_cons, List.map_cons, List.prod_cons] at ih' ⊢
    exact (h j List.mem_cons_self).comp ih'

theorem wordElt_mem {C : Subgroup (Equiv.Perm (Fin 1782))} {ls : ℕ → Equiv.Perm (Fin 1782)}
    (w : List ℕ) (h : ∀ j ∈ w, ls j ∈ C) : wordElt ls w ∈ C := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact h j hj

theorem map_getElem!_toArray {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α)
    {j : ℕ} (hj : j < l.length) : (l.map f).toArray[j]! = f l[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos l j hj]
  simp

structure Checked (EP IA IB IC EE : Enum) : Prop where
  hsz : ∀ j < 5, gensC[j]!.size = 1782
  enumP : enumOK 1782 gensP EP = true
  sizeP : EP.tabs.size = 256
  orbA : orbitOK 1782 gensC (gensC.map (invTab 1782)) (repTab 0) IA = true
  sizeA : IA.tabs.size = 315
  orbB : orbitOK 1782 gensC (gensC.map (invTab 1782)) (repTab 1) IB = true
  sizeB : IB.tabs.size = 2520
  orbC : orbitOK 1782 gensC (gensC.map (invTab 1782)) (repTab 2) IC = true
  sizeC : IC.tabs.size = 1800
  cover : coverOK 1782 EP.tabs #[IA.tabs, IB.tabs, IC.tabs] = true
  enumE : enumOK 1782 (gensE IA) EE = true
  sizeE : EE.tabs.size = 128

theorem checked_of_check {EP IA IB IC EE : Enum}
    (h : suzOuterCheckWith (gensC.map (invTab 1782)) EP IA IB IC EE = true) :
    Checked EP IA IB IC EE := by
  simp only [suzOuterCheckWith, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h
  obtain ⟨-, hsz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨fun j hj => by simpa using hsz j hj, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

variable {EP IA IB IC EE : Enum}

section Tables


theorem tabRep_gen (hc : Checked EP IA IB IC EE) {j : ℕ} (hj : j < 5) :
    TabRep gensC[j]! (gen j) := by
  refine ⟨hc.hsz j hj, fun x => ?_⟩
  have hj' : j < (CFSG.Sporadic.SuzOddCore.invInnerGenArrs 3).size := by
    have := size_gensC
    simp only [gensC] at this
    omega
  exact CFSG.Sporadic.SuzOddCore.rep_invInnerGen (by norm_num) hj' x

theorem invsOK_of_checked (hc : Checked EP IA IB IC EE) :
    invsOK 1782 gensC (gensC.map (invTab 1782)) = true := by
  have h := hc.orbA
  simp only [orbitOK, Bool.and_eq_true] at h
  exact h.1

theorem tabRep_letter (hc : Checked EP IA IB IC EE) {j : ℕ} (hj : j < 10) :
    TabRep (letterTab j) (letterElt j) := by
  unfold letterTab letterElt
  by_cases h5 : j < 5
  · simp only [h5, ↓reduceIte]
    exact tabRep_gen hc h5
  · simp only [h5, ↓reduceIte]
    have hk : j - 5 < gensC.size := by rw [size_gensC]; omega
    have h := invsOK_spec (invsOK_of_checked hc) hk (tabRep_gen hc (by omega : j - 5 < 5))
    have e : (gensC.map (invTab 1782))[j - 5]! = invTab 1782 gensC[j - 5]! := by
      rw [getElem!_pos _ (j - 5) (by simpa using hk), Array.getElem_map,
        ← getElem!_pos gensC (j - 5) hk]
    rwa [e] at h

@[expose] def pElt (j : ℕ) : Equiv.Perm (Fin 1782) := wordElt letterElt wordsP[j]!

theorem wordsP_letters : ∀ w ∈ wordsP, ∀ l ∈ w, l < 10 := by decide

theorem size_gensP : gensP.size = 3 := by simp [gensP, wordsP]

theorem tabRep_gensP (hc : Checked EP IA IB IC EE) {j : ℕ} (hj : j < 3) :
    TabRep gensP[j]! (pElt j) := by
  have hj' : j < wordsP.length := by simpa [wordsP] using hj
  have e : gensP[j]! = wordTab letterTab wordsP[j]! := map_getElem!_toArray _ _ hj'
  rw [e]
  exact tabRep_wordTab _ fun l hl =>
    tabRep_letter hc (wordsP_letters _ (by
      rw [getElem!_pos wordsP j hj']
      exact List.getElem_mem hj') l hl)

end Tables

@[expose] def CC : Subgroup (Equiv.Perm (Fin 1782)) := CFSG.Sporadic.SuzOddCore.invE 3

@[expose] def PP : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure {g | ∃ j < gensP.size, TabRep gensP[j]! g}

@[expose] def repElt (k : ℕ) : Equiv.Perm (Fin 1782) := wordElt pElt (repWords.getD k [])

@[expose] def Cls (k : ℕ) : Set (Equiv.Perm (Fin 1782)) :=
  {x | ∃ c ∈ CC, x = c * repElt k * c⁻¹}

theorem repWords_letters : ∀ w ∈ repWords, ∀ l ∈ w, l < 3 := by decide

theorem mem_repWords {k : ℕ} (hk : k < 3) : repWords.getD k [] ∈ repWords := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

section Main


theorem card_CC : Nat.card CC = 1209600 := by
  have := CFSG.Sporadic.SuzOddCore.card_invE (i := 3) (by norm_num)
  simpa [CC, CFSG.Sporadic.SuzOddCore.invInnerOrders] using this

theorem gen_mem_CC {j : ℕ} (hj : j < 5) : gen j ∈ CC := by
  refine CFSG.Sporadic.SuzOddCore.invInnerGen_mem (i := 3) (by norm_num) ?_
  have := size_gensC
  simp only [gensC] at this
  omega

theorem letterElt_mem_CC {j : ℕ} (hj : j < 10) : letterElt j ∈ CC := by
  unfold letterElt
  split_ifs with h
  · exact gen_mem_CC h
  · exact inv_mem (gen_mem_CC (by omega))

theorem CC_eq_closure : CC = Subgroup.closure {g | ∃ k < 5, gen k = g} := by
  have h := CFSG.Sporadic.SuzOddCore.invE_eq_closure (i := 3) (by norm_num)
  have hs := size_gensC
  simp only [gensC] at hs
  rw [hs] at h
  exact h

theorem closure_AC (hc : Checked EP IA IB IC EE) :
    Subgroup.closure {g | ∃ j < gensC.size, TabRep gensC[j]! g} = CC := by
  rw [CC_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, hg⟩
    rw [size_gensC] at hj
    exact ⟨j, hj, (tabRep_gen hc hj).perm_eq hg⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by rw [size_gensC]; exact hj, tabRep_gen hc hj⟩

theorem pElt_mem_PP (hc : Checked EP IA IB IC EE) {j : ℕ} (hj : j < 3) : pElt j ∈ PP :=
  Subgroup.subset_closure ⟨j, by rw [size_gensP]; exact hj, tabRep_gensP hc hj⟩

theorem PP_le_CC (hc : Checked EP IA IB IC EE) : PP ≤ CC := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, hj, hg⟩
  have hj3 : j < 3 := by rwa [size_gensP] at hj
  have hgj : g = pElt j := ((tabRep_gensP hc hj3).perm_eq hg).symm
  rw [hgj]
  have hj' : j < wordsP.length := by simpa [wordsP] using hj3
  exact wordElt_mem _ fun l hl => letterElt_mem_CC (wordsP_letters _ (by
    rw [getElem!_pos wordsP j hj']
    exact List.getElem_mem hj') l hl)

theorem enumerates_PP (hc : Checked EP IA IB IC EE) : Enumerates PP EP.tabs.toList :=
  enumerates_closure (fun a ha => ha)
    (fun j hj => ⟨pElt j, ⟨j, hj, tabRep_gensP hc (by rwa [size_gensP] at hj)⟩,
      tabRep_gensP hc (by rwa [size_gensP] at hj)⟩) hc.enumP

theorem card_PP (hc : Checked EP IA IB IC EE) : Nat.card PP = 256 := by
  rw [(enumerates_PP hc).card, Array.length_toList, hc.sizeP]

theorem factorization_CC : (Nat.card CC).factorization 2 = 8 := by
  rw [card_CC]
  have h : (1209600 : ℕ) = 2 ^ 8 * 4725 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 4725)]
  simp

theorem tabRep_repTab (hc : Checked EP IA IB IC EE) {k : ℕ} (hk : k < 3) :
    TabRep (repTab k) (repElt k) :=
  tabRep_wordTab _ fun l hl =>
    tabRep_gensP hc (repWords_letters _ (mem_repWords hk) l hl)

theorem repElt_mem_PP (hc : Checked EP IA IB IC EE) {k : ℕ} (hk : k < 3) : repElt k ∈ PP :=
  wordElt_mem _ fun l hl => pElt_mem_PP hc (repWords_letters _ (mem_repWords hk) l hl)

theorem orbit_facts (hc : Checked EP IA IB IC EE) {k : ℕ} (hk : k < 3) {E : Enum}
    (hE : orbitOK 1782 gensC (gensC.map (invTab 1782)) (repTab k) E = true) :
    (∀ t ∈ E.tabs.toList, ∃ c ∈ CC, TabRep t (c * repElt k * c⁻¹)) ∧
      (∀ c ∈ CC, ∃ t ∈ E.tabs.toList, TabRep t (c * repElt k * c⁻¹)) ∧
        E.tabs.toList.Nodup := by
  obtain ⟨h1, h2, h3⟩ := conj_orbit (gens := gensC)
    (A := {g | ∃ j < gensC.size, TabRep gensC[j]! g}) (fun a ha => ha)
    (fun j hj => ⟨gen j, ⟨j, hj, tabRep_gen hc (by rwa [size_gensC] at hj)⟩,
      tabRep_gen hc (by rwa [size_gensC] at hj)⟩) (tabRep_repTab hc hk) hE
  rw [closure_AC hc] at h1 h2
  exact ⟨h1, h2, h3⟩

theorem card_Cls (hc : Checked EP IA IB IC EE) {k : ℕ} (hk : k < 3) {E : Enum}
    (hE : orbitOK 1782 gensC (gensC.map (invTab 1782)) (repTab k) E = true) :
    Nat.card ↥(Cls k) = E.tabs.size := by
  obtain ⟨h1, h2, h3⟩ := orbit_facts hc hk hE
  have := card_set_of_tabs (X := Cls k) (L := E.tabs.toList)
    (fun t ht => by
      obtain ⟨c, hc', hr⟩ := h1 t ht
      exact ⟨_, ⟨c, hc', rfl⟩, hr⟩)
    (fun g ⟨c, hc', hg⟩ => by
      obtain ⟨t, ht, hr⟩ := h2 c hc'
      exact ⟨t, ht, hg ▸ hr⟩) h3
  rw [this, Array.length_toList]

theorem card_centralizer_cls {k : ℕ} (hrC : repElt k ∈ CC) {u : ↥CC}
    (hu : (u : Equiv.Perm (Fin 1782)) ∈ Cls k) :
    Nat.card (Subgroup.centralizer ({u} : Set ↥CC)) * Nat.card ↥(Cls k) = Nat.card CC := by
  have h := card_conj_mul_card_centralizer u
  obtain ⟨c₀, hc₀, hu₀⟩ := hu
  have e : {y : ↥CC // ∃ c : ↥CC, y = c * u * c⁻¹} ≃ ↥(Cls k) :=
    { toFun := fun y => ⟨(y.1 : Equiv.Perm (Fin 1782)), by
        obtain ⟨c, hy⟩ := y.2
        refine ⟨(c : Equiv.Perm (Fin 1782)) * c₀, mul_mem c.2 hc₀, ?_⟩
        have := congrArg Subtype.val hy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [this, hu₀]
        group⟩
      invFun := fun z => ⟨⟨z.1, by
          obtain ⟨d, hd, hz⟩ := z.2
          rw [hz]
          exact mul_mem (mul_mem hd hrC) (inv_mem hd)⟩, by
          obtain ⟨d, hd, hz⟩ := z.2
          refine ⟨⟨d * c₀⁻¹, mul_mem hd (inv_mem hc₀)⟩, ?_⟩
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hz, hu₀]
          group⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e] at h
  rwa [mul_comm] at h

theorem involution_in_cls (hc : Checked EP IA IB IC EE) :
    ∀ z : ↥CC, orderOf z = 2 → ∃ k < 3, (z : Equiv.Perm (Fin 1782)) ∈ Cls k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (PP.subgroupOf CC) = 2 ^ (Nat.card CC).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (PP_le_CC hc)).toEquiv, card_PP hc,
      factorization_CC]
    norm_num
  let Sy : Sylow 2 ↥CC := Sylow.ofCard (PP.subgroupOf CC) hcard
  let S : Set ↥CC := {z | ∃ k < 3, (z : Equiv.Perm (Fin 1782)) ∈ Cls k}
  have hS : ∀ n z, z ∈ S → n * z * n⁻¹ ∈ S := by
    rintro n z ⟨k, hk, c, hcC, hz⟩
    refine ⟨k, hk, (n : Equiv.Perm (Fin 1782)) * c, mul_mem n.2 hcC, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hz]
    group
  have hT : ∀ z ∈ (Sy : Subgroup ↥CC), orderOf z = 2 → z ∈ S := by
    intro z hz hz2
    have hzP : (z : Equiv.Perm (Fin 1782)) ∈ PP := hz
    have hzz : (z : Equiv.Perm (Fin 1782)) * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz2, pow_two] at this
      exact congrArg Subtype.val this
    have hz1 : (z : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => by
      have : z = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz2
      omega
    obtain ⟨i, hi, t, ht, hrep⟩ := exists_of_coverOK (enumerates_PP hc) hc.cover hzP hz1 hzz
    have hi3 : i < 3 := by simpa using hi
    refine ⟨i, hi3, ?_⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · obtain ⟨c, hcC, hr⟩ := (orbit_facts hc (by norm_num) hc.orbA).1 t (by simpa using ht)
      exact ⟨c, hcC, hrep.perm_eq hr⟩
    · obtain ⟨c, hcC, hr⟩ := (orbit_facts hc (by norm_num) hc.orbB).1 t (by simpa using ht)
      exact ⟨c, hcC, hrep.perm_eq hr⟩
    · obtain ⟨c, hcC, hr⟩ := (orbit_facts hc (by norm_num) hc.orbC).1 t (by simpa using ht)
      exact ⟨c, hcC, hrep.perm_eq hr⟩
  intro z hz
  exact cover_of_sylow Sy S hS hT z hz

theorem gensE_get (IA : Enum) {j : ℕ} (hj : j < pairsE.length) :
    (gensE IA)[j]! = comp 1782 IA.tabs[pairsE[j]!.1]! IA.tabs[pairsE[j]!.2]! := by
  unfold gensE
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos pairsE j hj]
  simp

theorem no_group_in_invE3_of_checked (hc : Checked EP IA IB IC EE)
    (X : Subgroup (Equiv.Perm (Fin 1782))) (hX : X ≤ CC)
    (hcount : 315 ≤ Nat.card {u : ↥X // u * u = 1 ∧ u ≠ 1})
    (hcent : ∀ u : ↥X, u * u = 1 → u ≠ 1 →
      64 ∣ Nat.card (Subgroup.centralizer ({u} : Set ↥X)))
    (h2 : ¬ 128 ∣ Nat.card ↥X) : False := by
  have hrC : ∀ k < 3, repElt k ∈ CC := fun k hk => PP_le_CC hc (repElt_mem_PP hc hk)
  have hA : ∀ u : ↥X, u * u = 1 → u ≠ 1 → (u : Equiv.Perm (Fin 1782)) ∈ Cls 0 := by
    intro u hu hu1
    let u' : ↥CC := ⟨(u : Equiv.Perm (Fin 1782)), hX u.2⟩
    have hu'2 : orderOf u' = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        have := congrArg (fun z : ↥X => (z : Equiv.Perm (Fin 1782))) hu
        simpa [pow_two, u'] using this
      · intro h
        apply hu1
        apply Subtype.ext
        have := congrArg (fun z : ↥CC => (z : Equiv.Perm (Fin 1782))) h
        simpa [u'] using this
    obtain ⟨k, hk, hkcls⟩ := involution_in_cls hc u' hu'2
    have hle : (Subgroup.centralizer ({u} : Set ↥X)).map (Subgroup.inclusion hX) ≤
        Subgroup.centralizer ({u'} : Set ↥CC) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.1 hy
      refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      have := congrArg (fun z : ↥X => (z : Equiv.Perm (Fin 1782))) hy'
      simpa [u'] using this
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hX)] at hdvd
    have h64 := (hcent u hu hu1).trans hdvd
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact hkcls
    · exfalso
      have h := card_centralizer_cls (hrC 1 hk) hkcls
      rw [card_Cls hc hk hc.orbB, hc.sizeB, card_CC] at h
      have h480 : Nat.card (Subgroup.centralizer ({u'} : Set ↥CC)) = 480 := by omega
      rw [h480] at h64
      exact absurd h64 (by norm_num)
    · exfalso
      have h := card_centralizer_cls (hrC 2 hk) hkcls
      rw [card_Cls hc hk hc.orbC, hc.sizeC, card_CC] at h
      have h672 : Nat.card (Subgroup.centralizer ({u'} : Set ↥CC)) = 672 := by omega
      rw [h672] at h64
      exact absurd h64 (by norm_num)
  let f : {u : ↥X // u * u = 1 ∧ u ≠ 1} → ↥(Cls 0) :=
    fun u => ⟨(u.1 : Equiv.Perm (Fin 1782)), hA u.1 u.2.1 u.2.2⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 : (a.1 : Equiv.Perm (Fin 1782)) = b.1 :=
      congrArg (fun z : ↥(Cls 0) => (z : Equiv.Perm (Fin 1782))) h
    exact Subtype.ext (Subtype.ext h1)
  have hCls : Nat.card ↥(Cls 0) = 315 := by
    rw [card_Cls hc (by norm_num) hc.orbA, hc.sizeA]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hCls]; exact hcount)
  have hClsX : ∀ x ∈ Cls 0, x ∈ X := by
    intro x hx
    obtain ⟨⟨u, hu⟩, hux⟩ := hbij.2 ⟨x, hx⟩
    have := congrArg (fun z : ↥(Cls 0) => (z : Equiv.Perm (Fin 1782))) hux
    simp only [f] at this
    rw [← this]
    exact u.2
  have hIA : ∀ a < 315, ∃ x ∈ Cls 0, TabRep IA.tabs[a]! x := by
    intro a ha
    obtain ⟨c, hcC, hr⟩ := (orbit_facts hc (by norm_num) hc.orbA).1 IA.tabs[a]!
      (getElem!_mem (by rw [hc.sizeA]; exact ha))
    exact ⟨_, ⟨c, hcC, rfl⟩, hr⟩
  have hsE : (gensE IA).size = 4 := by simp [gensE, pairsE]
  have hpairs : ∀ p ∈ pairsE, p.1 < 315 ∧ p.2 < 315 := by decide
  have hgensE : ∀ j < (gensE IA).size, ∃ g ∈ X, TabRep (gensE IA)[j]! g := by
    intro j hj
    rw [hsE] at hj
    have hj' : j < pairsE.length := by simpa [pairsE] using hj
    have e := gensE_get IA hj'
    have hp := hpairs (pairsE[j]!) (by rw [getElem!_pos pairsE j hj']; exact List.getElem_mem hj')
    obtain ⟨x, hx, hxr⟩ := hIA _ hp.1
    obtain ⟨y, hy, hyr⟩ := hIA _ hp.2
    exact ⟨x * y, mul_mem (hClsX x hx) (hClsX y hy), by rw [e]; exact hxr.comp hyr⟩
  have hEnum : Enumerates (Subgroup.closure {g | ∃ j < (gensE IA).size, TabRep (gensE IA)[j]! g})
      EE.tabs.toList :=
    enumerates_closure (fun a ha => ha) (fun j hj => by
      obtain ⟨g, -, hg⟩ := hgensE j hj
      exact ⟨g, ⟨j, hj, hg⟩, hg⟩) hc.enumE
  have hle : Subgroup.closure {g | ∃ j < (gensE IA).size, TabRep (gensE IA)[j]! g} ≤ X := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨j, hj, hg⟩
    obtain ⟨g', hg'X, hg'⟩ := hgensE j hj
    rw [hg.perm_eq hg']
    exact hg'X
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hEnum.card, Array.length_toList, hc.sizeE] at hdvd
  exact h2 hdvd

end Main

theorem no_group_in_invE3
    (X : Subgroup (Equiv.Perm (Fin 1782))) (hX : X ≤ CC)
    (hcount : 315 ≤ Nat.card {u : ↥X // u * u = 1 ∧ u ≠ 1})
    (hcent : ∀ u : ↥X, u * u = 1 → u ≠ 1 →
      64 ∣ Nat.card (Subgroup.centralizer ({u} : Set ↥X)))
    (h2 : ¬ 128 ∣ Nat.card ↥X) : False := by
  have h : suzOuterCheck = true := Certificates.certificate27215
  unfold suzOuterCheck at h
  exact no_group_in_invE3_of_checked (checked_of_check h) X hX hcount hcent h2

end CFSG.EvenSporadicStandard.SuzOuter
