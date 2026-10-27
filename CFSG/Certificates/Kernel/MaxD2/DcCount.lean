module

public import CFSG.Certificates.Kernel.MaxD2.Count
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Certificates.Data.Kernel.MaxD2.Heis

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

section

variable {n : Nat}

theorem tabRep_of_perm {w p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    ∃ σ : Equiv.Perm (Fin n), TabRep (unpack n w p) σ ∧ TabRep (unpack n w q) σ⁻¹ := by
  have hs := perm_spec h
  let σ : Equiv.Perm (Fin n) :=
    { toFun := fun i => ⟨pg w (mask w) p i, (hs.1 i i.2).1⟩
      invFun := fun j => ⟨pg w (mask w) q j, (hs.2 j j.2).1⟩
      left_inv := fun i => Fin.ext (hs.1 i i.2).2
      right_inv := fun j => Fin.ext (hs.2 j j.2).2 }
  exact ⟨σ, ⟨size_u _, fun i => get_u i.2⟩, ⟨size_u _, fun j => get_u j.2⟩⟩

theorem mem_tabs_iff {H : Subgroup (Equiv.Perm (Fin n))} {T : Array Tab}
    (hH : Enumerates H T.toList) {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    (∃ m < T.size, T[m]! = t) ↔ g ∈ H := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨g', hg', hr⟩ := hH.exists_elt hm
    rwa [ht.perm_eq hr]
  · intro hg
    obtain ⟨k, hk, hr⟩ := hH.exists_pos hg
    exact ⟨k, hk, hr.tab_eq ht⟩

theorem countBelow_tabs (T : Array Tab) (p : Tab → Bool) :
    countBelow T.size (fun k => p T[k]!) = (T.toList.filter p).length := by
  have h : (List.range T.size).map (fun k => T[k]!) = T.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos T i (by simpa using h1)]
      simp
  rw [← h, List.filter_map, List.length_map]
  rfl

theorem conjCount_card {H : Subgroup (Equiv.Perm (Fin n))} {pts : List Nat} {T : Array Tab}
    (hH : Enumerates H T.toList)
    (hinj : ∀ a < T.size, ∀ b < T.size, fpTab pts T[a]! = fpTab pts T[b]! → a = b)
    {x xi : Tab} {σ : Equiv.Perm (Fin n)} (hx : TabRep x σ) (hxi : TabRep xi σ⁻¹) :
    conjCount n pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T xi x =
      Nat.card ↥(H ⊓ H.comap (MulAut.conj σ⁻¹).toMonoidHom) := by
  unfold conjCount
  rw [countBelow_tabs T (fun t => memFp pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T
    (comp n (comp n xi t) x))]
  have hf := hH.filter (K := H.comap (MulAut.conj σ⁻¹).toMonoidHom)
    (fun t => memFp pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T
      (comp n (comp n xi t) x)) (by
    intro t a ht
    rw [memFp_iff hinj, mem_tabs_iff hH ((hxi.comp ht).comp hx)]
    simp [Subgroup.mem_comap])
  rw [← hf.card, inf_comm]

theorem card_conjStab_dc {H : Subgroup (Equiv.Perm (Fin n))} {σ τ α β : Equiv.Perm (Fin n)}
    (hα : α ∈ H) (hβ : β ∈ H) (e : σ⁻¹ * α * τ = β) :
    Nat.card ↥(H ⊓ H.comap (MulAut.conj τ⁻¹).toMonoidHom) =
      Nat.card ↥(H ⊓ H.comap (MulAut.conj σ⁻¹).toMonoidHom) := by
  have hτ : τ = α⁻¹ * σ * β := by
    rw [← e]
    group
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj α).toEquiv fun a => ?_)
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  have e1 : τ⁻¹ * a * τ = β⁻¹ * (σ⁻¹ * (α * a * α⁻¹) * σ) * β := by
    rw [hτ]
    group
  rw [e1]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨H.mul_mem (H.mul_mem hα ha) (H.inv_mem hα), ?_⟩
    have e2 : σ⁻¹ * (α * a * α⁻¹) * σ = β * (β⁻¹ * (σ⁻¹ * (α * a * α⁻¹) * σ) * β) * β⁻¹ := by
      group
    rw [e2]
    exact H.mul_mem (H.mul_mem hβ hc) (H.inv_mem hβ)
  · rintro ⟨ha, hc⟩
    have e3 : a = α⁻¹ * (α * a * α⁻¹) * α := by group
    refine ⟨?_, H.mul_mem (H.mul_mem (H.inv_mem hβ) hc) hβ⟩
    rw [e3]
    exact H.mul_mem (H.mul_mem (H.inv_mem hα) ha) hα

theorem conjCount_dc {H : Subgroup (Equiv.Perm (Fin n))} {pts : List Nat} {T : Array Tab}
    (hH : Enumerates H T.toList)
    (hinj : ∀ a < T.size, ∀ b < T.size, fpTab pts T[a]! = fpTab pts T[b]! → a = b)
    {x xi y yi a b : Tab} {σ τ α β : Equiv.Perm (Fin n)} (hx : TabRep x σ) (hxi : TabRep xi σ⁻¹)
    (hy : TabRep y τ) (hyi : TabRep yi τ⁻¹) (ha : TabRep a α) (hα : α ∈ H) (hb : TabRep b β)
    (hβ : β ∈ H) (e : comp n (comp n xi a) y = b) :
    conjCount n pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T yi y =
      conjCount n pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T xi x := by
  rw [conjCount_card hH hinj hx hxi, conjCount_card hH hinj hy hyi]
  refine card_conjStab_dc hα hβ ?_
  have h := (hxi.comp ha).comp hy
  rw [e] at h
  exact h.perm_eq hb

end

section

variable {D : Data} {K : Pk}

@[expose] def nSub (D : Data) (n : Nat) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ j < (nGens D).size, TabRep (nGens D)[j]! g}

theorem c_enumN (H : HypsC D K) : Enumerates (nSub D K.n) (nEnum D).tabs.toList := by
  obtain ⟨e, hok⟩ := c_nEnum_eq H
  rw [e]
  refine enumerates_closure (fun a ha => ha) (fun j hj => ?_) hok
  have hs : (nGens D).size = K.kN := (c_ngens H).1
  have hj' : j < K.kN := by rw [← hs]; exact hj
  obtain ⟨σ, hσ, -⟩ := tabRep_of_perm (H.hNI j hj')
  rw [← c_ng_get H hj'] at hσ
  exact ⟨σ, ⟨j, hj, hσ⟩, hσ⟩

theorem c_cnt_dc (H : HypsC D K) {i j k m : Nat} (hi : i < K.nr) (hj : j < K.nr) (hk : k < K.cnt)
    (hm : m < K.cnt)
    (em : K.NT m = pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.REPI i) (K.NT k))
      (K.REP j)) :
    (if i = 0 then K.cnt else K.CN i) = (if j = 0 then K.cnt else K.CN j) := by
  rw [← c_conjCount_eq H hi, ← c_conjCount_eq H hj, c_repi_get H hi, c_rep_get H hi,
    c_repi_get H hj, c_rep_get H hj, H.hDn]
  have hE := c_enumN H
  obtain ⟨σ, hσ, hσi⟩ := tabRep_of_perm (H.hRi i hi)
  obtain ⟨τ, hτ, hτi⟩ := tabRep_of_perm (H.hRi j hj)
  obtain ⟨α, hα, ha⟩ := hE.exists_elt (by rw [c_nT_size H]; exact hk)
  obtain ⟨β, hβ, hb⟩ := hE.exists_elt (by rw [c_nT_size H]; exact hm)
  rw [c_nT_get H hk] at ha
  rw [c_nT_get H hm] at hb
  have hri := c_rep_perm H hi
  have hrj := c_rep_perm H hj
  have hnk := c_nt_canon H hk
  refine (conjCount_dc hE (c_fp_inj H) hσ hσi hτ hτi ha hα hb hβ ?_).symm
  rw [comp_u hri.2 hnk, comp_u (cc hri.2 hnk) hrj.1, em]

structure HypsBC (D : Data) (K : Pk) : Prop extends HypsC D K where
  hSum : (List.range K.nr).foldl
    (fun s i => s + D.nOrder * D.nOrder / (if i = 0 then K.cnt else K.CN i)) 0 = D.gOrder
  hL : labK K.n K.w K.kN K.NG K.L = true
  hM : K.n ≤ 64 * K.hi
  hMK : ∀ i < K.nr, K.MK i = mkeyK K.n K.w K.hi K.cw K.nl K.L (K.REP i)
  hMd : ∀ i < K.nr, ∀ j < K.nr, i < j → K.MK i ≠ K.MK j ∨
    (if i = 0 then K.cnt else K.CN i) ≠ (if j = 0 then K.cnt else K.CN j) ∨
    pairK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB2 K.H2 (K.PQ i j) i j =
      true

theorem cc_dcSum_of (H : HypsBC D K) :
    dcSum D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder := by
  unfold dcSum
  rw [← H.hSum, c_rep_size H.toHypsC]
  refine foldl_congr_range (fun s i hi => ?_) 0
  rw [c_conjCount_eq H.toHypsC hi]

theorem cc_disj_spec (H : HypsBC D K) {i j k : Nat} (hi : i < K.nr) (hj : j < K.nr) (hij : i < j)
    (hk : k < K.cnt) : ¬ ∃ m < K.cnt, K.NT m =
      pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.REPI i) (K.NT k)) (K.REP j) := by
  have hn := H.hn
  have hLP := enum_facts hn H.hNh H.hNp H.hNI H.hL
  rintro ⟨m, hm', em⟩
  have hj' := perm_spec (H.hRi j hj)
  rcases H.hMd i hi j hj hij with hd | hc | hp
  · have key := mkey_eq hn (hi := K.hi) (cw := K.cw) (nl := K.nl) H.hM (H.hRi i hi)
      (fun y hy => (hj'.1 y hy).1) (hLP k hk) (hLP m hm') (fun y hy => by
        rw [em, pg_pc hn hy, pg_pc hn ((hj'.1 y hy).1)])
    rw [← H.hMK j hj, ← H.hMK i hi] at key
    exact hd key.symm
  · exact hc (c_cnt_dc H.toHypsC hi hj hk hm' em)
  · exact pairK_spec hn (fun _ he => c_nt_canon H.toHypsC he) H.hS
      (fun t ht => (H.hPts.2 t ht).2) (fun y hy => (hj'.1 y hy).1) hk hp ⟨m, hm', em⟩

theorem cc_dcDisjoint_of (H : HypsBC D K) :
    dcDisjoint D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = true := by
  have HC := H.toHypsC
  unfold dcDisjoint
  rw [allBelow_iff']
  intro i hi
  rw [allBelow_iff']
  intro j hj
  rw [c_rep_size HC] at hi hj
  rw [Bool.or_eq_true]
  by_cases hij : i < j
  · right
    rw [allBelow_iff']
    intro k hk
    rw [c_nT_size HC] at hk
    have hri := c_rep_perm HC hi
    have hrj := c_rep_perm HC hj
    have ha := c_nt_canon HC hk
    rw [c_repi_get HC hi, c_rep_get HC hj, c_nT_get HC hk, H.hDn, comp_u hri.2 ha,
      comp_u (cc hri.2 ha) hrj.1, Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    exact cc_disj_spec H hi hj hij hk ((c_memN_iff HC (cc (cc hri.2 ha) hrj.1)).1 hm)
  · left
    simpa using hij

end

theorem md_of_sel {nr np2 : Nat} {MK CN PQ PI PJ : Nat → Nat} {P : Nat → Nat → Nat → Bool}
    (hs : selK nr np2 MK CN PQ PI PJ = true) (hp : ∀ q < np2, P q (PI q) (PJ q) = true) :
    ∀ i < nr, ∀ j < nr, i < j →
      MK i ≠ MK j ∨ CN i ≠ CN j ∨ P (PQ (j * (j - 1) / 2 + i)) i j = true := by
  intro i _ j hj hij
  unfold selK at hs
  have h := (PK.allN_iff.1 ((PK.allN_iff.1 hs) j hj)) i hij
  by_cases h1 : Nat.beq (MK i) (MK j) = true
  · have h' := bif_t h1 h
    by_cases h2 : Nat.beq (CN i) (CN j) = true
    · have h'' := bif_t h2 h'
      rw [PK.strictB_eq] at h''
      obtain ⟨hq, h3⟩ := band_e h''
      obtain ⟨hi', hj'⟩ := band_e h3
      right
      right
      have e := hp _ (Nat.blt_eq.mp hq)
      rwa [Nat.eq_of_beq_eq_true hi', Nat.eq_of_beq_eq_true hj'] at e
    · right
      left
      intro e
      rw [e, Nat.beq_refl] at h2
      exact h2 rfl
  · left
    intro e
    rw [e, Nat.beq_refl] at h1
    exact h1 rfl

end CFSG.KS.MaxD2

end
