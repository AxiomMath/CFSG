module

public import CFSG.Sporadic.FischerOddCore.RefineSpec
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefineInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative

variable {n : ℕ} {nbr : Array (List ℕ)} {t c0 : Array ℕ} {T σ : Equiv.Perm (Fin n)}

theorem initX_map (ht : Rep n t T) (hcomm : σ * T = T * σ) (hc0 : ColMap n c0 c0 σ)
    {pre : List ℕ} (hpre : ∀ x ∈ pre, x < n) :
    ColMap n (initX n t c0 pre) (initX n t c0 (pre.map (permNat σ))) σ := by
  intro v
  unfold initX
  rw [getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only [List.length_map]
  rw [hc0 v, initT_map ht hcomm hpre v]

theorem colourX_map (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (hσ : NbrInv nbr σ)
    (ht : Rep n t T) (hcomm : σ * T = T * σ) (hc0 : ColMap n c0 c0 σ) {pre : List ℕ}
    (hpre : ∀ x ∈ pre, x < n) (k : ℕ) :
    ColMap n (colourX n nbr t c0 pre k) (colourX n nbr t c0 (pre.map (permNat σ)) k) σ :=
  refineT_map hnbr hσ ht hcomm (initX_map ht hcomm hc0 hpre) k

theorem card_le_of_boundsXOK {K : Subgroup (Equiv.Perm (Fin n))} [Finite K]
    (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (ht : Rep n t T) {pre0 : List ℕ}
    (hK : ∀ σ ∈ K, NbrInv nbr σ ∧ σ * T = T * σ ∧ ColMap n c0 c0 σ ∧
      pre0.map (permNat σ) = pre0)
    (hn : 0 < n) {pts bounds : List ℕ} {k : ℕ} (hpre : ∀ x ∈ pre0, x < n)
    (hpts : ∀ x ∈ pts, x < n) (hok : boundsXOK n nbr t c0 pre0 pts bounds k = true) :
    Nat.card K ≤ bounds.prod := by
  rw [boundsXOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hlen, hcells⟩, hinj⟩ := hok
  have hmap : ∀ s ≤ pts.length, ∀ σ ∈ stabChain (G := K) (ptsPt n hn pts) s,
      ColMap n (colourX n nbr t c0 (pre0 ++ pts.take s) k)
        (colourX n nbr t c0 (pre0 ++ pts.take s) k) (σ : Equiv.Perm (Fin n)) := by
    intro s hs σ hσ
    have hfix : ∀ j < s, (σ : Equiv.Perm (Fin n)) (ptsPt n hn pts j) = ptsPt n hn pts j :=
      fun j hj => (mem_stabChain.1 hσ) j hj
    obtain ⟨h1, h2, h3, h4⟩ := hK _ σ.2
    have h := colourX_map hnbr h1 ht h2 h3 (pre := pre0 ++ pts.take s)
      (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hpre x hx
        · exact hpts x (List.mem_of_mem_take hx)) k
    rwa [List.map_append, h4, take_map_permNat hpts hs hfix] at h
  have horb : ∀ s < pts.length, (MulAction.orbit (stabChain (G := K) (ptsPt n hn pts) s)
      (ptsPt n hn pts s)).ncard ≤ bounds.getD s 0 := by
    intro s hs
    have hc := allLt_spec hcells hs
    rw [beq_iff_eq, cellCount_eq] at hc
    rw [← hc]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨σ, rfl⟩
    have e := hmap s hs.le σ σ.2 (ptsPt n hn pts s)
    rw [← ptsPt_val hpts hs]
    exact e
  have htriv : stabChain (G := K) (ptsPt n hn pts) pts.length = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Equiv.ext
    intro v
    have e := hmap pts.length le_rfl σ hσ v
    rw [List.take_length] at e
    exact colInj_injective hinj e
  have h := card_le_prod_of_stabChain (G := K) (ptsPt n hn pts) (fun s => bounds.getD s 0)
    pts.length horb htriv
  refine h.trans (le_of_eq ?_)
  rw [hlen]
  clear h horb htriv hmap hcells hinj hlen
  induction bounds using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ, List.prod_append,
      List.prod_singleton, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero]
    congr 1
    rw [← ih]
    apply Finset.prod_congr rfl
    intro s hs
    rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hs)]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
