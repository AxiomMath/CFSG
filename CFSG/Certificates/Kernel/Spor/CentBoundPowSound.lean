module

public import Certificates.Data.Kernel.Spor.CentBoundPow
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.Certificates.Kernel.Spor.RawSiftK
import all CFSG.Certificates.Kernel.U6Sec3.ProdAll

public section

namespace CFSG.KS.CentBound

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Certificates CFSG.Certificates.ChainArrays
open CFSG.KS.Raw.Orb

theorem cbS_foldl_mul (f : Nat → Nat) : ∀ n : Nat,
    (List.range n).foldl (fun acc t => acc * f t) 1 = ∏ t ∈ Finset.range n, f t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, cbS_foldl_mul f n, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ]

theorem foldUp_count (b : Nat → Bool) (c : Nat) :
    foldUp c (fun k acc => nIf(b k, Nat.succ acc, acc)) (nat_lit 0) =
      ((Finset.range c).filter fun k => b k = true).card := by
  rw [Orb.foldUp_eq, Finset.card_filter]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil, Orb.nIf_eq]
    split_ifs <;> omega

theorem ubPowK_sound {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : G = Raw.Orb.Gen n S kO)
    {L : Nat} {RS : Nat → Nat} {ρ : Nat → Equiv.Perm (Fin n)}
    (hr : ∀ l < L, Raw.Orb.PRep n w (RS l) (ρ l)) {O : Nat → Nat → Nat}
    (h : ubPowOkK n w (mask w) PS PSI kS BP nb L RS O = true) :
    Nat.card ↥(G ⊓ Subgroup.centralizer (ρ '' {l | l < L})) ≤
      ubPowProdK n w (mask w) (n * w) LR TRI nb L RS O := by
  have hraw := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  have hF := chainCheckFacts hraw
  obtain ⟨hk, hH⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hd := Raw.Orb.hd_of_head hk hH
  obtain ⟨hp, -, hkS⟩ := Raw.Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbt : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hcard : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod := by
    rw [prod_sizes]
    let F : ((j : Fin base.size) → Fin (lev n S base j).pts.size) → Equiv.Perm (Fin n) :=
      fun κ => ((List.range base.size).map fun j =>
        levT n S base j (if hj : j < base.size then (κ ⟨j, hj⟩ : Nat) else 0)).prod
    have hsub : ((Gen n S kO : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) ⊆
        Set.range F := by
      intro x hx
      have hx' : x ∈ Subgroup.closure (permsA n (S.extract 0 kO)) := by
        refine (Subgroup.closure_le _).2 ?_ hx
        rintro _ ⟨j, rfl⟩
        have hj0 : j.val < (S.extract 0 kO).size := by simp [Array.size_extract]; omega
        refine Subgroup.subset_closure ⟨j.val, hj0, ?_⟩
        change permOfArr n (S.extract 0 kO)[j.val]! = permOfArr n S[j.val]!
        rw [getElem!_pos (S.extract 0 kO) j.val hj0, Array.getElem_extract,
          getElem!_pos S j.val (by omega)]
        simp
      obtain ⟨κ, hκ, e⟩ := CFSG.KC.U6Sec3.ProdPf.decomp hF hx'
      refine ⟨fun j => ⟨κ j, hκ j j.2⟩, ?_⟩
      rw [e]
      exact congrArg List.prod (List.map_congr_left fun j hj => by
        rw [dif_pos (List.mem_range.1 hj)])
    calc Nat.card (Gen n S kO) ≤ Nat.card (Set.range F) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card ((j : Fin base.size) → Fin (lev n S base j).pts.size) := Finite.card_range_le F
      _ = ∏ i ∈ Finset.range base.size, (lev n S base i).pts.size := by
        rw [Nat.card_pi]
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
        exact Fin.prod_univ_eq_prod_range (fun i => (lev n S base i).pts.size) base.size
  set Z := Subgroup.centralizer (ρ '' {l | l < L}) with hZ
  set Pass : Nat → Finset Nat := fun i => (Finset.range (rcnt (LR i))).filter fun k =>
    allN L (fun l => hasBit (O l i) (pg w (mask w) (TRI (Nat.add (roff n (n * w) (LR i)) k))
      (pg w (mask w) (RS l) (rpt w (mask w) (LR i) k)))) = true with hPass
  have hcnt : ∀ i, ubCntLK n w (mask w) (n * w) TRI (LR i) L RS (fun l => O l i) = (Pass i).card := by
    intro i
    unfold ubCntLK
    rw [Orb.strictN_eq, Orb.strictN_eq]
    exact foldUp_count (fun k => allN L fun l => hasBit (O l i)
      (pg w (mask w) (TRI (Nat.add (roff n (n * w) (LR i)) k))
        (pg w (mask w) (RS l) (rpt w (mask w) (LR i) k)))) _
  have step : ∀ i < nb, Nat.card ↥(Fix n S kO base i ⊓ Z) ≤
      (Pass i).card * Nat.card ↥(Fix n S kO base (i + 1) ⊓ Z) := by
    intro i hi
    have hib : i < base.size := hbs ▸ hi
    set bi : Fin n := ⟨base[i]!, hd.base_lt i hib⟩ with hbi
    obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    have hclos : ∀ l < L, ∀ g ∈ CFSG.KC.U6Sec3.ProdPf.H n S base (i + 1),
        hasBit (O l i) ((g (ρ l bi) : Fin n) : Nat) = true := by
      intro l hlL g hg
      have hok : closK n w (mask w) PS PSI kS (stepsAt n w PS kS BP (i + 1)) (O l i)
          (pg w (mask w) (RS l) (pg w (mask w) BP i)) = true :=
        Orb.allN_iff.1 (Orb.allN_iff.1 h l hlL) i hi
      unfold closK at hok
      rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff] at hok
      obtain ⟨h0, hcl⟩ := hok
      obtain ⟨hcnt', hstp, -, -⟩ := Raw.Orb.kernel_steps hb hp hkS hbl (i := i + 1) (by omega)
      have hst : ∀ x : Fin n, hasBit (O l i) (x : Nat) = true →
          ∀ j < (rawSteps n S base (i + 1)).size,
            hasBit (O l i) ((stp n S base (i + 1) j x : Fin n) : Nat) = true := by
        intro x hx j hj
        have e := hcl x x.2
        rw [Orb.bIf_eq, if_pos hx, Orb.allN_iff] at e
        have e2 := e j (by rw [hcnt']; exact hj)
        rwa [hstp j hj x] at e2
      have e0 : pg w (mask w) (RS l) (pg w (mask w) BP i) = ((ρ l bi : Fin n) : Nat) := by
        rw [← hbt i hi]
        exact hr l hlL bi
      rw [e0] at h0
      refine Subgroup.closure_induction_left
        (p := fun g _ => hasBit (O l i) ((g (ρ l bi) : Fin n) : Nat) = true) h0 ?_ ?_ hg
      · intro s hs y _ hy
        obtain ⟨j, hj, hrj⟩ := (CFSG.KC.U6Sec3.ProdPf.gen_step hF hs).1
        have e := Rep.unique hrj (Raw.Orb.rep_stp hb hp hj)
        rw [Equiv.Perm.mul_apply, e]
        exact hst _ hy j hj
      · intro s hs y _ hy
        obtain ⟨j, hj, hrj⟩ := (CFSG.KC.U6Sec3.ProdPf.gen_step hF hs).2
        have e := Rep.unique hrj (Raw.Orb.rep_stp hb hp hj)
        rw [Equiv.Perm.mul_apply, e]
        exact hst _ hy j hj
    have key : ∀ c ∈ Fix n S kO base i ⊓ Z, ∃ k, k ∈ Pass i ∧
        ((c bi : Fin n) : Nat) = (lev n S base i).pts[k]! := by
      intro c hc
      obtain ⟨hcF, hcZ⟩ := Subgroup.mem_inf.1 hc
      obtain ⟨k, hk, hck⟩ := fix_surj hd hcard hib hcF
      have hkc : k < rcnt (LR i) := A.cnt ▸ hk
      have hT := tr_spec hd hib k hk
      have eT : permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k))) = trP n S base i k :=
        Rep.unique (A.tr k hk).1 (rep_tr hd hib hk)
      have hTI : PRep n w (TRI (Nat.add (roff n (n * w) (LR i)) k)) (trP n S base i k)⁻¹ := by
        rw [← eT]
        exact (P k hkc).2
      have hu : (trP n S base i k)⁻¹ * c ∈ Fix n S kO base (i + 1) := by
        have hTi := Subgroup.inv_mem _ hT.1
        refine ⟨Subgroup.mul_mem _ hTi.1 hcF.1, fun t ht hbt' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · rw [Equiv.Perm.mul_apply, hcF.2 t ht hbt', hTi.2 t ht hbt']
        · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
          apply Fin.ext
          rw [hT.2]
          exact hck
      have hu' : (trP n S base i k)⁻¹ * c ∈ CFSG.KC.U6Sec3.ProdPf.H n S base (i + 1) := by
        have hrep : Rep n (Array.ofFn (n := n) fun x => ((((trP n S base i k)⁻¹ * c) x : Fin n) :
            Nat)) ((trP n S base i k)⁻¹ * c) := fun z => getElem!_ofFn_nat _ z.2
        exact CFSG.KC.U6Sec3.ProdPf.mem_of_sift hF (by omega) hrep
          (siftA_fix hd hcard (base.size - (i + 1)) (i + 1) (by omega) _ _ hrep hu)
      refine ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hkc, Orb.allN_iff.2 fun l hlL => ?_⟩,
        hck⟩
      beta_reduce
      have hcomm : ρ l * c = c * ρ l := Subgroup.mem_centralizer_iff.1 hcZ (ρ l) ⟨l, hlL, rfl⟩
      have e1 : rpt w (mask w) (LR i) k = ((c bi : Fin n) : Nat) := (A.pt k hk).trans hck.symm
      have e3 : (trP n S base i k)⁻¹ (ρ l (c bi)) = ((trP n S base i k)⁻¹ * c) (ρ l bi) := by
        rw [← Equiv.Perm.mul_apply (ρ l) c, hcomm]
        rfl
      rw [e1, hr l hlL (c bi), hTI (ρ l (c bi)), e3]
      exact hclos l hlL _ hu'
    choose! kf hkP hkE using key
    have hR : ∀ k, ∃ r : Equiv.Perm (Fin n),
        (∃ c ∈ Fix n S kO base i ⊓ Z, kf c = k) → r ∈ Fix n S kO base i ⊓ Z ∧ kf r = k := by
      intro k
      by_cases hx : ∃ c ∈ Fix n S kO base i ⊓ Z, kf c = k
      · obtain ⟨c, hc, e⟩ := hx
        exact ⟨c, fun _ => ⟨hc, e⟩⟩
      · exact ⟨1, fun h' => absurd h' hx⟩
    choose rep hrep using hR
    have hmem : ∀ c ∈ Fix n S kO base i ⊓ Z,
        (rep (kf c))⁻¹ * c ∈ Fix n S kO base (i + 1) ⊓ Z := by
      intro c hc
      obtain ⟨hr1, hr2⟩ := hrep (kf c) ⟨c, hc, rfl⟩
      obtain ⟨hcF, hcZ⟩ := Subgroup.mem_inf.1 hc
      obtain ⟨hrF, hrZ⟩ := Subgroup.mem_inf.1 hr1
      have himg : rep (kf c) bi = c bi := Fin.ext (by rw [hkE _ hr1, hr2, ← hkE c hc])
      have hri := Subgroup.inv_mem _ hrF
      refine Subgroup.mem_inf.2 ⟨⟨Subgroup.mul_mem _ hri.1 hcF.1, fun t ht hbt' => ?_⟩,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hrZ) hcZ⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [Equiv.Perm.mul_apply, hcF.2 t ht hbt', hri.2 t ht hbt']
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        exact himg.symm
    let f : ↥(Fix n S kO base i ⊓ Z) → ↥(Pass i) × ↥(Fix n S kO base (i + 1) ⊓ Z) :=
      fun c => (⟨kf c, hkP c c.2⟩, ⟨(rep (kf c))⁻¹ * c, hmem c c.2⟩)
    have hf : Function.Injective f := by
      rintro ⟨a, ha⟩ ⟨b, hb'⟩ e
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      rw [e1] at e2
      exact Subtype.ext (mul_left_cancel e2)
    have hle := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_finsetCard] at hle
  have hlast : Nat.card ↥(Fix n S kO base nb ⊓ Z) ≤ 1 := by
    have hle : Fix n S kO base nb ⊓ Z ≤ ⊥ := fun x hx => by
      have hx1 := (Subgroup.mem_inf.1 hx).1
      rw [← hbs] at hx1
      exact Subgroup.mem_bot.2 (fix_one hd hcard hx1)
    exact (Subgroup.card_le_of_le hle).trans Subgroup.card_bot.le
  have chain : ∀ d i, i + d = nb →
      Nat.card ↥(Fix n S kO base i ⊓ Z) ≤ ∏ j ∈ Finset.Ico i nb, (Pass j).card := by
    intro d
    induction d with
    | zero =>
      intro i hi
      obtain rfl : i = nb := by omega
      rw [Finset.Ico_self, Finset.prod_empty]
      exact hlast
    | succ d ih =>
      intro i hi
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : i < nb)]
      exact (step i (by omega)).trans (Nat.mul_le_mul_left _ (ih (i + 1) (by omega)))
  have hprod : ubPowProdK n w (mask w) (n * w) LR TRI nb L RS O =
      ∏ j ∈ Finset.range nb, (Pass j).card := by
    have e : (fun acc i => Nat.mul acc (ubCntLK n w (mask w) (n * w) TRI (LR i) L RS
        (fun l => O l i))) = fun acc t => acc * (Pass t).card :=
      funext fun acc => funext fun t => by rw [hcnt t]; rfl
    rw [← cbS_foldl_mul]
    unfold ubPowProdK
    rw [Orb.foldUp_eq]
    exact congrArg (fun f => List.foldl f 1 (List.range nb)) e
  rw [hprod, Finset.range_eq_Ico, hG, ← Fix_zero (base := base)]
  exact chain nb 0 (Nat.zero_add nb)

end CFSG.KS.CentBound

end
