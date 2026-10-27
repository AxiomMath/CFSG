module

public import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.SiftKComplete
import CFSG.Certificates.Kernel.Spor.PackFld
import all CFSG.Certificates.Kernel.U6Sec3.ProdAll

public section

namespace CFSG.KC.J2Enum.GrpPf

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Certificates CFSG.Certificates.ChainArrays

private theorem eq_one_of_siftA {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {c : ℕ} (hF : ChainCheckFacts n O S base W c) :
    ∀ d l, l + d = base.size → ∀ (a : Array ℕ) (g : Equiv.Perm (Fin n)), Rep n a g →
      siftA n (rawLevels n S base) base l a = true →
      (∀ t, l ≤ t → t < base.size → ∀ h : base[t]! < n, g ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) →
      g = 1 := by
  intro d
  induction d with
  | zero =>
    intro l hl a g ha h _
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega), eqA_iff ha rep_idA] at h
    exact h
  | succ d ih =>
    intro l hl a g ha h hfix
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    have F := CFSG.KC.U6Sec3.ProdPf.facts hF hlb
    have hb : base[l]! < n := hF.base_lt l hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, h⟩ := h
    have hpos : (lev n S base l).pos[a[base[l]!]!]! = 0 := by
      rw [ha.apply hb, hfix l le_rfl hlb hb]
      show (lev n S base l).pos[base[l]!]! = 0
      rw [← F.root, F.pos_pts 0 F.pos]
    rw [hpos] at h
    have hT := (CFSG.KC.U6Sec3.ProdPf.rep_T hF hlb F.pos).2
    rw [CFSG.KC.U6Sec3.ProdPf.T_zero hF hlb, inv_one] at hT
    have hr := rep_compA hT ha
    rw [one_mul] at hr
    exact ih (l + 1) (by omega) _ g hr h fun t ht ht' hbt => hfix t (by omega) ht' hbt

private theorem rep_of_siftA {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {c : ℕ} (hF : ChainCheckFacts n O S base W c) :
    ∀ d l, l + d = base.size → ∀ g : Array ℕ, (∀ i < n, g[i]! < n) →
      siftA n (rawLevels n S base) base l g = true → ∃ γ, Rep n g γ := by
  intro d
  induction d with
  | zero =>
    intro l hl' g _ h
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)] at h
    refine ⟨1, fun x => ?_⟩
    have := allLt_spec h x.2
    rw [beq_iff_eq, idA_get x.2] at this
    exact this
  | succ d ih =>
    intro l hl' g hg h
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    have rI := (CFSG.KC.U6Sec3.ProdPf.rep_T hF hlb hk).2
    obtain ⟨γ', hγ'⟩ := ih (l + 1) (by omega) _ (fun i hi => by
      rw [compA_get hi]
      exact rI.lt (hg i hi)) h
    refine ⟨levT n S base l ((lev n S base l).pos[g[base[l]!]!]!) * γ', fun x => ?_⟩
    have e1 := hγ' x
    rw [compA_get x.2] at e1
    have e2 : γ' x = (levT n S base l ((lev n S base l).pos[g[base[l]!]!]!))⁻¹
        ⟨g[(x : ℕ)]!, hg x x.2⟩ :=
      Fin.ext (by rw [← e1, rI.apply (hg x x.2)])
    rw [Equiv.Perm.mul_apply, e2]
    simp

private theorem fixesFirst_zero (base t : Array ℕ) : fixesFirst base t 0 = true := by
  unfold fixesFirst
  exact allLt_iff.2 fun k hk => absurd hk (Nat.not_lt_zero _)

theorem group3 {n w kS kO BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    (∀ γ ∈ Raw.Orb.Gen n S kO,
      (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1) ∧
    (∀ j < 3, ∀ k < rcnt (LR j),
      canonK n w (mask w) (n * w) (TR (roff n (n * w) (LR j) + k)) = true ∧
        ∃ γ ∈ Raw.Orb.Gen n S kO, Raw.Orb.PRep n w (TR (roff n (n * w) (LR j) + k)) γ) ∧
    (∀ X, canonK n w (mask w) (n * w) X = true →
      (siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 X = true ↔
        ∃ γ ∈ Raw.Orb.Gen n S kO, Raw.Orb.PRep n w X γ)) ∧
    ∀ t < 3, pg w (mask w) BP t < n := by
  have hp := (Raw.Orb.head_facts hh).1
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = 3 := hb.2.2.2.2.2.1
  have hbt : ∀ t < 3, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hraw := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  have hF := chainCheckFacts hraw
  obtain ⟨hk, hH⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hd := Raw.Orb.hd_of_head hk hH
  have hGH : Raw.Orb.Gen n S kO = CFSG.KC.U6Sec3.ProdPf.H n S base 0 := by
    apply le_antisymm
    · rw [Raw.Orb.Gen, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨j.val, by have := j.2; omega, fixesFirst_zero _ _, rfl⟩
    · rw [CFSG.KC.U6Sec3.ProdPf.H, Subgroup.closure_le]
      rintro _ ⟨j, hj, -, rfl⟩
      exact Raw.Orb.S_mem_Gen hd j hj
  refine ⟨fun γ hγ hfix => ?_, fun j hj k hk => ?_, fun X hX => ?_,
    fun t ht => hbt t ht ▸ hbl t ht⟩
  · rw [hGH] at hγ
    have ha : Rep n (Array.ofFn (n := n) fun i => (γ i : ℕ)) γ := fun z =>
      getElem!_ofFn_nat _ z.2
    have hsA := CFSG.KC.U6Sec3.ProdPf.sift_complete hF base.size 0 (by simp) _ _ ha hγ
    have key : ∀ (x : ℕ) (h1 : x < n) (y : ℕ) (h2 : y < n), x = y →
        (γ ⟨y, h2⟩ = ⟨y, h2⟩ → γ ⟨x, h1⟩ = ⟨x, h1⟩) := by
      rintro x h1 y h2 rfl
      exact id
    refine eq_one_of_siftA hF base.size 0 (by simp) _ _ ha hsA fun t _ ht hb' => ?_
    rw [hbs] at ht
    exact key _ hb' _ (hbt t ht ▸ hb') (hbt t ht) (hfix t ht _)
  · have hk' : k < (lev n S base j).pts.size := by
      rw [← (Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hj (hl j hj)).1.cnt]
      exact hk
    obtain ⟨-, hcan, hpg⟩ := CFSG.KC.U6Sec3.ProdPf.kernel_T hb hp hl hF hj hk'
    refine ⟨hcan, levT n S base j k, ?_, fun z => hpg z⟩
    rw [hGH]
    exact CFSG.KC.U6Sec3.ProdPf.H_anti (Nat.zero_le j) (CFSG.KC.U6Sec3.ProdPf.T_mem hF (by omega) k hk')
  · obtain ⟨-, -, hX0, hXr⟩ := PF.canon_facts hX
    have hr : allN n (fun i => Nat.blt (pg w (mask w) X i) n) = true :=
      PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hXr i hi)
    constructor
    · intro h
      have hsA := siftK_sound hb hp hl rfl hr h
      obtain ⟨γ, hγ⟩ := rep_of_siftA hF base.size 0 (by simp) _
        (fun i hi => by rw [Raw.Orb.unpack_get hi]; exact hXr i hi) hsA
      refine ⟨γ, ?_, fun z => by rw [← Raw.Orb.unpack_get z.2]; exact hγ z⟩
      rw [hGH]
      exact CFSG.KC.U6Sec3.ProdPf.mem_of_sift hF (Nat.zero_le _) hγ hsA
    · rintro ⟨γ, hγ, hP⟩
      rw [hGH] at hγ
      exact Raw.Orb.siftK_of_siftA hb hp hl rfl hX0 hr
        (CFSG.KC.U6Sec3.ProdPf.sift_complete hF base.size 0 (by simp) _ _ (Raw.Orb.rep_unpack hP) hγ)

theorem enum3 {n w kS kO BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    (∀ j < 3, ∀ k < rcnt (LR j), levT n S base j k ∈ Raw.Orb.Gen n S kO ∧
      Raw.Orb.PRep n w (TR (roff n (n * w) (LR j) + k)) (levT n S base j k)) ∧
    (∀ x ∈ Raw.Orb.Gen n S kO, ∃ a < rcnt (LR 0), ∃ b < rcnt (LR 1), ∃ c < rcnt (LR 2),
      x = levT n S base 0 a * levT n S base 1 b * levT n S base 2 c) ∧
    ∀ a < rcnt (LR 0), ∀ a' < rcnt (LR 0), ∀ b < rcnt (LR 1), ∀ b' < rcnt (LR 1),
      ∀ c < rcnt (LR 2), ∀ c' < rcnt (LR 2),
      levT n S base 0 a * levT n S base 1 b * levT n S base 2 c =
          levT n S base 0 a' * levT n S base 1 b' * levT n S base 2 c' →
        a = a' ∧ b = b' ∧ c = c' := by
  have hp := (Raw.Orb.head_facts hh).1
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = 3 := hb.2.2.2.2.2.1
  have hraw := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  have hF := chainCheckFacts hraw
  obtain ⟨hk, hH⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hd := Raw.Orb.hd_of_head hk hH
  have hcnt : ∀ j < 3, rcnt (LR j) = (lev n S base j).pts.size := fun j hj =>
    (Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hj (hl j hj)).1.cnt
  have hGH : Raw.Orb.Gen n S kO = CFSG.KC.U6Sec3.ProdPf.H n S base 0 := by
    apply le_antisymm
    · rw [Raw.Orb.Gen, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨j.val, by have := j.2; omega, fixesFirst_zero _ _, rfl⟩
    · rw [CFSG.KC.U6Sec3.ProdPf.H, Subgroup.closure_le]
      rintro _ ⟨j, hj, -, rfl⟩
      exact Raw.Orb.S_mem_Gen hd j hj
  have hfix : ∀ j < 3, ∀ k < rcnt (LR j), levT n S base j k ∈ Raw.Orb.Fix n S kO base j :=
    fun j hj k hk => (Raw.Orb.tr_spec hd (by omega) k (by rw [← hcnt j hj]; exact hk)).1
  refine ⟨fun j hj k hk => ?_, fun x hx => ?_, ?_⟩
  · have hk' : k < (lev n S base j).pts.size := by rw [← hcnt j hj]; exact hk
    obtain ⟨-, -, hpg⟩ := CFSG.KC.U6Sec3.ProdPf.kernel_T hb hp hl hF hj hk'
    refine ⟨?_, fun z => hpg z⟩
    rw [hGH]
    exact CFSG.KC.U6Sec3.ProdPf.H_anti (Nat.zero_le j)
      (CFSG.KC.U6Sec3.ProdPf.T_mem hF (by omega) k hk')
  · have hx' : x ∈ Subgroup.closure (permsA n (S.extract 0 kO)) := by
      refine (Subgroup.closure_le _).2 ?_ hx
      rintro _ ⟨j, rfl⟩
      have hj0 : j.val < (S.extract 0 kO).size := by simp [Array.size_extract]; omega
      refine Subgroup.subset_closure ⟨j.val, hj0, ?_⟩
      change permOfArr n (S.extract 0 kO)[j.val]! = permOfArr n S[j.val]!
      rw [getElem!_pos (S.extract 0 kO) j.val hj0, Array.getElem_extract,
        getElem!_pos S j.val (by omega)]
      simp
    obtain ⟨κ, hκ, e⟩ := CFSG.KC.U6Sec3.ProdPf.decomp hF hx'
    rw [hbs, show List.range 3 = [0, 1, 2] from rfl] at e
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at e
    have hκ' : ∀ j < 3, κ j < rcnt (LR j) := fun j hj => by
      rw [hcnt j hj]; exact hκ j (by omega)
    exact ⟨κ 0, hκ' 0 (by norm_num), κ 1, hκ' 1 (by norm_num), κ 2, hκ' 2 (by norm_num),
      by rw [e, mul_assoc]⟩
  · intro a ha a' ha' b hb' b' hb'' c hc c' hc' e
    have step : ∀ i (hi : i < 3) (u u' : ℕ) (hu : u < rcnt (LR i)) (hu' : u' < rcnt (LR i))
        (f f' : Equiv.Perm (Fin n)) (hf : f ∈ Raw.Orb.Fix n S kO base (i + 1))
        (hf' : f' ∈ Raw.Orb.Fix n S kO base (i + 1)),
        levT n S base i u * f = levT n S base i u' * f' → u = u' ∧ f = f' := by
      intro i hi u u' hu hu' f f' hf hf' e
      have hiz : i < base.size := by omega
      have F := Raw.Orb.lev_facts hd hiz
      have hbi := hd.base_lt i hiz
      have img : ∀ v < rcnt (LR i), ∀ g ∈ Raw.Orb.Fix n S kO base (i + 1),
          ((levT n S base i v * g) ⟨base[i]!, hbi⟩ : ℕ) = (lev n S base i).pts[v]! := by
        intro v hv g hg
        rw [Equiv.Perm.mul_apply, hg.2 i (by omega) hbi]
        exact (Raw.Orb.tr_spec hd hiz v (by rw [← hcnt i hi]; exact hv)).2
      have h1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨base[i]!, hbi⟩ : Fin n) : ℕ)) e
      rw [img u hu f hf, img u' hu' f' hf'] at h1
      have huu : u = u' := by
        have p1 := F.pos_pts u (by rw [← hcnt i hi]; exact hu)
        have p2 := F.pos_pts u' (by rw [← hcnt i hi]; exact hu')
        rw [h1] at p1
        omega
      subst huu
      exact ⟨rfl, mul_left_cancel e⟩
    have m2 := hfix 2 (by norm_num) c hc
    have m2' := hfix 2 (by norm_num) c' hc'
    have m1 := Subgroup.mul_mem _ (hfix 1 (by norm_num) b hb') (Raw.Orb.Fix_succ_le m2)
    have m1' := Subgroup.mul_mem _ (hfix 1 (by norm_num) b' hb'') (Raw.Orb.Fix_succ_le m2')
    obtain ⟨r1, e1⟩ := step 0 (by norm_num) a a' ha ha' _ _ m1 m1' (by simpa [mul_assoc] using e)
    obtain ⟨r2, e2⟩ := step 1 (by norm_num) b b' hb' hb'' _ _ m2 m2' e1
    obtain ⟨r3, -⟩ := step 2 (by norm_num) c c' hc hc' 1 1 (Subgroup.one_mem _)
      (Subgroup.one_mem _) (by simpa using e2)
    exact ⟨r1, r2, r3⟩

end CFSG.KC.J2Enum.GrpPf

end
