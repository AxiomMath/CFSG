module

public import Certificates.Data.Kernel.SporSch.BaseBound
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
import CFSG.Certificates.Kernel.LceSP.Main
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2

private theorem hasBit_iff (M l : Nat) : hasBit M l = true ↔ M.testBit l = true := by
  unfold hasBit
  rw [Nat.blt_eq]
  change 0 < M &&& 1 <<< l ↔ _
  rw [Nat.one_shiftLeft, CFSG.Certificates.LceP.land_two_pow]
  split_ifs with h
  · exact iff_of_true (Nat.two_pow_pos l) h
  · exact iff_of_false (lt_irrefl 0) h

private theorem inS_bbMask : ∀ (L : List Nat) (x : Nat), inS (bbMask L) x = true ↔ x ∈ L
  | [], x => by
    unfold inS
    rw [hasBit_iff]
    change Nat.testBit 0 x = true ↔ _
    simp
  | y :: L, x => by
    unfold inS
    rw [hasBit_iff]
    change (bbMask L ||| 1 <<< y).testBit x = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ← hasBit_iff,
      ← inS, inS_bbMask L x, List.mem_cons, decide_eq_true_iff]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm), fun h => h.elim (fun h => Or.inr h.symm)
      Or.inl⟩

private theorem foldr_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i) :
    ∀ m s, (List.range m).foldr f s = s + ∑ i ∈ Finset.range m, g i
  | 0, s => by simp
  | m + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_add hf m,
      hf, Finset.sum_range_succ]
    ring

private theorem foldr_mul {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s * g i) :
    ∀ m s, (List.range m).foldr f s = s * ∏ i ∈ Finset.range m, g i
  | 0, s => by simp
  | m + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_mul hf m,
      hf, Finset.prod_range_succ]
    ring

private theorem sideCnt_eq (w SP R b : Nat) : sideCnt w SP R b =
    ((Finset.range (rcnt R)).filter
      (fun k => inS SP (rpt w (mask w) R k) = inS SP b)).card := by
  unfold sideCnt
  rw [CFSG.KC.Pack.foldN_eq, foldr_add (g := fun k =>
    if inS SP (rpt w (mask w) R k) = inS SP b then 1 else 0), Nat.zero_add, Finset.card_filter]
  intro k s
  cases inS SP b <;> cases inS SP (rpt w (mask w) R k) <;> rfl

private theorem bbProd_eq (w SP : Nat) (LR : Nat → Nat) (BP nb : Nat) :
    bbProd w SP LR BP nb = ∏ i ∈ Finset.range nb, sideCnt w SP (LR i) (pg w (mask w) BP i) := by
  unfold bbProd
  rw [CFSG.KC.Pack.foldN_eq, foldr_mul (g := fun i => sideCnt w SP (LR i) (pg w (mask w) BP i)),
    Nat.one_mul]
  intro i s
  rfl

private theorem getElem!_ofFn' {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem stab_iff {n : Nat} {L : List Nat} {g : Equiv.Perm (Fin n)}
    (h : ∀ x : Fin n, x.val ∈ L → (g x).val ∈ L) : ∀ x : Fin n, (g x).val ∈ L ↔ x.val ∈ L := by
  classical
  intro x
  refine ⟨fun hx => ?_, h x⟩
  set T : Finset (Fin n) := Finset.univ.filter (fun y => y.val ∈ L)
  have hsub : T.image g ⊆ T := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h z hz
  have he := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_image_of_injective _ g.injective])
  have hgx : g x ∈ T.image g := by
    rw [he]
    simpa [T] using hx
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 hgx
  rw [← g.injective hzx]
  simpa [T] using hz

open CFSG.KS.Raw.Orb CFSG.Certificates.ChainArrays CFSG.Certificates.Native in
theorem baseBound_sound {n w kS kO nb BP NS CH SP : Nat} {PS PSI LR : Nat → Nat}
    {D : List (List Int)} {L : List Nat} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : G = Subgroup.closure (Set.range fun j : Fin kO => permOfArr n (unpack n w (PS j))))
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH) (hn : n < 65536)
    (hcard : Nat.card G ≤ ((List.range nb).map fun i => rcnt (LR i)).prod)
    (hS : maskOK n SP L = true) :
    Nat.card {g : G // ∀ x : Fin n, x.val ∈ L → ((g : Equiv.Perm (Fin n)) x).val ∈ L} ≤
      bbProd w SP LR BP nb := by
  classical
  have hSP : SP = bbMask L := by
    have h2 := ((bAnd_iff _ _).1 hS).2
    exact (Nat.eq_of_beq_eq_true h2).symm
  have hin : ∀ x, inS SP x = true ↔ x ∈ L := by
    rw [hSP]
    exact inS_bbMask L
  rcases Nat.eq_zero_or_pos nb with hnb | hnb
  · subst hnb
    rw [bbProd_eq, Finset.prod_range_zero]
    simp only [List.range_zero, List.map_nil, List.prod_nil] at hcard
    exact le_trans (Finite.card_subtype_le _) hcard
  have hh0 := hh
  unfold headK at hh0
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh0
  obtain ⟨hsz, -, hkO, -, hperm, -, -, -⟩ := hh0
  unfold szOK at hsz
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hsz
  have hw' : n + 1 < 2 ^ w := by
    have := hsz.2
    rwa [Orb.shl_eq', Nat.one_mul] at this
  have hkO' : kO ≤ kS := Nat.le_of_ble_eq_true hkO
  have hn0 : 0 < n := by
    have R := recFacts_of (ho.1 0 hnb) (ho.2 0 hnb) hN
    exact lt_of_lt_of_le R.c_pos R.c_le
  set S : Array (Array Nat) := Array.ofFn (fun j : Fin kS => unpack n w (PS j)) with hSdef
  set base : Array Nat := Array.ofFn (fun t : Fin nb => pg w (mask w) BP t) with hbdef
  have hbs : base.size = nb := by simp [base]
  have hbt : ∀ t < nb, base[t]! = pg w (mask w) BP t := fun t ht => getElem!_ofFn' _ ht
  have hb : Binds n w PS kS nb BP S base :=
    ⟨hn0, hw', hn, by simp [S], fun j hj => getElem!_ofFn' _ hj, hbs, hbt⟩
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  have hGen : Gen n S kO = G := by
    rw [hG]
    unfold Gen
    congr 2
    funext j
    rw [getElem!_ofFn' _ (lt_of_lt_of_le j.2 hkO')]
  have hcard' : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod := by
    rw [rawOrbitSizesK_orb hb hperm ho hN, hGen]
    exact hcard
  have hbl : ∀ t < nb, base[t]! < n := fun t ht => hd.base_lt t (hbs ▸ ht)
  have hrec : ∀ i (hi : i < nb), ∀ k < (lev n S base i).pts.size,
      rpos w (mask w) (n * w) (LR i) (lev n S base i).pts[k]! < rcnt (LR i) := by
    intro i hi
    have F := lev_facts hd (hbs ▸ hi : i < base.size)
    have R := recFacts_of (ho.1 i hi) (ho.2 i hi) hN
    obtain ⟨hcnt, hstep⟩ := steps_eq hb hperm R.kS_lt (Nat.le_of_lt hi) hbl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [F.root, hbt i hi, ← R.root, (R.pt 0 R.c_pos).2]
        exact R.c_pos
      · have hp := F.par_lt k hk hk0
        have hl := F.lab_lt k hk hk0
        have h1 := ih _ hp (by omega)
        have hpn := F.pts_lt (lev n S base i).par[k]! (by omega)
        have e1 := R.pos _ hpn h1
        rw [← F.edge k hk hk0, ← e1, ← hstep _ hl _ (by rw [e1]; exact hpn)]
        exact R.closed _ h1 _ (by rw [hcnt]; exact hl)
  set s : Nat → Nat := fun i => sideCnt w SP (LR i) (pg w (mask w) BP i) with hsdef
  set P : Nat → Nat := fun i => ∏ t ∈ Finset.Ico i nb, s t with hPdef
  set St : Equiv.Perm (Fin n) → Prop := fun g => ∀ x : Fin n, (g x).val ∈ L ↔ x.val ∈ L
  set A : Nat → Equiv.Perm (Fin n) → Finset (Equiv.Perm (Fin n)) := fun i x =>
    Finset.univ.filter (fun g => x⁻¹ * g ∈ Fix n S kO base i ∧ St g) with hAdef
  have key : ∀ d i, i + d = nb → ∀ x ∈ Gen n S kO, (A i x).card ≤ P i := by
    intro d
    induction d with
    | zero =>
      intro i hi x _
      have hP : P i = 1 := by
        simp only [hPdef]
        rw [show i = nb by omega, Finset.Ico_self, Finset.prod_empty]
      rw [hP]
      refine Finset.card_le_one.2 fun g hg g' hg' => ?_
      simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
      have e1 := fix_one hd hcard' (by rw [hbs, ← hi, Nat.add_zero]; exact hg.1)
      have e2 := fix_one hd hcard' (by rw [hbs, ← hi, Nat.add_zero]; exact hg'.1)
      rw [inv_mul_eq_one] at e1 e2
      rw [← e1, ← e2]
    | succ d ih =>
      intro i hi x hx
      have hin' : i < nb := by omega
      have hib : i < base.size := hbs ▸ hin'
      rcases (A i x).eq_empty_or_nonempty with hA | ⟨g0, hg0⟩
      · rw [hA, Finset.card_empty]
        exact Nat.zero_le _
      simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hg0
      have hg0G : g0 ∈ Gen n S kO := by
        have := (Gen n S kO).mul_mem hx hg0.1.1
        rwa [mul_inv_cancel_left] at this
      set m := (lev n S base i).pts.size
      set bi : Fin n := ⟨base[i]!, hd.base_lt i hib⟩
      set K := (Finset.range m).filter (fun k => ((lev n S base i).pts[k]! ∈ L ↔ base[i]! ∈ L))
      have hsub : A i x ⊆ K.biUnion (fun k => A (i + 1) (g0 * trP n S base i k)) := by
        intro g hg
        simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        have hh' : g0⁻¹ * g ∈ Fix n S kO base i := by
          have := (Fix n S kO base i).mul_mem ((Fix n S kO base i).inv_mem hg0.1) hg.1
          rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
        obtain ⟨k, hk, hkp⟩ := fix_surj hd hcard' hib hh'
        obtain ⟨ht1, ht2⟩ := tr_spec hd hib k hk
        set t := trP n S base i k
        have hf : t⁻¹ * (g0⁻¹ * g) ∈ Fix n S kO base (i + 1) := by
          refine ⟨((Fix n S kO base i).mul_mem ((Fix n S kO base i).inv_mem ht1) hh').1,
            fun u hu hun => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · exact ((Fix n S kO base i).mul_mem ((Fix n S kO base i).inv_mem ht1) hh').2 u hu hun
          · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
            exact Fin.ext (by rw [hkp, ← ht2])
        have hpk : ((g0⁻¹ * g) bi).val = (lev n S base i).pts[k]! := hkp
        refine Finset.mem_biUnion.2 ⟨k, ?_, ?_⟩
        · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩
          rw [← hpk]
          have e : g bi = g0 ((g0⁻¹ * g) bi) := by
            rw [← Equiv.Perm.mul_apply, mul_inv_cancel_left]
          rw [← hg0.2 ((g0⁻¹ * g) bi), ← e]
          exact hg.2 bi
        · simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, hg.2⟩
          rw [mul_inv_rev, mul_assoc]
          exact hf
      have hK : K.card ≤ s i := by
        have R := recFacts_of (ho.1 i hin') (ho.2 i hin') hN
        have F := lev_facts hd hib
        simp only [hsdef]
        rw [sideCnt_eq]
        refine Finset.card_le_card_of_injOn
          (fun k => rpos w (mask w) (n * w) (LR i) (lev n S base i).pts[k]!) ?_ ?_
        · intro k hk
          simp only [K, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
          have h1 := hrec i hin' k hk.1
          have e1 := R.pos _ (F.pts_lt k hk.1) h1
          refine Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, ?_⟩
          rw [e1, ← hbt i hin']
          rcases Bool.eq_false_or_eq_true (inS SP base[i]!) with hb1 | hb1
          · rw [hb1]
            exact (hin _).2 (hk.2.2 ((hin _).1 hb1))
          · rw [hb1]
            by_contra hc
            rw [Bool.not_eq_false] at hc
            exact absurd ((hin _).2 (hk.2.1 ((hin _).1 hc))) (by rw [hb1]; exact Bool.false_ne_true)
        · intro k1 hk1 k2 hk2 e
          simp only [K, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk1 hk2
          have e1 := R.pos _ (F.pts_lt k1 hk1.1) (hrec i hin' k1 hk1.1)
          have e2 := R.pos _ (F.pts_lt k2 hk2.1) (hrec i hin' k2 hk2.1)
          have e' : (lev n S base i).pts[k1]! = (lev n S base i).pts[k2]! := by
            rw [← e1, ← e2]
            exact congrArg _ e
          rw [← F.pos_pts k1 hk1.1, ← F.pos_pts k2 hk2.1, e']
      have hPi : P i = s i * P (i + 1) := by
        simp only [hPdef]
        exact Finset.prod_eq_prod_Ico_succ_bot hin' s
      calc (A i x).card ≤ (K.biUnion (fun k => A (i + 1) (g0 * trP n S base i k))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ k ∈ K, (A (i + 1) (g0 * trP n S base i k)).card := Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ K, P (i + 1) := Finset.sum_le_sum fun k hk => by
            have hkm : k < m := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
            exact ih (i + 1) (by omega) _ ((Gen n S kO).mul_mem hg0G
              (tr_spec hd hib k hkm).1.1)
        _ = K.card * P (i + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ s i * P (i + 1) := Nat.mul_le_mul_right _ hK
        _ = P i := hPi.symm
  have h0 := key nb 0 (Nat.zero_add nb) 1 (Gen n S kO).one_mem
  have hP0 : P 0 = bbProd w SP LR BP nb := by
    rw [bbProd_eq, Finset.range_eq_Ico]
  rw [← hP0]
  refine le_trans ?_ h0
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun g => ⟨g.1.1, ?_⟩) ?_
  · simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and, inv_one, one_mul]
    refine ⟨?_, stab_iff g.2⟩
    have hg : (g.1 : Equiv.Perm (Fin n)) ∈ Gen n S kO := by
      rw [hGen]
      exact g.1.2
    rw [← Fix_zero (base := base)] at hg
    exact hg
  · intro g g' e
    have e' := congrArg Subtype.val e
    simp only at e'
    exact Subtype.ext (Subtype.ext e')

end CFSG.KS.SporSch

end
