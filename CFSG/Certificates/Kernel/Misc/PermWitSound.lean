module

public import Certificates.Data.Kernel.Misc.PermWit
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Spor.SiftRSound

public section

namespace CFSG.KC.PermWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.KC.Bfs CFSG.Certificates.Native
open CFSG.KC.BfsPin (PP compA_PP idA_eq validA_unpack)
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB conj_unpack' comp_unpack' eqA_unpack')
open CFSG.KLie.CT (fget)

theorem siftR_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (h : siftR n w LR TRI BP nb G = true) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) = true := by
  unfold siftR at h
  simp only [Bool.and_eq_true] at h
  exact siftK_soundR hb hp hl rfl (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem cntK_eq (f : Nat → Bool) : ∀ N, cntK N f = (List.range N).countP f
  | 0 => rfl
  | N + 1 => by
    change strictN (cntK N f) (fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (f N)) = _
    rw [CFSG.KS.PEnum.strictN_app', cntK_eq f N, List.range_succ, List.countP_append]
    cases h : f N <;> simp [h]

theorem arr_eq_of_rep {n : Nat} {t u : Array Nat} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hgt : Rep n t g) (hgu : Rep n u g) : t = u := by
  apply Array.ext (by rw [ht, hu])
  intro i h1 h2
  rw [← getElem!_pos t i h1, ← getElem!_pos u i h2, hgt.apply (ht ▸ h1), hgu.apply (ht ▸ h1)]

theorem enumBfs_of_group {n w N fuel : Nat} {T : Nat → Nat} {gs : Array (Array Nat)}
    {ps : List Nat} (hps : ∀ p ∈ ps, p < n)
    (hval : ∀ i < N, validA n (unpack n w (T i)) = true)
    (hgv : ∀ k < gs.size, validA n gs[k]! = true)
    (hid : ∃ i < N, unpack n w (T i) = idA n)
    (hcl : ∀ i < N, ∀ k < gs.size, ∃ j < N, leftA n gs k (unpack n w (T i)) = unpack n w (T j))
    (hR : ∀ i < N, Reach (leftA n gs) gs.size (idA n) (unpack n w (T i)))
    (hkey : ∀ i < N, ∀ j < N, keyA n ps (unpack n w (T i)) = keyA n ps (unpack n w (T j)) → i = j)
    (hf : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧ (enumBfs n gs ps fuel).pts.size = N := by
  classical
  let U : Nat → Array Nat := fun i => unpack n w (T i)
  let Sf : Finset (Array Nat) := (Finset.range N).image U
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ i < N, unpack n w (T i) = x := by
    intro x
    simp only [Sf, U, Finset.mem_image, Finset.mem_range]
  obtain ⟨i0, hi0, e0⟩ := hid
  have hroot : idA n ∈ Sf := (hmemS _).2 ⟨i0, hi0, e0⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < gs.size, leftA n gs k x ∈ Sf := by
    intro x hx k hk
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, e⟩ := hcl i hi k hk
    rw [e]
    exact (hmemS _).2 ⟨j, hj, rfl⟩
  have hRS : ∀ x ∈ Sf, Reach (leftA n gs) gs.size (idA n) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hR i hi
  have hS := reach_iff_of_closed hroot hclosed hRS
  have hv : ∀ x ∈ Sf, validA n x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hval i hi
  have hkeyS : ∀ x ∈ Sf, ∀ y ∈ Sf, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmemS y).1 hy
    rw [hkey i hi j hj e]
  have hcard : Sf.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hkey i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (congrArg (keyA n ps) e)
  obtain ⟨hcert, -, hsize, -⟩ := arrBfs_spec (act := leftA n gs) (ngen := gs.size)
    (valid := validA n) (key := keyA n ps) (root := idA n) (fuel := fuel) Sf hS hv hkeyS
    (by rw [hcard]; exact hf)
  refine ⟨?_, hsize.trans hcard⟩
  unfold enumOK enumBfs
  rw [Bool.and_eq_true]
  exact ⟨allLt_iff.2 hgv, hcert⟩

theorem ctreePt_spec {n w N k : Nat} {T : Nat → Nat} {row i : Nat}
    (h : ctreePt n w N k T row i = true) (hi : i ≠ 0) :
    cLab (fget row i 16) < N ∧ cPar (fget row i 16) < N ∧
      cDep (fget row (cPar (fget row i 16)) 16) + 1 = cDep (fget row i 16) ∧
      T i = pcomp n w (mask w) (CFSG.KC.ConjOrb.pconj n w (mask w) (T (cLab (fget row i 16)))
        (pinvS n w (mask w) (T (cLab (fget row i 16)))) (T k)) (T (cPar (fget row i 16))) := by
  unfold ctreePt at h
  have hb : Nat.beq i 0 = false := by
    cases e : Nat.beq i 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hi
  have e : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
  rw [hb, Bool.false_or, e] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1.1.1, Nat.blt_eq.mp h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem conjSimpleOK_of_ctree {n w N : Nat} (hw : szOK n w = true) {T WT : Nat → Nat}
    {gs : Array (Array Nat)} {ps : List Nat} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hc : enumOK n gs ps c = true)
    (hpts : c.pts = Array.ofFn (n := N) fun i => unpack n w (T i.val))
    (hperm : ∀ i < N, permB n w (T i) = true) (h0 : T 0 = pidn n w)
    (hkey : ∀ i < N, ∀ j < N, keyA n ps (unpack n w (T i)) = keyA n ps (unpack n w (T j)) → i = j)
    (htree : ∀ k < N, Nat.beq (T k) (pidn n w) = true ∨
      ∀ i < N, ctreePt n w N k T (WT k) i = true) :
    conjSimpleOK n ps c = true := by
  classical
  have hsz : c.pts.size = N := by rw [hpts, Array.size_ofFn]
  have hget : ∀ i < N, c.pts[i]! = unpack n w (T i) := by
    intro i hi
    rw [hpts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  have hPP : ∀ i < N, PP n w (T i) := fun i hi => pp_of_permB hw (hperm i hi)
  have hval : ∀ i < N, validA n (unpack n w (T i)) = true := fun i hi => validA_unpack (hperm i hi)
  obtain ⟨hmem, -, -⟩ := enumOK_spec hps hc
  have hin : ∀ i < N, permOfArr n (unpack n w (T i)) ∈ Subgroup.closure (permsA n gs) := by
    intro i hi
    exact (hmem _).2 ⟨i, by rw [hsz]; exact hi, by rw [hget i hi]⟩
  unfold conjSimpleOK
  rw [allLt_iff]
  intro k hk
  rw [hsz] at hk
  rcases htree k hk with hid | htr
  · rw [hget k hk, Nat.eq_of_beq_eq_true hid, ← idA_eq hw]
    have : eqA n (idA n) (idA n) = true := (eqA_iff rep_idA rep_idA).2 rfl
    rw [this, Bool.true_or]
  · have hN : 0 < N := by omega
    set gk := conjGens n c k with hgk
    have hgs : gk.size = N := by rw [hgk, conjGens_size, hsz]
    have hgget : ∀ j < N, gk[j]! = unpack n w (pcomp n w (mask w) (T j)
        (pcomp n w (mask w) (T k) (pinvS n w (mask w) (T j)))) := by
      intro j hj
      rw [hgk, conjGens_get (by rw [hsz]; exact hj), hget j hj, hget k hk,
        conj_unpack' hw (hperm j hj) (hperm k hk)]
    have hgv : ∀ j < gk.size, validA n gk[j]! = true := by
      intro j hj
      rw [hgs] at hj
      rw [hgk, conjGens_get (by rw [hsz]; exact hj), hget j hj, hget k hk]
      exact CFSG.RankThree.Native.F2.validA_of_rep
        (rep_conjA (hval j hj) (rep_of_validA (hval k hk)))
    have hcl : ∀ i < N, ∀ j < gk.size, ∃ i' < N,
        leftA n gk j (unpack n w (T i)) = unpack n w (T i') := by
      intro i hi j hj
      rw [hgs] at hj
      set Q := permOfArr n (unpack n w (T j)) * permOfArr n (unpack n w (T k)) *
        (permOfArr n (unpack n w (T j)))⁻¹ * permOfArr n (unpack n w (T i)) with hQ
      have hQm : Q ∈ Subgroup.closure (permsA n gs) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hin j hj) (hin k hk))
          (Subgroup.inv_mem _ (hin j hj))) (hin i hi)
      obtain ⟨i', hi', e⟩ := (hmem Q).1 hQm
      rw [hsz] at hi'
      refine ⟨i', hi', ?_⟩
      have hrep : Rep n (leftA n gk j (unpack n w (T i))) Q := by
        unfold leftA
        rw [hgk, conjGens_get (by rw [hsz]; exact hj), hget j hj, hget k hk]
        exact rep_compA (rep_conjA (hval j hj) (rep_of_validA (hval k hk)))
          (rep_of_validA (hval i hi))
      have hrep' : Rep n (unpack n w (T i')) Q := by
        rw [← e, hget i' hi']
        exact rep_of_validA (hval i' hi')
      refine arr_eq_of_rep (by simp [leftA, compA]) (by simp [unpack]) hrep hrep'
    have hreach : ∀ d, ∀ i < N, cDep (fget (WT k) i 16) = d →
        Reach (leftA n gk) gk.size (idA n) (unpack n w (T i)) := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro i hi hd
        by_cases hi0 : i = 0
        · rw [hi0, h0, ← idA_eq hw]
          exact Reach.root
        · obtain ⟨hl, hp, hdep, he⟩ := ctreePt_spec (htr i hi) hi0
          have hpr := ih _ (by omega) _ hp rfl
          have hlab : cLab (fget (WT k) i 16) < gk.size := by rw [hgs]; exact hl
          have e : unpack n w (T i) = leftA n gk (cLab (fget (WT k) i 16))
              (unpack n w (T (cPar (fget (WT k) i 16)))) := by
            unfold leftA
            rw [hgget _ hl, he, CFSG.KC.ConjOrb.pconj,
              compA_PP ((hPP _ hl).mul ((hPP k hk).mul (hPP _ hl).inv)) (hPP _ hp)]
          rw [e]
          exact Reach.step _ hlab hpr
    have hR : ∀ i < N, Reach (leftA n gk) gk.size (idA n) (unpack n w (T i)) :=
      fun i hi => hreach _ i hi rfl
    obtain ⟨hE, hS⟩ := enumBfs_of_group (fuel := c.pts.size + 1) hps hval hgv
      ⟨0, hN, by rw [h0, ← idA_eq hw]⟩ hcl hR hkey (by rw [hsz]; omega)
    unfold conjPointOK
    rw [hE, hS, hsz, beq_self_eq_true, Bool.and_true, Bool.or_true]

end CFSG.KC.PermWit

end
