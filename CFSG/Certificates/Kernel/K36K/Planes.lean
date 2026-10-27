module

public import Certificates.Data.Kernel.K36K.Planes
public import CFSG.Certificates.Kernel.K36K.Sound
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPlane

public section

namespace CFSG.KD.K36K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
  CFSG.KS.K36K CFSG.KD.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm Certificates.K36Spor

section Packed

variable {n w : Nat}

theorem gens_facts (hn : szOK n w = true) {V : VData} {GP GPI EG GT GTI : ℕ → ℕ}
    (h : gensK n w V GP GPI EG GT GTI = true) {a b : Equiv.Perm (Fin n)}
    (ha : TabRep (unpack n w (GP 0)) a) (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ (e : ℕ → Equiv.Perm (Fin n)) (L : List (Equiv.Perm (Fin n))),
      (∀ k < V.base.eW.length, PR n w (EG k) (e k) ∧
        e k ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) ∧
      L.length = V.base.gWs.length ∧
      allN V.base.gWs.length (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) = true ∧
      (∀ j < V.base.gWs.length, PR n w (GT j) (L.getD j 1)) ∧
      ∀ g ∈ L, g ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) := by
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  unfold gensK at h
  obtain ⟨hG2, hrest⟩ := band_e h
  obtain ⟨hE1, hG1⟩ := band_e hrest
  have hG2' : allN 2 (fun j => permOK n w (mask w) (n * w) (GP j) (GPI j)) = true := hG2
  have hSr : ∀ j < 2, TabRep (unpack n w (GP j)) (S.getD j 1) := by
    intro j hj
    rcases j with _ | _ | j
    · exact ha
    · exact hb
    · omega
  have hword : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GP GPI 2 wd r = true → TabRep (unpack n w r) (wordVal S wd) :=
    fun h => pr_word (k := 2) rfl hG2' hSr h
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  set Lg : List (Equiv.Perm (Fin n)) := V.base.gWs.map (wordVal S) with hLg
  have hLgget : ∀ j < V.base.gWs.length, Lg.getD j 1 = wordVal S (V.base.gWs.getD j []) :=
    fun j hj => by
      rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj), List.getD_eq_getElem _ _ hj,
        List.getElem_map]
  have hGk : ∀ j < V.base.gWs.length,
      wordEqK n w (mask w) (pidn n w) GP GPI 2 (V.base.gWs.getD j []) (GT j) = true ∧
        permOK n w (mask w) (n * w) (GT j) (GTI j) = true := fun j hj =>
    band_e (PK.allN_iff.1 hG1 j hj)
  refine ⟨fun k => wordVal S (V.base.eW.getD k []), Lg, fun k hk => ?_, by simp [hLg],
    PK.allN_iff.2 fun j hj => (hGk j hj).2, fun j hj => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hE1 k hk)
    exact ⟨⟨h2, hword h1⟩, wordVal_mem S G hSG _⟩
  · exact ⟨(perm_canon (hGk j hj).2 hn).1, by rw [hLgget j hj]; exact hword (hGk j hj).1⟩
  · intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd

theorem planes_two (hn : szOK n w = true) {S : SData} {GP GPI EG GT GTI : ℕ → ℕ}
    (hgens : gensK n w (vOf S) GP GPI EG GT GTI = true)
    (hcen : cenK n w S.base.p S.base.eW.length EG = true)
    (hys : S.ys.getD 0 0 < S.base.eW.length)
    (hv : vK n w S.base.p (EG 0) (EG (S.ys.getD 0 0)) = true)
    (hcent : centSK n w S EG GT = true) (hwords : wordsSK n w S GP GT GTI = true)
    (hgen : ∃ k < S.gen.length, S.gen.getD k 0 = 0) (hp : S.base.p.Prime)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), Nat.card E = S.base.p ^ 2 ∧
      E ≤ Subgroup.closure {a, b} ∧ ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E →
        Nat.card A = S.base.p ^ 2 → ∃ Γ : Set (Equiv.Perm (Fin n)),
          Γ ⊆ Subgroup.closure {a, b} ∧ ({a, b} : Set (Equiv.Perm (Fin n))) ⊆ Subgroup.closure Γ ∧
            ∀ g ∈ Γ, ∃ u ∈ A, u ≠ 1 ∧ u * g = g * u := by
  obtain ⟨e, L, he, hL, hGT, hgP, hLG⟩ := gens_facts hn hgens ha hb
  set p := S.base.p with hpdef
  unfold cenK at hcen
  rw [PK.strictB_eq] at hcen
  obtain ⟨h0, hcen⟩ := band_e hcen
  obtain ⟨hzp, hcen⟩ := band_e hcen
  obtain ⟨hz1, hzc⟩ := band_e hcen
  have h0' : 0 < S.base.eW.length := Nat.blt_eq.mp h0
  have hzP := (he 0 h0').1
  have hvP := (he _ hys).1
  have hzp' : e 0 ^ p = 1 := (pr_beq (pr_pow hn hzP p) (pr_one hn)).1 hzp
  have hz1' : e 0 ≠ 1 := pr_ne hzP (pr_one hn) hz1
  have hzv : e 0 * e (S.ys.getD 0 0) = e (S.ys.getD 0 0) * e 0 := by
    have hc := PK.allN_iff.1 hzc _ hys
    rw [PK.strictB_eq] at hc
    exact (pr_beq (pr_mul hzP hvP) (pr_mul hvP hzP)).1 hc
  unfold vK at hv
  obtain ⟨hv1, hv2⟩ := band_e hv
  have hvp : e (S.ys.getD 0 0) ^ p = 1 := (pr_beq (pr_pow hn hvP p) (pr_one hn)).1 hv1
  have hvz : ∀ k < p, e (S.ys.getD 0 0) ≠ e 0 ^ k := fun k hk =>
    pr_ne hvP (pr_pow hn hzP k) (PK.allN_iff.1 hv2 k hk)
  have hEc := card_closure_pair_of_pow hp hzp' hvp hzv hz1' hvz
  refine ⟨Subgroup.closure {e 0, e (S.ys.getD 0 0)}, hEc, ?_, fun A hAE hAc => ?_⟩
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨(he 0 h0').2, (he _ hys).2⟩
  · have hAE' : A = Subgroup.closure {e 0, e (S.ys.getD 0 0)} :=
      Subgroup.eq_of_le_of_card_ge hAE (by rw [hEc, hAc])
    obtain ⟨k, hk, hk0⟩ := hgen
    obtain ⟨Γ, hΓL, hab, hΓ⟩ :=
      gen_sound hn (fun k hk => (he k hk).1) hL hGT hgP ha hb hcent hwords k hk
    refine ⟨Γ, fun g hg => hLG g (hΓL hg), hab, fun g hg => ?_⟩
    obtain ⟨u, hu, hu1, hug⟩ := hΓ g hg
    rw [hk0] at hu
    exact ⟨u, hAE' ▸ hu, hu1, hug⟩

structure PHyps0 (n w : Nat) (S : SData) (GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat)
    (cnt cap len : Nat) : Prop where
  hn : szOK n w = true
  hgens : gensK n w (vOf S) GP GPI EG GT GTI = true
  hh : penumHdK (pidn n w) cnt cap T PL = true
  hsl : penumSlK n w (mask w) (n * w) false EG EGI S.base.eW.length cnt T PL POS SRT SRI 0 len =
    true
  hlen : cnt ≤ len
  hcnt : cnt = S.base.p ^ 3
  hnab : nabK n w S.base.eW.length EG = true
  hcen : cenK n w S.base.p S.base.eW.length EG = true
  hlines : linesK n w S.base.p (vOf S) EG = true

structure PHyps (n w : Nat) (S : SData) (GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat)
    (cnt cap len : Nat) : Prop extends PHyps0 n w S GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len
    where
  hcent : centSK n w S EG GT = true
  hwords : wordsSK n w S GP GT GTI = true
  hgen : ∀ i < S.ys.length, ∃ k < S.gen.length, S.gen.getD k 0 = i

theorem planes_three_idx {S : SData} {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat}
    {cnt cap len : Nat} (H : PHyps0 n w S GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hp : S.base.p.Prime) {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ (e : ℕ → Equiv.Perm (Fin n)) (L : List (Equiv.Perm (Fin n))),
      (∀ k < S.base.eW.length, PR n w (EG k) (e k) ∧
        e k ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) ∧
      L.length = S.base.gWs.length ∧
      allN S.base.gWs.length (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) = true ∧
      (∀ j < S.base.gWs.length, PR n w (GT j) (L.getD j 1)) ∧
      (∀ g ∈ L, g ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) ∧
      e 0 ^ S.base.p = 1 ∧ e 0 ≠ 1 ∧
      (∀ i < S.ys.length, S.ys.getD i 0 < S.base.eW.length ∧ e (S.ys.getD i 0) ^ S.base.p = 1 ∧
        e 0 * e (S.ys.getD i 0) = e (S.ys.getD i 0) * e 0) ∧
      ∃ E : Subgroup (Equiv.Perm (Fin n)), Nat.card E = S.base.p ^ 3 ∧
        E ≤ Subgroup.closure {a, b} ∧ ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E →
          IsElemAbelian S.base.p A → Nat.card A = S.base.p ^ 2 →
            ∃ i < S.ys.length, Subgroup.closure {e 0, e (S.ys.getD i 0)} = A := by
  have hn := H.hn
  obtain ⟨e, L, he, hL, hGT, hgP, hLG⟩ := gens_facts hn H.hgens ha hb
  set p := S.base.p with hpdef
  set ne := S.base.eW.length with hne
  have hEP : ∀ k < ne, PR n w (EG k) (e k) := fun k hk => (he k hk).1
  set gens : Array Tab := Array.ofFn (n := ne) fun k => unpack n w (EG k.val) with hgens'
  have hgget : ∀ k < ne, gens[k]! = unpack n w (EG k) := fun k hk => by
    rw [hgens', getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hgsz : gens.size = ne := Array.size_ofFn
  have hgOK : GensOK n w ne EG gens := ⟨hgsz, fun j hj => ⟨hgget j hj, (hEP j hj).1⟩⟩
  obtain ⟨-, henum⟩ := penumK_left_sound hn hgOK H.hh
    (fun i hi => CFSG.KS.BaseMask.penumSl_spec H.hsl (Nat.zero_le i) (by have := H.hlen; omega) hi)
  set E := Subgroup.closure {g | ∃ k < ne, e k = g} with hEdef
  have hA : ∀ g ∈ {g | ∃ k < ne, e k = g}, ∃ j < gens.size, TabRep gens[j]! g := by
    rintro g ⟨k, hk, rfl⟩
    exact ⟨k, by rw [hgsz]; exact hk, by rw [hgget k hk]; exact (hEP k hk).2⟩
  have hgensE : ∀ j < gens.size, ∃ g ∈ {g | ∃ k < ne, e k = g}, TabRep gens[j]! g := by
    intro j hj
    rw [hgsz] at hj
    exact ⟨e j, ⟨j, hj, rfl⟩, by rw [hgget j hj]; exact (hEP j hj).2⟩
  have hE := enumerates_closure hA hgensE henum
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE.card, Array.length_toList, rec_size, H.hcnt]
  have hEG : E ≤ Subgroup.closure {a, b} := by
    rw [hEdef, Subgroup.closure_le]
    rintro g ⟨k, hk, rfl⟩
    exact (he k hk).2
  have hmemE : ∀ k < ne, e k ∈ E := fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hnab := H.hnab
  unfold nabK at hnab
  have hnab' := bnot_e hnab
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hall : allN ne (fun i => strictB (EG i) (fun x => allN ne (fun j => strictB (EG j)
        (fun y => Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x))))) = true := by
      refine PK.allN_iff.2 fun i hi => ?_
      rw [PK.strictB_eq]
      refine PK.allN_iff.2 fun j hj => ?_
      rw [PK.strictB_eq]
      exact (pr_beq (pr_mul (hEP i hi) (hEP j hj)) (pr_mul (hEP j hj) (hEP i hi))).2
        (hcon _ (hmemE i hi) _ (hmemE j hj))
    rw [hall] at hnab'
    exact absurd hnab' (by decide)
  have hcen := H.hcen
  unfold cenK at hcen
  rw [PK.strictB_eq] at hcen
  obtain ⟨h0, hcen⟩ := band_e hcen
  obtain ⟨hzp, hcen⟩ := band_e hcen
  obtain ⟨hz1, hzc⟩ := band_e hcen
  have h0' : 0 < ne := Nat.blt_eq.mp h0
  have hzP : PR n w (EG 0) (e 0) := hEP 0 h0'
  have hzE : e 0 ∈ E := hmemE 0 h0'
  have hzp' : e 0 ^ p = 1 := (pr_beq (pr_pow hn hzP p) (pr_one hn)).1 hzp
  have hz1' : e 0 ≠ 1 := pr_ne hzP (pr_one hn) hz1
  have hzcent : ∀ x ∈ E, x * e 0 = e 0 * x := by
    have hcl : E ≤ Subgroup.centralizer ({e 0} : Set (Equiv.Perm (Fin n))) := by
      rw [hEdef, Subgroup.closure_le]
      rintro g ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hc := PK.allN_iff.1 hzc k hk
      rw [PK.strictB_eq] at hc
      exact ((pr_beq (pr_mul hzP (hEP k hk)) (pr_mul (hEP k hk) hzP)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  have hlines := H.hlines
  unfold linesK at hlines
  rw [PK.strictB_eq] at hlines
  obtain ⟨hys, hlines⟩ := band_e hlines
  obtain ⟨hvs, hds⟩ := band_e hlines
  have hys' : S.ys.length = p + 1 := Nat.eq_of_beq_eq_true hys
  set v : ℕ → Equiv.Perm (Fin n) := fun i => e (S.ys.getD i 0) with hvdef
  have hvK : ∀ i < S.ys.length, S.ys.getD i 0 < ne ∧
      vK n w p (EG 0) (EG (S.ys.getD i 0)) = true := fun i hi => by
    obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hvs i hi)
    exact ⟨Nat.blt_eq.mp h1, h2⟩
  have hvP : ∀ i < S.ys.length, PR n w (EG (S.ys.getD i 0)) (v i) := fun i hi =>
    hEP _ (hvK i hi).1
  have hvfacts : ∀ i < S.ys.length, v i ∈ E ∧ v i ^ p = 1 ∧ e 0 * v i = v i * e 0 ∧
      ∀ k < p, v i ≠ e 0 ^ k := by
    intro i hi
    obtain ⟨hlt, hk⟩ := hvK i hi
    unfold vK at hk
    obtain ⟨hk1, hk2⟩ := band_e hk
    have hvE : v i ∈ E := hmemE _ hlt
    exact ⟨hvE, (pr_beq (pr_pow hn (hvP i hi) p) (pr_one hn)).1 hk1, (hzcent _ hvE).symm,
      fun k hk' => pr_ne (hvP i hi) (pr_pow hn hzP k) (PK.allN_iff.1 hk2 k hk')⟩
  have hv' : ∀ i ≤ p, v i ∈ E ∧ v i ^ p = 1 ∧ e 0 * v i = v i * e 0 ∧ ∀ k < p, v i ≠ e 0 ^ k :=
    fun i hi => hvfacts i (by omega)
  have hd : ∀ j ≤ p, ∀ i < j,
      v j ∉ Subgroup.closure ({e 0, v i} : Set (Equiv.Perm (Fin n))) := by
    intro j hj i hij hmem
    have hj' : j < S.ys.length := by omega
    have hi' : i < S.ys.length := by omega
    have hdj := PK.allN_iff.1 hds j hj'
    rw [PK.strictB_eq] at hdj
    have hout := PK.allN_iff.1 hdj i hij
    obtain ⟨hvi, hvp, hzv, -⟩ := hvfacts i hi'
    obtain ⟨c, hc, d, hd, hcd⟩ := exists_pow_mul_pow_of_mem hp.pos hzv hzp' hvp hmem
    exact outK_sound hn hzP (hvP i hi') (hvP j hj') hout c hc d hd hcd
  refine ⟨e, L, he, hL, hGT, hgP, hLG, hzp', hz1', fun i hi =>
    ⟨(hvK i hi).1, (hvfacts i hi).2.1, (hvfacts i hi).2.2.1⟩, E, hEc, hEG,
    fun A hAE hAe hAc => ?_⟩
  obtain ⟨i, hi, hYA⟩ :=
    eq_line_of_elemAbelian hp hEc hnc hzE hzp' hz1' hzcent hv' hd hAE hAe hAc
  exact ⟨i, by omega, hYA⟩

theorem planes_three {S : SData} {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat}
    {cnt cap len : Nat} (H : PHyps n w S GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hp : S.base.p.Prime) {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), Nat.card E = S.base.p ^ 3 ∧
      E ≤ Subgroup.closure {a, b} ∧ ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E →
        IsElemAbelian S.base.p A → Nat.card A = S.base.p ^ 2 → ∃ Γ : Set (Equiv.Perm (Fin n)),
          Γ ⊆ Subgroup.closure {a, b} ∧ ({a, b} : Set (Equiv.Perm (Fin n))) ⊆ Subgroup.closure Γ ∧
            ∀ g ∈ Γ, ∃ u ∈ A, u ≠ 1 ∧ u * g = g * u := by
  obtain ⟨e, L, he, hL, hGT, hgP, hLG, -, -, -, E, hEc, hEG, hE⟩ :=
    planes_three_idx H.toPHyps0 hp ha hb
  refine ⟨E, hEc, hEG, fun A hAE hAe hAc => ?_⟩
  obtain ⟨i, hi, hYA⟩ := hE A hAE hAe hAc
  obtain ⟨k, hk, hki⟩ := H.hgen i hi
  obtain ⟨Γ, hΓL, hab, hΓ⟩ :=
    gen_sound H.hn (fun k hk => (he k hk).1) hL hGT hgP ha hb H.hcent H.hwords k hk
  refine ⟨Γ, fun g hg => hLG g (hΓL hg), hab, fun g hg => ?_⟩
  obtain ⟨u, hu, hu1, hug⟩ := hΓ g hg
  rw [hki] at hu
  exact ⟨u, hYA ▸ hu, hu1, hug⟩

end Packed

open CFSG.LocalAnalysis.UniquenessCase.UCK.Spor in
theorem closure_centSet_eq_top {X : Type*} [Group X] {a b : X} {G : Subgroup X}
    (hG : G = Subgroup.closure {a, b}) {p k : ℕ}
    (h : ∃ E : Subgroup X, Nat.card E = p ^ k ∧ E ≤ G ∧ ∀ A : Subgroup X, A ≤ E →
      IsElemAbelian p A → Nat.card A = p ^ 2 → ∃ Γ : Set X, Γ ⊆ G ∧
        ({a, b} : Set X) ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ, ∃ u ∈ A, u ≠ 1 ∧ u * g = g * u) :
    ∃ E : Subgroup ↥G, Nat.card E = p ^ k ∧ ∀ A : Subgroup ↥G, A ≤ E → IsElemAbelian p A →
      Nat.card A = p ^ 2 → Subgroup.closure (centSet A) = ⊤ := by
  obtain ⟨E, hEc, hEG, hE⟩ := h
  refine ⟨E.subgroupOf G, ?_, fun A hAE hAe hAc => ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  set A0 : Subgroup X := A.map G.subtype with hA0
  have hA0E : A0 ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hAE hx)
  have hA0c : Nat.card A0 = p ^ 2 := by
    rw [hA0, Subgroup.card_map_of_injective G.subtype_injective, hAc]
  obtain ⟨Γ, hΓG, hab, hΓ⟩ := hE A0 hA0E (CFSG.Open.IsElemAbelian.map hAe _) hA0c
  have hmap : (Subgroup.closure {x : ↥G | (x : X) ∈ Γ}).map G.subtype = Subgroup.closure Γ := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hz
      exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
  have hle : G ≤ (Subgroup.closure {x : ↥G | (x : X) ∈ Γ}).map G.subtype := by
    rw [hmap, hG, Subgroup.closure_le]
    exact hab
  rw [eq_top_iff]
  intro x _
  have hsub : {x : ↥G | (x : X) ∈ Γ} ⊆ centSet A := by
    intro x hx
    obtain ⟨u, ⟨u', hu', rfl⟩, hu1, hux⟩ := hΓ x hx
    exact ⟨u', hu', fun h1 => hu1 (by rw [h1]; rfl), Subtype.ext hux⟩
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rw [← Subtype.ext hyx]
  exact Subgroup.closure_mono hsub hy

end CFSG.KD.K36K

end
