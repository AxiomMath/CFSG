
module

public import Certificates.Data.Kernel.CoreD2K.Pairs
public import CFSG.Certificates.Kernel.CoreD2K.Sound

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm

theorem isPGroup_of_pow_eq_one {X : Type*} [Group X] {p : ℕ} {H : Subgroup X}
    (h : ∀ x ∈ H, x ^ p = 1) : IsPGroup p H :=
  fun x => ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, h _ x.2, Subgroup.coe_one])⟩

theorem isPGroup_closure_three {X : Type*} [Group X] [Finite X] {p : ℕ} {e₀ e₁ e₂ : X}
    (h0 : e₀ ^ p = 1) (h1 : e₁ ^ p = 1) (h2 : e₂ ^ p = 1) (h02 : e₀ * e₂ = e₂ * e₀)
    (hN : e₁ ∈ Subgroup.normalizer ((Subgroup.closure ({e₀, e₂} : Set X) : Subgroup X) : Set X))
    {E : Subgroup X} (hE : ∀ x ∈ E, x ∈ Subgroup.closure ({e₀, e₁, e₂} : Set X)) :
    IsPGroup p E := by
  have hNp : IsPGroup p (Subgroup.closure ({e₀, e₂} : Set X)) :=
    isPGroup_of_pow_eq_one (isElemAbelian_closure_pair h0 h2 h02).2
  have hZp : IsPGroup p (Subgroup.zpowers e₁) := isPGroup_of_pow_eq_one fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  have hH := hZp.to_sup_of_normal_right' hNp (Subgroup.zpowers_le.2 hN)
  refine hH.to_le fun x hx => ?_
  have hle : Subgroup.closure ({e₀, e₁, e₂} : Set X) ≤
      Subgroup.zpowers e₁ ⊔ Subgroup.closure ({e₀, e₂} : Set X) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact le_sup_right (a := Subgroup.zpowers e₁) (Subgroup.subset_closure (by simp))
    · exact le_sup_left (b := Subgroup.closure ({e₀, e₂} : Set X)) (Subgroup.mem_zpowers y)
    · exact le_sup_right (a := Subgroup.zpowers e₁) (Subgroup.subset_closure (by simp))
  exact hle (hE x hx)

theorem kindK_zero {n w p u v g f1 f2 f3 f4 : Nat} (h : kindK n w p u v g 0 f1 f2 f3 f4 = true) :
    Nat.beq (pcomp n w (mask w) g u)
        (pcomp n w (mask w) (pcomp n w (mask w) (pw n w u f1) (pw n w v f2)) g) = true ∧
      Nat.beq (pcomp n w (mask w) g v)
        (pcomp n w (mask w) (pcomp n w (mask w) (pw n w u f3) (pw n w v f4)) g) = true := by
  unfold kindK at h
  rw [PK.strictB_eq] at h
  exact band_e h

theorem gensK_facts {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    (hn : szOK n w = true) (hgens : gensK n w V GP GPI EG GT GTI = true)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    (∀ k < V.base.eW.length, PR n w (EG k) ((V.base.eW.map (wordVal [a, b])).getD k 1)) ∧
    (∀ j < V.base.gWs.length, PR n w (GT j) ((V.base.gWs.map (wordVal [a, b])).getD j 1)) ∧
    ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length wd r = true →
        TabRep (unpack n w r) (wordVal (V.base.gWs.map (wordVal [a, b])) wd) := by
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  unfold gensK at hgens
  obtain ⟨hG2, hrest⟩ := band_e hgens
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
  have hEP : ∀ k < V.base.eW.length, PR n w (EG k) ((V.base.eW.map (wordVal S)).getD k 1) := by
    intro k hk
    obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hE1 k hk)
    refine ⟨h2, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      ← List.getD_eq_getElem _ [] hk]
    exact hword h1
  have hgP : ∀ j < V.base.gWs.length, PR n w (GT j) ((V.base.gWs.map (wordVal S)).getD j 1) := by
    intro j hj
    obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hG1 j hj)
    refine ⟨(perm_canon h2 hn).1, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      ← List.getD_eq_getElem _ [] hj]
    exact hword h1
  have hGTp : allN V.base.gWs.length (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) =
      true := PK.allN_iff.2 fun j hj => (band_e (PK.allN_iff.1 hG1 j hj)).2
  exact ⟨hEP, hgP, fun h => pr_word (by simp) hGTp (fun j hj => (hgP j hj).2) h⟩

theorem coreGenerationOf_of_pchecks {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    {f1 f2 f3 f4 : Nat} (hn : szOK n w = true) (hgens : gensK n w V GP GPI EG GT GTI = true)
    (hpairs : pairsK n w V.base GP EG GT GTI = true)
    (hnorm : normK n w V.base.p V.base.eW.length EG f1 f2 f3 f4 = true) (hp : V.base.p.Prime)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    CoreGenerationOf ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) V.base.p := by
  obtain ⟨hEP, hgP, hwordG⟩ := gensK_facts hn hgens ha hb
  set D := V.base with hD
  set p := D.p with hpdef
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  set ne := D.eW.length with hne
  set Le : List (Equiv.Perm (Fin n)) := D.eW.map (wordVal S) with hLe
  set Lg : List (Equiv.Perm (Fin n)) := D.gWs.map (wordVal S) with hLg
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hLmem : ∀ k < ne, Le.getD k 1 ∈ Le := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLe] using hk)]
    exact List.getElem_mem _
  have hLgmem : ∀ j < D.gWs.length, Lg.getD j 1 ∈ Lg := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj)]
    exact List.getElem_mem _
  set E := Subgroup.closure {g | g ∈ Le} with hEdef
  have hEG : E ≤ G := by
    rw [hEdef, Subgroup.closure_le]
    intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  have hmemE : ∀ k < ne, Le.getD k 1 ∈ E := fun k hk => Subgroup.subset_closure (hLmem k hk)
  unfold normK at hnorm
  obtain ⟨h3, hnorm⟩ := band_e hnorm
  obtain ⟨h0p, hnorm⟩ := band_e hnorm
  obtain ⟨h1p, hnorm⟩ := band_e hnorm
  obtain ⟨h2p, hnorm⟩ := band_e hnorm
  obtain ⟨h02, hk⟩ := band_e hnorm
  have hne3 : ne = 3 := Nat.eq_of_beq_eq_true h3
  have hP0 := hEP 0 (by omega)
  have hP1 := hEP 1 (by omega)
  have hP2 := hEP 2 (by omega)
  obtain ⟨n1, n2⟩ := kindK_zero hk
  have hEp : IsPGroup p E := by
    refine isPGroup_closure_three (e₀ := Le.getD 0 1) (e₁ := Le.getD 1 1) (e₂ := Le.getD 2 1)
      ((pr_beq (pr_pow hn hP0 p) (pr_one hn)).1 h0p) ((pr_beq (pr_pow hn hP1 p) (pr_one hn)).1 h1p)
      ((pr_beq (pr_pow hn hP2 p) (pr_one hn)).1 h2p)
      ((pr_beq (pr_mul hP0 hP2) (pr_mul hP2 hP0)).1 h02)
      (mem_normalizer_closure_pair (α := f1) (β := f2) (γ := f3) (δ := f4)
        ((pr_beq (pr_mul hP1 hP0) (pr_mul (pr_mul (pr_pow hn hP0 f1) (pr_pow hn hP2 f2)) hP1)).1 n1)
        ((pr_beq (pr_mul hP1 hP2)
          (pr_mul (pr_mul (pr_pow hn hP0 f3) (pr_pow hn hP2 f4)) hP1)).1 n2)) fun x hx => ?_
    refine (Subgroup.closure_le _).2 ?_ hx
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have hk' : k < 3 := by simpa [hLe, ← hne, hne3] using hk
    rw [← List.getD_eq_getElem _ 1 hk]
    interval_cases k <;> exact Subgroup.subset_closure (by simp)
  unfold pairsK at hpairs
  obtain ⟨hpall, hpairs⟩ := band_e hpairs
  obtain ⟨hfus, hpairs⟩ := band_e hpairs
  obtain ⟨hwA, hwB⟩ := band_e hpairs
  unfold fusK at hfus
  obtain ⟨-, hfall⟩ := band_e hfus
  have hΓ : ∀ g ∈ {g | g ∈ Lg}, ∃ u v : Equiv.Perm (Fin n), u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧
      v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
        g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < D.gWs.length := by simpa [hLg] using hj
    rw [← List.getD_eq_getElem _ 1 hj]
    obtain ⟨hfp, hkj⟩ := band_e (PK.allN_iff.1 hfall j hj')
    generalize hf : D.fd.getD j default = f at hfp hkj
    have hfp' : f.pair < D.pairs.length := Nat.blt_eq.mp hfp
    generalize hq : D.pairs.getD f.pair (0, 0) = q at hkj
    have hpq : pairPK n w p ne EG q = true := by
      have := PK.allN_iff.1 hpall f.pair hfp'
      rwa [hq] at this
    unfold pairPK at hpq
    obtain ⟨hq1, hpq⟩ := band_e hpq
    obtain ⟨hq2, hpq⟩ := band_e hpq
    rw [PK.strictB_eq, PK.strictB_eq] at hpq
    obtain ⟨hup, hpq⟩ := band_e hpq
    obtain ⟨hu1, hpq⟩ := band_e hpq
    obtain ⟨huv, hvK⟩ := band_e hpq
    unfold vK at hvK
    obtain ⟨hvp, hvu⟩ := band_e hvK
    have hq1' : q.1 < ne := Nat.blt_eq.mp hq1
    have hq2' : q.2 < ne := Nat.blt_eq.mp hq2
    have hu := hEP q.1 hq1'
    have hv := hEP q.2 hq2'
    have hg := hgP j hj'
    obtain ⟨e1, e2⟩ := kindK_zero hkj
    refine ⟨_, _, hmemE _ hq1', hmemE _ hq2', (pr_beq (pr_pow hn hu p) (pr_one hn)).1 hup,
      (pr_beq (pr_pow hn hv p) (pr_one hn)).1 hvp, (pr_beq (pr_mul hu hv) (pr_mul hv hu)).1 huv,
      pr_ne hu (pr_one hn) hu1, fun k hk => pr_ne hv (pr_pow hn hu k) (PK.allN_iff.1 hvu k hk),
      f.α, f.β, f.γ, f.δ, ?_, ?_⟩
    · exact (pr_beq (pr_mul hg hu) (pr_mul (pr_mul (pr_pow hn hu f.α) (pr_pow hn hv f.β)) hg)).1 e1
    · exact (pr_beq (pr_mul hg hv) (pr_mul (pr_mul (pr_pow hn hu f.γ) (pr_pow hn hv f.δ)) hg)).1 e2
  have hA' : wordVal Lg D.wA = a := (hwordG hwA).perm_eq ha
  have hB' : wordVal Lg D.wB = b := (hwordG hwB).perm_eq hb
  refine coreGenerationOf_of_gens hp rfl hEp hEG (Γ := {g | g ∈ Lg}) ?_ ?_ hΓ
  · intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  · intro z hz
    rcases hz with rfl | hz
    · rw [← hA']
      exact wordVal_mem Lg _ (fun g hg => Subgroup.subset_closure hg) _
    · rw [Set.mem_singleton_iff] at hz
      rw [hz, ← hB']
      exact wordVal_mem Lg _ (fun g hg => Subgroup.subset_closure hg) _

end CFSG.KD.CoreD2K

end
