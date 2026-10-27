module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1FbarRows
public import CFSG.Certificates.Kernel.Spor.HBfsTree
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.BfsPairsSound
public import CFSG.Certificates.Kernel.SporSch.TblSound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1AutModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ}

theorem mulTreeOK_mulClosureH (gens : Array Table) (cap : ℕ) :
    mulTreeOK n gens (mulClosureH n gens cap).1 (mulClosureH n gens cap).2.1
      (mulClosureH n gens cap).2.2 = true := by
  have e : mulClosureH n gens cap = CFSG.KS.HBfs.hbfs (hkey n)
      (fun l y => compT n y gens[l]!) gens.size (idT n) cap := rfl
  obtain ⟨a1, a2, -, -, a5⟩ := CFSG.KS.HBfs.hbfs_tree (hkey n)
    (fun l y => compT n y gens[l]!) gens.size (idT n) cap
  rw [e]
  unfold mulTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨a1, by rw [a2]; exact CFSG.KS.MulH.tblEqH_self n _⟩,
    CFSG.KS.MulH.allInH_of fun i h1 h2 => ?_⟩
  obtain ⟨b1, b2, b3⟩ := a5 i (by omega) h2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨b1, b2⟩, ?_⟩
  rw [b3]
  exact CFSG.KS.MulH.tblEqH_self n _

theorem tp_mem_genOf_of_memT_mul {cap : ℕ} (hn : n < 2 ^ 32) {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) {x : Table} (hx : permOK n x = true)
    (h : memT n (mulClosureH n gs.toArray cap).1 x = true) : tp n x ∈ genOf n gs := by
  have hga : ∀ l < gs.toArray.size, Rep n gs.toArray[l]! (tp n gs.toArray[l]!) ∧
      tp n gs.toArray[l]! ∈ genOf n gs := fun l hl =>
    ⟨rep_tp (hg _ (by simpa using getElem!_mem_array hl)),
      subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hE := mulTreeOK_spec hn (genOf n gs) hga (mulTreeOK_mulClosureH gs.toArray cap)
  have hErep : ∀ k < (mulClosureH n gs.toArray cap).1.size,
      Rep n (mulClosureH n gs.toArray cap).1[k]!
        (tablePerm n (mulClosureH n gs.toArray cap).1[k]!) ∧
      tablePerm n (mulClosureH n gs.toArray cap).1[k]! ∈ genOf n gs := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hE k hk
    rw [tablePerm_eq hrep]
    exact ⟨hrep, hc⟩
  obtain ⟨k, hk, hxk⟩ := memT_spec (fun k hk => (hErep k hk).1) (rep_tp hx) h
  rw [hxk]
  exact (hErep k hk).2

theorem pocket_of_facts {A₀ : Subgroup (Equiv.Perm (Fin n))} {cap : ℕ} {gs : List Table}
    {t₂ : Table} {tg : Equiv.Perm (Fin n)} {rho : List Table} (hn : n < 2 ^ 32)
    (ht : Rep n t₂ tg) (hord : orderOf tg = 2) (hgs : ∀ g ∈ gs, Rep n g (tp n g))
    (hle : genOf n gs ≤ A₀ ⊓ centralizer ({tg} : Set (Equiv.Perm (Fin n))))
    (hN : A₀ ⊓ centralizer ({tg} : Set (Equiv.Perm (Fin n))) ≤
      normalizer (genOf n gs : Set (Equiv.Perm (Fin n))))
    (h : pocketOK n cap gs t₂ rho = true) : IsI4PlusIn A₀ tg := by
  have hgp : ∀ g ∈ gs, permOK n g = true := fun g hg => CFSG.KC.BfsPairs.permOK_of_rep (hgs g hg)
  have hgc : ∀ c ∈ gs, permOK n c = true ∧ invOK n c (invT n c) = true :=
    fun g hg => ⟨hgp g hg, CFSG.KS.Tbl.invOK_invT hn (hgs g hg)⟩
  simp only [pocketOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hpr⟩, hhom⟩, hinj⟩, hany⟩, hmem⟩, hK24⟩, hnorm⟩ := h
  have hperm : ∀ A : SL2F3, permOK n (rhoT n rho A) = true := by
    intro A
    have hA : slCode A < rho.length := by rw [hlen]; exact slCode_lt A
    rw [rhoT, List.getD_eq_getElem _ _ hA]
    exact hpr _ (List.getElem_mem hA)
  have hrep : ∀ A : SL2F3, Rep n (rhoT n rho A) (tp n (rhoT n rho A)) := fun A => rep_tp (hperm A)
  have hmul : ∀ A B : SL2F3,
      tp n (rhoT n rho (A * B)) = tp n (rhoT n rho A) * tp n (rhoT n rho B) := by
    intro A B
    exact ((tblEq_iff_eq (Rep.compT (hrep A) (hrep B)) (hrep (A * B))).1
      (hhom A (slList_complete A) B (slList_complete B))).symm
  let ρ : SL2F3 →* Equiv.Perm (Fin n) := MonoidHom.mk' (fun A => tp n (rhoT n rho A)) hmul
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : tblEq n (rhoT n rho A) (idT n) = true :=
      (tblEq_idT_iff hn (hrep A)).2 hA
    rcases hinj A (slList_complete A) with h2 | h2
    · rw [h1] at h2
      exact absurd h2 (by decide)
    · exact h2
  obtain ⟨A₂, -, hA₂⟩ := hany
  have hA₂' : ρ A₂ = tg := (tblEq_iff_eq (hrep A₂) ht).1 hA₂
  have hKset : genOf n (slList ()|>.map (rhoT n rho)) = ρ.range := by
    rw [genOf, ← Subgroup.closure_eq ρ.range, MonoidHom.coe_range]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨A, -, rfl⟩ := List.mem_map.mp (by simpa using hx)
      exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨rhoT n rho A, by simpa using List.mem_map_of_mem (slList_complete A), rfl⟩
  have hKM : ρ.range ≤ genOf n gs := by
    rintro _ ⟨A, rfl⟩
    exact tp_mem_genOf_of_memT_mul hn hgp (hperm A)
      (hmem _ (List.mem_map_of_mem (slList_complete A)))
  have hNK := normOK_spec hn (fun g hg => by
    obtain ⟨A, -, rfl⟩ := List.mem_map.mp hg
    exact hperm A) hK24 hgc hnorm
  rw [hKset] at hNK
  refine sec63PC_isI4PlusIn_of_chain hord (MonoidHom.mem_range.2 ⟨A₂, hA₂'⟩) hKM hle
    (fun k hk m hm => (mem_normalizer_iff.mp (hNK hm) k).mp hk)
    (fun m hm c hc => (mem_normalizer_iff.mp (hN hc) m).mp hm)
    (isSL23Mod_of_mulEquiv (MonoidHom.ofInjective hρinj) isSL23Mod_sl2f3)

variable {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  {sift : Table → Bool} {cap : ℕ} {runs : List Run}

theorem outerOK_fact_of_facts (hD : GroupData n A₀ pg gg sift)
    (hRun : ∀ R ∈ runs, RunFacts A₀ R)
    (hrows : ∀ i < runs.length, ∀ r ∈ (runs.getD i default).rows, FbarRowFacts A₀ (i == 0) r)
    {l₁ l₂ : Table} {tg : Equiv.Perm (Fin n)} (hl₁ : permOK n l₁ = true)
    (hl₂ : permOK n l₂ = true) (hA : Sec63PCA6 A₀ tg (genOf n [l₁, l₂]))
    {d : Certificates.Asc82Fbar.OuterData} (h : outerOK n cap sift runs l₁ l₂ d = true) :
    Sec63PCFact A₀ tg := by
  have hn := hD.lt
  have hg2 : ∀ g ∈ [l₁, l₂], permOK n g = true := by
    intro g hg
    rcases List.mem_pair.mp hg with rfl | rfl
    · exact hl₁
    · exact hl₂
  simp only [outerOK] at h
  split at h
  next _ t₂ outer cs co cg op od gs ord heq =>
    obtain ⟨R, hRget, hrowget⟩ := Option.bind_eq_some_iff.mp heq
    obtain ⟨hi, hRi⟩ := List.getElem?_eq_some_iff.mp hRget
    obtain ⟨hj, hrj⟩ := List.getElem?_eq_some_iff.mp hrowget
    have hR : R ∈ runs := by
      rw [← hRi]
      exact List.getElem_mem hi
    have hrmem : (⟨⟨t₂, outer, cs, co, cg, op, od⟩, .small gs ord⟩ : Row) ∈ R.rows := by
      rw [← hrj]
      exact List.getElem_mem hj
    have hRF₂ := (hRun R hR).row _ hrmem
    have hrow := hrows d.run hi _ (by rw [List.getD_eq_getElem _ _ hi, hRi]; exact hrmem)
    simp only [FbarRowFacts] at hrow
    obtain ⟨-, hgs, hle, hN⟩ := hrow
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨henum, hpb⟩, -⟩, -⟩, hall⟩, hpc⟩, hsc⟩, htb⟩, hpock⟩ := h
    have hpocket : IsI4PlusIn A₀ (tp n t₂) :=
      pocket_of_facts hn hRF₂.rep hRF₂.ord hgs hle hN hpock
    have hb : Rep n d.b (tp n d.b) := rep_tp hpb
    have hc : Rep n d.c (tp n d.c) := rep_tp hpc
    have hcA : tp n d.c ∈ A₀ := (hD.sift _ _ hc).1 hsc
    have hct : tp n d.c * tp n t₂ * (tp n d.c)⁻¹ = tp n d.b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (tblEq_iff_eq (Rep.compT hc hRF₂.rep) (Rep.compT hb hc)).1 htb
    have hpocketb : IsI4PlusIn A₀ (tp n d.b) := by
      have h1 := sec63PC_isI4PlusIn_conj hcA hpocket
      rwa [hct] at h1
    exact sec63PC_fact_outer hA (allInvConj_spec hn hg2 henum hb hall) hpocketb
  next => exact absurd h (by decide)

theorem rowFbar_fact_of_facts (hD : GroupData n A₀ pg gg sift)
    (hRun : ∀ R ∈ runs, RunFacts A₀ R)
    (hrows : ∀ i < runs.length, ∀ r ∈ (runs.getD i default).rows, FbarRowFacts A₀ (i == 0) r)
    {r : Row} (hRF : RowFacts A₀ r.row) {first : Bool} (hrow : FbarRowFacts A₀ first r)
    (hfirst : r.row.outer = false → first = true) {inn : InnerData}
    {out : Certificates.Asc82Fbar.OuterData}
    (hF : rowFbarOK n cap sift runs inn out r = true) : Sec63PCFact A₀ (tp n r.row.rep) := by
  have hn := hD.lt
  unfold FbarRowFacts at hrow
  match hk : r.kind with
  | .inner =>
    rw [hk] at hrow
    exact absurd (hfirst hrow.1) (by rw [hrow.2]; decide)
  | .noFive =>
    rw [hk] at hrow
    exact sec63PC_fact_of_not_five_dvd hrow
  | .small gs ord =>
    rw [hk] at hrow
    exact sec63PC_fact_of_not_five_dvd hrow.1
  | .five gs ord =>
    rw [hk] at hrow
    simp only [rowFbarOK, hk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hF
    obtain ⟨hgs, hcard⟩ := hrow
    obtain ⟨h16, h25⟩ := hF
    refine sec63PC_fact_of_five (S := tp n '' {x | x ∈ gs.toArray}) ?_ ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hgs g (by simpa using hg)
    · intro _ h25'
      rw [hRF.card] at h25'
      exact h25 (Nat.mod_eq_zero_of_dvd h25')
    · change 16 ∣ Nat.card ↥(genOf n gs)
      rw [hcard]
      exact Nat.dvd_of_mod_eq_zero h16
  | .a6 l₁ l₂ w =>
    rw [hk] at hrow
    obtain ⟨hl₁, hl₂, hle, hN, hpow, ⟨e⟩⟩ := hrow
    have hA : Sec63PCA6 A₀ (tp n r.row.rep) (genOf n [l₁, l₂]) := by
      refine ⟨hle, fun c hc x hx => (mem_normalizer_iff.mp (hN hc) x).mp hx, hpow, ?_⟩
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    have hp₁ := CFSG.KC.BfsPairs.permOK_of_rep hl₁
    have hp₂ := CFSG.KC.BfsPairs.permOK_of_rep hl₂
    cases hout : r.row.outer
    · simp only [rowFbarOK, hk, hout, Bool.false_eq_true, if_false] at hF
      exact innerOK_fact hD hRF.rep hp₁ hp₂ hA hF
    · simp only [rowFbarOK, hk, hout, if_true] at hF
      exact outerOK_fact_of_facts hD hRun hrows hp₁ hp₂ hA hF

theorem fbar_of_facts {P : Type} [Group P] [Finite P] (M : AutModel P n)
    (hD : GroupData n A₀ pg gg sift) (hrange : M.π.range = A₀) {extra : List Table}
    (hextra : ∀ u ∈ extra, extraOK n pg sift u = true) (hne : runs ≠ [])
    (hcos : ∀ α : MulAut P, M.T α ∈ A₀ ∨ (∃ R ∈ runs, M.T α * (tp n R.u)⁻¹ ∈ A₀) ∨
      (∃ u ∈ extra, M.T α * (tp n u)⁻¹ ∈ A₀))
    (hRun : ∀ R ∈ runs, RunFacts A₀ R)
    (hrows : ∀ i < runs.length, ∀ r ∈ (runs.getD i default).rows, FbarRowFacts A₀ (i == 0) r)
    {inn : InnerData} {out : Certificates.Asc82Fbar.OuterData}
    (hF : fbarCheck n cap sift runs inn out = true) (α : MulAut P) (hα : orderOf α = 2) :
    Sec63PTFactAt P α := by
  classical
  have hlen : 0 < runs.length := List.length_pos_of_ne_nil hne
  have hidx : ∀ R ∈ runs, ∃ i < runs.length, runs.getD i default = R := by
    intro R hR
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
    exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩
  set τ := M.T α with hτdef
  have hτ2 : orderOf τ = 2 := (M.orderOf_T α).trans hα
  obtain ⟨i, hi, hτR⟩ : ∃ i < runs.length,
      (τ ∈ A₀ ∧ i = 0) ∨ τ * (tp n (runs.getD i default).u)⁻¹ ∈ A₀ := by
    rcases mem_A₀_or_run_of_involution hD hextra hτ2 (hcos α) with h0 | ⟨R, hR, hRu⟩
    · exact ⟨0, hlen, Or.inl ⟨h0, rfl⟩⟩
    · obtain ⟨i, hi, rfl⟩ := hidx R hR
      exact ⟨i, hi, Or.inr hRu⟩
  set R := runs.getD i default with hRdef
  have hR : R ∈ runs := by
    rw [hRdef, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hRF₀ := hRun R hR
  have hτmem : τ ∈ A₀ ⊔ zpowers (tp n R.u) := by
    rcases hτR with ⟨h0, -⟩ | hRu
    · exact mem_sup_left h0
    · refine (hRF₀.memR τ).mpr (Or.inr ?_)
      have hUinv : (tp n R.u)⁻¹ = tp n R.u := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hRF₀.u2]
      rwa [hUinv] at hRu
  obtain ⟨r, hr, g, hg, hτg⟩ := hRF₀.cover τ hτmem hτ2
  have hRF := hRF₀.row r hr
  have hrow := hrows i hi r hr
  have hfirst : r.row.outer = false → (i == 0) = true := by
    intro hout
    have htA : tp n r.row.rep ∈ A₀ := by
      by_contra hnot
      rw [hRF.outer.mpr hnot] at hout
      exact Bool.noConfusion hout
    have hτA : τ ∈ A₀ := by
      rw [hτg]
      exact A₀.mul_mem (A₀.mul_mem hg htA) (A₀.inv_mem hg)
    rcases hτR with ⟨-, rfl⟩ | hRu
    · rfl
    · exfalso
      apply hRF₀.uout
      have h1 : tp n R.u = (τ * (tp n R.u)⁻¹)⁻¹ * τ := by group
      rw [h1]
      exact A₀.mul_mem (A₀.inv_mem hRu) hτA
  have hrF : rowFbarOK n cap sift runs inn out r = true := by
    simp only [fbarCheck, List.all_eq_true] at hF
    exact hF R hR r hr
  have hfact : Sec63PCFact A₀ (tp n r.row.rep) :=
    rowFbar_fact_of_facts hD hRun hrows hRF hrow hfirst hrF
  have hfact' : Sec63PCFact A₀ τ := by
    rw [hτg]
    exact sec63PC_fact_conj hg hfact
  have hfix : (fixSub α).map M.π = M.π.range ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin n))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact ((M.fixed_iff α x).mp (mem_fixSub_iff.mp hx)).symm
    · intro hy
      obtain ⟨⟨x, rfl⟩, hyc⟩ := mem_inf.mp hy
      rw [mem_centralizer_singleton_iff] at hyc
      exact ⟨x, mem_fixSub_iff.mpr ((M.fixed_iff α x).mpr hyc.symm), rfl⟩
  refine sec63PC_factAt_of_fact M.π M.inj α τ hfix ?_
  rw [hrange]
  exact hfact'

end CFSG.OddStandard.SmallF3.Omega
