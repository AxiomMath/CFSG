module

public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabSuzB

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne
open CFSG.Certificates.ChainArrays

@[expose] def pheadOKQ (n : ℕ) (L : Array Level) (base : Array ℕ) (xs : Array (Array ℕ))
    (rels : List (ℕ × ℕ × ℕ)) (T : Array ℕ → Bool) : ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => T acc
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOK base xs rels i acc (L[i]!).pts[k]!) ||
        pheadOKQ n L base xs rels T fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

section Facts

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}
  (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem pheadOKQ_spec {X : Equiv.Perm (Fin n)}
    {xs : Array (Array ℕ)} (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e))
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {T : Array ℕ → Bool} :
    ∀ fuel i, i + fuel ≤ Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      pheadOKQ n (rawLevels n S base) base xs rels T fuel i acc = true →
      ∀ h ∈ Q.levelSubgroup i, A * h * X = X * (A * h) →
        ∃ e, T e = true ∧ ∀ l (hl : l < Q.baseCount), l < i + fuel →
          e[base[l]!]! = ((A * h) (Q.base.get ⟨l, hl⟩) : ℕ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc A hacc htail h hh hcomm
    simp only [pheadOKQ] at htail
    refine ⟨acc, htail, fun l hl hli => ?_⟩
    have hbase : ((Q.base.get ⟨l, hl⟩ : Fin n) : ℕ) = base[l]! := hA.base_val ⟨l, hl⟩
    have hfix := Q.levelSubgroup_fixes_base_index i h hh ⟨l, hl⟩ (by simpa using hli)
    rw [Equiv.Perm.mul_apply, hfix, ← hbase]
    exact hacc (Q.base.get ⟨l, hl⟩)
  | succ fuel ih =>
    intro i hi acc A hacc htail h hh hcomm
    have hib : i < Q.baseCount := by omega
    obtain ⟨k, hk, hpt, hk'⟩ := exists_levT_inv_mul_mem hA hF hQ hib hh
    have hstep := allLt_spec htail hk
    have hcX : Commute (A * h) X := hcomm
    have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
      fun m hm => hA.base_val ⟨m, hm⟩
    have himg : ∀ m (hm : m ≤ i), relImg base i acc ((rawLevels n S base)[i]!).pts[k]! m =
        ((A * h) (Q.base.get ⟨m, by omega⟩) : ℕ) := by
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hlt | rfl
      · rw [relImg, ite_eq_left hlt, ← hbase m (by omega), hacc, Equiv.Perm.mul_apply,
          Q.levelSubgroup_fixes_base_index i h hh ⟨m, by omega⟩ hlt]
      · rw [relImg, ite_eq_right (lt_irrefl _), show ((rawLevels n S base)[m]!).pts[k]! =
          (lev n S base m).pts[k]! from rfl, hpt, hacc, Equiv.Perm.mul_apply]
    have hrel : relOK base xs rels i acc ((rawLevels n S base)[i]!).pts[k]! = true := by
      rw [relOK, List.all_eq_true]
      intro r hr
      obtain ⟨he, hl, hl', hrx⟩ := hrels r hr
      rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
      by_cases hmax : max r.1 r.2.1 = i
      · right
        have hl1 : r.1 ≤ i := hmax ▸ le_max_left _ _
        have hl2 : r.2.1 ≤ i := hmax ▸ le_max_right _ _
        have hbs := hA.base_size
        have hXe : (X ^ r.2.2) (Q.base.get ⟨r.1, by omega⟩) = Q.base.get ⟨r.2.1, by omega⟩ := by
          apply Fin.ext
          rw [← hxs r.2.2 he, hbase r.1 (by omega), hbase r.2.1 (by omega), hrx]
        rw [himg r.2.1 hl2, himg r.1 hl1, hxs r.2.2 he, ← hXe]
        congr 1
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, (hcX.pow_right r.2.2).eq]
      · exact Or.inl hmax
    rw [hrel, Bool.not_true, Bool.false_or] at hstep
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have e : A * h = A * levT n S base i k * ((levT n S base i k)⁻¹ * h) := by group
    have hcomm' : A * levT n S base i k * ((levT n S base i k)⁻¹ * h) * X =
        X * (A * levT n S base i k * ((levT n S base i k)⁻¹ * h)) := by
      rw [← e]
      exact hcomm
    obtain ⟨e', hT, hag⟩ := ih (i + 1) (by omega) _ _ hrep hstep _ hk' hcomm'
    refine ⟨e', hT, fun l hl hli => ?_⟩
    have := hag l hl (by omega)
    rw [← e] at this
    exact this

end Facts

@[expose] def agreeBase (base : Array ℕ) (m : ℕ) (e r : Array ℕ) : Bool :=
  allLt m fun l => e[base[l]!]! == r[base[l]!]!

@[expose] def hasAgree (rs : Array (Array ℕ)) (base : Array ℕ) (m : ℕ) (e : Array ℕ) : Bool :=
  !(allLt rs.size fun j => !(agreeBase base m e rs[j]!))

theorem agreeBase_spec {base : Array ℕ} {m : ℕ} {e r : Array ℕ}
    (h : agreeBase base m e r = true) : ∀ l < m, e[base[l]!]! = r[base[l]!]! := by
  intro l hl
  have := allLt_spec h hl
  rwa [beq_iff_eq] at this

theorem exists_agree {rs : Array (Array ℕ)} {base : Array ℕ} {m : ℕ} {e : Array ℕ}
    (h : hasAgree rs base m e = true) :
    ∃ j < rs.size, agreeBase base m e rs[j]! = true := by
  unfold hasAgree at h
  rw [Bool.not_eq_true'] at h
  by_contra hne
  have hall : (allLt rs.size fun j => !(agreeBase base m e rs[j]!)) = true := by
    rw [allLt_iff]
    intro j hj
    cases hb : agreeBase base m e rs[j]! with
    | true => exact absurd ⟨j, hj, hb⟩ hne
    | false => rfl
  rw [hall] at h
  exact absurd h (by decide)

@[expose] def memBkt (n : ℕ) (B : Array (List (Array ℕ))) (a : Array ℕ) : Bool :=
  (B[bucketIdx n a]!).any (eqA n a)

@[expose] def centFilter (n : ℕ) (base : Array ℕ) (gR : Array (Array ℕ)) (r s : Array ℕ) : Bool :=
  allLt gR.size fun l => allLt base.size fun m =>
    r[s[(gR[l]!)[base[m]!]!]!]! == (gR[l]!)[r[s[base[m]!]!]!]!

theorem centFilter_of_comm {n : ℕ} {base r s : Array ℕ} {gR : Array (Array ℕ)}
    {R S' : Equiv.Perm (Fin n)} (hr : Rep n r R) (hs : Rep n s S')
    (hg : ∀ l < gR.size, validA n gR[l]! = true) (hb : ∀ i < base.size, base[i]! < n)
    (hcomm : ∀ l < gR.size, permOfArr n gR[l]! * (R * S') = (R * S') * permOfArr n gR[l]!) :
    centFilter n base gR r s = true := by
  unfold centFilter
  refine allLt_iff.2 fun l hl => allLt_iff.2 fun m hm => ?_
  have hG := rep_of_validA (hg l hl)
  have hbm := hb m hm
  set G := permOfArr n gR[l]! with hGdef
  have e := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ ⟨base[m]!, hbm⟩ : Fin n) : ℕ))
    (hcomm l hl)
  simp only [Equiv.Perm.mul_apply] at e
  have h1 : (gR[l]!)[base[m]!]! = ((G ⟨base[m]!, hbm⟩ : Fin n) : ℕ) := hG ⟨base[m]!, hbm⟩
  have h2 : s[((G ⟨base[m]!, hbm⟩ : Fin n) : ℕ)]! = ((S' (G ⟨base[m]!, hbm⟩) : Fin n) : ℕ) :=
    hs (G ⟨base[m]!, hbm⟩)
  have h3 : r[((S' (G ⟨base[m]!, hbm⟩) : Fin n) : ℕ)]! =
      ((R (S' (G ⟨base[m]!, hbm⟩)) : Fin n) : ℕ) := hr (S' (G ⟨base[m]!, hbm⟩))
  have h4 : s[base[m]!]! = ((S' ⟨base[m]!, hbm⟩ : Fin n) : ℕ) := hs ⟨base[m]!, hbm⟩
  have h5 : r[((S' ⟨base[m]!, hbm⟩ : Fin n) : ℕ)]! = ((R (S' ⟨base[m]!, hbm⟩) : Fin n) : ℕ) :=
    hr (S' ⟨base[m]!, hbm⟩)
  have h6 : (gR[l]!)[((R (S' ⟨base[m]!, hbm⟩) : Fin n) : ℕ)]! =
      ((G (R (S' ⟨base[m]!, hbm⟩)) : Fin n) : ℕ) := hG (R (S' ⟨base[m]!, hbm⟩))
  rw [beq_iff_eq, h1, h2, h3, h4, h5, h6]
  exact e.symm

@[expose] def tailTest (n : ℕ) (base : Array ℕ) (gR : Array (Array ℕ)) (B : Array (List (Array ℕ)))
    (rs : Array (Array ℕ)) (s : Array ℕ) : Bool :=
  leafNC n gR B s && allLt rs.size fun j =>
    !(centFilter n base gR rs[j]! s) || memBkt n B (compA n rs[j]! s)

@[expose] def centSplitOKP (p n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (rs : Array (Array ℕ)) (m : ℕ) (gR : Array (Array ℕ)) (ps : List ℕ)
    (cR : ArrCert) (N : ℕ) : Bool :=
  let L := rawLevels n S base
  let B := mkBuckets n cR.pts.toList
  relsOKP p n base x rels && enumOK n gR ps cR && cR.pts.size == N &&
    allLt gR.size (fun k => commA n gR[k]! x) &&
    allLt gR.size (fun k => siftA n L base 0 gR[k]!) && siftA n L base 0 x &&
    allLt rs.size (fun j => validA n rs[j]! && commA n rs[j]! x && siftA n L base 0 rs[j]! &&
      leafNC n gR B rs[j]!) &&
    pheadOKQ n L base (powPA p n x) rels (hasAgree rs base m) m 0 (idA n) &&
    ptailOKQ n L base x (powPA p n x) rels (tailTest n base gR B rs) (base.size - m) m (idA n)

section Spec

variable {n p chunks m : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
  {base : Array ℕ} {W : Array (List ℤ)}

theorem centSplit_chunks (hA : ChainArrays Q O S base W) (hc0 : 0 < chunks)
    (hc : rawChainOK n O S base W chunks = true) (hm : m ≤ base.size) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {rs gR : Array (Array ℕ)} {ps : List ℕ} {cR : ArrCert} {N : ℕ} (hps : ∀ q ∈ ps, q < n)
    (h : centSplitOKP p n S base x rels rs m gR ps cR N = true) :
    Nat.card (closure (permsA n gR)) = N ∧ X ∈ Q.originalSubgroup ∧
      closure (permsA n gR) ≤ centralizer {X} ⊓ Q.originalSubgroup ∧
      (∀ g ∈ centralizer {X} ⊓ Q.originalSubgroup, ∀ r ∈ closure (permsA n gR),
        g * r * g⁻¹ ∈ closure (permsA n gR)) ∧
      centralizer (closure (permsA n gR) : Set (Equiv.Perm (Fin n))) ⊓
        (centralizer {X} ⊓ Q.originalSubgroup) ≤ closure (permsA n gR) := by
  simp only [centSplitOKP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrels, hR⟩, hsize⟩, hcomm⟩, hsift⟩, hsx⟩, hreps⟩, hhead⟩, htail⟩ := h
  have hcard : Nat.card (closure (permsA n gR)) = N := (enumOK_spec hps hR).2.1.trans hsize
  have hXP : X ∈ Q.originalSubgroup := (siftA_iff_mem_originalSubgroup hA hc0 hc hx).1 hsx
  have hle : closure (permsA n gR) ≤ centralizer {X} ⊓ Q.originalSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hR hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (allLt_spec hcomm hk)
    · exact (siftA_iff_mem_originalSubgroup hA hc0 hc hrep).1 (allLt_spec hsift hk)
  have hVF := chainCheckFacts hc
  have hVQ := (validSchreier_of_chainOK hA hc0 hc).1
  have hxs := rep_powPA (p := p) hx
  have hrels' := relsOKP_spec hrels
  have hbc : base.size = Q.baseCount := hA.base_size
  have hrs : ∀ j < rs.size, ∃ R : Equiv.Perm (Fin n), Rep n rs[j]! R ∧ R ∈ Q.originalSubgroup ∧
      R * X = X * R ∧ ∀ l < gR.size, R * permOfArr n gR[l]! * R⁻¹ ∈ closure (permsA n gR) := by
    intro j hj
    have h1 := allLt_spec hreps hj
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨hv, hcm⟩, hs⟩, hleaf⟩ := h1
    have hRrep := rep_of_validA hv
    exact ⟨_, hRrep, (siftA_iff_mem_originalSubgroup hA hc0 hc hRrep).1 hs,
      (commA_iff hRrep hx).1 hcm, (leafNC_spec hps hR hRrep hleaf).1⟩
  have hgenval : ∀ l < gR.size, validA n gR[l]! = true := fun l hl => enumOK_gens_valid hR hl
  have hbaselt : ∀ i < base.size, base[i]! < n := fun i hi => hVF.base_lt i hi
  have hmain : ∀ c ∈ centralizer {X} ⊓ Q.originalSubgroup,
      (∀ l < gR.size, c * permOfArr n gR[l]! * c⁻¹ ∈ closure (permsA n gR)) ∧
      ((∀ l < gR.size, permOfArr n gR[l]! * c = c * permOfArr n gR[l]!) →
        c ∈ closure (permsA n gR)) := by
    intro c hc'
    obtain ⟨hcX, hcP⟩ := Subgroup.mem_inf.1 hc'
    have hcc : c * X = X * c := Subgroup.mem_centralizer_singleton_iff.1 hcX
    have hc0' : c ∈ Q.levelSubgroup 0 := by
      rw [Q.levelSubgroup_zero_eq_original hVQ]
      exact hcP
    obtain ⟨e, hT, hag⟩ := pheadOKQ_spec hA hVF hVQ hxs hrels' m 0 (by omega) (idA n) 1 rep_idA
      hhead c hc0' (by rw [one_mul]; exact hcc)
    obtain ⟨j, hj, hjag⟩ := exists_agree hT
    obtain ⟨R, hRrep, hRP, hRX, hRnorm⟩ := hrs j hj
    have hageq := agreeBase_spec hjag
    have hsP : R⁻¹ * c ∈ Q.originalSubgroup :=
      Q.originalSubgroup.mul_mem (Q.originalSubgroup.inv_mem hRP) hcP
    have hsfix : ∀ l (hl : l < Q.baseCount), l < m →
        (R⁻¹ * c) (Q.base.get ⟨l, hl⟩) = Q.base.get ⟨l, hl⟩ := by
      intro l hl hlm
      have h1 := hag l hl (by omega)
      rw [one_mul] at h1
      have h2 := hageq l hlm
      have hbl : base[l]! < n := hbaselt l (by omega)
      have h3 : ((Q.base.get ⟨l, hl⟩ : Fin n) : ℕ) = base[l]! := hA.base_val ⟨l, hl⟩
      have h4 : (rs[j]!)[base[l]!]! = ((R (Q.base.get ⟨l, hl⟩) : Fin n) : ℕ) := by
        rw [← h3]
        exact hRrep (Q.base.get ⟨l, hl⟩)
      have h5 : R (Q.base.get ⟨l, hl⟩) = c (Q.base.get ⟨l, hl⟩) :=
        Fin.ext (h4.symm.trans (h2.symm.trans h1))
      rw [Equiv.Perm.mul_apply, ← h5]
      simp
    have hslev : R⁻¹ * c ∈ Q.levelSubgroup m := by
      rw [Q.mem_levelSubgroup_iff hVQ m (by omega)]
      refine ⟨hsP, fun b hb => ?_⟩
      obtain ⟨i, hi, hib⟩ := List.mem_take_iff_getElem.1 hb
      have hi1 : i < m := lt_of_lt_of_le hi (min_le_left _ _)
      have hi2 : i < Q.baseCount := by
        have := lt_of_lt_of_le hi (min_le_right _ _)
        simpa using this
      have hbi : b = Q.base.get ⟨i, hi2⟩ := by
        rw [← hib]
        simp [Vector.get, Vector.getElem_toList]
      rw [hbi]
      exact hsfix i hi2 hi1
    have hscomm : 1 * (R⁻¹ * c) * X = X * (1 * (R⁻¹ * c)) := by
      rw [one_mul]
      have hRc : Commute R⁻¹ X := (show Commute R X from hRX).inv_left
      have hcc' : Commute c X := hcc
      exact (hRc.mul_left hcc').eq
    obtain ⟨e', hrep', hT'⟩ := ptailOKQ_spec hA hVF hVQ hx hxs hrels' (base.size - m) m
      (by omega) (idA n) 1 rep_idA htail _ hslev hscomm
    rw [one_mul] at hrep'
    simp only [tailTest, Bool.and_eq_true] at hT'
    obtain ⟨hleaf', hcent'⟩ := hT'
    have hsnorm := (leafNC_spec hps hR hrep' hleaf').1
    have hRn : ∀ r ∈ closure (permsA n gR), R * r * R⁻¹ ∈ closure (permsA n gR) := by
      refine conj_mem_closure_of_gens (T := permsA n gR) (g := R) (fun t ht => ?_)
      obtain ⟨l, hl, rfl⟩ := ht
      exact hRnorm l hl
    have hceq : c = R * (R⁻¹ * c) := by group
    constructor
    · intro l hl
      have h1 := hRn _ (hsnorm l hl)
      have h2 : c * permOfArr n gR[l]! * c⁻¹ =
          R * ((R⁻¹ * c) * permOfArr n gR[l]! * (R⁻¹ * c)⁻¹) * R⁻¹ := by group
      rw [h2]
      exact h1
    · intro hcent
      have hcrep : Rep n (compA n rs[j]! e') c := by
        have := rep_compA hRrep hrep'
        rwa [← hceq] at this
      have hfilt : centFilter n base gR rs[j]! e' = true :=
        centFilter_of_comm hRrep hrep' hgenval hbaselt fun l hl => by
          rw [← hceq]
          exact hcent l hl
      have hmem := allLt_spec hcent' hj
      rw [hfilt, Bool.not_true, Bool.false_or] at hmem
      obtain ⟨e'', he'', hee⟩ := mem_of_bucket_any hmem
      exact enumOK_mem_of_mem hps hR (rep_of_eqA hcrep hee) he''
  refine ⟨hcard, hXP, hle, ?_, ?_⟩
  · intro g hg r hr
    refine conj_mem_closure_of_gens (T := permsA n gR) (g := g) (fun t ht => ?_) r hr
    obtain ⟨l, hl, rfl⟩ := ht
    exact (hmain g hg).1 l hl
  · intro g hg
    obtain ⟨hgR, hgC⟩ := Subgroup.mem_inf.1 hg
    exact (hmain g hgC).2 fun l hl => mem_centralizer_closure_iff.1 hgR l hl

end Spec

end CFSG.HardMathSupport.Dickson.I271.TabSuzB
