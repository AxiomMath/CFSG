module

public import CFSG.Certificates.Kernel.Spor.SiftBKSound
public import CFSG.Certificates.Kernel.Spor.RawSiftB
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem pg_baseImK {w nb q BP t : Nat} (ht : t < nb) :
    pg w (mask w) (baseImK w (mask w) nb q BP) t = pg w (mask w) q (pg w (mask w) BP t) := by
  set v : Nat → Nat := fun t => pg w (mask w) q (pg w (mask w) BP t) with hv
  have hvl : ∀ t, v t < 2 ^ w := fun t => PF.pg_lt _ _ _
  have key : ∀ k, PF.Fld w ((List.range k).foldl
      (fun acc t => Nat.lor acc (Nat.shiftLeft (v t) (Nat.mul w t))) 0)
      (fun i => if i < k then v i else 0) := by
    intro k
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      exact PF.fld_congr (PF.fld_zero w) (fun i => by simp)
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine PF.fld_congr (PF.fld_or ih (PF.fld_shl k (PF.fld_one (hvl k)))) (fun i => ?_)
      by_cases h1 : i < k
      · simp [h1, show i < k + 1 by omega, show ¬ k ≤ i by omega]
      · by_cases h2 : i = k
        · subst h2
          simp
        · simp [h1, show ¬ i < k + 1 by omega, show k ≤ i by omega,
            show i - k ≠ 0 by omega]
  have e : baseImK w (mask w) nb q BP = (List.range nb).foldl
      (fun acc t => Nat.lor acc (Nat.shiftLeft (v t) (Nat.mul w t))) 0 := by
    unfold baseImK
    rw [foldUp_eq]
  rw [e, PF.pg_of_fld (key nb) (by simp only [ht, ↓reduceIte]; exact hvl t)]
  simp only [ht, ↓reduceIte, hv]

section SiftMem

variable {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  {W : Array (List Int)}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hd : Hd n S base kO W)
include hb hp hd

theorem sift_mem_aux (hn : 0 < n) (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
    {LR ST : Nat → Nat} (hst : StepsOK n w PS ST kS nb BP) (hag : TreeAgree n w nb S base LR)
    {X : Subgroup (Equiv.Perm (Fin n))} (hGX : Gen n S kO ≤ X)
    (hX : ∀ G ∈ X, (∀ t < base.size, ∀ h : base[t]! < n, G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) →
      G = 1) :
    ∀ d l, l + d = nb → ∀ (G : Nat) (γ : Equiv.Perm (Fin n)),
      BI n w nb l G (fun t => toF hn base[t]!) γ → γ ∈ X →
      (∀ t < l, ∀ h : base[t]! < n, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) →
      siftBK n w (mask w) (n * w) nb PS PSI LR ST kS d l G = true → γ ∈ Gen n S kO := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl G γ _ hγX hfix _
    rw [hX γ hγX (fun t ht h => hfix t (by omega) h)]
    exact Subgroup.one_mem _
  | succ d ih =>
    intro l hl G γ hG hγX hfix h
    have hlb : l < nb := by omega
    have hlb' : l < base.size := by omega
    obtain ⟨hpar, A⟩ := hag l hlb
    obtain ⟨_, _, _, hinv⟩ := kernel_steps hb hp hk hbl hlb.le
    have F := lev_facts hd hlb'
    have hbl' := hbl l hlb
    rw [siftBK_succ, hst l hlb] at h
    simp only [strictB_eq, bIf_eq] at h
    have hGl := hG l le_rfl hlb
    simp only [toF_eq hn hbl'] at hGl
    have hzn : pg w (mask w) G l < n := by
      rw [hGl]
      exact (γ ⟨base[l]!, hbl'⟩).2
    split at h
    · rename_i hk1
      have hk' := Nat.blt_eq.mp hk1
      have hK := (A.pos _ hzn).1 hk'
      have hKe := A.posE _ hzn hK
      set K := rpos w (mask w) (n * w) (LR l) (pg w (mask w) G l) with hKdef
      have hW := bi_walkIT (σ := stp n S base l) (b := fun t => toF hn base[t]!)
        (fun k hk hk0 => (hpar k hk hk0).1)
        (fun k hk hk0 => hinv _ (hpar k hk hk0).2) K K hk' G γ (bi_mono hG)
      have hKm : K < (lev n S base l).pts.size := by rw [hKe]; exact hK
      have eT : treeF (stp n S base l) (rpar w (mask w) (n * w) (LR l))
          (rlab n (n * w) (LR l)) K K = trP n S base l K :=
        Rep.unique (A.tr K hKm).1 (rep_tr hd hlb' hKm)
      rw [eT] at hW
      have hT := tr_spec hd hlb' K hKm
      have hTi := Subgroup.inv_mem _ hT.1
      have hfix' : ∀ t < l + 1, ∀ h : base[t]! < n,
          ((trP n S base l K)⁻¹ * γ) ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩ := by
        intro t ht hb'
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · rw [Equiv.Perm.mul_apply, hfix t ht hb', hTi.2 t ht hb']
        · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
          apply Fin.ext
          rw [hT.2, hKe, F.pts_pos _ hzn hK, hGl]
      have hres := ih (l + 1) (by omega) _ _ hW (Subgroup.mul_mem _ (hGX hTi.1) hγX) hfix' h
      have hm := Subgroup.mul_mem _ hT.1.1 hres
      rwa [mul_inv_cancel_left] at hm
    · exact absurd h Bool.false_ne_true

end SiftMem

end CFSG.KS.Raw.Orb

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw.Orb

theorem siftBK_mem {n w kS kO nb BP : Nat} {PS PSI LR ST : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) (hst : StepsOK n w PS ST kS nb BP)
    {X : Subgroup (Equiv.Perm (Fin n))} (hSX : ∀ j < kS, permOfArr n S[j]! ∈ X)
    (hX : ∀ G ∈ X, (∀ t < base.size, ∀ h : base[t]! < n, G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) →
      G = 1)
    {q : Nat} {G : Equiv.Perm (Fin n)} (hq : Rep n (unpack n w q) G) (hG : G ∈ X)
    (hs : siftBK n w (mask w) (n * w) nb PS PSI LR ST kS nb 0 (baseImK w (mask w) nb q BP) =
      true) :
    G ∈ Subgroup.closure {g : Equiv.Perm (Fin n) | ∃ j < S.size, permOfArr n S[j]! = g} := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of hb hh
  have hd := Orb.hd_of_head hk hH
  obtain ⟨hp, _, hkS⟩ := Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hSs : S.size = kS := hb.2.2.2.1
  have hn : 0 < n := hb.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht' => hd.base_lt t (by omega)
  have hsub : Set.range (fun j : Fin kO => permOfArr n S[j.val]!) ⊆
      {g : Equiv.Perm (Fin n) | ∃ j < S.size, permOfArr n S[j]! = g} := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j.val, lt_of_lt_of_le j.2 hd.kO_le, rfl⟩
  have hGX : Gen n S kO ≤ X := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact hSX j.val (by have := hd.kO_le; omega)
  have hBI : BI n w nb 0 (baseImK w (mask w) nb q BP) (fun t => toF hn base[t]!) G := by
    intro t _ ht2
    have e := hq ⟨base[t]!, hbl t ht2⟩
    rw [unpack, getElem!_ofFn_nat _ (hbl t ht2)] at e
    beta_reduce
    rw [pg_baseImK ht2, toF_eq hn (hbl t ht2), ← hb.2.2.2.2.2.2 t ht2]
    exact e
  exact Subgroup.closure_mono hsub (sift_mem_aux hb hp hd hn hkS hbl hst
    (treeAgree_of hb hp hbl ht) hGX hX nb 0 (by omega) _ G hBI hG
    (fun t ht' => absurd ht' (Nat.not_lt_zero t)) hs)

end CFSG.KS.Raw

end
