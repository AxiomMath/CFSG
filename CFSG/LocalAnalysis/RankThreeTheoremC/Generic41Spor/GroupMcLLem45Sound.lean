module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLLem45Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45

open Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.AGLEmbedding.FusD2 CFSG.AGLEmbedding.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis
open Certificates.FusD2Perm (powT wordT)

section Orbit

theorem forall_getElem!_push {P : Tab → Prop} {A : Array Tab} (hA : ∀ k < A.size, P A[k]!)
    {x : Tab} (hx : P x) : ∀ k < (A.push x).size, P (A.push x)[k]! := by
  intro k hk
  rw [Array.size_push] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
  · rw [getElem!_pos (A.push x) k (by rwa [Array.size_push]), Array.getElem_push_lt h,
      ← getElem!_pos A k h]
    exact hA k h
  · subst h
    rw [getElem!_pos (A.push x) A.size (by simp), Array.getElem_push_eq]
    exact hx

theorem treeOK_bounds {D : Data} {tr : List (ℕ × ℕ)} (h : McLLem45.treeOK D tr = true) :
    ∀ k < tr.length, (tr[k]!).1 < 1 + k ∧ (tr[k]!).2 < 2 * (nGens D).size := by
  simp only [McLLem45.treeOK, allBelow_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  intro k hk
  obtain ⟨h1, h2⟩ := h k hk
  exact ⟨by omega, h2⟩

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}
variable (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem orbitStep_rep (hNorm : checkHNormal D = true) {A : Array Tab}
    (hA : ∀ k < A.size, ∃ n ∈ Nsub D S, TabRep A[k]! (n * wordVal S D.uW * n⁻¹))
    {p g : ℕ} (hp : p < A.size) (hg : g < 2 * (nGens D).size) :
    ∀ k < (orbitStep D A (p, g)).size,
      ∃ n ∈ Nsub D S, TabRep (orbitStep D A (p, g))[k]! (n * wordVal S D.uW * n⁻¹) := by
  have hinv := invsOK_of_checkHNormal hNorm
  have hng : (nGens D).size = D.nW.length := by simp [nGens]
  have hgen : ∀ j (hj : j < D.nW.length), ∃ m ∈ Nsub D S, TabRep (nGens D)[j]! m ∧
      TabRep (nGensI D)[j]! m⁻¹ := by
    intro j hj
    have hrep := rep_getElem!_of_words S D.gT (giT D) hgs hgi D.nW hj
    refine ⟨_, Subgroup.subset_closure (List.getElem_mem _), hrep, ?_⟩
    exact invsOK_spec hinv (by rw [hng]; exact hj) hrep
  obtain ⟨n₀, hn₀, hrep₀⟩ := hA p hp
  have hP : ∃ n ∈ Nsub D S, TabRep
      (let ng := (nGens D).size
       let gt := if g < ng then (nGens D)[g]! else (nGensI D)[g - ng]!
       let gi := if g < ng then (nGensI D)[g]! else (nGens D)[g - ng]!
       conjTab D.n gt gi A[p]!) (n * wordVal S D.uW * n⁻¹) := by
    by_cases hgl : g < (nGens D).size
    · obtain ⟨m, hm, hmt, hmi⟩ := hgen g (by rwa [hng] at hgl)
      refine ⟨m * n₀, Subgroup.mul_mem _ hm hn₀, ?_⟩
      simp only [hgl, if_true]
      have := hmt.conjTab hrep₀ hmi
      rwa [show m * (n₀ * wordVal S D.uW * n₀⁻¹) * m⁻¹ = m * n₀ * wordVal S D.uW * (m * n₀)⁻¹ by
        group] at this
    · obtain ⟨m, hm, hmt, hmi⟩ := hgen (g - (nGens D).size) (by omega)
      refine ⟨m⁻¹ * n₀, Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn₀, ?_⟩
      simp only [hgl, if_false]
      have hmi' : TabRep (nGens D)[g - (nGens D).size]! (m⁻¹)⁻¹ := by rwa [inv_inv]
      have := hmi.conjTab hrep₀ hmi'
      rwa [show m⁻¹ * (n₀ * wordVal S D.uW * n₀⁻¹) * (m⁻¹)⁻¹ =
        m⁻¹ * n₀ * wordVal S D.uW * (m⁻¹ * n₀)⁻¹ by group] at this
  exact forall_getElem!_push (P := fun t => ∃ n ∈ Nsub D S, TabRep t (n * wordVal S D.uW * n⁻¹))
    hA hP

theorem foldl_orbitStep_rep (hNorm : checkHNormal D = true) :
    ∀ (tr : List (ℕ × ℕ)) (A : Array Tab),
      (∀ k < A.size, ∃ n ∈ Nsub D S, TabRep A[k]! (n * wordVal S D.uW * n⁻¹)) →
      (∀ k < tr.length, (tr[k]!).1 < A.size + k ∧ (tr[k]!).2 < 2 * (nGens D).size) →
      ∀ k < (tr.foldl (orbitStep D) A).size,
        ∃ n ∈ Nsub D S, TabRep (tr.foldl (orbitStep D) A)[k]! (n * wordVal S D.uW * n⁻¹)
  | [], A, hA, _ => by simpa using hA
  | pg :: tr, A, hA, htr => by
    rw [List.foldl_cons]
    obtain ⟨hp, hg⟩ := htr 0 (by simp)
    have hp' : pg.1 < A.size := by simpa using hp
    have hg' : pg.2 < 2 * (nGens D).size := by simpa using hg
    have hstep := orbitStep_rep hgs hgi hNorm hA hp' hg'
    refine foldl_orbitStep_rep hNorm tr (orbitStep D A pg) hstep ?_
    intro k hk
    have := htr (k + 1) (by simpa using hk)
    have hsz : (orbitStep D A pg).size = A.size + 1 := by simp [orbitStep]
    rw [hsz]
    simp only [List.getElem!_cons_succ] at this
    refine ⟨by omega, this.2⟩

theorem orbitList_rep (hNorm : checkHNormal D = true) {tr : List (ℕ × ℕ)}
    (htr : McLLem45.treeOK D tr = true) :
    ∀ k < (orbitList D tr).size,
      ∃ n ∈ Nsub D S, TabRep (orbitList D tr)[k]! (n * wordVal S D.uW * n⁻¹) := by
  refine foldl_orbitStep_rep hgs hgi hNorm tr #[wT D D.uW] ?_ ?_
  · intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    have := wT_rep hgs hgi D.uW
    simpa using this
  · intro k hk
    exact treeOK_bounds htr k hk

end Orbit

section Check

theorem conj_pow_mod_five {X : Type*} [Group X] {u : X} (w : X) (hu : u ^ 5 = 1) (i : ℕ) :
    u ^ i * w * (u ^ i)⁻¹ = u ^ (i % 5) * w * u ^ (5 - i % 5) := by
  have hlt : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h1 : u ^ i = u ^ (i % 5) := pow_eq_pow_mod i hu
  have h2 : (u ^ (i % 5))⁻¹ = u ^ (5 - i % 5) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show i % 5 + (5 - i % 5) = 5 by omega]
    exact hu
  rw [h1, h2]

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}
variable (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem check_u_pow {w : List ℤ} {tr : List (ℕ × ℕ)} (h : check D w tr = true) :
    wordVal S D.uW ^ 5 = 1 := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ((powT_rep (wT_rep hgs hgi D.uW) 5).beq_iff TabRep.idTab).1 h1

theorem check_uv_ne {w : List ℤ} {tr : List (ℕ × ℕ)} (h : check D w tr = true) :
    wordVal S D.uW * wordVal S D.vW ≠ wordVal S D.vW * wordVal S D.uW := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro hc
  have hu := wT_rep hgs hgi D.uW
  have hv := wT_rep hgs hgi D.vW
  have hb := ((hu.comp hv).beq_iff (hv.comp hu)).2 hc
  rw [hb] at h2
  exact absurd h2 (by decide)

theorem check_w_sq {w : List ℤ} {tr : List (ℕ × ℕ)} (h : check D w tr = true) :
    wordVal S w * wordVal S w = 1 := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hw := wT_rep hgs hgi w
  exact ((hw.comp hw).beq_iff TabRep.idTab).1 h3

theorem check_conj_comm {w : List ℤ} {tr : List (ℕ × ℕ)} (h : check D w tr = true) (i j : ℕ) :
    (wordVal S D.uW ^ i * wordVal S w * (wordVal S D.uW ^ i)⁻¹) *
        (wordVal S D.uW ^ j * wordVal S w * (wordVal S D.uW ^ j)⁻¹) =
      (wordVal S D.uW ^ j * wordVal S w * (wordVal S D.uW ^ j)⁻¹) *
        (wordVal S D.uW ^ i * wordVal S w * (wordVal S D.uW ^ i)⁻¹) := by
  have hu5 := check_u_pow hgs hgi h
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩ := h
  rw [allBelow_eq_true] at h4
  have h4' := h4 (i % 5) (Nat.mod_lt _ (by norm_num))
  rw [allBelow_eq_true] at h4'
  have h4'' := h4' (j % 5) (Nat.mod_lt _ (by norm_num))
  have hu := wT_rep hgs hgi D.uW
  have hw := wT_rep hgs hgi w
  have hWi := ((powT_rep hu (i % 5)).comp hw).comp (powT_rep hu (5 - i % 5))
  have hWj := ((powT_rep hu (j % 5)).comp hw).comp (powT_rep hu (5 - j % 5))
  rw [conj_pow_mod_five _ hu5 i, conj_pow_mod_five _ hu5 j]
  exact ((hWi.comp hWj).beq_iff (hWj.comp hWi)).1 h4''

theorem check_conj_ne {w : List ℤ} {tr : List (ℕ × ℕ)} (h : check D w tr = true) :
    wordVal S D.uW * wordVal S w * (wordVal S D.uW)⁻¹ ≠ wordVal S w := by
  have hu5 := check_u_pow hgs hgi h
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, -⟩, -⟩ := h
  intro hc
  have hu := wT_rep hgs hgi D.uW
  have hw := wT_rep hgs hgi w
  have h1 := (((powT_rep hu 1).comp hw).comp (powT_rep hu (5 - 1)))
  have h0 := (((powT_rep hu 0).comp hw).comp (powT_rep hu (5 - 0)))
  have e1 : wordVal S D.uW ^ 1 * wordVal S w * wordVal S D.uW ^ (5 - 1) =
      wordVal S D.uW * wordVal S w * (wordVal S D.uW)⁻¹ := by
    have := conj_pow_mod_five (wordVal S w) hu5 1
    simpa using this.symm
  have e0 : wordVal S D.uW ^ 0 * wordVal S w * wordVal S D.uW ^ (5 - 0) = wordVal S w := by
    simp [hu5]
  have hb : (wConj D (wT D D.uW) (wT D w) 1 == wConj D (wT D D.uW) (wT D w) 0) = true :=
    (h1.beq_iff h0).2 (by rw [e1, e0]; exact hc)
  rw [hb] at h5
  exact absurd h5 (by decide)

theorem check_trans (hR : checkHR D = true) (hNorm : checkHNormal D = true) {w : List ℤ}
    {tr : List (ℕ × ℕ)} (h : check D w tr = true) {x : Equiv.Perm (Fin D.n)} (hx : x ∈ Rsub D S)
    (hnc : ∃ s ∈ Rsub D S, s * x ≠ x * s) :
    ∃ n ∈ Nsub D S, n * wordVal S D.uW * n⁻¹ = x := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hF⟩, hG⟩ := h
  have hE := enum_RH hgs hgi hR
  obtain ⟨t, ht, hrep⟩ := hE.complete x hx
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  rw [allBelow_eq_true] at hG
  have hGi := hG i hi
  rw [Bool.or_eq_true, Array.any_eq_true, Array.any_eq_true] at hGi
  rcases hGi with ⟨j, hj, hjt⟩ | ⟨j, hj, hjt⟩
  · exfalso
    rw [beq_iff_eq] at hjt
    have hmem : (hrEnum D).tabs[i]! ∈ (zTabs D).toList := by
      rw [← hjt]
      exact Array.getElem_mem_toList hj
    have hxc := (mem_enum_iff (enum_Z hgs hgi hR) hrep).1 hmem
    obtain ⟨s, hs, hsx⟩ := hnc
    exact hsx (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxc).2 s hs)
  · rw [beq_iff_eq] at hjt
    obtain ⟨n, hn, hrep'⟩ := orbitList_rep hgs hgi hNorm hF j hj
    rw [getElem!_pos (orbitList D tr) j hj, hjt] at hrep'
    exact ⟨n, hn, hrep'.perm_eq hrep⟩

end Check

section Transport

theorem model_of_subgroups {X : Type*} [Group X] {G R N : Subgroup X} {u v w : X}
    (hRG : R ≤ G) (hNR : N ≤ normalizer (R : Set X)) (hNG : N ≤ G)
    (hcard : Nat.card R = 5 ^ 3) (huR : u ∈ R) (hvR : v ∈ R) (hwG : w ∈ G)
    (hu5 : u ^ 5 = 1) (huv : u * v ≠ v * u) (hww : w * w = 1) (hne : u * w * u⁻¹ ≠ w)
    (hcomm : ∀ i j : ℕ, (u ^ i * w * (u ^ i)⁻¹) * (u ^ j * w * (u ^ j)⁻¹) =
      (u ^ j * w * (u ^ j)⁻¹) * (u ^ i * w * (u ^ i)⁻¹))
    (htrans : ∀ x ∈ R, (∃ s ∈ R, s * x ≠ x * s) → ∃ n ∈ N, n * u * n⁻¹ = x) :
    ∃ (R₀ : Subgroup ↥G) (u₀ w₀ : ↥G),
      Nat.card R₀ = 5 ^ 3 ∧ u₀ ∈ R₀ ∧ u₀ ^ 5 = 1 ∧ (∃ s ∈ R₀, s * u₀ ≠ u₀ * s) ∧
      w₀ * w₀ = 1 ∧ u₀ * w₀ * u₀⁻¹ ≠ w₀ ∧
      (∀ i j : ℕ, (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹) * (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) =
        (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) * (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹)) ∧
      (∀ x ∈ R₀, (∃ s ∈ R₀, s * x ≠ x * s) →
        ∃ n ∈ normalizer (R₀ : Set ↥G), n * u₀ * n⁻¹ = x) := by
  have huG : u ∈ G := hRG huR
  have hvG : v ∈ G := hRG hvR
  refine ⟨R.subgroupOf G, ⟨u, huG⟩, ⟨w, hwG⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hcard]
  · exact Subgroup.mem_subgroupOf.2 huR
  · exact Subtype.ext (by simpa using hu5)
  · refine ⟨⟨v, hvG⟩, Subgroup.mem_subgroupOf.2 hvR, fun hc => huv ?_⟩
    exact (congrArg Subtype.val hc).symm
  · exact Subtype.ext (by simpa using hww)
  · intro hc
    exact hne (congrArg Subtype.val hc)
  · intro i j
    exact Subtype.ext (by simpa using hcomm i j)
  · intro x hx ⟨s, hs, hsx⟩
    have hxR : (x : X) ∈ R := Subgroup.mem_subgroupOf.1 hx
    have hsR : (s : X) ∈ R := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨n, hnN, hn⟩ := htrans x hxR ⟨s, hsR, fun h => hsx (Subtype.ext h)⟩
    refine ⟨⟨n, hNG hnN⟩, ?_, Subtype.ext (by simpa using hn)⟩
    rw [← Subgroup.subgroupOf_normalizer_eq hRG]
    exact Subgroup.mem_subgroupOf.2 (hNR hnN)

end Transport

section Assembly

theorem checkHeis_parts {D : Data} (h : checkHeis D = true) :
    checkInv D = true ∧ checkHR D = true ∧ checkHNormal D = true := by
  simp only [checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, -⟩, hNorm⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hInv, hR, hNorm⟩

theorem model_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1)) (hp : D.p = 5)
    (hHeis : checkHeis D = true) {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : Subgroup.closure {g | g ∈ S} = G) {w : List ℤ} {tr : List (ℕ × ℕ)}
    (hchk : check D w tr = true) :
    ∃ (R₀ : Subgroup ↥G) (u₀ w₀ : ↥G),
      Nat.card R₀ = 5 ^ 3 ∧ u₀ ∈ R₀ ∧ u₀ ^ 5 = 1 ∧ (∃ s ∈ R₀, s * u₀ ≠ u₀ * s) ∧
      w₀ * w₀ = 1 ∧ u₀ * w₀ * u₀⁻¹ ≠ w₀ ∧
      (∀ i j : ℕ, (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹) * (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) =
        (u₀ ^ j * w₀ * (u₀ ^ j)⁻¹) * (u₀ ^ i * w₀ * (u₀ ^ i)⁻¹)) ∧
      (∀ x ∈ R₀, (∃ s ∈ R₀, s * x ≠ x * s) →
        ∃ n ∈ normalizer (R₀ : Set ↥G), n * u₀ * n⁻¹ = x) := by
  subst hn
  subst hG
  obtain ⟨hInv, hR, hNorm⟩ := checkHeis_parts hHeis
  have hgi := giT_rep hS hInv
  refine model_of_subgroups (G := Gsub S) (R := Rsub D S) (N := Nsub D S) (u := wordVal S D.uW)
    (v := wordVal S D.vW) (w := wordVal S w) Rsub_le_Gsub (N_le_normalizer_H hS hgi hR hNorm)
    Nsub_le_Gsub ?_ uW_mem vW_mem (wordVal_mem_Gsub w) (check_u_pow hS hgi hchk)
    (check_uv_ne hS hgi hchk) (check_w_sq hS hgi hchk) (check_conj_ne hS hgi hchk)
    (check_conj_comm hS hgi hchk) ?_
  · rw [card_RH hS hgi hR, hp]
  · intro x hx hnc
    exact check_trans hS hgi hR hNorm hchk hx hnc

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.AGLEmbeddingD2 CFSG.RankThree.Native

theorem mclLem45Model_of_check
    (hchk : McLLem45.check Certificates.MaxD2Heis.mclFiveDataP McLLem45.wordW
      McLLem45.tree = true) :
    McLLem45Model :=
  McLLem45.model_of_check (n := 275) (S := [mcl275A, mcl275B])
    (D := Certificates.MaxD2Heis.mclFiveDataP) rfl mclFiveDataP_hS rfl mcl_five_check_P
    mclP_closure_eq hchk

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
