module

import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import Certificates.Data.MaxD2Heis

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.MaxD2Heis
open Certificates.FusD2Perm (powT wordT)
open scoped commutatorElement

section Generic

theorem isSolvable_of_normal_pow {X : Type*} [Group X] [Finite X] {p k a b : ℕ} (hp : p.Prime)
    {N R : Subgroup X} (hRN : R ≤ N) (hnorm : N ≤ Subgroup.normalizer (R : Set X))
    (hR : Nat.card R = p ^ k) (hN : Nat.card N = p ^ k * (2 ^ a * 3 ^ b)) :
    Group.IsSolvable N := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).2 hnorm
  have hR' : Nat.card (R.subgroupOf N) = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv, hR]
  have hRp : IsPGroup p (R.subgroupOf N) := IsPGroup.of_card hR'
  have : Group.IsNilpotent (R.subgroupOf N) := hRp.isNilpotent
  have hsolvR : Group.IsSolvable (R.subgroupOf N) := inferInstance
  have hq : Nat.card (N ⧸ R.subgroupOf N) = 2 ^ a * 3 ^ b := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf N)
    rw [hN, hR'] at h
    have hpos : 0 < p ^ k := pow_pos hp.pos k
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [h, mul_comm])).symm
  have hsolvQ : Group.IsSolvable (N ⧸ R.subgroupOf N) := by
    have := Fintype.ofFinite (N ⧸ R.subgroupOf N)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hq])
  exact Group.isSolvable_of_ker_le_range (R.subgroupOf N).subtype
    (QuotientGroup.mk' (R.subgroupOf N)) (by simp [QuotientGroup.ker_mk'])

theorem exists_pow_mul_of_mem {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Z F : Subgroup X} (hZ : Nat.card Z = p) (hZF : Z ≤ F) (hF : Nat.card F = p ^ 2)
    {x : X} (hxF : x ∈ F) (hxZ : x ∉ Z) (hx : x ^ p = 1) {y : X} (hyF : y ∈ F) :
    ∃ j < p, ∃ z ∈ Z, y = x ^ j * z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := by
    refine orderOf_eq_prime hx ?_
    rintro rfl
    exact hxZ Z.one_mem
  have hZY : Z ⊓ Subgroup.zpowers x = ⊥ := by
    have hW : Nat.card (Z ⊓ Subgroup.zpowers x : Subgroup X) ∣ p :=
      hZ ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hW with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Z ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (inf_le_right) (by rw [h1, Nat.card_zpowers, hord])
      have hxW : x ∈ Z ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxZ hxW.1
  let f : Fin p × Z → F := fun jz =>
    ⟨x ^ (jz.1 : ℕ) * (jz.2 : X), F.mul_mem (F.pow_mem hxF _) (hZF jz.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨j, z⟩ ⟨j', z'⟩ h
    have h1 : x ^ (j : ℕ) * (z : X) = x ^ (j' : ℕ) * (z' : X) := congrArg Subtype.val h
    have h2 : x ^ ((j : ℤ) - (j' : ℤ)) * (z : X) = (z' : X) := by
      calc x ^ ((j : ℤ) - (j' : ℤ)) * (z : X)
          = (x ^ (j' : ℕ))⁻¹ * (x ^ (j : ℕ) * (z : X)) := by
            rw [zpow_sub, zpow_natCast, zpow_natCast]
            group
        _ = (z' : X) := by rw [h1]; group
    have h3 : x ^ ((j : ℤ) - (j' : ℤ)) = (z' : X) * (z : X)⁻¹ := eq_mul_inv_of_mul_eq h2
    have h4 : x ^ ((j : ℤ) - (j' : ℤ)) ∈ Z ⊓ Subgroup.zpowers x :=
      ⟨h3 ▸ Z.mul_mem z'.2 (Z.inv_mem z.2), Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _⟩
    rw [hZY, Subgroup.mem_bot] at h4
    have hj := j.2
    have hj' := j'.2
    have h5 : ((j : ℤ) - (j' : ℤ)) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ)) ?_ ?_
      · have h8 := orderOf_dvd_iff_zpow_eq_one.2 h4
        rwa [hord] at h8
      · rw [abs_lt]
        constructor <;> omega
    have h6 : j = j' := Fin.ext (by omega)
    subst h6
    have h7 : (z : X) = z' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext h7)
  have hbij : Function.Bijective f :=
    Function.Injective.bijective_of_nat_card_le hinj
      (by rw [Nat.card_prod, Nat.card_fin, hZ, hF, sq])
  obtain ⟨⟨j, z⟩, hjz⟩ := hbij.2 ⟨y, hyF⟩
  exact ⟨j, j.2, z, z.2, (congrArg Subtype.val hjz).symm⟩

end Generic

@[expose] def HeisData (p m lam e : ℕ) {Q : Type*} [Group Q] (G R : Subgroup Q) : Prop :=
  R ≤ G ∧ Nat.card R = p ^ 3 ∧
  (∀ Y : Subgroup Q, Subgroup.normalizer (R : Set Q) ⊓ G ≤ Y → Y ≤ G →
    Y = Subgroup.normalizer (R : Set Q) ⊓ G ∨ Y = G) ∧
  (∀ g ∈ G, (∀ r ∈ R, g * r = r * g) → g ∈ R) ∧
  Nat.card (R ⊓ Subgroup.centralizer (R : Set Q) : Subgroup Q) = p ∧
  ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set Q) ∧
  (∀ r ∈ R, r ^ p = 1) ∧
  Group.IsSolvable ↥(Subgroup.normalizer (R : Set Q) ⊓ G) ∧
  ∃ t ∈ Subgroup.normalizer (R : Set Q) ⊓ G,
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set Q), t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set Q), t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ F : Subgroup Q, R ⊓ Subgroup.centralizer (R : Set Q) ≤ F →
      F ≤ R → F.relIndex R = p → t ^ k ∉ Subgroup.normalizer (F : Set Q)

section Perm

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}

theorem Rsub_eq_closure :
    Rsub D S = Subgroup.closure {wordVal S D.uW, wordVal S D.vW} := by
  unfold Rsub
  congr 1
  ext g
  simp [rWs]

theorem uW_mem : wordVal S D.uW ∈ Rsub D S := Subgroup.subset_closure (by simp [rWs])

theorem vW_mem : wordVal S D.vW ∈ Rsub D S := Subgroup.subset_closure (by simp [rWs])

theorem mem_centralizer_Rsub {g : Equiv.Perm (Fin D.n)} :
    g ∈ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ↔
      (wordVal S D.uW * g = g * wordVal S D.uW ∧ wordVal S D.vW * g = g * wordVal S D.vW) := by
  constructor
  · intro h
    exact ⟨Subgroup.mem_centralizer_iff.1 h _ uW_mem, Subgroup.mem_centralizer_iff.1 h _ vW_mem⟩
  · rintro ⟨hu, hv⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hle : Rsub D S ≤ Subgroup.centralizer {g} := by
      rw [Rsub_eq_closure, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hu
      · exact Subgroup.mem_centralizer_singleton_iff.2 hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hr)

theorem commutesUV_iff {u v x : Tab} {U V X : Equiv.Perm (Fin D.n)} (hu : TabRep u U)
    (hv : TabRep v V) (hx : TabRep x X) :
    commutesUV D.n u v x = true ↔ X * U = U * X ∧ X * V = V * X := by
  simp only [commutesUV, Bool.and_eq_true]
  rw [(hx.comp hu).beq_iff (hu.comp hx), (hx.comp hv).beq_iff (hv.comp hx)]

theorem invsOK_of_checkHNormal (h : checkHNormal D = true) :
    invsOK D.n (nGens D) (nGensI D) = true := by
  simp only [checkHNormal, normalOK, Bool.and_eq_true] at h
  exact h.1

variable (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem rep_u : TabRep (rGens D)[0]! (wordVal S D.uW) :=
  rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) (j := 0) (by simp [rWs])

theorem rep_v : TabRep (rGens D)[1]! (wordVal S D.vW) :=
  rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) (j := 1) (by simp [rWs])

theorem enum_RH (h : checkHR D = true) : Enumerates (Rsub D S) (hrEnum D).tabs.toList := by
  simp only [checkHR, Bool.and_eq_true] at h
  exact enumerates_of_words S D.gT (giT D) hgs hgi (rWs D) h.1

theorem card_RH (h : checkHR D = true) : Nat.card (Rsub D S) = D.p ^ 3 := by
  have h' := h
  simp only [checkHR, Bool.and_eq_true, beq_iff_eq] at h'
  rw [(enum_RH hgs hgi h).card, Array.length_toList, h'.2]

theorem N_le_normalizer_H (hR : checkHR D = true) (hNorm : checkHNormal D = true) :
    Nsub D S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  unfold Nsub
  rw [Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < D.nW.length := by simpa using hj
  refine mem_normalizer_of_conj_gens (A := {g | g ∈ (rWs D).map (wordVal S)}) ?_
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have hi' : i < (rWs D).length := by simpa using hi
  have hja : j < (nGens D).size := by simp [nGens, hj']
  have hia : i < (rGens D).size := by simp [rGens, hi']
  exact (conj_mem_of_normalOK (enum_RH hgs hgi hR) hNorm hja hia
    (rep_getElem!_of_words S D.gT (giT D) hgs hgi D.nW hj')
    (rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) hi')).1

theorem not_le_normalizer_H (hlen : S.length = D.gT.size) (hR : checkHR D = true)
    (hMoves : checkHMoves D = true) :
    ¬ Gsub S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  intro hle
  have hRok : enumOK D.n (rGens D) (hrEnum D) = true := by
    simp only [checkHR, Bool.and_eq_true] at hR
    exact hR.1
  have hR' := enum_RH hgs hgi hR
  simp only [checkHMoves, anyBelow_eq_true, Bool.not_eq_true'] at hMoves
  obtain ⟨j, hj, hnot⟩ := hMoves
  have hjS : j < S.length := by omega
  have hsG : S[j] ∈ Gsub S := Gsub_mem_of_mem (List.getElem_mem hjS)
  have hsN := hle hsG
  have hs := hgs j
  rw [show D.gT.getD j (idTab D.n) = D.gT[j]! by simp [hj]] at hs
  rw [show S.getD j 1 = S[j] by simp [hjS]] at hs
  have hsi := hgi j
  rw [show (giT D).getD j (idTab D.n) = (giT D)[j]! by simp [giT, hj]] at hsi
  rw [show S.getD j 1 = S[j] by simp [hjS]] at hsi
  have hall : (allBelow (rGens D).size fun i =>
      found (indexOf (hrEnum D).tabs) (hrEnum D).tabs
        (conjTab D.n D.gT[j]! (giT D)[j]! (rGens D)[i]!)) = true := by
    rw [allBelow_eq_true]
    intro i hi
    have hi' : i < (rWs D).length := by simpa [rGens] using hi
    have hr : TabRep (rGens D)[i]! (((rWs D).map (wordVal S))[i]'(by simpa using hi')) :=
      rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) hi'
    rw [found_iff_mem hRok hR' (hs.conjTab hr hsi)]
    have hmem : ((rWs D).map (wordVal S))[i]'(by simpa using hi') ∈ Rsub D S :=
      Subgroup.subset_closure (List.getElem_mem _)
    exact ((Subgroup.mem_normalizer_iff.1 hsN _).1 hmem)
  rw [hall] at hnot
  exact Bool.noConfusion hnot

theorem normalizer_inf_eq_H (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hR : checkHR D = true) (hN : checkN D = true) (hNorm : checkHNormal D = true)
    (hMoves : checkHMoves D = true) (hMax : checkMax D = true) :
    Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S = Nsub D S := by
  have hle : Nsub D S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S :=
    le_inf (N_le_normalizer_H hgs hgi hR hNorm) Nsub_le_Gsub
  rcases maximal_N hgs hgi hlen hcard hN (invsOK_of_checkHNormal hNorm) hMax _ hle
    inf_le_right with h | h
  · exact h
  · exact absurd (inf_eq_right.1 h) (not_le_normalizer_H hgs hgi hlen hR hMoves)

theorem centralizer_le_H (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hR : checkHR D = true) (hN : checkN D = true) (hNorm : checkHNormal D = true)
    (hMoves : checkHMoves D = true) (hMax : checkMax D = true) (hCent : checkHCent D = true) :
    ∀ g ∈ Gsub S, (∀ r ∈ Rsub D S, g * r = r * g) → g ∈ Rsub D S := by
  intro g hgG hgc
  have hR' := enum_RH hgs hgi hR
  have hN' := enum_N hgs hgi hN
  have hRok : enumOK D.n (rGens D) (hrEnum D) = true := by
    simp only [checkHR, Bool.and_eq_true] at hR
    exact hR.1
  have hNeq := normalizer_inf_eq_H hgs hgi hlen hcard hR hN hNorm hMoves hMax
  have hgN : g ∈ Nsub D S := by
    rw [← hNeq]
    refine ⟨Subgroup.mem_normalizer_fintype (S := (Rsub D S : Set (Equiv.Perm (Fin D.n))))
      (fun r hr => ?_), hgG⟩
    rw [hgc r hr, mul_inv_cancel_right]
    exact hr
  obtain ⟨k, hk, hgk⟩ := hN'.exists_pos hgN
  simp only [checkHCent, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hCent
  rcases hCent k hk with h | h
  · exfalso
    have hc := (commutesUV_iff (rep_u hgs hgi) (rep_v hgs hgi) hgk).2
      ⟨(hgc _ uW_mem), (hgc _ vW_mem)⟩
    rw [hc] at h
    exact absurd h (by decide)
  · exact (found_iff_mem hRok hR' hgk).1 h

theorem enum_Z (hR : checkHR D = true) :
    Enumerates (Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))))
      (zTabs D).toList := by
  have hR' := enum_RH hgs hgi hR
  rw [inf_comm]
  show Enumerates _ ((hrEnum D).tabs.filter
    (commutesUV D.n (rGens D)[0]! (rGens D)[1]!)).toList
  rw [Array.toList_filter]
  exact hR'.filter (K := Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))))
    (commutesUV D.n (rGens D)[0]! (rGens D)[1]!) (fun t g ht => by
      rw [commutesUV_iff (rep_u hgs hgi) (rep_v hgs hgi) ht, mem_centralizer_Rsub]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2.symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2.symm⟩)

theorem card_Z (hR : checkHR D = true) (hZ : checkHZ D = true) :
    Nat.card (Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) :
      Subgroup (Equiv.Perm (Fin D.n))) = D.p := by
  have h' := hZ
  simp only [checkHZ, beq_iff_eq] at h'
  rw [(enum_Z hgs hgi hR).card, Array.length_toList, h']

theorem exp_R (hR : checkHR D = true) (hexp : checkHExp D = true) :
    ∀ r ∈ Rsub D S, r ^ D.p = 1 := by
  intro r hr
  obtain ⟨k, hk, hkr⟩ := (enum_RH hgs hgi hR).exists_pos hr
  simp only [checkHExp, allBelow_eq_true, beq_iff_eq] at hexp
  exact ((powT_rep hkr D.p).eq_iff TabRep.idTab).1 (hexp k hk)

theorem commutator_eq (hp : D.p.Prime) (hR : checkHR D = true) (hZ : checkHZ D = true)
    (hComm : checkHComm D = true) :
    ⁅Rsub D S, Rsub D S⁆ =
      Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  have hR' := enum_RH hgs hgi hR
  have hZ' := enum_Z hgs hgi hR
  have hZc := card_Z hgs hgi hR hZ
  have hu := rep_u hgs hgi
  have hv := rep_v hgs hgi
  simp only [checkHComm, Bool.and_eq_true, bne_iff_ne, ne_eq, allBelow_eq_true, anyBelow_eq_true,
    beq_iff_eq] at hComm
  obtain ⟨hne, hall⟩ := hComm
  have hle : ∀ x ∈ Rsub D S, ∀ y ∈ Rsub D S, ⁅x, y⁆ ∈
      Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
    intro x hx y hy
    obtain ⟨k, hk, hkx⟩ := hR'.exists_pos hx
    obtain ⟨l, hl, hly⟩ := hR'.exists_pos hy
    obtain ⟨j, hj, hjeq⟩ := hall k hk l hl
    obtain ⟨z, hz, hzrep⟩ := hZ'.exists_elt hj
    have hxy : x * y = z * (y * x) := ((hkx.comp hly).eq_iff (hzrep.comp (hly.comp hkx))).1 hjeq
    have : ⁅x, y⁆ = z := by
      rw [commutatorElement_def]
      calc x * y * x⁻¹ * y⁻¹ = z * (y * x) * x⁻¹ * y⁻¹ := by rw [hxy]
        _ = z := by group
    rw [this]
    exact hz
  refine le_antisymm (Subgroup.commutator_le.2 hle) ?_
  have hc := hle _ uW_mem _ vW_mem
  have hc1 : ⁅wordVal S D.uW, wordVal S D.vW⁆ ≠ 1 := by
    intro h
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact hne (((hu.comp hv).eq_iff (hv.comp hu)).2 h)
  have hzp := (zpowers_eq_of_card_prime hp hZc hc hc1).1
  rw [← hzp]
  exact Subgroup.zpowers_le.2 (Subgroup.commutator_mem_commutator uW_mem vW_mem)

theorem torus_data_H (hp : D.p.Prime) (hR : checkHR D = true) (hN : checkN D = true)
    (hZ : checkHZ D = true) (hexp : checkHExp D = true) (hT : checkHTorus D = true) :
    ∃ t ∈ Nsub D S,
      (∀ x ∈ Rsub D S,
        ∃ z ∈ Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))),
          t ^ D.tm * x * (t ^ D.tm)⁻¹ = x ^ D.tlam * z) ∧
      (∀ x ∈ Rsub D S,
        ∃ z ∈ Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))),
          t ^ D.te * x * (t ^ D.te)⁻¹ = x⁻¹ * z) ∧
      ∀ k : ℕ, 0 < k → k < D.tm → ∀ F : Subgroup (Equiv.Perm (Fin D.n)),
        Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ≤ F →
          F ≤ Rsub D S → F.relIndex (Rsub D S) = D.p → t ^ k ∉ Subgroup.normalizer (F : Set _) := by
  have htrep := wT_rep hgs hgi D.tW
  have hR' := enum_RH hgs hgi hR
  have hZ' := enum_Z hgs hgi hR
  have hZc := card_Z hgs hgi hR hZ
  have hN' := enum_N hgs hgi hN
  have hNok : enumOK D.n (nGens D) (nEnum D) = true := by
    simp only [checkN, Bool.and_eq_true] at hN
    exact hN.1
  simp only [checkHTorus, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, anyBelow_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hT
  obtain ⟨⟨⟨⟨⟨hsz, hinv⟩, hfound⟩, hm⟩, he⟩, hk⟩ := hT
  have hti := htrep.inv hsz hinv
  refine ⟨wordVal S D.tW, (found_iff_mem hNok hN' htrep).1 hfound, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := hR'.exists_pos hx
    obtain ⟨j, hj, hjeq⟩ := hm k hk
    obtain ⟨z, hz, hzrep⟩ := hZ'.exists_elt hj
    have hA := ((powT_rep htrep D.tm).comp hkx).comp (powT_rep hti D.tm)
    have hB := (powT_rep hkx D.tlam).comp hzrep
    refine ⟨z, hz, ?_⟩
    have := (hA.eq_iff hB).1 hjeq
    rwa [inv_pow] at this
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := hR'.exists_pos hx
    obtain ⟨j, hj, hjeq⟩ := he k hk
    obtain ⟨z, hz, hzrep⟩ := hZ'.exists_elt hj
    have hA := (((powT_rep htrep D.te).comp hkx).comp (powT_rep hti D.te)).comp hkx
    refine ⟨z, hz, ?_⟩
    have h1 := (hA.eq_iff hzrep).1 hjeq
    rw [inv_pow] at h1
    have h2 : wordVal S D.tW ^ D.te * x * (wordVal S D.tW ^ D.te)⁻¹ = z * x⁻¹ :=
      eq_mul_inv_of_mul_eq h1
    rw [h2]
    have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.1 hz.2 x hx
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * z := by rw [hxz]; group
  · intro k hk0 hkm F hZF hFR hidx hnorm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hcardR := card_RH hgs hgi hR
    have hF : Nat.card F = D.p ^ 2 := by
      have h := Subgroup.relIndex_mul_card (H := F) (K := Rsub D S)
      rw [hidx, inf_eq_left.2 hFR, hcardR] at h
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring)
    obtain ⟨x, hxF, hxZ⟩ : ∃ x ∈ F, x ∉ Rsub D S ⊓
        Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
      refine IsConcreteLE.not_le_iff_exists.1 fun hle => ?_
      have := Subgroup.card_le_of_le hle
      rw [hF, hZc] at this
      have h2 := hp.two_le
      nlinarith
    have hxR := hFR hxF
    obtain ⟨i, hi, hix⟩ := hR'.exists_pos hxR
    have hyF : wordVal S D.tW ^ (k' + 1) * x * (wordVal S D.tW ^ (k' + 1))⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.1 hnorm x).1 hxF
    obtain ⟨j, hj, z, hz, hyjz⟩ := exists_pow_mul_of_mem hp hZc hZF hF hxF hxZ
      (exp_R hgs hgi hR hexp x hxR) hyF
    obtain ⟨l, hl, hzl⟩ := hZ'.exists_pos hz
    rcases hk k' (by omega) i hi with hcont | hall
    · apply hxZ
      have hmem : (hrEnum D).tabs[i]! ∈ (zTabs D).toList := by
        simpa using hcont
      exact (mem_enum_iff hZ' hix).1 hmem
    · refine hall j hj l hl ?_
      have hy := ((powT_rep htrep (k' + 1)).comp hix).comp (powT_rep hti (k' + 1))
      have hy2 := (powT_rep hix j).comp hzl
      refine (hy.eq_iff hy2).2 ?_
      rw [inv_pow]
      exact hyjz

end Perm

theorem heisData_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hp : D.p.Prime) (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (hsolv : ∃ a b : ℕ, D.nOrder = D.p ^ 3 * (2 ^ a * 3 ^ b)) (h : checkHeis D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)),
      HeisData D.p D.tm D.tlam D.te (Subgroup.closure {g | g ∈ S}) R := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), HeisData D.p D.tm D.tlam D.te (Gsub S) R
  simp only [checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hZ⟩, hExp⟩, hComm⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq_H hS hgi hlen hcardG hR hN hNorm hMoves hMax
  refine ⟨Rsub D S, Rsub_le_Gsub, card_RH hS hgi hR, ?_, centralizer_le_H hS hgi hlen hcardG hR hN
    hNorm hMoves hMax hCent, card_Z hS hgi hR hZ, commutator_eq hS hgi hp hR hZ hComm,
    exp_R hS hgi hR hExp, ?_, ?_⟩
  · intro Y hY hYG
    rw [hNeq] at hY ⊢
    exact maximal_N hS hgi hlen hcardG hN (invsOK_of_checkHNormal hNorm) hMax Y hY hYG
  · rw [hNeq]
    obtain ⟨a, b, hab⟩ := hsolv
    refine isSolvable_of_normal_pow (k := 3) (a := a) (b := b) hp ?_
      (N_le_normalizer_H hS hgi hR hNorm) (card_RH hS hgi hR) (by rw [card_N hS hgi hN, hab])
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  · obtain ⟨t, htN, h1, h2, h3⟩ := torus_data_H hS hgi hp hR hN hZ hExp hTorus
    exact ⟨t, by rw [hNeq]; exact htN, h1, h2, h3⟩

end CFSG.AGLEmbedding.MaxD2
