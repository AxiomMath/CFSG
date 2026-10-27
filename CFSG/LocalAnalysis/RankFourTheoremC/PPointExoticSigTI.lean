module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
public import Certificates.Data.MaxD2TI

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbedding.MaxD2 CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.MaxD2TI

theorem inf_map_conj_eq_bot_of_doubleCosets {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {G N R : Subgroup Q} (hNG : N ≤ G) (hRN : R ≤ N)
    (hNR : N ≤ normalizer (R : Set Q)) (hRp : IsPGroup p R) (g : ℕ → Q) (r : ℕ) (hg0 : g 0 = 1)
    (hgG : ∀ i ≤ r, g i ∈ G)
    (hsum : ∑ i ∈ Finset.range (r + 1),
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) = Nat.card G)
    (hdisj : ∀ i ≤ r, ∀ j ≤ r, i < j → ∀ a ∈ N, (g i)⁻¹ * a * g j ∉ N)
    (hcop : ∀ i, 1 ≤ i → i ≤ r → ¬ p ∣ Nat.card (conjStab N (g i))) :
    ∀ y ∈ G, y ∉ N → R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥ := by
  intro y hy hyN
  obtain ⟨i, hi, a, ha, b, hb, rfl⟩ := exists_dcoset_of_sum hNG g r hgG hsum hdisj y hy
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hyN
    rw [hg0, mul_one]
    exact N.mul_mem ha hb
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxy⟩
  obtain ⟨r', hr'R, hr'⟩ := Subgroup.mem_map.1 hxy
  have hxeq : x = (a * g i * b) * r' * (a * g i * b)⁻¹ := by
    rw [← hr']
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  obtain ⟨w, hw⟩ : ∃ w, w = a⁻¹ * x * a := ⟨_, rfl⟩
  have hwR : w ∈ R := by
    have := (Subgroup.mem_normalizer_iff.1 (hNR (N.inv_mem ha)) x).1 hxR
    rw [hw]
    simpa using this
  obtain ⟨r'', hr''⟩ : ∃ r'', r'' = b * r' * b⁻¹ := ⟨_, rfl⟩
  have hr''R : r'' ∈ R := by
    have := (Subgroup.mem_normalizer_iff.1 (hNR hb) r').1 hr'R
    rw [hr'']
    simpa using this
  have hwg : w = g i * r'' * (g i)⁻¹ := by
    rw [hw, hxeq, hr'']
    group
  have hwstab : w ∈ conjStab N (g i) := by
    refine mem_conjStab.2 ⟨hRN hwR, ?_⟩
    have : (g i)⁻¹ * w * g i = r'' := by
      rw [hwg]; group
    rw [this]
    exact hRN hr''R
  by_cases hw1 : w = 1
  · rw [Subgroup.mem_bot]
    have : x = a * w * a⁻¹ := by rw [hw]; group
    rw [this, hw1]
    group
  · exfalso
    obtain ⟨k, hk⟩ := hRp ⟨w, hwR⟩
    have hk' : w ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : orderOf w ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hw1 (orderOf_eq_one_iff.1 (by simpa using hj))
    have hpd : p ∣ orderOf w := by
      rw [hj]
      exact dvd_pow_self p hj0
    have hd2 : orderOf w ∣ Nat.card (conjStab N (g i)) := by
      have := Subgroup.orderOf_dvd_natCard (conjStab N (g i)) hwstab
      simpa using this
    exact hcop i (Nat.pos_of_ne_zero hi0) hi (hpd.trans hd2)

section Perm

variable {D : Certificates.MaxD2Perm.Data} {S : List (Equiv.Perm (Fin D.n))}

theorem inf_map_conj_eq_bot_of_checkTI
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)
    (hcard : Nat.card (Gsub S) = D.gOrder) (hp : D.p.Prime) (hN : checkN D = true)
    (hMax : checkMax D = true) (hTI : checkTI D = true)
    {R : Subgroup (Equiv.Perm (Fin D.n))} (hRN : R ≤ Nsub D S)
    (hNR : Nsub D S ≤ normalizer (R : Set (Equiv.Perm (Fin D.n)))) (hRp : IsPGroup D.p R) :
    ∀ y ∈ Gsub S, y ∉ Nsub D S → R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥ := by
  have hN' := enum_N hgs hgi hN
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, -⟩ := hMax
  simp only [dcDisjoint, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep hgs hgi
  have hrepI := repI_rep hgs hgi hinvs
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 →
      TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  simp only [checkTI, allBelow_eq_true, bne_iff_ne, ne_eq] at hTI
  refine inf_map_conj_eq_bot_of_doubleCosets hp Nsub_le_Gsub hRN hNR hRp
    (fun i => (repElts D S).getD i 1) D.repW.length (by simp [repElts])
    (fun i hi => repElts_mem (getD_mem_of_lt (by simp [repElts]; omega) 1))
    (by rw [sum_eq hgs hgi hN hfp hinvs hsum, hcard]) ?_ ?_
  · intro i hi j hj hij a ha hmem
    obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
    rcases hdisj i (by omega) j (by omega) with h | h
    · exact h hij
    · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
      have hmemT := (mem_enum_iff hN' hy).2 hmem
      have := (memFp_iff hfp _).2 hmemT
      rw [h k hk] at this
      exact Bool.noConfusion this
  · intro i hi1 hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < D.repW.length := by omega
    have hc := hTI i' hi'
    rw [conjCount_eq hgs hgi hN hfp (by omega) hinvs] at hc
    exact fun hd => hc (Nat.mod_eq_zero_of_dvd hd)

theorem tiTorus_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Certificates.MaxD2Perm.Data}
    (hn : D.n = n) (hp : D.p.Prime) (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : Certificates.MaxD2Perm.check D = true) (hTI : checkTI D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 2 ∧
      ∀ y ∈ Subgroup.closure {g | g ∈ S}, y ∉ normalizer (R : Set (Equiv.Perm (Fin n))) →
        R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥ := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), R ≤ Gsub S ∧ Nat.card R = D.p ^ 2 ∧
    ∀ y ∈ Gsub S, y ∉ normalizer (R : Set (Equiv.Perm (Fin D.n))) →
      R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥
  simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq hS hgi hlen hcardG hR hN hNorm hMoves hMax
  have hNR := N_le_normalizer hS hgi hR hNorm
  have hRN : Rsub D S ≤ Nsub D S := by
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  have hcR := card_R hS hgi hR
  refine ⟨Rsub D S, Rsub_le_Gsub, hcR, ?_⟩
  intro y hy hyN
  exact inf_map_conj_eq_bot_of_checkTI hS hgi hcardG hp hN hMax hTI hRN hNR
    (IsPGroup.of_card hcR) y hy (fun hyN' => hyN (hNR hyN'))

theorem tiHeis_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Certificates.MaxD2Perm.Data}
    (hn : D.n = n) (hp : D.p.Prime) (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : Certificates.MaxD2Heis.checkHeis D = true) (hTI : checkTI D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 3 ∧
      ∀ y ∈ Subgroup.closure {g | g ∈ S}, y ∉ normalizer (R : Set (Equiv.Perm (Fin n))) →
        R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥ := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), R ≤ Gsub S ∧ Nat.card R = D.p ^ 3 ∧
    ∀ y ∈ Gsub S, y ∉ normalizer (R : Set (Equiv.Perm (Fin D.n))) →
      R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥
  simp only [Certificates.MaxD2Heis.checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hZ⟩, hExp⟩, hComm⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq_H hS hgi hlen hcardG hR hN hNorm hMoves hMax
  have hNR := N_le_normalizer_H hS hgi hR hNorm
  have hRN : Rsub D S ≤ Nsub D S := by
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  have hcR := card_RH hS hgi hR
  refine ⟨Rsub D S, Rsub_le_Gsub, hcR, ?_⟩
  intro y hy hyN
  exact inf_map_conj_eq_bot_of_checkTI hS hgi hcardG hp hN hMax hTI hRN hNR
    (IsPGroup.of_card hcR) y hy (fun hyN' => hyN (hNR hyN'))

end Perm

theorem exists_sylow_weakTI_of_equiv {X Q : Type*} [Group X] [Finite X] [Group Q]
    {G R : Subgroup Q} {p : ℕ} (hp : p.Prime) (e : X ≃* G) (hRG : R ≤ G)
    (hcard : Nat.card R = p ^ (Nat.card X).factorization p)
    (hTI : ∀ y ∈ G, y ∉ normalizer (R : Set Q) →
      R ⊓ R.map (MulAut.conj y).toMonoidHom = ⊥) :
    ∃ R₀ : Sylow p X, WeakTI (R₀ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardR' : Nat.card ((R.subgroupOf G).map e.symm.toMonoidHom) =
      p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv
  refine ⟨Sylow.ofCard _ hcardR', ?_⟩
  rw [Sylow.coe_ofCard]
  refine WeakTI.map (R := R.subgroupOf G) ?_ e.symm
  intro g x hx hx1 hxg
  have hxR : (x : Q) ∈ R := hx
  by_contra hg
  have hgN : (g : Q) ∉ normalizer (R : Set Q) := by
    intro hN
    apply hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 hN (h : Q)
    exact this
  have h1 := hTI g g.2 hgN
  have hxg' : ((g⁻¹ * x * g : G) : Q) ∈ R := hxg
  have hmem : (x : Q) ∈ R ⊓ R.map (MulAut.conj (g : Q)).toMonoidHom := by
    refine ⟨hxR, ⟨_, hxg', ?_⟩⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  rw [h1, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext hmem)

end CFSG.LocalAnalysis.RankFourTheoremC
