module

public import CFSG.Certificates.Kernel.SporSch.OddWitSound
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporSpec
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.KS.SporSch.OddWit

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3 CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {n w : Nat}

theorem conj_mem_of_gens {K : Subgroup (Equiv.Perm (Fin n))} {gA gB g : Equiv.Perm (Fin n)}
    (hK : K = Subgroup.closure {gA, gB}) (ha : g * gA * g⁻¹ ∈ K) (hb : g * gB * g⁻¹ ∈ K) :
    ∀ h ∈ K, g * h * g⁻¹ ∈ K := by
  intro h hh
  rw [hK] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact K.mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact K.inv_mem hx

theorem rowOK_of_cands (hsz : szOK n w = true) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (gG : List (Equiv.Perm (Fin n))) {u : Equiv.Perm (Fin n)} (hu : u * u = 1) (r : Row)
    {OG : List Nat} (hOG : List.Forall₂ (PRep n w) OG (r.oddWords.map (evalCodes gG)))
    (hp : 0 < r.prime) (hodd : r.oddExp % 2 = 1)
    (hcube : Q.orderCertificate % r.prime ^ (r.pexp + 1) ≠ 0)
    (hog : ∀ g ∈ r.oddWords.map (evalCodes gG), u * g = g * u ∧ g ^ r.oddExp = 1)
    (hcand : ∀ x ∈ Q.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = r.prime →
      ∃ X, PRep n w X x ∧ witPK n w OG (r.prime ^ r.pexp) X = true) :
    rowOK n Q gG u (candAll n Q (toTable u)) r = true := by
  have hf := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hrep := rep_toTable hn
  unfold rowOK
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, hodd⟩, hcube⟩, fun g hg => ?_⟩, fun T hT => ?_⟩
  · rw [tblEq_eq_iff (Rep.compT (hrep u) (hrep u)) (Rep.idT hn)]
    exact hu
  · obtain ⟨h1, h2⟩ := hog g hg
    rw [commT_eq (hrep u) (hrep g), decide_eq_true_eq,
      powFixW_iff perm_faithful (List.Forall₂.cons (hrep g) List.Forall₂.nil)]
    exact ⟨h1, by simpa using h2⟩
  · obtain ⟨x, hx, hTx⟩ := exists_of_mem_left_forall₂ (forall₂_candAllT hn Q rfl (hrep u)) hT
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ hQ] at hx
    obtain ⟨hxG, hsq⟩ := hx
    rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ordTest_iff perm_faithful hTx hp]
    by_cases hxo : orderOf x = r.prime
    · right
      obtain ⟨X, pX, hX⟩ := hcand x hxG hsq hxo
      exact witnessOK_of_witPK hsz hOG pX hTx hX
    · exact Or.inl hxo

theorem cands_of_classes {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat} (hsz : szOK n w = true)
    (pA : PRep n w (packL w tA) gA) (pB : PRep n w (packL w tB) gB)
    {mx cap : Nat} {CL : List ClsD} (hcls : ClsOK n w tA tB mx cap CL)
    {reps : List (Equiv.Perm (Fin n))}
    (hR : reps.length = CL.length ∧ ∀ j < CL.length, PRep n w (CL.getD j clsD0).R (reps.getD j 1))
    (hne : 0 < CL.length) {K : Subgroup (Equiv.Perm (Fin n))}
    (hK : K = Subgroup.closure {gA, gB}) {g₀ u : Equiv.Perm (Fin n)} (hu : g₀⁻¹ * u ∈ K)
    (hcov : ∀ s, g₀⁻¹ * s ∈ K → orderOf s = 2 → ∃ r ∈ reps, ∃ c ∈ K, s = c * r * c⁻¹)
    {rows : List (Nat × Nat × List Nat)} {Ui : Nat} (pU : PRep n w Ui u⁻¹)
    (hinv : ∀ j < CL.length, invCandK n w rows Ui (CL.getD j clsD0) = true) :
    ∀ x ∈ K, (u * x) * (u * x) = 1 → ∃ X, PRep n w X x ∧ rowsPK n w rows X = true := by
  intro x hx hsq
  have hf := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw : n < 2 ^ w := by omega
  have pAi := (prep_pinvS hw pA).1
  have pBi := (prep_pinvS hw pB).1
  by_cases h1 : u * x = 1
  · obtain ⟨hd, he, -⟩ := hcls 0 hne
    exact rowsPK_of_invCandK hn pA pAi pB pBi hd he (hR.2 0 hne) pU (hinv 0 hne) (Or.inl h1)
  · have ho : orderOf (u * x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
    have hg : g₀⁻¹ * (u * x) ∈ K := by
      rw [← mul_assoc]
      exact K.mul_mem hu hx
    obtain ⟨r, hr, c, hc, e⟩ := hcov _ hg ho
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hjC : j < CL.length := hR.1 ▸ hj
    obtain ⟨hd, he, -⟩ := hcls j hjC
    have pR := hR.2 j hjC
    rw [List.getD_eq_getElem _ _ hj] at pR
    refine rowsPK_of_invCandK hn pA pAi pB pBi hd he pR pU (hinv j hjC) (Or.inr ?_)
    rw [← hK]
    exact ⟨c, hc, e⟩

theorem commAll_pow (hn : n < 2 ^ 32) {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {a b : Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : Q.originalSubgroup ⊓ Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n))) ≤ H)
    {e : Nat} (hel : ∀ g ∈ H, g * b = b * g → g ^ e = 1) :
    ∀ T ∈ Certificates.CF67.commAllT n (levelTables Q) (toTable a) (toTable b),
      powFixW n [T] e = true := by
  intro T hT
  obtain ⟨g, hg, hTg⟩ := exists_of_mem_left_forall₂
    (forall₂_commAllT hn Q rfl (rep_toTable hn a) (rep_toTable hn b)) hT
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff _ hQ] at hg
  obtain ⟨hgG, hga, hgb⟩ := hg
  rw [powFixW_iff perm_faithful (List.Forall₂.cons hTg List.Forall₂.nil)]
  simpa using hel g (hH ⟨hgG, Subgroup.mem_centralizer_singleton_iff.2 hga.symm⟩) hgb.symm

theorem canon_ne {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hw : 0 < w) (hP : PRep n w P g)
    (hQ : PRep n w Q h) (sP : P >>> (n * w) = 0) (sQ : Q >>> (n * w) = 0)
    (hne : (Nat.beq P Q).not = true) : g ≠ h := by
  rw [beq_eq_decide hw hP hQ sP sQ] at hne
  simpa using hne

theorem pow_eq_one_of {P : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true)
    (hP : PRep n w P g) {e : Nat}
    (h : Nat.beq (powK n w (mask w) (pidn n w) P e) (pidn n w) = true) : g ^ e = 1 := by
  have hf := szOK_facts hsz
  obtain ⟨p1, s1⟩ := prep_powK hsz hP e
  rw [beq_eq_decide (PF.w_pos hf.2) p1 (prep_pidn hf.1 hf.2) s1 (PF.pidn_shr hf.1 hf.2)] at h
  exact of_decide_eq_true h

theorem mul_eq_of {P Q R S : Nat} {a b c d : Equiv.Perm (Fin n)} (hsz : szOK n w = true)
    (hP : PRep n w P a) (hQ : PRep n w Q b) (hR : PRep n w R c) (hS : PRep n w S d)
    (h : Nat.beq (pcomp n w (mask w) P Q) (pcomp n w (mask w) R S) = true) : a * b = c * d := by
  have hf := szOK_facts hsz
  rw [beq_pcomp_iff (by omega) (PF.w_pos hf.2) hP hQ hR hS] at h
  exact of_decide_eq_true h

theorem cf67OKT_of (hsz : szOK n w = true) {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {a b : Equiv.Perm (Fin n)} {A B : Nat} (pA : PRep n w A a) (pB : PRep n w B b)
    (sA : A >>> (n * w) = 0) (sB : B >>> (n * w) = 0) {r : Nat}
    (f1 : Nat.beq (powK n w (mask w) (pidn n w) A r) (pidn n w) = true)
    (f2 : Nat.beq (powK n w (mask w) (pidn n w) B r) (pidn n w) = true)
    (f3 : Nat.beq (pcomp n w (mask w) A B) (pcomp n w (mask w) B A) = true)
    (f4 : (Nat.beq A (pidn n w)).not = true)
    (f5 : allN r (fun i => (Nat.beq B (powK n w (mask w) (pidn n w) A i)).not) = true)
    (hNG : Q.orderCertificate % r ^ 3 ≠ 0)
    (hcomm : ∀ T ∈ Certificates.CF67.commAllT n (levelTables Q) (toTable a) (toTable b),
      powFixW n [T] (r ^ 2) = true) :
    Certificates.CF67.cf67OKT n Q.orderCertificate (levelTables Q) (toTable a) (toTable b) r =
      true := by
  have hf := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw : 0 < w := PF.w_pos hf.2
  have hrep := rep_toTable hn
  have sId : pidn n w >>> (n * w) = 0 := PF.pidn_shr hf.1 hf.2
  have pId : PRep n w (pidn n w) 1 := prep_pidn hf.1 hf.2
  unfold Certificates.CF67.cf67OKT
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun i hi => ?_⟩, hNG⟩, hcomm⟩
  · rw [powFixW_iff perm_faithful (List.Forall₂.cons (hrep a) List.Forall₂.nil)]
    simpa using pow_eq_one_of hsz pA f1
  · rw [powFixW_iff perm_faithful (List.Forall₂.cons (hrep b) List.Forall₂.nil)]
    simpa using pow_eq_one_of hsz pB f2
  · rw [commT_eq (hrep a) (hrep b), decide_eq_true_eq]
    exact mul_eq_of hsz pA pB pB pA f3
  · cases h : tblEq n (toTable a) (idT n)
    · rfl
    · exact absurd ((tblEq_eq_iff (hrep a) (Rep.idT hn)).1 h) (canon_ne hw pA pId sA sId f4)
  · cases h : tblEq n (toTable b) (Certificates.CF67.cf67PowT n (toTable a) i)
    · rfl
    · obtain ⟨p1, s1⟩ := prep_powK hsz pA i
      exact absurd ((tblEq_eq_iff (hrep b) (rep_powT hn (hrep a) i)).1 h)
        (canon_ne hw pB p1 sB s1 (allN_spec f5 i hi))

end CFSG.KS.SporSch.OddWit

end
