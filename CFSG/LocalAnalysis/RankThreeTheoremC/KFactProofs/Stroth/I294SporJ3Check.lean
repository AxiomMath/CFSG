module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalDetWitness
public import Certificates.Data.J3Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.SectionRank.LocalWitness
open scoped Matrix

theorem sylowCentral_of_check {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    [Inhabited M] [Inhabited V] (hWF : ∀ X : M, Sp.WF X) (D : SylowCentralData)
    (hc : O.sylowCentralCheck D = true) :
    ∃ P Z : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      Nat.card P = D.nP ∧ Z ≤ P ∧ (∀ z ∈ Z, ∀ g ∈ P, Commute z g) ∧ Nat.card Z = 3 ^ 2 := by
  classical
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.sylowCentralCheck at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨-, hprog⟩, hregs⟩, hf⟩ := hc
  unfold SylowCentralData.regsLt at hregs
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hregs
  obtain ⟨rk1, rk2, rx, ry⟩ := hregs
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  set En := O.enumBFS #[R[D.rk1]!, R[D.rk2]!] D.nP
  unfold Ops.sylowCentralFacts at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨hgen, henum⟩, hq⟩, hcent⟩ := hf
  unfold Ops.sylowGenFacts at hgen
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgen
  obtain ⟨⟨⟨ho1, ho2⟩, hK1⟩, hK2⟩ := hgen
  have mem : ∀ {r}, r < D.nregs → Sp.toMat R[r]! ∈ S := fun hr => (Sp.regsOf_ok hprog hr).2
  have eK1 := Sp.pow_eq_one_of_check (hWF _) hK1
  have eK2 := Sp.pow_eq_one_of_check (hWF _) hK2
  let k1 := unitOf S (mem rk1) ho1.ne' eK1
  let k2 := unitOf S (mem rk2) ho2.ne' eK2
  have f1 : valHom S k1 = Sp.toMat R[D.rk1]! := valHom_unitOf S _ _ _
  have f2 : valHom S k2 = Sp.toMat R[D.rk2]! := valHom_unitOf S _ _ _
  obtain ⟨e, emat, emem, eall, einj⟩ := Sp.enum_spec hWF f1 f2 ho1.ne' ho2.ne'
    (unitOf_pow S _ _ eK1) (unitOf_pow S _ _ eK2) henum
  set K := Subgroup.closure ({k1, k2} : Set Sˣ)
  have hEsize : En.1.size = D.nP := by
    unfold Ops.enumOK at henum
    simp only [Bool.and_eq_true, beq_iff_eq] at henum
    exact henum.1.1.1.1.1.1.1.1
  have hcardK : Nat.card K = D.nP := by
    let F : Fin D.nP → K := fun i => ⟨e i, emem i i.isLt⟩
    have hF : Function.Bijective F := by
      refine ⟨fun i j hij => Fin.ext (einj i i.isLt j j.isLt (congrArg Subtype.val hij)),
        fun u => ?_⟩
      obtain ⟨i, hi, hu⟩ := eall u u.2
      exact ⟨⟨i, hi⟩, Subtype.ext hu.symm⟩
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]
  have listed : ∀ {X : M}, O.memOK En.1 X = true → ∃ u ∈ K, valHom S u = Sp.toMat X := by
    intro X hX
    obtain ⟨j, hj, hjX⟩ := Sp.memOK_spec hWF hX
    rw [hEsize] at hj
    exact ⟨e j, emem j hj, by rw [emat j hj, hjX]⟩
  unfold Ops.qFacts at hq
  simp only [Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨⟨hxK, hyK⟩, hx3⟩, hy3⟩, hxy⟩, hnf⟩ := hq
  obtain ⟨xu, hxu, fx⟩ := listed hxK
  obtain ⟨yu, hyu, fy⟩ := listed hyK
  have hx3' : xu ^ 3 = 1 := valHom_injective S (by
    rw [map_pow, fx, Sp.pow_eq_one_of_check (hWF _) hx3, map_one])
  have hy3' : yu ^ 3 = 1 := valHom_injective S (by
    rw [map_pow, fy, Sp.pow_eq_one_of_check (hWF _) hy3, map_one])
  have hxy' : xu * yu = yu * xu := valHom_injective S (by
    rw [map_mul, map_mul, fx, fy]
    have := Sp.toMat_eq (hWF _) (hWF _) hxy
    rwa [Sp.toMat_mul (hWF _) (hWF _), Sp.toMat_mul (hWF _) (hWF _)] at this)
  have hinj : Function.Injective fun t : Fin 3 × Fin 3 => xu ^ (t.1 : ℕ) * yu ^ (t.2 : ℕ) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hm := congrArg (valHom S) hij
    simp only [map_mul, map_pow] at hm
    rw [fx, fy] at hm
    unfold Ops.normalFormOK at hnf
    set vs := Array.ofFn (n := 3 ^ [R[D.rx]!, R[D.ry]!].length) fun n =>
      O.appBase 3 [R[D.rx]!, R[D.ry]!] n.val (O.unit D.t)
    have hvs : ∀ n < 3 ^ 2, Sp.toVec vs[n]! = Sp.toVec (O.unit D.t) ᵥ*
        (Sp.toMat R[D.rx]! ^ (n % 3) * Sp.toMat R[D.ry]! ^ (n / 3 % 3)) := by
      intro n hn'
      rw [getElem!_pos vs n (by simpa [vs] using hn'), Array.getElem_ofFn]
      exact Sp.appBase_two (hWF _) (hWF _) 3 n (Sp.unit_wf D.t)
    have hcode : ∀ (i j : Fin 3), (i + 3 * j : ℕ) < 3 ^ 2 ∧ (i + 3 * j : ℕ) % 3 = i ∧
        (i + 3 * j : ℕ) / 3 % 3 = j := by
      intro i j
      have := i.isLt
      have := j.isLt
      omega
    obtain ⟨c1, c2, c3⟩ := hcode i j
    obtain ⟨c1', c2', c3'⟩ := hcode i' j'
    by_contra hne
    have hcne : (i + 3 * j : ℕ) ≠ i' + 3 * j' := by
      intro hc
      apply hne
      have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
      have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have hsz : vs.size = 3 ^ 2 := by simp [vs]
    apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
    rw [hvs _ c1, hvs _ c1', c2, c3, c2', c3', hm]
  have hZcard : Nat.card (Subgroup.closure ({xu, yu} : Set Sˣ)) = 3 ^ 2 :=
    card_closure_eq_sq (by norm_num) hx3' hy3' hxy' hinj
  have hZK : Subgroup.closure ({xu, yu} : Set Sˣ) ≤ K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact hxu
    · exact hyu
  unfold Ops.centralFacts at hcent
  simp only [Bool.and_eq_true] at hcent
  obtain ⟨⟨⟨hXK1, hXK2⟩, hYK1⟩, hYK2⟩ := hcent
  have ccomm : ∀ {uu kk : Sˣ} {U Kx : M}, valHom S uu = Sp.toMat U →
      valHom S kk = Sp.toMat Kx → O.commOK U Kx = true → Commute uu kk := by
    intro uu kk U Kx hu hk hce
    apply valHom_injective S
    rw [map_mul, map_mul, hu, hk]
    have := Sp.toMat_eq (Sp.mul_wf (hWF _) (hWF _)) (Sp.mul_wf (hWF _) (hWF _)) hce
    rwa [Sp.toMat_mul (hWF _) (hWF _), Sp.toMat_mul (hWF _) (hWF _)] at this
  have hcomm : ∀ {uu : Sˣ} {U : M}, valHom S uu = Sp.toMat U →
      O.commOK U R[D.rk1]! = true → O.commOK U R[D.rk2]! = true → ∀ g ∈ K, Commute uu g := by
    intro uu U hu h1 h2 g hg
    have hle : K ≤ Subgroup.centralizer {uu} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (ccomm hu f1 h1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (ccomm hu f2 h2).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hxc := hcomm fx hXK1 hXK2
  have hyc := hcomm fy hYK1 hYK2
  refine ⟨K, Subgroup.closure ({xu, yu} : Set Sˣ), hcardK, hZK, fun z hz g hg => ?_, hZcard⟩
  have hle : Subgroup.closure ({xu, yu} : Set Sˣ) ≤ Subgroup.centralizer {g} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hxc g hg)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hyc g hg)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
