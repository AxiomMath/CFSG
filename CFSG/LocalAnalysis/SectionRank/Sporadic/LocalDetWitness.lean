module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Data.CFSGNative.SectionRank.LocalDet

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.SectionRank.Native LocalWitness
open scoped Matrix commutatorElement

namespace LocalWitness

variable {G : Type*} [Group G]

noncomputable def treeElt (par lab : Array ℕ) (g : ℕ → G) : ℕ → G
  | 0 => 1
  | i + 1 =>
    if _ : par[i + 1]! < i + 1 then treeElt par lab g par[i + 1]! * g lab[i + 1]! else 1
termination_by i => i

theorem treeElt_zero (par lab : Array ℕ) (g : ℕ → G) : treeElt par lab g 0 = 1 := by
  rw [treeElt]

theorem treeElt_of_lt (par lab : Array ℕ) (g : ℕ → G) {i : ℕ} (hi : 0 < i)
    (hp : par[i]! < i) : treeElt par lab g i = treeElt par lab g par[i]! * g lab[i]! := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [zero_add] at hp ⊢
  rw [treeElt, dite_eq_left hp]

end LocalWitness

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem enum_spec [Inhabited M] [Inhabited V] (hWF : ∀ X : M, Sp.WF X)
    {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} {K1 K2 : M} {k1 k2 : Sˣ}
    (f1 : valHom S k1 = Sp.toMat K1) (f2 : valHom S k2 = Sp.toMat K2) {o1 o2 : ℕ}
    (ho1 : o1 ≠ 0) (ho2 : o2 ≠ 0) (hk1 : k1 ^ o1 = 1) (hk2 : k2 ^ o2 = 1) {n t : ℕ}
    {E : Array M} {par lab : Array ℕ} {cl : Array (Array ℕ)}
    (h : O.enumOK #[K1, K2] n t E par lab cl = true) :
    ∃ e : ℕ → Sˣ, (∀ i < n, valHom S (e i) = Sp.toMat E[i]!) ∧
      (∀ i < n, e i ∈ Subgroup.closure ({k1, k2} : Set Sˣ)) ∧
      (∀ u ∈ Subgroup.closure ({k1, k2} : Set Sˣ), ∃ i < n, u = e i) ∧
      (∀ i < n, ∀ j < n, e i = e j → i = j) := by
  unfold Ops.enumOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, -⟩, -⟩, -⟩, hn⟩, h0⟩, htree⟩, hcl⟩, hdist⟩ := h
  rw [List.all_eq_true] at htree hcl
  set g : ℕ → Sˣ := fun s => if s = 0 then k1 else k2
  set gens : Array M := #[K1, K2]
  have fg : ∀ s < 2, valHom S (g s) = Sp.toMat gens[s]! := by
    intro s hs
    interval_cases s
    · exact f1
    · exact f2
  set e := treeElt par lab g
  have he0 : e 0 = 1 := treeElt_zero par lab g
  have hes : ∀ i, 0 < i → par[i]! < i → e i = e par[i]! * g lab[i]! :=
    fun i => treeElt_of_lt par lab g
  have hmat : ∀ i < n, valHom S (e i) = Sp.toMat E[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [he0, map_one, Sp.toMat_eq (hWF _) Sp.one_wf h0, Sp.toMat_one]
      · have := htree i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
        rcases this with h1 | ⟨⟨hp, hl⟩, heq⟩
        · omega
        · rw [hes i hpos hp, map_mul, ih _ hp (by omega),
            Sp.toMat_eq (hWF _) (hWF _) heq, Sp.toMat_mul (hWF _) (hWF _), fg _ hl]
  have hmem : ∀ i < n, e i ∈ Subgroup.closure ({k1, k2} : Set Sˣ) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [he0]; exact Subgroup.one_mem _
      · have := htree i (List.mem_range.2 hi)
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
        rcases this with h1 | ⟨⟨hp, hl⟩, -⟩
        · omega
        · rw [hes i hpos hp]
          refine Subgroup.mul_mem _ (ih _ hp (by omega)) (Subgroup.subset_closure ?_)
          simp only [g]
          split_ifs
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
  have hright : ∀ i < n, ∀ s < 2, ∃ j < n, e i * g s = e j := by
    intro i hi s hs
    have := List.all_eq_true.1 (hcl i (List.mem_range.2 hi)) s (List.mem_range.2 hs)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    refine ⟨_, this.1, valHom_injective S ?_⟩
    rw [map_mul, hmat i hi, fg s hs, hmat _ this.1, ← Sp.toMat_mul (hWF _) (hWF _)]
    exact Sp.toMat_eq (hWF _) (hWF _) this.2
  have hpow : ∀ s < 2, ∀ m, ∀ i < n, ∃ j < n, e i * g s ^ m = e j := by
    intro s hs m
    induction m with
    | zero => intro i hi; exact ⟨i, hi, by rw [pow_zero, mul_one]⟩
    | succ m ih =>
      intro i hi
      obtain ⟨j, hj, hje⟩ := ih i hi
      obtain ⟨j', hj', hj'e⟩ := hright j hj s hs
      exact ⟨j', hj', by rw [pow_succ, ← mul_assoc, hje, hj'e]⟩
  have hgen : ∀ s ∈ ({k1, k2} : Set Sˣ), ∃ t < 2, g t = s ∧ ∃ o, o ≠ 0 ∧ s ^ o = 1 := by
    rintro s (rfl | rfl)
    · exact ⟨0, by norm_num, by simp [g], o1, ho1, hk1⟩
    · exact ⟨1, by norm_num, by simp [g], o2, ho2, hk2⟩
  have hall : ∀ u ∈ Subgroup.closure ({k1, k2} : Set Sˣ), ∃ i < n, u = e i := by
    intro u hu
    induction hu using Subgroup.closure_induction_right with
    | one => exact ⟨0, hn, by rw [he0]⟩
    | mul_right u _ s hs ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨t', ht, rfl, -⟩ := hgen s hs
      obtain ⟨j, hj, hje⟩ := hright i hi t' ht
      exact ⟨j, hj, hje⟩
    | mul_inv_cancel u _ s hs ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨t', ht, rfl, o, ho, hso⟩ := hgen s hs
      have hinv : (g t')⁻¹ = g t' ^ (o - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel
          (Nat.pos_of_ne_zero ho), hso]
      obtain ⟨j, hj, hje⟩ := hpow t' ht (o - 1) i hi
      exact ⟨j, hj, by rw [hinv, hje]⟩
  refine ⟨e, hmat, hmem, hall, fun i hi j hj hij => ?_⟩
  by_contra hne
  have hsz : (E.map fun X => O.vmul (O.unit t) X).size = n := by simp [hE]
  apply Sp.toVec_ne_of_distinctOK hdist (by rw [hsz]; exact hi) (by rw [hsz]; exact hj) hne
  rw [getElem!_pos _ i (by rw [hsz]; exact hi), getElem!_pos _ j (by rw [hsz]; exact hj),
    Array.getElem_map, Array.getElem_map, Sp.toVec_vmul (Sp.unit_wf _) (hWF _),
    Sp.toVec_vmul (Sp.unit_wf _) (hWF _), ← getElem!_pos E i (by rw [hE]; exact hi),
    ← getElem!_pos E j (by rw [hE]; exact hj), ← hmat i hi, ← hmat j hj, hij]

theorem memOK_spec [Inhabited M] (hWF : ∀ X : M, Sp.WF X) {E : Array M} {X : M}
    (h : O.memOK E X = true) : ∃ j < E.size, Sp.toMat X = Sp.toMat E[j]! := by
  obtain ⟨j, hj, hjx⟩ := List.any_eq_true.1 h
  exact ⟨j, List.mem_range.1 hj, Sp.toMat_eq (hWF _) (hWF _) hjx⟩

theorem conjMemOK_spec [Inhabited M] (hWF : ∀ X : M, Sp.WF X) {E : Array M} {H X : M}
    (h : O.conjMemOK E H X = true) :
    ∃ j < E.size, Sp.toMat H * Sp.toMat X = Sp.toMat E[j]! * Sp.toMat H := by
  obtain ⟨j, hj, hjx⟩ := List.any_eq_true.1 h
  exact ⟨j, List.mem_range.1 hj, Sp.toMat_of_conjOK (hWF _) (hWF _) (hWF _) hjx⟩

theorem notMemOK_spec [Inhabited M] (hWF : ∀ X : M, Sp.WF X) {E : Array M} {X : M} {t : ℕ}
    (h : O.notMemOK E X t = true) : ∀ j < E.size, Sp.toMat X ≠ Sp.toMat E[j]! := by
  intro j hj hX
  apply Sp.toVec_ne (List.all_eq_true.1 h j (List.mem_range.2 hj))
  rw [Sp.toVec_vmul (Sp.unit_wf _) (hWF _), Sp.toVec_vmul (Sp.unit_wf _) (hWF _), hX]

theorem localDet_of_check [Inhabited M] [Inhabited V] (hWF : ∀ X : M, Sp.WF X)
    (D : LocDetData) (hfac : D.nK.factorization 3 = 2) (hc : O.localDetCheck D = true) :
    ∃ (K : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) (_ : Group.IsPerfect K)
      (Q : Sylow 3 K) (x y : K) (h cc : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ),
      Nat.card K = D.nK ∧ IsElemAbelian 3 (Q : Subgroup K) ∧
      Nat.card (Q : Subgroup K) = 3 ^ 2 ∧
      h ∈ Subgroup.normalizer (K : Set (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) ∧
      Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ =
        (x : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) ^ D.a *
          (y : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) ^ D.c ∧
      h * y * h⁻¹ =
        (x : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) ^ D.b *
          (y : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ) ^ D.d ∧
      (∀ k ∈ K, Commute cc k) ∧ orderOf cc = 3 ∧ Subgroup.zpowers cc ⊓ K = ⊥ := by
  classical
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.localDetCheck at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨-, hprog⟩, hregs⟩, hf⟩ := hc
  unfold LocDetData.regsLt at hregs
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hregs
  obtain ⟨rk1, rk2, rx, ry, rh, rc, ru1, rv1, ru2, rv2⟩ := hregs
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  set En := O.enumBFS #[R[D.rk1]!, R[D.rk2]!] D.nK
  unfold Ops.localDetFacts at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨hgen, henum⟩, hq⟩, hh⟩, hcf⟩, hp1⟩, hp2⟩ := hf
  unfold Ops.genFacts at hgen
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
  have hEsize : En.1.size = D.nK := by
    unfold Ops.enumOK at henum
    simp only [Bool.and_eq_true, beq_iff_eq] at henum
    exact henum.1.1.1.1.1.1.1.1
  have hcardK : Nat.card K = D.nK := by
    let F : Fin D.nK → K := fun i => ⟨e i, emem i i.isLt⟩
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
  let x : K := ⟨xu, hxu⟩
  let y : K := ⟨yu, hyu⟩
  have hx3' : x ^ 3 = 1 := Subtype.ext (valHom_injective S (by
    rw [Subgroup.coe_pow, map_pow, fx, Sp.pow_eq_one_of_check (hWF _) hx3]; rfl))
  have hy3' : y ^ 3 = 1 := Subtype.ext (valHom_injective S (by
    rw [Subgroup.coe_pow, map_pow, fy, Sp.pow_eq_one_of_check (hWF _) hy3]; rfl))
  have hxy' : x * y = y * x := Subtype.ext (valHom_injective S (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, fx, fy]
    have := Sp.toMat_eq (hWF _) (hWF _) hxy
    rwa [Sp.toMat_mul (hWF _) (hWF _), Sp.toMat_mul (hWF _) (hWF _)] at this))
  have hinj : Function.Injective fun t : Fin 3 × Fin 3 => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hm := congrArg (fun w : K => valHom S (w : Sˣ)) hij
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow] at hm
    rw [show ((x : Sˣ)) = xu from rfl, show ((y : Sˣ)) = yu from rfl, fx, fy] at hm
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
  have hQcard : Nat.card (Subgroup.closure ({x, y} : Set K)) = 3 ^ 2 :=
    card_closure_eq_sq (by norm_num) hx3' hy3' hxy' hinj
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnK : 0 < D.nK := by
    unfold Ops.enumOK at henum
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at henum
    exact henum.1.1.1.1.2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; omega)
  let Q : Sylow 3 K := Sylow.ofCard (Subgroup.closure ({x, y} : Set K)) (by
    rw [hQcard, hcardK, hfac])
  have hQ : (Q : Subgroup K) = Subgroup.closure ({x, y} : Set K) := rfl
  have hQab : IsElemAbelian 3 (Q : Subgroup K) := by
    rw [hQ]
    refine ⟨Subgroup.isMulCommutative_closure ?_, fun q hq => ?_⟩
    · rintro a (rfl | rfl) b (rfl | rfl) _
      · exact Commute.refl _
      · exact hxy'
      · exact hxy'.symm
      · exact Commute.refl _
    · have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy'
      obtain ⟨i, j, k, -, -, -, rfl⟩ := mem_closure_normalForm (by norm_num) hx3' hy3'
        (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) hq
      rw [hz, one_pow, mul_one, (Commute.pow_pow hxy' i j).mul_pow, ← pow_mul, ← pow_mul,
        mul_comm i, mul_comm j, pow_mul, pow_mul, hx3', hy3', one_pow, one_pow, one_mul]
  have hperf : Group.IsPerfect K := by
    have comm : ∀ {kk : Sˣ} {Kx U W : M}, valHom S kk = Sp.toMat Kx →
        O.perfFacts En.1 Kx U W = true → kk ∈ ⁅K, K⁆ := by
      intro kk Kx U W hkk hpf
      unfold Ops.perfFacts at hpf
      simp only [Bool.and_eq_true] at hpf
      obtain ⟨⟨hU, hW⟩, hUW⟩ := hpf
      obtain ⟨u, hu, fu⟩ := listed hU
      obtain ⟨w, hw, fw⟩ := listed hW
      have hrel : u * w = kk * w * u := valHom_injective S (by
        rw [map_mul, map_mul, map_mul, fu, fw, hkk]
        have := Sp.toMat_eq (hWF _) (hWF _) hUW
        rwa [Sp.toMat_mul (hWF _) (hWF _), Sp.toMat_mul (hWF _) (hWF _),
          Sp.toMat_mul (hWF _) (hWF _)] at this)
      have : kk = ⁅u, w⁆ := by
        rw [commutatorElement_def, hrel]
        group
      rw [this]
      exact Subgroup.commutator_mem_commutator hu hw
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact comm f1 hp1
      · exact comm f2 hp2
  unfold Ops.hFacts at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨⟨⟨hoh, hH⟩, hHK1⟩, hHK2⟩, hHX⟩, hHY⟩ := hh
  have eH := Sp.pow_eq_one_of_check (hWF _) hH
  let h := unitOf S (mem rh) hoh.ne' eH
  have fh : valHom S h = Sp.toMat R[D.rh]! := valHom_unitOf S _ _ _
  have conjK : ∀ {kk : Sˣ} {Kx : M}, valHom S kk = Sp.toMat Kx →
      O.conjMemOK En.1 R[D.rh]! Kx = true → h * kk * h⁻¹ ∈ K := by
    intro kk Kx hkk hcm
    obtain ⟨j, hj, hjm⟩ := Sp.conjMemOK_spec hWF hcm
    rw [hEsize] at hj
    have : h * kk * h⁻¹ = e j := by
      rw [mul_inv_eq_iff_eq_mul]
      apply valHom_injective S
      rw [map_mul, map_mul, fh, hkk, emat j hj, hjm]
    rw [this]
    exact emem j hj
  have hnorm : h ∈ Subgroup.normalizer (K : Set Sˣ) := by
    have hle : K.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact conjK f1 hHK1
      · exact conjK f2 hHK2
    have heq : K.map (MulAut.conj h).toMonoidHom = K :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj h).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [← heq]
      exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← heq] at hg
      obtain ⟨g', hg', hgg⟩ := hg
      have : g' = g := by
        simpa [MulAut.conj_apply] using hgg
      rw [← this]
      exact hg'
  have conj : ∀ {w : Sˣ} {W : M}, valHom S w = Sp.toMat W → ∀ {u : Sˣ} {U : M},
      valHom S u = Sp.toMat U → O.conjOK R[D.rh]! U W = true → h * u * h⁻¹ = w := by
    intro w W hw u U hu hc
    rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    rw [map_mul, map_mul, fh, hu, hw]
    exact Sp.toMat_of_conjOK (hWF _) (hWF _) (hWF _) hc
  have word : ∀ i j : ℕ, valHom S ((x : Sˣ) ^ i * (y : Sˣ) ^ j) =
      Sp.toMat (O.mul (O.pow R[D.rx]! i) (O.pow R[D.ry]! j)) := by
    intro i j
    rw [map_mul, map_pow, map_pow, show ((x : Sˣ)) = xu from rfl, show ((y : Sˣ)) = yu from rfl,
      fx, fy, Sp.toMat_mul (hWF _) (hWF _), (Sp.pow_spec (hWF _) i).2, (Sp.pow_spec (hWF _) j).2]
  unfold Ops.cFacts at hcf
  simp only [Bool.and_eq_true] at hcf
  obtain ⟨⟨⟨⟨⟨hC3, hCt⟩, hCK1⟩, hCK2⟩, hCn⟩, hC2n⟩ := hcf
  have eC := Sp.pow_eq_one_of_check (hWF _) hC3
  let cc := unitOf S (mem rc) (by norm_num) eC
  have fc : valHom S cc = Sp.toMat R[D.rc]! := valHom_unitOf S _ _ _
  have hcc3 : cc ^ 3 = 1 := unitOf_pow S _ _ eC
  have hcc1 : cc ≠ 1 := by
    intro h1
    apply Sp.toVec_ne hCt
    rw [Sp.toVec_vmul (Sp.unit_wf _) (hWF _), ← fc, h1, map_one, Matrix.vecMul_one]
  have ccomm : ∀ {kk : Sˣ} {Kx : M}, valHom S kk = Sp.toMat Kx →
      O.eq (O.mul R[D.rc]! Kx) (O.mul Kx R[D.rc]!) = true → Commute cc kk := by
    intro kk Kx hkk hce
    apply valHom_injective S
    rw [map_mul, map_mul, fc, hkk]
    have := Sp.toMat_eq (hWF _) (hWF _) hce
    rwa [Sp.toMat_mul (hWF _) (hWF _), Sp.toMat_mul (hWF _) (hWF _)] at this
  have hcK : ∀ k ∈ K, Commute cc k := by
    have hle : K ≤ Subgroup.centralizer {cc} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (ccomm f1 hCK1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (ccomm f2 hCK2).symm
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hk)).symm
  have hnot : ∀ {u : Sˣ} {U : M}, valHom S u = Sp.toMat U → O.notMemOK En.1 U D.t = true →
      u ∉ K := by
    intro u U hu hn huK
    obtain ⟨j, hj, rfl⟩ := eall u huK
    have := Sp.notMemOK_spec hWF hn j (by rw [hEsize]; exact hj)
    rw [← hu, emat j hj] at this
    exact this rfl
  have hcK1 : Subgroup.zpowers cc ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgz, hgK⟩
    rw [Subgroup.mem_bot]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgz
    have hm : cc ^ m = cc ^ (m % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact (zpow_eq_zpow_emod' m hcc3).trans rfl
    rw [hm] at hgK ⊢
    have hlt : (m % 3).toNat < 3 := by omega
    interval_cases hk : (m % 3).toNat
    · rfl
    · rw [pow_one] at hgK
      exact absurd hgK (hnot fc hCn)
    · exact absurd hgK (hnot (by
        rw [map_pow, fc, pow_two, ← Sp.toMat_mul (hWF _) (hWF _)]) hC2n)
  refine ⟨K, hperf, Q, x, y, h, cc, hcardK, hQab, by rw [hQ]; exact hQcard, hnorm, hQ.symm,
    conj (word _ _) (show valHom S (x : Sˣ) = Sp.toMat R[D.rx]! from fx) hHX,
    conj (word _ _) (show valHom S (y : Sˣ) = Sp.toMat R[D.ry]! from fy) hHY, hcK,
    orderOf_eq_prime hcc3 hcc1, hcK1⟩

end OpsSpec

end CFSG.SectionRank
