
module

public import Certificates.Data.Kernel.CoreD2K.PairsZ
public import CFSG.Certificates.Kernel.CoreD2K.Pairs

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm
open scoped Pointwise

theorem card_sup_le_of_le_normalizer {X : Type*} [Group X] {H K : Subgroup X}
    (h : H ≤ Subgroup.normalizer (K : Set X)) : Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right H K h
  calc Nat.card ↥(H ⊔ K) = Nat.card ((H : Set X) * (K : Set X)) := by rw [← e]; rfl
    _ ≤ _ := Set.natCard_mul_le

theorem card_zpowers_le {X : Type*} [Group X] {p : ℕ} (hp : 0 < p) {x : X} (hx : x ^ p = 1) :
    Nat.card (Subgroup.zpowers x) ≤ p := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one hp hx

theorem card_closure_three_le {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : 0 < p)
    {e₀ e₁ e₂ : X} (h0 : e₀ ^ p = 1) (h1 : e₁ ^ p = 1) (h2 : e₂ ^ p = 1)
    (h02 : e₀ * e₂ = e₂ * e₀)
    (hN : e₁ ∈ Subgroup.normalizer ((Subgroup.closure ({e₀, e₂} : Set X) : Subgroup X) : Set X))
    {E : Subgroup X} (hE : ∀ x ∈ E, x ∈ Subgroup.closure ({e₀, e₁, e₂} : Set X)) :
    Nat.card E ≤ p ^ 3 := by
  set N := Subgroup.closure ({e₀, e₂} : Set X) with hNdef
  have hN02 : N ≤ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers e₂ := by
    rw [hNdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hz02 : Subgroup.zpowers e₀ ≤
      Subgroup.normalizer ((Subgroup.zpowers e₂ : Subgroup X) : Set X) :=
    Subgroup.zpowers_le.2 (mem_normalizer_zpowers_of_mul_eq (α := 1) (by rw [pow_one]; exact h02))
  have hNc : Nat.card N ≤ p * p :=
    (Subgroup.card_le_of_le hN02).trans ((card_sup_le_of_le_normalizer hz02).trans
      (Nat.mul_le_mul (card_zpowers_le hp h0) (card_zpowers_le hp h2)))
  have hle : Subgroup.closure ({e₀, e₁, e₂} : Set X) ≤ Subgroup.zpowers e₁ ⊔ N := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact le_sup_right (a := Subgroup.zpowers e₁) (Subgroup.subset_closure (by simp))
    · exact le_sup_left (b := N) (Subgroup.mem_zpowers y)
    · exact le_sup_right (a := Subgroup.zpowers e₁) (Subgroup.subset_closure (by simp))
  have hEle : E ≤ Subgroup.zpowers e₁ ⊔ N := fun x hx => hle (hE x hx)
  calc Nat.card E ≤ Nat.card ↥(Subgroup.zpowers e₁ ⊔ N) := Subgroup.card_le_of_le hEle
    _ ≤ Nat.card (Subgroup.zpowers e₁) * Nat.card N :=
      card_sup_le_of_le_normalizer (Subgroup.zpowers_le.2 hN)
    _ ≤ p * (p * p) := Nat.mul_le_mul (card_zpowers_le hp h1) hNc
    _ = p ^ 3 := by ring

theorem card_eq_of_nonabelian {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E : Subgroup X} (hEp : IsPGroup p E) (hle : Nat.card E ≤ p ^ 3)
    (hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) : Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  rw [hk] at hle ⊢
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hcomm : ¬ ∀ a b : E, a * b = b * a := fun h =>
    hxy (congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hdvd : Nat.card E ∣ p := by
      rw [hk]
      exact (pow_dvd_pow p (by omega : k ≤ 1)).trans (by rw [pow_one])
    have : IsCyclic E := isCyclic_of_card_dvd_prime hdvd
    exact absurd (fun a b => IsCyclic.commutative.is_comm.comm a b) hcomm
  · rcases Nat.lt_or_ge k 3 with hk2' | hk3'
    · have hk2'' : k = 2 := by omega
      subst hk2''
      exact absurd (IsPGroup.commutative_of_card_eq_prime_sq hk) hcomm
    · rw [show k = 3 by omega]

theorem coreGenerationZOf_of_zchecks {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    {f1 f2 f3 f4 : Nat} (hn : szOK n w = true) (hgens : gensK n w V GP GPI EG GT GTI = true)
    (hnab : nabK n w V.base.eW.length EG = true)
    (hcen : cenK n w V.base.p V.base.eW.length EG = true)
    (hpairs : pairsZK n w V.base GP EG GT GTI = true)
    (hnorm : normK n w V.base.p V.base.eW.length EG f1 f2 f3 f4 = true) (hp : V.base.p.Prime)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    CoreGenerationZOf ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))) V.base.p := by
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
  have he0 := (pr_beq (pr_pow hn hP0 p) (pr_one hn)).1 h0p
  have he1 := (pr_beq (pr_pow hn hP1 p) (pr_one hn)).1 h1p
  have he2 := (pr_beq (pr_pow hn hP2 p) (pr_one hn)).1 h2p
  have he02 := (pr_beq (pr_mul hP0 hP2) (pr_mul hP2 hP0)).1 h02
  have hN := mem_normalizer_closure_pair (α := f1) (β := f2) (γ := f3) (δ := f4)
    ((pr_beq (pr_mul hP1 hP0) (pr_mul (pr_mul (pr_pow hn hP0 f1) (pr_pow hn hP2 f2)) hP1)).1 n1)
    ((pr_beq (pr_mul hP1 hP2) (pr_mul (pr_mul (pr_pow hn hP0 f3) (pr_pow hn hP2 f4)) hP1)).1 n2)
  have hE3 : ∀ x ∈ E, x ∈ Subgroup.closure ({Le.getD 0 1, Le.getD 1 1, Le.getD 2 1} :
      Set (Equiv.Perm (Fin n))) := by
    intro x hx
    refine (Subgroup.closure_le _).2 ?_ hx
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have hk' : k < 3 := by simpa [hLe, ← hne, hne3] using hk
    rw [← List.getD_eq_getElem _ 1 hk]
    interval_cases k <;> exact Subgroup.subset_closure (by simp)
  have hEp : IsPGroup p E := isPGroup_closure_three he0 he1 he2 he02 hN hE3
  have hEle : Nat.card E ≤ p ^ 3 := card_closure_three_le hp.pos he0 he1 he2 he02 hN hE3
  unfold nabK at hnab
  have hnab' := bnot_e hnab
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hall : allN ne (fun i => strictB (EG i) (fun x => allN ne (fun j => strictB (EG j)
        (fun y => Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x))))) = true := by
      refine PK.allN_iff.2 fun i hi => ?_
      rw [PK.strictB_eq]
      refine PK.allN_iff.2 fun j hj => ?_
      rw [PK.strictB_eq]
      exact (pr_beq (pr_mul (hEP i hi) (hEP j hj)) (pr_mul (hEP j hj) (hEP i hi))).2
        (hcon _ (hmemE i hi) _ (hmemE j hj))
    rw [hall] at hnab'
    exact absurd hnab' (by decide)
  have hEc : Nat.card E = p ^ 3 := card_eq_of_nonabelian hp hEp hEle hnc
  unfold cenK at hcen
  rw [PK.strictB_eq] at hcen
  obtain ⟨h0, hcen⟩ := band_e hcen
  obtain ⟨hzp, hcen⟩ := band_e hcen
  obtain ⟨hz1, hzc⟩ := band_e hcen
  have h0' : 0 < ne := Nat.blt_eq.mp h0
  set z := Le.getD 0 1 with hzdef
  have hzP : PR n w (EG 0) z := hEP 0 h0'
  have hzE : z ∈ E := hmemE 0 h0'
  have hzp' : z ^ p = 1 := (pr_beq (pr_pow hn hzP p) (pr_one hn)).1 hzp
  have hz1' : z ≠ 1 := pr_ne hzP (pr_one hn) hz1
  have hzcent : ∀ x ∈ E, x * z = z * x := by
    have hcl : E ≤ Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin n))) := by
      rw [hEdef, Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hk' : k < ne := by simpa [hLe] using hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← List.getD_eq_getElem _ 1 hk]
      have hc := PK.allN_iff.1 hzc k hk'
      rw [PK.strictB_eq] at hc
      exact ((pr_beq (pr_mul hzP (hEP k hk')) (pr_mul (hEP k hk') hzP)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  unfold pairsZK at hpairs
  obtain ⟨hpall, hpairs⟩ := band_e hpairs
  obtain ⟨hfus, hpairs⟩ := band_e hpairs
  obtain ⟨hwA, hwB⟩ := band_e hpairs
  unfold fusK at hfus
  obtain ⟨-, hfall⟩ := band_e hfus
  have hΓ : ∀ g ∈ {g | g ∈ Lg},
      (∃ u v : Equiv.Perm (Fin n), u ∈ E ∧ v ∈ E ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧
        u ≠ 1 ∧ (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
          g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
      (∃ u ∈ E, u ≠ 1 ∧ u ^ p = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧ ∃ α : ℕ, g * u = u ^ α * g) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < D.gWs.length := by simpa [hLg] using hj
    rw [← List.getD_eq_getElem _ 1 hj]
    obtain ⟨hfp, hkj⟩ := band_e (PK.allN_iff.1 hfall j hj')
    generalize hf : D.fd.getD j default = f at hfp hkj
    have hfp' : f.pair < D.pairs.length := Nat.blt_eq.mp hfp
    generalize hq : D.pairs.getD f.pair (0, 0) = q at hkj
    have hpq : pairZK n w p ne EG q = true := by
      have := PK.allN_iff.1 hpall f.pair hfp'
      rwa [hq] at this
    have hg := hgP j hj'
    obtain ⟨e1, e2⟩ := kindK_zero hkj
    unfold pairZK at hpq
    cases hqq : Nat.beq q.1 q.2 with
    | true =>
      rw [hqq] at hpq
      have hq1 : q.1 = 0 := Nat.eq_of_beq_eq_true hpq
      have hq2 : q.2 = 0 := (Nat.eq_of_beq_eq_true hqq).symm.trans hq1
      rw [hq1, hq2] at e1
      right
      refine ⟨z, hzE, hz1', hzp', hzcent, f.α + f.β, ?_⟩
      rw [pow_add]
      exact (pr_beq (pr_mul hg hzP)
        (pr_mul (pr_mul (pr_pow hn hzP f.α) (pr_pow hn hzP f.β)) hg)).1 e1
    | false =>
      rw [hqq] at hpq
      have hpq' : pairPK n w p ne EG q = true := hpq
      unfold pairPK at hpq'
      obtain ⟨hq1, hpq'⟩ := band_e hpq'
      obtain ⟨hq2, hpq'⟩ := band_e hpq'
      rw [PK.strictB_eq, PK.strictB_eq] at hpq'
      obtain ⟨hup, hpq'⟩ := band_e hpq'
      obtain ⟨hu1, hpq'⟩ := band_e hpq'
      obtain ⟨huv, hvK⟩ := band_e hpq'
      unfold vK at hvK
      obtain ⟨hvp, hvu⟩ := band_e hvK
      have hq1' : q.1 < ne := Nat.blt_eq.mp hq1
      have hq2' : q.2 < ne := Nat.blt_eq.mp hq2
      have hu := hEP q.1 hq1'
      have hv := hEP q.2 hq2'
      left
      refine ⟨_, _, hmemE _ hq1', hmemE _ hq2', (pr_beq (pr_pow hn hu p) (pr_one hn)).1 hup,
        (pr_beq (pr_pow hn hv p) (pr_one hn)).1 hvp, (pr_beq (pr_mul hu hv) (pr_mul hv hu)).1 huv,
        pr_ne hu (pr_one hn) hu1, fun k hk => pr_ne hv (pr_pow hn hu k) (PK.allN_iff.1 hvu k hk),
        f.α, f.β, f.γ, f.δ, ?_, ?_⟩
      · exact (pr_beq (pr_mul hg hu)
          (pr_mul (pr_mul (pr_pow hn hu f.α) (pr_pow hn hv f.β)) hg)).1 e1
      · exact (pr_beq (pr_mul hg hv)
          (pr_mul (pr_mul (pr_pow hn hu f.γ) (pr_pow hn hv f.δ)) hg)).1 e2
  have hA' : wordVal Lg D.wA = a := (hwordG hwA).perm_eq ha
  have hB' : wordVal Lg D.wB = b := (hwordG hwB).perm_eq hb
  refine coreGenerationZOf_of_gens hp rfl hEp hEc hEG hnc (Γ := {g | g ∈ Lg}) ?_ ?_ hΓ
  · intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact wordVal_mem Lg _ (fun g hg => Subgroup.subset_closure hg) _
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact wordVal_mem Lg _ (fun g hg => Subgroup.subset_closure hg) _

end CFSG.KD.CoreD2K

end
