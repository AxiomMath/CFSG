module

public import Certificates.Certificate5137
public import Certificates.Data.FooteLitCF23L216Check
public import Certificates.Data.Kernel.PermCent.L216Syl
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.PermCent.SylowReps
public import CFSG.CGT.Stroth77.NonSplit.Closure

public section

namespace CFSG.KC.L216Syl

open Subgroup

section Generic

variable {G : Type*} [Group G]

@[expose] def PhiR (H : Subgroup G) (a b x : G) : Prop :=
  x * x = 1 → x = 1 ∨ ∃ c ∈ H, c * x * c⁻¹ = a ∨ c * x * c⁻¹ = b

theorem conj_sq (g x : G) : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group

theorem phiR_conj_mem (H : Subgroup G) (a b : G) {p : G} (hp : p ∈ H) (x : G) :
    PhiR H a b (p * x * p⁻¹) ↔ PhiR H a b x := by
  unfold PhiR
  rw [conj_sq, conj_eq_one_iff, conj_eq_one_iff]
  refine imp_congr_right fun _ => or_congr_right ⟨?_, ?_⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨c * p, mul_mem hc hp, ?_⟩
    rwa [show c * p * x * (c * p)⁻¹ = c * (p * x * p⁻¹) * c⁻¹ by group]
  · rintro ⟨c, hc, h⟩
    refine ⟨c * p⁻¹, mul_mem hc (inv_mem hp), ?_⟩
    rwa [show c * p⁻¹ * (p * x * p⁻¹) * (c * p⁻¹)⁻¹ = c * x * c⁻¹ by group]

theorem phiR_conj_norm (H : Subgroup G) {a b s : G} (hs : ∀ c ∈ H, s * c * s⁻¹ ∈ H)
    (hs' : ∀ c ∈ H, s⁻¹ * c * s ∈ H) (ha : s * a = a * s) (hb : s * b = b * s) (x : G) :
    PhiR H a b (s * x * s⁻¹) ↔ PhiR H a b x := by
  have ha' : s * a * s⁻¹ = a := by rw [ha, mul_inv_cancel_right]
  have hb' : s * b * s⁻¹ = b := by rw [hb, mul_inv_cancel_right]
  have ha'' : s⁻¹ * a * s = a := by rw [mul_assoc, ← ha, inv_mul_cancel_left]
  have hb'' : s⁻¹ * b * s = b := by rw [mul_assoc, ← hb, inv_mul_cancel_left]
  unfold PhiR
  rw [conj_sq, conj_eq_one_iff, conj_eq_one_iff]
  refine imp_congr_right fun _ => or_congr_right ⟨?_, ?_⟩
  · rintro ⟨c, hc, h | h⟩
    · refine ⟨s⁻¹ * c * s, hs' c hc, Or.inl ?_⟩
      rw [← ha'', ← h]
      group
    · refine ⟨s⁻¹ * c * s, hs' c hc, Or.inr ?_⟩
      rw [← hb'', ← h]
      group
  · rintro ⟨c, hc, h | h⟩
    · refine ⟨s * c * s⁻¹, hs c hc, Or.inl ?_⟩
      rw [← ha', ← h]
      group
    · refine ⟨s * c * s⁻¹, hs c hc, Or.inr ?_⟩
      rw [← hb', ← h]
      group

@[expose] def stabP (P : G → Prop) : Subgroup G where
  carrier := {g | ∀ x, P (g * x * g⁻¹) ↔ P x}
  one_mem' := fun x => by simp
  mul_mem' := fun {a b} ha hb x => by
    change P (a * b * x * (a * b)⁻¹) ↔ P x
    rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group, ha, hb]
  inv_mem' := fun {a} ha x => by
    change P (a⁻¹ * x * a⁻¹⁻¹) ↔ P x
    rw [← ha, show a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ = x by group]

theorem conj_inv_mem (H : Subgroup G) [Finite H] {s : G} (hs : ∀ c ∈ H, s * c * s⁻¹ ∈ H) :
    ∀ c ∈ H, s⁻¹ * c * s ∈ H := by
  have hle : H.map (MulAut.conj s).toMonoidHom ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    exact hs d hd
  have heq : H.map (MulAut.conj s).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj s).injective])
  intro c hc
  rw [← heq] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  change s⁻¹ * (s * d * s⁻¹) * s ∈ H
  rwa [show s⁻¹ * (s * d * s⁻¹) * s = d by group]

end Generic

section CV

open CFSG.Certificates.Kernel.PkCV

variable {n : Nat} [Small n]

theorem productsC_mem (K : Subgroup (CV n)) :
    ∀ Ts : List (List (CV n)), (∀ T ∈ Ts, ∀ t ∈ T, t ∈ K) → ∀ x ∈ productsC Ts, x ∈ K
  | [], _, x, hx => by
    simp only [productsC, List.mem_singleton] at hx
    rw [hx]
    exact one_mem K
  | T :: Ts, h, x, hx => by
    simp only [productsC, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    exact mul_mem (h T (List.mem_cons_self ..) t ht)
      (productsC_mem K Ts (fun T' hT' => h T' (List.mem_cons_of_mem _ hT')) y hy)

theorem nodupC_iff_aux (L : List (CV 17)) :
    L.rec true (fun a l r => (l.all fun b => !decide (a = b)) && r) = true → L.Nodup := by
  induction L with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    rw [Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, ih h.2⟩
    have := List.all_eq_true.1 h.1 a ha
    simp at this

end CV

section L216

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.L216S CFSG.ComponentClassification.GSThmB.CF23I.L216

theorem QP_eq : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QA_eq : QA.originalSubgroup = Subgroup.closure {pa, pb, sg} := by
  rw [QA, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QP_le : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_eq, QA_eq]
  exact closure_mono (by simp [Set.insert_subset_iff])

theorem wordC_mem : ∀ w : List Nat, ev (wordC w) ∈ QP.originalSubgroup
  | [] => by
    rw [wordC, List.foldr_nil, ev_one]
    exact one_mem _
  | i :: w => by
    have hw := wordC_mem w
    rw [wordC, List.foldr_cons, ev_mul] at *
    refine mul_mem ?_ hw
    rw [QP_eq]
    split_ifs <;> rw [ev_cOf] <;> exact subset_closure (by simp)


theorem QP_ok' : ValidSchreier QP := Certificates.certificate5137.1.1

theorem QA_ok' : ValidSchreier QA := Certificates.certificate5137.2.1.1

theorem sg_conj_mem : ∀ c ∈ QP.originalSubgroup, sg * c * sg⁻¹ ∈ QP.originalSubgroup := by
  have hn := Certificates.certificate5137.2.2.2.1
  rw [normCheck, QA, certificate_original, List.all_eq_true] at hn
  have h := hn sg (by simp)
  rw [Bool.and_eq_true, ← mem_iff_sift QP QP_ok', ← mem_iff_sift QP QP_ok'] at h
  have hle : Subgroup.closure {pa, pb} ≤
      QP.originalSubgroup.comap (MulAut.conj sg).toMonoidHom := by
    simp only [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h
  intro c hc
  rw [QP_eq] at hc
  have := hle hc
  simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

variable (hsift : siftC QP (sC * sC) 0 = false) (hcomm : eq22C sC (cOf pa) (cOf pa) sC = true)
  (hlen : elT.length = 64) (hnd : nodupC elT = true) (hst : stableC elT = true)
  (hcov : covC elT conjC = true)

include hcomm in
theorem le_stab : QA.originalSubgroup ≤ stabP (PhiR QP.originalSubgroup pa (sg * sg)) := by
  have hsa : sg * pa = pa * sg := by
    rw [eq22C_eq, decide_eq_true_eq, ← ev_eq_iff, ev_mul, ev_mul, sC, ev_cOf, ev_cOf] at hcomm
    exact hcomm
  have hpa : pa ∈ QP.originalSubgroup := by rw [QP_eq]; exact subset_closure (by simp)
  have hpb : pb ∈ QP.originalSubgroup := by rw [QP_eq]; exact subset_closure (by simp)
  rw [QA_eq, closure_le]
  rintro x (rfl | rfl | rfl)
  · exact phiR_conj_mem _ _ _ hpa
  · exact phiR_conj_mem _ _ _ hpb
  · exact phiR_conj_norm _ sg_conj_mem (conj_inv_mem _ sg_conj_mem) hsa (by group)

@[expose] noncomputable def TS : Subgroup (Equiv.Perm (Fin 17)) :=
  Subgroup.closure {g | g ∈ [ev tC, sg]}

include hst in
theorem stable_ev : (1 : Equiv.Perm (Fin 17)) ∈ elT.map ev ∧
    ∀ s ∈ elT.map ev, ∀ g ∈ [ev tC, sg], s * g ∈ elT.map ev := by
  rw [stableC, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hst
  obtain ⟨⟨y, hy, h1⟩, hall⟩ := hst
  refine ⟨List.mem_map.2 ⟨y, hy, by rw [of_decide_eq_true h1, ev_one]⟩, ?_⟩
  rintro _ hs g hg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  have h := hall x hx
  rw [Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at h
  obtain ⟨⟨y1, hy1, e1⟩, ⟨y2, hy2, e2⟩⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact List.mem_map.2 ⟨y1, hy1, by rw [← of_decide_eq_true e1, ev_mul]⟩
  · exact List.mem_map.2 ⟨y2, hy2, by rw [← of_decide_eq_true e2, ev_mul, sC, ev_cOf]⟩

theorem elT_mem : ∀ s ∈ elT.map ev, s ∈ TS := by
  rintro _ hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  let K := TS.comap (evHom 17)
  have ht : tC ∈ K := by
    change ev tC ∈ TS
    exact subset_closure (by simp)
  have hs : sC ∈ K := by
    change ev sC ∈ TS
    rw [sC, ev_cOf]
    exact subset_closure (by simp)
  have h3 : s3C ∈ K := mul_mem (mul_mem hs hs) hs
  have h1 : a1C ∈ K := mul_mem (mul_mem hs ht) h3
  have h2 : a2C ∈ K := mul_mem (mul_mem hs h1) h3
  have h3' : a3C ∈ K := mul_mem (mul_mem hs h2) h3
  refine productsC_mem K facC ?_ x hx
  simp only [facC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨⟨one_mem K, ht⟩, ⟨one_mem K, h1⟩, ⟨one_mem K, h2⟩, ⟨one_mem K, h3'⟩,
    ⟨one_mem K, hs, mul_mem hs hs, mul_mem (mul_mem hs hs) hs⟩⟩

include hlen hnd hst in
theorem card_TS : Nat.card TS = 2 ^ 6 := by
  obtain ⟨h1, hst'⟩ := stable_ev hst
  rw [TS, CFSG.CGT.Stroth77.card_closure_of_stable _ _ h1 elT_mem hst',
    List.toFinset_card_of_nodup ((nodup_map_ev _).2 (nodupC_iff_aux _ hnd)), List.length_map, hlen]
  norm_num

include hst in
theorem TS_mem : ∀ x ∈ TS, x ∈ elT.map ev := by
  obtain ⟨h1, hst'⟩ := stable_ev hst
  exact fun x hx => (CFSG.CGT.Stroth77.mem_closure_iff_of_stable _ _ h1 elT_mem hst' x).1 hx

theorem TS_le : TS ≤ QA.originalSubgroup := by
  rw [TS, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact QP_le (wordC_mem _)
  · rw [QA_eq]
    exact subset_closure (by simp)

include hst hcov in
theorem phi_TS : ∀ x ∈ TS, PhiR QP.originalSubgroup pa (sg * sg) x := by
  intro x' hx' hsq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (TS_mem hst x' hx')
  have h := List.all_eq_true.1 hcov x hx
  rw [ev_mul', one_eq_ev, ev_eq_iff] at hsq
  simp only [hsq, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, eq22C_eq] at h
  rcases h with rfl | ⟨g, hg, h⟩
  · exact Or.inl ev_one
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    refine Or.inr ⟨ev (wordC w), wordC_mem w, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    rcases h with h | h
    · left
      rw [ev_mul', h, ev_mul, ev_cOf]
    · right
      rw [ev_mul', h, ev_mul, ev_mul, sC, ev_cOf, mul_inv_cancel_right]

include hsift hcomm hlen hnd hst hcov in
theorem l216CosetOK_of : l216CosetOK = true := by
  have hΦ := CFSG.KC.SylowReps.forall_of_sylow QA.originalSubgroup TS Nat.prime_two TS_le
    (card_TS hlen hnd hst) (m := 255)
    (by rw [card_group QA QA_ok', Certificates.certificate5137.2.1.2]; norm_num)
    (by norm_num) (PhiR QP.originalSubgroup pa (sg * sg))
    (fun g hg x _ h => ((le_stab hcomm hg) x).1 h) (phi_TS hst hcov)
  unfold l216CosetOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun g hg => ?_⟩
  · rw [show sg * sg = ev (sC * sC) by rw [ev_mul, sC, ev_cOf], sift_ev, hsift]
    rfl
  · have hgA := (mem_elemsT QA QA_ok' g).1 hg
    by_cases hsq : g * g = 1
    · have h64 : g ^ (2 ^ 6) = 1 := by
        rw [show 2 ^ 6 = 2 * 32 by norm_num, pow_mul, pow_two, hsq, one_pow]
      rcases hΦ g hgA h64 hsq with h1 | ⟨c, hc, h⟩
      · simp [h1]
      · simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
        exact Or.inr ⟨c, (mem_elemsT QP QP_ok' c).2 hc, h⟩
    · simp [hsq]

end L216

end CFSG.KC.L216Syl

end
