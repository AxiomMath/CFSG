module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCCentral

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem forall_sup_of_forall {C N A B : Subgroup X} (hCN : C ≤ normalizer (N : Set X)) {d : X}
    (hAC : A ≤ C) (hBC : B ≤ C) (hA : ∀ x ∈ A, x⁻¹ * d⁻¹ * x * d ∈ N)
    (hB : ∀ x ∈ B, x⁻¹ * d⁻¹ * x * d ∈ N) : ∀ x ∈ A ⊔ B, x⁻¹ * d⁻¹ * x * d ∈ N := by
  let Z : Subgroup X :=
    { carrier := {x | x ∈ C ∧ x⁻¹ * d⁻¹ * x * d ∈ N}
      mul_mem' := by
        rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
        refine ⟨mul_mem hxC hyC, ?_⟩
        have h1 : y⁻¹ * (x⁻¹ * d⁻¹ * x * d) * y⁻¹⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hCN (inv_mem hyC)) _).mp hx
        rw [show (x * y)⁻¹ * d⁻¹ * (x * y) * d =
          (y⁻¹ * (x⁻¹ * d⁻¹ * x * d) * y⁻¹⁻¹) * (y⁻¹ * d⁻¹ * y * d) by group]
        exact mul_mem h1 hy
      one_mem' := ⟨one_mem C, by simp⟩
      inv_mem' := by
        rintro x ⟨hxC, hx⟩
        refine ⟨inv_mem hxC, ?_⟩
        have h1 : x * (x⁻¹ * d⁻¹ * x * d)⁻¹ * x⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hCN hxC) _).mp (inv_mem hx)
        rw [show x⁻¹⁻¹ * d⁻¹ * x⁻¹ * d = x * (x⁻¹ * d⁻¹ * x * d)⁻¹ * x⁻¹ by group]
        exact h1 }
  have hle : A ⊔ B ≤ Z := sup_le (fun x hx => ⟨hAC hx, hA x hx⟩) fun x hx => ⟨hBC hx, hB x hx⟩
  exact fun x hx => (hle hx).2

omit [Finite X] in
theorem inf_le_map_pPrimeCore {T N : Subgroup X} (hTN : T ≤ normalizer (N : Set X))
    (hN : Nat.Coprime 2 (Nat.card N)) : T ⊓ N ≤ (pPrimeCore 2 T).map T.subtype := by
  intro x hx
  obtain ⟨hxT, hxN⟩ := mem_inf.mp hx
  have hK : (N.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hTN g.2) n).mp hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf T)) := by
    have h1 : Nat.card (N.subgroupOf T) = Nat.card ↥(N ⊓ T) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective T.subtype_injective]
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hN
  have hle : N.subgroupOf T ≤ pPrimeCore 2 T := le_sSup ⟨hK, hcop⟩
  exact ⟨⟨x, hxT⟩, hle (mem_subgroupOf.mpr hxN), rfl⟩

theorem mem_coreActionKernel_of_target {a b d : X} {J M : Subgroup X} (hb : orderOf b = 2)
    (hab : a * b = b * a) (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hMb : M ≤ centralizer ({b} : Set X))
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a)
    (hda : d * a = a * d) (hdb : d * b = b * d) (hdJ : d ∈ normalizer (J : Set X))
    (hdM : ∀ m ∈ M, m⁻¹ * d⁻¹ * m * d ∈
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype) :
    d ∈ coreActionKernel J := by
  set Cb := centralizer ({b} : Set X) with hCb
  set N := (pPrimeCore 2 Cb).map Cb.subtype with hN
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  set OJ := (pPrimeCore 2 J).map J.subtype with hOJ
  have hCbN : Cb ≤ normalizer (N : Set X) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Cb (pPrimeCore 2 Cb)
      (le_normalizer hg)
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have hdCb : d ∈ Cb := mem_centralizer_singleton_iff.mpr hdb
  have hMaCb : conjugate M a ≤ Cb := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h2 := mul_mem (mul_mem (inv_mem haCb) (hMb hy)) haCb
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h2
  have he1 : a * d⁻¹ * a⁻¹ = d⁻¹ := by
    rw [show a * d⁻¹ * a⁻¹ = (a * d * a⁻¹)⁻¹ by group, ← hda, mul_inv_cancel_right]
  have hMa : ∀ y ∈ conjugate M a, y⁻¹ * d⁻¹ * y * d ∈ N := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    set m := a * y * a⁻¹ with hm
    have hym : y = a⁻¹ * m * a := by rw [hm]; group
    have h1 := (mem_normalizer_iff.mp (hCbN (inv_mem haCb)) _).mp (hdM m hy)
    rw [inv_inv] at h1
    have heq : y⁻¹ * d⁻¹ * y * d = a⁻¹ * (m⁻¹ * d⁻¹ * m * d) * a :=
      calc y⁻¹ * d⁻¹ * y * d = a⁻¹ * m⁻¹ * (a * d⁻¹ * a⁻¹) * m * a * d := by rw [hym]; group
        _ = a⁻¹ * m⁻¹ * d⁻¹ * m * (a * d) := by rw [he1]; group
        _ = a⁻¹ * (m⁻¹ * d⁻¹ * m * d) * a := by rw [← hda]; group
    rw [heq]
    exact h1
  have hsup := forall_sup_of_forall hCbN hMb hMaCb hdM hMa
  have hdT : d ∈ normalizer (T : Set X) := by
    have : (pLayer ↥(J ⊓ Cb) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (J ⊓ Cb)
      (pLayer ↥(J ⊓ Cb) 2) (normalizer_inf_mem hdJ (le_normalizer hdCb))
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hTJ : T ≤ J := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left
  have hTCb : T ≤ Cb := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_right
  have hTsup : T ⊔ OJ = J := gsFixedLayer_sup_map_pPrimeCore hb hJq hbJ hJb
  obtain ⟨hcore, -⟩ := restriction_quotient_mulEquiv hTJ hTsup
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    rw [hN, card_map_of_injective Cb.subtype_injective]
    exact pPrimeCore_coprime_card
  have hTN := inf_le_map_pPrimeCore (hTCb.trans hCbN) hNodd
  have hTd : ∀ t ∈ T, t⁻¹ * d⁻¹ * t * d ∈ OJ := by
    intro t ht
    have h3 : d⁻¹ * t * d ∈ T := by
      have h4 := (mem_normalizer_iff.mp (inv_mem hdT) t).mp ht
      rwa [inv_inv] at h4
    have h2 : t⁻¹ * d⁻¹ * t * d ∈ T := by
      rw [show t⁻¹ * d⁻¹ * t * d = t⁻¹ * (d⁻¹ * t * d) by group]
      exact mul_mem (inv_mem ht) h3
    have h4 := hTN (mem_inf.mpr ⟨h2, hsup t (hT ht)⟩)
    rw [hcore] at h4
    exact (mem_inf.mp h4).2
  have hJN : J ≤ normalizer (OJ : Set X) := fun j hj =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
      (le_normalizer hj)
  have hdOJ : d ∈ normalizer (OJ : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J) hdJ
  have hO : ∀ o ∈ OJ, o⁻¹ * d⁻¹ * o * d ∈ OJ := by
    intro o ho
    have h1 : d⁻¹ * o * d ∈ OJ := by
      have h2 := (mem_normalizer_iff.mp (inv_mem hdOJ) o).mp ho
      rwa [inv_inv] at h2
    rw [show o⁻¹ * d⁻¹ * o * d = o⁻¹ * (d⁻¹ * o * d) by group]
    exact mul_mem (inv_mem ho) h1
  have hall := forall_sup_of_forall hJN hTJ (map_subtype_le _) hTd hO
  rw [hTsup] at hall
  exact mem_coreActionKernel.mpr ⟨hdJ, hall⟩

theorem Config.not_commutator_le_target {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {M : Subgroup X} (hMb : M ≤ centralizer ({b} : Set X))
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) {D : Subgroup X}
    (hD : centralizer ({a} : Set X) ⊓ wCore E ⊓ centralizer ({b} : Set X) ≤ D) :
    ¬ ⁅M, D⁆ ≤
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype := by
  intro hle
  apply not_le_coreActionKernel h hb hab hbJ hJb hbE
  intro d hd
  obtain ⟨hdF, hdb⟩ := mem_inf.mp hd
  obtain ⟨hda, -⟩ := mem_inf.mp hdF
  refine mem_coreActionKernel_of_target hb hab h.le_centralizer h.isPComponent hbJ hJb hMb hT
    (mem_centralizer_singleton_iff.mp hda) (mem_centralizer_singleton_iff.mp hdb)
    (h.le_normalizer hdF) fun m hm => ?_
  have h1 : ⁅m⁻¹, d⁻¹⁆ ∈ ⁅M, D⁆ := commutator_mem_commutator (inv_mem hm) (inv_mem (hD hd))
  have h2 := hle h1
  rwa [commutatorElement_def, inv_inv, inv_inv] at h2

theorem Config.not_commutator_le_target' {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {M : Subgroup X} (hMb : M ≤ centralizer ({b} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) {D : Subgroup X}
    (hD : centralizer ({a} : Set X) ⊓ wCore E ⊓ centralizer ({b} : Set X) ≤ D) :
    ¬ ⁅M, D⁆ ≤ (pPrimeCore 2 M).map M.subtype := fun hle =>
  h.not_commutator_le_target hb hab hbJ hJb hbE hMb hT hD
    (hle.trans (GSLit.map_pPrimeCore_le_of_isPComponent hMb hMc))

theorem Config.le_normalizer_target (hSol : GrSLit.SolomonCommutingCoreInput) {a : X}
    {J E : Subgroup X} (h : Config a J E) {b : X} (hb : orderOf b = 2) (hab : a * b = b * a)
    (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {M : Subgroup X} (hMb : M ≤ centralizer ({b} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) : E ≤ normalizer (M : Set X) := by
  intro e he
  by_cases he1 : e = 1
  · rw [he1]
    exact one_mem _
  have heo : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.mul_self_eq he) he1
  obtain ⟨-, h3⟩ := (GrSLit.GrS5.solomon_involutions hSol heo hb (hbE e he)).2 M hMb hMc
  refine (h3 ?_).1
  refine h.not_commutator_le_target' hb hab hbJ hJb hbE hMb hMc hT fun d hd => ?_
  obtain ⟨hdF, hdb⟩ := mem_inf.mp hd
  exact mem_inf.mpr ⟨wCore_le he he1 (mem_inf.mp hdF).2, hdb⟩

theorem Config.config_of_target (hSol : GrSLit.SolomonCommutingCoreInput) {a : X}
    {J E : Subgroup X} (h : Config a J E) {b : X} (hb : orderOf b = 2) (hab : a * b = b * a)
    (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {M : Subgroup X} (hMb : M ≤ centralizer ({b} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hT : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a)
    (h7 : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7))) : Config b M E := by
  obtain ⟨e7⟩ := h7
  have hs : IsSimpleGroup (M ⧸ pPrimeCore 2 M) :=
    @MulEquiv.isSimpleGroup _ _ _ _
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))) e7
  have hEb : E ≤ centralizer ({b} : Set X) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hbE e he)
  have hEN := h.le_normalizer_target hSol hb hab hbJ hJb hbE hMb hMc hT
  obtain ⟨e₀, he₀E, he₀1, he₀⟩ := h.exists_involution
  have hD : centralizer ({b} : Set X) ⊓ wCore E ≤ normalizer (M : Set X) := by
    have h1 := ((GrSLit.GrS5.solomon_involutions hSol he₀ hb (hbE e₀ he₀E)).2 M hMb hMc).1
    exact fun d hd => h1 (mem_inf.mpr ⟨wCore_le he₀E he₀1 (mem_inf.mp hd).2, (mem_inf.mp hd).1⟩)
  have hnot : ¬ ⁅M, centralizer ({b} : Set X) ⊓ wCore E⁆ ≤ (pPrimeCore 2 M).map M.subtype :=
    h.not_commutator_le_target' hb hab hbJ hJb hbE hMb hMc hT fun d hd =>
      mem_inf.mpr ⟨(mem_inf.mp hd).2, (mem_inf.mp (mem_inf.mp hd).1).2⟩
  exact ⟨hb, hMb, hMc, ⟨e7⟩, le_inf hEb hEN, h.four,
    commutator_eq_of_simple hMb hMc hs hD hnot⟩

end CFSG.ComponentClassification.GSThmB.CorC
