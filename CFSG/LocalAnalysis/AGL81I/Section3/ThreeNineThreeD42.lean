module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42Over
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeM11
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieF
public import Certificates.Certificate1322030
public import Certificates.Certificate1322031
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.D42Over.Native
open CFSG.LocalAnalysis.AGL81I.Section3.D42Over
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem D42Over.exists_conj_kA_kB
    (hG : Nat.card trialityGroup8 = 211341312) (t : trialityGroup8) (ht : orderOf t = 3) :
    ∃ g : trialityGroup8, g * t * g⁻¹ = wordElt kAW ∨ g * t * g⁻¹ = wordElt kBW := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht3 : t ^ 3 = 1 := ht ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hG (Subgroup.zpowers t) (isElemAbelian_zpowers ht3)
  have hmem := hg (g * t * g⁻¹) ⟨t, Subgroup.mem_zpowers t, rfl⟩
  obtain ⟨a, ha, hga⟩ := exists_sylowElems_eq _ hmem
  have hchk : d42ConjCheck = true := Certificates.certificate1322031
  unfold d42ConjCheck at hchk
  have hx := List.all_eq_true.mp hchk a ha
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true, List.mem_map] at hx
  have hmat : ∀ u : trialityGroup8, ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      ((wordGL [] : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) → u = 1 := by
    intro u hu
    exact Subtype.ext (Units.ext (hu.trans (by simp [wordGL])))
  rcases hx with (h1 | h3) | ⟨_, ⟨w, -, rfl⟩, hw⟩
  · exfalso
    apply ht1
    have : g * t * g⁻¹ = 1 := hmat _ (by rw [hga, h1, coe_wordGL]; rfl)
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, ‹g * t * g⁻¹ = 1›]
    group
  · exfalso
    have e3 : (g * t * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, ht3, mul_one, mul_inv_cancel]
    have heq : mulArr a (mulArr a a) = oneArr := by
      apply eq_of_toMat_eq (size_mulArr _ _) size_oneArr
      rw [toMat_mulArr, toMat_mulArr, ← hga, oneArr, toMat_ofMat]
      have := congrArg
        (fun u : trialityGroup8 => ((u : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8)) e3
      simpa [pow_succ, mul_assoc] using this
    simp [heq] at h3
  · refine ⟨wordElt w * g, ?_⟩
    have hconj : (((wordElt w * g * t * (wordElt w * g)⁻¹ : trialityGroup8) : GL (Fin 8) GF8) :
        Matrix (Fin 8) (Fin 8) GF8) =
        toMat (mulArr (mulArr (wordArr w) a) (wordArr w.reverse)) := by
      rw [toMat_mulArr, toMat_mulArr, ← hga, ← coe_wordGL, ← coe_wordGL, ← wordGL_reverse]
      simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      simp only [wordElt, mul_assoc]
    rcases hw with hw | hw
    · left
      exact Subtype.ext (Units.ext (by rw [hconj, hw, ← coe_wordGL]; rfl))
    · right
      exact Subtype.ext (Units.ext (by rw [hconj, hw, ← coe_wordGL]; rfl))

theorem D42Over.card_eq_of_conj_mem {G : Type*} [Group G] [Finite G] (k : G) (H : Subgroup G)
    (hC : Subgroup.centralizer {k} ≤ H)
    (hH : ∀ h ∈ H, h * k * h⁻¹ = k ∨ h * k * h⁻¹ = k * k) :
    ∃ m, (m = 1 ∨ m = 2) ∧ Nat.card H = m * Nat.card (Subgroup.centralizer ({k} : Set G)) := by
  classical
  set C := Subgroup.centralizer ({k} : Set G)
  set C' := C.subgroupOf H
  have hcomm : ∀ a b : G, a * k * a⁻¹ = b * k * b⁻¹ → a⁻¹ * b ∈ C := by
    intro a b hab
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : k = a⁻¹ * (b * k * b⁻¹) * a := by rw [← hab]; group
    calc a⁻¹ * b * k = a⁻¹ * (b * k * b⁻¹) * a * (a⁻¹ * b) := by group
      _ = k * (a⁻¹ * b) := by rw [← this]
  let f : H ⧸ C' → Bool := Quotient.lift (fun h : H => decide ((h : G) * k * (h : G)⁻¹ = k))
    (by
      intro a b hab
      have hab2 := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab2
      have hab' : ((a : G)⁻¹ * b) * k = k * ((a : G)⁻¹ * b) :=
        Subgroup.mem_centralizer_singleton_iff.mp (by simpa using hab2)
      have e : (b : G) * k * (b : G)⁻¹ = (a : G) * k * (a : G)⁻¹ := by
        calc (b : G) * k * (b : G)⁻¹
            = a * (((a : G)⁻¹ * b) * k) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by group
          _ = a * (k * ((a : G)⁻¹ * b)) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by rw [hab']
          _ = a * k * (a : G)⁻¹ := by group
      simp only [e])
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hfa : f a = decide ((a : G) * k * (a : G)⁻¹ = k) := rfl
    have hfb : f b = decide ((b : G) * k * (b : G)⁻¹ = k) := rfl
    rw [hfa, hfb] at hxy
    apply hcomm
    by_cases ha : (a : G) * k * (a : G)⁻¹ = k
    · have hb : (b : G) * k * (b : G)⁻¹ = k := by simpa [ha] using hxy.symm
      rw [ha, hb]
    · have hb : ¬ (b : G) * k * (b : G)⁻¹ = k := by simpa [ha] using hxy.symm
      rw [(hH a a.2).resolve_left ha, (hH b b.2).resolve_left hb]
  have hidx : C'.index ≤ 2 := by
    have := Nat.card_le_card_of_injective f hinj
    simpa [Subgroup.index] using this
  have hC' : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
  have hmul := C'.card_mul_index
  rw [hC'] at hmul
  have hpos : 0 < C'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine ⟨C'.index, by omega, ?_⟩
  rw [← hmul, mul_comm]

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_D42
    (h : ThreeNineHyp K E D X₁ 3 d) (hK : ChevalleyExceptionalModel ↥K .trialityD4 2 1) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have hL : LieModel ↥K .trialityD4 0 2 1 :=
    CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, hK⟩
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel _ hL
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  let φ : ↥K ≃* trialityGroup8 := e2.trans e3.symm
  have hcardK : Nat.card ↥K = 211341312 :=
    CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_trialityD4 hL
  have hG : Nat.card trialityGroup8 = 211341312 := by
    rw [← Nat.card_congr φ.toEquiv, hcardK]
  have hZ : Subgroup.center ↥K = ⊥ := CFSG.Quasithin.H23P4.center_eq_bot_of_is3D4 hK
  have hOut : Nat.card (Outer ↥K) = 3 := CFSG.Quasithin.H23Out.card_outer_is3D4 hK
  have hdOut : ¬ d ∣ Nat.card (Outer ↥K) := by
    rw [hOut]
    intro hd
    exact h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp hd)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hdOut
  obtain ⟨hdY, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hQK : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup X) ⊓ K) K :=
    hQtop.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  have hQY : ((Q : Subgroup X) ⊓ K).subgroupOf K ≤ X₁.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.normQ Q Q.isPGroup' hEQ
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (Subgroup.mem_inf.mp hx).1,
        le_sup_left (a := K) (Subgroup.mem_inf.mp hx).2⟩)
  have h81 : (3 : ℕ) ^ (211341312 : ℕ).factorization 3 = 81 :=
    (pow_eq_pow_factorization_of_eq (a := 4) (k := 2609152) Nat.prime_three (by norm_num)
      (by norm_num)).symm
  have h81Y : 81 ∣ Nat.card (X₁.subgroupOf K) := by
    have := Subgroup.card_dvd_of_le hQY
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hQK.card_eq, hcardK,
      h81] at this
  let f : E →* Outer ↥K := (QuotientGroup.mk' _).comp (MulAut.conjNormal.comp E.subtype)
  have hninj : ¬ Function.Injective f := fun hinj => by
    have := Nat.card_le_card_of_injective f hinj
    rw [h.card_E, hOut] at this
    norm_num at this
  rw [injective_iff_map_eq_one] at hninj
  push Not at hninj
  obtain ⟨e, hef, he1⟩ := hninj
  have he1' : (e : X) ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  have hin : MulAut.conjNormal (e : X) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    (QuotientGroup.eq_one_iff _).mp hef
  obtain ⟨k, hk⟩ := hin
  have hconj : ∀ c : ↥K, (e : X) * c * (e : X)⁻¹ = ((k * c * k⁻¹ : ↥K) : X) := by
    intro c
    have := congrArg (fun α : MulAut ↥K => ((α c : ↥K) : X)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at this
    exact this.symm
  have hCY : ∀ c : ↥K, c * k = k * c → c ∈ X₁.subgroupOf K := by
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    refine h.mem_of_commute_E e.2 he1' (le_sup_left (a := K) c.2) ?_
    have := hconj c
    rw [show k * c * k⁻¹ = c by rw [← hc, mul_inv_cancel_right]] at this
    calc (e : X) * c = (e : X) * c * (e : X)⁻¹ * e := by group
      _ = c * e := by rw [this]
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply he1'
    refine h.E_faithful e.2 fun c hc => ?_
    have := hconj ⟨c, hc⟩
    simp only [one_mul, inv_one, mul_one] at this
    calc (e : X) * c = (e : X) * c * (e : X)⁻¹ * e := by group
      _ = c * e := by rw [this]
  have hk3 : k ^ 3 = 1 := by
    have he3 : (e : X) ^ 3 = 1 := h.elem.2 _ e.2
    have hc3 : MulAut.conj (k ^ 3) = 1 := by
      rw [map_pow, hk, ← map_pow, he3, map_one]
    have hmem : k ^ 3 ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro c
      have := congrArg (fun α : MulAut ↥K => α c) hc3
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc c * k ^ 3 = k ^ 3 * c * (k ^ 3)⁻¹ * k ^ 3 := by rw [this]
        _ = k ^ 3 * c := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hto : orderOf (φ k) = 3 := by rw [MulEquiv.orderOf_eq, hko]
  obtain ⟨g, hg⟩ := D42Over.exists_conj_kA_kB hG (φ k) hto
  let ψ : ↥K ≃* trialityGroup8 := φ.trans (MulAut.conj g)
  have hψk : ψ k = g * φ k * g⁻¹ := rfl
  set Y := X₁.subgroupOf K
  have hYK : Y ≠ ⊤ := by
    intro hY
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := hY ▸ Subgroup.mem_top _
    exact this
  have key : ∀ (k₀ : trialityGroup8) (n₀ : ℕ), (Subgroup.centralizer {k₀}).index = n₀ →
      D42Over.OvergroupConj k₀ → ψ k = k₀ →
      ∃ m, (m = 1 ∨ m = 2) ∧ Nat.card Y * n₀ = m * 211341312 := by
    intro k₀ n₀ hidx hov hck
    set H := Y.map ψ.toMonoidHom
    have hCH : ∀ x : trialityGroup8, x * k₀ = k₀ * x → x ∈ H := by
      intro x hx
      refine ⟨ψ.symm x, hCY _ ?_, by simp⟩
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hck]
      exact hx
    have hCH' : Subgroup.centralizer {k₀} ≤ H :=
      fun x hx => hCH x (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rcases hov H hCH' with hH | hH
    · obtain ⟨m, hm, hcard⟩ := D42Over.card_eq_of_conj_mem k₀ H hCH' hH
      refine ⟨m, hm, ?_⟩
      have hHY : Nat.card H = Nat.card Y :=
        Nat.card_congr (Subgroup.equivMapOfInjective Y _ ψ.injective).toEquiv.symm
      have hCm := (Subgroup.centralizer ({k₀} : Set trialityGroup8)).card_mul_index
      rw [hidx, hG] at hCm
      rw [← hHY, hcard, mul_assoc, hCm]
    · exfalso
      apply hYK
      rw [eq_top_iff]
      intro y _
      obtain ⟨z, hz, hzy⟩ := (hH ▸ Subgroup.mem_top (ψ y) : ψ y ∈ H)
      have : z = y := ψ.injective hzy
      exact this ▸ hz
  have hF : D42Over.D42ClsFacts := Certificates.certificate1322030
  rcases hg with hg | hg
  · obtain ⟨m, hm, hY⟩ := key D42Over.kA 139776 hF.index_kA hF.overgroup_kA
      (by rw [hψk, hg]; rfl)
    have hYc : Nat.card Y = m * 1512 := by omega
    rw [hYc] at h81Y
    rcases hm with rfl | rfl <;> norm_num at h81Y
  · obtain ⟨m, hm, hY⟩ := key D42Over.kB 326144 hF.index_kB hF.overgroup_kB
      (by rw [hψk, hg]; rfl)
    have hYc : Nat.card Y ∣ 2 ^ 4 * 3 ^ 4 := by
      rcases hm with rfl | rfl
      · exact ⟨2, by omega⟩
      · exact ⟨1, by omega⟩
    have hd := hdY.trans hYc
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hd with h2 | h3
    · exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
        (h.d_prime.dvd_of_dvd_pow h2))
    · exact h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
        (h.d_prime.dvd_of_dvd_pow h3))

theorem threeNineThreeD42_holds :
    ThreeNineThreeD42 :=
  fun _ _ _ _ _ _ _ _ h hK => false_of_threeNineHyp_D42 h hK

end CFSG.LocalAnalysis.AGL81I.Section3
