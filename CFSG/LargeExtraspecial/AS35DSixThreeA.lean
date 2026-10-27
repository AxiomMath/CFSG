module

public import CFSG.LargeExtraspecial.AS35DFourFiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem mem_M_of_commute_cqx {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z)
    (hnc : ¬ IsConj S.z t) {h : G}
    (hh : ∀ y ∈ S.QG, y * t = t * y → y * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * y) :
    h ∈ S.M := by
  by_contra hhM
  exact hnc ((S.isConj_iff_exists_le_conj ht ht1 htz).mpr ⟨h, hhM, hh⟩)

theorem le_M_of_isPGroup_of_cqx_le {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z)
    (hnc : ¬ IsConj S.z t) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hPT : S.QG ⊓ centralizer ({t} : Set G) ≤ T) : T ≤ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hTM
  set T₀ := (T ⊓ S.M).subgroupOf T with hT₀
  have hlt : T₀ < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hTM fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ T₀ := by rw [h]; exact mem_top _
    rw [hT₀, mem_subgroupOf] at this
    exact (mem_inf.mp this).2
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := T) T₀ hlt
  obtain ⟨x, hxN, hxT₀⟩ := Set.exists_of_ssubset hnorm
  have hxM : (x : G) ∈ S.M := by
    refine S.mem_M_of_commute_cqx ht ht1 htz hnc fun y hyQ hyt => ?_
    have hyT : y ∈ T := hPT (mem_inf.mpr ⟨hyQ, mem_centralizer_singleton_iff.mpr hyt⟩)
    have hyM : y ∈ S.M := S.mem_M_iff.mpr (S.z_comm_QG hyQ)
    have h1 : x⁻¹ * ⟨y, hyT⟩ * x ∈ T₀ := by
      have := (mem_normalizer_iff.mp (inv_mem hxN) ⟨y, hyT⟩).mp
        (by rw [hT₀, mem_subgroupOf]; exact mem_inf.mpr ⟨hyT, hyM⟩)
      rwa [inv_inv] at this
    rw [hT₀, mem_subgroupOf] at h1
    have h2 := S.mem_M_iff.mp (mem_inf.mp h1).2
    change (x : G)⁻¹ * y * x * S.z = S.z * ((x : G)⁻¹ * y * x) at h2
    calc y * ((x : G) * S.z * (x : G)⁻¹) = x * ((x : G)⁻¹ * y * x * S.z) * (x : G)⁻¹ := by
          group
      _ = x * (S.z * ((x : G)⁻¹ * y * x)) * (x : G)⁻¹ := by rw [h2]
      _ = (x : G) * S.z * (x : G)⁻¹ * y := by group
  have hx : x ∈ T₀ := by
    rw [hT₀, mem_subgroupOf]
    exact mem_inf.mpr ⟨x.2, hxM⟩
  exact hxT₀ hx

abbrev Esub (u v : G) : Subgroup G :=
  S.QG ⊓ centralizer ({u} : Set G) ⊓ centralizer ({v} : Set G)

omit [Finite G] in
theorem mem_Esub {u v y : G} :
    y ∈ S.Esub u v ↔ y ∈ S.QG ∧ y * u = u * y ∧ y * v = v * y := by
  simp only [Esub, mem_inf, mem_centralizer_singleton_iff, and_assoc]

theorem exists_mul_mem_Esub {u v : G} (hu : u ∈ S.QG) (hv : v ∈ S.QG) (huv : u * v ≠ v * u)
    {q : G} (hq : q ∈ S.QG) :
    ∃ c ∈ ({1, u} : Set G), ∃ d ∈ ({1, v} : Set G), q * c * d ∈ S.Esub u v ∧
      (q * u = u * q → d = 1) := by
  have hpuv : polar S.q (S.cl u) (S.cl v) = 1 := (S.polar_cl_eq_one_iff hu hv).mpr huv
  have hcomm : ∀ a ∈ S.QG, ∀ b ∈ S.QG, a * b = b * a ↔ polar S.q (S.cl a) (S.cl b) = 0 :=
    fun a ha b hb => (S.polar_cl_eq_zero_iff ha hb).symm
  obtain ⟨c, hc, hq₁⟩ : ∃ c ∈ ({1, u} : Set G), q * c * v = v * (q * c) := by
    by_cases h : q * v = v * q
    · exact ⟨1, Or.inl rfl, by rw [mul_one]; exact h⟩
    · refine ⟨u, Or.inr rfl, ?_⟩
      rw [hcomm _ (S.QG.mul_mem hq hu) v hv, S.cl_mul hq hu, polar_add_left, hpuv,
        (S.polar_cl_eq_one_iff hq hv).mpr h]
      decide
  have hcQ : c ∈ S.QG := by
    rcases hc with rfl | rfl
    · exact S.QG.one_mem
    · exact hu
  have hq₁Q : q * c ∈ S.QG := S.QG.mul_mem hq hcQ
  have hcu : c * u = u * c := by
    rcases hc with rfl | rfl
    · group
    · rfl
  by_cases h : q * c * u = u * (q * c)
  · refine ⟨c, hc, 1, Or.inl rfl, ?_, fun _ => rfl⟩
    rw [mul_one]
    exact (S.mem_Esub).mpr ⟨hq₁Q, h, hq₁⟩
  · refine ⟨c, hc, v, Or.inr rfl, (S.mem_Esub).mpr ⟨S.QG.mul_mem hq₁Q hv, ?_, ?_⟩, ?_⟩
    · rw [hcomm _ (S.QG.mul_mem hq₁Q hv) u hu, S.cl_mul hq₁Q hv, polar_add_left,
        polar_comm (⇑S.q) (S.cl v) (S.cl u), hpuv, (S.polar_cl_eq_one_iff hq₁Q hu).mpr h]
      decide
    · calc q * c * v * v = v * (q * c) * v := by rw [hq₁]
        _ = v * (q * c * v) := by group
    · intro hqu
      exfalso
      apply h
      calc q * c * u = q * (u * c) := by rw [mul_assoc, hcu]
        _ = u * (q * c) := by rw [← mul_assoc, hqu, mul_assoc]

theorem eq_one_or_z_of_mem_Esub {u v : G} (hu : u ∈ S.QG) (hv : v ∈ S.QG)
    (huv : u * v ≠ v * u) {x : G} (hx : x ∈ S.Esub u v)
    (hxE : ∀ y ∈ S.Esub u v, x * y = y * x) : x = 1 ∨ x = S.z := by
  obtain ⟨hxQ, hxu, hxv⟩ := (S.mem_Esub).mp hx
  refine S.eq_one_or_z_of_commute hxQ fun q hq => ?_
  obtain ⟨c, hc, d, hd, he, -⟩ := S.exists_mul_mem_Esub hu hv huv hq
  have hxc : x * c = c * x := by
    rcases hc with rfl | rfl
    · group
    · exact hxu
  have hxd : x * d = d * x := by
    rcases hd with rfl | rfl
    · group
    · exact hxv
  have h1 : Commute x (q * c * d) := hxE _ he
  have hq' : q = q * c * d * d⁻¹ * c⁻¹ := by group
  rw [hq']
  exact (Commute.mul_right (Commute.mul_right h1 (Commute.inv_right hxd))
    (Commute.inv_right hxc)).eq

theorem two_pow_le_card_Esub (u v : G) (hu : u ∈ S.QG) (hv : v ∈ S.QG) :
    2 ^ (2 * S.width - 1) ≤ Nat.card (S.Esub u v) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set Wu := LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ S.cl u) with hWu
  set Wv := LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ S.cl v) with hWv
  have hE : S.Esub u v = S.clPre (Wu ⊓ Wv) := by
    ext y
    rw [mem_Esub, S.mem_clPre, Submodule.mem_inf]
    have h1 := S.centralizer_singleton_inf_QG hu
    have h2 := S.centralizer_singleton_inf_QG hv
    constructor
    · rintro ⟨hy, hyu, hyv⟩
      have a1 : y ∈ S.QG ⊓ centralizer ({u} : Set G) :=
        mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyu⟩
      have a2 : y ∈ S.QG ⊓ centralizer ({v} : Set G) :=
        mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyv⟩
      rw [h1] at a1
      rw [h2] at a2
      exact ⟨hy, (S.mem_clPre.mp a1).2, (S.mem_clPre.mp a2).2⟩
    · rintro ⟨hy, hyu, hyv⟩
      have a1 : y ∈ S.clPre Wu := S.mem_clPre.mpr ⟨hy, hyu⟩
      have a2 : y ∈ S.clPre Wv := S.mem_clPre.mpr ⟨hy, hyv⟩
      rw [← h1] at a1
      rw [← h2] at a2
      exact ⟨hy, mem_centralizer_singleton_iff.mp (mem_inf.mp a1).2,
        mem_centralizer_singleton_iff.mp (mem_inf.mp a2).2⟩
  rw [hE, S.card_clPre, S.card_submodule]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq Wu Wv
  have hle : finrank (ZMod 2) ↥(Wu ⊔ Wv) ≤ 2 * S.width := by
    rw [← S.finrank_Qt_eq_two_mul_width]
    exact Submodule.finrank_le _
  have hdu : 2 * S.width - 1 ≤ finrank (ZMod 2) Wu := by
    rw [hWu, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
      S.finrank_Qt_eq_two_mul_width]
    have := finrank_span_le_card (R := ZMod 2) ({S.cl u} : Set S.Qt)
    simp only [Set.toFinset_singleton, Finset.card_singleton] at this
    omega
  have hdv : 2 * S.width - 1 ≤ finrank (ZMod 2) Wv := by
    rw [hWv, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
      S.finrank_Qt_eq_two_mul_width]
    have := finrank_span_le_card (R := ZMod 2) ({S.cl v} : Set S.Qt)
    simp only [Set.toFinset_singleton, Finset.card_singleton] at this
    omega
  have h1 : 2 * S.width - 2 ≤ finrank (ZMod 2) ↥(Wu ⊓ Wv) := by omega
  calc 2 ^ (2 * S.width - 1) ≤ 2 ^ (finrank (ZMod 2) ↥(Wu ⊓ Wv) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ finrank (ZMod 2) ↥(Wu ⊓ Wv) := by ring

theorem exists_not_commute_Esub_of_two_le (hn : 2 ≤ S.width) {u v : G} (hu : u ∈ S.QG)
    (hv : v ∈ S.QG) (huv : u * v ≠ v * u) :
    ∃ a ∈ S.Esub u v, ∃ b ∈ S.Esub u v, a * b ≠ b * a := by
  by_contra! h
  set E := S.Esub u v with hEdef
  set s : Set G := insert u (E : Set G) with hs
  have hss : s ⊆ centralizer s := by
    have huE : ∀ e ∈ E, e * u = u * e := fun e he => ((S.mem_Esub).mp he).2.1
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact huE b hb
    · exact (huE a ha).symm
    · exact h b hb a ha
  set A := closure s with hA
  have hA1 : A ≤ centralizer s := (closure_le _).mpr hss
  have hA2 : A ≤ centralizer (A : Set G) := by
    rw [hA, closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact ((mem_centralizer_iff.mp (hA1 hb)) a ha).symm
  have hAQ : A ≤ S.QG := by
    rw [hA, closure_le]
    rintro a (rfl | ha)
    · exact hu
    · exact (inf_le_left.trans inf_le_left : E ≤ S.QG) ha
  have hcard := S.card_le_of_commute hAQ fun x hx y hy =>
    (mem_centralizer_iff.mp (hA2 hy)) x hx
  have hEA : E ≤ A := fun e he => subset_closure (Set.mem_insert_of_mem _ he)
  have huA : u ∈ A := subset_closure (Set.mem_insert _ _)
  have huE : u ∉ E := fun hu' => huv ((S.mem_Esub).mp hu').2.2
  have hlt : Nat.card E < Nat.card A := by
    rcases (Nat.card_le_card_of_injective _ (inclusion_injective hEA)).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Subgroup.eq_of_le_of_card_ge hEA heq.symm.le ▸ huA) huE
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEA
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp [hk] at hlt
    · simp [hk] at hlt
    · omega
  have h2 := S.two_pow_le_card_Esub u v hu hv
  have h3 : 2 ^ (2 * S.width - 1) * 2 ≤ 2 ^ (S.width + 1) := by
    calc 2 ^ (2 * S.width - 1) * 2 ≤ Nat.card E * k := Nat.mul_le_mul h2 hk2
      _ = Nat.card A := hk.symm
      _ ≤ _ := hcard
  rw [← pow_succ] at h3
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

theorem isExtraspecialPGroup_Esub (hn : 2 ≤ S.width) {u v : G} (hu : u ∈ S.QG)
    (hv : v ∈ S.QG) (huv : u * v ≠ v * u) : IsExtraspecialPGroup 2 (S.Esub u v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := S.Esub u v with hEdef
  have hEQ : E ≤ S.QG := inf_le_left.trans inf_le_left
  have hE2 : IsPGroup 2 E := S.isPGroup_QG.to_le hEQ
  have : Fact (IsPGroup 2 E) := ⟨hE2⟩
  have hzE : S.z ∈ E :=
    (S.mem_Esub).mpr ⟨S.z_mem_QG, (S.z_comm_QG hu).symm, (S.z_comm_QG hv).symm⟩
  set z' : E := ⟨S.z, hzE⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact S.orderOf_z
  have hmemZ : ∀ x : E, x ∈ zpowers z' ↔ (x : G) = 1 ∨ (x : G) = S.z := by
    intro x
    rw [mem_zpowers_iff_of_mul_self (by
      apply Subtype.ext
      change S.z * S.z = 1
      exact S.z_mul_z)]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have hcenter : center E = zpowers z' := by
    ext x
    rw [mem_center_iff, hmemZ]
    constructor
    · intro hx
      exact S.eq_one_or_z_of_mem_Esub hu hv huv x.2 fun y hy =>
        (congrArg Subtype.val (hx ⟨y, hy⟩)).symm
    · rintro (h | h) g
      · rw [show x = 1 from Subtype.ext h]
        group
      · apply Subtype.ext
        change (g : G) * x = x * g
        rw [h]
        exact S.z_comm_QG (hEQ g.2)
  have hcomm_le : _root_.commutator E ≤ zpowers z' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [hmemZ]
    exact S.commutator_eq_one_or_z (hEQ x.2) (hEQ y.2)
  have hcomm : _root_.commutator E = zpowers z' := by
    refine le_antisymm hcomm_le ?_
    obtain ⟨a, ha, b, hb, hab⟩ := S.exists_not_commute_Esub_of_two_le hn hu hv huv
    have h1 : (⁅(⟨a, ha⟩ : E), ⟨b, hb⟩⁆ : E) = z' := by
      apply Subtype.ext
      change a * b * a⁻¹ * b⁻¹ = S.z
      rcases S.commutator_eq_one_or_z (hEQ ha) (hEQ hb) with h | h
      · exfalso
        apply hab
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [h, one_mul]
      · exact h
    rw [zpowers_le, ← h1, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  have hfr : frattini E = zpowers z' := by
    refine le_antisymm ?_ (hcomm ▸ CFSG.commutator_le_frattini_of_isPGroup (R := E) (p := 2))
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcomm_le hx
    · rw [SetLike.mem_coe, hmemZ]
      have := S.sq_eq_one_or_z (hEQ y.2)
      rwa [← Subgroup.coe_pow] at this
  refine ⟨hE2, ?_, ?_, ?_⟩
  · rw [hcomm, hcenter]
  · rw [hfr, hcenter]
  · rw [hcenter, Nat.card_zpowers, hz'2]

theorem sup_Esub {u v : G} (hu : u ∈ S.QG) (hv : v ∈ S.QG) (huv : u * v ≠ v * u) :
    zpowers u ⊔ S.Esub u v = S.QG ⊓ centralizer ({u} : Set G) := by
  refine le_antisymm (sup_le ?_ ?_) fun y hy => ?_
  · rw [zpowers_le]
    exact mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr rfl⟩
  · exact inf_le_left
  · obtain ⟨hyQ, hyu⟩ := mem_inf.mp hy
    obtain ⟨c, hc, d, hd, he, hd1⟩ := S.exists_mul_mem_Esub hu hv huv hyQ
    rw [hd1 (mem_centralizer_singleton_iff.mp hyu), mul_one] at he
    have hc' : c⁻¹ ∈ zpowers u := by
      rcases hc with h | h
      · rw [h]
        exact inv_mem (one_mem _)
      · rw [h]
        exact inv_mem (mem_zpowers u)
    have := mul_mem (mem_sup_right he : y * c ∈ zpowers u ⊔ S.Esub u v)
      (mem_sup_left hc' : c⁻¹ ∈ zpowers u ⊔ S.Esub u v)
    rwa [mul_inv_cancel_right] at this

omit [Finite G] in
theorem zpowers_inf_Esub {u v : G} (huu : u * u = 1) (huv : u * v ≠ v * u) :
    zpowers u ⊓ S.Esub u v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxu, hxE⟩ := mem_inf.mp hx
  rw [mem_zpowers_iff_of_mul_self huu] at hxu
  rcases hxu with rfl | rfl
  · exact one_mem _
  · exact absurd ((S.mem_Esub).mp hxE).2.2 huv

section CaseOne

variable {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
  (hk : Nat.card S.QG = 2 ^ finrank (ZMod 2) (commSpace (S.rhoL hxM)) *
    Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)))
include hk

theorem cqxSub_eq_fixSpace (hxx : x * x = 1) : S.cqxSub x = fixSpace (S.rhoL hxM) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h1 := S.card_QG_eq_mul hxM
  rw [h1] at hk
  have hpos : 0 < Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := Nat.card_pos
  have h2 := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos hk)
  have h3 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
  rw [S.finrank_Qt_eq_two_mul_width] at h3
  have h4 : finrank (ZMod 2) (S.cqxSub x) ≤ 2 * S.width := by
    rw [← S.finrank_Qt_eq_two_mul_width]
    exact Submodule.finrank_le _
  refine Submodule.eq_of_le_of_finrank_eq (S.cqxSub_le_fixSpace hxM) ?_
  have := S.rhoL_mul_self hxM hxx
  omega

theorem cqx_eq_clPre_fixSpace (hxx : x * x = 1) :
    S.QG ⊓ centralizer ({x} : Set G) = S.clPre (fixSpace (S.rhoL hxM)) := by
  rw [← S.cqxSub_eq_fixSpace hxM hk hxx, S.clPre_cqxSub hxM]

theorem center_cqx_eq_clPre_commSpace (hxx : x * x = 1) :
    S.QG ⊓ centralizer ({x} : Set G) ⊓
        centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) =
      S.clPre (commSpace (S.rhoL hxM)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hσ2 := S.rhoL_mul_self hxM hxx
  have hCU := fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.rhoL_mem hxM) hσ2
  have hCperp : LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (S.rhoL hxM)) =
      commSpace (S.rhoL hxM) := by
    rw [hCU, LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]
  rw [S.center_cqx_eq hxM, S.cqxSub_eq_fixSpace hxM hk hxx, hCperp,
    inf_eq_right.mpr (commSpace_le_fixSpace hσ2)]

end CaseOne

end Setting

end CFSG.LargeExtraspecial
