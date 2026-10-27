module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {K A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ A) :
    ∃ k ∈ K, ∃ a ∈ A, x = k * a := by
  let M : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ a ∈ A, x = k * a}
      one_mem' := ⟨1, K.one_mem, 1, A.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, a, ha, rfl⟩ ⟨k', hk', a', ha', rfl⟩
        refine ⟨k * (a * k' * a⁻¹), K.mul_mem hk ?_, a * a', A.mul_mem ha ha', by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA ha) k').1 hk'
        exact this
      inv_mem' := by
        rintro _ ⟨k, hk, a, ha, rfl⟩
        refine ⟨a⁻¹ * k⁻¹ * a, ?_, a⁻¹, A.inv_mem ha, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha)) k⁻¹).1 (K.inv_mem hk)
        simpa [mul_assoc] using this }
  have : K ⊔ A ≤ M :=
    sup_le (fun k hk => ⟨k, hk, 1, A.one_mem, by simp⟩) (fun a ha => ⟨1, K.one_mem, a, ha, by simp⟩)
  exact this hx

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem le_normalizer_inf_of_le {M A C : Subgroup G}
    (hA : M ≤ Subgroup.normalizer (A : Set G)) (hC : M ≤ Subgroup.normalizer (C : Set G)) :
    M ≤ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := Subgroup.mem_normalizer_iff.1 (hA hg) h
  have h2 := Subgroup.mem_normalizer_iff.1 (hC hg) h
  exact ⟨fun hh => ⟨h1.1 hh.1, h2.1 hh.2⟩, fun hh => ⟨h1.2 hh.1, h2.2 hh.2⟩⟩

omit [Finite G] in
theorem y_le_normalizer_I {B T I : Subgroup G} (h : Setup710 B T I) :
    yOf B T I ≤ Subgroup.normalizer (I : Set G) :=
  sup_le (sup_le Subgroup.le_normalizer h.tnI) h.bnI

omit [Finite G] in
theorem I_le_yOf (B T I : Subgroup G) : I ≤ yOf B T I := le_sup_left.trans le_sup_left

omit [Finite G] in
theorem T_le_yOf (B T I : Subgroup G) : T ≤ yOf B T I := le_sup_right.trans le_sup_left

omit [Finite G] in
theorem B_le_yOf (B T I : Subgroup G) : B ≤ yOf B T I := le_sup_right

omit [Finite G] in
theorem pOf_le_yOf (B T I : Subgroup G) : pOf B T I ≤ yOf B T I :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem y_le_normalizer_pOf (B T I : Subgroup G) :
    yOf B T I ≤ Subgroup.normalizer (pOf B T I : Set G) :=
  le_normalizer_glaPPrimeCoreOf 3 _

theorem not_three_dvd_card_pOf (B T I : Subgroup G) : ¬ 3 ∣ Nat.card ↥(pOf B T I) :=
  not_dvd_card_glaPPrimeCoreOf Nat.prime_three _

omit [Finite G] in
theorem isSubnormal_I_yOf {B T I : Subgroup G} (h : Setup710 B T I) :
    IsSubnormal I (yOf B T I) :=
  IsSubnormal.step (I_le_yOf B T I)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (I_le_yOf B T I)).2 (y_le_normalizer_I h))
    (IsSubnormal.refl _)

theorem inf_pOf_eq {B T I : Subgroup G} (h : Setup710 B T I) :
    I ⊓ pOf B T I = GLAPPrimeCoreOf 3 I :=
  glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three (isSubnormal_I_yOf h)

omit [Finite G] in
theorem exists_mul_of_mem_yOf {B T I : Subgroup G} (h : Setup710 B T I) {y : G}
    (hy : y ∈ yOf B T I) : ∃ i ∈ I, ∃ t ∈ T, ∃ b ∈ B, y = i * t * b := by
  have hTB : T ⊔ B ≤ Subgroup.normalizer (I : Set G) := sup_le h.tnI h.bnI
  have hy' : y ∈ I ⊔ (T ⊔ B) := by
    rw [yOf, sup_assoc] at hy
    exact hy
  obtain ⟨i, hi, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hTB hy'
  obtain ⟨t, ht, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer h.bnT ha
  exact ⟨i, hi, t, ht, b, hb, by rw [mul_assoc]⟩

theorem factorization_card_le {B T I : Subgroup G} (h : Setup710 B T I) :
    (Nat.card ↥I).factorization 3 ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥I))
  have hQ := Sylow.card_eq_multiplicity Q
  have hle := h.ord3 (Q.map I.subtype) (by
    rintro _ ⟨x, _, rfl⟩; exact x.2) (Q.isPGroup'.map I.subtype)
  rw [Subgroup.card_map_of_injective I.subtype_injective, hQ] at hle
  by_contra hlt
  replace hlt := not_le.mp hlt
  have : 3 ^ 3 ≤ 3 ^ (Nat.card ↥I).factorization 3 := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem b_sylow_y {B T I : Subgroup G} (h : Setup710 B T I) :
    ¬ 3 ∣ B.relIndex (yOf B T I) := by
  intro hdvd
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := T ⊔ B with hH
  have hHN : H ≤ Subgroup.normalizer (I : Set G) := sup_le h.tnI h.bnI
  have hY : yOf B T I = H ⊔ I := by rw [yOf, sup_assoc, sup_comm]
  have hBTc := card_sup_mul_card_inf_of_le_normalizer h.bnT
  have hHIc := card_sup_mul_card_inf_of_le_normalizer hHN
  rw [← hY] at hHIc
  have hBH : B ⊔ T = H := sup_comm _ _
  rw [hBH, h.card_b] at hBTc
  obtain ⟨k, hk⟩ := h.tTwo.exists_card_eq
  have hBTpos : 0 < Nat.card ↥(B ⊓ T : Subgroup G) := Nat.card_pos
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hIpos : 0 < Nat.card ↥I := Nat.card_pos
  have hYpos : 0 < Nat.card ↥(yOf B T I) := Nat.card_pos
  have hHIpos : 0 < Nat.card ↥(H ⊓ I : Subgroup G) := Nat.card_pos
  have h81 : (81 : ℕ).factorization 3 = 4 := by
    have : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [this, Nat.Prime.factorization_pow hp3]; simp
  have h2k : (2 ^ k).factorization 3 = 0 := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]; simp
  have hvH : (Nat.card ↥H).factorization 3 ≤ 4 := by
    rw [hk] at hBTc
    have hfac : ((Nat.card ↥H) * Nat.card ↥(B ⊓ T : Subgroup G)).factorization 3 =
        (81 * 2 ^ k).factorization 3 := by rw [hBTc]
    rw [Nat.factorization_mul hHpos.ne' hBTpos.ne',
      Nat.factorization_mul (by norm_num) (by positivity)] at hfac
    simp only [Finsupp.add_apply] at hfac
    omega
  have hvHI : 2 ≤ (Nat.card ↥(H ⊓ I : Subgroup G)).factorization 3 := by
    have hd : 9 ∣ Nat.card ↥(H ⊓ I : Subgroup G) := by
      rw [← h.card_bI]
      exact Subgroup.card_dvd_of_le (inf_le_inf_right _ (le_sup_right : B ≤ T ⊔ B))
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    have := (hp3.pow_dvd_iff_le_factorization hHIpos.ne').1 (by rw [← h9]; exact hd)
    exact this
  have hvI := factorization_card_le h
  have hvY : (Nat.card ↥(yOf B T I)).factorization 3 ≤ 4 := by
    have := congrArg (fun n => n.factorization 3) hHIc
    simp only [Nat.factorization_mul hYpos.ne' hHIpos.ne', Nat.factorization_mul hHpos.ne'
      hIpos.ne', Finsupp.add_apply] at this
    omega
  have hrel := Subgroup.relIndex_mul_card B (yOf B T I)
  rw [inf_of_le_left (B_le_yOf B T I), h.card_b] at hrel
  have hrpos : B.relIndex (yOf B T I) ≠ 0 := by
    intro h0; rw [h0] at hrel; simp at hrel; exact hYpos.ne' hrel.symm
  have h1 := congrArg (fun n => n.factorization 3) hrel
  simp only [Nat.factorization_mul hrpos (by norm_num : (81 : ℕ) ≠ 0), Finsupp.add_apply] at h1
  have hpos := hp3.factorization_pos_of_dvd hrpos hdvd
  omega

omit [Finite G] in
theorem b_le_wOf {B T I : Subgroup G} (h : Setup710 B T I) : B ≤ wOf B T I :=
  le_inf (le_normalizer_inf_of_le h.bnT
    ((B_le_yOf B T I).trans (y_le_normalizer_pOf B T I))) (B_le_yOf B T I)

omit [Finite G] in
theorem t_le_wOf {B T I : Subgroup G} (_h : Setup710 B T I) : T ≤ wOf B T I :=
  le_inf (le_normalizer_inf_of_le Subgroup.le_normalizer
    ((T_le_yOf B T I).trans (y_le_normalizer_pOf B T I))) (T_le_yOf B T I)

theorem not_two_dvd_card_zOf (B T I : Subgroup G) : ¬ 2 ∣ Nat.card ↥(zOf B T I) :=
  not_dvd_card_glaPPrimeCoreOf Nat.prime_two _

theorem frattini_aux {Y P S : Subgroup G} (hPY : Y ≤ Subgroup.normalizer (P : Set G))
    (hPle : P ≤ Y) (hSP : S ≤ P) (hS2 : IsPGroup 2 ↥S) (hidx : ¬ 2 ∣ S.relIndex P) {y : G}
    (hy : y ∈ Y) :
    ∃ p ∈ P, ∃ w ∈ Subgroup.normalizer (S : Set G) ⊓ Y, y = p * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyP : ∀ x : G, x ∈ P ↔ y * x * y⁻¹ ∈ P := fun x =>
    Subgroup.mem_normalizer_iff.1 (hPY hy) x
  let f : ↥P →* ↥P :=
    { toFun := fun x => ⟨y * x * y⁻¹, (hyP x).1 x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simpa [f] using this
  let S' : Subgroup ↥P := S.subgroupOf P
  have hS'p : IsPGroup 2 ↥S' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hS'i : ¬ 2 ∣ S'.index := hidx
  let S2 : Subgroup ↥P := S'.map f
  have hS2p : IsPGroup 2 ↥S2 := hS'p.map f
  have hcard : Nat.card S2 = Nat.card S' := Subgroup.card_map_of_injective hf
  have hS2i : ¬ 2 ∣ S2.index := by
    have e1 := Subgroup.card_mul_index S'
    have e2 := Subgroup.card_mul_index S2
    have : S2.index = S'.index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hcard] at e2; rw [e1, e2])
    rw [this]; exact hS'i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) (hS'p.toSylow hS'i) (hS2p.toSylow hS2i)
  have hg' : (MulAut.conj g) • S' = S2 := by
    have := congrArg (fun Q : Sylow 2 ↥P => (Q : Subgroup ↥P)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  have hmemS2 : ∀ x : ↥P, x ∈ S2 ↔ g⁻¹ * x * g ∈ S' := by
    intro x
    rw [← hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  have key : ∀ x : ↥P, y⁻¹ * (x : G) * y ∈ S ↔ g⁻¹ * (x : G) * g ∈ S := by
    intro x
    have h2 : x ∈ S2 ↔ y⁻¹ * (x : G) * y ∈ S := by
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hs' : (s : G) ∈ S := hs
        simpa [f, mul_assoc] using hs'
      · intro hx
        refine ⟨⟨y⁻¹ * x * y, ?_⟩, ?_, ?_⟩
        · exact hSP hx
        · exact hx
        · ext; simp [f, mul_assoc]
    rw [← h2, hmemS2]
    simp [S', Subgroup.mem_subgroupOf]
  have hgP : (g : G) ∈ P := g.2
  have key' : ∀ x : G, x ∈ P → (y⁻¹ * x * y ∈ S ↔ (g : G)⁻¹ * x * g ∈ S) :=
    fun x hx => key ⟨x, hx⟩
  refine ⟨g, hgP, (g : G)⁻¹ * y, ?_, by simp⟩
  refine ⟨?_, Y.mul_mem (Y.inv_mem (hPle hgP)) hy⟩
  change _ ∈ Subgroup.normalizer (S : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : (g : G)⁻¹ * y * h * ((g : G)⁻¹ * y)⁻¹ = (g : G)⁻¹ * (y * h * y⁻¹) * g := by group
  rw [e]
  constructor
  · intro hh
    have hx : y * h * y⁻¹ ∈ P := (hyP h).1 (hSP hh)
    exact (key' _ hx).1 (by simpa [mul_assoc] using hh)
  · intro hh
    have hx : y * h * y⁻¹ ∈ P := by
      have hu : (g : G)⁻¹ * (y * h * y⁻¹) * g ∈ P := hSP hh
      have := P.mul_mem (P.mul_mem hgP hu) (P.inv_mem hgP)
      simpa [mul_assoc] using this
    simpa [mul_assoc] using (key' _ hx).2 hh

theorem exists_mul_wOf {B T I : Subgroup G} (hf : YFacts B T I) {y : G} (hy : y ∈ yOf B T I) :
    ∃ p ∈ pOf B T I, ∃ w ∈ wOf B T I, y = p * w :=
  frattini_aux (y_le_normalizer_pOf B T I) (pOf_le_yOf B T I) inf_le_right hf.sylow.1
    hf.sylow.2 hy

omit [Finite G] in
theorem zOf_le_pOf {B T I : Subgroup G} (hf : YFacts B T I) : zOf B T I ≤ pOf B T I :=
  (Subgroup.map_subtype_le _).trans hf.cent

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
