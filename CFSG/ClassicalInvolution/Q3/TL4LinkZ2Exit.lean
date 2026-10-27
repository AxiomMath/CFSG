module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF165A
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenU3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

namespace Z2Exit

section Equiv

variable {G P : Type} [Group G] [Group P]

theorem orderOf_map_eq_two (e : G ≃* P) {a : G} (ha : a * a = 1) (ha1 : a ≠ 1) :
    orderOf (e a) = 2 := by
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime (by rw [pow_two]; exact ha) ha1

theorem exists_conj_of_mulEquiv (e : G ≃* P)
    (h : ∀ a b : P, orderOf a = 2 → orderOf b = 2 → ∃ g : P, g * a * g⁻¹ = b)
    (a a' : G) (ha : a * a = 1) (ha1 : a ≠ 1) (ha' : a' * a' = 1) (ha'1 : a' ≠ 1) :
    ∃ g : G, g * a * g⁻¹ = a' := by
  obtain ⟨g, hg⟩ := h _ _ (orderOf_map_eq_two e ha ha1) (orderOf_map_eq_two e ha' ha'1)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]

theorem sup_centralizer_of_mulEquiv (e : G ≃* P)
    (h : ∀ a b : P, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a ≠ b →
      Subgroup.centralizer ({a} : Set P) ⊔ Subgroup.centralizer ({b} : Set P) = ⊤)
    (a a' : G) (ha : a * a = 1) (ha1 : a ≠ 1) (ha' : a' * a' = 1) (ha'1 : a' ≠ 1)
    (hne : a' ≠ a) (hc : a * a' = a' * a) :
    Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({a'} : Set G) = ⊤ :=
  E3C269G.sup_centralizer_eq_top_of_equiv e (h _ _ (orderOf_map_eq_two e ha ha1)
    (orderOf_map_eq_two e ha' ha'1) (by rw [← map_mul, hc, map_mul])
    fun h' => hne (e.injective h').symm)

end Equiv

section Member

variable {X : Type} [Group X] [Finite X]

theorem nonabelian_of_member {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨x, -, y, -, hxy⟩ := hm.datum.sylow_nonabelian S
  exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩

theorem concl163_conjClass {R : Subgroup X} {S : Sylow 2 R} {z : X} (hd : TightDatum R S z)
    (h : Concl163Syl R S z) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ a : X, IsUniqueInvolution L a →
      ∀ P : Subgroup X, IsSylow2In P L → ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) →
        β = 1 ∨ β = MulAut.conj a := by
  rintro L ⟨g, rfl⟩ a ha P hP β hβ hfix
  have hz := hd.isUniqueInvolution_core
  have hS₀ : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := by
    have h1 := isSylow2In_map_subtype R S
    exact ⟨MF163.sylow_le_tightCore S, h1.2.1,
      fun V hV h2 hle => h1.2.2 V (hV.trans (tightCore_le R)) h2 hle⟩
  have hP' : IsSylow2In (conjSub g⁻¹ P) (tightCore R) := by
    have := hP.conj g⁻¹
    rwa [conjSub_inv_conjSub] at this
  obtain ⟨k, hk, hkS⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hS₀ hP'
  have hPc : P = conjSub (g * k) ((S : Subgroup R).map R.subtype) := by
    rw [conjSub_mul, hkS, conjSub_conjSub_inv]
  have hkz : k * z * k⁻¹ = z := by
    have hm : k * z * k⁻¹ ∈ tightCore R :=
      (tightCore R).mul_mem ((tightCore R).mul_mem hk hz.mem) ((tightCore R).inv_mem hk)
    have h2 : k * z * k⁻¹ * (k * z * k⁻¹) = 1 := by
      calc k * z * k⁻¹ * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    refine (hz.unique _ hm h2).resolve_left fun h1 => hz.ne_one ?_
    calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have ha' : a = g * k * z * (g * k)⁻¹ := by
    rw [ha.eq (hz.conj g)]
    calc g * z * g⁻¹ = g * (k * z * k⁻¹) * g⁻¹ := by rw [hkz]
      _ = g * k * z * (g * k)⁻¹ := by group
  set c := g * k with hc
  have hγ2 : ((MulAut.conj c)⁻¹ * β * MulAut.conj c) * ((MulAut.conj c)⁻¹ * β * MulAut.conj c) =
      1 := by
    calc ((MulAut.conj c)⁻¹ * β * MulAut.conj c) * ((MulAut.conj c)⁻¹ * β * MulAut.conj c)
        = (MulAut.conj c)⁻¹ * (β * β) * MulAut.conj c := by group
      _ = 1 := by rw [hβ]; group
  have hγS : ∀ x ∈ (S : Subgroup R).map R.subtype,
      ((MulAut.conj c)⁻¹ * β * MulAut.conj c) x = x := by
    intro x hx
    have hxP : c * x * c⁻¹ ∈ P := by
      rw [hPc]
      exact conj_mem_conjSub hx c
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hfix _ hxP, ← map_inv,
      MulAut.conj_apply]
    group
  have hβc : β = MulAut.conj c * ((MulAut.conj c)⁻¹ * β * MulAut.conj c) * (MulAut.conj c)⁻¹ := by
    group
  rcases h _ hγ2 hγS with h1 | h1
  · left
    rw [hβc, h1]
    group
  · right
    rw [hβc, h1, ha', ← map_inv, ← map_mul, ← map_mul]

theorem isSporadic_fstarQuot_of_simple [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (e : X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12) :
    NativeSporadic.IsSporadic (FStarQuot X) .M12 := by
  have hF :=
    ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hZX : Subgroup.center X = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right ?_
    intro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hZF : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (f := eF.toMonoidHom) eF.injective,
      show (Subgroup.center ↥(genFittingFStar X)).map eF.toMonoidHom = Subgroup.center X from
        Subgroup.map_center_eq eF, hZX]
  exact ⟨((((QuotientGroup.quotientMulEquivOfEq hZF).trans QuotientGroup.quotientBot).trans
    eF).trans ((QuotientGroup.quotientMulEquivOfEq hZX).trans
      QuotientGroup.quotientBot).symm).trans e⟩

theorem linkZ2Model_of_mulEquiv {Q : Type} [Group Q] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {Φ : Set (Subgroup X)} (e : X ≃* Q)
    (hα : AutAlphaPairs ↥(genFittingFStar X))
    (hconj : ∀ a b : Q, orderOf a = 2 → orderOf b = 2 → ∃ g : Q, g * a * g⁻¹ = b)
    (hgen : ∀ a b : Q, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a ≠ b →
      Subgroup.centralizer ({a} : Set Q) ⊔ Subgroup.centralizer ({b} : Set Q) = ⊤)
    (h163 : ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a) :
    LinkZ2Model X Φ := by
  have hF : genFittingFStar X = ⊤ :=
    ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨eF.isSimpleGroup, ⟨eF.symm a, eF.symm b, fun h => hab ?_⟩, fun x _ => hF ▸
    Subgroup.mem_top x, hα, exists_conj_of_mulEquiv (eF.trans e) hconj,
    sup_centralizer_of_mulEquiv e hgen, h163⟩
  simpa using congrArg eF h

end Member

section Exit

variable {X : Type} [Group X] [Finite X]

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

theorem concl163Syl_of_exit
    (hs : IsSimpleGroup X) {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hm : EdgelessMember3 R S z) (h3 : ¬ TightActs3 R z) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hl : LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f) :
    Concl163Syl R S z := by
  have hnab := nonabelian_of_member hm
  by_cases hq3 : p ^ f = 3
  · exfalso
    obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
    rcases hl with hl | hl
    · obtain ⟨e⟩ := GH74.KGroups.L33.equiv_of_lieModel hl
      exact h3 (MF163.tightActs3_of_equiv_l33 e hm.datum hm.cls)
    · obtain ⟨e⟩ := GH74.KGroups.U33.equiv_of_lieModel hl
      exact h3 (MF163.tightActs3_of_equiv_u33 e hm.datum hm.cls)
  have h5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3p : 3 ≤ p := by have := hp.two_le; omega
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf
      rcases hl with hl | hl
      · exact absurd (CFSG.GH74.Generic.lieModel_psl_data hl).2.1 (by norm_num)
      · exact absurd (CFSG.GH74.Generic.lieModel_psu_data hl).2.1 (by norm_num)
    · have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      obtain ⟨k, hk⟩ := hodd
      omega
  have hZ : Subgroup.center X = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right ?_
    intro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  rcases hl with hl | hl
  · have hF : genFittingFStar X = ⊤ :=
      ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
    let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
    have : IsSimpleGroup ↥(genFittingFStar X) := eF.isSimpleGroup
    obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hl
    exact MF163.L3.concl163Syl_of_psl3 hm hp hp2 hf hK h5
      ((eF.trans e₀).trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)))
  · obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hl
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have : IsSimpleGroup ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).isSimpleGroup
    have hC : Subgroup.centralizer ((⊤ : Subgroup X) : Set X) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
    exact MF163.U3.concl163Syl_ge_five hm.datum hm.cls.1 hC h hp2 h5 (Subgroup.topEquiv.trans e₀)

theorem linkZ2Model_of_exit (hs : IsSimpleGroup X) {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) (h3 : ¬ TightActs3 R z) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hl : LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f) :
    LinkZ2Model X (CoreAssembly.conjClass (tightCore R)) := by
  have hnab := nonabelian_of_member hm
  have hF : genFittingFStar X = ⊤ :=
    ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hα : AutAlphaPairs ↥(genFittingFStar X) := autAlphaPairs_of_lieModel _ p f hp hp2
    (hl.imp (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inl rfl))
      (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inr rfl)))
  have h163 := concl163_conjClass hm.datum (concl163Syl_of_exit hs hm h3 hp hp2 hl)
  rcases hl with hl | hl
  · obtain ⟨-, -, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hl
    have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    exact linkZ2Model_of_mulEquiv hs hnab (e₀.trans
      ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))) hα
      (fun a b ha hb => E3S3Gen.exists_conj_psl3 hodd ha hb)
      (fun a b ha hb hab hne => E3C269G.sup_centralizer_eq_top_psl3 hodd ha hb hab hne) h163
  · obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hl
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    exact linkZ2Model_of_mulEquiv hs hnab e₀ hα
      (fun a b ha hb => E3S3Gen.exists_conj_psu3 h hp2 ha hb)
      (fun a b ha hb hab hne => E3C269G.sup_centralizer_eq_top_psu3 h hp2 ha hb hab hne) h163

end Exit

end Z2Exit

end CFSG.ClassicalInvolution.Q3.TL4
