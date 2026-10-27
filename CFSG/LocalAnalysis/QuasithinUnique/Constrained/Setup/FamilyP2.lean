module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCentral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonNonsplitTorus
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag


noncomputable def p2Equiv (K : Type*) [Field K] :
    projectiveSL 2 K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 K)

theorem isOddPrimePower_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [Nat.card_zmod, pow_one]⟩

theorem p2_card {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (projectiveSL 2 (ZMod p)) = p * (p ^ 2 - 1) / 2 := by
  have hp : p.Prime := hpf.out
  rw [Nat.card_congr (p2Equiv (ZMod p)).toEquiv,
    GorensteinWalter.psl2_card_formula (ZMod p) (isOddPrimePower_prime hp hp2), Nat.card_zmod]

theorem inverting_pair_transport {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {C : Subgroup G} {w : G} (hC : IsCyclic C) (hw : w ∉ C) (hw2 : w * w = 1)
    (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    ∃ (C' : Subgroup G') (w' : G'), IsCyclic C' ∧ Nat.card C' = Nat.card C ∧ w' ∉ C' ∧
      w' * w' = 1 ∧ ∀ c ∈ C', w' * c * w'⁻¹ = c⁻¹ := by
  have hequiv : C ≃* C.map e.toMonoidHom := Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
  refine ⟨C.map e.toMonoidHom, e w, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective hequiv.toMonoidHom hequiv.surjective
  · exact (Nat.card_congr hequiv.toEquiv).symm
  · rintro ⟨c, hc, hce⟩
    exact hw (by rw [← e.injective hce]; exact hc)
  · rw [← map_mul, hw2, map_one]
  · rintro _ ⟨c, hc, rfl⟩
    show e w * e c * (e w)⁻¹ = (e c)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hinv c hc, map_inv]

theorem two_dvd_sub_one_of_odd {p : ℕ} (hp : Odd p) : 2 ∣ p - 1 :=
  (Nat.Odd.sub_odd hp odd_one).two_dvd

theorem two_dvd_sq_sub_one_of_odd {p : ℕ} (hp : Odd p) : 2 ∣ p ^ 2 - 1 :=
  (Nat.Odd.sub_odd (hp.pow) odd_one).two_dvd

theorem gcd_sub_one_two_of_odd' {p : ℕ} (hp : Odd p) : Nat.gcd (p - 1) 2 = 2 :=
  Nat.gcd_eq_right (two_dvd_sub_one_of_odd hp)

theorem p2_split_torus_data {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (projectiveSL 2 (ZMod p)) = p * (p ^ 2 - 1) / 2 ∧
    (∃ U : Subgroup (projectiveSL 2 (ZMod p)), IsCyclic U ∧ Nat.card U = p) ∧
    ∃ (C : Subgroup (projectiveSL 2 (ZMod p))) (w : projectiveSL 2 (ZMod p)),
      IsCyclic C ∧ Nat.card C = (p - 1) / 2 ∧ w ∉ C ∧ w * w = 1 ∧
        ∀ c ∈ C, w * c * w⁻¹ = c⁻¹ := by
  have hp : p.Prime := hpf.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨p2_card hp2, ?_, ?_⟩
  · have hdvd : p ∣ Nat.card (projectiveSL 2 (ZMod p)) := by
      rw [p2_card hp2, Nat.mul_div_assoc _ (two_dvd_sq_sub_one_of_odd hodd)]
      exact Dvd.intro _ rfl
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨Subgroup.zpowers g, inferInstance, by rw [Nat.card_zpowers, hg]⟩
  · obtain ⟨U, w, hUc, hUcard, -, hwU, hw2, hinv, -, -⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := ZMod p) (p := p)
        (f := 1) (by rw [Nat.card_zmod, pow_one])
    obtain ⟨C, w', hC, hCcard, hw', hw2', hinv'⟩ :=
      inverting_pair_transport (p2Equiv (ZMod p)).symm hUc hwU hw2 hinv
    refine ⟨C, w', hC, ?_, hw', hw2', hinv'⟩
    rw [hCcard, hUcard, Nat.card_zmod, gcd_sub_one_two_of_odd' hodd]

theorem dihedral_two_reflections_generate (n : ℕ) [NeZero n] :
    Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup n)) = ⊤ := by
  rw [eq_top_iff]
  have h0 : (DihedralGroup.sr 0 : DihedralGroup n) ∈
      Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup n)) :=
    Subgroup.subset_closure (by simp)
  have h1 : (DihedralGroup.sr 1 : DihedralGroup n) ∈
      Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup n)) :=
    Subgroup.subset_closure (by simp)
  have hr1 : (DihedralGroup.r 1 : DihedralGroup n) ∈
      Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup n)) := by
    have := Subgroup.mul_mem _ h0 h1
    simpa [DihedralGroup.sr_mul_sr] using this
  have hr : ∀ k : ZMod n, (DihedralGroup.r k : DihedralGroup n) ∈
      Subgroup.closure ({DihedralGroup.sr 0, DihedralGroup.sr 1} : Set (DihedralGroup n)) := by
    intro k
    have := Subgroup.pow_mem _ hr1 k.val
    rwa [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] at this
  intro g _
  cases g with
  | r k => exact hr k
  | sr k =>
    have := Subgroup.mul_mem _ h0 (hr k)
    simpa using this

theorem dihedral_sr_zero_ne_one (n : ℕ) [NeZero n] : (DihedralGroup.sr 0 : DihedralGroup n) ≠ 1 :=
  fun h => by cases h

theorem dihedral_sr_one_ne_one (n : ℕ) [NeZero n] : (DihedralGroup.sr 1 : DihedralGroup n) ≠ 1 :=
  fun h => by cases h

theorem not_dvd_sq_sub_one_div_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ p ∣ (p ^ 2 - 1) / 2 := by
  intro h
  obtain ⟨c, hc⟩ := two_dvd_sq_sub_one_of_odd hodd
  have hdiv : (p ^ 2 - 1) / 2 = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c two_pos
  rw [hdiv] at h
  have h3 : p ∣ p ^ 2 - 1 := by rw [hc]; exact Dvd.dvd.mul_left h 2
  have h4 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h5 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h4 h3
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
  exact hp.not_dvd_one h5

theorem p2_sylow_p_cyclic {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (P : Sylow p (projectiveSL 2 (ZMod p))) : IsCyclic P := by
  have hp : p.Prime := hpf.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hm0 : (p ^ 2 - 1) / 2 ≠ 0 := by
    have h2le := hp.two_le
    have h3 : 3 ≤ p := by omega
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    exact (Nat.div_pos (by omega) two_pos).ne'
  have hcard : Nat.card P = p := by
    rw [Sylow.card_eq_multiplicity, p2_card hp2,
      Nat.mul_div_assoc _ (two_dvd_sq_sub_one_of_odd hodd),
      Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, hp.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_sq_sub_one_div_two hp hodd), add_zero, pow_one]
  exact isCyclic_of_prime_card (p := p) hcard

theorem p2_sylow_two_dihedral {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (P : Sylow 2 (projectiveSL 2 (ZMod p))) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥P ≃* DihedralGroup (2 ^ m)) := by
  have hp : p.Prime := hpf.out
  have hsurj : Function.Surjective (p2Equiv (ZMod p)).toMonoidHom :=
    (p2Equiv (ZMod p)).surjective
  obtain ⟨m, hm, ⟨φ⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p)
    (isOddPrimePower_prime hp hp2) (Sylow.mapSurjective hsurj P)
  let φ' : ↥(Subgroup.map (p2Equiv (ZMod p)).toMonoidHom (P : Subgroup _)) ≃*
      DihedralGroup (2 ^ m) := φ
  exact ⟨m, hm, ⟨(Subgroup.equivMapOfInjective P (p2Equiv (ZMod p)).toMonoidHom
    (p2Equiv (ZMod p)).injective).trans φ'⟩⟩

theorem p2_sylow_shapes {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ P : Sylow ℓ (projectiveSL 2 (ZMod p)), IsCyclic P) ∧
    (∀ P : Sylow 2 (projectiveSL 2 (ZMod p)), ∃ a b : P, a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧
      Subgroup.closure ({a, b} : Set P) = ⊤) := by
  have hp : p.Prime := hpf.out
  have hcardK : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hsurj : Function.Surjective (p2Equiv (ZMod p)).toMonoidHom :=
    (p2Equiv (ZMod p)).surjective
  constructor
  · intro ℓ _ hℓ2 P
    by_cases hℓp : ℓ = p
    · subst hℓp
      exact p2_sylow_p_cyclic hp2 P
    · have hR := SectionRank.OddCover.psl_two_sylow_isCyclic hp hp2 hcardK hℓ2 hℓp
        (Sylow.mapSurjective hsurj P)
      have hR' : IsCyclic ↥(Subgroup.map (p2Equiv (ZMod p)).toMonoidHom (P : Subgroup _)) := hR
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective P (p2Equiv (ZMod p)).toMonoidHom
          (p2Equiv (ZMod p)).injective).symm.toMonoidHom
        (Subgroup.equivMapOfInjective P (p2Equiv (ZMod p)).toMonoidHom
          (p2Equiv (ZMod p)).injective).symm.surjective
  · intro P
    obtain ⟨m, hm, ⟨ψ⟩⟩ := p2_sylow_two_dihedral hp2 P
    refine ⟨ψ.symm (DihedralGroup.sr 0), ψ.symm (DihedralGroup.sr 1), ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact dihedral_sr_zero_ne_one (2 ^ m) (by simpa using congrArg ψ h)
    · intro h
      exact dihedral_sr_one_ne_one (2 ^ m) (by simpa using congrArg ψ h)
    · rw [← map_mul]
      simp
    · rw [← map_mul]
      simp
    · have h1 := dihedral_two_reflections_generate (2 ^ m)
      have h2 := congrArg (Subgroup.map ψ.symm.toMonoidHom) h1
      rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ ψ.symm.surjective] at h2
      rw [← h2]
      congr 1
      simp

theorem dihedral_elemAbelian_card_le_four {n : ℕ} [NeZero n] (E : Subgroup (DihedralGroup n))
    (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 4 := by
  classical
  let R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r 1)
  have hRcard : Nat.card R = n := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hGcard : Nat.card (DihedralGroup n) = 2 * n := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hRidx : R.index = 2 := by
    have h := Subgroup.card_mul_index R
    rw [hRcard, hGcard] at h
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith
  have : R.Normal := Subgroup.normal_of_index_eq_two hRidx
  have h1 : R.relIndex E ∣ 2 := hRidx ▸ Subgroup.relIndex_dvd_index_of_normal R E
  have hE : R.relIndex E * Nat.card (R ⊓ E : Subgroup (DihedralGroup n)) = Nat.card E :=
    Subgroup.relIndex_mul_card R E
  have hbound : Nat.card (R ⊓ E : Subgroup (DihedralGroup n)) ≤ 2 := by
    have hf := IsCyclic.card_pow_eq_one_le (α := R) (n := 2) two_pos
    have hinj : Function.Injective (fun x : (R ⊓ E : Subgroup (DihedralGroup n)) =>
        (⟨⟨x.1, x.2.1⟩, Subtype.ext (by simpa [pow_two] using h2 x.1 x.2.2)⟩ :
          {a : R // a ^ 2 = 1})) := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : {a : R // a ^ 2 = 1} => (z.1 : DihedralGroup n)) hxy)
    have := Nat.card_le_card_of_injective _ hinj
    refine this.trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hf
  have hidx2 : R.relIndex E ≤ 2 := Nat.le_of_dvd two_pos h1
  rw [← hE]
  calc R.relIndex E * Nat.card (R ⊓ E : Subgroup (DihedralGroup n)) ≤ 2 * 2 :=
        Nat.mul_le_mul hidx2 hbound
    _ = 4 := rfl

theorem p2_involution_structure {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p) :
    (∀ x y : projectiveSL 2 (ZMod p), x ≠ 1 → x * x = 1 → y ≠ 1 → y * y = 1 →
      ∃ g : projectiveSL 2 (ZMod p), g * x * g⁻¹ = y) ∧
    ∀ B : Subgroup (projectiveSL 2 (ZMod p)), (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      (∀ a ∈ B, a * a = 1) → Nat.card B ≤ 4 := by
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  refine ⟨fun x y hx hx2 hy hy2 => ?_, fun B _ hB2 => ?_⟩
  · obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power (ZMod p)
      (isOddPrimePower_prime hp hp2) (p2Equiv (ZMod p) x) (p2Equiv (ZMod p) y)
      ⟨fun h => hx ((p2Equiv (ZMod p)).map_eq_one_iff.1 h), by
        rw [← map_pow, pow_two, hx2, map_one]⟩
      ⟨fun h => hy ((p2Equiv (ZMod p)).map_eq_one_iff.1 h), by
        rw [← map_pow, pow_two, hy2, map_one]⟩
    refine ⟨(p2Equiv (ZMod p)).symm g, (p2Equiv (ZMod p)).injective ?_⟩
    simpa using hg
  · have hBp : IsPGroup 2 B := fun a => ⟨1, by
      rw [pow_one, pow_two]
      exact Subtype.ext (by simpa using hB2 a.1 a.2)⟩
    obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
    obtain ⟨m, hm, ⟨ψ⟩⟩ := p2_sylow_two_dihedral hp2 P
    let E : Subgroup (DihedralGroup (2 ^ m)) := (B.subgroupOf (P : Subgroup _)).map ψ.toMonoidHom
    have hE2 : ∀ a ∈ E, a * a = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul]
      have : b * b = 1 := Subtype.ext (by simpa using hB2 b.1 hb)
      simp [this]
    have h1 := dihedral_elemAbelian_card_le_four E hE2
    have h2 : Nat.card E = Nat.card B :=
      calc Nat.card E = Nat.card (B.subgroupOf (P : Subgroup _)) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).toEquiv).symm
        _ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
    rw [← h2]
    exact h1


theorem p2_nonsplit_torus_data {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ (C : Subgroup (projectiveSL 2 (ZMod p))) (w : projectiveSL 2 (ZMod p)),
      IsCyclic C ∧ Nat.card C = (p + 1) / 2 ∧ w ∉ C ∧ w * w = 1 ∧
        ∀ c ∈ C, w * c * w⁻¹ = c⁻¹ := by
  have hodd : Odd p := hpf.out.odd_of_ne_two hp2
  obtain ⟨S, hS, hScard, -, ⟨w, -, hwS, hw2, hinv, -, -⟩, -⟩ :=
    Glauberman.Dickson.h84_nonsplit_torus_data (F := ZMod p) (p := p) (f := 1)
      (by rw [Nat.card_zmod, pow_one])
  obtain ⟨C, w', hC, hCcard, hw', hw2', hinv'⟩ :=
    inverting_pair_transport (p2Equiv (ZMod p)).symm hS hwS hw2 hinv
  refine ⟨C, w', hC, ?_, hw', hw2', hinv'⟩
  rw [hCcard, hScard, Nat.card_zmod, gcd_sub_one_two_of_odd' hodd]

theorem p2_central_kernel_bound {s : ℕ} [hsf : Fact s.Prime] (hs5 : 5 ≤ s) {E : Type*} [Group E]
    [Finite E] [Group.IsPerfect E] (f : E →* projectiveSL 2 (ZMod s))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E) : Nat.card f.ker ≤ 2 := by
  have hs2 : s ≠ 2 := by omega
  obtain ⟨hodd, htwo⟩ := p2_sylow_shapes (p := s) hs2
  exact sylow_shape_central_kernel_bound (fun ℓ _ hℓ P => hodd ℓ hℓ P)
    (fun P => by
      obtain ⟨a, b, -, -, ha, hb, hab⟩ := htwo P
      exact ⟨a, b, ha, hb, hab⟩) f hf hker

end CFSG.QuasithinUnique.Setup.Family
