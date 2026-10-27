module

public import CFSG.RankThree.PartOne.CTP.SeitzToral
public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.Open

theorem closure_centralizers_map_conj {G : Type*} [Group G] (g : G) (E : Subgroup G) :
    Subgroup.closure {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x} =
      (Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x}).map (MulAut.conj g).toMonoidHom := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have himg : {k | ∃ x ∈ E.map φ, x ≠ 1 ∧ Commute k x} =
      φ '' {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx⟩
      refine ⟨g⁻¹ * k * g, ⟨x, hx, fun h => hx1 (by rw [h, map_one]), ?_⟩, ?_⟩
      · have h := hkx.map (MulAut.conj g⁻¹).toMonoidHom
        simpa [hφ, MulAut.conj_apply, mul_assoc] using h
      · simp [hφ, MulAut.conj_apply, mul_assoc]
    · rintro ⟨k', ⟨x, hx, hx1, hkx⟩, rfl⟩
      refine ⟨φ x, ⟨x, hx, rfl⟩, fun h => hx1 ?_, hkx.map φ⟩
      exact (MulAut.conj g).injective (h.trans (map_one φ).symm)
  rw [himg, ← MonoidHom.map_closure]

theorem map_conj_map_conj_inv {G : Type*} [Group G] (n : G) (X : Subgroup G) :
    (X.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = X := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨n * x * n⁻¹, ⟨x, hx, rfl⟩, by simp [mul_assoc]⟩

theorem closure_centralizers_eq_top_of_map_conj_eq_top {G : Type*} [Group G] (g : G)
    (E : Subgroup G)
    (h : Subgroup.closure {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x} = ⊤) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  rw [closure_centralizers_map_conj] at h
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [h, Subgroup.map_top, MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective]

theorem closure_centralizers_eq_top_of_two_conj {G : Type*} [Group G] {p : ℕ} (X P : Subgroup G)
    (n : G) (hPX : P ≤ X) (hPXn : P ≤ X.map (MulAut.conj n).toMonoidHom)
    (hclose : ∀ M : Subgroup G, X ≤ M → X.map (MulAut.conj n).toMonoidHom ≤ M → M = ⊤)
    (hX : ∀ E : Subgroup G, E ≤ X → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
      X ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x})
    (E₀ : Subgroup G) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hSyl : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  obtain ⟨g, hg⟩ := hSyl
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hE₁X : E₁ ≤ X := hg.trans hPX
  set E₂ := E₁.map (MulAut.conj n⁻¹).toMonoidHom with hE₂
  have hE₂p : ∀ x ∈ E₂, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₁p x hx, map_one]
  have hE₂c : Nat.card E₂ = p ^ 2 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hE₁c]
  have hE₂X : E₂ ≤ X := by
    have h : E₁ ≤ X.map (MulAut.conj n).toMonoidHom := hg.trans hPXn
    calc E₂ ≤ (X.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom :=
          Subgroup.map_mono h
      _ = X := map_conj_map_conj_inv n X
  have hM1 : X ≤ Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x} :=
    hX E₁ hE₁X hE₁p hE₁c
  have hM2 : X ≤ Subgroup.closure {k | ∃ x ∈ E₂, x ≠ 1 ∧ Commute k x} :=
    hX E₂ hE₂X hE₂p hE₂c
  have hM2' : X.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x} := by
    rw [hE₂, closure_centralizers_map_conj] at hM2
    have h3 := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hM2
    have h4 := map_conj_map_conj_inv n⁻¹ (Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x})
    rw [inv_inv] at h4
    rwa [h4] at h3
  have htop : Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x} = ⊤ := hclose _ hM1 hM2'
  exact closure_centralizers_eq_top_of_map_conj_eq_top g E₀ htop

section SylowFrame

variable {K : Type} [Field K] [Finite K]

theorem card_specialLinear_fin_two :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let : Fintype K := Fintype.ofFinite K
  let q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have hsq : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
  rw [← Nat.card_eq_fintype_card]
  change ((q ^ 2 - q ^ 0) * (q ^ 2 - q ^ 1)) / (q - 1) = q * (q ^ 2 - 1)
  rw [pow_zero, pow_one, hsq, ← mul_assoc, Nat.mul_div_cancel]
  · exact Nat.mul_comm _ _
  · omega

theorem factorization_card_SL2_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card SL(2, K)).factorization p = (Nat.card K + 1).factorization p := by
  rw [card_specialLinear_fin_two (K := K)]
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have e : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    zify [Nat.one_le_pow 2 (m + 1) (by omega)]
    ring
  have hq0 : Nat.card K ≠ 0 := by omega
  have hq21 : Nat.card K - 1 ≠ 0 := by
    intro h
    apply hpq1
    rw [h]
    exact dvd_zero p
  have hq22 : Nat.card K + 1 ≠ 0 := by omega
  rw [e, Nat.factorization_mul hq0 (mul_ne_zero hq21 hq22), Finsupp.add_apply,
    Nat.factorization_mul hq21 hq22, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpK,
    Nat.factorization_eq_zero_of_not_dvd hpq1]
  simp

theorem exists_conj_le_frame_sylow {G : Type*} [Group G] [Finite G] {k : ℕ}
    (ρ : Fin k → SL(2, K) →* G) (hρi : ∀ i, Function.Injective (ρ i))
    (hρc : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y))
    {p : ℕ} [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hord : (Nat.card G).factorization p ≤ k * (Nat.card K + 1).factorization p) :
    ∃ Q : Subgroup (Fin k → SL(2, K)),
      Disjoint Q (MonoidHom.noncommPiCoprod ρ hρc).ker ∧
      ∀ E : Subgroup G, (∀ x ∈ E, x ^ p = 1) →
        ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ Q.map (MonoidHom.noncommPiCoprod ρ hρc) := by
  classical
  set μ := MonoidHom.noncommPiCoprod ρ hρc with hμ
  obtain ⟨Q⟩ : Nonempty (Sylow p (Fin k → SL(2, K))) := inferInstance
  have hdisj : Disjoint (Q : Subgroup (Fin k → SL(2, K))) μ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxk
    have hx1 : μ x = 1 := hxk
    have hcent : ∀ i, ∀ y : SL(2, K), x i * y = y * x i := by
      intro i y
      set x' : Fin k → SL(2, K) := Function.update x i 1 with hx'
      have hsplit : x = Pi.mulSingle i (x i) * x' := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hx']
        · simp [hx', hj]
      have hcomm' : Commute (μ x') (ρ i y) := by
        rw [hμ, MonoidHom.noncommPiCoprod_apply]
        refine (Finset.noncommProd_commute _ _ _ (ρ i y) fun j _ => ?_).symm
        by_cases hj : j = i
        · subst hj
          simp [hx']
        · exact (hρc (Ne.symm hj) _ _)
      have h1 : ρ i (x i) * μ x' = 1 := by
        have := hx1
        rw [hsplit, map_mul, hμ, MonoidHom.noncommPiCoprod_mulSingle] at this
        exact this
      have h2 : ρ i (x i) = (μ x')⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : Commute (ρ i (x i)) (ρ i y) := by
        rw [h2]
        exact (hcomm'.inv_left).symm.symm
      apply (hρi i)
      rw [map_mul, map_mul]
      exact h3.eq
    have hsq : x ^ 2 = 1 := by
      funext i
      have hc : x i ∈ Subgroup.center SL(2, K) :=
        Subgroup.mem_center_iff.2 fun y => (hcent i y).symm
      obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
      simp only [Fintype.card_fin] at hr
      have hmul : x i * x i = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul, ← pow_two, hr, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      rw [Pi.pow_apply, Pi.one_apply, pow_two]
      exact hmul
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨x, hxQ⟩
    have hm' : x ^ (p ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcop : Nat.Coprime 2 (p ^ m) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hpF.out).2 (by omega))
    have hd : orderOf x ∣ Nat.gcd 2 (p ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hm')
    rw [hcop] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  refine ⟨Q, hdisj, fun E hEp => ?_⟩
  have hcard : (Nat.card G).factorization p =
      (Nat.card ((Q : Subgroup _).map μ)).factorization p := by
    have h1 : Nat.card ((Q : Subgroup _).map μ) = Nat.card Q := by
      have hinj : Function.Injective (μ.comp (Q : Subgroup _).subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        exact Subtype.ext (Subgroup.disjoint_def.mp hdisj x.2 hx)
      have hrange : (μ.comp (Q : Subgroup _).subtype).range = (Q : Subgroup _).map μ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h2 : (Nat.card ((Q : Subgroup _).map μ)).factorization p =
        k * (Nat.card K + 1).factorization p := by
      rw [h1, Sylow.card_eq_multiplicity Q, Nat.Prime.factorization_pow hpF.out,
        Finsupp.single_eq_same, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        factorization_card_SL2_of_dvd_add_one hpF.out hp5 hpq]
    have h3 : (Nat.card ((Q : Subgroup _).map μ)).factorization p ≤
        (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card _) p
    omega
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (p := p) (Y := ⊤)
    (H := (Q : Subgroup _).map μ) (A := E) le_top le_top hEp
    (by rw [Subgroup.card_top]; exact hcard)
  exact ⟨g, hg⟩

theorem map_noncommPiCoprod_le {G : Type*} [Group G] {k : ℕ} (ρ : Fin k → SL(2, K) →* G)
    (hρc : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y))
    (Q : Subgroup (Fin k → SL(2, K))) :
    Q.map (MonoidHom.noncommPiCoprod ρ hρc) ≤ ⨆ i, (ρ i).range := by
  refine le_trans (fun x hx => ?_) (MonoidHom.noncommPiCoprod_range (hcomm := hρc) ρ).le
  rcases hx with ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

end SylowFrame

section Cover

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [hpF : Fact p.Prime]

theorem card_map_eq_of_disjoint_ker {A B : Type*} [Group A] [Group B] (φ : A →* B)
    {E : Subgroup A} (h : Disjoint E φ.ker) : Nat.card (E.map φ) = Nat.card E := by
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : A) ∈ φ.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.mp h x.2 hx')
  have hrange : (φ.comp E.subtype).range = E.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_lift_elemAbelian_of_coprime_ker [Finite H] {Q : Type*} [Group Q] (π : H →* Q)
    (hπ : Function.Surjective π) (hcop : ¬ p ∣ Nat.card π.ker) {F : Subgroup Q}
    (hF : IsElemAbelian p F) :
    ∃ E' : Subgroup H, E'.map π = F ∧ Disjoint E' π.ker ∧ IsElemAbelian p E' := by
  have hFp : IsPGroup p F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨E', hmap, hdis⟩ :=
    CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hcop F hFp
  have hmem : ∀ x ∈ E', π x ∈ F := fun x hx => hmap ▸ ⟨x, hx, rfl⟩
  have hexp : ∀ x ∈ E', x ^ p = 1 := by
    intro x hx
    refine Subgroup.disjoint_def.mp hdis (E'.pow_mem hx p) ?_
    rw [MonoidHom.mem_ker, map_pow]
    exact hF.2 _ (hmem x hx)
  have hcomm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := congrArg Subtype.val (hF.1.is_comm.comm ⟨π a, hmem a ha⟩ ⟨π b, hmem b hb⟩)
      have h : π a * π b = π b * π a := this
      rw [h]
      group
    have := Subgroup.disjoint_def.mp hdis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  exact ⟨E', hmap, hdis, IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩

theorem closure_in_range_of_cover [Finite H] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker)
    (hH : ∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (F : Subgroup G) (hF : F ≤ ψ.range) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    ψ.range ≤ Subgroup.closure {g | g ∈ ψ.range ∧ ∃ x ∈ F, x ≠ 1 ∧ Commute g x} := by
  classical
  set ψ' : H →* ψ.range := ψ.rangeRestrict with hψ'
  have hker' : ¬ p ∣ Nat.card ψ'.ker := by
    rw [hψ', ψ.ker_rangeRestrict]
    exact hker
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup F := IsPGroup.commGroupOfCardEqPrimeSq hFc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  set F1 : Subgroup ψ.range := F.subgroupOf ψ.range with hF1def
  have hF1 : IsElemAbelian p F1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hFp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ' ψ.rangeRestrict_surjective hker' hF1
  have hcardF1 : Nat.card F1 = p ^ 2 := by
    rw [← hFc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardF1, ← hmapE', card_map_eq_of_disjoint_ker ψ' hdisE']
  have htop := hH E' hE'ea hcardE'
  intro g hg
  obtain ⟨h, rfl⟩ := hg
  have hh : h ∈ Subgroup.closure {h : H | ∃ x ∈ E', x ≠ 1 ∧ Commute h x} := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap : (Subgroup.closure {h : H | ∃ x ∈ E', x ≠ 1 ∧ Commute h x}).map ψ ≤
      Subgroup.closure {g | g ∈ ψ.range ∧ ∃ x ∈ F, x ≠ 1 ∧ Commute g x} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
    have hxF : ψ x ∈ F := by
      have h1 : ψ' x ∈ F1 := hmapE' ▸ ⟨x, hx, rfl⟩
      exact h1
    have hx1' : ψ x ≠ 1 := by
      intro h1
      apply hx1
      refine Subgroup.disjoint_def.mp hdisE' hx ?_
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    exact Subgroup.subset_closure ⟨⟨k, rfl⟩, ψ x, hxF, hx1', hkx.map ψ⟩
  exact hmap ⟨h, hh, rfl⟩

end Cover

end CFSG.LieType.SeitzGeneration.ExcHigh
