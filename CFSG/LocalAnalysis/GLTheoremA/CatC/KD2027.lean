module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.Models.Blueprint
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

namespace KD2027Aux

@[expose] def SL3Faithful (P : Type*) [Group P] : Prop :=
  ∃ (K : Type) (_ : Field K), (2 : K) ≠ 0 ∧ ∃ ψ : P →* GL (Fin 3) K, Function.Injective ψ ∧
    ∀ x, ((ψ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1

theorem SL3Faithful.of_injective {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Injective f) (h : SL3Faithful Q) : SL3Faithful P := by
  obtain ⟨K, hK, h2, ψ, hψ, hdet⟩ := h
  exact ⟨K, hK, h2, ψ.comp f, hψ.comp hf, fun x => hdet (f x)⟩

theorem derived_comm_of_gl2 {K : Type*} [Field K] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (ψ : P →* GL (Fin 2) K) (hψ : Function.Injective ψ) :
    ∀ x ∈ commutator P, ∀ y ∈ commutator P, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hcomm : ∀ a b : P, a * b = b * a
  · have hbot : commutator P = ⊥ := by
      rw [eq_bot_iff, commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_def, hcomm a b]
      group
    intro x hx y hy
    rw [hbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · push Not at hcomm
    obtain ⟨a, b, hab⟩ := hcomm
    have hnt : Nontrivial (P ⧸ Subgroup.center P) := by
      by_contra hns
      rw [not_nontrivial_iff_subsingleton] at hns
      apply hab
      have ha : a ∈ Subgroup.center P :=
        (QuotientGroup.eq_one_iff a).1 (Subsingleton.elim _ _)
      exact ((Subgroup.mem_center_iff.1 ha) b).symm
    have hQ : IsPGroup 2 (P ⧸ Subgroup.center P) := hP.to_quotient _
    haveI := hQ.center_nontrivial
    obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (1 : Subgroup.center (P ⧸ Subgroup.center P))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hq1' : (x : P ⧸ Subgroup.center P) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hxz : x ∉ Subgroup.center P := fun h => hq1' ((QuotientGroup.eq_one_iff x).2 h)
    have hxc : ∀ g : P, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.center P := by
      intro g
      rw [← QuotientGroup.eq_one_iff]
      have h1 := Subgroup.mem_center_iff.1 hq (g : P ⧸ Subgroup.center P)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← h1]
      group
    have hns : ¬ ∃ c : K, ((ψ x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
      rintro ⟨c, hc⟩
      apply hxz
      rw [Subgroup.mem_center_iff]
      intro g
      apply hψ
      apply Units.ext
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hc]
      simp [Matrix.smul_mul, Matrix.mul_smul]
    have hN : ∀ g h : P, g * x = x * g → h * x = x * h → g * h = h * g := by
      intro g h hg hh
      apply hψ
      apply Units.ext
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
      refine CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns ?_ ?_
      · rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hg.symm]
      · rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hh.symm]
    let c : P →* Subgroup.center P :=
      MonoidHom.mk' (fun g => ⟨x * g * x⁻¹ * g⁻¹, hxc g⟩) (by
        intro g h
        apply Subtype.ext
        have h1 : g * (x * h * x⁻¹ * h⁻¹) * g⁻¹ = x * h * x⁻¹ * h⁻¹ := by
          have := Subgroup.mem_center_iff.1 (hxc h) g
          rw [this]
          group
        calc x * (g * h) * x⁻¹ * (g * h)⁻¹
            = (x * g * x⁻¹ * g⁻¹) * (g * (x * h * x⁻¹ * h⁻¹) * g⁻¹) := by group
          _ = (x * g * x⁻¹ * g⁻¹) * (x * h * x⁻¹ * h⁻¹) := by rw [h1])
    have hcomm_le : commutator P ≤ c.ker := Abelianization.commutator_subset_ker c
    have hcx : ∀ u ∈ commutator P, u * x = x * u := by
      intro u hu
      have h1 : c u = 1 := hcomm_le hu
      have h2 : x * u * x⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : x * u = u * x := by
        calc x * u = (x * u * x⁻¹ * u⁻¹) * (u * x) := by group
          _ = u * x := by rw [h2, one_mul]
      exact h3.symm
    intro u hu v hv
    exact hN u v (hcx u hu) (hcx v hv)

theorem derived_comm_of_sl3 {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h : SL3Faithful P) : ∀ x ∈ commutator P, ∀ y ∈ commutator P, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hsub : Subsingleton P
  · intro x _ y _
    exact Subsingleton.elim _ _
  · have hnt : Nontrivial P := not_subsingleton_iff_nontrivial.1 hsub
    haveI := hP.center_nontrivial
    have h2dvd : 2 ∣ Nat.card (Subgroup.center P) := by
      rcases (hP.to_subgroup (Subgroup.center P)).card_eq_or_dvd with h1 | h1
      · exact absurd h1 (Finite.one_lt_card (α := Subgroup.center P)).ne'
      · exact h1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 h2dvd
    obtain ⟨hz2, hz1⟩ := orderOf_eq_prime_iff.1 hz
    have hzz : (z : P) * z = 1 := by
      have := congrArg Subtype.val hz2
      simpa [sq] using this
    have hz1' : (z : P) ≠ 1 := fun h' => hz1 (Subtype.ext h')
    have hzc : ∀ p : P, p * z = z * p := fun p => Subgroup.mem_center_iff.1 z.2 p
    obtain ⟨K, hK, h2, ψ, hψ, hdet⟩ := h
    have hψt1 : ψ z ≠ 1 := fun h' => hz1' (hψ (by rw [h', map_one]))
    obtain ⟨ρ, hρ, -⟩ := CFSG.RankThree.SubgroupLists.exists_injective_gl2_of_commute h2
      (t := ψ z) (by rw [← map_mul, hzz, map_one]) hψt1 (hdet z) ψ.range
      (by
        rintro _ ⟨x, rfl⟩
        rw [← map_mul, ← map_mul, hzc])
      (by
        rintro _ ⟨x, rfl⟩
        exact hdet x)
    exact derived_comm_of_gl2 hP (ρ.comp ψ.rangeRestrict)
      (hρ.comp (MonoidHom.rangeRestrict_injective_iff.2 hψ))

theorem card_le_four_of_sl3 {P : Type*} [Group P] (h : SL3Faithful P) (E : Subgroup P)
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  obtain ⟨K, hK, h2, ψ, hψ, hdet⟩ := h
  have h4 := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 (E.map ψ)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hE x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hdet x)
  rwa [Subgroup.card_map_of_injective hψ] at h4

theorem comm_of_central_involutions {P : Type*} [Group P] (h : SL3Faithful P) {t u : P}
    (ht : t * t = 1) (hu : u * u = 1) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u)
    (hct : ∀ p : P, p * t = t * p) (hcu : ∀ p : P, p * u = u * p) :
    ∀ x y : P, x * y = y * x := by
  obtain ⟨K, hK, h2, ψ, hψ, hdet⟩ := h
  have hψt1 : ψ t ≠ 1 := fun h => ht1 (hψ (by rw [h, map_one]))
  obtain ⟨ρ, hρ, hρt⟩ := CFSG.RankThree.SubgroupLists.exists_injective_gl2_of_commute h2
    (t := ψ t) (by rw [← map_mul, ht, map_one]) hψt1 (hdet t) ψ.range
    (by
      rintro _ ⟨x, rfl⟩
      rw [← map_mul, ← map_mul, hct])
    (by
      rintro _ ⟨x, rfl⟩
      exact hdet x)
  set ψ' : P →* GL (Fin 2) K := ρ.comp ψ.rangeRestrict with hψ'def
  have hψ' : Function.Injective ψ' :=
    hρ.comp (MonoidHom.rangeRestrict_injective_iff.2 hψ)
  have hψ't : ψ' t = -1 := hρt (ψ.rangeRestrict t) rfl
  have hs2 : ψ' u * ψ' u = 1 := by rw [← map_mul, hu, map_one]
  have hs1 : ψ' u ≠ 1 := fun h => hu1 (hψ' (by rw [h, map_one]))
  have hsm : ψ' u ≠ -1 := fun h => htu (hψ' (by rw [hψ't, h]))
  have hns : ¬ ∃ c : K, ((ψ' u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    rintro ⟨c, hc⟩
    have hss : ((ψ' u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((ψ' u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, hs2, Units.val_one]
    rw [hc] at hss
    have hcc : c * c = 1 := by
      have := congrFun (congrFun hss 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    rcases mul_self_eq_one_iff.mp hcc with h1 | h1
    · apply hs1
      apply Units.ext
      rw [hc, h1, one_smul, Units.val_one]
    · apply hsm
      apply Units.ext
      rw [hc, h1, neg_smul, one_smul, Units.val_neg, Units.val_one]
  have hcomm : ∀ x : P, ((ψ' u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((ψ' x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ψ' x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((ψ' u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro x
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcu x]
  intro x y
  apply hψ'
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  exact CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns (hcomm x) (hcomm y)

theorem centralizes_of_centralizes_omega {Γ : Type*} [Group Γ] (R : Subgroup Γ)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hR2 : IsPGroup 2 R) (a : Γ)
    (haR : ∀ x ∈ R, a * x * a⁻¹ ∈ R) {m : ℕ} (hm : Odd m) (ham : a ^ m = 1)
    (hΩ : ∀ x ∈ R, x * x = 1 → a * x * a⁻¹ = x) : ∀ x ∈ R, a * x * a⁻¹ = x := by
  have key : ∀ j : ℕ, ∀ x ∈ R, x ^ (2 ^ j) = 1 → a * x * a⁻¹ = x := by
    intro j
    induction j with
    | zero =>
      intro x _ hx
      rw [pow_zero, pow_one] at hx
      rw [hx]
      group
    | succ j ih =>
      intro x hx hxj
      have hx2 : x ^ 2 ∈ R := R.pow_mem hx 2
      have hx2j : (x ^ 2) ^ (2 ^ j) = 1 := by
        rw [← pow_mul, ← pow_succ']
        exact hxj
      have h1 : a * x ^ 2 * a⁻¹ = x ^ 2 := ih _ hx2 hx2j
      have hyR : a * x * a⁻¹ ∈ R := haR x hx
      set u : Γ := a * x * a⁻¹ * x⁻¹ with hu
      have huR : u ∈ R := R.mul_mem hyR (R.inv_mem hx)
      have hy2 : (a * x * a⁻¹) * (a * x * a⁻¹) = x * x := by
        calc (a * x * a⁻¹) * (a * x * a⁻¹) = a * x ^ 2 * a⁻¹ := by rw [sq]; group
          _ = x ^ 2 := h1
          _ = x * x := sq x
      have huu : u * u = 1 := by
        have hc : x⁻¹ * (a * x * a⁻¹) = (a * x * a⁻¹) * x⁻¹ :=
          hR _ (R.inv_mem hx) _ hyR
        calc u * u = (a * x * a⁻¹) * (x⁻¹ * (a * x * a⁻¹)) * x⁻¹ := by rw [hu]; group
          _ = (a * x * a⁻¹) * ((a * x * a⁻¹) * x⁻¹) * x⁻¹ := by rw [hc]
          _ = ((a * x * a⁻¹) * (a * x * a⁻¹)) * x⁻¹ * x⁻¹ := by group
          _ = 1 := by rw [hy2]; group
      have hau : a * u * a⁻¹ = u := hΩ u huR huu
      have hax : a * x * a⁻¹ = u * x := by rw [hu]; group
      have hpow : ∀ k : ℕ, a ^ k * x * (a ^ k)⁻¹ = u ^ k * x := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹
              = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by group
            _ = a * (u ^ k * x) * a⁻¹ := by rw [ihk]
            _ = (a * u * a⁻¹) ^ k * (a * x * a⁻¹) := by rw [conj_pow]; group
            _ = u ^ (k + 1) * x := by rw [hau, hax]; group
      have hm' : u ^ m * x = x := by
        have := hpow m
        rw [ham] at this
        simpa using this.symm
      have hum : u ^ m = 1 := by
        have : u ^ m * x = 1 * x := by rw [hm', one_mul]
        exact mul_right_cancel this
      obtain ⟨r, hr⟩ := hm
      have hu1 : u = 1 := by
        have : u ^ m = u := by
          rw [hr, pow_succ, pow_mul, sq, huu, one_pow, one_mul]
        rw [← this, hum]
      rw [hu1] at hax
      simpa using hax
  intro x hx
  obtain ⟨j, hj⟩ := hR2 ⟨x, hx⟩
  exact key j x hx (by simpa using congrArg Subtype.val hj)

theorem fix_of_sq_fix {Γ : Type*} [Group Γ] {a x : Γ} {m : ℕ} (hm : Odd m) (ham : a ^ m = 1)
    (h : a ^ 2 * x * (a ^ 2)⁻¹ = x) : a * x * a⁻¹ = x := by
  obtain ⟨r, hr⟩ := hm
  have hpow : ∀ k : ℕ, (a ^ 2) ^ k * x * ((a ^ 2) ^ k)⁻¹ = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (a ^ 2) ^ (k + 1) * x * ((a ^ 2) ^ (k + 1))⁻¹
          = (a ^ 2) ^ k * (a ^ 2 * x * (a ^ 2)⁻¹) * ((a ^ 2) ^ k)⁻¹ := by group
        _ = x := by rw [h, ih]
  have hea : (a ^ 2) ^ (r + 1) = a := by
    rw [← pow_mul, show 2 * (r + 1) = m + 1 by omega, pow_succ, ham, one_mul]
  calc a * x * a⁻¹ = (a ^ 2) ^ (r + 1) * x * ((a ^ 2) ^ (r + 1))⁻¹ := by rw [hea]
    _ = x := hpow _

theorem eq_of_card_le_four {Γ : Type*} [Group Γ] [Finite Γ] (Ω : Subgroup Γ)
    (hΩ : Nat.card Ω ≤ 4) {v w : Γ} (hv : v ∈ Ω) (hw : w ∈ Ω) (hv1 : v ≠ 1) (hw1 : w ≠ 1)
    (hvw : v ≠ w) (hvv : v * v = 1) :
    ∀ x ∈ Ω, x = 1 ∨ x = v ∨ x = w ∨ x = v * w := by
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxv, hxw, hxz⟩ := hcon
  have hz1 : v * w ≠ 1 := by
    intro h
    apply hvw
    have h' : v⁻¹ = w := inv_eq_of_mul_eq_one_right h
    rw [← h', inv_eq_of_mul_eq_one_right hvv]
  have hzv : v ≠ v * w := fun h => hw1 (mul_left_cancel (h.symm.trans (mul_one v).symm))
  have hzw : w ≠ v * w := fun h => hv1 (mul_right_cancel (h.symm.trans (one_mul w).symm))
  let f : Fin 5 → Ω := ![1, ⟨v, hv⟩, ⟨w, hw⟩, ⟨v * w, Ω.mul_mem hv hw⟩, ⟨x, hx⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;> first
      | exact absurd hij'.symm ‹_›
      | exact absurd hij' ‹_›
  have h5 : Nat.card (Fin 5) ≤ Nat.card Ω := Nat.card_le_card_of_injective f hinj
  simp at h5
  omega

theorem map_subtype_commutator {Γ : Type*} [Group Γ] (T : Subgroup Γ) :
    (commutator ↥T).map T.subtype = ⁅T, T⁆ := by
  rw [commutator, Subgroup.map_commutator]
  have : (⊤ : Subgroup ↥T).map T.subtype = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [this]

theorem exists_section {G S : Type*} [Group G] [Finite G] [Group S] (π : G →* S)
    (hπ : Function.Surjective π) (hker : ∀ g ∈ π.ker, g ^ 3 = 1) (T₀ : Subgroup S)
    (hT₀ : IsPGroup 2 T₀) : ∃ ι : T₀ →* G, ∀ t : T₀, π (ι t) = (t : S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := T₀.comap π with hM
  let πM : M →* T₀ := (π.comp M.subtype).codRestrict T₀ (fun x => x.2)
  have hπM : Function.Surjective πM := by
    intro t
    obtain ⟨g, hg⟩ := hπ t
    exact ⟨⟨g, by rw [hM, Subgroup.mem_comap, hg]; exact t.2⟩, Subtype.ext hg⟩
  haveI : Finite M := inferInstance
  obtain ⟨Q₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 T₀))
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hπM 2 Q₀
  have hQ₀ : (Q₀ : Subgroup T₀) = ⊤ := (Q₀.3 (hT₀.to_subgroup ⊤) le_top).symm
  have hQmap : (Q : Subgroup M).map πM = ⊤ := by
    have := congrArg (fun P : Sylow 2 T₀ => (P : Subgroup T₀)) hQ
    simpa [hQ₀] using this
  let f : Q →* T₀ := πM.comp (Q : Subgroup M).subtype
  have hfsurj : Function.Surjective f := by
    intro t
    have ht : t ∈ (Q : Subgroup M).map πM := by rw [hQmap]; exact Subgroup.mem_top t
    obtain ⟨q, hq, hqt⟩ := ht
    exact ⟨⟨q, hq⟩, hqt⟩
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (((x : M) : G)) = 1 := congrArg Subtype.val hx
    have h3 : ((x : M) : G) ^ 3 = 1 := hker _ (MonoidHom.mem_ker.2 h1)
    obtain ⟨k, hk⟩ := Q.2 x
    have h2 : ((x : M) : G) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : Q => ((z : M) : G)) hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have := CFSG.RankThree.SubgroupLists.eq_one_of_pow_three_of_pow h3 hcop h2
    exact Subtype.ext (Subtype.ext this)
  let e : Q ≃* T₀ := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨M.subtype.comp ((Q : Subgroup M).subtype.comp e.symm.toMonoidHom), fun t => ?_⟩
  have h1 : f (e.symm t) = t := e.apply_symm_apply t
  exact congrArg Subtype.val h1

theorem kd2027_abs {Γ : Type*} [Group Γ] [Finite Γ] (A T : Subgroup Γ) (hA : IsPGroup 3 A)
    (hT : IsPGroup 2 T) (hN : A ≤ Subgroup.normalizer (T : Set Γ)) (hAT : ⁅A, T⁆ = T)
    (hF : SL3Faithful T) : ⁅A, ⁅T, T⁆⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ a ∈ A, ∀ t : Γ, t ∈ T ↔ a * t * a⁻¹ ∈ T := fun a ha =>
    Subgroup.mem_normalizer_iff.1 (hN ha)
  have hnorm' : ∀ a ∈ A, ∀ t : Γ, t ∈ T → a * t * a⁻¹ ∈ T := fun a ha t ht =>
    (hnorm a ha t).1 ht
  have hnorm'' : ∀ a ∈ A, ∀ t ∈ T, a⁻¹ * t * a ∈ T := by
    intro a ha t ht
    have := hnorm' a⁻¹ (A.inv_mem ha) t ht
    simpa using this
  set R : Subgroup Γ := ⁅T, T⁆ with hRdef
  have hRT : R ≤ T := Subgroup.commutator_le.2 fun g hg h hh =>
    T.mul_mem (T.mul_mem (T.mul_mem hg hh) (T.inv_mem hg)) (T.inv_mem hh)
  have hRT' : ∀ t ∈ T, ∀ x ∈ R, t * x * t⁻¹ ∈ R := by
    intro t ht x hx
    have h1 : ⁅t, x⁆ ∈ R := Subgroup.commutator_mem_commutator ht (hRT hx)
    have : t * x * t⁻¹ = ⁅t, x⁆ * x := by rw [commutatorElement_def]; group
    rw [this]
    exact R.mul_mem h1 hx
  have hRA : ∀ a ∈ A, ∀ x ∈ R, a * x * a⁻¹ ∈ R := by
    intro a ha x hx
    have hx' : x ∈ Subgroup.closure {z | ∃ g₁ ∈ T, ∃ g₂ ∈ T, ⁅g₁, g₂⁆ = z} := by
      rw [← Subgroup.commutator_def]; exact hx
    refine Subgroup.closure_induction (p := fun x _ => a * x * a⁻¹ ∈ R) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      have : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁ * a⁻¹, a * g₂ * a⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (hnorm' a ha g₁ hg₁) (hnorm' a ha g₂ hg₂)
    · simp
    · intro x y _ _ hx hy
      have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [this]; exact R.mul_mem hx hy
    · intro x _ hx
      have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [this]; exact R.inv_mem hx
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have hmap : (commutator ↥T).map T.subtype = R := map_subtype_commutator T
    rw [← hmap] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have := derived_comm_of_sl3 hT hF x' hx' y' hy'
    simpa using congrArg Subtype.val this
  by_contra hne
  have hex : ∃ a ∈ A, ∃ v ∈ R, v * v = 1 ∧ a * v * a⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha x hx
    rw [Subgroup.mem_bot]
    have hR2 : IsPGroup 2 R := hT.to_le hRT
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have hak : a ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have := centralizes_of_centralizes_omega R hRcomm hR2 a (hRA a ha) hodd hak
      (fun v hv hvv => hcon a ha v hv hvv) x hx
    rw [commutatorElement_def, this, mul_inv_cancel]
  obtain ⟨a, ha, v, hvR, hvv, hav⟩ := hex
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  have hak : a ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  set w : Γ := a * v * a⁻¹ with hw
  have hwR : w ∈ R := hRA a ha v hvR
  have hww : w * w = 1 := by
    calc w * w = a * (v * v) * a⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hvv]; group
  have hv1 : v ≠ 1 := fun h => hav (by rw [hw, h]; group)
  have hw1 : w ≠ 1 := fun h => hv1 (by
    have h1 : a * v = a * 1 := by rw [mul_one]; exact mul_inv_eq_one.1 h
    exact mul_left_cancel h1)
  have hvw : v ≠ w := fun h => hav h.symm
  have hcvw : v * w = w * v := hRcomm v hvR w hwR
  let Ω : Subgroup Γ :=
    { carrier := {x | x ∈ R ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => ⟨R.mul_mem hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hRcomm y hy.1 x hx.1]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, mul_one]⟩
      one_mem' := ⟨R.one_mem, mul_one 1⟩
      inv_mem' := fun {x} hx => ⟨R.inv_mem hx.1, by
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx.2, inv_one]⟩ }
  have hvΩ : v ∈ Ω := ⟨hvR, hvv⟩
  have hwΩ : w ∈ Ω := ⟨hwR, hww⟩
  have hΩT : Ω ≤ T := fun x hx => hRT hx.1
  have hΩcard : Nat.card Ω ≤ 4 := by
    have h1 := card_le_four_of_sl3 hF (Ω.subgroupOf T)
      (fun x hx => Subtype.ext (by simpa using (Subgroup.mem_subgroupOf.1 hx).2))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩT).toEquiv] at h1
  have hΩdesc : ∀ x ∈ Ω, x = 1 ∨ x = v ∨ x = w ∨ x = v * w :=
    eq_of_card_le_four Ω hΩcard hvΩ hwΩ hv1 hw1 hvw hvv
  have hawz : a * w * a⁻¹ = v * w := by
    have hmem : a * w * a⁻¹ ∈ Ω := ⟨hRA a ha w hwR, by
      calc a * w * a⁻¹ * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
        _ = 1 := by rw [hww]; group⟩
    rcases hΩdesc _ hmem with h | h | h | h
    · exact absurd (by
        have h1 : a * w = a * 1 := by rw [mul_one]; exact mul_inv_eq_one.1 h
        exact mul_left_cancel h1) hw1
    · exfalso
      apply hav
      apply fix_of_sq_fix hodd hak
      calc a ^ 2 * v * (a ^ 2)⁻¹ = a * (a * v * a⁻¹) * a⁻¹ := by rw [pow_two]; group
        _ = v := by rw [← hw, h]
    · exfalso
      apply hvw
      have h1 : a * w * a⁻¹ = a * v * a⁻¹ := by rw [h, ← hw]
      have h2 : a * w = a * v := mul_right_cancel h1
      exact (mul_left_cancel h2).symm
    · exact h
  have hazv : a * (v * w) * a⁻¹ = v := by
    calc a * (v * w) * a⁻¹ = (a * v * a⁻¹) * (a * w * a⁻¹) := by group
      _ = w * (v * w) := by rw [← hw, hawz]
      _ = (w * v) * w := by group
      _ = (v * w) * w := by rw [← hcvw]
      _ = v * (w * w) := by group
      _ = v := by rw [hww, mul_one]
  haveI hnil : Group.IsNilpotent T := IsPGroup.isNilpotent hT
  have hΩnormal : (Ω.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΩT]
    intro x t hx ht
    exact ⟨hRT' t ht x hx.1, by
      calc t * x * t⁻¹ * (t * x * t⁻¹) = t * (x * x) * t⁻¹ := by group
        _ = 1 := by rw [hx.2]; group⟩
  have hΩne : Ω.subgroupOf T ≠ ⊥ := by
    intro h
    have : (⟨v, hRT hvR⟩ : T) ∈ Ω.subgroupOf T := hvΩ
    rw [h, Subgroup.mem_bot] at this
    exact hv1 (congrArg Subtype.val this)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hΩne)
  have hyΩ : ((y : T) : Γ) ∈ Ω := (Subgroup.mem_inf.1 y.2).1
  have hyc : ∀ t ∈ T, t * ((y : T) : Γ) = ((y : T) : Γ) * t := by
    intro t ht
    have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 y.2).2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hy1' : ((y : T) : Γ) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hcenA : ∀ y : Γ, (∀ t ∈ T, t * y = y * t) →
      ∀ t ∈ T, t * (a * y * a⁻¹) = (a * y * a⁻¹) * t := by
    intro y hy t ht
    have hs := hy (a⁻¹ * t * a) (hnorm'' a ha t ht)
    calc t * (a * y * a⁻¹) = a * ((a⁻¹ * t * a) * y) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * t * a)) * a⁻¹ := by rw [hs]
      _ = (a * y * a⁻¹) * t := by group
  have hcentv : ∀ t ∈ T, t * v = v * t := by
    rcases hΩdesc _ hyΩ with h | h | h | h
    · exact absurd h hy1'
    · rw [← h]; exact hyc
    · have h0 : ∀ t ∈ T, t * w = w * t := by rw [← h]; exact hyc
      have h1 : ∀ t ∈ T, t * (v * w) = (v * w) * t := by
        have := hcenA w h0
        rw [hawz] at this
        exact this
      have h2 := hcenA (v * w) h1
      rw [hazv] at h2
      exact h2
    · have h0 : ∀ t ∈ T, t * (v * w) = (v * w) * t := by rw [← h]; exact hyc
      have h2 := hcenA (v * w) h0
      rw [hazv] at h2
      exact h2
  have hcentw : ∀ t ∈ T, t * w = w * t := hcenA v hcentv
  have hTcomm := comm_of_central_involutions hF (t := (⟨v, hRT hvR⟩ : T)) (u := (⟨w, hRT hwR⟩ : T))
    (Subtype.ext hvv) (Subtype.ext hww) (fun h => hv1 (congrArg Subtype.val h))
    (fun h => hw1 (congrArg Subtype.val h)) (fun h => hvw (congrArg Subtype.val h))
    (fun p => Subtype.ext (hcentv p.1 p.2)) (fun p => Subtype.ext (hcentw p.1 p.2))
  have hRbot : R = ⊥ := by
    rw [hRdef, eq_bot_iff, Subgroup.commutator_le]
    intro g hg h hh
    rw [Subgroup.mem_bot]
    have := hTcomm ⟨g, hg⟩ ⟨h, hh⟩
    have h2 : g * h = h * g := congrArg Subtype.val this
    rw [commutatorElement_def, h2]
    group
  rw [hRbot, Subgroup.mem_bot] at hvR
  exact hv1 hvR

@[expose] def OutInner (S : Type*) [Group S] : Prop :=
  ∀ A T : Subgroup (MulAut S), IsPGroup 3 A → IsPGroup 2 T →
    A ≤ Subgroup.normalizer (T : Set (MulAut S)) → ⁅A, T⁆ = T →
    T ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S

theorem OutInner.of_mulEquiv {S P : Type*} [Group S] [Group P] (e : S ≃* P) (h : OutInner P) :
    OutInner S := by
  intro A T hA hT hN hAT
  let φ : MulAut S ≃* MulAut P := MulAut.congr e
  have hN' : A.map φ.toMonoidHom ≤ Subgroup.normalizer
      ((T.map φ.toMonoidHom : Subgroup (MulAut P)) : Set (MulAut P)) :=
    (Subgroup.map_mono (f := φ.toMonoidHom) hN).trans (Subgroup.le_normalizer_map φ.toMonoidHom)
  have hAT' : (⁅A.map φ.toMonoidHom, T.map φ.toMonoidHom⁆ : Subgroup (MulAut P)) =
      T.map φ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hAT]
  have hle := h _ _ (hA.map φ.toMonoidHom) (hT.map φ.toMonoidHom) hN' hAT'
  intro x hx
  have hx' : φ x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P :=
    hle ⟨x, hx, rfl⟩
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have : y = x := φ.injective hyx
  exact this ▸ hy

theorem comm_mem_of_cyc {G : Type*} [Group G] (E D : Subgroup G) [D.Normal]
    (hcyc : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) :
    ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ D := by
  obtain ⟨g, -, hcyc⟩ := hcyc
  intro x hx y hy
  have key : ∀ z ∈ E, ∃ k : ℤ, (z : G ⧸ D) = (g : G ⧸ D) ^ k := by
    intro z hz
    obtain ⟨k, hk⟩ := hcyc z hz
    refine ⟨-k, ?_⟩
    have h1 : ((g ^ k * z : G) : G ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).2 hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨k, hk⟩ := key x hx
  obtain ⟨l, hl⟩ := key y hy
  have h1 : (QuotientGroup.mk' D) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    change Commute (x : G ⧸ D) (y : G ⧸ D)
    rw [hk, hl]
    exact Commute.zpow_zpow_self _ _ _
  exact (QuotientGroup.eq_one_iff _).1 h1

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem outInner_projectiveSL {K : Type} [Field K] [Finite K] : OutInner (projectiveSL 3 K) := by
  intro A T hA hT hN hAT
  obtain ⟨hgen, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨-, -, hDN, hEN, -, hEcyc, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  rw [hgen] at hDN hEN hidx
  have hDnorm : (linearAutGroup 3 K).Normal :=
    ⟨fun n hn g => (Subgroup.normal_subgroupOf_iff le_top).1 hDN n g hn (Subgroup.mem_top g)⟩
  have hEnorm : (semilinearAutGroup 3 K).Normal :=
    ⟨fun n hn g => (Subgroup.normal_subgroupOf_iff le_top).1 hEN n g hn (Subgroup.mem_top g)⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right] at hidx
  have hsq : ∀ x : MulAut (projectiveSL 3 K), x ^ 2 ∈ semilinearAutGroup 3 K := by
    intro x
    have hne : (semilinearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 := Subgroup.pow_index_mem (semilinearAutGroup 3 K) x
    interval_cases hi : (semilinearAutGroup 3 K).index
    · exact absurd rfl hne
    · rw [pow_one] at h1
      rw [pow_two]
      exact mul_mem h1 h1
    · exact h1
  have hAE : ∀ a ∈ A, a ∈ semilinearAutGroup 3 K := by
    intro a ha
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    have hak : a ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨r, hr⟩ := hodd
    have hea : (a ^ 2) ^ (r + 1) = a := by
      rw [← pow_mul, show 2 * (r + 1) = 3 ^ k + 1 by omega, pow_succ, hak, one_mul]
    rw [← hea]
    exact Subgroup.pow_mem _ (hsq a) _
  have hTE : T ≤ semilinearAutGroup 3 K := by
    rw [← hAT, Subgroup.commutator_le]
    intro a ha t _
    have h1 : t * a⁻¹ * t⁻¹ ∈ semilinearAutGroup 3 K :=
      hEnorm.conj_mem a⁻¹ (inv_mem (hAE a ha)) t
    have : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem (hAE a ha) h1
  have hTD : T ≤ linearAutGroup 3 K := by
    have := comm_mem_of_cyc (semilinearAutGroup 3 K) (linearAutGroup 3 K) hEcyc
    rw [← hAT, Subgroup.commutator_le]
    intro a ha t ht
    exact this a (hAE a ha) t (hTE ht)
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact mem_range_conj_of_mem_linearAutGroup_of_coprime (hTD ht)
    (Nat.Coprime.pow_left k (by norm_num)) htk

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem outInner_primeFormP {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : ¬(3 = 3 ∧ p ^ f = 2)) :
    OutInner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  intro A T hA hT hN hAT
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC (le_refl 3) hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (le_refl 3) hq
  have hring : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hRcomm : ∀ a b : K ≃+* K, Commute a b := fun a b => by
    have : IsMulCommutative (RingAut K) := hring.isMulCommutative
    exact this.is_comm.comm a b
  set Φ := primeFormFieldFactor h hC (le_refl 3) hq with hΦ
  set D := primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
  have hTD : T ≤ D := by
    have hle : ⁅A, T⁆ ≤ Φ.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hRcomm _ _
    rw [← hFker, ← hAT]
    exact hle
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner
    (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) with hI
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  set x : D := ⟨t, hTD ht⟩ with hx
  have h3 : (QuotientGroup.mk x : D ⧸ I.subgroupOf D) ^ 3 = 1 := by
    have hdvd : Nat.card (D ⧸ I.subgroupOf D) ∣ 3 := by
      rw [hcard]; exact Nat.gcd_dvd_left _ _
    obtain ⟨c, hc⟩ := hdvd
    have h1 : (QuotientGroup.mk x : D ⧸ I.subgroupOf D) ^ (Nat.card (D ⧸ I.subgroupOf D) * c) =
        1 := by
      rw [pow_mul, pow_card_eq_one', one_pow]
    rw [← hc] at h1
    exact h1
  have h2 : (QuotientGroup.mk x : D ⧸ I.subgroupOf D) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ (2 ^ k) = 1 := Subtype.ext htk
    rw [this, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk x : D ⧸ I.subgroupOf D) = 1 :=
    CFSG.RankThree.SubgroupLists.eq_one_of_pow_three_of_pow h3
      (Nat.Coprime.pow_left k (by norm_num)) h2
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem sl3Faithful_of_model {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (H : Subgroup (GL (Fin 3) K))
    (hdet : ∀ x ∈ H, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {S : Type} [Group S] (e : S ≃* StatedProj H) (T₀ : Subgroup S) (hT₀ : IsPGroup 2 T₀) :
    SL3Faithful T₀ := by
  let π : H →* StatedProj H := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ g ∈ π.ker, g ^ 3 = 1 := by
    intro g hg
    have hg' : (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
      have h1 : g ∈ (StatedScalars (Fin 3) K).subgroupOf H :=
        (QuotientGroup.eq_one_iff g).1 (MonoidHom.mem_ker.1 hg)
      exact h1
    obtain ⟨c, hc⟩ := hg'
    have hdet' := hdet g g.2
    rw [← hc] at hdet'
    have hc3 : (c : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K))
        (Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) c)
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin,
        Units.val_pow_eq_pow_val] at this
      rw [← this]; exact hdet'
    have hc3' : c ^ 3 = 1 := Units.ext (by simpa using hc3)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3', map_one]
    rfl
  obtain ⟨ι, hι⟩ := exists_section π hπ hker (T₀.map e.toMonoidHom) (hT₀.map e.toMonoidHom)
  have hιinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    have := congrArg π hab
    rw [hι, hι] at this
    exact this
  have hF1 : SL3Faithful (T₀.map e.toMonoidHom) :=
    ⟨K, inferInstance, h2, H.subtype.comp ι, H.subtype_injective.comp hιinj,
      fun x => hdet _ (ι x).2⟩
  let eT : T₀ ≃* T₀.map e.toMonoidHom := T₀.equivMapOfInjective e.toMonoidHom e.injective
  exact SL3Faithful.of_injective eT.toMonoidHom eT.injective hF1

theorem sl3Faithful_of_le_inner {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hS2 : ∀ T₀ : Subgroup S, IsPGroup 2 T₀ → SL3Faithful T₀)
    (T : Subgroup (MulAut S)) (hT : IsPGroup 2 T)
    (hle : T ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S) : SL3Faithful T := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
  · have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxc : x ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut S => φ g) hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * x = (x * g * x⁻¹) * x := by rw [this]
          _ = x * g := by group
      rw [hc] at hxc
      exact (Subgroup.mem_bot).1 hxc
    let T₀ : Subgroup S := T.comap (MulAut.conj : S →* MulAut S)
    have hT₀ : IsPGroup 2 T₀ := hT.comap_of_injective _ hinj
    have hmap : T₀.map (MulAut.conj : S →* MulAut S) = T := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hle
    let eT : T₀ ≃* T :=
      (T₀.equivMapOfInjective (MulAut.conj : S →* MulAut S) hinj).trans
        (MulEquiv.subgroupCongr hmap)
    exact SL3Faithful.of_injective eT.symm.toMonoidHom eT.symm.injective (hS2 T₀ hT₀)
  · have hbot : T = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      obtain ⟨s, rfl⟩ := hle ht
      rw [Subgroup.mem_bot]
      ext g
      have hs : s ∈ Subgroup.center S := by rw [hc]; exact Subgroup.mem_top s
      have := Subgroup.mem_center_iff.1 hs g
      simp only [MulAut.conj_apply, MulAut.one_apply]
      calc s * g * s⁻¹ = (g * s) * s⁻¹ := by rw [this]
        _ = g := by group
    subst hbot
    exact ⟨ℚ, inferInstance, by norm_num, 1, fun a b _ => Subsingleton.elim a b, fun x => by simp⟩

@[expose] def L3Model (S : Type) [Group S] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 6 = 1 ∧
      Nonempty (S ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (p f : ℕ), p.Prime ∧ 1 ≤ f ∧ p ^ f % 6 = 5 ∧
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 3 (p ^ f) K)))

theorem k3Lie_cases {ld : TauCeti.LieTypeIndex} (h : k3Lie ld) :
    (∃ q : TauCeti.PrimePower, ld = .A 2 q ∧ q.card % 6 = 1) ∨
      (∃ q : TauCeti.PrimePower, ld = .twistedA 2 q ∧ q.card % 6 = 5) := by
  cases ld with
  | A n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact Or.inl ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | twistedA n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact Or.inr ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | _ => exact (show False from h).elim

theorem l3Model_of_catalogIs {S : Type} [Group S] (h : catalogIs S (onLie k3Lie)) :
    L3Model S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic n hn => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    have hk : k3Lie ld := hi
    rcases k3Lie_cases hk with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
    · left
      have hm := CFSG.Models.lieModel_A 2 q hv e
      obtain ⟨-, K, hK, hKf, hKc, ⟨e'⟩⟩ :=
        CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm
      refine ⟨K, hK, hKf, ?_, ⟨e'⟩⟩
      rw [hKc, ← TauCeti.PrimePower.card_def]
      exact hq
    · right
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA 2 q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
      have hm := CFSG.Models.lieModel_twistedA 2 q hv e
      rw [hc, hf] at hm
      obtain ⟨⟨hp, hf1, -⟩, K, hK, hKf, hKc, ⟨e'⟩⟩ :=
        CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hm
      refine ⟨K, hK, hKf, q.p, q.exponent, hp, hf1, ?_, hKc, ⟨e'⟩⟩
      rw [← TauCeti.PrimePower.card_def]
      exact hq

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem outInner_of_l3Model {S : Type} [Group S] (h : L3Model S) : OutInner S := by
  rcases h with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · let e' : S ≃* LinearFlag.projectiveSL 3 K :=
      e.trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
          (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 K)).symm)
    exact OutInner.of_mulEquiv e' outInner_projectiveSL
  · have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun h' => by omega
    have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
    obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (le_refl 3) hq
    let e' := (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm).trans
      eT.symm
    exact OutInner.of_mulEquiv e' (outInner_primeFormP hU hq)

theorem sl3Faithful_of_l3Model {S : Type} [Group S] (h : L3Model S) :
    ∀ T₀ : Subgroup S, IsPGroup 2 T₀ → SL3Faithful T₀ := by
  intro T₀ hT₀
  rcases h with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (by omega)
    exact sl3Faithful_of_model (CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd)
      (StatedSL 3 K) (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL hx) e T₀ hT₀
  · have hodd : Odd (Nat.card K) := by
      rw [hcard]; exact Odd.pow (Nat.odd_iff.2 (by omega))
    exact sl3Faithful_of_model (CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd)
      (StatedSU 3 (p ^ f) K) (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU hx) e T₀ hT₀

end KD2027Aux

open KD2027Aux in
theorem kd2027_holds : KD2027 := by
  intro S _ _ hS hcat A T hA hT hN hAT
  have hmodel := l3Model_of_catalogIs hcat
  have hinner := outInner_of_l3Model hmodel A T hA hT hN hAT
  have hF := sl3Faithful_of_le_inner hS (sl3Faithful_of_l3Model hmodel) T hT hinner
  exact kd2027_abs A T hA hT hN hAT hF

end CFSG.LocalAnalysis.GLTheoremA
