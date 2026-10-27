module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCaseAPropB
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCaseB

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

theorem five_le_of_isPerfect_sl {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (hq : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))) : 5 ≤ p ^ n := by
  have h3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hodd : Odd (p ^ n) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
  have hle : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  by_contra hlt
  have h3eq : p ^ n = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hp3 : p = 3 := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ p) hn
    omega
  subst hp3
  have hn1 : n = 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hn1
  let _ : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = Fintype.card (ZMod 3) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 1 one_ne_zero, ZMod.card]
    norm_num
  let e := specialLinearTwoRingEquiv (FiniteField.ringEquivOfCardEq hcard)
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) := hq
  exact not_isPerfect_sl2Three (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem isQuasisimple_sl_two {F : Type*} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hsimple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≤
      center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center _)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (center _)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hperf.commutator_eq_top] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    center (Matrix.SpecialLinearGroup (Fin 2) F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (mem_top _)))

theorem pPrimeCore_eq_bot_of_mulEquiv_sl {T : Type*} [Group T] [Finite T] {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n) (e : T ≃* SL(2, GaloisField p n)) :
    pPrimeCore 2 T = ⊥ := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hn]
    omega
  have hq : IsQuasisimple T := LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl_two h4)
  have hF : Odd (Nat.card (GaloisField p n)) := by
    rw [GaloisField.card p n hn]
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hZ : Nat.card (center T) = 2 := by
    have h1 : Nat.card ((center T).map e.toMonoidHom) = Nat.card (center T) :=
      card_map_of_injective (by exact e.injective)
    rw [map_center_mulEquiv e] at h1
    rw [← h1]
    exact ABGLocalTools.card_center_sl2 hF
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 T)) := pPrimeCore_coprime_card
  have : (pPrimeCore 2 T).Normal := pPrimeCore_normal
  rcases Quasisimple.normal_le_center_or_eq_top ⟨hq.1.commutator_eq_top, hq.2.1⟩
      (pPrimeCore 2 T) with hle | htop
  · have hd : Nat.card (pPrimeCore 2 T) ∣ 2 := by
      have h1 := card_dvd_of_le hle
      rwa [hZ] at h1
    rw [← card_eq_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hcop
      norm_num at hcop
  · exfalso
    have hd : 2 ∣ Nat.card T := by
      have h1 := card_subgroup_dvd_card (center T)
      rwa [hZ] at h1
    rw [htop, card_top] at hcop
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hd hcop

theorem exists_central_involution {Q : Type*} [Group Q] {S : Subgroup Q} {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (e : S ≃* SL(2, GaloisField p n)) :
    ∃ z ∈ S, orderOf z = 2 ∧ z ≠ 1 ∧ (∀ x ∈ S, z * x = x * z) ∧
      ∀ y ∈ S, (∀ x ∈ S, y * x = x * y) → y = 1 ∨ y = z := by
  have hF : Odd (Nat.card (GaloisField p n)) := by
    rw [GaloisField.card p n hn.ne']
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hcard : Nat.card (center S) = 2 := by
    have h1 : Nat.card ((center S).map e.toMonoidHom) = Nat.card (center S) :=
      card_map_of_injective (by exact e.injective)
    rw [map_center_mulEquiv e] at h1
    rw [← h1]
    exact ABGLocalTools.card_center_sl2 hF
  obtain ⟨z₀, hz₀, hz₀all⟩ := exists_involution_of_card_eq_two hcard
  refine ⟨((z₀ : S) : Q), (z₀ : S).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz₀
  · intro h
    have h1 : z₀ = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz₀
    omega
  · intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp z₀.2 ⟨x, hx⟩).symm
  · intro y hy hyc
    have hyC : (⟨y, hy⟩ : S) ∈ center S := by
      rw [mem_center_iff]
      intro x
      exact Subtype.ext (hyc x x.2).symm
    rcases hz₀all ⟨⟨y, hy⟩, hyC⟩ with h | h
    · left
      exact congrArg (fun c : center S => ((c : S) : Q)) h
    · right
      exact congrArg (fun c : center S => ((c : S) : Q)) h

theorem fixed_of_unique_central {Q : Type*} [Group Q] {S : Subgroup Q} {z : Q} (hzS : z ∈ S)
    (hz1 : z ≠ 1) (hzc : ∀ x ∈ S, z * x = x * z)
    (hzu : ∀ y ∈ S, (∀ x ∈ S, y * x = x * y) → y = 1 ∨ y = z) (φ : MulAut Q)
    (hφS : ∀ x ∈ S, φ x ∈ S) (hφφ : ∀ x, φ (φ x) = x) : φ z = z := by
  rcases hzu (φ z) (hφS z hzS) (fun x hx => by
      calc φ z * x = φ z * φ (φ x) := by rw [hφφ]
        _ = φ (z * φ x) := by rw [map_mul]
        _ = φ (φ x * z) := by rw [hzc _ (hφS x hx)]
        _ = φ (φ x) * φ z := by rw [map_mul]
        _ = x * φ z := by rw [hφφ]) with h | h
  · exact absurd (φ.injective (h.trans (map_one φ).symm)) hz1
  · exact h

theorem eq_of_mem_sup_zpowers {G : Type*} [Group G] {u c : G} (hu : u ^ 2 = 1)
    (hc : c ^ 2 = 1) (huc : u * c = c * u) {x : G} (hx : x ∈ zpowers u ⊔ zpowers c) :
    x = 1 ∨ x = u ∨ x = c ∨ x = u * c := by
  have hcomm : ∀ h ∈ zpowers c, u * h * u⁻¹ = h := by
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    rw [(Commute.zpow_right (show Commute u c from huc) k).eq, mul_inv_cancel_right]
  have hle : zpowers u ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rwa [hcomm h hh]
    · intro hh
      have h1 := hcomm _ hh
      have h2 : u * h * u⁻¹ = h := by
        calc u * h * u⁻¹ = u⁻¹ * (u * (u * h * u⁻¹) * u⁻¹) * u := by group
          _ = u⁻¹ * (u * h * u⁻¹) * u := by rw [h1]
          _ = h := by group
      rwa [h2] at hh
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨y, hy, w, hw, rfl⟩ := hx
  rcases eq_one_or_eq_of_mem_zpowers hu hy with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers hc hw with rfl | rfl <;> simp

theorem mem_triple_of_klein {G : Type*} [Group G] {u c z₁ z₂ : G} (hc : c ^ 2 = 1)
    (huc : u * c = c * u) (h₁ : z₁ = 1 ∨ z₁ = u ∨ z₁ = c ∨ z₁ = u * c)
    (h₂ : z₂ = 1 ∨ z₂ = u ∨ z₂ = c ∨ z₂ = u * c) (h₁1 : z₁ ≠ 1) (h₂1 : z₂ ≠ 1)
    (h12 : z₁ ≠ z₂) : z₁ = u ∨ z₂ = u ∨ z₁ * z₂ = u := by
  have hcc : c * c = 1 := by rw [← pow_two, hc]
  rcases h₁ with h₁ | h₁ | h₁ | h₁
  · exact absurd h₁ h₁1
  · exact .inl h₁
  all_goals rcases h₂ with h₂ | h₂ | h₂ | h₂
  all_goals first
    | exact absurd h₂ h₂1
    | exact .inr (.inl h₂)
    | exact absurd (h₁.trans h₂.symm) h12
    | skip
  · refine .inr (.inr ?_)
    rw [h₁, h₂]
    calc c * (u * c) = c * (c * u) := by rw [huc]
      _ = c * c * u := by group
      _ = u := by rw [hcc, one_mul]
  · refine .inr (.inr ?_)
    rw [h₁, h₂]
    calc u * c * c = u * (c * c) := by group
      _ = u := by rw [hcc, mul_one]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem centralizer_inf_eq_of_mem_triple {δ γ w₁ w₂ : X} (hδ : δ * δ = 1) (hγ : γ * γ = 1)
    (hw₁ : w₁ = δ ∨ w₁ = γ ∨ w₁ = δ * γ) (hw₂ : w₂ = δ ∨ w₂ = γ ∨ w₂ = δ * γ) (hne : w₁ ≠ w₂) :
    centralizer ({w₂} : Set X) ⊓ centralizer ({w₁} : Set X) =
      centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  have key : ∀ w, (w = δ ∨ w = γ ∨ w = δ * γ) → x * γ = γ * x → x * δ = δ * x →
      x * w = w * x := by
    intro w hw h1 h2
    rcases hw with rfl | rfl | rfl
    · exact h2
    · exact h1
    · exact ((show Commute x δ from h2).mul_right (show Commute x γ from h1)).eq
  have hγ' : δ * (δ * γ) = γ := by rw [← mul_assoc, hδ, one_mul]
  have hδ' : δ * γ * γ = δ := by rw [mul_assoc, hγ, mul_one]
  constructor
  · rintro ⟨h2, h1⟩
    have c1 : Commute x w₁ := h1
    have c2 : Commute x w₂ := h2
    have hfin : Commute x γ ∧ Commute x δ := by
      rcases hw₁ with e₁ | e₁ | e₁ <;> rcases hw₂ with e₂ | e₂ | e₂ <;> rw [e₁] at c1 <;>
        rw [e₂] at c2
      · exact absurd (e₁.trans e₂.symm) hne
      · exact ⟨c2, c1⟩
      · exact ⟨by rw [← hγ']; exact c1.mul_right c2, c1⟩
      · exact ⟨c1, c2⟩
      · exact absurd (e₁.trans e₂.symm) hne
      · exact ⟨c1, by rw [← hδ']; exact c2.mul_right c1⟩
      · exact ⟨by rw [← hγ']; exact c2.mul_right c1, c2⟩
      · exact ⟨c2, by rw [← hδ']; exact c1.mul_right c2⟩
      · exact absurd (e₁.trans e₂.symm) hne
    exact ⟨hfin.1.eq, hfin.2.eq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨key w₂ hw₂ h1 h2, key w₁ hw₁ h1 h2⟩

omit [Finite X] in
theorem commute_of_mem_triple {δ γ w : X} (hδγ : δ * γ = γ * δ)
    (hw : w = δ ∨ w = γ ∨ w = δ * γ) : Commute w δ ∧ Commute w γ := by
  have h : Commute δ γ := hδγ
  rcases hw with rfl | rfl | rfl
  · exact ⟨Commute.refl _, h⟩
  · exact ⟨h.symm, Commute.refl _⟩
  · exact ⟨(Commute.refl δ).mul_left h.symm, h.mul_left (Commute.refl γ)⟩

omit [Finite X] in
theorem commute_triple_of_commute {δ γ w g : X} (hw : w = δ ∨ w = γ ∨ w = δ * γ)
    (hgδ : Commute g δ) (hgγ : Commute g γ) : Commute g w := by
  rcases hw with rfl | rfl | rfl
  · exact hgδ
  · exact hgγ
  · exact hgδ.mul_right hgγ

omit [Finite X] in
theorem sq_eq_one_of_mem_triple {δ γ w : X} (hδ : δ * δ = 1) (hγ : γ * γ = 1)
    (hδγ : δ * γ = γ * δ) (hw : w = δ ∨ w = γ ∨ w = δ * γ) : w ^ 2 = 1 := by
  rw [pow_two]
  rcases hw with rfl | rfl | rfl
  · exact hδ
  · exact hγ
  · calc δ * γ * (δ * γ) = δ * (γ * δ) * γ := by group
      _ = δ * (δ * γ) * γ := by rw [hδγ]
      _ = (δ * δ) * (γ * γ) := by group
      _ = 1 := by rw [hδ, hγ, one_mul]

theorem mem_normalizer_of_forall_conj {N : Subgroup X} {g : X}
    (h : ∀ x ∈ N, g * x * g⁻¹ ∈ N) : g ∈ normalizer (N : Set X) := by
  have hle : N.map (MulAut.conj g).toMonoidHom ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (N.map (MulAut.conj g).toMonoidHom) = Nat.card N :=
    card_map_of_injective (by exact (MulAut.conj g).injective)
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle hcard.ge)

omit [Finite X] in
theorem conjugate_le_of_le_of_mem {E K : Subgroup X} {g : X} (hE : E ≤ K) (hg : g ∈ K) :
    conjugate E g ≤ K := by
  intro x hx
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hE hx)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

omit [Finite X] in
theorem mem_oddCoreIn_iff_mk {M : Subgroup X} (m : M) :
    (m : X) ∈ oddCoreIn M ↔ (m : M ⧸ pPrimeCore 2 M) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨o, ho, hom⟩
    rwa [← Subtype.ext hom]
  · intro h
    exact ⟨m, h, rfl⟩

theorem mem_of_mem_quotImage {M N : Subgroup X} {w : X} (hwM : w ∈ M) (hw : w ^ 2 = 1)
    (hwN : ∀ n ∈ N, n * w = w * n)
    (hq : ((⟨w, hwM⟩ : M) : M ⧸ pPrimeCore 2 M) ∈ quotImage M N) : w ∈ N := by
  obtain ⟨m, hm, hmw⟩ := hq
  have h1 : m⁻¹ * ⟨w, hwM⟩ ∈ pPrimeCore 2 M := QuotientGroup.eq.mp hmw
  have hodd : Odd (orderOf ((m : X)⁻¹ * w)) := by
    have h2 : orderOf (⟨m⁻¹ * ⟨w, hwM⟩, h1⟩ : pPrimeCore 2 M) ∣ Nat.card (pPrimeCore 2 M) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h2
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h2
  exact mem_of_eq_mul_of_odd' hw (show (m : X) ∈ N from hm) (by group) hodd (hwN _ hm)

theorem forall_fixed_of_trivial {M S : Subgroup X} (hSM : S ≤ M) {g : X}
    (hgM : g ∈ normalizer (M : Set X)) (hgS : g ∈ normalizer (S : Set X))
    (hO : pPrimeCore 2 (quotImage M S) = ⊥) (h : ∀ x ∈ S, ⁅x, g⁆ ∈ oddCoreIn S) :
    ∀ q ∈ quotImage M S, oddQuotAction M ⟨g, hgM⟩ q = q := by
  intro q hq
  have h1 := (forall_quotImage_iff hSM hgM hgS).mpr h q hq
  rw [hO, Subgroup.map_bot, mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem exists_inf_centralizer_hom {M : Subgroup X} {b : X} (hbM : b ∈ normalizer (M : Set X))
    (hb : b * b = 1) :
    ∃ f : ↥(M ⊓ centralizer ({b} : Set X)) →* autFixed (oddQuotAction M ⟨b, hbM⟩),
      Function.Surjective f ∧ ¬ 2 ∣ Nat.card f.ker ∧
      ∀ x : ↥(M ⊓ centralizer ({b} : Set X)),
        (f x : M ⧸ pPrimeCore 2 M) = ((⟨x, (mem_inf.mp x.2).1⟩ : M) : M ⧸ pPrimeCore 2 M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : MulAut M := M.normalizerMonoidHom ⟨b, hbM⟩ with hσ
  have hσv : ∀ m : M, ((σ m : M) : X) = b * m * b⁻¹ := fun m => rfl
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [MulAut.mul_apply, hσv, hσv, MulAut.one_apply]
    calc b * (b * (m : X) * b⁻¹) * b⁻¹ = (b * b) * m * (b * b)⁻¹ := by group
      _ = m := by rw [hb]; group
  let f : ↥(M ⊓ centralizer ({b} : Set X)) →* autFixed (oddQuotAction M ⟨b, hbM⟩) :=
    { toFun := fun x => ⟨((⟨x, (mem_inf.mp x.2).1⟩ : M) : M ⧸ pPrimeCore 2 M), by
        change oddQuotAction M ⟨b, hbM⟩ _ = _
        rw [oddQuotAction_mk]
        congr 1
        apply Subtype.ext
        change b * (x : X) * b⁻¹ = x
        rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2]
        group⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨f, ?_, ?_, fun x => rfl⟩
  · rintro ⟨q, hq⟩
    obtain ⟨k, hk, hkq⟩ := autFixed_quotAutOfChar_surjective σ hσσ q hq
    have hkb : (k : X) ∈ centralizer ({b} : Set X) := by
      have h1 : ((σ k : M) : X) = k := congrArg Subtype.val hk
      rw [hσv] at h1
      rw [mem_centralizer_singleton_iff]
      calc (k : X) * b = (b * k * b⁻¹) * b := by rw [h1]
        _ = b * k := by group
    exact ⟨⟨k, mem_inf.mpr ⟨k.2, hkb⟩⟩, Subtype.ext hkq⟩
  · let ι : f.ker →* pPrimeCore 2 M :=
      { toFun := fun x => ⟨⟨((x : ↥(M ⊓ centralizer ({b} : Set X))) : X),
          (mem_inf.mp (x : ↥(M ⊓ centralizer ({b} : Set X))).2).1⟩, by
          have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact (QuotientGroup.eq_one_iff _).mp h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' := congrArg (fun z : pPrimeCore 2 M => ((z : M) : X)) h
      exact Subtype.ext (Subtype.ext h')
    intro h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
      (h2.trans (Subgroup.card_dvd_of_injective ι hι)) (pPrimeCore_coprime_card (p := 2))

theorem exists_isPComponent_of_autFixed {M : Subgroup X} {b : X}
    (hbM : b ∈ normalizer (M : Set X)) (hb : b * b = 1)
    {T : Subgroup (M ⧸ pPrimeCore 2 M)} (hT : T ≤ autFixed (oddQuotAction M ⟨b, hbM⟩))
    (hTc : IsPComponent 2 (T.subgroupOf (autFixed (oddQuotAction M ⟨b, hbM⟩)))) :
    ∃ N : Subgroup X, N ≤ M ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (M ⊓ centralizer ({b} : Set X))) ∧ quotImage M N = T ∧
      ∀ g : X, ∀ hgM : g ∈ normalizer (M : Set X), g * b = b * g →
        (∀ x ∈ T, oddQuotAction M ⟨g, hgM⟩ x ∈ T) → g ∈ normalizer (N : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hker, hfv⟩ := exists_inf_centralizer_hom hbM hb
  set s : Set ↥(M ⊓ centralizer ({b} : Set X)) :=
    {x | x ∈ (T.subgroupOf (autFixed (oddQuotAction M ⟨b, hbM⟩))).comap f ∧
      ∃ k : ℕ, orderOf x = 2 ^ k} with hs
  obtain ⟨hN₀, hN₀f⟩ := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf
    hker).2.1 _ hTc
  refine ⟨(closure s).map (M ⊓ centralizer ({b} : Set X)).subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [show ((closure s).map (M ⊓ centralizer ({b} : Set X)).subtype).subgroupOf
        (M ⊓ centralizer ({b} : Set X)) = closure s from
      comap_map_eq_self_of_injective (M ⊓ centralizer ({b} : Set X)).subtype_injective _]
    exact hN₀
  · ext q
    constructor
    · rintro ⟨m, ⟨c, hc, hcm⟩, rfl⟩
      have h1 : f c ∈ (closure s).map f := mem_map_of_mem f hc
      rw [hN₀f] at h1
      have h2 : ((f c : autFixed (oddQuotAction M ⟨b, hbM⟩)) : M ⧸ pPrimeCore 2 M) ∈ T := h1
      rw [hfv] at h2
      have hm' : (⟨c, (mem_inf.mp c.2).1⟩ : M) = m := Subtype.ext hcm
      rw [hm'] at h2
      exact h2
    · intro hq
      have h1 : (⟨q, hT hq⟩ : autFixed (oddQuotAction M ⟨b, hbM⟩)) ∈ (closure s).map f := by
        rw [hN₀f]
        exact hq
      obtain ⟨c, hc, hcq⟩ := h1
      refine ⟨⟨c, (mem_inf.mp c.2).1⟩, ⟨c, hc, rfl⟩, ?_⟩
      have h2 := congrArg Subtype.val hcq
      rw [hfv] at h2
      exact h2
  · intro g hgM hgb hgT
    apply mem_normalizer_of_forall_conj
    have hle : closure s ≤ ((closure s).map (M ⊓ centralizer ({b} : Set X)).subtype).comap
        ((MulAut.conj g).toMonoidHom.comp (M ⊓ centralizer ({b} : Set X)).subtype) := by
      rw [closure_le]
      intro y hy
      obtain ⟨hyT, k, hyk⟩ := hy
      have hgyM : g * (y : X) * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM _).mp (mem_inf.mp y.2).1
      have hgyb : g * (y : X) * g⁻¹ ∈ centralizer ({b} : Set X) := by
        have hgb' : Commute b g := (show Commute g b from hgb).symm
        have hyb : Commute b (y : X) :=
          (show Commute (y : X) b from mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2).symm
        rw [mem_centralizer_singleton_iff]
        exact ((hgb'.mul_right hyb).mul_right hgb'.inv_right).eq.symm
      have hmem : (⟨g * y * g⁻¹, mem_inf.mpr ⟨hgyM, hgyb⟩⟩ : ↥(M ⊓ centralizer ({b} : Set X))) ∈
          s := by
        refine ⟨?_, k, ?_⟩
        · change ((f ⟨g * y * g⁻¹, mem_inf.mpr ⟨hgyM, hgyb⟩⟩ :
            autFixed (oddQuotAction M ⟨b, hbM⟩)) : M ⧸ pPrimeCore 2 M) ∈ T
          rw [hfv]
          have h1 : ((f y : autFixed (oddQuotAction M ⟨b, hbM⟩)) : M ⧸ pPrimeCore 2 M) ∈ T := hyT
          rw [hfv] at h1
          have h2 := hgT _ h1
          rw [oddQuotAction_mk] at h2
          exact h2
        · have h1 := MulEquiv.orderOf_eq (MulAut.conj g) (y : X)
          rw [MulAut.conj_apply] at h1
          rw [Subgroup.orderOf_mk, h1, Subgroup.orderOf_coe, hyk]
      exact ⟨_, subset_closure hmem, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy

theorem isPComponent_inf_centralizer {γ δ : X} {M N : Subgroup X}
    (hM : M ≤ centralizer ({γ} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))))
    (hN : N ≤ M ⊓ centralizer ({δ} : Set X))
    (hNc : IsPComponent 2 (N.subgroupOf (M ⊓ centralizer ({δ} : Set X)))) :
    N ≤ centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X) with hH
  set Y := M ⊓ centralizer ({δ} : Set X) with hY
  have hYH : Y ≤ H := inf_le_inf_right _ hM
  refine ⟨hN.trans hYH, ?_⟩
  have hMsub := (isPComponent_data hM hMc).1
  have hYsub : (Y.subgroupOf H).IsSubnormal := by
    have h1 := hMsub.subgroupOf (K := H.subgroupOf (centralizer ({γ} : Set X)))
    have heq : Y.subgroupOf H = ((M.subgroupOf (centralizer ({γ} : Set X))).subgroupOf
        (H.subgroupOf (centralizer ({γ} : Set X)))).comap
          (subgroupOfEquivOfLe (inf_le_left : H ≤ centralizer ({γ} : Set X))).symm.toMonoidHom := by
      ext x
      change (x : X) ∈ M ⊓ centralizer ({δ} : Set X) ↔ (x : X) ∈ M
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
    rw [heq]
    exact h1.comap _
  rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hYH 2 Nat.prime_two] at hNc
  exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (N.subgroupOf H)
    (Y.subgroupOf H) (fun _ hx => hN hx) hYsub).mp hNc

theorem lift_component {a γ δ : X} {M E : Subgroup X} (ha : orderOf a = 2)
    (hM : M ≤ centralizer ({γ} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))))
    (hδM : δ ∈ M) (hδ : δ * δ = 1) (hδa : δ * a = a * δ)
    (haM : a ∈ normalizer (M : Set X)) (hEa : E ≤ oddCentralizerCore a)
    (hEM : E ≤ normalizer (M : Set X)) {T : Subgroup (M ⧸ pPrimeCore 2 M)}
    (hT : T ≤ centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set (M ⧸ pPrimeCore 2 M)))
    (hTc : IsPComponent 2 (T.subgroupOf
      (centralizer ({((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M)} : Set (M ⧸ pPrimeCore 2 M)))))
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (eT : T ≃* SL(2, GaloisField p n))
    (haT : ∀ x ∈ T, oddQuotAction M ⟨a, haM⟩ x ∈ T)
    (hET : ∀ e (he : e ∈ E), ∀ x ∈ T, oddQuotAction M ⟨e, hEM he⟩ x ∈ T)
    (hant : ∃ x ∈ T, oddQuotAction M ⟨a, haM⟩ x ≠ x)
    (hent : ∃ e, ∃ he : e ∈ E, ∃ x ∈ T, oddQuotAction M ⟨e, hEM he⟩ x ≠ x) :
    ∃ N : Subgroup X, N ≤ M ∧
      N ≤ centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({γ} : Set X) ⊓ centralizer ({δ} : Set X))) ∧
      quotImage M N = T ∧ Nonempty (N ⧸ pPrimeCore 2 N ≃* SL(2, GaloisField p n)) ∧
      ActsProperly a ((E ⊔ conjugate E δ) ⊓ centralizer ({δ} : Set X)) N (oddCoreIn N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : M ⧸ pPrimeCore 2 M := ((⟨δ, hδM⟩ : M) : M ⧸ pPrimeCore 2 M) with hu
  have hδMn : δ ∈ normalizer (M : Set X) := le_normalizer hδM
  have hφδ : ∀ q, oddQuotAction M ⟨δ, hδMn⟩ q = u * q * u⁻¹ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      rw [oddQuotAction_mk, hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
  have hfix : autFixed (oddQuotAction M ⟨δ, hδMn⟩) = centralizer ({u} : Set _) := by
    ext q
    rw [mem_centralizer_singleton_iff]
    change oddQuotAction M ⟨δ, hδMn⟩ q = q ↔ _
    rw [hφδ]
    constructor
    · intro h
      calc q * u = (u * q * u⁻¹) * u := by rw [h]
        _ = u * q := by group
    · intro h
      rw [← h]
      group
  obtain ⟨N, hNC, hNc, hNT, hnorm⟩ := exists_isPComponent_of_autFixed hδMn hδ
    (T := T) (by rw [hfix]; exact hT) (by rw [hfix]; exact hTc)
  have hNM : N ≤ M := hNC.trans inf_le_left
  obtain ⟨hNH, hNHc⟩ := isPComponent_inf_centralizer hM hMc hNC hNc
  subst hNT
  have h5 : 5 ≤ p ^ n := by
    have hperf := commutator_self_of_isPComponent hT hTc
    have : Group.IsPerfect (quotImage M N) := Subgroup.isPerfect_iff.mpr hperf
    exact five_le_of_isPerfect_sl hp2 hn
      (Group.IsPerfect.ofSurjective (f := eT.toMonoidHom) eT.surjective)
  have hO : pPrimeCore 2 (quotImage M N) = ⊥ := pPrimeCore_eq_bot_of_mulEquiv_sl hp2 h5 eT
  have eN : Nonempty (N ⧸ pPrimeCore 2 N ≃* SL(2, GaloisField p n)) := by
    obtain ⟨ψ, hψ, -, hψk⟩ := exists_quotImage_hom hNM
    obtain ⟨eψ, -⟩ := exists_quotient_pPrimeCore_equiv ψ hψ hψk
    exact ⟨eψ.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans
      (QuotientGroup.quotientBot.trans eT))⟩
  set P : Subgroup X := ((quotImage M N).comap (QuotientGroup.mk' (pPrimeCore 2 M))).map
    M.subtype with hP
  have hPM : P ≤ M := map_subtype_le _
  have hmemP : ∀ m : M, (m : X) ∈ P ↔ (m : M ⧸ pPrimeCore 2 M) ∈ quotImage M N := by
    intro m
    constructor
    · rintro ⟨m', hm', hm'm⟩
      rw [← Subtype.ext hm'm]
      exact hm'
    · intro h
      exact ⟨m, h, rfl⟩
  have hPq : quotImage M P = quotImage M N := by
    ext q
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (hmemP m).mp hm
    · intro hq
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨m, (hmemP m).mpr hq, rfl⟩
  have hOP : pPrimeCore 2 (quotImage M P) = ⊥ := by
    rw [hPq]
    exact hO
  have hnormP : ∀ g (hgM : g ∈ normalizer (M : Set X)),
      (∀ x ∈ quotImage M N, oddQuotAction M ⟨g, hgM⟩ x ∈ quotImage M N) →
        g ∈ normalizer (P : Set X) := by
    intro g hgM hg
    apply mem_normalizer_of_forall_conj
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hgm : g * (m : X) * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM _).mp m.2
    refine (hmemP ⟨_, hgm⟩).mpr ?_
    have h1 := hg _ hm
    rw [QuotientGroup.mk'_apply, oddQuotAction_mk] at h1
    exact h1
  have hPT : ∀ g (hgM : g ∈ normalizer (M : Set X)), g ∈ normalizer (P : Set X) →
      ∀ x ∈ quotImage M N, oddQuotAction M ⟨g, hgM⟩ x ∈ quotImage M N := by
    intro g hgM hgP x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    have hm : (m : X) ∈ P := (hmemP m).mpr hx
    have hgm : g * (m : X) * g⁻¹ ∈ P := (mem_normalizer_iff.mp hgP _).mp hm
    have hgmM : g * (m : X) * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM _).mp m.2
    rw [oddQuotAction_mk]
    exact (hmemP ⟨_, hgmM⟩).mp hgm
  set F := E ⊔ conjugate E δ with hF
  have hδaC : δ ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hδa
  have hFa : F ≤ oddCentralizerCore a := sup_le hEa (conjugate_le_oddCentralizerCore hδaC hEa)
  have hFodd : Odd (Nat.card F) := Nat.coprime_two_left.mp
    ((coprime_card_oddCentralizerCore a).coprime_dvd_right (card_dvd_of_le hFa))
  have hδF : δ ∈ normalizer (F : Set X) := mem_normalizer_sup_conjugate hδ E
  have hFM : F ≤ normalizer (M : Set X) := sup_le hEM (conjugate_le_of_le_of_mem hEM hδMn)
  have hδT : ∀ x ∈ quotImage M N, oddQuotAction M ⟨δ, hδMn⟩ x = x := by
    intro x hx
    rw [hφδ, show u * x = x * u from (mem_centralizer_singleton_iff.mp (hT hx)).symm]
    group
  have hδP : δ ∈ normalizer (P : Set X) :=
    hnormP δ hδMn (fun x hx => by rw [hδT x hx]; exact hx)
  have hEP : E ≤ normalizer (P : Set X) := fun e he => hnormP e (hEM he) (hET e he)
  have hFP : F ≤ normalizer (P : Set X) := sup_le hEP (conjugate_le_of_le_of_mem hEP hδP)
  have hδ2 : δ ^ 2 = 1 := by rw [pow_two]; exact hδ
  have hFC : ∀ x ∈ F, x * a = a * x := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hFa hx
    exact mem_centralizer_singleton_iff.mp y.2
  have haE : a ∈ normalizer ((F ⊓ centralizer ({δ} : Set X) : Subgroup X) : Set X) := by
    apply mem_normalizer_of_forall_conj
    intro x hx
    rwa [show a * x * a⁻¹ = x by rw [← hFC x (mem_inf.mp hx).1]; group]
  have hE'odd : Odd (Nat.card (F ⊓ centralizer ({δ} : Set X) : Subgroup X)) :=
    Odd.of_dvd_nat hFodd (card_dvd_of_le inf_le_left)
  have haN : a ∈ normalizer (N : Set X) := hnorm a haM hδa.symm haT
  have hE'N : F ⊓ centralizer ({δ} : Set X) ≤ normalizer (N : Set X) := fun e he =>
    hnorm e (hFM (mem_inf.mp he).1) (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2)
      (hPT e (hFM (mem_inf.mp he).1) (hFP (mem_inf.mp he).1))
  refine ⟨N, hNM, hNH, hNHc, rfl, eN, actsProperly_of_involution ha haE hE'odd haN hE'N ?_ ?_⟩
  · intro h
    obtain ⟨x, hx, hne⟩ := hant
    exact hne (forall_fixed_of_trivial hNM haM haN hO h x hx)
  ·
    have hδtriv : ∀ s ∈ P, ⁅s, δ⁆ ∈ oddCoreIn P := by
      refine (forall_quotImage_iff hPM hδMn hδP).mp fun q hq => ?_
      rw [hδT q (hPq ▸ hq), mul_inv_cancel]
      exact one_mem _
    have hEntP : ∃ e ∈ F, ∃ s ∈ P, ⁅s, e⁆ ∉ oddCoreIn P := by
      obtain ⟨e, he, x, hx, hex⟩ := hent
      refine ⟨e, mem_sup_left he, ?_⟩
      by_contra hall
      push Not at hall
      exact hex (forall_fixed_of_trivial hPM (hEM he) (hEP he) hOP hall x (hPq ▸ hx))
    obtain ⟨e, he, s, hs, hes⟩ := exists_centralizer_mem_nontrivial hδ2 hδF hFodd hδP hFP hδtriv
      hEntP
    refine ⟨e, he, ?_⟩
    by_contra hall
    push Not at hall
    have heM := hFM (mem_inf.mp he).1
    have h1 := forall_fixed_of_trivial hNM heM (hE'N he) hO hall
    apply hes
    refine (forall_quotImage_iff hPM heM (hFP (mem_inf.mp he).1)).mp (fun q hq => ?_) s hs
    rw [h1 q (hPq ▸ hq), mul_inv_cancel]
    exact one_mem _

end CFSG.ComponentClassification.TBLit
