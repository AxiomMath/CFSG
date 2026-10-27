module

public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusCentralizerSupport
public import CFSG.CharacterTheory.Semidihedral.Local.ParameterNineTorusNormalizerSupport

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

theorem exists_mul_eq_of_mem_sup_of_le_centralizer {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (h | h)
    · exact ⟨y, h, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, h, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, A.mul_mem hy₁ hy₂, z₁ * z₂, B.mul_mem hz₁ hz₂, ?_⟩
    have hc : z₁ * y₂ = y₂ * z₁ := Subgroup.mem_centralizer_iff.mp (hAB hy₂) z₁ hz₁
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [hc]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, A.inv_mem hy, z⁻¹, B.inv_mem hz, ?_⟩
    have hc : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp (hAB (A.inv_mem hy)) z⁻¹ (B.inv_mem hz)
      exact h
    rw [mul_inv_rev, hc]

theorem exists_sq_eq_commutator_of_kleinFour {V : Type*} [Group V] [IsKleinFour V]
    (σ : MulAut V) : ∃ a b : MulAut V, σ ^ 2 = a * b * a⁻¹ * b⁻¹ := by
  have hS3 : ∀ τ : Equiv.Perm (Fin 3), ∃ a b : Equiv.Perm (Fin 3),
      τ ^ 2 = a * b * a⁻¹ * b⁻¹ := by decide
  obtain ⟨e, -⟩ := (CFSG.Semidihedral.Local.kleinFour_automorphism_action (V := V)).1
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  have : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card {x : V // x ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      IsKleinFour.card_four]
  let E : MulAut V ≃* Equiv.Perm (Fin 3) :=
    e.trans (Fintype.equivFinOfCardEq hcard).permCongrHom
  obtain ⟨a, b, hab⟩ := hS3 (E σ)
  refine ⟨E.symm a, E.symm b, ?_⟩
  apply E.injective
  simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
  exact hab

theorem klein_centralizer_odd_core {G : Type*} [Group G] [Finite G] (V W : Subgroup G)
    (hV : IsKleinFour V) (hWodd : Odd (Nat.card W)) (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W) :
    Nat.card (Subgroup.centralizer (V : Set G)) = 4 * Nat.card W ∧
      (CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype = W ∧
      Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (W : Set G) ∧
      (∀ x ∈ Subgroup.centralizer (V : Set G), Odd (orderOf x) → x ∈ W) ∧
      (∀ x ∈ Subgroup.centralizer (V : Set G), x ^ 2 = 1 → x ∈ V) := by
  set D := Subgroup.centralizer (V : Set G) with hDdef
  have hVcomm : ∀ a b : V, a * b = b * a := mul_comm_of_exponent_two hV.exponent_two
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hVW : V ≤ Subgroup.centralizer (W : Set G) := Subgroup.le_centralizer_iff.mpr hWD
  have hv2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
    rw [hV.exponent_two] at h
    exact congrArg Subtype.val h
  have hdec : ∀ x ∈ D, ∃ v ∈ V, ∃ w ∈ W, v * w = x := fun x hx =>
    exists_mul_eq_of_mem_sup_of_le_centralizer hVW (hsup ▸ hx)
  have hvw : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    (Subgroup.mem_centralizer_iff.mp (hVW hv) w hw).symm
  have hDW : D ≤ Subgroup.centralizer (W : Set G) := by
    intro x hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    calc w' * (v * w) = v * (w' * w) := by
          rw [← mul_assoc, ← hvw v hv w' hw', mul_assoc]
      _ = v * w * w' := by rw [hWcomm w' hw' w hw, mul_assoc]
  have hcard : Nat.card D = 4 * Nat.card W := by
    let f : V × W → D := fun p => ⟨(p.1 : G) * p.2, hsup ▸ Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨v, w⟩ ⟨v', w'⟩ h
        have h' : (v : G) * w = v' * w' := congrArg Subtype.val h
        have hvv : (v' : G)⁻¹ * v = w' * (w : G)⁻¹ := by
          calc (v' : G)⁻¹ * v = (v' : G)⁻¹ * (v * w) * (w : G)⁻¹ := by group
            _ = (v' : G)⁻¹ * (v' * w') * (w : G)⁻¹ := by rw [h']
            _ = w' * (w : G)⁻¹ := by group
        have h1 : (v' : G)⁻¹ * v = 1 := Subgroup.disjoint_def.mp hdisj
          (V.mul_mem (V.inv_mem v'.2) v.2) (hvv ▸ W.mul_mem w'.2 (W.inv_mem w.2))
        have hveq : (v : G) = v' := by
          rw [inv_mul_eq_one] at h1
          exact h1.symm
        have hweq : (w : G) = w' := by
          rw [hveq] at h'
          exact mul_left_cancel h'
        exact Prod.ext (Subtype.ext hveq) (Subtype.ext hweq)
      · rintro ⟨x, hx⟩
        obtain ⟨v, hv, w, hw, rfl⟩ := hdec x hx
        exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hV.card_four]
  have hodd : ∀ x ∈ D, Odd (orderOf x) → x ∈ W := by
    intro x hx hxo
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec x hx
    obtain ⟨j, hj⟩ := hxo
    have hpow : (v * w) ^ orderOf (v * w) = 1 := pow_orderOf_eq_one _
    rw [(Commute.mul_pow (hvw v hv w hw) _)] at hpow
    have hvk : v ^ orderOf (v * w) = v := by
      rw [hj, pow_succ, pow_mul, hv2 v hv, one_pow, one_mul]
    rw [hvk] at hpow
    have hvW : v ∈ W := by
      rw [mul_eq_one_iff_eq_inv.mp hpow]
      exact W.inv_mem (W.pow_mem hw _)
    have hv1 : v = 1 := Subgroup.disjoint_def.mp hdisj hv hvW
    rw [hv1, one_mul]
    exact hw
  have hinv2 : ∀ x ∈ D, x ^ 2 = 1 → x ∈ V := by
    intro x hx hx2
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec x hx
    rw [(Commute.mul_pow (hvw v hv w hw) _), hv2 v hv, one_mul] at hx2
    have hw1 : w = 1 := by
      have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      have hodd' : Odd (orderOf w) := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw)
      have h1 : orderOf w = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact h
        · rw [h] at hodd'
          exact absurd hodd' (by decide)
      exact orderOf_eq_one_iff.mp h1
    rw [hw1, mul_one]
    exact hv
  have hcore : (CFSG.pPrimeCore 2 D).map D.subtype = W := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      apply hodd _ y.2
      have hdvd : orderOf y ∣ Nat.card (CFSG.pPrimeCore 2 D) := by
        have := Subgroup.orderOf_dvd_natCard _ hy
        exact this
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) hdvd
    · have hWn : (W.subgroupOf D).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have hgx : (g : G) * x = x * g :=
          (Subgroup.mem_centralizer_iff.mp (hDW g.2) x hx).symm
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hgx, mul_assoc, mul_inv_cancel, mul_one]
        exact hx
      have hcardW : Nat.card (W.subgroupOf D) = Nat.card W :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWD).toEquiv
      have hle : W.subgroupOf D ≤ CFSG.pPrimeCore 2 D :=
        le_sSup ⟨hWn, by rw [hcardW]; exact Nat.coprime_two_left.mpr hWodd⟩
      intro w hw
      exact ⟨⟨w, hWD hw⟩, hle hw, rfl⟩
  exact ⟨hcard, hcore, hDW, hodd, hinv2⟩

theorem relIndex_centralizer_eq_two_of_dichotomy {G : Type*} [Group G] {W L : Subgroup G}
    {d : G} (hdL : d ∈ L) (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) (hW2 : ∃ w ∈ W, w⁻¹ ≠ w)
    (hdich : ∀ h ∈ L, (∀ w ∈ W, h * w * h⁻¹ = w) ∨ (∀ w ∈ W, h * w * h⁻¹ = w⁻¹)) :
    (Subgroup.centralizer (W : Set G)).relIndex L = 2 ∧
      (∀ h ∈ L, h ∉ Subgroup.centralizer (W : Set G) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      d ∉ Subgroup.centralizer (W : Set G) := by
  obtain ⟨w₁, hw₁, hw₁inv⟩ := hW2
  have hinvK : ∀ h : G, (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) →
      h ∉ Subgroup.centralizer (W : Set G) := by
    intro h hinv hK
    apply hw₁inv
    rw [← hinv w₁ hw₁, (Subgroup.mem_centralizer_iff.mp hK w₁ hw₁).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  have hcentK : ∀ h : G, (∀ w ∈ W, h * w * h⁻¹ = w) → h ∈ Subgroup.centralizer (W : Set G) := by
    intro h hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hc w hw
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  refine ⟨?_, fun h hh hK w hw => ?_, hinvK d hdW⟩
  · rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨d, hdL, fun b hb => ?_⟩
    rcases hdich b hb with hc | hi
    · have hbd : ∀ w ∈ W, b * d * w * (b * d)⁻¹ = w⁻¹ := fun w hw => by
        calc b * d * w * (b * d)⁻¹ = b * (d * w * d⁻¹) * b⁻¹ := by group
          _ = b * w⁻¹ * b⁻¹ := by rw [hdW w hw]
          _ = (b * w * b⁻¹)⁻¹ := by group
          _ = w⁻¹ := by rw [hc w hw]
      exact Or.inr ⟨hcentK b hc, hinvK _ hbd⟩
    · have hbd : ∀ w ∈ W, b * d * w * (b * d)⁻¹ = w := fun w hw => by
        calc b * d * w * (b * d)⁻¹ = b * (d * w * d⁻¹) * b⁻¹ := by group
          _ = b * w⁻¹ * b⁻¹ := by rw [hdW w hw]
          _ = (b * w * b⁻¹)⁻¹ := by group
          _ = w := by rw [hi w hw, inv_inv]
      exact Or.inl ⟨hcentK _ hbd, hinvK b hi⟩
  · rcases hdich h hh with hc | hi
    · exact absurd (hcentK h hc) hK
    · exact hi w hw

theorem cyclic_torus_normalizer_basic {G : Type*} [Group G] [Finite G]
    {t s₀ : G} (V : Subgroup G) (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hV : IsKleinFour V) (hs₀2 : orderOf s₀ = 2) (hs₀t : s₀ ≠ t)
    (W : Subgroup G) (hWcyc : IsCyclic W) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.centralizer (V : Set G))
    (hsurj : Function.Surjective V.normalizerMonoidHom)
    {d : G} (hdC : d ∈ Subgroup.centralizer ({t} : Set G))
    (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hds : d * s₀ * d⁻¹ = t * s₀) (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G) ∧
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W : Set G) =
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G) ∧
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W : Set G) :
        Subgroup G) = 8 * Nat.card W ∧
      Nat.card (Subgroup.normalizer (V : Set G)) = 24 * Nat.card W ∧
      d ∉ Subgroup.centralizer (W : Set G) ∧
      (∀ g ∈ Subgroup.normalizer (V : Set G), (∀ w ∈ W, g * w * g⁻¹ = w) ∨
        (∀ w ∈ W, g * w * g⁻¹ = w⁻¹)) ∧
      (∀ v ∈ V, v ≠ 1 → ∃ g ∈ Subgroup.normalizer (V : Set G), g * t * g⁻¹ = v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set D := Subgroup.centralizer (V : Set G) with hDdef
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hDcard, -, hDK, hodd, hinv2⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have htV : t ∈ V := hVdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := hVdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hWD : W ≤ D := hsup ▸ le_sup_right
  have hDC : D ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx t htV).symm
  have hv2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
    rw [hV.exponent_two] at h
    exact congrArg Subtype.val h
  have hconjOrd : ∀ g x : G, orderOf (g * x * g⁻¹) = orderOf x := fun g x => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hMH : M ≤ H := by
    have key : ∀ g ∈ M, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      have hgD := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V hg
      apply hodd _ ((Subgroup.mem_normalizer_iff.mp hgD w).mp (hWD hw))
      rw [hconjOrd]
      exact Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key g hg w, fun hw => ?_⟩
    have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hw
    simpa [mul_assoc] using h
  have hCH : C ⊓ H = C ⊓ M := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgC, hgH⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨hgC, ?_⟩
      have key : ∀ g' : G, g' ∈ C → g' ∈ Subgroup.normalizer (K : Set G) → ∀ v ∈ V,
          g' * v * g'⁻¹ ∈ V := by
        intro g' hg'C hg'K v hv
        apply hinv2
        · change _ ∈ D
          rw [← hCK]
          exact Subgroup.mem_inf.mpr ⟨C.mul_mem (C.mul_mem hg'C (hDC (hVD hv))) (C.inv_mem hg'C),
            (Subgroup.mem_normalizer_iff.mp hg'K v).mp (hDK (hVD hv))⟩
        · rw [conj_pow, hv2 v hv, mul_one, mul_inv_cancel]
      have hgK := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W hgH
      rw [Subgroup.mem_normalizer_iff]
      intro v
      refine ⟨key g hgC hgK v, fun hv => ?_⟩
      have h := key g⁻¹ (C.inv_mem hgC) (Subgroup.inv_mem _ hgK) _ hv
      simpa [mul_assoc] using h
    · exact inf_le_inf_left _ hMH
  have hMcard : Nat.card M = 24 * Nat.card W := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V.normalizerMonoidHom.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Subgroup.normalizerMonoidHom_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer _)).toEquiv, hDcard,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      (CFSG.Semidihedral.Local.kleinFour_automorphism_action (V := V)).2.1] at h1
    rw [h1]
    ring
  have ht1 : t ≠ 1 := by
    rw [← hd2]
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hd4] at this
    norm_num at this
  have hfusM : ∀ v ∈ V, v ≠ 1 → ∃ g ∈ M, g * t * g⁻¹ = v := by
    intro v hv hv1
    obtain ⟨⟨e, he⟩, -, -, -⟩ := CFSG.Semidihedral.Local.kleinFour_automorphism_action (V := V)
    let v' : {x : V // x ≠ 1} := ⟨⟨t, htV⟩, fun h => ht1 (congrArg Subtype.val h)⟩
    let w' : {x : V // x ≠ 1} := ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h)⟩
    have hφ : e.symm (Equiv.swap v' w') ⟨t, htV⟩ = ⟨v, hv⟩ := by
      have h := he (e.symm (Equiv.swap v' w')) v'
      rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left] at h
      exact h.symm
    obtain ⟨y, hy⟩ := hsurj (e.symm (Equiv.swap v' w'))
    refine ⟨y, y.2, ?_⟩
    have h := congrArg (fun ψ : MulAut V => ((ψ ⟨t, htV⟩ : V) : G)) hy
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    rw [h, hφ]
  have hDM : D ≤ M := Subgroup.centralizer_le_normalizer _
  have hDCM : D ≤ C ⊓ M := le_inf hDC hDM
  have hdD : d ∉ D := by
    intro hd
    have h := hd s₀ hsV
    have h' : d * s₀ * d⁻¹ = s₀ := by rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hds] at h'
    apply ht1
    calc t = t * s₀ * s₀⁻¹ := by group
      _ = s₀ * s₀⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel s₀
  have htD : t ∈ D := hVD htV
  have hCMcard : Nat.card (C ⊓ M : Subgroup G) = 8 * Nat.card W := by
    have hDn : (D.subgroupOf (C ⊓ M)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hgD := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V (Subgroup.mem_inf.mp g.2).2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (Subgroup.mem_normalizer_iff.mp hgD x).mp hx
    have hcm := Subgroup.card_mul_index (D.subgroupOf (C ⊓ M))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDCM).toEquiv, hDcard] at hcm
    set k := (D.subgroupOf (C ⊓ M)).index with hk
    have hdCM : d ∈ C ⊓ M := Subgroup.mem_inf.mpr ⟨hdC, hdM⟩
    have h2k : 2 ∣ k := by
      have hord : orderOf (QuotientGroup.mk (s := D.subgroupOf (C ⊓ M)) ⟨d, hdCM⟩) = 2 := by
        apply orderOf_eq_prime
        · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          simp only [SubmonoidClass.coe_pow]
          rw [hd2]
          exact htD
        · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hdD
      rw [hk, Subgroup.index_eq_card, ← hord]
      exact orderOf_dvd_natCard _
    have hk6 : k ∣ 6 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : C ⊓ M ≤ M)
      rw [← hcm, hMcard] at h
      have hm0 : 0 < Nat.card W := Nat.card_pos
      have : 4 * Nat.card W * k ∣ 4 * Nat.card W * 6 := by
        rw [show 4 * Nat.card W * 6 = 24 * Nat.card W by ring]
        exact h
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) this
    have hkne : k ≠ 6 := by
      intro h6
      obtain ⟨g, hgM, hg⟩ := hfusM s₀ hsV (fun h => by
        rw [h, orderOf_one] at hs₀2
        norm_num at hs₀2)
      have heq : C ⊓ M = M := Subgroup.eq_of_le_of_card_ge inf_le_right (by
        rw [← hcm, h6, hMcard]
        ring_nf
        exact le_refl _)
      have hgCM : g ∈ C ⊓ M := by rw [heq]; exact hgM
      have hgC : g ∈ C := (Subgroup.mem_inf.mp hgCM).1
      rw [Subgroup.mem_centralizer_singleton_iff] at hgC
      apply hs₀t
      rw [← hg, hgC, mul_assoc, mul_inv_cancel, mul_one]
    have hk2 : k = 2 := by
      have hk6' := Nat.le_of_dvd (by norm_num) hk6
      interval_cases k <;> omega
    rw [← hcm, hk2]
    ring
  obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    exact hW1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
  have hw₁inv : w₁⁻¹ ≠ w₁ := by
    intro h
    have h2 : w₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel w₁
    have hodd₁ : Odd (orderOf w₁) := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw₁)
    have h1 : orderOf w₁ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
      · exact h
      · rw [h] at hodd₁
        exact absurd hodd₁ (by decide)
    exact hw₁1 (orderOf_eq_one_iff.mp h1)
  have hdK : d ∉ K := by
    intro hK
    apply hw₁inv
    rw [← hdW w₁ hw₁, (Subgroup.mem_centralizer_iff.mp hK w₁ hw₁).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  have hdichM : ∀ g ∈ M, (∀ w ∈ W, g * w * g⁻¹ = w) ∨ (∀ w ∈ W, g * w * g⁻¹ = w⁻¹) := by
    let ψ : M →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hMH)
    have hψapp : ∀ (g : M) (w : W), ((ψ g w : W) : G) = (g : G) * w * (g : G)⁻¹ := by
      intro g w
      exact Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion hMH g) w
    have hAutComm : ∀ a b : MulAut W, a * b = b * a := by
      let e := IsCyclic.mulAutMulEquiv (G := W)
      intro a b
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    have hkerD : ∀ g : M, (g : G) ∈ D → ψ g = 1 := by
      intro g hg
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      rw [hψapp, MulAut.one_apply, (Subgroup.mem_centralizer_iff.mp (hDK hg) w w.2).symm,
        mul_assoc, mul_inv_cancel, mul_one]
    have hsq : ∀ g : M, ψ g ^ 2 = 1 := by
      intro g
      obtain ⟨a, b, hab⟩ := exists_sq_eq_commutator_of_kleinFour (V := V)
        (V.normalizerMonoidHom g)
      obtain ⟨a', ha'⟩ := hsurj a
      obtain ⟨b', hb'⟩ := hsurj b
      have hker : V.normalizerMonoidHom ((a' * b' * a'⁻¹ * b'⁻¹)⁻¹ * g ^ 2) = 1 := by
        rw [map_mul, map_inv, map_pow, hab, map_mul, map_mul, map_mul, map_inv, map_inv, ha', hb',
          inv_mul_cancel]
      have hmem : ((a' * b' * a'⁻¹ * b'⁻¹)⁻¹ * g ^ 2 : M) ∈
          (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) := by
        rw [← Subgroup.normalizerMonoidHom_ker]
        exact hker
      have h1 := hkerD ((a' * b' * a'⁻¹ * b'⁻¹)⁻¹ * g ^ 2) (Subgroup.mem_subgroupOf.mp hmem)
      rw [map_mul, map_inv, map_pow, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have hc : ψ a' * ψ b' * (ψ a')⁻¹ * (ψ b')⁻¹ = 1 := by
        rw [hAutComm (ψ a') (ψ b'), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
      rw [hc, inv_one, one_mul] at h1
      exact h1
    have hψd : ψ ⟨d, hdM⟩ ≠ 1 := by
      intro h
      apply hdK
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h' := congrArg (fun σ : MulAut W => ((σ ⟨w, hw⟩ : W) : G)) h
      simp only [MulAut.one_apply] at h'
      rw [hψapp] at h'
      calc w * d = d * w * d⁻¹ * d := by rw [h']
        _ = d * w := by group
    have hrange2 : Nat.card ψ.range ∣ 2 := by
      have hp2 : IsPGroup 2 ψ.range := by
        rw [IsPGroup.iff_orderOf]
        rintro ⟨x, g, rfl⟩
        have hx : orderOf (⟨ψ g, g, rfl⟩ : ψ.range) ∣ 2 := by
          apply orderOf_dvd_of_pow_eq_one
          apply Subtype.ext
          simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
          exact hsq g
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (pow_one 2 ▸ hx)
        exact ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hp2.exists_card_eq
      have h6 : Nat.card ψ.range ∣ 6 := by
        have hcm := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hMcard] at hcm
        have hDker : (D.subgroupOf M) ≤ ψ.ker := fun g hg => hkerD g hg
        have hdvd := Subgroup.card_dvd_of_le hDker
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv, hDcard] at hdvd
        obtain ⟨j, hj⟩ := hdvd
        rw [hj] at hcm
        have hm0 : 0 < Nat.card W := Nat.card_pos
        have : 4 * Nat.card W * (Nat.card ψ.range * j) = 4 * Nat.card W * 6 := by
          rw [show 4 * Nat.card W * 6 = 24 * Nat.card W by ring, hcm]
          ring
        exact Dvd.intro j (Nat.eq_of_mul_eq_mul_left (by positivity) this)
      rw [hk] at h6 ⊢
      have hk1 : k ≤ 1 := by
        by_contra hk1
        push Not at hk1
        have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hk1).trans h6
        norm_num at this
      exact (pow_dvd_pow 2 hk1).trans (by norm_num)
    have hkeridx : ψ.ker.index = 2 := by
      rw [Subgroup.index_ker]
      have hpos : 0 < Nat.card ψ.range := Nat.card_pos
      have hne1 : Nat.card ψ.range ≠ 1 := by
        intro h1
        have hsub : Subsingleton ψ.range := (Nat.card_eq_one_iff_unique.mp h1).1
        apply hψd
        have := Subsingleton.elim (⟨ψ ⟨d, hdM⟩, ⟨d, hdM⟩, rfl⟩ : ψ.range) 1
        exact congrArg Subtype.val this
      have hle := Nat.le_of_dvd (by norm_num) hrange2
      interval_cases h : Nat.card ψ.range <;> omega
    intro g hg
    by_cases hgk : (⟨g, hg⟩ : M) ∈ ψ.ker
    · left
      intro w hw
      have h := congrArg (fun σ : MulAut W => ((σ ⟨w, hw⟩ : W) : G)) (MonoidHom.mem_ker.mp hgk)
      simp only [MulAut.one_apply] at h
      rw [hψapp] at h
      exact h
    · right
      have hdk : (⟨d, hdM⟩ : M) ∉ ψ.ker := fun h => hψd (MonoidHom.mem_ker.mp h)
      have hmul : (⟨g, hg⟩ : M) * (⟨d, hdM⟩ : M)⁻¹ ∈ ψ.ker := by
        rw [Subgroup.mul_mem_iff_of_index_two hkeridx]
        exact iff_of_false hgk (fun h => hdk (by simpa using h))
      have hψeq : ψ ⟨g, hg⟩ = ψ ⟨d, hdM⟩ := by
        have h := MonoidHom.mem_ker.mp hmul
        rw [map_mul, map_inv, mul_inv_eq_one] at h
        exact h
      intro w hw
      have h := congrArg (fun σ : MulAut W => ((σ ⟨w, hw⟩ : W) : G)) hψeq
      simp only [hψapp] at h
      rw [h, hdW w hw]
  exact ⟨hMH, hCH, by rw [hCH, hCMcard], hMcard, hdK, hdichM, hfusM⟩

theorem cyclic_torus_normalizer_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {t s₀ : G} (V : Subgroup G) (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (hV : IsKleinFour V) (hs₀2 : orderOf s₀ = 2) (hs₀t : s₀ ≠ t)
    (W : Subgroup G) (hWcyc : IsCyclic W) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.centralizer (V : Set G))
    (hsurj : Function.Surjective V.normalizerMonoidHom)
    {d : G} (hdC : d ∈ Subgroup.centralizer ({t} : Set G))
    (hdM : d ∈ Subgroup.normalizer (V : Set G)) (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t)
    (hds : d * s₀ * d⁻¹ = t * s₀) (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) :
    (Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
      Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
      ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
        (P : Subgroup _).map (Subgroup.normalizer (W : Set G)).subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      (∃ P : Sylow 2 (Subgroup.centralizer (W : Set G)),
        (P : Subgroup _).map (Subgroup.centralizer (W : Set G)).subtype = V) ∧
      (Subgroup.centralizer (W : Set G) : Set G) * (Subgroup.normalizer (V : Set G) : Set G) =
        (Subgroup.normalizer (W : Set G) : Set G) ∧
      (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2 ∧
      (∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
        ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      Nat.card (Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) :
        Subgroup G) = 12 * Nat.card W ∧
      (∀ v ∈ V, v ≠ 1 → ∃ k ∈ Subgroup.centralizer (W : Set G), k * t * k⁻¹ = v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMH, hCH, hCHcard, hMcard, hdK, hdichM, hfusM⟩ := cyclic_torus_normalizer_basic V hVdef
    hV hs₀2 hs₀t W hWcyc hWodd hW1 hsup hdisj hCK hsurj hdC hdM hd4 hd2 hds hdW
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set D := Subgroup.centralizer (V : Set G) with hDdef
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hDcard, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have htV : t ∈ V := hVdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := hVdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hVD : V ≤ D := hsup ▸ le_sup_left
  have hVK : V ≤ K := hVD.trans hDK
  have hKH : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hDM : D ≤ M := Subgroup.centralizer_le_normalizer _
  have hdH : d ∈ H := hMH hdM
  have hKnorm : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := fun h hh k hk =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W hh) k).mp hk
  have hV4 : Nat.card V = 4 := hV.card_four
  have hs₀sq : s₀ ^ 2 = 1 := by rw [← hs₀2]; exact pow_orderOf_eq_one s₀
  have hs₀inv : s₀⁻¹ = s₀ := by rw [inv_eq_iff_mul_eq_one, ← sq, hs₀sq]
  have hd4' : d ^ 4 = 1 := by rw [← hd4]; exact pow_orderOf_eq_one d
  have hts : s₀ * t = t * s₀ := by
    have h := (hVD hsV) t htV
    exact h.symm
  have hds' : d * s₀ = t * s₀ * d := by rw [← hds]; group
  have hrel : s₀ * d * s₀⁻¹ = d⁻¹ := by
    calc s₀ * d * s₀⁻¹ = s₀ * (d * s₀) := by rw [hs₀inv, mul_assoc]
      _ = s₀ * (t * s₀ * d) := by rw [hds']
      _ = (s₀ * t) * s₀ * d := by group
      _ = (t * s₀) * s₀ * d := by rw [hts]
      _ = t * (s₀ * s₀) * d := by group
      _ = t * d := by rw [← sq, hs₀sq, mul_one]
      _ = d ^ 2 * d := by rw [hd2]
      _ = d⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← hd4']
        group
  have hnotmem : s₀ ∉ Subgroup.zpowers d := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hd4] at hk
    have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
    obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
        k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
    · rw [h, zpow_zero] at hk
      rw [← hk, orderOf_one] at hs₀2
      norm_num at hs₀2
    · rw [h, zpow_one] at hk
      rw [← hk, hd4] at hs₀2
      norm_num at hs₀2
    · rw [h] at hk
      apply hs₀t
      rw [← hk, ← hd2]
      exact zpow_natCast d 2
    · rw [h] at hk
      have h3 : orderOf (d ^ 3) = 4 := by
        rw [Nat.Coprime.orderOf_pow (by rw [hd4]; norm_num), hd4]
      rw [← hk, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, h3] at hs₀2
      norm_num at hs₀2
  have hdih : Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃*
      DihedralGroup 4) :=
    MatrixFourGroupNormalizer.generatedDihedral_equiv d s₀ hd4 hs₀sq hrel hnotmem
  have hP₀card : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 := by
    obtain ⟨e⟩ := hdih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hsK : s₀ ∈ K := hVK hsV
  have hP₀H : Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr hdH) (Subgroup.zpowers_le.mpr (hKH hsK))
  have h16 : ¬ 2 ^ 4 ∣ Nat.card (C ⊓ H : Subgroup G) := by
    rw [hCHcard, show (2 : ℕ) ^ 4 = 16 by norm_num]
    intro h
    obtain ⟨j, hj⟩ := hWodd
    omega
  obtain ⟨P, hP⟩ := CFSG.Semidihedral.Local.exists_sylow_eq_of_order_four_square_of_not_dvd S hSC
    hS4 H _ hP₀H hP₀card (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) hd4 hd2 h16
  have hPcard : Nat.card (P : Subgroup H) = 8 := by
    rw [← hP₀card, ← hP, Subgroup.card_map_of_injective H.subtype_injective]
  have hfacH : (Nat.card H).factorization 2 = 3 := by
    have h := Sylow.card_eq_multiplicity P
    rw [hPcard, show (8 : ℕ) = 2 ^ 3 by norm_num] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hKdvdH : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le hKH
  have hK8 : ¬ 8 ∣ Nat.card K := by
    intro h8
    obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
    have hfacK : (Nat.card K).factorization 2 = 3 := by
      have hle : (Nat.card K).factorization 2 ≤ 3 := by
        rw [← hfacH]
        exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hKdvdH 2
      have hge : 3 ≤ (Nat.card K).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
          (by norm_num; exact h8)
      omega
    have hQcard : Nat.card (Q : Subgroup K) = 8 := by
      rw [Sylow.card_eq_multiplicity, hfacK]
      norm_num
    set Q₁ := (Q : Subgroup K).map K.subtype with hQ₁
    have hQ₁H : Q₁ ≤ H := (Subgroup.map_subtype_le _).trans hKH
    have hQ₁card : Nat.card (Q₁.subgroupOf H) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁H).toEquiv, hQ₁,
        Subgroup.card_map_of_injective K.subtype_injective, hQcard]
    let Q' : Sylow 2 H := Sylow.ofCard (Q₁.subgroupOf H) (by rw [hQ₁card, hfacH]; norm_num)
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q' P
    have hdP : (⟨d, hdH⟩ : H) ∈ (P : Subgroup H) := by
      have hd : d ∈ (P : Subgroup H).map H.subtype := by
        rw [hP]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
      obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hd
      have : x = ⟨d, hdH⟩ := Subtype.ext hxd
      exact this ▸ hx
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hdP
    have hconj : ((h⁻¹ : H) : G) * d * ((h⁻¹ : H) : G)⁻¹ ∈ Q₁ := by
      have h' : (MulAut.conj h)⁻¹ • (⟨d, hdH⟩ : H) ∈ Q₁.subgroupOf H := hdP
      rw [Subgroup.mem_subgroupOf] at h'
      simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] using h'
    have hK' : ((h⁻¹ : H) : G) * d * ((h⁻¹ : H) : G)⁻¹ ∈ K :=
      (Subgroup.map_subtype_le _) hconj
    apply hdK
    have := hKnorm h h.2 _ hK'
    simpa [mul_assoc] using this
  have hVKidx : ¬ 2 ∣ (V.subgroupOf K).index := by
    intro h2
    apply hK8
    have hcm := Subgroup.card_mul_index (V.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4] at hcm
    rw [← hcm]
    exact Nat.mul_dvd_mul_left 4 h2
  have hVp : IsPGroup 2 (V.subgroupOf K) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4]; norm_num)
  let PV : Sylow 2 K := hVp.toSylow hVKidx
  have hPV : (PV : Subgroup K).map K.subtype = V := by
    change (V.subgroupOf K).map _ = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVK]
  have hfacK2 : (Nat.card K).factorization 2 = 2 := by
    have h := Sylow.card_eq_multiplicity PV
    have hc : Nat.card (PV : Subgroup K) = 4 := by
      change Nat.card (V.subgroupOf K) = 4
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4]
    rw [hc, show (4 : ℕ) = 2 ^ 2 by norm_num] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hdecH : ∀ h ∈ H, ∃ k ∈ K, k * h ∈ M := by
    intro h hh
    set V₁ := V.map (MulAut.conj h).toMonoidHom with hV₁
    have hV₁K : V₁ ≤ K := by
      rintro _ ⟨v, hv, rfl⟩
      exact hKnorm h hh v (hVK hv)
    have hV₁card : Nat.card (V₁.subgroupOf K) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁K).toEquiv, hV₁,
        Subgroup.card_map_of_injective (MulAut.conj h).injective, hV4]
    let S₁ : Sylow 2 K := Sylow.ofCard (V₁.subgroupOf K) (by rw [hV₁card, hfacK2]; norm_num)
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₁ PV
    refine ⟨k, k.2, ?_⟩
    have hsub : ∀ v ∈ V, ((k : G) * h) * v * ((k : G) * h)⁻¹ ∈ V := by
      intro v hv
      have hmem : (⟨h * v * h⁻¹, hV₁K ⟨v, hv, rfl⟩⟩ : K) ∈ (S₁ : Subgroup K) := by
        change _ ∈ V₁.subgroupOf K
        rw [Subgroup.mem_subgroupOf]
        exact ⟨v, hv, rfl⟩
      have hmem' : MulAut.conj k • (⟨h * v * h⁻¹, hV₁K ⟨v, hv, rfl⟩⟩ : K) ∈
          ((k • S₁ : Sylow 2 K) : Subgroup K) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
      rw [hk] at hmem'
      have h' : ((MulAut.conj k • (⟨h * v * h⁻¹, hV₁K ⟨v, hv, rfl⟩⟩ : K) : K) : G) ∈ V := by
        have := hmem'
        change _ ∈ V.subgroupOf K at this
        rw [Subgroup.mem_subgroupOf] at this
        exact this
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h'
      have he : ((k : G) * h) * v * ((k : G) * h)⁻¹ = k * (h * v * h⁻¹) * (k : G)⁻¹ := by
        group
      rw [he]
      exact h'
    have hle : V.map (MulAut.conj ((k : G) * h)).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hsub v hv
    have heq : V.map (MulAut.conj ((k : G) * h)).toMonoidHom = V :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hsub y hy, fun hy => ?_⟩
    rw [← heq] at hy
    obtain ⟨v, hv, hvy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvy
    have : v = y := by
      have := congrArg (fun x => ((k : G) * h)⁻¹ * x * ((k : G) * h)) hvy
      simpa [mul_assoc] using this
    exact this ▸ hv
  have hdichH : ∀ h ∈ H, (∀ w ∈ W, h * w * h⁻¹ = w) ∨ (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) := by
    intro h hh
    obtain ⟨k, hk, hkh⟩ := hdecH h hh
    have hkc : ∀ w ∈ W, k * w * k⁻¹ = w := fun w hw => by
      rw [(Subgroup.mem_centralizer_iff.mp hk w hw).symm, mul_assoc, mul_inv_cancel, mul_one]
    have hkc' : ∀ w ∈ W, k⁻¹ * w * k = w := fun w hw => by
      have := hkc w hw
      calc k⁻¹ * w * k = k⁻¹ * (k * w * k⁻¹) * k := by rw [this]
        _ = w := by group
    have hheq : ∀ w ∈ W, h * w * h⁻¹ = k⁻¹ * ((k * h) * w * (k * h)⁻¹) * k := fun w _ => by
      group
    rcases hdichM (k * h) hkh with hc | hi
    · left
      intro w hw
      rw [hheq w hw, hc w hw, hkc' w hw]
    · right
      intro w hw
      rw [hheq w hw, hi w hw, hkc' w⁻¹ (W.inv_mem hw)]
  have hW2 : ∃ w ∈ W, w⁻¹ ≠ w := by
    obtain ⟨w₁, hw₁, hw₁1⟩ : ∃ w ∈ W, w ≠ 1 := by
      by_contra! hall
      exact hW1 ((Subgroup.eq_bot_iff_forall _).mpr hall)
    refine ⟨w₁, hw₁, fun h => hw₁1 ?_⟩
    have h2 : w₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel w₁
    have hodd₁ : Odd (orderOf w₁) := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw₁)
    have h1 : orderOf w₁ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
      · exact h
      · rw [h] at hodd₁
        exact absurd hodd₁ (by decide)
    exact orderOf_eq_one_iff.mp h1
  obtain ⟨hKH2, hinvH, -⟩ := relIndex_centralizer_eq_two_of_dichotomy hdH hdW hW2 hdichH
  obtain ⟨hKM2, -, -⟩ := relIndex_centralizer_eq_two_of_dichotomy hdM hdW hW2 hdichM
  have hKMcard : Nat.card (K ⊓ M : Subgroup G) = 12 * Nat.card W := by
    have h := Subgroup.card_mul_index (K.subgroupOf M)
    have hc : Nat.card (K.subgroupOf M) = Nat.card (K ⊓ M : Subgroup G) := by
      rw [← Subgroup.inf_subgroupOf_left, inf_comm,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    have hri : (K.subgroupOf M).index = 2 := hKM2
    rw [hc, hri, hMcard] at h
    omega
  have hKMset : (K : Set G) * (M : Set G) = (H : Set G) := by
    ext h
    constructor
    · rintro ⟨k, hk, g, hg, rfl⟩
      exact H.mul_mem (hKH hk) (hMH hg)
    · intro hh
      obtain ⟨k, hk, hkh⟩ := hdecH h hh
      exact ⟨k⁻¹, K.inv_mem hk, k * h, hkh, by group⟩
  have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hdinv : ∀ w ∈ W, d⁻¹ * w * d = w⁻¹ := by
    intro w hw
    have h := hdW w⁻¹ (W.inv_mem hw)
    rw [inv_inv] at h
    calc d⁻¹ * w * d = d⁻¹ * (d * w⁻¹ * d⁻¹) * d := by rw [h]
      _ = w⁻¹ := by group
  have htrans : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ K, k * t * k⁻¹ = v := by
    intro v hv hv1
    obtain ⟨g, hgM, hg⟩ := hfusM v hv hv1
    by_cases hgK : g ∈ K
    · exact ⟨g, hgK, hg⟩
    · refine ⟨g * d⁻¹, ?_, ?_⟩
      · have hgi := hinvH g (hMH hgM) hgK
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 : (g * d⁻¹) * w * (g * d⁻¹)⁻¹ = w := by
          calc (g * d⁻¹) * w * (g * d⁻¹)⁻¹ = g * (d⁻¹ * w * d) * g⁻¹ := by group
            _ = g * w⁻¹ * g⁻¹ := by rw [hdinv w hw]
            _ = (g * w * g⁻¹)⁻¹ := by group
            _ = w := by rw [hgi w hw, inv_inv]
        calc w * (g * d⁻¹) = (g * d⁻¹) * w * (g * d⁻¹)⁻¹ * (g * d⁻¹) := by rw [h1]
          _ = (g * d⁻¹) * w := by group
      · have hdt' : d⁻¹ * t * d = t := by
          rw [mul_assoc, ← hdt, ← mul_assoc, inv_mul_cancel, one_mul]
        calc g * d⁻¹ * t * (g * d⁻¹)⁻¹ = g * (d⁻¹ * t * d) * g⁻¹ := by group
          _ = g * t * g⁻¹ := by rw [hdt']
          _ = v := hg
  exact ⟨⟨hdih, hP₀card, P, hP⟩, ⟨PV, hPV⟩, hKMset, hKH2, hinvH, hKMcard, htrans⟩

theorem cyclic_torus_centralizer_quotient_of_data
    {G : Type} [Group G] [Finite G] {t s₀ : G}
    (V W : Subgroup G) (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (hV : IsKleinFour V) (ht2 : orderOf t = 2) (hWodd : Odd (Nat.card W))
    (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hCK : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.centralizer (V : Set G))
    (hVsyl : ∃ P : Sylow 2 (Subgroup.centralizer (W : Set G)),
      (P : Subgroup (Subgroup.centralizer (W : Set G))).map
        (Subgroup.centralizer (W : Set G)).subtype = V)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hKM : Nat.card (Subgroup.centralizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G) :
      Subgroup G) = 12 * Nat.card W)
    (htrans : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Subgroup.centralizer (W : Set G), k * t * k⁻¹ = v) :
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let π : K →* K ⧸ CFSG.pPrimeCore 2 K := QuotientGroup.mk' (CFSG.pPrimeCore 2 K)
    (CFSG.pPrimeCore 2 K).map K.subtype = W ∧ (CFSG.pPrimeCore 2 H).map H.subtype = W ∧
      W ≤ (Subgroup.center K).map K.subtype ∧
      (((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W)) ∧
        ¬ ((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W))) ∧
      IsKleinFour (((V ⊔ W).subgroupOf K).map π) ∧
      (∃ P : Sylow 2 (K ⧸ CFSG.pPrimeCore 2 K),
        (P : Subgroup _) = ((V ⊔ W).subgroupOf K).map π) ∧
      ∀ tK : K, (tK : G) = t → ((V ⊔ W).subgroupOf K).map π = Subgroup.centralizer {π tK} := by
  intro H K π
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hDK, hodd, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hWD : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hVD : V ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_left
  have htV : t ∈ V := hVdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hVK : V ≤ K := hVD.trans hDK
  have hWK : W ≤ K := hWD.trans hDK
  have htK : t ∈ K := hVK htV
  have hKc : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k := fun k hk w hw =>
    (Subgroup.mem_centralizer_iff.mp hk w hw).symm
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hWZ : W ≤ (Subgroup.center K).map K.subtype := by
    intro w hw
    refine ⟨⟨w, hWK hw⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hKc k k.2 w hw
  set R' := CFSG.pPrimeCore 2 K with hR'def
  set R := R'.map K.subtype with hRdef
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRcard : Nat.card R = Nat.card R' := Subgroup.card_map_of_injective K.subtype_injective
  have hRodd : Odd (Nat.card R) :=
    hRcard ▸ Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hRnorm : ∀ k ∈ K, ∀ x ∈ R, k * x * k⁻¹ ∈ R := by
    intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (inferInstance : R'.Normal).conj_mem y hy _, rfl⟩
  have hWR : W ≤ R := by
    have hWn : (W.subgroupOf K).Normal := by
      refine ⟨fun x hx k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have h : (k : G) * x * (k : G)⁻¹ = x := by
        rw [hKc k k.2 x hx, mul_assoc, mul_inv_cancel, mul_one]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, h] using hx
    have hcardW : Nat.card (W.subgroupOf K) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv
    have hle : W.subgroupOf K ≤ R' :=
      le_sSup ⟨hWn, by rw [hcardW]; exact Nat.coprime_two_left.mpr hWodd⟩
    intro w hw
    exact ⟨⟨w, hWK hw⟩, hle hw, rfl⟩
  have hRt : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ W := by
    intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxD : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [← hCK]
      exact Subgroup.mem_inf.mpr ⟨hxC, hRK hxR⟩
    exact hodd x hxD (Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hxR))
  have hRv : ∀ v ∈ V, v ≠ 1 → R ⊓ Subgroup.centralizer ({v} : Set G) ≤ W := by
    intro v hv hv1 x hx
    obtain ⟨k, hkK, hk⟩ := htrans v hv hv1
    obtain ⟨hxR, hxv⟩ := Subgroup.mem_inf.mp hx
    have hy : k⁻¹ * x * k ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := hRnorm k⁻¹ (K.inv_mem hkK) x hxR
        rwa [inv_inv] at h
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxv ⊢
        rw [← hk] at hxv
        calc k⁻¹ * x * k * t = k⁻¹ * (x * (k * t * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * t * k⁻¹) * x) * k := by rw [hxv]
          _ = t * (k⁻¹ * x * k) := by group
    have hyW := hRt hy
    have hx' : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [hx', hKc k hkK _ hyW, mul_assoc, mul_inv_cancel, mul_one]
    exact hyW
  have hVN : V ≤ Subgroup.normalizer (R : Set G) := fun v hv => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hRnorm v (hVK hv) x, fun h => ?_⟩
    have h' := hRnorm v⁻¹ (K.inv_mem (hVK hv)) _ h
    simpa [mul_assoc] using h'
  let φ : V →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hVN)
  let : MulDistribMulAction V R := MulDistribMulAction.compHom R φ
  have : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two hV.exponent_two⟩⟩
      exponent_dvd_p := by rw [hV.exponent_two] }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := V) (H := R)
    (by rw [hV.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h))
  have hRW : R ≤ W := by
    intro x hx
    have hmem : (⟨x, hx⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [← hgen] at hmem
    have hle : (⨆ (a : V) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) R) ≤
        W.comap R.subtype := by
      refine iSup₂_le fun a ha => ?_
      intro y hy
      rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
      have hy' : (a : G) * (y : G) * (a : G)⁻¹ = y := by
        have h := congrArg Subtype.val hy
        exact h
      apply hRv a a.2 (fun h => ha (Subtype.ext h))
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * (y : G) * (a : G)⁻¹ * a := by rw [hy']
        _ = a * y := by group
    exact hle hmem
  have hReq : R = W := le_antisymm hRW hWR
  have hR'card : Nat.card R' = Nat.card W := by rw [← hRcard, hReq]
  have hXK : Nat.card K = Nat.card (K ⧸ R') * Nat.card W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R', hR'card]
  have hWR' : ∀ w : K, (w : G) ∈ W → w ∈ R' := by
    intro w hw
    rw [← hReq] at hw
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  have hR'W : ∀ w : K, w ∈ R' → (w : G) ∈ W := fun w hw => hReq ▸ ⟨w, hw, rfl⟩
  have hinj : Function.Injective (π.comp (V.subgroupOf K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxW := hR'W _ hx
    have hxV : ((x : K) : G) ∈ V := x.2
    have h1 : ((x : K) : G) = 1 := Subgroup.disjoint_def.mp hdisj hxV hxW
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
  have hVbeq : (V.subgroupOf K).map π = (π.comp (V.subgroupOf K).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eV : V ≃* (V.subgroupOf K).map π :=
    ((Subgroup.subgroupOfEquivOfLe hVK).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hVbeq.symm)
  have hVbcard : Nat.card ((V.subgroupOf K).map π) = 4 := by
    rw [← Nat.card_congr eV.toEquiv, hV.card_four]
  have hVbk : IsKleinFour ((V.subgroupOf K).map π) :=
    ⟨hVbcard, (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two⟩
  obtain ⟨P, hP⟩ := hVsyl
  have hPcard : Nat.card (P : Subgroup K) = 4 := by
    rw [← hV.card_four, ← hP, Subgroup.card_map_of_injective K.subtype_injective]
  have hPidx : 4 * (P : Subgroup K).index = Nat.card K := by
    rw [← hPcard]
    exact Subgroup.card_mul_index (P : Subgroup K)
  have hPodd := P.not_dvd_index
  have hVbidx : 4 * ((V.subgroupOf K).map π).index = Nat.card (K ⧸ R') := by
    rw [← hVbcard]
    exact Subgroup.card_mul_index ((V.subgroupOf K).map π)
  have hidx : (P : Subgroup K).index = Nat.card W * ((V.subgroupOf K).map π).index := by
    have h : 4 * (P : Subgroup K).index =
        4 * (Nat.card W * ((V.subgroupOf K).map π).index) := by
      rw [hPidx, hXK, ← hVbidx]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hVbodd : ¬ 2 ∣ ((V.subgroupOf K).map π).index := fun h =>
    hPodd (hidx ▸ Dvd.dvd.mul_left h _)
  have hVbp : IsPGroup 2 ((V.subgroupOf K).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hVbcard]; norm_num)
  let VbS : Sylow 2 (K ⧸ R') := hVbp.toSylow hVbodd
  have hVbS : (VbS : Subgroup (K ⧸ R')) = (V.subgroupOf K).map π := rfl
  let tK : K := ⟨t, htK⟩
  have htb1 : π tK ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have htW := hR'W tK h
    have hodd' := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W htW)
    rw [ht2] at hodd'
    exact absurd hodd' (by decide)
  have htbV : π tK ∈ (V.subgroupOf K).map π := ⟨tK, htV, rfl⟩
  have hDmap : ((Subgroup.centralizer (V : Set G)).subgroupOf K).map π =
      (V.subgroupOf K).map π := by
    rw [← hsup, Subgroup.subgroupOf_sup hVK hWK, Subgroup.map_sup]
    have hWb : (W.subgroupOf K).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro w hw
      exact hWR' w hw
    rw [hWb, sup_bot_eq]
  have hCX : Subgroup.centralizer {π tK} = (V.subgroupOf K).map π := by
    apply le_antisymm
    · intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R' q
      rw [Subgroup.mem_centralizer_singleton_iff] at hq
      have hA : IsPGroup 2 (Subgroup.zpowers tK) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one])
      let α : Subgroup.zpowers tK →* MulAut K := MulAut.conj.comp (Subgroup.zpowers tK).subtype
      have hcop : ¬ 2 ∣ Nat.card R' := by
        rw [hR'card]
        exact fun h => (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h)
      obtain ⟨c, hc, hfix⟩ := (coprime_invariant_coset_fixed 2 hA α R' hcop g).2 (by
        intro a x hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
        have hcomm : Commute (π g) (π tK) := hq
        have hxg : π x = π g := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
          exact hx
        rw [← QuotientGroup.eq_one_iff]
        change π (g⁻¹ * ((a : K) * x * (a : K)⁻¹)) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxg, ← hk, map_zpow,
          ← (hcomm.zpow_right k).eq]
        group)
      have hct := hfix ⟨tK, Subgroup.mem_zpowers tK⟩
      change tK * c * tK⁻¹ = c at hct
      have hcD : (c : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [← hCK]
        refine Subgroup.mem_inf.mpr ⟨?_, c.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun x : K => (x : G)) hct
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        calc (c : G) * t = t * (c : G) * t⁻¹ * t := by rw [h]
          _ = t * c := by group
      have hgc : π g = π c := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact hc
      rw [hgc, ← hDmap]
      exact ⟨c, hcD, rfl⟩
    · intro q hq
      obtain ⟨v, hv, rfl⟩ := hq
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hvV : (v : G) ∈ V := hv
      have h := mul_comm_of_exponent_two hV.exponent_two (⟨v, hvV⟩ : V) ⟨t, htV⟩
      have h' : (v : G) * t = t * (v : G) := congrArg Subtype.val h
      simpa only [Subgroup.coe_mul] using h'
  have h3 := odd_core_free_selfcentralizing_four_group_involution_centralizer_three_alternatives
    (X := K ⧸ R') (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) VbS hVbk (π tK) htbV htb1 hCX
  obtain ⟨halt, -, -, -⟩ := h3
  have hm0 : 0 < Nat.card W := Nat.card_pos
  have hK12 : 12 * Nat.card W ≤ Nat.card K := hKM ▸ Subgroup.card_le_of_le inf_le_left
  have hHK : Nat.card H = 2 * Nat.card K := by
    have h := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH').toEquiv] at h
    have hri : (K.subgroupOf H).index = 2 := hKH
    rw [hri] at h
    omega
  have hcases : (Nonempty ((K ⧸ R') ≃* alternatingGroup (Fin 4)) ∧
        Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ R') .PSL 2 5 1 ∧
        Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W) := by
    rcases halt with h1 | h2 | h3
    · exfalso
      have h1' : (VbS : Subgroup (K ⧸ R')) = ⊤ := h1
      have hX4 : Nat.card (K ⧸ R') = 4 := by rw [← hVbcard, ← hVbS, h1', Subgroup.card_top]
      rw [hX4] at hXK
      omega
    · obtain ⟨e⟩ := h2
      have hX12 : Nat.card (K ⧸ R') = 12 := by
        rw [Nat.card_congr e.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)]
      rw [hX12] at hXK
      exact Or.inl ⟨⟨e⟩, by omega, by omega⟩
    · have hX60 : Nat.card (K ⧸ R') = 60 := h3.1
      rw [hX60] at hXK
      exact Or.inr ⟨h3.2, by omega, by omega⟩
  have hH2 : (CFSG.pPrimeCore 2 H).map H.subtype = W := by
    have hUodd : Odd (Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    have hUH : (CFSG.pPrimeCore 2 H).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hUK : (CFSG.pPrimeCore 2 H).map H.subtype ≤ K :=
      le_of_odd_card_of_relIndex_eq_two hKH hUH hUodd
    apply le_antisymm
    · have hUn : (((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K).Normal := by
        refine ⟨fun x hx k => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        refine ⟨⟨k, hKH' k.2⟩ * y * ⟨k, hKH' k.2⟩⁻¹,
          (inferInstance : (CFSG.pPrimeCore 2 H).Normal).conj_mem y hy _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        rw [hyx]
      have hUcard : Nat.card (((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K) =
          Nat.card ((CFSG.pPrimeCore 2 H).map H.subtype) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
      have hle : ((CFSG.pPrimeCore 2 H).map H.subtype).subgroupOf K ≤ R' :=
        le_sSup ⟨hUn, by rw [hUcard]; exact Nat.coprime_two_left.mpr hUodd⟩
      intro u hu
      exact hR'W ⟨u, hUK hu⟩ (hle hu)
    · have hWH : W ≤ H := Subgroup.le_normalizer
      have hWn : (W.subgroupOf H).Normal := Subgroup.normal_in_normalizer
      have hcardW : Nat.card (W.subgroupOf H) = Nat.card W :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
      have hle : W.subgroupOf H ≤ CFSG.pPrimeCore 2 H :=
        le_sSup ⟨hWn, by rw [hcardW]; exact Nat.coprime_two_left.mpr hWodd⟩
      intro w hw
      exact ⟨⟨w, hWH hw⟩, hle hw, rfl⟩
  have hVWb : ((V ⊔ W).subgroupOf K).map π = (V.subgroupOf K).map π := by
    rw [hsup]
    exact hDmap
  refine ⟨hReq, hH2, hWZ, ⟨hcases, fun h => by have := h.1.2.1; have := h.2.2.1; omega⟩,
    by rw [hVWb]; exact hVbk, ⟨VbS, by rw [hVWb]; exact hVbS⟩, fun tK' htK' => ?_⟩
  have : tK' = tK := Subtype.ext htK'
  rw [this, hVWb, hCX]

end CFSG.Semidihedral.Principal
