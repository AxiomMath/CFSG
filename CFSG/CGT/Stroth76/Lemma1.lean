module

public import CFSG.CGT.Stroth76.Lemma1Data
public import CFSG.CGT.Stroth77.Extension22Data
public import CFSG.CGT.Stroth76.NoInv
public import CFSG.CGT.Stroth77.Arch76Frame

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

theorem torus300_two_decomp : ∀ y : Torus (Type300.k 2),
    y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b := by
  decide +kernel

theorem torus310_two_decomp : ∀ y : Torus (Type310.k 2),
    y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b := by
  decide +kernel

theorem torus200_one_decomp : ∀ y : Torus (Type200.k 1),
    y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b := by
  decide +kernel

theorem torus201_one_decomp : ∀ y : Torus (Type201.k 1),
    y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b := by
  decide +kernel

section Shapes

variable {X : Type*} [Group X] {C : Subgroup X} {τ : StrothTypeIndex}

theorem closure_eq_of_decomp (W : StrothWeakTypeData C τ)
    (hdec : ∀ y : Torus τ.k,
      y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b) :
    C = Subgroup.closure {(W.c : X), (W.a : X), (W.b : X)} := by
  apply le_antisymm
  · intro x hx
    have h := W.ofTorus_e ⟨x, hx⟩
    rw [hdec (W.e (Additive.ofMul ⟨x, hx⟩)), W.ofTorus_add, W.ofTorus_add, W.ofTorus_nsmul,
      W.ofTorus_nsmul, W.ofTorus_nsmul, ← W.c_eq, ← W.a_eq, ← W.b_eq] at h
    rw [← show ((⟨x, hx⟩ : C) : X) = x from rfl, ← h]
    have hc : (W.c : X) ∈ Subgroup.closure {(W.c : X), (W.a : X), (W.b : X)} :=
      Subgroup.subset_closure (by simp)
    have ha : (W.a : X) ∈ Subgroup.closure {(W.c : X), (W.a : X), (W.b : X)} :=
      Subgroup.subset_closure (by simp)
    have hb : (W.b : X) ∈ Subgroup.closure {(W.c : X), (W.a : X), (W.b : X)} :=
      Subgroup.subset_closure (by simp)
    exact mul_mem (mul_mem (pow_mem hc _) (pow_mem ha _)) (pow_mem hb _)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [W.c.2, W.a.2, W.b.2]

theorem images_t300_two (W : StrothWeakTypeData C (StrothTypeIndex.t300 2)) :
    W.uv⁻¹ * W.c * W.uv = (W.c : X) * (W.a : X)⁻¹ * (W.b : X)⁻¹ ∧
      W.t⁻¹ * W.c * W.t = (W.c : X) * W.a ∧ W.u⁻¹ * W.c * W.u = (W.c : X) ∧
      W.ρ⁻¹ * W.c * W.ρ = (W.c : X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_neg,
      ← W.ofTorus_neg, ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.conj_ofTorus W.u_mem W.u_conj]
    congr 1; decide
  · rw [W.c_eq, W.conj_ofTorus W.ρ_mem W.ρ_conj]
    congr 1; decide

theorem images_t310_two {h : 2 ≤ 2} (W : StrothWeakTypeData C (StrothTypeIndex.t310 2 h)) :
    W.uv⁻¹ * W.c * W.uv = (W.c : X) * W.a * (W.b : X)⁻¹ ∧
      W.t⁻¹ * W.c * W.t = (W.c : X) * W.a * (W.b : X) ^ 2 ∧
      W.u⁻¹ * W.c * W.u = (W.c : X)⁻¹ ∧ W.ρ⁻¹ * W.c * W.ρ = (W.c : X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_neg,
      ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide +revert
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_nsmul,
      ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide +revert
  · rw [W.c_eq, W.conj_ofTorus W.u_mem W.u_conj, ← W.ofTorus_neg]
    congr 1; decide +revert
  · rw [W.c_eq, W.conj_ofTorus W.ρ_mem W.ρ_conj]
    congr 1; decide +revert

theorem images_t200_one (W : StrothWeakTypeData C (StrothTypeIndex.t200 1)) :
    W.uv⁻¹ * W.a * W.uv = (W.c : X) * W.a * (W.b : X) ^ 2 ∧
      W.uv⁻¹ * W.b * W.uv = (W.c : X) * W.b * (W.a : X) ^ 2 ∧
      W.t⁻¹ * W.a * W.t = (W.a : X)⁻¹ ∧
      W.t⁻¹ * W.b * W.t = (W.c : X) * (W.b : X)⁻¹ * (W.a : X)⁻¹ ^ 2 ∧
      W.u⁻¹ * W.a * W.u = (W.b : X) ∧ W.ρ⁻¹ * W.a * W.ρ = (W.b : X) ∧
      W.ρ⁻¹ * W.b * W.ρ = (W.c : X) * (W.a : X)⁻¹ * (W.b : X)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_nsmul,
      ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_nsmul,
      ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.a_eq, W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_neg]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_neg,
      ← W.ofTorus_neg, ← W.ofTorus_nsmul, ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.a_eq, W.b_eq, W.conj_ofTorus W.u_mem W.u_conj]
    congr 1; decide
  · rw [W.a_eq, W.b_eq, W.conj_ofTorus W.ρ_mem W.ρ_conj]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, W.conj_ofTorus W.ρ_mem W.ρ_conj, ← W.ofTorus_neg,
      ← W.ofTorus_neg, ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide

theorem images_t201_one (W : StrothWeakTypeData C (StrothTypeIndex.t201 1)) :
    W.uv⁻¹ * ((W.a : X) * W.c) * W.uv =
        (W.c : X) * ((W.a : X) * W.c) ^ 5 * ((W.b : X) * W.c) ^ 2 ∧
      W.uv⁻¹ * ((W.b : X) * W.c) * W.uv =
        (W.c : X) * ((W.b : X) * W.c) ^ 5 * ((W.a : X) * W.c) ^ 2 ∧
      W.t⁻¹ * ((W.a : X) * W.c) * W.t = ((W.a : X) * W.c)⁻¹ ∧
      W.t⁻¹ * ((W.b : X) * W.c) * W.t =
        (W.c : X) * ((W.b : X) * W.c) ^ 3 * ((W.a : X) * W.c)⁻¹ ^ 2 ∧
      W.u⁻¹ * ((W.a : X) * W.c) * W.u = (W.b : X) * W.c ∧
      W.ρ⁻¹ * ((W.a : X) * W.c) * W.ρ = (W.b : X) * W.c ∧
      W.ρ⁻¹ * ((W.b : X) * W.c) * W.ρ = ((W.a : X) * W.c)⁻¹ * ((W.b : X) * W.c)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_nsmul, ← W.ofTorus_nsmul, ← W.ofTorus_add,
      ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.uv_mem W.uv_conj, ← W.ofTorus_nsmul, ← W.ofTorus_nsmul, ← W.ofTorus_add,
      ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, ← W.ofTorus_add, W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_neg]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.t_mem W.t_conj, ← W.ofTorus_neg, ← W.ofTorus_nsmul, ← W.ofTorus_nsmul,
      ← W.ofTorus_add, ← W.ofTorus_add]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.u_mem W.u_conj]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.ρ_mem W.ρ_conj]
    congr 1; decide
  · rw [W.c_eq, W.a_eq, W.b_eq, ← W.ofTorus_add, ← W.ofTorus_add,
      W.conj_ofTorus W.ρ_mem W.ρ_conj, ← W.ofTorus_neg, ← W.ofTorus_neg, ← W.ofTorus_add]
    congr 1; decide

end Shapes

theorem mem_normalizer_centralizer_of_mem {X : Type*} [Group X] {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (H : Set X) : Set X) := by
  have key : ∀ k ∈ Subgroup.normalizer (H : Set X), ∀ c ∈ Subgroup.centralizer (H : Set X),
      k * c * k⁻¹ ∈ Subgroup.centralizer (H : Set X) := by
    intro k hk c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : k⁻¹ * a * k ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) a).mp ha
      simpa using this
    have hca := Subgroup.mem_centralizer_iff.mp hc _ ha'
    calc a * (k * c * k⁻¹) = k * ((k⁻¹ * a * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * a * k)) * k⁻¹ := by rw [hca]
      _ = k * c * k⁻¹ * a := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

variable {X : Type*} [Group X] [Finite X]

theorem card_centralizer_of_ne (K : Config X)
    (hC : Nat.card (Subgroup.centralizer (K.A : Set X)) ∣ 2 ^ 7)
    (hne : Subgroup.centralizer (K.A : Set X) ≠ K.A) :
    Nat.card (Subgroup.centralizer (K.A : Set X)) = 2 * Nat.card K.A ∨
      Nat.card (Subgroup.centralizer (K.A : Set X)) = 4 * Nat.card K.A := by
  have hAC : K.A ≤ Subgroup.centralizer (K.A : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => K.comm hb ha
  have hdvd : Nat.card K.A ∣ Nat.card (Subgroup.centralizer (K.A : Set X)) :=
    Subgroup.card_dvd_of_le hAC
  rw [K.hAcard] at hdvd ⊢
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hC
  have hne' : Nat.card (Subgroup.centralizer (K.A : Set X)) ≠ 32 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hAC (by rw [h, K.hAcard])).symm
  rw [hk'] at hdvd hne' ⊢
  interval_cases k <;> simp_all <;> omega

theorem arch76Lemma1 (K : Config X) (hρodd : Odd (orderOf K.ρ)) {C : Subgroup X}
    (hCA : Subgroup.centralizer (K.A : Set X) = C) (hC : Nat.card C ∣ 2 ^ 7) (hne : C ≠ K.A)
    (hE : ∀ g ∈ C, g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) → g ∈ K.A) :
    IsMulCommutative C ∧
    ((∃ a b : X, C = Subgroup.closure {K.w, a, b} ∧ a ^ 2 = K.x ∧ b ^ 2 = K.y ∧
        K.uv⁻¹ * a * K.uv = K.w * a * b ^ 2 ∧ K.uv⁻¹ * b * K.uv = K.w * b * a ^ 2 ∧
        K.t⁻¹ * a * K.t = a⁻¹ ∧ K.t⁻¹ * b * K.t = K.w * b⁻¹ * a⁻¹ ^ 2 ∧
        K.u⁻¹ * a * K.u = b ∧ K.ρ⁻¹ * a * K.ρ = b ∧ K.ρ⁻¹ * b * K.ρ = K.w * a⁻¹ * b⁻¹) ∨
      (∃ a b : X, C = Subgroup.closure {K.w, a, b} ∧ a ^ 2 = K.x ∧ b ^ 2 = K.y ∧
        K.uv⁻¹ * a * K.uv = K.w * a ^ 5 * b ^ 2 ∧ K.uv⁻¹ * b * K.uv = K.w * b ^ 5 * a ^ 2 ∧
        K.t⁻¹ * a * K.t = a⁻¹ ∧ K.t⁻¹ * b * K.t = K.w * b ^ 3 * a⁻¹ ^ 2 ∧
        K.u⁻¹ * a * K.u = b ∧ K.ρ⁻¹ * a * K.ρ = b ∧ K.ρ⁻¹ * b * K.ρ = a⁻¹ * b⁻¹) ∨
      (∃ c : X, C = Subgroup.closure {c, K.x, K.y} ∧ c ^ 2 = K.w ∧
        K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x ∧
        K.u⁻¹ * c * K.u = c ∧ K.ρ⁻¹ * c * K.ρ = c) ∨
      (∃ c : X, C = Subgroup.closure {c, K.x, K.y} ∧ c ^ 2 = K.w ∧
        K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2 ∧
        K.u⁻¹ * c * K.u = c⁻¹ ∧ K.ρ⁻¹ * c * K.ρ = c)) := by
  subst hCA
  have hρ3 := rho_cube_eq_one K hρodd hC
  set D := dataA K hρ3 with hD
  have hAC : K.A ≤ Subgroup.centralizer (K.A : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => K.comm hb ha
  have hNC := fun {g : X} (hg : g ∈ Subgroup.normalizer (K.A : Set X)) =>
    mem_normalizer_centralizer_of_mem hg
  have hL : D.L ≤ Subgroup.normalizer (Subgroup.centralizer (K.A : Set X) : Set X) := by
    rw [hD, dataA_L, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exacts [hNC (uv_mem_normalizer_A K), hNC (t_mem_normalizer_A K), hNC (u_mem_normalizer_A K),
      hNC (ρ_mem_normalizer_A K)]
  have hcard := card_centralizer_of_ne K hC hne
  have hV := conj_mem_of_card_le_four hAC le_rfl (by rcases hcard with h | h <;> omega)
    (hNC (uv_mem_normalizer_A K)) (uv_mem_normalizer_A K) (hNC (t_mem_normalizer_A K))
    (t_mem_normalizer_A K) (hNC (ρ_mem_normalizer_A K)) (ρ_mem_normalizer_A K)
    (uv_mul_self K) K.huvt K.hρuv K.hρt
  have hH : NoInvolutionsCentralizing (Subgroup.centralizer (K.A : Set X)) K.A :=
    noInvolutionsCentralizing_of_conj_mem K le_rfl (fun b hb _ => hb) hE
      (fun z hz => (hV z hz).1) (fun z hz => (hV z hz).2)
  have hDc : (D.c : X) = K.w := dataA_c hρ3
  have hDa : (D.a : X) = K.x := dataA_a hρ3
  have hDb : (D.b : X) = K.y := dataA_b hρ3
  have hDuv : D.uv = K.uv := rfl
  have hDt : D.t = K.t := rfl
  have hDu : D.u = K.u := rfl
  have hDρ : D.ρ = K.ρ := rfl
  rcases hcard with h2 | h4
  · obtain ⟨d, -, hd2, hD'⟩ := strothTypeData_t300_or_t310_of_data D hAC le_rfl h2 hL hH le_rfl hne
    rcases hD' with ⟨D', huv, ht, hu, hρ, hc, ha, hb⟩ | ⟨D', huv, ht, hu, hρ, hc, ha, hb⟩
    · refine ⟨D'.toWeak.isMulCommutative, Or.inr (Or.inr (Or.inl ⟨d, ?_⟩))⟩
      have hcl := closure_eq_of_decomp D'.toWeak torus300_two_decomp
      obtain ⟨h1, h2, h3, h4⟩ := images_t300_two D'.toWeak
      change D'.uv⁻¹ * (D'.c : X) * D'.uv = (D'.c : X) * (D'.a : X)⁻¹ * (D'.b : X)⁻¹ at h1
      change D'.t⁻¹ * (D'.c : X) * D'.t = (D'.c : X) * (D'.a : X) at h2
      change D'.u⁻¹ * (D'.c : X) * D'.u = (D'.c : X) at h3
      change D'.ρ⁻¹ * (D'.c : X) * D'.ρ = (D'.c : X) at h4
      change _ = Subgroup.closure {(D'.c : X), (D'.a : X), (D'.b : X)} at hcl
      rw [huv, ht, hu, hρ, hDuv, hDt, hDu, hDρ, hc, ha, hb, hDa, hDb] at *
      exact ⟨hcl, by rw [pow_two, hd2, hDc], h1, h2, h3, h4⟩
    · refine ⟨D'.toWeak.isMulCommutative, Or.inr (Or.inr (Or.inr ⟨d, ?_⟩))⟩
      have hcl := closure_eq_of_decomp D'.toWeak torus310_two_decomp
      obtain ⟨h1, h2, h3, h4⟩ := images_t310_two D'.toWeak
      change D'.uv⁻¹ * (D'.c : X) * D'.uv = (D'.c : X) * (D'.a : X) * (D'.b : X)⁻¹ at h1
      change D'.t⁻¹ * (D'.c : X) * D'.t = (D'.c : X) * (D'.a : X) * (D'.b : X) ^ 2 at h2
      change D'.u⁻¹ * (D'.c : X) * D'.u = (D'.c : X)⁻¹ at h3
      change D'.ρ⁻¹ * (D'.c : X) * D'.ρ = (D'.c : X) at h4
      change _ = Subgroup.closure {(D'.c : X), (D'.a : X), (D'.b : X)} at hcl
      rw [huv, ht, hu, hρ, hDuv, hDt, hDu, hDρ, hc, ha, hb, hDa, hDb] at *
      exact ⟨hcl, by rw [pow_two, hd2, hDc], h1, h2, h3, h4⟩
  · obtain ⟨e, f, he, hf, hD'⟩ := strothTypeData_t200_or_t201_of_data D hAC le_rfl h4 hL hH
      le_rfl hne
    rcases hD' with ⟨D', huv, ht, hu, hρ, hc, ha, hb⟩ | ⟨D', huv, ht, hu, hρ, hc, ha, hb⟩
    · refine ⟨D'.toWeak.isMulCommutative, Or.inl ⟨e, f, ?_⟩⟩
      have hcl := closure_eq_of_decomp D'.toWeak torus200_one_decomp
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := images_t200_one D'.toWeak
      change D'.uv⁻¹ * (D'.a : X) * D'.uv = (D'.c : X) * (D'.a : X) * (D'.b : X) ^ 2 at h1
      change D'.uv⁻¹ * (D'.b : X) * D'.uv = (D'.c : X) * (D'.b : X) * (D'.a : X) ^ 2 at h2
      change D'.t⁻¹ * (D'.a : X) * D'.t = (D'.a : X)⁻¹ at h3
      change D'.t⁻¹ * (D'.b : X) * D'.t = (D'.c : X) * (D'.b : X)⁻¹ * (D'.a : X)⁻¹ ^ 2 at h4
      change D'.u⁻¹ * (D'.a : X) * D'.u = (D'.b : X) at h5
      change D'.ρ⁻¹ * (D'.a : X) * D'.ρ = (D'.b : X) at h6
      change D'.ρ⁻¹ * (D'.b : X) * D'.ρ = (D'.c : X) * (D'.a : X)⁻¹ * (D'.b : X)⁻¹ at h7
      change _ = Subgroup.closure {(D'.c : X), (D'.a : X), (D'.b : X)} at hcl
      rw [huv, ht, hu, hρ, hDuv, hDt, hDu, hDρ, hc, ha, hb, hDc] at *
      exact ⟨hcl, by rw [pow_two, he, hDa], by rw [pow_two, hf, hDb], h1, h2, h3, h4, h5, h6, h7⟩
    · refine ⟨D'.toWeak.isMulCommutative, Or.inr (Or.inl ⟨(e : X) * K.w, (f : X) * K.w, ?_⟩)⟩
      have hcl := closure_eq_of_decomp D'.toWeak torus201_one_decomp
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := images_t201_one D'.toWeak
      have hcomm := D'.toWeak.isMulCommutative
      change D'.uv⁻¹ * ((D'.a : X) * D'.c) * D'.uv =
        (D'.c : X) * ((D'.a : X) * D'.c) ^ 5 * ((D'.b : X) * D'.c) ^ 2 at h1
      change D'.uv⁻¹ * ((D'.b : X) * D'.c) * D'.uv =
        (D'.c : X) * ((D'.b : X) * D'.c) ^ 5 * ((D'.a : X) * D'.c) ^ 2 at h2
      change D'.t⁻¹ * ((D'.a : X) * D'.c) * D'.t = ((D'.a : X) * D'.c)⁻¹ at h3
      change D'.t⁻¹ * ((D'.b : X) * D'.c) * D'.t =
        (D'.c : X) * ((D'.b : X) * D'.c) ^ 3 * ((D'.a : X) * D'.c)⁻¹ ^ 2 at h4
      change D'.u⁻¹ * ((D'.a : X) * D'.c) * D'.u = (D'.b : X) * D'.c at h5
      change D'.ρ⁻¹ * ((D'.a : X) * D'.c) * D'.ρ = (D'.b : X) * D'.c at h6
      change D'.ρ⁻¹ * ((D'.b : X) * D'.c) * D'.ρ =
        ((D'.a : X) * D'.c)⁻¹ * ((D'.b : X) * D'.c)⁻¹ at h7
      change _ = Subgroup.closure {(D'.c : X), (D'.a : X), (D'.b : X)} at hcl
      rw [huv, ht, hu, hρ, hDuv, hDt, hDu, hDρ, hc, ha, hb, hDc] at *
      have hw2 : K.w * K.w = 1 := by rw [← pow_two, K.hw]
      have hwC : K.w ∈ Subgroup.centralizer (K.A : Set X) := hAC K.w_mem
      have hew : (e : X) * K.w = K.w * e :=
        Subgroup.mul_comm_of_mem_isMulCommutative _ e.2 hwC
      have hfw : (f : X) * K.w = K.w * f :=
        Subgroup.mul_comm_of_mem_isMulCommutative _ f.2 hwC
      refine ⟨?_, ?_, ?_, h1, h2, h3, h4, h5, h6, h7⟩
      · refine hcl.trans ?_
        have hw : K.w ∈ Subgroup.closure {K.w, (e : X) * K.w, (f : X) * K.w} :=
          Subgroup.subset_closure (by simp)
        have hew' : (e : X) * K.w ∈ Subgroup.closure {K.w, (e : X) * K.w, (f : X) * K.w} :=
          Subgroup.subset_closure (by simp)
        have hfw' : (f : X) * K.w ∈ Subgroup.closure {K.w, (e : X) * K.w, (f : X) * K.w} :=
          Subgroup.subset_closure (by simp)
        have hw0 : K.w ∈ Subgroup.closure {K.w, (e : X), (f : X)} :=
          Subgroup.subset_closure (by simp)
        have he0 : (e : X) ∈ Subgroup.closure {K.w, (e : X), (f : X)} :=
          Subgroup.subset_closure (by simp)
        have hf0 : (f : X) ∈ Subgroup.closure {K.w, (e : X), (f : X)} :=
          Subgroup.subset_closure (by simp)
        apply le_antisymm
        · rw [Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          · exact hw
          · simpa using mul_mem hew' (inv_mem hw)
          · simpa using mul_mem hfw' (inv_mem hw)
        · rw [Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          · exact hw0
          · exact mul_mem he0 hw0
          · exact mul_mem hf0 hw0
      · calc ((e : X) * K.w) ^ 2 = (e : X) * (K.w * e) * K.w := by rw [pow_two]; group
          _ = (e : X) * ((e : X) * K.w) * K.w := by rw [← hew]
          _ = (e : X) * e * (K.w * K.w) := by group
          _ = K.x := by rw [hw2, mul_one, he, hDa]
      · calc ((f : X) * K.w) ^ 2 = (f : X) * (K.w * f) * K.w := by rw [pow_two]; group
          _ = (f : X) * ((f : X) * K.w) * K.w := by rw [← hfw]
          _ = (f : X) * f * (K.w * K.w) := by group
          _ = K.y := by rw [hw2, mul_one, hf, hDb]
