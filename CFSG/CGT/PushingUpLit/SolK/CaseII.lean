module

public import CFSG.CGT.PushingUpLit.SolK.CaseIIStruct

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

theorem comm_of_odd_order {G : Type*} [Group G] {y t₁ τ : G} (hodd : Odd (orderOf y))
    (ht₁ : y * t₁ * y⁻¹ = t₁) (hsq : t₁ * t₁ = 1)
    (hdich : y * τ * y⁻¹ * τ⁻¹ = 1 ∨ y * τ * y⁻¹ * τ⁻¹ = t₁) : y * τ * y⁻¹ = τ := by
  have h2 : (y * y) * τ * (y * y)⁻¹ = τ := by
    rcases hdich with h | h
    · have h' : y * τ * y⁻¹ = τ := by
        calc y * τ * y⁻¹ = (y * τ * y⁻¹ * τ⁻¹) * τ := by group
          _ = τ := by rw [h, one_mul]
      calc (y * y) * τ * (y * y)⁻¹ = y * (y * τ * y⁻¹) * y⁻¹ := by group
        _ = τ := by rw [h', h']
    · have h' : y * τ * y⁻¹ = t₁ * τ := by
        calc y * τ * y⁻¹ = (y * τ * y⁻¹ * τ⁻¹) * τ := by group
          _ = t₁ * τ := by rw [h]
      calc (y * y) * τ * (y * y)⁻¹ = y * (y * τ * y⁻¹) * y⁻¹ := by group
        _ = y * (t₁ * τ) * y⁻¹ := by rw [h']
        _ = (y * t₁ * y⁻¹) * (y * τ * y⁻¹) := by group
        _ = t₁ * (t₁ * τ) := by rw [ht₁, h']
        _ = (t₁ * t₁) * τ := by rw [mul_assoc]
        _ = τ := by rw [hsq, one_mul]
  have hC : y * y ∈ Subgroup.centralizer ({τ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 h2
  obtain ⟨k, hk⟩ := hodd
  have hy : y = (y * y) ^ (k + 1) := by
    have h1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h1, one_mul]
  have hyC : y ∈ Subgroup.centralizer ({τ} : Set G) := by
    rw [hy]
    exact Subgroup.pow_mem _ hC _
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  calc y * τ * y⁻¹ = (τ * y) * y⁻¹ := by rw [hyC]
    _ = τ := by group

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

omit [Finite G] S in
theorem swap_ne_one' {d : ℕ} {a b : Fin d} (hab : a ≠ b) : swap a b ≠ 1 := by
  intro h
  have := congrArg (fun f : Perm (Fin d) => f a) h
  simp only [swap_apply_left, Perm.one_apply] at this
  exact hab this.symm

theorem caseII_false_of_unique (hP : TightDataPlus S) (hU : TQUnique M X) {g : G} (hgM : g ∉ M)
    (hTM : conjSubgroup g (rOf M X) ≤ M) (hcard : 3 ≤ Nat.card ↥(rOf M X))
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) : False := by
  classical
  set R := rOf M X with hR
  set Q := pCoreOf 2 M with hQ
  set T := conjSubgroup g R with hT
  obtain ⟨a, b, hab, ⟨s, hsM, hsT, hsθ⟩, hallθ, t₁, ht₁T, ht₁W, ht₁1, hTQ'⟩ :=
    S.TQ_structure hP hU hgM hTM hcard hTQ
  have hRle : ∀ r ∈ R, g⁻¹ * r * g ∈ M := S.R_le_conj hP hTM hcard
  have hRT : ∀ r ∈ R, ∀ τ ∈ T, r * τ * r⁻¹ = τ := S.comm_RT hP hgM hTM hcard
  have hQle : ∀ q ∈ Q, g⁻¹ * q * g ∈ M := S.Q_le_conj hP hTQ
  set T'' := conjSubgroup g⁻¹ R with hT''
  have hmem'' : ∀ x, x ∈ T'' ↔ g * x * g⁻¹ ∈ R := fun x => by
    rw [hT'', mem_conjSubgroup]
    simp
  have hTM'' : T'' ≤ M := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ R := (hmem'' x).1 hx
    have h2 := hRle _ h1
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [this] at h2
  have hgM'' : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hTQne'' : T'' ⊓ Q ≠ ⊥ := fun h => S.false_of_caseI hP hTM'' h hcard
  obtain ⟨a'', b'', hab'', -, hallθ'', t₁'', ht₁''T, ht₁''W, ht₁''1, hTQ''⟩ :=
    S.TQ_structure hP hU hgM'' hTM'' hcard hTQne''
  have hodd : ∀ y : G, ∀ hy : y ∈ M, S.θ ⟨y, hy⟩ = 1 → Odd (orderOf y) →
      ∀ r ∈ R, y * r * y⁻¹ = r := by
    intro y hy hθy hoy
    have hyW : ∀ w ∈ S.D.W, y * w * y⁻¹ = w :=
      (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨y, hy⟩).1 hθy
    have hyt₁ : y * t₁ * y⁻¹ = t₁ := hyW t₁ ht₁W
    have ht₁sq : t₁ * t₁ = 1 := by
      have := S.D.sq ht₁W
      rwa [pow_two] at this
    have hyT : ∀ τ ∈ T, y * τ * y⁻¹ ∈ T := fun τ hτ =>
      S.conjR_normal_of_comm g ht₁T ht₁1 hyt₁ hτ
    have hyτ : ∀ τ ∈ T, y * τ * y⁻¹ = τ := by
      intro τ hτ
      refine comm_of_odd_order hoy hyt₁ ht₁sq ?_
      have hcT : y * τ * y⁻¹ * τ⁻¹ ∈ T := T.mul_mem (hyT τ hτ) (T.inv_mem hτ)
      have hτM : τ ∈ M := hTM hτ
      have hcM : y * τ * y⁻¹ * τ⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem (M.mul_mem hy hτM) (M.inv_mem hy)) (M.inv_mem hτM)
      have hθc : S.θ ⟨y * τ * y⁻¹ * τ⁻¹, hcM⟩ = 1 := by
        have : (⟨y * τ * y⁻¹ * τ⁻¹, hcM⟩ : ↥M) =
            ⟨y, hy⟩ * ⟨τ, hτM⟩ * ⟨y, hy⟩⁻¹ * ⟨τ, hτM⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hθy]
        group
      have hcQ : y * τ * y⁻¹ * τ⁻¹ ∈ Q := hP.ker_two ⟨_, hcM⟩ hθc (conjR_two g hcT)
      exact hTQ' _ hcT hcQ
    have hr₁ : g⁻¹ * t₁ * g ∈ R := mem_conjSubgroup.1 ht₁T
    have hr₁1 : g⁻¹ * t₁ * g ≠ 1 := by
      intro h
      apply ht₁1
      have : t₁ = g * (g⁻¹ * t₁ * g) * g⁻¹ := by group
      rw [this, h]
      group
    have hy'M : g⁻¹ * y * g ∈ M := by
      refine S.mem_M_of_comm_R hr₁ hr₁1 ?_
      calc (g⁻¹ * y * g) * (g⁻¹ * t₁ * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * t₁ * y⁻¹) * g := by group
        _ = g⁻¹ * t₁ * g := by rw [hyt₁]
    set y' : G := g⁻¹ * y * g with hy'
    have hoy' : Odd (orderOf y') := by
      have h1 : orderOf ((MulAut.conj g⁻¹).toMonoidHom y) = orderOf y :=
        orderOf_injective _ (MulAut.conj g⁻¹).injective y
      have h2 : (MulAut.conj g⁻¹).toMonoidHom y = y' := by
        simp [hy']
      rw [h2] at h1
      rw [h1]
      exact hoy
    have hy'T'' : ∀ τ ∈ T'', y' * τ * y'⁻¹ ∈ T'' := by
      intro τ hτ
      rw [hmem''] at hτ ⊢
      have h1 : y * (g * τ * g⁻¹) * y⁻¹ ∈ R := S.R_normalized hy hτ
      have : g * (y' * τ * y'⁻¹) * g⁻¹ = y * (g * τ * g⁻¹) * y⁻¹ := by rw [hy']; group
      rw [this]
      exact h1
    have hdich'' : ∀ τ ∈ T'', y' * τ * y'⁻¹ * τ⁻¹ = 1 ∨ y' * τ * y'⁻¹ * τ⁻¹ = t₁'' := by
      intro τ hτ
      have hτM : τ ∈ M := hTM'' hτ
      have hyτT : y' * τ * y'⁻¹ ∈ T'' := hy'T'' τ hτ
      have hyτM : y' * τ * y'⁻¹ ∈ M := M.mul_mem (M.mul_mem hy'M hτM) (M.inv_mem hy'M)
      have hcT : y' * τ * y'⁻¹ * τ⁻¹ ∈ T'' := T''.mul_mem hyτT (T''.inv_mem hτ)
      have hcM : y' * τ * y'⁻¹ * τ⁻¹ ∈ M := M.mul_mem hyτM (M.inv_mem hτM)
      have hθyτ : S.θ ⟨y' * τ * y'⁻¹, hyτM⟩ =
          S.θ ⟨y', hy'M⟩ * S.θ ⟨τ, hτM⟩ * (S.θ ⟨y', hy'M⟩)⁻¹ := by
        have : (⟨y' * τ * y'⁻¹, hyτM⟩ : ↥M) = ⟨y', hy'M⟩ * ⟨τ, hτM⟩ * ⟨y', hy'M⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv]
      have hθc : S.θ ⟨y' * τ * y'⁻¹ * τ⁻¹, hcM⟩ = 1 := by
        have hcdef : (⟨y' * τ * y'⁻¹ * τ⁻¹, hcM⟩ : ↥M) =
            ⟨y' * τ * y'⁻¹, hyτM⟩ * ⟨τ, hτM⟩⁻¹ := rfl
        rw [hcdef, map_mul, map_inv]
        rcases hallθ'' τ hτM hτ with h1 | h1
        · rw [hθyτ, h1]
          group
        · have hθ1 : S.θ ⟨y' * τ * y'⁻¹, hyτM⟩ = swap a'' b'' := by
            rcases hallθ'' _ hyτM hyτT with h2 | h2
            · exfalso
              rw [h1] at hθyτ
              rw [h2] at hθyτ
              apply swap_ne_one' hab''
              have h3 : (S.θ ⟨y', hy'M⟩)⁻¹ * 1 * S.θ ⟨y', hy'M⟩ =
                  (S.θ ⟨y', hy'M⟩)⁻¹ * (S.θ ⟨y', hy'M⟩ * swap a'' b'' *
                    (S.θ ⟨y', hy'M⟩)⁻¹) * S.θ ⟨y', hy'M⟩ := by rw [hθyτ]
              simpa [mul_assoc] using h3.symm
            · exact h2
          rw [hθ1, h1]
          group
      have hcQ : y' * τ * y'⁻¹ * τ⁻¹ ∈ Q := hP.ker_two ⟨_, hcM⟩ hθc (conjR_two g⁻¹ hcT)
      exact hTQ'' _ hcT hcQ
    have ht₁''y' : y' * t₁'' * y'⁻¹ = t₁'' := by
      have h1 : y' * t₁'' * y'⁻¹ ∈ T'' := hy'T'' t₁'' ht₁''T
      have h2 : y' * t₁'' * y'⁻¹ ∈ Q := pCoreOf_normalized M hy'M (S.W_le_Q ht₁''W)
      have h3 : y' * t₁'' * y'⁻¹ ≠ 1 := by
        intro h
        apply ht₁''1
        have : t₁'' = y'⁻¹ * (y' * t₁'' * y'⁻¹) * y' := by group
        rw [this, h]
        group
      rcases hTQ'' _ h1 h2 with h | h
      · exact absurd h h3
      · exact h
    have ht₁''sq : t₁'' * t₁'' = 1 := by
      have := S.D.sq ht₁''W
      rwa [pow_two] at this
    have hy'τ : ∀ τ ∈ T'', y' * τ * y'⁻¹ = τ := fun τ hτ =>
      comm_of_odd_order hoy' ht₁''y' ht₁''sq (hdich'' τ hτ)
    intro r hr
    have hrT'' : g⁻¹ * r * g ∈ T'' := by
      rw [hmem'']
      have : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
      rw [this]
      exact hr
    have h4 := hy'τ _ hrT''
    have e : y' * (g⁻¹ * r * g) * y'⁻¹ = g⁻¹ * (y * r * y⁻¹) * g := by rw [hy']; group
    rw [e] at h4
    have h5 := congrArg (fun z => g * z * g⁻¹) h4
    have e1 : g * (g⁻¹ * (y * r * y⁻¹) * g) * g⁻¹ = y * r * y⁻¹ := by group
    have e2 : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    rw [e1, e2] at h5
    exact h5
  have hD : ∀ y : G, ∀ hy : y ∈ M, S.θ ⟨y, hy⟩ = 1 → ∀ r ∈ R, y * r * y⁻¹ = r := by
    intro y hy hθy r hr
    obtain ⟨k, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hym'M : y ^ m' ∈ M := M.pow_mem hy m'
    have hθym' : S.θ ⟨y ^ m', hym'M⟩ = 1 := by
      have : (⟨y ^ m', hym'M⟩ : ↥M) = (⟨y, hy⟩ : ↥M) ^ m' := rfl
      rw [this, map_pow, hθy, one_pow]
    have hym'2 : ∃ i : ℕ, (y ^ m') ^ (2 ^ i) = 1 :=
      ⟨k, by rw [← pow_mul, mul_comm, ← hm]; exact pow_orderOf_eq_one y⟩
    have hym'Q : y ^ m' ∈ Q := hP.ker_two ⟨y ^ m', hym'M⟩ hθym' hym'2
    have h1 : y ^ m' ∈ Subgroup.centralizer ({r} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hP.abelian _ hym'Q r hr.1
    have hy2kM : y ^ (2 ^ k) ∈ M := M.pow_mem hy _
    have hθy2k : S.θ ⟨y ^ (2 ^ k), hy2kM⟩ = 1 := by
      have : (⟨y ^ (2 ^ k), hy2kM⟩ : ↥M) = (⟨y, hy⟩ : ↥M) ^ (2 ^ k) := rfl
      rw [this, map_pow, hθy, one_pow]
    have hodd2k : Odd (orderOf (y ^ (2 ^ k))) := by
      have h1 : (y ^ (2 ^ k)) ^ m' = 1 := by
        rw [← pow_mul, ← hm]
        exact pow_orderOf_eq_one y
      exact hm'.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    have h2 : y ^ (2 ^ k) ∈ Subgroup.centralizer ({r} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.1 (hodd _ hy2kM hθy2k hodd2k r hr)
    have hcop : Nat.Coprime m' (2 ^ k) := (Nat.coprime_two_right.2 hm').pow_right k
    have hC : y ∈ Subgroup.centralizer ({r} : Set G) :=
      mem_of_pow_mem_of_coprime _ hcop h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff] at hC
    calc y * r * y⁻¹ = (r * y) * y⁻¹ := by rw [hC]
      _ = r := by group
  have hmul : ∀ a b : G, (∀ r ∈ R, a * r * a⁻¹ = r) → (∀ r ∈ R, b * r * b⁻¹ = r) →
      ∀ r ∈ R, (a * b) * r * (a * b)⁻¹ = r := by
    intro a b ha hb r hr
    calc (a * b) * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
      _ = r := by rw [hb r hr, ha r hr]
  have hseven : ∀ m : G, ∀ hm : m ∈ M, Equiv.Perm.sign (S.θ ⟨m, hm⟩) = 1 →
      ∀ r ∈ R, m * r * m⁻¹ = r := by
    intro m hm hsign
    have hmalt : S.θ ⟨m, hm⟩ ∈ alternatingGroup (Fin (2 * n + 1)) :=
      Equiv.Perm.mem_alternatingGroup.2 hsign
    obtain ⟨x, hx⟩ := S.D.ρ_surj _ hmalt
    have hxM : (x : G) ∈ M := S.hyp.le x.2
    have hθx : S.θ ⟨(x : G), hxM⟩ = S.θ ⟨m, hm⟩ := by
      rw [S.θ_X x]
      exact hx
    have hdM : (x : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hxM) hm
    have hθd : S.θ ⟨(x : G)⁻¹ * m, hdM⟩ = 1 := by
      have : (⟨(x : G)⁻¹ * m, hdM⟩ : ↥M) = (⟨(x : G), hxM⟩ : ↥M)⁻¹ * ⟨m, hm⟩ := rfl
      rw [this, map_mul, map_inv, hθx, inv_mul_cancel]
    have hd := hD _ hdM hθd
    have hm_eq : m = (x : G) * ((x : G)⁻¹ * m) := by group
    intro r hr
    rw [hm_eq]
    exact hmul _ _ (fun r hr => X_comm_R x.2 hr) hd r hr
  have hsodd : ∀ r ∈ R, s * r * s⁻¹ = r := fun r hr => comm_symm (hRT r hr s hsT)
  have hMc : ∀ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ = r := by
    intro m hm
    rcases (by decide : ∀ u : ℤˣ, u = 1 ∨ u = -1) (Equiv.Perm.sign (S.θ ⟨m, hm⟩)) with h | h
    · exact hseven m hm h
    · have hms : m * s⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hsM)
      have hsign : Equiv.Perm.sign (S.θ ⟨m * s⁻¹, hms⟩) = 1 := by
        have : (⟨m * s⁻¹, hms⟩ : ↥M) = ⟨m, hm⟩ * (⟨s, hsM⟩ : ↥M)⁻¹ := rfl
        rw [this, map_mul, map_inv, map_mul, map_inv, h, hsθ, Equiv.Perm.sign_swap hab]
        decide
      have hm_eq : m = (m * s⁻¹) * s := by group
      intro r hr
      rw [hm_eq]
      exact hmul _ _ (hseven _ hms hsign) hsodd r hr
  have hsθ1 : S.θ ⟨s, hsM⟩ ≠ 1 := by
    rw [hsθ]
    exact swap_ne_one' hab
  obtain ⟨w₀, hw₀, hw₀s⟩ : ∃ w₀ ∈ S.D.W, s * w₀ * s⁻¹ ≠ w₀ := by
    by_contra h
    push Not at h
    exact hsθ1 ((theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨s, hsM⟩).2 h)
  have hw₀Q : w₀ ∈ Q := S.W_le_Q hw₀
  have hgw : g⁻¹ * w₀ * g ∈ M := hQle w₀ hw₀Q
  have hrs : g⁻¹ * s * g ∈ R := mem_conjSubgroup.1 hsT
  have hcomm := hMc _ hgw _ hrs
  have e : (g⁻¹ * w₀ * g) * (g⁻¹ * s * g) * (g⁻¹ * w₀ * g)⁻¹ = g⁻¹ * (w₀ * s * w₀⁻¹) * g := by
    group
  rw [e] at hcomm
  have h5 := congrArg (fun z => g * z * g⁻¹) hcomm
  have e1 : g * (g⁻¹ * (w₀ * s * w₀⁻¹) * g) * g⁻¹ = w₀ * s * w₀⁻¹ := by group
  have e2 : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rw [e1, e2] at h5
  exact hw₀s (comm_symm h5)

theorem caseII_false (hP : TightDataPlus S) {g : G} (hgM : g ∉ M)
    (hTM : conjSubgroup g (rOf M X) ≤ M) (hcard : 3 ≤ Nat.card ↥(rOf M X))
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥) : False :=
  S.caseII_false_of_unique hP (S.tqUnique_of_two_le hP) hgM hTM hcard hTQ

theorem rSmall_of_two_le (hP : TightDataPlus S) : RSmall S := by
  refine S.rSmall_of_caseII hP fun g hg hTM _ hTQ => ?_
  by_contra hRS
  unfold RSmall at hRS
  exact S.caseII_false hP hg hTM (by omega) hTQ

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
