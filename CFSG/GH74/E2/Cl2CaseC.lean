module

public import CFSG.GH74.E2.Cl2CaseDefs
import CFSG.GH74.E2.Cl2Cl3

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q]

private theorem cC_sqsub_le (A : Subgroup Q) : sqsub A ≤ A :=
  (Subgroup.closure_le _).2 (fun w hw => by
    obtain ⟨u, hu, rfl⟩ := hw
    exact A.mul_mem hu hu)

private theorem cC_mem_sqsub {A : Subgroup Q} {u : Q} (hu : u ∈ A) : u * u ∈ sqsub A :=
  Subgroup.subset_closure ⟨u, hu, rfl⟩

private theorem cC_comm_mem_dsub (g h : Q) : ⁅g, h⁆ ∈ dsub Q :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)

private theorem cC_eq_one_of_zpow_odd (hQ : IsPGroup 2 Q) {x : Q} {m : ℤ}
    (hm : Odd m) (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hQ x
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : (orderOf x : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by rw [hj]; rfl))
  have h3 : (2 : ℤ) ∣ m := by
    refine dvd_trans ?_ h2
    rw [hj]
    rcases j with _ | j'
    · exact absurd rfl hj0
    · exact ⟨2 ^ j', by push_cast; ring⟩
  exact (Int.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)

private theorem cC_cube {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) : g (g (g x)) = x := by
  have := congrArg (fun f : MulAut Q => f x) hg
  simpa [pow_succ, MulAut.mul_apply] using this

private theorem cC_comm_of_closure {S : Set Q} (hS : Subgroup.closure S = ⊤)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : ∀ g h : Q, g * h = h * g := by
  have h1 : ∀ s ∈ S, ∀ g : Q, g * s = s * g := by
    intro s hs g
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set Q) := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hcomm s hs t ht
    have hg : g ∈ Subgroup.centralizer ({s} : Set Q) := hle (hS ▸ Subgroup.mem_top g)
    exact ((Subgroup.mem_centralizer_iff.1 hg) s rfl).symm
  intro g h
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set Q) := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact h1 t ht g
  have hh : h ∈ Subgroup.centralizer ({g} : Set Q) := hle (hS ▸ Subgroup.mem_top h)
  exact (Subgroup.mem_centralizer_iff.1 hh) g rfl

private theorem cC_dsub_le_center {S : Set Q} (hS : Subgroup.closure S = ⊤)
    (hcen : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ center Q) : dsub Q ≤ center Q := by
  have hπ : Subgroup.closure ((QuotientGroup.mk' (center Q)) '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, hS,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcomm : ∀ g h : Q ⧸ center Q, g * h = h * g := by
    refine cC_comm_of_closure hπ ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have h1 : (QuotientGroup.mk' (center Q)) ⁅s, t⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcen s hs t ht)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  refine Subgroup.commutator_le.2 (fun g _ h _ => ?_)
  have h1 : (QuotientGroup.mk' (center Q)) ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  exact (QuotientGroup.eq_one_iff _).1 h1

private theorem cC_invol_comm {g h : Q} (hg : g * g = 1) (hh : h * h = 1) :
    ⁅⁅g, h⁆, g⁆ = ⁅g, h⁆ * ⁅g, h⁆ := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  simp only [commutatorElement_def, hg', hh', mul_inv_rev, mul_assoc, hg, mul_one]

end Aux

section Bilin

variable {Q : Type*} [Group Q] {N : Subgroup Q}

private theorem cC_comm_mul_right {u k k' : Q} (h : ⁅u, k'⁆ ∈ center Q) :
    ⁅u, k * k'⁆ = ⁅u, k⁆ * ⁅u, k'⁆ := by
  have hc : k * ⁅u, k'⁆ = ⁅u, k'⁆ * k := Subgroup.mem_center_iff.1 h k
  calc ⁅u, k * k'⁆ = ⁅u, k⁆ * (k * ⁅u, k'⁆ * k⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅u, k⁆ * ⁅u, k'⁆ := by rw [hc]; group

private theorem cC_comm_mul_left {u v k : Q} (h : ⁅v, k⁆ ∈ center Q) :
    ⁅u * v, k⁆ = ⁅v, k⁆ * ⁅u, k⁆ := by
  have hc : u * ⁅v, k⁆ = ⁅v, k⁆ * u := Subgroup.mem_center_iff.1 h u
  calc ⁅u * v, k⁆ = (u * ⁅v, k⁆ * u⁻¹) * ⁅u, k⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅v, k⁆ * ⁅u, k⁆ := by rw [hc]; group

private theorem cC_comm_conj {g v k : Q} (hg : ⁅g, v⁆ ∈ center Q) (hv : ⁅v, k⁆ ∈ center Q) :
    ⁅g * v * g⁻¹, k⁆ = ⁅v, k⁆ := by
  have e : g * v * g⁻¹ = ⁅g, v⁆ * v := by simp only [commutatorElement_def]; group
  have h1 : ⁅⁅g, v⁆, k⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hg k).symm
  rw [e, cC_comm_mul_left hv, h1, mul_one]

private theorem cC_inner_mul (hNc : N ≤ center Q) (hcomm : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N)
    (g g' h k : Q) : ⁅⁅g * g', h⁆, k⁆ = ⁅⁅g, h⁆, k⁆ * ⁅⁅g', h⁆, k⁆ := by
  have e : ⁅g * g', h⁆ = (g * ⁅g', h⁆ * g⁻¹) * ⁅g, h⁆ := by
    simp only [commutatorElement_def]; group
  have hv : ⁅⁅g', h⁆, k⁆ ∈ center Q := hNc (hcomm _ (cC_comm_mem_dsub _ _) _)
  have hu : ⁅⁅g, h⁆, k⁆ ∈ center Q := hNc (hcomm _ (cC_comm_mem_dsub _ _) _)
  have hgv : ⁅g, ⁅g', h⁆⁆ ∈ center Q := by
    rw [← commutatorElement_inv]
    exact (center Q).inv_mem (hNc (hcomm _ (cC_comm_mem_dsub _ _) _))
  rw [e, cC_comm_mul_left hu, cC_comm_conj hgv hv]

private theorem cC_invol (hcomm : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N)
    (hsqN : ∀ n ∈ N, (∃ u ∈ dsub Q, n = u * u) → n = 1) {g h : Q} (hg : g * g = 1)
    (hh : h * h = 1) : ⁅⁅g, h⁆, g⁆ = 1 :=
  hsqN _ (hcomm _ (cC_comm_mem_dsub g h) g) ⟨⁅g, h⁆, cC_comm_mem_dsub g h, cC_invol_comm hg hh⟩

private theorem cC_key (hNc : N ≤ center Q) (hcomm : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N)
    (σ : MulAut Q) (hσ3 : ∀ z : Q, σ (σ (σ z)) = z) (hσN : ∀ n ∈ N, σ n = n → n = 1)
    {h₀ g₁ g₂ : Q} (hh₀ : σ h₀ = h₀) (hg₁ : σ g₁ = g₂) (hg₂ : σ g₂ = g₁ * g₂)
    (hd : ⁅⁅g₂, h₀⁆, g₂⁆ = 1) : ⁅⁅g₁, h₀⁆, g₂⁆ = 1 ∧ ⁅⁅g₂, h₀⁆, g₁⁆ = 1 := by
  have hZ : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ center Q := fun u hu z => hNc (hcomm u hu z)
  have e1 : σ ⁅⁅g₁, h₀⁆, g₂⁆ = ⁅⁅g₂, h₀⁆, g₁⁆ := by
    rw [map_commutatorElement, map_commutatorElement, hg₁, hh₀, hg₂,
      cC_comm_mul_right (hZ _ (cC_comm_mem_dsub _ _) _), hd, mul_one]
  have e2 : σ ⁅⁅g₂, h₀⁆, g₁⁆ = ⁅⁅g₁, h₀⁆, g₂⁆ := by
    rw [map_commutatorElement, map_commutatorElement, hg₂, hh₀, hg₁,
      cC_inner_mul hNc hcomm, hd, mul_one]
  have hfix : σ ⁅⁅g₁, h₀⁆, g₂⁆ = ⁅⁅g₁, h₀⁆, g₂⁆ := by
    have h3 := hσ3 ⁅⁅g₁, h₀⁆, g₂⁆
    rw [e1, e2] at h3
    exact h3
  have h1 : ⁅⁅g₁, h₀⁆, g₂⁆ = 1 := hσN _ (hcomm _ (cC_comm_mem_dsub _ _) _) hfix
  refine ⟨h1, ?_⟩
  rw [← e1, h1, map_one]

private theorem cC_pair (hNc : N ≤ center Q) (hcomm : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N)
    (hsqN : ∀ n ∈ N, (∃ u ∈ dsub Q, n = u * u) → n = 1) (σ : MulAut Q)
    (hσ3 : ∀ z : Q, σ (σ (σ z)) = z) (hσN : ∀ n ∈ N, σ n = n → n = 1)
    {h₀ g₁ g₂ : Q} (hh₀ : h₀ * h₀ = 1) (hg₁ : g₁ * g₁ = 1) (hg₂ : g₂ * g₂ = 1)
    (hσh : σ h₀ = h₀) (hσ₁ : σ g₁ = g₂) (hσ₂ : σ g₂ = g₁ * g₂) :
    ∀ s ∈ ({g₁, g₂} : Set Q), ∀ k ∈ ({g₁, g₂} : Set Q), ⁅⁅s, h₀⁆, k⁆ = 1 := by
  obtain ⟨k1, k2⟩ := cC_key hNc hcomm σ hσ3 hσN hσh hσ₁ hσ₂ (cC_invol hcomm hsqN hg₂ hh₀)
  rintro s (rfl | rfl) k (rfl | rfl)
  · exact cC_invol hcomm hsqN hg₁ hh₀
  · exact k1
  · exact k2
  · exact cC_invol hcomm hsqN hg₂ hh₀

end Bilin

section Fixed

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem cC_fix_comm {φ : MulAut Q} (hφ : ∀ u ∈ dsub Q, φ u = u → u = 1) {x x' : Q}
    (hx : φ x = x) (hx' : φ x' = x') : x * x' = x' * x := by
  have h1 : ⁅x, x'⁆ = 1 :=
    hφ _ (cC_comm_mem_dsub x x') (by rw [map_commutatorElement, hx, hx'])
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

private theorem cC_sq_eq_one [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N)
    (hrk : 16 ≤ (sqsub (dsub Q)).relIndex (dsub Q)) {φ : MulAut Q}
    (hφ : ∀ u ∈ dsub Q, φ u = u → u = 1) {x : Q} (hx : φ x = x) : x * x = 1 := by
  by_contra hne
  have hφs : φ (x * x) = x * x := by rw [map_mul, hx]
  have hscomm : ∀ u ∈ dsub Q, Commute u (x * x) := fun u hu =>
    commutatorElement_eq_one_iff_mul_comm.1 (h.sq_cent hQ hu x)
  have hint : ∀ v ∈ dsub Q, v ∈ Subgroup.zpowers (x * x) → v = 1 := by
    intro v hv hvs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hvs
    exact hφ _ hv (by rw [map_zpow, hφs])
  have hRV : Subgroup.zpowers ((x * x) * (x * x)) ≤ Subgroup.zpowers (x * x) :=
    Subgroup.zpowers_le.2 (Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
  have hbound := FourGen.relIndex_mul_le h.four (U := dsub Q) (V := Subgroup.zpowers (x * x))
    (RU := sqsub (dsub Q)) (RV := Subgroup.zpowers ((x * x) * (x * x)))
    (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      exact ((hscomm u hu).zpow_right k).eq)
    (cC_sqsub_le _) hRV
    (fun u hu r hr => by
      have hrD : r ∈ dsub Q := cC_sqsub_le _ hr
      rw [h.dsub_comm hQ u hu r hrD, mul_inv_cancel_right]
      exact hr)
    (fun v hv r hr => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hRV hr)
      rw [(Commute.zpow_zpow_self (x * x) i j).eq, mul_inv_cancel_right]
      exact hr)
    (fun u hu => cC_mem_sqsub hu)
    (fun v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      exact Subgroup.mem_zpowers_iff.2 ⟨k, (Commute.refl (x * x)).mul_zpow k⟩)
    (fun v hv => by
      have h1 : v = 1 := hint v hv.1 hv.2
      subst h1
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩)
  have hV0 : (Subgroup.zpowers ((x * x) * (x * x))).relIndex (Subgroup.zpowers (x * x)) ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_dvd_card (H := Subgroup.zpowers ((x * x) * (x * x)))
      (K := Subgroup.zpowers (x * x))
    rw [h0, zero_dvd_iff] at h1
    exact Nat.card_pos.ne' h1
  have hV1 : (Subgroup.zpowers ((x * x) * (x * x))).relIndex (Subgroup.zpowers (x * x)) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (h1 (Subgroup.mem_zpowers (x * x)))
    have e : (x * x * (x * x)) ^ m = (x * x) ^ (2 * m) := by
      rw [(Commute.refl (x * x)).mul_zpow, ← zpow_add, two_mul]
    rw [e] at hm
    have h2 : (x * x) ^ (2 * m - 1) = 1 := by
      rw [zpow_sub_one, hm, mul_inv_cancel]
    exact hne (cC_eq_one_of_zpow_odd hQ ⟨m - 1, by ring⟩ h2)
  have hV2 : 2 ≤ (Subgroup.zpowers ((x * x) * (x * x))).relIndex (Subgroup.zpowers (x * x)) := by
    omega
  have h32 := Nat.mul_le_mul hrk hV2
  exact absurd (le_trans h32 hbound) (by norm_num)

private theorem cC_quot_comm : ∀ x y : Q ⧸ dsub Q, x * y = y * x := by
  intro x y
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction y using QuotientGroup.induction_on with
    | H g' =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact cC_comm_mem_dsub _ _

private theorem cC_frattini_le [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N)
    (ha : ∀ x : Q, a x = x → x * x = 1) (hb : ∀ x : Q, b x = x → x * x = 1) :
    frattini Q ≤ dsub Q := by
  have hc := cC_quot_comm (Q := Q)
  let K : Subgroup (Q ⧸ dsub Q) :=
    { carrier := {z | z * z = 1}
      one_mem' := mul_one 1
      mul_mem' := fun {x y} hx hy => by
        have hx' : x * x = 1 := hx
        have hy' : y * y = 1 := hy
        show x * y * (x * y) = 1
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hc y x]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx', hy', one_mul]
      inv_mem' := fun {x} hx => by
        have hx' : x * x = 1 := hx
        show x⁻¹ * x⁻¹ = 1
        rw [← mul_inv_rev, hx', inv_one] }
  have hmk : ∀ g : Q, g * g = 1 → (QuotientGroup.mk g : Q ⧸ dsub Q) ∈ K := fun g hg => by
    show (QuotientGroup.mk g : Q ⧸ dsub Q) * QuotientGroup.mk g = 1
    rw [← QuotientGroup.mk_mul, hg, QuotientGroup.mk_one]
  have hle : fixSub a ⊔ fixSub b ≤ K.comap (QuotientGroup.mk' (dsub Q)) :=
    sup_le (fun x hx => hmk x (ha x hx)) (fun x hx => hmk x (hb x hx))
  rw [h.bpair.sup_fix hQ h.four] at hle
  have hexp : ∀ z : Q ⧸ dsub Q, z * z = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g => exact hle (Subgroup.mem_top g)
  have h2 : frattini (Q ⧸ dsub Q) = ⊥ := frattini_eq_bot_of_exponent_two hc hexp
  have h1 := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective (dsub Q))
  rw [h2] at h1
  intro x hx
  have := h1 hx
  simpa [QuotientGroup.eq_one_iff] using this

private theorem cC_apply_apply [Finite Q] (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N)
    (hΦ : frattini Q ≤ dsub Q) (hfb : ∀ u ∈ dsub Q, b u = u → u = 1)
    (hsb : ∀ x : Q, b x = x → x * x = 1) {x : Q} (hx : b x = x) : a (a x) = x * a x := by
  have hab : ∀ z : Q, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  have hbax : b (a x) = a x := by rw [← hab, hx]
  have hbaax : b (a (a x)) = a (a x) := by rw [← hab, hbax]
  have heps : eps a x = 1 := by
    apply hfb _ (hΦ (h.bpair.eps_a_mem hQ h.four hx))
    unfold eps
    rw [map_mul, map_mul, hx, hbax, hbaax]
  have hx1 : x * x = 1 := hsb x hx
  have hax1 : a x * a x = 1 := by rw [← map_mul, hx1, map_one]
  have hcomm : x * a x = a x * x := cC_fix_comm hfb hx hbax
  have hinv : (x * a x)⁻¹ = x * a x := by
    apply inv_eq_of_mul_eq_one_right
    calc x * a x * (x * a x) = x * (a x * x) * a x := by group
      _ = x * (x * a x) * a x := by rw [hcomm]
      _ = (x * x) * (a x * a x) := by group
      _ = 1 := by rw [hx1, hax1, one_mul]
  have h2 : a (a x) = (x * a x)⁻¹ := eq_inv_of_mul_eq_one_right heps
  rw [h2, hinv]

end Fixed

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

theorem caseC (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseCHyp Q a b N) : False := by
  obtain ⟨⟨hNab, hNa⟩, hsqN, hfa, hfb, hrk⟩ := hc
  have hcomm : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N := fun u hu z => h.comm_mem hQ hu z
  have hNc : N ≤ center Q := h.N_central
  have hNb : ∀ n ∈ N, b n = n → n = 1 := fun n hn hbn =>
    hNa n hn (by rw [hNab n hn, hbn])
  have hsa : ∀ x : Q, a x = x → x * x = 1 := fun x hx => cC_sq_eq_one hQ h hrk hfa hx
  have hsb : ∀ x : Q, b x = x → x * x = 1 := fun x hx => cC_sq_eq_one hQ h hrk hfb hx
  have hΦ : frattini Q ≤ dsub Q := cC_frattini_le hQ h hsa hsb
  have hab : ∀ z : Q, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  obtain ⟨x, hx, y, hy, hgen⟩ := h.bpair.exists_gens hQ h.four
  have hxb : b x = x := hx
  have hya : a y = y := commSub_le_fixSub_a h.bpair hy
  have hxb2 : b (a x) = a x := by rw [← hab, hxb]
  have hya2 : a (b y) = b y := by rw [hab, hya]
  have hx1 : x * x = 1 := hsb x hxb
  have hx2 : a x * a x = 1 := by rw [← map_mul, hx1, map_one]
  have hy1 : y * y = 1 := hsa y hya
  have hy2 : b y * b y = 1 := by rw [← map_mul, hy1, map_one]
  have hxx : a (a x) = x * a x := cC_apply_apply hQ h hΦ hfb hsb hxb
  have hyy : b (b y) = y * b y := cC_apply_apply hQ h.swap hΦ hfa hsa hya
  have hXY : ∀ t ∈ ({y, b y} : Set Q), ∀ s ∈ ({x, a x} : Set Q), ∀ k ∈ ({x, a x} : Set Q),
      ⁅⁅s, t⁆, k⁆ = 1 := by
    intro t ht
    have ht' : t * t = 1 ∧ a t = t := by
      rcases ht with rfl | ht
      · exact ⟨hy1, hya⟩
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact ⟨hy2, hya2⟩
    exact cC_pair hNc hcomm hsqN a (cC_cube h.bpair.a_cube) hNa ht'.1 hx1 hx2 ht'.2 rfl hxx
  have hYX : ∀ s ∈ ({x, a x} : Set Q), ∀ t ∈ ({y, b y} : Set Q), ∀ k ∈ ({y, b y} : Set Q),
      ⁅⁅t, s⁆, k⁆ = 1 := by
    intro s hs
    have hs' : s * s = 1 ∧ b s = s := by
      rcases hs with rfl | hs
      · exact ⟨hx1, hxb⟩
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact ⟨hx2, hxb2⟩
    exact cC_pair hNc hcomm hsqN b (cC_cube h.bpair.b_cube) hNb hs'.1 hy1 hy2 hs'.2 rfl hyy
  have hS : Subgroup.closure ({x, a x, y, b y} : Set Q) = ⊤ := hgen
  have hmemS : ∀ k ∈ ({x, a x, y, b y} : Set Q),
      k ∈ ({x, a x} : Set Q) ∨ k ∈ ({y, b y} : Set Q) := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk ⊢
    tauto
  have hXS : ∀ k ∈ ({x, a x} : Set Q), k ∈ ({x, a x, y, b y} : Set Q) := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk ⊢
    tauto
  have hYS : ∀ k ∈ ({y, b y} : Set Q), k ∈ ({x, a x, y, b y} : Set Q) := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk ⊢
    tauto
  have hcenXY : ∀ s ∈ ({x, a x} : Set Q), ∀ t ∈ ({y, b y} : Set Q), ⁅s, t⁆ ∈ center Q := by
    intro s hs t ht
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : Subgroup.closure ({x, a x, y, b y} : Set Q) ≤
        Subgroup.centralizer ({⁅s, t⁆} : Set Q) := by
      rw [Subgroup.closure_le]
      intro k hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      rcases hmemS k hk with hkX | hkY
      · have h1 : ⁅⁅s, t⁆, k⁆ = 1 := hXY t ht s hs k hkX
        exact commutatorElement_eq_one_iff_mul_comm.1 h1
      · have h1 : ⁅⁅t, s⁆, k⁆ = 1 := hYX s hs t ht k hkY
        have h2 : Commute ⁅t, s⁆ k := commutatorElement_eq_one_iff_mul_comm.1 h1
        have h3 : Commute ⁅s, t⁆ k := by
          rw [← commutatorElement_inv t s]
          exact h2.inv_left
        exact h3.eq
    have hg : g ∈ Subgroup.centralizer ({⁅s, t⁆} : Set Q) := hle (hS ▸ Subgroup.mem_top g)
    exact ((Subgroup.mem_centralizer_iff.1 hg) ⁅s, t⁆ rfl).symm
  have hXa : ∀ s ∈ ({x, a x} : Set Q), b s = s := by
    intro s hs
    rcases hs with rfl | hs
    · exact hxb
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hxb2
  have hYb : ∀ t ∈ ({y, b y} : Set Q), a t = t := by
    intro t ht
    rcases ht with rfl | ht
    · exact hya
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hya2
  have hcen : ∀ s ∈ ({x, a x, y, b y} : Set Q), ∀ t ∈ ({x, a x, y, b y} : Set Q),
      ⁅s, t⁆ ∈ center Q := by
    intro s hs t ht
    rcases hmemS s hs with hsX | hsY <;> rcases hmemS t ht with htX | htY
    · have : ⁅s, t⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (cC_fix_comm hfb (hXa s hsX) (hXa t htX))
      rw [this]
      exact (center Q).one_mem
    · exact hcenXY s hsX t htY
    · rw [← commutatorElement_inv t s]
      exact (center Q).inv_mem (hcenXY t htX s hsY)
    · have : ⁅s, t⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (cC_fix_comm hfa (hYb s hsY) (hYb t htY))
      rw [this]
      exact (center Q).one_mem
  have hDc : dsub Q ≤ center Q := cC_dsub_le_center hS hcen
  have hN : N = ⊥ := by
    rw [h.N_eq, eq_bot_iff, Subgroup.commutator_le]
    intro u hu k _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (hDc hu) k).symm
  exact h.N_ne hN

end CFSG.GH74.E2
