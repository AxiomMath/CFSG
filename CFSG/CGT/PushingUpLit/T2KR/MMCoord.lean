module

public import CFSG.CGT.PushingUpLit.T2KR.MMRoot
public import CFSG.CGT.PushingUpLit.T2KR.MMKappa
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization

noncomputable instance fintypeFq (n : ℕ) : Fintype (Fq n) := Fintype.ofFinite _

theorem card_Fq {n : ℕ} (hn : n ≠ 0) : Fintype.card (Fq n) = 2 ^ n := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 n hn

variable {G : Type} [Group G] [Finite G]

theorem two_roots_algebra {F : Type} [Field F] [Fintype F] [CharP F 2] {w θ s₁ s₂ : F}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h12 : s₁ ≠ s₂) (hc₁ : s₁ * w + θ * sqrtF s₁ = 0)
    (hc₂ : s₂ * w + θ * sqrtF s₂ = 0) : w = 0 ∧ θ = 0 := by
  have ha : sqrtF s₁ ^ 2 = s₁ := sqrtF_sq s₁
  have hb : sqrtF s₂ ^ 2 = s₂ := sqrtF_sq s₂
  have ha0 : sqrtF s₁ ≠ 0 := fun h => h₁ (by rw [← ha, h]; ring)
  have hb0 : sqrtF s₂ ≠ 0 := fun h => h₂ (by rw [← hb, h]; ring)
  have e1 : sqrtF s₁ * w + θ = 0 := by
    have : sqrtF s₁ * (sqrtF s₁ * w + θ) = 0 := by
      linear_combination hc₁ + w * ha
    exact (mul_eq_zero.1 this).resolve_left ha0
  have e2 : sqrtF s₂ * w + θ = 0 := by
    have : sqrtF s₂ * (sqrtF s₂ * w + θ) = 0 := by
      linear_combination hc₂ + w * hb
    exact (mul_eq_zero.1 this).resolve_left hb0
  have hab : sqrtF s₁ ≠ sqrtF s₂ := fun h => h12 (by rw [← ha, ← hb, h])
  have h3 : (sqrtF s₁ - sqrtF s₂) * w = 0 := by linear_combination e1 - e2
  have hw : w = 0 := (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hab)
  refine ⟨hw, ?_⟩
  rw [hw, mul_zero, zero_add] at e1
  exact e1

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem n_ne_zero : n ≠ 0 := by have := H.nat.two_le; omega

include H in
theorem hcard : Fintype.card (Fq n) = 2 ^ n := card_Fq H.n_ne_zero

include H in
theorem two_lt_card : 2 < Fintype.card (Fq n) := by
  rw [H.hcard]
  have := H.nat.two_le
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this

theorem exists_decomp {u : G} (hu : u ∈ QM L M) :
    ∃ p : (Fin 2 → Fq n) × Fq n, ∀ g, kap H.D u g =
      coboundaryA (mu2 (F := Fq n)) p.1 g + p.2 • f0 g := by
  obtain ⟨B, hB⟩ := exists_sub_mem_B1A (a := n) H.hcard (by have := H.nat.two_le; omega)
    (kappa_mem_Z1A H.nat H.D H.le H.normal hu)
  obtain ⟨w, hw⟩ := hB
  refine ⟨(w, B), fun g => ?_⟩
  have := congrFun hw g
  simp only [Pi.sub_apply, Pi.smul_apply] at this
  show _ = coboundaryA (mu2 (F := Fq n)) w g + B • f0 g
  rw [this]
  abel

include H in
theorem decomp_unique {w w' : Fin 2 → Fq n} {B B' : Fq n}
    (h : ∀ g, coboundaryA (mu2 (F := Fq n)) w g + B • f0 g =
      coboundaryA (mu2 (F := Fq n)) w' g + B' • f0 g) : w = w' ∧ B = B' := by
  have h1 : (B - B') • (f0 : SL2 (Fq n) → Fin 2 → Fq n) ∈ B1A (mu2 (F := Fq n)) := by
    refine ⟨w' - w, ?_⟩
    funext g
    have := h g
    simp only [map_sub, sub_smul, Pi.smul_apply, coboundaryA_apply] at this ⊢
    linear_combination (norm := module) (-1 : Fq n) • this
  have hB : B - B' = 0 := eq_zero_of_smul_f0_mem_B1A H.two_lt_card h1
  have hBB : B = B' := sub_eq_zero.1 hB
  subst hBB
  refine ⟨?_, rfl⟩
  have h2 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (Fq n), g • (w - w') = w - w' := by
    intro g
    have := h g
    simp only [coboundaryA_apply, mu2_apply] at this
    show (g : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec (w - w') = w - w'
    rw [Matrix.mulVec_sub]
    linear_combination (norm := module) this
  exact sub_eq_zero.1 (CFSG.QuasithinUnique.Setup.Campbell.eq_zero_of_forall_smul_eq h2)

@[expose] noncomputable def decomp (u : ↥(QM L M)) : (Fin 2 → Fq n) × Fq n :=
  Classical.choose (H.exists_decomp u.2)

@[expose] noncomputable def vco (u : ↥(QM L M)) : Fin 2 → Fq n := (H.decomp u).1

@[expose] noncomputable def theta (u : ↥(QM L M)) : Fq n := (H.decomp u).2

theorem kap_eq (u : ↥(QM L M)) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    kap H.D u g = coboundaryA (mu2 (F := Fq n)) (H.vco u) g + H.theta u • f0 g :=
  Classical.choose_spec (H.exists_decomp u.2) g

include H in
theorem vco_mul (u u' : ↥(QM L M)) : H.vco (u * u') = H.vco u + H.vco u' ∧
    H.theta (u * u') = H.theta u + H.theta u' := by
  refine H.decomp_unique (fun g => ?_)
  rw [← H.kap_eq, map_add, Pi.add_apply, add_smul]
  have h1 : kap H.D ((u * u' : ↥(QM L M)) : G) g = kap H.D u g + kap H.D u' g :=
    kappa_mul_left H.nat H.D H.normal u.2 u'.2 g
  rw [h1, H.kap_eq u, H.kap_eq u']
  abel

include H in
theorem blockU_le_QM : blockU L ≤ QM L M := fun v hv =>
  ⟨H.le (blockU_le L hv), Subgroup.mem_centralizer_iff.2 fun w hw => H.nat.blockU_comm w hw v hv⟩

include H in
theorem vco_blockU {v : G} (hv : v ∈ blockU L) :
    H.vco ⟨v, H.blockU_le_QM hv⟩ = H.D.ψe v ∧ H.theta ⟨v, H.blockU_le_QM hv⟩ = 0 := by
  refine H.decomp_unique (fun g => ?_)
  rw [← H.kap_eq, zero_smul, add_zero]
  exact kappa_blockU H.D hv g

include H in
theorem eq_one_of_coords {u : ↥(QM L M)} (h1 : H.vco u = 0) (h2 : H.theta u = 0) :
    (u : G) = 1 := by
  have h0 : kap H.D u = 0 := by
    funext g
    rw [H.kap_eq u g, h1, h2]
    simp [coboundaryA_apply]
  have hC := (kappa_eq_zero_iff H.nat H.D H.le H.normal u.2).1 h0
  rw [H.C_G] at hC
  exact Subgroup.mem_bot.1 hC

include H in
theorem coords_injective {u u' : ↥(QM L M)} (h1 : H.vco u = H.vco u')
    (h2 : H.theta u = H.theta u') : u = u' := by
  have hm := H.vco_mul (u * u'⁻¹) u'
  have e : u * u'⁻¹ * u' = u := by group
  rw [e] at hm
  have hv : H.vco (u * u'⁻¹) = 0 := by
    have := hm.1
    rw [h1] at this
    exact add_eq_right.1 this.symm
  have ht : H.theta (u * u'⁻¹) = 0 := by
    have := hm.2
    rw [h2] at this
    exact add_eq_right.1 this.symm
  have h1' := H.eq_one_of_coords hv ht
  have : u * u'⁻¹ = 1 := Subtype.ext h1'
  exact mul_inv_eq_one.1 this

include H in
theorem theta_eq_zero_iff (u : ↥(QM L M)) : H.theta u = 0 ↔ (u : G) ∈ blockU L := by
  constructor
  · intro hθ
    let v : ↥(QM L M) := ⟨H.vec (H.vco u), H.blockU_le_QM (H.vec_mem _)⟩
    have hv := H.vco_blockU (H.vec_mem (H.vco u))
    have := H.coords_injective (u := u) (u' := v) (by rw [hv.1, H.ψe_vec]) (by rw [hv.2, hθ])
    rw [this]
    exact H.vec_mem _
  · intro hu
    exact (H.vco_blockU (v := u) hu).2

include H in
theorem commutator_mem_V {x : G} (hx : x ∈ L ⊔ QM L M) {u : G} (hu : u ∈ QM L M) :
    u⁻¹ * (x * u * x⁻¹) ∈ blockU L := by
  obtain ⟨l, hl, q, hq, rfl⟩ := H.mem_LQ_iff.1 hx
  have hqu : q * u = u * q := H.Q_comm q hq u hu
  have e : u⁻¹ * (l * q * u * (l * q)⁻¹) = delta u l := by
    have h1 : q * u * q⁻¹ = u := by rw [hqu]; group
    calc u⁻¹ * (l * q * u * (l * q)⁻¹) = u⁻¹ * (l * (q * u * q⁻¹) * l⁻¹) := by group
      _ = delta u l := by rw [h1]; simp only [delta]; group
  rw [e]
  exact H.nat.delta_mem H.normal hu hl

include H in
theorem rho_mul_eq {l q : G} (hl : l ∈ L) (hq : q ∈ QM L M) (hx : l * q ∈ L ⊔ QM L M) :
    H.rho ⟨l * q, hx⟩ = H.D.φ ⟨l, hl⟩ := by
  have : (⟨l * q, hx⟩ : ↥(L ⊔ QM L M)) =
      ⟨l, (le_sup_left : L ≤ L ⊔ QM L M) hl⟩ * ⟨q, (le_sup_right : QM L M ≤ L ⊔ QM L M) hq⟩ :=
    rfl
  rw [this, map_mul, H.rho_of_mem_L hl, H.rho_of_mem_Q hq, mul_one]

include H in
theorem psie_delta {x u : G} (hx : x ∈ L ⊔ QM L M) (hu : u ∈ QM L M) :
    H.D.ψe (u⁻¹ * (x * u * x⁻¹)) = kap H.D u (H.rho ⟨x, hx⟩) := by
  obtain ⟨l, hl, q, hq, rfl⟩ := H.mem_LQ_iff.1 hx
  rw [H.rho_mul_eq hl hq hx, kappa_apply H.nat H.D H.le H.normal hu hl]
  congr 1
  have hqu : q * u = u * q := H.Q_comm q hq u hu
  have h1 : q * u * q⁻¹ = u := by rw [hqu]; group
  calc u⁻¹ * (l * q * u * (l * q)⁻¹) = u⁻¹ * (l * (q * u * q⁻¹) * l⁻¹) := by group
    _ = delta u l := by rw [h1]; simp only [delta]; group

include H in
theorem commutes_iff {x u : G} (hx : x ∈ L ⊔ QM L M) (hu : u ∈ QM L M) :
    x * u = u * x ↔ kap H.D u (H.rho ⟨x, hx⟩) = 0 := by
  rw [← H.psie_delta hx hu]
  have hv := H.commutator_mem_V hx hu
  constructor
  · intro h
    have : u⁻¹ * (x * u * x⁻¹) = 1 := by rw [h]; group
    rw [this, H.D.ψe_one]
  · intro h
    have h1 : u⁻¹ * (x * u * x⁻¹) = 1 := H.ψe_injOn hv (one_mem _) (by rw [h, H.D.ψe_one])
    calc x * u = (u * (u⁻¹ * (x * u * x⁻¹))) * x := by group
      _ = u * x := by rw [h1]; group

theorem kap_uMat (u : ↥(QM L M)) (s : Fq n) :
    kap H.D u (uMat s) = ![s * H.vco u 1 + H.theta u * sqrtF s, 0] := by
  rw [H.kap_eq, f0_uMat]
  funext i
  fin_cases i
  · simp [coboundaryA_apply, mu2_apply, uMat_coe, dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]
  · simp [coboundaryA_apply, mu2_apply, uMat_coe, dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

include H in
theorem mem_of_two_roots {X : Subgroup G} (hX : X ≤ L ⊔ QM L M) {x₁ x₂ : G} (hx₁ : x₁ ∈ X)
    (hx₂ : x₂ ∈ X) {s₁ s₂ : Fq n} (hρ₁ : H.rho ⟨x₁, hX hx₁⟩ = uMat s₁)
    (hρ₂ : H.rho ⟨x₂, hX hx₂⟩ = uMat s₂) (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) (h12 : s₁ ≠ s₂) {u : G}
    (hu : u ∈ QM L M) (hc : u ∈ Subgroup.centralizer (X : Set G)) :
    u ∈ blockU L ∧ H.D.ψe u 1 = 0 := by
  have key : ∀ (x : G) (hxX : x ∈ X) (s : Fq n), H.rho ⟨x, hX hxX⟩ = uMat s →
      s * H.vco ⟨u, hu⟩ 1 + H.theta ⟨u, hu⟩ * sqrtF s = 0 := by
    intro x hxX s hρ
    have h1 : x * u = u * x := Subgroup.mem_centralizer_iff.1 hc x hxX
    have h2 := (H.commutes_iff (hX hxX) hu).1 h1
    rw [hρ] at h2
    exact congrFun ((H.kap_uMat ⟨u, hu⟩ s).symm.trans h2) 0
  obtain ⟨hw, hθ⟩ := two_roots_algebra h₁ h₂ h12 (key x₁ hx₁ s₁ hρ₁) (key x₂ hx₂ s₂ hρ₂)
  have huV : u ∈ blockU L := (H.theta_eq_zero_iff ⟨u, hu⟩).1 hθ
  refine ⟨huV, ?_⟩
  rw [← (H.vco_blockU huV).1]
  exact hw

include H in
theorem centralizer_QM_eq_of_three_le (X : Subgroup G) (hX : X ≤ L ⊔ QM L M)
    (hX2 : ∀ x ∈ X, x * x = 1) (h3 : 3 ≤ (X ⊓ QM L M).relIndex X) :
    QM L M ⊓ Subgroup.centralizer (X : Set G) = blockU L ⊓ Subgroup.centralizer (X : Set G) ∧
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (X : Set G)) = Nat.card (Fq n) := by
  have hne : ¬ X ≤ QM L M := by
    intro h
    rw [inf_of_le_left h, Subgroup.relIndex_self] at h3
    omega
  refine ⟨?_, H.card_CV_eq X hX hX2 hne⟩
  refine le_antisymm ?_ (inf_le_inf_right _ H.blockU_le_QM)
  obtain ⟨p, hp⟩ := H.exists_root_point X hX hX2
  obtain ⟨x₀, rfl⟩ := exists_smul_pt0 p
  have hρ' : ∀ x (hx : x ∈ X), (H.twist x₀).rho ⟨x, hX hx⟩ ∈
      rootGrp (pt0 : ℙ (Fq n) (Fin 2 → Fq n)) := by
    intro x hx
    rw [H.twist_rho]
    exact mem_rootGrp_smul_iff.1 (hp ⟨⟨x, hx⟩, rfl⟩)
  have hS : ∀ x (hx : x ∈ X), ∃ s : Fq n, (H.twist x₀).rho ⟨x, hX hx⟩ = uMat s := by
    intro x hx
    have := hρ' x hx
    rw [rootGrp_pt0] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨Multiplicative.toAdd t, ht.symm⟩
  have hcard := (H.twist x₀).relIndex_eq_card_range X hX
  have h3' : 2 < Nat.card ((H.twist x₀).rhoOn X hX).range := by omega
  have hfin : Fintype ↥((H.twist x₀).rhoOn X hX).range := Fintype.ofFinite _
  have h3'' : 2 < Fintype.card ↥((H.twist x₀).rhoOn X hX).range := by
    rw [← Nat.card_eq_fintype_card]
    exact h3'
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3''
  have hpar : ∀ r : ↥((H.twist x₀).rhoOn X hX).range, ∃ (x : G) (hx : x ∈ X) (s : Fq n),
      (H.twist x₀).rho ⟨x, hX hx⟩ = uMat s ∧ (r : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) = uMat s := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    obtain ⟨s, hs⟩ := hS x x.2
    exact ⟨x, x.2, s, hs, hs⟩
  obtain ⟨xa, hxa, sa, hρa, hra⟩ := hpar a
  obtain ⟨xb, hxb, sb, hρb, hrb⟩ := hpar b
  obtain ⟨xc, hxc, sc, hρc, hrc⟩ := hpar c
  have hne_ab : sa ≠ sb := fun h => hab (Subtype.ext (by rw [hra, hrb, h]))
  have hne_ac : sa ≠ sc := fun h => hac (Subtype.ext (by rw [hra, hrc, h]))
  have hne_bc : sb ≠ sc := fun h => hbc (Subtype.ext (by rw [hrb, hrc, h]))
  intro u hu
  have key : ∀ {x₁ x₂ : G} (h₁ : x₁ ∈ X) (h₂ : x₂ ∈ X) {s₁ s₂ : Fq n},
      (H.twist x₀).rho ⟨x₁, hX h₁⟩ = uMat s₁ → (H.twist x₀).rho ⟨x₂, hX h₂⟩ = uMat s₂ →
      s₁ ≠ 0 → s₂ ≠ 0 → s₁ ≠ s₂ → u ∈ blockU L ⊓ Subgroup.centralizer (X : Set G) := by
    intro x₁ x₂ h₁ h₂ s₁ s₂ hρ₁ hρ₂ n₁ n₂ n₁₂
    exact ⟨((H.twist x₀).mem_of_two_roots hX h₁ h₂ hρ₁ hρ₂ n₁ n₂ n₁₂ hu.1 hu.2).1, hu.2⟩
  by_cases h0a : sa = 0
  · exact key hxb hxc hρb hρc (fun h => hne_ab (h0a.trans h.symm)) (fun h => hne_ac (h0a.trans h.symm)) hne_bc
  · by_cases h0b : sb = 0
    · exact key hxa hxc hρa hρc h0a (fun h => hne_bc (h0b.trans h.symm)) hne_ac
    · exact key hxa hxb hρa hρb h0a h0b hne_ab

end MData

end CFSG.CGT.PushingUpLit.T2KR
