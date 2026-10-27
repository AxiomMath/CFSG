module

public import CFSG.CGT.PushingUpLit.A78G0.TorusK
public import CFSG.CGT.PushingUpLit.A78G0.Diag
public import CFSG.CGT.PushingUpLit.A78G0.KCount

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.CGT.PushingUpLit.A78L3 CFSG.ABGLocalTools Matrix

section Generic

variable {G : Type} [Group G] {L V K : Subgroup G} {F : Type} [Field F]

theorem rho_pow (D : NatCoordK G L V K F) {l : G} (hl : l ∈ L) (n : ℕ) :
    D.ρ (l ^ n) = D.ρ l ^ n := by
  induction n with
  | zero => simp [D.ρ_one]
  | succ n ih => rw [pow_succ, D.ρ_mul _ (pow_mem hl n) _ hl, ih, pow_succ]

end Generic

section RhoK

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  {h : G0Core G L₁ L₂ V W Z Z₂ e} {y : G}

theorem Torus₀.exists_rho_K (hy : Torus₀ h y) (D : NatCoordK G L₁ V Z (GaloisField 2 e))
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :
    ∃ k ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G), D.ρ k = u := by
  obtain ⟨l, hl, rfl⟩ := D.ρ_surj u
  obtain ⟨v, hv, k, hk, rfl⟩ := hy.decomp hl
  refine ⟨k, hk, ?_⟩
  rw [D.ρ_mul v (h.V_le_L hv) k (Subgroup.mem_inf.1 hk).1, (D.ρ_eq_one v (h.V_le_L hv)).2 hv,
    one_mul]

theorem Torus₀.rho_inj_K (hy : Torus₀ h y) (D : NatCoordK G L₁ V Z (GaloisField 2 e)) {k k' : G}
    (hk : k ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G))
    (hk' : k' ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G)) (hρ : D.ρ k = D.ρ k') : k = k' := by
  have h1 : k'⁻¹ * k ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G) := mul_mem (inv_mem hk') hk
  have h2 : D.ρ (k'⁻¹ * k) = 1 := by
    rw [D.ρ_mul _ (inv_mem (Subgroup.mem_inf.1 hk').1) _ (Subgroup.mem_inf.1 hk).1,
      D.ρ_inv (Subgroup.mem_inf.1 hk').1, hρ, inv_mul_cancel]
  have h3 : k'⁻¹ * k ∈ V := (D.ρ_eq_one _ (Subgroup.mem_inf.1 h1).1).1 h2
  have h4 : k'⁻¹ * k ∈ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V := Subgroup.mem_inf.2 ⟨h1, h3⟩
  rw [hy.inf_V, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.1 h4).symm

theorem Torus₀.exists_eta (hy : Torus₀ h y) (D : NatCoordK G L₁ V Z (GaloisField 2 e))
    (fr : S4Side.Frame h.pair.side₁ D) {t : GaloisField 2 e} (ht : t ≠ 0) :
    ∃ η s : G, η ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G) ∧
      s ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G) ∧
      (D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = t • D.κ fr.n₀ ∧
      (D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = t⁻¹ • fr.y₀ ∧
      (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = fr.y₀ ∧
      (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = D.κ fr.n₀ := by
  obtain ⟨M, hM1, hM2⟩ := exists_diag_SL2 fr.hdet ht
  obtain ⟨S, hS1, hS2⟩ := exists_swap_SL2 fr.hdet
  obtain ⟨η, hη, hρη⟩ := hy.exists_rho_K D M
  obtain ⟨s, hs, hρs⟩ := hy.exists_rho_K D S
  exact ⟨η, s, hη, hs, by rw [hρη]; exact hM1, by rw [hρη]; exact hM2,
    by rw [hρs]; exact hS1, by rw [hρs]; exact hS2⟩

end RhoK

section Eta

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}

theorem sq_ne_one_of_ne_one {F : Type} [Field F] [CharP F 2] {t : F} (ht : t ≠ 1) :
    t ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  apply ht
  have h3 : (t - 1) ^ 2 = t ^ 2 - 1 ^ 2 := sub_pow_char t 1
  rw [h2, one_pow, sub_self] at h3
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

omit [Finite G] in
theorem rho_inv_vec {F : Type} [Field F] {L V K : Subgroup G} (D : NatCoordK G L V K F) {l : G}
    (hl : l ∈ L) {w : Fin 2 → F} {c : F} (hc : c ≠ 0)
    (h : (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w = c • w) :
    (D.ρ l⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ w = c⁻¹ • w := by
  have h1 : (D.ρ l⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w) =
      w := by
    rw [← D.ρ_mulVec_mul (inv_mem hl) hl, inv_mul_cancel,
      D.ρ_mulVec_of_mem L.one_mem V.one_mem]
  rw [h, mulVec_smul] at h1
  rw [eq_inv_smul_iff₀ hc]
  exact h1

structure EtaSpec (h : G0Core G L₁ L₂ V W Z Z₂ e) (D : NatCoordK G L₁ V Z (GaloisField 2 e))
    (fr : S4Side.Frame h.pair.side₁ D) (t : GaloisField 2 e) (η : G) : Prop where
  ht0 : t ≠ 0
  ht1 : t ≠ 1
  mem : η ∈ L₁
  w : (D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = t • D.κ fr.n₀
  y : (D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = t⁻¹ • fr.y₀

namespace EtaSpec

variable {h : G0Core G L₁ L₂ V W Z Z₂ e} {D : NatCoordK G L₁ V Z (GaloisField 2 e)}
  {fr : S4Side.Frame h.pair.side₁ D} {t : GaloisField 2 e} {η : G}

theorem normalizer_J (he : EtaSpec h D fr t η) :
    η ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_le'
  intro j hj
  have hjL : j ∈ L₁ := h.J_le_L hj
  have hηL := he.mem
  have hcL : η * j * η⁻¹ ∈ L₁ := mul_mem (mul_mem hηL hjL) (inv_mem hηL)
  have hjfix := (h.pair.side₁.mem_J_iff D fr.hn₀ fr.hn₀Z hjL).1 hj
  have hinv := rho_inv_vec D hηL he.ht0 he.w
  rw [h.pair.side₁.mem_J_iff D fr.hn₀ fr.hn₀Z hcL,
    D.ρ_mulVec_mul (mul_mem hηL hjL) (inv_mem hηL), D.ρ_mulVec_mul hηL hjL, hinv,
    Matrix.mulVec_smul, hjfix, Matrix.mulVec_smul, he.w, smul_smul, inv_mul_cancel₀ he.ht0,
    one_smul]

theorem normalizer_W (he : EtaSpec h D fr t η) : η ∈ Subgroup.normalizer (W : Set G) :=
  h.normalizer_J_le_W he.normalizer_J

theorem cent_V (he : EtaSpec h D fr t η) {v : G} (hv : v ∈ V) (hc : η * v * η⁻¹ = v) :
    v ∈ Z := by
  have h1 := D.conj η he.mem v hv
  rw [hc] at h1
  exact (D.κ_eq_zero v hv).1 (eq_zero_of_diag_fix fr.hdet he.w he.y he.ht1 h1.symm)

theorem two_elt (he : EtaSpec h D fr t η) {u : G} (hu : u ∈ L₁) (hc : u * η = η * u) {k : ℕ}
    (hk : u ^ 2 ^ k = 1) : u ∈ V := by
  have hρc : ∀ x : Fin 2 → GaloisField 2 e,
      (D.ρ u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ
        ((D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ x) =
      (D.ρ η : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ
        ((D.ρ u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ x) := by
    intro x
    rw [← D.ρ_mulVec_mul hu he.mem, ← D.ρ_mulVec_mul he.mem hu, hc]
  obtain ⟨⟨c, hcw⟩, ⟨c', hcy⟩⟩ := commutes_diag fr.hdet he.w he.y he.ht0
    (sq_ne_one_of_ne_one he.ht1) hρc
  have hpow : D.ρ u ^ (2 ^ k) = 1 := by
    rw [← rho_pow D hu, hk, D.ρ_one]
  exact (D.ρ_eq_one u hu).1 (eq_one_of_eigen_two_pow fr.hdet hcw hcy hpow)

end EtaSpec

namespace EtaSpec

variable {h : G0Core G L₁ L₂ V W Z Z₂ e} {D : NatCoordK G L₁ V Z (GaloisField 2 e)}
  {fr : S4Side.Frame h.pair.side₁ D} {t : GaloisField 2 e} {η y : G}

theorem pow_card_sub_one (he : EtaSpec h D fr t η) (hy : Torus₀ h y)
    (hηK : η ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G)) : η ^ (2 ^ e - 1) = 1 := by
  have : Fintype (GaloisField 2 e) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 e) = 2 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 e h.pair.side₁.e_ne_zero
  have htn : t ^ (2 ^ e - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one t he.ht0
    rwa [hcard] at this
  have key : ∀ u : Fin 2 → GaloisField 2 e,
      ((D.ρ η ^ (2 ^ e - 1) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u = u := by
    intro u
    rw [Matrix.SpecialLinearGroup.coe_pow]
    conv_lhs => rw [eq_basis fr.hdet u]
    rw [mulVec_add, mulVec_smul, mulVec_smul, pow_mulVec_of_eigen he.w,
      pow_mulVec_of_eigen he.y, htn, inv_pow, htn, inv_one, one_smul, one_smul]
    exact (eq_basis fr.hdet u).symm
  have h1 : D.ρ η ^ (2 ^ e - 1) = 1 :=
    CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec (fun u => by rw [key u]; simp)
  have h2 : D.ρ (η ^ (2 ^ e - 1)) = 1 := by rw [rho_pow D he.mem, h1]
  have h3 : η ^ (2 ^ e - 1) ∈ V := (D.ρ_eq_one _ (pow_mem he.mem _)).1 h2
  have h4 : η ^ (2 ^ e - 1) ∈ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V :=
    Subgroup.mem_inf.2 ⟨pow_mem hηK _, h3⟩
  rw [hy.inf_V, Subgroup.mem_bot] at h4
  exact h4

end EtaSpec

section KIso

variable {h : G0Core G L₁ L₂ V W Z Z₂ e} {y : G}

theorem Torus₀.nonempty_kEquiv (hy : Torus₀ h y) (D : NatCoordK G L₁ V Z (GaloisField 2 e)) :
    Nonempty (↥(L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
  let f : ↥(L₁ ⊓ Subgroup.centralizer ({y} : Set G)) →*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    MonoidHom.mk' (fun k => D.ρ k) (fun a b =>
      D.ρ_mul a (Subgroup.mem_inf.1 a.2).1 b (Subgroup.mem_inf.1 b.2).1)
  have hinj : Function.Injective f := fun a b hab => Subtype.ext (hy.rho_inj_K D a.2 b.2 hab)
  have hsurj : Function.Surjective f := fun u => by
    obtain ⟨k, hk, hku⟩ := hy.exists_rho_K D u
    exact ⟨⟨k, hk⟩, hku⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end KIso

end Eta

section Base

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}

structure BaseData (h : G0Core G L₁ L₂ V W Z Z₂ e) (y : G) (A : Subgroup G) : Prop where
  torus : IsTorus h y
  kdata : KData h (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) A
  A_le_W : A ≤ W

theorem G0Core.exists_baseData (h : G0Core G L₁ L₂ V W Z Z₂ e) :
    ∃ (y : G) (A : Subgroup G), BaseData h y A := by
  obtain ⟨y, A, hy, hK, hW⟩ := h.exists_kData
  exact ⟨y, A, hy, hK, hW⟩

namespace BaseData

variable {h : G0Core G L₁ L₂ V W Z Z₂ e} {y : G} {A : Subgroup G} (hb : BaseData h y A)

include hb

theorem cent : ∀ a ∈ A, y * a * y⁻¹ = a := by
  intro a ha
  have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hb.kdata.A_le ha)).2
  rw [← this]
  group

theorem inf_V : A ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h1 : a ∈ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V :=
    ⟨hb.kdata.A_le ha.1, ha.2⟩
  rw [hb.torus.inf_V] at h1
  exact h1

theorem ne_Z : A ≠ Z := by
  intro hAZ
  have h1 := hb.inf_V
  rw [hAZ, inf_eq_left.2 h.Z_le_V] at h1
  exact h.hZ h1

theorem mem_cliq : A ∈ cliq Z W := ⟨hb.kdata.A_mem, hb.ne_Z, hb.A_le_W⟩

theorem sq : ∀ a ∈ A, a * a = 1 := fun a ha =>
  (h.elemAb2_of_mem_zClass hb.kdata.A_mem a ha a ha).2

theorem A_le_J : A ≤ V ⊔ W := hb.A_le_W.trans le_sup_right

theorem A_le_L : A ≤ L₁ := fun _ ha => (Subgroup.mem_inf.1 (hb.kdata.A_le ha)).1

theorem card_cent_le : Nat.card ↥(W ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 2 ^ e := by
  set C : Subgroup G := W ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hCW : C ≤ W := inf_le_left
  set C' : Subgroup ↥W := C.subgroupOf W with hC'
  set N' : Subgroup ↥W := (V ⊓ W).subgroupOf W with hN'
  have hN'idx : N'.index = 2 ^ e := h.jst.index_V₂
  have h2 : C' ⊓ N' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxC : (x : G) ∈ C := Subgroup.mem_subgroupOf.1 hx.1
    have hxN : (x : G) ∈ V ⊓ W := Subgroup.mem_subgroupOf.1 hx.2
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hxC).2
    have hx1 : (x : G) = 1 := by
      refine hb.torus.cent_V _ hxN.1 ?_
      rw [← hcomm]
      group
    exact Subtype.ext hx1
  have h1 : (C' ⊓ N').index ≤ C'.index * N'.index := Subgroup.index_inf_le
  rw [h2, Subgroup.index_bot] at h1
  have h3 : Nat.card C' * C'.index = Nat.card ↥W := Subgroup.card_mul_index C'
  have h4 : Nat.card C' = Nat.card C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  have h5 : Nat.card C * Nat.card ↥W ≤ 2 ^ e * Nat.card ↥W := by
    calc Nat.card C * Nat.card ↥W ≤ Nat.card C * (C'.index * 2 ^ e) := by
          rw [← hN'idx]
          exact Nat.mul_le_mul_left _ h1
      _ = (Nat.card C' * C'.index) * 2 ^ e := by rw [h4]; ring
      _ = Nat.card ↥W * 2 ^ e := by rw [h3]
      _ = 2 ^ e * Nat.card ↥W := by ring
  exact Nat.le_of_mul_le_mul_right h5 hWpos

theorem eq_cent : A = W ⊓ Subgroup.centralizer ({y} : Set G) := by
  have hle : A ≤ W ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨hb.A_le_W ha, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := hb.cent a ha
    calc a * y = (y * a * y⁻¹) * y := by rw [this]
      _ = y * a := by group
  refine le_antisymm hle ?_
  have hcard := hb.kdata.A_card
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hb.card_cent_le)).symm.le

theorem normalizer_A {g : G} (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgy : g * y = y * g) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  apply mem_normalizer_of_conj_le'
  intro a ha
  rw [hb.eq_cent] at ha ⊢
  refine Subgroup.mem_inf.2 ⟨conj_mem_of_mem_normalizer' hgW (Subgroup.mem_inf.1 ha).1,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hay := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
  calc g * a * g⁻¹ * y = g * a * (g⁻¹ * y) := by group
    _ = g * a * (y * g⁻¹) := by
        rw [show g⁻¹ * y = y * g⁻¹ by
          calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hgy]
            _ = y * g⁻¹ := by group]
    _ = g * (a * y) * g⁻¹ := by group
    _ = g * (y * a) * g⁻¹ := by rw [hay]
    _ = y * (g * a * g⁻¹) := by
        calc g * (y * a) * g⁻¹ = (g * y) * a * g⁻¹ := by group
          _ = (y * g) * a * g⁻¹ := by rw [hgy]
          _ = y * (g * a * g⁻¹) := by group

variable {D : NatCoordK G L₁ V Z (GaloisField 2 e)} {fr : S4Side.Frame h.pair.side₁ D}
  {t : GaloisField 2 e} {η : G}

theorem cent_eta (he : EtaSpec h D fr t η) {a : G} (ha : a ∈ A) (hc : a * η = η * a) :
    a = 1 := by
  have h1 : a ∈ V :=
    he.two_elt (hb.A_le_L ha) hc (k := 1) (by rw [pow_one, pow_two]; exact hb.sq a ha)
  have h2 : a ∈ A ⊓ V := ⟨ha, h1⟩
  rw [hb.inf_V, Subgroup.mem_bot] at h2
  exact h2

end BaseData

section Swap

variable {h : G0Core G L₁ L₂ V W Z Z₂ e} {D : NatCoordK G L₁ V Z (GaloisField 2 e)}
  {fr : S4Side.Frame h.pair.side₁ D} {y s η : G} {A : Subgroup G} {t : GaloisField 2 e}

theorem Torus₀.swap_sq (hy : Torus₀ h y) (hsK : s ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G))
    (hs1 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = fr.y₀)
    (hs2 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = D.κ fr.n₀) :
    s * s = 1 := by
  have hsL := (Subgroup.mem_inf.1 hsK).1
  have h1 : D.ρ (s * s) = 1 := by
    refine SL2_eq_of_basis fr.hdet ?_ ?_
    · rw [D.ρ_mulVec_mul hsL hsL, hs1, hs2, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · rw [D.ρ_mulVec_mul hsL hsL, hs2, hs1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have h2 : s * s ∈ V := (D.ρ_eq_one _ (mul_mem hsL hsL)).1 h1
  have h3 : s * s ∈ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V :=
    Subgroup.mem_inf.2 ⟨mul_mem hsK hsK, h2⟩
  rw [hy.inf_V, Subgroup.mem_bot] at h3
  exact h3

theorem Torus₀.swap_conj (hy : Torus₀ h y) (he : EtaSpec h D fr t η)
    (hηK : η ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G))
    (hsK : s ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G))
    (hs1 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = fr.y₀)
    (hs2 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = D.κ fr.n₀) :
    s * η * s = η⁻¹ := by
  have hsL := (Subgroup.mem_inf.1 hsK).1
  have hηL := he.mem
  have hinvw := rho_inv_vec D hηL he.ht0 he.w
  have hinvy := rho_inv_vec D hηL (inv_ne_zero he.ht0) he.y
  have h1 : D.ρ (s * η * s) = D.ρ η⁻¹ := by
    refine SL2_eq_of_basis fr.hdet ?_ ?_
    · rw [D.ρ_mulVec_mul (mul_mem hsL hηL) hsL, D.ρ_mulVec_mul hsL hηL, hs1, he.y, mulVec_smul,
        hs2, hinvw]
    · rw [D.ρ_mulVec_mul (mul_mem hsL hηL) hsL, D.ρ_mulVec_mul hsL hηL, hs2, he.w, mulVec_smul,
        hs1, hinvy, inv_inv]
  have h2 : D.ρ (s * η * s * η) = 1 := by
    rw [D.ρ_mul _ (mul_mem (mul_mem hsL hηL) hsL) _ hηL, h1, D.ρ_inv hηL, inv_mul_cancel]
  have h3 : s * η * s * η ∈ V :=
    (D.ρ_eq_one _ (mul_mem (mul_mem (mul_mem hsL hηL) hsL) hηL)).1 h2
  have h4 : s * η * s * η ∈ (L₁ ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ V :=
    Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hsK hηK) hsK) hηK, h3⟩
  rw [hy.inf_V, Subgroup.mem_bot] at h4
  exact eq_inv_of_mul_eq_one_left h4

namespace BaseData

variable (hb : BaseData h y A)

include hb

theorem swap_ne (hsL : s ∈ L₁) (hss : s * s = 1)
    (hs1 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = fr.y₀)
    (hs2 : (D.ρ s : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ = D.κ fr.n₀) :
    cs A s ≠ A := by
  intro hAs
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h.ne_bot_of_mem_cliq hb.mem_cliq ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have haJ : a ∈ V ⊔ W := hb.A_le_J ha
  have haL : a ∈ L₁ := hb.A_le_L ha
  have hmem : s * a * s⁻¹ ∈ A := by
    have := conj_mem_cs s ha
    rwa [hAs] at this
  have hfix := (h.pair.side₁.mem_J_iff D fr.hn₀ fr.hn₀Z
    (mul_mem (mul_mem hsL haL) (inv_mem hsL))).1 (hb.A_le_J hmem)
  rw [hsinv, D.ρ_mulVec_mul (mul_mem hsL haL) hsL, D.ρ_mulVec_mul hsL haL, hs1,
    fr.ρ_mulVec haJ, mulVec_add, mulVec_smul, hs2, hs1, fr.hdet, one_mul] at hfix
  have hba : fr.b a • fr.y₀ = 0 := by
    have : D.κ fr.n₀ + fr.b a • fr.y₀ = D.κ fr.n₀ + 0 := by rw [add_zero]; exact hfix
    exact add_left_cancel this
  have hy₀ : fr.y₀ ≠ 0 := by
    intro h0
    have := fr.hdet
    rw [h0] at this
    simp [det2] at this
  have hb0 : fr.b a = 0 := by
    rcases smul_eq_zero.1 hba with h1 | h1
    · exact h1
    · exact absurd h1 hy₀
  have haV : a ∈ V := (fr.mem_V_iff_b haJ).2 hb0
  have h2 : a ∈ A ⊓ V := ⟨ha, haV⟩
  rw [hb.inf_V, Subgroup.mem_bot] at h2
  exact ha1 h2

theorem sup_eq (hsK : s ∈ L₁ ⊓ Subgroup.centralizer ({y} : Set G))
    (hne : cs A s ≠ A) : A ⊔ cs A s = L₁ ⊓ Subgroup.centralizer ({y} : Set G) := by
  obtain ⟨D⟩ := h.pair.side₁.nat
  obtain ⟨φ⟩ := hb.torus.nonempty_kEquiv D
  have hcsK : cs A s ≤ L₁ ⊓ Subgroup.centralizer ({y} : Set G) := by
    have := cs_mono hb.kdata.A_le s
    rwa [cs_of_mem_normalizer (Subgroup.le_normalizer hsK)] at this
  exact sylow_sup_eq φ h.two_le hb.kdata.A_le hcsK hb.kdata.A_card
    (by rw [card_cs]; exact hb.kdata.A_card) hne.symm

end BaseData

end Swap

end Base

end CFSG.CGT.PushingUpLit.A78G0
