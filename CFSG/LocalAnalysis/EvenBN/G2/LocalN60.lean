module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalN59
import CFSG.CGT.PushingUpLit.CGT6K1.Closed

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open scoped commutatorElement Pointwise MatrixGroups

namespace N60

section Generic

variable {G : Type*} [Group G]

theorem eq_one_of_crossed_fixed {t : G} {A X T N : Subgroup G}
    (hAt : ∀ j ∈ A, j * t = t * j)
    (hAT : A ≤ normalizer (T : Set G)) (hAN : A ≤ normalizer (N : Set G))
    (hcross : ∀ x ∈ X, ∃ a ∈ T, ∃ u ∈ N, x * t * x⁻¹ = t * (a * u))
    (hcop : ∀ a ∈ T, (∀ j ∈ A, a⁻¹ * (j * a * j⁻¹) ∈ T ⊓ N) →
      ∃ c ∈ T ⊓ centralizer (A : Set G), ∃ n ∈ T ⊓ N, a = c * n)
    (hCT : ∀ c ∈ T, (∀ j ∈ A, j * c = c * j) → c = 1)
    (hCN : ∀ u ∈ N, (∀ j ∈ A, j * u = u * j) → u = 1)
    (hXC : ∀ x ∈ X, x * t = t * x → x ∈ T)
    {x : G} (hx : x ∈ X) (hfix : ∀ j ∈ A, j * x = x * j) : x = 1 := by
  obtain ⟨a, ha, u, hu, hxt⟩ := hcross x hx
  have hau : ∀ j ∈ A, j * (a * u) * j⁻¹ = a * u := by
    intro j hj
    have e1 : j * x * j⁻¹ = x := by rw [hfix j hj, mul_inv_cancel_right]
    have e2 : j * t * j⁻¹ = t := by rw [hAt j hj, mul_inv_cancel_right]
    have h1 : j * (x * t * x⁻¹) * j⁻¹ = x * t * x⁻¹ := by
      calc j * (x * t * x⁻¹) * j⁻¹ = (j * x * j⁻¹) * (j * t * j⁻¹) * (j * x * j⁻¹)⁻¹ := by group
        _ = x * t * x⁻¹ := by rw [e1, e2]
    rw [hxt] at h1
    have h2 : j * (t * (a * u)) * j⁻¹ = t * (j * (a * u) * j⁻¹) := by
      calc j * (t * (a * u)) * j⁻¹ = (j * t * j⁻¹) * (j * (a * u) * j⁻¹) := by group
        _ = t * (j * (a * u) * j⁻¹) := by rw [e2]
    rw [h2] at h1
    exact mul_left_cancel h1
  have hP : ∀ j ∈ A, a⁻¹ * (j * a * j⁻¹) ∈ T ⊓ N := by
    intro j hj
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hAT hj) a).1 ha), ?_⟩
    have e : a⁻¹ * (j * a * j⁻¹) = u * (j * u * j⁻¹)⁻¹ := by
      calc a⁻¹ * (j * a * j⁻¹) = a⁻¹ * ((j * (a * u) * j⁻¹) * (j * u * j⁻¹)⁻¹) := by group
        _ = a⁻¹ * ((a * u) * (j * u * j⁻¹)⁻¹) := by rw [hau j hj]
        _ = u * (j * u * j⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hu (inv_mem ((mem_normalizer_iff.1 (hAN hj) u).1 hu))
  obtain ⟨c, hc, n, hn, hcn⟩ := hcop a ha hP
  have hc1 : c = 1 := hCT c (Subgroup.mem_inf.1 hc).1 fun j hj =>
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j hj
  have han : a ∈ N := by
    rw [hcn, hc1, one_mul]
    exact (Subgroup.mem_inf.1 hn).2
  have hauN : a * u = 1 := hCN _ (mul_mem han hu) fun j hj => by
    calc j * (a * u) = (j * (a * u) * j⁻¹) * j := by group
      _ = (a * u) * j := by rw [hau j hj]
  rw [hauN, mul_one] at hxt
  have hxc : x * t = t * x := by
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [hxt]
  exact hCT x (hXC x hx hxc) hfix

end Generic

section ModelLevel

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem rootSubgroup_r_inf_D : rootSubgroup .G2 K g2r ⊓ Model.D K = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxr, hxD⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨A, rfl⟩ := mem_rootSubgroup.1 hxr
  rw [pinnedX_r_eq_g2N] at hxD ⊢
  have hA : A = 0 := Model.g2N_mem_D_iff.1 hxD
  subst hA
  exact Subgroup.mem_bot.2 g2N_zero

theorem rootSubgroup_a_inf_M : rootSubgroup .G2 K g2a ⊓ Model.M K = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxr, hxM⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨B, rfl⟩ := mem_rootSubgroup.1 hxr
  rw [pinnedX_a_eq_g2N] at hxM ⊢
  have hB : B = 0 := Model.g2N_mem_M_iff.1 hxM
  subst hB
  exact Subgroup.mem_bot.2 g2N_zero

variable (d : G2Data L K)

theorem rootGroup_r_inf_D : d.rootGroup g2r ⊓ d.D = ⊥ := by
  rw [G2Data.rootGroup, G2Data.D, ← d.image_inf, rootSubgroup_r_inf_D, d.image_bot]

theorem rootGroup_a_inf_M : d.rootGroup g2a ⊓ d.M = ⊥ := by
  rw [G2Data.rootGroup, G2Data.M, ← d.image_inf, rootSubgroup_a_inf_M, d.image_bot]

end ModelLevel

section SetupLevel

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
  [Finite K] [CharP K 2]

theorem J_comm_t (h : Setup G L f t) (d : G2Data L K) {j : G} (hj : j ∈ d.J) : j * t = t * j :=
  mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d hj)).1

theorem eq_one_of_mem_U_of_forall_J₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} (hx : x ∈ d.U)
    (hfix : ∀ j ∈ d.J₃, j * x = x * j) : x = 1 := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hxD : x ∈ d.D := (hUY.trans (hYX.trans (hXF.trans hFD))) hx
  have hxS : x ∈ d.S ⊓ centralizer (d.J₃ : Set G) :=
    Subgroup.mem_inf.2 ⟨hDS hxD, mem_centralizer_iff.2 hfix⟩
  rw [Setup.JWeight.S_inf_centralizer_J₃ hW h d hK hQ] at hxS
  have : x ∈ d.rootGroup g2r ⊓ d.D := Subgroup.mem_inf.2 ⟨hxS, hxD⟩
  rw [rootGroup_r_inf_D d] at this
  exact Subgroup.mem_bot.1 this

theorem eq_one_of_mem_U_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {x : G} (hx : x ∈ d.U)
    (hfix : ∀ j ∈ d.J₄, j * x = x * j) : x = 1 := by
  obtain ⟨hUY, hYX, -, hXF, -, -, hFM, -, hMS, -⟩ := d.inclusions
  have hxM : x ∈ d.M := (hUY.trans (hYX.trans (hXF.trans hFM))) hx
  have hxS : x ∈ d.S ⊓ centralizer (d.J₄ : Set G) :=
    Subgroup.mem_inf.2 ⟨hMS hxM, mem_centralizer_iff.2 hfix⟩
  rw [Setup.JWeight.S_inf_centralizer_J₄ hW h d hK h8] at hxS
  have : x ∈ d.rootGroup g2a ⊓ d.M := Subgroup.mem_inf.2 ⟨hxS, hxM⟩
  rw [rootGroup_a_inf_M d] at this
  exact Subgroup.mem_bot.1 this

theorem eq_one_of_mem_yamadaU₁_of_forall_J₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaU₁ d t) (hfix : ∀ j ∈ d.J₃, j * x = x * j) : x = 1 :=
  h.eq_one_of_mem_yamadaU₁_of_forall d hK hQ.doubling
    (T := (d.J₃ : Set G)) (fun k hk => J_comm_t h d (Setup.J₃_le_J d hk))
    (fun y hy hy' => eq_one_of_mem_U_of_forall_J₃ hW h d hK hQ hy hy') hx hfix

theorem eq_one_of_mem_yamadaU₁_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {x : G}
    (hx : x ∈ yamadaU₁ d t) (hfix : ∀ j ∈ d.J₄, j * x = x * j) : x = 1 :=
  h.eq_one_of_mem_yamadaU₁_of_forall d hK (h.doublingFacts_of_eight d hK h8)
    (T := (d.J₄ : Set G)) (fun k hk => J_comm_t h d (Setup.J₄_le_J d hk))
    (fun y hy hy' => eq_one_of_mem_U_of_forall_J₄ hW h d hK h8 hy hy') hx hfix

theorem mem_S_of_mem_yamadaP_of_commute (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaP d t) (hxt : x * t = t * x) : x ∈ d.S := by
  obtain ⟨-, hPR₈, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  have hSP : d.S ≤ yamadaP d t := (S_le_yamadaS₆ d t).trans hS₆P
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_49_1 hW d hK hQ).2.2]
    exact Subgroup.mem_inf.2 ⟨hPR₈ hx, mem_centralizer_singleton_iff.2 hxt⟩
  rw [h.yamadaR_eq d] at hxR
  have htS : t ∈ normalizer (d.S : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htS).1 hxR with hs | ⟨s, hs, e⟩
  · exact hs
  · exfalso
    apply htP
    have := mul_mem (inv_mem (hSP hs)) hx
    rwa [e, inv_mul_cancel_left] at this

theorem mem_D_of_mem_yamadaD₇_of_commute (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaD₇ d t) (hxt : x * t = t * x) : x ∈ d.D := by
  have hD := hQ.doubling
  have hxS : x ∈ d.S :=
    mem_S_of_mem_yamadaP_of_commute hW h d hK hQ (yamadaD₇_le_yamadaP d t hx) hxt
  exact h.S_inf_yamadaCstar_le_D hW d hK hD (Subgroup.mem_inf.2 ⟨hxS, yamadaD₇_le_yamadaC₇ d t hx⟩)

theorem mem_M_of_mem_yamadaM₆_of_commute (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaM₆ d t) (hxt : x * t = t * x) : x ∈ d.M := by
  have hxS : x ∈ d.S :=
    mem_S_of_mem_yamadaP_of_commute hW h d hK hQ (h.yamadaM₆_le_yamadaP hW d hK hQ hx) hxt
  rw [← h.yamadaL₆_inf_S hW d hK hQ]
  exact Subgroup.mem_inf.2 ⟨h.yamadaM₆_le_yamadaL₆ hW d hK hQ hx, hxS⟩

theorem eq_one_of_mem_yamadaD₇_of_forall_J₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaD₇ d t) (hfix : ∀ j ∈ d.J₃, j * x = x * j) : x = 1 := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have hJ₃J := Setup.J₃_le_J d
  have hDU₁ : d.D ≤ normalizer (yamadaU₁ d t : Set G) := fun g hg =>
    h.S_le_normalizer_yamadaU₁ d hK hD (hDS hg)
  have hJU₁ := h.J_le_normalizer_yamadaU₁ d hK hD
  have hJD := Setup.JWeight.J_le_normalizer_D hW h d hK hQ
  refine eq_one_of_crossed_fixed (t := t) (A := d.J₃) (X := yamadaD₇ d t) (T := d.D)
    (N := yamadaU₁ d t) (fun j hj => J_comm_t h d (hJ₃J hj)) (fun j hj => hJD (hJ₃J hj))
    (fun j hj => hJU₁ (hJ₃J hj)) ?_ ?_ ?_ ?_ ?_ hx hfix
  · intro x hx
    obtain ⟨δ, hδ, hxδ⟩ := (h.yamada_5_19 d hK hD).2.1.1 x (yamadaD₇_le_yamadaC₇ d t hx)
    rw [hD.D₁_eq] at hδ
    obtain ⟨a, ha, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hDU₁ δ hδ
    exact ⟨a, ha, u, hu, hxδ⟩
  · intro a ha hfix'
    have hD2 : IsPGroup 2 d.D := d.isSylowOf_S.isPGroup.to_le hDS
    exact Setup.exists_centralizer_mul_of_le_J d (A := d.J₃) (M := d.D)
      (N := d.D ⊓ yamadaU₁ d t) hJ₃J inf_le_left
      (fun g hg => Common.mem_normalizer_inf (Subgroup.le_normalizer hg) (hDU₁ hg))
      (fun j hj => hJD (hJ₃J hj))
      (fun j hj => Common.mem_normalizer_inf (hJD (hJ₃J hj)) (hJU₁ (hJ₃J hj))) hD2 ha hfix'
  · intro c hc hfixc
    have hcS : c ∈ d.S ⊓ centralizer (d.J₃ : Set G) :=
      Subgroup.mem_inf.2 ⟨hDS hc, mem_centralizer_iff.2 hfixc⟩
    rw [Setup.JWeight.S_inf_centralizer_J₃ hW h d hK hQ] at hcS
    have : c ∈ d.rootGroup g2r ⊓ d.D := Subgroup.mem_inf.2 ⟨hcS, hc⟩
    rw [rootGroup_r_inf_D d] at this
    exact Subgroup.mem_bot.1 this
  · intro u hu hfixu
    exact eq_one_of_mem_yamadaU₁_of_forall_J₃ hW h d hK hQ hu hfixu
  · intro x hx hxt
    exact mem_D_of_mem_yamadaD₇_of_commute hW h d hK hQ hx hxt

theorem eq_one_of_mem_yamadaY₂_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {x : G}
    (hx : x ∈ yamadaY₂ d t) (hfix : ∀ k ∈ d.J₄, k * x = x * k) : x = 1 := by
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨⟨hU₁U₁', hU₁'C⟩, -⟩ := h.yamada_5_13_1 d hK hD
  have hJ₄J := Setup.J₄_le_J d
  have hJU₁ := h.J_le_normalizer_yamadaU₁ d hK hD
  have hwb : ∀ k ∈ d.J₄, d.wb * k = k * d.wb := fun k hk =>
    (mem_centralizer_iff.1 ((d.yamada_3_13_3_G).2.2.2.1 hk) d.wb d.wb_mem_leviB)
  obtain ⟨u, hu, u', hu', rfl⟩ := Common.exists_mul_of_le_normalizer
    (hU₁'C.trans (Subgroup.centralizer_le_normalizer _)) x hx
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
  have hsplit : ∀ k ∈ d.J₄, k * u * k⁻¹ = u ∧ k * u₀ * k⁻¹ = u₀ := by
    intro k hk
    have e := hfix k hk
    have hkw : k * d.wb = d.wb * k := (hwb k hk).symm
    have hku : k * u * k⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 (hJU₁ (hJ₄J hk)) u).1 hu
    have hku₀ : k * u₀ * k⁻¹ ∈ yamadaU₁ d t :=
      (mem_normalizer_iff.1 (hJU₁ (hJ₄J hk)) u₀).1 hu₀
    have hky : k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹ = d.wb * (k * u₀ * k⁻¹) * d.wb⁻¹ := by
      calc k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹ = (k * d.wb) * u₀ * (k * d.wb)⁻¹ := by group
        _ = (d.wb * k) * u₀ * (d.wb * k)⁻¹ := by rw [hkw]
        _ = d.wb * (k * u₀ * k⁻¹) * d.wb⁻¹ := by group
    have e' : k * u * k⁻¹ * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹) = u * (d.wb * u₀ * d.wb⁻¹) := by
      calc k * u * k⁻¹ * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)
          = k * (u * (d.wb * u₀ * d.wb⁻¹)) * k⁻¹ := by group
        _ = u * (d.wb * u₀ * d.wb⁻¹) := by rw [e]; group
    have e1 : u⁻¹ * (k * u * k⁻¹) =
        d.wb * (u₀ * (k * u₀ * k⁻¹)⁻¹) * d.wb⁻¹ := by
      calc u⁻¹ * (k * u * k⁻¹)
          = u⁻¹ * (k * u * k⁻¹ * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)) *
              (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by group
        _ = u⁻¹ * (u * (d.wb * u₀ * d.wb⁻¹)) * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by rw [e']
        _ = (d.wb * u₀ * d.wb⁻¹) * (d.wb * (k * u₀ * k⁻¹) * d.wb⁻¹)⁻¹ := by rw [hky]; group
        _ = d.wb * (u₀ * (k * u₀ * k⁻¹)⁻¹) * d.wb⁻¹ := by group
    have hmem : u⁻¹ * (k * u * k⁻¹) ∈
        yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hku, Subgroup.mem_map.2
        ⟨u₀ * (k * u₀ * k⁻¹)⁻¹, mul_mem hu₀ (inv_mem hku₀), ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact e1.symm
    rw [hU₁U₁', Subgroup.mem_bot] at hmem
    have hku' : k * u * k⁻¹ = u := by
      calc k * u * k⁻¹ = u * (u⁻¹ * (k * u * k⁻¹)) := by group
        _ = u := by rw [hmem, mul_one]
    refine ⟨hku', ?_⟩
    have e2 : k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹ = d.wb * u₀ * d.wb⁻¹ := by
      rw [hku'] at e'
      exact mul_left_cancel e'
    have e3 : d.wb * (k * u₀ * k⁻¹) * d.wb⁻¹ = d.wb * u₀ * d.wb⁻¹ := by
      rw [← hky]
      exact e2
    exact mul_left_cancel (mul_right_cancel e3)
  have hu1 : u = 1 := eq_one_of_mem_yamadaU₁_of_forall_J₄ hW h d hK h8 hu fun k hk => by
    calc k * u = k * u * k⁻¹ * k := by group
      _ = u * k := by rw [(hsplit k hk).1]
  have hu₀1 : u₀ = 1 := eq_one_of_mem_yamadaU₁_of_forall_J₄ hW h d hK h8 hu₀ fun k hk => by
    calc k * u₀ = k * u₀ * k⁻¹ * k := by group
      _ = u₀ * k := by rw [(hsplit k hk).2]
  rw [hu1, hu₀1]
  group

theorem eq_one_of_mem_yamadaM₆_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) {x : G}
    (hx : x ∈ yamadaM₆ d t) (hfix : ∀ j ∈ d.J₄, j * x = x * j) : x = 1 := by
  have hQ := h.qFacts_of_eight d hK h8
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hJ₄J := Setup.J₄_le_J d
  have hJY₂ := h.J_le_normalizer_yamadaY₂ d hK hD
  have hJM := Setup.JWeight.J_le_normalizer_M hW h d hK hQ
  have hMY₂ : d.M ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg =>
    (h.yamada_5_13_3 d hK hD).1 (hMS hg)
  refine eq_one_of_crossed_fixed (t := t) (A := d.J₄) (X := yamadaM₆ d t) (T := d.M)
    (N := yamadaY₂ d t) (fun j hj => J_comm_t h d (hJ₄J hj)) (fun j hj => hJM (hJ₄J hj))
    (fun j hj => hJY₂ (hJ₄J hj)) ?_ ?_ ?_ ?_ ?_ hx hfix
  · intro x hx
    have hκ : t * x * t * x⁻¹ ∈ yamadaM₂ d t := h.crossed_mem_yamadaM₂ d hK hD
      (yamadaL₆_le d t (h.yamadaM₆_le_yamadaL₆ hW d hK hQ hx))
    obtain ⟨m, hm, y, hy, hmy⟩ :=
      Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_M d hK hD) _ hκ
    refine ⟨m, hm, y, hy, ?_⟩
    rw [h.conj_t_eq_mul_crossed x, hmy]
  · intro a ha hfix'
    have hM2 : IsPGroup 2 d.M := d.isSylowOf_S.isPGroup.to_le hMS
    exact Setup.exists_centralizer_mul_of_le_J d (A := d.J₄) (M := d.M)
      (N := d.M ⊓ yamadaY₂ d t) hJ₄J inf_le_left
      (fun g hg => Common.mem_normalizer_inf (Subgroup.le_normalizer hg) (hMY₂ hg))
      (fun j hj => hJM (hJ₄J hj))
      (fun j hj => Common.mem_normalizer_inf (hJM (hJ₄J hj)) (hJY₂ (hJ₄J hj))) hM2 ha hfix'
  · intro c hc hfixc
    have hcS : c ∈ d.S ⊓ centralizer (d.J₄ : Set G) :=
      Subgroup.mem_inf.2 ⟨hMS hc, mem_centralizer_iff.2 hfixc⟩
    rw [Setup.JWeight.S_inf_centralizer_J₄ hW h d hK h8] at hcS
    have : c ∈ d.rootGroup g2a ⊓ d.M := Subgroup.mem_inf.2 ⟨hcS, hc⟩
    rw [rootGroup_a_inf_M d] at this
    exact Subgroup.mem_bot.1 this
  · intro u hu hfixu
    exact eq_one_of_mem_yamadaY₂_of_forall_J₄ hW h d hK h8 hu hfixu
  · intro x hx hxt
    exact mem_M_of_mem_yamadaM₆_of_commute hW h d hK hQ hx hxt

theorem commutator_yamadaP_J₃_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ⁅yamadaP d t, d.J₃⁆ ≤ yamadaD₇ d t := by
  refine commutator_le.2 fun x hx j hj => ?_
  obtain ⟨hPD, -⟩ := h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ
  have hJD := h.J_le_normalizer_yamadaD₇ hW d hK hQ (Setup.J₃_le_J d hj)
  have hx' : x ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
    rw [← h.yamadaP_eq_mul hW d hK hQ]
    exact hx
  obtain ⟨m, hm, e, he, rfl⟩ := Set.mem_mul.1 hx'
  have hmP : m ∈ yamadaP d t := h.yamadaM₆_le_yamadaP hW d hK hQ hm
  have key : ⁅m * e, j⁆ = m * ⁅e, j⁆ * m⁻¹ * (⁅j, m⁆)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅e, j⁆ ∈ yamadaD₇ d t := by
    rw [show ⁅e, j⁆ = e * (j * e⁻¹ * j⁻¹) by simp only [commutatorElement_def]; group]
    exact mul_mem he ((mem_normalizer_iff.1 hJD e⁻¹).1 (inv_mem he))
  have h2 : m * ⁅e, j⁆ * m⁻¹ ∈ yamadaD₇ d t := (mem_normalizer_iff.1 (hPD hmP) _).1 h1
  have h3 : ⁅j, m⁆ ∈ yamadaD₇ d t :=
    h.yamadaF₅_le_yamadaD₇ hW d hK hQ (h.commutator_J₃_yamadaM₆_le_yamadaF₅ hW d hK hQ j hj m hm)
  rw [key]
  exact mul_mem h2 (inv_mem h3)

theorem commutator_yamadaP_J₄_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ⁅yamadaP d t, d.J₄⁆ ≤ yamadaM₆ d t := by
  refine commutator_le.2 fun x hx j hj => ?_
  have hJM := h.J_le_normalizer_yamadaM₆ hW d hK hQ (Setup.J₄_le_J d hj)
  have hx' : x ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
    rw [← h.yamadaP_eq_mul hW d hK hQ]
    exact hx
  obtain ⟨m, hm, e, he, rfl⟩ := Set.mem_mul.1 hx'
  have key : ⁅m * e, j⁆ = m * ⁅e, j⁆ * m⁻¹ * (⁅j, m⁆)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅e, j⁆ ∈ yamadaM₆ d t := by
    rw [show ⁅e, j⁆ = (⁅j, e⁆)⁻¹ by simp only [commutatorElement_def]; group]
    exact inv_mem (h.yamadaF₅_le_yamadaM₆ hW d hK hQ
      (h.commutator_J₄_yamadaD₇_le_yamadaF₅ hW d hK hQ j hj e he))
  have h3 : ⁅j, m⁆ ∈ yamadaM₆ d t := by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 hJM m).1 hm) (inv_mem hm)
  rw [key]
  exact mul_mem (mul_mem (mul_mem hm h1) (inv_mem hm)) (inv_mem h3)

end SetupLevel

end N60

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem yamada_5_60_J₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J₃ ≤ normalizer (yamadaD₇ d t : Set G) ∧ d.J₃ ≤ normalizer (yamadaP d t : Set G) ∧
      ⁅yamadaP d t, d.J₃⁆ ≤ yamadaD₇ d t ∧ yamadaD₇ d t ⊓ centralizer (d.J₃ : Set G) = ⊥ := by
  refine ⟨fun j hj => h.J_le_normalizer_yamadaD₇ hW d hK hQ (J₃_le_J d hj),
    fun j hj => h.J_le_normalizer_yamadaP hW d hK hQ (J₃_le_J d hj),
    N60.commutator_yamadaP_J₃_le hW h d hK hQ, ?_⟩
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_bot.2 (N60.eq_one_of_mem_yamadaD₇_of_forall_J₃ hW h d hK hQ hxD
    fun j hj => mem_centralizer_iff.1 hxC j hj)

theorem yamada_5_60_J₄_acts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J₄ ≤ normalizer (yamadaM₆ d t : Set G) ∧ d.J₄ ≤ normalizer (yamadaP d t : Set G) ∧
      ⁅yamadaP d t, d.J₄⁆ ≤ yamadaM₆ d t :=
  ⟨fun j hj => h.J_le_normalizer_yamadaM₆ hW d hK hQ (J₄_le_J d hj),
    fun j hj => h.J_le_normalizer_yamadaP hW d hK hQ (J₄_le_J d hj),
    N60.commutator_yamadaP_J₄_le hW h d hK hQ⟩

theorem yamada_5_60_J₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    d.J₄ ≤ normalizer (yamadaM₆ d t : Set G) ∧ d.J₄ ≤ normalizer (yamadaP d t : Set G) ∧
      ⁅yamadaP d t, d.J₄⁆ ≤ yamadaM₆ d t ∧ yamadaM₆ d t ⊓ centralizer (d.J₄ : Set G) = ⊥ := by
  obtain ⟨h1, h2, h3⟩ := h.yamada_5_60_J₄_acts hW d hK (h.qFacts_of_eight d hK h8)
  refine ⟨h1, h2, h3, ?_⟩
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_bot.2 (N60.eq_one_of_mem_yamadaM₆_of_forall_J₄ hW h d hK h8 hxM
    fun j hj => mem_centralizer_iff.1 hxC j hj)

theorem yamada_5_60_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaN₁ d t = (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊔ yamadaD₇ d t ∧
      (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊓ yamadaD₇ d t = ⊥ ∧
      d.leviA ≤ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hJ₃D, hJ₃P, hJP, hJD⟩ := h.yamada_5_60_J₃ hW d hK hQ
  obtain ⟨-, -, -, hKN, -, hDC, -⟩ := h.yamada_5_59_N₁_centralizer hW d hK hQ
  obtain ⟨⟨hDP, hPN, hP2⟩, hPN₁, -⟩ := h.yamada_5_59_N₁_P hW d hK hQ
  obtain ⟨α, hdata⟩ := h.yamada_5_59_N₁_data hW d hK hQ
  have hex := hdata.exactClosure CFSG.CGT.PushingUpLit.CGT6K1.catSelector_holds
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer.smallSurvivorsNoElementary
  have hsup := hdata.sup_eq hex
  have hbarN := barSub_yamadaN₁ d t hKN
  have hleviK : d.leviA ≤ yamadaK₁ d := by
    rw [yamadaK₁_eq d h4]
    exact le_sup_right
  have hleviC : d.leviA ≤ centralizer (d.J₃ : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun j hj =>
      (mem_centralizer_iff.1 ((d.yamada_3_13_2_G).2.2.1 hj) x hx).symm
  have hlev : d.leviA ≤ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) :=
    le_inf (hleviK.trans (yamadaK₁_le_yamadaN₁ d t)) hleviC
  refine ⟨?_, ?_, hlev⟩
  · refine le_antisymm ?_ (sup_le inf_le_left (yamadaD₇_le_yamadaN₁ d t))
    set H : Subgroup G := (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊔ yamadaD₇ d t with hH
    have hDH : yamadaD₇ d t ≤ H := le_sup_right
    have hDD : d.D ≤ yamadaD₇ d t := by
      rw [← hDC]
      exact inf_le_left
    have hKH : yamadaK₁ d ≤ H := by
      rw [yamadaK₁_eq d h4]
      exact sup_le (hDD.trans hDH) (hlev.trans le_sup_left)
    have hPH : yamadaP d t ≤ H := by
      have hJ₃J : d.J₃ ≤ d.J := d.image_mono inf_le_left
      have hcop : (Nat.card d.J₃).Coprime (Nat.card (yamadaP d t)) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP2
        rw [hk]
        exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
          ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₃J)))
      have : Group.IsNilpotent (yamadaP d t) := hP2.isNilpotent
      intro x hx
      obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hDP hPN
        hJ₃P hJ₃D inferInstance hcop hx fun s hs => by
          have := Subgroup.commutator_mem_commutator (inv_mem hx) hs
          rw [commutatorElement_def, inv_inv] at this
          rw [show x⁻¹ * (s * x * s⁻¹) = x⁻¹ * s * x * s⁻¹ by group]
          exact hJP this
      exact mul_mem (mem_sup_left (mem_inf.2 ⟨hPN₁ (mem_inf.1 hc).1, (mem_inf.1 hc).2⟩))
        (hDH hn)
    intro n hn
    have hnN : n ∈ normalizer (yamadaD₇ d t : Set G) := yamadaN₁_le_normalizer d t hKN hn
    have hbn : barMap (yamadaD₇ d t) ⟨n, hnN⟩ ∈ barSub (yamadaD₇ d t) (yamadaN₁ d t) :=
      ⟨⟨n, hnN⟩, mem_subgroupOf.2 hn, rfl⟩
    rw [hbarN, ← hsup] at hbn
    refine (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDH
      ⟨n, hnN⟩).1 ?_
    refine (sup_le (Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hPH (mem_subgroupOf.1 hx)))
      (Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hKH (mem_subgroupOf.1 hx)))) hbn
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨_, hxC⟩, hxD⟩ := mem_inf.1 hx
    rw [← hJD]
    exact mem_inf.2 ⟨hxD, hxC⟩

theorem yamada_5_60_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaN₂ d t = (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊔ yamadaM₆ d t ∧
      d.leviB ≤ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hJ₄M, hJ₄P, hJP⟩ := h.yamada_5_60_J₄_acts hW d hK hQ
  obtain ⟨-, -, -, hKN, -, hMC, -⟩ := h.yamada_5_59_N₂_centralizer hW d hK hQ
  obtain ⟨⟨hMP, hPN, hP2⟩, hPN₂, -⟩ := h.yamada_5_59_N₂_P hW d hK hQ
  obtain ⟨α, hdata⟩ := h.yamada_5_59_N₂_data hW d hK hQ
  have hex := hdata.exactClosure CFSG.CGT.PushingUpLit.CGT6K1.catSelector_holds
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer.smallSurvivorsNoElementary
  have hsup := hdata.sup_eq hex
  have hbarN := barSub_yamadaN₂ d t hKN
  have hleviK : d.leviB ≤ yamadaK₂ d := by
    rw [yamadaK₂_eq d h4]
    exact le_sup_right
  have hleviC : d.leviB ≤ centralizer (d.J₄ : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun j hj =>
      (mem_centralizer_iff.1 ((d.yamada_3_13_3_G).2.2.2.1 hj) x hx).symm
  have hlev : d.leviB ≤ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) :=
    le_inf (hleviK.trans (yamadaK₂_le_yamadaN₂ d t)) hleviC
  refine ⟨?_, hlev⟩
  refine le_antisymm ?_ (sup_le inf_le_left (yamadaM₆_le_yamadaN₂ d t))
  set H : Subgroup G := (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊔ yamadaM₆ d t with hH
  have hMH : yamadaM₆ d t ≤ H := le_sup_right
  have hMM : d.M ≤ yamadaM₆ d t := by
    rw [← hMC]
    exact inf_le_left
  have hKH : yamadaK₂ d ≤ H := by
    rw [yamadaK₂_eq d h4]
    exact sup_le (hMM.trans hMH) (hlev.trans le_sup_left)
  have hPH : yamadaP d t ≤ H := by
    have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
    have hcop : (Nat.card d.J₄).Coprime (Nat.card (yamadaP d t)) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP2
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
        ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₄J)))
    have : Group.IsNilpotent (yamadaP d t) := hP2.isNilpotent
    intro x hx
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hMP hPN
      hJ₄P hJ₄M inferInstance hcop hx fun s hs => by
        have := Subgroup.commutator_mem_commutator (inv_mem hx) hs
        rw [commutatorElement_def, inv_inv] at this
        rw [show x⁻¹ * (s * x * s⁻¹) = x⁻¹ * s * x * s⁻¹ by group]
        exact hJP this
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨hPN₂ (mem_inf.1 hc).1, (mem_inf.1 hc).2⟩))
      (hMH hn)
  intro n hn
  have hnN : n ∈ normalizer (yamadaM₆ d t : Set G) := yamadaN₂_le_normalizer d t hKN hn
  have hbn : barMap (yamadaM₆ d t) ⟨n, hnN⟩ ∈ barSub (yamadaM₆ d t) (yamadaN₂ d t) :=
    ⟨⟨n, hnN⟩, mem_subgroupOf.2 hn, rfl⟩
  rw [hbarN, ← hsup] at hbn
  refine (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hMH
    ⟨n, hnN⟩).1 ?_
  refine (sup_le (Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hPH (mem_subgroupOf.1 hx)))
    (Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hKH (mem_subgroupOf.1 hx)))) hbn

theorem yamada_5_60_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊓ yamadaM₆ d t = ⊥ := by
  obtain ⟨-, -, -, hJM⟩ := h.yamada_5_60_J₄ hW d hK h8
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨_, hxC⟩, hxM⟩ := mem_inf.1 hx
  rw [← hJM]
  exact mem_inf.2 ⟨hxM, hxC⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
