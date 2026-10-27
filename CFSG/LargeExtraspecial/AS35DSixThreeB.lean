module

public import CFSG.LargeExtraspecial.AS35DSixThreeA
public import CFSG.LargeExtraspecial.AS35DFourEight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

structure SixThreeCtx where
  hn : 2 ≤ S.width
  hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t
  u : G
  huQ : u ∈ S.QG
  huu : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ S.z
  hunc : ¬ IsConj S.z u
  N : Subgroup G
  hPN : S.QG ⊓ centralizer ({u} : Set G) ≤ N
  hNu : N ≤ centralizer ({u} : Set G)
  hNM : ¬ N ≤ S.M
  hNmin : ∀ N' : Subgroup G, S.QG ⊓ centralizer ({u} : Set G) ≤ N' → N' ≤ N → ¬ N' ≤ S.M →
    N' = N
  g : G
  hgN : g ∈ N
  hgM : g ∉ S.M

namespace SixThreeCtx

variable {S} (c : SixThreeCtx S)

abbrev P : Subgroup G := S.QG ⊓ centralizer ({c.u} : Set G)

abbrev t : G := c.g * S.z * c.g⁻¹

omit [Finite G] in
theorem hzN : S.z ∈ c.N := c.hPN (S.z_mem_cqx (S.mem_M_iff.mpr (S.z_comm_QG c.huQ)))

omit [Finite G] in
theorem commute_u {x : G} (hx : x ∈ c.N) : x * c.u = c.u * x :=
  mem_centralizer_singleton_iff.mp (c.hNu hx)

omit [Finite G] in
theorem exists_v : ∃ v ∈ S.QG, c.u * v ≠ v * c.u := by
  by_contra! h
  rcases S.eq_one_or_z_of_commute c.huQ h with h1 | h1
  · exact c.hu1 h1
  · exact c.huz h1

omit [Finite G] in
theorem conj_mem_P {x : G} (hxN : x ∈ c.N) (hxM : x * S.z = S.z * x) {y : G} (hy : y ∈ c.P) :
    x * y * x⁻¹ ∈ c.P := by
  obtain ⟨hyQ, hyu⟩ := mem_inf.mp hy
  refine mem_inf.mpr ⟨S.conj_mem_QG (S.mem_M_iff.mpr hxM) hyQ, ?_⟩
  exact mul_mem (mul_mem (c.hNu hxN) hyu) (inv_mem (c.hNu hxN))

omit [Finite G] in
theorem z_mem_pCore : S.z ∈ (CFSG.pCore 2 c.N).map c.N.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : orderOf c.u = 2 := orderOf_eq_prime (by rw [pow_two]; exact c.huu) c.hu1
  have hzO := c.hO c.u c.huQ hu2
  set X := (oTwoCent c.u).subgroupOf c.N with hX
  have hXn : X.Normal := ⟨fun x hx n => by
    rw [hX, mem_subgroupOf] at hx ⊢
    exact conj_mem_oTwoCent (c.hNu n.2) hx⟩
  have hX2 : IsPGroup 2 X :=
    (isPGroup_oTwoCent c.u).comap_of_injective c.N.subtype c.N.subtype_injective
  have hle : X ≤ CFSG.pCore 2 c.N := le_sSup ⟨hXn, hX2⟩
  exact ⟨⟨S.z, c.hzN⟩, hle (by rw [hX, mem_subgroupOf]; exact hzO), rfl⟩

omit [Finite G] in
theorem le_M_of_lt {H : Subgroup G} (hPH : c.P ≤ H) (hHN : H ≤ c.N) (hne : H ≠ c.N) :
    H ≤ S.M := by
  by_contra h
  exact hne (c.hNmin H hPH hHN h)

theorem le_closure : c.N ≤ closure {x | ∃ n ∈ c.N, ∃ q ∈ zpowers c.u ⊔ S.Esub c.u
    (Classical.choose c.exists_v), n * q * n⁻¹ = x} := by
  set v := Classical.choose c.exists_v
  obtain ⟨hvQ, huv⟩ := Classical.choose_spec c.exists_v
  rw [S.sup_Esub c.huQ hvQ huv]
  set R := closure {x | ∃ n ∈ c.N, ∃ q ∈ c.P, n * q * n⁻¹ = x} with hR
  have hRN : R ≤ c.N := by
    rw [hR, closure_le]
    rintro _ ⟨n, hn, q, hq, rfl⟩
    exact c.N.mul_mem (c.N.mul_mem hn (c.hPN hq)) (c.N.inv_mem hn)
  have hPR : c.P ≤ R := fun q hq => subset_closure ⟨1, c.N.one_mem, q, hq, by group⟩
  by_contra hNR
  have hRM := c.le_M_of_lt hPR hRN fun h => hNR (h ▸ le_refl _)
  apply c.hNM
  intro n hn
  refine S.mem_M_of_commute_cqx c.huQ c.hu1 c.huz c.hunc fun y hyQ hyu => ?_
  have h1 : n⁻¹ * y * n⁻¹⁻¹ ∈ S.M := hRM (subset_closure ⟨n⁻¹, c.N.inv_mem hn, y,
    mem_inf.mpr ⟨hyQ, mem_centralizer_singleton_iff.mpr hyu⟩, rfl⟩)
  have h2 := S.mem_M_iff.mp h1
  rw [inv_inv] at h2
  calc y * (n * S.z * n⁻¹) = n * ((n⁻¹ * y * n) * S.z) * n⁻¹ := by group
    _ = n * (S.z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h2]
    _ = n * S.z * n⁻¹ * y := by group

theorem exists_sylow : ∃ T : Sylow 2 c.N, ∀ x ∈ (T : Subgroup c.N), (x : G) * S.z = S.z * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (c.P.subgroupOf c.N) :=
    (S.isPGroup_QG.to_le inf_le_left).comap_of_injective c.N.subtype c.N.subtype_injective
  obtain ⟨T, hT⟩ := hP2.exists_le_sylow
  refine ⟨T, fun x hx => ?_⟩
  have hle : (T : Subgroup c.N).map c.N.subtype ≤ S.M := by
    refine S.le_M_of_isPGroup_of_cqx_le c.huQ c.hu1 c.huz c.hunc (T.isPGroup'.map _) ?_
    intro q hq
    exact ⟨⟨q, c.hPN hq⟩, hT (by rw [mem_subgroupOf]; exact hq), rfl⟩
  exact S.mem_M_iff.mp (hle ⟨x, hx, rfl⟩)

theorem twoTwo (h22 : S14.AschbacherTwoTwoStmt) : IsSThreeAt S.z c.N ∨ IsAFiveAt S.z c.N := by
  set v := Classical.choose c.exists_v with hv
  obtain ⟨hvQ, huv⟩ := Classical.choose_spec c.exists_v
  have hsup := S.sup_Esub c.huQ hvQ huv
  have hEN : S.Esub c.u v ≤ c.N := fun x hx => c.hPN (hsup ▸ mem_sup_right hx)
  have hUN : zpowers c.u ≤ c.N := by
    rw [zpowers_le]
    exact c.hPN (mem_inf.mpr ⟨c.huQ, mem_centralizer_singleton_iff.mpr rfl⟩)
  refine h22 G c.N (zpowers c.u) (S.Esub c.u v) S.z hUN hEN ?_ ?_
    (S.zpowers_inf_Esub c.huu huv) (S.isExtraspecialPGroup_Esub c.hn c.huQ hvQ huv)
    ((S.mem_Esub).mpr ⟨S.z_mem_QG, (S.z_comm_QG c.huQ).symm, (S.z_comm_QG hvQ).symm⟩)
    (fun x hx hc => S.eq_one_or_z_of_mem_Esub c.huQ hvQ huv hx fun y hy => hc y hy) ?_
    c.exists_sylow c.z_mem_pCore c.hNM ?_ c.le_closure
  · intro x hx n hn
    rw [mem_zpowers_iff_of_mul_self c.huu] at hx
    rcases hx with rfl | rfl
    · group
    · exact (c.commute_u hn).symm
  · intro x hx
    rw [mem_zpowers_iff_of_mul_self c.huu] at hx
    rcases hx with rfl | rfl
    · exact mul_one 1
    · exact c.huu
  · intro x hxN hxz q hq
    rw [hsup] at hq ⊢
    exact c.conj_mem_P hxN hxz hq
  · intro H hQH hHN hne
    rw [hsup] at hQH
    exact c.le_M_of_lt hQH hHN hne

omit [Finite G] in
theorem t_mem_zConj : c.t ∈ S.zConj c.N := conj_mem_conjIn c.hgN

omit [Finite G] in
theorem t_ne_z : c.t ≠ S.z := by
  intro h
  apply c.hgM
  rw [S.mem_M_iff]
  calc c.g * S.z = c.g * S.z * c.g⁻¹ * c.g := by group
    _ = S.z * c.g := by rw [show c.g * S.z * c.g⁻¹ = S.z from h]

omit [Finite G] in
theorem t_not_mem_QG : c.t ∉ S.QG := fun h => c.t_ne_z (c.hW c.g h)

omit [Finite G] in
theorem t_mul_self : c.t * c.t = 1 := by
  change c.g * S.z * c.g⁻¹ * (c.g * S.z * c.g⁻¹) = 1
  rw [show c.g * S.z * c.g⁻¹ * (c.g * S.z * c.g⁻¹) = c.g * (S.z * S.z) * c.g⁻¹ by group,
    S.z_mul_z]
  group

omit [Finite G] in
theorem u_mem_Qa : c.u ∈ S.Qa c.g := by
  rw [S.Qa_eq_map]
  refine ⟨c.u, c.huQ, ?_⟩
  change c.g * c.u * c.g⁻¹ = c.u
  rw [c.commute_u c.hgN]
  group

omit [Finite G] in
theorem commute_u_t : c.u * c.t = c.t * c.u := by
  have h1 : c.g * c.u = c.u * c.g := c.commute_u c.hgN
  have h2 : c.u * S.z = S.z * c.u := S.z_comm_QG c.huQ
  have h3 : c.u * c.g⁻¹ = c.g⁻¹ * c.u := by
    calc c.u * c.g⁻¹ = c.g⁻¹ * (c.g * c.u) * c.g⁻¹ := by group
      _ = c.g⁻¹ * (c.u * c.g) * c.g⁻¹ := by rw [h1]
      _ = c.g⁻¹ * c.u := by group
  change c.u * (c.g * S.z * c.g⁻¹) = c.g * S.z * c.g⁻¹ * c.u
  calc c.u * (c.g * S.z * c.g⁻¹) = (c.u * c.g) * S.z * c.g⁻¹ := by group
    _ = c.g * (c.u * S.z) * c.g⁻¹ := by rw [← h1]; group
    _ = c.g * S.z * (c.u * c.g⁻¹) := by rw [h2]; group
    _ = c.g * S.z * c.g⁻¹ * c.u := by rw [h3]; group

omit [Finite G] in
theorem cqt_le : S.QG ⊓ centralizer ({c.t} : Set G) ≤ c.P := by
  intro x hx
  obtain ⟨hxQ, hxt⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩
  by_contra hxu
  have hc : x * c.u * x⁻¹ * c.u⁻¹ = S.z := by
    rcases S.commutator_eq_one_or_z hxQ c.huQ with h | h
    · exfalso
      apply hxu
      calc x * c.u = x * c.u * x⁻¹ * c.u⁻¹ * (c.u * x) := by group
        _ = c.u * x := by rw [h, one_mul]
    · exact h
  have hxT : x ∈ (S.conjBy c.g).M := by
    rw [(S.conjBy c.g).mem_M_iff, conjBy_z]
    exact mem_centralizer_singleton_iff.mp hxt
  have hu' : x * c.u * x⁻¹ ∈ S.Qa c.g := (S.conjBy c.g).conj_mem_QG hxT c.u_mem_Qa
  have hz : S.z ∈ S.Qa c.g := by
    rw [← hc]
    exact mul_mem hu' (inv_mem c.u_mem_Qa)
  exact S.z_not_mem_Qa c.hW c.t_ne_z hz

theorem not_le_centralizer_t : ¬ c.P ≤ centralizer ({c.t} : Set G) := by
  intro h
  apply c.hunc
  refine (S.isConj_iff_exists_le_conj c.huQ c.hu1 c.huz).mpr ⟨c.g, c.hgM, fun x hxQ hxu => ?_⟩
  exact mem_centralizer_singleton_iff.mp
    (h (mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr hxu⟩))

end SixThreeCtx

theorem exists_sixThreeCtx (hn : 2 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t)
    {g₀ : G} (hg₀M : g₀ ∉ S.M) (hg₀ : S.QG ⊓ S.Qa g₀ ≠ ⊥) : Nonempty (SixThreeCtx S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev := even_card_of_isPGroup (S.isPGroup_QG.to_le inf_le_left) hg₀
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S.QG ⊓ S.Qa g₀)) 2
    (even_iff_two_dvd.mp hev)
  set u : G := (u' : G) with hu
  have hu2 : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hu'
  have huQ : u ∈ S.QG := (mem_inf.mp u'.2).1
  have huQa : u ∈ S.Qa g₀ := (mem_inf.mp u'.2).2
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z := by
    intro h
    apply hg₀M
    rw [S.mem_M_iff]
    calc g₀ * S.z = g₀ * S.z * g₀⁻¹ * g₀ := by group
      _ = S.z * g₀ := by rw [h]
  have huz : u ≠ S.z := fun h => S.z_not_mem_Qa hW hg₀z (h ▸ huQa)
  have hunc : ¬ IsConj S.z u := by
    intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact huz (hc ▸ hW c (hc ▸ huQ))
  have hCu : ¬ centralizer ({u} : Set G) ≤ S.M := by
    intro hle
    set T := S.conjBy g₀ with hT
    have hTz : T.z = g₀ * S.z * g₀⁻¹ := rfl
    have huT : u ∈ T.QG := huQa
    have huTz : u ≠ T.z := fun h => S.conj_not_mem_QG hW hg₀z (by rw [← hTz, ← h]; exact huQ)
    have hnc : ¬ IsConj T.z u := fun h => hunc ((isConj_iff.mpr ⟨g₀, rfl⟩).trans h)
    apply hnc
    refine (T.isConj_iff_exists_le_conj huT hu1 huTz).mpr ⟨g₀⁻¹, ?_, fun x _ hxu => ?_⟩
    · rw [T.mem_M_iff, hTz]
      intro h
      apply hg₀M
      rw [S.mem_M_iff]
      calc g₀ * S.z = (g₀ * S.z * g₀⁻¹ * g₀⁻¹) * g₀ * g₀ := by group
        _ = (g₀⁻¹ * (g₀ * S.z * g₀⁻¹)) * g₀ * g₀ := by rw [← h]
        _ = S.z * g₀ := by group
    · have hxM := S.mem_M_iff.mp (hle (mem_centralizer_singleton_iff.mpr hxu))
      rw [hTz, show g₀⁻¹ * (g₀ * S.z * g₀⁻¹) * g₀⁻¹⁻¹ = S.z by group]
      exact hxM
  let 𝒩 : Set (Subgroup G) := {N | S.QG ⊓ centralizer ({u} : Set G) ≤ N ∧
    N ≤ centralizer ({u} : Set G) ∧ ¬ N ≤ S.M}
  have hmem : centralizer ({u} : Set G) ∈ 𝒩 := ⟨inf_le_right, le_rfl, hCu⟩
  obtain ⟨N, ⟨hPN, hNu, hNM⟩, hNmin⟩ := (Set.toFinite 𝒩).exists_minimal ⟨_, hmem⟩
  obtain ⟨g, hgN, hgM⟩ := Set.not_subset.mp hNM
  exact ⟨SixThreeCtx.mk hn hW hO u huQ huu hu1 huz hunc N hPN hNu hNM
    (fun N' h1 h2 h3 => le_antisymm h2 (hNmin ⟨h1, h2.trans hNu, h3⟩ h2)) g hgN hgM⟩

end Setting

end CFSG.LargeExtraspecial
