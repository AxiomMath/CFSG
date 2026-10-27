module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {u v : G → K} {κ : K}

structure RegData (H : SzC1Next G L f a t T d V U U₁ k K u v κ)
    (E : Subgroup (Equiv.Perm K)) : Prop where
  le : E ≤ H.perm.range
  normal : (E.subgroupOf H.perm.range).Normal
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x ^ 2 = 1
  card : Nat.card E = 2 ^ f
  reg : ∀ β γ : K, ∃! e : E, (e : Equiv.Perm K) β = γ
  trans : ∀ e ∈ E, ∀ c, e c = e 0 + c

variable (H : SzC1Next G L f a t T d V U U₁ k K u v κ)

include H in
theorem ker_perm :
    H.perm.ker = U.subgroupOf (normalizer (U : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact ⟨H.mem_U_of_perm_eq_one n, H.perm_eq_one_of_mem_U n⟩

noncomputable def nextU (E : Subgroup (Equiv.Perm K)) : Subgroup G :=
  (E.comap H.perm).map (normalizer (U : Set G)).subtype

variable {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E)
include H hE

theorem mem_nextU {x : G} :
    x ∈ H.nextU E ↔ ∃ hx : x ∈ normalizer (U : Set G), H.perm ⟨x, hx⟩ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxE⟩
    exact ⟨⟨x, hx⟩, hxE, rfl⟩

theorem nextU_le : H.nextU E ≤ normalizer (U : Set G) := map_subtype_le _

theorem perm_mem_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) :
    H.perm ⟨x, H.nextU_le hE hx⟩ ∈ E := by
  obtain ⟨hx', hxE⟩ := (H.mem_nextU hE).mp hx
  exact hxE

theorem U_le_nextU : U ≤ H.nextU E := fun x hx =>
  (H.mem_nextU hE).mpr ⟨le_normalizer hx, by
    rw [H.perm_eq_one_of_mem_U ⟨x, le_normalizer hx⟩ hx]; exact one_mem E⟩

theorem conj_mem_nextU {n : G} (hn : n ∈ normalizer (U : Set G)) {x : G}
    (hx : x ∈ H.nextU E) : n * x * n⁻¹ ∈ H.nextU E := by
  have hxN := H.nextU_le hE hx
  have hxE := H.perm_mem_of_mem_nextU hE hx
  have h1 := hE.normal.conj_mem ⟨H.perm ⟨x, hxN⟩, hE.le hxE⟩ (mem_subgroupOf.mpr hxE)
    ⟨H.perm ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩
  rw [mem_subgroupOf] at h1
  refine (H.mem_nextU hE).mpr ⟨mul_mem (mul_mem hn hxN) (inv_mem hn), ?_⟩
  have e : (⟨n * x * n⁻¹, mul_mem (mul_mem hn hxN) (inv_mem hn)⟩ : normalizer (U : Set G)) =
      ⟨n, hn⟩ * ⟨x, hxN⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact h1

theorem normalizer_le_normalizer_nextU :
    normalizer (U : Set G) ≤ normalizer (H.nextU E : Set G) := by
  intro n hn
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => H.conj_mem_nextU hE hn hx, fun hx => ?_⟩
  have h1 := H.conj_mem_nextU hE (inv_mem hn) hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1

theorem card_nextU : Nat.card (H.nextU E) = 2 * (2 ^ f) ^ (k + 1 + 3) := by
  have h1 : Nat.card (H.nextU E) = Nat.card (E.comap H.perm) :=
    Subgroup.card_map_of_injective (normalizer (U : Set G)).subtype_injective
  have h2 := card_eq_card_map_mul_card_ker_of_ker_le H.perm (S := E.comap H.perm)
    (fun n hn => by rw [mem_comap, (MonoidHom.mem_ker).mp hn]; exact one_mem E)
  rw [map_comap_eq_self hE.le] at h2
  have hker : Nat.card H.perm.ker = Nat.card U := by
    rw [H.ker_perm, Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv]
  rw [h1, h2, hE.card, hker, H.stage.card_U]
  ring

theorem isPGroup_nextU : IsPGroup 2 (H.nextU E) :=
  IsPGroup.of_card (n := 1 + f * (k + 1 + 3)) (by rw [H.card_nextU hE, pow_add 2 1, pow_one, pow_mul])

theorem isSylowOf_nextU :
    CFSG.ABGLocalTools.IsSylowOf 2 (H.nextU E) (normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨H.nextU_le hE, H.isPGroup_nextU hE, ?_⟩
  have h1 : (H.nextU E).relIndex (normalizer (U : Set G)) = E.relIndex H.perm.range := by
    rw [relIndex, subgroupOf, nextU,
      comap_map_eq_self_of_injective (normalizer (U : Set G)).subtype_injective, index_comap]
  have htr : ∀ β γ : K, ∃ m ∈ H.perm.range, m β = γ := by
    intro β γ
    obtain ⟨e, he, -⟩ := hE.reg β γ
    exact ⟨e, hE.le e.2, he⟩
  have h2 := card_eq_card_mul_card_inf_stabilizer htr 0
  have h3 := Subgroup.relIndex_mul_card E H.perm.range
  rw [inf_eq_left.mpr hE.le, h2, hE.card, Nat.card_eq_fintype_card, H.card_K, mul_comm] at h3
  have h4 : E.relIndex H.perm.range = Nat.card (H.perm.range ⊓ MulAction.stabilizer
      (Equiv.Perm K) (0 : K) : Subgroup (Equiv.Perm K)) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h3
  rw [h1, h4, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact H.perm_stabilizer.1

theorem perm_nextU {x : G} (hx : x ∈ H.nextU E) (s : K) :
    H.perm ⟨x, H.nextU_le hE hx⟩ s = H.perm ⟨x, H.nextU_le hE hx⟩ 0 + s :=
  hE.trans _ (H.perm_mem_of_mem_nextU hE hx) s

theorem mem_U_of_mem_nextU {x : G} (hx : x ∈ H.nextU E)
    (h0 : H.perm ⟨x, H.nextU_le hE hx⟩ 0 = 0) : x ∈ U := by
  refine H.mem_U_of_perm_eq_one ⟨x, H.nextU_le hE hx⟩ (Equiv.ext fun s => ?_)
  rw [H.perm_nextU hE hx, h0, zero_add, Equiv.Perm.one_apply]

theorem X_conj_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((x * w * x⁻¹) ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) := by
  have e1 := H.perm_apply ⟨x, H.nextU_le hE hx⟩ hw
  rw [H.perm_nextU hE hx, H.perm_zero, add_comm] at e1
  exact (add_right_cancel e1).symm

theorem conj_szA₁_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) :
    ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b :=
  H.conj_szA₁_of_X_conj (H.nextU_le hE hx) fun _ hw => H.X_conj_of_mem_nextU hE hx hw

theorem conj_T₁_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) {y : G} (hy : y ∈ szT₁ L T) :
    y⁻¹ * (x * y * x⁻¹) ∈ szA₁ (szT₁ L T) := by
  have hK' := H.card_K'
  have hxy : x * y * x⁻¹ ∈ szT₁ L T :=
    (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_T₁ H.card_K H.coords H.mu H.lam
      H.nu (H.nextU_le hE hx)) y).mp hy
  have hsq : (x * y * x⁻¹) ^ 2 = y ^ 2 := by
    rw [conj_pow, H.conj_szA₁_of_mem_nextU hE hx _ (H.coords.sq_mem_szA₁ H.stage.ha hK' hy)]
  have hpow : u (x * y * x⁻¹) ^ (2 ^ (a + 1) + 1) = u y ^ (2 ^ (a + 1) + 1) := by
    rw [← (H.coords.sq hxy).2, ← (H.coords.sq hy).2, hsq]
  have hinj : Function.Injective (fun z : K => z ^ (2 ^ (a + 1) + 1)) :=
    Finite.injective_iff_surjective.mpr fun z => SzStartField.exists_pow_theta_succ_eq hK' z
  exact H.coords.inv_mul_mem_szA₁_of_u_eq H.stage.ha hK' hy hxy (hinj hpow).symm

theorem inf_centralizer_nextU :
    H.nextU E ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxC⟩ := mem_inf.mp hx
    have hxU' := H.mem_U_of_mem_nextU hE hxU
      (H.perm_zero_of_mem_centralizer ⟨x, H.nextU_le hE hxU⟩ hxC)
    rw [← H.stage.inf_centralizer]
    exact mem_inf.mpr ⟨hxU', hxC⟩
  · rw [← H.stage.inf_centralizer]
    exact inf_le_inf_right _ (H.U_le_nextU hE)

theorem conj_t_not_mem_of_mem_nextU {x : G} (hx : x ∈ H.nextU E) (hxU : x ∉ U) :
    x * t * x⁻¹ ∉ szA L T t := by
  intro hA
  have htN : t ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun b hb => by
      rw [H.stage.t_inv, ← H.stage.t_comm (szA₁_le _ hb), mul_assoc, H.stage.t_mul_self, mul_one]
      exact hb
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers H.stage.t_mul_self htN hA with
    h1 | h1
  · exact H.stage.conj_not_mem_U₁ x (H.stage.V_le_U₁ (H.stage.le h1))
  · apply hxU
    refine H.mem_U_of_mem_nextU hE hx ?_
    rw [H.perm_zero]
    show v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = 0
    rw [H.stage.t_inv]
    exact H.stage.X_eq_zero_of_mem_V H.card_K H.coords (H.stage.le h1)

end SzC1Next

end CFSG.SeitzReduction.RankOne
