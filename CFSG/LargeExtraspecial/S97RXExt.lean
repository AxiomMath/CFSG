module

public import CFSG.LargeExtraspecial.S111BA5Tv
public import CFSG.LargeExtraspecial.S97RXLam
public import CFSG.LargeExtraspecial.S9SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M}

variable (S g A) in
@[expose] def BadPair (h k : G) (m : S.M) : Prop :=
  Pair111 S g A h k ((m : G) * k) ∧ Ebar S k ((m : G) * k) ≠ ⊥ ∧
    4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k)

namespace BadPair

variable (B : BadPair S g A h k m)
include B

theorem map_eq_of_max (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    {y : S.M} (hx : S.ρ y ∈ S9.X97 S k m) {l : S.O} (hl : l ∈ S.Lbar k)
    (hlE : l ∉ Ebar S k ((m : G) * k))
    (hxN : S.ρ y * l * (S.ρ y)⁻¹ ∈ normalizer (S.Lbar k : Set S.O)) :
    A.map (MulAut.conj (y : G)).toMonoidHom = A := by
  obtain ⟨P, hE, h4⟩ := B
  rcases P.cfg.inter y.2 with hA | hdisj
  · exact hA
  exfalso
  set O := O2Sub (S9.X97 S k m) with hO
  have hmem' : ((y : G) * k) * S.z * ((y : G) * k)⁻¹ ∈ A.map (MulAut.conj (y : G)).toMonoidHom :=
    mem_map_conj_iff.mpr (by
      rw [show (y : G)⁻¹ * ((y : G) * k * S.z * ((y : G) * k)⁻¹) * y = k * S.z * k⁻¹ by group]
      exact P.mem)
  have P₁ : Pair111 S g A (y : G) k ((y : G) * k) :=
    ⟨P.cfg, y.2, hdisj, P.mem, P.ne, hmem', conj_ne_z' S y.2 P.ne⟩
  have hconjE : (Ebar S k ((m : G) * k)).map (MulAut.conj (S.ρ y)).toMonoidHom ≤
      Ebar S ((y : G) * k) k := by
    rintro _ ⟨e, he, rfl⟩
    have heO : e ∈ O := by
      rw [← P.inf_O2Sub_eq] at he
      exact he.2
    refine ⟨conj_mem_Lbar_mul S y he.1, ?_⟩
    exact O2Sub_le_normalizer_Lbar P.hy.hyp4 P.hy.cons le_sup_left (Lbar_sup_le_Mbar S _ _)
      (O2Sub_normal hx heO)
  have hlF : S.ρ y * l * (S.ρ y)⁻¹ ∈ Ebar S ((y : G) * k) k :=
    ⟨conj_mem_Lbar_mul S y hl, hxN⟩
  have hlnot : S.ρ y * l * (S.ρ y)⁻¹ ∉
      (Ebar S k ((m : G) * k)).map (MulAut.conj (S.ρ y)).toMonoidHom := by
    rintro ⟨e, he, he'⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he'
    have hel : e = l := by
      have := congrArg (fun w => (S.ρ y)⁻¹ * w * S.ρ y) he'
      simpa [mul_assoc] using this
    exact hlE (hel ▸ he)
  have hlt : Nat.card (Ebar S k ((m : G) * k)) < Nat.card (Ebar S ((y : G) * k) k) := by
    rw [← card_map_of_injective (f := (MulAut.conj (S.ρ y)).toMonoidHom)
      (MulAut.conj (S.ρ y)).injective]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hconjE) fun hc => hlnot ?_
    rw [Subgroup.eq_of_le_of_card_ge hconjE hc.ge]
    exact hlF
  rw [← P₁.card_Ebar_eq] at hlt
  have hE0 : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
  have hE₁ : Ebar S k ((y : G) * k) ≠ ⊥ := fun h0 => by
    rw [h0, card_bot] at hlt
    omega
  by_cases hidx : Nat.card (S.Lbar k) = 2 * Nat.card (Ebar S k ((y : G) * k))
  · exact P₁.false_of_index_two hE₁ hidx
  have X₁ := P₁.hyp97 hE₁
  have h4₁ := X₁.four_mul_card_le P₁.not_Lbar_le_O2Sub (by rw [P₁.inf_O2Sub_eq]; exact hidx)
  rw [P₁.inf_O2Sub_eq] at h4₁
  have := hmax (y : G) k y ⟨P₁, hE₁, h4₁⟩
  omega

omit B in
theorem mem_ptFix_span_iff {x : S.O} {w : S.Qt} :
    x ∈ ptFix S ((ZMod 2) ∙ w) ↔ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  rw [mem_ptFix]
  constructor
  · exact fun h => h w (Submodule.mem_span_singleton_self w)
  · intro h v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, h]

theorem map_clSub_of_max (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    {x : S.O} (hx : x ∈ S9.X97 S k m) {l : S.O} (hl : l ∈ S.Lbar k)
    (hlE : l ∉ Ebar S k ((m : G) * k)) (hxN : x * l * x⁻¹ ∈ normalizer (S.Lbar k : Set S.O))
    {v : S.Qt} (hv : v ∈ S.clSub A) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp (S9.X97_le_Mbar hx)
  exact ρ_apply_mem_clSub (B.map_eq_of_max hmax hx hl hlE hxN) hv

theorem false_of_forall_map_clSub
    (hall : ∀ x ∈ S9.X97 S k m, ∀ v ∈ S.clSub A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A) :
    False := by
  obtain ⟨P, -, -⟩ := B
  have hU : S9.Ut S k (S9.X97 S k m) ≤ S.clSub A := by
    rw [S9.Ut, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx _ (S.cl_mem_clSub P.mem P.memQ)
  have hb : S.cl (((m : G) * k) * S.z * ((m : G) * k)⁻¹) ∈ S9.Ut S k (S9.X97 S k m) := by
    rw [← S9.Ut_mul_eq P.hy.hyp4 m le_sup_left le_sup_right]
    exact S9.cl_mem_Ut _
  exact cl_conj_z_ne_zero S P.memQ' P.ne'
    (P.eq_zero_of_mem_clSub (hU hb) (S.cl_mem_clSub P.mem' P.memQ'))

theorem false_of_meet (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
    (hmeet : ∀ c : Lam97 S k m,
      conjSubgroup c (T97 S k m k) ⊓ normalizer (T97 S k m k : Set (Lam97 S k m)) ≠ ⊥) :
    False := by
  refine B.false_of_forall_map_clSub fun x hx v hv => ?_
  have P := B.1
  have hE := B.2.1
  have X := P.hyp97 hE
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (hmeet (pi97 S k m ⟨x, hx⟩))
  obtain ⟨huc, huN⟩ := mem_inf.mp hu
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  have hl := (mem_conjSubgroup).mp huc
  obtain ⟨l, hlL, hle⟩ := exists_of_mem_T97 hl
  have hue : u = pi97 S k m (⟨x, hx⟩ * l * (⟨x, hx⟩ : ↥(S9.X97 S k m))⁻¹) := by
    simp only [map_mul, map_inv, hle]
    group
  rw [hue] at huN hu1'
  have hN := (H97.pi97_mem_normalizer_iff X hodd le_sup_left P.hy.hyp4 P.hy.cons _).mp huN
  have hlE : (l : S.O) ∉ Ebar S k ((m : G) * k) := by
    intro hlE
    rw [← P.inf_O2Sub_eq] at hlE
    have h1 := (H97.pi97_eq_one_iff X hodd P.hy.hyp4 hlL).mpr hlE.2
    apply hu1'
    simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  exact B.map_clSub_of_max hmax hx hlL hlE
    (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hN) hv

end BadPair

end CFSG.LargeExtraspecial.S11
