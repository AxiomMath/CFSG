module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Cover
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightCover

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup CFSG.Open

namespace Child8Weyl

variable {W : Type} [Group W] [Finite W] (M : Child8Weyl W)

theorem z_mem_center : (⟨M.z, M.z_mem⟩ : M.Wp) ∈ center M.Wp :=
  mem_center_iff.2 fun x => Subtype.ext (M.z_comm x)

theorem z_mul_self : M.z * M.z = 1 := by
  have h := pow_card_eq_one' (G := center M.Wp) (x := ⟨_, M.z_mem_center⟩)
  rw [M.card_center, pow_two] at h
  exact congrArg (fun y : center M.Wp => ((y : M.Wp) : W)) h

theorem s_inv : M.s⁻¹ = M.s := inv_eq_of_mul_eq_one_right M.s_mul_self

theorem conj_mem {x : W} (hx : x ∈ M.Wp) (w : W) : w * x * w⁻¹ ∈ M.Wp :=
  M.normal.conj_mem x hx w

@[expose] noncomputable def sConj : MulAut M.Wp := @MulAut.conjNormal W _ M.Wp M.normal M.s

theorem coe_sConj (x : M.Wp) : (M.sConj x : W) = M.s * x * M.s⁻¹ :=
  @MulAut.conjNormal_apply W _ M.Wp M.normal M.s x

theorem sConj_sConj (x : M.Wp) : M.sConj (M.sConj x) = x := by
  apply Subtype.ext
  rw [coe_sConj, coe_sConj, M.s_inv]
  calc M.s * (M.s * x * M.s) * M.s = (M.s * M.s) * x * (M.s * M.s) := by group
    _ = x := by rw [M.s_mul_self, one_mul, mul_one]

end Child8Weyl

section Standard

variable {G : Type} [Group G] {L : Subgroup G} {W : Type} [Group W] [Finite W]

structure Std (L : Subgroup G) (M : Child8Weyl W) where
  θ : M.Wp ≃* L
  centralizer_eq : centralizer (L : Set G) = zpowers ((θ ⟨M.z, M.z_mem⟩ : L) : G)
  centralizer_z : centralizer ({((θ ⟨M.z, M.z_mem⟩ : L) : G)} : Set G) = normalizer (L : Set G)

namespace Std

variable {M : Child8Weyl W} (S : Std L M)

@[expose] noncomputable def phi : M.Wp →* G := L.subtype.comp S.θ.toMonoidHom

theorem phi_apply (x : M.Wp) : S.phi x = ((S.θ x : L) : G) := rfl

theorem phi_injective : Function.Injective S.phi := fun _ _ h =>
  S.θ.injective (Subtype.ext h)

theorem phi_mem (x : M.Wp) : S.phi x ∈ L := (S.θ x).2

theorem exists_phi_eq {l : G} (hl : l ∈ L) : ∃ x, S.phi x = l :=
  ⟨S.θ.symm ⟨l, hl⟩, by rw [phi_apply, MulEquiv.apply_symm_apply]⟩

@[expose] noncomputable def zG : G := S.phi ⟨M.z, M.z_mem⟩

theorem zG_mem : S.zG ∈ L := S.phi_mem _

theorem zG_ne_one : S.zG ≠ 1 := fun h =>
  M.z_ne_one (congrArg Subtype.val (S.phi_injective (h.trans (map_one S.phi).symm)))

theorem zG_mul_self : S.zG * S.zG = 1 := by
  rw [zG, ← map_mul, show (⟨M.z, M.z_mem⟩ * ⟨M.z, M.z_mem⟩ : M.Wp) = 1 from
    Subtype.ext M.z_mul_self, map_one]

theorem orderOf_zG : orderOf S.zG = 2 :=
  orderOf_eq_prime (by rw [pow_two, S.zG_mul_self]) S.zG_ne_one

theorem mem_centralizer_L_iff {g : G} : g ∈ centralizer (L : Set G) ↔ g = 1 ∨ g = S.zG := by
  rw [S.centralizer_eq]
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    change S.zG ^ k = 1 ∨ S.zG ^ k = S.zG
    rw [← zpow_mod_orderOf, S.orderOf_zG]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h] <;> simp
  · rintro (rfl | rfl)
    exacts [one_mem _, mem_zpowers _]

theorem mem_normalizer_iff_comm {g : G} : g ∈ normalizer (L : Set G) ↔ g * S.zG = S.zG * g := by
  rw [← S.centralizer_z, mem_centralizer_singleton_iff]
  rfl

theorem phi_conj (u x : M.Wp) : S.phi (u * x * u⁻¹) = S.phi u * S.phi x * (S.phi u)⁻¹ := by
  simp only [map_mul, map_inv]

theorem mem_of_inner {h : G} (u : M.Wp)
    (hu : ∀ x : M.Wp, h * S.phi x * h⁻¹ = S.phi (u * x * u⁻¹)) : h ∈ L := by
  have hc : (S.phi u)⁻¹ * h ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨x, rfl⟩ := S.exists_phi_eq hl
    have h1 := hu x
    rw [S.phi_conj] at h1
    calc S.phi x * ((S.phi u)⁻¹ * h) =
          (S.phi u)⁻¹ * (S.phi u * S.phi x * (S.phi u)⁻¹) * h := by group
      _ = (S.phi u)⁻¹ * (h * S.phi x * h⁻¹) * h := by rw [h1]
      _ = (S.phi u)⁻¹ * h * S.phi x := by group
  have hcL : (S.phi u)⁻¹ * h ∈ L := by
    rcases S.mem_centralizer_L_iff.1 hc with h1 | h1 <;> rw [h1]
    exacts [one_mem L, S.zG_mem]
  have h' : h = S.phi u * ((S.phi u)⁻¹ * h) := by group
  rw [h']
  exact mul_mem (S.phi_mem u) hcL

end Std

end Standard

section Exists

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {W : Type} [Group W] [Finite W]

open CFSG.LocalAnalysis.ComponentInitial in
theorem card_center_eq_two (hset : StandardSetting G L) (hZ : center L ≠ ⊥)
    (hZ2 : IsPGroup 2 (center L))
    (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    Nat.card (center L) = 2 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hset.standard.1.1
  obtain ⟨-, -, -, hcyc, -⟩ := std_center_involution hset hZ
  have hel := binary_split_orthogonal_eight_perfect_central_two_kernel_elementary
    (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hZ2) hX
  rw [QuotientGroup.ker_mk'] at hel
  have hdvd : Nat.card (center L) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 _
  have h1 : Nat.card (center L) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.1 h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h h1
  · exact h

theorem exists_std
    (M : Child8Weyl W) (hset : StandardSetting G L)
    (h2 : Nat.card (center L) = 2)
    (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) : Nonempty (Std L M) := by
  obtain ⟨zL, hzL1, -⟩ := (Nat.card_eq_two_iff' (1 : center L)).mp h2
  obtain ⟨θ, hθ⟩ := Cover.omega8plus_double_cover_unique_of_mem_center M.Wp L M.perfect
    hset.standard.1.1 M.card_center h2 M.lieModel hX M.z_mem_center
    (fun h => M.z_ne_one (congrArg Subtype.val h)) zL.2 (fun h => hzL1 (Subtype.ext h))
  have hsq : ((zL : L) : G) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := zL)
    rw [h2] at h
    simpa using congrArg (fun y : center L => ((y : L) : G)) h
  have hz1 : ((zL : L) : G) ≠ 1 := fun h => hzL1 (Subtype.ext (Subtype.ext h))
  have hz2 : orderOf ((zL : L) : G) = 2 := orderOf_eq_prime hsq hz1
  have htZ : ((zL : L) : G) ∈ (center L).map L.subtype := ⟨zL, zL.2, rfl⟩
  refine ⟨⟨θ, ?_, ?_⟩⟩
  · rw [hθ]
    exact centralizer_eq_zpowers_of_standard hset (hypothesisOne_of_lieModel hX)
      (FoursGroupCondition.of_mulEquiv θ M.fours) hz2 htZ
  · rw [hθ]
    exact centralizer_eq_normalizer_of_standard hset.standard h2 zL.2 hz2

end Exists

namespace Std

variable {G : Type} [Group G] {L : Subgroup G} {W : Type} [Group W] [Finite W]
  {M : Child8Weyl W} (S : Std L M)

@[expose] noncomputable def autOf (h : normalizer (L : Set G)) : MulAut M.Wp :=
  (S.θ.trans (L.normalizerMonoidHom h)).trans S.θ.symm

theorem phi_autOf (h : normalizer (L : Set G)) (x : M.Wp) :
    S.phi (S.autOf h x) = h * S.phi x * (h : G)⁻¹ := by
  rw [autOf, phi_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply,
    normalizerMonoidHom_apply_apply_coe, phi_apply]

theorem mem_of_autOf_eq {h : G} (hh : h ∈ normalizer (L : Set G)) {w : W} (hwW : w ∈ M.Wp)
    (hw : ∀ x : M.Wp, (S.autOf ⟨h, hh⟩ x : W) = w * x * w⁻¹) : h ∈ L :=
  S.mem_of_inner ⟨w, hwW⟩ fun x => by
    rw [← S.phi_autOf ⟨h, hh⟩ x]
    congr 1
    exact Subtype.ext (hw x)

theorem exists_outer (hN : ∃ h ∈ normalizer (L : Set G), h ∉ L) :
    ∃ c ∈ normalizer (L : Set G), c ∉ L ∧
      ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x) := by
  obtain ⟨h, hh, hhL⟩ := hN
  obtain ⟨w, hw⟩ := M.aut (S.autOf ⟨h, hh⟩)
  rcases M.mem_or_mul_mem w with hwW | hwW
  · exact absurd (S.mem_of_autOf_eq hh hwW hw) hhL
  set u : M.Wp := ⟨w * M.s, hwW⟩ with hu
  refine ⟨(S.phi u)⁻¹ * h, mul_mem (inv_mem (le_normalizer (S.phi_mem u))) hh, fun hc => hhL ?_,
    fun x => ?_⟩
  · have e : h = S.phi u * ((S.phi u)⁻¹ * h) := by group
    rw [e]
    exact mul_mem (S.phi_mem u) hc
  · have e1 : (S.phi u)⁻¹ * h * S.phi x * ((S.phi u)⁻¹ * h)⁻¹ =
        (S.phi u)⁻¹ * (h * S.phi x * h⁻¹) * S.phi u := by group
    rw [e1, ← S.phi_autOf ⟨h, hh⟩ x, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_mul, coe_mul, coe_inv, hw x, M.coe_sConj, hu]
    calc (w * M.s)⁻¹ * (w * x * w⁻¹) * (w * M.s) = M.s⁻¹ * x * M.s := by group
      _ = M.s * x * M.s⁻¹ := by rw [M.s_inv]

theorem mul_self_eq {c : G} (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x)) :
    c * c = 1 ∨ c * c = S.zG := by
  apply S.mem_centralizer_L_iff.1
  rw [mem_centralizer_iff]
  intro l hl
  obtain ⟨x, rfl⟩ := S.exists_phi_eq hl
  have h1 : c * c * S.phi x * (c * c)⁻¹ = S.phi x := by
    calc c * c * S.phi x * (c * c)⁻¹ = c * (c * S.phi x * c⁻¹) * c⁻¹ := by group
      _ = S.phi x := by rw [hc, hc, M.sConj_sConj]
  calc S.phi x * (c * c) = (c * c * S.phi x * (c * c)⁻¹) * (c * c) := by rw [h1]
    _ = c * c * S.phi x := by group

theorem inv_conj_eq {c : G} (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x))
    (x : M.Wp) : c⁻¹ * S.phi x * c = S.phi (M.sConj x) := by
  have h1 := hc (M.sConj x)
  rw [M.sConj_sConj] at h1
  rw [← h1]
  group

theorem mem_or_mul_inv_mem {c : G} (hc : ∀ x : M.Wp, c * S.phi x * c⁻¹ = S.phi (M.sConj x))
    {h : G} (hh : h ∈ normalizer (L : Set G)) : h ∈ L ∨ h * c⁻¹ ∈ L := by
  obtain ⟨w, hw⟩ := M.aut (S.autOf ⟨h, hh⟩)
  rcases M.mem_or_mul_mem w with hwW | hwW
  · exact Or.inl (S.mem_of_autOf_eq hh hwW hw)
  refine Or.inr (S.mem_of_inner ⟨w * M.s, hwW⟩ fun x => ?_)
  calc h * c⁻¹ * S.phi x * (h * c⁻¹)⁻¹ = h * (c⁻¹ * S.phi x * c) * h⁻¹ := by group
    _ = h * S.phi (M.sConj x) * h⁻¹ := by rw [S.inv_conj_eq hc]
    _ = S.phi (S.autOf ⟨h, hh⟩ (M.sConj x)) := (S.phi_autOf ⟨h, hh⟩ _).symm
    _ = S.phi (⟨w * M.s, hwW⟩ * x * ⟨w * M.s, hwW⟩⁻¹) := by
      congr 1
      apply Subtype.ext
      rw [hw, M.coe_sConj, coe_mul, coe_mul, coe_inv]
      group

end Std

end CFSG.EvenSmallLie.OmegaEight.Child8
