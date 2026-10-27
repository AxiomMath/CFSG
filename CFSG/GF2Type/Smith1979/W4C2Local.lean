module

public import CFSG.GF2Type.Smith1979.W4C2Coord
public import CFSG.GF2Type.Smith1979.W4C2Test
public import CFSG.GF2Type.Smith1979.W4C1Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.GLR
  CFSG.RankThree.OrthogonalInvolutions

namespace Local

section Conj

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

theorem conjEquiv_apply_T (T : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V) (v : V) :
    conjEquiv T f (T v) = T (f v) := by
  rw [conjEquiv_apply, T.symm_apply_apply]

theorem conjEquiv_mul (T : V ≃ₗ[ZMod 2] V') (f g : V ≃ₗ[ZMod 2] V) :
    conjEquiv T (f * g) = conjEquiv T f * conjEquiv T g := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, conjEquiv_apply, conjEquiv_apply, conjEquiv_apply,
    T.symm_apply_apply]
  rfl

theorem conjEquiv_one (T : V ≃ₗ[ZMod 2] V') : conjEquiv T 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [conjEquiv_apply]
  exact T.apply_symm_apply v

theorem conjEquiv_injective (T : V ≃ₗ[ZMod 2] V') : Function.Injective (conjEquiv T) := by
  intro f g h
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun F : V' ≃ₗ[ZMod 2] V' => F (T v)) h
  simp only [conjEquiv_apply_T] at this
  exact T.injective this

theorem commSpace_conjEquiv (T : V ≃ₗ[ZMod 2] V') (t : V ≃ₗ[ZMod 2] V) :
    commSpace (conjEquiv T t) = (commSpace t).map (T : V →ₗ[ZMod 2] V') := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨t (T.symm v) - T.symm v, sub_mem_commSpace t _, ?_⟩
    rw [map_sub, LinearEquiv.coe_coe, conjEquiv_apply, T.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hy
    refine ⟨T w, ?_⟩
    rw [conjEquiv_apply_T, map_sub]
    rfl

theorem isTypeA_of_conjEquiv (T : V ≃ₗ[ZMod 2] V') [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} {q' : QuadraticForm (ZMod 2) V'}
    (hq : ∀ v, q' (T v) = q v) {t : V ≃ₗ[ZMod 2] V} {l : ℕ}
    (h : IsTypeA q' (conjEquiv T t) l) : IsTypeA q t l := by
  obtain ⟨hiso, hne, hinv, hdim, hsing⟩ := h
  refine ⟨fun v => ?_, fun h1 => hne (by rw [h1, conjEquiv_one]), ?_, ?_, fun x hx => ?_⟩
  · rw [← hq (t v), ← hq v, ← conjEquiv_apply_T T t v, hiso]
  · apply conjEquiv_injective T
    rw [conjEquiv_mul, hinv, conjEquiv_one]
  · rw [← hdim, commSpace_conjEquiv, LinearEquiv.finrank_map_eq]
  · rw [← hq x]
    refine hsing _ ?_
    rw [commSpace_conjEquiv]
    exact Submodule.mem_map_of_mem hx

end Conj

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def cT (T : S.Qt ≃ₗ[ZMod 2] Vm) : S.Mbar →* (Vm ≃ₗ[ZMod 2] Vm) where
  toFun m := conjEquiv T ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  map_one' := conjEquiv_one T
  map_mul' _ _ := conjEquiv_mul T _ _

theorem cT_apply (T : S.Qt ≃ₗ[ZMod 2] Vm) (m : S.Mbar) (v : S.Qt) :
    cT T m (T v) = T (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := conjEquiv_apply_T T _ v

theorem cT_injective (T : S.Qt ≃ₗ[ZMod 2] Vm) : Function.Injective (cT (S := S) T) := by
  intro m m' h
  exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => by
    have := congrArg (fun F : Vm ≃ₗ[ZMod 2] Vm => F (T v)) h
    simp only [cT_apply] at this
    exact T.injective this))

theorem polar_q0_T (T : S.Qt ≃ₗ[ZMod 2] Vm) (hTq : ∀ v, q0 (T v) = S.q v) (x v : S.Qt) :
    polar q0 (T x) (T v) = polar S.q x v := by
  unfold polar
  rw [← map_add, hTq, hTq, hTq]

end Local

open Local

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem transport (T : S.Qt ≃ₗ[ZMod 2] Vm)
    (hTq : ∀ v, q0 (T v) = S.q v)
    (hTm : ∀ m ∈ S.Mbar, conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Hm)
    (hTs : ∀ f ∈ Hm, ∃ m ∈ S.Mbar, conjEquiv T (m : S.Qt ≃ₗ[ZMod 2] S.Qt) = f)
    {a : S.Qt} (ha0 : a ≠ 0) (haq : S.q a = 0) (L : Subgroup S.Mbar)
    (hLc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hLs : ∀ x ∈ L, x * x = 1)
    (hL8 : 8 ≤ Nat.card L) (hLa : ∀ ℓ ∈ L, ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a)
    (hLn : ∀ m : S.Mbar, ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L)
    (D : Submodule (ZMod 2) S.Qt) (haD : a ∈ D)
    (hLD : ∀ ℓ ∈ L, ∀ v, polar S.q a v = 0 →
      ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ D)
    (hcard : Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) = 2 ^ 8)
    (hfaith : finrank (ZMod 2) D = 4 → ∀ ℓ ∈ L,
      (∀ v ∈ D, ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → ℓ = 1) :
    (T a ∈ Nsub ∨ T a ∈ Nssub) ∧
      ∀ ℓ ∈ L, ℓ ≠ 1 → IsTypeA S.q ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hinj : Function.Injective (cT (S := S) T) := cT_injective T
  have hmem : ∀ {ℓh : Vm ≃ₗ[ZMod 2] Vm}, ℓh ∈ L.map (cT (S := S) T) →
      ∃ ℓ ∈ L, cT (S := S) T ℓ = ℓh := fun h => by
    obtain ⟨ℓ, hℓ, e⟩ := Subgroup.mem_map.mp h
    exact ⟨ℓ, hℓ, e⟩
  have key := localTest_model (b := T a) (by simpa using ha0) (by rw [hTq]; exact haq)
    (L.map (cT (S := S) T)) ?_ ?_ ?_ ?_ ?_ ?_ (D.map (T : S.Qt →ₗ[ZMod 2] Vm)) ?_ ?_ ?_ ?_
  · refine ⟨key.1, fun ℓ hℓ hℓ1 => ?_⟩
    have h1 : cT (S := S) T ℓ ≠ 1 := fun h => hℓ1 (hinj (h.trans (map_one _).symm))
    exact isTypeA_of_conjEquiv T hTq (key.2 _ (Subgroup.mem_map_of_mem _ hℓ) h1)
  · intro ℓh h
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem h
    exact hTm ℓ.1 ℓ.2
  · rintro _ h _ h'
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem h
    obtain ⟨ℓ', hℓ', rfl⟩ := hmem h'
    rw [← map_mul, ← map_mul, hLc ℓ hℓ ℓ' hℓ']
  · rintro _ h
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem h
    rw [← map_mul, hLs ℓ hℓ, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hL8
  · rintro _ h
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem h
    rw [cT_apply]
    exact congrArg T (hLa ℓ hℓ)
  · intro m hm hmb ℓh hℓh
    obtain ⟨m₀, hm₀, rfl⟩ := hTs m hm
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem hℓh
    have hfix : ((⟨m₀, hm₀⟩ : S.Mbar) : S.O).1 a = a := by
      rw [conjEquiv_apply_T] at hmb
      exact T.injective hmb
    have hn := hLn ⟨m₀, hm₀⟩ hfix ℓ hℓ
    have : cT (S := S) T ((⟨m₀, hm₀⟩ : S.Mbar) * ℓ * (⟨m₀, hm₀⟩ : S.Mbar)⁻¹) =
        conjEquiv T (m₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) * cT (S := S) T ℓ *
          (conjEquiv T (m₀ : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hn
  · exact Submodule.mem_map_of_mem haD
  · intro ℓh hℓh v hv
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem hℓh
    obtain ⟨v₀, rfl⟩ := T.surjective v
    rw [polar_q0_T T hTq] at hv
    refine ⟨_, hLD ℓ hℓ v₀ hv, ?_⟩
    rw [LinearEquiv.coe_coe, map_sub, cT_apply]
  · rw [Subgroup.card_map_of_injective hinj, LinearEquiv.finrank_map_eq]
    exact hcard
  · intro h4 ℓh hℓh hfixD
    obtain ⟨ℓ, hℓ, rfl⟩ := hmem hℓh
    rw [LinearEquiv.finrank_map_eq] at h4
    have := hfaith h4 ℓ hℓ fun v hv => by
      have := hfixD (T v) (Submodule.mem_map_of_mem hv)
      rw [cT_apply] at this
      exact T.injective this
    rw [this, map_one]

theorem localTest_setting {X : Subgroup S.O}
    {A B : Submodule (ZMod 2) S.Qt} (hP : Pair S X A B) (hw : S.width = 4) (hXM : X ≤ S.Mbar)
    (hidx : X.relIndex S.Mbar = 2)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG) (hne : k * S.z * k⁻¹ ≠ S.z) :
    (S.cl (k * S.z * k⁻¹) ∈ A ∨ S.cl (k * S.z * k⁻¹) ∈ B) ∧
      ∀ ℓ ∈ S.Lbar k, ℓ ≠ 1 → IsTypeA S.q (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨T, hTq, hTA, hTB, hTm, hTs⟩ := exists_model_iso hP hw hXM hidx hmap
  have ha0 : S.cl (k * S.z * k⁻¹) ≠ 0 := S.s12_cl_ne_zero_of_conj hk hne
  have haq : S.q (S.cl (k * S.z * k⁻¹)) = 0 := (S.q_cl_eq_zero_iff hk).mpr (S.s12_conj_z_sq k)
  have hfaith : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa k)) = 4 → ∀ ℓ ∈ W4C1.Lgrp S k,
      (∀ v ∈ S.clSub (S.QG ⊓ S.Qa k), W4C1.rhoM S ℓ v = v) → ℓ = 1 := by
    intro hk4 ℓ hℓ hfix
    have hX : Nat.card (S.QG ⊓ S.Qa k : Subgroup G) = 2 ^ (S.width + 1) := by
      rw [S.card_QG_inf_Qa_eq hk hne, hk4, hw]
      norm_num
    exact Subtype.ext (W4C1.faithful_of_card S hk hne hX ((W4C1.mem_Lgrp S).mp hℓ) hfix)
  have key := transport T hTq hTm hTs ha0 haq (W4C1.Lgrp S k) (W4C1.Lgrp_comm S hk)
    (W4C1.Lgrp_sq S hk) (W4C1.eight_le_card_Lgrp S hk hne hw) (W4C1.Lgrp_fix S hk)
    (W4C1.Lgrp_normalized S hk hne hw) (S.clSub (S.QG ⊓ S.Qa k)) (S6.cl_mem_clSub_self hk)
    (fun ℓ hℓ v hv => S.s12_Lbar_apply_sub_mem hk ((W4C1.mem_Lgrp S).mp hℓ) hv)
    (W4C1.card_Lgrp_mul S hk hne hw) hfaith
  refine ⟨?_, fun ℓ hℓ hℓ1 => ?_⟩
  · rcases key.1 with h | h
    · left
      rw [← hTA] at h
      obtain ⟨y, hy, hyT⟩ := Submodule.mem_map.mp h
      exact (T.injective hyT) ▸ hy
    · right
      rw [← hTB] at h
      obtain ⟨y, hy, hyT⟩ := Submodule.mem_map.mp h
      exact (T.injective hyT) ▸ hy
  · have h1 : (⟨ℓ, S.Lbar_le_Mbar k hℓ⟩ : S.Mbar) ≠ 1 := fun h => hℓ1 (congrArg Subtype.val h)
    exact key.2 _ ((W4C1.mem_Lgrp S).mpr hℓ) h1

end CFSG.GF2Type.Smith1979.W4C2
