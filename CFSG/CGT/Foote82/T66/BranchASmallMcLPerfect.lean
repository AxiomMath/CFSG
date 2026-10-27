module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSym
public import CFSG.CGT.Foote82.T66.BranchASmallGL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11 CFSG.ComponentClassification.OutcomeLocal
open CFSG.LocalAnalysis.ComponentInitial

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def flagQ (a : V) (φ : Module.Dual (ZMod 2) V) : Subgroup (GLV V) where
  carrier := {g | (∀ v, φ (g v) = φ v) ∧
    (∀ v, φ v = 0 → g v - v ∈ Submodule.span (ZMod 2) {a}) ∧ g a = a}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun v => ?_, fun v hv => ?_, ?_⟩
    · show φ (g (h v)) = φ v
      rw [hg1, hh1]
    · show g (h v) - v ∈ _
      have e : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [e]
      exact Submodule.add_mem _ (hg2 _ (by rw [hh1]; exact hv)) (hh2 v hv)
    · show g (h a) = a
      rw [hh3, hg3]
  one_mem' := ⟨fun v => rfl, fun v _ => by simp, rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hgi : ∀ v, g (g⁻¹ v) = v := glv_apply_inv_apply g
    refine ⟨fun v => ?_, fun v hv => ?_, ?_⟩
    · have := hg1 (g⁻¹ v)
      rw [hgi] at this
      exact this.symm
    · have hw : φ (g⁻¹ v) = 0 := by
        have := hg1 (g⁻¹ v)
        rw [hgi] at this
        rw [← this]
        exact hv
      have := hg2 _ hw
      rw [hgi] at this
      have h2 := Submodule.neg_mem _ this
      rwa [neg_sub] at h2
    · have := congrArg (fun w => (g⁻¹ : GLV V) w) hg3
      simp only [glv_inv_apply_apply] at this
      exact this.symm

theorem mem_flagQ {a : V} {φ : Module.Dual (ZMod 2) V} {g : GLV V} :
    g ∈ flagQ a φ ↔ (∀ v, φ (g v) = φ v) ∧
      (∀ v, φ v = 0 → g v - v ∈ Submodule.span (ZMod 2) {a}) ∧ g a = a := Iff.rfl

theorem pow_four_eq_one_of_mem_flagQ {a : V} {φ : Module.Dual (ZMod 2) V} (hφa : φ a = 0)
    {g : GLV V} (hg : g ∈ flagQ a φ) : g ^ 4 = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set u : V → V := fun v => g v - v with hu
  have hgu : ∀ v, g v = v + u v := fun v => by simp [hu]
  have hu_add : ∀ v w, u (v + w) = u v + u w := fun v w => by
    simp only [hu, map_add]
    abel
  have hu1 : ∀ v, φ (u v) = 0 := fun v => by
    show φ (g v - v) = 0
    rw [map_sub, hg1]
    exact sub_self _
  have hu2 : ∀ v, u (u v) ∈ Submodule.span (ZMod 2) {a} := fun v => hg2 _ (hu1 v)
  have hua : ∀ x ∈ Submodule.span (ZMod 2) {a}, u x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    simp [hu, hg3]
  have hu3 : ∀ v, u (u (u v)) = 0 := fun v => hua _ (hu2 v)
  have hsq : ∀ v, (g * g) v = v + u (u v) := by
    intro v
    rw [glv_mul_apply, hgu (g v), hgu v, hu_add]
    have : u v + u v = 0 := zmod2_add_self _
    calc v + u v + (u v + u (u v)) = v + (u v + u v) + u (u v) := by abel
      _ = v + u (u v) := by rw [this, add_zero]
  apply LinearEquiv.ext
  intro v
  have h4 : g ^ 4 = (g * g) * (g * g) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, glv_mul_apply, hsq ((g * g) v), hsq v, hu_add, hu_add, hu3 (u v)]
  show v + u (u v) + (u (u v) + 0) = v
  rw [add_zero, add_assoc, zmod2_add_self, add_zero]

theorem isPGroup_flagQ_inf {a : V} {φ : Module.Dual (ZMod 2) V} (hφa : φ a = 0)
    (H : Subgroup (GLV V)) : IsPGroup 2 ↥(flagQ a φ ⊓ H) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_four_eq_one_of_mem_flagQ hφa g.2.1


theorem exists_dual_ne {a : V} (φ : Module.Dual (ZMod 2) V)
    (hn : 3 ≤ Module.finrank (ZMod 2) V) :
    ∃ ψ : Module.Dual (ZMod 2) V, ψ a = 0 ∧ ψ ≠ 0 ∧ ψ ≠ φ := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hrank := LinearMap.finrank_range_add_finrank_ker (Module.Dual.eval (ZMod 2) V a)
  have hr : Module.finrank (ZMod 2) ↥(LinearMap.range (Module.Dual.eval (ZMod 2) V a)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (Module.Dual.eval (ZMod 2) V a))
    rwa [Module.finrank_self] at this
  rw [Subspace.dual_finrank_eq] at hrank
  have hW : 2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)) := by
    omega
  by_contra hall
  push Not at hall
  have hsub : ((LinearMap.ker (Module.Dual.eval (ZMod 2) V a) : Submodule (ZMod 2) _) :
      Set (Module.Dual (ZMod 2) V)) ⊆ {0, φ} := by
    intro ψ hψ
    by_cases h0 : ψ = 0
    · exact Or.inl h0
    · exact Or.inr (hall ψ hψ h0)
  have h1 : Nat.card ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)) ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc Set.ncard ((LinearMap.ker (Module.Dual.eval (ZMod 2) V a) : Submodule (ZMod 2) _) :
          Set (Module.Dual (ZMod 2) V)) ≤ Set.ncard ({0, φ} : Set (Module.Dual (ZMod 2) V)) :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          calc Set.ncard ({0, φ} : Set (Module.Dual (ZMod 2) V))
              ≤ Set.ncard ({φ} : Set (Module.Dual (ZMod 2) V)) + 1 := Set.ncard_insert_le _ _
            _ = 2 := by rw [Set.ncard_singleton]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h1
  have : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker (Module.Dual.eval (ZMod 2) V a)) :=
    Nat.pow_le_pow_right (by norm_num) hW
  omega

theorem exists_mem_ker_notMem_span {φ : Module.Dual (ZMod 2) V} (hφ : φ ≠ 0) (a : V)
    (hn : 3 ≤ Module.finrank (ZMod 2) V) :
    ∃ b : V, φ b = 0 ∧ b ∉ Submodule.span (ZMod 2) {a} := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have h2 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {a}) ≤ 1 := by
    by_cases ha : a = 0
    · rw [ha, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton ha]
  by_contra hall
  push Not at hall
  have hle : LinearMap.ker φ ≤ Submodule.span (ZMod 2) {a} := fun b hb => hall b hb
  have := Submodule.finrank_mono hle
  omega

theorem exists_apply_zero_one {f : LinearMap.BilinForm (ZMod 2) V} (hnd : f.Nondegenerate)
    {a b : V} (hb : b ∉ Submodule.span (ZMod 2) {a}) : ∃ v, f a v = 0 ∧ f b v = 1 := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  by_contra hall
  push Not at hall
  have hker : (⨅ _ : Unit, LinearMap.ker (f a)) ≤ LinearMap.ker (f b) := by
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hv' : f a v = 0 := hv ()
    rw [LinearMap.mem_ker]
    rcases zmod2_eq_zero_or_one (f b v) with h | h
    · exact h
    · exact absurd h (hall v hv')
  have hmem := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => f a) hker
  rw [Set.range_const, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  apply hb
  have h0 : b - c • a = 0 := by
    apply hnd.1
    intro v
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, ← hc]
    simp
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)

theorem eq_of_tv_mem_bilinIsometryGroup {f : LinearMap.BilinForm (ZMod 2) V}
    (hnd : f.Nondegenerate) (halt : f.IsAlt) {φ : Module.Dual (ZMod 2) V} {a : V}
    (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) (hmem : tv φ a h ∈ bilinIsometryGroup f) :
    φ = f a := by
  have key : ∀ x y, φ y * f a x + φ x * f a y = 0 := by
    intro x y
    have h1 := hmem x y
    simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, halt.self_eq_zero, mul_zero, add_zero] at h1
    have hxa : f x a = f a x := by
      rw [← halt.neg_eq a x, zmod2_neg]
    rw [hxa, add_assoc] at h1
    have h2 := add_left_cancel (h1.trans (add_zero _).symm)
    rw [add_comm] at h2
    exact h2
  obtain ⟨v₀, hv₀⟩ := exists_apply_eq_one hφ
  have hfa : ∀ y, f a y = φ y * f a v₀ := by
    intro y
    have := key v₀ y
    rw [hv₀, one_mul] at this
    have h2 : f a y = -(φ y * f a v₀) := eq_neg_of_add_eq_zero_right this
    rw [h2, zmod2_neg]
  have hv₀1 : f a v₀ = 1 := by
    rcases zmod2_eq_zero_or_one (f a v₀) with h0 | h1
    · exfalso
      apply ha
      apply hnd.1
      intro y
      rw [hfa y, h0, mul_zero]
    · exact h1
  ext y
  rw [hfa y, hv₀1, mul_one]

theorem commutator_orthGL_ne {Q : QuadraticForm (ZMod 2) V}
    (hQ : (_root_.QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank (ZMod 2) V) :
    ⁅CFSG.HardMathSupport.Cooperstein.StructureLie.orthGL Q,
      CFSG.HardMathSupport.Cooperstein.StructureLie.orthGL Q⁆ ≠
      CFSG.HardMathSupport.Cooperstein.StructureLie.orthGL Q := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  intro h
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  have hmap : (CFSG.HardMathSupport.Cooperstein.StructureLie.orthGL Q).map e.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  have h2 : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [← hmap, ← Subgroup.map_commutator, h]
  have hcard := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_orthogonalGroup_eq_two_mul hQ h6
  rw [h2] at hcard
  have hpos : 0 < Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := Nat.card_pos
  omega

theorem range_not_perfect {m : ℕ} (hm : 5 ≤ m) {Γ : Type*} [Group Γ]
    (ρ : Equiv.Perm (Fin m) →* Γ) (hρ : Function.Injective ρ) :
    ⁅ρ.range, ρ.range⁆ ≠ ρ.range := by
  intro h
  have h5 : 5 ≤ Nat.card (Fin m) := by simpa using hm
  have hA : ⁅(⊤ : Subgroup (Equiv.Perm (Fin m))), ⊤⁆ = alternatingGroup (Fin m) := by
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq h5
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hA] at h
  have h' := Subgroup.map_injective hρ h
  have hmem : Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ ∈ alternatingGroup (Fin m) :=
    h' ▸ Subgroup.mem_top _
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by simp)] at hmem
  exact absurd hmem (by decide)

variable {G L : Subgroup (GLV V)} {z : GLV V}

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem fix_of_mem_centralizer {a : V} {φ : Module.Dual (ZMod 2) V} (ha : a ≠ 0)
    (hφ : φ ≠ 0) (hz : ∀ v, z v = v + φ v • a) {c : GLV V}
    (hc' : c ∈ Subgroup.centralizer ({z} : Set (GLV V))) :
    c a = a ∧ ∀ v, φ (c v) = φ v := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc'
  have key : ∀ v, φ v • c a = φ (c v) • a := by
    intro v
    have h1 := congrArg (fun f : GLV V => f v) hc'
    simp only [glv_mul_apply] at h1
    rw [hz, map_add, map_smul, hz] at h1
    have := add_left_cancel h1
    exact this
  obtain ⟨v₀, hv₀⟩ := exists_apply_eq_one hφ
  have hca : c a = φ (c v₀) • a := by
    have := key v₀
    rwa [hv₀, one_smul] at this
  have hca' : c a = a := by
    rcases zmod2_eq_zero_or_one (φ (c v₀)) with h | h
    · exfalso
      rw [h, zero_smul] at hca
      apply ha
      have := congrArg (fun w => (c⁻¹ : GLV V) w) hca
      simpa only [glv_inv_apply_apply, map_zero] using this
    · rwa [h, one_smul] at hca
  refine ⟨hca', fun v => ?_⟩
  have := key v
  rw [hca'] at this
  exact (smul_left_injective (ZMod 2) ha this).symm

theorem false_of_flagQ {a : V} {φ : Module.Dual (ZMod 2) V} (ha : a ≠ 0) (hφ : φ ≠ 0)
    (hφa : φ a = 0) (hz : ∀ v, z v = v + φ v • a) {u : GLV V} (huG : u ∈ G)
    (hu : u ∈ flagQ a φ) (hu2 : orderOf u = 2) (hne : u ≠ z) : False := by
  set N := flagQ a φ ⊓ G with hN
  have hQz : ∀ g ∈ flagQ a φ, g * z = z * g := by
    intro g hg
    obtain ⟨hg1, -, hg3⟩ := hg
    apply LinearEquiv.ext
    intro v
    simp only [glv_mul_apply]
    rw [hz, hz, map_add, map_smul, hg3, hg1]
  have hNC : N ≤ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) := fun g hg =>
    ⟨hg.2, Subgroup.mem_centralizer_singleton_iff.2 (hQz g hg.1)⟩
  have hNn : ∀ c ∈ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)), ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
    intro c hc' x hx
    obtain ⟨hca, hcφ⟩ := hc.fix_of_mem_centralizer ha hφ hz hc'.2
    have hcinvφ : ∀ v, φ (c⁻¹ v) = φ v := fun v => by
      have := hcφ (c⁻¹ v)
      rw [glv_apply_inv_apply] at this
      exact this.symm
    have hcinva : c⁻¹ a = a := by
      have := congrArg (fun w => (c⁻¹ : GLV V) w) hca
      simp only [glv_inv_apply_apply] at this
      exact this.symm
    obtain ⟨hx1, hx2, hx3⟩ := hx.1
    refine ⟨⟨fun v => ?_, fun v hv => ?_, ?_⟩, G.mul_mem (G.mul_mem hc'.1 hx.2) (G.inv_mem hc'.1)⟩
    · simp only [glv_mul_apply]
      rw [hcφ, hx1, hcinvφ]
    · simp only [glv_mul_apply]
      have hw : φ (c⁻¹ v) = 0 := by rw [hcinvφ]; exact hv
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 (hx2 _ hw)
      have e : c (x (c⁻¹ v)) - v = c (x (c⁻¹ v) - c⁻¹ v) := by
        rw [map_sub, glv_apply_inv_apply]
      rw [e, ← hk, map_smul, hca]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    · simp only [glv_mul_apply]
      rw [hcinva, hx3, hca]
  have hNsolv : Group.IsSolvable ↥N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (isPGroup_flagQ_inf hφa G).isNilpotent
    infer_instance
  have hcomm := CFSG.Fischer.Classification.Recognition.SpU.commute_of_isComponentOf
    hc.component hNC hNn hNsolv
  have huN : u ∈ N := ⟨hu, huG⟩
  have huK : u ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
    ⟨huG, Subgroup.mem_centralizer_iff.2 fun l hl => hcomm l hl u huN⟩
  exact hne (hc.eq_z_of_commute huK hu2 (hQz u hu))

theorem false_of_perfect
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1)
    (hzE : z ∈ layerIn G) (hn6 : 6 ≤ Module.finrank (ZMod 2) V) : False := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hGE := hc.eq_layerIn_of_mem hzE
  have hGperf : ⁅G, G⁆ = G := hc.conf.derived.trans hGE.symm
  have hperf : ⁅mapGL G, mapGL G⁆ = mapGL G := by rw [← mapGL_commutator, hGperf]
  obtain ⟨S, hS, hGS⟩ := hc.genByTransvections_mapGL hdim
  have htr := isF2Transvection_toGL hc.z_mul_z hc.z_ne_one hdim
  obtain ⟨φ, a, hφa, hφ, ha, hza⟩ := (isF2Transvection_iff _).1 htr
  have hz : ∀ v, z v = v + φ v • a := fun v => by
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) v) hza
    simpa only [toGL_apply, tv_apply] using this
  rcases mclaughlin_transvection_groups_F2 (by omega) (mapGL G) ⟨S, hS, hGS⟩
      hc.irreducible_mapGL with hGL | ⟨-, f, hnd, halt, hSp⟩ | ⟨-, Q, hQ, hO⟩ | ⟨-, hSym⟩
  ·
    obtain ⟨ψ, hψa, hψ0, hψφ⟩ := exists_dual_ne (a := a) φ (by omega)
    set u : GLV V := toGL.symm (tv ψ a hψa) with hudef
    have hu_apply : ∀ v, u v = v + ψ v • a := fun v => by
      rw [hudef, toGL_symm_apply, tv_apply]
    have huG : u ∈ G := by
      have h1 : toGL u ∈ mapGL G := by rw [hGL]; exact Subgroup.mem_top _
      simpa using mem_mapGL.1 h1
    have hu : u ∈ flagQ a φ := by
      refine ⟨fun v => ?_, fun v _ => ?_, ?_⟩
      · rw [hu_apply, map_add, map_smul, hφa, smul_zero, add_zero]
      · rw [hu_apply, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
      · rw [hu_apply, hψa, zero_smul, add_zero]
    have hu1 : u ≠ 1 := by
      intro h
      apply tv_ne_one hψa hψ0 ha
      have := congrArg toGL h
      rwa [hudef, MulEquiv.apply_symm_apply, map_one] at this
    have hu2 : orderOf u = 2 := by
      refine orderOf_eq_prime ?_ hu1
      rw [sq, hudef, ← map_mul, tv_mul_self, map_one]
    have hne : u ≠ z := by
      intro h
      apply hψφ
      ext v
      have h1 : ψ v • a = φ v • a := by
        have := congrArg (fun g : GLV V => g v) h
        simp only [hu_apply, hz] at this
        exact add_left_cancel this
      exact smul_left_injective (ZMod 2) ha h1
    exact hc.false_of_flagQ ha hφ hφa hz huG hu hu2 hne
  ·
    have hzSp : tv φ a hφa ∈ bilinIsometryGroup f := by
      rw [← hza, ← hSp]
      exact toGL_mem_mapGL hc.z_mem
    have hφf := eq_of_tv_mem_bilinIsometryGroup hnd halt hφa hφ ha hzSp
    obtain ⟨b, hb, hbs⟩ := exists_mem_ker_notMem_span hφ a (by omega)
    have hsymm : ∀ x y, f x y = f y x := fun x y => by
      rw [← halt.neg_eq, zmod2_neg]
    have hbb : f b b = 0 := halt.self_eq_zero b
    have hab : f (a + b) (a + b) = 0 := halt.self_eq_zero _
    have hfab : f a b = 0 := by rw [← hφf]; exact hb
    have hfba : f b a = 0 := by rw [hsymm]; exact hfab
    have hfaa : f a a = 0 := halt.self_eq_zero a
    have ht₁ := tv_mem_bilinIsometryGroup hsymm hbb
    have ht₂ := tv_mem_bilinIsometryGroup hsymm hab
    set u : GLV V := toGL.symm (tv (f b) b hbb * tv (f (a + b)) (a + b) hab) with hudef
    have hfba' : f b (a + b) = 0 := by rw [map_add (f b) a b, hfba, hbb, add_zero]
    have hu_apply : ∀ v, u v = v + f (a + b) v • (a + b) + f b v • b := fun v => by
      rw [hudef, toGL_symm_apply]
      show (tv (f b) b hbb : V →ₗ[ZMod 2] V) ((tv (f (a + b)) (a + b) hab : V →ₗ[ZMod 2] V) v) = _
      rw [tv_apply, tv_apply]
      have hfb : (f b) (v + (f (a + b)) v • (a + b)) = f b v := by
        rw [map_add (f b), map_smul (f b), hfba', smul_zero, add_zero]
      rw [hfb]
    have huG : u ∈ G := by
      have h1 : tv (f b) b hbb * tv (f (a + b)) (a + b) hab ∈ mapGL G := by
        rw [hSp]
        exact (bilinIsometryGroup f).mul_mem ht₁ ht₂
      simpa [hudef] using mem_mapGL.1 h1
    have hfapb : ∀ v, f (a + b) v = f a v + f b v := fun v => by rw [map_add]; rfl
    have hu : u ∈ flagQ a φ := by
      refine ⟨fun v => ?_, fun v hv => ?_, ?_⟩
      · have hfa' : f a (a + b) = 0 := by rw [map_add (f a) a b, hfaa, hfab, add_zero]
        rw [hu_apply, hφf, map_add (f a), map_add (f a), map_smul (f a), map_smul (f a), hfa',
          hfab, smul_zero, smul_zero, add_zero, add_zero]
      · rw [hφf] at hv
        have e : u v - v = f b v • a := by
          have h1 : f (a + b) v = f b v := by rw [hfapb, hv, zero_add]
          rw [hu_apply, h1, smul_add]
          have h2 : f b v • b + f b v • b = 0 := zmod2_add_self _
          calc v + (f b v • a + f b v • b) + f b v • b - v = f b v • a + (f b v • b + f b v • b) := by
                abel
            _ = f b v • a := by rw [h2, add_zero]
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
      · have h1 : f (a + b) a = 0 := by rw [hfapb, hfaa, hfba, add_zero]
        rw [hu_apply, h1, hfba, zero_smul, zero_smul, add_zero, add_zero]
    obtain ⟨v, hv0, hv1⟩ := exists_apply_zero_one hnd hbs
    have huv : u v = v + a := by
      have h1 : f (a + b) v = 1 := by rw [hfapb, hv0, hv1, zero_add]
      rw [hu_apply, h1, hv1, one_smul, one_smul]
      have h2 : b + b = 0 := zmod2_add_self b
      calc v + (a + b) + b = v + a + (b + b) := by abel
        _ = v + a := by rw [h2, add_zero]
    have hzv : z v = v := by rw [hz, hφf, hv0, zero_smul, add_zero]
    have hu1 : u ≠ 1 := by
      intro h
      have := congrArg (fun g : GLV V => g v) h
      simp only [huv] at this
      exact ha (add_left_cancel (this.trans (add_zero v).symm))
    have hfab' : f (a + b) b = 0 := by rw [hfapb, hfab, hbb, add_zero]
    have hf1 : ∀ w, f (a + b) (u w) = f (a + b) w := fun w => by
      rw [hu_apply, map_add (f (a + b)), map_add (f (a + b)), map_smul (f (a + b)),
        map_smul (f (a + b)), hab, hfab', smul_zero, smul_zero, add_zero, add_zero]
    have hf2 : ∀ w, f b (u w) = f b w := fun w => by
      rw [hu_apply, map_add (f b), map_add (f b), map_smul (f b), map_smul (f b), hfba', hbb,
        smul_zero, smul_zero, add_zero, add_zero]
    have hu2 : orderOf u = 2 := by
      refine orderOf_eq_prime ?_ hu1
      apply LinearEquiv.ext
      intro w
      rw [sq, glv_mul_apply, hu_apply (u w), hf1, hf2, hu_apply w]
      have e1 : f (a + b) w • (a + b) + f (a + b) w • (a + b) = 0 := zmod2_add_self _
      have e2 : f b w • b + f b w • b = 0 := zmod2_add_self _
      calc w + f (a + b) w • (a + b) + f b w • b + f (a + b) w • (a + b) + f b w • b
          = w + (f (a + b) w • (a + b) + f (a + b) w • (a + b)) + (f b w • b + f b w • b) := by
            abel
        _ = w := by rw [e1, e2, add_zero, add_zero]
    have hne : u ≠ z := by
      intro h
      have := congrArg (fun g : GLV V => g v) h
      simp only [huv, hzv] at this
      exact ha (add_left_cancel (this.trans (add_zero v).symm))
    exact hc.false_of_flagQ ha hφ hφa hz huG hu hu2 hne
  ·
    exact commutator_orthGL_ne hQ hn6 (by
      rw [show CFSG.HardMathSupport.Cooperstein.StructureLie.orthGL Q = mapGL G from hO.symm]
      exact hperf)
  ·
    rcases hSym with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · refine range_not_perfect (m := Module.finrank (ZMod 2) V + 1) (by omega)
        (sumZeroRep (Module.finrank (ZMod 2) V + 1))
        (CFSG.HardMathSupport.Cooperstein.StructureLie.sumZeroRep_injective (by omega)) ?_
      rw [← hβ, ← Subgroup.map_commutator, hperf]
    · refine range_not_perfect (m := Module.finrank (ZMod 2) V + 2) (by omega)
        (heartRep (Module.finrank (ZMod 2) V + 2))
        (CFSG.HardMathSupport.Cooperstein.StructureLie.heartRep_injective (by omega)) ?_
      rw [← hβ, ← Subgroup.map_commutator, hperf]

end Hyp

end CFSG.CGT.Foote82.BAS
