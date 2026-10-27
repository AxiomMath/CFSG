module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A.GL

open CFSG.Open
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut projEquiv)

section Gen

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {e : V ≃ₗ[ZMod 2] V}

@[expose] noncomputable def NsubEquivC {c : ℕ} (h3 : e ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (fixSp e) = c) : Nsub h3 ≃* VecAut c :=
  (MonoidHom.ofInjective (glueHom_injective (isCompl_fixSp_comSp h3))).symm.trans
    (conjEquiv (LinearEquiv.ofFinrankEq (fixSp e) (Fin c → ZMod 2) (by
      rw [Module.finrank_fin_fun]; exact hc)))

theorem Nsub_simple_nonab_c {c : ℕ} (hc3 : 3 ≤ c) (h3 : e ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (fixSp e) = c) :
    IsSimpleGroup (Nsub h3) ∧ ∃ a b : Nsub h3, a * b ≠ b * a :=
  simple_nonab_of_equiv (NsubEquivC h3 hc) (vecAut_simple_nonab hc3)

theorem Nsub_isQuasisimple_c {c : ℕ} (hc3 : 3 ≤ c) (h3 : e ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (fixSp e) = c) : CFSG.Open.IsQuasisimple (Nsub h3) := by
  obtain ⟨hs, hn⟩ := Nsub_simple_nonab_c hc3 h3 hc
  haveI := hs
  exact isQuasisimple_of_simple_nonab hn

theorem Nsub_center_c {c : ℕ} (hc3 : 3 ≤ c) (h3 : e ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (fixSp e) = c) : Subgroup.center (Nsub h3) = ⊥ := by
  obtain ⟨hs, hn⟩ := Nsub_simple_nonab_c hc3 h3 hc
  haveI := hs
  exact center_eq_bot_of_simple_nonab hn

theorem three_dvd_card_Nsub_c {k : ℕ} (hk : 1 ≤ k) (h3 : e ^ 3 = 1)
    (hc : Module.finrank (ZMod 2) (fixSp e) = 2 * k + 1) : 3 ∣ Nat.card (Nsub h3) := by
  obtain ⟨T, hTel, hTcard, -⟩ := exists_torus_fixed (V := fixSp e) (r := k) hc
  have h1 : Nat.card T ∣ Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) := Subgroup.card_subgroup_dvd_card T
  have h2 : Nat.card (Nsub h3) = Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) :=
    Nat.card_congr (MonoidHom.ofInjective (glueHom_injective (isCompl_fixSp_comSp h3))).symm.toEquiv
  rw [h2]
  refine dvd_trans ?_ h1
  rw [hTcard]
  exact dvd_pow_self 3 (by omega)

end Gen

section Count

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem card_le_three_pow (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ (Module.finrank (ZMod 2) V / 2) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨kE, hkE⟩ := card_eq_pow_three hE
  have hodd : Odd (Fintype.card E) := by
    rw [← Nat.card_eq_fintype_card, hkE]
    exact Odd.pow (by decide)
  have hinvtop : Inv2 E (⊤ : Submodule (ZMod 2) V) := fun _ _ _ _ => trivial
  obtain ⟨k, X, hXprop, hXle, hind, hsup, hfr⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.exists_decomp E hodd _ ⊤ hinvtop rfl
  have hdim : Module.finrank (ZMod 2) V = ∑ i, Module.finrank (ZMod 2) (X i) := by
    rw [← finrank_top (ZMod 2) V]
    exact hfr
  obtain ⟨ρf, hρf⟩ := exists_gen_data hE (fun i => (hXprop i).1) (fun i => (hXprop i).2)
  obtain ⟨hcardle, hdimle⟩ := card_le_planes hE hρf hsup hdim
  calc Nat.card E = Fintype.card E := Nat.card_eq_fintype_card
    _ ≤ 3 ^ Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := hcardle
    _ ≤ 3 ^ (Module.finrank (ZMod 2) V / 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)

variable {e : V ≃ₗ[ZMod 2] V}

@[expose] noncomputable def resFixEquiv (g : V ≃ₗ[ZMod 2] V) (hg : g * e = e * g) :
    fixSp e ≃ₗ[ZMod 2] fixSp e :=
  LinearEquiv.ofInjectiveEndo ((g : V →ₗ[ZMod 2] V).restrict (fun w hw => cent_fix hg hw)) (by
    intro a b hab
    apply Subtype.ext
    exact g.injective (congrArg Subtype.val hab))

@[expose] noncomputable def resFix (e : V ≃ₗ[ZMod 2] V) :
    Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) →* (fixSp e ≃ₗ[ZMod 2] fixSp e) where
  toFun g := resFixEquiv g.1 (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl

theorem resFix_apply (g : Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))) (w : fixSp e) :
    ((resFix e g w : fixSp e) : V) = (g : V ≃ₗ[ZMod 2] V) w := rfl

theorem isElemAbelian_range_hom {G Γ : Type*} [Group G] [Group Γ] {B : Subgroup G}
    (φ : ↥B →* Γ) (hB : IsElemAbelian 3 B) : IsElemAbelian 3 φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨b₁, h₁⟩ := a.2
    obtain ⟨b₂, h₂⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hB.1.is_comm.comm b₁ b₂))
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have : b ^ 3 = (1 : ↥B) := Subtype.ext (by simpa using hB.2 b b.2)
    rw [this, map_one]

theorem exists_pointwise_ker {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {d : V ≃ₗ[ZMod 2] V} (hdE : d ∈ E) :
    ∃ K0 : Subgroup (V ≃ₗ[ZMod 2] V), K0 ≤ E ∧ (∀ g ∈ K0, ∀ w ∈ fixSp d, g w = w) ∧
      Nat.card E ≤ Nat.card K0 * 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2) := by
  have hEC : E ≤ Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨d, hdE⟩)
  let ψ : ↥E →* (fixSp d ≃ₗ[ZMod 2] fixSp d) := (resFix d).comp (Subgroup.inclusion hEC)
  have hel : IsElemAbelian 3 ψ.range := isElemAbelian_range_hom ψ hE
  have hrange : Nat.card ψ.range ≤ 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2) :=
    card_le_three_pow ψ.range hel
  refine ⟨ψ.ker.map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ w hw
    have h1 : ψ x = 1 := hx
    have h2 := congrArg (fun f : fixSp d ≃ₗ[ZMod 2] fixSp d => ((f ⟨w, hw⟩ : fixSp d) : V)) h1
    exact h2
  · have hmul := Subgroup.card_ker_mul_card_range ψ
    have hk : Nat.card (ψ.ker.map E.subtype) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [hk, ← hmul]
    exact Nat.mul_le_mul_left _ hrange

theorem pointwise_ker_le_cent {d : V ≃ₗ[ZMod 2] V} (h3 : d ^ 3 = 1)
    {g : V ≃ₗ[ZMod 2] V} (hgC : g ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)))
    (hg : ∀ w ∈ fixSp d, g w = w) : ∀ h ∈ Nsub h3, g * h = h * g := by
  intro h hh
  have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
  rw [mem_Nsub] at hh
  have hc := isCompl_fixSp_comSp h3
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, u', rfl⟩ := exists_decomp hc v
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hg _ (hh.2 _ u.2), hh.1 _ u'.2, hg _ u.2, hh.1 _ (cent_com hgd u'.2)]

end Count

section Ext

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {e : V ≃ₗ[ZMod 2] V}

theorem glue_resFix_of_mem_Nsub (h3 : e ^ 3 = 1) {n : V ≃ₗ[ZMod 2] V} (hn : n ∈ Nsub h3)
    (hnC : n ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))) :
    glue (isCompl_fixSp_comSp h3) (resFix e ⟨n, hnC⟩) = n := by
  have hc := isCompl_fixSp_comSp h3
  rw [mem_Nsub] at hn
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, u', rfl⟩ := exists_decomp hc v
  rw [map_add, map_add, glue_apply_left, glue_apply_right, hn.1 u' u'.2]
  rfl

theorem conj_glue (h3 : e ^ 3 = 1) (g : Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))
    (f : fixSp e ≃ₗ[ZMod 2] fixSp e) :
    (g : V ≃ₗ[ZMod 2] V) * glue (isCompl_fixSp_comSp h3) f * (g : V ≃ₗ[ZMod 2] V)⁻¹ =
      glue (isCompl_fixSp_comSp h3) (resFix e g * f * (resFix e g)⁻¹) := by
  have hc := isCompl_fixSp_comSp h3
  have hg : (g : V ≃ₗ[ZMod 2] V) * e = e * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hgi : (g : V ≃ₗ[ZMod 2] V)⁻¹ * e = e * (g : V ≃ₗ[ZMod 2] V)⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.centralizer _).inv_mem g.2)
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, u', rfl⟩ := exists_decomp hc v
  simp only [LinearEquiv.mul_apply, map_add]
  have hu : ((g : V ≃ₗ[ZMod 2] V)⁻¹ (u : V)) ∈ fixSp e := cent_fix hgi u.2
  have hu' : ((g : V ≃ₗ[ZMod 2] V)⁻¹ (u' : V)) ∈ comSp e := cent_com hgi u'.2
  rw [show ((g : V ≃ₗ[ZMod 2] V)⁻¹ (u : V)) = (((⟨_, hu⟩ : fixSp e)) : V) from rfl,
    show ((g : V ≃ₗ[ZMod 2] V)⁻¹ (u' : V)) = (((⟨_, hu'⟩ : comSp e)) : V) from rfl,
    glue_apply_left, glue_apply_right]
  have e1 : (resFix e g)⁻¹ u = ⟨(g : V ≃ₗ[ZMod 2] V)⁻¹ (u : V), hu⟩ := by
    rw [← map_inv]
    apply Subtype.ext
    rfl
  rw [glue_apply_left, glue_apply_right]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, resFix_apply]
  congr 1
  exact apply_inv_apply (g : V ≃ₗ[ZMod 2] V) (u' : V)

theorem glue_comm_of_comm (h3 : e ^ 3 = 1) {d : V ≃ₗ[ZMod 2] V}
    (hd : d ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))
    {f : fixSp e ≃ₗ[ZMod 2] fixSp e}
    (hf : f * resFix e ⟨d, hd⟩ = resFix e ⟨d, hd⟩ * f) :
    glue (isCompl_fixSp_comSp h3) f * d = d * glue (isCompl_fixSp_comSp h3) f := by
  have hc := isCompl_fixSp_comSp h3
  have hde : d * e = e * d := Subgroup.mem_centralizer_singleton_iff.1 hd
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, u', rfl⟩ := exists_decomp hc v
  simp only [LinearEquiv.mul_apply, map_add]
  have hdu : d (u : V) ∈ fixSp e := cent_fix hde u.2
  have hdu' : d (u' : V) ∈ comSp e := cent_com hde u'.2
  rw [show d (u : V) = ((⟨_, hdu⟩ : fixSp e) : V) from rfl,
    show d (u' : V) = ((⟨_, hdu'⟩ : comSp e) : V) from rfl, glue_apply_left, glue_apply_right,
    glue_apply_left, glue_apply_right]
  have h1 := congrArg (fun φ : fixSp e ≃ₗ[ZMod 2] fixSp e => ((φ u : fixSp e) : V)) hf
  simp only [LinearEquiv.mul_apply] at h1
  have e1 : (resFix e ⟨d, hd⟩) u = ⟨d (u : V), hdu⟩ := rfl
  rw [e1] at h1
  have e2 : (((resFix e ⟨d, hd⟩) (f u) : fixSp e) : V) = d ((f u : fixSp e) : V) := rfl
  rw [e2] at h1
  show _ + d (u' : V) = _ + d (u' : V)
  rw [h1]

theorem ext_layer (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2)
    {d : V ≃ₗ[ZMod 2] V} (hd : d ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))
    (F : Subgroup (fixSp e ≃ₗ[ZMod 2] fixSp e))
    (hFle : F ≤ Subgroup.centralizer ({resFix e ⟨d, hd⟩} : Set (fixSp e ≃ₗ[ZMod 2] fixSp e)))
    (hFn : (F.subgroupOf (Subgroup.centralizer
      ({resFix e ⟨d, hd⟩} : Set (fixSp e ≃ₗ[ZMod 2] fixSp e)))).Normal)
    (hFc : ⁅Subgroup.centralizer ({resFix e ⟨d, hd⟩} : Set (fixSp e ≃ₗ[ZMod 2] fixSp e)),
      Subgroup.centralizer ({resFix e ⟨d, hd⟩} : Set (fixSp e ≃ₗ[ZMod 2] fixSp e))⁆ ≤ F) :
    F.map (glueHom (isCompl_fixSp_comSp h3)) ≤
        Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
          Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) ∧
      ((F.map (glueHom (isCompl_fixSp_comSp h3))).subgroupOf
        (Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
          Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)))).Normal ∧
      ⁅Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
          Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)),
        Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
          Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V))⁆ ≤
        F.map (glueHom (isCompl_fixSp_comSp h3)) := by
  have hc := isCompl_fixSp_comSp h3
  set Cd : Subgroup (fixSp e ≃ₗ[ZMod 2] fixSp e) :=
    Subgroup.centralizer ({resFix e ⟨d, hd⟩} : Set (fixSp e ≃ₗ[ZMod 2] fixSp e)) with hCd
  have hfcomm : ∀ f ∈ F, f * resFix e ⟨d, hd⟩ = resFix e ⟨d, hd⟩ * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.1 (hFle hf)
  have hle : F.map (glueHom hc) ≤ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
      Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨Nsub_le_cent h3 ⟨f, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact glue_comm_of_comm h3 hd (hfcomm f hf)
  have hhat : ∀ (k : V ≃ₗ[ZMod 2] V) (hk : k ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) ⊓
      Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V))),
      resFix e ⟨k, hk.1⟩ ∈ Cd := by
    intro k hk
    rw [hCd, Subgroup.mem_centralizer_singleton_iff]
    have hkd : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
    have : (⟨k, hk.1⟩ : Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))) * ⟨d, hd⟩ =
        ⟨d, hd⟩ * ⟨k, hk.1⟩ := Subtype.ext hkd
    rw [← map_mul, this, map_mul]
  refine ⟨hle, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    obtain ⟨f, hf, rfl⟩ := hh
    have hconj := conj_glue h3 ⟨k, hk.1⟩ f
    have hmem : resFix e ⟨k, hk.1⟩ * f * (resFix e ⟨k, hk.1⟩)⁻¹ ∈ F :=
      (Subgroup.normal_subgroupOf_iff hFle).1 hFn f _ hf (hhat k hk)
    refine ⟨_, hmem, ?_⟩
    exact hconj.symm
  · rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    have hkC₁ := hk₁.1
    have hkC₂ := hk₂.1
    have hcomm : ⁅k₁, k₂⁆ ∈ Nsub h3 :=
      comm_le_Nsub h3 hfr (Subgroup.commutator_mem_commutator hkC₁ hkC₂)
    have hcC : ⁅k₁, k₂⁆ ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) :=
      by
        rw [commutatorElement_def]
        exact (Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).mul_mem
          ((Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).mul_mem
            ((Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).mul_mem hkC₁ hkC₂)
            ((Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).inv_mem hkC₁))
          ((Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).inv_mem hkC₂)
    have hglue := glue_resFix_of_mem_Nsub h3 hcomm hcC
    have hres : resFix e ⟨⁅k₁, k₂⁆, hcC⟩ =
        ⁅resFix e ⟨k₁, hkC₁⟩, resFix e ⟨k₂, hkC₂⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    have hF : resFix e ⟨⁅k₁, k₂⁆, hcC⟩ ∈ F := by
      rw [hres]
      exact hFc (Subgroup.commutator_mem_commutator (hhat k₁ hk₁) (hhat k₂ hk₂))
    exact ⟨_, hF, hglue⟩

end Ext

section Classify

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem finrank_comSp_pos {d : V ≃ₗ[ZMod 2] V} (hd1 : d ≠ 1) :
    0 < Module.finrank (ZMod 2) (comSp d) := by
  by_contra hcon
  have h0 : Module.finrank (ZMod 2) (comSp d) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  apply hd1
  apply LinearEquiv.ext
  intro v
  have : d v - v ∈ comSp d := mem_comSp.2 ⟨v, rfl⟩
  rw [h0, Submodule.mem_bot, sub_eq_zero] at this
  exact this

theorem finrank_comSp_eq_two {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E) (hge : 3 ^ r ≤ Nat.card E)
    {d : V ≃ₗ[ZMod 2] V} (hdE : d ∈ E) (h3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hsmall : ∀ K0 : Subgroup (V ≃ₗ[ZMod 2] V), K0 ≤ E →
      (∀ g ∈ K0, ∀ h ∈ Nsub h3, g * h = h * g) → Nat.card K0 ≤ 3) :
    Module.finrank (ZMod 2) (comSp d) = 2 := by
  obtain ⟨K0, hK0E, hK0fix, hcard⟩ := exists_pointwise_ker hE hdE
  have hEC : E ≤ Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨d, hdE⟩)
  have hK03 : Nat.card K0 ≤ 3 :=
    hsmall K0 hK0E (fun g hg => pointwise_ker_le_cent h3 (hEC (hK0E hg)) (hK0fix g hg))
  have hsum := finrank_fixSp h3
  have hpos := finrank_comSp_pos hd1
  obtain ⟨m, hm⟩ := even_finrank_comSp h3
  have h1 : 3 ^ r ≤ 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2 + 1) := by
    calc 3 ^ r ≤ Nat.card E := hge
      _ ≤ Nat.card K0 * 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2) := hcard
      _ ≤ 3 * 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2) := Nat.mul_le_mul_right _ hK03
      _ = 3 ^ (Module.finrank (ZMod 2) (fixSp d) / 2 + 1) := by rw [pow_succ]; ring
  have h2 : r ≤ Module.finrank (ZMod 2) (fixSp d) / 2 + 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  omega

end Classify

end CFSG.LocalAnalysis.GLTheoremA.S172A.GL

end
